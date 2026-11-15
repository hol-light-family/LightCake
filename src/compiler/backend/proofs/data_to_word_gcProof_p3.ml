(* ========================================================================= *)
(* data_to_word_gcProof_p3: part 3 of 3 (HOL4 lines 5934-8850) of the port   *)
(* of HOL4 compiler/backend/proofs/data_to_word_gcProofScript.sml (CakeML    *)
(* v3479).  Part of the correctness proof for data_to_word.                  *)
(* The parts _p1, _p2, _p3 are loaded one after the other (each needs the    *)
(* previous one); data_to_word_gcProof.ml needs the last.                    *)
(* GCP3AUX_ names are local helpers of this part.                            *)
(* Rendering: HOL4 'a ml_heap is written out as                              *)
(*   ((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list *)
(* and HOL4 Type state (wordSem state) is (A,C,FFI)wl_state; wordSem is a    *)
(* qualified ancestor in HOL4, so its constants are the wl_ ones.            *)
(* ========================================================================= *)

needs "compiler/backend/proofs/data_to_word_gcProof_p2.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 3: HOL4 lines 5934-8850 ===== *)

(* ------------------------------------------------------------------------- *)
(* Helpers of this part (GCP3AUX_ theorems and tactics, gcp3aux_ functions). *)
(* ------------------------------------------------------------------------- *)

(* gcp3aux: the kit's PAIRARG_TAC with fresh names that also avoid the     *)
(* variables free in the hypotheses of the assumption theorems (a variable *)
(* eliminated by an earlier split is still free there, and reusing its    *)
(* name made the tactic invalid: Failure CHOOSE at the end of the proof)   *)
let GCP3AUX_PAIRARG_TAC : tactic =
  fun (asl,w as gl) ->
    let whole = list_mk_conj(w :: map (concl o snd) asl) in
    let is_cand t =
      is_case_app t &&
      (let c,x,fs = dest_case_app t in
       fst(dest_const c) = "pair_CASE" && not (is_pair x) &&
       free_in x whole) in
    let t = find_term is_cand whole in
    let _,x,fs = dest_case_app t in
    let f = hd fs in
    let tya,tyb = match dest_type(type_of x) with
        "prod",[a;b] -> a,b | _ -> failwith "GCP3AUX_PAIRARG_TAC" in
    let n1,n2 =
      try let a,b = dest_abs f in let b1,_ = dest_abs b in
          fst(dest_var a),fst(dest_var b1)
      with Failure _ -> "p1","p2" in
    let avoid = union (frees whole)
                  (itlist (fun (_,th) acc -> union (freesl (hyp th)) acc) asl []) in
    let v1 = variant avoid (mk_var(n1,tya)) in
    let v2 = variant (v1::avoid) (mk_var(n2,tyb)) in
    let nch = ISPEC x (nchotomy_of_type (type_of x)) in
    (MP_TAC nch THEN
     DISCH_THEN(X_CHOOSE_THEN v1 (X_CHOOSE_THEN v2
       (fun th -> if is_var x then SUBST_ALL_TAC th
                  else SUBST_ALL_TAC th THEN ASSUME_TAC th))) THEN
     CASE_ASM_TIDY_TAC THEN CASE_REWRITE_TAC[]) gl;;

(* gcp3aux: assumptions that equate tuples are split into their components, *)
(* conjunctions are split, and variable equations are eliminated            *)
let GCP3AUX_SPLIT_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC;;

(* gcp3aux: GCP3AUX_PAIRARG_TAC splitting only pairs in the assumptions    *)
let GCP3AUX_PAIRARG_ASM_TAC : tactic =
  fun (asl,w as gl) ->
    let whole = list_mk_conj(w :: map (concl o snd) asl) in
    let wasm = list_mk_conj(`T` :: map (concl o snd) asl) in
    let is_cand t =
      is_case_app t &&
      (let c,x,fs = dest_case_app t in
       fst(dest_const c) = "pair_CASE" && not (is_pair x) &&
       free_in x wasm) in
    let t = find_term is_cand wasm in
    let _,x,fs = dest_case_app t in
    let f = hd fs in
    let tya,tyb = match dest_type(type_of x) with
        "prod",[a;b] -> a,b | _ -> failwith "GCP3AUX_PAIRARG_ASM_TAC" in
    let n1,n2 =
      try let a,b = dest_abs f in let b1,_ = dest_abs b in
          fst(dest_var a),fst(dest_var b1)
      with Failure _ -> "p1","p2" in
    let avoid = union (frees whole)
                  (itlist (fun (_,th) acc -> union (freesl (hyp th)) acc) asl []) in
    let v1 = variant avoid (mk_var(n1,tya)) in
    let v2 = variant (v1::avoid) (mk_var(n2,tyb)) in
    let nch = ISPEC x (nchotomy_of_type (type_of x)) in
    (MP_TAC nch THEN
     DISCH_THEN(X_CHOOSE_THEN v1 (X_CHOOSE_THEN v2
       (fun th -> if is_var x then SUBST_ALL_TAC th
                  else SUBST_ALL_TAC th THEN ASSUME_TAC th))) THEN
     CASE_ASM_TIDY_TAC THEN CASE_REWRITE_TAC[]) gl;;

let GCP3AUX_IN_domain_adjust_set = prove
 (`!(s:A spt) k. k IN domain (adjust_set s) <=> ?n. k = adjust_var n /\ n IN domain s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[adjust_set_def; domain_fromAList; IN_SET_OF_LIST; MEM_MAP; EXISTS_PROD; FST;
              PAIR_EQ] THEN
  REWRITE_TAC[domain_lookup; GSYM MEM_toAList] THEN MESON_TAC[]);;

(* HOL4 line 5934 *)
let NOT_1_domain = prove
 (`!names:A spt. ~(1 IN domain (adjust_set names))`,
  REWRITE_TAC[GCP3AUX_IN_domain_adjust_set] THEN MESON_TAC[adjust_var_NEQ]);;

(* HOL4 line 5941 *)
let NOT_3_domain = prove
 (`!names:A spt. ~(3 IN domain (adjust_set names))`,
  REWRITE_TAC[GCP3AUX_IN_domain_adjust_set] THEN MESON_TAC[adjust_var_NEQ]);;

(* HOL4 line 5949 *)
let NOT_5_domain = prove
 (`!names:A spt. ~(5 IN domain (adjust_set names))`,
  REWRITE_TAC[GCP3AUX_IN_domain_adjust_set] THEN MESON_TAC[adjust_var_NEQ]);;

(* HOL4 line 5957 *)
let data_to_word_gcProof_cut_names_adjust_set_insert_1 = prove
 (`!(names:A spt) (w:B) l.
     cut_names (adjust_set names) (insert 1 w l) = cut_names (adjust_set names) l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_names_def; domain_insert] THEN
  SIMP_TAC[SUBSET_INSERT_EQ_SUBSET; NOT_1_domain] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THEN
  SIMP_TAC[spt_eq_thm; wf_inter; lookup_inter_alt; lookup_insert] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[NOT_1_domain]);;

(* HOL4 line 5966 *)
let data_to_word_gcProof_cut_names_adjust_set_insert_3 = prove
 (`!(names:A spt) (w:B) l.
     cut_names (adjust_set names) (insert 3 w l) = cut_names (adjust_set names) l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_names_def; domain_insert] THEN
  SIMP_TAC[SUBSET_INSERT_EQ_SUBSET; NOT_3_domain] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THEN
  SIMP_TAC[spt_eq_thm; wf_inter; lookup_inter_alt; lookup_insert] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[NOT_3_domain]);;

(* HOL4 line 5975 *)
let case_EQ_SOME_IFF = prove
 (CASE_TERM
  `!(p:A option) (g:A->B option) y.
     (match p with NONE -> NONE | SOME x -> g x) = SOME y <=>
     ?x. p = SOME x /\ g x = SOME y`,
  GEN_TAC THEN CASES_ON `p:A option` THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

(* HOL4 line 5982 *)
let state_rel_set_store_AllocSize = prove
 (`!c l1 l2 (s:(C,FFI)data_state) w (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s (wl_set_store AllocSize (wl_Word w) t) v locs =
     data_to_word_gcProof_state_rel c l1 l2 s t v locs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_def; wl_set_store_def; heap_in_memory_store_def;
              code_oracle_rel_def] THEN
  SIMP[FLOOKUP_UPDATE; FAPPLY_FUPDATE_THM; FDOM_FUPDATE; IN_INSERT; ALL]);;

(* HOL4 line 5993 *)
let inter_insert = prove
 (`!n (x:A) t1 (t2:B spt).
     inter (insert n x t1) t2 =
     if n IN domain t2 then insert n x (inter t1 t2) else inter t1 t2`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  SIMP_TAC[spt_eq_thm; wf_inter; wf_insert; lookup_inter_alt; lookup_insert] THEN
  GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 6001 *)
let lookup_0_adjust_set = prove
 (`!l:A spt. lookup 0 (adjust_set l) = NONE`,
  REWRITE_TAC[lookup_NONE_domain; GCP3AUX_IN_domain_adjust_set] THEN
  MESON_TAC[adjust_var_NEQ]);;

(* HOL4 line 6007 *)
let lookup_1_adjust_set = prove
 (`!l:A spt. lookup 1 (adjust_set l) = NONE`,
  REWRITE_TAC[lookup_NONE_domain; GCP3AUX_IN_domain_adjust_set] THEN
  MESON_TAC[adjust_var_NEQ]);;

(* HOL4 line 6014 *)
let lookup_3_adjust_set = prove
 (`!l:A spt. lookup 3 (adjust_set l) = NONE`,
  REWRITE_TAC[lookup_NONE_domain; GCP3AUX_IN_domain_adjust_set] THEN
  MESON_TAC[adjust_var_NEQ]);;

(* HOL4 line 6021 *)
let lookup_5_adjust_set = prove
 (`!l:A spt. lookup 5 (adjust_set l) = NONE`,
  REWRITE_TAC[lookup_NONE_domain; GCP3AUX_IN_domain_adjust_set] THEN
  MESON_TAC[adjust_var_NEQ]);;

(* HOL4 line 6028 *)
let lookup_ODD_adjust_set = prove
 (`!n l:A spt. ODD n ==> lookup n (adjust_set l) = NONE`,
  REWRITE_TAC[lookup_NONE_domain; GCP3AUX_IN_domain_adjust_set] THEN
  MESON_TAC[EVEN_adjust_var; NOT_EVEN]);;

(* HOL4 line 6036 *)
let wf_adjust_set = prove
 (`!s:A spt. wf (adjust_set s)`,
  REWRITE_TAC[adjust_set_def; wf_fromAList]);;

(* GCP3AUX: adjust_var of a variable is in the adjusted domain iff the     *)
(* variable is in the domain (adjust_var_IN_adjust_set is for num_set only) *)
let GCP3AUX_adjust_var_IN_adjust_set = prove
 (`!n (s:A spt). adjust_var n IN domain (adjust_set s) <=> n IN domain s`,
  REWRITE_TAC[GCP3AUX_IN_domain_adjust_set; adjust_var_11] THEN MESON_TAC[]);;

(* HOL4 line 6042 *)
let lookup_adjust_set = prove
 (`!n s:A spt.
     lookup n (adjust_set s) =
     if ODD n \/ n = 0 then NONE else
     if (n - 2) DIV 2 IN domain s then SOME one else NONE`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [REWRITE_TAC[lookup_NONE_domain; GCP3AUX_IN_domain_adjust_set] THEN
    POP_ASSUM MP_TAC THEN MESON_TAC[EVEN_adjust_var; NOT_EVEN; adjust_var_NEQ];
    ALL_TAC] THEN
  POP_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM; NOT_ODD]) THEN
  MP_TAC(SPEC `n:num` IMP_adjust_var) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM th]) THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `adjust_var ((n - 2) DIV 2) IN domain (adjust_set (s:A spt))` MP_TAC THENL
     [ASM_REWRITE_TAC[GCP3AUX_adjust_var_IN_adjust_set]; ALL_TAC] THEN
    REWRITE_TAC[domain_lookup] THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
    MESON_TAC[one];
    ASM_REWRITE_TAC[lookup_NONE_domain; GCP3AUX_adjust_var_IN_adjust_set]]);;

(* GCP3AUX: the adjusted domain, pointwise *)
let GCP3AUX_IN_domain_adjust_set_alt = prove
 (`!n (s:A spt). n IN domain (adjust_set s) <=>
                 ~(ODD n \/ n = 0) /\ (n - 2) DIV 2 IN domain s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[domain_lookup; lookup_adjust_set] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  ASM_MESON_TAC[domain_lookup]);;

(* HOL4 line 6066 *)
let adjust_set_inter = prove
 (`!(t1:A spt) (t2:B spt).
     adjust_set (inter t1 t2) = inter (adjust_set t1) (adjust_set t2)`,
  REPEAT GEN_TAC THEN SIMP_TAC[spt_eq_thm; wf_adjust_set; wf_inter] THEN
  REWRITE_TAC[lookup_inter_alt; lookup_adjust_set; domain_inter; IN_INTER;
              GCP3AUX_IN_domain_adjust_set_alt] THEN
  X_GEN_TAC `n:num` THEN ASM_CASES_TAC `ODD n \/ n = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(n - 2) DIV 2 IN domain (t1:A spt)` THEN
  ASM_CASES_TAC `(n - 2) DIV 2 IN domain (t2:B spt)` THEN ASM_REWRITE_TAC[]);;

(* GCP3AUX: odd numbers are not in an adjusted domain *)
let GCP3AUX_ODD_NOT_IN_domain_adjust_set = prove
 (`!n (s:A spt). ODD n ==> ~(n IN domain (adjust_set s))`,
  SIMP_TAC[GCP3AUX_IN_domain_adjust_set_alt]);;

(* HOL4 line 6073 *)
let state_rel_insert_1 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) x (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s
       (wl_state_locals_fupd (K (insert 1 x (wl_state_locals t))) t) v locs =
     data_to_word_gcProof_state_rel c l1 l2 s t v locs`,
  REPEAT GEN_TAC THEN
  SIMP[data_to_word_gcProof_state_rel_def; lookup_insert; adjust_var_NEQ_1; inter_insert;
       NOT_1_domain]);;

(* HOL4 line 6083 *)
let state_rel_insert_3 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) x (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s
       (wl_state_locals_fupd (K (insert 3 x (wl_state_locals t))) t) v locs =
     data_to_word_gcProof_state_rel c l1 l2 s t v locs`,
  REPEAT GEN_TAC THEN
  SIMP[data_to_word_gcProof_state_rel_def; lookup_insert; adjust_var_NEQ; inter_insert;
       NOT_3_domain]);;

(* HOL4 line 6093 *)
let state_rel_insert_7 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) x (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s
       (wl_state_locals_fupd (K (insert 7 x (wl_state_locals t))) t) v locs =
     data_to_word_gcProof_state_rel c l1 l2 s t v locs`,
  REPEAT GEN_TAC THEN
  SIMP[data_to_word_gcProof_state_rel_def; lookup_insert; adjust_var_NEQ; inter_insert;
       GCP3AUX_ODD_NOT_IN_domain_adjust_set]);;

(* HOL4 line 6103 *)
let state_rel_insert_3_1 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) x y (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s
       (wl_state_locals_fupd (K (insert 3 x (insert 1 y (wl_state_locals t)))) t) v locs =
     data_to_word_gcProof_state_rel c l1 l2 s t v locs`,
  REPEAT GEN_TAC THEN
  SIMP[data_to_word_gcProof_state_rel_def; lookup_insert; adjust_var_NEQ; inter_insert;
       NOT_3_domain; NOT_1_domain]);;

(* HOL4 line 6114 *)
let state_rel_inc_clock = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs ==>
     data_to_word_gcProof_state_rel c l1 l2
       (data_state_clock_fupd (K (data_state_clock s + 1)) s)
       (wl_state_clock_fupd (K (wl_state_clock t + 1)) t) NONE locs`,
  REPEAT GEN_TAC THEN SIMP[data_to_word_gcProof_state_rel_def] THEN MESON_TAC[]);;

(* HOL4 line 6122 *)
let data_to_word_gcProof_dec_clock_inc_clock = prove
 (`!(s:(C,FFI)data_state) (t:(A,C,FFI)wl_state).
     (data_dec_clock (data_state_clock_fupd (K (data_state_clock s + 1)) s) = s) /\
     (wl_dec_clock (wl_state_clock_fupd (K (wl_state_clock t + 1)) t) = t)`,
  REWRITE_TAC[data_dec_clock_def; wl_dec_clock_def;
              (record_info "data_state").ri_component_equality;
              (record_info "wl_state").ri_component_equality] THEN
  SIMP[ADD_SUB]);;

(* GCP3AUX: a pair case in terms of FST and SND *)
let GCP3AUX_pair_CASE_FST_SND = prove
 (`!(p:A#B) (f:A->B->C). pair_CASE p f = f (FST p) (SND p)`,
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; FST; SND]);;

(* HOL4 line 6131 *)
let word_gc_move_IMP_isWord = prove
 (`!c' (c:A word) i pa old m dm w1 i1 pa1 m1 c1.
     word_gc_move c' (wl_Word c,i,pa,old,m,dm) = (w1,i1,pa1,m1,c1) ==> isWord w1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `FST:A word_loc#A word#A word#(A word->A word_loc)#bool->A word_loc`) THEN
  REWRITE_TAC[FST] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[word_gc_move_def; LET_DEF; LET_END_DEF; GCP3AUX_pair_CASE_FST_SND] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[isWord_def]);;

(* HOL4 line 6139 *)
let word_gen_gc_move_IMP_isWord = prove
 (`!c' (c:A word) i pa ib pb old m dm w1 i1 pa1 ib1 pb1 m1 c1.
     word_gen_gc_move c' (wl_Word c,i,pa,ib,pb,old,m,dm) =
       (w1,i1,pa1,ib1,pb1,m1,c1) ==>
     isWord w1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM
    `FST:A word_loc#A word#A word#A word#A word#(A word->A word_loc)#bool->A word_loc`) THEN
  REWRITE_TAC[FST] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[word_gen_gc_move_def; LET_DEF; LET_END_DEF; GCP3AUX_pair_CASE_FST_SND] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[isWord_def]);;

(* HOL4 line 6148 *)
let word_gen_gc_partial_move_IMP_isWord = prove
 (`!c' (c:A word) i pa old m dm gs rs w1 i1 pa1 m1 c1.
     word_gen_gc_partial_move c' (wl_Word c,i,pa,old,m,dm,gs,rs) = (w1,i1,pa1,m1,c1) ==>
     isWord w1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `FST:A word_loc#A word#A word#(A word->A word_loc)#bool->A word_loc`) THEN
  REWRITE_TAC[FST] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[word_gen_gc_partial_move_def; LET_DEF; LET_END_DEF; GCP3AUX_pair_CASE_FST_SND] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[isWord_def]);;

(* HOL4 line 6157 ([simp]) *)
let loc_ok_def = cake_def
  `(loc_ok (wl_Loc m n:A word_loc) <=> (n = 0)) /\
   (loc_ok (_:A word_loc) <=> T)`;;

let _ = cake_add_simps [loc_ok_def];;

(* HOL4 line 6162 *)
let loc_ok_word_addr = prove
 (`!c (w:(A word_loc)heap_address). loc_ok (word_addr c w)`,
  REPEAT GEN_TAC THEN CASES_ON `w:(A word_loc)heap_address` THEN
  TRY(CASES_ON `a:A word_loc`) THEN REWRITE_TAC[word_addr_def; loc_ok_def]);;

(* HOL4 line 6170 (local) *)
let word_gc_move_roots_IMP_FILTER0 = prove
 (`!ws i pa old m dm ws2 i2 pa2 m2 c2 (c:data_to_word_config).
     word_gc_move_roots c (ws,i,pa,old,m,dm) = (ws2,i2,pa2,m2,c2) /\
     ALL loc_ok ws ==>
     word_gc_move_roots c (FILTER isWord ws,i:A word,pa,old,m,dm) =
       (FILTER isWord ws2,i2,pa2,m2,c2)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[word_gc_move_roots_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[FILTER; word_gc_move_roots_def];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL] THEN CASES_ON `h:A word_loc` THEN
  REWRITE_TAC[FILTER; isWord_def; loc_ok_def; word_gc_move_roots_def] THEN
  REPEAT GCP3AUX_PAIRARG_TAC THENL
   [STRIP_TAC THEN RVEQ_TAC THEN IMP_RES_TAC word_gc_move_IMP_isWord THEN
    FIRST_X_ASSUM DRULE THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    GCP3AUX_SPLIT_TAC THEN ASM_REWRITE_TAC[FILTER];
    RULE_ASSUM_TAC(REWRITE_RULE[word_gc_move_def]) THEN STRIP_TAC THEN
    GCP3AUX_SPLIT_TAC THEN
    FIRST_X_ASSUM DRULE THEN ASM_REWRITE_TAC[FILTER; isWord_def]]);;

(* HOL4 line 6190 (local) *)
let word_gen_gc_move_roots_IMP_FILTER0 = prove
 (`!ws i pa ib pb old m dm ws2 i2 pa2 ib2 pb2 m2 c2 (c:data_to_word_config).
     word_gen_gc_move_roots c (ws,i,pa,ib,pb,old,m,dm) =
       (ws2,i2,pa2,ib2,pb2,m2,c2) /\
     ALL loc_ok ws ==>
     word_gen_gc_move_roots c (FILTER isWord ws,i:A word,pa,ib,pb,old,m,dm) =
       (FILTER isWord ws2,i2,pa2,ib2,pb2,m2,c2)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[word_gen_gc_move_roots_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[FILTER; word_gen_gc_move_roots_def];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL] THEN CASES_ON `h:A word_loc` THEN
  REWRITE_TAC[FILTER; isWord_def; loc_ok_def; word_gen_gc_move_roots_def] THEN
  REPEAT GCP3AUX_PAIRARG_TAC THENL
   [STRIP_TAC THEN RVEQ_TAC THEN IMP_RES_TAC word_gen_gc_move_IMP_isWord THEN
    FIRST_X_ASSUM DRULE THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    GCP3AUX_SPLIT_TAC THEN ASM_REWRITE_TAC[FILTER];
    RULE_ASSUM_TAC(REWRITE_RULE[word_gen_gc_move_def]) THEN STRIP_TAC THEN
    GCP3AUX_SPLIT_TAC THEN
    FIRST_X_ASSUM DRULE THEN ASM_REWRITE_TAC[FILTER; isWord_def]]);;

(* HOL4 line 6211 (the unused bound variables ib pb ib2 pb2 are left out;   *)
(* the theorem of line 6325 rebinds the name)                               *)
let word_gen_gc_partial_move_roots_IMP_FILTER = prove
 (`!ws i pa old m dm ws2 i2 pa2 m2 c2 (c:data_to_word_config) gs rs.
     word_gen_gc_partial_move_roots c (ws,i,pa,old,m,dm,gs,rs) =
       (ws2,i2,pa2,m2,c2) /\
     ALL loc_ok ws ==>
     word_gen_gc_partial_move_roots c (FILTER isWord ws,i:A word,pa,old,m,dm,gs,rs) =
       (FILTER isWord ws2,i2,pa2,m2,c2)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[word_gen_gc_partial_move_roots_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[FILTER; word_gen_gc_partial_move_roots_def];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL] THEN CASES_ON `h:A word_loc` THEN
  REWRITE_TAC[FILTER; isWord_def; loc_ok_def; word_gen_gc_partial_move_roots_def] THEN
  REPEAT GCP3AUX_PAIRARG_TAC THENL
   [STRIP_TAC THEN RVEQ_TAC THEN IMP_RES_TAC word_gen_gc_partial_move_IMP_isWord THEN
    FIRST_X_ASSUM DRULE THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    GCP3AUX_SPLIT_TAC THEN ASM_REWRITE_TAC[FILTER];
    RULE_ASSUM_TAC(REWRITE_RULE[word_gen_gc_partial_move_def]) THEN STRIP_TAC THEN
    GCP3AUX_SPLIT_TAC THEN
    FIRST_X_ASSUM DRULE THEN ASM_REWRITE_TAC[FILTER; isWord_def]]);;

(* HOL4 line 6232 (val IMP_EQ_DISJ) *)
let IMP_EQ_DISJ = prove
 (`!b1 b2. (b1 ==> b2) <=> ~b1 \/ b2`,
  MESON_TAC[]);;

(* GCP3AUX: the theorem of HOL4 line 6211 under its own name (the theorem   *)
(* of line 6325 rebinds word_gen_gc_partial_move_roots_IMP_FILTER)         *)
let GCP3AUX_word_gen_gc_partial_move_roots_IMP_FILTER0 =
  word_gen_gc_partial_move_roots_IMP_FILTER;;

(* GCP3AUX: moving the roots CONS g xs with the locations of xs filtered    *)
(* out (the root g, the global, is moved as it is)                          *)
let GCP3AUX_word_gc_move_roots_CONS_FILTER = prove
 (`!g xs i pa old m dm rs i2 pa2 m2 c2 (c:data_to_word_config).
     word_gc_move_roots c (CONS g xs,i,pa,old,m,dm) = (rs,i2,pa2,m2,c2) /\
     ALL loc_ok xs ==>
     word_gc_move_roots c (CONS g (FILTER isWord xs),i:A word,pa,old,m,dm) =
       (CONS (HD rs) (FILTER isWord (TL rs)),i2,pa2,m2,c2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_gc_move_roots_def] THEN
  REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN STRIP_TAC THEN
  REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN GCP3AUX_SPLIT_TAC THEN
  DRULE_ALL word_gc_move_roots_IMP_FILTER0 THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[HD; TL]);;

let GCP3AUX_word_gen_gc_move_roots_CONS_FILTER = prove
 (`!g xs i pa ib pb old m dm rs i2 pa2 ib2 pb2 m2 c2 (c:data_to_word_config).
     word_gen_gc_move_roots c (CONS g xs,i,pa,ib,pb,old,m,dm) =
       (rs,i2,pa2,ib2,pb2,m2,c2) /\
     ALL loc_ok xs ==>
     word_gen_gc_move_roots c (CONS g (FILTER isWord xs),i:A word,pa,ib,pb,old,m,dm) =
       (CONS (HD rs) (FILTER isWord (TL rs)),i2,pa2,ib2,pb2,m2,c2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_gen_gc_move_roots_def] THEN
  REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN STRIP_TAC THEN
  REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN GCP3AUX_SPLIT_TAC THEN
  DRULE_ALL word_gen_gc_move_roots_IMP_FILTER0 THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[HD; TL]);;

let GCP3AUX_word_gen_gc_partial_move_roots_CONS_FILTER = prove
 (`!g xs i pa old m dm gs rs' rs i2 pa2 m2 c2 (c:data_to_word_config).
     word_gen_gc_partial_move_roots c (CONS g xs,i,pa,old,m,dm,gs,rs') =
       (rs,i2,pa2,m2,c2) /\
     ALL loc_ok xs ==>
     word_gen_gc_partial_move_roots c
       (CONS g (FILTER isWord xs),i:A word,pa,old,m,dm,gs,rs') =
       (CONS (HD rs) (FILTER isWord (TL rs)),i2,pa2,m2,c2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_gen_gc_partial_move_roots_def] THEN
  REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN STRIP_TAC THEN
  REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN GCP3AUX_SPLIT_TAC THEN
  DRULE_ALL GCP3AUX_word_gen_gc_partial_move_roots_IMP_FILTER0 THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[HD; TL]);;

(* gcp3aux: rewrite the goal with the assumptions and reduce cases, until  *)
(* nothing changes                                                          *)
let GCP3AUX_ASM_CASE_TAC : tactic =
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[HD; TL]));;

(* gcp3aux: from an assumption (if .. then SOME .. else ..) = SOME .. to the *)
(* goal of the same shape, case by case                                      *)
let GCP3AUX_COND_SOME_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ]) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];;

(* HOL4 line 6234 *)
let word_gc_fun_IMP_FILTER = prove
 (`!c xs (m:A word->A word_loc) dm s stack1 m1 s1.
     word_gc_fun c (xs,m,dm,s) = SOME (stack1,m1,s1) /\
     ALL loc_ok xs ==>
     word_gc_fun c (FILTER isWord xs,m,dm,s) = SOME (FILTER isWord stack1,m1,s1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_gc_fun_def; word_full_gc_def; word_gen_gc_def; word_gen_gc_partial_def;
              word_gen_gc_partial_full_def] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CASES_ON `data_to_word_config_gc_kind c` THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN GCP3AUX_SPLIT_TAC THENL
   [ALL_TAC;
    DRULE_ALL GCP3AUX_word_gc_move_roots_CONS_FILTER THEN DISCH_TAC;
    DRULE_ALL GCP3AUX_word_gen_gc_move_roots_CONS_FILTER THEN DISCH_TAC THEN
    DRULE_ALL GCP3AUX_word_gen_gc_partial_move_roots_CONS_FILTER THEN DISCH_TAC] THEN
  GCP3AUX_ASM_CASE_TAC THEN GCP3AUX_COND_SOME_TAC);;

(* HOL4 line 6274 *)
let loc_merge_def = cake_def
  `(loc_merge [] (ys:(A word_loc)list) = []) /\
   (loc_merge (CONS (wl_Loc l1 l2) xs) ys = CONS (wl_Loc l1 l2) (loc_merge xs ys)) /\
   (loc_merge (CONS (wl_Word w) xs) (CONS y ys) = CONS y (loc_merge xs ys)) /\
   (loc_merge (CONS (wl_Word w) xs) [] = CONS (wl_Word w) xs)`;;

(* HOL4 loc_merge_ind (made by Definition) *)
let loc_merge_ind = cake_ind "loc_merge";;

(* HOL4 line 6281 *)
let LENGTH_loc_merge = prove
 (`!xs (ys:(A word_loc)list). LENGTH (loc_merge xs ys) = LENGTH xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[loc_merge_def; LENGTH] THEN
  CASES_ON `h:A word_loc` THEN GEN_TAC THEN TRY(CASES_ON `ys:(A word_loc)list`) THEN
  ASM_REWRITE_TAC[loc_merge_def; LENGTH]);;

(* HOL4 line 6289 *)
let word_gc_move_roots_IMP_FILTER = prove
 (`!ws i pa old m dm ws2 i2 pa2 m2 c2 (c:data_to_word_config).
     word_gc_move_roots c (FILTER isWord ws,i:A word,pa,old,m,dm) =
       (ws2,i2,pa2,m2,c2) /\
     ALL loc_ok ws ==>
     word_gc_move_roots c (ws,i,pa,old,m,dm) = (loc_merge ws ws2,i2,pa2,m2,c2)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[FILTER; word_gc_move_roots_def; loc_merge_def; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[loc_merge_def];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL] THEN CASES_ON `h:A word_loc` THEN
  REWRITE_TAC[FILTER; isWord_def; loc_ok_def] THEN STRIP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[word_gc_move_roots_def]) THEN
    REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN GCP3AUX_SPLIT_TAC THEN
    FIRST_X_ASSUM DRULE THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[word_gc_move_roots_def] THEN GCP3AUX_ASM_CASE_TAC THEN
    REWRITE_TAC[loc_merge_def];
    FIRST_X_ASSUM DRULE THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[word_gc_move_roots_def; word_gc_move_def] THEN GCP3AUX_ASM_CASE_TAC THEN
    REWRITE_TAC[loc_merge_def]]);;

(* HOL4 line 6307 *)
let word_gen_gc_move_roots_IMP_FILTER = prove
 (`!ws i pa ib pb old m dm ws2 i2 pa2 ib2 pb2 m2 c2 (c:data_to_word_config).
     word_gen_gc_move_roots c (FILTER isWord ws,i:A word,pa,ib,pb,old,m,dm) =
       (ws2,i2,pa2,ib2,pb2,m2,c2) /\
     ALL loc_ok ws ==>
     word_gen_gc_move_roots c (ws,i,pa,ib,pb,old,m,dm) =
       (loc_merge ws ws2,i2,pa2,ib2,pb2,m2,c2)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[FILTER; word_gen_gc_move_roots_def; loc_merge_def; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[loc_merge_def];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL] THEN CASES_ON `h:A word_loc` THEN
  REWRITE_TAC[FILTER; isWord_def; loc_ok_def] THEN STRIP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[word_gen_gc_move_roots_def]) THEN
    REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN GCP3AUX_SPLIT_TAC THEN
    FIRST_X_ASSUM DRULE THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[word_gen_gc_move_roots_def] THEN GCP3AUX_ASM_CASE_TAC THEN
    REWRITE_TAC[loc_merge_def];
    FIRST_X_ASSUM DRULE THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[word_gen_gc_move_roots_def; word_gen_gc_move_def] THEN GCP3AUX_ASM_CASE_TAC THEN
    REWRITE_TAC[loc_merge_def]]);;

(* HOL4 line 6325 (allow_rebind: rebinds the name of the theorem of line    *)
(* 6211)                                                                    *)
let word_gen_gc_partial_move_roots_IMP_FILTER = prove
 (`!ws i pa old m dm gs rs ws2 i2 pa2 m2 c2 (c:data_to_word_config).
     word_gen_gc_partial_move_roots c (FILTER isWord ws,i:A word,pa,old,m,dm,gs,rs) =
       (ws2,i2,pa2,m2,c2) /\
     ALL loc_ok ws ==>
     word_gen_gc_partial_move_roots c (ws,i,pa,old,m,dm,gs,rs) =
       (loc_merge ws ws2,i2,pa2,m2,c2)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[FILTER; word_gen_gc_partial_move_roots_def; loc_merge_def; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[loc_merge_def];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL] THEN CASES_ON `h:A word_loc` THEN
  REWRITE_TAC[FILTER; isWord_def; loc_ok_def] THEN STRIP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[word_gen_gc_partial_move_roots_def]) THEN
    REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN GCP3AUX_SPLIT_TAC THEN
    FIRST_X_ASSUM DRULE THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[word_gen_gc_partial_move_roots_def] THEN GCP3AUX_ASM_CASE_TAC THEN
    REWRITE_TAC[loc_merge_def];
    FIRST_X_ASSUM DRULE THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[word_gen_gc_partial_move_roots_def; word_gen_gc_partial_move_def] THEN
    GCP3AUX_ASM_CASE_TAC THEN REWRITE_TAC[loc_merge_def]]);;

(* HOL4 line 6343 *)
let loc_merge_FILTER_isWord = prove
 (`!xs:(A word_loc)list. loc_merge xs (FILTER isWord xs) = xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; loc_merge_def] THEN
  CASES_ON `h:A word_loc` THEN ASM_REWRITE_TAC[isWord_def; loc_merge_def]);;

(* GCP3AUX: moving the roots CONS g xs from the moves of CONS g (FILTER      *)
(* isWord xs) (the root g, the global, is moved as it is)                   *)
let GCP3AUX_word_gc_move_roots_CONS_MERGE = prove
 (`!g xs i pa old m dm rs i2 pa2 m2 c2 (c:data_to_word_config).
     word_gc_move_roots c (CONS g (FILTER isWord xs),i:A word,pa,old,m,dm) =
       (rs,i2,pa2,m2,c2) /\
     ALL loc_ok xs ==>
     word_gc_move_roots c (CONS g xs,i,pa,old,m,dm) =
       (CONS (HD rs) (loc_merge xs (TL rs)),i2,pa2,m2,c2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_gc_move_roots_def] THEN
  REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN STRIP_TAC THEN
  REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN GCP3AUX_SPLIT_TAC THEN
  DRULE_ALL word_gc_move_roots_IMP_FILTER THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[HD; TL]);;

(* GCP3AUX: the same for the generational collector *)
let GCP3AUX_word_gen_gc_move_roots_CONS_MERGE = prove
 (`!g xs i pa ib pb old m dm rs i2 pa2 ib2 pb2 m2 c2 (c:data_to_word_config).
     word_gen_gc_move_roots c (CONS g (FILTER isWord xs),i:A word,pa,ib,pb,old,m,dm) =
       (rs,i2,pa2,ib2,pb2,m2,c2) /\
     ALL loc_ok xs ==>
     word_gen_gc_move_roots c (CONS g xs,i,pa,ib,pb,old,m,dm) =
       (CONS (HD rs) (loc_merge xs (TL rs)),i2,pa2,ib2,pb2,m2,c2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_gen_gc_move_roots_def] THEN
  REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN STRIP_TAC THEN
  REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN GCP3AUX_SPLIT_TAC THEN
  DRULE_ALL word_gen_gc_move_roots_IMP_FILTER THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[HD; TL]);;

(* GCP3AUX: the same for the partial generational collector *)
let GCP3AUX_word_gen_gc_partial_move_roots_CONS_MERGE = prove
 (`!g xs i pa old m dm gs rs' rs i2 pa2 m2 c2 (c:data_to_word_config).
     word_gen_gc_partial_move_roots c
       (CONS g (FILTER isWord xs),i:A word,pa,old,m,dm,gs,rs') =
       (rs,i2,pa2,m2,c2) /\
     ALL loc_ok xs ==>
     word_gen_gc_partial_move_roots c (CONS g xs,i,pa,old,m,dm,gs,rs') =
       (CONS (HD rs) (loc_merge xs (TL rs)),i2,pa2,m2,c2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_gen_gc_partial_move_roots_def] THEN
  REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN STRIP_TAC THEN
  REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN GCP3AUX_SPLIT_TAC THEN
  DRULE_ALL word_gen_gc_partial_move_roots_IMP_FILTER THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[HD; TL]);;

(* HOL4 line 6349 *)
let word_gc_fun_loc_merge = prove
 (`!c xs (m:A word->A word_loc) dm s ys m1 s1.
     word_gc_fun c (FILTER isWord xs,m,dm,s) = SOME (ys,m1,s1) /\
     ALL loc_ok xs ==>
     word_gc_fun c (xs,m,dm,s) = SOME (loc_merge xs ys,m1,s1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_gc_fun_def; word_full_gc_def; word_gen_gc_def; word_gen_gc_partial_def;
              word_gen_gc_partial_full_def] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CASES_ON `data_to_word_config_gc_kind c` THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN GCP3AUX_SPLIT_TAC THENL
   [ALL_TAC;
    DRULE_ALL GCP3AUX_word_gc_move_roots_CONS_MERGE THEN DISCH_TAC;
    DRULE_ALL GCP3AUX_word_gen_gc_move_roots_CONS_MERGE THEN DISCH_TAC THEN
    DRULE_ALL GCP3AUX_word_gen_gc_partial_move_roots_CONS_MERGE THEN DISCH_TAC] THEN
  GCP3AUX_ASM_CASE_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ]) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN RVEQ_TAC THEN
  REWRITE_TAC[loc_merge_FILTER_isWord]);;

(* HOL4 line 6390 *)
let word_gc_fun_IMP = prove
 (`!c xs (m:A word->A word_loc) dm s ys m1 s1.
     word_gc_fun c (xs,m,dm,s) = SOME (ys,m1,s1) ==>
     FLOOKUP s1 AllocSize = FLOOKUP s AllocSize /\
     FLOOKUP s1 Handler = FLOOKUP s Handler /\
     FLOOKUP s1 CodeBuffer = FLOOKUP s CodeBuffer /\
     FLOOKUP s1 CodeBufferEnd = FLOOKUP s CodeBufferEnd /\
     FLOOKUP s1 BitmapBuffer = FLOOKUP s BitmapBuffer /\
     FLOOKUP s1 BitmapBufferEnd = FLOOKUP s BitmapBufferEnd /\
     FLOOKUP s1 (Temp (word 29)) = FLOOKUP s (Temp (word 29)) /\
     FLOOKUP s1 HeapLength = FLOOKUP s HeapLength /\
     Globals IN FDOM s1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_gc_fun_def] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CASES_ON `data_to_word_config_gc_kind c` THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN GCP3AUX_SPLIT_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_gc_fun_assum_def; INSERT_SUBSET]) THEN
  ASM SIMP[FUPDATE_LIST_THM; FLOOKUP_UPDATE; FDOM_FUPDATE; IN_INSERT]);;

(* HOL4 line 6409 *)
let gc_fun_const_ok_word_gc_fun = prove
 (`!c. gc_fun_const_ok (word_gc_fun c:(A word_loc)list#(A word->A word_loc)#
                        (A word->bool)#(store_name,A word_loc)fmap ->
                        ((A word_loc)list#(A word->A word_loc)#
                         (store_name,A word_loc)fmap)option)`,
  GEN_TAC THEN REWRITE_TAC[gc_fun_const_ok_def; FORALL_PAIR_THM; FST] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP word_gc_IMP_EVERY2) THEN
  MATCH_MP_TAC MONO_ALL2 THEN MESON_TAC[]);;

(* GCP3AUX: an iterated update that does not touch k, of a map with k in   *)
(* its domain, is the update of the map without k, updated at k            *)
let GCP3AUX_FUPDATE_LIST_DOMSUB = prove
 (`!(L:(A#B)list) s k.
     k IN FDOM s /\ ~MEM k (MAP FST L) ==>
     s |++ L = ((s \\ k) |++ L) |+ (k,FAPPLY s k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fmap_eq_flookup; FLOOKUP_UPDATE; FLOOKUP_FUPDATE_LIST] THEN
  X_GEN_TAC `x:A` THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    SUBGOAL_THEN `ALOOKUP (REVERSE (L:(A#B)list)) k = NONE` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[ALOOKUP_NONE; GSYM MAP_REVERSE; MEM_REVERSE]; ALL_TAC] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[FLOOKUP_DEF];
    CASES_ON `ALOOKUP (REVERSE (L:(A#B)list)) x` THEN CASE_REWRITE_TAC[] THEN
    ASM_MESON_TAC[DOMSUB_FLOOKUP_NEQ]]);;

(* GCP3AUX: the assumption of the collector does not look at the handler *)
let GCP3AUX_word_gc_fun_assum_domsub = prove
 (`!c (s:(store_name,A word_loc)fmap).
     word_gc_fun_assum c (s \\ Handler) <=> word_gc_fun_assum c s`,
  REWRITE_TAC[word_gc_fun_assum_def; INSERT_SUBSET; EMPTY_SUBSET; FDOM_DOMSUB; IN_DELETE] THEN
  SIMP[DOMSUB_FAPPLY_THM]);;

(* GCP3AUX: nor does the test for a partial collection *)
let GCP3AUX_word_gen_gc_can_do_partial_domsub = prove
 (`!(gen_sizes:num list) (s:(store_name,A word_loc)fmap).
     word_gen_gc_can_do_partial gen_sizes (s \\ Handler) <=>
     word_gen_gc_can_do_partial gen_sizes s`,
  REWRITE_TAC[word_gen_gc_can_do_partial_def] THEN SIMP[DOMSUB_FAPPLY_THM]);;

(* HOL4 line 6419 *)
let gc_fun_ok_word_gc_fun = prove
 (`!c1. gc_fun_ok (word_gc_fun c1:(A word_loc)list#(A word->A word_loc)#
                   (A word->bool)#(store_name,A word_loc)fmap ->
                   ((A word_loc)list#(A word->A word_loc)#
                    (store_name,A word_loc)fmap)option)`,
  GEN_TAC THEN REWRITE_TAC[gc_fun_ok_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP word_gc_fun_LENGTH) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP word_gc_fun_IMP) THEN REWRITE_TAC[DOMSUB_FLOOKUP] THEN
  STRIP_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT]; ALL_TAC] THEN
  UNDISCH_TAC `word_gc_fun c1 (wl,m,d,s \\ Handler) =
               SOME (wl1,m1,s1:(store_name,A word_loc)fmap)` THEN
  REWRITE_TAC[word_gc_fun_def] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[GCP3AUX_word_gc_fun_assum_domsub; GCP3AUX_word_gen_gc_can_do_partial_domsub] THEN
  SIMP[DOMSUB_FAPPLY_THM] THEN
  CASES_ON `data_to_word_config_gc_kind c1` THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN GCP3AUX_SPLIT_TAC THEN
  GCP3AUX_ASM_CASE_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC GCP3AUX_FUPDATE_LIST_DOMSUB THEN ASM SIMP[MAP; MEM]);;

(* HOL4 line 6439 *)
let word_gc_fun_APPEND_IMP = prove
 (`!c xs ys (m:A word->A word_loc) dm s zs m1 s1.
     word_gc_fun c (APPEND xs ys,m,dm,s) = SOME (zs,m1,s1) ==>
     ?zs1 zs2. zs = APPEND zs1 zs2 /\ LENGTH xs = LENGTH zs1 /\ LENGTH ys = LENGTH zs2`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP word_gc_fun_LENGTH) THEN
  REWRITE_TAC[LENGTH_APPEND] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`TAKE (LENGTH (xs:(A word_loc)list)) (zs:(A word_loc)list)`;
                        `DROP (LENGTH (xs:(A word_loc)list)) (zs:(A word_loc)list)`] THEN
  REWRITE_TAC[TAKE_DROP; LENGTH_DROP] THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC LENGTH_TAKE THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

(* HOL4 line 6452 (allow_rebind; HOL4: Q.prove ... |> SPEC_ALL) *)
let IMP_loc_merge_APPEND = prove
 (`!ts qs xs (ys:(A word_loc)list).
     LENGTH (FILTER isWord ts) = LENGTH qs ==>
     loc_merge (APPEND ts xs) (APPEND qs ys) = APPEND (loc_merge ts qs) (loc_merge xs ys)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[FILTER; LENGTH; APPEND; loc_merge_def] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(SUBST1_TAC o REWRITE_RULE[LENGTH_EQ_NIL] o SYM) THEN REWRITE_TAC[APPEND];
    ALL_TAC] THEN
  CASES_ON `h:A word_loc` THEN REWRITE_TAC[FILTER; isWord_def; APPEND; loc_merge_def] THENL
   [X_GEN_TAC `qs:(A word_loc)list` THEN
    MP_TAC(ISPEC `qs:(A word_loc)list` list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `q:A word_loc` (X_CHOOSE_THEN `qs':(A word_loc)list` SUBST1_TAC))) THEN
    ASM_SIMP_TAC[LENGTH; NOT_SUC; SUC_INJ; APPEND; loc_merge_def];
    ASM_SIMP_TAC[APPEND]]);;

(* HOL4 line 6460 *)
let TAKE_DROP_loc_merge_APPEND = prove
 (`!(q:(B#A word_loc)list) xs ys.
     TAKE (LENGTH q) (APPEND (loc_merge (MAP SND q) xs) ys) = loc_merge (MAP SND q) xs /\
     DROP (LENGTH q) (APPEND (loc_merge (MAP SND q) xs) ys) = ys`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `LENGTH (q:(B#A word_loc)list) =
                LENGTH (loc_merge (MAP SND q) (xs:(A word_loc)list))` SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH_loc_merge; LENGTH_MAP];
    REWRITE_TAC[TAKE_LENGTH_APPEND; DROP_LENGTH_APPEND]]);;

(* HOL4 line 6468 *)
let loc_merge_NIL = prove
 (`!xs:(A word_loc)list. loc_merge xs [] = xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[loc_merge_def] THEN
  CASES_ON `h:A word_loc` THEN ASM_REWRITE_TAC[loc_merge_def]);;

(* HOL4 line 6474 *)
let loc_merge_APPEND = prove
 (`!xs1 xs2 (ys:(A word_loc)list).
     ?zs1 zs2. loc_merge (APPEND xs1 xs2) ys = APPEND zs1 zs2 /\
               LENGTH zs1 = LENGTH xs1 /\ LENGTH xs2 = LENGTH xs2 /\
               ?ts. loc_merge xs2 ts = zs2`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    MAP_EVERY EXISTS_TAC [`[]:(A word_loc)list`; `loc_merge (xs2:(A word_loc)list) ys`] THEN
    REWRITE_TAC[APPEND; LENGTH] THEN MESON_TAC[];
    ALL_TAC] THEN
  CASES_ON `h:A word_loc` THEN REPEAT GEN_TAC THEN REWRITE_TAC[APPEND] THENL
   [MP_TAC(ISPEC `ys:(A word_loc)list` list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `y:A word_loc` (X_CHOOSE_THEN `ys':(A word_loc)list` SUBST1_TAC))) THEN
    REWRITE_TAC[loc_merge_def] THENL
     [MAP_EVERY EXISTS_TAC [`CONS (wl_Word a) (t:(A word_loc)list)`; `xs2:(A word_loc)list`] THEN
      REWRITE_TAC[APPEND; LENGTH] THEN MESON_TAC[loc_merge_NIL];
      FIRST_X_ASSUM(X_CHOOSE_THEN `zs1:(A word_loc)list` (X_CHOOSE_THEN `zs2:(A word_loc)list`
        STRIP_ASSUME_TAC) o SPECL [`xs2:(A word_loc)list`; `ys':(A word_loc)list`]) THEN
      MAP_EVERY EXISTS_TAC [`CONS (y:A word_loc) zs1`; `zs2:(A word_loc)list`] THEN
      ASM_REWRITE_TAC[APPEND; LENGTH] THEN ASM_MESON_TAC[]];
    REWRITE_TAC[loc_merge_def] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `zs1:(A word_loc)list` (X_CHOOSE_THEN `zs2:(A word_loc)list`
      STRIP_ASSUME_TAC) o SPECL [`xs2:(A word_loc)list`; `ys:(A word_loc)list`]) THEN
    MAP_EVERY EXISTS_TAC [`CONS (wl_Loc a0 a1:A word_loc) zs1`; `zs2:(A word_loc)list`] THEN
    ASM_REWRITE_TAC[APPEND; LENGTH] THEN ASM_MESON_TAC[]]);;

(* HOL4 line 6492 *)
let EVERY2_loc_merge = prove
 (`!xs (ys:(A word_loc)list).
     ALL2 (\x y. (isWord y ==> isWord x) /\ (~isWord x ==> x = y)) xs (loc_merge xs ys)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[loc_merge_def; ALL2] THEN
  CASES_ON `h:A word_loc` THEN GEN_TAC THEN TRY(CASES_ON `ys:(A word_loc)list`) THEN
  ASM_REWRITE_TAC[loc_merge_def; ALL2; isWord_def] THEN
  MATCH_MP_TAC EVERY2_refl THEN MESON_TAC[]);;

(* GCP3AUX: the clause of dec_stack for a frame, for any list of values *)
let GCP3AUX_dec_stack_CONS = prove
 (CASE_TERM
  `!(ws:(A word_loc)list) n l0 l handler st.
     wl_dec_stack ws (CONS (StackFrame n l0 l handler) st) =
     if LENGTH ws < LENGTH l then NONE else
     match wl_dec_stack (DROP (LENGTH l) ws) st with
       NONE -> NONE
     | SOME s -> SOME (CONS (StackFrame n l0 (ZIP (MAP FST l) (TAKE (LENGTH l) ws)) handler) s)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wl_dec_stack_def]);;

(* HOL4 line 6501 *)
let dec_stack_loc_merge_enc_stack = prove
 (`!(xs:((A)stack_frame)list) ys.
     ?ss. wl_dec_stack (loc_merge (wl_enc_stack xs) ys) xs = SOME ss`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[wl_enc_stack_def; loc_merge_def; wl_dec_stack_def] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `h:(A)stack_frame` THEN REWRITE_TAC[wl_enc_stack_def; GCP3AUX_dec_stack_CONS] THEN
  X_GEN_TAC `ys:(A word_loc)list` THEN
  MP_TAC(ISPECL [`MAP SND (a2:(num#(A)word_loc)list)`; `wl_enc_stack (t:((A)stack_frame)list)`;
                 `ys:(A word_loc)list`] loc_merge_APPEND) THEN
  REWRITE_TAC[LENGTH_MAP] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `DROP (LENGTH (a2:(num#(A)word_loc)list)) (APPEND zs1 zs2) = zs2:(A word_loc)list`
    SUBST1_TAC THENL [ASM_MESON_TAC[DROP_LENGTH_APPEND]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; ARITH_RULE `~(a + b < a:num)`] THEN
  EXPAND_TAC "zs2" THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `ss:((A)stack_frame)list` SUBST1_TAC o
    SPEC `ts:(A word_loc)list`) THEN
  CASE_REWRITE_TAC[option_INJ] THEN MESON_TAC[]);;

(* HOL4 line 6517 *)
let ALOOKUP_ZIP = prove
 (`!l zs1 q r.
     ALOOKUP l (0:num) = SOME (wl_Loc q r:A word_loc) /\
     ALL2 (\x y. (isWord y ==> isWord x) /\ (~isWord x ==> x = y)) (MAP SND l) zs1 ==>
     ALOOKUP (ZIP (MAP FST l) zs1) 0 = SOME (wl_Loc q r)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_def; option_DISTINCT] THEN
  CASES_ON `h:num#A word_loc` THEN
  X_GEN_TAC `zs1:(A word_loc)list` THEN
  MP_TAC(ISPEC `zs1:(A word_loc)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `z:A word_loc` (X_CHOOSE_THEN `zs:(A word_loc)list` SUBST1_TAC))) THEN
  REWRITE_TAC[MAP; ALL2; ZIP; ALOOKUP_def; FST; SND; HD; TL] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[option_INJ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[isWord_def]) THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* GCP3AUX: membership in the domain of fromAList *)
let GCP3AUX_IS_SOME_lookup_fromAList = prove
 (`!k (vs:(num#A)list). IS_SOME (lookup k (fromAList vs)) <=> MEM k (MAP FST vs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_fromAList] THEN
  CASES_ON `ALOOKUP (vs:(num#A)list) k` THEN REWRITE_TAC[IS_SOME_DEF] THEN
  ASM_MESON_TAC[ALOOKUP_NONE; option_DISTINCT]);;

(* GCP3AUX: a property of the keys of a list of pairs *)
let GCP3AUX_ALL_FST = prove
 (`!(P:A->bool) (vs:(A#B)list). ALL (\(x1,x2). P x1) vs <=> ALL P (MAP FST vs)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; MAP] THEN
  CASES_ON `h:A#B` THEN REWRITE_TAC[FST] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[]);;

(* GCP3AUX: stack_rel looks only at the keys of the variables of a frame *)
let GCP3AUX_stack_rel_ZIP = prove
 (`!x n ws (vs:(num#A word_loc)list) zs h.
     LENGTH zs = LENGTH vs ==>
     (data_to_word_gcProof_stack_rel x (StackFrame n ws (ZIP (MAP FST vs) zs) h) <=>
      data_to_word_gcProof_stack_rel x (StackFrame n ws vs h))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `MAP FST (ZIP (MAP FST (vs:(num#A word_loc)list)) (zs:(A word_loc)list)) =
                MAP FST vs` ASSUME_TAC THENL
   [SUBGOAL_THEN `LENGTH (MAP FST (vs:(num#A word_loc)list)) = LENGTH (zs:(A word_loc)list)`
      (fun th -> REWRITE_TAC[MATCH_MP MAP_ZIP th]) THEN ASM_REWRITE_TAC[LENGTH_MAP];
    ALL_TAC] THEN
  SPEC_TAC(`h:(num#num#num)option`,`h:(num#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  CASES_ON `x:stack` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_stack_rel_def; GCP3AUX_ALL_FST;
              GCP3AUX_IS_SOME_lookup_fromAList] THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 6528 *)
let stack_rel_dec_stack_IMP_stack_rel = prove
 (`!(xs:((A)stack_frame)list) ys ts stack locs.
     ALL2 data_to_word_gcProof_stack_rel ts xs /\ ALL2 contains_loc xs locs /\
     wl_dec_stack (loc_merge (wl_enc_stack xs) ys) xs = SOME stack ==>
     ALL2 data_to_word_gcProof_stack_rel ts stack /\ ALL2 contains_loc stack locs`,
  SUBGOAL_THEN
   `!ts (xs:((A)stack_frame)list) ys stack locs.
      ALL2 data_to_word_gcProof_stack_rel ts xs /\ ALL2 contains_loc xs locs /\
      wl_dec_stack (loc_merge (wl_enc_stack xs) ys) xs = SOME stack ==>
      ALL2 data_to_word_gcProof_stack_rel ts stack /\ ALL2 contains_loc stack locs`
    (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THEN X_GEN_TAC `xs:((A)stack_frame)list` THEN
  MP_TAC(ISPEC `xs:((A)stack_frame)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `x:(A)stack_frame` (X_CHOOSE_THEN `xs':((A)stack_frame)list` SUBST1_TAC))) THEN
  REWRITE_TAC[ALL2] THEN REPEAT GEN_TAC THENL
   [MP_TAC(ISPEC `locs:(num#num)list` list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `lc:num#num` (X_CHOOSE_THEN `locs':(num#num)list` SUBST1_TAC))) THEN
    REWRITE_TAC[ALL2; wl_enc_stack_def; loc_merge_def; wl_dec_stack_def; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[ALL2];
    ALL_TAC] THEN
  MP_TAC(ISPEC `locs:(num#num)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `lc:num#num` (X_CHOOSE_THEN `locs':(num#num)list` SUBST1_TAC))) THEN
  REWRITE_TAC[ALL2] THEN
  CASES_ON `x:(A)stack_frame` THEN REWRITE_TAC[wl_enc_stack_def; GCP3AUX_dec_stack_CONS] THEN
  MP_TAC(ISPECL [`MAP SND (a2:(num#(A)word_loc)list)`; `wl_enc_stack (xs':((A)stack_frame)list)`;
                 `ys:(A word_loc)list`] loc_merge_APPEND) THEN
  REWRITE_TAC[LENGTH_MAP] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `DROP (LENGTH (a2:(num#(A)word_loc)list)) (APPEND zs1 zs2) = zs2:(A word_loc)list /\
                TAKE (LENGTH (a2:(num#(A)word_loc)list)) (APPEND zs1 zs2) = zs1`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[DROP_LENGTH_APPEND; TAKE_LENGTH_APPEND]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; ARITH_RULE `~(a + b < a:num)`] THEN
  EXPAND_TAC "zs2" THEN
  MP_TAC(ISPEC `wl_dec_stack (loc_merge (wl_enc_stack (xs':((A)stack_frame)list)) ts) xs'`
           (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `ss:((A)stack_frame)list` (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`xs':((A)stack_frame)list`; `ts:(A word_loc)list`;
                                `ss:((A)stack_frame)list`; `locs':(num#num)list`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ALL2] THEN
  ASM_SIMP_TAC[GCP3AUX_stack_rel_ZIP] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`lc:num#num`,`lc:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM; contains_loc_def] THEN
  MESON_TAC[]);;

(* HOL4 line 6558 *)
let join_env_NIL = prove
 (`!s:A spt. join_env s ([]:(num#B)list) = []`,
  REWRITE_TAC[join_env_def; FILTER; MAP]);;

(* HOL4 line 6564 *)
let join_env_CONS = prove
 (`!(s:A spt) n (v:B) xs.
     join_env s (CONS (n,v) xs) =
     if ~(n = 0) /\ EVEN n then
       CONS (THE (lookup ((n - 2) DIV 2) s),v) (join_env s xs)
     else join_env s xs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[join_env_def; FILTER] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN COND_CASES_TAC THEN
  REWRITE_TAC[MAP] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

(* GCP3AUX: the values of join_env when every key is kept *)
let GCP3AUX_MAP_SND_join_env = prove
 (`!(vs:(num#B)list) (env:A spt).
     ALL (\(x1,x2). ~(x1 = 0) /\ EVEN x1) vs ==> MAP SND (join_env env vs) = MAP SND vs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[join_env_NIL; MAP; ALL] THEN
  CASES_ON `h:num#B` THEN REWRITE_TAC[join_env_CONS] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN SIMP_TAC[MAP] THEN ASM_MESON_TAC[]);;

(* HOL4 line 6573 *)
let FILTER_enc_stack_lemma = prove
 (`!xs (ys:((A)stack_frame)list).
     ALL2 data_to_word_gcProof_stack_rel xs ys ==>
     FILTER isWord (MAP SND (data_to_word_gcProof_flat xs ys)) = FILTER isWord (wl_enc_stack ys)`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `ys:((A)stack_frame)list` THEN
  MP_TAC(ISPEC `ys:((A)stack_frame)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `y:(A)stack_frame` (X_CHOOSE_THEN `ys':((A)stack_frame)list` SUBST1_TAC))) THEN
  REWRITE_TAC[ALL2; flat_def; wl_enc_stack_def; MAP; FILTER] THEN
  CASES_ON `h:stack` THEN CASES_ON `y:(A)stack_frame` THEN
  SPEC_TAC(`a3:(num#num#num)option`,`a3:(num#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_stack_rel_def; flat_def; wl_enc_stack_def] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[MAP_APPEND; FILTER_APPEND; GCP3AUX_MAP_SND_join_env]);;

(* HOL4 line 6590 *)
let stack_rel_simp = prove
 (`!i s n (y:(A)stack_frame).
     (data_to_word_gcProof_stack_rel (data_Env i s) y <=>
      ?rets vs. data_to_word_gcProof_stack_rel (data_Env i s) y /\
                (y = StackFrame i rets vs NONE)) /\
     (data_to_word_gcProof_stack_rel (Exc i s n) y <=>
      ?rets vs x1 x2 x3. data_to_word_gcProof_stack_rel (Exc i s n) y /\
                         (y = StackFrame i rets vs (SOME (x1,x2,x3))))`,
  REPEAT GEN_TAC THEN CASES_ON `y:(A)stack_frame` THEN
  SPEC_TAC(`a3:(num#num#num)option`,`a3:(num#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_stack_rel_def; injectivity "stack_frame";
              injectivity "option"; PAIR_EQ; distinctness "option"] THEN
  MESON_TAC[]);;

(* HOL4 line 6604 *)
let join_env_EQ_ZIP = prove
 (`!vs (s:B spt) (zs1:(A word_loc)list).
     ALL (\(x1,x2). ~(x1 = 0) /\ EVEN x1) vs /\
     LENGTH (join_env s vs) = LENGTH zs1 /\
     ALL2 (\x y. isWord x = isWord y /\ (~isWord x ==> x = y))
       (MAP SND (join_env s vs)) zs1 ==>
     join_env s (ZIP (MAP FST vs) (loc_merge (MAP SND vs) (FILTER isWord zs1))) =
     ZIP (MAP FST (join_env s vs)) zs1`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `s:B spt` THEN X_GEN_TAC `zs1:(A word_loc)list` THEN
  MP_TAC(ISPEC `zs1:(A word_loc)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `z:A word_loc` (X_CHOOSE_THEN `zs:(A word_loc)list` SUBST1_TAC))) THEN
  REWRITE_TAC[join_env_NIL; MAP; FILTER; loc_merge_def; ZIP; LENGTH; NOT_SUC] THEN
  CASES_ON `h:num#A word_loc` THEN REWRITE_TAC[ALL; join_env_CONS; MAP; FST; SND] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_CASES_TAC `~(x = 0) /\ EVEN x` THEN ASM_REWRITE_TAC[LENGTH; MAP; ALL2; NOT_SUC; SUC_INJ] THEN
  STRIP_TAC THEN CASES_ON `y:A word_loc` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[isWord_def]) THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[isWord_def; loc_merge_def; ZIP; HD; TL; join_env_CONS] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:B spt`; `zs:(A word_loc)list`]) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* GCP3AUX: lists that agree on which elements are words have as many words *)
let GCP3AUX_ALL2_isWord_FILTER_LENGTH = prove
 (`!(l1:(A word_loc)list) l2.
     ALL2 (\x y. (isWord x = isWord y) /\ (~isWord x ==> x = y)) l1 l2 ==>
     LENGTH (FILTER isWord l1) = LENGTH (FILTER isWord l2)`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `l2:(A word_loc)list` THEN
  MP_TAC(ISPEC `l2:(A word_loc)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `z:A word_loc` (X_CHOOSE_THEN `zs:(A word_loc)list` SUBST1_TAC))) THEN
  REWRITE_TAC[ALL2; FILTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `zs:(A word_loc)list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH]);;

(* HOL4 line 6622 *)
let LENGTH_MAP_SND_join_env_IMP = prove
 (`!vs (zs1:(A word_loc)list) (s:B spt).
     ALL2 (\x y. (isWord x = isWord y) /\ (~isWord x ==> x = y))
       (MAP SND (join_env s vs)) zs1 /\
     ALL (\(x1,x2). ~(x1 = 0) /\ EVEN x1) vs /\
     LENGTH (join_env s vs) = LENGTH zs1 ==>
     LENGTH (FILTER isWord (MAP SND vs)) = LENGTH (FILTER isWord zs1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`vs:(num#A word_loc)list`; `s:B spt`] GCP3AUX_MAP_SND_join_env) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  MATCH_MP_TAC GCP3AUX_ALL2_isWord_FILTER_LENGTH THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 6639 *)
let lemma1 = prove
 (`!(y1:B) y2 (x1:A) x2 (f:A->B->C). (y1 = y2) /\ (x1 = x2) ==> (f x1 y1 = f x2 y2)`,
  SIMP_TAC[]);;

(* GCP3AUX: the frame case of word_gc_fun_EL_lemma *)
let GCP3AUX_word_gc_fun_EL_frame = prove
 (`!t (env:data_v spt) vs vs' n0 n1 rets rets' (h:(num#num#num)option) h' ys' stack'
    (stack1:(A word_loc)list).
     (!ys stack1 stack:((A)stack_frame)list.
        ALL2 data_to_word_gcProof_stack_rel t stack /\
        ALL2 (\x y. isWord x = isWord y /\ (~isWord x ==> x = y))
          (MAP SND (data_to_word_gcProof_flat t ys)) stack1 /\
        wl_dec_stack (loc_merge (wl_enc_stack ys) (FILTER isWord stack1)) ys = SOME stack /\
        ALL2 data_to_word_gcProof_stack_rel t ys ==>
        data_to_word_gcProof_flat t stack =
        ZIP (MAP FST (data_to_word_gcProof_flat t ys)) stack1) /\
     ALL (\(x1,x2). ~(x1 = 0) /\ EVEN x1) vs /\
     ALL2 (\x y. isWord x = isWord y /\ (~isWord x ==> x = y))
       (MAP SND (APPEND (join_env env vs) (data_to_word_gcProof_flat t ys'))) stack1 /\
     wl_dec_stack (loc_merge (APPEND (MAP SND vs) (wl_enc_stack ys')) (FILTER isWord stack1))
       (CONS (StackFrame n0 rets vs h) ys') =
       SOME (CONS (StackFrame n1 rets' vs' h') stack') /\
     ALL2 data_to_word_gcProof_stack_rel t stack' /\
     ALL2 data_to_word_gcProof_stack_rel t ys' ==>
     APPEND (join_env env vs') (data_to_word_gcProof_flat t stack') =
     ZIP (MAP FST (APPEND (join_env env vs) (data_to_word_gcProof_flat t ys'))) stack1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP EVERY2_APPEND_IMP o REWRITE_RULE[MAP_APPEND] o
    check (fun th -> not (is_forall (concl th)) &&
                     free_in `stack1:(A word_loc)list` (concl th) &&
                     not (is_eq (concl th)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `zs1:(A word_loc)list` (X_CHOOSE_THEN `zs2:(A word_loc)list`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `LENGTH (join_env (env:data_v spt) (vs:(num#A word_loc)list)) = LENGTH (zs1:(A word_loc)list) /\
                LENGTH (data_to_word_gcProof_flat t (ys':((A)stack_frame)list)) =
                LENGTH (zs2:(A word_loc)list)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_REL_LENGTH; LENGTH_MAP]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (FILTER isWord (MAP SND (vs:(num#A word_loc)list))) =
                LENGTH (FILTER isWord (zs1:(A word_loc)list))` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`vs:(num#A word_loc)list`; `zs1:(A word_loc)list`; `env:data_v spt`]
      LENGTH_MAP_SND_join_env_IMP) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `wl_dec_stack
      (loc_merge (APPEND (MAP SND (vs:(num#A word_loc)list)) (wl_enc_stack ys'))
      (FILTER isWord (APPEND zs1 zs2)))
      (CONS (StackFrame n0 rets vs h) ys') =
      SOME (CONS (StackFrame n1 rets' vs' h') stack')` THEN
  REWRITE_TAC[FILTER_APPEND] THEN ASM_SIMP_TAC[IMP_loc_merge_APPEND] THEN
  REWRITE_TAC[GCP3AUX_dec_stack_CONS; TAKE_DROP_loc_merge_APPEND] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_loc_merge; LENGTH_MAP; ARITH_RULE `~(a + b < a:num)`] THEN
  MP_TAC(ISPEC `wl_dec_stack (loc_merge (wl_enc_stack (ys':((A)stack_frame)list))
                  (FILTER isWord (zs2:(A word_loc)list))) ys'` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `ss:((A)stack_frame)list` (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ; injectivity "list";
                   injectivity "stack_frame"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[MAP_APPEND] THEN
  SUBGOAL_THEN `LENGTH (MAP FST (join_env (env:data_v spt) (vs:(num#A word_loc)list))) = LENGTH (zs1:(A word_loc)list) /\
                LENGTH (MAP FST (data_to_word_gcProof_flat t (ys':((A)stack_frame)list))) =
                LENGTH (zs2:(A word_loc)list)`
    (fun th -> REWRITE_TAC[GSYM(MATCH_MP ZIP_APPEND th)]) THENL
   [ASM_REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC join_env_EQ_ZIP THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 6645 (allow_rebind; HOL4: Q.prove ... |> SPEC_ALL) *)
let word_gc_fun_EL_lemma = prove
 (`!xs ys stack1 stack:((A)stack_frame)list.
     ALL2 data_to_word_gcProof_stack_rel xs stack /\
     ALL2 (\x y. isWord x = isWord y /\ (~isWord x ==> x = y))
       (MAP SND (data_to_word_gcProof_flat xs ys)) stack1 /\
     wl_dec_stack (loc_merge (wl_enc_stack ys) (FILTER isWord stack1)) ys = SOME stack /\
     ALL2 data_to_word_gcProof_stack_rel xs ys ==>
     (data_to_word_gcProof_flat xs stack = ZIP (MAP FST (data_to_word_gcProof_flat xs ys)) stack1)`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `ys:((A)stack_frame)list` THEN
  MP_TAC(ISPEC `ys:((A)stack_frame)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `y:(A)stack_frame` (X_CHOOSE_THEN `ys':((A)stack_frame)list` SUBST1_TAC))) THEN
  X_GEN_TAC `stack1:(A word_loc)list` THEN X_GEN_TAC `stack:((A)stack_frame)list` THEN
  MP_TAC(ISPEC `stack:((A)stack_frame)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `s1:(A)stack_frame` (X_CHOOSE_THEN `stack':((A)stack_frame)list` SUBST1_TAC))) THEN
  REWRITE_TAC[ALL2; flat_def; MAP; ZIP_DEF] THEN
  CASES_ON `h:stack` THEN CASES_ON `y:(A)stack_frame` THEN CASES_ON `s1:(A)stack_frame` THEN
  SPEC_TAC(`a3:(num#num#num)option`,`a3:(num#num#num)option`) THEN
  SPEC_TAC(`a3':(num#num#num)option`,`a3':(num#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_stack_rel_def; flat_def; wl_enc_stack_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DRULE_ALL GCP3AUX_word_gc_fun_EL_frame THEN REWRITE_TAC[]);;

(* HOL4 line 6672 *)
let word_ml_inv_cons_snoc = prove
 (`!heap be a sp sp1 gens limit ts c refs (x:data_v#A word_loc) xs.
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs (CONS x xs) ==>
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs (APPEND xs [x])`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC word_ml_inv_rearrange THEN
  REWRITE_TAC[MEM_APPEND; MEM] THEN MESON_TAC[]);;

(* HOL4 line 6680 *)
let size_of_cons = prove
 (CASE_TERM
  `!lims x xs refs (seen:num_set).
     size_of lims (CONS x xs) refs seen =
     let (n1,refs1,seen1) = size_of lims xs refs seen in
     let (n2,refs2,seen2) = size_of lims [x] refs1 seen1 in
       (n1 + n2,refs2,seen2)`,
  REPEAT GEN_TAC THEN CASES_ON `xs:data_v list` THEN REWRITE_TAC[size_of_def] THEN
  CASE_REWRITE_TAC[ADD_CLAUSES] THEN REPEAT GCP3AUX_PAIRARG_TAC THEN
  REWRITE_TAC[ADD_CLAUSES]);;

(* HOL4 line 6690 *)
let size_of_global_to_vs = prove
 (`!lims x refs seen xs.
     size_of lims (APPEND xs (global_to_vs x)) refs seen =
     size_of lims (APPEND xs [the_global x]) refs seen`,
  REPEAT GEN_TAC THEN SPEC_TAC(`xs:data_v list`,`xs:data_v list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND] THENL
   [CASES_ON `x:num option` THEN
    REWRITE_TAC[global_to_vs_def; the_global_def; the_def; OPTION_MAP_DEF; size_of_def] THEN
    REWRITE_TAC[small_num_def] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[COND_ID];
    ONCE_REWRITE_TAC[size_of_cons] THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 6699 *)
let toListA_mk = prove
 (`!(a:A list) t1 t2 x.
     toListA a (mk_BN t1 t2) = toListA a (BN t1 t2) /\
     toListA a (mk_BS t1 x t2) = toListA a (BS t1 x t2)`,
  REPEAT GEN_TAC THEN CASES_ON `t1:A spt` THEN CASES_ON `t2:A spt` THEN
  REWRITE_TAC[mk_BN_def; mk_BS_def; toListA_def]);;

(* GCP3AUX: toList of the tree constructors *)
let GCP3AUX_toList_clauses = prove
 (`toList (LN:A spt) = [] /\
   (!a:A. toList (LS a) = [a]) /\
   (!t1 t2:A spt. toList (BN t1 t2) = APPEND (toList t1) (toList t2)) /\
   (!t1 (a:A) t2. toList (BS t1 a t2) = APPEND (toList t1) (CONS a (toList t2))) /\
   (!t1 t2:A spt. toList (mk_BN t1 t2) = toList (BN t1 t2)) /\
   (!t1 (a:A) t2. toList (mk_BS t1 a t2) = toList (BS t1 a t2))`,
  REWRITE_TAC[toList_def; toListA_mk; toListA_def] THEN
  ONCE_REWRITE_TAC[toListA_append] THEN REWRITE_TAC[APPEND; GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[toListA_def; APPEND_NIL]);;

(* GCP3AUX: moving an element to the front is a permutation *)
let GCP3AUX_PERM_APPEND_CONS = prove
 (`!(x:A) l1 l2. PERM (APPEND l1 (CONS x l2)) (CONS x (APPEND l1 l2))`,
  REWRITE_TAC[PERM_FUN_APPEND_CONS; APPEND; PERM_REFL]);;

(* HOL4 line 6707 *)
let PERM_toList_delete = prove
 (`!k (s:A spt) x. lookup k s = SOME x ==> PERM (toList s) (CONS x (toList (delete k s)))`,
  MATCH_MP_TAC lookup_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[lookup_def; delete_def; option_DISTINCT] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GCP3AUX_toList_clauses; PERM_REFL];
    ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
    ASM_CASES_TAC `EVEN k` THEN ASM_REWRITE_TAC[GCP3AUX_toList_clauses] THEN
    DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 APPEND)] THEN MATCH_MP_TAC PERM_CONG THEN
      ASM_REWRITE_TAC[PERM_REFL];
      MATCH_MP_TAC PERM_TRANS THEN
      EXISTS_TAC `APPEND (toList (t1:A spt)) (CONS (x:A) (toList (delete ((k - 1) DIV 2) t2)))` THEN
      REWRITE_TAC[GCP3AUX_PERM_APPEND_CONS] THEN MATCH_MP_TAC PERM_CONG THEN
      ASM_REWRITE_TAC[PERM_REFL]];
    ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[option_INJ] THENL
     [X_GEN_TAC `x:A` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GCP3AUX_toList_clauses; GCP3AUX_PERM_APPEND_CONS];
      ALL_TAC] THEN
    ASM_CASES_TAC `EVEN k` THEN ASM_REWRITE_TAC[GCP3AUX_toList_clauses] THEN
    DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 APPEND)] THEN MATCH_MP_TAC PERM_CONG THEN
      ASM_REWRITE_TAC[PERM_REFL];
      MATCH_MP_TAC PERM_TRANS THEN
      EXISTS_TAC `APPEND (toList (t1:A spt)) (CONS (a:A) (CONS (x:A)
                    (toList (delete ((k - 1) DIV 2) t2))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PERM_CONG THEN ASM_SIMP_TAC[PERM_REFL; PERM_MONO]; ALL_TAC] THEN
      MATCH_MP_TAC PERM_TRANS THEN
      EXISTS_TAC `APPEND (toList (t1:A spt)) (CONS (x:A) (CONS (a:A)
                    (toList (delete ((k - 1) DIV 2) t2))))` THEN
      REWRITE_TAC[GCP3AUX_PERM_APPEND_CONS] THEN MATCH_MP_TAC PERM_CONG THEN
      REWRITE_TAC[PERM_REFL; PERM_SWAP_AT_FRONT]]]);;

(* GCP3AUX: a tree without elements has an empty toList *)
let GCP3AUX_toList_NIL = prove
 (`!(s:A spt). (!n. lookup n s = NONE) ==> toList s = []`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `toList (s:A spt)` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC
    (X_CHOOSE_THEN `h:A` (X_CHOOSE_THEN `t:A list` ASSUME_TAC))) THEN
  SUBGOAL_THEN `MEM (h:A) (toList (s:A spt))` MP_TAC THENL
   [ASM_REWRITE_TAC[MEM]; ASM_REWRITE_TAC[MEM_toList; option_DISTINCT]]);;

(* GCP3AUX: join_env ignores the deleted variable when its slot is not a key *)
let GCP3AUX_join_env_delete = prove
 (`!(l:(num#B)list) (s:A spt) k.
     ~MEM (adjust_var k) (MAP FST l) ==> join_env (delete k s) l = join_env s l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[join_env_NIL] THEN
  CASES_ON `h:num#B` THEN REWRITE_TAC[join_env_CONS; MAP; MEM; FST; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[injectivity "list"; PAIR_EQ; lookup_delete] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `x = adjust_var k` (fun th -> ASM_MESON_TAC[th]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC(GSYM IMP_adjust_var) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 6746 *)
let PERM_lookup_toList_lemma = prove
 (`!(l:(num#B)list) (s:A spt).
     (!n. IS_SOME (lookup n s) <=> IS_SOME (ALOOKUP l (adjust_var n))) /\
     ALL_DISTINCT (MAP FST l) ==>
     PERM (MAP FST
        (MAP (\(n,v). (THE (lookup ((n - 2) DIV 2) s),v))
           (FILTER (\(n,v). ~(n = 0) /\ EVEN n) l))) (toList s)`,
  REWRITE_TAC[GSYM join_env_def] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[join_env_NIL; MAP; ALOOKUP_def; IS_SOME_DEF] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `toList (s:A spt) = []` SUBST1_TAC THENL
     [MATCH_MP_TAC GCP3AUX_toList_NIL THEN X_GEN_TAC `n:num` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
      CASES_ON `lookup n (s:A spt)` THEN REWRITE_TAC[IS_SOME_DEF];
      REWRITE_TAC[PERM_REFL]];
    ALL_TAC] THEN
  CASES_ON `h:num#B` THEN X_GEN_TAC `s:A spt` THEN
  REWRITE_TAC[join_env_CONS; ALL_DISTINCT; MAP; FST; ALOOKUP_def] THEN
  ASM_CASES_TAC `~(x = 0) /\ EVEN x` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ABBREV_TAC `k = (x - 2) DIV 2` THEN
    SUBGOAL_THEN `adjust_var k = x` ASSUME_TAC THENL
     [EXPAND_TAC "k" THEN MATCH_MP_TAC IMP_adjust_var THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?a:A. lookup k (s:A spt) = SOME a` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `IS_SOME (lookup k (s:A spt))` MP_TAC THENL
       [ASM_REWRITE_TAC[IS_SOME_DEF]; ALL_TAC] THEN
      CASES_ON `lookup k (s:A spt)` THEN REWRITE_TAC[IS_SOME_DEF] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[MAP; FST; THE_DEF] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `delete k (s:A spt)`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[lookup_delete] THEN X_GEN_TAC `n:num` THEN COND_CASES_TAC THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN
        SUBGOAL_THEN `ALOOKUP (t:(num#B)list) x = NONE` (fun th -> REWRITE_TAC[th; IS_SOME_DEF]) THEN
        ASM_REWRITE_TAC[ALOOKUP_NONE];
        FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
        SUBGOAL_THEN `~(x = adjust_var n)` (fun th -> REWRITE_TAC[th]) THEN
        ASM_MESON_TAC[adjust_var_11]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GCP3AUX_join_env_delete] THEN DISCH_TAC THEN
    MATCH_MP_TAC PERM_TRANS THEN EXISTS_TAC `CONS (a:A) (toList (delete k (s:A spt)))` THEN
    ASM_SIMP_TAC[PERM_MONO] THEN ONCE_REWRITE_TAC[PERM_SYM] THEN
    MATCH_MP_TAC PERM_toList_delete THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    SUBGOAL_THEN `~(x = adjust_var n)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[EVEN_adjust_var; adjust_var_NEQ]]);;

(* HOL4 line 6804 *)
let flat_PERM_extract_stack = prove
 (`!xs (ys:((A)stack_frame)list).
     ALL2 data_to_word_gcProof_stack_rel xs ys ==>
     PERM (MAP FST (data_to_word_gcProof_flat xs ys)) (FLAT (MAP extract_stack xs))`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `ys:((A)stack_frame)list` THEN
  MP_TAC(ISPEC `ys:((A)stack_frame)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `y:(A)stack_frame` (X_CHOOSE_THEN `ys':((A)stack_frame)list` SUBST1_TAC))) THEN
  REWRITE_TAC[ALL2; flat_def; MAP; FLAT; PERM_REFL] THEN
  CASES_ON `h:stack` THEN CASES_ON `y:(A)stack_frame` THEN
  SPEC_TAC(`a3:(num#num#num)option`,`a3:(num#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_stack_rel_def; flat_def; extract_stack_def; MAP_APPEND] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC PERM_CONG THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[join_env_def] THEN MATCH_MP_TAC PERM_lookup_toList_lemma THEN
  ASM_REWRITE_TAC[GSYM lookup_fromAList]);;

(* HOL4 line 6822 *)
let ALL_DISTINCT_data_pointers = prove
 (`!heap:((A,B)heap_element)list. ALL_DISTINCT (data_pointers heap)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[data_pointers_def; ALL_DISTINCT] THEN
  CASES_ON `h:(A,B)heap_element` THEN REWRITE_TAC[data_pointers_def; ALL_DISTINCT] THEN
  REWRITE_TAC[MEM_MAP; el_length_def; NOT_EXISTS_THM; ARITH_RULE `~(0 = x + a + 1)`] THEN
  MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  SIMP_TAC[EQ_ADD_RCANCEL]);;

(* HOL4 line 6831 *)
let SUM_MAP_lookup_len_LESS_EQ = prove
 (`!p1 p2 (heap:((A,B)heap_element)list).
     set_of_list p1 SUBSET set_of_list p2 /\ ALL_DISTINCT p1 ==>
     SUM (MAP (lookup_len heap) p1) <= SUM (MAP (lookup_len heap) p2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; SUM; LE_0] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[set_of_list; INSERT_SUBSET; ALL_DISTINCT; IN_SET_OF_LIST] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> not (is_neg (concl th))) o
    REWRITE_RULE[MEM_APPEND_DECOMPOSE] o check (fun th -> concl th = `MEM (h:num) p2`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:num list` (X_CHOOSE_THEN `l2:num list` SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`APPEND l1 l2:num list`; `heap:((A,B)heap_element)list`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `set_of_list t SUBSET set_of_list (APPEND l1 (CONS (h:num) l2))` THEN
    UNDISCH_TAC `~MEM (h:num) t` THEN
    REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_APPEND; MEM] THEN MESON_TAC[];
    REWRITE_TAC[MAP_APPEND; SUM_APPEND; MAP; SUM] THEN ARITH_TAC]);;

(* GCP3AUX: membership in a translated set of numbers *)
let GCP3AUX_IN_IMAGE_ADD = prove
 (`!k s x. x IN IMAGE (\n. n + k) s <=> k <= x /\ (x - k) IN s`,
  REWRITE_TAC[IN_IMAGE] THEN REPEAT GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[ADD_SUB; LE_ADDR];
    STRIP_TAC THEN EXISTS_TAC `x - k:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* HOL4 line 6845 *)
let set_data_pointers = prove
 (`!heap:((A,B)heap_element)list.
     set_of_list (data_pointers heap) = {a | isSomeDataElement (heap_lookup a heap)}`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[data_pointers_def; heap_lookup_def; set_of_list; isSomeDataElement_def;
              EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; option_DISTINCT] THEN
  CASES_ON `h:(A,B)heap_element` THEN
  ASM_REWRITE_TAC[data_pointers_def; set_of_list; SET_OF_LIST_MAP; el_length_def;
                  IN_INSERT; GCP3AUX_IN_IMAGE_ADD; IN_ELIM_THM] THEN
  X_GEN_TAC `x:num` THEN ASM_CASES_TAC `x = 0` THEN
  ASM_REWRITE_TAC[option_INJ; injectivity "heap_element"; distinctness "heap_element";
                  isSomeDataElement_def; ARITH_RULE `~(a + 1 <= 0)`; UNWIND_THM1] THEN
  TRY COND_CASES_TAC THEN
  ASM_SIMP_TAC[option_DISTINCT; distinctness "option"; ARITH_RULE `x < n ==> ~(n <= x)`;
               ARITH_RULE `~(x < n) ==> n <= x`] THEN
  SIMP[]);;

(* HOL4 line 6857 *)
let traverse_heap_rules,traverse_heap_ind,traverse_heap_cases,traverse_heap_strongind =
  cake_inductive
  `(!(heap:((A,B)heap_element)list) p1.
      traverse_heap heap p1 [] p1) /\
   (!heap vs1 vs2 vars p1 p2 p3.
      traverse_heap heap p1 vs1 p2 /\
      traverse_heap heap p2 vs2 p3 /\
      set_of_list vars = set_of_list (APPEND vs1 vs2) ==>
      traverse_heap heap p1 vars p3) /\
   (!heap p1 d.
      traverse_heap heap p1 [gc_shared_Data d] p1) /\
   (!heap p1 n t.
      MEM n p1 ==>
      traverse_heap heap p1 [Pointer n t] p1) /\
   (!heap p1 n t p2 xs l d.
      heap_lookup n heap = SOME (DataElement xs l d) /\
      traverse_heap heap (CONS n p1) xs p2 ==>
      traverse_heap heap p1 [Pointer n t] p2)`;;

(* HOL4 line 6876 (local) *)
let size_of_Block = prove
 (CASE_TERM
  `!lims ts tag vs refs (seen:num_set).
     size_of lims [data_Block ts tag vs] refs seen =
     if vs = [] \/ IS_SOME (lookup ts seen) then (0,refs,seen)
     else let (n,refs',seen') = size_of lims vs refs (insert ts one seen) in
            (n + LENGTH vs + 1,refs',seen')`,
  REPEAT GEN_TAC THEN CASES_ON `vs:data_v list` THEN
  REWRITE_TAC[size_of_def; NOT_CONS_NIL]);;

(* HOL4 line 6885 *)
let LENGTH_n2mw_LE_bignum_digits = prove
 (`!n m. good_dimindex (:A) /\ n <= m ==>
         LENGTH ((n2mw n):(A word)list) <= bignum_digits (dimindex (:A) = 64) m`,
  MATCH_MP_TAC (INST_TYPE [`:A`,`:N`] n2mw_ind) THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[n2mw_def] THEN COND_CASES_TAC THEN REWRITE_TAC[LENGTH; LE_0] THEN
  ONCE_REWRITE_TAC[bignum_digits_def] THEN
  SUBGOAL_THEN `~(m = 0)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ARITH_RULE `SUC a <= 1 + b <=> a <= b`] THEN
  SUBGOAL_THEN `2 EXP (if dimindex (:A) = 64 then 64 else 32) = dimword (:A)` SUBST1_TAC THENL
   [REWRITE_TAC[dimword_def] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def]) THEN
    ASM_REWRITE_TAC[ARITH_EQ];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIV_MONO THEN
  ASM_REWRITE_TAC[dimword_def; EXP_EQ_0; ARITH_EQ]);;

(* gcp3aux: helper of soundness_size_of *)
let GCP3AUX_th_rules = CONJUNCTS traverse_heap_rules;;

(* gcp3aux: the base cases of soundness_size_of: no new heap pointers *)
let gcp3aux_sound_nil_tac : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[size_of_def; PAIR_EQ; PERM_NIL] THEN STRIP_TAC THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_NIL]) THEN RVEQ_TAC THEN
  EXISTS_TAC `p1:num list` THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; LE_REFL; el 0 GCP3AUX_th_rules];;

(* GCP3AUX: a pointer to a heap block without pointers is traversed in one step *)
let GCP3AUX_th_ptr_leaf = prove
 (`!(heap:((A,B)heap_element)list) ptr t p1 l d.
     heap_lookup ptr heap = SOME (DataElement [] l d) ==>
     traverse_heap heap p1 [Pointer ptr t] (CONS ptr p1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC (el 4 GCP3AUX_th_rules) THEN
  MAP_EVERY EXISTS_TAC [`[]:((A)heap_address)list`; `l:num`; `d:B`] THEN
  ASM_REWRITE_TAC[el 0 GCP3AUX_th_rules]);;

(* GCP3AUX: subsets of a list's elements stay subsets after a CONS *)
let GCP3AUX_SUBSET_CONS = prove
 (`!s x (p:A list). s SUBSET set_of_list p ==> s SUBSET set_of_list (CONS x p)`,
  REWRITE_TAC[set_of_list] THEN SET_TAC[]);;

(* gcp3aux: helper of soundness_size_of *)
let gcp3aux_sound_data_tac : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[size_of_def; PAIR_EQ; PERM_SING] THEN STRIP_TAC THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `v:(A word_loc)heap_address` (X_CHOOSE_THEN `vs:((A word_loc)heap_address)list`
    STRIP_ASSUME_TAC)) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[v_inv_def]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && lhs (concl th) = `v:(A word_loc)heap_address`)) THEN
  DISCH_THEN SUBST1_TAC THEN
  EXISTS_TAC `p1:num list` THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; LE_REFL; LE_ADDR; el 2 GCP3AUX_th_rules];;

(* gcp3aux: helper of soundness_size_of *)
let gcp3aux_sound_word64_tac : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[size_of_def; PAIR_EQ; PERM_SING] THEN STRIP_TAC THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `v:(A word_loc)heap_address` (X_CHOOSE_THEN `vs:((A word_loc)heap_address)list`
    STRIP_ASSUME_TAC)) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[v_inv_def]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `ptr:num` STRIP_ASSUME_TAC o check (is_exists o concl)) THEN
  RVEQ_TAC THEN EXISTS_TAC `CONS ptr p1:num list` THEN
  ASM_SIMP_TAC[GCP3AUX_SUBSET_CONS; MAP; SUM; lookup_len_def] THEN CONJ_TAC THENL
   [CASE_REWRITE_TAC[] THEN REWRITE_TAC[Word64Rep_def] THEN COND_CASES_TAC THEN
    REWRITE_TAC[el_length_def] THEN ARITH_TAC;
    MATCH_MP_TAC GCP3AUX_th_ptr_leaf THEN REWRITE_TAC[GSYM Word64Rep_def] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REWRITE_TAC[Word64Rep_def] THEN
    COND_CASES_TAC THEN MESON_TAC[]];;

(* GCP3AUX: numbers that are small for the limits are small integers *)
let GCP3AUX_small_num_small_int = prove
 (`!i. good_dimindex (:A) /\ small_num (dimindex (:A) = 64) i ==> small_int (:A) i`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def; small_num_def; small_int_def; dimword_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[]);;

(* gcp3aux: helper of soundness_size_of *)
let gcp3aux_sound_number_tac : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[size_of_def; PAIR_EQ; PERM_SING] THEN STRIP_TAC THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `v:(A word_loc)heap_address` (X_CHOOSE_THEN `vs:((A word_loc)heap_address)list`
    STRIP_ASSUME_TAC)) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[v_inv_def]) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_cond (concl th))) THEN
  COND_CASES_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `p1:num list` THEN
    ASM_REWRITE_TAC[LE_ADDR; el 2 GCP3AUX_th_rules];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr:num` STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  SUBGOAL_THEN `~small_num (limits_arch_64_bit lims) i` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `~small_int (:A) i`)) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC GCP3AUX_small_num_small_int THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `CONS ptr p1:num list` THEN
  ASM_SIMP_TAC[GCP3AUX_SUBSET_CONS; MAP; SUM; lookup_len_def] THEN CONJ_TAC THENL
   [CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[data_to_word_memoryProof_Bignum_def; i2mw_def; el_length_def; bignum_size_def] THEN
    CASE_REWRITE_TAC[el_length_def] THEN
    MP_TAC(ISPECL [`num_of_int (abs i)`; `num_of_int (abs i)`]
             (INST_TYPE [`:A`,`:A`] LENGTH_n2mw_LE_bignum_digits)) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN ARITH_TAC;
    MATCH_MP_TAC GCP3AUX_th_ptr_leaf THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `heap_lookup:num->
      ((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list->
      ((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)option`))
      (concl th))) THEN
    REWRITE_TAC[data_to_word_memoryProof_Bignum_def; i2mw_def] THEN CASE_REWRITE_TAC[] THEN
    MESON_TAC[]];;

(* GCP3AUX: reachable_refs is monotone in the roots *)
let GCP3AUX_reachable_refs_mono = prove
 (`!xs ys refs n.
     (!x. MEM x xs ==> MEM x ys) /\ reachable_refs xs refs n ==> reachable_refs ys refs n`,
  REWRITE_TAC[reachable_refs_def] THEN MESON_TAC[]);;

(* gcp3aux: helper of soundness_size_of *)
let gcp3aux_sound_cons_tac : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term ((=) `CONS (x:data_v) (CONS y ys)`)) (lhs (concl th)))) THEN
  REWRITE_TAC[size_of_def] THEN DISCH_TAC THEN REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN
  GCP3AUX_SPLIT_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
    fst (strip_comb (concl th)) = `PERM:data_v list->data_v list->bool`)) THEN
  ONCE_REWRITE_TAC[PERM_CONS_EQ_APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:data_v list` (X_CHOOSE_THEN `N:data_v list` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP EVERY2_APPEND_CONS o check (fun th -> is_comb (concl th) &&
    fst (strip_comb (concl th)) <> `PERM:data_v list->data_v list->bool` &&
    can (find_term ((=) `APPEND (M:data_v list) (CONS x N)`)) (concl th) &&
    not (is_forall (concl th)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `t:(A word_loc)heap_address` (X_CHOOSE_THEN `t2:((A word_loc)heap_address)list`
      STRIP_ASSUME_TAC))) THEN RVEQ_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`APPEND M N:data_v list`;
    `APPEND t1 t2:((A word_loc)heap_address)list`; `n1:num`; `refs1:((data_v)bvl_ref)spt`;
    `seen1:num_set`; `p1:num list`; `refs':((data_v)bvl_ref)spt`; `f:(num,num)fmap`;
    `tf:(num,num)fmap`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `c:data_to_word_config`; `be:bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC GCP3AUX_reachable_refs_mono THEN EXISTS_TAC `APPEND M N:data_v list` THEN
      ASM_REWRITE_TAC[MEM_APPEND; MEM] THEN MESON_TAC[];
      MATCH_MP_TAC LIST_REL_APPEND_suff THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2a:num list` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "ih2" (MP_TAC o SPECL [`n1:num`; `refs1:((data_v)bvl_ref)spt`; `seen1:num_set`]) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`[x]:data_v list`; `[t]:((A word_loc)heap_address)list`;
    `n2':num`; `r2:((data_v)bvl_ref)spt`; `s2:num_set`; `p2a:num list`;
    `refs':((data_v)bvl_ref)spt`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `c:data_to_word_config`; `be:bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ALL2; PERM_REFL] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GCP3AUX_reachable_refs_mono THEN EXISTS_TAC `[x]:data_v list` THEN
    ASM_REWRITE_TAC[MEM_APPEND; MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2b:num list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p2b:num list` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_ARITH_TAC;
    MATCH_MP_TAC (el 1 GCP3AUX_th_rules) THEN
    MAP_EVERY EXISTS_TAC [`APPEND t1 t2:((A word_loc)heap_address)list`;
                          `[t]:((A word_loc)heap_address)list`; `p2a:num list`] THEN
    ASM_REWRITE_TAC[SET_OF_LIST_APPEND; set_of_list] THEN SET_TAC[]];;

(* GCP3AUX: a reference root reaches itself *)
let GCP3AUX_reachable_refs_RefPtr_self = prove
 (`!b r refs. reachable_refs [data_RefPtr b r] refs r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[reachable_refs_def] THEN
  MAP_EVERY EXISTS_TAC [`data_RefPtr b r`; `r:num`] THEN
  REWRITE_TAC[MEM; get_refs_def; RTC_REFL]);;

(* GCP3AUX: what a reference reaches through one edge, a reference root reaches *)
let GCP3AUX_reachable_refs_RefPtr_step = prove
 (`!b r refs xs n.
     (!y. MEM y (FLAT (MAP get_refs xs)) ==> ref_edge refs r y) /\
     reachable_refs xs refs n ==> reachable_refs [data_RefPtr b r] refs n`,
  REWRITE_TAC[reachable_refs_def; MEM; get_refs_def; MEM_FLAT; MEM_MAP] THEN
  REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`data_RefPtr b r`; `r:num`] THEN
  REWRITE_TAC[MEM; get_refs_def] THEN ONCE_REWRITE_TAC[RTC_CASES_R] THEN DISJ2_TAC THEN
  EXISTS_TAC `r':num` THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `get_refs x` THEN ASM_MESON_TAC[]);;

(* GCP3AUX: a block root reaches what its payload reaches *)
let GCP3AUX_reachable_refs_Block = prove
 (`!vs refs n ts tag. reachable_refs vs refs n ==> reachable_refs [data_Block ts tag vs] refs n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[reachable_refs_def] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`data_Block ts tag vs`; `r:num`] THEN
  ASM_REWRITE_TAC[MEM; get_refs_def; MEM_FLAT; MEM_MAP] THEN ASM_MESON_TAC[]);;

(* GCP3AUX: the pointed-to references outside the cut, after removing r *)
let GCP3AUX_IMAGE_delete_SUBSET = prove
 (`!(f:(num,num)fmap) (refs':A spt) (refs:A spt) r p1.
     IMAGE (FAPPLY f) (domain refs' DIFF domain refs) SUBSET set_of_list p1 ==>
     IMAGE (FAPPLY f) (domain refs' DIFF domain (delete r refs)) SUBSET
       set_of_list (CONS (FAPPLY f r) p1)`,
  REWRITE_TAC[domain_delete; set_of_list; SUBSET; IN_IMAGE; IN_DIFF; IN_DELETE; IN_INSERT] THEN
  MESON_TAC[]);;

(* GCP3AUX: deleting keeps a sub-tree *)
let GCP3AUX_subspt_delete = prove
 (`!k (t1:A spt) t2. subspt t1 t2 ==> subspt (delete k t1) t2`,
  REWRITE_TAC[subspt_lookup; lookup_delete] THEN MESON_TAC[option_DISTINCT]);;

(* GCP3AUX: a reference value is a pointer to its heap block *)
let GCP3AUX_v_inv_RefPtr = prove
 (`!c x r refs' (v:(A word_loc)heap_address) f tf heap.
     no_thunks_in_refs refs' /\ v_inv c (data_RefPtr x r) refs' (v,f,tf,heap) ==>
     r IN FDOM f /\ v = Pointer (FAPPLY f r) (ref_ptr_annot c (lookup r refs'))`,
  REWRITE_TAC[v_inv_def; no_thunks_in_refs_def] THEN MESON_TAC[]);;

(* GCP3AUX: the case of soundness_size_of for a reference whose payload is  *)
(* traversed recursively (value arrays and mutable blocks)                  *)
let GCP3AUX_sound_payload = prove
 (`!lims payload refs (seen:num_set) r x n refs3 seen3 zs d p1 refs' f tf
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
    c be t.
     (!root_vars (vars:((A word_loc)heap_address)list) n2 r2 s2 p1 refs' f tf heap c be.
        (!n. reachable_refs root_vars refs' n /\ n IN FDOM f ==>
             bc_ref_inv c n refs' (f,tf,heap,be)) /\
        no_thunks_in_refs refs' /\
        ALL2 (\v x. v_inv c v refs' (x,f,tf,heap)) root_vars vars /\
        PERM payload root_vars /\ good_dimindex (:A) /\
        IMAGE (FAPPLY tf) (domain seen) SUBSET set_of_list p1 /\
        IMAGE (FAPPLY f) (domain refs' DIFF domain (delete r refs)) SUBSET set_of_list p1 /\
        FDOM f SUBSET domain refs' /\ subspt (delete r refs) refs' /\
        (limits_arch_64_bit lims <=> dimindex (:A) = 64) /\
        size_of lims payload (delete r refs) seen = (n2,r2,s2) ==>
        ?p2. SUM (MAP (lookup_len heap) p2) <= n2 + SUM (MAP (lookup_len heap) p1) /\
             traverse_heap heap p1 vars p2 /\ subspt r2 refs' /\
             IMAGE (FAPPLY tf) (domain s2) SUBSET set_of_list p2 /\
             IMAGE (FAPPLY f) (domain refs' DIFF domain r2) SUBSET set_of_list p2) /\
     (!y. MEM y (FLAT (MAP get_refs payload)) ==> ref_edge refs' r y) /\
     (!n. reachable_refs [data_RefPtr x r] refs' n /\ n IN FDOM f ==>
          bc_ref_inv c n refs' (f,tf,heap,be)) /\
     no_thunks_in_refs refs' /\ good_dimindex (:A) /\
     IMAGE (FAPPLY tf) (domain seen) SUBSET set_of_list p1 /\
     IMAGE (FAPPLY f) (domain refs' DIFF domain refs) SUBSET set_of_list p1 /\
     FDOM f SUBSET domain refs' /\ subspt refs refs' /\
     (limits_arch_64_bit lims <=> dimindex (:A) = 64) /\
     heap_lookup (FAPPLY f r) heap = SOME (DataElement zs (LENGTH zs) d) /\
     ALL2 (\z y. v_inv c y refs' (z,f,tf,heap)) zs payload /\
     size_of lims payload (delete r refs) seen = (n,refs3,seen3) ==>
     ?p2. SUM (MAP (lookup_len heap) p2) <=
            (n + LENGTH zs + 1) + SUM (MAP (lookup_len heap) p1) /\
          traverse_heap heap p1 [Pointer (FAPPLY f r) t] p2 /\ subspt refs3 refs' /\
          IMAGE (FAPPLY tf) (domain seen3) SUBSET set_of_list p2 /\
          IMAGE (FAPPLY f) (domain refs' DIFF domain refs3) SUBSET set_of_list p2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`payload:data_v list`; `zs:((A word_loc)heap_address)list`;
    `n:num`; `refs3:((data_v)bvl_ref)spt`; `seen3:num_set`; `CONS (FAPPLY (f:(num,num)fmap) r) p1:num list`;
    `refs':((data_v)bvl_ref)spt`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `c:data_to_word_config`; `be:bool`] o check (is_forall o concl)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PERM_REFL; GCP3AUX_SUBSET_CONS; GCP3AUX_IMAGE_delete_SUBSET;
                 GCP3AUX_subspt_delete] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC GCP3AUX_reachable_refs_RefPtr_step THEN
      EXISTS_TAC `payload:data_v list` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP EVERY2_SWAP o check (fun th ->
        is_comb (concl th) && can (find_term ((=) `zs:((A word_loc)heap_address)list`)) (concl th) &&
        not (is_eq (concl th)))) THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:num list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p2:num list` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "<=" (concl th))) THEN
    ASM_REWRITE_TAC[MAP; SUM; lookup_len_def] THEN CASE_REWRITE_TAC[el_length_def] THEN
    ARITH_TAC;
    MATCH_MP_TAC (el 4 GCP3AUX_th_rules) THEN
    MAP_EVERY EXISTS_TAC [`zs:((A word_loc)heap_address)list`; `LENGTH (zs:((A word_loc)heap_address)list)`;
                          `d:data_to_word_memoryProof_tag#(A word_loc)list`] THEN
    ASM_REWRITE_TAC[]]);;

(* gcp3aux: helper of soundness_size_of *)
let gcp3aux_sound_refptr_tac : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PERM_SING]) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `v:(A word_loc)heap_address` (X_CHOOSE_THEN `vs:((A word_loc)heap_address)list`
    STRIP_ASSUME_TAC) o check (is_exists o concl)) THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `x:bool`; `r:num`; `refs':((data_v)bvl_ref)spt`;
                 `v:(A word_loc)heap_address`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`]
           GCP3AUX_v_inv_RefPtr) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `v:(A word_loc)heap_address`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_comb (lhs (concl th)) &&
    can (find_term ((=) `size_of`)) (concl th) || false) o
    check (fun th -> is_eq (concl th))) THEN
  REWRITE_TAC[size_of_def] THEN
  MP_TAC(ISPEC `lookup r (refs:((data_v)bvl_ref)spt)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th)
    (X_CHOOSE_THEN `a:(data_v)bvl_ref` (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))) THEN
  CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `p1:num list` THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; LE_REFL] THEN MATCH_MP_TAC (el 3 GCP3AUX_th_rules) THEN
    REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "DIFF")) (concl th))) THEN
    REWRITE_TAC[IN_IMAGE; IN_DIFF] THEN EXISTS_TAC `r:num` THEN
    ASM_REWRITE_TAC[GSYM lookup_NONE_domain] THEN
    UNDISCH_TAC `FDOM (f:(num,num)fmap) SUBSET domain (refs':((data_v)bvl_ref)spt)` THEN
    UNDISCH_TAC `(r:num) IN FDOM (f:(num,num)fmap)` THEN REWRITE_TAC[SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lookup r (refs':((data_v)bvl_ref)spt) = SOME a` ASSUME_TAC THENL
   [UNDISCH_TAC `subspt (refs:((data_v)bvl_ref)spt) refs'` THEN
    REWRITE_TAC[subspt_lookup] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bc_ref_inv c r refs' (f,tf,heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list,be:bool)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[GCP3AUX_reachable_refs_RefPtr_self];
    ALL_TAC] THEN
  SUBGOAL_THEN `FLOOKUP (f:(num,num)fmap) r = SOME (FAPPLY f r)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FLOOKUP_DEF]; ALL_TAC] THEN
  ASM_REWRITE_TAC[bc_ref_inv_def] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a:(data_v)bvl_ref` THEN CASE_REWRITE_TAC[] THENL
   [DISCH_THEN(X_CHOOSE_THEN `zs:((A word_loc)heap_address)list` STRIP_ASSUME_TAC) THEN
    DISCH_TAC THEN REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN GCP3AUX_SPLIT_TAC THEN
    SUBGOAL_THEN `LENGTH (a':data_v list) = LENGTH (zs:((A word_loc)heap_address)list)`
      SUBST1_TAC THENL [ASM_MESON_TAC[LIST_REL_LENGTH]; ALL_TAC] THEN
    MP_TAC(ISPECL [`lims:limits`; `a':data_v list`; `refs:((data_v)bvl_ref)spt`;
      `seen:num_set`; `r:num`; `x:bool`; `n:num`; `r2:((data_v)bvl_ref)spt`; `s2:num_set`;
      `zs:((A word_loc)heap_address)list`;
      `(RefTag,[]):data_to_word_memoryProof_tag#(A word_loc)list`; `p1:num list`;
      `refs':((data_v)bvl_ref)spt`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
      `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `c:data_to_word_config`; `be:bool`;
      `ref_ptr_annot (c:data_to_word_config) (SOME (bvl_ValueArray (a':data_v list))):A word_loc`]
      GCP3AUX_sound_payload) THEN
    ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        fst(dest_var(fst(dest_forall(concl th)))) = "vs")) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ref_edge_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[get_refs_def];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM RefBlock_def];
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    DISCH_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
    EXISTS_TAC `CONS (FAPPLY (f:(num,num)fmap) r) p1` THEN
    ASM_SIMP_TAC[GCP3AUX_SUBSET_CONS; GCP3AUX_IMAGE_delete_SUBSET; GCP3AUX_subspt_delete;
                 MAP; SUM; lookup_len_def] THEN
    REWRITE_TAC[data_to_word_memoryProof_Bytes_def; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CASE_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[el_length_def; LENGTH_write_bytes; LENGTH_REPLICATE; arch_size_def] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def] o
        check (fun th -> concl th = `good_dimindex (:A)`)) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      MATCH_MP_TAC GCP3AUX_th_ptr_leaf THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "Bytes")) (concl th))) THEN
      REWRITE_TAC[data_to_word_memoryProof_Bytes_def; LET_DEF; LET_END_DEF] THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN MESON_TAC[]];
    SUBGOAL_THEN `F` CONTR_TAC THEN
    UNDISCH_TAC `no_thunks_in_refs (refs':((data_v)bvl_ref)spt)` THEN
    REWRITE_TAC[no_thunks_in_refs_def] THEN DISCH_THEN(MP_TAC o SPEC `r:num`) THEN
    ASM_REWRITE_TAC[injectivity "option"; injectivity "bvl_ref"] THEN MESON_TAC[];
    STRIP_TAC THEN DISCH_TAC THEN REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN GCP3AUX_SPLIT_TAC THEN
    SUBGOAL_THEN `n + LENGTH (a2:data_v list) + LENGTH (a4:data_v list) + 2 =
                  n + LENGTH (zs:((A word_loc)heap_address)list) + 1` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP LIST_REL_LENGTH o check (fun th ->
        free_in `zs:((A word_loc)heap_address)list` (concl th) && not (is_eq (concl th)))) THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`lims:limits`; `APPEND (APPEND (a2:data_v list) [a3]) a4`;
      `refs:((data_v)bvl_ref)spt`;
      `seen:num_set`; `r:num`; `x:bool`; `n:num`; `r2:((data_v)bvl_ref)spt`; `s2:num_set`;
      `zs:((A word_loc)heap_address)list`;
      `(BlockTag a0,[]):data_to_word_memoryProof_tag#(A word_loc)list`; `p1:num list`;
      `refs':((data_v)bvl_ref)spt`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
      `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `c:data_to_word_config`; `be:bool`;
      `ref_ptr_annot (c:data_to_word_config)
         (SOME (MutBlock a0 a1 (a2:data_v list) a3 a4)):A word_loc`]
      GCP3AUX_sound_payload) THEN
    ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        fst(dest_var(fst(dest_forall(concl th)))) = "tg")) THEN
      FIRST_ASSUM(fun th -> if is_eq (concl th) &&
        free_in `refs:((data_v)bvl_ref)spt` (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "MutBlock")) (concl th)
        then MESON_TAC[th] else NO_TAC);
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ref_edge_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[get_refs_def];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM BlockRep_def]];;

(* gcp3aux: helper of soundness_size_of *)
let gcp3aux_sound_block_tac : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PERM_SING]) THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `v:(A word_loc)heap_address` (X_CHOOSE_THEN `vs:((A word_loc)heap_address)list`
    STRIP_ASSUME_TAC) o check (is_exists o concl)) THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> not (is_forall (concl th)) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "v_inv")) (concl th))) THEN
  REWRITE_TAC[v_inv_def; NOT_CONS_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `ptr:num` (X_CHOOSE_THEN `xs:((A word_loc)heap_address)list`
    STRIP_ASSUME_TAC)) THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "size_of")) (concl th))) THEN
  REWRITE_TAC[size_of_def] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `p1:num list` THEN
    ASM_REWRITE_TAC[LE_ADDR] THEN MATCH_MP_TAC (el 3 GCP3AUX_th_rules) THEN
    REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term ((=) `FAPPLY (tf:(num,num)fmap)`)) (concl th))) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `ts:num` THEN
    UNDISCH_TAC `FLOOKUP (tf:(num,num)fmap) ts = SOME ptr` THEN
    UNDISCH_TAC `IS_SOME (lookup ts (s2:num_set))` THEN
    REWRITE_TAC[FLOOKUP_DEF; domain_lookup] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    CASES_ON `lookup ts (s2:num_set)` THEN REWRITE_TAC[IS_SOME_DEF] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN GCP3AUX_SPLIT_TAC THEN
  SUBGOAL_THEN `FAPPLY (tf:(num,num)fmap) ts = ptr` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FAPPLY_FLOOKUP; THE_DEF]; ALL_TAC] THEN
  REMOVE_THEN "ih" (fun ih -> FIRST_ASSUM (fun th -> MP_TAC (MP ih th))) THEN
  DISCH_THEN(MP_TAC o SPECL [`CONS (v16:data_v) v17`; `xs:((A word_loc)heap_address)list`;
    `n:num`; `r2:((data_v)bvl_ref)spt`; `s2:num_set`; `CONS (ptr:num) p1`;
    `refs':((data_v)bvl_ref)spt`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `c:data_to_word_config`; `be:bool`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PERM_REFL; GCP3AUX_SUBSET_CONS; domain_insert; IMAGE_CLAUSES] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC GCP3AUX_reachable_refs_Block THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[set_of_list] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:num list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p2:num list` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `LENGTH (CONS (v16:data_v) v17) = LENGTH (xs:((A word_loc)heap_address)list)`
      SUBST1_TAC THENL [ASM_MESON_TAC[LIST_REL_LENGTH]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "<=" (concl th))) THEN
    ASM_REWRITE_TAC[MAP; SUM; lookup_len_def; BlockRep_def] THEN CASE_REWRITE_TAC[el_length_def] THEN
    ARITH_TAC;
    MATCH_MP_TAC (el 4 GCP3AUX_th_rules) THEN
    MAP_EVERY EXISTS_TAC [`xs:((A word_loc)heap_address)list`;
      `LENGTH (xs:((A word_loc)heap_address)list)`;
      `(BlockTag tag,[]):data_to_word_memoryProof_tag#(A word_loc)list`] THEN
    ASM_REWRITE_TAC[GSYM BlockRep_def]];;

(* HOL4 line 6904 *)
let soundness_size_of = prove
 (`!lims roots r1 s1 root_vars (vars:((A word_loc)heap_address)list) n2 r2 s2 p1 refs
    f tf heap c be.
     (!n. reachable_refs root_vars refs n /\ n IN FDOM f ==>
          bc_ref_inv c n refs (f,tf,heap,be)) /\
     no_thunks_in_refs refs /\
     ALL2 (\v x. v_inv c v refs (x,f,tf,heap)) root_vars vars /\
     PERM roots root_vars /\ good_dimindex (:A) /\
     IMAGE (FAPPLY tf) (domain s1) SUBSET set_of_list p1 /\
     IMAGE (FAPPLY f) (domain refs DIFF domain r1) SUBSET set_of_list p1 /\
     FDOM f SUBSET domain refs /\ subspt r1 refs /\
     (limits_arch_64_bit lims <=> dimindex (:A) = 64) /\
     size_of lims roots r1 s1 = (n2,r2,s2) ==>
     ?p2. SUM (MAP (lookup_len heap) p2) <= n2 + SUM (MAP (lookup_len heap) p1) /\
          traverse_heap heap p1 vars p2 /\ subspt r2 refs /\
          IMAGE (FAPPLY tf) (domain s2) SUBSET set_of_list p2 /\
          IMAGE (FAPPLY f) (domain refs DIFF domain r2) SUBSET set_of_list p2`,
  MATCH_MP_TAC size_of_ind THEN REPEAT CONJ_TAC THENL
   [gcp3aux_sound_nil_tac; gcp3aux_sound_cons_tac; gcp3aux_sound_word64_tac;
    gcp3aux_sound_number_tac; gcp3aux_sound_data_tac; gcp3aux_sound_refptr_tac;
    gcp3aux_sound_data_tac; gcp3aux_sound_block_tac]);;

(* HOL4 line 7121 *)
let traverse_heap_reachable_set_mono = prove
 (`!(heap1:((A,B)heap_element)list) ps vars ps2.
     traverse_heap heap1 ps vars ps2 ==> set_of_list ps SUBSET set_of_list ps2`,
  MATCH_MP_TAC traverse_heap_ind THEN REWRITE_TAC[SUBSET_REFL; set_of_list] THEN
  REPEAT STRIP_TAC THEN ASM SET_TAC[]);;

(* HOL4 line 7129 *)
let traverse_heap_reachable_aux_vars_gc_edge = prove
 (`!(heap:((A,B)heap_element)list) ps vars ps2.
     traverse_heap heap ps vars ps2 ==>
     !vars2.
       (!y z. MEM y ps /\ gc_edge heap y z ==>
              MEM z ps \/ (?t. MEM (Pointer z t) (APPEND vars vars2))) ==>
       (set_of_list ps SUBSET set_of_list ps2) /\
       (!y t. MEM (Pointer y t) vars ==>
              MEM y ps2 \/ (?t. MEM (Pointer y t) vars2)) /\
       (!y z. MEM y ps2 /\ gc_edge heap y z ==>
              MEM z ps2 \/ (?t. MEM (Pointer z t) vars2))`,
  MATCH_MP_TAC traverse_heap_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MEM; APPEND; SUBSET_REFL];
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (CONJUNCTS_THEN2 (LABEL_TAC "ih2") ASSUME_TAC)) THEN
    X_GEN_TAC `vars2:((A)heap_address)list` THEN DISCH_TAC THEN
    REMOVE_THEN "ih1" (MP_TAC o SPEC `APPEND vs2 vars2:((A)heap_address)list`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[APPEND_ASSOC; MEM_APPEND] THEN
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[EXTENSION; IN_SET_OF_LIST; MEM_APPEND] o
        check (fun th -> is_eq (concl th) && is_comb (lhs (concl th)))) THEN
      UNDISCH_TAC `!y z. MEM y (p1:num list) /\ gc_edge (heap:((A,B)heap_element)list) y z ==>
                    MEM z p1 \/ (?t. MEM (Pointer z t) (APPEND (vars:((A)heap_address)list) vars2))` THEN
      REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN
    REMOVE_THEN "ih2" (MP_TAC o SPEC `vars2:((A)heap_address)list`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET_TRANS];
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[EXTENSION; IN_SET_OF_LIST; MEM_APPEND] o
        check (fun th -> is_eq (concl th) && is_comb (lhs (concl th)))) THEN
      UNDISCH_TAC `set_of_list (p2:num list) SUBSET set_of_list p3` THEN
      REWRITE_TAC[SUBSET; IN_SET_OF_LIST] THEN
      UNDISCH_TAC `!y t. MEM (Pointer y t) (vs1:((A)heap_address)list) ==>
                    MEM y (p2:num list) \/
                         (?t. MEM (Pointer y t) (APPEND vs2 (vars2:((A)heap_address)list)))` THEN
      UNDISCH_TAC `!y t. MEM (Pointer y t) (vs2:((A)heap_address)list) ==>
                    MEM y (p3:num list) \/ (?t. MEM (Pointer y t) (vars2:((A)heap_address)list))` THEN
      REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[];
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[MEM; APPEND; SUBSET_REFL; distinctness "heap_address"] THEN MESON_TAC[];
    REWRITE_TAC[MEM; APPEND; SUBSET_REFL; injectivity "heap_address"] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ih")) THEN
    X_GEN_TAC `vars2:((A)heap_address)list` THEN DISCH_TAC THEN
    REMOVE_THEN "ih" (MP_TAC o SPEC `vars2:((A)heap_address)list`) THEN ANTS_TAC THENL
     [REWRITE_TAC[MEM; MEM_APPEND] THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[gc_edge_def]) THEN
        ASM_REWRITE_TAC[option_INJ; injectivity "heap_element"] THEN MESON_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPECL [`y:num`; `z:num`]) THEN
        ASM_REWRITE_TAC[MEM; APPEND; injectivity "heap_address"] THEN MESON_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[set_of_list; MEM; injectivity "heap_address"; INSERT_SUBSET] THEN
    MESON_TAC[IN_SET_OF_LIST]]);;

(* HOL4 line 7165 *)
let traverse_heap_reachable_RTC_gc_edge = prove
 (`!(heap:((A,B)heap_element)list) vars ps2.
     traverse_heap heap [] vars ps2 ==>
     (!p x. RTC (gc_edge heap) p x ==> MEM p ps2 ==> MEM x ps2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `[]:((A)heap_address)list` o
    MATCH_MP traverse_heap_reachable_aux_vars_gc_edge) THEN
  REWRITE_TAC[MEM; APPEND_NIL] THEN STRIP_TAC THEN
  MATCH_MP_TAC RTC_INDUCT THEN ASM_MESON_TAC[]);;

(* HOL4 line 7177 *)
let traverse_heap_reachable = prove
 (`!(heap1:((A,B)heap_element)list) vars p2 x.
     traverse_heap heap1 [] vars p2 /\
     reachable_addresses vars heap1 x ==> MEM x p2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[reachable_addresses_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `[]:((A)heap_address)list` o
    MATCH_MP traverse_heap_reachable_aux_vars_gc_edge) THEN
  REWRITE_TAC[MEM; APPEND_NIL] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP traverse_heap_reachable_RTC_gc_edge) THEN
  DISCH_THEN(MP_TAC o SPECL [`x':num`; `x:num`]) THEN ASM_MESON_TAC[]);;

(* HOL4 line 7189 (local) *)
let stack_rel_imp_subset = prove
 (`!xs (ys:((A)stack_frame)list).
     ALL2 data_to_word_gcProof_stack_rel xs ys ==>
     set_of_list (wl_enc_stack ys) SUBSET set_of_list (MAP SND (data_to_word_gcProof_flat xs ys))`,
  LIST_INDUCT_TAC THEN X_GEN_TAC `ys:((A)stack_frame)list` THEN
  MP_TAC(ISPEC `ys:((A)stack_frame)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `y:(A)stack_frame` (X_CHOOSE_THEN `ys':((A)stack_frame)list` SUBST1_TAC))) THEN
  REWRITE_TAC[ALL2; wl_enc_stack_def; set_of_list; EMPTY_SUBSET] THEN
  CASES_ON `h:stack` THEN CASES_ON `y:(A)stack_frame` THEN
  SPEC_TAC(`a3:(num#num#num)option`,`a3:(num#num#num)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_stack_rel_def; flat_def; wl_enc_stack_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MAP_APPEND; GCP3AUX_MAP_SND_join_env; SET_OF_LIST_APPEND] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ys':((A)stack_frame)list`) THEN ASM_REWRITE_TAC[] THEN
  SET_TAC[]);;

(* GCP3AUX: a tree with an element has a non-zero size *)
let GCP3AUX_lookup_size = prove
 (`!k (t:A spt) v. lookup k t = SOME v ==> ~(size t = 0)`,
  REWRITE_TAC[size_zero_empty; EXTENSION; NOT_IN_EMPTY; domain_lookup] THEN MESON_TAC[]);;

(* HOL4 line 7213 *)
let PERM_toList_lookup_eq = prove
 (`!m1 (m2:A spt). (!k. lookup k m1 = lookup k m2) ==> PERM (toList m1) (toList m2)`,
  SUBGOAL_THEN `!n (m1:A spt) m2. size m1 = n /\ (!k. lookup k m1 = lookup k m2) ==>
                                  PERM (toList m1) (toList m2)`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `?k (v:A). lookup k (m1:A spt) = SOME v` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` (X_CHOOSE_TAC `v:A`)) THEN
    SUBGOAL_THEN `lookup k (m2:A spt) = SOME (v:A)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `PERM (toList (delete k (m1:A spt))) (toList (delete k (m2:A spt)))`
      ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `size (delete k (m1:A spt))` o check (fun th ->
        is_forall (concl th) && is_imp (snd (dest_forall (concl th))))) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[size_delete; option_DISTINCT] THEN
        MP_TAC(ISPECL [`k:num`; `m1:A spt`; `v:A`] GCP3AUX_lookup_size) THEN
        ASM_REWRITE_TAC[] THEN ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`delete k (m1:A spt)`; `delete k (m2:A spt)`]) THEN
      ASM_REWRITE_TAC[lookup_delete];
      ALL_TAC] THEN
    MATCH_MP_TAC PERM_TRANS THEN EXISTS_TAC `CONS (v:A) (toList (delete k (m1:A spt)))` THEN
    ASM_SIMP_TAC[PERM_toList_delete] THEN
    MATCH_MP_TAC PERM_TRANS THEN EXISTS_TAC `CONS (v:A) (toList (delete k (m2:A spt)))` THEN
    ASM_SIMP_TAC[PERM_MONO] THEN ONCE_REWRITE_TAC[PERM_SYM] THEN
    MATCH_MP_TAC PERM_toList_delete THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `!j. lookup j (m1:A spt) = NONE` ASSUME_TAC THENL
     [X_GEN_TAC `j:num` THEN CASES_ON `lookup j (m1:A spt)` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
      DISCH_THEN(MP_TAC o SPECL [`j:num`; `a:A`]) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `toList (m1:A spt) = [] /\ toList (m2:A spt) = []`
      (fun th -> REWRITE_TAC[th; PERM_REFL]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC GCP3AUX_toList_NIL THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC GCP3AUX_toList_NIL THEN
      GEN_TAC THEN UNDISCH_TAC `!k. lookup k (m1:A spt) = lookup k m2` THEN
      UNDISCH_TAC `!j. lookup j (m1:A spt) = NONE` THEN MESON_TAC[]]]);;

(* HOL4 line 7237 *)
let LIST_REL_exists_witness = prove
 (`!(xs:A list) (P:A->B->bool).
     (!x. MEM x xs ==> ?y. P x y) ==> ?ys. ALL2 P xs ys`,
  LIST_INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `[]:B list` THEN REWRITE_TAC[ALL2];
    X_GEN_TAC `P:A->B->bool` THEN REWRITE_TAC[MEM] THEN DISCH_TAC THEN
    FIRST_ASSUM(X_CHOOSE_TAC `y:B` o C MP (DISJ1 (REFL `h:A`) `MEM (h:A) t`) o
      SPEC `h:A`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `P:A->B->bool`) THEN ANTS_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `ys:B list`) THEN EXISTS_TAC `CONS (y:B) ys` THEN
    ASM_REWRITE_TAC[ALL2]]);;

(* HOL4 line 7243 *)
let get_vars_PERM_toList_inter = prove
 (`!args (x':num_set) (vals:A list) locals.
     data_get_vars args locals = SOME vals ==>
     ?dups.
       PERM (APPEND vals (toList (inter locals x')))
            (APPEND dups (toList (inter locals (list_insert args x')))) /\
       set_of_list dups SUBSET set_of_list vals /\
       set_of_list vals SUBSET set_of_list (toList (inter locals (list_insert args x')))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[data_get_vars_def; list_insert_def; option_INJ] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN EXISTS_TAC `[]:A list` THEN
    REWRITE_TAC[APPEND; PERM_REFL; set_of_list; EMPTY_SUBSET];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x2:num_set`; `vals:A list`; `locals:A spt`] THEN
  REWRITE_TAC[data_get_vars_def; data_get_var_def; list_insert_def] THEN
  MP_TAC(ISPEC `lookup h (locals:A spt)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `v:A` (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  CASE_REWRITE_TAC[option_DISTINCT] THEN
  MP_TAC(ISPEC `data_get_vars t (locals:A spt)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `ws:A list` (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`insert h one (x2:num_set)`; `ws:A list`; `locals:A spt`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `dups:A list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `MEM (v:A) (toList (inter (locals:A spt) (list_insert t (insert h one (x2:num_set)))))`
    ASSUME_TAC THENL
   [REWRITE_TAC[MEM_toList] THEN EXISTS_TAC `h:num` THEN
    ASM_REWRITE_TAC[lookup_inter_alt; domain_list_insert; domain_insert; IN_INSERT];
    ALL_TAC] THEN
  ASM_CASES_TAC `h IN domain (x2:num_set)` THENL
   [EXISTS_TAC `CONS (v:A) dups` THEN
    SUBGOAL_THEN `PERM (toList (inter (locals:A spt) (insert h one x2)))
                       (toList (inter locals (x2:num_set)))` ASSUME_TAC THENL
     [MATCH_MP_TAC PERM_toList_lookup_eq THEN
      REWRITE_TAC[lookup_inter_alt; domain_insert; IN_INSERT] THEN
      GEN_TAC THEN ASM_CASES_TAC `k:num = h` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[APPEND; set_of_list] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PERM_MONO THEN MATCH_MP_TAC PERM_TRANS THEN
      EXISTS_TAC `APPEND (ws:A list) (toList (inter (locals:A spt) (insert h one x2)))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PERM_CONG THEN
      ONCE_REWRITE_TAC[PERM_SYM] THEN ASM_REWRITE_TAC[PERM_REFL];
      ASM SET_TAC[];
      REWRITE_TAC[INSERT_SUBSET; IN_SET_OF_LIST] THEN ASM_REWRITE_TAC[]];
    EXISTS_TAC `dups:A list` THEN
    SUBGOAL_THEN `PERM (toList (inter (locals:A spt) (insert h one x2)))
                       (CONS (v:A) (toList (inter locals (x2:num_set))))` ASSUME_TAC THENL
     [MATCH_MP_TAC PERM_TRANS THEN
      EXISTS_TAC `CONS (v:A) (toList (delete h (inter (locals:A spt) (insert h one x2))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PERM_toList_delete THEN
        ASM_REWRITE_TAC[lookup_inter_alt; domain_insert; IN_INSERT];
        MATCH_MP_TAC PERM_MONO THEN MATCH_MP_TAC PERM_toList_lookup_eq THEN
        REWRITE_TAC[lookup_delete; lookup_inter_alt; domain_insert; IN_INSERT] THEN
        GEN_TAC THEN ASM_CASES_TAC `k:num = h` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[APPEND; set_of_list] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PERM_TRANS THEN
      EXISTS_TAC `APPEND (ws:A list) (toList (inter (locals:A spt) (insert h one x2)))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PERM_TRANS THEN
      EXISTS_TAC `APPEND (ws:A list) (CONS v (toList (inter (locals:A spt) (x2:num_set))))` THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC[PERM_SYM] THEN REWRITE_TAC[GCP3AUX_PERM_APPEND_CONS];
        MATCH_MP_TAC PERM_CONG THEN ONCE_REWRITE_TAC[PERM_SYM] THEN
        ASM_REWRITE_TAC[PERM_REFL]];
      ASM SET_TAC[];
      REWRITE_TAC[INSERT_SUBSET; IN_SET_OF_LIST] THEN ASM_REWRITE_TAC[]]]);;

(* HOL4 line 7306 *)
let soundness_size_of_gen = prove
 (`!lims (roots2:data_v list) dups root_vars
    (vars:((A word_loc)heap_address)list) n2 r2 s2 refs c f tf heap be.
     (!n. reachable_refs root_vars refs n /\ n IN FDOM f ==>
          bc_ref_inv c n refs (f,tf,heap,be)) /\
     no_thunks_in_refs refs /\
     ALL2 (\v x. v_inv c v refs (x,f,tf,heap)) root_vars vars /\
     PERM roots2 (APPEND dups root_vars) /\
     set_of_list dups SUBSET set_of_list root_vars /\
     good_dimindex (:A) /\
     FDOM f SUBSET domain refs /\
     (limits_arch_64_bit lims <=> dimindex (:A) = 64) /\
     size_of lims roots2 refs LN = (n2,r2,s2) ==>
     ?p2. SUM (MAP (lookup_len heap) p2) <= n2 /\
          !x. reachable_addresses vars heap x ==> MEM x p2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?dvars. ALL2 (\v x. v_inv c v refs (x,f,tf,heap)) (dups:data_v list)
                                (dvars:((A word_loc)heap_address)list)`
    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC LIST_REL_exists_witness THEN X_GEN_TAC `y:data_v` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`root_vars:data_v list`; `vars:((A word_loc)heap_address)list`;
      `\v x. v_inv c v refs (x,f,tf,heap:((A word_loc,data_to_word_memoryProof_tag#
        (A word_loc)list)heap_element)list)`; `y:data_v`] LIST_REL_MEM_IMP) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[SUBSET; IN_SET_OF_LIST]; MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lims:limits`; `roots2:data_v list`; `refs:((data_v)bvl_ref)spt`; `LN:num_set`;
    `APPEND (dups:data_v list) root_vars`;
    `APPEND (dvars:((A word_loc)heap_address)list) vars`; `n2:num`;
    `r2:((data_v)bvl_ref)spt`; `s2:num_set`; `[]:num list`; `refs:((data_v)bvl_ref)spt`;
    `f:(num,num)fmap`; `tf:(num,num)fmap`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `c:data_to_word_config`; `be:bool`] soundness_size_of) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[subspt_refl; DIFF_EQ_EMPTY; IMAGE_CLAUSES; EMPTY_SUBSET; domain_def] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC GCP3AUX_reachable_refs_mono THEN
      EXISTS_TAC `APPEND (dups:data_v list) root_vars` THEN ASM_REWRITE_TAC[MEM_APPEND] THEN
      ASM_MESON_TAC[SUBSET; IN_SET_OF_LIST];
      MATCH_MP_TAC LIST_REL_APPEND_suff THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[MAP; SUM; ADD_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:num list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p2:num list` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPECL
    [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
     `APPEND (dvars:((A word_loc)heap_address)list) vars`; `p2:num list`; `x:num`]
    traverse_heap_reachable) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `reachable_addresses (vars:((A word_loc)heap_address)list)
                 (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list) x` THEN
  REWRITE_TAC[reachable_addresses_def; MEM_APPEND] THEN MESON_TAC[]);;

(* GCP3AUX: after a collection that leaves too little space, the reachable  *)
(* data of the roots does not fit together with the request               *)
let GCP3AUX_gc_space_bound = prove
 (`!c ts (stack:data_v list) refs v1 xs
    (heap1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
    be limit sp1 sp2 k lims roots2 dups n2 r2 s2.
     heap_ok heap1 limit /\
     bc_stack_ref_inv c ts stack refs (CONS v1 xs,heap1,be) /\
     all_reachable_from_roots (CONS v1 xs) heap1 /\
     heap_length heap1 = data_length heap1 + sp1 + sp2 /\ sp1 + sp2 < k /\
     no_thunks_in_refs refs /\ good_dimindex (:A) /\
     (limits_arch_64_bit lims <=> dimindex (:A) = 64) /\
     PERM roots2 (APPEND dups stack) /\ set_of_list dups SUBSET set_of_list stack /\
     size_of lims roots2 refs LN = (n2,r2,s2) ==>
     limit < n2 + k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `f:(num,num)fmap` (X_CHOOSE_THEN `tf:(num,num)fmap`
    STRIP_ASSUME_TAC) o REWRITE_RULE[bc_stack_ref_inv_def] o
    check (fun th -> can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "bc_stack_ref_inv")) (concl th))) THEN
  MP_TAC(ISPECL [`lims:limits`; `roots2:data_v list`; `dups:data_v list`;
    `stack:data_v list`; `CONS v1 xs:((A word_loc)heap_address)list`; `n2:num`;
    `r2:((data_v)bvl_ref)spt`; `s2:num_set`; `refs:((data_v)bvl_ref)spt`;
    `c:data_to_word_config`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
    `heap1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `be:bool`] soundness_size_of_gen) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:num list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `data_length (heap1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                  heap_element)list) <= n2` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `SUM (MAP (lookup_len (heap1:((A word_loc,data_to_word_memoryProof_tag#
                   (A word_loc)list)heap_element)list)) p2)` THEN
    ASM_REWRITE_TAC[data_length_def] THEN MATCH_MP_TAC SUM_MAP_lookup_len_LESS_EQ THEN
    REWRITE_TAC[set_data_pointers; ALL_DISTINCT_data_pointers] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SET_OF_LIST; isSomeDataElement_def] THEN
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `all_reachable_from_roots (CONS v1 xs)
      (heap1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)` THEN
    REWRITE_TAC[all_reachable_from_roots_def; IN] THEN
    DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `heap_ok (heap1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                 heap_element)list) limit` THEN
  REWRITE_TAC[heap_ok_def] THEN STRIP_TAC THEN ASM_ARITH_TAC);;

(* GCP3AUX: the heap length is determined by its byte size *)
let GCP3AUX_heap_limit_eq = prove
 (`!hl limit.
     good_dimindex (:A) /\
     word_mul bytes_in_word (word hl):A word = word_mul bytes_in_word (word limit) /\
     hl * val (bytes_in_word:A word) < dimword (:A) /\
     (limit + 3) * dimindex (:A) DIV 8 + 1 < dimword (:A) ==>
     hl = limit`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bytes_in_word_def; word_mul_n2w; n2w_11; w2n_n2w] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `4 <= dimindex (:A) DIV 8 /\ dimindex (:A) DIV 8 < dimword (:A)`
    STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[good_dimindex_def] o
      check (fun th -> concl th = `good_dimindex (:A)`)) THEN
    ASM_REWRITE_TAC[dimword_def] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `(dimindex (:A) DIV 8) MOD dimword (:A) = dimindex (:A) DIV 8`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `dimindex (:A) DIV 8 * hl < dimword (:A) /\
                dimindex (:A) DIV 8 * limit < dimword (:A)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `(limit + 3) * dimindex (:A) DIV 8` THEN
      CONJ_TAC THENL [ARITH_TAC; ASM_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "MOD")) (concl th))) THEN
  ASM_SIMP_TAC[MOD_LT; EQ_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

(* GCP3AUX: word addresses are loc_ok, also in lists *)
let GCP3AUX_ALL2_word_addr_loc_ok = prove
 (`!(hs:((A word_loc)heap_address)list) ws c.
     ALL2 (\v w. word_addr c v = w) hs ws ==> ALL loc_ok ws`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  MP_TAC(ISPEC `ws:(A word_loc)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `w:A word_loc` (X_CHOOSE_THEN `ws':(A word_loc)list` SUBST1_TAC))) THEN
  REWRITE_TAC[ALL2; ALL] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[loc_ok_word_addr] THEN ASM_MESON_TAC[]);;

(* GCP3AUX: the values of a word_ml_inv stack are loc_ok *)
let GCP3AUX_word_ml_inv_loc_ok = prove
 (`!heap be a sp sp1 gens limit ts c refs (stack:(data_v#A word_loc)list).
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs stack ==> ALL loc_ok (MAP SND stack)`,
  REWRITE_TAC[word_ml_inv_def] THEN MESON_TAC[GCP3AUX_ALL2_word_addr_loc_ok]);;

(* GCP3AUX: an adjusted empty name set cuts away everything *)
let GCP3AUX_toAList_inter_adjust_set_LN = prove
 (`!t:A spt. toAList (inter t (adjust_set (LN:B spt))) = []`,
  GEN_TAC THEN MP_TAC(ISPEC `toAList (inter (t:A spt) (adjust_set (LN:B spt)))` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC
    (X_CHOOSE_THEN `h:num#A` (X_CHOOSE_THEN `r:(num#A)list` ASSUME_TAC))) THEN
  SUBGOAL_THEN `MEM (h:num#A) (toAList (inter (t:A spt) (adjust_set (LN:B spt))))` MP_TAC THENL
   [ASM_REWRITE_TAC[MEM]; ALL_TAC] THEN
  SPEC_TAC(`h:num#A`,`h:num#A`) THEN REWRITE_TAC[FORALL_PAIR_THM; MEM_toAList] THEN
  REWRITE_TAC[lookup_inter_alt; GCP3AUX_IN_domain_adjust_set; domain_def; NOT_IN_EMPTY] THEN
  REWRITE_TAC[option_DISTINCT]);;

(* GCP3AUX: code_oracle_rel looks at four entries of the store only *)
let GCP3AUX_code_oracle_rel_store = prove
 (`!c (sc:C->(num#num#data_prog)list->(byte list#int64 list#C)option)
    (sco:num->C#(num#num#data_prog)list) (s1:(store_name,A word_loc)fmap) s
    (tc:C->(num#num#(A)wl_prog)list->(byte list#(A word)list#C)option)
    (tco:num->C#(num#num#(A)wl_prog)list) (cb:(A,8)buffer) (db:(A,A)buffer).
     FLOOKUP s1 CodeBuffer = FLOOKUP s CodeBuffer /\
     FLOOKUP s1 CodeBufferEnd = FLOOKUP s CodeBufferEnd /\
     FLOOKUP s1 BitmapBuffer = FLOOKUP s BitmapBuffer /\
     FLOOKUP s1 BitmapBufferEnd = FLOOKUP s BitmapBufferEnd ==>
     (code_oracle_rel c sc sco s1 tc tco cb db <=> code_oracle_rel c sc sco s tc tco cb db)`,
  SIMP_TAC[code_oracle_rel_def]);;

(* GCP3AUX: code_oracle_rel looks at four entries of the store only *)
let GCP3AUX_code_oracle_rel_store_IMP = prove
 (`!c (sc:C->(num#num#data_prog)list->(byte list#int64 list#C)option)
    (sco:num->C#(num#num#data_prog)list) (s1:(store_name,A word_loc)fmap) s
    (tc:C->(num#num#(A)wl_prog)list->(byte list#(A word)list#C)option)
    (tco:num->C#(num#num#(A)wl_prog)list) (cb:(A,8)buffer) (db:(A,A)buffer).
     FLOOKUP s1 CodeBuffer = FLOOKUP s CodeBuffer /\
     FLOOKUP s1 CodeBufferEnd = FLOOKUP s CodeBufferEnd /\
     FLOOKUP s1 BitmapBuffer = FLOOKUP s BitmapBuffer /\
     FLOOKUP s1 BitmapBufferEnd = FLOOKUP s BitmapBufferEnd /\
     code_oracle_rel c sc sco s tc tco cb db ==>
     code_oracle_rel c sc sco s1 tc tco cb db`,
  SIMP_TAC[code_oracle_rel_def]);;

(* HOL4 line 7342 (the unused existentials t2 w1 w2 are left out) *)
let state_rel_gc_gen = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs k.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs ==>
     FLOOKUP (wl_state_store t) AllocSize = SOME (wl_Word (alloc_size k)) /\
     data_state_locals s = LN /\
     wl_state_locals t = LS (wl_Loc l1 l2) ==>
     ?wl m st stack.
       wl_state_gc_fun t (wl_enc_stack (wl_state_stack t),wl_state_memory t,
                          wl_state_mdomain t,wl_state_store t) =
         SOME (wl,m,st) /\
       wl_dec_stack wl (wl_state_stack t) = SOME stack /\
       FLOOKUP st (Temp (word 29)) = FLOOKUP (wl_state_store t) (Temp (word 29)) /\
       FLOOKUP st AllocSize = SOME (wl_Word (alloc_size k)) /\
       (wl_has_space (wl_Word ((alloc_size k):A word)) (wl_state_store_fupd (K st) t) =
          SOME F /\
        ~(data_to_word_config_gc_kind c = data_to_word_None) /\
        no_thunks_in_refs (data_state_refs s) ==>
        !roots2 dups n2 r2 s2.
          PERM roots2 (APPEND (APPEND dups (FLAT (MAP extract_stack (data_state_stack s))))
                         [the_global (data_state_global s)]) /\
          set_of_list dups SUBSET
            set_of_list (APPEND (FLAT (MAP extract_stack (data_state_stack s)))
                           [the_global (data_state_global s)]) /\
          size_of (data_state_limits s) roots2 (data_state_refs s) LN = (n2,r2,s2) ==>
          limits_heap_limit (data_state_limits s) < n2 + k) /\
       data_to_word_gcProof_state_rel c l1 l2 (data_state_space_fupd (K 0) s)
         (wl_state_stack_fupd (K stack)
            (wl_state_store_fupd (K st) (wl_state_memory_fupd (K m) t))) NONE locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_def] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `join_env (data_state_locals (s:(C,FFI)data_state))
     (toAList (inter (wl_state_locals (t:(A,C,FFI)wl_state))
       (adjust_set (data_state_locals s)))) = []`
    (fun th -> RULE_ASSUM_TAC(CASE_REWRITE_RULE[th; APPEND])) THENL
   [ASM_REWRITE_TAC[GCP3AUX_toAList_inter_adjust_set_LN; join_env_NIL]; ALL_TAC] THEN
  ABBREV_TAC `FL = data_to_word_gcProof_flat (data_state_stack (s:(C,FFI)data_state))
                     (wl_state_stack (t:(A,C,FFI)wl_state))` THEN
  SUBGOAL_THEN `ALL loc_ok (MAP SND (FL:(data_v#A word_loc)list)) /\
                ALL loc_ok (wl_enc_stack (wl_state_stack (t:(A,C,FFI)wl_state)))`
    STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP GCP3AUX_word_ml_inv_loc_ok o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "word_ml_inv")) (concl th))) THEN
    REWRITE_TAC[MAP; ALL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`data_state_stack (s:(C,FFI)data_state)`;
                   `wl_state_stack (t:(A,C,FFI)wl_state)`] stack_rel_imp_subset) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ALL loc_ok (MAP SND (FL:(data_v#A word_loc)list))` THEN
    REWRITE_TAC[GSYM ALL_MEM; SUBSET; IN_SET_OF_LIST] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `a:num`; `sp:num`; `sp1:num`; `gens:gen_state`; `c:data_to_word_config`;
    `wl_state_store (t:(A,C,FFI)wl_state)`; `wl_state_memory (t:(A,C,FFI)wl_state)`;
    `wl_state_mdomain (t:(A,C,FFI)wl_state)`; `limit:num`; `wl_state_be (t:(A,C,FFI)wl_state)`;
    `THE (data_state_tstamps (s:(C,FFI)data_state))`; `data_state_refs (s:(C,FFI)data_state)`;
    `the_global (data_state_global (s:(C,FFI)data_state))`; `FL:(data_v#A word_loc)list`;
    `k:num`; `t:(A,C,FFI)wl_state`] word_gc_fun_correct) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `stack1:(A word_loc)list` (X_CHOOSE_THEN `m1:A word->A word_loc`
    (X_CHOOSE_THEN `s1:(store_name,A word_loc)fmap`
    (X_CHOOSE_THEN `heap1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`
    (X_CHOOSE_THEN `a1:num` (X_CHOOSE_THEN `sp1':num` (X_CHOOSE_THEN `sp2:num`
    (X_CHOOSE_THEN `gens2:gen_state` (X_CHOOSE_THEN `v1:(A word_loc)heap_address`
    (X_CHOOSE_THEN `xs:((A word_loc)heap_address)list` STRIP_ASSUME_TAC)))))))))) THEN
  SUBGOAL_THEN `word_gc_fun c (wl_enc_stack (wl_state_stack (t:(A,C,FFI)wl_state)),
       wl_state_memory t,wl_state_mdomain t,wl_state_store t) =
     SOME (loc_merge (wl_enc_stack (wl_state_stack t)) (FILTER isWord stack1),m1,s1)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC word_gc_fun_loc_merge THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`data_state_stack (s:(C,FFI)data_state)`;
                   `wl_state_stack (t:(A,C,FFI)wl_state)`] FILTER_enc_stack_lemma) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC word_gc_fun_IMP_FILTER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP word_gc_fun_IMP o check (fun th ->
    is_eq (concl th) && can (find_term ((=) `MAP SND (FL:(data_v#A word_loc)list)`)) (concl th))) THEN
  MP_TAC(ISPECL [`wl_state_stack (t:(A,C,FFI)wl_state)`; `FILTER isWord (stack1:(A word_loc)list)`]
           dec_stack_loc_merge_enc_stack) THEN
  DISCH_THEN(X_CHOOSE_TAC `stack:((A)stack_frame)list`) THEN
  MP_TAC(ISPECL [`wl_state_stack (t:(A,C,FFI)wl_state)`; `FILTER isWord (stack1:(A word_loc)list)`;
    `data_state_stack (s:(C,FFI)data_state)`; `stack:((A)stack_frame)list`; `locs:(num#num)list`]
    stack_rel_dec_stack_IMP_stack_rel) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `data_to_word_gcProof_flat (data_state_stack (s:(C,FFI)data_state)) (stack:((A)stack_frame)list) =
                ZIP (MAP FST (FL:(data_v#A word_loc)list)) (stack1:(A word_loc)list)` ASSUME_TAC THENL
   [EXPAND_TAC "FL" THEN MATCH_MP_TAC word_gc_fun_EL_lemma THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP word_gc_IMP_EVERY2 o check (fun th ->
      is_eq (concl th) && can (find_term ((=) `MAP SND (FL:(data_v#A word_loc)list)`)) (concl th))) THEN
    MATCH_MP_TAC MONO_ALL2 THEN REWRITE_TAC[] THEN
    GEN_TAC THEN GEN_TAC THEN CASES_ON `x:A word_loc` THEN
    REWRITE_TAC[isWord_def; is_gc_word_const_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`loc_merge (wl_enc_stack (wl_state_stack (t:(A,C,FFI)wl_state)))
       (FILTER isWord (stack1:(A word_loc)list))`;
    `m1:A word->A word_loc`; `s1:(store_name,A word_loc)fmap`; `stack:((A)stack_frame)list`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "wl_has_space")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `limits_heap_limit (data_state_limits (s:(C,FFI)data_state)) = limit`
      SUBST1_TAC THENL
     [MATCH_MP_TAC (INST_TYPE [`:A`,`:A`] GCP3AUX_heap_limit_eq) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `limits_inv (data_state_limits (s:(C,FFI)data_state))
        (FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) HeapLength)
        (wl_state_stack_limit t) (data_to_word_config_len_size c)
        (data_to_word_config_has_fp_ops c) (data_to_word_config_has_fp_tern c)` THEN
      UNDISCH_TAC `heap_in_memory_store
        (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
        a sp sp1 gens c (wl_state_store (t:(A,C,FFI)wl_state)) (wl_state_memory t)
        (wl_state_mdomain t) limit` THEN
      REWRITE_TAC[heap_in_memory_store_def; limits_inv_def] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) HeapLength =
                   SOME (wl_Word (word_mul bytes_in_word (word limit)))` THEN
      ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `MAP FST (ZIP (MAP FST (FL:(data_v#A word_loc)list)) (stack1:(A word_loc)list)) =
                  MAP FST FL` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [SUBGOAL_THEN `LENGTH (MAP FST (FL:(data_v#A word_loc)list)) = LENGTH (stack1:(A word_loc)list)`
        (fun th -> REWRITE_TAC[MATCH_MP MAP_ZIP th]) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP word_gc_fun_LENGTH o check (fun th ->
        is_eq (concl th) && can (find_term ((=) `MAP SND (FL:(data_v#A word_loc)list)`)) (concl th))) THEN
      REWRITE_TAC[LENGTH_MAP];
      ALL_TAC] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[abs_ml_inv_def] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "abs_ml_inv")) (concl th))) THEN
    MP_TAC(ISPECL [`data_state_stack (s:(C,FFI)data_state)`; `wl_state_stack (t:(A,C,FFI)wl_state)`]
             flat_PERM_extract_stack) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:data_to_word_config`; `THE (data_state_tstamps (s:(C,FFI)data_state))`;
      `CONS (the_global (data_state_global (s:(C,FFI)data_state))) (MAP FST (FL:(data_v#A word_loc)list))`;
      `data_state_refs (s:(C,FFI)data_state)`; `v1:(A word_loc)heap_address`;
      `xs:((A word_loc)heap_address)list`;
      `heap1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
      `wl_state_be (t:(A,C,FFI)wl_state)`; `limit:num`; `sp1':num`; `sp2:num`; `k:num`;
      `data_state_limits (s:(C,FFI)data_state)`; `roots2:data_v list`; `dups:data_v list`;
      `n2:num`; `r2:((data_v)bvl_ref)spt`; `s2:num_set`] GCP3AUX_gc_space_bound) THEN
    ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `limits_inv (data_state_limits (s:(C,FFI)data_state))
        (FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) HeapLength)
        (wl_state_stack_limit t) (data_to_word_config_len_size c)
        (data_to_word_config_has_fp_ops c) (data_to_word_config_has_fp_tern c)` THEN
      REWRITE_TAC[limits_inv_def] THEN MESON_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PERM_TRANS THEN
      EXISTS_TAC `APPEND (APPEND dups (FLAT (MAP extract_stack (data_state_stack (s:(C,FFI)data_state)))))
                    [the_global (data_state_global s)]` THEN
      ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN MATCH_MP_TAC PERM_CONG THEN
      REWRITE_TAC[PERM_REFL] THEN MATCH_MP_TAC PERM_TRANS THEN
      EXISTS_TAC `CONS (the_global (data_state_global (s:(C,FFI)data_state)))
                    (FLAT (MAP extract_stack (data_state_stack s)))` THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`FLAT (MAP extract_stack (data_state_stack (s:(C,FFI)data_state)))`;
                       `[the_global (data_state_global (s:(C,FFI)data_state))]`] PERM_APPEND) THEN
        REWRITE_TAC[APPEND];
        MATCH_MP_TAC PERM_MONO THEN ONCE_REWRITE_TAC[PERM_SYM] THEN ASM_REWRITE_TAC[]];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP PERM_LIST_TO_SET o check (fun th ->
        can (find_term ((=) `MAP FST (FL:(data_v#A word_loc)list)`)) (concl th) &&
        is_comb (concl th) && fst(strip_comb (concl th)) = `PERM:data_v list->data_v list->bool`)) THEN
      UNDISCH_TAC `set_of_list (dups:data_v list) SUBSET
        set_of_list (APPEND (FLAT (MAP extract_stack (data_state_stack (s:(C,FFI)data_state))))
                       [the_global (data_state_global s)])` THEN
      REWRITE_TAC[SET_OF_LIST_APPEND; set_of_list] THEN SET_TAC[]];
    REWRITE_TAC[(record_info "wl_state").ri_accfupds; (record_info "data_state").ri_accfupds;
                K_THM] THEN
    ASM_REWRITE_TAC[ALL] THEN
    ASM_SIMP_TAC[GCP3AUX_code_oracle_rel_store] THEN
    MP_TAC(ISPECL [`data_state_stack (s:(C,FFI)data_state)`; `stack:((A)stack_frame)list`]
             stack_rel_IMP_size_of_stack) THEN
    MP_TAC(ISPECL [`data_state_stack (s:(C,FFI)data_state)`;
                   `wl_state_stack (t:(A,C,FFI)wl_state)`] stack_rel_IMP_size_of_stack) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC GCP3AUX_code_oracle_rel_store_IMP THEN
      EXISTS_TAC `wl_state_store (t:(A,C,FFI)wl_state)` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack (t:(A,C,FFI)wl_state)))
                     (wl_state_locals_size t)) (wl_state_stack_max t)` THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC
       [`heap1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
        `limit:num`; `a1:num`; `sp1':num`; `sp2:num`; `gens2:gen_state`] THEN
      ASM_REWRITE_TAC[LE_0] THEN
      CASE_REWRITE_TAC[GCP3AUX_toAList_inter_adjust_set_LN; join_env_NIL; APPEND] THEN
      REWRITE_TAC[word_ml_inv_def] THEN EXISTS_TAC `CONS (v1:(A word_loc)heap_address) xs` THEN
      ASM_REWRITE_TAC[MAP; ALL2]]]);;

(* HOL4 line 7544 *)
let cut_locals_def = cake_def
  `cut_locals names (s:(A,B)data_state) =
     match data_cut_env names (data_state_locals s) with
       SOME env -> data_state_locals_fupd (K env) s
     | NONE -> data_state_locals_fupd (K LN) s`;;

(* HOL4 line 7551 *)
let size_of_heap_call_push_env = prove
 (`!names (s:(C,FFI)data_state) x ss.
     data_cut_env names (data_state_locals s) = SOME x ==>
     size_of_heap (data_call_env [] ss (data_push_env x F s)) =
     size_of_heap (data_state_locals_fupd (K x) s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[size_of_heap_def; stack_to_vs_def; data_call_env_def; data_push_env_def;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  SIMP[extract_stack_def; MAP; FLAT; APPEND; fromList_def; FOLDL; GCP3AUX_toList_clauses;
       APPEND_ASSOC]);;

(* GCP3AUX: state_rel looks at all fields of the data state but           *)
(* safe_for_space and peak_heap_length                                      *)
let GCP3AUX_state_rel_data_cong = prove
 (`!c l1 l2 (s1:(C,FFI)data_state) s2 (t:(A,C,FFI)wl_state) v locs.
     data_state_ffi s1 = data_state_ffi s2 /\ data_state_clock s1 = data_state_clock s2 /\
     data_state_handler s1 = data_state_handler s2 /\
     data_state_code s1 = data_state_code s2 /\
     data_state_compile s1 = data_state_compile s2 /\
     data_state_compile_oracle s1 = data_state_compile_oracle s2 /\
     data_state_tstamps s1 = data_state_tstamps s2 /\
     data_state_locals s1 = data_state_locals s2 /\
     data_state_stack s1 = data_state_stack s2 /\
     data_state_stack_max s1 = data_state_stack_max s2 /\
     data_state_stack_frame_sizes s1 = data_state_stack_frame_sizes s2 /\
     data_state_locals_size s1 = data_state_locals_size s2 /\
     data_state_limits s1 = data_state_limits s2 /\
     data_state_refs s1 = data_state_refs s2 /\
     data_state_space s1 = data_state_space s2 /\
     data_state_global s1 = data_state_global s2 ==>
     (data_to_word_gcProof_state_rel c l1 l2 s1 t v locs <=>
      data_to_word_gcProof_state_rel c l1 l2 s2 t v locs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_def] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 7559 (the unused existentials w1 w2 are left out) *)
let gc_lemma_gen = prove
 (`!l1 l2 ss y (t:(A,C,FFI)wl_state) names (s:(C,FFI)data_state) x c locs k.
     let t0 = wl_call_env [wl_Loc l1 l2] ss
                (wl_push_env y (NONE:(num#(A)wl_prog#num#num)option) t) in
     data_cut_env names (data_state_locals s) = SOME x /\
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     FLOOKUP (wl_state_store t) AllocSize = SOME (wl_Word (alloc_size k)) /\
     cut_envs (adjust_sets names) (wl_state_locals t) = SOME y ==>
     ?t2 wl m st stack.
       wl_state_gc_fun t0 (wl_enc_stack (wl_state_stack t0),wl_state_memory t0,
                           wl_state_mdomain t0,wl_state_store t0) =
         SOME (wl,m,st) /\
       wl_dec_stack wl (wl_state_stack t0) = SOME stack /\
       wl_pop_env (wl_state_stack_fupd (K stack)
                     (wl_state_store_fupd (K st) (wl_state_memory_fupd (K m) t0))) =
         SOME t2 /\
       FLOOKUP (wl_state_store t2) (Temp (word 29)) =
         FLOOKUP (wl_state_store t) (Temp (word 29)) /\
       FLOOKUP (wl_state_store t2) AllocSize = SOME (wl_Word (alloc_size k)) /\
       (wl_has_space (wl_Word ((alloc_size k):A word)) t2 = SOME F /\
        ~(data_to_word_config_gc_kind c = data_to_word_None) /\
        no_thunks_in_refs (data_state_refs s) ==>
        !roots2 dups n2 r2 s2.
          PERM roots2 (APPEND (APPEND (APPEND dups (toList x))
                         (FLAT (MAP extract_stack (data_state_stack s))))
                         [the_global (data_state_global s)]) /\
          set_of_list dups SUBSET
            set_of_list (APPEND (APPEND (toList x)
                           (FLAT (MAP extract_stack (data_state_stack s))))
                           [the_global (data_state_global s)]) /\
          size_of (data_state_limits s) roots2 (data_state_refs s) LN = (n2,r2,s2) ==>
          limits_heap_limit (data_state_limits s) < n2 + k) /\
       data_to_word_gcProof_state_rel c l1 l2
         (data_state_locals_fupd (K x) (data_state_space_fupd (K 0)
            (data_state_stack_max_fupd
               (K (OPTION_MAP2 MAX
                    (OPTION_MAP2 MAX (data_state_stack_max s)
                       (size_of_stack (CONS (data_Env (data_state_locals_size s) x)
                                            (data_state_stack s))))
                    (OPTION_MAP2 (+)
                       (size_of_stack (CONS (data_Env (data_state_locals_size s) x)
                                            (data_state_stack s))) ss))) s)))
         t2 NONE locs`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`NONE:(num#(A)wl_prog#num#num)option`; `c:data_to_word_config`;
    `l1:num`; `l2:num`;
    `data_state_clock_fupd (K (data_state_clock s + 1)) (s:(C,FFI)data_state)`;
    `wl_state_clock_fupd (K (wl_state_clock t + 1)) (t:(A,C,FFI)wl_state)`;
    `locs:(num#num)list`; `[]:num list`; `[]:data_v list`; `[]:(A word_loc)list`;
    `names:num_set`; `x:data_v spt`; `y:(A word_loc)spt#(A word_loc)spt`;
    `l1:num`; `l2:num`; `ss:num option`] state_rel_call_env_push_env) THEN
  REWRITE_TAC[data_to_word_gcProof_dec_clock_inc_clock; MAP; data_get_vars_def;
              wl_get_vars_def; IS_SOME_DEF] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[state_rel_inc_clock] THEN SIMP[] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`;
    `data_call_env [] ss (data_push_env x F (s:(C,FFI)data_state))`;
    `wl_call_env [wl_Loc l1 l2] ss (wl_push_env y NONE (t:(A,C,FFI)wl_state))`;
    `CONS (l1,l2) locs:(num#num)list`; `k:num`] state_rel_gc_gen) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[data_call_env_def; wl_call_env_def; data_push_env_def; wl_push_env_def;
                LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN GCP3AUX_PAIRARG_TAC THEN
    SIMP[fromList_def; fromList2_def; FOLDL] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[insert_def] THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `wl:(A word_loc)list` (X_CHOOSE_THEN `m:A word->A word_loc`
    (X_CHOOSE_THEN `st:(store_name,A word_loc)fmap`
    (X_CHOOSE_THEN `stack:((A)stack_frame)list` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(CAKE_SIMP_CONV[data_pop_env_def; data_call_env_def; data_push_env_def;
                        LET_DEF; LET_END_DEF]
    `data_pop_env (data_state_space_fupd (K 0)
       (data_call_env [] ss (data_push_env x F (s:(C,FFI)data_state))))`) THEN
  DISCH_TAC THEN
  FIRST_ASSUM(fun pe -> if is_eq (concl pe) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "data_pop_env")) (lhs (concl pe))
    then FIRST_ASSUM(fun sr -> MP_TAC(MATCH_MP state_rel_pop_env_IMP (CONJ sr pe)))
    else NO_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)wl_state` (X_CHOOSE_THEN `l8:num`
    (X_CHOOSE_THEN `l9:num` (X_CHOOSE_THEN `ll:(num#num)list` STRIP_ASSUME_TAC)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONS_11; PAIR_EQ]) THEN GCP3AUX_SPLIT_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP wl_pop_env_const) THEN
  MAP_EVERY EXISTS_TAC [`t2:(A,C,FFI)wl_state`; `wl:(A word_loc)list`;
    `m:A word->A word_loc`; `st:(store_name,A word_loc)fmap`; `stack:((A)stack_frame)list`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      can (find_term ((=) `Temp (word 29)`)) (concl th))) THEN SIMP[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `FLOOKUP (st:(store_name,A word_loc)fmap) AllocSize`)) THEN SIMP[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "wl_has_space")) (concl th))) THEN
    REWRITE_TAC[wl_has_space_def; wl_get_store_def] THEN ASM_REWRITE_TAC[] THEN
    SIMP[data_call_env_def; data_push_env_def; LET_DEF; LET_END_DEF; extract_stack_def;
         MAP; FLAT; APPEND_ASSOC];
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `t2:(A,C,FFI)wl_state`)) (concl th) &&
      can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "data_to_word_gcProof_state_rel")) (concl th))) THEN
    MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN
    MATCH_MP_TAC GCP3AUX_state_rel_data_cong THEN
    REWRITE_TAC[(record_info "data_state").ri_accfupds; K_THM]]);;

(* GCP3AUX: the stack bound of a call with no extra stack space *)
let GCP3AUX_OPTION_MAP2_MAX_ADD0 = prove
 (`!a b. OPTION_MAP2 MAX (OPTION_MAP2 MAX a b) (OPTION_MAP2 (+) b (SOME 0)) =
         OPTION_MAP2 MAX a b`,
  REPEAT GEN_TAC THEN CASES_ON `a:num option` THEN CASES_ON `b:num option` THEN
  REWRITE_TAC[OPTION_MAP2_THM; ADD_CLAUSES; option_INJ] THEN ARITH_TAC);;

(* GCP3AUX: pop_env does not look at the locals or their size *)
let GCP3AUX_pop_env_locals = prove
 (`!(s:(A,C,FFI)wl_state) X Y.
     wl_pop_env (wl_state_locals_fupd (K X) (wl_state_locals_size_fupd (K Y) s)) =
     wl_pop_env s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_pop_env_def] THEN SIMP[] THEN
  CASES_ON `wl_state_stack (s:(A,C,FFI)wl_state)` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a0:(A)stack_frame` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a3:(num#num#num)option` THEN CASE_REWRITE_TAC[] THEN
  TRY(GCP3AUX_PAIRARG_TAC THEN GCP3AUX_PAIRARG_TAC) THEN SIMP[]);;

(* GCP3AUX: neither does flush_state *)
let GCP3AUX_flush_state_locals = prove
 (`!b (s:(A,C,FFI)wl_state) X Y.
     wl_flush_state b (wl_state_locals_fupd (K X) (wl_state_locals_size_fupd (K Y) s)) =
     wl_flush_state b s`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[wl_flush_state_def] THEN SIMP[]);;

(* HOL4 line 7644 *)
let gc_add_call_env = prove
 (CASE_TERM
  `!y (t5:(A,C,FFI)wl_state) x f (res:((A)wl_result)option) t l1 l2.
     (match wl_gc (wl_push_env y NONE t5) with
        NONE -> (SOME wl_Error,x)
      | SOME s' -> (match wl_pop_env s' with
                      NONE -> (SOME wl_Error,wl_flush_state T s')
                    | SOME s' -> f s')) = (res,t) ==>
     (match wl_gc (wl_call_env [wl_Loc l1 l2] (SOME 0) (wl_push_env y NONE t5)) with
        NONE -> (SOME wl_Error,x)
      | SOME s' -> (match wl_pop_env s' with
                      NONE -> (SOME wl_Error,wl_flush_state T s')
                    | SOME s' -> f s')) = (res,t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wl_gc_def; wl_call_env_def; wl_push_env_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  GCP3AUX_PAIRARG_TAC THEN SIMP[GCP3AUX_OPTION_MAP2_MAX_ADD0] THEN
  CASE_TAC THEN CASE_REWRITE_TAC[] THEN
  REPEAT GCP3AUX_PAIRARG_TAC THEN CASE_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[GCP3AUX_pop_env_locals; GCP3AUX_flush_state_locals]);;

(* HOL4 line 7664 *)
let has_space_state_rel = prove
 (`!k (r:(A,C,FFI)wl_state) c l1 l2 (s:(C,FFI)data_state) locs.
     wl_has_space (wl_Word ((alloc_size k):A word)) r = SOME T /\
     data_to_word_gcProof_state_rel c l1 l2 s r NONE locs ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_state_space_fupd (K k) s) r NONE locs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_def] THEN STRIP_TAC THEN
  REWRITE_TAC[(record_info "data_state").ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC
   [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp:num`; `sp1:num`; `gens:gen_state`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC alloc_size_LEQ_IMP THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `wl_has_space (wl_Word ((alloc_size k):A word)) (r:(A,C,FFI)wl_state) = SOME T` THEN
    UNDISCH_TAC `heap_in_memory_store
        (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list)
        a sp sp1 gens c (wl_state_store (r:(A,C,FFI)wl_state)) (wl_state_memory r)
        (wl_state_mdomain r) limit` THEN
    REWRITE_TAC[heap_in_memory_store_def; wl_has_space_def; wl_get_store_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_INJ] THEN
    REWRITE_TAC[WORD_RULE `word_sub (word_add c (word_mul b (word (a + sp))))
                             (word_add c (word_mul b (word a))) = word_mul b (word sp):A word`] THEN
    REWRITE_TAC[word_ule; relational2] THEN MESON_TAC[];
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP word_ml_inv_SP_LIMIT o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "word_ml_inv")) (concl th))) THEN
    MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `(limit + 3) * dimindex (:A) DIV 8` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

(* HOL4 line 7686 *)
let evaluate_IMP_inc_clock = prove
 (`!q (t:(A,C,FFI)wl_state) t1 ck.
     wl_evaluate (q,t) = (NONE,t1) ==>
     wl_evaluate (q,data_to_word_gcProof_inc_clock ck t) =
       (NONE,data_to_word_gcProof_inc_clock ck t1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[data_to_word_gcProof_inc_clock_def] THEN
  MATCH_MP_TAC wl_evaluate_add_clock THEN ASM_REWRITE_TAC[option_DISTINCT]);;

(* HOL4 line 7694 *)
let evaluate_IMP_inc_clock_Ex = prove
 (`!q (t:(A,C,FFI)wl_state) x y t1 ck.
     wl_evaluate (q,t) = (SOME (wl_Exception x y),t1) ==>
     wl_evaluate (q,data_to_word_gcProof_inc_clock ck t) =
       (SOME (wl_Exception x y),data_to_word_gcProof_inc_clock ck t1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[data_to_word_gcProof_inc_clock_def] THEN
  MATCH_MP_TAC wl_evaluate_add_clock THEN ASM_REWRITE_TAC[option_INJ; distinctness "wl_result"]);;

(* HOL4 line 7702 *)
let get_var_inc_clock = prove
 (`!n k (s:(A,C,FFI)wl_state).
     wl_get_var n (data_to_word_gcProof_inc_clock k s) = wl_get_var n s`,
  REWRITE_TAC[wl_get_var_def; data_to_word_gcProof_inc_clock_def] THEN SIMP[]);;

(* HOL4 line 7708 *)
let get_vars_inc_clock = prove
 (`!n k (s:(A,C,FFI)wl_state).
     wl_get_vars n (data_to_word_gcProof_inc_clock k s) = wl_get_vars n s`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[wl_get_vars_def; get_var_inc_clock]);;

(* HOL4 line 7715 *)
let set_var_inc_clock = prove
 (`!n x ck (t:(A,C,FFI)wl_state).
     wl_set_var n x (data_to_word_gcProof_inc_clock ck t) =
     data_to_word_gcProof_inc_clock ck (wl_set_var n x t)`,
  REWRITE_TAC[wl_set_var_def; data_to_word_gcProof_inc_clock_def] THEN SIMP[]);;

(* HOL4 line 7721: val do_app = LIST_CONJ [...] (a simp list of definitions, *)
(* not stated)                                                               *)

(* HOL4 line 7726 *)
let w2n_minus_1_LESS_EQ = prove
 (`!w:A word. (val (word_neg (word 1):A word) <= val w) <=> word_add w (word 1) = word 0`,
  GEN_TAC THEN REWRITE_TAC[w2n_minus1] THEN EQ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `w = word_neg (word 1):A word` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ; w2n_minus1] THEN MP_TAC(ISPEC `w:A word` VAL_BOUND) THEN
      REWRITE_TAC[GSYM dimword_def] THEN ASM_ARITH_TAC;
      CONV_TAC WORD_RULE];
    SUBGOAL_THEN `w = word_neg (word 1):A word` SUBST1_TAC THENL
     [MP_TAC(AP_THM (AP_TERM `word_add:A word->A word->A word`
        (ASSUME `word_add w (word 1) = word 0:A word`)) `word_neg (word 1):A word`) THEN
      REWRITE_TAC[WORD_RULE `word_add (word_add w (word 1)) (word_neg (word 1)):A word = w`;
                  WORD_RULE `word_add (word 0) x:A word = x`];
      REWRITE_TAC[w2n_minus1; LE_REFL]]]);;

(* HOL4 line 7735 *)
let bytes_in_word_ADD_1_NOT_ZERO = prove
 (`!w:A word. good_dimindex (:A) ==>
              ~(word_add (word_mul bytes_in_word w) (word 1) = word 0)`,
  GEN_TAC THEN DISCH_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `bit 0:A word->bool`) THEN
  REWRITE_TAC[WORD_ADD_BIT0; WORD_MUL_BIT0; bytes_in_word_def; BIT_WORD_0; BIT_WORD_1] THEN
  REWRITE_TAC[BIT_WORD; EXP; DIV_1; DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> 0 < n`] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o REWRITE_RULE[good_dimindex_def]) THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 7746 *)
let option_le_OPTION_MAP2_MAX = prove
 (`!n m. option_le (OPTION_MAP2 MAX n m) n = option_le m n /\
         option_le (OPTION_MAP2 MAX m n) n = option_le m n`,
  REPEAT GEN_TAC THEN CASES_ON `n:num option` THEN CASES_ON `m:num option` THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_le_def] THEN ARITH_TAC);;

(* GCP3AUX: the stack_max after the call_env and push_env of alloc stays below sm *)
let GCP3AUX_call_env_push_env_stack_max = prove
 (`!(t5:(A,C,FFI)wl_state) (y1:(A word_loc)spt) y2 l1 l2 sm.
     option_le (OPTION_MAP2 (+) (wl_stack_size (wl_state_stack t5)) (wl_state_locals_size t5))
       (wl_state_stack_max t5) /\
     option_le (wl_state_stack_max t5) sm ==>
     option_le (wl_state_stack_max (wl_call_env [wl_Loc l1 l2] (SOME 0)
                  (wl_push_env (y1,y2) NONE t5))) sm`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_call_env_def; wl_push_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN GCP3AUX_PAIRARG_TAC THEN
  REWRITE_TAC[(record_info "wl_state").ri_accfupds; K_THM; GCP3AUX_OPTION_MAP2_MAX_ADD0] THEN
  REWRITE_TAC[option_le_max; wl_stack_size_def; ITLIST; o_THM; stack_size_frame_def] THEN
  MESON_TAC[option_le_trans; option_add_comm]);;

(* GCP3AUX: under state_rel, has_space of a word is defined *)
let GCP3AUX_state_rel_has_space_SOME = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs (w:A word).
     data_to_word_gcProof_state_rel c l1 l2 s t v locs ==>
     ?b. wl_has_space (wl_Word w) t = SOME b`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_def; heap_in_memory_store_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[wl_has_space_def; wl_get_store_def] THEN
  CASE_REWRITE_TAC[option_INJ] THEN MESON_TAC[]);;

(* GCP3AUX: under state_rel, has_space never holds for the word -1 *)
let GCP3AUX_has_space_T_not_minus1 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs (w:A word).
     data_to_word_gcProof_state_rel c l1 l2 s t v locs ==>
     wl_has_space (wl_Word w) t = SOME T ==> ~(w = word_neg (word 1))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_def; heap_in_memory_store_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[wl_has_space_def; wl_get_store_def] THEN
  CASE_REWRITE_TAC[option_INJ] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add c (word_mul b (word (a + sp))))
                           (word_add c (word_mul b (word a))) = word_mul b (word sp):A word`] THEN
  DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[w2n_minus_1_LESS_EQ] o check (fun th ->
    can (find_term ((=) `word_neg (word 1):A word`)) (concl th))) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC bytes_in_word_ADD_1_NOT_ZERO THEN ASM_REWRITE_TAC[]);;

(* GCP3AUX: state_rel only bounds the stack_max of the data state from below *)
let GCP3AUX_state_rel_stack_max_le = prove
 (`!c l1 l2 (s1:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs s2.
     data_to_word_gcProof_state_rel c l1 l2 s1 t v locs ==>
     data_state_ffi s1 = data_state_ffi s2 /\ data_state_clock s1 = data_state_clock s2 /\
     data_state_handler s1 = data_state_handler s2 /\
     data_state_code s1 = data_state_code s2 /\
     data_state_compile s1 = data_state_compile s2 /\
     data_state_compile_oracle s1 = data_state_compile_oracle s2 /\
     data_state_tstamps s1 = data_state_tstamps s2 /\
     data_state_locals s1 = data_state_locals s2 /\
     data_state_stack s1 = data_state_stack s2 /\
     data_state_stack_frame_sizes s1 = data_state_stack_frame_sizes s2 /\
     data_state_locals_size s1 = data_state_locals_size s2 /\
     data_state_limits s1 = data_state_limits s2 /\
     data_state_refs s1 = data_state_refs s2 /\
     data_state_space s1 = data_state_space s2 /\
     data_state_global s1 = data_state_global s2 /\
     option_le (wl_state_stack_max t) (data_state_stack_max s2) ==>
     data_to_word_gcProof_state_rel c l1 l2 s2 t v locs`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 (s1:(C,FFI)data_state)
    (t:(A,C,FFI)wl_state) v locs` THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* GCP3AUX: recognise a state_rel assumption about the word state t *)
let gcp3aux_is_state_rel_of t th =
  let f,args = strip_comb (concl th) in
  is_const f && fst(dest_const f) = "data_to_word_gcProof_state_rel" &&
  length args = 7 && el 4 args = t;;

(* HOL4 line 7753 *)
let alloc_lemma_gen = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs names x k q r.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_cut_env names (data_state_locals s) = SOME x /\
     wl_alloc (alloc_size k) (adjust_sets names) t = ((q:((A)wl_result)option),r) ==>
     (q = SOME NotEnoughSpace ==>
      wl_state_ffi r = data_state_ffi s /\
      option_le (wl_state_stack_max r) (data_state_stack_max s) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) /\
       no_thunks_in_refs (data_state_refs s) ==>
       !roots2 dups n2 r2 s2.
         PERM roots2 (APPEND (APPEND (APPEND dups (toList x))
                        (FLAT (MAP extract_stack (data_state_stack s))))
                        [the_global (data_state_global s)]) /\
         set_of_list dups SUBSET
           set_of_list (APPEND (APPEND (toList x)
                          (FLAT (MAP extract_stack (data_state_stack s))))
                          [the_global (data_state_global s)]) /\
         size_of (data_state_limits s) roots2 (data_state_refs s) LN = (n2,r2,s2) ==>
         limits_heap_limit (data_state_limits s) < n2 + k)) /\
     (~(q = SOME NotEnoughSpace) ==>
      data_to_word_gcProof_state_rel c l1 l2
        (data_state_locals_fupd (K x) (data_state_space_fupd (K k) s)) r NONE locs /\
      ~(alloc_size k = word_neg (word 1):A word) /\
      FLOOKUP (wl_state_store r) (Temp (word 29)) =
        FLOOKUP (wl_state_store t) (Temp (word 29)) /\
      wl_state_code r = wl_state_code t /\
      wl_state_code_buffer r = wl_state_code_buffer t /\
      wl_state_data_buffer r = wl_state_data_buffer t /\
      wl_state_compile_oracle r = wl_state_compile_oracle t /\
      q = NONE)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP alloc_code_gc_fun_const o check (fun th ->
    is_eq (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "wl_alloc")) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "wl_alloc")) (concl th))) THEN
  REWRITE_TAC[wl_alloc_def] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `names:num_set`; `x:data_v spt`]
    cut_env_IMP_cut_env) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `yy:(A word_loc)spt` (MP_TAC o MATCH_MP cut_env_IMP_cut_envs)) THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:(A word_loc)spt` (X_CHOOSE_THEN `y2:(A word_loc)spt`
    STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o SPECL [`l1:num`; `l2:num`] o MATCH_MP gc_add_call_env) THEN
  ABBREV_TAC `t5 = wl_set_store AllocSize (wl_Word (alloc_size k)) (t:(A,C,FFI)wl_state)` THEN
  SUBGOAL_THEN `data_to_word_gcProof_state_rel c l1 l2 s (t5:(A,C,FFI)wl_state) NONE locs`
    ASSUME_TAC THENL
   [EXPAND_TAC "t5" THEN REWRITE_TAC[state_rel_set_store_AllocSize] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l1:num`; `l2:num`; `SOME 0`; `(y1,y2):(A word_loc)spt#(A word_loc)spt`;
    `t5:(A,C,FFI)wl_state`; `names:num_set`; `s:(C,FFI)data_state`; `x:data_v spt`;
    `c:data_to_word_config`; `locs:(num#num)list`; `k:num`] gc_lemma_gen) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "t5" THEN
    REWRITE_TAC[wl_set_store_def] THEN SIMP[FLOOKUP_UPDATE] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)wl_state` (X_CHOOSE_THEN `wl:(A word_loc)list`
    (X_CHOOSE_THEN `m:A word->A word_loc` (X_CHOOSE_THEN `st:(store_name,A word_loc)fmap`
    (X_CHOOSE_THEN `stack:((A)stack_frame)list` STRIP_ASSUME_TAC))))) THEN
  (* the stack_max of t2 *)
  SUBGOAL_THEN `option_le (wl_state_stack_max (t2:(A,C,FFI)wl_state))
                  (data_state_stack_max (s:(C,FFI)data_state))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP wl_pop_env_const o check (fun th -> is_eq (concl th) &&
      rand(concl th) = `SOME (t2:(A,C,FFI)wl_state)`)) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[(record_info "wl_state").ri_accfupds; K_THM] THEN
    MATCH_MP_TAC GCP3AUX_call_env_push_env_stack_max THEN
    UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 s (t5:(A,C,FFI)wl_state) NONE locs` THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* has_space of t2 is defined *)
  FIRST_ASSUM(MP_TAC o SPEC `alloc_size k:A word` o MATCH_MP GCP3AUX_state_rel_has_space_SOME o
    check (gcp3aux_is_state_rel_of `t2:(A,C,FFI)wl_state`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:bool` ASSUME_TAC) THEN
  (* the alloc case expression in terms of t2 *)
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rand (concl th) = `(q:((A)wl_result)option),(r:(A,C,FFI)wl_state)`)) THEN
  REWRITE_TAC[wl_gc_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  GCP3AUX_ASM_CASE_TAC THEN REWRITE_TAC[wl_get_store_def] THEN GCP3AUX_ASM_CASE_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
    `wl_has_space (wl_Word (alloc_size k:A word)) (t2:(A,C,FFI)wl_state) = SOME b`)) THEN
  BOOL_CASES_TAC `b:bool` THEN DISCH_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[option_INJ; distinctness "option"; distinctness "wl_result"] THENL
   [(* enough space: the state relation with space k *)
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP has_space_state_rel o CONJ (ASSUME
        `wl_has_space (wl_Word (alloc_size k:A word)) (t2:(A,C,FFI)wl_state) = SOME T`) o
        check (gcp3aux_is_state_rel_of `t2:(A,C,FFI)wl_state`)) THEN
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP GCP3AUX_state_rel_stack_max_le) THEN
      ASM_REWRITE_TAC[(record_info "data_state").ri_accfupds; K_THM];
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP GCP3AUX_has_space_T_not_minus1 o
        check (gcp3aux_is_state_rel_of `t2:(A,C,FFI)wl_state`)) THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "t5" THEN REWRITE_TAC[wl_set_store_def] THEN
      SIMP[FLOOKUP_UPDATE]];
    (* not enough space *)
    REWRITE_TAC[wl_flush_state_def; (record_info "wl_state").ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o check (gcp3aux_is_state_rel_of `t2:(A,C,FFI)wl_state`)) THEN
      REWRITE_TAC[data_to_word_gcProof_state_rel_thm; (record_info "data_state").ri_accfupds;
                  K_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
        can (find_term ((=) `no_thunks_in_refs (data_state_refs (s:(C,FFI)data_state))`))
          (concl th))) THEN
      ASM_REWRITE_TAC[]]]);;

(* HOL4 line 7887 (val alloc_alt_gen: alloc_lemma_gen with its conjunct     *)
(* alloc_size k <> -1w weakened away by WEAKEN_CONSEQ_CONV_RULE)             *)
let alloc_alt_gen = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs names x k q r.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_cut_env names (data_state_locals s) = SOME x /\
     wl_alloc (alloc_size k) (adjust_sets names) t = ((q:((A)wl_result)option),r) ==>
     (q = SOME NotEnoughSpace ==>
      wl_state_ffi r = data_state_ffi s /\
      option_le (wl_state_stack_max r) (data_state_stack_max s) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) /\
       no_thunks_in_refs (data_state_refs s) ==>
       !roots2 dups n2 r2 s2.
         PERM roots2 (APPEND (APPEND (APPEND dups (toList x))
                        (FLAT (MAP extract_stack (data_state_stack s))))
                        [the_global (data_state_global s)]) /\
         set_of_list dups SUBSET
           set_of_list (APPEND (APPEND (toList x)
                          (FLAT (MAP extract_stack (data_state_stack s))))
                          [the_global (data_state_global s)]) /\
         size_of (data_state_limits s) roots2 (data_state_refs s) LN = (n2,r2,s2) ==>
         limits_heap_limit (data_state_limits s) < n2 + k)) /\
     (~(q = SOME NotEnoughSpace) ==>
      data_to_word_gcProof_state_rel c l1 l2
        (data_state_locals_fupd (K x) (data_state_space_fupd (K k) s)) r NONE locs /\
      FLOOKUP (wl_state_store r) (Temp (word 29)) =
        FLOOKUP (wl_state_store t) (Temp (word 29)) /\
      wl_state_code r = wl_state_code t /\
      wl_state_code_buffer r = wl_state_code_buffer t /\
      wl_state_data_buffer r = wl_state_data_buffer t /\
      wl_state_compile_oracle r = wl_state_compile_oracle t /\
      q = NONE)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP alloc_lemma_gen) THEN
  MESON_TAC[]);;

(* HOL4 line 7894 *)
let alloc_lemma = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs names x k q r.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_cut_env names (data_state_locals s) = SOME x /\
     wl_alloc (alloc_size k) (adjust_sets names) t = ((q:((A)wl_result)option),r) ==>
     (q = SOME NotEnoughSpace ==>
      wl_state_ffi r = data_state_ffi s /\
      option_le (wl_state_stack_max r) (data_state_stack_max s) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) /\
       no_thunks_in_refs (data_state_refs s) ==>
       limits_heap_limit (data_state_limits s) < size_of_heap (cut_locals names s) + k)) /\
     (~(q = SOME NotEnoughSpace) ==>
      data_to_word_gcProof_state_rel c l1 l2
        (data_state_locals_fupd (K x) (data_state_space_fupd (K k) s)) r NONE locs /\
      ~(alloc_size k = word_neg (word 1):A word) /\
      FLOOKUP (wl_state_store r) (Temp (word 29)) =
        FLOOKUP (wl_state_store t) (Temp (word 29)) /\
      wl_state_code r = wl_state_code t /\
      wl_state_code_buffer r = wl_state_code_buffer t /\
      wl_state_data_buffer r = wl_state_data_buffer t /\
      wl_state_compile_oracle r = wl_state_compile_oracle t /\
      q = NONE)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC(MATCH_MP alloc_lemma_gen th)) THEN
  SUBGOAL_THEN `?n2 r2 s2. size_of (data_state_limits (s:(C,FFI)data_state))
      (APPEND (APPEND (toList x) (FLAT (MAP extract_stack (data_state_stack s))))
        [the_global (data_state_global s)]) (data_state_refs s) LN = (n2,r2,s2)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `size_of_heap (cut_locals names (s:(C,FFI)data_state)) = n2` SUBST1_TAC THENL
   [REWRITE_TAC[size_of_heap_def; cut_locals_def] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[stack_to_vs_def; (record_info "data_state").ri_accfupds; K_THM;
                size_of_global_to_vs] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(fun th -> MP_TAC(MP th
      (ASSUME `q = SOME (NotEnoughSpace:(A)wl_result)`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      is_forall (snd(dest_imp(concl th))))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`APPEND (APPEND (toList x) (FLAT (MAP extract_stack (data_state_stack s))))
        [the_global (data_state_global (s:(C,FFI)data_state))]`; `[]:data_v list`;
      `r2:((data_v)bvl_ref)spt`; `s2:(1)spt`] THEN
    ASM_REWRITE_TAC[APPEND; PERM_REFL; set_of_list; EMPTY_SUBSET];
    FIRST_ASSUM ACCEPT_TAC]);;

(* GCP3AUX: an insert outside the domain of t does not change inter _ t *)
let GCP3AUX_inter_insert_NOT_IN = prove
 (`!n (w:A) s (t:B spt). ~(n IN domain t) ==> inter (insert n w s) t = inter s t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inter_eq; lookup_inter_alt; lookup_insert] THEN
  X_GEN_TAC `k:num` THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* GCP3AUX: nor cut_names t *)
let GCP3AUX_cut_names_insert_NOT_IN = prove
 (`!n (w:A) s (t:B spt).
     ~(n IN domain t) ==> cut_names t (insert n w s) = cut_names t s`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[cut_names_def; GCP3AUX_inter_insert_NOT_IN] THEN
  REWRITE_TAC[domain_insert] THEN
  SUBGOAL_THEN `domain (t:B spt) SUBSET n INSERT domain (s:A spt) <=>
                domain t SUBSET domain s` (fun th -> REWRITE_TAC[th]) THEN
  ASM SET_TAC[]);;

(* HOL4 line 7934 *)
let cut_names_adjust_set_insert_ODD = prove
 (`!n (the_names:B spt) (w:A) s.
     ODD n ==> cut_names (adjust_set the_names) (insert n w s) =
               cut_names (adjust_set the_names) s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GCP3AUX_cut_names_insert_NOT_IN THEN
  ASM_MESON_TAC[GCP3AUX_ODD_NOT_IN_domain_adjust_set]);;

(* GCP3AUX: an odd variable is not in the domain of the first cut set *)
let GCP3AUX_ODD_NOT_IN_LS = prove
 (`!n. ODD n ==> ~(n IN domain (LS one:num_set))`,
  GEN_TAC THEN REWRITE_TAC[domain_def; IN_SING] THEN
  DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `ODD 0` THEN
  REWRITE_TAC[ODD]);;

(* HOL4 line 7948 *)
let cut_env_adjust_sets_ODD = prove
 (`!n (names:B spt) (w:A) s.
     ODD n ==> wl_cut_env (adjust_sets names) (insert n w s) =
               wl_cut_env (adjust_sets names) s`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[wl_cut_env_def; cut_envs_def; adjust_sets_def;
               GCP3AUX_cut_names_insert_NOT_IN; GCP3AUX_ODD_NOT_IN_LS;
               GCP3AUX_ODD_NOT_IN_domain_adjust_set]);;

(* HOL4 line 7963 *)
let cut_envs_adjust_sets_ODD = prove
 (`!n (names:B spt) (w:A) s.
     ODD n ==> cut_envs (adjust_sets names) (insert n w s) =
               cut_envs (adjust_sets names) s`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[cut_envs_def; adjust_sets_def;
               GCP3AUX_cut_names_insert_NOT_IN; GCP3AUX_ODD_NOT_IN_LS;
               GCP3AUX_ODD_NOT_IN_domain_adjust_set]);;

(* GCP3AUX: alloc looks at the locals only through cut_envs *)
let GCP3AUX_alloc_locals_cong = prove
 (`!k names (t:(A,C,FFI)wl_state) l.
     cut_envs names l = cut_envs names (wl_state_locals t) ==>
     wl_alloc k names (wl_state_locals_fupd (K l) t) = wl_alloc k names t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_alloc_def] THEN
  SIMP[wl_set_store_with_const; wl_push_env_with_const; wl_gc_with_const;
       wl_pop_env_with_const]);;

(* HOL4 line 7976 *)
let alloc_locals_insert_1 = prove
 (`!k (names:B spt) w (t:(A,C,FFI)wl_state).
     wl_alloc k (adjust_sets names)
       (wl_state_locals_fupd (K (insert 1 w (wl_state_locals t))) t) =
     wl_alloc k (adjust_sets names) t`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC GCP3AUX_alloc_locals_cong THEN
  MATCH_MP_TAC cut_envs_adjust_sets_ODD THEN REWRITE_TAC[ODD; ARITH]);;

(* GCP3AUX: under state_rel the data space is below dimword *)
let GCP3AUX_state_rel_space_LT = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s t v locs ==>
     data_state_space s < dimword (:A)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP word_ml_inv_SP_LIMIT) THEN
  SUBGOAL_THEN `1 <= dimindex (:A) DIV 8` ASSUME_TAC THENL
   [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `limit + 3 <= (limit + 3) * (dimindex (:A) DIV 8)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x * 1 <= x * y ==> x <= x * y`) THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL];
    ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* HOL4 line 7990 *)
let evaluate_GiveUp = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs ==>
     ?r. wl_evaluate (GiveUp,t) = (SOME NotEnoughSpace,r) /\
         wl_state_ffi r = data_state_ffi s /\ wl_state_ffi t = data_state_ffi s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GiveUp_def; wl_evaluate_def; wl_word_exp_def] THEN
  CASE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
  REWRITE_TAC[wl_get_var_def; wl_set_var_def] THEN SIMP[lookup_insert] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[alloc_locals_insert_1] THEN
  SUBGOAL_THEN `good_dimindex (:A) /\
    wl_state_ffi (t:(A,C,FFI)wl_state) = data_state_ffi (s:(C,FFI)data_state)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 s (t:(A,C,FFI)wl_state) NONE locs` THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `word_neg (word 1):A word = alloc_size (dimword (:A))` SUBST1_TAC THENL
   [UNDISCH_TAC `good_dimindex (:A)` THEN REWRITE_TAC[good_dimindex_def; alloc_size_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `~(x * 4 < x)`; ARITH_RULE `~(x * 8 < x)`];
    ALL_TAC] THEN
  MP_TAC(ISPEC `wl_alloc (alloc_size (dimword (:A))) (adjust_sets (LN:num_set))
    (t:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:((A)wl_result)option` (X_CHOOSE_THEN `r:(A,C,FFI)wl_state`
    ASSUME_TAC)) THEN
  EXISTS_TAC `r:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `LN:num_set`; `LN:data_v spt`;
    `dimword(:A)`; `q:((A)wl_result)option`; `r:(A,C,FFI)wl_state`] alloc_lemma) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[data_cut_env_def; domain_def; EMPTY_SUBSET; inter_LN; mk_wf_def];
    ALL_TAC] THEN
  ASM_CASES_TAC `q = SOME (NotEnoughSpace:(A)wl_result)` THEN ASM_REWRITE_TAC[] THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o MATCH_MP GCP3AUX_state_rel_space_LT o CONJUNCT1) THEN
    REWRITE_TAC[(record_info "data_state").ri_accfupds; K_THM; LT_REFL]]);;

(* HOL4 line 8017 *)
let insert_insert_3_1 = prove
 (`!(x:A) y t. insert 3 x (insert 1 y t) = insert 1 y (insert 3 x t)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [insert_insert] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* HOL4 line 8023 *)
let shift_lsl = prove
 (`!w:A word. good_dimindex (:A) ==>
              word_shl w (backend_common_word_shift (:A)) = word_mul w bytes_in_word`,
  GEN_TAC THEN
  REWRITE_TAC[good_dimindex_def; backend_common_word_shift_def; bytes_in_word_def;
              WORD_MUL_LSL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_ACCEPT_TAC WORD_MUL_SYM);;

(* HOL4 line 8030 (val alloc_alt: alloc_lemma with its conjunct             *)
(* alloc_size k <> -1w weakened away by WEAKEN_CONSEQ_CONV_RULE)             *)
let alloc_alt = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs names x k q r.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_cut_env names (data_state_locals s) = SOME x /\
     wl_alloc (alloc_size k) (adjust_sets names) t = ((q:((A)wl_result)option),r) ==>
     (q = SOME NotEnoughSpace ==>
      wl_state_ffi r = data_state_ffi s /\
      option_le (wl_state_stack_max r) (data_state_stack_max s) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) /\
       no_thunks_in_refs (data_state_refs s) ==>
       limits_heap_limit (data_state_limits s) < size_of_heap (cut_locals names s) + k)) /\
     (~(q = SOME NotEnoughSpace) ==>
      data_to_word_gcProof_state_rel c l1 l2
        (data_state_locals_fupd (K x) (data_state_space_fupd (K k) s)) r NONE locs /\
      FLOOKUP (wl_state_store r) (Temp (word 29)) =
        FLOOKUP (wl_state_store t) (Temp (word 29)) /\
      wl_state_code r = wl_state_code t /\
      wl_state_code_buffer r = wl_state_code_buffer t /\
      wl_state_data_buffer r = wl_state_data_buffer t /\
      wl_state_compile_oracle r = wl_state_compile_oracle t /\
      q = NONE)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP alloc_lemma) THEN
  MESON_TAC[]);;

(* HOL4 line 8037 *)
let alloc_size_dimword = prove
 (`good_dimindex (:A) ==> alloc_size (dimword (:A)) = word_neg (word 1):A word`,
  REWRITE_TAC[good_dimindex_def; alloc_size_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `~(x * 4 < x)`; ARITH_RULE `~(x * 8 < x)`]);;

(* HOL4 line 8045: val alloc_fail_lemma (alloc_lemma at k = dimword (:'a),  *)
(* used only in the proof of alloc_fail; not stated)                        *)

(* HOL4 line 8051 *)
let alloc_fail = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs names x q r.
     good_dimindex (:A) /\ data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_cut_env names (data_state_locals s) = SOME x /\
     wl_alloc (word_neg (word 1):A word) (adjust_sets names) t = (q,r) ==>
     (q = SOME NotEnoughSpace ==>
      wl_state_ffi r = data_state_ffi s /\
      option_le (wl_state_stack_max r) (data_state_stack_max s)) /\
     q = SOME NotEnoughSpace`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `names:num_set`; `x:data_v spt`;
    `dimword(:A)`; `q:((A)wl_result)option`; `r:(A,C,FFI)wl_state`] alloc_lemma) THEN
  ASM_SIMP_TAC[alloc_size_dimword] THEN MESON_TAC[]);;

(* HOL4 line 8061 (HOL4: LIST_CONJ of definitions) *)
let word_exp_rw = end_itlist CONJ
  [wl_word_exp_def; word_op_def; word_sh_def; wl_get_var_def; wl_get_var_imm_def;
   the_words_def; wl_get_store_def; lookup_insert];;

(* HOL4 line 8072 *)
let data_to_word_gcProof_get_var_set_var_thm = prove
 (`!n m (x:A word_loc) (y:(A,C,FFI)wl_state).
     wl_get_var n (wl_set_var m x y) = if n = m then SOME x else wl_get_var n y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_get_var_def; wl_set_var_def] THEN SIMP[lookup_insert]);;

(* GCP3AUX: what a successful wl_cut_env with adjust_sets is *)
let GCP3AUX_wl_cut_env_adjust_sets = prove
 (`!(names:B spt) (l:A spt) y.
     wl_cut_env (adjust_sets names) l = SOME y ==>
     y = union (inter l (adjust_set names)) (inter l (LS one)) /\
     domain (adjust_set names) SUBSET domain l /\ 0 IN domain l`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wl_cut_env_def; cut_envs_def; adjust_sets_def; cut_names_def; FST; SND] THEN
  ASM_CASES_TAC `domain (LS one:num_set) SUBSET domain (l:A spt)` THEN
  ASM_CASES_TAC `domain (adjust_set (names:B spt)) SUBSET domain (l:A spt)` THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_INJ; distinctness "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `domain (LS one:num_set) SUBSET domain (l:A spt)` THEN
  REWRITE_TAC[domain_def; SING_SUBSET]);;

(* GCP3AUX: lookups in the result of such a cut *)
let GCP3AUX_lookup_cut_env_adjust_sets = prove
 (`!(names:B spt) (l:A spt) y.
     wl_cut_env (adjust_sets names) l = SOME y ==>
     lookup 0 y = lookup 0 l /\
     (!k. k IN domain (adjust_set names) ==> lookup k y = lookup k l)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP GCP3AUX_wl_cut_env_adjust_sets) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[lookup_union; lookup_inter_alt; domain_def; IN_SING] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GCP3AUX_IN_domain_adjust_set_alt] THEN
    CASES_ON `lookup 0 (l:A spt)` THEN REWRITE_TAC[option_CASE];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[GCP3AUX_IN_domain_adjust_set_alt]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASES_ON `lookup k (l:A spt)` THEN REWRITE_TAC[option_CASE]]);;

(* HOL4 line 8078 *)
let state_rel_cut_env_cut_env = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs names x y.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_cut_env names (data_state_locals s) = SOME x /\
     wl_cut_env (adjust_sets names) (wl_state_locals t) = SOME y ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_state_locals_fupd (K x) s)
       (wl_state_locals_fupd (K y) t) NONE locs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `names:num_set`; `x:data_v spt`]
    state_rel_cut_env) THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GCP3AUX_lookup_cut_env_adjust_sets) THEN
  SUBGOAL_THEN `domain (x:data_v spt) SUBSET domain (names:num_set)` ASSUME_TAC THENL
   [UNDISCH_TAC `data_cut_env names (data_state_locals (s:(C,FFI)data_state)) = SOME x` THEN
    REWRITE_TAC[data_cut_env_def] THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_INJ; distinctness "option"] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[domain_mk_wf; domain_inter] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inter (y:(A word_loc)spt) (adjust_set (x:data_v spt)) =
                inter (wl_state_locals (t:(A,C,FFI)wl_state)) (adjust_set x)` ASSUME_TAC THENL
   [REWRITE_TAC[inter_eq; lookup_inter_alt] THEN X_GEN_TAC `k:num` THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[GCP3AUX_IN_domain_adjust_set; GCP3AUX_adjust_var_IN_adjust_set; SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; (record_info "wl_state").ri_accfupds;
              (record_info "data_state").ri_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `adjust_var n IN domain (adjust_set (names:num_set))` ASSUME_TAC THENL
   [REWRITE_TAC[GCP3AUX_adjust_var_IN_adjust_set] THEN
    UNDISCH_TAC `IS_SOME (lookup n (x:data_v spt))` THEN
    REWRITE_TAC[IS_SOME_EXISTS; GSYM domain_lookup] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 8122 *)
let domain_adjust_set_EVEN = prove
 (`!k s:A spt. k IN domain (adjust_set s) ==> EVEN k`,
  REWRITE_TAC[GCP3AUX_IN_domain_adjust_set] THEN MESON_TAC[EVEN_adjust_var]);;

(* HOL4 line 8130 *)
let cut_env_adjust_sets_insert_ODD = prove
 (`!n (names:B spt) (w:A) t.
     ODD n ==>
     wl_cut_env (adjust_sets names) (insert n w t) = wl_cut_env (adjust_sets names) t`,
  MATCH_ACCEPT_TAC cut_env_adjust_sets_ODD);;

(* HOL4 line 8154 *)
let data_to_word_gcProof_cut_envs_adjust_sets_insert_ODD = prove
 (`!n (names:B spt) (w:A) t.
     ODD n ==>
     cut_envs (adjust_sets names) (insert n w t) = cut_envs (adjust_sets names) t`,
  MATCH_ACCEPT_TAC cut_envs_adjust_sets_ODD);;

(* HOL4 line 8178 *)
let cut_names_insert_1_insert_1 = prove
 (CASE_TERM
  `!(names:B spt) (w:A) t.
     cut_names (insert 1 one (adjust_set names)) (insert 1 w t) =
     match cut_names (adjust_set names) (t:A spt) with
       NONE -> NONE
     | SOME e -> SOME (insert 1 w e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_names_def; domain_insert] THEN
  SUBGOAL_THEN `(1 INSERT domain (adjust_set (names:B spt)) SUBSET 1 INSERT domain (t:A spt)) <=>
                domain (adjust_set names) SUBSET domain t` SUBST1_TAC THENL
   [MP_TAC(ISPEC `names:B spt` NOT_1_domain) THEN SET_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN CASE_REWRITE_TAC[option_INJ] THEN
  SIMP_TAC[spt_eq_thm; wf_inter; wf_insert] THEN
  REWRITE_TAC[lookup_inter_alt; lookup_insert; domain_insert; IN_INSERT] THEN
  X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[]);;

(* GCP3AUX: the collector keeps CurrHeap, TriggerGC, NextFree and HeapLength words *)
let GCP3AUX_word_gc_fun_store_words = prove
 (`!c xs (m:A word->A word_loc) dm s ys m1 s1 cu e nx hl.
     word_gc_fun c (xs,m,dm,s) = SOME (ys,m1,s1) /\
     FLOOKUP s CurrHeap = SOME (wl_Word cu) /\ FLOOKUP s TriggerGC = SOME (wl_Word e) /\
     FLOOKUP s NextFree = SOME (wl_Word nx) /\ FLOOKUP s HeapLength = SOME (wl_Word hl) ==>
     ?e nx hl cu.
       FLOOKUP s1 CurrHeap = SOME (wl_Word cu) /\ FLOOKUP s1 TriggerGC = SOME (wl_Word e) /\
       FLOOKUP s1 NextFree = SOME (wl_Word nx) /\ FLOOKUP s1 HeapLength = SOME (wl_Word hl)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_gc_fun_def] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CASES_ON `data_to_word_config_gc_kind c` THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN REPEAT GCP3AUX_PAIRARG_ASM_TAC THEN GCP3AUX_SPLIT_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  ASM SIMP[FUPDATE_LIST_THM; FLOOKUP_UPDATE] THEN MESON_TAC[]);;

(* GCP3AUX: what a successful gc is *)
let GCP3AUX_wl_gc_SOME = prove
 (`!(s:(A,C,FFI)wl_state) s2. wl_gc s = SOME s2 ==>
     ?wl m st stack.
       wl_state_gc_fun s (wl_enc_stack (wl_state_stack s), wl_state_memory s,
                          wl_state_mdomain s, wl_state_store s) = SOME (wl,m,st) /\
       wl_dec_stack wl (wl_state_stack s) = SOME stack /\
       s2 = wl_state_stack_fupd (K stack)
              (wl_state_store_fupd (K st) (wl_state_memory_fupd (K m) s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_gc_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SPEC_TAC(`wl_state_gc_fun (s:(A,C,FFI)wl_state) (wl_enc_stack (wl_state_stack s),
              wl_state_memory s, wl_state_mdomain s, wl_state_store s)`,
           `r:((A word_loc)list#(A word->A word_loc)#(store_name,A word_loc)fmap)option`) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[distinctness "option"] THEN
  MAP_EVERY X_GEN_TAC [`wl:(A word_loc)list`; `m:A word->A word_loc`;
                       `st:(store_name,A word_loc)fmap`] THEN
  MP_TAC(ISPEC `wl_dec_stack (wl:(A word_loc)list) (wl_state_stack (s:(A,C,FFI)wl_state))`
    (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN
      CASE_REWRITE_TAC[distinctness "option"])
    (X_CHOOSE_THEN `stack:((A)stack_frame)list` (fun th -> REWRITE_TAC[th] THEN
      ASSUME_TAC th))) THEN
  CASE_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MAP_EVERY EXISTS_TAC [`wl:(A word_loc)list`; `m:A word->A word_loc`;
    `st:(store_name,A word_loc)fmap`; `stack:((A)stack_frame)list`] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 8195 *)
let alloc_store = prove
 (`!k names (t:(A,C,FFI)wl_state) s1 c cu end next heap_length1.
     wl_alloc k names t = (NONE,s1) /\
     wl_state_gc_fun t = word_gc_fun c /\
     FLOOKUP (wl_state_store t) CurrHeap = SOME (wl_Word cu) /\
     FLOOKUP (wl_state_store t) TriggerGC = SOME (wl_Word end) /\
     FLOOKUP (wl_state_store t) NextFree = SOME (wl_Word next) /\
     FLOOKUP (wl_state_store t) HeapLength = SOME (wl_Word heap_length1) ==>
     ?end next heap_length1 cu.
       FLOOKUP (wl_state_store s1) CurrHeap = SOME (wl_Word cu) /\
       FLOOKUP (wl_state_store s1) TriggerGC = SOME (wl_Word end) /\
       FLOOKUP (wl_state_store s1) NextFree = SOME (wl_Word next) /\
       FLOOKUP (wl_state_store s1) HeapLength = SOME (wl_Word heap_length1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `wl_alloc k names (t:(A,C,FFI)wl_state) = (NONE,s1)` THEN
  REWRITE_TAC[wl_alloc_def] THEN
  MP_TAC(ISPEC `cut_envs names (wl_state_locals (t:(A,C,FFI)wl_state))` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `envs:(A word_loc)spt#(A word_loc)spt` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[PAIR_EQ; distinctness "option"] THEN
  ABBREV_TAC `t1 = wl_push_env envs (NONE:(num#(A)wl_prog#num#num)option)
                     (wl_set_store AllocSize (wl_Word k) (t:(A,C,FFI)wl_state))` THEN
  MP_TAC(ISPEC `wl_gc (t1:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `s2:(A,C,FFI)wl_state`
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  CASE_REWRITE_TAC[PAIR_EQ; distinctness "option"] THEN
  MP_TAC(ISPEC `wl_pop_env (s2:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `s3:(A,C,FFI)wl_state`
    (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  CASE_REWRITE_TAC[PAIR_EQ; distinctness "option"] THEN
  MP_TAC(ISPEC `wl_get_store AllocSize (s3:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `w:A word_loc` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[PAIR_EQ; distinctness "option"] THEN
  MP_TAC(ISPEC `wl_has_space (w:A word_loc) (s3:(A,C,FFI)wl_state)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `b:bool` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[PAIR_EQ; distinctness "option"] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ; distinctness "option"] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP wl_pop_env_const o check (fun th -> is_eq (concl th) &&
    rand(concl th) = `SOME (s3:(A,C,FFI)wl_state)`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GCP3AUX_wl_gc_SOME) THEN
  ASM_REWRITE_TAC[(record_info "wl_state").ri_accfupds; K_THM] THEN
  MATCH_MP_TAC GCP3AUX_word_gc_fun_store_words THEN
  MAP_EVERY EXISTS_TAC [`c:data_to_word_config`;
    `wl_enc_stack (wl_state_stack (t1:(A,C,FFI)wl_state))`;
    `wl_state_memory (t1:(A,C,FFI)wl_state)`; `wl_state_mdomain (t1:(A,C,FFI)wl_state)`;
    `wl_state_store (t1:(A,C,FFI)wl_state)`; `wl:(A word_loc)list`;
    `m:A word->A word_loc`; `cu:A word`; `end:A word`; `next:A word`;
    `heap_length1:A word`] THEN
  SUBGOAL_THEN `wl_state_gc_fun (t1:(A,C,FFI)wl_state) = wl_state_gc_fun (t:(A,C,FFI)wl_state) /\
                wl_state_store t1 = wl_state_store t |+ (AllocSize,wl_Word k)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t1" THEN REWRITE_TAC[wl_push_env_def; wl_set_store_def] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN GCP3AUX_PAIRARG_TAC THEN SIMP[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_comb (lhs (concl th)) &&
    rator (lhs (concl th)) = `wl_state_gc_fun (t1:(A,C,FFI)wl_state)`)) THEN
  ASM_REWRITE_TAC[FLOOKUP_UPDATE; distinctness "store_name"]);;

(* HOL4 line 8220 (local) *)
let alloc_with_locals_1_3 = prove
 (`!k (names:B spt) w1 w2 (t:(A,C,FFI)wl_state).
     wl_alloc k (adjust_sets names)
       (wl_state_locals_fupd (K (insert 1 w1 (insert 3 w2 (wl_state_locals t)))) t) =
     wl_alloc k (adjust_sets names) t`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC GCP3AUX_alloc_locals_cong THEN
  ASM_SIMP_TAC[cut_envs_adjust_sets_ODD; ODD; ARITH]);;

(* HOL4 line 8235 *)
let cut_names_imp_wf = prove
 (`!(s:B spt) (t:A spt) x. cut_names s t = SOME x ==> wf x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cut_names_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; distinctness "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[wf_inter]);;

(* HOL4 line 8241 *)
let cut_env_insert_1 = prove
 (CASE_TERM
  `!(names:B spt) (w:A) t.
     wl_cut_env (FST (adjust_sets names),insert 1 one (SND (adjust_sets names)))
       (insert 1 w t) =
     match wl_cut_env (adjust_sets names) t with
       NONE -> NONE
     | SOME v -> SOME (insert 1 w v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_cut_env_def; cut_envs_def; adjust_sets_def; FST; SND] THEN
  REWRITE_TAC[cut_names_insert_1_insert_1] THEN
  SIMP_TAC[GCP3AUX_cut_names_insert_NOT_IN; GCP3AUX_ODD_NOT_IN_LS; ODD; ARITH] THEN
  MP_TAC(ISPEC `cut_names (LS one:num_set) (t:A spt)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `cut_names (adjust_set (names:B spt)) (t:A spt)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[insert_union] THEN REWRITE_TAC[union_assoc]);;

(* GCP3AUX: a Seq whose first part ends normally *)
let GCP3AUX_evaluate_Seq_NONE = prove
 (`!c1 c2 (s:(A,C,FFI)wl_state) s1.
     wl_evaluate (c1,s) = (NONE,s1) ==> wl_evaluate (wl_Seq c1 c2,s) = wl_evaluate (c2,s1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

(* GCP3AUX: an assignment whose expression evaluates *)
let GCP3AUX_evaluate_Assign = prove
 (`!n e (s:(A,C,FFI)wl_state) v.
     wl_word_exp s e = SOME v ==> wl_evaluate (wl_Assign n e,s) = (NONE,wl_set_var n v s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

(* GCP3AUX: a conditional whose comparison evaluates *)
let GCP3AUX_evaluate_If = prove
 (`!cmp r1 ri c1 c2 (s:(A,C,FFI)wl_state) x y b.
     wl_get_var r1 s = SOME x /\ wl_get_var_imm ri s = SOME y /\
     wl_word_cmp cmp x y = SOME b ==>
     wl_evaluate (wl_If cmp r1 ri c1 c2,s) =
     if b then wl_evaluate (c1,s) else wl_evaluate (c2,s)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [wl_evaluate_def] THEN
  GCP3AUX_ASM_CASE_TAC);;

(* GCP3AUX: an Alloc whose variable holds a word *)
let GCP3AUX_evaluate_Alloc = prove
 (`!n names (s:(A,C,FFI)wl_state) w.
     wl_get_var n s = SOME (wl_Word w) ==>
     wl_evaluate (wl_Alloc n names,s) = wl_alloc w names s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

(* GCP3AUX: SilentFFI is a Skip without empty FFI calls *)
let GCP3AUX_SilentFFI_F = prove
 (`!c n names (s:(A,C,FFI)wl_state).
     ~data_to_word_config_call_empty_ffi c ==>
     wl_evaluate (SilentFFI c n names,s) = (NONE,s)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SilentFFI_def; wl_evaluate_def]);;

(* GCP3AUX: Skip *)
let GCP3AUX_evaluate_Skip = prove
 (`!(s:(A,C,FFI)wl_state). wl_evaluate (wl_Skip,s) = (NONE,s)`,
  REWRITE_TAC[wl_evaluate_def]);;

(* GCP3AUX: the shifted size of AllocVar is the alloc_size *)
let GCP3AUX_AllocVar_alloc_size = prove
 (`!(w:A word) limit.
     good_dimindex(:A) /\ val w DIV 4 < limit /\ limit < dimword(:A) DIV 8 ==>
     word_shl (word_add (word_ushr w 2) (word 1)) (backend_common_word_shift(:A)) =
     alloc_size (val w DIV 4 + 1)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[shift_lsl] THEN
  SUBGOAL_THEN `word_ushr w 2 = word (val w DIV 4):A word` SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM WORD_VAL] THEN REWRITE_TAC[VAL_WORD_USHR] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[bytes_in_word_def; GSYM WORD_ADD; GSYM WORD_MUL; alloc_size_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
  UNDISCH_TAC `limit < dimword(:A) DIV 8` THEN UNDISCH_TAC `val (w:A word) DIV 4 < limit` THEN
  UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def; dimword_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* GCP3AUX: the first steps of AllocVar *)
let GCP3AUX_AllocVar_prefix = prove
 (`!c limit names (t:(A,C,FFI)wl_state) w e nx nw t3.
     good_dimindex(:A) /\ wl_get_var 1 t = SOME (wl_Word w) /\ limit < dimword(:A) DIV 8 /\
     FLOOKUP (wl_state_store t) TriggerGC = SOME (wl_Word e) /\
     FLOOKUP (wl_state_store t) NextFree = SOME (wl_Word nx) /\
     nw = (if val w DIV 4 < limit then alloc_size (val w DIV 4 + 1)
           else word_neg (word 1)) /\
     t3 = wl_state_locals_fupd (K (insert 1 (wl_Word nw)
            (insert 3 (wl_Word (word_sub e nx)) (wl_state_locals t)))) t ==>
     wl_evaluate (AllocVar c limit names,t) =
     if word_ult (word_sub e nx) nw then
       wl_evaluate (wl_Seq (SilentFFI c 3 (FST (adjust_sets names),
                                           insert 1 one (SND (adjust_sets names))))
                     (wl_Seq (wl_Alloc 1 (adjust_sets names))
                             (SilentFFI c 3 (adjust_sets names))),t3)
     else (NONE,t3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  REWRITE_TAC[AllocVar_def; data_to_word_list_Seq_def] THEN
  SUBGOAL_THEN `~(2 >= dimindex(:A)) /\ ~(backend_common_word_shift(:A) >= dimindex(:A)) /\
                val (word 2:A word) = 2 /\
                val (word (backend_common_word_shift(:A)):A word) = backend_common_word_shift(:A) /\
                val (word limit:A word) = limit`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `limit < dimword(:A) DIV 8` THEN UNDISCH_TAC `good_dimindex(:A)` THEN
    REWRITE_TAC[good_dimindex_def; backend_common_word_shift_def; dimword_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[VAL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_evaluate (wl_Assign 1 (wl_Shift Lsr (wl_Var 1) (wl_Const (word 2))),t) =
     (NONE, wl_set_var 1 (wl_Word (word_ushr w 2)) (t:(A,C,FFI)wl_state))`
    (fun th -> REWRITE_TAC[MATCH_MP GCP3AUX_evaluate_Seq_NONE th]) THENL
   [MATCH_MP_TAC GCP3AUX_evaluate_Assign THEN ASM_REWRITE_TAC[word_exp_rw] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[OPTION_MAP_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_evaluate (wl_If Lower 1 (Imm (word limit))
     (wl_Assign 1 (wl_Shift Lsl (wl_Op asm_Add [wl_Var 1; wl_Const (word 1)])
        (wl_Const (word (backend_common_word_shift (:A))))))
     (wl_Assign 1 (wl_Const (word_neg (word 1)))),
     wl_set_var 1 (wl_Word (word_ushr w 2)) (t:(A,C,FFI)wl_state)) =
     (NONE, wl_set_var 1 (wl_Word nw) (wl_set_var 1 (wl_Word (word_ushr w 2)) t))`
    (fun th -> REWRITE_TAC[MATCH_MP GCP3AUX_evaluate_Seq_NONE th]) THENL
   [MP_TAC(ISPECL [`Lower`; `1`; `Imm (word limit):(A)reg_imm`;
      `wl_Assign 1 (wl_Shift Lsl (wl_Op asm_Add [wl_Var 1; wl_Const (word 1)])
         (wl_Const (word (backend_common_word_shift (:A))))):(A)wl_prog`;
      `wl_Assign 1 (wl_Const (word_neg (word 1))):(A)wl_prog`;
      `wl_set_var 1 (wl_Word (word_ushr w 2)) (t:(A,C,FFI)wl_state)`;
      `wl_Word (word_ushr w 2):A word_loc`; `wl_Word (word limit):A word_loc`;
      `val (w:A word) DIV 4 < limit`] GCP3AUX_evaluate_If) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[wl_get_var_def; wl_set_var_def; wl_get_var_imm_def; wl_word_cmp_def;
                  WORD_ULT; VAL_WORD_USHR] THEN
      SIMP[lookup_insert] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GCP3AUX_evaluate_Assign THEN
    REWRITE_TAC[word_exp_rw; wl_set_var_def; MAP; ITLIST] THEN SIMP[] THEN
    ASM_REWRITE_TAC[WORD_ADD_0; OPTION_MAP_DEF] THEN
    MATCH_MP_TAC GCP3AUX_AllocVar_alloc_size THEN EXISTS_TAC `limit:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_evaluate (wl_Assign 3 (wl_Op asm_Sub [Lookup TriggerGC; Lookup NextFree]),
      wl_set_var 1 (wl_Word nw) (wl_set_var 1 (wl_Word (word_ushr w 2))
        (t:(A,C,FFI)wl_state))) = (NONE, t3)`
    (fun th -> REWRITE_TAC[MATCH_MP GCP3AUX_evaluate_Seq_NONE th]) THENL
   [SUBGOAL_THEN `t3 = wl_set_var 3 (wl_Word (word_sub e nx)) (wl_set_var 1 (wl_Word nw)
        (wl_set_var 1 (wl_Word (word_ushr w 2)) (t:(A,C,FFI)wl_state)))` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[wl_set_var_def] THEN SIMP[insert_shadow; insert_insert_3_1]; ALL_TAC] THEN
    MATCH_MP_TAC GCP3AUX_evaluate_Assign THEN
    REWRITE_TAC[word_exp_rw; wl_set_var_def; MAP] THEN SIMP[] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[OPTION_MAP_DEF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Lower`; `3`; `Reg 1:(A)reg_imm`;
    `wl_Seq (SilentFFI c 3 (FST (adjust_sets (names:num_set)),
                            insert 1 one (SND (adjust_sets names))))
       (wl_Seq (wl_Alloc 1 (adjust_sets names)) (SilentFFI c 3 (adjust_sets names))):(A)wl_prog`;
    `wl_Skip:(A)wl_prog`; `t3:(A,C,FFI)wl_state`; `wl_Word (word_sub e nx):A word_loc`;
    `wl_Word nw:A word_loc`; `word_ult (word_sub e nx) (nw:A word)`] GCP3AUX_evaluate_If) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[wl_get_var_def; wl_get_var_imm_def; wl_word_cmp_def] THEN
    SIMP[lookup_insert; ARITH_EQ];
    DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[GCP3AUX_evaluate_Skip]]);;

(* GCP3AUX: the SilentFFI after alloc, with the cut of adjust_sets *)
let GCP3AUX_SilentFFI_T = prove
 (`!c names (s:(A,C,FFI)wl_state) cu nx hl env.
     data_to_word_config_call_empty_ffi c /\
     FLOOKUP (wl_state_store s) NextFree = SOME (wl_Word nx) /\
     FLOOKUP (wl_state_store s) CurrHeap = SOME (wl_Word cu) /\
     FLOOKUP (wl_state_store s) HeapLength = SOME (wl_Word hl) /\
     wl_cut_env names (insert 9 (wl_Word hl) (insert 7 (wl_Word (word_sub nx cu))
                         (insert 3 (wl_Word (word 0)) (wl_state_locals s)))) = SOME env ==>
     wl_evaluate (SilentFFI c 3 names,s) =
       (NONE, wl_state_locals_fupd (K env) (wl_state_fp_regs_fupd (K FEMPTY) s))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SilentFFI_def; data_to_word_list_Seq_def] THEN
  REWRITE_TAC[wl_evaluate_def] THEN
  REPEAT(CHANGED_TAC(SIMP[word_exp_rw; wl_set_var_def; MAP; VAL_WORD_0; read_bytearray_def;
                          call_FFI_def; write_bytearray_def] THEN CASE_REWRITE_TAC[])) THEN
  REWRITE_TAC[(record_info "wl_state").ri_component_equality;
              (record_info "wl_state").ri_accfupds; K_THM]);;

(* GCP3AUX: state_rel gives the heap words of the store *)
let GCP3AUX_state_rel_store_words = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s t v locs ==>
     ?cu e nx hl.
       FLOOKUP (wl_state_store t) CurrHeap = SOME (wl_Word cu) /\
       FLOOKUP (wl_state_store t) TriggerGC = SOME (wl_Word e) /\
       FLOOKUP (wl_state_store t) NextFree = SOME (wl_Word nx) /\
       FLOOKUP (wl_state_store t) HeapLength = SOME (wl_Word hl)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_def; heap_in_memory_store_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* GCP3AUX: under state_rel, the free space is always below the word -1 *)
let GCP3AUX_state_rel_minus1_ult = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) v locs e nx.
     data_to_word_gcProof_state_rel c l1 l2 s t v locs /\
     FLOOKUP (wl_state_store t) TriggerGC = SOME (wl_Word e) /\
     FLOOKUP (wl_state_store t) NextFree = SOME (wl_Word nx) ==>
     word_ult (word_sub e nx) (word_neg (word 1))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_def; heap_in_memory_store_def] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) TriggerGC = SOME (wl_Word e)` THEN
  UNDISCH_TAC `FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) NextFree = SOME (wl_Word nx)` THEN
  ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add c (word_mul b (word (a + sp))))
                           (word_add c (word_mul b (word a))) = word_mul b (word sp):A word`] THEN
  REWRITE_TAC[WORD_ULT; GSYM NOT_LE; w2n_minus_1_LESS_EQ] THEN
  MATCH_MP_TAC bytes_in_word_ADD_1_NOT_ZERO THEN ASM_REWRITE_TAC[]);;

(* GCP3AUX: cutting the locals of a cut gives the same cut *)
let GCP3AUX_data_cut_env_idem = prove
 (`!names (l:A spt) x. data_cut_env names l = SOME x ==> data_cut_env names x = SOME x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_cut_env_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; distinctness "option"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[domain_mk_wf; domain_inter] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[option_INJ; mk_wf_eq; lookup_inter_alt; lookup_mk_wf] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* GCP3AUX: state_rel ignores the temporaries 1 and 3 *)
let GCP3AUX_state_rel_insert_1_3 = prove
 (`!c l1 l2 (s:(C,FFI)data_state) x y (t:(A,C,FFI)wl_state) v locs.
     data_to_word_gcProof_state_rel c l1 l2 s
       (wl_state_locals_fupd (K (insert 1 x (insert 3 y (wl_state_locals t)))) t) v locs =
     data_to_word_gcProof_state_rel c l1 l2 s t v locs`,
  REWRITE_TAC[GSYM insert_insert_3_1; state_rel_insert_3_1]);;

(* GCP3AUX: inserts at other keys commute with an insert at 1 *)
let GCP3AUX_insert_1_front = prove
 (`!k (a:A) b t. ~(k = 1) ==> insert k a (insert 1 b t) = insert 1 b (insert k a t)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [insert_insert] THEN ASM_REWRITE_TAC[]);;

(* GCP3AUX: the end of AllocVar without empty FFI calls *)
let GCP3AUX_AllocVar_tail_F = prove
 (`!c (names:num_set) (t:(A,C,FFI)wl_state) nw v3.
     ~data_to_word_config_call_empty_ffi c ==>
     wl_evaluate (wl_Seq (SilentFFI c 3 (FST (adjust_sets names),
                                         insert 1 one (SND (adjust_sets names))))
                   (wl_Seq (wl_Alloc 1 (adjust_sets names)) (SilentFFI c 3 (adjust_sets names))),
                  wl_state_locals_fupd (K (insert 1 (wl_Word nw) (insert 3 v3 (wl_state_locals t))))
                    t) =
     wl_alloc nw (adjust_sets names) t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN ASM_SIMP_TAC[GCP3AUX_SilentFFI_F] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[wl_get_var_def] THEN SIMP[lookup_insert] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[alloc_with_locals_1_3] THEN
  GCP3AUX_PAIRARG_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* GCP3AUX: the end of AllocVar with empty FFI calls *)
let GCP3AUX_AllocVar_tail_T = prove
 (`!c (names:num_set) (t:(A,C,FFI)wl_state) nw v3 y cu nx hl res s1.
     data_to_word_config_call_empty_ffi c /\
     FLOOKUP (wl_state_store t) NextFree = SOME (wl_Word nx) /\
     FLOOKUP (wl_state_store t) CurrHeap = SOME (wl_Word cu) /\
     FLOOKUP (wl_state_store t) HeapLength = SOME (wl_Word hl) /\
     wl_cut_env (adjust_sets names) (wl_state_locals t) = SOME y /\
     wl_alloc nw (adjust_sets names)
       (wl_state_locals_fupd (K y) (wl_state_fp_regs_fupd (K FEMPTY) t)) = (res,s1) ==>
     wl_evaluate (wl_Seq (SilentFFI c 3 (FST (adjust_sets names),
                                         insert 1 one (SND (adjust_sets names))))
                   (wl_Seq (wl_Alloc 1 (adjust_sets names)) (SilentFFI c 3 (adjust_sets names))),
                  wl_state_locals_fupd (K (insert 1 (wl_Word nw) (insert 3 v3 (wl_state_locals t))))
                    t) =
     if res = NONE then wl_evaluate (SilentFFI c 3 (adjust_sets names),s1) else (res,s1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`;
    `(FST (adjust_sets (names:num_set)), insert 1 one (SND (adjust_sets names)))`;
    `wl_state_locals_fupd (K (insert 1 (wl_Word nw) (insert 3 v3 (wl_state_locals t))))
       (t:(A,C,FFI)wl_state)`;
    `cu:A word`; `nx:A word`; `hl:A word`; `insert 1 (wl_Word nw) (y:(A word_loc)spt)`]
    GCP3AUX_SilentFFI_T) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[(record_info "wl_state").ri_accfupds; K_THM] THEN
    SIMP[GCP3AUX_insert_1_front; ARITH_EQ] THEN REWRITE_TAC[cut_env_insert_1] THEN
    ASM_SIMP_TAC[cut_env_adjust_sets_ODD; ODD; ARITH] THEN CASE_REWRITE_TAC[];
    DISCH_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP GCP3AUX_evaluate_Seq_NONE th]) THEN
  GEN_REWRITE_TAC LAND_CONV [wl_evaluate_def] THEN
  SUBGOAL_THEN `wl_evaluate (wl_Alloc 1 (adjust_sets (names:num_set)),
     wl_state_locals_fupd (K (insert 1 (wl_Word nw) y))
       (wl_state_fp_regs_fupd (K FEMPTY)
         (wl_state_locals_fupd (K (insert 1 (wl_Word nw) (insert 3 v3 (wl_state_locals t))))
           (t:(A,C,FFI)wl_state)))) = (res,s1)` SUBST1_TAC THENL
   [SUBGOAL_THEN `wl_get_var 1 (wl_state_locals_fupd (K (insert 1 (wl_Word nw) y))
       (wl_state_fp_regs_fupd (K FEMPTY) (wl_state_locals_fupd
         (K (insert 1 (wl_Word nw) (insert 3 v3 (wl_state_locals t)))) (t:(A,C,FFI)wl_state)))) =
       SOME (wl_Word nw)` (fun th -> REWRITE_TAC[MATCH_MP GCP3AUX_evaluate_Alloc th]) THENL
     [REWRITE_TAC[wl_get_var_def] THEN SIMP[lookup_insert]; ALL_TAC] THEN
    UNDISCH_TAC `wl_alloc nw (adjust_sets (names:num_set))
      (wl_state_locals_fupd (K y) (wl_state_fp_regs_fupd (K FEMPTY) (t:(A,C,FFI)wl_state))) =
      (res,s1)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`nw:A word`; `adjust_sets (names:num_set)`;
      `wl_state_locals_fupd (K y) (wl_state_fp_regs_fupd (K FEMPTY) (t:(A,C,FFI)wl_state))`;
      `insert 1 (wl_Word nw) (y:(A word_loc)spt)`] GCP3AUX_alloc_locals_cong) THEN
    REWRITE_TAC[(record_info "wl_state").ri_accfupds; K_THM] THEN
    ANTS_TAC THENL [MATCH_MP_TAC cut_envs_adjust_sets_ODD THEN REWRITE_TAC[ODD; ARITH]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
    REWRITE_TAC[(record_info "wl_state").ri_component_equality;
                (record_info "wl_state").ri_accfupds; K_THM];
    CASE_REWRITE_TAC[]]);;

(* GCP3AUX: the state relation after the cuts of AllocVar *)
let GCP3AUX_state_rel_cut_fp = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs names x y.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_cut_env names (data_state_locals s) = SOME x /\
     wl_cut_env (adjust_sets names) (wl_state_locals t) = SOME y ==>
     data_to_word_gcProof_state_rel c l1 l2 (data_state_locals_fupd (K x) s)
       (wl_state_locals_fupd (K y) (wl_state_fp_regs_fupd (K FEMPTY) t)) NONE locs`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wl_state_locals_fupd (K y) (wl_state_fp_regs_fupd (K FEMPTY) (t:(A,C,FFI)wl_state)) =
                wl_state_fp_regs_fupd (K FEMPTY) (wl_state_locals_fupd (K y) t)` SUBST1_TAC THENL
   [REWRITE_TAC[(record_info "wl_state").ri_component_equality;
                (record_info "wl_state").ri_accfupds; K_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC state_rel_with_fp_regs THEN MATCH_MP_TAC state_rel_cut_env_cut_env THEN
  EXISTS_TAC `names:num_set` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 8272 *)
let AllocVar_thm_gen = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs names x w limit q r.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_cut_env names (data_state_locals s) = SOME x /\
     wl_get_var 1 t = SOME (wl_Word w) /\
     wl_evaluate (AllocVar c limit names,t) = (q,r) /\
     limit < dimword (:A) DIV 8 ==>
     (q = SOME NotEnoughSpace ==>
      wl_state_ffi r = data_state_ffi s /\
      option_le (wl_state_stack_max r) (data_state_stack_max s) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) /\ val w DIV 4 < limit /\
       no_thunks_in_refs (data_state_refs s) ==>
       !roots2 dups n2 r2 s2.
         PERM roots2 (APPEND (APPEND (APPEND dups (toList x))
                        (FLAT (MAP extract_stack (data_state_stack s))))
                        [the_global (data_state_global s)]) /\
         set_of_list dups SUBSET
           set_of_list (APPEND (APPEND (toList x)
                          (FLAT (MAP extract_stack (data_state_stack s))))
                          [the_global (data_state_global s)]) /\
         size_of (data_state_limits s) roots2 (data_state_refs s) LN = (n2,r2,s2) ==>
         limits_heap_limit (data_state_limits s) < n2 + (val w DIV 4 + 1))) /\
     (~(q = SOME NotEnoughSpace) ==>
      val w DIV 4 < limit /\
      data_to_word_gcProof_state_rel c l1 l2
        (data_state_locals_fupd (K x) (data_state_space_fupd (K (val w DIV 4 + 1)) s))
        r NONE locs /\
      FLOOKUP (wl_state_store r) (Temp (word 29)) =
        FLOOKUP (wl_state_store t) (Temp (word 29)) /\
      wl_state_code r = wl_state_code t /\
      wl_state_code_buffer r = wl_state_code_buffer t /\
      wl_state_data_buffer r = wl_state_data_buffer t /\
      wl_state_compile_oracle r = wl_state_compile_oracle t /\
      q = NONE)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `good_dimindex (:A)` ASSUME_TAC THENL
   [UNDISCH_TAC `data_to_word_gcProof_state_rel c l1 l2 s (t:(A,C,FFI)wl_state) NONE locs` THEN
    REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `cu:A word` (X_CHOOSE_THEN `e:A word` (X_CHOOSE_THEN `nx:A word`
    (X_CHOOSE_THEN `hl:A word` STRIP_ASSUME_TAC))) o MATCH_MP GCP3AUX_state_rel_store_words) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `names:num_set`; `x:data_v spt`]
    cut_env_IMP_cut_env) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `y:(A word_loc)spt`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GCP3AUX_data_cut_env_idem) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "AllocVar")) (concl th))) THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `limit:num`; `names:num_set`; `t:(A,C,FFI)wl_state`;
    `w:A word`; `e:A word`; `nx:A word`;
    `if val (w:A word) DIV 4 < limit then alloc_size (val w DIV 4 + 1) else word_neg (word 1):A word`;
    `wl_state_locals_fupd (K (insert 1 (wl_Word (if val (w:A word) DIV 4 < limit
        then alloc_size (val w DIV 4 + 1) else word_neg (word 1):A word))
        (insert 3 (wl_Word (word_sub e nx)) (wl_state_locals t)))) (t:(A,C,FFI)wl_state)`]
    GCP3AUX_AllocVar_prefix) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `val (w:A word) DIV 4 < limit` THEN ASM_REWRITE_TAC[] THENL
   [(* the size fits *)
    ASM_CASES_TAC `word_ult (word_sub e nx) (alloc_size (val (w:A word) DIV 4 + 1):A word)` THEN
    ASM_REWRITE_TAC[] THENL
     [ASM_CASES_TAC `data_to_word_config_call_empty_ffi c` THENL
       [MP_TAC(ISPEC `wl_alloc (alloc_size (val (w:A word) DIV 4 + 1):A word)
          (adjust_sets (names:num_set))
          (wl_state_locals_fupd (K y) (wl_state_fp_regs_fupd (K FEMPTY) (t:(A,C,FFI)wl_state)))`
          PAIR_SURJECTIVE) THEN
        DISCH_THEN(X_CHOOSE_THEN `res:((A)wl_result)option` (X_CHOOSE_THEN `s1:(A,C,FFI)wl_state`
          ASSUME_TAC)) THEN
        MP_TAC(ISPECL [`c:data_to_word_config`; `names:num_set`; `t:(A,C,FFI)wl_state`;
          `alloc_size (val (w:A word) DIV 4 + 1):A word`; `wl_Word (word_sub e nx):A word_loc`;
          `y:(A word_loc)spt`; `cu:A word`; `nx:A word`; `hl:A word`;
          `res:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] GCP3AUX_AllocVar_tail_T) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`;
          `data_state_locals_fupd (K x) (s:(C,FFI)data_state)`;
          `wl_state_locals_fupd (K y) (wl_state_fp_regs_fupd (K FEMPTY) (t:(A,C,FFI)wl_state))`;
          `locs:(num#num)list`; `names:num_set`; `x:data_v spt`; `val (w:A word) DIV 4 + 1`;
          `res:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] alloc_alt_gen) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[(record_info "data_state").ri_accfupds; K_THM] THEN
          MATCH_MP_TAC GCP3AUX_state_rel_cut_fp THEN EXISTS_TAC `names:num_set` THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[(record_info "data_state").ri_accfupds; (record_info "wl_state").ri_accfupds;
                    K_THM] THEN
        STRIP_TAC THEN ASM_CASES_TAC `res = (NONE:((A)wl_result)option)` THENL
         [FIRST_X_ASSUM SUBST_ALL_TAC THEN
          RULE_ASSUM_TAC(REWRITE_RULE[distinctness "option"]) THEN
          FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
          FIRST_ASSUM(X_CHOOSE_THEN `cu1:A word` (X_CHOOSE_THEN `e1:A word`
            (X_CHOOSE_THEN `nx1:A word` (X_CHOOSE_THEN `hl1:A word` STRIP_ASSUME_TAC))) o
            MATCH_MP GCP3AUX_state_rel_store_words) THEN
          FIRST_ASSUM(MP_TAC o SPECL [`names:num_set`; `x:data_v spt`] o
            MATCH_MP (REWRITE_RULE[IMP_CONJ] cut_env_IMP_cut_env)) THEN
          REWRITE_TAC[(record_info "data_state").ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
          DISCH_THEN(X_CHOOSE_TAC `y1:(A word_loc)spt`) THEN
          MP_TAC(ISPECL [`c:data_to_word_config`; `adjust_sets (names:num_set)`;
            `s1:(A,C,FFI)wl_state`; `cu1:A word`; `nx1:A word`; `hl1:A word`;
            `y1:(A word_loc)spt`] GCP3AUX_SilentFFI_T) THEN
          ANTS_TAC THENL [ASM_SIMP_TAC[cut_env_adjust_sets_ODD; ODD; ARITH]; ALL_TAC] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
          DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
          REWRITE_TAC[distinctness "option"; (record_info "wl_state").ri_accfupds; K_THM] THEN
          ASM_REWRITE_TAC[] THEN
          MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`;
            `data_state_locals_fupd (K x) (data_state_space_fupd (K (val (w:A word) DIV 4 + 1))
               (data_state_locals_fupd (K x) (s:(C,FFI)data_state)))`;
            `s1:(A,C,FFI)wl_state`; `locs:(num#num)list`; `names:num_set`; `x:data_v spt`;
            `y1:(A word_loc)spt`] GCP3AUX_state_rel_cut_fp) THEN
          ASM_REWRITE_TAC[(record_info "data_state").ri_accfupds; K_THM] THEN
          MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN
          MATCH_MP_TAC GCP3AUX_state_rel_data_cong THEN
          REWRITE_TAC[(record_info "data_state").ri_accfupds; K_THM];
          ASM_CASES_TAC `res = SOME (NotEnoughSpace:(A)wl_result)` THENL
           [ALL_TAC;
            FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
              is_neg (fst(dest_imp (concl th))))) THEN
            ASM_REWRITE_TAC[]] THEN
          FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
            concl th = `res = SOME (NotEnoughSpace:(A)wl_result)`)) THEN
          REWRITE_TAC[distinctness "option"; PAIR_EQ] THEN
          DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
          RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_REWRITE_TAC[]];
        ASM_SIMP_TAC[GCP3AUX_AllocVar_tail_F] THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
          `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `names:num_set`; `x:data_v spt`;
          `val (w:A word) DIV 4 + 1`; `q:((A)wl_result)option`; `r:(A,C,FFI)wl_state`]
          alloc_alt_gen) THEN
        ASM_REWRITE_TAC[]];
      (* enough space without a collection *)
      REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      REWRITE_TAC[distinctness "option"; GCP3AUX_state_rel_insert_1_3;
                  (record_info "wl_state").ri_accfupds; K_THM] THEN
      SUBGOAL_THEN `data_state_locals_fupd (K x)
          (data_state_space_fupd (K (val (w:A word) DIV 4 + 1)) (s:(C,FFI)data_state)) =
        data_state_space_fupd (K (val w DIV 4 + 1)) (data_state_locals_fupd (K x) s)`
        SUBST1_TAC THENL
       [REWRITE_TAC[(record_info "data_state").ri_component_equality;
                    (record_info "data_state").ri_accfupds; K_THM];
        ALL_TAC] THEN
      MATCH_MP_TAC has_space_state_rel THEN CONJ_TAC THENL
       [REWRITE_TAC[wl_has_space_def; wl_get_store_def] THEN ASM_REWRITE_TAC[] THEN
        CASE_REWRITE_TAC[option_INJ] THEN
        UNDISCH_TAC `~word_ult (word_sub e nx) (alloc_size (val (w:A word) DIV 4 + 1):A word)` THEN
        REWRITE_TAC[WORD_ULT; NOT_LT];
        MATCH_MP_TAC state_rel_cut_env THEN EXISTS_TAC `names:num_set` THEN ASM_REWRITE_TAC[]]];
    (* the size does not fit *)
    MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
      `t:(A,C,FFI)wl_state`; `NONE:((data_v#A word_loc)list)option`; `locs:(num#num)list`;
      `e:A word`; `nx:A word`] GCP3AUX_state_rel_minus1_ult) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `data_to_word_config_call_empty_ffi c` THENL
     [MP_TAC(ISPEC `wl_alloc (word_neg (word 1):A word) (adjust_sets (names:num_set))
        (wl_state_locals_fupd (K y) (wl_state_fp_regs_fupd (K FEMPTY) (t:(A,C,FFI)wl_state)))`
        PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `res:((A)wl_result)option` (X_CHOOSE_THEN `s1:(A,C,FFI)wl_state`
        ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`c:data_to_word_config`; `names:num_set`; `t:(A,C,FFI)wl_state`;
        `word_neg (word 1):A word`; `wl_Word (word_sub e nx):A word_loc`;
        `y:(A word_loc)spt`; `cu:A word`; `nx:A word`; `hl:A word`;
        `res:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] GCP3AUX_AllocVar_tail_T) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`;
        `data_state_locals_fupd (K x) (s:(C,FFI)data_state)`;
        `wl_state_locals_fupd (K y) (wl_state_fp_regs_fupd (K FEMPTY) (t:(A,C,FFI)wl_state))`;
        `locs:(num#num)list`; `names:num_set`; `x:data_v spt`;
        `res:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`] alloc_fail) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[(record_info "data_state").ri_accfupds; K_THM] THEN
        MATCH_MP_TAC GCP3AUX_state_rel_cut_fp THEN EXISTS_TAC `names:num_set` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[(record_info "data_state").ri_accfupds; K_THM] THEN
      DISCH_THEN(fun th -> let a,b = CONJ_PAIR th in ASSUME_TAC b THEN ASSUME_TAC (MP a b)) THEN
      ASM_REWRITE_TAC[distinctness "option"; PAIR_EQ] THEN
      DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[GCP3AUX_AllocVar_tail_F] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
        `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `names:num_set`; `x:data_v spt`;
        `q:((A)wl_result)option`; `r:(A,C,FFI)wl_state`] alloc_fail) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]]]);;

(* HOL4 line 8461 *)
let AllocVar_thm = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs names x w limit q r.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_cut_env names (data_state_locals s) = SOME x /\
     wl_get_var 1 t = SOME (wl_Word w) /\
     wl_evaluate (AllocVar c limit names,t) = (q,r) /\
     limit < dimword (:A) DIV 8 ==>
     (q = SOME NotEnoughSpace ==>
      wl_state_ffi r = data_state_ffi s /\
      option_le (wl_state_stack_max r) (data_state_stack_max s) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) /\ val w DIV 4 < limit /\
       no_thunks_in_refs (data_state_refs s) ==>
       limits_heap_limit (data_state_limits s) <
         size_of_heap (cut_locals names s) + val w DIV 4 + 1)) /\
     (~(q = SOME NotEnoughSpace) ==>
      val w DIV 4 < limit /\
      data_to_word_gcProof_state_rel c l1 l2
        (data_state_locals_fupd (K x) (data_state_space_fupd (K (val w DIV 4 + 1)) s))
        r NONE locs /\
      FLOOKUP (wl_state_store r) (Temp (word 29)) =
        FLOOKUP (wl_state_store t) (Temp (word 29)) /\
      wl_state_code r = wl_state_code t /\
      wl_state_code_buffer r = wl_state_code_buffer t /\
      wl_state_data_buffer r = wl_state_data_buffer t /\
      wl_state_compile_oracle r = wl_state_compile_oracle t /\
      q = NONE)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC(MATCH_MP AllocVar_thm_gen th)) THEN
  SUBGOAL_THEN `?n2 r2 s2. size_of (data_state_limits (s:(C,FFI)data_state))
      (APPEND (APPEND (toList x) (FLAT (MAP extract_stack (data_state_stack s))))
        [the_global (data_state_global s)]) (data_state_refs s) LN = (n2,r2,s2)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `size_of_heap (cut_locals names (s:(C,FFI)data_state)) = n2` SUBST1_TAC THENL
   [REWRITE_TAC[size_of_heap_def; cut_locals_def] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[stack_to_vs_def; (record_info "data_state").ri_accfupds; K_THM;
                size_of_global_to_vs] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(fun th -> MP_TAC(MP th
      (ASSUME `q = SOME (NotEnoughSpace:(A)wl_result)`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      is_forall (snd(dest_imp(concl th))))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`APPEND (APPEND (toList x) (FLAT (MAP extract_stack (data_state_stack s))))
        [the_global (data_state_global (s:(C,FFI)data_state))]`; `[]:data_v list`;
      `r2:((data_v)bvl_ref)spt`; `s2:(1)spt`] THEN
    ASM_REWRITE_TAC[APPEND; PERM_REFL; set_of_list; EMPTY_SUBSET];
    FIRST_ASSUM ACCEPT_TAC]);;

(* HOL4 line 8501 *)
let AllocVar_thm_nary = prove
 (`!c l1 l2 s (t:(A,C,FFI)wl_state) locs args (x':num_set) xa vals i limit q r.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_cut_env (list_insert args x') (data_state_locals s) = SOME xa /\
     data_get_vars args (data_state_locals s) = SOME vals /\
     wl_get_var 1 t = SOME (wl_Word (word (4 * i))) /\
     4 * i < dimword (:A) /\
     wl_evaluate (AllocVar c limit (list_insert args x'),t) = (q,r) /\
     limit < dimword (:A) DIV 8 ==>
     (q = SOME NotEnoughSpace ==>
      wl_state_ffi r = data_state_ffi s /\
      option_le (wl_state_stack_max r) (data_state_stack_max s) /\
      (~(data_to_word_config_gc_kind c = data_to_word_None) /\ i < limit /\
       no_thunks_in_refs (data_state_refs s) ==>
       limits_heap_limit (data_state_limits s) <
         size_of_heap_args vals (cut_locals x' s) + (i + 1))) /\
     (~(q = SOME NotEnoughSpace) ==>
      i < limit /\
      data_to_word_gcProof_state_rel c l1 l2
        (data_state_locals_fupd (K xa) (data_state_space_fupd (K (i + 1)) s)) r NONE locs /\
      FLOOKUP (wl_state_store r) (Temp (word 29)) =
        FLOOKUP (wl_state_store t) (Temp (word 29)) /\
      wl_state_code r = wl_state_code t /\
      wl_state_code_buffer r = wl_state_code_buffer t /\
      wl_state_data_buffer r = wl_state_data_buffer t /\
      wl_state_compile_oracle r = wl_state_compile_oracle t /\
      q = NONE)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val (word (4 * i):A word) DIV 4 = i` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD_EQ; GSYM dimword_def] THEN
    MATCH_MP_TAC DIV_MULT THEN REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `l1:num`; `l2:num`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `locs:(num#num)list`; `list_insert args (x':num_set)`;
    `xa:data_v spt`; `word (4 * i):A word`; `limit:num`; `q:((A)wl_result)option`;
    `r:(A,C,FFI)wl_state`] AllocVar_thm_gen) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(fun th -> MP_TAC(MP th
    (ASSUME `q = SOME (NotEnoughSpace:(A)wl_result)`))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the cut of x' and the value of xa *)
  SUBGOAL_THEN `domain (list_insert args (x':num_set)) SUBSET
                domain (data_state_locals (s:(C,FFI)data_state)) /\
                xa = inter (data_state_locals s) (list_insert args x')` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `data_cut_env (list_insert args (x':num_set))
       (data_state_locals (s:(C,FFI)data_state)) = SOME xa` THEN
    REWRITE_TAC[data_cut_env_def] THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_INJ; distinctness "option"] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[wf_mk_id; wf_inter];
    ALL_TAC] THEN
  SUBGOAL_THEN `data_cut_env (x':num_set) (data_state_locals (s:(C,FFI)data_state)) =
                SOME (inter (data_state_locals s) x')` ASSUME_TAC THENL
   [REWRITE_TAC[data_cut_env_def] THEN SIMP_TAC[wf_mk_id; wf_inter] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `~(domain (x':num_set) SUBSET domain (data_state_locals (s:(C,FFI)data_state)))` THEN
    UNDISCH_TAC `domain (list_insert args (x':num_set)) SUBSET
                 domain (data_state_locals (s:(C,FFI)data_state))` THEN
    REWRITE_TAC[SUBSET; domain_list_insert] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?n2 r2 s2. size_of (data_state_limits (s:(C,FFI)data_state))
      (APPEND (APPEND (APPEND vals (toList (inter (data_state_locals s) (x':num_set))))
         (FLAT (MAP extract_stack (data_state_stack s))))
        [the_global (data_state_global s)]) (data_state_refs s) LN = (n2,r2,s2)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `size_of_heap_args vals (cut_locals (x':num_set) (s:(C,FFI)data_state)) = n2`
    SUBST1_TAC THENL
   [REWRITE_TAC[size_of_heap_args_def; cut_locals_def] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[stack_to_vs_def; (record_info "data_state").ri_accfupds; K_THM] THEN
    REWRITE_TAC[APPEND_ASSOC; size_of_global_to_vs] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`args:num list`; `x':num_set`; `vals:data_v list`;
    `data_state_locals (s:(C,FFI)data_state)`] get_vars_PERM_toList_inter) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `dups:data_v list` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
    is_forall (snd(dest_imp(concl th))))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`APPEND (APPEND (APPEND vals (toList (inter (data_state_locals s) (x':num_set))))
       (FLAT (MAP extract_stack (data_state_stack s))))
       [the_global (data_state_global (s:(C,FFI)data_state))]`; `dups:data_v list`;
    `r2:((data_v)bvl_ref)spt`; `s2:(1)spt`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PERM_CONG THEN REWRITE_TAC[PERM_REFL] THEN
    MATCH_MP_TAC PERM_CONG THEN ASM_REWRITE_TAC[PERM_REFL];
    REWRITE_TAC[SET_OF_LIST_APPEND] THEN ASM SET_TAC[]]);;

(* HOL4 line 8564 *)
let state_rel_with_clock_0 = prove
 (`!c r1 r2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) x locs.
     data_to_word_gcProof_state_rel c r1 r2 s t x locs ==>
     data_to_word_gcProof_state_rel c r1 r2 (data_state_space_fupd (K 0) s) t x locs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; (record_info "data_state").ri_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "memory_rel")) (concl th))) THEN
  REWRITE_TAC[memory_rel_def] THEN MESON_TAC[LE_0]);;

(* HOL4 line 8572 *)
let word_heap_non_empty_limit = prove
 (`!limit (other:A word) c.
     ~(limit = 0) ==>
     word_heap other (heap_expand limit) c =
     SEP_EXISTS w1. set_sep_one (other,w1) STAR
       word_heap (word_add other bytes_in_word) (heap_expand (limit - 1)) c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `limit:num` num_CASES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
  REWRITE_TAC[heap_expand_def; NOT_SUC; SUC_SUB1] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[word_heap_def; word_el_def; SEP_CLAUSES] THENL
   [REWRITE_TAC[GSYM ADD1; data_to_word_memoryProof_word_list_exists_thm; SEP_CLAUSES];
    ASM_SIMP_TAC[SUB_ADD; ARITH_RULE `~(n = 0) ==> 1 <= n`] THEN
    REWRITE_TAC[GSYM ADD1; data_to_word_memoryProof_word_list_exists_thm]]);;

(* HOL4 line 8592 *)
let small_int_0 = prove
 (`good_dimindex (:A) ==> small_int (:A) (&0)`,
  REWRITE_TAC[good_dimindex_def; small_int_def; dimword_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV);;

(* HOL4 line 8598 *)
let state_rel_imp_clock = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs ==>
     data_state_clock s = wl_state_clock t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_to_word_gcProof_state_rel_thm] THEN MESON_TAC[]);;

(* HOL4 line 8604 *)
let get_vars_SOME_IFF_data = prove
 (`!(t:A spt) x xs y ys.
     (data_get_vars [] t = SOME [] <=> T) /\
     (data_get_vars (CONS x xs) t = SOME (CONS y ys) <=>
      data_get_var x t = SOME y /\ data_get_vars xs t = SOME ys)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_get_vars_def] THEN
  MP_TAC(ISPEC `data_get_var x (t:A spt)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  MP_TAC(ISPEC `data_get_vars xs (t:A spt)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ; CONS_11]);;

(* HOL4 line 8613 *)
let get_vars_SOME_IFF_data_eq = prove
 (`!(t:A spt) z x xs.
     ((data_get_vars [] t = SOME z) <=> (z = [])) /\
     (data_get_vars (CONS x xs) t = SOME z <=>
      ?y ys. z = CONS y ys /\ data_get_var x t = SOME y /\ data_get_vars xs t = SOME ys)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_get_vars_def] THEN
  CONJ_TAC THENL [REWRITE_TAC[option_INJ] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `data_get_var x (t:A spt)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  MP_TAC(ISPEC `data_get_vars xs (t:A spt)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

(* HOL4 line 8623 *)
let get_vars_SOME_IFF = prove
 (`!(t:(A,C,FFI)wl_state) x xs y ys.
     (wl_get_vars [] t = SOME [] <=> T) /\
     (wl_get_vars (CONS x xs) t = SOME (CONS y ys) <=>
      wl_get_var x t = SOME y /\ wl_get_vars xs t = SOME ys)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_get_vars_def] THEN
  MP_TAC(ISPEC `wl_get_var x (t:(A,C,FFI)wl_state)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT] THEN
  MP_TAC(ISPEC `wl_get_vars xs (t:(A,C,FFI)wl_state)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ; CONS_11]);;

(* HOL4 line 8632 *)
let get_vars_SOME_IFF_eq = prove
 (`!(t:(A,C,FFI)wl_state) z x xs.
     ((wl_get_vars [] t = SOME z) <=> (z = [])) /\
     (wl_get_vars (CONS x xs) t = SOME z <=>
      ?y ys. z = CONS y ys /\ wl_get_var x t = SOME y /\ wl_get_vars xs t = SOME ys)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_get_vars_def] THEN
  CONJ_TAC THENL [REWRITE_TAC[option_INJ] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `wl_get_var x (t:(A,C,FFI)wl_state)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  MP_TAC(ISPEC `wl_get_vars xs (t:(A,C,FFI)wl_state)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

(* HOL4 line 8642 *)
let memory_rel_get_vars_IMP_lemma = prove
 (`!c be ts refs sp st (m:A word->A word_loc) dm ll (t:(A,C,FFI)wl_state) envs n x w.
     memory_rel c be ts refs sp st m dm
       (APPEND (join_env ll (toAList (inter (wl_state_locals t) (adjust_set ll)))) envs) /\
     data_get_vars n ll = SOME x /\
     wl_get_vars (MAP adjust_var n) t = SOME w ==>
     memory_rel c be ts refs sp st m dm
       (APPEND (APPEND (ZIP x w)
          (join_env ll (toAList (inter (wl_state_locals t) (adjust_set ll))))) envs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[memory_rel_def] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp':num`; `sp1:num`; `gens:gen_state`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC word_ml_inv_get_vars_IMP_lemma THEN
  EXISTS_TAC `n:num list` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 8657 *)
let memory_rel_get_vars_IMP = prove
 (`!c be ts (s:(C,FFI)data_state) sp st (m:A word->A word_loc) dm (t:(A,C,FFI)wl_state)
    envs n x w.
     memory_rel c be ts (data_state_refs s) sp st m dm
       (APPEND (join_env (data_state_locals s)
          (toAList (inter (wl_state_locals t) (adjust_set (data_state_locals s))))) envs) /\
     data_get_vars n (data_state_locals s) = SOME x /\
     wl_get_vars (MAP adjust_var n) t = SOME w ==>
     memory_rel c be ts (data_state_refs s) sp st m dm
       (APPEND (APPEND (ZIP x w)
          (join_env (data_state_locals s)
             (toAList (inter (wl_state_locals t) (adjust_set (data_state_locals s))))))
          envs)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC memory_rel_get_vars_IMP_lemma THEN
  EXISTS_TAC `n:num list` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 8671 (HOL4: memory_rel_get_vars_IMP |> Q.INST [n |-> [u]] |>  *)
(* GEN_ALL |> SIMP_RULE std_ss [MAP,get_vars_SOME_IFF_eq,                    *)
(* get_vars_SOME_IFF_data_eq,PULL_EXISTS,ZIP,APPEND])                        *)
let memory_rel_get_var_IMP = prove
 (`!c be ts (s:(C,FFI)data_state) sp st (m:A word->A word_loc) dm (t:(A,C,FFI)wl_state)
    envs u y y'.
     memory_rel c be ts (data_state_refs s) sp st m dm
       (APPEND (join_env (data_state_locals s)
          (toAList (inter (wl_state_locals t) (adjust_set (data_state_locals s))))) envs) /\
     data_get_var u (data_state_locals s) = SOME y /\
     wl_get_var (adjust_var u) t = SOME y' ==>
     memory_rel c be ts (data_state_refs s) sp st m dm
       (CONS (y,y')
          (APPEND (join_env (data_state_locals s)
             (toAList (inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
             envs))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:data_to_word_config`; `be:bool`; `ts:num`; `s:(C,FFI)data_state`;
    `sp:num`; `st:(store_name,A word_loc)fmap`; `m:A word->A word_loc`; `dm:A word->bool`;
    `t:(A,C,FFI)wl_state`; `envs:(data_v#A word_loc)list`; `[u:num]`; `[y:data_v]`;
    `[y':A word_loc]`] memory_rel_get_vars_IMP) THEN
  ASM_REWRITE_TAC[MAP; data_get_vars_def; wl_get_vars_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ZIP; APPEND]);;

(* HOL4 line 8676 *)
let lookup_RefByte_location = prove
 (`!c l1 l2 (x:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs.
     data_to_word_gcProof_state_rel c l1 l2 x t NONE locs ==>
     lookup RefByte_location (wl_state_code t) = SOME (4,RefByte_code c) /\
     lookup RefArray_location (wl_state_code t) = SOME (3,RefArray_code c) /\
     lookup FromList_location (wl_state_code t) = SOME (4,FromList_code c) /\
     lookup Replicate_location (wl_state_code t) = SOME (5,Replicate_code) /\
     lookup AnyArith_location (wl_state_code t) = SOME (4,AnyArith_code c) /\
     lookup Add_location (wl_state_code t) = SOME (3,Add_code) /\
     lookup Sub_location (wl_state_code t) = SOME (3,Sub_code) /\
     lookup Mul_location (wl_state_code t) = SOME (3,Mul_code) /\
     lookup Div_location (wl_state_code t) = SOME (3,Div_code) /\
     lookup Mod_location (wl_state_code t) = SOME (3,Mod_code)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_to_word_gcProof_code_rel_def;
              data_to_word_stubs_def; ALL_APPEND; ALL] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 8692 *)
let memory_rel_insert = prove
 (`!c be ts refs sp st (m:A word->A word_loc) dm x w d l xs dest.
     memory_rel c be ts refs sp st m dm
       (APPEND (APPEND [(x,w)] (join_env d (toAList (inter l (adjust_set d))))) xs) ==>
     memory_rel c be ts refs sp st m dm
       (APPEND (join_env (insert dest x d)
          (toAList (inter (insert (adjust_var dest) w l)
                          (adjust_set (insert dest x d))))) xs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[memory_rel_def] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `limit:num`; `a:num`; `sp':num`; `sp1:num`; `gens:gen_state`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC word_ml_inv_insert THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 8705 *)
let state_rel_IMP_Number_arg = prove
 (`!c l1 l2 xs ss (s:(C,FFI)data_state) ys (t:(A,C,FFI)wl_state) locs n.
     data_to_word_gcProof_state_rel c l1 l2 (data_call_env xs ss s) (wl_call_env ys ss t)
       NONE locs /\
     n < dimword (:A) DIV 16 /\ LENGTH ys = LENGTH xs + 1 ==>
     data_to_word_gcProof_state_rel c l1 l2
       (data_call_env (APPEND xs [data_Number (&n)]) ss s)
       (wl_call_env (APPEND ys [wl_Word (word (4 * n):A word)]) ss t) NONE locs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_gcProof_state_rel_thm; data_call_env_def; wl_call_env_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[(record_info "data_state").ri_accfupds; (record_info "wl_state").ri_accfupds;
              K_THM] THEN
  CASE_REWRITE_TAC[APPEND] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `0 < LENGTH (ys:(A word_loc)list)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `lookup 0 (fromList2 (ys:(A word_loc)list)) = SOME (wl_Loc l1 l2)` THEN
    REWRITE_TAC[lookup_fromList2; lookup_fromList; EVEN; LENGTH_APPEND; EL_APPEND] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[ARITH_RULE `0 < a ==> 0 < a + b`];
    X_GEN_TAC `k:num` THEN
    REWRITE_TAC[lookup_fromList2; lookup_fromList; EVEN_adjust_var; adjust_var_DIV_2_ANY;
                LENGTH_APPEND; LENGTH] THEN
    COND_CASES_TAC THEN REWRITE_TAC[IS_SOME_DEF] THEN
    COND_CASES_TAC THEN REWRITE_TAC[IS_SOME_DEF] THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "memory_rel")) (concl th))) THEN
    SUBGOAL_THEN `fromList (APPEND xs [data_Number (&n)]) =
                  insert (LENGTH xs) (data_Number (&n)) (fromList xs)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM SNOC_APPEND; fromList_SNOC]; ALL_TAC] THEN
    SUBGOAL_THEN `fromList2 (APPEND ys [wl_Word (word (4 * n):A word)]) =
                  insert (adjust_var (LENGTH (xs:data_v list))) (wl_Word (word (4 * n)))
                    (fromList2 ys)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM SNOC_APPEND; fromList2_SNOC] THEN AP_THM_TAC THEN AP_THM_TAC THEN
      AP_TERM_TAC THEN ASM_REWRITE_TAC[adjust_var_def] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN DISCH_TAC THEN MATCH_MP_TAC memory_rel_insert THEN
    SUBGOAL_THEN `word (4 * n):A word = Smallnum (&n)` SUBST1_TAC THENL
     [REWRITE_TAC[data_to_word_Smallnum_def; INT_OF_NUM_LT; LT; INT_OF_NUM_MUL;
                  NUM_OF_INT_OF_NUM];
      ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[APPEND] THEN DISCH_TAC THEN
    MATCH_MP_TAC IMP_memory_rel_Number THEN ASM_REWRITE_TAC[small_int_def; INT_OF_NUM_LT] THEN
    CONJ_TAC THENL
     [INT_ARITH_TAC;
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `dimword (:A) DIV 16` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIV_MONO2 THEN ARITH_TAC]]);;

(* HOL4 line 8732 *)
let state_rel_cut_IMP = prove
 (`!c l1 l2 (s:(C,FFI)data_state) (t:(A,C,FFI)wl_state) locs names_opt x.
     data_to_word_gcProof_state_rel c l1 l2 s t NONE locs /\
     data_cut_state_opt names_opt s = SOME x ==>
     data_to_word_gcProof_state_rel c l1 l2 x t NONE locs`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `names_opt:(num_set)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `names:num_set` SUBST1_TAC)) THEN
  REWRITE_TAC[data_cut_state_opt_def] THEN CASE_REWRITE_TAC[option_INJ] THENL
   [STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[data_cut_state_def] THEN
    MP_TAC(ISPEC `data_cut_env names (data_state_locals (s:(C,FFI)data_state))`
      (cases "option")) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `env:data_v spt` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    MATCH_MP_TAC state_rel_cut_env THEN EXISTS_TAC `names:num_set` THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 8744 *)
let get_vars_1_IMP = prove
 (`!x1 (s:(A,C,FFI)wl_state) v1.
     wl_get_vars [x1] s = SOME [v1] ==> wl_get_var x1 s = SOME v1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_get_vars_def] THEN
  MP_TAC(ISPEC `wl_get_var x1 (s:(A,C,FFI)wl_state)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ; CONS_11]);;

(* HOL4 line 8751 *)
let get_vars_2_IMP = prove
 (`!x1 x2 (s:(A,C,FFI)wl_state) v1 v2.
     (wl_get_vars [x1;x2] s = SOME [v1;v2]) ==>
     wl_get_var x1 s = SOME v1 /\ wl_get_var x2 s = SOME v2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_get_vars_def] THEN
  MP_TAC(ISPEC `wl_get_var x1 (s:(A,C,FFI)wl_state)` (cases "option")) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `wl_get_var x2 (s:(A,C,FFI)wl_state)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ; CONS_11]);;

(* HOL4 line 8759 *)
let get_vars_3_IMP = prove
 (`!x1 x2 x3 (s:(A,C,FFI)wl_state) v1 v2 v3.
     (wl_get_vars [x1;x2;x3] s = SOME [v1;v2;v3]) ==>
     wl_get_var x1 s = SOME v1 /\ wl_get_var x2 s = SOME v2 /\
     wl_get_var x3 s = SOME v3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_get_vars_def] THEN
  MP_TAC(ISPEC `wl_get_var x1 (s:(A,C,FFI)wl_state)` (cases "option")) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `wl_get_var x2 (s:(A,C,FFI)wl_state)` (cases "option")) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `wl_get_var x3 (s:(A,C,FFI)wl_state)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ; CONS_11]);;

(* HOL4 line 8768 *)
let inter_insert_ODD_adjust_set = prove
 (`!k dest (w:A) v s (t:B spt).
     ODD k ==>
     inter (insert (adjust_var dest) w (insert k v s)) (adjust_set t) =
     inter (insert (adjust_var dest) w s) (adjust_set t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inter_eq; lookup_inter_alt; lookup_insert] THEN
  X_GEN_TAC `n:num` THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(n:num = k)` (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[GCP3AUX_ODD_NOT_IN_domain_adjust_set]);;

(* HOL4 line 8778 *)
let inter_insert_ODD_adjust_set_alt = prove
 (`!k (v:A) s (t:B spt).
     ODD k ==> inter (insert k v s) (adjust_set t) = inter s (adjust_set t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GCP3AUX_inter_insert_NOT_IN THEN
  ASM_MESON_TAC[GCP3AUX_ODD_NOT_IN_domain_adjust_set]);;

(* HOL4 line 8788 *)
let inter_delete_ODD_adjust_set_alt = prove
 (`!k (s:A spt) (t:B spt).
     ODD k ==> inter (delete k s) (adjust_set t) = inter s (adjust_set t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inter_eq; lookup_inter_alt; lookup_delete] THEN
  X_GEN_TAC `n:num` THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(n:num = k)` (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[GCP3AUX_ODD_NOT_IN_domain_adjust_set]);;

(* HOL4 line 8798 *)
let get_vars_termdep = prove
 (`!xs (t:(A,C,FFI)wl_state).
     wl_get_vars xs (wl_state_termdep_fupd (K (wl_state_termdep t - 1)) t) =
     wl_get_vars xs t`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[wl_get_vars_def; wl_get_var_def] THEN
  REWRITE_TAC[(record_info "wl_state").ri_accfupds]);;

let _ = cake_add_simps [get_vars_termdep];;

(* HOL4 line 8804 *)
let join_env_locals_def = cake_def
  `join_env_locals (sl:A spt) (tl:(B)spt) =
     join_env sl (toAList (inter tl (adjust_set sl)))`;;

(* HOL4 line 8809 *)
let join_env_locals_insert_odd = prove
 (`!n (sl:A spt) (v:B) ls.
     ODD n ==> join_env_locals sl (insert n v ls) = join_env_locals sl ls`,
  SIMP_TAC[join_env_locals_def; inter_insert_ODD_adjust_set_alt]);;

let _ = cake_add_simps [join_env_locals_insert_odd];;

(* HOL4 line 8815 *)
let join_env_locals_insert_dest_odd = prove
 (`!n (sl:A spt) dest (w:B) v ls.
     ODD n ==>
     join_env_locals sl (insert (adjust_var dest) w (insert n v ls)) =
     join_env_locals sl (insert (adjust_var dest) w ls)`,
  SIMP_TAC[join_env_locals_def; inter_insert_ODD_adjust_set]);;

let _ = cake_add_simps [join_env_locals_insert_dest_odd];;

(* HOL4 line 8821 *)
let MustTerminate_limit_NOT_0 = prove
 (`~(MustTerminate_limit (:A) = 0)`,
  REWRITE_TAC[MustTerminate_limit_def] THEN MP_TAC(INST_TYPE [`:A`,`:N`] ZERO_LT_dimword) THEN
  ARITH_TAC);;

let _ = cake_add_simps [MustTerminate_limit_NOT_0];;

(* HOL4 line 8827 *)
let memory_rel_Temp = prove
 (`!c be ts refs sp st i w (m:A word->A word_loc) dm vars.
     memory_rel c be ts refs sp (st |+ (Temp i,w)) m dm vars <=>
     memory_rel c be ts refs sp st m dm vars`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[memory_rel_def; heap_in_memory_store_def; FLOOKUP_UPDATE; FDOM_FUPDATE;
              IN_INSERT; distinctness "store_name"]);;

let _ = cake_add_simps [memory_rel_Temp];;

(* HOL4 line 8834 *)
let adjust_var_not_15 = prove
 (`!a2. ~(adjust_var a2 = 15)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN REWRITE_TAC[EVEN_adjust_var] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let _ = cake_add_simps [adjust_var_not_15];;

(* HOL4 line 8840 *)
let get_vars_sing = prove
 (`!n (t:(A,C,FFI)wl_state) x.
     wl_get_vars [n] t = SOME x <=> ?x1. wl_get_vars [n] t = SOME [x1] /\ x = [x1]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_get_vars_def] THEN
  MP_TAC(ISPEC `wl_get_var n (t:(A,C,FFI)wl_state)` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ; CONS_11] THEN
  MESON_TAC[]);;

(* HOL4 line 8846 (allow_rebind: rebinds the name of the theorem of line    *)
(* 453.  HOL4: word_ml_inv_get_vars_IMP |> Q.INST [n |-> [n1], x |-> [x1]]  *)
(* |> GEN_ALL |> REWRITE_RULE [...] |> SIMP_RULE std_ss [Once get_vars_sing, *)
(* PULL_EXISTS,get_vars_SOME_IFF,ZIP,APPEND])                               *)
let word_ml_inv_get_var_IMP = prove
 (`!heap be a sp sp1 gens limit ts c refs (s:(C,FFI)data_state)
    (t:(A,C,FFI)wl_state) n1 x1 x1' envs.
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (APPEND (join_env (data_state_locals s)
          (toAList (inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
          envs) /\
     data_get_var n1 (data_state_locals s) = SOME x1 /\
     wl_get_var (adjust_var n1) t = SOME x1' ==>
     word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
       (CONS (x1,x1')
          (APPEND (join_env (data_state_locals s)
             (toAList (inter (wl_state_locals t) (adjust_set (data_state_locals s)))))
             envs))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)list`;
    `be:bool`; `a:num`; `sp:num`; `sp1:num`; `gens:gen_state`; `limit:num`; `ts:num`;
    `c:data_to_word_config`; `refs:((data_v)bvl_ref)spt`; `s:(C,FFI)data_state`;
    `t:(A,C,FFI)wl_state`; `[n1:num]`; `[x1:data_v]`; `[x1':A word_loc]`;
    `envs:(data_v#A word_loc)list`] word_ml_inv_get_vars_IMP) THEN
  ASM_REWRITE_TAC[MAP; data_get_vars_def; wl_get_vars_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ZIP; APPEND]);;
