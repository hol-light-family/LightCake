(* ========================================================================= *)
(* stack_to_labProof_p1: part 1 of 2 (HOL4 lines 1-2740) of the port of     *)
(* HOL4 compiler/backend/proofs/stack_to_labProofScript.sml (CakeML v3479).  *)
(* Correctness proof for stack_to_lab.                                       *)
(* The parts stack_to_labProof_p1.ml and stack_to_labProof.ml (HOL4 lines    *)
(* 2741-5221) are loaded one after the other (the second needs the first).   *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Records: s.f (stackSem state) is stack_state_f s, t.f (labSem state)    *)
(*   lab_state_f t, c.f (stack_to_lab config) stack_to_lab_config_f c;       *)
(*   r with f := v is RECTYPE_f_fupd (K v) r; t with <| f1 := v1; f2 := v2 |> *)
(*   is RECTYPE_f1_fupd (K v1) (RECTYPE_f2_fupd (K v2) t).                   *)
(* - Constants of two theories with one HOL4 name: stackSem's evaluate,      *)
(*   semantics, find_code, inst, dec_clock, ... are stack_ ones, labSem's    *)
(*   lab_ ones (decided by the types); the results Halt, Error, TimeOut of   *)
(*   lab programs are targetSem's (target_Halt, ...), the results of stack   *)
(*   programs stackSem's (stack_Result, stackSem_Halt, ...); extract_labels  *)
(*   of stackLang programs is stackProps' and of lab programs labProps'      *)
(*   (lab_extract_labels); get_labels of stackLang programs is stackSem's;   *)
(*   HOL4 read_reg r t of a labSem state is its Overload lab_state_regs t r. *)
(* - HOL4 <<= is isPREFIX; EVERY is ALL; set is set_of_list; ++ is APPEND;   *)
(*   $~ o is_Label is (~) o is_Label; words as in hol4/words4.ml (n2w =      *)
(*   word, w2n = val, ...).                                                  *)
(* - Free variables of HOL4 statements are universally quantified, after    *)
(*   HOL4's explicit binders; unused bound variables are left out.           *)
(* - HOL4 theorems derived by rules (Theorem X = ..., val X = ... |> RULE)  *)
(*   are stated with their resulting statement.                              *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/proofs/stack_namesProof.ml";;
needs "compiler/backend/proofs/stack_rawcallProof.ml";;
needs "compiler/backend/stack_to_lab.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/stackProps.ml";;
needs "compiler/backend/stack_alloc.ml";;
needs "compiler/backend/semantics/labSem.ml";;
needs "compiler/backend/word_to_stack.ml";;
needs "compiler/backend/proofs/data_to_word_gcProof.ml";;
needs "compiler/backend/proofs/word_to_stackProof.ml";;
(* stack_allocProof (a HOL4 ancestor) is not loaded; the three theorems of   *)
(* it that part 1 uses (next_lab_EQ_MAX, next_lab_thm,                       *)
(* extract_labels_next_lab) are proved below under the S2LP1AUX_ prefix.     *)
needs "compiler/backend/proofs/stack_removeProof.ml";;
needs "compiler/backend/semantics/labProps.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 1: HOL4 lines 1-2740 ===== *)

(* HOL4 lines 14-21: simpset settings (temp_delsimps, diminish_srw_ss,       *)
(* set_trace): not needed.  HOL4 lines 23-24: val get_labels_def =           *)
(* stackSemTheory.get_labels_def, get_reg_value_def =                        *)
(* targetSemTheory.get_reg_value_def (abbreviations for the proofs).         *)
(* HOL4 line 28: Overload Loc = wordLang$Loc (wl_Loc).                       *)

(* ------------------------------------------------------------------------- *)
(* Local tactics.  S2LP1AUX_CASES_ON tm is the kit's CASES_ON with the names *)
(* of the constructor arguments chosen fresh for the goal (the kit's         *)
(* CASES_ON of a compound term fails with CHOOSE when the nchotomy's bound   *)
(* name is already free), and with a boolean variable replaced by T or F in *)
(* the assumptions too (BOOL_CASES_TAC rewrites only the goal);             *)
(* S2LP1AUX_TOP_CASE_TAC is TOP_CASE_TAC with it.                           *)
(* ------------------------------------------------------------------------- *)

let rec S2LP1AUX_STRIP_FRESH (keep:bool) (th:thm) : tactic = fun (asl,w as g) ->
  let c = concl th in
  if is_disj c then DISJ_CASES_THEN (S2LP1AUX_STRIP_FRESH keep) th g
  else if is_exists c then
    let v,_ = dest_exists c in
    let avoid = itlist (union o thm_frees o snd) asl
                  (union (frees w) (thm_frees th)) in
    let v' = variant avoid v in
    X_CHOOSE_THEN v' (S2LP1AUX_STRIP_FRESH keep) th g
  else if keep then ((SUBST_ALL_TAC th THEN ASSUME_TAC th) ORELSE ASSUME_TAC th) g
  else (SUBST_ALL_TAC th ORELSE ASSUME_TAC th) g;;

let S2LP1AUX_CASES_ON (tm:term) : tactic = fun (asl,w as g) ->
  let ty = type_of tm in
  if ty = bool_ty && is_var tm then
    (ASM_CASES_TAC tm THENL
      [FIRST_X_ASSUM(SUBST_ALL_TAC o EQT_INTRO);
       FIRST_X_ASSUM(SUBST_ALL_TAC o EQF_INTRO)]) g else
  if ty = bool_ty then CASES_ON tm g else
  let nch = ISPEC tm (nchotomy_of_type ty) in
  (MP_TAC nch THEN DISCH_THEN (S2LP1AUX_STRIP_FRESH (not (is_var tm)))) g;;

let S2LP1AUX_TOP_CASE_TAC : tactic = fun (asl,w as g) ->
  let x = first_case_scrutinee w w in
  (S2LP1AUX_CASES_ON x THEN CASE_TIDY_TAC) g;;

(* S2LP1AUX_PAIRARG_TAC is the kit's PAIRARG_TAC splitting an innermost     *)
(* pair_CASE (one whose scrutinee contains no other candidate), so that a    *)
(* let (a,b) = (case ...) in ... is split after the inner pair cases.       *)

let S2LP1AUX_PAIRARG_TAC : tactic =
  fun (asl,w as gl) ->
    let whole = list_mk_conj(w :: map (concl o snd) asl) in
    let is_cand t =
      is_case_app t &&
      (let c,x,fs = dest_case_app t in
       fst(dest_const c) = "pair_CASE" && not (is_pair x) &&
       free_in x whole) in
    let cands = find_terms is_cand whole in
    let inner t = let _,x,_ = dest_case_app t in
                  not (exists (fun u -> not (u = t) && free_in u x) cands) in
    let t = try find inner cands with Failure _ -> failwith "S2LP1AUX_PAIRARG_TAC" in
    let _,x,fs = dest_case_app t in
    let f = hd fs in
    let tya,tyb = match dest_type(type_of x) with
        "prod",[a;b] -> a,b | _ -> failwith "S2LP1AUX_PAIRARG_TAC" in
    let n1,n2 =
      try let a,b = dest_abs f in let b1,_ = dest_abs b in
          fst(dest_var a),fst(dest_var b1)
      with Failure _ -> "p1","p2" in
    let avoid = itlist (union o thm_frees o snd) asl (frees w) in
    let v1 = variant avoid (mk_var(n1,tya)) in
    let v2 = variant (v1::avoid) (mk_var(n2,tyb)) in
    let nch = ISPEC x (nchotomy_of_type (type_of x)) in
    (MP_TAC nch THEN
     DISCH_THEN(X_CHOOSE_THEN v1 (X_CHOOSE_THEN v2
       (fun th -> if is_var x then SUBST_ALL_TAC th
                  else SUBST_ALL_TAC th THEN ASSUME_TAC th))) THEN
     CASE_ASM_TIDY_TAC THEN CAKE_REWRITE_TAC[]) gl;;

(* S2LP1AUX_FULL_CASE_TAC splits the outermost case (or conditional) of the *)
(* goal or the assumptions with S2LP1AUX_CASES_ON (the kit's FULL_CASE_TAC   *)
(* splits the innermost one with CASES_ON)                                   *)

let S2LP1AUX_FULL_CASE_TAC : tactic = fun (asl,w as gl) ->
  let whole = list_mk_conj(w :: map (concl o snd) asl) in
  let x = first_case_scrutinee whole whole in
  (S2LP1AUX_CASES_ON x THEN CASE_ASM_TIDY_TAC THEN CASE_TIDY_TAC) gl;;

(* S2LP1AUX_EXISTS_ASM_TAC: for a goal ?v1 .. vk. C1 /\ ... /\ Cn, find   *)
(* the witnesses by matching conjuncts with assumptions (instantiating only *)
(* the vi), then go on with the instantiated conjunction                     *)

let S2LP1AUX_EXISTS_ASM_TAC : tactic = fun (asl,w as g) ->
  let vs,body = strip_exists w in
  if vs = [] then ALL_TAC g else
  let facts = map (concl o snd) asl in
  let rec go theta cjs =
    match cjs with
      [] -> theta
    | c::rest ->
        let c' = vsubst theta c in
        let fvs = filter (fun v -> mem v vs && not (can (rev_assoc v) theta)) (frees c') in
        if fvs = [] then go theta rest else
        let try_m t =
          let (_,tmi,tyi) = term_match [] c' t in
          if forall (fun (t,v) -> mem v fvs || t = v) tmi && tyi = []
          then filter (fun (t,v) -> mem v fvs) tmi else failwith "" in
        let tmi = try tryfind try_m facts with Failure _ -> [] in
        go (tmi @ theta) rest in
  let theta = go [] (conjuncts body) in
  let wits = map (fun v -> try rev_assoc v theta with Failure _ -> v) vs in
  (MAP_EVERY EXISTS_TAC wits) g;;

(* prove a conjunction of assumptions, label facts (\(l1,l2). ...) (a,b)    *)
(* and arithmetic consequences of the assumptions                           *)

let S2LP1AUX_CONJS_TAC : tactic =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (ASM_REWRITE_TAC[ALL_DISTINCT_APPEND; ALL_DISTINCT; MEM; MEM_APPEND; APPEND; PAIR_EQ] THEN
    NO_TAC) ORELSE
   (CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[] THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC)));;

(* HOL4 line 32 (word_shift is asmSem's) *)
let word_sh_word_shift = prove
 (`!a (b:A word) c z.
     word_sh a b c = SOME z ==> c < dimindex (:A) /\ z = asm_word_shift a b c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_sh_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `a:shift` THEN CAKE_REWRITE_TAC[option_INJ; asm_word_shift_def] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[] THEN
  MP_TAC(ISPEC `(:A)` DIMINDEX_GE_1) THEN ASM_ARITH_TAC);;

(* HOL4 line 39 [simp] (labSem's assert) *)
let assert_T = prove
 (`!(s:(A,C,FFI)lab_state). lab_assert T s = s`,
  REWRITE_TAC[lab_assert_def; lab_state_component_equality] THEN SIMP[]);;

let _ = cake_add_simps [assert_T];;

(* HOL4 line 45 (l1, l2 and x are free in HOL4) *)
let asm_fetch_aux_no_label = prove
 (`!pc (code:((A)sec)list) l1 l2 x.
     asm_fetch_aux pc code = SOME (lab_Label l1 l2 x) ==> F`,
  MATCH_MP_TAC asm_fetch_aux_ind THEN
  REWRITE_TAC[asm_fetch_aux_def; option_DISTINCT] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[option_INJ] THEN
  DISCH_THEN SUBST_ALL_TAC THEN FS[]);;

(* HOL4 line 53 (HOL4 leaves the Word case of the inner case unspecified) *)
let dest_to_loc_def = cake_def
  `dest_to_loc (regs:(num,(A)word_loc)fmap) dest =
     match dest with
       INL p -> p
     | INR r -> (match FAPPLY regs r with wl_Loc loc _ -> loc)`;;

(* HOL4 line 58 *)
let dest_to_loc'_def = cake_def
  `dest_to_loc' (regs:num->(A)word_loc) dest =
     match dest with
       INL p -> p
     | INR r -> (match regs r with wl_Loc loc _ -> loc)`;;

(* HOL4 line 63 (stackSem's find_code) *)
let find_code_lookup = prove
 (`!dest (regs:(num,(A)word_loc)fmap) (code:(B)spt) p.
     stack_find_code dest regs code = SOME p
     ==> lookup (dest_to_loc regs dest) code = SOME p /\
         (!r. dest = INR r ==> r IN FDOM regs)`,
  GEN_TAC THEN CASES_ON `dest:num+num` THEN
  REWRITE_TAC[stack_find_code_def; dest_to_loc_def] THEN CAKE_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[FLOOKUP_DEF] THEN
  COND_CASES_TAC THEN CAKE_REWRITE_TAC[option_DISTINCT] THEN
  ASM_REWRITE_TAC[] THEN EVERY_CASE_TAC THEN FS[]);;

(* HOL4 line 72 [simp] *)
let not_is_Label_compile_jump = prove
 (`!dest. is_Label (compile_jump dest:(A)line) <=> F`,
  GEN_TAC THEN CASES_ON `dest:num+num` THEN
  REWRITE_TAC[compile_jump_def; is_Label_def]);;

let _ = cake_add_simps [not_is_Label_compile_jump];;

(* HOL4 line 78 [simp] (wordSem's word_cmp) *)
let word_cmp_not_NONE = prove
 (`!cmp (w1:A word) w2. ~(wl_word_cmp cmp (wl_Word w1) (wl_Word w2) = NONE)`,
  GEN_TAC THEN CASES_ON `cmp:cmp` THEN
  REWRITE_TAC[wl_word_cmp_def; option_DISTINCT]);;

let _ = cake_add_simps [word_cmp_not_NONE];;

(* HOL4 line 84 [simp] (asm's word_cmp) *)
let word_cmp_negate_alt = prove
 (`!cmp (w1:A word) w2. asm_word_cmp (stack_to_lab_negate cmp) w1 w2 <=> ~asm_word_cmp cmp w1 w2`,
  GEN_TAC THEN CASES_ON `cmp:cmp` THEN
  REWRITE_TAC[stack_to_lab_negate_def; asm_word_cmp_def]);;

let _ = cake_add_simps [word_cmp_negate_alt];;

(* HOL4 line 90 [simp] (wordSem's word_cmp; $~ is (~)) *)
let word_cmp_negate = prove
 (`!cmp (w1:(A)word_loc) w2.
     wl_word_cmp (stack_to_lab_negate cmp) w1 w2 = OPTION_MAP (~) (wl_word_cmp cmp w1 w2)`,
  GEN_TAC THEN CASES_ON `cmp:cmp` THEN
  REPEAT GEN_TAC THEN CASES_ON `w1:(A)word_loc` THEN CASES_ON `w2:(A)word_loc` THEN
  REWRITE_TAC[stack_to_lab_negate_def; wl_word_cmp_def; OPTION_MAP_DEF] THEN
  ASM_CASES_TAC `a1 = 0` THEN ASM_CASES_TAC `a:A word = word 1` THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF]);;

let _ = cake_add_simps [word_cmp_negate];;

(* HOL4 line 102 (HOL4 leaves the non-Label cases of the inner case          *)
(* unspecified) *)
let stack_to_labProof_code_installed_def = cake_def
  `(stack_to_labProof_code_installed n ([]:((A)line)list) (code:((A)sec)list) <=> T) /\
   (stack_to_labProof_code_installed n (CONS x xs) code <=>
      if is_Label x then
        (match x with lab_Label l1 l2 _ -> loc_to_pc l1 l2 code = SOME n) /\
        stack_to_labProof_code_installed n xs code
      else
        asm_fetch_aux n code = SOME x /\
        stack_to_labProof_code_installed (n + 1) xs code)`;;

(* HOL4 line 113 ($~ o is_Label is (~) o is_Label) *)
let code_installed_append_imp = prove
 (`!l1 pc l2 (code:((A)sec)list).
     stack_to_labProof_code_installed pc (APPEND l1 l2) code
     ==> stack_to_labProof_code_installed pc l1 code /\
         stack_to_labProof_code_installed (pc + LENGTH (FILTER ((~) o is_Label) l1)) l2 code`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; FILTER; LENGTH; ADD_CLAUSES; o_THM;
              stack_to_labProof_code_installed_def] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`pc:num`; `l2:((A)line)list`; `code:((A)sec)list`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`pc + 1`; `l2:((A)line)list`; `code:((A)sec)list`])] THEN
  ASM_REWRITE_TAC[ARITH_RULE `(pc + 1) + n = pc + SUC n`] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[]);;

(* code_installed of an APPEND, as an equation (local helper; HOL4 uses     *)
(* code_installed_append_imp with imp_res_tac)                               *)
let S2LP1AUX_code_installed_APPEND_EQ = prove
 (`!l1 pc l2 (code:((A)sec)list).
     stack_to_labProof_code_installed pc (APPEND l1 l2) code <=>
     stack_to_labProof_code_installed pc l1 code /\
     stack_to_labProof_code_installed (pc + LENGTH (FILTER ((~) o is_Label) l1)) l2 code`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; FILTER; LENGTH; ADD_CLAUSES; o_THM;
              stack_to_labProof_code_installed_def] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[LENGTH; ARITH_RULE `pc + SUC n = (pc + 1) + n`; CONJ_ACI]);;

(* HOL4 line 122 [local] (c, l1 and l2 are free in HOL4; get_labels is       *)
(* stackSem's) *)
let code_installed_get_labels_IMP = prove
 (`!top (e:(A)stack_prog) n q cs bs pc c l1 l2.
     stack_to_labProof_code_installed pc (append (FST (stack_to_lab_flatten top e n q cs bs))) c /\
     (l1,l2) IN stack_get_labels e
     ==> ?v. loc_to_pc l1 l2 c = SOME v`,
  MATCH_MP_TAC stack_to_lab_flatten_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN
  CASES_ON `p:(A)stack_prog` THEN REWRITE_TAC[stack_get_labels_def] THEN
  CAKE_REWRITE_TAC[NOT_IN_EMPTY; LET_DEF; LET_END_DEF] THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  REPEAT (PAIRARG_TAC ORELSE S2LP1AUX_TOP_CASE_TAC) THEN GVS[NOT_IN_EMPTY] THEN
  REWRITE_TAC[S2LP1AUX_code_installed_APPEND_EQ; stack_to_labProof_code_installed_def;
              is_Label_def; not_is_Label_compile_jump; APPEND] THEN
  CAKE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[stack_get_labels_def; NOT_IN_EMPTY]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN RES_TAC THEN SIMP[]);;

(* HOL4 line 155 [local] *)
let asm_fetch_aux_SOME_append = prove
 (`!pc (code:((A)sec)list) l code2.
     asm_fetch_aux pc code = SOME l ==> asm_fetch_aux pc (APPEND code code2) = SOME l`,
  MATCH_MP_TAC asm_fetch_aux_ind THEN
  REWRITE_TAC[asm_fetch_aux_def; APPEND; option_DISTINCT] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

(* HOL4 line 163 [local] (HOL4 <<= is isPREFIX) *)
let asm_fetch_aux_SOME_isPREFIX = prove
 (`!pc (code:((A)sec)list) l code2.
     asm_fetch_aux pc code = SOME l /\ code <<= code2 ==> asm_fetch_aux pc code2 = SOME l`,
  REWRITE_TAC[IS_PREFIX_APPEND] THEN MESON_TAC[asm_fetch_aux_SOME_append]);;

(* HOL4 line 173 *)
let loc_to_pc_APPEND = prove
 (`!n m (code:((A)sec)list) pc code2.
     loc_to_pc n m code = SOME pc ==> loc_to_pc n m (APPEND code code2) = SOME pc`,
  MATCH_MP_TAC loc_to_pc_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[loc_to_pc_def; option_DISTINCT]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[APPEND] THEN ONCE_REWRITE_TAC[loc_to_pc_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `xs:((A)line)list` THEN CAKE_REWRITE_TAC[] THEN FS[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `loc_to_pc n1 n2 (CONS (Section k a1) (ys:((A)sec)list))` THEN
  CAKE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  RES_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `code2:((A)sec)list`]) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CAKE_REWRITE_TAC[option_INJ]);;

(* HOL4 line 195 *)
let code_installed_APPEND = prove
 (`!ls pc (code:((A)sec)list) code2.
     stack_to_labProof_code_installed pc ls code
     ==> stack_to_labProof_code_installed pc ls (APPEND code code2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[stack_to_labProof_code_installed_def] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [CASES_ON `h:(A)line` THEN FS[] THEN ASM_MESON_TAC[loc_to_pc_APPEND];
    ASM_MESON_TAC[asm_fetch_aux_SOME_append]]);;

(* HOL4 line 208 *)
let code_installed_isPREFIX = prove
 (`!ls pc (code:((A)sec)list) code2.
     stack_to_labProof_code_installed pc ls code /\ code <<= code2
     ==> stack_to_labProof_code_installed pc ls code2`,
  REWRITE_TAC[IS_PREFIX_APPEND] THEN MESON_TAC[code_installed_APPEND]);;

(* HOL4 line 219 *)
let loc_to_pc_isPREFIX = prove
 (`!n m (code:((A)sec)list) pc code2.
     loc_to_pc n m code = SOME pc /\ code <<= code2 ==> loc_to_pc n m code2 = SOME pc`,
  REWRITE_TAC[IS_PREFIX_APPEND] THEN MESON_TAC[loc_to_pc_APPEND]);;

(* HOL4 line 228 [local] *)
let MAP_prog_to_section_FST = prove
 (CASE_TERM
  `!(prog:(num#(A)stack_prog)list).
     MAP (\s. match s with Section n v -> n) (MAP prog_to_section prog) = MAP FST prog`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP] THEN ASM_REWRITE_TAC[CONS_11] THEN
  SPEC_TAC(`h:num#(A)stack_prog`,`h:num#(A)stack_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; prog_to_section_def] THEN REPEAT GEN_TAC THEN
  REPEAT PAIRARG_TAC THEN CAKE_REWRITE_TAC[FST]);;

(* HOL4 line 236 *)
let MAP_prog_to_section_Section_num = prove
 (`!(prog:(num#(A)stack_prog)list).
     MAP Section_num (MAP prog_to_section prog) = MAP FST prog`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP] THEN ASM_REWRITE_TAC[CONS_11] THEN
  SPEC_TAC(`h:num#(A)stack_prog`,`h:num#(A)stack_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; prog_to_section_def] THEN REPEAT GEN_TAC THEN
  REPEAT PAIRARG_TAC THEN REWRITE_TAC[lab_Section_num_def; FST]);;

(* skipping the lines of a section in asm_fetch_aux (local helper of        *)
(* asm_fetch_aux_SOME_append2 and loc_to_pc_append2; asm_fetch_aux_add below *)
(* is the HOL4 form with the count on the right)                            *)
let S2LP1AUX_asm_fetch_aux_skip = prove
 (`!ls k pc (rest:((A)sec)list).
     asm_fetch_aux (LENGTH (FILTER ((~) o is_Label) ls) + pc) (CONS (Section k ls) rest) =
     asm_fetch_aux pc rest`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[asm_fetch_aux_def; FILTER; o_THM; LENGTH; ADD_CLAUSES] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[LENGTH; ADD_CLAUSES; NOT_SUC; SUC_SUB1]);;

(* HOL4 line 245 *)
let asm_fetch_aux_SOME_append2 = prove
 (`!pc (code:((A)sec)list) l code2.
     asm_fetch_aux pc code2 = SOME l
     ==> asm_fetch_aux
           (LENGTH (FLAT (MAP (FILTER ((~) o is_Label) o Section_lines) code)) + pc)
           (APPEND code code2) = SOME l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; FLAT; LENGTH; ADD_CLAUSES; APPEND] THEN
  SPEC_TAC(`h:(A)sec`,`h:(A)sec`) THEN MATCH_MP_TAC sec_INDUCT THEN
  REWRITE_TAC[o_THM; lab_Section_lines_def; LENGTH_APPEND; GSYM ADD_ASSOC;
              S2LP1AUX_asm_fetch_aux_skip] THEN
  ASM_REWRITE_TAC[]);;

(* loc_to_pc over a section of other labels (local helper of                 *)
(* loc_to_pc_append2)                                                        *)
let S2LP1AUX_loc_to_pc_skip = prove
 (`!ls n k ll (rest:((A)sec)list) pc.
     ~(n = k) /\ ALL (sec_label_ok n) ls /\ loc_to_pc k ll rest = SOME pc
     ==> loc_to_pc k ll (CONS (Section n ls) rest) =
         SOME (pc + LENGTH (FILTER ((~) o is_Label) ls))`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[loc_to_pc_def] THEN
  REWRITE_TAC[FILTER; LENGTH; ADD_CLAUSES; ALL; o_THM] THEN
  CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((?j. (h:(A)line) = lab_Label k ll j) /\ ~(ll = 0))` ASSUME_TAC THENL
   [STRIP_TAC THEN UNDISCH_TAC `sec_label_ok n (h:(A)line)` THEN
    ASM_REWRITE_TAC[sec_label_ok_def];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `k:num`; `ll:num`; `rest:((A)sec)list`;
                                `pc:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ] THEN ARITH_TAC);;

(* HOL4 line 257 *)
let loc_to_pc_append2 = prove
 (`!k ll (code:((A)sec)list) code2 pc.
     ~MEM k (MAP Section_num code) /\
     ALL sec_labels_ok code /\
     loc_to_pc k ll code2 = SOME pc
     ==> loc_to_pc k ll (APPEND code code2) =
         SOME (pc + LENGTH (FLAT (MAP (FILTER ((~) o is_Label) o Section_lines) code)))`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; FLAT; LENGTH; ADD_CLAUSES; APPEND; MEM; ALL] THEN
  SPEC_TAC(`h:(A)sec`,`h:(A)sec`) THEN MATCH_MP_TAC sec_INDUCT THEN
  REWRITE_TAC[o_THM; lab_Section_lines_def; lab_Section_num_def; sec_labels_ok_def;
              LENGTH_APPEND] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a1:((A)line)list`; `a0:num`; `k:num`; `ll:num`;
                 `APPEND t (code2:((A)sec)list)`;
                 `pc + LENGTH (FLAT (MAP (FILTER ((~) o is_Label) o Section_lines)
                                       (t:((A)sec)list)))`]
         S2LP1AUX_loc_to_pc_skip) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[option_INJ] THEN ARITH_TAC);;

(* HOL4 line 278 *)
let code_installed_append2 = prove
 (`!lines pc (c1:((A)sec)list) c2 k.
     ~MEM k (MAP Section_num c1) /\
     ALL sec_labels_ok c1 /\
     ALL (sec_label_ok k) lines /\
     stack_to_labProof_code_installed pc lines c2
     ==> stack_to_labProof_code_installed
           (LENGTH (FLAT (MAP (FILTER ((~) o is_Label) o Section_lines) c1)) + pc)
           lines (APPEND c1 c2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[stack_to_labProof_code_installed_def; ALL] THEN
  REPEAT GEN_TAC THEN CASES_ON `h:(A)line` THEN
  REWRITE_TAC[is_Label_def; sec_label_ok_def] THEN CAKE_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [RVEQ_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`k:num`; `a1:num`; `c1:((A)sec)list`; `c2:((A)sec)list`; `pc:num`]
               loc_to_pc_append2) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ADD_SYM];
      ASM_MESON_TAC[]];
    CONJ_TAC THENL
     [ASM_MESON_TAC[asm_fetch_aux_SOME_append2];
      FIRST_X_ASSUM(MP_TAC o SPECL [`pc + 1`; `c1:((A)sec)list`; `c2:((A)sec)list`;
                                    `k:num`]) THEN
      ASM_REWRITE_TAC[ADD_ASSOC]];
    CONJ_TAC THENL
     [ASM_MESON_TAC[asm_fetch_aux_SOME_append2];
      FIRST_X_ASSUM(MP_TAC o SPECL [`pc + 1`; `c1:((A)sec)list`; `c2:((A)sec)list`;
                                    `k:num`]) THEN
      ASM_REWRITE_TAC[ADD_ASSOC]]]);;

(* HOL4 line 309 *)
let ALOOKUP_PARTITION = prove
 (`!(ls:(A#B)list) n v.
     ALOOKUP ls n = SOME v
     ==> ?ls1 ls2. ls = APPEND (APPEND ls1 [(n,v)]) ls2 /\ ~MEM n (MAP FST ls1)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_THM; option_DISTINCT] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; ALOOKUP_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [REWRITE_TAC[option_INJ] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`[]:(A#B)list`; `t:(A#B)list`] THEN
    ASM_REWRITE_TAC[APPEND; MAP; MEM];
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `ls1:(A#B)list` (X_CHOOSE_THEN `ls2:(A#B)list`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`CONS ((p1:A),(p2:B)) ls1`; `ls2:(A#B)list`] THEN
    ASM_REWRITE_TAC[APPEND; MAP; MEM; FST]]);;

(* HOL4 line 325 *)
let code_installed'_def = cake_def
  `(code_installed' n ([]:((A)line)list) (code:((A)sec)list) <=> T) /\
   (code_installed' n (CONS x xs) code <=>
      if is_Label x then code_installed' n xs code
      else asm_fetch_aux n code = SOME x /\ code_installed' (n + 1) xs code)`;;

(* HOL4 line 332 (h, n, xs and other are free in HOL4) *)
let code_installed'_cons_label = prove
 (`!lines pos (h:(A)line) n xs other.
     is_Label h
     ==> (code_installed' pos lines (CONS (Section n (CONS h xs)) other) <=>
          code_installed' pos lines (CONS (Section n xs) other))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[code_installed'_def] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[asm_fetch_aux_def]);;

(* HOL4 line 342: Theorem code_installed'_cons_non_label = Q.prove (...) |> *)
(* Q.SPECL [lines, 0] |> SIMP_RULE std_ss [] (its resulting statement) *)
let code_installed'_cons_non_label = prove
 (`!lines (h:(A)line) n xs other.
     ~is_Label h
     ==> (code_installed' 1 lines (CONS (Section n (CONS h xs)) other) <=>
          code_installed' 0 lines (CONS (Section n xs) other))`,
  SUBGOAL_THEN
   `!lines pos (h:(A)line) n xs other.
      ~is_Label h
      ==> (code_installed' (pos + 1) lines (CONS (Section n (CONS h xs)) other) <=>
           code_installed' pos lines (CONS (Section n xs) other))`
   (fun th -> REPEAT GEN_TAC THEN
              MP_TAC(SPECL [`lines:((A)line)list`; `0`; `h:(A)line`; `n:num`;
                            `xs:((A)line)list`; `other:((A)sec)list`] th) THEN
              REWRITE_TAC[ADD_CLAUSES]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[code_installed'_def] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[asm_fetch_aux_def; ADD_EQ_0; ARITH_EQ; ADD_SUB]);;

(* HOL4 line 351 *)
let code_installed'_simp = prove
 (`!lines n rest (other:((A)sec)list).
     code_installed' 0 lines (CONS (Section n (APPEND lines rest)) other)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[code_installed'_def; APPEND] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[code_installed'_cons_label; code_installed'_cons_non_label;
               asm_fetch_aux_def; ADD_CLAUSES]);;

(* HOL4 line 360 *)
let loc_to_pc_skip_section = prove
 (CASE_TERM
  `!lines n p (xs:((A)sec)list).
     ~(n = p)
     ==> loc_to_pc n 0 (CONS (Section p lines) xs) =
         (match loc_to_pc n 0 xs with
            NONE -> NONE
          | SOME k -> SOME (k + LENGTH (FILTER (\x. ~is_Label x) lines)))`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[loc_to_pc_def] THEN
  ASM_REWRITE_TAC[FILTER; LENGTH; ADD_CLAUSES] THEN CAKE_REWRITE_TAC[] THENL
   [CASES_ON `loc_to_pc n 0 (xs:((A)sec)list)` THEN CAKE_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `p:num`; `xs:((A)sec)list`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN
  CASES_ON `loc_to_pc n 0 (xs:((A)sec)list)` THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ] THEN ARITH_TAC);;

(* HOL4 line 373 *)
let asm_fetch_aux_add = prove
 (`!ys pc (rest:((A)sec)list) pos.
     asm_fetch_aux (pc + LENGTH (FILTER (\x. ~is_Label x) ys)) (CONS (Section pos ys) rest) =
     asm_fetch_aux pc rest`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\x. ~is_Label x) = ((~) o is_Label:(A)line->bool)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[S2LP1AUX_asm_fetch_aux_skip]);;

(* HOL4 line 381 *)
let labs_correct_def = cake_def
  `(labs_correct n ([]:((A)line)list) (code:((A)sec)list) <=> T) /\
   (labs_correct n (CONS x xs) code <=>
      if is_Label x then
        labs_correct n xs code /\
        (match x with
           lab_Label l1 l2 v2 -> loc_to_pc l1 l2 code = SOME n
         | _ -> T)
      else labs_correct (n + 1) xs code)`;;

(* HOL4 line 391: val is_Label_def = labSemTheory.is_Label_def (an          *)
(* abbreviation) *)

(* HOL4 line 393 *)
let code_installed_eq = prove
 (`!pc xs (code:((A)sec)list).
     stack_to_labProof_code_installed pc xs code <=>
     code_installed' pc xs code /\ labs_correct pc xs code`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[stack_to_labProof_code_installed_def; code_installed'_def;
              labs_correct_def] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [CASES_ON `h:(A)line` THEN FS[] THEN CONV_TAC TAUT;
    CONV_TAC TAUT]);;

(* HOL4 line 406 (rest is free in HOL4) *)
let stack_to_labProof_code_installed_cons = prove
 (`!xs ys pos pc (rest:((A)sec)list).
     code_installed' pc xs rest
     ==> code_installed' (pc + LENGTH (FILTER (\x. ~is_Label x) ys)) xs
           (CONS (Section pos ys) rest)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[code_installed'_def] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[asm_fetch_aux_add] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ys:((A)line)list`; `pos:num`; `pc + 1`;
                                `rest:((A)sec)list`]) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH_RULE `(pc + 1) + l = (pc + l) + 1`]);;

(* the section made by prog_to_section is named by its first argument      *)
(* (local helper)                                                            *)
let S2LP1AUX_prog_to_section_Section = prove
 (`!n (p:(A)stack_prog). ?ls. prog_to_section (n,p) = Section n ls`,
  REPEAT GEN_TAC THEN REWRITE_TAC[prog_to_section_def] THEN
  REPEAT PAIRARG_TAC THEN MESON_TAC[]);;

(* HOL4 line 417 [local] *)
let code_installed_prog_to_section_lemma = prove
 (`!(prog4:(num#(A)stack_prog)list) n prog3.
     ALOOKUP prog4 n = SOME prog3
     ==> ?pc. code_installed' pc
                (append (FST (stack_to_lab_flatten T prog3 n (next_lab prog3 2) [] [])))
                (MAP prog_to_section prog4) /\
              loc_to_pc n 0 (MAP prog_to_section prog4) = SOME pc`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_THM; option_DISTINCT; MAP] THEN
  SPEC_TAC(`h:num#(A)stack_prog`,`h:num#(A)stack_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; ALOOKUP_THM] THEN
  MAP_EVERY X_GEN_TAC [`n0:num`; `p0:(A)stack_prog`; `n:num`; `prog3:(A)stack_prog`] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[option_INJ] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[prog_to_section_def] THEN
    REPEAT PAIRARG_TAC THEN ONCE_REWRITE_TAC[loc_to_pc_def] THEN
    REWRITE_TAC[FST; append_thm; code_installed'_simp];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `prog3:(A)stack_prog`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `pc:num` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`n0:num`; `p0:(A)stack_prog`] S2LP1AUX_prog_to_section_Section) THEN
    DISCH_THEN(X_CHOOSE_THEN `ls:((A)line)list` SUBST1_TAC) THEN
    EXISTS_TAC `pc + LENGTH (FILTER (\x. ~is_Label x) (ls:((A)line)list))` THEN
    ASM_SIMP_TAC[stack_to_labProof_code_installed_cons; loc_to_pc_skip_section] THEN
    CAKE_REWRITE_TAC[]]);;

(* HOL4 lines 434-435: val extract_labels_def, extract_labels_append (the   *)
(* labProps theorems, abbreviations for the proofs)                          *)

(* a label of the section is found after the lines before it (local helper *)
(* of labs_correct_hd)                                                       *)
let S2LP1AUX_loc_to_pc_label = prove
 (`!extra n l2 v ts (code:((A)sec)list).
     ~(l2 = 0) /\ ~MEM (n,l2) (lab_extract_labels extra)
     ==> loc_to_pc n l2 (CONS (Section n (APPEND extra (CONS (lab_Label n l2 v) ts))) code) =
         SOME (LENGTH (FILTER (\x. ~is_Label x) extra))`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[loc_to_pc_def] THEN
  ASM_REWRITE_TAC[APPEND; FILTER; LENGTH] THEN CAKE_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(?k. (h:(A)line) = lab_Label n l2 k)` ASSUME_TAC THENL
   [STRIP_TAC THEN UNDISCH_TAC `~MEM (n,l2) (lab_extract_labels (CONS (h:(A)line) t))` THEN
    ASM_REWRITE_TAC[lab_extract_labels_def; MEM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~MEM (n,l2) (lab_extract_labels (t:((A)line)list))` ASSUME_TAC THENL
   [UNDISCH_TAC `~MEM (n,l2) (lab_extract_labels (CONS (h:(A)line) t))` THEN
    SPEC_TAC(`h:(A)line`,`h:(A)line`) THEN MATCH_MP_TAC line_INDUCT THEN
    REWRITE_TAC[lab_extract_labels_def; MEM; DE_MORGAN_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `l2:num`; `v:num`; `ts:((A)line)list`;
                                `code:((A)sec)list`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ] THEN ARITH_TAC);;

(* HOL4 line 437 (n and code are free in HOL4; extract_labels is labProps')  *)
let labs_correct_hd = prove
 (`!extra l n (code:((A)sec)list).
     ALL_DISTINCT (lab_extract_labels (APPEND extra l)) /\
     ALL (\(l1,l2). l1 = n /\ ~(l2 = 0)) (lab_extract_labels (APPEND extra l))
     ==> labs_correct (LENGTH (FILTER (\x. ~is_Label x) extra)) l
           (CONS (Section n (APPEND extra l)) code)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[labs_correct_def] THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN `APPEND extra (CONS h t) = APPEND (APPEND extra [h:(A)line]) t`
    SUBST1_TAC THENL [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`APPEND extra [h:(A)line]`; `n:num`;
                                `code:((A)sec)list`]) THEN
  ASM_REWRITE_TAC[FILTER_APPEND; LENGTH_APPEND; FILTER] THEN
  CASES_ON `h:(A)line` THEN REWRITE_TAC[is_Label_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH; ADD_CLAUSES; ADD1] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[extract_labels_append; lab_extract_labels_def; ALL_APPEND;
    ALL; ALL_DISTINCT_APPEND; ALL_DISTINCT; MEM_APPEND; MEM]) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV GEN_BETA_CONV)) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN RVEQ_TAC THEN
  MATCH_MP_TAC S2LP1AUX_loc_to_pc_label THEN ASM_MESON_TAC[]);;

(* HOL4 line 468 *)
let labels_ok_def = cake_def
  `labels_ok (code:((A)sec)list) <=>
     ALL_DISTINCT (MAP (\s. match s with Section n _ -> n) code) /\
     ALL (\s. match s with
                Section n lines ->
                  (let labs = lab_extract_labels lines in
                     ALL (\(l1,l2). l1 = n /\ ~(l2 = 0)) labs /\ ALL_DISTINCT labs)) code`;;

(* HOL4 line 478 *)
let labels_ok_imp = prove
 (`!(code:((A)sec)list).
     labels_ok code
     ==> ALL sec_labels_ok code /\
         ALL_DISTINCT (MAP Section_num code) /\
         ALL (ALL_DISTINCT o lab_extract_labels o Section_lines) code`,
  GEN_TAC THEN REWRITE_TAC[labels_ok_def] THEN
  SUBGOAL_THEN (CASE_TERM `!s:(A)sec. (match s with Section n _ -> n) = Section_num s`)
    (fun th -> REWRITE_TAC[th; ETA_AX]) THENL
   [MATCH_MP_TAC sec_INDUCT THEN CAKE_REWRITE_TAC[lab_Section_num_def]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  DISCH_TAC THEN CONJ_TAC THEN X_GEN_TAC `s:(A)sec` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:(A)sec`) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`s:(A)sec`,`s:(A)sec`) THEN MATCH_MP_TAC sec_INDUCT THEN
  CAKE_REWRITE_TAC[LET_DEF; LET_END_DEF; sec_labels_ok_def; o_THM;
                   lab_Section_lines_def; GSYM EVERY_sec_label_ok] THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[]);;

(* labels_ok of a section and more code (local helper) *)
let S2LP1AUX_labels_ok_cons = prove
 (`(labels_ok ([]:((A)sec)list) <=> T) /\
   (!n l (code:((A)sec)list).
      labels_ok (CONS (Section n l) code) <=>
      ~MEM n (MAP Section_num code) /\ ALL (sec_label_ok n) l /\
      ALL_DISTINCT (lab_extract_labels l) /\ labels_ok code)`,
  REWRITE_TAC[labels_ok_def; MAP; ALL_DISTINCT; ALL] THEN
  SUBGOAL_THEN (CASE_TERM `!s:(A)sec. (match s with Section n _ -> n) = Section_num s`)
    (fun th -> REWRITE_TAC[th; ETA_AX]) THENL
   [MATCH_MP_TAC sec_INDUCT THEN CAKE_REWRITE_TAC[lab_Section_num_def]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  CAKE_REWRITE_TAC[LET_DEF; LET_END_DEF; lab_Section_num_def; GSYM EVERY_sec_label_ok] THEN
  CONV_TAC TAUT);;

(* (\x. ~is_Label x) is (~) o is_Label (local helper) *)
let S2LP1AUX_o_is_Label = prove
 (`((~) o is_Label:(A)line->bool) = (\x. ~is_Label x)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM]);;

(* labs_correct over a section with another name (local helper of         *)
(* labels_ok_labs_correct)                                                   *)
let S2LP1AUX_labs_correct_cons = prove
 (`!ls pc n m lines (code:((A)sec)list).
     ~(n = m) /\ ALL (sec_label_ok m) ls /\ ALL (sec_label_ok n) lines /\
     labs_correct pc ls code
     ==> labs_correct (pc + LENGTH (FILTER (\x. ~is_Label x) lines)) ls
           (CONS (Section n lines) code)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[labs_correct_def; ALL] THEN
  REPEAT GEN_TAC THEN CASES_ON `h:(A)line` THEN
  REWRITE_TAC[is_Label_def; sec_label_ok_def] THEN CAKE_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [RVEQ_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MP_TAC(ISPECL [`lines:((A)line)list`; `n:num`; `m:num`; `a1:num`;
                     `code:((A)sec)list`; `pc:num`] S2LP1AUX_loc_to_pc_skip) THEN
      ASM_REWRITE_TAC[S2LP1AUX_o_is_Label]];
    FIRST_X_ASSUM(MP_TAC o SPECL [`pc + 1`; `n:num`; `m:num`; `lines:((A)line)list`;
                                  `code:((A)sec)list`]) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH_RULE `(pc + 1) + l = (pc + l) + 1`];
    FIRST_X_ASSUM(MP_TAC o SPECL [`pc + 1`; `n:num`; `m:num`; `lines:((A)line)list`;
                                  `code:((A)sec)list`]) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH_RULE `(pc + 1) + l = (pc + l) + 1`]]);;

(* HOL4 line 499 *)
let labels_ok_labs_correct = prove
 (CASE_TERM
  `!(code:((A)sec)list).
     labels_ok code
     ==> ALL (\s. match s with
                    Section n lines ->
                      (match loc_to_pc n 0 code with
                         SOME pc -> labs_correct pc lines code
                       | _ -> T)) code`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THEN
  SPEC_TAC(`h:(A)sec`,`h:(A)sec`) THEN MATCH_MP_TAC sec_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `l:((A)line)list`] THEN
  REWRITE_TAC[S2LP1AUX_labels_ok_cons] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [CAKE_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[loc_to_pc_def] THEN CAKE_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`[]:((A)line)list`; `l:((A)line)list`; `n:num`; `t:((A)sec)list`]
             labs_correct_hd) THEN
    REWRITE_TAC[APPEND; FILTER; LENGTH; EVERY_sec_label_ok] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL sec_labels_ok (t:((A)sec)list)` MP_TAC THENL
   [ASM_MESON_TAC[labels_ok_imp]; ALL_TAC] THEN
  UNDISCH_TAC `~MEM n (MAP Section_num (t:((A)sec)list))` THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN
  REPEAT DISCH_TAC THEN X_GEN_TAC `s:(A)sec` THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `s:(A)sec` o check (is_forall o concl))) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `s:(A)sec` THEN
  REWRITE_TAC[sec_labels_ok_def; lab_Section_num_def] THEN CAKE_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(a0:num = n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lab_Section_num_def]; ALL_TAC] THEN
  ASM_SIMP_TAC[loc_to_pc_skip_section] THEN
  CASES_ON `loc_to_pc a0 0 (t:((A)sec)list)` THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN CAKE_REWRITE_TAC[] THEN
  MATCH_MP_TAC S2LP1AUX_labs_correct_cons THEN ASM_MESON_TAC[]);;

(* HOL4 line 569 (rest and code are free in HOL4) *)
let labs_correct_append = prove
 (`!ls pc rest (code:((A)sec)list).
     labs_correct pc (APPEND ls rest) code ==> labs_correct pc ls code`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[labs_correct_def; APPEND] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 577 *)
let code_installed_prog_to_section = prove
 (`!(prog4:(num#(A)stack_prog)list) n prog3.
     labels_ok (MAP prog_to_section prog4) /\ ALOOKUP prog4 n = SOME prog3
     ==> ?pc. stack_to_labProof_code_installed pc
                (append (FST (stack_to_lab_flatten T prog3 n (next_lab prog3 2) [] [])))
                (MAP prog_to_section prog4) /\
              loc_to_pc n 0 (MAP prog_to_section prog4) = SOME pc`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[code_installed_eq] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP code_installed_prog_to_section_lemma) THEN
  DISCH_THEN(X_CHOOSE_THEN `pc:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `pc:num` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP labels_ok_labs_correct) THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN
  DISCH_THEN(MP_TAC o SPEC `prog_to_section (n:num,prog3:(A)stack_prog)`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ALOOKUP_MEM]; ALL_TAC] THEN
  REWRITE_TAC[prog_to_section_def] THEN REPEAT PAIRARG_TAC THEN
  UNDISCH_TAC `loc_to_pc n 0 (MAP prog_to_section (prog4:(num#(A)stack_prog)list)) =
               SOME pc` THEN
  REWRITE_TAC[FST; append_thm] THEN DISCH_THEN SUBST1_TAC THEN CAKE_REWRITE_TAC[] THEN
  MESON_TAC[labs_correct_append]);;

(* HOL4 line 601 (extract_labels of stackLang programs is stackProps';       *)
(* the third component of the oracle, HOL4 _, is named b0) *)
let stack_to_labProof_state_rel_def = cake_def
  `stack_to_labProof_state_rel (s:(A,C,FFI)stack_state) (t:(A,C,FFI)lab_state) <=>
     (!n v. FLOOKUP (stack_state_regs s) n = SOME v ==> lab_state_regs t n = v) /\
     (!n v. FLOOKUP (stack_state_fp_regs s) n = SOME v ==> lab_state_fp_regs t n = v) /\
     lab_state_mem t = stack_state_memory s /\
     lab_state_mem_domain t = stack_state_mdomain s /\
     lab_state_shared_mem_domain t = stack_state_sh_mdomain s /\
     lab_state_be t = stack_state_be s /\
     lab_state_ffi t = stack_state_ffi s /\
     lab_state_clock t = stack_state_clock s /\
     (!n prog.
        lookup n (stack_state_code s) = SOME prog
        ==> call_args prog (lab_state_ptr_reg t) (lab_state_len_reg t) (lab_state_ptr2_reg t)
              (lab_state_len2_reg t) (lab_state_link_reg t) /\
            ?pc. stack_to_labProof_code_installed pc
                   (append (FST (stack_to_lab_flatten T prog n (next_lab prog 2) [] [])))
                   (lab_state_code t) /\
                 loc_to_pc n 0 (lab_state_code t) = SOME pc) /\
     domain (stack_state_code s) = set_of_list (MAP Section_num (lab_state_code t)) /\
     ALL sec_labels_ok (lab_state_code t) /\
     ~lab_state_failed t /\
     ~(lab_state_link_reg t = lab_state_len_reg t) /\
     ~(lab_state_link_reg t = lab_state_ptr_reg t) /\
     ~(lab_state_link_reg t = lab_state_len2_reg t) /\
     ~(lab_state_link_reg t = lab_state_ptr2_reg t) /\
     ~(lab_state_link_reg t IN stack_state_ffi_save_regs s) /\
     (!k i n. k IN stack_state_ffi_save_regs s ==> lab_state_io_regs t n i k = NONE) /\
     (!k n. k IN stack_state_ffi_save_regs s ==> lab_state_cc_regs t n k = NONE) /\
     (!x. x IN stack_state_mdomain s ==> val x MOD (dimindex (:A) DIV 8) = 0) /\
     (!x. x IN stack_state_sh_mdomain s ==> val x MOD (dimindex (:A) DIV 8) = 0) /\
     stack_state_code_buffer s = lab_state_code_buffer t /\
     stack_state_compile s = (\c p. lab_state_compile t c (MAP prog_to_section p)) /\
     lab_state_compile_oracle t =
       (\n. let (c,p,b0) = stack_state_compile_oracle s n in (c,MAP prog_to_section p)) /\
     (!k. let (c,ps,b0) = stack_state_compile_oracle s k in
            ALL (\(n,p).
                   call_args p (lab_state_ptr_reg t) (lab_state_len_reg t)
                     (lab_state_ptr2_reg t) (lab_state_len2_reg t) (lab_state_link_reg t) /\
                   ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
                   ALL_DISTINCT (stack_extract_labels p)) ps /\
            ALL_DISTINCT (MAP FST ps)) /\
     ~stack_state_use_stack s /\
     ~stack_state_use_store s /\
     ~stack_state_use_alloc s /\
     good_dimindex (:A)`;;

(* HOL4 line 645 *)
let loc_check_IMP_loc_to_pc = prove
 (`!(s:(A,C,FFI)stack_state) l1 l2 t1.
     loc_check (stack_state_code s) (l1,l2) /\ stack_to_labProof_state_rel s t1
     ==> ?v. loc_to_pc l1 l2 (lab_state_code t1) = SOME v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[loc_check_def; domain_lookup] THEN
  REWRITE_TAC[stack_to_labProof_state_rel_def] THEN STRIP_TAC THEN
  RVEQ_TAC THEN RES_TAC THEN ASM_MESON_TAC[code_installed_get_labels_IMP]);;

(* HOL4 line 655 *)
let stack_to_labProof_state_rel_dec_clock = prove
 (`!(s:(A,C,FFI)stack_state) t.
     stack_to_labProof_state_rel s t
     ==> stack_to_labProof_state_rel (stack_dec_clock s) (lab_dec_clock t)`,
  REWRITE_TAC[stack_to_labProof_state_rel_def; stack_dec_clock_def; lab_dec_clock_def] THEN
  SIMP[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 662 *)
let state_rel_with_pc = prove
 (`!(s:(A,C,FFI)stack_state) t pc.
     stack_to_labProof_state_rel s t ==> stack_to_labProof_state_rel s (lab_upd_pc pc t)`,
  REWRITE_TAC[stack_to_labProof_state_rel_def; lab_upd_pc_def] THEN
  SIMP[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 669 *)
let stack_to_labProof_state_rel_with_clock = prove
 (`!(s:(A,C,FFI)stack_state) t k.
     stack_to_labProof_state_rel s t
     ==> stack_to_labProof_state_rel (stack_state_clock_fupd (combin_K k) s)
           (lab_state_clock_fupd (combin_K k) t)`,
  REWRITE_TAC[stack_to_labProof_state_rel_def] THEN
  SIMP[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 675 *)
let set_var_upd_reg = prove
 (`!(s:(A,C,FFI)stack_state) t a b.
     stack_to_labProof_state_rel s t
     ==> stack_to_labProof_state_rel (stack_set_var a b s) (lab_upd_reg a b t)`,
  REWRITE_TAC[stack_to_labProof_state_rel_def; stack_set_var_def; lab_upd_reg_def] THEN
  SIMP[FLOOKUP_UPDATE; APPLY_UPDATE_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN TRY(ASM_MESON_TAC[]) THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[option_INJ]);;

(* HOL4 line 683 [simp] *)
let set_var_Word_upd_reg = prove
 (`!(s:(A,C,FFI)stack_state) t a b.
     stack_to_labProof_state_rel s t
     ==> stack_to_labProof_state_rel (stack_set_var a (wl_Word b) s)
           (lab_upd_reg a (wl_Word b) t)`,
  MESON_TAC[set_var_upd_reg]);;

let _ = cake_add_simps [set_var_Word_upd_reg];;

(* HOL4 line 690 *)
let set_fp_var_upd_fp_reg = prove
 (`!(s:(A,C,FFI)stack_state) t a b.
     stack_to_labProof_state_rel s t
     ==> stack_to_labProof_state_rel (stack_set_fp_var a b s) (lab_upd_fp_reg a b t)`,
  REWRITE_TAC[stack_to_labProof_state_rel_def; stack_set_fp_var_def; lab_upd_fp_reg_def] THEN
  SIMP[FLOOKUP_UPDATE; APPLY_UPDATE_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN TRY(ASM_MESON_TAC[]) THEN
  POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[option_INJ]);;

(* HOL4 line 698 *)
let mem_store_upd_mem = prove
 (`!(s:(A,C,FFI)stack_state) t x y s1.
     stack_to_labProof_state_rel s t /\ stack_mem_store x y s = SOME s1
     ==> stack_to_labProof_state_rel s1 (lab_upd_mem x y t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_mem_store_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[stack_to_labProof_state_rel_def; lab_upd_mem_def] THEN
  SIMP[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 711 (HOL4 read_reg x t, an Overload of labSem, is              *)
(* lab_state_regs t x) *)
let state_rel_read_reg_FLOOKUP_regs = prove
 (`!(s:(A,C,FFI)stack_state) t x y.
     stack_to_labProof_state_rel s t /\ FLOOKUP (stack_state_regs s) x = SOME y
     ==> y = lab_state_regs t x`,
  REWRITE_TAC[stack_to_labProof_state_rel_def] THEN MESON_TAC[]);;

(* HOL4 line 719 *)
let state_rel_read_fp_reg_FLOOKUP_fp_regs = prove
 (`!(s:(A,C,FFI)stack_state) t n x.
     stack_to_labProof_state_rel s t /\ stack_get_fp_var n s = SOME x
     ==> x = lab_read_fp_reg n t`,
  REWRITE_TAC[stack_to_labProof_state_rel_def; stack_get_fp_var_def; lab_read_fp_reg_def] THEN
  MESON_TAC[]);;

(* HOL4 line 728 *)
let state_rel_get_var_imm = prove
 (`!(s:(A,C,FFI)stack_state) t r x.
     stack_to_labProof_state_rel s t /\ stack_get_var_imm r s = SOME x
     ==> lab_reg_imm r t = x`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN CASES_ON `r:(A)reg_imm` THEN
  REWRITE_TAC[stack_get_var_imm_def; lab_reg_imm_def; stack_get_var_def; option_INJ] THEN
  MESON_TAC[state_rel_read_reg_FLOOKUP_regs]);;

(* ------------------------------------------------------------------------- *)
(* Local helpers of inst_correct: what state_rel says about registers,      *)
(* memory and the memory domain, and memory updates.                        *)
(* ------------------------------------------------------------------------- *)

let S2LP1AUX_rel_regs = prove
 (`!(s:(A,C,FFI)stack_state) t r v.
     stack_to_labProof_state_rel s t /\ FLOOKUP (stack_state_regs s) r = SOME v
     ==> lab_state_regs t r = v`,
  REWRITE_TAC[stack_to_labProof_state_rel_def] THEN MESON_TAC[]);;

let S2LP1AUX_rel_fp_regs = prove
 (`!(s:(A,C,FFI)stack_state) t d f.
     stack_to_labProof_state_rel s t /\ FLOOKUP (stack_state_fp_regs s) d = SOME f
     ==> lab_state_fp_regs t d = f`,
  REWRITE_TAC[stack_to_labProof_state_rel_def] THEN MESON_TAC[]);;

let S2LP1AUX_rel_mem = prove
 (`!(s:(A,C,FFI)stack_state) t.
     stack_to_labProof_state_rel s t
     ==> lab_state_mem t = stack_state_memory s /\
         lab_state_mem_domain t = stack_state_mdomain s /\
         lab_state_be t = stack_state_be s /\
         (!x. x IN stack_state_mdomain s ==> val x MOD (dimindex (:A) DIV 8) = 0)`,
  SIMP_TAC[stack_to_labProof_state_rel_def]);;

let S2LP1AUX_rel_memory_fupd = prove
 (`!(s:(A,C,FFI)stack_state) t m.
     stack_to_labProof_state_rel s t
     ==> stack_to_labProof_state_rel (stack_state_memory_fupd (combin_K m) s)
           (lab_state_mem_fupd (combin_K m) t)`,
  REWRITE_TAC[stack_to_labProof_state_rel_def] THEN
  SIMP[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* S2LP1AUX_ASM_CASE_TAC splits the outermost case of the assumptions      *)
let S2LP1AUX_ASM_CASE_TAC : tactic = fun (asl,w as gl) ->
  let whole = list_mk_conj(map (concl o snd) asl) in
  let x = first_case_scrutinee whole whole in
  (S2LP1AUX_CASES_ON x THEN CASE_ASM_TIDY_TAC THEN CASE_TIDY_TAC) gl;;

(* close a goal with two contradictory assumptions P and ~P *)
let S2LP1AUX_CONTRA_TAC : tactic = fun (asl,w as g) ->
  let cs = map (concl o snd) asl in
  let p = find (fun c -> is_neg c && mem (dest_neg c) cs) cs in
  (FIRST_ASSUM(fun th -> if concl th = p then
     FIRST_ASSUM(fun th' -> if concl th' = dest_neg p then
       CONTR_TAC (MP (NOT_ELIM th) th') else NO_TAC) else NO_TAC)) g;;

let S2LP1AUX_INST_RWS = [stack_assign_def; stack_word_exp_def; MAP; ALL; LET_DEF; LET_END_DEF;
   IS_SOME_DEF; THE_DEF; stack_get_vars_def; stack_get_var_def; stack_get_fp_var_def;
   stack_mem_load_def; stack_mem_store_def; word_op_def; option_INJ; option_DISTINCT; ITLIST;
   WORD_ADD_0; WORD_AND_NOT0; WORD_OR_0; WORD_XOR_0];;

let S2LP1AUX_INST_SPLIT_TAC : tactic =
  STRIP_TAC THEN
  REPEAT(RULE_ASSUM_TAC(CAKE_REWRITE_RULE S2LP1AUX_INST_RWS) THEN
         TRY(FIRST_ASSUM CONTR_TAC) THEN S2LP1AUX_ASM_CASE_TAC) THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE S2LP1AUX_INST_RWS) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN
  IMP_RES_TAC S2LP1AUX_rel_regs THEN IMP_RES_TAC S2LP1AUX_rel_fp_regs THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP S2LP1AUX_rel_mem);;

let S2LP1AUX_LAB_RWS = [lab_arith_upd_def; lab_reg_imm_def; lab_fp_upd_def; lab_mem_op_def;
  lab_mem_load_def; lab_mem_store_def; mem_load32_def; mem_store32_def; mem_load_byte_def;
  mem_store_byte_def; lab_addr_def; lab_read_fp_reg_def];;

let S2LP1AUX_INST_FIN_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[word_op_def]) THEN
  REPEAT (S2LP1AUX_ASM_CASE_TAC ORELSE S2LP1AUX_TOP_CASE_TAC) THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE S2LP1AUX_INST_RWS) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN IMP_RES_TAC word_sh_word_shift THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[lab_binop_upd_def; WORD_OR_REFL; ITLIST; WORD_ADD_0; WORD_AND_NOT0;
              WORD_OR_0; WORD_XOR_0; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[assert_T] THEN
  TRY S2LP1AUX_CONTRA_TAC THEN
  RES_TAC THEN REWRITE_TAC[lab_upd_mem_def] THEN ASM_REWRITE_TAC[assert_T] THEN
  REPEAT(MATCH_MP_TAC set_var_upd_reg ORELSE MATCH_MP_TAC set_fp_var_upd_fp_reg ORELSE
         MATCH_MP_TAC S2LP1AUX_rel_memory_fupd) THEN ASM_REWRITE_TAC[];;

let S2LP1AUX_INST_TAC : tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[stack_inst_def; asm_inst_def] THEN CAKE_REWRITE_TAC[] THEN
  S2LP1AUX_INST_SPLIT_TAC THEN
  REWRITE_TAC S2LP1AUX_LAB_RWS THEN
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[])) THEN
  S2LP1AUX_INST_FIN_TAC;;

let S2LP1AUX_inst_arith = prove
 (`!a (s1:(A,C,FFI)stack_state) s2 t1.
     stack_inst (asm_Arith a) s1 = SOME s2 /\ stack_to_labProof_state_rel s1 t1
     ==> stack_to_labProof_state_rel s2 (asm_inst (asm_Arith a) t1)`,
  GEN_TAC THEN CASES_ON `a:(A)asm_arith` THEN S2LP1AUX_INST_TAC);;

let S2LP1AUX_inst_mem = prove
 (`!m r ad (s1:(A,C,FFI)stack_state) s2 t1.
     stack_inst (Mem m r ad) s1 = SOME s2 /\ stack_to_labProof_state_rel s1 t1
     ==> stack_to_labProof_state_rel s2 (asm_inst (Mem m r ad) t1)`,
  GEN_TAC THEN CASES_ON `m:memop` THEN GEN_TAC THEN GEN_TAC THEN CASES_ON `ad:(A)addr` THEN
  S2LP1AUX_INST_TAC);;

let S2LP1AUX_inst_fp = prove
 (`!f (s1:(A,C,FFI)stack_state) s2 t1.
     stack_inst (FP f) s1 = SOME s2 /\ stack_to_labProof_state_rel s1 t1
     ==> stack_to_labProof_state_rel s2 (asm_inst (FP f) t1)`,
  GEN_TAC THEN CASES_ON `f:fp` THEN S2LP1AUX_INST_TAC);;

(* HOL4 line 737 *)
let stack_to_labProof_inst_correct = prove
 (`!i (s1:(A,C,FFI)stack_state) s2 t1.
     stack_inst i s1 = SOME s2 /\ stack_to_labProof_state_rel s1 t1
     ==> stack_to_labProof_state_rel s2 (asm_inst i t1)`,
  GEN_TAC THEN CASES_ON `i:(A)inst` THEN
  REWRITE_TAC[S2LP1AUX_inst_arith; S2LP1AUX_inst_mem; S2LP1AUX_inst_fp] THEN
  S2LP1AUX_INST_TAC);;

(* HOL4 line 890 *)
let flatten_leq = prove
 (`!t (x:(A)stack_prog) y z cs bs. z <= SND (SND (stack_to_lab_flatten t x y z cs bs))`,
  MATCH_MP_TAC stack_to_lab_flatten_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN
  CASES_ON `p:(A)stack_prog` THEN CAKE_REWRITE_TAC[LE_REFL] THEN
  FS[] THEN REPEAT (PAIRARG_TAC ORELSE TOP_CASE_TAC) THEN GVS[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (snd (strip_forall (concl th)))))) THEN
  ASM_SIMP_TAC[] THEN ASM_ARITH_TAC);;

(* HOL4 line 903 [local] *)
let NOT_bad_fun_return_IMP_SOME = prove
 (`!(q:((A)stack_result)option). ~stack_bad_fun_return q ==> ?n. q = SOME n`,
  GEN_TAC THEN CASES_ON `q:((A)stack_result)option` THEN
  REWRITE_TAC[stack_bad_fun_return_def; option_INJ] THEN MESON_TAC[]);;

(* HOL4 line 909 *)
let no_ret_correct = prove
 (`!t (p:(A)stack_prog) y z cs bs.
     FST (SND (stack_to_lab_flatten t p y z cs bs))
     ==> !(s:(A,C,FFI)stack_state). IS_SOME (FST (stack_evaluate (p,s)))`,
  MATCH_MP_TAC stack_to_lab_flatten_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN
  CASES_ON `p:(A)stack_prog` THEN CAKE_REWRITE_TAC[] THEN
  FS[] THEN REPEAT (PAIRARG_TAC ORELSE S2LP1AUX_TOP_CASE_TAC) THEN GVS[] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[stack_evaluate_def] THEN CAKE_REWRITE_TAC[] THEN
  REPEAT (PAIRARG_TAC ORELSE S2LP1AUX_TOP_CASE_TAC) THEN GVS[IS_SOME_DEF] THEN
  TRY(FIRST_X_ASSUM(MP_TAC o MATCH_MP NOT_bad_fun_return_IMP_SOME) THEN
      DISCH_THEN CAKE_STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[IS_SOME_DEF]) THEN
  ASM_MESON_TAC[FST; IS_SOME_DEF; cases "option"]);;

(* HOL4 line 926: val s = s:('a,'c,'ffi) labSem$state (an annotation) *)

(* HOL4 line 928 (the free variables are quantified; read_reg r s is        *)
(* lab_state_regs s r) *)
let compile_jump_correct = prove
 (`!pc code dest regs pc' (s:(A,C,FFI)lab_state).
     asm_fetch_aux pc code = SOME (compile_jump dest) /\
     loc_to_pc (dest_to_loc' regs dest) 0 code = SOME pc' /\
     (!r. dest = INR r ==> ?p. lab_state_regs s r = wl_Loc p 0) /\
     lab_state_pc s = pc /\ lab_state_code s = code /\ lab_state_regs s = regs /\
     ~(lab_state_clock s = 0)
     ==> lab_evaluate s = lab_evaluate (lab_upd_pc pc' (lab_dec_clock s))`,
  REPEAT GEN_TAC THEN CASES_ON `dest:num+num` THEN
  REWRITE_TAC[compile_jump_def; dest_to_loc'_def] THEN CAKE_REWRITE_TAC[] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [lab_evaluate_def] THEN
  ASM_REWRITE_TAC[asm_fetch_def] THEN CAKE_REWRITE_TAC[get_pc_value_def] THEN
  TRY(ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN NO_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:num`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` (fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th])) THEN
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

(* HOL4 line 941 *)
let result_view_INDUCT,result_view_RECURSION = cake_type
  "result_view = Vloc num num | Vcont num num | Vtimeout | Verr";;

(* HOL4 line 945 [simp] (stackSem's results) *)
let result_view_def = cake_def
  `(result_view (stack_Result (wl_Loc n1 n2:(A)word_loc)) (_:num) (_:num list) (_:num list) =
      Vloc n1 n2) /\
   (result_view (stack_Exception (wl_Loc n1 n2)) _ _ _ = Vloc n1 n2) /\
   (result_view stack_TimeOut _ _ _ = Vtimeout) /\
   (result_view (stackSem_Continue n) l cs _ = Vcont l (find_lab n cs)) /\
   (result_view (stackSem_Break n) l _ bs = Vloc l (find_lab n bs)) /\
   (result_view _ _ _ _ = Verr)`;;

let _ = cake_add_simps [result_view_def];;

(* HOL4 line 954 [simp] (the results are targetSem's; the literal pattern   *)
(* Word 0w is not a kit pattern: halt_word_view_DEF tests w = word 0, and    *)
(* halt_word_view_def is HOL4's clause form) *)
let halt_word_view_DEF = cake_def
  `(halt_word_view (wl_Word (w:A word)) =
      if w = word 0 then target_Halt Success else target_Halt Resource_limit_hit) /\
   (halt_word_view (wl_Loc l1 l2:(A)word_loc) = target_Error)`;;

let halt_word_view_def = prove
 (`(halt_word_view (wl_Word (word 0:A word)) = target_Halt Success) /\
   (!w. ~(w = word 0) ==> halt_word_view (wl_Word (w:A word)) = target_Halt Resource_limit_hit) /\
   (!l1 l2. halt_word_view (wl_Loc l1 l2:(A)word_loc) = target_Error)`,
  SIMP_TAC[halt_word_view_DEF]);;

let _ = cake_add_simps [halt_word_view_def];;

(* HOL4 line 960 [simp] *)
let halt_view_def = cake_def
  `(halt_view (SOME (stackSem_Halt (w:(A)word_loc))) = SOME (halt_word_view w)) /\
   (halt_view (SOME (stack_FinalFFI outcome:(A)stack_result)) =
      SOME (target_Halt (FFI_outcome outcome))) /\
   (halt_view (_:((A)stack_result)option) = NONE)`;;

let _ = cake_add_simps [halt_view_def];;

(* HOL4 line 966: val finish_tac (an ML tactic) *)
(* HOL4 line 1020: val sextract_labels_def = stackPropsTheory.               *)
(* extract_labels_def (an abbreviation) *)

(* ------------------------------------------------------------------------- *)
(* Local copies of three theorems of HOL4 stack_allocProof (lines 6111-6165: *)
(* next_lab_EQ_MAX, next_lab_thm, extract_labels_next_lab), which the proofs *)
(* below use; stack_allocProof is not ported yet.                            *)
(* ------------------------------------------------------------------------- *)

let S2LP1AUX_next_lab_EQ_MAX = prove
 (`!q aux. next_lab (q:(A)stack_prog) aux = MAX aux (next_lab q 0)`,
  SUBGOAL_THEN `!q (n:num) aux. next_lab (q:(A)stack_prog) aux = MAX aux (next_lab q 0)`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC next_lab_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[next_lab_def] THEN
  CASES_ON `p:(A)stack_prog` THEN CAKE_REWRITE_TAC[] THEN
  REPEAT S2LP1AUX_TOP_CASE_TAC THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `T`))) THEN
  ONCE_ASM_REWRITE_TAC[] THEN ONCE_ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `MAX 0 x = x /\ MAX x 0 = x`] THEN ARITH_TAC);;

let S2LP1AUX_next_lab_thm = prove
 (CASE_TERM
  `!p. next_lab (p:(A)stack_prog) 2 =
       match p with
         stack_Seq p1 p2 -> MAX (next_lab p1 2) (next_lab p2 2)
       | stack_If _ _ _ p1 p2 -> MAX (next_lab p1 2) (next_lab p2 2)
       | stack_Loop p -> next_lab p 2
       | stack_Call NONE _ NONE -> 2
       | stack_Call NONE _ (SOME (_,_,l2)) -> MAX (l2 + 2) 2
       | stack_Call (SOME (p,_,_,l2)) _ NONE -> MAX (next_lab p 2) (l2 + 2)
       | stack_Call (SOME (p,_,_,l2)) _ (SOME (p',_,l3)) ->
           MAX (MAX (next_lab p 2) (next_lab p' 2)) (MAX l2 l3 + 2)
       | _ -> 2`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [next_lab_def] THEN
  CASES_ON `p:(A)stack_prog` THEN CAKE_REWRITE_TAC[] THEN
  REPEAT S2LP1AUX_TOP_CASE_TAC THEN
  ONCE_REWRITE_TAC[S2LP1AUX_next_lab_EQ_MAX] THEN
  ONCE_REWRITE_TAC[S2LP1AUX_next_lab_EQ_MAX] THEN
  REWRITE_TAC[ARITH_RULE `MAX 0 x = x /\ MAX x 0 = x`] THEN ARITH_TAC);;

let S2LP1AUX_extract_labels_next_lab = prove
 (`!(p:(A)stack_prog) e. MEM e (stack_extract_labels p) ==> SND e < next_lab p 2`,
  SUBGOAL_THEN
   `!(p:(A)stack_prog) (aux:num) e. MEM e (stack_extract_labels p) ==> SND e < next_lab p 2`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC next_lab_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[S2LP1AUX_next_lab_thm] THEN
  CASES_ON `p:(A)stack_prog` THEN
  REWRITE_TAC[stack_extract_labels_def] THEN CAKE_REWRITE_TAC[MEM] THEN
  REPEAT S2LP1AUX_TOP_CASE_TAC THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  REWRITE_TAC[MEM_APPEND; MEM; LET_DEF; LET_END_DEF] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `T`))) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[SND] THEN
  RES_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 1022 (rebound at HOL4 line 3211, part 2) *)
let next_lab_non_zero = prove
 (`!(p:(A)stack_prog). 2 <= next_lab p 2`,
  ONCE_REWRITE_TAC[S2LP1AUX_next_lab_EQ_MAX] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Local helpers of stack_to_lab_lab_pres: the labels of the code of each    *)
(* kind of program, as list facts (P is the property of the labels; a       *)
(* sub-result Lx has the labels of its program Ex or new ones in a range).  *)
(* ------------------------------------------------------------------------- *)

let S2LP1AUX_MEM_CASES_TAC : tactic = fun (asl,w as g) ->
  let mems = setify (find_terms (fun t -> is_comb t && is_comb (rator t) &&
                        is_const (rator (rator t)) &&
                        fst (dest_const (rator (rator t))) = "MEM") w) in
  (MAP_EVERY (fun t -> ASM_CASES_TAC t THEN POP_ASSUM (fun th -> REWRITE_TAC[th])) mems) g;;

(* specialize every universal assumption at every element of a MEM fact *)
let S2LP1AUX_SPEC_MEMS_TAC : tactic = fun (asl,w as g) ->
  let is_mem t = is_comb t && is_comb (rator t) && is_const (rator (rator t)) &&
                 fst (dest_const (rator (rator t))) = "MEM" in
  let facts = filter (fun th -> not (is_forall (concl th))) (map snd asl) in
  let elts = setify (map (fun t -> rand (rator t))
                       (itlist (fun th l -> find_terms is_mem (concl th) @ l) facts
                               (find_terms is_mem w))) in
  let elts = filter (fun t -> type_of t = `:num#num` && frees t = frees t) elts in
  let univs = filter (fun th -> is_forall (concl th)) (map snd asl) in
  let insts = flat (map (fun th -> mapfilter (fun t -> ISPEC t th) elts) univs) in
  (MAP_EVERY (fun th -> ASSUME_TAC (BETA_RULE th)) insts) g;;

let S2LP1AUX_LP_TAC : tactic =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ALL_APPEND; ALL_DISTINCT_APPEND; ALL_DISTINCT; ALL; MEM_APPEND; MEM; APPEND] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
  REPEAT STRIP_TAC THEN S2LP1AUX_SPEC_MEMS_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; FST; SND]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> not (is_forall (concl th))))) THEN
  REWRITE_TAC[PAIR_EQ; FST; SND] THEN S2LP1AUX_MEM_CASES_TAC THEN ARITH_TAC;;

let S2LP1AUX_lp_seq = prove
 (`!(P:num#num->bool) Lx Ly E0 E1 m m1 m2.
     ALL P Lx /\ ALL_DISTINCT Lx /\
     (!lab. MEM lab Lx ==> MEM lab E0 \/ m <= SND lab /\ SND lab < m1) /\ m <= m1 /\
     ALL P Ly /\ ALL_DISTINCT Ly /\
     (!lab. MEM lab Ly ==> MEM lab E1 \/ m1 <= SND lab /\ SND lab < m2) /\ m1 <= m2 /\
     (!e. MEM e E0 ==> SND e < m) /\ (!e. MEM e E1 ==> SND e < m) /\
     ALL_DISTINCT (APPEND E0 E1)
     ==> ALL P (APPEND Lx Ly) /\ ALL_DISTINCT (APPEND Lx Ly) /\
         (!lab. MEM lab (APPEND Lx Ly)
                ==> MEM lab (APPEND E0 E1) \/ m <= SND lab /\ SND lab < m2) /\
         m <= m2`,
  S2LP1AUX_LP_TAC);;

let S2LP1AUX_lp_if1 = prove
 (`!(P:num#num->bool) L E n m m1.
     ALL P L /\ ALL_DISTINCT L /\
     (!lab. MEM lab L ==> MEM lab E \/ m <= SND lab /\ SND lab < m1) /\ m <= m1 /\
     (!e. MEM e E ==> SND e < m) /\ P (n,m1)
     ==> ALL P (APPEND L [n,m1]) /\ ALL_DISTINCT (APPEND L [n,m1]) /\
         (!lab. MEM lab (APPEND L [n,m1])
                ==> MEM lab E \/ m <= SND lab /\ SND lab < m1 + 1) /\
         m <= m1 + 1`,
  S2LP1AUX_LP_TAC);;

let S2LP1AUX_lp_if2 = prove
 (`!(P:num#num->bool) Lx Ly E0 E1 n m m1 m2.
     ALL P Lx /\ ALL_DISTINCT Lx /\
     (!lab. MEM lab Lx ==> MEM lab E0 \/ m <= SND lab /\ SND lab < m1) /\ m <= m1 /\
     ALL P Ly /\ ALL_DISTINCT Ly /\
     (!lab. MEM lab Ly ==> MEM lab E1 \/ m1 <= SND lab /\ SND lab < m2) /\ m1 <= m2 /\
     (!e. MEM e E0 ==> SND e < m) /\ (!e. MEM e E1 ==> SND e < m) /\
     ALL_DISTINCT (APPEND E0 E1) /\ P (n,m2)
     ==> ALL P (APPEND (APPEND Lx [n,m2]) Ly) /\
         ALL_DISTINCT (APPEND (APPEND Lx [n,m2]) Ly) /\
         (!lab. MEM lab (APPEND (APPEND Lx [n,m2]) Ly)
                ==> MEM lab (APPEND E0 E1) \/ m <= SND lab /\ SND lab < m2 + 1) /\
         m <= m2 + 1`,
  S2LP1AUX_LP_TAC);;

let S2LP1AUX_lp_if3 = prove
 (`!(P:num#num->bool) Lx Ly E0 E1 n m m1 m2.
     ALL P Lx /\ ALL_DISTINCT Lx /\
     (!lab. MEM lab Lx ==> MEM lab E0 \/ m <= SND lab /\ SND lab < m1) /\ m <= m1 /\
     ALL P Ly /\ ALL_DISTINCT Ly /\
     (!lab. MEM lab Ly ==> MEM lab E1 \/ m1 <= SND lab /\ SND lab < m2) /\ m1 <= m2 /\
     (!e. MEM e E0 ==> SND e < m) /\ (!e. MEM e E1 ==> SND e < m) /\
     ALL_DISTINCT (APPEND E0 E1) /\ P (n,m2)
     ==> ALL P (APPEND (APPEND Ly [n,m2]) Lx) /\
         ALL_DISTINCT (APPEND (APPEND Ly [n,m2]) Lx) /\
         (!lab. MEM lab (APPEND (APPEND Ly [n,m2]) Lx)
                ==> MEM lab (APPEND E0 E1) \/ m <= SND lab /\ SND lab < m2 + 1) /\
         m <= m2 + 1`,
  S2LP1AUX_LP_TAC);;

let S2LP1AUX_lp_if4 = prove
 (`!(P:num#num->bool) Lx Ly E0 E1 n m m1 m2.
     ALL P Lx /\ ALL_DISTINCT Lx /\
     (!lab. MEM lab Lx ==> MEM lab E0 \/ m <= SND lab /\ SND lab < m1) /\ m <= m1 /\
     ALL P Ly /\ ALL_DISTINCT Ly /\
     (!lab. MEM lab Ly ==> MEM lab E1 \/ m1 <= SND lab /\ SND lab < m2) /\ m1 <= m2 /\
     (!e. MEM e E0 ==> SND e < m) /\ (!e. MEM e E1 ==> SND e < m) /\
     ALL_DISTINCT (APPEND E0 E1) /\ P (n,m2) /\ P (n,m2 + 1)
     ==> ALL P (APPEND (APPEND (APPEND Ly [n,m2]) Lx) [n,m2 + 1]) /\
         ALL_DISTINCT (APPEND (APPEND (APPEND Ly [n,m2]) Lx) [n,m2 + 1]) /\
         (!lab. MEM lab (APPEND (APPEND (APPEND Ly [n,m2]) Lx) [n,m2 + 1])
                ==> MEM lab (APPEND E0 E1) \/ m <= SND lab /\ SND lab < m2 + 2) /\
         m <= m2 + 2`,
  S2LP1AUX_LP_TAC);;

let S2LP1AUX_lp_loop = prove
 (`!(P:num#num->bool) L E n m m1.
     ALL P L /\ ALL_DISTINCT L /\
     (!lab. MEM lab L ==> MEM lab E \/ m + 2 <= SND lab /\ SND lab < m1) /\ m + 2 <= m1 /\
     (!e. MEM e E ==> SND e < m) /\ P (n,m) /\ P (n,m + 1)
     ==> ALL P (CONS (n,m) (APPEND L [n,m + 1])) /\
         ALL_DISTINCT (CONS (n,m) (APPEND L [n,m + 1])) /\
         (!lab. MEM lab (CONS (n,m) (APPEND L [n,m + 1]))
                ==> MEM lab E \/ m <= SND lab /\ SND lab < m1) /\
         m <= m1`,
  S2LP1AUX_LP_TAC);;

let S2LP1AUX_lp_call1 = prove
 (`!(P:num#num->bool) L E l1 l2 m m1.
     ALL P L /\ ALL_DISTINCT L /\
     (!lab. MEM lab L ==> MEM lab E \/ m <= SND lab /\ SND lab < m1) /\ m <= m1 /\
     (!e. MEM e E ==> SND e < m) /\ ALL_DISTINCT (CONS (l1,l2) E) /\ P (l1,l2) /\ l2 < m
     ==> ALL P (CONS (l1,l2) L) /\ ALL_DISTINCT (CONS (l1,l2) L) /\
         (!lab. MEM lab (CONS (l1,l2) L)
                ==> MEM lab (CONS (l1,l2) E) \/ m <= SND lab /\ SND lab < m1) /\
         m <= m1`,
  S2LP1AUX_LP_TAC);;

let S2LP1AUX_lp_call2 = prove
 (`!(P:num#num->bool) Lx Ly E0 E1 l1 l2 k1 k2 n m m1 m2.
     ALL P Lx /\ ALL_DISTINCT Lx /\
     (!lab. MEM lab Lx ==> MEM lab E0 \/ m <= SND lab /\ SND lab < m1) /\ m <= m1 /\
     ALL P Ly /\ ALL_DISTINCT Ly /\
     (!lab. MEM lab Ly ==> MEM lab E1 \/ m1 <= SND lab /\ SND lab < m2) /\ m1 <= m2 /\
     (!e. MEM e E0 ==> SND e < m) /\ (!e. MEM e E1 ==> SND e < m) /\
     ALL_DISTINCT (CONS (l1,l2) (CONS (k1,k2) (APPEND E0 E1))) /\
     P (l1,l2) /\ P (k1,k2) /\ P (n,m2) /\ l2 < m /\ k2 < m
     ==> ALL P (CONS (l1,l2) (APPEND Lx (CONS (k1,k2) (APPEND Ly [n,m2])))) /\
         ALL_DISTINCT (CONS (l1,l2) (APPEND Lx (CONS (k1,k2) (APPEND Ly [n,m2])))) /\
         (!lab. MEM lab (CONS (l1,l2) (APPEND Lx (CONS (k1,k2) (APPEND Ly [n,m2]))))
                ==> MEM lab (CONS (l1,l2) (CONS (k1,k2) (APPEND E0 E1))) \/
                    m <= SND lab /\ SND lab < m2 + 1) /\
         m <= m2 + 1`,
  S2LP1AUX_LP_TAC);;

let S2LP1AUX_extract_labels_lt = prove
 (`!(p:(A)stack_prog) m. next_lab p 2 <= m ==> !e. MEM e (stack_extract_labels p) ==> SND e < m`,
  MESON_TAC[S2LP1AUX_extract_labels_next_lab; LTE_TRANS]);;

let S2LP1AUX_extract_labels_compile_jump = prove
 (`!d (l:((A)line)list). lab_extract_labels (CONS (compile_jump d) l) = lab_extract_labels l`,
  GEN_TAC THEN CASES_ON `d:num+num` THEN
  REWRITE_TAC[compile_jump_def; lab_extract_labels_def]);;

let S2LP1AUX_flatten_Skip = prove
 (`!t n m cs bs. stack_to_lab_flatten t (stack_Skip:(A)stack_prog) n m cs bs =
                 (misc_List [],F,m)`,
  ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN CAKE_REWRITE_TAC[]);;

(* the antecedents of the induction hypotheses (implications with an        *)
(* arithmetic or assumption antecedent) discharged in any order            *)
let S2LP1AUX_ANTS_ARITH_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_imp (concl th) then
      MP_TAC th THEN ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC]
    else NO_TAC));;

(* the end of each case: the labels of the code, the bounds of the labels  *)
(* of the subprograms, then one of the list lemmas above                    *)
let S2LP1AUX_LP_FIN_TAC (lemmas:thm list) : tactic =
  REWRITE_TAC[append_thm; extract_labels_append; lab_extract_labels_def; APPEND;
              APPEND_NIL; stack_extract_labels_def; S2LP1AUX_extract_labels_compile_jump] THEN
  CAKE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN REWRITE_TAC[APPEND] THEN
  TRY(REWRITE_TAC[ALL; ALL_DISTINCT; MEM; LE_REFL] THEN NO_TAC) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
           MATCH_MP (ARITH_RULE `MAX a b <= m ==> a <= m /\ b <= m`))) THEN
  IMP_RES_TAC (MESON[next_lab_non_zero; LE_TRANS]
                 `!(p:(A)stack_prog) m. next_lab p 2 <= m ==> 2 <= m`) THEN
  IMP_RES_TAC S2LP1AUX_extract_labels_lt THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; MEM; MEM_APPEND]) THEN
  FIRST (map (fun th -> MATCH_MP_TAC th THEN S2LP1AUX_EXISTS_ASM_TAC THEN
                        S2LP1AUX_CONJS_TAC) lemmas);;

(* a case with subprograms: split the code, use the induction hypotheses   *)
let S2LP1AUX_LP_CASE_TAC (lemmas:thm list) : tactic =
  ONCE_REWRITE_TAC[S2LP1AUX_next_lab_thm] THEN CAKE_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  REPEAT (S2LP1AUX_PAIRARG_TAC ORELSE S2LP1AUX_FULL_CASE_TAC) THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[PAIR_EQ; stack_extract_labels_def; ALL_APPEND;
                                ALL_DISTINCT_APPEND; S2LP1AUX_flatten_Skip]) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `T`))) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN RES_TAC THEN S2LP1AUX_ANTS_ARITH_TAC THEN
  S2LP1AUX_LP_FIN_TAC lemmas;;

(* stack_to_lab_lab_pres with the result of flatten named (local helper)   *)
let S2LP1AUX_lab_pres_eq = prove
 (`!t (p:(A)stack_prog) n nl cs bs cp nr nl'.
     stack_to_lab_flatten t p n nl cs bs = (cp,nr,nl') /\
     ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
     ALL_DISTINCT (stack_extract_labels p) /\ ~t /\ next_lab p 2 <= nl
     ==> ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (lab_extract_labels (append cp)) /\
         ALL_DISTINCT (lab_extract_labels (append cp)) /\
         (!lab. MEM lab (lab_extract_labels (append cp))
                ==> MEM lab (stack_extract_labels p) \/ (nl <= SND lab /\ SND lab < nl')) /\
         nl <= nl'`,
  MATCH_MP_TAC stack_to_lab_flatten_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [stack_to_lab_flatten_def] THEN
  CASES_ON `p:(A)stack_prog` THEN CAKE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  TRY(REWRITE_TAC[PAIR_EQ] THEN ONCE_REWRITE_TAC[S2LP1AUX_next_lab_thm] THEN
      CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
      REWRITE_TAC[append_thm; lab_extract_labels_def; ALL; ALL_DISTINCT; MEM; LE_REFL; APPEND;
                  stack_extract_labels_def; PAIR_EQ] THEN
      CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
      REPEAT CONJ_TAC THEN
      TRY(GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SND]) THEN ASM_ARITH_TAC) THENL
   [S2LP1AUX_LP_CASE_TAC [S2LP1AUX_lp_call2; S2LP1AUX_lp_call1];
    S2LP1AUX_LP_CASE_TAC [S2LP1AUX_lp_seq];
    S2LP1AUX_LP_CASE_TAC [S2LP1AUX_lp_if4; S2LP1AUX_lp_if3; S2LP1AUX_lp_if2;
                          S2LP1AUX_lp_if1];
    S2LP1AUX_LP_CASE_TAC [S2LP1AUX_lp_loop]]);;

(* HOL4 line 1028 (extract_labels of p is stackProps', of the lines         *)
(* labProps') *)
let stack_to_lab_lab_pres = prove
 (CASE_TERM
  `!t (p:(A)stack_prog) n nl cs bs.
     ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
     ALL_DISTINCT (stack_extract_labels p) /\ ~t /\
     next_lab p 2 <= nl
     ==> let (cp,nr,nl') = stack_to_lab_flatten t p n nl cs bs in
           ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (lab_extract_labels (append cp)) /\
           ALL_DISTINCT (lab_extract_labels (append cp)) /\
           (!lab. MEM lab (lab_extract_labels (append cp))
                  ==> MEM lab (stack_extract_labels p) \/ (nl <= SND lab /\ SND lab < nl')) /\
           nl <= nl'`,
  REPEAT STRIP_TAC THEN REPEAT S2LP1AUX_PAIRARG_TAC THEN
  MATCH_MP_TAC S2LP1AUX_lab_pres_eq THEN S2LP1AUX_EXISTS_ASM_TAC THEN ASM_REWRITE_TAC[]);;

(* the labels of flatten T of a Seq: those of flatten F and (n,1) (local   *)
(* helper of stack_to_lab_lab_pres_T)                                        *)
let S2LP1AUX_lp_seq_T = prove
 (`!(n:num) Lx Ly E nl nl'.
     ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (APPEND Lx Ly) /\
     ALL_DISTINCT (APPEND Lx Ly) /\
     (!lab. MEM lab (APPEND Lx Ly) ==> MEM lab E \/ nl <= SND lab /\ SND lab < nl') /\
     nl <= nl' /\ 2 <= nl
     ==> ALL (\(l1,l2). l1 = n /\ ~(l2 = 0)) (APPEND (APPEND Lx [n,1]) Ly) /\
         ALL_DISTINCT (APPEND (APPEND Lx [n,1]) Ly) /\
         (!lab. MEM lab (APPEND (APPEND Lx [n,1]) Ly) ==> MEM lab E \/ SND lab < nl') /\
         nl <= nl'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ALL_APPEND; ALL_DISTINCT_APPEND; ALL_DISTINCT; ALL; MEM_APPEND; MEM;
              GSYM ALL_MEM; FORALL_PAIR_THM; PAIR_EQ] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPECL [`p1:num`; `p2:num`] o check (is_forall o concl))) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN S2LP1AUX_MEM_CASES_TAC THEN ARITH_TAC);;

(* weakening the label facts of flatten F (local helper)                   *)
let S2LP1AUX_lp_weaken = prove
 (`!(n:num) L E nl nl'.
     ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) L /\ ALL_DISTINCT L /\
     (!lab. MEM lab L ==> MEM lab E \/ nl <= SND lab /\ SND lab < nl') /\ nl <= nl'
     ==> ALL (\(l1,l2). l1 = n /\ ~(l2 = 0)) L /\ ALL_DISTINCT L /\
         (!lab. MEM lab L ==> MEM lab E \/ SND lab < nl') /\ nl <= nl'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN MESON_TAC[]);;

(* HOL4 line 1091 *)
let stack_to_lab_lab_pres_T = prove
 (CASE_TERM
  `!t (p:(A)stack_prog) n nl cs bs.
     ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (stack_extract_labels p) /\
     ALL_DISTINCT (stack_extract_labels p) /\ t /\
     next_lab p 2 <= nl
     ==> let (cp,nr,nl') = stack_to_lab_flatten t p n nl cs bs in
           ALL (\(l1,l2). l1 = n /\ ~(l2 = 0)) (lab_extract_labels (append cp)) /\
           ALL_DISTINCT (lab_extract_labels (append cp)) /\
           (!lab. MEM lab (lab_extract_labels (append cp))
                  ==> MEM lab (stack_extract_labels p) \/ SND lab < nl') /\
           nl <= nl'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `t:bool` then SUBST_ALL_TAC (EQT_INTRO th) else NO_TAC) THEN
  ASM_CASES_TAC `stack_to_lab_flatten T (p:(A)stack_prog) n nl cs bs =
                  stack_to_lab_flatten F p n nl cs bs` THENL
   [ASM_REWRITE_TAC[] THEN REPEAT S2LP1AUX_PAIRARG_TAC THEN
    MATCH_MP_TAC S2LP1AUX_lp_weaken THEN
    MP_TAC (ISPECL [`F`; `p:(A)stack_prog`; `n:num`; `nl:num`; `cs:num list`;
                    `bs:num list`; `cp:((A)line)app_list`; `nr:bool`; `nl':num`]
                   S2LP1AUX_lab_pres_eq) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN CASES_ON `p:(A)stack_prog` THEN
  DISCH_THEN(fun th -> MP_TAC(CAKE_REWRITE_RULE[LET_DEF; LET_END_DEF]
                                (ONCE_REWRITE_RULE[stack_to_lab_flatten_def] th))) THEN
  REWRITE_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN (CASE_TERM
   `stack_to_lab_flatten T (stack_Seq a0 a1:(A)stack_prog) n nl cs bs =
      (let (xs,nr1,m) = stack_to_lab_flatten F a0 n nl cs bs in
       let (ys,nr2,m) = stack_to_lab_flatten F a1 n m cs bs in
       (misc_Append (misc_Append xs (misc_List [lab_Label n 1 0])) ys,(nr1 \/ nr2),m)) /\
    stack_to_lab_flatten F (stack_Seq a0 a1:(A)stack_prog) n nl cs bs =
      (let (xs,nr1,m) = stack_to_lab_flatten F a0 n nl cs bs in
       let (ys,nr2,m) = stack_to_lab_flatten F a1 n m cs bs in
       (misc_Append xs ys,(nr1 \/ nr2),m))`) STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [stack_to_lab_flatten_def] THEN CAKE_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_eq (concl th) && is_comb (lhs (concl th)) &&
     can (find_term (fun t -> t = `T`)) (lhs (concl th)) then REWRITE_TAC[th] else NO_TAC) THEN
  REPEAT S2LP1AUX_PAIRARG_TAC THEN
  MP_TAC (ISPECL [`F`; `stack_Seq a0 a1:(A)stack_prog`; `n:num`; `nl:num`; `cs:num list`;
                  `bs:num list`; `misc_Append xs ys:((A)line)app_list`; `nr1 \/ nr2`;
                  `m':num`] S2LP1AUX_lab_pres_eq) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[append_thm; extract_labels_append; lab_extract_labels_def; APPEND] THEN
  STRIP_TAC THEN MATCH_MP_TAC S2LP1AUX_lp_seq_T THEN ASM_REWRITE_TAC[] THEN
  MP_TAC (ISPEC `stack_Seq a0 a1:(A)stack_prog` next_lab_non_zero) THEN ASM_ARITH_TAC);;

(* HOL4 line 1139 *)
let flatten_T_F = prove
 (`!(p_2:(A)stack_prog) p_1 m cs bs.
     ~is_Seq p_2 ==> stack_to_lab_flatten T p_2 p_1 m cs bs = stack_to_lab_flatten F p_2 p_1 m cs bs`,
  GEN_TAC THEN CASES_ON `p_2:(A)stack_prog` THEN REWRITE_TAC[is_Seq_def] THEN
  ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN CAKE_REWRITE_TAC[]);;

(* HOL4 line 1147 *)
let prog_to_section_labels_ok = prove
 (`!(prog:(num#(A)stack_prog)list).
     ALL (\(n,p). let labs = stack_extract_labels p in
                    ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) labs /\ ALL_DISTINCT labs)
       prog /\
     ALL_DISTINCT (MAP FST prog)
     ==> labels_ok (MAP prog_to_section prog)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[labels_ok_def; MAP_prog_to_section_FST] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ALL (\(n,p). let labs = stack_extract_labels p in
                   ALL (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) labs /\ ALL_DISTINCT labs)
                (prog:(num#(A)stack_prog)list)` THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN DISCH_TAC THEN
  X_GEN_TAC `s:(A)sec` THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num#(A)stack_prog` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:num#(A)stack_prog`) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`y:num#(A)stack_prog`,`y:num#(A)stack_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [`n:num`; `p:(A)stack_prog`] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
  REWRITE_TAC[prog_to_section_def] THEN REPEAT S2LP1AUX_PAIRARG_TAC THEN
  MP_TAC (ISPECL [`T`; `p:(A)stack_prog`; `n:num`; `next_lab (p:(A)stack_prog) 2`;
                  `[]:num list`; `[]:num list`] stack_to_lab_lab_pres_T) THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; LE_REFL] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN CAKE_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC (ISPEC `p:(A)stack_prog` next_lab_non_zero) THEN DISCH_TAC THEN
  REWRITE_TAC[append_thm; extract_labels_append; lab_extract_labels_def; ALL_DISTINCT_APPEND;
              ALL_DISTINCT; MEM_APPEND; MEM; PAIR_EQ] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!e. MEM e (stack_extract_labels (p:(A)stack_prog)) ==> SND e < m`
    ASSUME_TAC THENL
   [MATCH_MP_TAC S2LP1AUX_extract_labels_lt THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN REPEAT GEN_TAC THEN
    DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    RES_TAC THEN RES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[SND]) THEN ASM_ARITH_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    SUBGOAL_THEN `stack_to_lab_flatten F (p:(A)stack_prog) n (next_lab p 2) [] [] = (lines,nr,m)`
      ASSUME_TAC THENL [ASM_MESON_TAC[flatten_T_F]; ALL_TAC] THEN
    MP_TAC (ISPECL [`F`; `p:(A)stack_prog`; `n:num`; `next_lab (p:(A)stack_prog) 2`;
                    `[]:num list`; `[]:num list`; `lines:((A)line)app_list`; `nr:bool`;
                    `m:num`] S2LP1AUX_lab_pres_eq) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN REPEAT GEN_TAC THEN
    DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    RES_TAC THEN RES_TAC THEN ASM_ARITH_TAC]);;

(* HOL4 line 1183 *)
let NOT_MEM_find_lab_IMP = prove
 (`!bs n. ~MEM (find_lab n bs) bs ==> find_lab n bs = 0`,
  REWRITE_TAC[find_lab_def; oEL_THM] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN CAKE_REWRITE_TAC[] THEN ASM_MESON_TAC[MEM_EL]);;

(* HOL4 line 1192 *)
let is_some_loc_to_pc_prefix = prove
 (`!n k (c1:((A)sec)list) c2.
     IS_SOME (loc_to_pc n k c1) /\ c1 <<= c2 ==> IS_SOME (loc_to_pc n k c2)`,
  REPEAT GEN_TAC THEN
  CASES_ON `loc_to_pc n k (c1:((A)sec)list)` THEN REWRITE_TAC[IS_SOME_DEF] THEN
  STRIP_TAC THEN IMP_RES_TAC loc_to_pc_isPREFIX THEN ASM_REWRITE_TAC[IS_SOME_DEF]);;

(* HOL4 line 1200 *)
let every_is_some_loc_to_pc_prefix = prove
 (`!n cs (c1:((A)sec)list) c2.
     ALL (\k. IS_SOME (loc_to_pc n k c1)) cs /\ c1 <<= c2
     ==> ALL (\k. IS_SOME (loc_to_pc n k c2)) cs`,
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[is_some_loc_to_pc_prefix]);;

(* ------------------------------------------------------------------------- *)
(* flatten_correct is proved by induction on stack_evaluate; the property   *)
(* proved for each (prog,s1) is S2LP1AUX_fc prog s1 (local definition), and *)
(* each case of the induction is a lemma S2LP1AUX_fc_...                     *)
(* ------------------------------------------------------------------------- *)

let S2LP1AUX_fc_def = new_definition (CASE_TERM
 `S2LP1AUX_fc (prog:(A)stack_prog) (s1:(A,C,FFI)stack_state) <=>
  !t r s2 n l cs bs (t1:(A,C,FFI)lab_state).
     stack_evaluate (prog,s1) = (r,s2) /\ ~(r = SOME stack_Error) /\
     stack_to_labProof_state_rel s1 t1 /\
     call_args prog (lab_state_ptr_reg t1) (lab_state_len_reg t1) (lab_state_ptr2_reg t1)
       (lab_state_len2_reg t1) (lab_state_link_reg t1) /\
     stack_to_labProof_code_installed (lab_state_pc t1)
       (append (FST (stack_to_lab_flatten t prog n l cs bs))) (lab_state_code t1) /\
     ALL (\k. IS_SOME (loc_to_pc n k (lab_state_code t1))) (APPEND (APPEND cs bs) [0])
     ==> ?ck t2.
           (match halt_view r with
              SOME res ->
                lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock t1 + ck)) t1) = (res,t2) /\
                lab_state_ffi t2 = stack_state_ffi s2
            | NONE ->
                (!ck1. lab_evaluate (lab_state_clock_fupd (combin_K ((lab_state_clock t1 + ck) + ck1)) t1) =
                       lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock t2 + ck1)) t2)) /\
                lab_state_len_reg t2 = lab_state_len_reg t1 /\
                lab_state_ptr_reg t2 = lab_state_ptr_reg t1 /\
                lab_state_len2_reg t2 = lab_state_len2_reg t1 /\
                lab_state_ptr2_reg t2 = lab_state_ptr2_reg t1 /\
                lab_state_link_reg t2 = lab_state_link_reg t1 /\
                lab_state_code t1 <<= lab_state_code t2 /\
                (match OPTION_MAP (\w. result_view w n cs bs) r with
                   NONE ->
                     lab_state_pc t2 =
                       lab_state_pc t1 +
                       LENGTH (FILTER ((~) o is_Label)
                                 (append (FST (stack_to_lab_flatten t prog n l cs bs)))) /\
                     stack_to_labProof_state_rel s2 t2
                 | SOME (Vloc n1 n2) ->
                     (!n. IS_SOME (lookup n (stack_state_code s2))
                          ==> IS_SOME (loc_to_pc n 0 (lab_state_code t2))) /\
                     (!w. loc_to_pc n1 n2 (lab_state_code t2) = SOME w
                          ==> w = lab_state_pc t2 /\ stack_to_labProof_state_rel s2 t2)
                 | SOME (Vcont n1 n2) ->
                     stack_to_labProof_state_rel s2 t2 /\
                     stack_to_labProof_code_installed (lab_state_pc t2)
                       [LabAsm (lab_Jump (lab_Lab n1 n2)) (word 0) [] 0] (lab_state_code t2)
                 | SOME Vtimeout -> lab_state_ffi t2 = stack_state_ffi s2 /\ lab_state_clock t2 = 0
                 | _ -> F))`);;

(* the cases where state_rel makes the program fail (use_alloc, use_store, *)
(* use_stack are false)                                                    *)
let S2LP1AUX_FC_ERROR_TAC : tactic =
  REWRITE_TAC[S2LP1AUX_fc_def] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[stack_to_labProof_state_rel_def] o
              check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                   "stack_to_labProof_state_rel" with Failure _ -> false)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~stack_state_use_alloc (s:(A,C,FFI)stack_state)`;
    ASSUME `~stack_state_use_store (s:(A,C,FFI)stack_state)`;
    ASSUME `~stack_state_use_stack (s:(A,C,FFI)stack_state)`; PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;;

(* ------------------------------------------------------------------------- *)
(* One step of lab_evaluate on the code installed by flatten, with the      *)
(* clock written as k + 1 (local helpers of flatten_correct)                 *)
(* ------------------------------------------------------------------------- *)

let S2LP1AUX_LAB_STEP_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [lab_evaluate_def] THEN
  REWRITE_TAC[asm_fetch_def] THEN
  SIMP[ADD_EQ_0; ARITH_EQ; get_pc_value_def; lab_to_loc_def] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[lab_state_component_equality; lab_upd_pc_def; lab_dec_clock_def; inc_pc_def;
              lab_upd_reg_def] THEN
  SIMP[ADD_SUB];;

let S2LP1AUX_eval_jump = prove
 (`!(t1:(A,C,FFI)lab_state) n1 n2 w b k p ck.
     asm_fetch_aux (lab_state_pc t1) (lab_state_code t1) =
       SOME (LabAsm (lab_Jump (lab_Lab n1 n2)) w b k) /\
     loc_to_pc n1 n2 (lab_state_code t1) = SOME p
     ==> lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t1) =
         lab_evaluate (lab_state_clock_fupd (combin_K ck) (lab_upd_pc p t1))`,
  S2LP1AUX_LAB_STEP_TAC);;

let S2LP1AUX_eval_jumpreg = prove
 (`!(t1:(A,C,FFI)lab_state) r b k n1 n2 p ck.
     asm_fetch_aux (lab_state_pc t1) (lab_state_code t1) = SOME (Asm (Asmi (JumpReg r)) b k) /\
     lab_state_regs t1 r = wl_Loc n1 n2 /\
     loc_to_pc n1 n2 (lab_state_code t1) = SOME p
     ==> lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t1) =
         lab_evaluate (lab_state_clock_fupd (combin_K ck) (lab_upd_pc p t1))`,
  S2LP1AUX_LAB_STEP_TAC);;

let S2LP1AUX_eval_locvalue = prove
 (`!(t1:(A,C,FFI)lab_state) r n1 n2 w b k p ck.
     asm_fetch_aux (lab_state_pc t1) (lab_state_code t1) =
       SOME (LabAsm (lab_LocValue r (lab_Lab n1 n2)) w b k) /\
     loc_to_pc n1 n2 (lab_state_code t1) = SOME p
     ==> lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t1) =
         lab_evaluate (lab_state_clock_fupd (combin_K ck)
                         (inc_pc (lab_upd_reg r (wl_Loc n1 n2) t1)))`,
  S2LP1AUX_LAB_STEP_TAC);;

let S2LP1AUX_eval_jumpcmp_T = prove
 (`!(t1:(A,C,FFI)lab_state) c r ri n1 n2 w b k p ck.
     asm_fetch_aux (lab_state_pc t1) (lab_state_code t1) =
       SOME (LabAsm (lab_JumpCmp c r ri (lab_Lab n1 n2)) w b k) /\
     wl_word_cmp c (lab_state_regs t1 r) (lab_reg_imm ri t1) = SOME T /\
     loc_to_pc n1 n2 (lab_state_code t1) = SOME p
     ==> lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t1) =
         lab_evaluate (lab_state_clock_fupd (combin_K ck) (lab_upd_pc p t1))`,
  S2LP1AUX_LAB_STEP_TAC);;

let S2LP1AUX_eval_jumpcmp_F = prove
 (`!(t1:(A,C,FFI)lab_state) c r ri l w b k ck.
     asm_fetch_aux (lab_state_pc t1) (lab_state_code t1) =
       SOME (LabAsm (lab_JumpCmp c r ri l) w b k) /\
     wl_word_cmp c (lab_state_regs t1 r) (lab_reg_imm ri t1) = SOME F
     ==> lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t1) =
         lab_evaluate (lab_state_clock_fupd (combin_K ck) (inc_pc t1))`,
  S2LP1AUX_LAB_STEP_TAC);;

let S2LP1AUX_eval_inst = prove
 (`!(t1:(A,C,FFI)lab_state) i b k ck.
     asm_fetch_aux (lab_state_pc t1) (lab_state_code t1) = SOME (Asm (Asmi (asm_Inst i)) b k) /\
     ~lab_state_failed (asm_inst i t1)
     ==> lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t1) =
         lab_evaluate (lab_state_clock_fupd (combin_K ck) (inc_pc (asm_inst i t1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [lab_evaluate_def] THEN
  REWRITE_TAC[asm_fetch_def] THEN SIMP[ADD_EQ_0; ARITH_EQ] THEN
  CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[asm_inst_with_clock] THEN SIMP[] THEN
  CAKE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[lab_state_component_equality; lab_dec_clock_def; inc_pc_def] THEN
  SIMP[ADD_SUB; asm_inst_consts]);;

(* the code of the stack state is installed (local helper) *)
let S2LP1AUX_rel_lookup_loc = prove
 (`!(s:(A,C,FFI)stack_state) t n.
     stack_to_labProof_state_rel s t /\ IS_SOME (lookup n (stack_state_code s))
     ==> IS_SOME (loc_to_pc n 0 (lab_state_code t))`,
  REWRITE_TAC[stack_to_labProof_state_rel_def; IS_SOME_EXISTS] THEN MESON_TAC[]);;

(* some facts of state_rel (local helper) *)
let S2LP1AUX_rel_basic = prove
 (`!(s:(A,C,FFI)stack_state) t.
     stack_to_labProof_state_rel s t
     ==> lab_state_ffi t = stack_state_ffi s /\
         lab_state_clock t = stack_state_clock s /\
         ~lab_state_failed t /\
         lab_state_mem t = stack_state_memory s /\
         lab_state_mem_domain t = stack_state_mdomain s /\
         lab_state_be t = stack_state_be s /\
         lab_state_code_buffer t = stack_state_code_buffer s /\
         ~(lab_state_link_reg t = lab_state_len_reg t) /\
         ~(lab_state_link_reg t = lab_state_ptr_reg t) /\
         ~(lab_state_link_reg t = lab_state_len2_reg t) /\
         ~(lab_state_link_reg t = lab_state_ptr2_reg t)`,
  SIMP_TAC[stack_to_labProof_state_rel_def]);;

let S2LP1AUX_eval_halt = prove
 (`!(t1:(A,C,FFI)lab_state) w b k ck.
     asm_fetch_aux (lab_state_pc t1) (lab_state_code t1) = SOME (LabAsm lab_Halt w b k)
     ==> lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t1) =
         (halt_word_view (lab_state_regs t1 (lab_state_ptr_reg t1)),
          lab_state_clock_fupd (combin_K (ck + 1)) t1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [lab_evaluate_def] THEN
  REWRITE_TAC[asm_fetch_def] THEN SIMP[ADD_EQ_0; ARITH_EQ] THEN
  CASES_ON `lab_state_regs (t1:(A,C,FFI)lab_state) (lab_state_ptr_reg t1)` THEN
  CAKE_REWRITE_TAC[halt_word_view_DEF] THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* HOL4 flatten_correct, case Skip *)
let S2LP1AUX_fc_skip = prove
 (`!(s:(A,C,FFI)stack_state). S2LP1AUX_fc stack_Skip s`,
  REWRITE_TAC[S2LP1AUX_fc_def] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN REWRITE_TAC[PAIR_EQ; S2LP1AUX_flatten_Skip] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`0`; `t1:(A,C,FFI)lab_state`] THEN
  CAKE_REWRITE_TAC[halt_view_def; OPTION_MAP_DEF] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; IS_PREFIX_REFL; append_thm; FILTER; LENGTH]);;

(* case Halt *)
let S2LP1AUX_fc_halt = prove
 (`!v (s:(A,C,FFI)stack_state). S2LP1AUX_fc (stack_Halt v) s`,
  REWRITE_TAC[S2LP1AUX_fc_def] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN
  CAKE_REWRITE_TAC[append_thm; stack_to_labProof_code_installed_def; is_Label_def;
                   call_args_def] THEN
  CASES_ON `stack_get_var v (s:(A,C,FFI)stack_state)` THEN
  CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; stack_get_var_def]) THEN
  CAKE_REWRITE_TAC[halt_view_def] THEN
  IMP_RES_TAC S2LP1AUX_rel_regs THEN
  MAP_EVERY EXISTS_TAC [`1`; `lab_state_clock_fupd (combin_K (lab_state_clock t1 + 1))
                                (t1:(A,C,FFI)lab_state)`] THEN
  IMP_RES_TAC S2LP1AUX_eval_halt THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[stack_empty_env_def] THEN SIMP[] THEN
  ASM_MESON_TAC[S2LP1AUX_rel_basic]);;

(* case Break *)
let S2LP1AUX_fc_break = prove
 (`!k (s:(A,C,FFI)stack_state). S2LP1AUX_fc (stack_Break k) s`,
  REWRITE_TAC[S2LP1AUX_fc_def] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN
  CAKE_REWRITE_TAC[PAIR_EQ; append_thm; stack_to_labProof_code_installed_def; is_Label_def] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  CAKE_REWRITE_TAC[halt_view_def; OPTION_MAP_DEF; result_view_def] THEN
  SUBGOAL_THEN `?pc. loc_to_pc n (find_lab k bs) (lab_state_code (t1:(A,C,FFI)lab_state)) = SOME pc`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\k. IS_SOME (loc_to_pc n k (lab_state_code (t1:(A,C,FFI)lab_state))))
                   (APPEND (APPEND cs bs) [0])` THEN
    REWRITE_TAC[GSYM ALL_MEM; MEM_APPEND; MEM] THEN
    DISCH_THEN(MP_TAC o SPEC `find_lab k bs`) THEN
    REWRITE_TAC[GSYM IS_SOME_EXISTS] THEN
    DISCH_THEN MATCH_MP_TAC THEN MESON_TAC[NOT_MEM_find_lab_IMP];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`1`; `lab_upd_pc pc (t1:(A,C,FFI)lab_state)`] THEN
  REWRITE_TAC[ARITH_RULE `(c + 1) + ck1 = (c + ck1) + 1`] THEN
  IMP_RES_TAC S2LP1AUX_eval_jump THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[lab_upd_pc_def] THEN SIMP[IS_PREFIX_REFL] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[S2LP1AUX_rel_lookup_loc];
    ASM_MESON_TAC[state_rel_with_pc; lab_upd_pc_def]]);;

(* case Continue *)
let S2LP1AUX_fc_continue = prove
 (`!k (s:(A,C,FFI)stack_state). S2LP1AUX_fc (stack_Continue k) s`,
  REWRITE_TAC[S2LP1AUX_fc_def] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN
  CAKE_REWRITE_TAC[PAIR_EQ; append_thm] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  CAKE_REWRITE_TAC[halt_view_def; OPTION_MAP_DEF; result_view_def] THEN
  MAP_EVERY EXISTS_TAC [`0`; `t1:(A,C,FFI)lab_state`] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; IS_PREFIX_REFL]);;

let S2LP1AUX_fc_alloc = prove
 (`!n (s:(A,C,FFI)stack_state). S2LP1AUX_fc (stack_Alloc n) s`,
  S2LP1AUX_FC_ERROR_TAC);;
let S2LP1AUX_fc_storeconsts = prove
 (`!t1 t2 stub_opt (s:(A,C,FFI)stack_state). S2LP1AUX_fc (stack_StoreConsts t1 t2 stub_opt) s`,
  S2LP1AUX_FC_ERROR_TAC);;
let S2LP1AUX_fc_get = prove
 (`!v name (s:(A,C,FFI)stack_state). S2LP1AUX_fc (stack_Get v name) s`,
  S2LP1AUX_FC_ERROR_TAC);;
let S2LP1AUX_fc_set = prove
 (`!name v (s:(A,C,FFI)stack_state). S2LP1AUX_fc (stack_Set name v) s`,
  S2LP1AUX_FC_ERROR_TAC);;
let S2LP1AUX_fc_opcurrheap = prove
 (`!binop v src (s:(A,C,FFI)stack_state). S2LP1AUX_fc (stack_OpCurrHeap binop v src) s`,
  S2LP1AUX_FC_ERROR_TAC);;
let S2LP1AUX_fc_databufferwrite = prove
 (`!r1 r2 (s:(A,C,FFI)stack_state). S2LP1AUX_fc (stack_DataBufferWrite r1 r2) s`,
  S2LP1AUX_FC_ERROR_TAC);;
let S2LP1AUX_fc_stackalloc = prove
 (`!n (s:(A,C,FFI)stack_state). S2LP1AUX_fc (StackAlloc n) s`,
  S2LP1AUX_FC_ERROR_TAC);;
let S2LP1AUX_fc_stackfree = prove
 (`!n (s:(A,C,FFI)stack_state). S2LP1AUX_fc (StackFree n) s`,
  S2LP1AUX_FC_ERROR_TAC);;
let S2LP1AUX_fc_stackload = prove
 (`!r n (s:(A,C,FFI)stack_state). S2LP1AUX_fc (StackLoad r n) s`,
  S2LP1AUX_FC_ERROR_TAC);;
let S2LP1AUX_fc_stackloadany = prove
 (`!r rn (s:(A,C,FFI)stack_state). S2LP1AUX_fc (StackLoadAny r rn) s`,
  S2LP1AUX_FC_ERROR_TAC);;
let S2LP1AUX_fc_stackstore = prove
 (`!r n (s:(A,C,FFI)stack_state). S2LP1AUX_fc (StackStore r n) s`,
  S2LP1AUX_FC_ERROR_TAC);;
let S2LP1AUX_fc_stackstoreany = prove
 (`!r rn (s:(A,C,FFI)stack_state). S2LP1AUX_fc (StackStoreAny r rn) s`,
  S2LP1AUX_FC_ERROR_TAC);;
let S2LP1AUX_fc_stackgetsize = prove
 (`!r (s:(A,C,FFI)stack_state). S2LP1AUX_fc (StackGetSize r) s`,
  S2LP1AUX_FC_ERROR_TAC);;
let S2LP1AUX_fc_stacksetsize = prove
 (`!r (s:(A,C,FFI)stack_state). S2LP1AUX_fc (StackSetSize r) s`,
  S2LP1AUX_FC_ERROR_TAC);;
let S2LP1AUX_fc_bitmapload = prove
 (`!r v (s:(A,C,FFI)stack_state). S2LP1AUX_fc (BitmapLoad r v) s`,
  S2LP1AUX_FC_ERROR_TAC);;

let S2LP1AUX_eval_cbw = prove
 (`!(t1:(A,C,FFI)lab_state) r1 r2 b k w1 w2 cb ck.
     asm_fetch_aux (lab_state_pc t1) (lab_state_code t1) = SOME (Asm (Cbw r1 r2) b k) /\
     lab_state_regs t1 r1 = wl_Word w1 /\ lab_state_regs t1 r2 = wl_Word w2 /\
     buffer_write (lab_state_code_buffer t1) w1 (word_zx w2) = SOME cb
     ==> lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t1) =
         lab_evaluate (lab_state_clock_fupd (combin_K ck)
                         (inc_pc (lab_state_code_buffer_fupd (combin_K cb) t1)))`,
  S2LP1AUX_LAB_STEP_TAC);;

(* the start of each case: the definitions of evaluate and flatten on the  *)
(* program, the code installed *)
let S2LP1AUX_FC_START_TAC : tactic =
  REWRITE_TAC[S2LP1AUX_fc_def] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN
  CAKE_REWRITE_TAC[append_thm; stack_to_labProof_code_installed_def; is_Label_def;
                   call_args_def];;

(* after the evaluation result is known *)
let S2LP1AUX_FC_RESULT_TAC : tactic =
  CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  CAKE_REWRITE_TAC[halt_view_def; OPTION_MAP_DEF; result_view_def];;

(* HOL4 flatten_correct, case Inst *)
let S2LP1AUX_fc_inst = prove
 (`!i (s:(A,C,FFI)stack_state). S2LP1AUX_fc (stack_Inst i) s`,
  S2LP1AUX_FC_START_TAC THEN
  CASES_ON `stack_inst i (s:(A,C,FFI)stack_state)` THEN S2LP1AUX_FC_RESULT_TAC THEN
  IMP_RES_TAC stack_to_labProof_inst_correct THEN
  SUBGOAL_THEN `~lab_state_failed (asm_inst i (t1:(A,C,FFI)lab_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[S2LP1AUX_rel_basic]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`1`; `inc_pc (asm_inst i (t1:(A,C,FFI)lab_state))`] THEN
  REWRITE_TAC[ARITH_RULE `(c + 1) + ck1 = (c + ck1) + 1`] THEN
  IMP_RES_TAC S2LP1AUX_eval_inst THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[inc_pc_def] THEN SIMP[asm_inst_consts; IS_PREFIX_REFL] THEN
  REWRITE_TAC[FILTER; o_THM; is_Label_def; LENGTH; ONE] THEN
  REWRITE_TAC[GSYM lab_upd_pc_def; GSYM ONE] THEN ASM_SIMP_TAC[state_rel_with_pc]);;

(* case Tick *)
let S2LP1AUX_fc_tick = prove
 (`!(s:(A,C,FFI)stack_state). S2LP1AUX_fc stack_Tick s`,
  S2LP1AUX_FC_START_TAC THEN
  ASM_CASES_TAC `stack_state_clock (s:(A,C,FFI)stack_state) = 0` THEN
  ASM_REWRITE_TAC[] THEN S2LP1AUX_FC_RESULT_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP S2LP1AUX_rel_basic) THEN
  MP_TAC(ISPECL [`t1:(A,C,FFI)lab_state`; `asm_Skip:(A)inst`; `[]:byte list`; `0`]
          S2LP1AUX_eval_inst) THEN
  ASM_REWRITE_TAC[asm_inst_def] THEN DISCH_TAC THENL
   [MAP_EVERY EXISTS_TAC [`1`; `inc_pc (t1:(A,C,FFI)lab_state)`] THEN
    REWRITE_TAC[ARITH_RULE `(c + 1) + ck1 = (c + ck1) + 1`; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[inc_pc_def] THEN SIMP_NOASM[IS_PREFIX_REFL; stack_empty_env_def] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES];
    MAP_EVERY EXISTS_TAC [`0`; `inc_pc (lab_dec_clock (t1:(A,C,FFI)lab_state))`] THEN
    SUBGOAL_THEN `!ck1. (stack_state_clock (s:(A,C,FFI)stack_state) + 0) + ck1 =
                        ((stack_state_clock s - 1) + ck1) + 1` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[inc_pc_def; lab_dec_clock_def; lab_state_component_equality] THEN
      SIMP_NOASM[] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[inc_pc_def; lab_dec_clock_def] THEN
    SIMP_NOASM[IS_PREFIX_REFL; FILTER; o_THM; is_Label_def; LENGTH] THEN
    MP_TAC(ISPECL [`s:(A,C,FFI)stack_state`; `t1:(A,C,FFI)lab_state`]
             stack_to_labProof_state_rel_dec_clock) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `lab_state_pc (t1:(A,C,FFI)lab_state) + 1` o
               MATCH_MP state_rel_with_pc) THEN
    REWRITE_TAC[lab_upd_pc_def; lab_dec_clock_def] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[lab_state_component_equality] THEN SIMP_NOASM[] THEN ASM_REWRITE_TAC[]]);;

(* cases Return and Raise: a jump to the location in the register *)
let S2LP1AUX_FC_JUMPREG_TAC : tactic =
  S2LP1AUX_FC_START_TAC THEN REWRITE_TAC[stack_get_var_def] THEN
  CASES_ON `FLOOKUP (stack_state_regs (s:(A,C,FFI)stack_state)) k` THEN CAKE_REWRITE_TAC[] THEN
  TRY(CASES_ON `a:(A)word_loc`) THEN S2LP1AUX_FC_RESULT_TAC THEN
  IMP_RES_TAC S2LP1AUX_rel_regs THEN
  ASM_CASES_TAC `?pc. loc_to_pc a0 a1 (lab_state_code (t1:(A,C,FFI)lab_state)) = SOME pc` THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `pc:num`) THEN
    MAP_EVERY EXISTS_TAC [`1`; `lab_upd_pc pc (t1:(A,C,FFI)lab_state)`] THEN
    REWRITE_TAC[ARITH_RULE `(c + 1) + ck1 = (c + ck1) + 1`] THEN
    IMP_RES_TAC S2LP1AUX_eval_jumpreg THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[lab_upd_pc_def] THEN SIMP_NOASM[IS_PREFIX_REFL] THEN
    ASM_REWRITE_TAC[option_INJ] THEN
    REWRITE_TAC[GSYM lab_upd_pc_def] THEN
    ASM_MESON_TAC[S2LP1AUX_rel_lookup_loc; state_rel_with_pc];
    MAP_EVERY EXISTS_TAC [`1`; `lab_state_clock_fupd (combin_K (lab_state_clock t1 + 1))
                                  (t1:(A,C,FFI)lab_state)`] THEN
    SIMP_NOASM[IS_PREFIX_REFL] THEN
    ASM_MESON_TAC[S2LP1AUX_rel_lookup_loc]];;

let S2LP1AUX_fc_return = prove
 (`!k (s:(A,C,FFI)stack_state). S2LP1AUX_fc (stack_Return k) s`,
  S2LP1AUX_FC_JUMPREG_TAC);;

let S2LP1AUX_fc_raise = prove
 (`!k (s:(A,C,FFI)stack_state). S2LP1AUX_fc (stack_Raise k) s`,
  S2LP1AUX_FC_JUMPREG_TAC);;

let S2LP1AUX_rel_code_buffer_fupd = prove
 (`!(s:(A,C,FFI)stack_state) t cb.
     stack_to_labProof_state_rel s t
     ==> stack_to_labProof_state_rel (stack_state_code_buffer_fupd (combin_K cb) s)
           (lab_state_code_buffer_fupd (combin_K cb) t)`,
  REWRITE_TAC[stack_to_labProof_state_rel_def] THEN
  SIMP_NOASM[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* case LocValue *)
let S2LP1AUX_fc_locvalue = prove
 (`!rr k1 k2 (s:(A,C,FFI)stack_state). S2LP1AUX_fc (stack_LocValue rr k1 k2) s`,
  S2LP1AUX_FC_START_TAC THEN COND_CASES_TAC THEN S2LP1AUX_FC_RESULT_TAC THEN
  MP_TAC(ISPECL [`s:(A,C,FFI)stack_state`; `k1:num`; `k2:num`; `t1:(A,C,FFI)lab_state`]
           loc_check_IMP_loc_to_pc) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `p:num`) THEN
  MAP_EVERY EXISTS_TAC [`1`; `inc_pc (lab_upd_reg rr (wl_Loc k1 k2) (t1:(A,C,FFI)lab_state))`] THEN
  REWRITE_TAC[ARITH_RULE `(c + 1) + ck1 = (c + ck1) + 1`] THEN
  IMP_RES_TAC S2LP1AUX_eval_locvalue THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[inc_pc_def; lab_upd_reg_def; lab_state_component_equality] THEN
    SIMP_NOASM[];
    ALL_TAC] THEN
  REWRITE_TAC[inc_pc_def; lab_upd_reg_def] THEN
  SIMP_NOASM[IS_PREFIX_REFL; FILTER; o_THM; is_Label_def; LENGTH] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`rr:num`; `wl_Loc k1 k2:(A)word_loc`] o
              MATCH_MP set_var_upd_reg) THEN
  DISCH_THEN(MP_TAC o SPEC `lab_state_pc (t1:(A,C,FFI)lab_state) + 1` o
             MATCH_MP state_rel_with_pc) THEN
  REWRITE_TAC[lab_upd_pc_def; lab_upd_reg_def] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[lab_state_component_equality] THEN SIMP_NOASM[]);;

(* case CodeBufferWrite *)
let S2LP1AUX_fc_codebufferwrite = prove
 (`!q1 q2 (s:(A,C,FFI)stack_state). S2LP1AUX_fc (stack_CodeBufferWrite q1 q2) s`,
  S2LP1AUX_FC_START_TAC THEN REWRITE_TAC[stack_get_var_def] THEN
  STRIP_TAC THEN REPEAT S2LP1AUX_ASM_CASE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  CAKE_REWRITE_TAC[halt_view_def; OPTION_MAP_DEF] THEN
  IMP_RES_TAC S2LP1AUX_rel_regs THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP S2LP1AUX_rel_basic) THEN
  MAP_EVERY EXISTS_TAC [`1`; `inc_pc (lab_state_code_buffer_fupd (combin_K (a:(A,8)buffer))
                                         (t1:(A,C,FFI)lab_state))`] THEN
  REWRITE_TAC[ARITH_RULE `(c + 1) + ck1 = (c + ck1) + 1`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(ASSUME `lab_state_code_buffer (t1:(A,C,FFI)lab_state) =
                                           stack_state_code_buffer (s:(A,C,FFI)stack_state)`)]) THEN
  IMP_RES_TAC S2LP1AUX_eval_cbw THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[inc_pc_def; lab_state_component_equality] THEN SIMP_NOASM[];
    ALL_TAC] THEN
  REWRITE_TAC[inc_pc_def] THEN
  SIMP_NOASM[IS_PREFIX_REFL; FILTER; o_THM; is_Label_def; LENGTH] THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:(A,8)buffer` o MATCH_MP S2LP1AUX_rel_code_buffer_fupd o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                          "stack_to_labProof_state_rel" with Failure _ -> false)) THEN
  DISCH_THEN(MP_TAC o SPEC `lab_state_pc (t1:(A,C,FFI)lab_state) + 1` o
             MATCH_MP state_rel_with_pc) THEN
  REWRITE_TAC[lab_upd_pc_def] THEN ASM_REWRITE_TAC[]);;

(* the conclusion of flatten_correct for a result r, final stack state s2, *)
(* initial and final lab states t1 and t2, extra clock ck and code length  *)
(* len (local definition), and S2LP1AUX_fc in terms of it                  *)
let S2LP1AUX_concl_def = new_definition (CASE_TERM
 `S2LP1AUX_concl (r:((A)stack_result)option) (s2:(A,C,FFI)stack_state) (t1:(A,C,FFI)lab_state)
     (t2:(A,C,FFI)lab_state) ck len n cs bs <=>
   (match halt_view r with
      SOME res ->
        lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock t1 + ck)) t1) = (res,t2) /\
        lab_state_ffi t2 = stack_state_ffi s2
    | NONE ->
        (!ck1. lab_evaluate (lab_state_clock_fupd (combin_K ((lab_state_clock t1 + ck) + ck1)) t1) =
               lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock t2 + ck1)) t2)) /\
        lab_state_len_reg t2 = lab_state_len_reg t1 /\
        lab_state_ptr_reg t2 = lab_state_ptr_reg t1 /\
        lab_state_len2_reg t2 = lab_state_len2_reg t1 /\
        lab_state_ptr2_reg t2 = lab_state_ptr2_reg t1 /\
        lab_state_link_reg t2 = lab_state_link_reg t1 /\
        lab_state_code t1 <<= lab_state_code t2 /\
        (match OPTION_MAP (\w. result_view w n cs bs) r with
           NONE ->
             lab_state_pc t2 = lab_state_pc t1 + len /\
             stack_to_labProof_state_rel s2 t2
         | SOME (Vloc n1 n2) ->
             (!n. IS_SOME (lookup n (stack_state_code s2))
                  ==> IS_SOME (loc_to_pc n 0 (lab_state_code t2))) /\
             (!w. loc_to_pc n1 n2 (lab_state_code t2) = SOME w
                  ==> w = lab_state_pc t2 /\ stack_to_labProof_state_rel s2 t2)
         | SOME (Vcont n1 n2) ->
             stack_to_labProof_state_rel s2 t2 /\
             stack_to_labProof_code_installed (lab_state_pc t2)
               [LabAsm (lab_Jump (lab_Lab n1 n2)) (word 0) [] 0] (lab_state_code t2)
         | SOME Vtimeout -> lab_state_ffi t2 = stack_state_ffi s2 /\ lab_state_clock t2 = 0
         | _ -> F))`);;

let S2LP1AUX_fc_alt = prove
 (`!(prog:(A)stack_prog) (s1:(A,C,FFI)stack_state).
     S2LP1AUX_fc prog s1 <=>
     !t r s2 n l cs bs (t1:(A,C,FFI)lab_state).
       stack_evaluate (prog,s1) = (r,s2) /\ ~(r = SOME stack_Error) /\
       stack_to_labProof_state_rel s1 t1 /\
       call_args prog (lab_state_ptr_reg t1) (lab_state_len_reg t1) (lab_state_ptr2_reg t1)
         (lab_state_len2_reg t1) (lab_state_link_reg t1) /\
       stack_to_labProof_code_installed (lab_state_pc t1)
         (append (FST (stack_to_lab_flatten t prog n l cs bs))) (lab_state_code t1) /\
       ALL (\k. IS_SOME (loc_to_pc n k (lab_state_code t1))) (APPEND (APPEND cs bs) [0])
       ==> ?ck t2. S2LP1AUX_concl r s2 t1 t2 ck
                     (LENGTH (FILTER ((~) o is_Label)
                                (append (FST (stack_to_lab_flatten t prog n l cs bs)))))
                     n cs bs`,
  REWRITE_TAC[S2LP1AUX_fc_def; S2LP1AUX_concl_def]);;

(* a run to the end of a piece of code (result NONE) followed by a run of  *)
(* the rest (local helper) *)
let S2LP1AUX_concl_seq = prove
 (`!r (s2:(A,C,FFI)stack_state) (t1:(A,C,FFI)lab_state) t2 t3 ck ck' len1 len2 n cs bs.
     (!ck1. lab_evaluate (lab_state_clock_fupd (combin_K ((lab_state_clock t1 + ck) + ck1)) t1) =
            lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock t2 + ck1)) t2)) /\
     lab_state_len_reg t2 = lab_state_len_reg t1 /\
     lab_state_ptr_reg t2 = lab_state_ptr_reg t1 /\
     lab_state_len2_reg t2 = lab_state_len2_reg t1 /\
     lab_state_ptr2_reg t2 = lab_state_ptr2_reg t1 /\
     lab_state_link_reg t2 = lab_state_link_reg t1 /\
     lab_state_code t1 <<= lab_state_code t2 /\
     lab_state_pc t2 = lab_state_pc t1 + len1 /\
     S2LP1AUX_concl r s2 t2 t3 ck' len2 n cs bs
     ==> S2LP1AUX_concl r s2 t1 t3 (ck + ck') (len1 + len2) n cs bs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[S2LP1AUX_concl_def] THEN
  STRUCT_CASES_TAC(ISPEC `halt_view (r:((A)stack_result)option)` (cases "option")) THEN
  CAKE_REWRITE_TAC[] THEN STRIP_TAC THENL
   [CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[ARITH_RULE `(a + b + c) + d = (a + b) + (c + d)`] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[ADD_ASSOC] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[IS_PREFIX_TRANS]; ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN
    STRUCT_CASES_TAC(ISPEC `r:((A)stack_result)option` (cases "option")) THEN
    CAKE_REWRITE_TAC[OPTION_MAP_DEF] THEN TRY(ASM_REWRITE_TAC[ADD_ASSOC] THEN NO_TAC) THEN
    SPEC_TAC(`result_view (a:(A)stack_result) n cs bs`,`v:result_view`) THEN
    MATCH_MP_TAC result_view_INDUCT THEN CAKE_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `ck':num`) THEN
    REWRITE_TAC[ADD_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* the code length matters only for the result NONE (local helper) *)
let S2LP1AUX_concl_len = prove
 (`!r (s2:(A,C,FFI)stack_state) (t1:(A,C,FFI)lab_state) t2 ck len len' n cs bs.
     ~(r = NONE)
     ==> (S2LP1AUX_concl r s2 t1 t2 ck len n cs bs <=>
          S2LP1AUX_concl r s2 t1 t2 ck len' n cs bs)`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:((A)stack_result)option` (cases "option")) THEN
  REWRITE_TAC[S2LP1AUX_concl_def; OPTION_MAP_DEF; option_DISTINCT] THEN
  CAKE_REWRITE_TAC[]);;

(* case Seq *)
let S2LP1AUX_fc_seq = prove
 (`!c1 c2 (s:(A,C,FFI)stack_state).
     S2LP1AUX_fc c1 s /\ (!s1. stack_evaluate (c1,s) = (NONE,s1) ==> S2LP1AUX_fc c2 s1)
     ==> S2LP1AUX_fc (stack_Seq c1 c2) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[S2LP1AUX_fc_alt] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC[stack_evaluate_def] THEN ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN
   CAKE_REWRITE_TAC[LET_DEF; LET_END_DEF; call_args_def] THEN
   REPEAT S2LP1AUX_PAIRARG_TAC THEN
   ASM_CASES_TAC `t:bool` THEN ASM_REWRITE_TAC[FST] THEN
   REWRITE_TAC[append_thm; S2LP1AUX_code_installed_APPEND_EQ; FILTER_APPEND; LENGTH_APPEND;
               FILTER; o_THM; is_Label_def; LENGTH; stack_to_labProof_code_installed_def;
               ADD_CLAUSES] THEN
   CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN
   (ASM_CASES_TAC `res:((A)stack_result)option = NONE` THEN
   FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_cond (lhs (concl th)) then
     MP_TAC th else NO_TAC) THEN ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
   [REMOVE_THEN "ih1" (MP_TAC o SPECL [`F`; `NONE:((A)stack_result)option`;
       `s1:(A,C,FFI)stack_state`; `n:num`; `l:num`; `cs:num list`; `bs:num list`;
       `t1:(A,C,FFI)lab_state`]) THEN
    ASM_REWRITE_TAC[FST; option_DISTINCT] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(A,C,FFI)lab_state`
      (STRIP_ASSUME_TAC o CAKE_REWRITE_RULE[halt_view_def; OPTION_MAP_DEF] o
       REWRITE_RULE[S2LP1AUX_concl_def]))) THEN
    REMOVE_THEN "ih2" (MP_TAC o SPEC `s1:(A,C,FFI)stack_state`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`F`; `r:((A)stack_result)option`;
       `s2:(A,C,FFI)stack_state`; `n:num`; `m:num`; `cs:num list`; `bs:num list`;
       `t2:(A,C,FFI)lab_state`]) THEN
    ASM_REWRITE_TAC[FST] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC code_installed_isPREFIX THEN
        EXISTS_TAC `lab_state_code (t1:(A,C,FFI)lab_state)` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC every_is_some_loc_to_pc_prefix THEN
        EXISTS_TAC `lab_state_code (t1:(A,C,FFI)lab_state)` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck':num` (X_CHOOSE_THEN `t3:(A,C,FFI)lab_state`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ck + ck':num`; `t3:(A,C,FFI)lab_state`] THEN
    MATCH_MP_TAC S2LP1AUX_concl_seq THEN EXISTS_TAC `t2:(A,C,FFI)lab_state` THEN
    ASM_REWRITE_TAC[];
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`F`; `r:((A)stack_result)option`;
       `s2:(A,C,FFI)stack_state`; `n:num`; `l:num`; `cs:num list`; `bs:num list`;
       `t1:(A,C,FFI)lab_state`]) THEN
    ASM_REWRITE_TAC[FST] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(A,C,FFI)lab_state`
      ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`ck:num`; `t2:(A,C,FFI)lab_state`] THEN
    ASM_MESON_TAC[S2LP1AUX_concl_len]]));;

(* a run with result NONE, then one lab step (local helper) *)
let S2LP1AUX_concl_then_step = prove
 (`!(s2:(A,C,FFI)stack_state) (t1:(A,C,FFI)lab_state) t2 t3 ck len1 len n cs bs.
     S2LP1AUX_concl NONE s2 t1 t2 ck len1 n cs bs /\
     (!ck. lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t2) =
           lab_evaluate (lab_state_clock_fupd (combin_K ck) t3)) /\
     lab_state_clock t3 = lab_state_clock t2 /\
     lab_state_len_reg t3 = lab_state_len_reg t2 /\
     lab_state_ptr_reg t3 = lab_state_ptr_reg t2 /\
     lab_state_len2_reg t3 = lab_state_len2_reg t2 /\
     lab_state_ptr2_reg t3 = lab_state_ptr2_reg t2 /\
     lab_state_link_reg t3 = lab_state_link_reg t2 /\
     lab_state_code t3 = lab_state_code t2 /\
     lab_state_pc t3 = lab_state_pc t1 + len /\
     stack_to_labProof_state_rel s2 t3
     ==> S2LP1AUX_concl NONE s2 t1 t3 (ck + 1) len n cs bs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[S2LP1AUX_concl_def] THEN
  CAKE_REWRITE_TAC[halt_view_def; OPTION_MAP_DEF] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `(c + (ck + 1)) + ck1 = (c + ck) + (ck1 + 1)`] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH_RULE `c + (ck1 + 1) = (c + ck1) + 1`] THEN
  ASM_REWRITE_TAC[]);;

(* the result NONE (local helper) *)
let S2LP1AUX_concl_none = prove
 (`!(s2:(A,C,FFI)stack_state) (t1:(A,C,FFI)lab_state) t2 ck len n cs bs.
     S2LP1AUX_concl NONE s2 t1 t2 ck len n cs bs <=>
     (!ck1. lab_evaluate (lab_state_clock_fupd (combin_K ((lab_state_clock t1 + ck) + ck1)) t1) =
            lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock t2 + ck1)) t2)) /\
     lab_state_len_reg t2 = lab_state_len_reg t1 /\
     lab_state_ptr_reg t2 = lab_state_ptr_reg t1 /\
     lab_state_len2_reg t2 = lab_state_len2_reg t1 /\
     lab_state_ptr2_reg t2 = lab_state_ptr2_reg t1 /\
     lab_state_link_reg t2 = lab_state_link_reg t1 /\
     lab_state_code t1 <<= lab_state_code t2 /\
     lab_state_pc t2 = lab_state_pc t1 + len /\
     stack_to_labProof_state_rel s2 t2`,
  REWRITE_TAC[S2LP1AUX_concl_def] THEN CAKE_REWRITE_TAC[halt_view_def; OPTION_MAP_DEF]);;

(* lab_upd_pc changes only the pc, and inc_pc is a lab_upd_pc (local       *)
(* helpers of flatten_correct) *)
let S2LP1AUX_upd_pc_simps = prove
 (`!p (t:(A,C,FFI)lab_state).
     lab_state_pc (lab_upd_pc p t) = p /\
     lab_state_code (lab_upd_pc p t) = lab_state_code t /\
     lab_state_clock (lab_upd_pc p t) = lab_state_clock t /\
     lab_state_regs (lab_upd_pc p t) = lab_state_regs t /\
     lab_state_len_reg (lab_upd_pc p t) = lab_state_len_reg t /\
     lab_state_ptr_reg (lab_upd_pc p t) = lab_state_ptr_reg t /\
     lab_state_len2_reg (lab_upd_pc p t) = lab_state_len2_reg t /\
     lab_state_ptr2_reg (lab_upd_pc p t) = lab_state_ptr2_reg t /\
     lab_state_link_reg (lab_upd_pc p t) = lab_state_link_reg t /\
     lab_state_ffi (lab_upd_pc p t) = lab_state_ffi t`,
  REWRITE_TAC[lab_upd_pc_def] THEN SIMP[]);;

let S2LP1AUX_inc_pc_upd = prove
 (`!(t:(A,C,FFI)lab_state). inc_pc t = lab_upd_pc (lab_state_pc t + 1) t`,
  REWRITE_TAC[inc_pc_def; lab_upd_pc_def]);;

(* a run to t2, then a run from t2; the code length matters only for the  *)
(* result NONE (local helper) *)
let S2LP1AUX_concl_seq_gen = prove
 (`!r (s2:(A,C,FFI)stack_state) (t1:(A,C,FFI)lab_state) t2 t3 ck ck' len2 len n cs bs.
     (!ck1. lab_evaluate (lab_state_clock_fupd (combin_K ((lab_state_clock t1 + ck) + ck1)) t1) =
            lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock t2 + ck1)) t2)) /\
     lab_state_len_reg t2 = lab_state_len_reg t1 /\
     lab_state_ptr_reg t2 = lab_state_ptr_reg t1 /\
     lab_state_len2_reg t2 = lab_state_len2_reg t1 /\
     lab_state_ptr2_reg t2 = lab_state_ptr2_reg t1 /\
     lab_state_link_reg t2 = lab_state_link_reg t1 /\
     lab_state_code t1 <<= lab_state_code t2 /\
     (r = NONE ==> lab_state_pc t2 + len2 = lab_state_pc t1 + len) /\
     S2LP1AUX_concl r s2 t2 t3 ck' len2 n cs bs
     ==> S2LP1AUX_concl r s2 t1 t3 (ck + ck') len n cs bs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[S2LP1AUX_concl_def] THEN
  STRUCT_CASES_TAC(ISPEC `halt_view (r:((A)stack_result)option)` (cases "option")) THEN
  CAKE_REWRITE_TAC[] THENL
   [STRUCT_CASES_TAC(ISPEC `r:((A)stack_result)option` (cases "option")) THEN
    CAKE_REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT] THEN STRIP_TAC THEN
    (CONJ_TAC THENL
      [GEN_TAC THEN REWRITE_TAC[ARITH_RULE `(a + b + c) + d = (a + b) + (c + d)`] THEN
       ASM_REWRITE_TAC[] THEN REWRITE_TAC[ADD_ASSOC] THEN ASM_REWRITE_TAC[];
       ALL_TAC]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IS_PREFIX_TRANS];
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ck':num`) THEN
    REWRITE_TAC[ADD_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* a step to the pc p, then a run from there (local helper) *)
let S2LP1AUX_concl_jump = prove
 (`!r (s2:(A,C,FFI)stack_state) (t1:(A,C,FFI)lab_state) t3 ck p len2 len n cs bs.
     (!ck. lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t1) =
           lab_evaluate (lab_state_clock_fupd (combin_K ck) (lab_upd_pc p t1))) /\
     (r = NONE ==> p + len2 = lab_state_pc t1 + len) /\
     S2LP1AUX_concl r s2 (lab_upd_pc p t1) t3 ck len2 n cs bs
     ==> S2LP1AUX_concl r s2 t1 t3 (1 + ck) len n cs bs`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC S2LP1AUX_concl_seq_gen THEN
  EXISTS_TAC `lab_upd_pc p (t1:(A,C,FFI)lab_state)` THEN EXISTS_TAC `len2:num` THEN
  ASM_REWRITE_TAC[S2LP1AUX_upd_pc_simps; IS_PREFIX_REFL] THEN
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `(c + 1) + ck1 = (c + ck1) + 1`] THEN
  ASM_REWRITE_TAC[]);;

(* the empty run (local helper) *)
let S2LP1AUX_concl_refl = prove
 (`!(s:(A,C,FFI)stack_state) t n cs bs.
     stack_to_labProof_state_rel s t ==> S2LP1AUX_concl NONE s t t 0 0 n cs bs`,
  REWRITE_TAC[S2LP1AUX_concl_none; ADD_CLAUSES; IS_PREFIX_REFL] THEN MESON_TAC[]);;

(* a run with result NONE to a Jump, and the Jump (local helper) *)
let S2LP1AUX_concl_then_jump = prove
 (`!(s2:(A,C,FFI)stack_state) (t1:(A,C,FFI)lab_state) t2 ck len1 len q p n1 n2 w b k n cs bs.
     S2LP1AUX_concl NONE s2 t1 t2 ck len1 n cs bs /\
     asm_fetch_aux q (lab_state_code t1) = SOME (LabAsm (lab_Jump (lab_Lab n1 n2)) w b k) /\
     q = lab_state_pc t1 + len1 /\
     loc_to_pc n1 n2 (lab_state_code t1) = SOME p /\
     p = lab_state_pc t1 + len
     ==> S2LP1AUX_concl NONE s2 t1 (lab_upd_pc p t2) (ck + 1) len n cs bs`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC (REWRITE_RULE[S2LP1AUX_concl_none] th)) STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `p = lab_state_pc (t1:(A,C,FFI)lab_state) + len`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `q = lab_state_pc (t1:(A,C,FFI)lab_state) + len1`)) THEN
  MATCH_MP_TAC S2LP1AUX_concl_then_step THEN
  MAP_EVERY EXISTS_TAC [`t2:(A,C,FFI)lab_state`; `len1:num`] THEN
  ASM_REWRITE_TAC[S2LP1AUX_upd_pc_simps] THEN
  SUBGOAL_THEN
   `asm_fetch_aux (lab_state_pc t2) (lab_state_code (t2:(A,C,FFI)lab_state)) =
      SOME (LabAsm (lab_Jump (lab_Lab n1 n2)) w b k) /\
    loc_to_pc n1 n2 (lab_state_code t2) = SOME (lab_state_pc (t1:(A,C,FFI)lab_state) + len)`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC asm_fetch_aux_SOME_isPREFIX THEN
      EXISTS_TAC `lab_state_code (t1:(A,C,FFI)lab_state)` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC loc_to_pc_isPREFIX THEN
      EXISTS_TAC `lab_state_code (t1:(A,C,FFI)lab_state)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC S2LP1AUX_eval_jump THEN
    MAP_EVERY EXISTS_TAC [`n1:num`; `n2:num`; `w:A word`; `b:byte list`; `k:num`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC state_rel_with_pc THEN ASM_REWRITE_TAC[]]);;

(* tactics of the If case of flatten_correct (local helpers) *)
let S2LP1AUX_IF_RWS = [FST; append_thm; APPEND; S2LP1AUX_code_installed_APPEND_EQ;
  FILTER_APPEND; LENGTH_APPEND; FILTER; o_THM; is_Label_def; LENGTH; ADD_0;
  ARITH_RULE `SUC 0 = 1`; stack_to_labProof_code_installed_def];;

let S2LP1AUX_IF_NORM_TAC : tactic =
  RULE_ASSUM_TAC(CAKE_REWRITE_RULE S2LP1AUX_IF_RWS) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  CAKE_REWRITE_TAC S2LP1AUX_IF_RWS;;

let S2LP1AUX_IF_SKIP_EVAL_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term ((=) `stack_evaluate (stack_Skip,s:(A,C,FFI)stack_state)`)) (concl th))) THEN
  REWRITE_TAC[stack_evaluate_def; COND_ID; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC;;

(* the pc of the label (n,lab) installed in the code *)
let S2LP1AUX_WITH_LOC (lab:term) (ttac:term->tactic) : tactic = fun (asl,w as g) ->
  let is_loc th = let c = concl th in
    is_eq c && (let f,args = strip_comb (lhs c) in
                is_const f && fst(dest_const f) = "loc_to_pc" && length args = 3 &&
                el 1 args = lab) in
  let th = snd (find (fun (_,th) -> is_loc th) asl) in
  ttac (rand (rhs (concl th))) g;;

(* code_installed p l code from code_installed q l code with p = q *)
let S2LP1AUX_CI_ARITH_TAC : tactic = fun (asl,w as g) ->
  let f,args = strip_comb w in
  let p = el 0 args and l = el 1 args and code = el 2 args in
  let th = snd (find (fun (_,th) -> let c = concl th in
     let f',args' = strip_comb c in
     f' = f && length args' = 3 && el 1 args' = l && el 2 args' = code) asl) in
  let q = el 0 (snd (strip_comb (concl th))) in
  (SUBGOAL_THEN (mk_eq(p,q)) SUBST1_TAC THENL [ARITH_TAC; ACCEPT_TAC th]) g;;

let S2LP1AUX_upd_tm (p:term) = subst [p,`pp:num`] `lab_upd_pc pp (t1:(A,C,FFI)lab_state)`;;

(* the run of the branch prog with the induction hypothesis ih (case b of  *)
(* the test, label counter lv) from the pc p *)
let S2LP1AUX_IF_IH_TAC (ih:string) (bv:term) (lv:term) (p:term) : tactic =
  REMOVE_THEN ih (MP_TAC o SPECL [`x:(A)word_loc`; `y:(A)word_loc`; bv]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`F`; `r:((A)stack_result)option`; `s2:(A,C,FFI)stack_state`;
    `n:num`; lv; `cs:num list`; `bs:num list`; S2LP1AUX_upd_tm p]) THEN
  ASM_REWRITE_TAC[FST; S2LP1AUX_upd_pc_simps] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC state_rel_with_pc THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    S2LP1AUX_CI_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(A,C,FFI)lab_state` ASSUME_TAC));;

(* r is not NONE when the branch prog (label counter lv) does not return *)
let S2LP1AUX_IF_NORET_TAC (c:term) (lv:term) : tactic =
  DISCH_TAC THEN
  MP_TAC(ISPECL [`F`; c; `n:num`; lv; `cs:num list`; `bs:num list`] no_ret_correct) THEN
  ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN(MP_TAC o SPEC `s:(A,C,FFI)stack_state`) THEN
  ASM_REWRITE_TAC[FST; IS_SOME_DEF];;

(* the first step (lemma step) to the pc p, then the run th from there; the *)
(* arithmetic of the pcs by arith *)
let S2LP1AUX_IF_FINISH_TAC (step:thm) (p:term) (arith:tactic) : thm_tactic = fun th ->
  let args = snd (strip_comb (concl th)) in
  let t2 = el 3 args and ck = el 4 args and len2 = el 5 args in
  EXISTS_TAC (mk_binop `(+):num->num->num` `1` ck) THEN EXISTS_TAC t2 THEN
  MATCH_MP_TAC S2LP1AUX_concl_jump THEN EXISTS_TAC p THEN EXISTS_TAC len2 THEN
  REPEAT CONJ_TAC THENL
   [IMP_RES_TAC step THEN ASM_REWRITE_TAC[S2LP1AUX_inc_pc_upd];
    arith;
    ACCEPT_TAC th];;

let S2LP1AUX_IF_ARITH_TAC : tactic = DISCH_TAC THEN ARITH_TAC;;

(* a taken jump to the end, the branch being Skip *)
let S2LP1AUX_IF_JUMP_END_TAC (lab:term) : tactic =
  S2LP1AUX_WITH_LOC lab (fun p ->
    S2LP1AUX_IF_SKIP_EVAL_TAC THEN
    (fun (asl,w as g) ->
      let sst = el 1 (snd (strip_comb (snd (strip_exists w)))) in
      (SUBGOAL_THEN (subst [S2LP1AUX_upd_tm p,`tt:(A,C,FFI)lab_state`; sst,`ss:(A,C,FFI)stack_state`]
         `S2LP1AUX_concl NONE (ss:(A,C,FFI)stack_state) tt tt 0 0 n cs bs`) ASSUME_TAC THENL
       [MATCH_MP_TAC S2LP1AUX_concl_refl THEN MATCH_MP_TAC state_rel_with_pc THEN
        ASM_REWRITE_TAC[];
        ALL_TAC]) g) THEN
    POP_ASSUM(S2LP1AUX_IF_FINISH_TAC S2LP1AUX_eval_jumpcmp_T p S2LP1AUX_IF_ARITH_TAC));;

(* apply ttac to the assumption S2LP1AUX_concl ... (removing it) *)
let S2LP1AUX_CONCL_ASSUM (ttac:thm_tactic) : tactic =
  FIRST_X_ASSUM(fun th ->
    if (try fst(dest_const(fst(strip_comb(concl th)))) = "S2LP1AUX_concl" with Failure _ -> false)
    then ttac th else NO_TAC);;

(* the last case of If with b false: the run of the second branch, then the *)
(* Jump to the end if it ends normally *)
let S2LP1AUX_IF_LAST_TAC : tactic =
  let p1 = `lab_state_pc (t1:(A,C,FFI)lab_state) + 1` in
  ASM_CASES_TAC `r:((A)stack_result)option = NONE` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    S2LP1AUX_WITH_LOC `m' + 1` (fun pend ->
      let len' = rand pend in
      SUBGOAL_THEN (subst [pend,`pe:num`; len',`le:num`]
        `S2LP1AUX_concl NONE (s2:(A,C,FFI)stack_state) (lab_upd_pc (lab_state_pc t1 + 1) t1)
           (lab_upd_pc pe t2) (ck + 1) le n cs bs`) ASSUME_TAC THENL
       [MATCH_MP_TAC S2LP1AUX_concl_then_jump THEN
        MAP_EVERY EXISTS_TAC
         [`LENGTH (FILTER ((~) o is_Label) (append (ys:((A)line)app_list)))`;
          `(lab_state_pc (t1:(A,C,FFI)lab_state) + 1) +
           LENGTH (FILTER ((~) o is_Label) (append (ys:((A)line)app_list)))`;
          `n:num`; `m' + 1`; `word 0:A word`; `[]:byte list`; `0`] THEN
        ASM_REWRITE_TAC[S2LP1AUX_upd_pc_simps] THEN ARITH_TAC;
        ALL_TAC] THEN
      POP_ASSUM(S2LP1AUX_IF_FINISH_TAC S2LP1AUX_eval_jumpcmp_F p1 S2LP1AUX_IF_ARITH_TAC));
    S2LP1AUX_CONCL_ASSUM(S2LP1AUX_IF_FINISH_TAC S2LP1AUX_eval_jumpcmp_F p1 (ASM_REWRITE_TAC[]))];;

(* case If (HOL4 lines 1532-1817) *)
let S2LP1AUX_fc_if = prove
 (`!cmp r1 ri c1 c2 (s:(A,C,FFI)stack_state).
     (!x y b. stack_get_var r1 s = SOME x /\ stack_get_var_imm ri s = SOME y /\
              wl_word_cmp cmp x y = SOME b /\ b ==> S2LP1AUX_fc c1 s) /\
     (!x y b. stack_get_var r1 s = SOME x /\ stack_get_var_imm ri s = SOME y /\
              wl_word_cmp cmp x y = SOME b /\ ~b ==> S2LP1AUX_fc c2 s)
     ==> S2LP1AUX_fc (stack_If cmp r1 ri c1 c2) s`,
  let p1 = `lab_state_pc (t1:(A,C,FFI)lab_state) + 1` in
  REPEAT GEN_TAC THEN REWRITE_TAC[S2LP1AUX_fc_alt] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN
  CAKE_REWRITE_TAC[LET_DEF; LET_END_DEF; call_args_def] THEN
  REPEAT S2LP1AUX_PAIRARG_TAC THEN
  ASM_CASES_TAC `?x y b. stack_get_var r1 (s:(A,C,FFI)stack_state) = SOME x /\
                         stack_get_var_imm ri s = SOME y /\ wl_word_cmp cmp x y = SOME b` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `x:(A)word_loc` (X_CHOOSE_THEN `y:(A)word_loc`
      (X_CHOOSE_THEN `b:bool` STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN STRIP_TAC;
    STRIP_TAC THEN REPEAT S2LP1AUX_ASM_CASE_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
    REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
    ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN `wl_word_cmp cmp (lab_state_regs (t1:(A,C,FFI)lab_state) r1) (lab_reg_imm ri t1) = SOME b /\
                wl_word_cmp (stack_to_lab_negate cmp) (lab_state_regs t1 r1) (lab_reg_imm ri t1) =
                SOME (~b)` STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    IMP_RES_TAC S2LP1AUX_rel_regs THEN IMP_RES_TAC state_rel_get_var_imm THEN
    ASM_REWRITE_TAC[word_cmp_negate; OPTION_MAP_DEF];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term ((=) `stack_evaluate (c1,s:(A,C,FFI)stack_state)`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN DISCH_TAC THEN
  S2LP1AUX_CASES_ON `c1:(A)stack_prog = stack_Skip` THENL
   [S2LP1AUX_CASES_ON `c2:(A)stack_prog = stack_Skip` THENL
     [S2LP1AUX_IF_NORM_TAC THEN S2LP1AUX_IF_SKIP_EVAL_TAC THEN
      MAP_EVERY EXISTS_TAC [`0`; `t1:(A,C,FFI)lab_state`] THEN
      MATCH_MP_TAC S2LP1AUX_concl_refl THEN ASM_REWRITE_TAC[];
      S2LP1AUX_IF_NORM_TAC THEN S2LP1AUX_CASES_ON `b:bool` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THENL
       [S2LP1AUX_IF_JUMP_END_TAC `m':num`;
        S2LP1AUX_IF_IH_TAC "ih2" `F` `m:num` p1 THEN
        POP_ASSUM(S2LP1AUX_IF_FINISH_TAC S2LP1AUX_eval_jumpcmp_F p1 S2LP1AUX_IF_ARITH_TAC)]];
    S2LP1AUX_CASES_ON `c2:(A)stack_prog = stack_Skip` THENL
     [S2LP1AUX_IF_NORM_TAC THEN S2LP1AUX_CASES_ON `b:bool` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THENL
       [S2LP1AUX_IF_IH_TAC "ih1" `T` `l:num` p1 THEN
        POP_ASSUM(S2LP1AUX_IF_FINISH_TAC S2LP1AUX_eval_jumpcmp_F p1 S2LP1AUX_IF_ARITH_TAC);
        S2LP1AUX_IF_JUMP_END_TAC `m':num`];
      S2LP1AUX_CASES_ON `nr1:bool` THENL
       [S2LP1AUX_IF_NORM_TAC THEN S2LP1AUX_CASES_ON `b:bool` THEN
        RULE_ASSUM_TAC(REWRITE_RULE[]) THENL
         [S2LP1AUX_IF_IH_TAC "ih1" `T` `l:num` p1 THEN
          POP_ASSUM(S2LP1AUX_IF_FINISH_TAC S2LP1AUX_eval_jumpcmp_F p1
            (S2LP1AUX_IF_NORET_TAC `c1:(A)stack_prog` `l:num`));
          S2LP1AUX_WITH_LOC `m':num` (fun p -> S2LP1AUX_IF_IH_TAC "ih2" `F` `m:num` p THEN
            POP_ASSUM(S2LP1AUX_IF_FINISH_TAC S2LP1AUX_eval_jumpcmp_T p S2LP1AUX_IF_ARITH_TAC))];
        S2LP1AUX_CASES_ON `nr2:bool` THENL
         [S2LP1AUX_IF_NORM_TAC THEN S2LP1AUX_CASES_ON `b:bool` THEN
          RULE_ASSUM_TAC(REWRITE_RULE[]) THENL
           [S2LP1AUX_WITH_LOC `m':num` (fun p -> S2LP1AUX_IF_IH_TAC "ih1" `T` `l:num` p THEN
              POP_ASSUM(S2LP1AUX_IF_FINISH_TAC S2LP1AUX_eval_jumpcmp_T p S2LP1AUX_IF_ARITH_TAC));
            S2LP1AUX_IF_IH_TAC "ih2" `F` `m:num` p1 THEN
            POP_ASSUM(S2LP1AUX_IF_FINISH_TAC S2LP1AUX_eval_jumpcmp_F p1
              (S2LP1AUX_IF_NORET_TAC `c2:(A)stack_prog` `m:num`))];
          S2LP1AUX_IF_NORM_TAC THEN S2LP1AUX_CASES_ON `b:bool` THEN
          RULE_ASSUM_TAC(REWRITE_RULE[]) THENL
           [S2LP1AUX_WITH_LOC `m':num` (fun p -> S2LP1AUX_IF_IH_TAC "ih1" `T` `l:num` p THEN
              POP_ASSUM(S2LP1AUX_IF_FINISH_TAC S2LP1AUX_eval_jumpcmp_T p S2LP1AUX_IF_ARITH_TAC));
            S2LP1AUX_IF_IH_TAC "ih2" `F` `m:num` p1 THEN S2LP1AUX_IF_LAST_TAC]]]]]);;

(* find_lab of a list with a head (local helper) *)
let S2LP1AUX_find_lab_cons = prove
 (`!k x bs. find_lab 0 (CONS x bs) = x /\
            (~(k = 0) ==> find_lab k (CONS x bs) = find_lab (k - 1) bs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[find_lab_def; oEL_DEF] THEN CAKE_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);;

(* the body of a Loop exits the loop (local helper of flatten_correct) *)
let S2LP1AUX_concl_exit_loop = prove
 (`!res (s1:(A,C,FFI)stack_state) (t1:(A,C,FFI)lab_state) t2 ck len len' n l cs bs.
     ~stack_cont_loop res /\ ~(res = SOME stack_Error) /\
     S2LP1AUX_concl res s1 t1 t2 ck len n (CONS l cs) (CONS (l + 1) bs) /\
     loc_to_pc n (l + 1) (lab_state_code t1) = SOME (lab_state_pc t1 + len')
     ==> S2LP1AUX_concl (stack_exit_loop res) s1 t1 t2 ck len' n cs bs`,
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `res:((A)stack_result)option` (cases "option")) THEN
  REWRITE_TAC[stack_cont_loop_def] THEN
  STRUCT_CASES_TAC(ISPEC `a:(A)stack_result` (cases "stack_result")) THEN
  REWRITE_TAC[stack_cont_loop_def; stack_exit_loop_def; option_INJ;
              distinctness "stack_result"] THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[S2LP1AUX_concl_def] THEN
    CAKE_REWRITE_TAC[halt_view_def; OPTION_MAP_DEF] THEN
    CASES_ON `a':(A)word_loc` THEN CAKE_REWRITE_TAC[result_view_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[S2LP1AUX_concl_def] THEN
    CAKE_REWRITE_TAC[halt_view_def; OPTION_MAP_DEF] THEN
    CASES_ON `a':(A)word_loc` THEN CAKE_REWRITE_TAC[result_view_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN ASM_CASES_TAC `a':num = 0` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[S2LP1AUX_concl_def] THEN
    CAKE_REWRITE_TAC[halt_view_def; OPTION_MAP_DEF; result_view_def] THENL
     [REWRITE_TAC[S2LP1AUX_find_lab_cons] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `loc_to_pc n (l + 1) (lab_state_code (t2:(A,C,FFI)lab_state)) =
                    SOME (lab_state_pc (t1:(A,C,FFI)lab_state) + len')`
        (fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THENL
       [MATCH_MP_TAC loc_to_pc_isPREFIX THEN
        EXISTS_TAC `lab_state_code (t1:(A,C,FFI)lab_state)` THEN ASM_REWRITE_TAC[];
        STRIP_TAC THEN ASM_REWRITE_TAC[]];
      MP_TAC(SPECL [`a':num`; `l + 1`; `bs:num list`] S2LP1AUX_find_lab_cons) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[S2LP1AUX_concl_def] THEN
    CAKE_REWRITE_TAC[halt_view_def; OPTION_MAP_DEF; result_view_def] THEN
    MP_TAC(SPECL [`a':num`; `l:num`; `cs:num list`] S2LP1AUX_find_lab_cons) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[S2LP1AUX_concl_def] THEN
    CAKE_REWRITE_TAC[halt_view_def; OPTION_MAP_DEF; result_view_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[S2LP1AUX_concl_def] THEN
    CAKE_REWRITE_TAC[halt_view_def; OPTION_MAP_DEF; result_view_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[S2LP1AUX_concl_def] THEN
    CAKE_REWRITE_TAC[halt_view_def; OPTION_MAP_DEF; result_view_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* the body of a Loop continues the loop when the clock is 0 (local helper) *)
let S2LP1AUX_concl_loop_timeout = prove
 (`!res (s1:(A,C,FFI)stack_state) (t1:(A,C,FFI)lab_state) t2 ck len len' n l cs bs.
     stack_cont_loop res /\ stack_state_clock s1 = 0 /\
     S2LP1AUX_concl res s1 t1 t2 ck len n (CONS l cs) (CONS (l + 1) bs)
     ==> S2LP1AUX_concl (SOME stack_TimeOut) (stack_empty_env s1) t1 t2 ck len' n cs bs`,
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `res:((A)stack_result)option` (cases "option")) THEN
  REWRITE_TAC[stack_cont_loop_def] THENL
   [ALL_TAC;
    STRUCT_CASES_TAC(ISPEC `a:(A)stack_result` (cases "stack_result")) THEN
    REWRITE_TAC[stack_cont_loop_def]] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[S2LP1AUX_concl_def] THEN
  CAKE_REWRITE_TAC[halt_view_def; OPTION_MAP_DEF; result_view_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP S2LP1AUX_rel_basic) THEN
  ASM_REWRITE_TAC[stack_empty_env_def] THEN SIMP[]);;

(* the body of a Loop continues the loop: the Jump back is next (local     *)
(* helper) *)
let S2LP1AUX_concl_loop_cont = prove
 (`!res (s1:(A,C,FFI)stack_state) (t1:(A,C,FFI)lab_state) t2 ck len n l cs bs.
     stack_cont_loop res /\
     S2LP1AUX_concl res s1 t1 t2 ck len n (CONS l cs) (CONS (l + 1) bs) /\
     asm_fetch_aux (lab_state_pc t1 + len) (lab_state_code t1) =
       SOME (LabAsm (lab_Jump (lab_Lab n l)) (word 0) [] 0)
     ==> stack_to_labProof_state_rel s1 t2 /\
         asm_fetch_aux (lab_state_pc t2) (lab_state_code t2) =
           SOME (LabAsm (lab_Jump (lab_Lab n l)) (word 0) [] 0) /\
         (!ck1. lab_evaluate (lab_state_clock_fupd (combin_K ((lab_state_clock t1 + ck) + ck1)) t1) =
                lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock t2 + ck1)) t2)) /\
         lab_state_len_reg t2 = lab_state_len_reg t1 /\
         lab_state_ptr_reg t2 = lab_state_ptr_reg t1 /\
         lab_state_len2_reg t2 = lab_state_len2_reg t1 /\
         lab_state_ptr2_reg t2 = lab_state_ptr2_reg t1 /\
         lab_state_link_reg t2 = lab_state_link_reg t1 /\
         lab_state_code t1 <<= lab_state_code t2`,
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `res:((A)stack_result)option` (cases "option")) THEN
  REWRITE_TAC[stack_cont_loop_def] THENL
   [ALL_TAC;
    STRUCT_CASES_TAC(ISPEC `a:(A)stack_result` (cases "stack_result")) THEN
    REWRITE_TAC[stack_cont_loop_def]] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[S2LP1AUX_concl_def] THEN
  CAKE_REWRITE_TAC[halt_view_def; OPTION_MAP_DEF; result_view_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[S2LP1AUX_find_lab_cons; stack_to_labProof_code_installed_def;
                              is_Label_def]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC asm_fetch_aux_SOME_isPREFIX THEN
  EXISTS_TAC `lab_state_code (t1:(A,C,FFI)lab_state)` THEN ASM_REWRITE_TAC[]);;

(* lab_dec_clock changes only the clock (local helpers) *)
let S2LP1AUX_dec_clock_simps = prove
 (`!(t:(A,C,FFI)lab_state).
     lab_state_pc (lab_dec_clock t) = lab_state_pc t /\
     lab_state_code (lab_dec_clock t) = lab_state_code t /\
     lab_state_clock (lab_dec_clock t) = lab_state_clock t - 1 /\
     lab_state_regs (lab_dec_clock t) = lab_state_regs t /\
     lab_state_len_reg (lab_dec_clock t) = lab_state_len_reg t /\
     lab_state_ptr_reg (lab_dec_clock t) = lab_state_ptr_reg t /\
     lab_state_len2_reg (lab_dec_clock t) = lab_state_len2_reg t /\
     lab_state_ptr2_reg (lab_dec_clock t) = lab_state_ptr2_reg t /\
     lab_state_link_reg (lab_dec_clock t) = lab_state_link_reg t /\
     lab_state_ffi (lab_dec_clock t) = lab_state_ffi t`,
  REWRITE_TAC[lab_dec_clock_def] THEN SIMP[]);;

let S2LP1AUX_clock_fupd_dec = prove
 (`!c p (t:(A,C,FFI)lab_state).
     lab_state_clock_fupd (combin_K c) (lab_upd_pc p (lab_dec_clock t)) =
     lab_state_clock_fupd (combin_K c) (lab_upd_pc p t)`,
  REWRITE_TAC[lab_state_component_equality; lab_upd_pc_def; lab_dec_clock_def] THEN SIMP[]);;

(* a run to the Jump back to the start of a Loop, the Jump, and the run of *)
(* the Loop again (local helper) *)
let S2LP1AUX_concl_loop_back = prove
 (`!r (s2:(A,C,FFI)stack_state) (t1:(A,C,FFI)lab_state) t2 t4 ck ck' len n l w b k cs bs.
     (!ck1. lab_evaluate (lab_state_clock_fupd (combin_K ((lab_state_clock t1 + ck) + ck1)) t1) =
            lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock t2 + ck1)) t2)) /\
     lab_state_len_reg t2 = lab_state_len_reg t1 /\
     lab_state_ptr_reg t2 = lab_state_ptr_reg t1 /\
     lab_state_len2_reg t2 = lab_state_len2_reg t1 /\
     lab_state_ptr2_reg t2 = lab_state_ptr2_reg t1 /\
     lab_state_link_reg t2 = lab_state_link_reg t1 /\
     lab_state_code t1 <<= lab_state_code t2 /\
     ~(lab_state_clock t2 = 0) /\
     asm_fetch_aux (lab_state_pc t2) (lab_state_code t2) =
       SOME (LabAsm (lab_Jump (lab_Lab n l)) w b k) /\
     loc_to_pc n l (lab_state_code t2) = SOME (lab_state_pc t1) /\
     S2LP1AUX_concl r s2 (lab_upd_pc (lab_state_pc t1) (lab_dec_clock t2)) t4 ck' len n cs bs
     ==> S2LP1AUX_concl r s2 t1 t4 (ck + ck') len n cs bs`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC S2LP1AUX_concl_seq_gen THEN
  EXISTS_TAC `lab_upd_pc (lab_state_pc (t1:(A,C,FFI)lab_state))
               (lab_dec_clock (t2:(A,C,FFI)lab_state))` THEN
  EXISTS_TAC `len:num` THEN
  ASM_REWRITE_TAC[S2LP1AUX_upd_pc_simps; S2LP1AUX_dec_clock_simps] THEN
  GEN_TAC THEN
  SUBGOAL_THEN `lab_state_clock (t2:(A,C,FFI)lab_state) + ck1 =
                ((lab_state_clock t2 - 1) + ck1) + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  IMP_RES_TAC S2LP1AUX_eval_jump THEN ASM_REWRITE_TAC[S2LP1AUX_clock_fupd_dec]);;

(* case Loop (HOL4 lines 1818-1913) *)
let S2LP1AUX_fc_loop = prove
 (`!c1 (s:(A,C,FFI)stack_state).
     S2LP1AUX_fc c1 s /\
     (!res s1. stack_evaluate (c1,s) = (res,s1) /\ stack_cont_loop res /\
               ~(stack_state_clock s1 = 0)
               ==> S2LP1AUX_fc (stack_STOP (stack_Loop c1)) (stack_dec_clock s1))
     ==> S2LP1AUX_fc (stack_Loop c1) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[S2LP1AUX_fc_alt; stack_STOP_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[call_args_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ci0") ASSUME_TAC))))) THEN
  SUBGOAL_THEN `?xs nr m. stack_to_lab_flatten F (c1:(A)stack_prog) n (l + 2) (CONS l cs)
                            (CONS (l + 1) bs) = (xs,nr,m)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `stack_to_lab_flatten t (stack_Loop (c1:(A)stack_prog)) n l cs bs =
      (misc_Append (misc_Append (misc_List [lab_Label n l 0]) xs)
         (misc_List [LabAsm (lab_Jump (lab_Lab n l)) (word 0) [] 0; lab_Label n (l + 1) 0]),
       F, m)` (LABEL_TAC "fl") THENL
   [GEN_REWRITE_TAC LAND_CONV [stack_to_lab_flatten_def] THEN
    CAKE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "ci0" (fun ci -> USE_THEN "fl" (fun fl -> MP_TAC(REWRITE_RULE[fl] ci))) THEN
  REWRITE_TAC S2LP1AUX_IF_RWS THEN CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "fl" (fun fl -> REWRITE_TAC[fl]) THEN REWRITE_TAC S2LP1AUX_IF_RWS THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN CAKE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT S2LP1AUX_PAIRARG_TAC THEN
  DISCH_THEN(LABEL_TAC "ev") THEN
  SUBGOAL_THEN `~(res = SOME (stack_Error:(A)stack_result))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN REMOVE_THEN "ev" MP_TAC THEN
    REWRITE_TAC[stack_cont_loop_def; stack_exit_loop_def; PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`F`; `res:((A)stack_result)option`;
    `s1:(A,C,FFI)stack_state`; `n:num`; `l + 2`; `CONS (l:num) cs`; `CONS (l + 1) bs`;
    `t1:(A,C,FFI)lab_state`]) THEN
  ASM_REWRITE_TAC[FST] THEN
  ANTS_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[ALL_APPEND; ALL; IS_SOME_DEF] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[IS_SOME_DEF];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(A,C,FFI)lab_state` ASSUME_TAC)) THEN
  REMOVE_THEN "ev" MP_TAC THEN
  ASM_CASES_TAC `stack_cont_loop (res:((A)stack_result)option)` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `stack_state_clock (s1:(A,C,FFI)stack_state) = 0` THEN
    ASM_REWRITE_TAC[PAIR_EQ] THENL
     [STRIP_TAC THEN RVEQ_TAC THEN
      MAP_EVERY EXISTS_TAC [`ck:num`; `t2:(A,C,FFI)lab_state`] THEN
      MATCH_MP_TAC S2LP1AUX_concl_loop_timeout THEN
      MAP_EVERY EXISTS_TAC [`res:((A)stack_result)option`;
        `LENGTH (FILTER ((~) o is_Label) (append (xs:((A)line)app_list)))`; `l:num`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[stack_STOP_def] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`res:((A)stack_result)option`; `s1:(A,C,FFI)stack_state`;
      `t1:(A,C,FFI)lab_state`; `t2:(A,C,FFI)lab_state`; `ck:num`;
      `LENGTH (FILTER ((~) o is_Label) (append (xs:((A)line)app_list)))`; `n:num`; `l:num`;
      `cs:num list`; `bs:num list`] S2LP1AUX_concl_loop_cont) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`res:((A)stack_result)option`;
      `s1:(A,C,FFI)stack_state`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`t:bool`; `r:((A)stack_result)option`;
      `s2:(A,C,FFI)stack_state`; `n:num`; `l:num`; `cs:num list`; `bs:num list`;
      `lab_upd_pc (lab_state_pc (t1:(A,C,FFI)lab_state))
         (lab_dec_clock (t2:(A,C,FFI)lab_state))`]) THEN
    ASM_REWRITE_TAC[S2LP1AUX_upd_pc_simps; S2LP1AUX_dec_clock_simps] THEN
    REWRITE_TAC[call_args_def] THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC state_rel_with_pc THEN
        MATCH_MP_TAC stack_to_labProof_state_rel_dec_clock THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC code_installed_isPREFIX THEN
        EXISTS_TAC `lab_state_code (t1:(A,C,FFI)lab_state)` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "ci0" (fun ci -> USE_THEN "fl" (fun fl -> ACCEPT_TAC(REWRITE_RULE[fl; FST] ci)));
        MATCH_MP_TAC every_is_some_loc_to_pc_prefix THEN
        EXISTS_TAC `lab_state_code (t1:(A,C,FFI)lab_state)` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ck':num` (X_CHOOSE_THEN `t4:(A,C,FFI)lab_state`
      (ASSUME_TAC o REWRITE_RULE S2LP1AUX_IF_RWS))) THEN
    MAP_EVERY EXISTS_TAC [`ck + ck':num`; `t4:(A,C,FFI)lab_state`] THEN
    MATCH_MP_TAC S2LP1AUX_concl_loop_back THEN
    MAP_EVERY EXISTS_TAC [`t2:(A,C,FFI)lab_state`; `l:num`; `word 0:A word`; `[]:byte list`;
      `0`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP S2LP1AUX_rel_basic o
        check (fun th -> concl th = `stack_to_labProof_state_rel (s1:(A,C,FFI)stack_state) t2`)) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC loc_to_pc_isPREFIX THEN
      EXISTS_TAC `lab_state_code (t1:(A,C,FFI)lab_state)` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`ck:num`; `t2:(A,C,FFI)lab_state`] THEN
    MATCH_MP_TAC S2LP1AUX_concl_exit_loop THEN
    MAP_EVERY EXISTS_TAC
      [`LENGTH (FILTER ((~) o is_Label) (append (xs:((A)line)app_list)))`; `l:num`] THEN
    ASM_REWRITE_TAC[ADD_ASSOC]]);;

(* a jump not taken at the end of the code (the state of the result taken  *)
(* from the goal) *)
let S2LP1AUX_FALL_END_TAC : tactic = fun (asl,w as g) ->
  let sst = el 1 (snd (strip_comb (snd (strip_exists w)))) in
  let p1 = `lab_state_pc (t1:(A,C,FFI)lab_state) + 1` in
  (SUBGOAL_THEN (subst [S2LP1AUX_upd_tm p1,`tt:(A,C,FFI)lab_state`;
                        sst,`ss:(A,C,FFI)stack_state`]
     `S2LP1AUX_concl NONE (ss:(A,C,FFI)stack_state) tt tt 0 0 n cs bs`) ASSUME_TAC THENL
   [MATCH_MP_TAC S2LP1AUX_concl_refl THEN MATCH_MP_TAC state_rel_with_pc THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   POP_ASSUM(S2LP1AUX_IF_FINISH_TAC S2LP1AUX_eval_jumpcmp_F p1 S2LP1AUX_IF_ARITH_TAC)) g;;

(* the code of the stack state is installed in the code of the lab state  *)
(* (local helper) *)
let S2LP1AUX_rel_code = prove
 (`!(s:(A,C,FFI)stack_state) t n prog.
     stack_to_labProof_state_rel s t /\ lookup n (stack_state_code s) = SOME prog
     ==> call_args prog (lab_state_ptr_reg t) (lab_state_len_reg t) (lab_state_ptr2_reg t)
           (lab_state_len2_reg t) (lab_state_link_reg t) /\
         ?pc. stack_to_labProof_code_installed pc
                (append (FST (stack_to_lab_flatten T prog n (next_lab prog 2) [] [])))
                (lab_state_code t) /\
              loc_to_pc n 0 (lab_state_code t) = SOME pc`,
  REWRITE_TAC[stack_to_labProof_state_rel_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `prog:(A)stack_prog`]) THEN ASM_REWRITE_TAC[]);;

(* the conclusion for a result that is not a bad function return does not *)
(* depend on the code length, the section name and the label lists        *)
(* (local helper) *)
let S2LP1AUX_concl_view_indep = prove
 (`!r (s2:(A,C,FFI)stack_state) (t1:(A,C,FFI)lab_state) t2 ck len len' n n' cs cs' bs bs'.
     ~stack_bad_fun_return r
     ==> (S2LP1AUX_concl r s2 t1 t2 ck len n cs bs <=>
          S2LP1AUX_concl r s2 t1 t2 ck len' n' cs' bs')`,
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:((A)stack_result)option` (cases "option")) THEN
  REWRITE_TAC[stack_bad_fun_return_def] THEN
  STRUCT_CASES_TAC(ISPEC `a:(A)stack_result` (cases "stack_result")) THEN
  REWRITE_TAC[stack_bad_fun_return_def] THEN
  REWRITE_TAC[S2LP1AUX_concl_def] THEN CAKE_REWRITE_TAC[halt_view_def; OPTION_MAP_DEF] THEN
  TRY(CASES_ON `a':(A)word_loc`) THEN CAKE_REWRITE_TAC[result_view_def]);;

(* a step with a tick of the clock to the pc p, then a run from there      *)
(* (local helper) *)
let S2LP1AUX_concl_tick_jump = prove
 (`!r (s2:(A,C,FFI)stack_state) (t1:(A,C,FFI)lab_state) t4 ck' p len2 len n cs bs.
     ~(lab_state_clock t1 = 0) /\
     (!ck. lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t1) =
           lab_evaluate (lab_state_clock_fupd (combin_K ck) (lab_upd_pc p t1))) /\
     (r = NONE ==> p + len2 = lab_state_pc t1 + len) /\
     S2LP1AUX_concl r s2 (lab_upd_pc p (lab_dec_clock t1)) t4 ck' len2 n cs bs
     ==> S2LP1AUX_concl r s2 t1 t4 ck' len n cs bs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:((A)stack_result)option`; `s2:(A,C,FFI)stack_state`;
    `t1:(A,C,FFI)lab_state`; `lab_upd_pc p (lab_dec_clock (t1:(A,C,FFI)lab_state))`;
    `t4:(A,C,FFI)lab_state`; `0`; `ck':num`; `len2:num`; `len:num`; `n:num`;
    `cs:num list`; `bs:num list`] S2LP1AUX_concl_seq_gen) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[S2LP1AUX_upd_pc_simps; S2LP1AUX_dec_clock_simps; IS_PREFIX_REFL] THEN
  GEN_TAC THEN
  SUBGOAL_THEN `lab_state_clock (t1:(A,C,FFI)lab_state) + ck1 =
                ((lab_state_clock t1 - 1) + ck1) + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[S2LP1AUX_clock_fupd_dec]);;

(* the clock is 0 at a call (local helper) *)
let S2LP1AUX_concl_timeout_here = prove
 (`!(s:(A,C,FFI)stack_state) (t1:(A,C,FFI)lab_state) len n cs bs.
     stack_to_labProof_state_rel s t1 /\ stack_state_clock s = 0
     ==> S2LP1AUX_concl (SOME stack_TimeOut) (stack_empty_env s) t1 t1 0 len n cs bs`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP S2LP1AUX_rel_basic) THEN
  REWRITE_TAC[S2LP1AUX_concl_def] THEN
  CAKE_REWRITE_TAC[halt_view_def; OPTION_MAP_DEF; result_view_def] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; IS_PREFIX_REFL; stack_empty_env_def] THEN SIMP[]);;

(* case JumpLower (HOL4 lines 1914-1966) *)
let S2LP1AUX_fc_jumplower = prove
 (`!r1 r2 dest (s:(A,C,FFI)stack_state).
     (!x y prog. stack_get_var r1 s = SOME (wl_Word x) /\ stack_get_var r2 s = SOME (wl_Word y) /\
                 asm_word_cmp Lower x y /\
                 stack_find_code (INL dest) (stack_state_regs s) (stack_state_code s) = SOME prog /\
                 ~(stack_state_clock s = 0)
                 ==> S2LP1AUX_fc prog (stack_dec_clock s))
     ==> S2LP1AUX_fc (JumpLower r1 r2 dest) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[S2LP1AUX_fc_alt] THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN
  CAKE_REWRITE_TAC[call_args_def] THEN REWRITE_TAC S2LP1AUX_IF_RWS THEN
  ASM_CASES_TAC `?x y. stack_get_var r1 (s:(A,C,FFI)stack_state) = SOME (wl_Word x) /\
                       stack_get_var r2 s = SOME (wl_Word y)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `x:A word` (X_CHOOSE_THEN `y:A word` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN STRIP_TAC;
    STRIP_TAC THEN REPEAT S2LP1AUX_ASM_CASE_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
    REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
    RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
    ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN `wl_word_cmp Lower (lab_state_regs (t1:(A,C,FFI)lab_state) r1)
                  (lab_reg_imm (Reg r2) t1) = SOME (asm_word_cmp Lower (x:A word) y)` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN
    IMP_RES_TAC S2LP1AUX_rel_regs THEN
    ASM_REWRITE_TAC[lab_reg_imm_def; wl_word_cmp_def; asm_word_cmp_def];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  ASM_CASES_TAC `asm_word_cmp Lower (x:A word) y` THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  UNDISCH_TAC `wl_word_cmp Lower (lab_state_regs (t1:(A,C,FFI)lab_state) r1)
                 (lab_reg_imm (Reg r2) t1) = SOME (asm_word_cmp Lower (x:A word) y)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [ALL_TAC; STRIP_TAC THEN RVEQ_TAC THEN S2LP1AUX_FALL_END_TAC] THEN
  REWRITE_TAC[stack_find_code_def] THEN
  ASM_CASES_TAC `lookup dest (stack_state_code (s:(A,C,FFI)stack_state)) = NONE` THENL
   [ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `lookup dest (stack_state_code (s:(A,C,FFI)stack_state))` (cases "option")) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `prog:(A)stack_prog` ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `stack_state_clock (s:(A,C,FFI)stack_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`0`; `t1:(A,C,FFI)lab_state`] THEN
    MATCH_MP_TAC S2LP1AUX_concl_timeout_here THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `stack_evaluate (prog,stack_dec_clock (s:(A,C,FFI)stack_state))`
           PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:((A)stack_result)option`
    (X_CHOOSE_THEN `s3:(A,C,FFI)stack_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `stack_bad_fun_return (res:((A)stack_result)option)` THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC(ISPECL [`s:(A,C,FFI)stack_state`; `t1:(A,C,FFI)lab_state`; `dest:num`;
    `prog:(A)stack_prog`] S2LP1AUX_rel_code) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `pc':num` STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`x:A word`; `y:A word`; `prog:(A)stack_prog`]) THEN
  ASM_REWRITE_TAC[stack_find_code_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`T`; `r:((A)stack_result)option`; `s2:(A,C,FFI)stack_state`;
    `dest:num`; `next_lab (prog:(A)stack_prog) 2`; `[]:num list`; `[]:num list`;
    `lab_upd_pc pc' (lab_dec_clock (t1:(A,C,FFI)lab_state))`]) THEN
  ASM_REWRITE_TAC[S2LP1AUX_upd_pc_simps; S2LP1AUX_dec_clock_simps; APPEND; ALL; IS_SOME_DEF] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC state_rel_with_pc THEN
    MATCH_MP_TAC stack_to_labProof_state_rel_dec_clock THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(A,C,FFI)lab_state` ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `t2:(A,C,FFI)lab_state`] THEN
  MATCH_MP_TAC S2LP1AUX_concl_tick_jump THEN
  MAP_EVERY EXISTS_TAC [`pc':num`; `LENGTH (FILTER ((~) o is_Label)
    (append (FST (stack_to_lab_flatten T prog dest (next_lab (prog:(A)stack_prog) 2) [] []))))`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP S2LP1AUX_rel_basic) THEN ASM_REWRITE_TAC[];
    IMP_RES_TAC S2LP1AUX_eval_jumpcmp_T THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_bad_fun_return_def]) THEN FIRST_ASSUM CONTR_TAC;
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "S2LP1AUX_concl" with Failure _ -> false)) THEN
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC S2LP1AUX_concl_view_indep THEN ASM_REWRITE_TAC[]]);;

(* case RawCall (HOL4 lines 1967-2027) *)
let S2LP1AUX_fc_rawcall = prove
 (`!dest (s:(A,C,FFI)stack_state).
     (!prog x body. lookup dest (stack_state_code s) = SOME prog /\
                    stack_dest_Seq prog = SOME (x,body) /\ ~(stack_state_clock s = 0)
                    ==> S2LP1AUX_fc body (stack_dec_clock s))
     ==> S2LP1AUX_fc (RawCall dest) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[S2LP1AUX_fc_alt] THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN
  CAKE_REWRITE_TAC[call_args_def] THEN REWRITE_TAC S2LP1AUX_IF_RWS THEN
  ASM_CASES_TAC `lookup dest (stack_state_code (s:(A,C,FFI)stack_state)) = NONE` THENL
   [ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `lookup dest (stack_state_code (s:(A,C,FFI)stack_state))` (cases "option")) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `prog:(A)stack_prog` ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `stack_dest_Seq (prog:(A)stack_prog) = NONE` THENL
   [ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `stack_dest_Seq (prog:(A)stack_prog)` (cases "option")) THEN
  ASM_REWRITE_TAC[EXISTS_PAIR_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:(A)stack_prog` (X_CHOOSE_THEN `body:(A)stack_prog`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `stack_state_clock (s:(A,C,FFI)stack_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`0`; `t1:(A,C,FFI)lab_state`] THEN
    MATCH_MP_TAC S2LP1AUX_concl_timeout_here THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `stack_evaluate (body,stack_dec_clock (s:(A,C,FFI)stack_state))`
           PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:((A)stack_result)option`
    (X_CHOOSE_THEN `s3:(A,C,FFI)stack_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `stack_bad_fun_return (res:((A)stack_result)option)` THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[STACKPROPSAUX_dest_Seq_SOME] o
    check (fun th -> concl th = `stack_dest_Seq (prog:(A)stack_prog) = SOME (p1,body)`)) THEN
  MP_TAC(ISPECL [`s:(A,C,FFI)stack_state`; `t1:(A,C,FFI)lab_state`; `dest:num`;
    `stack_Seq p1 body:(A)stack_prog`] S2LP1AUX_rel_code) THEN
  ASM_REWRITE_TAC[call_args_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (X_CHOOSE_THEN `pc:num` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?xs nr1 m7. stack_to_lab_flatten F (p1:(A)stack_prog) dest
                  (next_lab (stack_Seq p1 body) 2) [] [] = (xs,nr1,m7)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `?ys nr2 m8. stack_to_lab_flatten F (body:(A)stack_prog) dest m7 [] [] =
                  (ys,nr2,m8)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `stack_to_lab_flatten T (stack_Seq p1 body:(A)stack_prog) dest
                  (next_lab (stack_Seq p1 body) 2) [] [] =
                (misc_Append (misc_Append xs (misc_List [lab_Label dest 1 0])) ys,
                 (nr1 \/ nr2), m8)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [stack_to_lab_flatten_def] THEN
    CAKE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun fl -> FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[fl] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "stack_to_labProof_code_installed"
    with Failure _ -> false))) THEN
  REWRITE_TAC S2LP1AUX_IF_RWS THEN CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN
  S2LP1AUX_WITH_LOC `1` (fun p ->
  REMOVE_THEN "ih" (MP_TAC o SPECL [`stack_Seq p1 body:(A)stack_prog`; `p1:(A)stack_prog`;
    `body:(A)stack_prog`]) THEN
  ASM_REWRITE_TAC[stack_dest_Seq_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`F`; `r:((A)stack_result)option`; `s2:(A,C,FFI)stack_state`;
    `dest:num`; `m7:num`; `[]:num list`; `[]:num list`;
    subst [p,`pp:num`] `lab_upd_pc pp (lab_dec_clock (t1:(A,C,FFI)lab_state))`]) THEN
  ASM_REWRITE_TAC[FST; S2LP1AUX_upd_pc_simps; S2LP1AUX_dec_clock_simps; APPEND; ALL;
                  IS_SOME_DEF] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC state_rel_with_pc THEN
    MATCH_MP_TAC stack_to_labProof_state_rel_dec_clock THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(A,C,FFI)lab_state` ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `t2:(A,C,FFI)lab_state`] THEN
  MATCH_MP_TAC S2LP1AUX_concl_tick_jump THEN
  MAP_EVERY EXISTS_TAC [p; `LENGTH (FILTER ((~) o is_Label) (append (ys:((A)line)app_list)))`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP S2LP1AUX_rel_basic) THEN ASM_REWRITE_TAC[];
    IMP_RES_TAC S2LP1AUX_eval_jump THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_bad_fun_return_def]) THEN FIRST_ASSUM CONTR_TAC;
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "S2LP1AUX_concl" with Failure _ -> false)) THEN
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC S2LP1AUX_concl_view_indep THEN ASM_REWRITE_TAC[]]));;

(* a run of the lab semantics from t1 with ck more clock ticks to t2 (local *)
(* definition of flatten_correct), and its properties *)
let S2LP1AUX_run_def = new_definition
 `S2LP1AUX_run (t1:(A,C,FFI)lab_state) t2 ck <=>
    !ck1. lab_evaluate (lab_state_clock_fupd (combin_K ((lab_state_clock t1 + ck) + ck1)) t1) =
          lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock t2 + ck1)) t2)`;;

let S2LP1AUX_run_trans = prove
 (`!(t1:(A,C,FFI)lab_state) t2 t3 ck ck'.
     S2LP1AUX_run t1 t2 ck /\ S2LP1AUX_run t2 t3 ck' ==> S2LP1AUX_run t1 t3 (ck + ck')`,
  REWRITE_TAC[S2LP1AUX_run_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `(c + ck + ck') + ck1 = (c + ck) + (ck' + ck1)`] THEN
  ASM_REWRITE_TAC[ADD_ASSOC]);;

let S2LP1AUX_run_step = prove
 (`!(t1:(A,C,FFI)lab_state) t1'.
     (!ck. lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t1) =
           lab_evaluate (lab_state_clock_fupd (combin_K ck) t1')) /\
     lab_state_clock t1' = lab_state_clock t1
     ==> S2LP1AUX_run t1 t1' 1`,
  REWRITE_TAC[S2LP1AUX_run_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `(c + 1) + ck1 = (c + ck1) + 1`]);;

let S2LP1AUX_run_tick = prove
 (`!(t1:(A,C,FFI)lab_state) p.
     ~(lab_state_clock t1 = 0) /\
     (!ck. lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t1) =
           lab_evaluate (lab_state_clock_fupd (combin_K ck) (lab_upd_pc p t1)))
     ==> S2LP1AUX_run t1 (lab_upd_pc p (lab_dec_clock t1)) 0`,
  REWRITE_TAC[S2LP1AUX_run_def; ADD_CLAUSES; S2LP1AUX_upd_pc_simps;
              S2LP1AUX_dec_clock_simps] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lab_state_clock (t1:(A,C,FFI)lab_state) + ck1 =
                ((lab_state_clock t1 - 1) + ck1) + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[S2LP1AUX_clock_fupd_dec]);;

let S2LP1AUX_concl_seq_run = prove
 (`!r (s2:(A,C,FFI)stack_state) (t1:(A,C,FFI)lab_state) t2 t3 ck ck' len2 len n cs bs.
     S2LP1AUX_run t1 t2 ck /\
     lab_state_len_reg t2 = lab_state_len_reg t1 /\
     lab_state_ptr_reg t2 = lab_state_ptr_reg t1 /\
     lab_state_len2_reg t2 = lab_state_len2_reg t1 /\
     lab_state_ptr2_reg t2 = lab_state_ptr2_reg t1 /\
     lab_state_link_reg t2 = lab_state_link_reg t1 /\
     lab_state_code t1 <<= lab_state_code t2 /\
     (r = NONE ==> lab_state_pc t2 + len2 = lab_state_pc t1 + len) /\
     S2LP1AUX_concl r s2 t2 t3 ck' len2 n cs bs
     ==> S2LP1AUX_concl r s2 t1 t3 (ck + ck') len n cs bs`,
  REWRITE_TAC[S2LP1AUX_run_def; S2LP1AUX_concl_seq_gen]);;

(* the result of a call returns to the label (a1,a2) (local helper) *)
let S2LP1AUX_concl_vloc = prove
 (`!res (s2:(A,C,FFI)stack_state) (tb:(A,C,FFI)lab_state) t2 ck len nn a1 a2 q.
     (res = stack_Result (wl_Loc a1 a2) \/ res = stack_Exception (wl_Loc a1 a2)) /\
     S2LP1AUX_concl (SOME res) s2 tb t2 ck len nn [] [] /\
     loc_to_pc a1 a2 (lab_state_code tb) = SOME q
     ==> S2LP1AUX_run tb t2 ck /\
         lab_state_len_reg t2 = lab_state_len_reg tb /\
         lab_state_ptr_reg t2 = lab_state_ptr_reg tb /\
         lab_state_len2_reg t2 = lab_state_len2_reg tb /\
         lab_state_ptr2_reg t2 = lab_state_ptr2_reg tb /\
         lab_state_link_reg t2 = lab_state_link_reg tb /\
         lab_state_code tb <<= lab_state_code t2 /\
         lab_state_pc t2 = q /\ stack_to_labProof_state_rel s2 t2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[S2LP1AUX_concl_def; S2LP1AUX_run_def] THEN
  CAKE_REWRITE_TAC[halt_view_def; OPTION_MAP_DEF; result_view_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q:num`) THEN
  (ANTS_TAC THENL
    [MATCH_MP_TAC loc_to_pc_isPREFIX THEN
     EXISTS_TAC `lab_state_code (tb:(A,C,FFI)lab_state)` THEN ASM_REWRITE_TAC[];
     SIMP_TAC[]]));;

(* find_code of a register (local helper) *)
let S2LP1AUX_find_code_INR = prove
 (`!r (regs:(num,(A)word_loc)fmap) (code:(B)spt) p.
     stack_find_code (INR r) regs code = SOME p <=>
     ?loc. FLOOKUP regs r = SOME (wl_Loc loc 0) /\ lookup loc code = SOME p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_find_code_def] THEN
  MP_TAC(ISPEC `FLOOKUP (regs:(num,(A)word_loc)fmap) r` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN CAKE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `a:(A)word_loc` (cases "word_loc")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[distinctness "word_loc"; injectivity "word_loc"; option_DISTINCT] THEN
  CAKE_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN MESON_TAC[]);;

(* the callee of a call is installed (local helper) *)
let S2LP1AUX_find_code_rel = prove
 (`!(s:(A,C,FFI)stack_state) t dest prog sregs (rf:num->(A)word_loc).
     stack_to_labProof_state_rel s t /\
     stack_find_code dest sregs (stack_state_code s) = SOME prog /\
     (!r v. FLOOKUP sregs r = SOME v ==> rf r = v)
     ==> call_args prog (lab_state_ptr_reg t) (lab_state_len_reg t) (lab_state_ptr2_reg t)
           (lab_state_len2_reg t) (lab_state_link_reg t) /\
         lookup (dest_to_loc' rf dest) (stack_state_code s) = SOME prog /\
         (!r. dest = INR r ==> ?p. rf r = wl_Loc p 0) /\
         ?pc. stack_to_labProof_code_installed pc
                (append (FST (stack_to_lab_flatten T prog (dest_to_loc' rf dest)
                                (next_lab prog 2) [] [])))
                (lab_state_code t) /\
              loc_to_pc (dest_to_loc' rf dest) 0 (lab_state_code t) = SOME pc`,
  REPEAT GEN_TAC THEN CASES_ON `dest:num+num` THEN
  REWRITE_TAC[dest_to_loc'_def; distinctness "sum"; injectivity "sum"] THEN
  CAKE_REWRITE_TAC[] THENL
   [REWRITE_TAC[stack_find_code_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC S2LP1AUX_rel_code THEN EXISTS_TAC `s:(A,C,FFI)stack_state` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[S2LP1AUX_find_code_INR] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(rf:num->(A)word_loc) a = wl_Loc loc 0` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!r. a = r ==> ?p. (rf:num->(A)word_loc) r = wl_Loc p 0`
      (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN EXISTS_TAC `loc:num` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC S2LP1AUX_rel_code THEN
    EXISTS_TAC `s:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[]]);;

(* one step of the jump to a callee (local helper) *)
let S2LP1AUX_eval_compile_jump = prove
 (`!(t1:(A,C,FFI)lab_state) dest p ck.
     asm_fetch_aux (lab_state_pc t1) (lab_state_code t1) = SOME (compile_jump dest) /\
     loc_to_pc (dest_to_loc' (lab_state_regs t1) dest) 0 (lab_state_code t1) = SOME p /\
     (!r. dest = INR r ==> ?l. lab_state_regs t1 r = wl_Loc l 0)
     ==> lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t1) =
         lab_evaluate (lab_state_clock_fupd (combin_K ck) (lab_upd_pc p t1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lab_state_pc (t1:(A,C,FFI)lab_state)`; `lab_state_code (t1:(A,C,FFI)lab_state)`;
    `dest:num+num`; `lab_state_regs (t1:(A,C,FFI)lab_state)`; `p:num`;
    `lab_state_clock_fupd (combin_K (ck + 1)) (t1:(A,C,FFI)lab_state)`] compile_jump_correct) THEN
  SIMP[ADD_EQ_0; ARITH_EQ] THEN DISCH_THEN(K ALL_TAC) THEN AP_TERM_TAC THEN
  REWRITE_TAC[lab_state_component_equality; lab_upd_pc_def; lab_dec_clock_def] THEN
  SIMP[ADD_SUB]);;

(* case Call without a return (HOL4 lines 2046-2128) *)
let S2LP1AUX_fc_call_none = prove
 (`!dest handler (s:(A,C,FFI)stack_state).
     (!prog. stack_find_code dest (stack_state_regs s) (stack_state_code s) = SOME prog /\
             handler = NONE /\ ~(stack_state_clock s = 0)
             ==> S2LP1AUX_fc prog (stack_dec_clock s))
     ==> S2LP1AUX_fc (stack_Call NONE dest handler) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[S2LP1AUX_fc_alt] THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN
  CAKE_REWRITE_TAC[call_args_def] THEN
  REWRITE_TAC(not_is_Label_compile_jump :: S2LP1AUX_IF_RWS) THEN
  ASM_CASES_TAC `stack_find_code dest (stack_state_regs (s:(A,C,FFI)stack_state))
                   (stack_state_code s) = NONE` THENL
   [ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `stack_find_code dest (stack_state_regs (s:(A,C,FFI)stack_state))
                  (stack_state_code s)` (cases "option")) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `prog:(A)stack_prog` ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `handler:((A)stack_prog#num#num)option = NONE` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC] THEN
  ASM_CASES_TAC `stack_state_clock (s:(A,C,FFI)stack_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`0`; `t1:(A,C,FFI)lab_state`] THEN
    MATCH_MP_TAC S2LP1AUX_concl_timeout_here THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `stack_evaluate (prog,stack_dec_clock (s:(A,C,FFI)stack_state))`
           PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:((A)stack_result)option`
    (X_CHOOSE_THEN `s3:(A,C,FFI)stack_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `stack_bad_fun_return (res:((A)stack_result)option)` THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  MP_TAC(ISPECL [`s:(A,C,FFI)stack_state`; `t1:(A,C,FFI)lab_state`; `dest:num+num`;
    `prog:(A)stack_prog`; `stack_state_regs (s:(A,C,FFI)stack_state)`;
    `lab_state_regs (t1:(A,C,FFI)lab_state)`] S2LP1AUX_find_code_rel) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC S2LP1AUX_rel_regs THEN
    EXISTS_TAC `s:(A,C,FFI)stack_state` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `pc':num` STRIP_ASSUME_TAC)))) THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `prog:(A)stack_prog`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`T`; `r:((A)stack_result)option`; `s2:(A,C,FFI)stack_state`;
    `dest_to_loc' (lab_state_regs (t1:(A,C,FFI)lab_state)) dest`;
    `next_lab (prog:(A)stack_prog) 2`; `[]:num list`; `[]:num list`;
    `lab_upd_pc pc' (lab_dec_clock (t1:(A,C,FFI)lab_state))`]) THEN
  ASM_REWRITE_TAC[S2LP1AUX_upd_pc_simps; S2LP1AUX_dec_clock_simps; APPEND; ALL; IS_SOME_DEF] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC state_rel_with_pc THEN
    MATCH_MP_TAC stack_to_labProof_state_rel_dec_clock THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(A,C,FFI)lab_state` ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`ck:num`; `t2:(A,C,FFI)lab_state`] THEN
  MATCH_MP_TAC S2LP1AUX_concl_tick_jump THEN
  MAP_EVERY EXISTS_TAC [`pc':num`; `LENGTH (FILTER ((~) o is_Label)
    (append (FST (stack_to_lab_flatten T prog
       (dest_to_loc' (lab_state_regs (t1:(A,C,FFI)lab_state)) dest)
       (next_lab (prog:(A)stack_prog) 2) [] []))))`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP S2LP1AUX_rel_basic) THEN ASM_REWRITE_TAC[];
    IMP_RES_TAC S2LP1AUX_eval_compile_jump THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[stack_bad_fun_return_def]) THEN FIRST_ASSUM CONTR_TAC;
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "S2LP1AUX_concl" with Failure _ -> false)) THEN
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC S2LP1AUX_concl_view_indep THEN ASM_REWRITE_TAC[]]);;

(* lab_upd_reg changes only the registers (local helper) *)
let S2LP1AUX_upd_reg_simps = prove
 (`!r v (t:(A,C,FFI)lab_state).
     lab_state_pc (lab_upd_reg r v t) = lab_state_pc t /\
     lab_state_code (lab_upd_reg r v t) = lab_state_code t /\
     lab_state_clock (lab_upd_reg r v t) = lab_state_clock t /\
     lab_state_regs (lab_upd_reg r v t) = (r =+ v) (lab_state_regs t) /\
     lab_state_len_reg (lab_upd_reg r v t) = lab_state_len_reg t /\
     lab_state_ptr_reg (lab_upd_reg r v t) = lab_state_ptr_reg t /\
     lab_state_len2_reg (lab_upd_reg r v t) = lab_state_len2_reg t /\
     lab_state_ptr2_reg (lab_upd_reg r v t) = lab_state_ptr2_reg t /\
     lab_state_link_reg (lab_upd_reg r v t) = lab_state_link_reg t /\
     lab_state_ffi (lab_upd_reg r v t) = lab_state_ffi t`,
  REWRITE_TAC[lab_upd_reg_def] THEN SIMP[]);;

(* the entry into the callee of a call with a return: the LocValue of the  *)
(* return label and the jump (local helper) *)
let S2LP1AUX_call_entry = prove
 (`!(s:(A,C,FFI)stack_state) (t1:(A,C,FFI)lab_state) lr l1 l2 dest prog.
     stack_to_labProof_state_rel s t1 /\ ~(stack_state_clock s = 0) /\
     stack_find_code dest (stack_state_regs s \\ lr) (stack_state_code s) = SOME prog /\
     asm_fetch_aux (lab_state_pc t1) (lab_state_code t1) =
       SOME (LabAsm (lab_LocValue lr (lab_Lab l1 l2)) (word 0) [] 0) /\
     asm_fetch_aux (lab_state_pc t1 + 1) (lab_state_code t1) = SOME (compile_jump dest) /\
     loc_to_pc l1 l2 (lab_state_code t1) = SOME (lab_state_pc t1 + 2)
     ==> ?tb. S2LP1AUX_run t1 tb 1 /\
              lab_state_len_reg tb = lab_state_len_reg t1 /\
              lab_state_ptr_reg tb = lab_state_ptr_reg t1 /\
              lab_state_len2_reg tb = lab_state_len2_reg t1 /\
              lab_state_ptr2_reg tb = lab_state_ptr2_reg t1 /\
              lab_state_link_reg tb = lab_state_link_reg t1 /\
              lab_state_code tb = lab_state_code t1 /\
              stack_to_labProof_state_rel
                (stack_dec_clock (stack_set_var lr (wl_Loc l1 l2) s)) tb /\
              call_args prog (lab_state_ptr_reg t1) (lab_state_len_reg t1)
                (lab_state_ptr2_reg t1) (lab_state_len2_reg t1) (lab_state_link_reg t1) /\
              stack_to_labProof_code_installed (lab_state_pc tb)
                (append (FST (stack_to_lab_flatten T prog
                                (dest_to_loc' (lab_state_regs tb) dest)
                                (next_lab prog 2) [] [])))
                (lab_state_code t1) /\
              loc_to_pc (dest_to_loc' (lab_state_regs tb) dest) 0 (lab_state_code t1) =
                SOME (lab_state_pc tb)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `ta = inc_pc (lab_upd_reg lr (wl_Loc l1 l2) (t1:(A,C,FFI)lab_state))` THEN
  SUBGOAL_THEN
   `lab_state_pc (ta:(A,C,FFI)lab_state) = lab_state_pc (t1:(A,C,FFI)lab_state) + 1 /\
    lab_state_code ta = lab_state_code t1 /\
    lab_state_clock ta = lab_state_clock t1 /\
    lab_state_len_reg ta = lab_state_len_reg t1 /\
    lab_state_ptr_reg ta = lab_state_ptr_reg t1 /\
    lab_state_len2_reg ta = lab_state_len2_reg t1 /\
    lab_state_ptr2_reg ta = lab_state_ptr2_reg t1 /\
    lab_state_link_reg ta = lab_state_link_reg t1`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ta" THEN
    REWRITE_TAC[S2LP1AUX_inc_pc_upd; S2LP1AUX_upd_pc_simps; S2LP1AUX_upd_reg_simps];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(A,C,FFI)stack_state`; `t1:(A,C,FFI)lab_state`; `dest:num+num`;
    `prog:(A)stack_prog`; `stack_state_regs (s:(A,C,FFI)stack_state) \\ lr`;
    `lab_state_regs (ta:(A,C,FFI)lab_state)`] S2LP1AUX_find_code_rel) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `lab_state_regs (ta:(A,C,FFI)lab_state) =
                  (lr =+ wl_Loc l1 l2) (lab_state_regs (t1:(A,C,FFI)lab_state))`
      SUBST1_TAC THENL
     [EXPAND_TAC "ta" THEN
      REWRITE_TAC[S2LP1AUX_inc_pc_upd; S2LP1AUX_upd_pc_simps; S2LP1AUX_upd_reg_simps];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[DOMSUB_FLOOKUP_THM; APPLY_UPDATE_THM] THEN
    REPEAT GEN_TAC THEN ASM_CASES_TAC `lr:num = r` THEN
    ASM_REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
    MATCH_MP_TAC S2LP1AUX_rel_regs THEN EXISTS_TAC `s:(A,C,FFI)stack_state` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `pc':num` STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `lab_upd_pc pc' (lab_dec_clock (ta:(A,C,FFI)lab_state))` THEN
  ASM_REWRITE_TAC[S2LP1AUX_upd_pc_simps; S2LP1AUX_dec_clock_simps] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `1 = 1 + 0` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC S2LP1AUX_run_trans THEN EXISTS_TAC `ta:(A,C,FFI)lab_state` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC S2LP1AUX_run_step THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "ta" THEN
      GEN_TAC THEN MATCH_MP_TAC S2LP1AUX_eval_locvalue THEN
      MAP_EVERY EXISTS_TAC [`word 0:A word`; `[]:byte list`; `0`;
        `lab_state_pc (t1:(A,C,FFI)lab_state) + 2`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC S2LP1AUX_run_tick THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP S2LP1AUX_rel_basic) THEN
      ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC S2LP1AUX_eval_compile_jump THEN
      EXISTS_TAC `dest:num+num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC state_rel_with_pc THEN
  MATCH_MP_TAC stack_to_labProof_state_rel_dec_clock THEN
  EXPAND_TAC "ta" THEN REWRITE_TAC[S2LP1AUX_inc_pc_upd; S2LP1AUX_upd_reg_simps] THEN
  MATCH_MP_TAC state_rel_with_pc THEN MATCH_MP_TAC set_var_upd_reg THEN
  ASM_REWRITE_TAC[]);;

(* the rewrites of the code of a call (local helper) *)
let S2LP1AUX_CALL_RWS = not_is_Label_compile_jump :: S2LP1AUX_IF_RWS;;

(* the evaluation of a call with a return, up to the run of the callee   *)
(* (local tactic of flatten_correct) *)
let S2LP1AUX_CALL_ENTER_TAC : tactic =
  let is_fc t = try fst(dest_const t) = "stack_find_code" with Failure _ -> false in
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term is_fc) (lhs (concl th)))) THEN
  ASM_CASES_TAC `stack_find_code dest (stack_state_regs (s:(A,C,FFI)stack_state) \\ lr)
                   (stack_state_code s) = NONE` THENL
   [ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `stack_find_code dest (stack_state_regs (s:(A,C,FFI)stack_state) \\ lr)
                  (stack_state_code s)` (cases "option")) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `prog:(A)stack_prog` ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `stack_state_clock (s:(A,C,FFI)stack_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`0`; `t1:(A,C,FFI)lab_state`] THEN
    MATCH_MP_TAC S2LP1AUX_concl_timeout_here THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `stack_evaluate (prog,stack_dec_clock (stack_set_var lr (wl_Loc l1 l2)
                  (s:(A,C,FFI)stack_state)))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:((A)stack_result)option`
    (X_CHOOSE_THEN `s3:(A,C,FFI)stack_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ev") THEN
  SUBGOAL_THEN `~(res = SOME (stack_Error:(A)stack_result))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN REMOVE_THEN "ev" MP_TAC THEN
    CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(A,C,FFI)stack_state`; `t1:(A,C,FFI)lab_state`; `lr:num`; `l1:num`;
    `l2:num`; `dest:num+num`; `prog:(A)stack_prog`] S2LP1AUX_call_entry) THEN
  ASM_REWRITE_TAC[ARITH_RULE `(p + 1) + 1 = p + 2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `tb:(A,C,FFI)lab_state` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "ih1" (MP_TAC o SPEC `prog:(A)stack_prog`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`T`; `res:((A)stack_result)option`; `s3:(A,C,FFI)stack_state`;
    `dest_to_loc' (lab_state_regs (tb:(A,C,FFI)lab_state)) dest`;
    `next_lab (prog:(A)stack_prog) 2`; `[]:num list`; `[]:num list`;
    `tb:(A,C,FFI)lab_state`]) THEN
  ASM_REWRITE_TAC[APPEND; ALL; IS_SOME_DEF] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `t2:(A,C,FFI)lab_state` ASSUME_TAC));;

(* split the result res of the callee into its constructors (the argument *)
(* named x) *)
let S2LP1AUX_RES_CASES_TAC : tactic =
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `a:(A)stack_result` SUBST_ALL_TAC)
    (ISPEC `res:((A)stack_result)option` (cases "option")) THENL
   [CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `a:(A)stack_result` (cases "stack_result")) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (fun th ->
    if is_exists (concl th) then
      let v = fst(dest_exists(concl th)) in
      X_CHOOSE_THEN (mk_var("x",type_of v)) SUBST_ALL_TAC th
    else SUBST_ALL_TAC th)) THEN
  CAKE_REWRITE_TAC[];;

(* a result that ends the call (local tactic) *)
let S2LP1AUX_CALL_ERR_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;;

(* a result of the callee that is the result of the call (local tactic) *)
let S2LP1AUX_CALL_PASS_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  S2LP1AUX_CONCL_ASSUM(fun th ->
    let args = snd(strip_comb(concl th)) in
    let t2 = el 3 args and ck = el 4 args in
    EXISTS_TAC (mk_binop `(+):num->num->num` `1` ck) THEN EXISTS_TAC t2 THEN
    MATCH_MP_TAC S2LP1AUX_concl_seq_run THEN
    EXISTS_TAC `tb:(A,C,FFI)lab_state` THEN EXISTS_TAC (el 5 args) THEN
    ASM_REWRITE_TAC[IS_PREFIX_REFL; option_DISTINCT] THEN
    MP_TAC th THEN MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC S2LP1AUX_concl_view_indep THEN
    REWRITE_TAC[stack_bad_fun_return_def]);;

(* the result of the callee returns to the label (a1,a2) at pc q *)
let S2LP1AUX_VLOC_TAC (a1:term) (a2:term) (q:term) : tactic =
  S2LP1AUX_CONCL_ASSUM(fun th ->
    let args = snd(strip_comb(concl th)) in
    let res = rand (el 0 args) in
    MP_TAC(ISPECL [res; el 1 args; el 2 args; el 3 args; el 4 args; el 5 args; el 6 args;
                   a1; a2; q] S2LP1AUX_concl_vloc) THEN
    ASM_REWRITE_TAC[th] THEN STRIP_TAC);;

(* case Call with a return (HOL4 lines 2129-2416) *)
let S2LP1AUX_fc_call_some = prove
 (`!ret_handler lr l1 l2 dest handler (s:(A,C,FFI)stack_state).
     (!prog. stack_find_code dest (stack_state_regs s \\ lr) (stack_state_code s) = SOME prog /\
             ~(stack_state_clock s = 0)
             ==> S2LP1AUX_fc prog (stack_dec_clock (stack_set_var lr (wl_Loc l1 l2) s))) /\
     (!prog s2. stack_find_code dest (stack_state_regs s \\ lr) (stack_state_code s) = SOME prog /\
                ~(stack_state_clock s = 0) /\
                stack_evaluate (prog,stack_dec_clock (stack_set_var lr (wl_Loc l1 l2) s)) =
                  (SOME (stack_Result (wl_Loc l1 l2)),s2)
                ==> S2LP1AUX_fc ret_handler s2) /\
     (!prog k1 k2 h s2. stack_find_code dest (stack_state_regs s \\ lr) (stack_state_code s) =
                          SOME prog /\
                        ~(stack_state_clock s = 0) /\
                        stack_evaluate (prog,stack_dec_clock (stack_set_var lr (wl_Loc l1 l2) s)) =
                          (SOME (stack_Exception (wl_Loc k1 k2)),s2) /\
                        handler = SOME (h,k1,k2)
                        ==> S2LP1AUX_fc h s2)
     ==> S2LP1AUX_fc (stack_Call (SOME (ret_handler,lr,l1,l2)) dest handler) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[S2LP1AUX_fc_alt] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1")
     (CONJUNCTS_THEN2 (LABEL_TAC "ih2") (LABEL_TAC "ih3"))) THEN
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC[stack_evaluate_def] THEN CAKE_REWRITE_TAC[call_args_def] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `?xs nr1 m1. stack_to_lab_flatten F (ret_handler:(A)stack_prog) n l cs bs =
                   (xs,nr1,m1)` STRIP_ASSUME_TAC THENL
    [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_CASES_TAC `handler:((A)stack_prog#num#num)option = NONE` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `stack_to_lab_flatten t (stack_Call (SOME (ret_handler,lr,l1,l2)) dest NONE)
                     n l cs bs =
                   (misc_Append (misc_List [LabAsm (lab_LocValue lr (lab_Lab l1 l2)) (word 0) [] 0;
                       compile_jump dest; lab_Label l1 l2 0]) (xs:((A)line)app_list), nr1, m1)`
       ASSUME_TAC THENL
      [GEN_REWRITE_TAC LAND_CONV [stack_to_lab_flatten_def] THEN
       CAKE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[];
       ALL_TAC] THEN
    FIRST_X_ASSUM(fun fl -> FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[fl] o check (fun th ->
     try fst(dest_const(fst(strip_comb(concl th)))) = "stack_to_labProof_code_installed"
     with Failure _ -> false)) THEN REWRITE_TAC[fl]) THEN
   REWRITE_TAC S2LP1AUX_CALL_RWS THEN CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN
   FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
     concl th = `lr = lab_state_link_reg (t1:(A,C,FFI)lab_state)`)) THEN
    S2LP1AUX_CALL_ENTER_TAC THEN REMOVE_THEN "ev" MP_TAC THEN S2LP1AUX_RES_CASES_TAC THENL
     [ASM_CASES_TAC `x:(A)word_loc = wl_Loc l1 l2` THEN ASM_REWRITE_TAC[] THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN DISCH_TAC THEN
     S2LP1AUX_VLOC_TAC `l1:num` `l2:num` `(lab_state_pc (t1:(A,C,FFI)lab_state) + 1) + 1` THEN
     REMOVE_THEN "ih2" (MP_TAC o SPECL [`prog:(A)stack_prog`; `s3:(A,C,FFI)stack_state`]) THEN
     ASM_REWRITE_TAC[] THEN
     DISCH_THEN(MP_TAC o SPECL [`F`; `r:((A)stack_result)option`; `s2:(A,C,FFI)stack_state`;
       `n:num`; `l:num`; `cs:num list`; `bs:num list`; `t2:(A,C,FFI)lab_state`]) THEN
     ASM_REWRITE_TAC[FST] THEN
     ANTS_TAC THENL
      [CONJ_TAC THENL
        [MATCH_MP_TAC code_installed_isPREFIX THEN
         EXISTS_TAC `lab_state_code (t1:(A,C,FFI)lab_state)` THEN ASM_MESON_TAC[];
         MATCH_MP_TAC every_is_some_loc_to_pc_prefix THEN
         EXISTS_TAC `lab_state_code (t1:(A,C,FFI)lab_state)` THEN ASM_MESON_TAC[]];
       ALL_TAC] THEN
     DISCH_THEN(X_CHOOSE_THEN `ck':num` (X_CHOOSE_THEN `t3:(A,C,FFI)lab_state` ASSUME_TAC)) THEN
     MAP_EVERY EXISTS_TAC [`(1 + ck) + ck':num`; `t3:(A,C,FFI)lab_state`] THEN
     MATCH_MP_TAC S2LP1AUX_concl_seq_run THEN
     MAP_EVERY EXISTS_TAC [`t2:(A,C,FFI)lab_state`;
       `LENGTH (FILTER ((~) o is_Label) (append (xs:((A)line)app_list)))`] THEN
     ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
     TRY(MATCH_MP_TAC S2LP1AUX_run_trans THEN EXISTS_TAC `tb:(A,C,FFI)lab_state` THEN
         ASM_REWRITE_TAC[] THEN NO_TAC) THEN
     TRY(DISCH_TAC THEN ARITH_TAC) THEN
     ASM_MESON_TAC[];
     S2LP1AUX_CALL_ERR_TAC];
      S2LP1AUX_CALL_PASS_TAC; S2LP1AUX_CALL_ERR_TAC; S2LP1AUX_CALL_ERR_TAC;
      S2LP1AUX_CALL_PASS_TAC; S2LP1AUX_CALL_PASS_TAC; S2LP1AUX_CALL_PASS_TAC;
      S2LP1AUX_CALL_ERR_TAC];
    SUBGOAL_THEN `?p2 k1 k2. handler = SOME (p2:(A)stack_prog,k1:num,k2:num)` STRIP_ASSUME_TAC THENL
    [MP_TAC(ISPEC `handler:((A)stack_prog#num#num)option` (cases "option")) THEN
     ASM_REWRITE_TAC[] THEN MESON_TAC[PAIR_SURJECTIVE];
     ALL_TAC] THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
   SUBGOAL_THEN `?ys nr2 m2. stack_to_lab_flatten F (p2:(A)stack_prog) n m1 cs bs = (ys,nr2,m2)`
     STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
   SUBGOAL_THEN `stack_to_lab_flatten t
                   (stack_Call (SOME (ret_handler,lr,l1,l2)) dest (SOME (p2,k1,k2))) n l cs bs =
                 (misc_Append
                    (misc_Append (misc_List [LabAsm (lab_LocValue lr (lab_Lab l1 l2)) (word 0) [] 0;
                       compile_jump dest; lab_Label l1 l2 0]) (xs:((A)line)app_list))
                    (misc_Append
                       (misc_Append
                          (misc_List [LabAsm (lab_Jump (lab_Lab n m2)) (word 0) [] 0;
                                      lab_Label k1 k2 0]) ys)
                       (misc_List [lab_Label n m2 0])), (nr1 /\ nr2), m2 + 1)`
     ASSUME_TAC THENL
    [GEN_REWRITE_TAC LAND_CONV [stack_to_lab_flatten_def] THEN
     CAKE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(fun fl -> FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[fl] o check (fun th ->
     try fst(dest_const(fst(strip_comb(concl th)))) = "stack_to_labProof_code_installed"
     with Failure _ -> false)) THEN REWRITE_TAC[fl]) THEN
   REWRITE_TAC S2LP1AUX_CALL_RWS THEN CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(CAKE_REWRITE_RULE[]) THEN
   FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
     concl th = `lr = lab_state_link_reg (t1:(A,C,FFI)lab_state)`)) THEN
    S2LP1AUX_CALL_ENTER_TAC THEN REMOVE_THEN "ev" MP_TAC THEN S2LP1AUX_RES_CASES_TAC THENL
     [ASM_CASES_TAC `x:(A)word_loc = wl_Loc l1 l2` THEN ASM_REWRITE_TAC[] THENL
    [ALL_TAC; S2LP1AUX_CALL_ERR_TAC] THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN DISCH_TAC THEN
   S2LP1AUX_VLOC_TAC `l1:num` `l2:num` `(lab_state_pc (t1:(A,C,FFI)lab_state) + 1) + 1` THEN
   REMOVE_THEN "ih2" (MP_TAC o SPECL [`prog:(A)stack_prog`; `s3:(A,C,FFI)stack_state`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`F`; `r:((A)stack_result)option`; `s2:(A,C,FFI)stack_state`;
     `n:num`; `l:num`; `cs:num list`; `bs:num list`; `t2:(A,C,FFI)lab_state`]) THEN
   ASM_REWRITE_TAC[FST] THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL
      [MATCH_MP_TAC code_installed_isPREFIX THEN
       EXISTS_TAC `lab_state_code (t1:(A,C,FFI)lab_state)` THEN ASM_MESON_TAC[];
       MATCH_MP_TAC every_is_some_loc_to_pc_prefix THEN
       EXISTS_TAC `lab_state_code (t1:(A,C,FFI)lab_state)` THEN ASM_MESON_TAC[]];
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `ck':num` (X_CHOOSE_THEN `t3:(A,C,FFI)lab_state` ASSUME_TAC)) THEN
ASM_CASES_TAC `r:((A)stack_result)option = NONE` THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN
     S2LP1AUX_WITH_LOC `m2:num` (fun pend ->
       let len' = `(LENGTH (FILTER ((~) o is_Label) (append (xs:((A)line)app_list))) + 1) +
                   LENGTH (FILTER ((~) o is_Label) (append (ys:((A)line)app_list)))` in
       SUBGOAL_THEN (subst [pend,`pe:num`; len',`le:num`]
         `S2LP1AUX_concl NONE (s2:(A,C,FFI)stack_state) t2 (lab_upd_pc pe t3) (ck' + 1) le
            n cs bs`) ASSUME_TAC THENL
        [MATCH_MP_TAC S2LP1AUX_concl_then_jump THEN
         MAP_EVERY EXISTS_TAC
          [`LENGTH (FILTER ((~) o is_Label) (append (xs:((A)line)app_list)))`;
           `((lab_state_pc (t1:(A,C,FFI)lab_state) + 1) + 1) +
            LENGTH (FILTER ((~) o is_Label) (append (xs:((A)line)app_list)))`;
           `n:num`; `m2:num`; `word 0:A word`; `[]:byte list`; `0`] THEN
         ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ARITH_TAC THEN
         TRY(MATCH_MP_TAC asm_fetch_aux_SOME_isPREFIX THEN
             EXISTS_TAC `lab_state_code (t1:(A,C,FFI)lab_state)` THEN ASM_REWRITE_TAC[] THEN
             NO_TAC) THEN
         MATCH_MP_TAC loc_to_pc_isPREFIX THEN
         EXISTS_TAC `lab_state_code (t1:(A,C,FFI)lab_state)` THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
       MAP_EVERY EXISTS_TAC [`(1 + ck) + (ck' + 1):num`;
         subst [pend,`pe:num`] `lab_upd_pc pe (t3:(A,C,FFI)lab_state)`] THEN
       MATCH_MP_TAC S2LP1AUX_concl_seq_run THEN
       MAP_EVERY EXISTS_TAC [`t2:(A,C,FFI)lab_state`; len'] THEN
       ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
       TRY(MATCH_MP_TAC S2LP1AUX_run_trans THEN EXISTS_TAC `tb:(A,C,FFI)lab_state` THEN
           ASM_REWRITE_TAC[] THEN NO_TAC) THEN
       ARITH_TAC);
     MAP_EVERY EXISTS_TAC [`(1 + ck) + ck':num`; `t3:(A,C,FFI)lab_state`] THEN
     MATCH_MP_TAC S2LP1AUX_concl_seq_run THEN
     MAP_EVERY EXISTS_TAC [`t2:(A,C,FFI)lab_state`;
       `LENGTH (FILTER ((~) o is_Label) (append (xs:((A)line)app_list)))`] THEN
     ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC S2LP1AUX_run_trans THEN EXISTS_TAC `tb:(A,C,FFI)lab_state` THEN
     ASM_REWRITE_TAC[]];
      ASM_CASES_TAC `x:(A)word_loc = wl_Loc k1 k2` THEN ASM_REWRITE_TAC[] THENL
    [ALL_TAC; S2LP1AUX_CALL_ERR_TAC] THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN DISCH_TAC THEN
   S2LP1AUX_VLOC_TAC `k1:num` `k2:num`
     `(((lab_state_pc (t1:(A,C,FFI)lab_state) + 1) + 1) +
       LENGTH (FILTER ((~) o is_Label) (append (xs:((A)line)app_list)))) + 1` THEN
   REMOVE_THEN "ih3" (MP_TAC o SPECL [`prog:(A)stack_prog`; `k1:num`; `k2:num`;
     `p2:(A)stack_prog`; `s3:(A,C,FFI)stack_state`]) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`F`; `r:((A)stack_result)option`; `s2:(A,C,FFI)stack_state`;
     `n:num`; `m1:num`; `cs:num list`; `bs:num list`; `t2:(A,C,FFI)lab_state`]) THEN
   ASM_REWRITE_TAC[FST] THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL
      [MATCH_MP_TAC code_installed_isPREFIX THEN
       EXISTS_TAC `lab_state_code (t1:(A,C,FFI)lab_state)` THEN ASM_MESON_TAC[];
       MATCH_MP_TAC every_is_some_loc_to_pc_prefix THEN
       EXISTS_TAC `lab_state_code (t1:(A,C,FFI)lab_state)` THEN ASM_MESON_TAC[]];
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `ck':num` (X_CHOOSE_THEN `t3:(A,C,FFI)lab_state` ASSUME_TAC)) THEN
   MAP_EVERY EXISTS_TAC [`(1 + ck) + ck':num`; `t3:(A,C,FFI)lab_state`] THEN
   MATCH_MP_TAC S2LP1AUX_concl_seq_run THEN
   MAP_EVERY EXISTS_TAC [`t2:(A,C,FFI)lab_state`;
     `LENGTH (FILTER ((~) o is_Label) (append (ys:((A)line)app_list)))`] THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
   TRY(MATCH_MP_TAC S2LP1AUX_run_trans THEN EXISTS_TAC `tb:(A,C,FFI)lab_state` THEN
       ASM_REWRITE_TAC[] THEN NO_TAC) THEN
   DISCH_TAC THEN ARITH_TAC;
      S2LP1AUX_CALL_ERR_TAC; S2LP1AUX_CALL_ERR_TAC;
      S2LP1AUX_CALL_PASS_TAC; S2LP1AUX_CALL_PASS_TAC; S2LP1AUX_CALL_PASS_TAC;
      S2LP1AUX_CALL_ERR_TAC]]);;

(* case Call (HOL4 lines 2028-2416) *)
let S2LP1AUX_fc_call = prove
 (`!ret dest handler (s:(A,C,FFI)stack_state).
     (!ret_handler prog link_reg l1 l2.
        ret = SOME (ret_handler,link_reg,l1,l2) /\
        stack_find_code dest (stack_state_regs s \\ link_reg) (stack_state_code s) = SOME prog /\
        ~(stack_state_clock s = 0)
        ==> S2LP1AUX_fc prog (stack_dec_clock (stack_set_var link_reg (wl_Loc l1 l2) s))) /\
     (!prog link_reg x l1 l2 ret_handler s2.
        ret = SOME (ret_handler,link_reg,l1,l2) /\
        stack_find_code dest (stack_state_regs s \\ link_reg) (stack_state_code s) = SOME prog /\
        ~(stack_state_clock s = 0) /\
        stack_evaluate (prog,stack_dec_clock (stack_set_var link_reg (wl_Loc l1 l2) s)) =
          (SOME (stack_Result x),s2) /\
        x = wl_Loc l1 l2
        ==> S2LP1AUX_fc ret_handler s2) /\
     (!ret_handler prog link_reg l1 l2 x l1' l2' h s2.
        ret = SOME (ret_handler,link_reg,l1,l2) /\
        stack_find_code dest (stack_state_regs s \\ link_reg) (stack_state_code s) = SOME prog /\
        ~(stack_state_clock s = 0) /\
        stack_evaluate (prog,stack_dec_clock (stack_set_var link_reg (wl_Loc l1 l2) s)) =
          (SOME (stack_Exception x),s2) /\
        handler = SOME (h,l1',l2') /\ x = wl_Loc l1' l2'
        ==> S2LP1AUX_fc h s2) /\
     (!prog. ret = NONE /\
        stack_find_code dest (stack_state_regs s) (stack_state_code s) = SOME prog /\
        handler = NONE /\ ~(stack_state_clock s = 0)
        ==> S2LP1AUX_fc prog (stack_dec_clock s))
     ==> S2LP1AUX_fc (stack_Call ret dest handler) s`,
  GEN_TAC THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `rr:(A)stack_prog#num#num#num` SUBST1_TAC)
    (ISPEC `ret:((A)stack_prog#num#num#num)option` (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC S2LP1AUX_fc_call_none THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?rh lr l1 l2. rr = (rh:(A)stack_prog,lr:num,l1:num,l2:num)`
    (REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THENL
   [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c1") (CONJUNCTS_THEN2 (LABEL_TAC "c2")
    (LABEL_TAC "c3"))) THEN
  MATCH_MP_TAC S2LP1AUX_fc_call_some THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [USE_THEN "c1" (MATCH_MP_TAC o SPECL [`rh:(A)stack_prog`; `prog:(A)stack_prog`; `lr:num`;
      `l1:num`; `l2:num`]) THEN ASM_REWRITE_TAC[];
    USE_THEN "c2" (MATCH_MP_TAC o SPECL [`prog:(A)stack_prog`; `lr:num`;
      `wl_Loc l1 l2:(A)word_loc`; `l1:num`; `l2:num`; `rh:(A)stack_prog`;
      `s2:(A,C,FFI)stack_state`]) THEN ASM_REWRITE_TAC[];
    USE_THEN "c3" (MATCH_MP_TAC o SPECL [`rh:(A)stack_prog`; `prog:(A)stack_prog`; `lr:num`;
      `l1:num`; `l2:num`; `wl_Loc k1 k2:(A)word_loc`; `k1:num`; `k2:num`;
      `h:(A)stack_prog`; `s2:(A,C,FFI)stack_state`]) THEN ASM_REWRITE_TAC[]]);;

(* the CallFFI step (local helpers of flatten_correct) *)
let S2LP1AUX_eval_ffi_final = prove
 (`!(t:(A,C,FFI)lab_state) i w b k w1 w2 w3 w4 n1 n2 bytes bytes2 p outcome ck.
     asm_fetch_aux (lab_state_pc t) (lab_state_code t) = SOME (LabAsm (CallFFI i) w b k) /\
     lab_state_regs t (lab_state_len_reg t) = wl_Word w1 /\
     lab_state_regs t (lab_state_ptr_reg t) = wl_Word w2 /\
     lab_state_regs t (lab_state_len2_reg t) = wl_Word w3 /\
     lab_state_regs t (lab_state_ptr2_reg t) = wl_Word w4 /\
     lab_state_regs t (lab_state_link_reg t) = wl_Loc n1 n2 /\
     read_bytearray w2 (val w1) (mem_load_byte_aux (lab_state_mem t) (lab_state_mem_domain t)
       (lab_state_be t)) = SOME bytes /\
     read_bytearray w4 (val w3) (mem_load_byte_aux (lab_state_mem t) (lab_state_mem_domain t)
       (lab_state_be t)) = SOME bytes2 /\
     loc_to_pc n1 n2 (lab_state_code t) = SOME p /\
     call_FFI (lab_state_ffi t) (ExtCall i) bytes bytes2 = FFI_final outcome
     ==> lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t) =
         (target_Halt (FFI_outcome outcome),lab_state_clock_fupd (combin_K (ck + 1)) t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [lab_evaluate_def] THEN
  REWRITE_TAC[asm_fetch_def] THEN SIMP[ADD_EQ_0; ARITH_EQ] THEN CAKE_REWRITE_TAC[]);;

let S2LP1AUX_eval_ffi_return = prove
 (`!(t:(A,C,FFI)lab_state) i w b k w1 w2 w3 w4 n1 n2 bytes bytes2 p new_ffi new_bytes ck.
     asm_fetch_aux (lab_state_pc t) (lab_state_code t) = SOME (LabAsm (CallFFI i) w b k) /\
     lab_state_regs t (lab_state_len_reg t) = wl_Word w1 /\
     lab_state_regs t (lab_state_ptr_reg t) = wl_Word w2 /\
     lab_state_regs t (lab_state_len2_reg t) = wl_Word w3 /\
     lab_state_regs t (lab_state_ptr2_reg t) = wl_Word w4 /\
     lab_state_regs t (lab_state_link_reg t) = wl_Loc n1 n2 /\
     read_bytearray w2 (val w1) (mem_load_byte_aux (lab_state_mem t) (lab_state_mem_domain t)
       (lab_state_be t)) = SOME bytes /\
     read_bytearray w4 (val w3) (mem_load_byte_aux (lab_state_mem t) (lab_state_mem_domain t)
       (lab_state_be t)) = SOME bytes2 /\
     loc_to_pc n1 n2 (lab_state_code t) = SOME p /\
     call_FFI (lab_state_ffi t) (ExtCall i) bytes bytes2 = FFI_return new_ffi new_bytes
     ==> lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t) =
         lab_evaluate (lab_state_clock_fupd (combin_K ck)
           (lab_state_mem_fupd (combin_K (write_bytearray w4 new_bytes (lab_state_mem t)
                                     (lab_state_mem_domain t) (lab_state_be t)))
           (lab_state_ffi_fupd (combin_K new_ffi)
           (lab_state_io_regs_fupd (combin_K (shift_seq 1 (lab_state_io_regs t)))
           (lab_state_io_fp_regs_fupd (combin_K (shift_seq 1 (lab_state_io_fp_regs t)))
           (lab_state_regs_fupd
              (combin_K (\a. get_reg_value (lab_state_io_regs t 0 (ExtCall i) a)
                        (lab_state_regs t a) wl_Word))
           (lab_state_fp_regs_fupd (combin_K (\n. lab_state_io_fp_regs t 0 n))
           (lab_state_pc_fupd (combin_K p) t))))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [lab_evaluate_def] THEN
  REWRITE_TAC[asm_fetch_def] THEN SIMP[ADD_EQ_0; ARITH_EQ] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  AP_TERM_TAC THEN REWRITE_TAC[lab_state_component_equality] THEN SIMP[ADD_SUB]);;


(* the state relation after an FFI call that returns (local helper) *)
let S2LP1AUX_rel_ffi_return = prove
 (`!(s:(A,C,FFI)stack_state) t lr n1 n2 i p new_ffi new_bytes w4.
     stack_to_labProof_state_rel s t /\ lr = lab_state_link_reg t
     ==> stack_to_labProof_state_rel
           (stack_state_memory_fupd (combin_K (write_bytearray w4 new_bytes (stack_state_memory s)
                                         (stack_state_mdomain s) (stack_state_be s)))
           (stack_state_regs_fupd (combin_K (DRESTRICT (stack_state_regs s)
                                         (stack_state_ffi_save_regs s)))
           (stack_state_fp_regs_fupd (combin_K FEMPTY)
           (stack_state_ffi_fupd (combin_K new_ffi) s))))
           (lab_state_clock_fupd (combin_K (lab_state_clock t))
           (lab_state_mem_fupd (combin_K (write_bytearray w4 new_bytes (lab_state_mem (inc_pc (lab_upd_reg lr (wl_Loc n1 n2) (t:(A,C,FFI)lab_state))))
                                     (lab_state_mem_domain (inc_pc (lab_upd_reg lr (wl_Loc n1 n2) (t:(A,C,FFI)lab_state)))) (lab_state_be (inc_pc (lab_upd_reg lr (wl_Loc n1 n2) (t:(A,C,FFI)lab_state))))))
           (lab_state_ffi_fupd (combin_K new_ffi)
           (lab_state_io_regs_fupd (combin_K (shift_seq 1 (lab_state_io_regs (inc_pc (lab_upd_reg lr (wl_Loc n1 n2) (t:(A,C,FFI)lab_state))))))
           (lab_state_io_fp_regs_fupd (combin_K (shift_seq 1 (lab_state_io_fp_regs (inc_pc (lab_upd_reg lr (wl_Loc n1 n2) (t:(A,C,FFI)lab_state))))))
           (lab_state_regs_fupd
              (combin_K (\a. get_reg_value (lab_state_io_regs (inc_pc (lab_upd_reg lr (wl_Loc n1 n2) (t:(A,C,FFI)lab_state))) 0 (ExtCall i) a)
                        (lab_state_regs (inc_pc (lab_upd_reg lr (wl_Loc n1 n2) (t:(A,C,FFI)lab_state))) a) wl_Word))
           (lab_state_fp_regs_fupd (combin_K (\n. lab_state_io_fp_regs (inc_pc (lab_upd_reg lr (wl_Loc n1 n2) (t:(A,C,FFI)lab_state))) 0 n))
           (lab_state_pc_fupd (combin_K p) (inc_pc (lab_upd_reg lr (wl_Loc n1 n2) (t:(A,C,FFI)lab_state)))))))))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_to_labProof_state_rel_def; inc_pc_def; lab_upd_reg_def] THEN
   SIMP[FLOOKUP_DRESTRICT; FLOOKUP_EMPTY; shift_seq_def; APPLY_UPDATE_THM] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
    [REPEAT STRIP_TAC THEN REWRITE_TAC[get_reg_value_def] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
     ASM_MESON_TAC[]]);;

(* record update lemmas of the clock (local helpers) *)
let S2LP1AUX_clock_fupd_fupd = prove
 (`!a b (t:(A,C,FFI)lab_state).
     lab_state_clock_fupd (combin_K a) (lab_state_clock_fupd (combin_K b) t) = lab_state_clock_fupd (combin_K a) t`,
  REWRITE_TAC[lab_state_component_equality] THEN SIMP[]);;

let S2LP1AUX_clock_clock_fupd = prove
 (`!c (t:(A,C,FFI)lab_state). lab_state_clock (lab_state_clock_fupd (combin_K c) t) = c`,
  SIMP[]);;

(* the lab state after the LocValue of an FFI call, and after the call    *)
(* (local terms of the FFI case) *)
let S2LP1AUX_TA =
  `inc_pc (lab_upd_reg (lab_state_link_reg t1) (wl_Loc n l) (t1:(A,C,FFI)lab_state))`;;

let S2LP1AUX_TAFTER = subst [S2LP1AUX_TA,`ta:(A,C,FFI)lab_state`]
  `lab_state_mem_fupd (combin_K (write_bytearray (w4:A word) new_bytes
                            (lab_state_mem (ta:(A,C,FFI)lab_state))
                            (lab_state_mem_domain ta) (lab_state_be ta)))
   (lab_state_ffi_fupd (combin_K new_ffi)
   (lab_state_io_regs_fupd (combin_K (shift_seq 1 (lab_state_io_regs ta)))
   (lab_state_io_fp_regs_fupd (combin_K (shift_seq 1 (lab_state_io_fp_regs ta)))
   (lab_state_regs_fupd
      (combin_K (\a. get_reg_value (lab_state_io_regs ta 0 (ExtCall ffi_index) a)
                (lab_state_regs ta a) wl_Word))
   (lab_state_fp_regs_fupd (combin_K (\n. lab_state_io_fp_regs ta 0 n))
   (lab_state_pc_fupd (combin_K ((lab_state_pc (t1:(A,C,FFI)lab_state) + 1) + 1)) ta))))))`;;

(* case FFI (HOL4 lines 2653-2712) *)
let S2LP1AUX_fc_ffi = prove
 (`!ffi_index ptr len ptr2 len2 ret (s:(A,C,FFI)stack_state).
     S2LP1AUX_fc (stack_FFI ffi_index ptr len ptr2 len2 ret) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[S2LP1AUX_fc_alt] THEN REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC[stack_evaluate_def] THEN ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN
   CAKE_REWRITE_TAC[call_args_def] THEN REWRITE_TAC S2LP1AUX_IF_RWS THEN CAKE_REWRITE_TAC[] THEN
   STRIP_TAC THEN RVEQ_TAC THEN
  ASM_CASES_TAC `?w1 w2 w3 w4.
     stack_get_var (lab_state_len_reg t1) (s:(A,C,FFI)stack_state) = SOME (wl_Word w1) /\
     stack_get_var (lab_state_ptr_reg (t1:(A,C,FFI)lab_state)) s = SOME (wl_Word w2) /\
     stack_get_var (lab_state_len2_reg t1) s = SOME (wl_Word w3) /\
     stack_get_var (lab_state_ptr2_reg t1) s = SOME (wl_Word (w4:A word))` THENL
    [FIRST_X_ASSUM(X_CHOOSE_THEN `w1:A word` (X_CHOOSE_THEN `w2:A word`
       (X_CHOOSE_THEN `w3:A word` (X_CHOOSE_THEN `w4:A word` STRIP_ASSUME_TAC)))) THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_pair (rhs (concl th)) &&
       not (is_pair (lhs (concl th))))) THEN
     ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN DISCH_TAC;
     REPEAT S2LP1AUX_ASM_CASE_TAC THEN
     RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
     REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
     RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
     ASM_MESON_TAC[]] THEN
  ASM_CASES_TAC `?bytes bytes2.
     read_bytearray w2 (val (w1:A word)) (mem_load_byte_aux (stack_state_memory (s:(A,C,FFI)stack_state))
       (stack_state_mdomain s) (stack_state_be s)) = SOME bytes /\
     read_bytearray w4 (val (w3:A word)) (mem_load_byte_aux (stack_state_memory s)
       (stack_state_mdomain s) (stack_state_be s)) = SOME bytes2` THENL
    [FIRST_X_ASSUM(X_CHOOSE_THEN `bytes:byte list` (X_CHOOSE_THEN `bytes2:byte list`
       STRIP_ASSUME_TAC)) THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_pair (rhs (concl th)) &&
       not (is_pair (lhs (concl th))))) THEN
     ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[];
     REPEAT S2LP1AUX_ASM_CASE_TAC THEN
     RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
     REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
     RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
     ASM_MESON_TAC[]] THEN
  ABBREV_TAC `ta = inc_pc (lab_upd_reg (lab_state_link_reg t1) (wl_Loc n l)
                      (t1:(A,C,FFI)lab_state))` THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP S2LP1AUX_rel_basic) THEN
   SUBGOAL_THEN `lab_state_regs t1 (lab_state_len_reg t1) = wl_Word (w1:A word) /\
                 lab_state_regs t1 (lab_state_ptr_reg t1) = wl_Word w2 /\
                 lab_state_regs t1 (lab_state_len2_reg t1) = wl_Word w3 /\
                 lab_state_regs (t1:(A,C,FFI)lab_state) (lab_state_ptr2_reg t1) = wl_Word w4`
     STRIP_ASSUME_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN IMP_RES_TAC S2LP1AUX_rel_regs THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN
    `asm_fetch_aux (lab_state_pc ta) (lab_state_code ta) =
       SOME (LabAsm (CallFFI ffi_index) (word 0) [] 0) /\
     lab_state_regs ta (lab_state_len_reg ta) = wl_Word (w1:A word) /\
     lab_state_regs ta (lab_state_ptr_reg ta) = wl_Word w2 /\
     lab_state_regs ta (lab_state_len2_reg ta) = wl_Word w3 /\
     lab_state_regs ta (lab_state_ptr2_reg ta) = wl_Word w4 /\
     lab_state_regs ta (lab_state_link_reg ta) = wl_Loc n l /\
     read_bytearray w2 (val w1) (mem_load_byte_aux (lab_state_mem ta) (lab_state_mem_domain ta)
       (lab_state_be ta)) = SOME bytes /\
     read_bytearray w4 (val w3) (mem_load_byte_aux (lab_state_mem ta) (lab_state_mem_domain ta)
       (lab_state_be ta)) = SOME bytes2 /\
     loc_to_pc n l (lab_state_code ta) =
       SOME ((lab_state_pc (t1:(A,C,FFI)lab_state) + 1) + 1) /\
     lab_state_ffi (ta:(A,C,FFI)lab_state) = stack_state_ffi (s:(A,C,FFI)stack_state)`
     STRIP_ASSUME_TAC THENL
    [EXPAND_TAC "ta" THEN
     REWRITE_TAC[S2LP1AUX_inc_pc_upd; S2LP1AUX_upd_pc_simps; S2LP1AUX_upd_reg_simps;
                 APPLY_UPDATE_THM] THEN
     ASM_REWRITE_TAC[] THEN SIMP[lab_upd_reg_def];
     ALL_TAC] THEN
   SUBGOAL_THEN `!ck. lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t1) =
                      lab_evaluate (lab_state_clock_fupd (combin_K ck) (ta:(A,C,FFI)lab_state))`
     ASSUME_TAC THENL
    [EXPAND_TAC "ta" THEN GEN_TAC THEN MATCH_MP_TAC S2LP1AUX_eval_locvalue THEN
     MAP_EVERY EXISTS_TAC [`word 0:A word`; `[]:byte list`; `0`;
       `(lab_state_pc (t1:(A,C,FFI)lab_state) + 1) + 1`] THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
  DISJ_CASES_THEN2
     (X_CHOOSE_THEN `new_ffi:(FFI)ffi_state` (X_CHOOSE_THEN `new_bytes:byte list` ASSUME_TAC))
     (X_CHOOSE_THEN `outcome:final_event` ASSUME_TAC)
     (ISPEC `call_FFI (stack_state_ffi (s:(A,C,FFI)stack_state)) (ExtCall ffi_index) bytes bytes2`
        (cases "ffi_result")) THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN
   STRIP_TAC THEN RVEQ_TAC THENL
   [EXISTS_TAC `2` THEN
   EXISTS_TAC (subst [S2LP1AUX_TAFTER,`tt:(A,C,FFI)lab_state`]
     `lab_state_clock_fupd (combin_K (lab_state_clock (t1:(A,C,FFI)lab_state))) (tt:(A,C,FFI)lab_state)`) THEN
   REWRITE_TAC[S2LP1AUX_concl_none] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[S2LP1AUX_clock_fupd_fupd; S2LP1AUX_clock_clock_fupd] THEN
   REWRITE_TAC[ARITH_RULE `(c + 2) + ck1 = ((c + ck1) + 1) + 1`] THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC S2LP1AUX_eval_ffi_return THEN
   MAP_EVERY EXISTS_TAC [`word 0:A word`; `[]:byte list`; `0`; `w1:A word`; `w2:A word`;
     `w3:A word`; `n:num`; `l:num`; `bytes:byte list`; `bytes2:byte list`] THEN
   ASM_REWRITE_TAC[];
      SIMP_NOASM[inc_pc_def; lab_upd_reg_def];
      SIMP_NOASM[inc_pc_def; lab_upd_reg_def];
      SIMP_NOASM[inc_pc_def; lab_upd_reg_def];
      SIMP_NOASM[inc_pc_def; lab_upd_reg_def];
      SIMP_NOASM[inc_pc_def; lab_upd_reg_def];
      SIMP_NOASM[inc_pc_def; lab_upd_reg_def; IS_PREFIX_REFL];
      SIMP_NOASM[inc_pc_def; lab_upd_reg_def] THEN ARITH_TAC;
      MATCH_MP_TAC S2LP1AUX_rel_ffi_return THEN ASM_REWRITE_TAC[]];
    EXISTS_TAC `2` THEN
   EXISTS_TAC (subst [S2LP1AUX_TA,`tt:(A,C,FFI)lab_state`]
     `lab_state_clock_fupd (combin_K (lab_state_clock (t1:(A,C,FFI)lab_state) + 1)) (tt:(A,C,FFI)lab_state)`) THEN
   REWRITE_TAC[S2LP1AUX_concl_def] THEN CAKE_REWRITE_TAC[halt_view_def] THEN CONJ_TAC THENL
    [REWRITE_TAC[ARITH_RULE `c + 2 = (c + 1) + 1`] THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC S2LP1AUX_eval_ffi_final THEN
     MAP_EVERY EXISTS_TAC [`ffi_index:mlstring`; `word 0:A word`; `[]:byte list`; `0`;
       `w1:A word`; `w2:A word`; `w3:A word`; `w4:A word`; `n:num`; `l:num`; `bytes:byte list`; `bytes2:byte list`;
       `(lab_state_pc (t1:(A,C,FFI)lab_state) + 1) + 1`] THEN
     ASM_REWRITE_TAC[];
     SIMP_NOASM[inc_pc_def; lab_upd_reg_def] THEN ASM_REWRITE_TAC[]]]);;

(* the address of a shared memory access does not depend on the clock      *)
(* (local helper) *)
let S2LP1AUX_lab_addr_clock = prove
 (`!ad c (t:(A,C,FFI)lab_state).
     lab_addr ad (lab_state_clock_fupd (combin_K c) t) = lab_addr ad t`,
  MATCH_MP_TAC addr_INDUCT THEN REWRITE_TAC[lab_addr_def] THEN SIMP[]);;

(* the shared memory load and store steps (local helpers) *)
let S2LP1AUX_eval_shload_final = prove
 (`!(t:(A,C,FFI)lab_state) m r ad b k n v outcome ck.
     asm_fetch_aux (lab_state_pc t) (lab_state_code t) = SOME (Asm (ShareMem m r ad) b k) /\
     (!s:(A,C,FFI)lab_state. share_mem_op m r ad s = share_mem_load r ad s n) /\
     lab_addr ad t = SOME v /\
     (if n = 0 then val v MOD (dimindex(:A) DIV 8) = 0 /\ v IN lab_state_shared_mem_domain t
      else byte_align v IN lab_state_shared_mem_domain t) /\
     call_FFI (lab_state_ffi t) (SharedMem MappedRead) [word n] (word_to_bytes v F) =
       FFI_final outcome
     ==> lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t) =
         (target_Halt (FFI_outcome outcome),lab_state_clock_fupd (combin_K (ck + 1)) t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [lab_evaluate_def] THEN
  REWRITE_TAC[asm_fetch_def] THEN SIMP[ADD_EQ_0; ARITH_EQ] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[share_mem_load_def; S2LP1AUX_lab_addr_clock] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[] THEN CAKE_REWRITE_TAC[]);;

let S2LP1AUX_eval_shload_return = prove
 (`!(t:(A,C,FFI)lab_state) m r ad b k n v nf nb ck.
     asm_fetch_aux (lab_state_pc t) (lab_state_code t) = SOME (Asm (ShareMem m r ad) b k) /\
     (!s:(A,C,FFI)lab_state. share_mem_op m r ad s = share_mem_load r ad s n) /\
     lab_addr ad t = SOME v /\
     (if n = 0 then val v MOD (dimindex(:A) DIV 8) = 0 /\ v IN lab_state_shared_mem_domain t
      else byte_align v IN lab_state_shared_mem_domain t) /\
     call_FFI (lab_state_ffi t) (SharedMem MappedRead) [word n] (word_to_bytes v F) =
       FFI_return nf nb
     ==> lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t) =
         lab_evaluate (lab_state_clock_fupd (combin_K ck)
           (lab_state_io_regs_fupd (combin_K (shift_seq 1 (lab_state_io_regs t)))
           (lab_state_io_fp_regs_fupd (combin_K (shift_seq 1 (lab_state_io_fp_regs t)))
           (lab_state_ffi_fupd (combin_K nf)
           (lab_state_regs_fupd
              (combin_K ((r =+ wl_Word (word_of_bytes F (word 0) nb)) (lab_state_regs t)))
           (lab_state_pc_fupd (combin_K (lab_state_pc t + 1)) t))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [lab_evaluate_def] THEN
  REWRITE_TAC[asm_fetch_def] THEN SIMP[ADD_EQ_0; ARITH_EQ] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[share_mem_load_def; S2LP1AUX_lab_addr_clock] THEN CAKE_REWRITE_TAC[] THEN
  SIMP[] THEN CAKE_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN REWRITE_TAC[lab_state_component_equality] THEN SIMP[ADD_SUB]);;

let S2LP1AUX_eval_shstore_final = prove
 (`!(t:(A,C,FFI)lab_state) m r ad b k n v wv outcome ck.
     asm_fetch_aux (lab_state_pc t) (lab_state_code t) = SOME (Asm (ShareMem m r ad) b k) /\
     (!s:(A,C,FFI)lab_state. share_mem_op m r ad s = share_mem_store r ad s n) /\
     lab_state_regs t r = wl_Word wv /\
     lab_addr ad t = SOME v /\
     (if n = 0 then val v MOD (dimindex(:A) DIV 8) = 0 /\ v IN lab_state_shared_mem_domain t
      else byte_align v IN lab_state_shared_mem_domain t) /\
     call_FFI (lab_state_ffi t) (SharedMem MappedWrite) [word n]
       (APPEND (if n = 0 then word_to_bytes wv F else TAKE n (word_to_bytes wv F))
               (word_to_bytes v F)) = FFI_final outcome
     ==> lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t) =
         (target_Halt (FFI_outcome outcome),lab_state_clock_fupd (combin_K (ck + 1)) t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [lab_evaluate_def] THEN
  REWRITE_TAC[asm_fetch_def] THEN SIMP[ADD_EQ_0; ARITH_EQ] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[share_mem_store_def; S2LP1AUX_lab_addr_clock] THEN SIMP[] THEN
  CAKE_REWRITE_TAC[] THEN SIMP[] THEN CAKE_REWRITE_TAC[]);;

let S2LP1AUX_eval_shstore_return = prove
 (`!(t:(A,C,FFI)lab_state) m r ad b k n v wv nf nb ck.
     asm_fetch_aux (lab_state_pc t) (lab_state_code t) = SOME (Asm (ShareMem m r ad) b k) /\
     (!s:(A,C,FFI)lab_state. share_mem_op m r ad s = share_mem_store r ad s n) /\
     lab_state_regs t r = wl_Word wv /\
     lab_addr ad t = SOME v /\
     (if n = 0 then val v MOD (dimindex(:A) DIV 8) = 0 /\ v IN lab_state_shared_mem_domain t
      else byte_align v IN lab_state_shared_mem_domain t) /\
     call_FFI (lab_state_ffi t) (SharedMem MappedWrite) [word n]
       (APPEND (if n = 0 then word_to_bytes wv F else TAKE n (word_to_bytes wv F))
               (word_to_bytes v F)) = FFI_return nf nb
     ==> lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t) =
         lab_evaluate (lab_state_clock_fupd (combin_K ck)
           (lab_state_io_regs_fupd (combin_K (shift_seq 1 (lab_state_io_regs t)))
           (lab_state_io_fp_regs_fupd (combin_K (shift_seq 1 (lab_state_io_fp_regs t)))
           (lab_state_ffi_fupd (combin_K nf)
           (lab_state_pc_fupd (combin_K (lab_state_pc t + 1)) t)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [lab_evaluate_def] THEN
  REWRITE_TAC[asm_fetch_def] THEN SIMP[ADD_EQ_0; ARITH_EQ] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[share_mem_store_def; S2LP1AUX_lab_addr_clock] THEN SIMP[] THEN
  CAKE_REWRITE_TAC[] THEN SIMP[] THEN CAKE_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[lab_state_component_equality; inc_pc_def; lab_dec_clock_def] THEN
  SIMP[ADD_SUB]);;

(* a step with a tick of the clock to t' (local helper) *)
let S2LP1AUX_run_tick_gen = prove
 (`!(t1:(A,C,FFI)lab_state) t'.
     ~(lab_state_clock t1 = 0) /\
     (!ck. lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t1) =
           lab_evaluate (lab_state_clock_fupd (combin_K ck) t'))
     ==> S2LP1AUX_run t1 (lab_state_clock_fupd (combin_K (lab_state_clock t1 - 1)) t') 0`,
  REWRITE_TAC[S2LP1AUX_run_def; ADD_CLAUSES; S2LP1AUX_clock_fupd_fupd;
              S2LP1AUX_clock_clock_fupd] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lab_state_clock (t1:(A,C,FFI)lab_state) + ck1 =
                ((lab_state_clock t1 - 1) + ck1) + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

(* the address of ShMemOp (local helper) *)
let S2LP1AUX_word_exp_add = prove
 (`!(s:(A,C,FFI)stack_state) a w v.
     stack_word_exp s (wl_Op asm_Add [wl_Var a; wl_Const w]) = SOME v <=>
     ?x. FLOOKUP (stack_state_regs s) a = SOME (wl_Word x) /\ v = word_add x w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[stack_word_exp_def; MAP; ALL; LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPEC `FLOOKUP (stack_state_regs (s:(A,C,FFI)stack_state)) a` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ; IS_SOME_DEF] THEN
  CAKE_REWRITE_TAC[IS_SOME_DEF] THEN
  MP_TAC(ISPEC `a':(A)word_loc` (cases "word_loc")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[distinctness "word_loc"; injectivity "word_loc"] THEN
  CAKE_REWRITE_TAC[IS_SOME_DEF; THE_DEF; option_DISTINCT; option_INJ] THEN
  REWRITE_TAC[word_op_def] THEN CAKE_REWRITE_TAC[ITLIST; WORD_ADD_0; option_INJ] THEN
  MESON_TAC[]);;

(* the state relation after a shared memory load or store that returns   *)
(* (local helpers) *)
let S2LP1AUX_rel_shload = prove
 (`!(s:(A,C,FFI)stack_state) t r v nf.
     stack_to_labProof_state_rel s t
     ==> stack_to_labProof_state_rel
           (stack_state_regs_fupd
              (combin_K (stack_state_regs (stack_dec_clock s) |+ (r,wl_Word v)))
              (stack_state_ffi_fupd (combin_K nf) (stack_dec_clock s)))
           (lab_state_clock_fupd (combin_K (lab_state_clock t - 1))
           (lab_state_io_regs_fupd (combin_K (shift_seq 1 (lab_state_io_regs t)))
           (lab_state_io_fp_regs_fupd (combin_K (shift_seq 1 (lab_state_io_fp_regs t)))
           (lab_state_ffi_fupd (combin_K nf)
           (lab_state_regs_fupd (combin_K ((r =+ wl_Word v) (lab_state_regs t)))
           (lab_state_pc_fupd (combin_K (lab_state_pc t + 1)) t))))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_to_labProof_state_rel_def; stack_dec_clock_def] THEN
  SIMP[FLOOKUP_UPDATE; APPLY_UPDATE_THM; shift_seq_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let S2LP1AUX_rel_shstore = prove
 (`!(s:(A,C,FFI)stack_state) t nf.
     stack_to_labProof_state_rel s t
     ==> stack_to_labProof_state_rel
           (stack_state_ffi_fupd (combin_K nf) (stack_dec_clock s))
           (lab_state_clock_fupd (combin_K (lab_state_clock t - 1))
           (lab_state_io_regs_fupd (combin_K (shift_seq 1 (lab_state_io_regs t)))
           (lab_state_io_fp_regs_fupd (combin_K (shift_seq 1 (lab_state_io_fp_regs t)))
           (lab_state_ffi_fupd (combin_K nf)
           (lab_state_pc_fupd (combin_K (lab_state_pc t + 1)) t)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_to_labProof_state_rel_def; stack_dec_clock_def] THEN
  SIMP[shift_seq_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* the first byte of a word (local helper) *)
let S2LP1AUX_take1_word_to_bytes = prove
 (`!w:A word. good_dimindex (:A) ==> TAKE 1 (word_to_bytes w F) = [get_byte (word 0) w F]`,
  GEN_TAC THEN REWRITE_TAC[good_dimindex_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[word_to_bytes_def] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[num_CONV `8`; num_CONV `7`; num_CONV `6`; num_CONV `5`; num_CONV `4`;
              num_CONV `3`; num_CONV `2`; num_CONV `1`] THEN
  REWRITE_TAC[word_to_bytes_aux_def; APPEND; TAKE_DEF; NOT_SUC] THEN
  REWRITE_TAC[ARITH_RULE `SUC 0 - 1 = 0`; TAKE_DEF]);;

(* facts of state_rel for the shared memory (local helper) *)
let S2LP1AUX_rel_shmem = prove
 (`!(s:(A,C,FFI)stack_state) t.
     stack_to_labProof_state_rel s t
     ==> lab_state_shared_mem_domain t = stack_state_sh_mdomain s /\
         (!x. x IN stack_state_sh_mdomain s ==> val x MOD (dimindex (:A) DIV 8) = 0) /\
         good_dimindex (:A)`,
  SIMP_TAC[stack_to_labProof_state_rel_def]);;

(* stack_dec_clock changes only the clock (local helper) *)
let S2LP1AUX_stack_dec_clock_simps = prove
 (`!(s:(A,C,FFI)stack_state).
     stack_state_sh_mdomain (stack_dec_clock s) = stack_state_sh_mdomain s /\
     stack_state_ffi (stack_dec_clock s) = stack_state_ffi s /\
     stack_state_regs (stack_dec_clock s) = stack_state_regs s`,
  REWRITE_TAC[stack_dec_clock_def] THEN SIMP[]);;

(* a shared memory load of n bytes (local helper of the ShMemOp case) *)
let S2LP1AUX_shm_load = prove
 (CASE_TERM `!op n r a w v (s:(A,C,FFI)stack_state) (t1:(A,C,FFI)lab_state) res s2 nn cs bs.
     (!s:(A,C,FFI)lab_state. share_mem_op op r (Addr a w) s = share_mem_load r (Addr a w) s n) /\
     stack_to_labProof_state_rel s t1 /\ ~(stack_state_clock s = 0) /\
     asm_fetch_aux (lab_state_pc t1) (lab_state_code t1) =
       SOME (Asm (ShareMem op r (Addr a w)) [] 0) /\
     lab_addr (Addr a w) t1 = SOME v /\
     (if n = 0 then v IN stack_state_sh_mdomain s
      else byte_align v IN stack_state_sh_mdomain s) /\
     (match call_FFI (stack_state_ffi s) (SharedMem MappedRead) [word n] (word_to_bytes v F) with
        FFI_final outcome -> (SOME (stack_FinalFFI outcome),stack_dec_clock s)
      | FFI_return nf nb ->
          (NONE,stack_state_regs_fupd
                  (combin_K (stack_state_regs s |+ (r,wl_Word (word_of_bytes F (word 0) nb))))
                  (stack_state_ffi_fupd (combin_K nf) (stack_dec_clock s)))) = (res,s2)
     ==> ?t2. S2LP1AUX_concl res s2 t1 t2 0 1 nn cs bs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP S2LP1AUX_rel_basic) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP S2LP1AUX_rel_shmem) THEN
   SUBGOAL_THEN `(if n = 0 then val (v:A word) MOD (dimindex(:A) DIV 8) = 0 /\
                   v IN lab_state_shared_mem_domain (t1:(A,C,FFI)lab_state)
                  else byte_align v IN lab_state_shared_mem_domain t1)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
     COND_CASES_TAC THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_pair (rhs (concl th)) &&
     not (is_pair (lhs (concl th))))) THEN
   DISJ_CASES_THEN2
     (X_CHOOSE_THEN `nf:(FFI)ffi_state` (X_CHOOSE_THEN `nb:byte list` ASSUME_TAC))
     (X_CHOOSE_THEN `outcome:final_event` ASSUME_TAC)
     (ISPEC `call_FFI (stack_state_ffi (s:(A,C,FFI)stack_state)) (SharedMem MappedRead)
               [word n] (word_to_bytes (v:A word) F)` (cases "ffi_result")) THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
   [EXISTS_TAC `lab_state_clock_fupd (combin_K (lab_state_clock (t1:(A,C,FFI)lab_state) - 1))
     (lab_state_io_regs_fupd (combin_K (shift_seq 1 (lab_state_io_regs t1)))
      (lab_state_io_fp_regs_fupd (combin_K (shift_seq 1 (lab_state_io_fp_regs t1)))
      (lab_state_ffi_fupd (combin_K (nf:(FFI)ffi_state))
      (lab_state_regs_fupd
         (combin_K ((r =+ wl_Word (word_of_bytes F (word 0) nb)) (lab_state_regs t1)))
      (lab_state_pc_fupd (combin_K (lab_state_pc t1 + 1)) t1)))))` THEN
   REWRITE_TAC[S2LP1AUX_concl_none] THEN REPEAT CONJ_TAC THENL
    [REWRITE_TAC[GSYM S2LP1AUX_run_def] THEN MATCH_MP_TAC S2LP1AUX_run_tick_gen THEN
     ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC S2LP1AUX_eval_shload_return THEN
     MAP_EVERY EXISTS_TAC [`op:memop`; `Addr a w:(A)addr`; `[]:byte list`; `0`; `n:num`;
       `v:A word`] THEN
     ASM_REWRITE_TAC[];
     SIMP_NOASM[]; SIMP_NOASM[]; SIMP_NOASM[]; SIMP_NOASM[]; SIMP_NOASM[];
     SIMP_NOASM[IS_PREFIX_REFL]; SIMP_NOASM[];
     MP_TAC(ISPECL [`s:(A,C,FFI)stack_state`; `t1:(A,C,FFI)lab_state`; `r:num`;
       `word_of_bytes F (word 0) (nb:byte list):A word`; `nf:(FFI)ffi_state`]
       S2LP1AUX_rel_shload) THEN
     ASM_REWRITE_TAC[S2LP1AUX_stack_dec_clock_simps]];
    EXISTS_TAC `t1:(A,C,FFI)lab_state` THEN
   REWRITE_TAC[S2LP1AUX_concl_def] THEN CAKE_REWRITE_TAC[halt_view_def] THEN
   REWRITE_TAC[ADD_CLAUSES; S2LP1AUX_stack_dec_clock_simps; lab_with_same_clock] THEN
   ASM_REWRITE_TAC[] THEN
   MP_TAC(ISPECL [`t1:(A,C,FFI)lab_state`; `op:memop`; `r:num`; `Addr a w:(A)addr`;
     `[]:byte list`; `0`; `n:num`; `v:A word`; `outcome:final_event`;
     `lab_state_clock (t1:(A,C,FFI)lab_state) - 1`] S2LP1AUX_eval_shload_final) THEN
   ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `stack_state_clock (s:(A,C,FFI)stack_state) - 1 + 1 =
                 lab_state_clock (t1:(A,C,FFI)lab_state)` SUBST1_TAC THENL
    [ASM_ARITH_TAC; REWRITE_TAC[lab_with_same_clock]]]);;

(* a shared memory store of n bytes (local helper of the ShMemOp case) *)
let S2LP1AUX_shm_store = prove
 (CASE_TERM `!op n r a w v wv (s:(A,C,FFI)stack_state) (t1:(A,C,FFI)lab_state) res s2 nn cs bs.
     (!s:(A,C,FFI)lab_state. share_mem_op op r (Addr a w) s = share_mem_store r (Addr a w) s n) /\
     stack_to_labProof_state_rel s t1 /\ ~(stack_state_clock s = 0) /\
     asm_fetch_aux (lab_state_pc t1) (lab_state_code t1) =
       SOME (Asm (ShareMem op r (Addr a w)) [] 0) /\
     lab_addr (Addr a w) t1 = SOME v /\
     FLOOKUP (stack_state_regs s) r = SOME (wl_Word wv) /\
     (if n = 0 then v IN stack_state_sh_mdomain s
      else byte_align v IN stack_state_sh_mdomain s) /\
     (match call_FFI (stack_state_ffi s) (SharedMem MappedWrite) [word n]
              (APPEND (if n = 0 then word_to_bytes wv F else TAKE n (word_to_bytes wv F))
                      (word_to_bytes v F)) with
        FFI_final outcome -> (SOME (stack_FinalFFI outcome),stack_dec_clock s)
      | FFI_return nf nb -> (NONE,stack_state_ffi_fupd (combin_K nf) (stack_dec_clock s))) = (res,s2)
     ==> ?t2. S2LP1AUX_concl res s2 t1 t2 0 1 nn cs bs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP S2LP1AUX_rel_basic) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP S2LP1AUX_rel_shmem) THEN
   SUBGOAL_THEN `lab_state_regs (t1:(A,C,FFI)lab_state) r = wl_Word wv` ASSUME_TAC THENL
    [MATCH_MP_TAC S2LP1AUX_rel_regs THEN EXISTS_TAC `s:(A,C,FFI)stack_state` THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `(if n = 0 then val (v:A word) MOD (dimindex(:A) DIV 8) = 0 /\
                   v IN lab_state_shared_mem_domain (t1:(A,C,FFI)lab_state)
                  else byte_align v IN lab_state_shared_mem_domain t1)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
     COND_CASES_TAC THEN ASM_MESON_TAC[];
     ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_pair (rhs (concl th)) &&
     not (is_pair (lhs (concl th))))) THEN
   DISJ_CASES_THEN2
     (X_CHOOSE_THEN `nf:(FFI)ffi_state` (X_CHOOSE_THEN `nb:byte list` ASSUME_TAC))
     (X_CHOOSE_THEN `outcome:final_event` ASSUME_TAC)
     (ISPEC `call_FFI (stack_state_ffi (s:(A,C,FFI)stack_state)) (SharedMem MappedWrite) [word n]
               (APPEND (if n = 0 then word_to_bytes (wv:A word) F else TAKE n (word_to_bytes wv F))
                       (word_to_bytes (v:A word) F))` (cases "ffi_result")) THEN
   ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
    [EXISTS_TAC `lab_state_clock_fupd (combin_K (lab_state_clock (t1:(A,C,FFI)lab_state) - 1))
       (lab_state_io_regs_fupd (combin_K (shift_seq 1 (lab_state_io_regs t1)))
        (lab_state_io_fp_regs_fupd (combin_K (shift_seq 1 (lab_state_io_fp_regs t1)))
        (lab_state_ffi_fupd (combin_K (nf:(FFI)ffi_state))
        (lab_state_pc_fupd (combin_K (lab_state_pc t1 + 1)) t1))))` THEN
     REWRITE_TAC[S2LP1AUX_concl_none] THEN REPEAT CONJ_TAC THENL
      [REWRITE_TAC[GSYM S2LP1AUX_run_def] THEN MATCH_MP_TAC S2LP1AUX_run_tick_gen THEN
       ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC S2LP1AUX_eval_shstore_return THEN
       MAP_EVERY EXISTS_TAC [`op:memop`; `r:num`; `Addr a w:(A)addr`; `[]:byte list`; `0`;
         `n:num`; `v:A word`; `wv:A word`; `nb:byte list`] THEN
       ASM_REWRITE_TAC[];
       SIMP_NOASM[]; SIMP_NOASM[]; SIMP_NOASM[]; SIMP_NOASM[]; SIMP_NOASM[];
       SIMP_NOASM[IS_PREFIX_REFL]; SIMP_NOASM[];
       MP_TAC(ISPECL [`s:(A,C,FFI)stack_state`; `t1:(A,C,FFI)lab_state`; `nf:(FFI)ffi_state`]
         S2LP1AUX_rel_shstore) THEN
       ASM_REWRITE_TAC[]];
     EXISTS_TAC `t1:(A,C,FFI)lab_state` THEN
     REWRITE_TAC[S2LP1AUX_concl_def] THEN CAKE_REWRITE_TAC[halt_view_def] THEN
     REWRITE_TAC[ADD_CLAUSES; S2LP1AUX_stack_dec_clock_simps; lab_with_same_clock] THEN
     ASM_REWRITE_TAC[] THEN
     MP_TAC(ISPECL [`t1:(A,C,FFI)lab_state`; `op:memop`; `r:num`; `Addr a w:(A)addr`;
       `[]:byte list`; `0`; `n:num`; `v:A word`; `wv:A word`; `outcome:final_event`;
       `lab_state_clock (t1:(A,C,FFI)lab_state) - 1`] S2LP1AUX_eval_shstore_final) THEN
     ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `stack_state_clock (s:(A,C,FFI)stack_state) - 1 + 1 =
                   lab_state_clock (t1:(A,C,FFI)lab_state)` SUBST1_TAC THENL
      [ASM_ARITH_TAC; REWRITE_TAC[lab_with_same_clock]]]);;

(* the shared memory operations of ShMemOp (local tactics) *)
let S2LP1AUX_IS_SHM th =
  let c = concl th in
  is_eq c && (try fst(dest_const(fst(strip_comb(lhs c)))) = "sh_mem_op" with Failure _ -> false);;

let S2LP1AUX_SHM_ERR_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;;

let S2LP1AUX_SHM_LOAD_TAC (opc:term) (n:term) (defn:thm) : tactic =
  FIRST_X_ASSUM(MP_TAC o check S2LP1AUX_IS_SHM) THEN
  REWRITE_TAC[sh_mem_op_def; defn; S2LP1AUX_stack_dec_clock_simps] THEN
  COND_CASES_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `0` THEN MATCH_MP_TAC S2LP1AUX_shm_load THEN
    MAP_EVERY EXISTS_TAC [opc; n; `r:num`; `a:num`; `w:A word`; `word_add (x:A word) w`;
      `s:(A,C,FFI)stack_state`] THEN
    ASM_REWRITE_TAC[share_mem_op_def] THEN REWRITE_TAC[ARITH_EQ] THEN
    ASM_REWRITE_TAC[];
    S2LP1AUX_SHM_ERR_TAC];;

let S2LP1AUX_SHM_STORE_TAC (opc:term) (n:term) (defn:thm) : tactic =
  FIRST_X_ASSUM(MP_TAC o check S2LP1AUX_IS_SHM) THEN
  REWRITE_TAC[sh_mem_op_def; defn; S2LP1AUX_stack_dec_clock_simps; stack_get_var_def] THEN
  ASM_CASES_TAC `?wv. FLOOKUP (stack_state_regs (s:(A,C,FFI)stack_state)) r =
                      SOME (wl_Word (wv:A word))` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `wv:A word` ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    COND_CASES_TAC THENL
     [REWRITE_TAC[GSYM (MATCH_MP S2LP1AUX_take1_word_to_bytes
                          (ASSUME `good_dimindex(:A)`))] THEN
      DISCH_TAC THEN EXISTS_TAC `0` THEN MATCH_MP_TAC S2LP1AUX_shm_store THEN
      MAP_EVERY EXISTS_TAC [opc; n; `r:num`; `a:num`; `w:A word`; `word_add (x:A word) w`;
        `wv:A word`; `s:(A,C,FFI)stack_state`] THEN
      ASM_REWRITE_TAC[share_mem_op_def] THEN REWRITE_TAC[ARITH_EQ] THEN
      ASM_REWRITE_TAC[];
      S2LP1AUX_SHM_ERR_TAC];
    MP_TAC(ISPEC `FLOOKUP (stack_state_regs (s:(A,C,FFI)stack_state)) r` (cases "option")) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THENL
     [S2LP1AUX_SHM_ERR_TAC;
      MP_TAC(ISPEC `a':(A)word_loc` (cases "word_loc")) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THENL
       [ASM_MESON_TAC[]; S2LP1AUX_SHM_ERR_TAC]]];;

(* case ShMemOp (HOL4 lines 2526-2640) *)
let S2LP1AUX_fc_shmemop = prove
 (`!op r a w (s:(A,C,FFI)stack_state). S2LP1AUX_fc (ShMemOp op r (Addr a w)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[S2LP1AUX_fc_alt] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[stack_evaluate_def] THEN ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN
  CAKE_REWRITE_TAC[call_args_def] THEN REWRITE_TAC S2LP1AUX_IF_RWS THEN CAKE_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `?x. FLOOKUP (stack_state_regs (s:(A,C,FFI)stack_state)) a = SOME (wl_Word x)`
  THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `x:A word` ASSUME_TAC) THEN
    SUBGOAL_THEN `stack_word_exp (s:(A,C,FFI)stack_state) (wl_Op asm_Add [wl_Var a; wl_Const w]) =
                  SOME (word_add x w)` ASSUME_TAC THENL
     [REWRITE_TAC[S2LP1AUX_word_exp_add] THEN ASM_MESON_TAC[]; ALL_TAC];
    SUBGOAL_THEN `stack_word_exp (s:(A,C,FFI)stack_state) (wl_Op asm_Add [wl_Var a; wl_Const w]) =
                  NONE` ASSUME_TAC THENL
     [MP_TAC(ISPEC `stack_word_exp (s:(A,C,FFI)stack_state)
                      (wl_Op asm_Add [wl_Var a; wl_Const w])` (cases "option")) THEN
      REWRITE_TAC[S2LP1AUX_word_exp_add] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_pair (rhs (concl th)) &&
      not (is_pair (lhs (concl th))))) THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_pair (rhs (concl th)) &&
    not (is_pair (lhs (concl th))))) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `stack_state_clock (s:(A,C,FFI)stack_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    MAP_EVERY EXISTS_TAC [`0`; `t1:(A,C,FFI)lab_state`] THEN
    MATCH_MP_TAC S2LP1AUX_concl_timeout_here THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP S2LP1AUX_rel_basic) THEN
  SUBGOAL_THEN `lab_addr (Addr a w) (t1:(A,C,FFI)lab_state) = SOME (word_add x w)` ASSUME_TAC
  THENL
   [REWRITE_TAC[lab_addr_def] THEN
    SUBGOAL_THEN `lab_state_regs (t1:(A,C,FFI)lab_state) a = wl_Word x` SUBST1_TAC THENL
     [MATCH_MP_TAC S2LP1AUX_rel_regs THEN EXISTS_TAC `s:(A,C,FFI)stack_state` THEN
      ASM_REWRITE_TAC[];
      CAKE_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP S2LP1AUX_rel_shmem) THEN
  MP_TAC(ISPEC `op:memop` (cases "memop")) THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THENL
   [S2LP1AUX_SHM_LOAD_TAC `asm_Load` `0` stack_sh_mem_load_def;
    S2LP1AUX_SHM_LOAD_TAC `Load8` `1` stack_sh_mem_load_byte_def;
    S2LP1AUX_SHM_LOAD_TAC `Load16` `2` stack_sh_mem_load16_def;
    S2LP1AUX_SHM_LOAD_TAC `asm_Load32` `4` stack_sh_mem_load32_def;
    S2LP1AUX_SHM_STORE_TAC `asm_Store` `0` stack_sh_mem_store_def;
    S2LP1AUX_SHM_STORE_TAC `Store8` `1` stack_sh_mem_store_byte_def;
    S2LP1AUX_SHM_STORE_TAC `Store16` `2` stack_sh_mem_store16_def;
    S2LP1AUX_SHM_STORE_TAC `asm_Store32` `4` stack_sh_mem_store32_def]);;

(* the compile oracle condition of state_rel (local helper) *)
let S2LP1AUX_rel_oracle =
  let th = SPEC_ALL stack_to_labProof_state_rel_def in
  let has_or t = can (find_term (fun u -> try fst(dest_const u) = "stack_state_compile_oracle"
                                          with Failure _ -> false)) t in
  let c = find (fun t -> is_forall t && has_or t) (conjuncts (rhs (concl th))) in
  prove(list_mk_forall(frees (lhs (concl th)), mk_imp(lhs (concl th), c)),
        REPEAT GEN_TAC THEN REWRITE_TAC[stack_to_labProof_state_rel_def] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* the state relation after an Install (local helper) *)
let S2LP1AUX_rel_install = prove
 (`!(s:(A,C,FFI)stack_state) t n1 n2 p cfg progs bm k cb db.
     stack_to_labProof_state_rel s t /\
     stack_state_compile_oracle s 0 = (cfg,progs,bm)
     ==> stack_to_labProof_state_rel
           (stack_state_bitmaps_fupd (combin_K (APPEND (stack_state_bitmaps s) bm))
           (stack_state_code_buffer_fupd (combin_K cb)
           (stack_state_data_buffer_fupd (combin_K db)
           (stack_state_code_fupd (combin_K (sptree_union (stack_state_code s) (fromAList progs)))
           (stack_state_regs_fupd
              (combin_K (DRESTRICT (stack_state_regs s) (stack_state_ffi_save_regs s) |+
                  (lab_state_ptr_reg t,wl_Loc k 0)))
           (stack_state_fp_regs_fupd (combin_K FEMPTY)
           (stack_state_compile_oracle_fupd (combin_K (shift_seq 1 (stack_state_compile_oracle s)))
              s)))))))
           (lab_state_clock_fupd (combin_K (lab_state_clock t))
           (lab_state_pc_fupd (combin_K p)
           (lab_state_code_buffer_fupd (combin_K cb)
           (lab_state_code_fupd (combin_K (APPEND (lab_state_code (inc_pc (lab_upd_reg (lab_state_link_reg t) (wl_Loc n1 n2) (t:(A,C,FFI)lab_state)))) (MAP prog_to_section progs)))
           (lab_state_cc_regs_fupd (combin_K (shift_seq 1 (lab_state_cc_regs (inc_pc (lab_upd_reg (lab_state_link_reg t) (wl_Loc n1 n2) (t:(A,C,FFI)lab_state))))))
           (lab_state_cc_fp_regs_fupd (combin_K (shift_seq 1 (lab_state_cc_fp_regs (inc_pc (lab_upd_reg (lab_state_link_reg t) (wl_Loc n1 n2) (t:(A,C,FFI)lab_state))))))
           (lab_state_regs_fupd
              (combin_K ((lab_state_ptr_reg (inc_pc (lab_upd_reg (lab_state_link_reg t) (wl_Loc n1 n2) (t:(A,C,FFI)lab_state))) =+ wl_Loc k 0)
                    (\a. get_reg_value (lab_state_cc_regs (inc_pc (lab_upd_reg (lab_state_link_reg t) (wl_Loc n1 n2) (t:(A,C,FFI)lab_state))) 0 a) (lab_state_regs (inc_pc (lab_upd_reg (lab_state_link_reg t) (wl_Loc n1 n2) (t:(A,C,FFI)lab_state))) a) wl_Word)))
           (lab_state_fp_regs_fupd (combin_K (\n. lab_state_cc_fp_regs (inc_pc (lab_upd_reg (lab_state_link_reg t) (wl_Loc n1 n2) (t:(A,C,FFI)lab_state))) 0 n))
           (lab_state_compile_oracle_fupd (combin_K (shift_seq 1 (lab_state_compile_oracle (inc_pc (lab_upd_reg (lab_state_link_reg t) (wl_Loc n1 n2) (t:(A,C,FFI)lab_state))))))
           (lab_state_clock_fupd (combin_K (lab_state_clock (inc_pc (lab_upd_reg (lab_state_link_reg t) (wl_Loc n1 n2) (t:(A,C,FFI)lab_state))) - 1)) (inc_pc (lab_upd_reg (lab_state_link_reg t) (wl_Loc n1 n2) (t:(A,C,FFI)lab_state)))))))))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_ASSUM(MP_TAC o SPEC `0` o MATCH_MP S2LP1AUX_rel_oracle) THEN ASM_REWRITE_TAC[] THEN
   CAKE_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `labels_ok (MAP prog_to_section (progs:(num#(A)stack_prog)list)) /\
                 ALL (\(n,p). call_args p (lab_state_ptr_reg (t:(A,C,FFI)lab_state))
                   (lab_state_len_reg t) (lab_state_ptr2_reg t) (lab_state_len2_reg t)
                   (lab_state_link_reg t)) progs` STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
      [MATCH_MP_TAC prog_to_section_labels_ok THEN ASM_REWRITE_TAC[] THEN
       FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
         (try fst(dest_const(fst(strip_comb(concl th)))) = "ALL" with Failure _ -> false))) THEN
       MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
       CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN CONV_TAC(DEPTH_CONV let_CONV) THEN SIMP_TAC[];
       FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
         (try fst(dest_const(fst(strip_comb(concl th)))) = "ALL" with Failure _ -> false))) THEN
       MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
       CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN SIMP_TAC[]];
     ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP labels_ok_imp) THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
     "stack_to_labProof_state_rel" with Failure _ -> false)) THEN
   REWRITE_TAC[stack_to_labProof_state_rel_def; inc_pc_def; lab_upd_reg_def] THEN
   SIMP[FLOOKUP_UPDATE; FLOOKUP_DRESTRICT; FLOOKUP_EMPTY; APPLY_UPDATE_THM; shift_seq_def] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `lab_state_cc_regs (t:(A,C,FFI)lab_state) 0 n = NONE` SUBST1_TAC THENL
    [ASM_MESON_TAC[]; REWRITE_TAC[get_reg_value_def]] THEN
   COND_CASES_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
    REPEAT GEN_TAC THEN REWRITE_TAC[lookup_union] THEN
   MP_TAC(ISPEC `lookup n (stack_state_code (s:(A,C,FFI)stack_state))` (cases "option")) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[option_INJ] THENL
    [REWRITE_TAC[lookup_fromAList] THEN DISCH_TAC THEN
     FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALOOKUP_MEM) THEN
     SUBGOAL_THEN `~MEM n (MAP Section_num (lab_state_code (t:(A,C,FFI)lab_state)))`
       ASSUME_TAC THENL
      [FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) =
         "domain" with Failure _ -> false)) THEN
       REWRITE_TAC[EXTENSION; IN_SET_OF_LIST] THEN
       DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[domain_lookup; option_DISTINCT] THEN
       MESON_TAC[];
       ALL_TAC] THEN
     CONJ_TAC THENL
      [UNDISCH_TAC `ALL (\(n,p). call_args p (lab_state_ptr_reg (t:(A,C,FFI)lab_state))
                   (lab_state_len_reg t) (lab_state_ptr2_reg t) (lab_state_len2_reg t)
                   (lab_state_link_reg t)) (progs:(num#(A)stack_prog)list)` THEN
       REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_THEN(MP_TAC o SPEC `(n:num,prog:(A)stack_prog)`) THEN
       ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[];
       MP_TAC(ISPECL [`progs:(num#(A)stack_prog)list`; `n:num`; `prog:(A)stack_prog`]
     code_installed_prog_to_section) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `pc:num` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `sec_labels_ok (prog_to_section (n:num,prog:(A)stack_prog))` MP_TAC THENL
    [UNDISCH_TAC `ALL sec_labels_ok (MAP prog_to_section (progs:(num#(A)stack_prog)list))` THEN
     REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN DISCH_THEN MATCH_MP_TAC THEN
     EXISTS_TAC `(n:num,prog:(A)stack_prog)` THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `?lines nr m. stack_to_lab_flatten T (prog:(A)stack_prog) n (next_lab prog 2) [] [] =
                   (lines,nr,m)` STRIP_ASSUME_TAC THENL
    [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
   ASM_REWRITE_TAC[prog_to_section_def] THEN CAKE_REWRITE_TAC[] THEN
   REWRITE_TAC[sec_labels_ok_def; append_thm; ALL_APPEND] THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN
   EXISTS_TAC `pc + LENGTH (FLAT (MAP (FILTER ((~) o is_Label) o Section_lines)
     (lab_state_code (t:(A,C,FFI)lab_state))))` THEN
   REWRITE_TAC[FST] THEN CONJ_TAC THENL
    [ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC code_installed_append2 THEN
     EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
     MATCH_MP_TAC loc_to_pc_append2 THEN ASM_REWRITE_TAC[]] THEN
       UNDISCH_TAC `stack_to_labProof_code_installed pc
     (append (FST (stack_to_lab_flatten T (prog:(A)stack_prog) n (next_lab prog 2) [] [])))
     (MAP prog_to_section (progs:(num#(A)stack_prog)list))` THEN ASM_REWRITE_TAC[FST]];
     DISCH_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
   FIRST_ASSUM(fun th -> MP_TAC (MATCH_MP th (ASSUME
     `lookup n (stack_state_code (s:(A,C,FFI)stack_state)) = SOME (prog:(A)stack_prog)`))) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `pc:num` THEN
   ASM_SIMP_TAC[code_installed_APPEND; loc_to_pc_APPEND]];
    REWRITE_TAC[domain_fromAList; MAP_prog_to_section_Section_num]]);;

(* the Install step (local helper) *)
let S2LP1AUX_eval_install = prove
 (`!(t:(A,C,FFI)lab_state) w b kk w1 w2 n1 n2 bytes cb new_pc cfg prog cfg' k lines rest ck.
     asm_fetch_aux (lab_state_pc t) (lab_state_code t) = SOME (LabAsm lab_Install w b kk) /\
     lab_state_regs t (lab_state_ptr_reg t) = wl_Word w1 /\
     lab_state_regs t (lab_state_len_reg t) = wl_Word w2 /\
     lab_state_regs t (lab_state_link_reg t) = wl_Loc n1 n2 /\
     buffer_flush (lab_state_code_buffer t) w1 w2 = SOME (bytes,cb) /\
     loc_to_pc n1 n2 (lab_state_code t) = SOME new_pc /\
     lab_state_compile_oracle t 0 = (cfg,prog) /\
     lab_state_compile t cfg prog = SOME (bytes,cfg') /\
     prog = CONS (Section k lines) rest /\
     FST (shift_seq 1 (lab_state_compile_oracle t) 0) = cfg'
     ==> lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t) =
         lab_evaluate (lab_state_clock_fupd (combin_K ck)
           (lab_state_pc_fupd (combin_K new_pc)
           (lab_state_code_buffer_fupd (combin_K cb)
           (lab_state_code_fupd (combin_K (APPEND (lab_state_code t) prog))
           (lab_state_cc_regs_fupd (combin_K (shift_seq 1 (lab_state_cc_regs t)))
           (lab_state_cc_fp_regs_fupd (combin_K (shift_seq 1 (lab_state_cc_fp_regs t)))
           (lab_state_regs_fupd
              (combin_K ((lab_state_ptr_reg t =+ wl_Loc k 0)
                    (\a. get_reg_value (lab_state_cc_regs t 0 a) (lab_state_regs t a) wl_Word)))
           (lab_state_fp_regs_fupd (combin_K (\n. lab_state_cc_fp_regs t 0 n))
           (lab_state_compile_oracle_fupd (combin_K (shift_seq 1 (lab_state_compile_oracle t)))
              t)))))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) && is_var (lhs (concl th)))) THEN
  GEN_REWRITE_TAC LAND_CONV [lab_evaluate_def] THEN
  REWRITE_TAC[asm_fetch_def] THEN SIMP[ADD_EQ_0; ARITH_EQ] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN REWRITE_TAC[lab_state_component_equality] THEN SIMP[ADD_SUB]);;

(* the compiler and the compile oracle of state_rel (local helper) *)
let S2LP1AUX_rel_compile = prove
 (`!(s:(A,C,FFI)stack_state) t.
     stack_to_labProof_state_rel s t
     ==> (!c p. stack_state_compile s c p = lab_state_compile t c (MAP prog_to_section p)) /\
         (!k. lab_state_compile_oracle t k =
              (FST (stack_state_compile_oracle s k),
               MAP prog_to_section (FST (SND (stack_state_compile_oracle s k)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[stack_to_labProof_state_rel_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  MP_TAC(ISPEC `stack_state_compile_oracle (s:(A,C,FFI)stack_state) k` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:C` (X_CHOOSE_THEN `pb:(num#(A)stack_prog)list#((A word)list)`
    SUBST1_TAC)) THEN
  MP_TAC(ISPEC `pb:(num#(A)stack_prog)list#((A word)list)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(num#(A)stack_prog)list` (X_CHOOSE_THEN `b0:(A word)list`
    SUBST1_TAC)) THEN
  CAKE_REWRITE_TAC[FST; SND]);;

(* the fields of the state after a LocValue step (local helper) *)
let S2LP1AUX_ta_simps = prove
 (`!r v (t:(A,C,FFI)lab_state).
     lab_state_pc (inc_pc (lab_upd_reg r v t)) = lab_state_pc t + 1 /\
     lab_state_code (inc_pc (lab_upd_reg r v t)) = lab_state_code t /\
     lab_state_regs (inc_pc (lab_upd_reg r v t)) = (r =+ v) (lab_state_regs t) /\
     lab_state_len_reg (inc_pc (lab_upd_reg r v t)) = lab_state_len_reg t /\
     lab_state_ptr_reg (inc_pc (lab_upd_reg r v t)) = lab_state_ptr_reg t /\
     lab_state_len2_reg (inc_pc (lab_upd_reg r v t)) = lab_state_len2_reg t /\
     lab_state_ptr2_reg (inc_pc (lab_upd_reg r v t)) = lab_state_ptr2_reg t /\
     lab_state_link_reg (inc_pc (lab_upd_reg r v t)) = lab_state_link_reg t /\
     lab_state_code_buffer (inc_pc (lab_upd_reg r v t)) = lab_state_code_buffer t /\
     lab_state_compile (inc_pc (lab_upd_reg r v t)) = lab_state_compile t /\
     lab_state_compile_oracle (inc_pc (lab_upd_reg r v t)) = lab_state_compile_oracle t /\
     lab_state_clock (inc_pc (lab_upd_reg r v t)) = lab_state_clock t`,
  REWRITE_TAC[inc_pc_def; lab_upd_reg_def] THEN SIMP[]);;

(* local tactics and terms of the Install case *)
let S2LP1AUX_IS_EVAL th = is_eq (concl th) &&
  rhs (concl th) = `(r:((A)stack_result)option),(s2:(A,C,FFI)stack_state)`;;

let S2LP1AUX_EVAL_REWRITE_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check S2LP1AUX_IS_EVAL) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN DISCH_TAC;;

let S2LP1AUX_EVAL_ERR_TAC : tactic =
  REPEAT S2LP1AUX_ASM_CASE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  ASM_MESON_TAC[];;

let S2LP1AUX_IAFTER = subst [S2LP1AUX_TA,`ta:(A,C,FFI)lab_state`]
  `lab_state_pc_fupd (combin_K ((lab_state_pc (t1:(A,C,FFI)lab_state) + 1) + 1))
           (lab_state_code_buffer_fupd (combin_K (cb:(A,8)buffer))
           (lab_state_code_fupd (combin_K (APPEND (lab_state_code (ta:(A,C,FFI)lab_state))
              (MAP prog_to_section (CONS (k,prog:(A)stack_prog) rest))))
           (lab_state_cc_regs_fupd (combin_K (shift_seq 1 (lab_state_cc_regs ta)))
           (lab_state_cc_fp_regs_fupd (combin_K (shift_seq 1 (lab_state_cc_fp_regs ta)))
           (lab_state_regs_fupd
              (combin_K ((lab_state_ptr_reg ta =+ wl_Loc k 0)
                    (\a. get_reg_value (lab_state_cc_regs ta 0 a) (lab_state_regs ta a) wl_Word)))
           (lab_state_fp_regs_fupd (combin_K (\n. lab_state_cc_fp_regs ta 0 n))
           (lab_state_compile_oracle_fupd (combin_K (shift_seq 1 (lab_state_compile_oracle ta)))
              ta)))))))`;;

(* case Install (HOL4 lines 2417-2525) *)
let S2LP1AUX_fc_install = prove
 (`!ptr len dptr dlen ret (s:(A,C,FFI)stack_state).
     S2LP1AUX_fc (stack_Install ptr len dptr dlen ret) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[S2LP1AUX_fc_alt] THEN REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC[stack_evaluate_def] THEN ONCE_REWRITE_TAC[stack_to_lab_flatten_def] THEN
   CAKE_REWRITE_TAC[call_args_def] THEN REWRITE_TAC S2LP1AUX_IF_RWS THEN CAKE_REWRITE_TAC[] THEN
   STRIP_TAC THEN RVEQ_TAC THEN
   ASM_CASES_TAC `?w1 w2 w3 w4.
     stack_get_var (lab_state_ptr_reg t1) (s:(A,C,FFI)stack_state) = SOME (wl_Word w1) /\
     stack_get_var (lab_state_len_reg (t1:(A,C,FFI)lab_state)) s = SOME (wl_Word w2) /\
     stack_get_var dptr s = SOME (wl_Word w3) /\
     stack_get_var dlen s = SOME (wl_Word (w4:A word))` THENL
    [FIRST_X_ASSUM(X_CHOOSE_THEN `w1:A word` (X_CHOOSE_THEN `w2:A word`
       (X_CHOOSE_THEN `w3:A word` (X_CHOOSE_THEN `w4:A word` STRIP_ASSUME_TAC)))) THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_pair (rhs (concl th)) &&
       not (is_pair (lhs (concl th))))) THEN
     ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN DISCH_TAC;
     REPEAT S2LP1AUX_ASM_CASE_TAC THEN
     RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
     REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
     RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
     ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN `?cfg progs bm. stack_state_compile_oracle (s:(A,C,FFI)stack_state) 0 =
                   (cfg,progs,bm)` STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP S2LP1AUX_rel_basic) THEN
   SUBGOAL_THEN `~stack_state_use_stack (s:(A,C,FFI)stack_state)` ASSUME_TAC THENL
    [(* a conjunct of the relation (ASM_MESON_TAC took 34 s) *)
     FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [stack_to_labProof_state_rel_def]) THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   S2LP1AUX_EVAL_REWRITE_TAC THEN
   ASM_CASES_TAC `?bytes cb. buffer_flush (stack_state_code_buffer (s:(A,C,FFI)stack_state)) w1 w2 =
                    SOME (bytes,cb)` THENL
    [FIRST_X_ASSUM(X_CHOOSE_THEN `bytes:byte list` (X_CHOOSE_THEN `cb:(A,8)buffer` ASSUME_TAC)) THEN
     S2LP1AUX_EVAL_REWRITE_TAC;
     S2LP1AUX_EVAL_ERR_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check S2LP1AUX_IS_EVAL) THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   DISCH_TAC THEN
   ASM_CASES_TAC `?bytes' cfg'. stack_state_compile (s:(A,C,FFI)stack_state) cfg progs =
                    SOME (bytes',cfg')` THENL
    [FIRST_X_ASSUM(X_CHOOSE_THEN `bytes':byte list` (X_CHOOSE_THEN `cfg':C` ASSUME_TAC)) THEN
     S2LP1AUX_EVAL_REWRITE_TAC;
     S2LP1AUX_EVAL_ERR_TAC] THEN
   ASM_CASES_TAC `?k prog rest. (progs:(num#(A)stack_prog)list) = CONS (k,prog) rest` THENL
    [FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `prog:(A)stack_prog`
       (X_CHOOSE_THEN `rest:(num#(A)stack_prog)list` ASSUME_TAC))) THEN
     FIRST_X_ASSUM(MP_TAC o check S2LP1AUX_IS_EVAL) THEN
     ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN DISCH_TAC;
     FIRST_X_ASSUM(MP_TAC o check S2LP1AUX_IS_EVAL) THEN
     MP_TAC(ISPEC `progs:(num#(A)stack_prog)list` list_CASES) THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ] THENL
      [STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC;
       ASM_MESON_TAC[PAIR_SURJECTIVE]]] THEN
  FIRST_X_ASSUM(MP_TAC o check S2LP1AUX_IS_EVAL) THEN
   ASM_CASES_TAC `(bytes:byte list) = bytes' /\
     FST (shift_seq 1 (stack_state_compile_oracle (s:(A,C,FFI)stack_state)) 0) = (cfg':C)` THEN
   ASM_REWRITE_TAC[PAIR_EQ] THEN
   TRY(STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC THEN
       NO_TAC) THEN
   FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
   DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  MP_TAC(ISPECL [`k:num`; `prog:(A)stack_prog`] S2LP1AUX_prog_to_section_Section) THEN
   DISCH_THEN(X_CHOOSE_THEN `ls0:((A)line)list` ASSUME_TAC) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP S2LP1AUX_rel_compile) THEN
   SUBGOAL_THEN `lab_state_regs t1 (lab_state_ptr_reg t1) = wl_Word (w1:A word) /\
                 lab_state_regs (t1:(A,C,FFI)lab_state) (lab_state_len_reg t1) = wl_Word w2`
     STRIP_ASSUME_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[stack_get_var_def]) THEN IMP_RES_TAC S2LP1AUX_rel_regs THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN
    (subst [S2LP1AUX_TA,`ta:(A,C,FFI)lab_state`]
    `asm_fetch_aux (lab_state_pc (ta:(A,C,FFI)lab_state)) (lab_state_code ta) =
       SOME (LabAsm lab_Install (word 0) [] 0) /\
     lab_state_regs ta (lab_state_ptr_reg ta) = wl_Word (w1:A word) /\
     lab_state_regs ta (lab_state_len_reg ta) = wl_Word w2 /\
     lab_state_regs ta (lab_state_link_reg ta) = wl_Loc n l /\
     buffer_flush (lab_state_code_buffer ta) w1 w2 = SOME (bytes,cb) /\
     loc_to_pc n l (lab_state_code ta) =
       SOME ((lab_state_pc (t1:(A,C,FFI)lab_state) + 1) + 1) /\
     lab_state_compile_oracle ta 0 =
       (cfg:C,MAP prog_to_section (CONS (k,prog) (rest:(num#(A)stack_prog)list))) /\
     lab_state_compile ta cfg (MAP prog_to_section (CONS (k,prog) rest)) = SOME (bytes,cfg') /\
     MAP prog_to_section (CONS (k,prog) rest) = CONS (Section k ls0) (MAP prog_to_section rest) /\
     FST (shift_seq 1 (lab_state_compile_oracle ta) 0) = cfg'`)
     STRIP_ASSUME_TAC THENL
    [REWRITE_TAC[S2LP1AUX_ta_simps; APPLY_UPDATE_THM; MAP; shift_seq_def; ADD_CLAUSES] THEN
     ASM_REWRITE_TAC[FST; SND; MAP] THEN
     UNDISCH_TAC `stack_state_compile (s:(A,C,FFI)stack_state) cfg progs =
                    SOME (bytes',cfg')` THEN
     ASM_REWRITE_TAC[MAP] THEN
     DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `FST (shift_seq 1 (stack_state_compile_oracle (s:(A,C,FFI)stack_state)) 0) =
                (cfg':C)` THEN
   REWRITE_TAC[shift_seq_def; ADD_CLAUSES];
     ALL_TAC] THEN
  SUBGOAL_THEN (subst [S2LP1AUX_TA,`ta:(A,C,FFI)lab_state`]
     `!ck. lab_evaluate (lab_state_clock_fupd (combin_K (ck + 1)) t1) =
           lab_evaluate (lab_state_clock_fupd (combin_K ck) (ta:(A,C,FFI)lab_state))`) ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC S2LP1AUX_eval_locvalue THEN
     MAP_EVERY EXISTS_TAC [`word 0:A word`; `[]:byte list`; `0`;
       `(lab_state_pc (t1:(A,C,FFI)lab_state) + 1) + 1`] THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   EXISTS_TAC `2` THEN
   EXISTS_TAC (subst [S2LP1AUX_IAFTER,`tt:(A,C,FFI)lab_state`]
     `lab_state_clock_fupd (combin_K (lab_state_clock (t1:(A,C,FFI)lab_state))) (tt:(A,C,FFI)lab_state)`) THEN
   REWRITE_TAC[S2LP1AUX_concl_none] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[S2LP1AUX_clock_fupd_fupd; S2LP1AUX_clock_clock_fupd] THEN
   REWRITE_TAC[ARITH_RULE `(c + 2) + ck1 = ((c + ck1) + 1) + 1`] THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC S2LP1AUX_eval_install THEN
   MAP_EVERY EXISTS_TAC [`word 0:A word`; `[]:byte list`; `0`; `w1:A word`; `w2:A word`;
     `n:num`; `l:num`; `bytes:byte list`; `cfg:C`; `cfg':C`; `ls0:((A)line)list`;
     `MAP prog_to_section (rest:(num#(A)stack_prog)list)`] THEN
   ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC (subst [S2LP1AUX_TA,`ta:(A,C,FFI)lab_state`]
     `lab_state_compile (ta:(A,C,FFI)lab_state) cfg
        (MAP prog_to_section (CONS (k,prog:(A)stack_prog) rest)) = SOME (bytes,cfg':C)`) THEN
   ASM_REWRITE_TAC[];
    SIMP_NOASM[inc_pc_def; lab_upd_reg_def];
    SIMP_NOASM[inc_pc_def; lab_upd_reg_def];
    SIMP_NOASM[inc_pc_def; lab_upd_reg_def];
    SIMP_NOASM[inc_pc_def; lab_upd_reg_def];
    SIMP_NOASM[inc_pc_def; lab_upd_reg_def];
    SIMP_NOASM[inc_pc_def; lab_upd_reg_def] THEN REWRITE_TAC[IS_PREFIX_APPEND] THEN MESON_TAC[];
    SIMP_NOASM[inc_pc_def; lab_upd_reg_def] THEN ARITH_TAC;
    MP_TAC(ISPECL [`s:(A,C,FFI)stack_state`; `t1:(A,C,FFI)lab_state`; `n:num`; `l:num`;
     `(lab_state_pc (t1:(A,C,FFI)lab_state) + 1) + 1`; `cfg:C`;
     `CONS (k:num,prog:(A)stack_prog) rest`; `bm:(A word)list`; `k:num`; `cb:(A,8)buffer`;
     `stack_state_data_buffer (s:(A,C,FFI)stack_state)`] S2LP1AUX_rel_install) THEN
   ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[lab_state_component_equality] THEN
   SIMP[]]);;

(* the induction of flatten_correct over stackSem's evaluate (local helper) *)
let S2LP1AUX_fc_all = prove
 (`!x:(A)stack_prog#(A,C,FFI)stack_state. S2LP1AUX_fc (FST x) (SND x)`,
  MATCH_MP_TAC stack_evaluate_ind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC [S2LP1AUX_fc_skip; S2LP1AUX_fc_halt; S2LP1AUX_fc_alloc;
    S2LP1AUX_fc_storeconsts; S2LP1AUX_fc_inst; S2LP1AUX_fc_get; S2LP1AUX_fc_set;
    S2LP1AUX_fc_opcurrheap; S2LP1AUX_fc_tick; S2LP1AUX_fc_seq; S2LP1AUX_fc_return;
    S2LP1AUX_fc_raise; S2LP1AUX_fc_break; S2LP1AUX_fc_continue; S2LP1AUX_fc_if;
    S2LP1AUX_fc_loop; S2LP1AUX_fc_jumplower; S2LP1AUX_fc_rawcall; S2LP1AUX_fc_call;
    S2LP1AUX_fc_install; S2LP1AUX_fc_shmemop; S2LP1AUX_fc_codebufferwrite;
    S2LP1AUX_fc_databufferwrite; S2LP1AUX_fc_ffi; S2LP1AUX_fc_locvalue;
    S2LP1AUX_fc_stackalloc; S2LP1AUX_fc_stackfree; S2LP1AUX_fc_stackload;
    S2LP1AUX_fc_stackloadany; S2LP1AUX_fc_stackstore; S2LP1AUX_fc_stackstoreany;
    S2LP1AUX_fc_stackgetsize; S2LP1AUX_fc_stacksetsize; S2LP1AUX_fc_bitmapload]));;

(* HOL4 line 1207 (evaluate of prog is stackSem's, of t1 labSem's; HOL4     *)
(* t1.clock + ck + ck1 is (t1.clock + ck) + ck1) *)
let flatten_correct = prove
 (CASE_TERM
  `!prog s1 t r s2 n l cs bs (t1:(A,C,FFI)lab_state).
     stack_evaluate (prog,s1) = (r,s2) /\ ~(r = SOME stack_Error) /\
     stack_to_labProof_state_rel s1 t1 /\
     call_args prog (lab_state_ptr_reg t1) (lab_state_len_reg t1) (lab_state_ptr2_reg t1)
       (lab_state_len2_reg t1) (lab_state_link_reg t1) /\
     stack_to_labProof_code_installed (lab_state_pc t1)
       (append (FST (stack_to_lab_flatten t prog n l cs bs))) (lab_state_code t1) /\
     ALL (\k. IS_SOME (loc_to_pc n k (lab_state_code t1))) (APPEND (APPEND cs bs) [0])
     ==> ?ck t2.
           (match halt_view r with
              SOME res ->
                lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock t1 + ck)) t1) = (res,t2) /\
                lab_state_ffi t2 = stack_state_ffi s2
            | NONE ->
                (!ck1. lab_evaluate (lab_state_clock_fupd (combin_K ((lab_state_clock t1 + ck) + ck1)) t1) =
                       lab_evaluate (lab_state_clock_fupd (combin_K (lab_state_clock t2 + ck1)) t2)) /\
                lab_state_len_reg t2 = lab_state_len_reg t1 /\
                lab_state_ptr_reg t2 = lab_state_ptr_reg t1 /\
                lab_state_len2_reg t2 = lab_state_len2_reg t1 /\
                lab_state_ptr2_reg t2 = lab_state_ptr2_reg t1 /\
                lab_state_link_reg t2 = lab_state_link_reg t1 /\
                lab_state_code t1 <<= lab_state_code t2 /\
                (match OPTION_MAP (\w. result_view w n cs bs) r with
                   NONE ->
                     lab_state_pc t2 =
                       lab_state_pc t1 +
                       LENGTH (FILTER ((~) o is_Label)
                                 (append (FST (stack_to_lab_flatten t prog n l cs bs)))) /\
                     stack_to_labProof_state_rel s2 t2
                 | SOME (Vloc n1 n2) ->
                     (!n. IS_SOME (lookup n (stack_state_code s2))
                          ==> IS_SOME (loc_to_pc n 0 (lab_state_code t2))) /\
                     (!w. loc_to_pc n1 n2 (lab_state_code t2) = SOME w
                          ==> w = lab_state_pc t2 /\ stack_to_labProof_state_rel s2 t2)
                 | SOME (Vcont n1 n2) ->
                     stack_to_labProof_state_rel s2 t2 /\
                     stack_to_labProof_code_installed (lab_state_pc t2)
                       [LabAsm (lab_Jump (lab_Lab n1 n2)) (word 0) [] 0] (lab_state_code t2)
                 | SOME Vtimeout -> lab_state_ffi t2 = stack_state_ffi s2 /\ lab_state_clock t2 = 0
                 | _ -> F))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC `(prog:(A)stack_prog,s1:(A,C,FFI)stack_state)` S2LP1AUX_fc_all) THEN
  REWRITE_TAC[FST; SND; S2LP1AUX_fc_def] THEN
  DISCH_THEN(ACCEPT_TAC o SPECL [`t:bool`; `r:((A)stack_result)option`;
    `s2:(A,C,FFI)stack_state`; `n:num`; `l:num`; `cs:num list`; `bs:num list`;
    `t1:(A,C,FFI)lab_state`]));;
