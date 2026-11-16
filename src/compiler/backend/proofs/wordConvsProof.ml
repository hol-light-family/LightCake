(* ========================================================================= *)
(* wordConvsProof: port of HOL4 compiler/backend/proofs/                     *)
(* wordConvsProofScript.sml (CakeML v3479).                                  *)
(* Syntactic properties proofs for wordConvs: the syntactic properties of   *)
(* wordLang that are preserved across the wordLang passes.                  *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - wordLang constructors wl_...; HOL4 extract_labels is                    *)
(*   wordConvs_extract_labels, word_get_code_labels (an overload of          *)
(*   wordConvs$get_code_labels) is wordConvs_get_code_labels,                *)
(*   word_good_handlers is good_handlers, word_good_code_labels is           *)
(*   wordConvs_good_code_labels; word_simp's Seq_assoc, dest_Seq and         *)
(*   compile_exp are Seq_assoc, word_simp_dest_Seq and word_simp_compile_exp; *)
(*   word_unreach's Seq_assoc_right is Seq_assoc_right;                      *)
(*   word_to_word's compile_single and compile are                           *)
(*   word_to_word_compile_single and word_to_word_compile.                   *)
(* - HOL4 FOLDR f e l = ITLIST f l e, EVERY = ALL, set = set_of_list,        *)
(*   ZIP (a,b) = ZIP a b, ++ = APPEND.                                       *)
(* - Free variables of HOL4 statements stay free; unused HOL4 variables     *)
(*   (s, k, conf) get their own type variable B or C.                        *)
(* - HOL4 addr_offset_ok c 0w is asm_offset_ok 0 (asm_config_addr_offset c)  *)
(*   (word 0), similarly hw_offset_ok and byte_offset_ok.                    *)
(* - The HOL4 ML values try_cancel_labels_rel_append, boring_tac, convs and  *)
(*   rmt_convs (tactics and lists of definitions) are not ported.           *)
(* - Proof method: most inductions over the passes are WF inductions on    *)
(*   wl_prog_size (WPROOF2AUX_PROG_STEP_TAC), stated for FST (or SND) of    *)
(*   the pass, with the shapes of the instructions and moves the passes     *)
(*   emit described by closure lemmas (WPROOF2AUX_..._closed); the HOL4    *)
(*   statements follow from them.                                            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_to_word.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/word_simp.ml";;
needs "compiler/backend/word_alloc.ml";;
needs "compiler/backend/word_inst.ml";;
needs "compiler/backend/word_unreach.ml";;
needs "compiler/backend/word_remove.ml";;
needs "compiler/backend/word_cse.ml";;
needs "compiler/backend/word_elim.ml";;
needs "compiler/backend/word_copy.ml";;

type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* extract_labels                                                            *)
(* ------------------------------------------------------------------------- *)


let extract_labels_SmartSeq = prove
 (`wordConvs_extract_labels (SmartSeq p1 p2:(A)wl_prog) =
   wordConvs_extract_labels (wl_Seq p1 p2)`,
  REWRITE_TAC[SmartSeq_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[wordConvs_extract_labels_def; APPEND]);;

let WPROOF2AUX_wc_ret_cases = prove
 (`!(ret:(num list#cutsets#(A)wl_prog#num#num)option).
     ret = NONE \/ ?n names rh l1 l2. ret = SOME (n,names,rh,l1,l2)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `ret:(num list#cutsets#(A)wl_prog#num#num)option`
                                        (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  SPEC_TAC(`a:num list#cutsets#(A)wl_prog#num#num`,`a:num list#cutsets#(A)wl_prog#num#num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

let WPROOF2AUX_wc_handler_cases = prove
 (`!(handler:(num#(A)wl_prog#num#num)option).
     handler = NONE \/ ?hn h hl1 hl2. handler = SOME (hn,h,hl1,hl2)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `handler:(num#(A)wl_prog#num#num)option`
                                        (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  SPEC_TAC(`a:num#(A)wl_prog#num#num`,`a:num#(A)wl_prog#num#num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

(* split the return and the exception handler of a call in the goal whose *)
(* arguments are variables                                                  *)

let WPROOF2AUX_wc_CALL_SPLIT_TAC : tactic = fun (asl,w as g) ->
  let is_call t = is_comb t &&
    (let f,args = strip_comb t in
     is_const f && fst(dest_const f) = "wl_Call" && length args = 4) in
  let t = find_term (fun t -> is_call t &&
                       let args = snd(strip_comb t) in
                       is_var (hd args) && is_var (last args)) w in
  let args = snd(strip_comb t) in
  let ret = hd args and handler = last args in
  (DISJ_CASES_THEN2 SUBST_ALL_TAC
     (X_CHOOSE_THEN `n:num list` (X_CHOOSE_THEN `names:cutsets`
       (X_CHOOSE_THEN `rh:(A)wl_prog` (X_CHOOSE_THEN `l1:num`
         (X_CHOOSE_THEN `l2:num` SUBST_ALL_TAC)))))
     (SPEC ret WPROOF2AUX_wc_ret_cases) THEN
   DISJ_CASES_THEN2 SUBST_ALL_TAC
     (X_CHOOSE_THEN `hn:num` (X_CHOOSE_THEN `h:(A)wl_prog`
       (X_CHOOSE_THEN `hl1:num` (X_CHOOSE_THEN `hl2:num` SUBST_ALL_TAC))))
     (SPEC handler WPROOF2AUX_wc_handler_cases) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; option_DISTINCT; PAIR_EQ]) THEN
   RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN CASE_REWRITE_TAC[]) g;;

let extract_labels_Seq_assoc_lemma = prove
 (`!p1 p2:(A)wl_prog.
     wordConvs_extract_labels (Seq_assoc p1 p2) =
     APPEND (wordConvs_extract_labels p1) (wordConvs_extract_labels p2)`,
  MATCH_MP_TAC word_simp_Seq_assoc_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  REWRITE_TAC[word_simp_Seq_assoc_def; extract_labels_SmartSeq;
              wordConvs_extract_labels_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[APPEND; APPEND_NIL; APPEND_ASSOC; LET_DEF; LET_END_DEF;
               wordConvs_extract_labels_def]);;

let extract_labels_Seq_assoc = prove
 (`wordConvs_extract_labels (Seq_assoc wl_Skip p:(A)wl_prog) = wordConvs_extract_labels p`,
  REWRITE_TAC[extract_labels_Seq_assoc_lemma; wordConvs_extract_labels_def; APPEND]);;

let extract_labels_drop_consts_1 = prove
 (`wordConvs_extract_labels (drop_consts (cs:(A word)spt) ls) = []`,
  SPEC_TAC(`ls:num list`,`ls:num list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[drop_consts_def; wordConvs_extract_labels_def] THEN
  REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_REWRITE_TAC[extract_labels_SmartSeq; wordConvs_extract_labels_def; APPEND]);;

let extract_labels_drop_consts = prove
 (`wordConvs_extract_labels (SmartSeq (drop_consts (cs:(A word)spt) ls) p) =
   wordConvs_extract_labels p`,
  REWRITE_TAC[extract_labels_SmartSeq; wordConvs_extract_labels_def;
              extract_labels_drop_consts_1; APPEND]);;
let _ = cake_add_simps [extract_labels_drop_consts];;

let WPROOF2AUX_wc_ceqs =
  [COND_CASE_EQ; option_case_eq; pair_case_eq; list_case_eq; case_eq "wl_exp"];;

(* strip the induction hypotheses (if any) of a goal                        *)
(* !x1 .. xn. IH ==> !y1 .. ym. f p cs = (p1,cs1) ==> concl                 *)
let WPROOF2AUX_wc_IH_TAC (f:string) : tactic =
  REPEAT GEN_TAC THEN
  (fun (asl,w as g) ->
     let a = fst(dest_imp w) in
     if is_eq a && (try fst(dest_const(fst(strip_comb(lhs a)))) = f with Failure _ -> false)
     then ALL_TAC g
     else (DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN REPEAT GEN_TAC) g);;

let WPROOF2AUX_wc_labels_rel_app1 = prove
 (`!xs ys (zs:A list). labels_rel xs zs ==> labels_rel (APPEND xs ys) zs`,
  REWRITE_TAC[labels_rel_def; ALL_DISTINCT_APPEND; SUBSET; IN_SET_OF_LIST; MEM_APPEND] THEN
  MESON_TAC[]);;

let WPROOF2AUX_wc_labels_rel_app2 = prove
 (`!xs ys (zs:A list). labels_rel ys zs ==> labels_rel (APPEND xs ys) zs`,
  REWRITE_TAC[labels_rel_def; ALL_DISTINCT_APPEND; SUBSET; IN_SET_OF_LIST; MEM_APPEND] THEN
  MESON_TAC[]);;

(* close a leaf of a labels_rel induction                                    *)
let WPROOF2AUX_wc_LABELS_FIN_TAC : tactic =
  CASE_REWRITE_TAC[LET_DEF; LET_END_DEF; APPEND] THEN
  RES_TAC THEN RES_TAC THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
         MATCH_MP_TAC labels_rel_APPEND THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         MATCH_MP_TAC labels_rel_CONS THEN ASM_REWRITE_TAC[labels_rel_refl] THEN NO_TAC;
         MATCH_MP_TAC WPROOF2AUX_wc_labels_rel_app1 THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         MATCH_MP_TAC WPROOF2AUX_wc_labels_rel_app2 THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         FIRST_ASSUM MATCH_MP_TAC THEN MESON_TAC[PAIR]];;

let extract_labels_const_fp_loop = prove
 (`!p (cs:(A word)spt) p1 cs1.
     const_fp_loop p cs = (p1,cs1) ==>
     labels_rel (wordConvs_extract_labels p) (wordConvs_extract_labels p1)`,
  MATCH_MP_TAC const_fp_loop_ind THEN REPEAT CONJ_TAC THEN
  WPROOF2AUX_wc_IH_TAC "const_fp_loop" THEN TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [const_fp_loop_def] THEN
  CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  DISCH_THEN(CAKE_STRIP_ASSUME_TAC o CAKE_SIMP_RULE(PAIR_EQ :: WPROOF2AUX_wc_ceqs)) THEN
  RVEQ_TAC THEN
  REWRITE_TAC[wordConvs_extract_labels_def; extract_labels_drop_consts; labels_rel_refl;
              extract_labels_SmartSeq] THEN
  WPROOF2AUX_wc_LABELS_FIN_TAC);;

let extract_labels_const_fp = prove
 (`labels_rel (wordConvs_extract_labels p)
              (wordConvs_extract_labels (const_fp (p:(A)wl_prog)))`,
  REWRITE_TAC[const_fp_def] THEN
  MP_TAC(ISPECL [`p:(A)wl_prog`; `LN:(A word)spt`] extract_labels_const_fp_loop) THEN
  MESON_TAC[PAIR]);;

let labels_rel_append_imp = prove
 (`labels_rel (APPEND Y X) (Z:(num#num)list) ==> labels_rel (APPEND X Y) Z`,
  MESON_TAC[PERM_APPEND; labels_rel_TRANS; PERM_IMP_labels_rel]);;

(* ------------------------------------------------------------------------- *)
(* HOL4 try_cancel_labels_rel_append (an ML tactic) is not ported: the     *)
(* rearrangements are done by the helpers below.                            *)
(* ------------------------------------------------------------------------- *)

let WPROOF2AUX_pair_CASE_FST_SND = prove
 (`!(p:A#B) (f:A->B->C). pair_CASE p f = f (FST p) (SND p)`,
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE]);;

let WPROOF2AUX_cfl_Seq = prove
 (`!p1 p2 (cs:(A word)spt).
     const_fp_loop (wl_Seq p1 p2) cs =
     (wl_Seq (FST (const_fp_loop p1 cs))
             (FST (const_fp_loop p2 (SND (const_fp_loop p1 cs)))),
      SND (const_fp_loop p2 (SND (const_fp_loop p1 cs))))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [const_fp_loop_def] THEN
  REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND]);;

let WPROOF2AUX_cfl_If_LN = prove
 (`!cmp l r p1 (p2:(A)wl_prog).
     const_fp_loop (wl_If cmp l r p1 p2) LN =
     (wl_If cmp l r (FST (const_fp_loop p1 LN)) (FST (const_fp_loop p2 LN)),
      inter_eq (SND (const_fp_loop p1 LN)) (SND (const_fp_loop p2 LN)))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [const_fp_loop_def] THEN
  REWRITE_TAC[lookup_def] THEN CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND]);;

let WPROOF2AUX_labels_rel_NIL = prove
 (`!ys:A list. labels_rel [] ys <=> ys = []`,
  GEN_TAC THEN
  REWRITE_TAC[labels_rel_def; ALL_DISTINCT; set_of_list; SUBSET_EMPTY;
              SET_OF_LIST_EQ_EMPTY] THEN
  EQ_TAC THEN SIMP_TAC[ALL_DISTINCT]);;

let WPROOF2AUX_el_cfl_FST = prove
 (`!p (cs:(A word)spt).
     labels_rel (wordConvs_extract_labels p)
                (wordConvs_extract_labels (FST (const_fp_loop p cs)))`,
  MESON_TAC[extract_labels_const_fp_loop; PAIR]);;

let WPROOF2AUX_el_cfl_NIL = prove
 (`!p (cs:(A word)spt).
     wordConvs_extract_labels p = [] ==>
     wordConvs_extract_labels (FST (const_fp_loop p cs)) = []`,
  MESON_TAC[WPROOF2AUX_el_cfl_FST; WPROOF2AUX_labels_rel_NIL]);;

let WPROOF2AUX_labels_rel_mid1 = prove
 (`!a b c d:A list.
     labels_rel (APPEND (APPEND a b) (APPEND c d)) (APPEND (APPEND a c) (APPEND b d))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC PERM_IMP_labels_rel THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; PERM_APPEND_IFF] THEN
  REWRITE_TAC[APPEND_ASSOC; PERM_APPEND_IFF; PERM_APPEND]);;

let WPROOF2AUX_labels_rel_mid2 = prove
 (`!a b c d:A list.
     labels_rel (APPEND (APPEND a b) (APPEND c d)) (APPEND (APPEND a d) (APPEND b c))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC PERM_IMP_labels_rel THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; PERM_APPEND_IFF] THEN
  GEN_REWRITE_TAC RAND_CONV [APPEND_ASSOC] THEN
  MATCH_ACCEPT_TAC PERM_APPEND);;

(* const_fp_loop_Seq: the clauses of const_fp_loop_def that *)
(* mention Seq                                                               *)
let const_fp_loop_Seq =
  end_itlist CONJ
    (filter (fun th -> can (find_term (fun t -> is_const t &&
                                       fst(dest_const t) = "wl_Seq")) (concl th))
            (CONJUNCTS const_fp_loop_def));;

let const_fp_loop_dummy_cases = prove
 (`const_fp_loop (wl_If cmp lhs rhs (wl_Raise 1) (wl_Raise 2)) (cs:(A word)spt) =
     (p2,cs2) ==>
   (dest_Raise_num p2 = 1 /\
    (!br1 br2. const_fp_loop (wl_If cmp lhs rhs br1 br2) cs = const_fp_loop br1 cs)) \/
   (dest_Raise_num p2 = 2 /\
    (!br1 br2. const_fp_loop (wl_If cmp lhs rhs br1 br2) cs = const_fp_loop br2 cs)) \/
   (dest_Raise_num p2 = 0)`,
  REWRITE_TAC[const_fp_loop_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  CASE_REWRITE_TAC[dest_Raise_num_def; ARITH_EQ] THEN ASM_REWRITE_TAC[]);;

let wordConvsProof_dest_If_thm = prove
 (`dest_If (x2:(A)wl_prog) = SOME (g1,g2,g3,g4,g5) <=> x2 = wl_If g1 g2 g3 g4 g5`,
  STRUCT_CASES_TAC (ISPEC `x2:(A)wl_prog` (nchotomy_of_type `:(A)wl_prog`)) THEN
  REWRITE_TAC[dest_If_def; option_DISTINCT; option_INJ; PAIR_EQ;
              distinctness "wl_prog"; injectivity "wl_prog"]);;

(* one branch of the hoisted If: the dummy If decides it                     *)

let WPROOF2AUX_hoist_branch = prove
 (`!b interm cmp lhs rhs br1 br2 (k:num).
     wordConvs_extract_labels (interm:(A)wl_prog) = [] /\
     dest_Raise_num (SND (word_simp_dest_Seq (const_fp
       (wl_Seq (wl_Seq b interm) (wl_If cmp lhs rhs (wl_Raise 1) (wl_Raise 2)))))) = k /\
     ~(k = 0)
     ==> (k = 1 /\
          labels_rel (APPEND (wordConvs_extract_labels b) (wordConvs_extract_labels br1))
            (wordConvs_extract_labels (FST (const_fp_loop
               (wl_Seq (wl_Seq b interm) (wl_If cmp lhs rhs br1 br2)) LN)))) \/
         (k = 2 /\
          labels_rel (APPEND (wordConvs_extract_labels b) (wordConvs_extract_labels br2))
            (wordConvs_extract_labels (FST (const_fp_loop
               (wl_Seq (wl_Seq b interm) (wl_If cmp lhs rhs br1 br2)) LN))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[const_fp_def; WPROOF2AUX_cfl_Seq; word_simp_dest_Seq_def; FST; SND] THEN
  ABBREV_TAC `cs1 = SND (const_fp_loop interm (SND (const_fp_loop b (LN:(A word)spt))))` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `k:num`)) THEN
  MP_TAC(MATCH_MP const_fp_loop_dummy_cases
    (GSYM(ISPEC `const_fp_loop (wl_If cmp lhs rhs (wl_Raise 1) (wl_Raise 2):(A)wl_prog)
                                (cs1:(A word)spt)` PAIR))) THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC];
    DISJ2_TAC THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC];
    ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) then REWRITE_TAC[th] else failwith "") THEN
  REWRITE_TAC[wordConvs_extract_labels_def] THEN
  ASM_SIMP_TAC[WPROOF2AUX_el_cfl_NIL; APPEND_NIL] THEN
  MATCH_MP_TAC labels_rel_APPEND THEN REWRITE_TAC[WPROOF2AUX_el_cfl_FST]);;

(* the hoisted If: one branch takes br1 and the other br2                    *)

let WPROOF2AUX_hoist_core = prove
 (`!b1 b2 interm cmp lhs rhs br1 br2 c' l' r'.
     wordConvs_extract_labels (interm:(A)wl_prog) = [] /\
     ~(dest_Raise_num (SND (word_simp_dest_Seq (const_fp
         (wl_Seq (wl_Seq b1 interm) (wl_If cmp lhs rhs (wl_Raise 1) (wl_Raise 2)))))) = 0) /\
     dest_Raise_num (SND (word_simp_dest_Seq (const_fp
         (wl_Seq (wl_Seq b1 interm) (wl_If cmp lhs rhs (wl_Raise 1) (wl_Raise 2)))))) +
     dest_Raise_num (SND (word_simp_dest_Seq (const_fp
         (wl_Seq (wl_Seq b2 interm) (wl_If cmp lhs rhs (wl_Raise 1) (wl_Raise 2)))))) = 3
     ==> labels_rel
           (APPEND (APPEND (wordConvs_extract_labels b1) (wordConvs_extract_labels b2))
                   (APPEND (wordConvs_extract_labels br1) (wordConvs_extract_labels br2)))
           (wordConvs_extract_labels (const_fp (wl_If c' l' r'
              (wl_Seq (wl_Seq b1 interm) (wl_If cmp lhs rhs br1 br2))
              (wl_Seq (wl_Seq b2 interm) (wl_If cmp lhs rhs br1 br2)))))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `k1 = dest_Raise_num (SND (word_simp_dest_Seq (const_fp
     (wl_Seq (wl_Seq b1 interm) (wl_If cmp lhs rhs (wl_Raise 1) (wl_Raise 2)):(A)wl_prog))))` THEN
  ABBREV_TAC `k2 = dest_Raise_num (SND (word_simp_dest_Seq (const_fp
     (wl_Seq (wl_Seq b2 interm) (wl_If cmp lhs rhs (wl_Raise 1) (wl_Raise 2)):(A)wl_prog))))` THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`b1:(A)wl_prog`; `interm:(A)wl_prog`; `cmp:cmp`; `lhs:num`;
                `rhs:(A)reg_imm`; `br1:(A)wl_prog`; `br2:(A)wl_prog`; `k1:num`]
               WPROOF2AUX_hoist_branch) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (MP_TAC(SPECL [`b2:(A)wl_prog`; `interm:(A)wl_prog`; `cmp:cmp`; `lhs:num`;
                 `rhs:(A)reg_imm`; `br1:(A)wl_prog`; `br2:(A)wl_prog`; `k2:num`]
                WPROOF2AUX_hoist_branch) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC) THEN
  TRY (FIRST_ASSUM(fun th -> if is_eq(concl th) && is_numeral(rhs(concl th))
                                then ALL_TAC else failwith "") THEN
       ASM_ARITH_TAC THEN NO_TAC) THEN
  REWRITE_TAC[const_fp_def; WPROOF2AUX_cfl_If_LN; wordConvs_extract_labels_def] THEN
  MATCH_MP_TAC labels_rel_TRANS THENL
   [EXISTS_TAC `APPEND (APPEND (wordConvs_extract_labels (b1:(A)wl_prog))
                               (wordConvs_extract_labels (br1:(A)wl_prog)))
                       (APPEND (wordConvs_extract_labels (b2:(A)wl_prog))
                               (wordConvs_extract_labels (br2:(A)wl_prog)))` THEN
    REWRITE_TAC[WPROOF2AUX_labels_rel_mid1];
    EXISTS_TAC `APPEND (APPEND (wordConvs_extract_labels (b1:(A)wl_prog))
                               (wordConvs_extract_labels (br2:(A)wl_prog)))
                       (APPEND (wordConvs_extract_labels (b2:(A)wl_prog))
                               (wordConvs_extract_labels (br1:(A)wl_prog)))` THEN
    REWRITE_TAC[WPROOF2AUX_labels_rel_mid2]] THEN
  MATCH_MP_TAC labels_rel_APPEND THEN ASM_REWRITE_TAC[]);;

let WPROOF2AUX_is_simple_el = prove
 (`!p:(A)wl_prog. is_simple p ==> wordConvs_extract_labels p = []`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `p:(A)wl_prog` (nchotomy_of_type `:(A)wl_prog`)) THEN
  CASE_REWRITE_TAC[is_simple_def; wordConvs_extract_labels_def]);;

let WPROOF2AUX_dest_If_cases = prove
 (`!p:(A)wl_prog. dest_If p = NONE \/ ?c l r q1 q2. p = wl_If c l r q1 q2`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `p:(A)wl_prog` (nchotomy_of_type `:(A)wl_prog`)) THEN
  REWRITE_TAC[dest_If_def; distinctness "wl_prog"; injectivity "wl_prog"] THEN MESON_TAC[]);;

let labels_rel_hoist2 = prove
 (`!N p1 interm dummy (p2:(A)wl_prog) (s:B).
     try_if_hoist2 N p1 interm dummy p2 = SOME p3 ==>
     dest_If p2 = SOME (cmp, lhs, rhs, br1, br2) ==>
     dummy = wl_If cmp lhs rhs (wl_Raise 1) (wl_Raise 2) ==>
     wordConvs_extract_labels interm = [] ==>
     labels_rel (APPEND (wordConvs_extract_labels p1) (wordConvs_extract_labels p2))
                (wordConvs_extract_labels p3)`,
  REWRITE_TAC[FORALL_SIMP] THEN
  MATCH_MP_TAC try_if_hoist2_ind THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `p1:(A)wl_prog`; `interm:(A)wl_prog`; `dummy:(A)wl_prog`;
                       `p2:(A)wl_prog`] THEN
  STRUCT_CASES_TAC (ISPEC `p1:(A)wl_prog` (nchotomy_of_type `:(A)wl_prog`)) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[distinctness "wl_prog"; injectivity "wl_prog"]) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [try_if_hoist2_def] THEN
  REWRITE_TAC[wordConvsProof_dest_If_thm] THEN
  DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `N = 0` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN CASE_REWRITE_TAC[option_DISTINCT] THENL
   [(* p1 = Seq a0 a1 *)
    DISJ_CASES_THEN2 (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th])
      (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      (SPEC `a1:(A)wl_prog` WPROOF2AUX_dest_If_cases) THEN
    CASE_REWRITE_TAC[dest_If_def; LET_DEF; LET_END_DEF] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_TAC THENL
     [(* a1 is simple: the induction hypothesis *)
      FIRST_X_ASSUM(MP_TAC o SPECL [`a0:(A)wl_prog`; `a1:(A)wl_prog`]) THEN
      ASM_SIMP_TAC[dest_If_def; wordConvs_extract_labels_def; WPROOF2AUX_is_simple_el;
                   APPEND_NIL; APPEND];
      (* a1 is an If: hoisted *)
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_var(rhs(concl th)))) THEN
      REWRITE_TAC[wordConvs_extract_labels_def] THEN
      MATCH_MP_TAC labels_rel_TRANS THEN
      EXISTS_TAC `APPEND (wordConvs_extract_labels (a0:(A)wl_prog))
                    (APPEND (APPEND (wordConvs_extract_labels (q1:(A)wl_prog))
                                    (wordConvs_extract_labels (q2:(A)wl_prog)))
                            (APPEND (wordConvs_extract_labels (br1:(A)wl_prog))
                                    (wordConvs_extract_labels (br2:(A)wl_prog))))` THEN
      CONJ_TAC THENL [REWRITE_TAC[APPEND_ASSOC; labels_rel_refl]; ALL_TAC] THEN
      MATCH_MP_TAC labels_rel_APPEND THEN REWRITE_TAC[labels_rel_refl] THEN
      MATCH_MP_TAC WPROOF2AUX_hoist_core THEN ASM_REWRITE_TAC[]];
    (* p1 = If a0 a1 a2 a3 a4: hoisted *)
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[wordConvs_extract_labels_def] THEN
    MATCH_MP_TAC WPROOF2AUX_hoist_core THEN ASM_REWRITE_TAC[]]);;
(* decompose labels_rel of two lists of the same APPEND/CONS shape          *)

let WPROOF2AUX_wc_LR_TAC : tactic =
  REPEAT (FIRST [MATCH_ACCEPT_TAC labels_rel_refl; FIRST_ASSUM ACCEPT_TAC;
                 MATCH_MP_TAC labels_rel_APPEND THEN CONJ_TAC;
                 MATCH_MP_TAC labels_rel_CONS THEN CONJ_TAC]);;

let WPROOF2AUX_hoist2_gen = prove
 (`!N p1 interm cmp lhs rhs br1 br2 (p3:(A)wl_prog).
     try_if_hoist2 N p1 interm (wl_If cmp lhs rhs (wl_Raise 1) (wl_Raise 2))
       (wl_If cmp lhs rhs br1 br2) = SOME p3 /\
     wordConvs_extract_labels interm = []
     ==> labels_rel
           (APPEND (wordConvs_extract_labels p1)
                   (APPEND (wordConvs_extract_labels br1) (wordConvs_extract_labels br2)))
           (wordConvs_extract_labels p3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`N:num`; `p1:(A)wl_prog`; `interm:(A)wl_prog`;
                 `wl_If cmp lhs rhs (wl_Raise 1) (wl_Raise 2):(A)wl_prog`;
                 `wl_If cmp lhs rhs br1 br2:(A)wl_prog`; `0`] labels_rel_hoist2) THEN
  ASM_REWRITE_TAC[dest_If_def; wordConvs_extract_labels_def]);;

let labels_rel_simp_duplicate_if = prove
 (`!p:(A)wl_prog.
     labels_rel (wordConvs_extract_labels p)
                (wordConvs_extract_labels (simp_duplicate_if p))`,
  MATCH_MP_TAC simp_duplicate_if_ind THEN GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [simp_duplicate_if_def] THEN
  CASES_ON `p:(A)wl_prog` THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  REWRITE_TAC[wordConvs_extract_labels_def; labels_rel_refl] THEN
  CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  TRY (WPROOF2AUX_wc_LR_TAC THEN NO_TAC) THEN
  (* Seq *)
  MP_TAC(ISPEC `try_if_hoist1 (simp_duplicate_if a0) (simp_duplicate_if (a1:(A)wl_prog))`
               (nchotomy_of_type `:((A)wl_prog)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[wordConvs_extract_labels_def; extract_labels_Seq_assoc] THENL
   [WPROOF2AUX_wc_LR_TAC; ALL_TAC] THEN
  MATCH_MP_TAC labels_rel_TRANS THEN
  EXISTS_TAC `APPEND (wordConvs_extract_labels (simp_duplicate_if (a0:(A)wl_prog)))
                     (wordConvs_extract_labels (simp_duplicate_if (a1:(A)wl_prog)))` THEN
  CONJ_TAC THENL [WPROOF2AUX_wc_LR_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_comb(rhs(concl th)))) THEN
  REWRITE_TAC[try_if_hoist1_def] THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[option_DISTINCT])
    (REPEAT_TCL CHOOSE_THEN (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))
    (SPEC `simp_duplicate_if (a1:(A)wl_prog)` WPROOF2AUX_dest_If_cases) THEN
  CASE_REWRITE_TAC[dest_If_def; LET_DEF; LET_END_DEF] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`rewrite_duplicate_if_max_reassoc`; `simp_duplicate_if (a0:(A)wl_prog)`;
                 `wl_Skip:(A)wl_prog`; `c:cmp`; `l:num`; `r:(A)reg_imm`;
                 `q1:(A)wl_prog`; `q2:(A)wl_prog`; `a:(A)wl_prog`] WPROOF2AUX_hoist2_gen) THEN
  ASM_REWRITE_TAC[wordConvs_extract_labels_def]);;
let WPROOF2AUX_FORALL_PAIR_EQ_IMP = prove
 (`!(t:A#B) (Q:A->B->bool). (!x y. t = (x,y) ==> Q x y) <=> Q (FST t) (SND t)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

let WPROOF2AUX_push_out_if_aux_labels = prove
 (`!p:(A)wl_prog.
     labels_rel (wordConvs_extract_labels p)
                (wordConvs_extract_labels (FST (push_out_if_aux p)))`,
  MATCH_MP_TAC push_out_if_aux_ind THEN GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [push_out_if_aux_def] THEN
  CASES_ON `p:(A)wl_prog` THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ; WPROOF2AUX_FORALL_PAIR_EQ_IMP]) THEN
  TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND] THEN
  REPEAT COND_CASES_TAC THEN RES_TAC THEN
  REWRITE_TAC[FST; SND; wordConvs_extract_labels_def; labels_rel_refl; APPEND; APPEND_NIL] THEN
  TRY (WPROOF2AUX_wc_LR_TAC THEN NO_TAC) THEN
  MATCH_MP_TAC labels_rel_append_imp THEN WPROOF2AUX_wc_LR_TAC);;

let labels_rel_push_out_if = prove
 (`!p:(A)wl_prog.
     labels_rel (wordConvs_extract_labels p) (wordConvs_extract_labels (push_out_if p))`,
  REWRITE_TAC[push_out_if_def; WPROOF2AUX_push_out_if_aux_labels]);;

let extract_labels_compile_exp = prove
 (`!p:(A)wl_prog.
     labels_rel (wordConvs_extract_labels p)
                (wordConvs_extract_labels (word_simp_compile_exp p))`,
  GEN_TAC THEN REWRITE_TAC[word_simp_compile_exp_def; LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC labels_rel_TRANS THEN
  EXISTS_TAC `wordConvs_extract_labels
                (simp_duplicate_if (const_fp (Seq_assoc wl_Skip (p:(A)wl_prog))))` THEN
  REWRITE_TAC[labels_rel_push_out_if] THEN
  MATCH_MP_TAC labels_rel_TRANS THEN
  EXISTS_TAC `wordConvs_extract_labels (const_fp (Seq_assoc wl_Skip (p:(A)wl_prog)))` THEN
  REWRITE_TAC[labels_rel_simp_duplicate_if] THEN
  MATCH_MP_TAC labels_rel_TRANS THEN
  EXISTS_TAC `wordConvs_extract_labels (Seq_assoc wl_Skip (p:(A)wl_prog))` THEN
  CONJ_TAC THENL [REWRITE_TAC[extract_labels_Seq_assoc; labels_rel_refl];
                  MATCH_ACCEPT_TAC extract_labels_const_fp]);;
(* ------------------------------------------------------------------------- *)
(* inst_ok_less                                                              *)
(* ------------------------------------------------------------------------- *)

let dest_Seq_no_inst = prove
 (`!prog:(A)wl_prog.
     every_inst P prog ==>
     every_inst P (FST (word_simp_dest_Seq prog)) /\
     every_inst P (SND (word_simp_dest_Seq prog))`,
  GEN_TAC THEN CASES_ON `prog:(A)wl_prog` THEN
  CASE_REWRITE_TAC[word_simp_dest_Seq_def; every_inst_def; FST; SND] THEN
  MESON_TAC[]);;

let wordConvsProof_Seq_assoc_no_inst = prove
 (`!p1 p2:(A)wl_prog.
     every_inst P p1 /\ every_inst P p2 ==> every_inst P (Seq_assoc p1 p2)`,
  MATCH_MP_TAC word_simp_Seq_assoc_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  REWRITE_TAC[word_simp_Seq_assoc_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[SmartSeq_def] THEN REPEAT COND_CASES_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[every_inst_def]) THEN
  ASM_SIMP_TAC[every_inst_def] THEN CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[]);;

let every_inst_SmartSeq = prove
 (`every_inst P (SmartSeq p q:(A)wl_prog) <=> every_inst P p /\ every_inst P q`,
  REWRITE_TAC[SmartSeq_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[every_inst_def]);;

let every_inst_drop_consts = prove
 (`every_inst P (SmartSeq (drop_consts (cs:(A word)spt) ls) p) <=> every_inst P p`,
  REWRITE_TAC[every_inst_SmartSeq] THEN
  SUBGOAL_THEN `every_inst P (drop_consts (cs:(A word)spt) ls)`
    (fun th -> REWRITE_TAC[th]) THEN
  SPEC_TAC(`ls:num list`,`ls:num list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[drop_consts_def; every_inst_def] THEN
  REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_REWRITE_TAC[every_inst_SmartSeq; every_inst_def]);;

let _ = cake_add_simps [every_inst_drop_consts];;

let WPROOF2AUX_every_inst_cfl = prove
 (`!p (cs:(A word)spt) p1 cs1.
     const_fp_loop p cs = (p1,cs1) ==> every_inst P p ==> every_inst P p1`,
  MATCH_MP_TAC const_fp_loop_ind THEN REPEAT CONJ_TAC THEN
  WPROOF2AUX_wc_IH_TAC "const_fp_loop" THEN TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [const_fp_loop_def] THEN
  CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  DISCH_THEN(CAKE_STRIP_ASSUME_TAC o CAKE_SIMP_RULE(PAIR_EQ :: WPROOF2AUX_wc_ceqs)) THEN
  RVEQ_TAC THEN
  REWRITE_TAC[every_inst_def; every_inst_drop_consts; every_inst_SmartSeq] THEN
  CASE_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PAIR]);;

let every_inst_const_fp = prove
 (`!prog:(A)wl_prog. every_inst P prog ==> every_inst P (const_fp prog)`,
  REWRITE_TAC[const_fp_def] THEN MESON_TAC[WPROOF2AUX_every_inst_cfl; PAIR]);;
let try_if_hoist2_no_inst = prove
 (`!N p1 interm dummy (p2:(A)wl_prog) (s:B).
     try_if_hoist2 N p1 interm dummy p2 = SOME p3 ==>
     every_inst P p1 ==>
     every_inst P interm ==>
     every_inst P p2 ==>
     every_inst P p3`,
  REWRITE_TAC[FORALL_SIMP] THEN
  MATCH_MP_TAC try_if_hoist2_ind THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `p1:(A)wl_prog`; `interm:(A)wl_prog`; `dummy:(A)wl_prog`;
                       `p2:(A)wl_prog`] THEN
  STRUCT_CASES_TAC (ISPEC `p1:(A)wl_prog` (nchotomy_of_type `:(A)wl_prog`)) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[distinctness "wl_prog"; injectivity "wl_prog"]) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [try_if_hoist2_def] THEN
  ASM_CASES_TAC `N = 0` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  CASE_REWRITE_TAC[option_DISTINCT] THENL
   [(* p1 = Seq a0 a1 *)
    DISJ_CASES_THEN2 (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th])
      (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      (SPEC `a1:(A)wl_prog` WPROOF2AUX_dest_If_cases) THEN
    CASE_REWRITE_TAC[dest_If_def; LET_DEF; LET_END_DEF] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`a0:(A)wl_prog`; `a1:(A)wl_prog`]) THEN
      ASM_REWRITE_TAC[every_inst_def] THEN MESON_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[every_inst_def] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC every_inst_const_fp THEN
      ASM_REWRITE_TAC[every_inst_def]];
    (* p1 = If a0 a1 a2 a3 a4 *)
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[every_inst_def] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC every_inst_const_fp THEN
    ASM_REWRITE_TAC[every_inst_def]]);;

let simp_duplicate_if_no_inst = prove
 (`!p:(A)wl_prog. every_inst P p ==> every_inst P (simp_duplicate_if p)`,
  MATCH_MP_TAC simp_duplicate_if_ind THEN GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [simp_duplicate_if_def] THEN
  CASES_ON `p:(A)wl_prog` THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  CASE_REWRITE_TAC[every_inst_def; LET_DEF; LET_END_DEF] THEN
  TRY (REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  (* Seq *)
  STRIP_TAC THEN RES_TAC THEN
  MP_TAC(ISPEC `try_if_hoist1 (simp_duplicate_if a0) (simp_duplicate_if (a1:(A)wl_prog))`
               (nchotomy_of_type `:((A)wl_prog)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[every_inst_def] THEN
  TRY (ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  MATCH_MP_TAC wordConvsProof_Seq_assoc_no_inst THEN REWRITE_TAC[every_inst_def] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_comb(rhs(concl th)) &&
                                          is_const(rator(rhs(concl th))))) THEN
  REWRITE_TAC[try_if_hoist1_def] THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[option_DISTINCT])
    (REPEAT_TCL CHOOSE_THEN (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))
    (SPEC `simp_duplicate_if (a1:(A)wl_prog)` WPROOF2AUX_dest_If_cases) THEN
  CASE_REWRITE_TAC[dest_If_def; LET_DEF; LET_END_DEF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP try_if_hoist2_no_inst) THEN
  ASM_MESON_TAC[every_inst_def]);;
let simp_push_out_if_no_inst = prove
 (`!p:(A)wl_prog. every_inst P p ==> every_inst P (push_out_if p)`,
  REWRITE_TAC[push_out_if_def] THEN
  MATCH_MP_TAC push_out_if_aux_ind THEN GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [push_out_if_aux_def] THEN
  CASES_ON `p:(A)wl_prog` THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ; WPROOF2AUX_FORALL_PAIR_EQ_IMP]) THEN
  TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[FST; SND; every_inst_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);;

let compile_exp_no_inst = prove
 (`!prog:(A)wl_prog. every_inst P prog ==> every_inst P (word_simp_compile_exp prog)`,
  GEN_TAC THEN REWRITE_TAC[word_simp_compile_exp_def; LET_DEF; LET_END_DEF] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC simp_push_out_if_no_inst THEN MATCH_MP_TAC simp_duplicate_if_no_inst THEN
  MATCH_MP_TAC every_inst_const_fp THEN MATCH_MP_TAC wordConvsProof_Seq_assoc_no_inst THEN
  ASM_REWRITE_TAC[every_inst_def]);;
(* ------------------------------------------------------------------------- *)
(* not_created_subprogs                                                      *)
(* ------------------------------------------------------------------------- *)

let not_created_subprogs_SmartSeq = prove
 (`not_created_subprogs P (SmartSeq p1 p2:(A)wl_prog) <=>
   not_created_subprogs P p1 /\ not_created_subprogs P p2`,
  REWRITE_TAC[SmartSeq_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[not_created_subprogs_def]);;

let not_created_subprogs_Seq_assoc = prove
 (`!p1 p2:(A)wl_prog.
     not_created_subprogs P (Seq_assoc p1 p2) <=>
     not_created_subprogs P p1 /\ not_created_subprogs P p2`,
  MATCH_MP_TAC word_simp_Seq_assoc_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[not_created_subprogs_def]) THEN
  ASM_REWRITE_TAC[word_simp_Seq_assoc_def; not_created_subprogs_SmartSeq] THEN
  CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[not_created_subprogs_def; not_created_subprogs_SmartSeq] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[CONJ_ASSOC] THEN
  REWRITE_TAC[CONJ_ACI]);;
let not_created_subprogs_drop_consts = prove
 (`not_created_subprogs P (SmartSeq (drop_consts (cs:(A word)spt) ls) p) <=>
   not_created_subprogs P p`,
  REWRITE_TAC[not_created_subprogs_SmartSeq] THEN
  SUBGOAL_THEN `not_created_subprogs P (drop_consts (cs:(A word)spt) ls)`
    (fun th -> REWRITE_TAC[th]) THEN
  SPEC_TAC(`ls:num list`,`ls:num list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[drop_consts_def; not_created_subprogs_def] THEN
  REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_REWRITE_TAC[not_created_subprogs_SmartSeq; not_created_subprogs_def]);;

let _ = cake_add_simps [not_created_subprogs_drop_consts];;

let not_created_subprogs_const_fp_loop = prove
 (`!p (cs:(A word)spt) p1 cs1.
     const_fp_loop p cs = (p1,cs1) ==>
     not_created_subprogs P p ==>
     not_created_subprogs P p1`,
  MATCH_MP_TAC const_fp_loop_ind THEN REPEAT CONJ_TAC THEN
  WPROOF2AUX_wc_IH_TAC "const_fp_loop" THEN TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [const_fp_loop_def] THEN
  CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  DISCH_THEN(CAKE_STRIP_ASSUME_TAC o CAKE_SIMP_RULE(PAIR_EQ :: WPROOF2AUX_wc_ceqs)) THEN
  RVEQ_TAC THEN
  REWRITE_TAC[not_created_subprogs_def; not_created_subprogs_drop_consts;
              not_created_subprogs_SmartSeq] THEN
  CASE_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PAIR]);;

let not_created_subprogs_const_fp = prove
 (`not_created_subprogs P (p:(A)wl_prog) ==> not_created_subprogs P (const_fp p)`,
  REWRITE_TAC[const_fp_def] THEN MESON_TAC[not_created_subprogs_const_fp_loop; PAIR]);;

let not_created_subprogs_hoist2 = prove
 (`!N p1 interm dummy (p2:(A)wl_prog).
     try_if_hoist2 N p1 interm dummy p2 = SOME p3 ==>
     not_created_subprogs P p1 ==> not_created_subprogs P interm ==>
     not_created_subprogs P p2 ==>
     not_created_subprogs P p3`,
  MATCH_MP_TAC try_if_hoist2_ind THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `p1:(A)wl_prog`; `interm:(A)wl_prog`; `dummy:(A)wl_prog`;
                       `p2:(A)wl_prog`] THEN
  STRUCT_CASES_TAC (ISPEC `p1:(A)wl_prog` (nchotomy_of_type `:(A)wl_prog`)) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[distinctness "wl_prog"; injectivity "wl_prog"]) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [try_if_hoist2_def] THEN
  ASM_CASES_TAC `N = 0` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  CASE_REWRITE_TAC[option_DISTINCT] THENL
   [(* p1 = Seq a0 a1 *)
    DISJ_CASES_THEN2 (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th])
      (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      (SPEC `a1:(A)wl_prog` WPROOF2AUX_dest_If_cases) THEN
    CASE_REWRITE_TAC[dest_If_def; LET_DEF; LET_END_DEF] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`a0:(A)wl_prog`; `a1:(A)wl_prog`]) THEN
      ASM_REWRITE_TAC[not_created_subprogs_def] THEN MESON_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[not_created_subprogs_def] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC not_created_subprogs_const_fp THEN
      ASM_REWRITE_TAC[not_created_subprogs_def]];
    (* p1 = If a0 a1 a2 a3 a4 *)
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[not_created_subprogs_def] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC not_created_subprogs_const_fp THEN
    ASM_REWRITE_TAC[not_created_subprogs_def]]);;

let not_created_subprogs_simp_duplicate_if = prove
 (`!p:(A)wl_prog.
     not_created_subprogs P p ==> not_created_subprogs P (simp_duplicate_if p)`,
  MATCH_MP_TAC simp_duplicate_if_ind THEN GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [simp_duplicate_if_def] THEN
  CASES_ON `p:(A)wl_prog` THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  CASE_REWRITE_TAC[not_created_subprogs_def; LET_DEF; LET_END_DEF] THEN
  TRY (REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  (* Seq *)
  STRIP_TAC THEN RES_TAC THEN
  MP_TAC(ISPEC `try_if_hoist1 (simp_duplicate_if a0) (simp_duplicate_if (a1:(A)wl_prog))`
               (nchotomy_of_type `:((A)wl_prog)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[not_created_subprogs_def] THEN
  TRY (ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  REWRITE_TAC[not_created_subprogs_Seq_assoc; not_created_subprogs_def] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_comb(rhs(concl th)) &&
                                          is_const(rator(rhs(concl th))))) THEN
  REWRITE_TAC[try_if_hoist1_def] THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[option_DISTINCT])
    (REPEAT_TCL CHOOSE_THEN (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))
    (SPEC `simp_duplicate_if (a1:(A)wl_prog)` WPROOF2AUX_dest_If_cases) THEN
  CASE_REWRITE_TAC[dest_If_def; LET_DEF; LET_END_DEF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP not_created_subprogs_hoist2) THEN
  ASM_MESON_TAC[not_created_subprogs_def]);;

let WPROOF2AUX_ncs_push_out_if_aux = prove
 (`!p:(A)wl_prog.
     not_created_subprogs P (FST (push_out_if_aux p)) <=> not_created_subprogs P p`,
  MATCH_MP_TAC push_out_if_aux_ind THEN GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [push_out_if_aux_def] THEN
  CASES_ON `p:(A)wl_prog` THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ; WPROOF2AUX_FORALL_PAIR_EQ_IMP]) THEN
  TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[FST; SND; not_created_subprogs_def] THEN CASE_REWRITE_TAC[] THEN
  RES_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[CONJ_ACI]);;

let not_created_subprogs_push_out_if = prove
 (`!p:(A)wl_prog.
     not_created_subprogs P (push_out_if p) <=> not_created_subprogs P p`,
  REWRITE_TAC[push_out_if_def; WPROOF2AUX_ncs_push_out_if_aux]);;

let compile_exp_not_created_subprogs = prove
 (`not_created_subprogs P (p:(A)wl_prog) ==>
   not_created_subprogs P (word_simp_compile_exp p)`,
  REWRITE_TAC[word_simp_compile_exp_def; LET_DEF; LET_END_DEF;
              not_created_subprogs_push_out_if] THEN
  DISCH_TAC THEN MATCH_MP_TAC not_created_subprogs_simp_duplicate_if THEN
  MATCH_MP_TAC not_created_subprogs_const_fp THEN
  ASM_REWRITE_TAC[not_created_subprogs_Seq_assoc; not_created_subprogs_def]);;
(* ------------------------------------------------------------------------- *)
(* get_code_labels and good_handlers                                         *)
(* ------------------------------------------------------------------------- *)

let word_get_code_labels_SmartSeq = prove
 (`wordConvs_get_code_labels (SmartSeq p q:(A)wl_prog) =
   wordConvs_get_code_labels p UNION wordConvs_get_code_labels q`,
  REWRITE_TAC[SmartSeq_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[wordConvs_get_code_labels_def; UNION_EMPTY]);;

let _ = cake_add_simps [word_get_code_labels_SmartSeq];;

let word_get_code_labels_drop_consts = prove
 (`!args. wordConvs_get_code_labels (drop_consts (l:(A word)spt) args) = {}`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[drop_consts_def; wordConvs_get_code_labels_def] THEN
  REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_REWRITE_TAC[word_get_code_labels_SmartSeq; wordConvs_get_code_labels_def;
                  UNION_EMPTY]);;

let _ = cake_add_simps [word_get_code_labels_drop_consts];;

(* the start of an induction over const_fp_loop p cs = (p1,cs1)             *)

let WPROOF2AUX_wc_CFL_TAC : tactic =
  MATCH_MP_TAC const_fp_loop_ind THEN REPEAT CONJ_TAC THEN
  WPROOF2AUX_wc_IH_TAC "const_fp_loop" THEN TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [const_fp_loop_def] THEN
  CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  DISCH_THEN(CAKE_STRIP_ASSUME_TAC o CAKE_SIMP_RULE(PAIR_EQ :: WPROOF2AUX_wc_ceqs)) THEN
  RVEQ_TAC;;

let WPROOF2AUX_gcl_cfl = prove
 (`!p (cs:(A word)spt) p1 cs1.
     const_fp_loop p cs = (p1,cs1) ==>
     wordConvs_get_code_labels p1 SUBSET wordConvs_get_code_labels p`,
  WPROOF2AUX_wc_CFL_TAC THEN
  REWRITE_TAC[wordConvs_get_code_labels_def; word_get_code_labels_SmartSeq;
              word_get_code_labels_drop_consts; UNION_EMPTY; SUBSET_REFL] THEN
  CASE_REWRITE_TAC[UNION_EMPTY; SUBSET_REFL] THEN RES_TAC THEN RES_TAC THEN
  TRY (ASM SET_TAC[] THEN NO_TAC) THEN ASM_MESON_TAC[PAIR]);;

let word_get_code_labels_const_fp_loop = prove
 (`!p (l:(A word)spt).
     wordConvs_get_code_labels (FST (const_fp_loop p l)) SUBSET
     wordConvs_get_code_labels p`,
  MESON_TAC[WPROOF2AUX_gcl_cfl; PAIR]);;

let word_good_handlers_SmartSeq = prove
 (`good_handlers n (SmartSeq p q:(A)wl_prog) <=>
   good_handlers n p /\ good_handlers n q`,
  REWRITE_TAC[SmartSeq_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[good_handlers_def]);;

let _ = cake_add_simps [word_good_handlers_SmartSeq];;

let word_good_handlers_drop_consts = prove
 (`!args. good_handlers n (drop_consts (l:(A word)spt) args)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[drop_consts_def; good_handlers_def] THEN
  REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_REWRITE_TAC[word_good_handlers_SmartSeq; good_handlers_def]);;

let _ = cake_add_simps [word_good_handlers_drop_consts];;

let WPROOF2AUX_gh_cfl = prove
 (`!p (cs:(A word)spt) p1 cs1.
     const_fp_loop p cs = (p1,cs1) ==> good_handlers n p ==> good_handlers n p1`,
  WPROOF2AUX_wc_CFL_TAC THEN
  REWRITE_TAC[good_handlers_def; word_good_handlers_SmartSeq;
              word_good_handlers_drop_consts] THEN
  CASE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PAIR]);;

let word_good_handlers_const_fp_loop = prove
 (`!p (l:(A word)spt).
     good_handlers n p ==> good_handlers n (FST (const_fp_loop p l))`,
  MESON_TAC[WPROOF2AUX_gh_cfl; PAIR]);;

let word_get_code_labels_Seq_assoc = prove
 (`!p1 p2:(A)wl_prog.
     wordConvs_get_code_labels (Seq_assoc p1 p2) =
     wordConvs_get_code_labels p1 UNION wordConvs_get_code_labels p2`,
  MATCH_MP_TAC word_simp_Seq_assoc_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[wordConvs_get_code_labels_def; UNION_EMPTY]) THEN
  ASM_REWRITE_TAC[word_simp_Seq_assoc_def; word_get_code_labels_SmartSeq] THEN
  CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[wordConvs_get_code_labels_def; word_get_code_labels_SmartSeq;
                  UNION_EMPTY] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[UNION_EMPTY; UNION_ACI]);;

let word_good_handlers_Seq_assoc = prove
 (`!p1 p2:(A)wl_prog.
     good_handlers n (Seq_assoc p1 p2) <=> good_handlers n p1 /\ good_handlers n p2`,
  MATCH_MP_TAC word_simp_Seq_assoc_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[good_handlers_def]) THEN
  ASM_REWRITE_TAC[word_simp_Seq_assoc_def; word_good_handlers_SmartSeq] THEN
  CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[good_handlers_def; word_good_handlers_SmartSeq] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[CONJ_ASSOC] THEN
  REWRITE_TAC[CONJ_ACI]);;
let word_good_handlers_try_if_hoist2 = prove
 (`!N p1 interm dummy (p2:(A)wl_prog) (s:B).
     try_if_hoist2 N p1 interm dummy p2 = SOME p3 ==>
     good_handlers n p1 /\ good_handlers n p2 /\ good_handlers n interm ==>
     good_handlers n p3`,
  REWRITE_TAC[FORALL_SIMP] THEN
  MATCH_MP_TAC try_if_hoist2_ind THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `p1:(A)wl_prog`; `interm:(A)wl_prog`; `dummy:(A)wl_prog`;
                       `p2:(A)wl_prog`] THEN
  STRUCT_CASES_TAC (ISPEC `p1:(A)wl_prog` (nchotomy_of_type `:(A)wl_prog`)) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[distinctness "wl_prog"; injectivity "wl_prog"]) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [try_if_hoist2_def] THEN
  ASM_CASES_TAC `N = 0` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  CASE_REWRITE_TAC[option_DISTINCT] THENL
   [(* p1 = Seq a0 a1 *)
    DISJ_CASES_THEN2 (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th])
      (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      (SPEC `a1:(A)wl_prog` WPROOF2AUX_dest_If_cases) THEN
    CASE_REWRITE_TAC[dest_If_def; LET_DEF; LET_END_DEF] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`a0:(A)wl_prog`; `a1:(A)wl_prog`]) THEN
      ASM_REWRITE_TAC[good_handlers_def] THEN MESON_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[good_handlers_def; const_fp_def] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC word_good_handlers_const_fp_loop THEN
      ASM_REWRITE_TAC[good_handlers_def]];
    (* p1 = If a0 a1 a2 a3 a4 *)
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[good_handlers_def; const_fp_def] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC word_good_handlers_const_fp_loop THEN
    ASM_REWRITE_TAC[good_handlers_def]]);;

let word_good_handlers_simp_duplicate_if = prove
 (`!p:(A)wl_prog. good_handlers n p ==> good_handlers n (simp_duplicate_if p)`,
  MATCH_MP_TAC simp_duplicate_if_ind THEN GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [simp_duplicate_if_def] THEN
  CASES_ON `p:(A)wl_prog` THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  CASE_REWRITE_TAC[good_handlers_def; LET_DEF; LET_END_DEF] THEN
  TRY (REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  (* Seq *)
  STRIP_TAC THEN RES_TAC THEN
  MP_TAC(ISPEC `try_if_hoist1 (simp_duplicate_if a0) (simp_duplicate_if (a1:(A)wl_prog))`
               (nchotomy_of_type `:((A)wl_prog)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[good_handlers_def] THEN
  TRY (ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  REWRITE_TAC[word_good_handlers_Seq_assoc; good_handlers_def] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_comb(rhs(concl th)) &&
                                          is_const(rator(rhs(concl th))))) THEN
  REWRITE_TAC[try_if_hoist1_def] THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[option_DISTINCT])
    (REPEAT_TCL CHOOSE_THEN (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))
    (SPEC `simp_duplicate_if (a1:(A)wl_prog)` WPROOF2AUX_dest_If_cases) THEN
  CASE_REWRITE_TAC[dest_If_def; LET_DEF; LET_END_DEF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP word_good_handlers_try_if_hoist2) THEN
  ASM_MESON_TAC[good_handlers_def]);;

let word_good_handlers_simp_push_out_if = prove
 (`!p:(A)wl_prog. good_handlers n p ==> good_handlers n (push_out_if p)`,
  REWRITE_TAC[push_out_if_def] THEN
  MATCH_MP_TAC push_out_if_aux_ind THEN GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [push_out_if_aux_def] THEN
  CASES_ON `p:(A)wl_prog` THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ; WPROOF2AUX_FORALL_PAIR_EQ_IMP]) THEN
  TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[FST; SND; good_handlers_def] THEN CASE_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);;

let word_good_handlers_word_simp = prove
 (`!ps:(A)wl_prog. good_handlers n ps ==> good_handlers n (word_simp_compile_exp ps)`,
  GEN_TAC THEN REWRITE_TAC[word_simp_compile_exp_def; LET_DEF; LET_END_DEF] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC word_good_handlers_simp_push_out_if THEN
  MATCH_MP_TAC word_good_handlers_simp_duplicate_if THEN
  REWRITE_TAC[const_fp_def] THEN MATCH_MP_TAC word_good_handlers_const_fp_loop THEN
  ASM_REWRITE_TAC[word_good_handlers_Seq_assoc; good_handlers_def]);;
(* get_code_labels of a const_fp_loop result in the goal: add the bound      *)

let WPROOF2AUX_wc_GCL_CFL_TAC : tactic = fun (asl,w as g) ->
  let is_cfl t =
    is_comb t && is_comb(rator t) &&
    (try fst(dest_const(rator(rator t))) = "const_fp_loop" with Failure _ -> false) in
  let t = find_term is_cfl w in
  MP_TAC(ISPECL [rand(rator t); rand t] word_get_code_labels_const_fp_loop) g;;

let word_get_code_labels_try_if_hoist2 = prove
 (`!N p1 interm dummy (p2:(A)wl_prog) (s:B).
     try_if_hoist2 N p1 interm dummy p2 = SOME p3 ==>
     wordConvs_get_code_labels p3 SUBSET
     (wordConvs_get_code_labels p1 UNION wordConvs_get_code_labels interm UNION
      wordConvs_get_code_labels p2)`,
  REWRITE_TAC[FORALL_SIMP] THEN
  MATCH_MP_TAC try_if_hoist2_ind THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `p1:(A)wl_prog`; `interm:(A)wl_prog`; `dummy:(A)wl_prog`;
                       `p2:(A)wl_prog`] THEN
  STRUCT_CASES_TAC (ISPEC `p1:(A)wl_prog` (nchotomy_of_type `:(A)wl_prog`)) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[distinctness "wl_prog"; injectivity "wl_prog"]) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [try_if_hoist2_def] THEN
  ASM_CASES_TAC `N = 0` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  CASE_REWRITE_TAC[option_DISTINCT] THENL
   [(* p1 = Seq a0 a1 *)
    DISJ_CASES_THEN2 (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th])
      (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      (SPEC `a1:(A)wl_prog` WPROOF2AUX_dest_If_cases) THEN
    CASE_REWRITE_TAC[dest_If_def; LET_DEF; LET_END_DEF] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`a0:(A)wl_prog`; `a1:(A)wl_prog`]) THEN
      ASM_REWRITE_TAC[wordConvs_get_code_labels_def] THEN SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[const_fp_def] THEN
      WPROOF2AUX_wc_GCL_CFL_TAC THEN
      REWRITE_TAC[wordConvs_get_code_labels_def] THEN SET_TAC[]];
    (* p1 = If a0 a1 a2 a3 a4 *)
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[const_fp_def] THEN
    WPROOF2AUX_wc_GCL_CFL_TAC THEN
    REWRITE_TAC[wordConvs_get_code_labels_def] THEN SET_TAC[]]);;

let word_get_code_labels_simp_duplicate_if = prove
 (`!p:(A)wl_prog.
     wordConvs_get_code_labels (simp_duplicate_if p) SUBSET wordConvs_get_code_labels p`,
  MATCH_MP_TAC simp_duplicate_if_ind THEN GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [simp_duplicate_if_def] THEN
  CASES_ON `p:(A)wl_prog` THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  CASE_REWRITE_TAC[wordConvs_get_code_labels_def; LET_DEF; LET_END_DEF; SUBSET_REFL] THEN
  TRY (ASM SET_TAC[] THEN NO_TAC) THEN
  (* Seq *)
  MP_TAC(ISPEC `try_if_hoist1 (simp_duplicate_if a0) (simp_duplicate_if (a1:(A)wl_prog))`
               (nchotomy_of_type `:((A)wl_prog)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[wordConvs_get_code_labels_def] THEN
  TRY (ASM SET_TAC[] THEN NO_TAC) THEN
  REWRITE_TAC[word_get_code_labels_Seq_assoc; wordConvs_get_code_labels_def; UNION_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_comb(rhs(concl th)) &&
                                          is_const(rator(rhs(concl th))))) THEN
  REWRITE_TAC[try_if_hoist1_def] THEN
  DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[option_DISTINCT])
    (REPEAT_TCL CHOOSE_THEN (fun th -> REWRITE_TAC[th] THEN
                                        RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th))
    (SPEC `simp_duplicate_if (a1:(A)wl_prog)` WPROOF2AUX_dest_If_cases) THEN
  CASE_REWRITE_TAC[dest_If_def; LET_DEF; LET_END_DEF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP word_get_code_labels_try_if_hoist2) THEN
  REWRITE_TAC[wordConvs_get_code_labels_def; UNION_EMPTY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wordConvs_get_code_labels_def]) THEN ASM SET_TAC[]);;

let WPROOF2AUX_gcl_push_out_if_aux = prove
 (`!p:(A)wl_prog.
     wordConvs_get_code_labels (FST (push_out_if_aux p)) SUBSET wordConvs_get_code_labels p`,
  MATCH_MP_TAC push_out_if_aux_ind THEN GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [push_out_if_aux_def] THEN
  CASES_ON `p:(A)wl_prog` THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ; WPROOF2AUX_FORALL_PAIR_EQ_IMP]) THEN
  TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[FST; SND; wordConvs_get_code_labels_def; SUBSET_REFL] THEN
  CASE_REWRITE_TAC[SUBSET_REFL] THEN RES_TAC THEN ASM SET_TAC[]);;

let word_get_code_labels_push_out_if = prove
 (`!p:(A)wl_prog.
     wordConvs_get_code_labels (push_out_if p) SUBSET wordConvs_get_code_labels p`,
  REWRITE_TAC[push_out_if_def; WPROOF2AUX_gcl_push_out_if_aux]);;

let word_get_code_labels_word_simp = prove
 (`!ps:(A)wl_prog.
     wordConvs_get_code_labels (word_simp_compile_exp ps) SUBSET
     wordConvs_get_code_labels ps`,
  GEN_TAC THEN REWRITE_TAC[word_simp_compile_exp_def; LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `wordConvs_get_code_labels
                (simp_duplicate_if (const_fp (Seq_assoc wl_Skip (ps:(A)wl_prog))))` THEN
  REWRITE_TAC[word_get_code_labels_push_out_if] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `wordConvs_get_code_labels (const_fp (Seq_assoc wl_Skip (ps:(A)wl_prog)))` THEN
  REWRITE_TAC[word_get_code_labels_simp_duplicate_if] THEN
  REWRITE_TAC[const_fp_def] THEN WPROOF2AUX_wc_GCL_CFL_TAC THEN
  REWRITE_TAC[word_get_code_labels_Seq_assoc; wordConvs_get_code_labels_def; UNION_EMPTY]);;
(* ------------------------------------------------------------------------- *)
(* inst_select                                                               *)
(* ------------------------------------------------------------------------- *)

let WPROOF2AUX_wc_exp_size = type_size_def "wl_exp";;

let WPROOF2AUX_list_cases3 = prove
 (`!l:(A)list. l = [] \/ (?e. l = [e]) \/ (?e1 e2. l = [e1; e2]) \/
               (?e1 e2 e3 r. l = CONS e1 (CONS e2 (CONS e3 r)))`,
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l:(A)list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN
  STRUCT_CASES_TAC(ISPEC `t:(A)list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN
  STRUCT_CASES_TAC(ISPEC `t':(A)list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]);;

(* split the argument list of the wl_Op in the goal into the shapes of the  *)
(* clauses of inst_select_exp_def                                            *)

let WPROOF2AUX_OP_LIST_TAC : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> is_comb t && is_var(rand t) &&
                       (try fst(dest_const(rator(rator t))) = "wl_Op"
                        with Failure _ -> false)) w in
  let l = rand t in
  REPEAT_TCL DISJ_CASES_THEN
    (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    (ISPEC l WPROOF2AUX_list_cases3) g;;

(* a property of programs closed under Seq and true of the instructions     *)
(* that inst_select_exp emits holds for every inst_select_exp result        *)

let WPROOF2AUX_ise_closed = prove
 (`!(Q:(A)wl_prog->bool) (c:(A)asm_config).
     (!p1 p2. Q p1 /\ Q p2 ==> Q (wl_Seq p1 p2)) /\
     (!tar temp w. asm_offset_ok 0 (asm_config_addr_offset c) w
                   ==> Q (wl_Inst (Mem asm_Load tar (Addr temp w)))) /\
     (!tar temp. Q (wl_Inst (Mem asm_Load tar (Addr temp (word 0))))) /\
     (!tar w. Q (wl_Inst (asm_Const tar w))) /\
     (!op tar temp w. asm_config_valid_imm c (INL op) w
                      ==> Q (wl_Inst (asm_Arith (Binop op tar temp (Imm w))))) /\
     (!op tar temp r. Q (wl_Inst (asm_Arith (Binop op tar temp (Reg r))))) /\
     (!sh tar temp n. ~(n = 0) /\ n < dimindex(:A)
                      ==> Q (wl_Inst (asm_Arith (asm_Shift sh tar temp (Imm (word n)))))) /\
     (!sh tar temp r. Q (wl_Inst (asm_Arith (asm_Shift sh tar temp (Reg r))))) /\
     (!v. Q (wl_Move 0 v)) /\ (!tar n. Q (wl_Get tar n)) /\
     (!op tar temp. Q (wl_OpCurrHeap op tar temp)) /\ Q wl_Skip
     ==> !tar temp exp. Q (inst_select_exp c tar temp exp)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!exp tar temp. Q (inst_select_exp (c:(A)asm_config) tar temp exp)`
    (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPEC `wl_exp_size (\x:A. 0)` WF_MEASURE) THEN
  REWRITE_TAC[WF_IND; MEASURE] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `exp:(A)wl_exp` THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[RIGHT_IMP_FORALL_THM]) THEN
  CASES_ON `exp:(A)wl_exp` THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[inst_select_exp_def] THEN
  TRY (WPROOF2AUX_OP_LIST_TAC THEN ONCE_REWRITE_TAC[inst_select_exp_def]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (FIRST [COND_CASES_TAC; TOP_CASE_TAC]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (MATCH_MP_TAC (ASSUME `!p1 p2. (Q:(A)wl_prog->bool) p1 /\ Q p2
                                         ==> Q (wl_Seq p1 p2)`) THEN CONJ_TAC) THEN
  ASM_SIMP_TAC[] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[WPROOF2AUX_wc_exp_size] THEN ARITH_TAC);;
let inst_select_exp_no_lab = prove
 (`!(c:(A)asm_config) temp temp' exp.
     wordConvs_extract_labels (inst_select_exp c temp temp' exp) = []`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\p:(A)wl_prog. wordConvs_extract_labels p = []`; `c:(A)asm_config`]
                WPROOF2AUX_ise_closed) THEN
  SIMP_TAC[wordConvs_extract_labels_def; APPEND_EQ_NIL]);;

(* the clauses of inst_select, the conditions split                         *)

let WPROOF2AUX_wc_IS_TAC : tactic =
  MATCH_MP_TAC inst_select_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  REWRITE_TAC[inst_select_def; o_THM; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  REPEAT (FIRST [COND_CASES_TAC; TOP_CASE_TAC]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF];;

let inst_select_lab_pres = prove
 (`!(c:(A)asm_config) temp prog.
     wordConvs_extract_labels prog = wordConvs_extract_labels (inst_select c temp prog)`,
  WPROOF2AUX_wc_IS_TAC THEN
  ASM_REWRITE_TAC[wordConvs_extract_labels_def; inst_select_exp_no_lab; APPEND;
                  APPEND_NIL] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let inst_select_exp_flat_exp_conventions = prove
 (`!(c:(A)asm_config) tar temp exp.
     flat_exp_conventions (inst_select_exp c tar temp exp)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`flat_exp_conventions:(A)wl_prog->bool`; `c:(A)asm_config`]
                WPROOF2AUX_ise_closed) THEN
  SIMP_TAC[flat_exp_conventions_def]);;

let inst_select_flat_exp_conventions = prove
 (`!(c:(A)asm_config) temp prog. flat_exp_conventions (inst_select c temp prog)`,
  WPROOF2AUX_wc_IS_TAC THEN
  ASM_REWRITE_TAC[flat_exp_conventions_def; inst_select_exp_flat_exp_conventions] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let inst_select_exp_not_created_subprogs = prove
 (`not_created_subprogs P (inst_select_exp (c:(A)asm_config) c' n exp)`,
  MP_TAC(ISPECL [`not_created_subprogs (P:(A)wl_prog->bool)`; `c:(A)asm_config`]
                WPROOF2AUX_ise_closed) THEN
  SIMP_TAC[not_created_subprogs_def]);;

let inst_select_not_created_subprogs = prove
 (`not_created_subprogs P prog ==>
   not_created_subprogs P (inst_select (c:(A)asm_config) n prog)`,
  SPEC_TAC(`prog:(A)wl_prog`,`prog:(A)wl_prog`) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN SPEC_TAC(`c:(A)asm_config`,`c:(A)asm_config`) THEN
  WPROOF2AUX_wc_IS_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[not_created_subprogs_def]) THEN
  POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC) THEN RES_TAC THEN
  ASM_REWRITE_TAC[not_created_subprogs_def; inst_select_exp_not_created_subprogs] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;
let WPROOF2AUX_val_word_small = prove
 (`!n. n < dimindex(:A) ==> val(word n:A word) = n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `dimindex(:A)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC[LT_POW2_REFL]);;

let WPROOF2AUX_word_small_nz = prove
 (`!n. ~(n = 0) /\ n < dimindex(:A) ==> ~(word n:A word = word 0)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `val:A word->num`) THEN
  ASM_SIMP_TAC[WPROOF2AUX_val_word_small; VAL_WORD_0]);;

let inst_select_exp_full_inst_ok_less = prove
 (`!(c:(A)asm_config) tar temp exp.
     asm_offset_ok 0 (asm_config_addr_offset c) (word 0) ==>
     full_inst_ok_less c (inst_select_exp c tar temp exp)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`full_inst_ok_less (c:(A)asm_config)`; `c:(A)asm_config`]
                WPROOF2AUX_ise_closed) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_SIMP_TAC[full_inst_ok_less_def; inst_ok_less_def; IN_INSERT;
               WPROOF2AUX_val_word_small; WPROOF2AUX_word_small_nz]);;

let inst_select_full_inst_ok_less = prove
 (`!(c:(A)asm_config) temp prog.
     asm_offset_ok 0 (asm_config_addr_offset c) (word 0) /\
     asm_offset_ok 0 (asm_config_hw_offset c) (word 0) /\
     asm_offset_ok 0 (asm_config_byte_offset c) (word 0) /\
     every_inst (inst_ok_less c) prog
     ==> full_inst_ok_less c (inst_select c temp prog)`,
  WPROOF2AUX_wc_IS_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[every_inst_def]) THEN
  POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC) THEN RES_TAC THEN
  ASM_SIMP_TAC[full_inst_ok_less_def; inst_ok_less_def; inst_select_exp_full_inst_ok_less;
               exp_to_addr_def; IN_INSERT; NOT_IN_EMPTY] THEN
  CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN
  TRY (FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o
         check (fun th -> is_disj(concl th))) THEN
       RVEQ_TAC THEN ASM_REWRITE_TAC[distinctness "memop"] THEN NO_TAC) THEN
  STRUCT_CASES_TAC (ISPEC `op:memop` (nchotomy_of_type `:memop`)) THEN
  ASM_REWRITE_TAC[distinctness "memop"]);;
let word_get_code_labels_inst_select_exp = prove
 (`!(a:(A)asm_config) b c exp. wordConvs_get_code_labels (inst_select_exp a b c exp) = {}`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\p:(A)wl_prog. wordConvs_get_code_labels p = {}`; `a:(A)asm_config`]
                WPROOF2AUX_ise_closed) THEN
  SIMP_TAC[wordConvs_get_code_labels_def; UNION_EMPTY]);;

let word_get_code_labels_inst_select = prove
 (`!(ac:(A)asm_config) v ps.
     wordConvs_get_code_labels (inst_select ac v ps) = wordConvs_get_code_labels ps`,
  WPROOF2AUX_wc_IS_TAC THEN
  ASM_REWRITE_TAC[wordConvs_get_code_labels_def; word_get_code_labels_inst_select_exp;
                  UNION_EMPTY] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let word_good_handlers_inst_select_exp = prove
 (`!(a:(A)asm_config) b c exp. good_handlers n (inst_select_exp a b c exp)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`good_handlers n:(A)wl_prog->bool`; `a:(A)asm_config`]
                WPROOF2AUX_ise_closed) THEN
  SIMP_TAC[good_handlers_def]);;

let word_good_handlers_inst_select = prove
 (`!(ac:(A)asm_config) v ps. good_handlers n (inst_select ac v ps) <=> good_handlers n ps`,
  WPROOF2AUX_wc_IS_TAC THEN
  ASM_REWRITE_TAC[good_handlers_def; word_good_handlers_inst_select_exp] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;
(* ------------------------------------------------------------------------- *)
(* full_ssa_cc_trans                                                         *)
(* ------------------------------------------------------------------------- *)

(* The moves and instructions made by ssa_cc_trans: a property of programs  *)
(* true of Skip, Inst and Move and closed under Seq holds for them.         *)

let WPROOF2AUX_scti_closed = prove
 (`!(Q:(A)wl_prog->bool).
     Q wl_Skip /\ (!p q. Q p /\ Q q ==> Q (wl_Seq p q)) /\ (!i. Q (wl_Inst i)) /\
     (!pr ms. Q (wl_Move pr ms))
     ==> !i ssa na. Q (FST (ssa_cc_trans_inst i ssa na))`,
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ssa_cc_trans_inst_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ssa_cc_trans_inst_def; next_var_rename_def; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND] THEN
  REPEAT (FIRST [COND_CASES_TAC; TOP_CASE_TAC]) THEN
  CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND; FST; SND] THEN
  ASM_SIMP_TAC[]);;

let WPROOF2AUX_fake_moves_closed = prove
 (`!(Q:(A)wl_prog->bool).
     Q wl_Skip /\ (!p q. Q p /\ Q q ==> Q (wl_Seq p q)) /\ (!i. Q (wl_Inst i)) /\
     (!pr ms. Q (wl_Move pr ms))
     ==> !prio ls a b c. Q (FST (fake_moves prio ls a b c)) /\
                         Q (FST (SND (fake_moves prio ls a b c)))`,
  GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[fake_moves_def; LET_DEF; LET_END_DEF] THEN
  ASM_REWRITE_TAC[FST; SND] THEN REPEAT GEN_TAC THEN
  CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND] THEN
  REPEAT (FIRST [COND_CASES_TAC; TOP_CASE_TAC]) THEN
  CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND; FST; SND; fake_move_def] THEN
  ASM_SIMP_TAC[]);;

let WPROOF2AUX_fix_inconsistencies_closed = prove
 (`!(Q:(A)wl_prog->bool).
     Q wl_Skip /\ (!p q. Q p /\ Q q ==> Q (wl_Seq p q)) /\ (!i. Q (wl_Inst i)) /\
     (!pr ms. Q (wl_Move pr ms))
     ==> !prio l r na. Q (FST (fix_inconsistencies prio l r na)) /\
                       Q (FST (SND (fix_inconsistencies prio l r na)))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP WPROOF2AUX_fake_moves_closed) THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM STRIP_ASSUME_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[fix_inconsistencies_def; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND; FST; SND] THEN
  ASM_SIMP_TAC[]);;

let WPROOF2AUX_fake_seq_closed = prove
 (`!(Q:(A)wl_prog->bool).
     Q wl_Skip /\ (!p q. Q p /\ Q q ==> Q (wl_Seq p q)) /\ (!i. Q (wl_Inst i))
     ==> !ls. Q (ITLIST wl_Seq (MAP (\r. fake_move r) ls) wl_Skip)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!v. (Q:(A)wl_prog->bool) (fake_move v)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[fake_move_def]; ALL_TAC] THEN
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[MAP; ITLIST]);;

let WPROOF2AUX_ssa_reconcile_closed = prove
 (`!(Q:(A)wl_prog->bool).
     Q wl_Skip /\ (!pr ms. Q (wl_Move pr ms))
     ==> !cur_ssa tgt_ssa (ns:B spt). Q (ssa_reconcile cur_ssa tgt_ssa ns)`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ssa_reconcile_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let WPROOF2AUX_lnvrm_FST = prove
 (`!ssa n ls. FST (list_next_var_rename_move ssa n ls:(A)wl_prog#num spt#num) =
              wl_Move 0 (ZIP (FST (list_next_var_rename ls ssa n))
                             (MAP (option_lookup ssa) ls))`,
  REWRITE_TAC[list_next_var_rename_move_def; LET_DEF; LET_END_DEF;
              WPROOF2AUX_pair_CASE_FST_SND; FST; SND]);;

let WPROOF2AUX_loop_setup_closed = prove
 (`!(Q:(A)wl_prog->bool).
     Q wl_Skip /\ (!p q. Q p /\ Q q ==> Q (wl_Seq p q)) /\ (!i. Q (wl_Inst i)) /\
     (!pr ms. Q (wl_Move pr ms))
     ==> !names exit_names ssa na. Q (FST (loop_setup names exit_names ssa na))`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[loop_setup_def; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND; FST; SND; WPROOF2AUX_lnvrm_FST] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `Q:(A)wl_prog->bool` WPROOF2AUX_fake_seq_closed) THEN
  ASM_SIMP_TAC[]);;
let WPROOF2AUX_fake_moves_closed_eq = prove
 (`!(Q:(A)wl_prog->bool).
     Q wl_Skip /\ (!p q. Q p /\ Q q ==> Q (wl_Seq p q)) /\ (!i. Q (wl_Inst i)) /\
     (!pr ms. Q (wl_Move pr ms))
     ==> !prio ls a b c d e f g h.
           fake_moves prio ls a b c = (d,e,f,g,h) ==> Q d /\ Q e`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP WPROOF2AUX_fake_moves_closed) THEN
  MESON_TAC[FST; SND]);;

let WPROOF2AUX_loop_setup_closed_eq = prove
 (`!(Q:(A)wl_prog->bool).
     Q wl_Skip /\ (!p q. Q p /\ Q q ==> Q (wl_Seq p q)) /\ (!i. Q (wl_Inst i)) /\
     (!pr ms. Q (wl_Move pr ms))
     ==> !names exit_names ssa na setup_prog ssa' na'.
           loop_setup names exit_names ssa na = (setup_prog,ssa',na') ==> Q setup_prog`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP WPROOF2AUX_loop_setup_closed) THEN
  MESON_TAC[FST]);;

(* the four closure conditions of a syntactic property                       *)

let WPROOF2AUX_MSI_TAC (ths:thm list) : tactic =
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC ths THEN TRY (DISCH_THEN(CONJUNCTS_THEN(fun th -> REWRITE_TAC[th]))) THEN
  REWRITE_TAC ths;;

let fake_moves_no_labs = prove
 (`!ls a b c (d:(A)wl_prog) e f g h.
     fake_moves prio ls a b c = (d,e,f,g,h) ==>
     wordConvs_extract_labels d = [] /\ wordConvs_extract_labels e = []`,
  MP_TAC(ISPEC `\p:(A)wl_prog. wordConvs_extract_labels p = []`
               WPROOF2AUX_fake_moves_closed_eq) THEN
  ANTS_TAC THENL [BETA_TAC THEN WPROOF2AUX_MSI_TAC[wordConvs_extract_labels_def; APPEND];
                  MESON_TAC[]]);;

let fake_seq_no_labs = prove
 (`!ls. wordConvs_extract_labels (ITLIST wl_Seq (MAP (\r. fake_move r) ls) wl_Skip:(A)wl_prog)
        = []`,
  MP_TAC(ISPEC `\p:(A)wl_prog. wordConvs_extract_labels p = []`
               WPROOF2AUX_fake_seq_closed) THEN
  ANTS_TAC THENL [BETA_TAC THEN WPROOF2AUX_MSI_TAC[wordConvs_extract_labels_def; APPEND];
                  MESON_TAC[]]);;

let fake_seq_get_code_labels = prove
 (`!ls. wordConvs_get_code_labels
          (ITLIST wl_Seq (MAP (\r. fake_move r) ls) wl_Skip:(A)wl_prog) = {}`,
  MP_TAC(ISPEC `\p:(A)wl_prog. wordConvs_get_code_labels p = {}`
               WPROOF2AUX_fake_seq_closed) THEN
  ANTS_TAC THENL [BETA_TAC THEN WPROOF2AUX_MSI_TAC[wordConvs_get_code_labels_def; UNION_EMPTY];
                  MESON_TAC[]]);;

let fake_seq_good_handlers = prove
 (`!ls. good_handlers n (ITLIST wl_Seq (MAP (\r. fake_move r) ls) wl_Skip:(A)wl_prog)`,
  MP_TAC(ISPEC `good_handlers n:(A)wl_prog->bool` WPROOF2AUX_fake_seq_closed) THEN
  ANTS_TAC THENL [WPROOF2AUX_MSI_TAC[good_handlers_def]; MESON_TAC[]]);;

let fake_seq_flat_exp_conventions = prove
 (`!ls. flat_exp_conventions (ITLIST wl_Seq (MAP (\r. fake_move r) ls) wl_Skip:(A)wl_prog)`,
  MP_TAC(ISPEC `flat_exp_conventions:(A)wl_prog->bool` WPROOF2AUX_fake_seq_closed) THEN
  ANTS_TAC THENL [WPROOF2AUX_MSI_TAC[flat_exp_conventions_def]; MESON_TAC[]]);;

let fake_seq_wf_cutsets = prove
 (`!ls. wf_cutsets (ITLIST wl_Seq (MAP (\r. fake_move r) ls) wl_Skip:(A)wl_prog)`,
  MP_TAC(ISPEC `wf_cutsets:(A)wl_prog->bool` WPROOF2AUX_fake_seq_closed) THEN
  ANTS_TAC THENL [WPROOF2AUX_MSI_TAC[wf_cutsets_def]; MESON_TAC[]]);;

let ssa_reconcile_no_labs = prove
 (`wordConvs_extract_labels (ssa_reconcile cur_ssa tgt_ssa (ns:B spt):(A)wl_prog) = []`,
  MP_TAC(ISPEC `\p:(A)wl_prog. wordConvs_extract_labels p = []`
               WPROOF2AUX_ssa_reconcile_closed) THEN
  ANTS_TAC THENL [BETA_TAC THEN WPROOF2AUX_MSI_TAC[wordConvs_extract_labels_def];
                  MESON_TAC[]]);;

let ssa_reconcile_get_code_labels = prove
 (`wordConvs_get_code_labels (ssa_reconcile cur_ssa tgt_ssa (ns:B spt):(A)wl_prog) = {}`,
  MP_TAC(ISPEC `\p:(A)wl_prog. wordConvs_get_code_labels p = {}`
               WPROOF2AUX_ssa_reconcile_closed) THEN
  ANTS_TAC THENL [BETA_TAC THEN WPROOF2AUX_MSI_TAC[wordConvs_get_code_labels_def];
                  MESON_TAC[]]);;

let ssa_reconcile_good_handlers = prove
 (`good_handlers n (ssa_reconcile cur_ssa tgt_ssa (ns:B spt):(A)wl_prog)`,
  MP_TAC(ISPEC `good_handlers n:(A)wl_prog->bool` WPROOF2AUX_ssa_reconcile_closed) THEN
  ANTS_TAC THENL [WPROOF2AUX_MSI_TAC[good_handlers_def]; MESON_TAC[]]);;

let ssa_reconcile_flat_exp_conventions = prove
 (`flat_exp_conventions (ssa_reconcile cur_ssa tgt_ssa (ns:B spt):(A)wl_prog)`,
  MP_TAC(ISPEC `flat_exp_conventions:(A)wl_prog->bool` WPROOF2AUX_ssa_reconcile_closed) THEN
  ANTS_TAC THENL [WPROOF2AUX_MSI_TAC[flat_exp_conventions_def]; MESON_TAC[]]);;

let ssa_reconcile_wf_cutsets = prove
 (`wf_cutsets (ssa_reconcile cur_ssa tgt_ssa (ns:B spt):(A)wl_prog)`,
  MP_TAC(ISPEC `wf_cutsets:(A)wl_prog->bool` WPROOF2AUX_ssa_reconcile_closed) THEN
  ANTS_TAC THENL [WPROOF2AUX_MSI_TAC[wf_cutsets_def]; MESON_TAC[]]);;

let loop_setup_no_labs = prove
 (`loop_setup names exit_names ssa na = (setup_prog:(A)wl_prog,ssa',na') ==>
   wordConvs_extract_labels setup_prog = []`,
  MP_TAC(ISPEC `\p:(A)wl_prog. wordConvs_extract_labels p = []`
               WPROOF2AUX_loop_setup_closed_eq) THEN
  ANTS_TAC THENL [BETA_TAC THEN WPROOF2AUX_MSI_TAC[wordConvs_extract_labels_def; APPEND];
                  MESON_TAC[]]);;

let loop_setup_get_code_labels = prove
 (`loop_setup names exit_names ssa na = (setup_prog:(A)wl_prog,ssa',na') ==>
   wordConvs_get_code_labels setup_prog = {}`,
  MP_TAC(ISPEC `\p:(A)wl_prog. wordConvs_get_code_labels p = {}`
               WPROOF2AUX_loop_setup_closed_eq) THEN
  ANTS_TAC THENL [BETA_TAC THEN WPROOF2AUX_MSI_TAC[wordConvs_get_code_labels_def; UNION_EMPTY];
                  MESON_TAC[]]);;

let loop_setup_good_handlers = prove
 (`loop_setup names exit_names ssa na = (setup_prog:(A)wl_prog,ssa',na') ==>
   good_handlers n setup_prog`,
  MP_TAC(ISPEC `good_handlers n:(A)wl_prog->bool` WPROOF2AUX_loop_setup_closed_eq) THEN
  ANTS_TAC THENL [WPROOF2AUX_MSI_TAC[good_handlers_def]; MESON_TAC[]]);;

let loop_setup_flat_exp_conventions = prove
 (`loop_setup names exit_names ssa na = (setup_prog:(A)wl_prog,ssa',na') ==>
   flat_exp_conventions setup_prog`,
  MP_TAC(ISPEC `flat_exp_conventions:(A)wl_prog->bool` WPROOF2AUX_loop_setup_closed_eq) THEN
  ANTS_TAC THENL [WPROOF2AUX_MSI_TAC[flat_exp_conventions_def]; MESON_TAC[]]);;

let loop_setup_wf_cutsets = prove
 (`loop_setup names exit_names ssa na = (setup_prog:(A)wl_prog,ssa',na') ==>
   wf_cutsets setup_prog`,
  MP_TAC(ISPEC `wf_cutsets:(A)wl_prog->bool` WPROOF2AUX_loop_setup_closed_eq) THEN
  ANTS_TAC THENL [WPROOF2AUX_MSI_TAC[wf_cutsets_def]; MESON_TAC[]]);;
(* WF induction on the program for a goal                                    *)
(* !prog ssa na lt. R prog (FST (ssa_cc_trans prog ssa na lt)): split the    *)
(* program, instantiate the induction hypothesis for its subprograms and    *)
(* unfold one step of ssa_cc_trans                                           *)

let WPROOF2AUX_SCT_IH_TAC : tactic = fun (asl,w as g) ->
  let pty = `:(A)wl_prog` in
  let is_ih th =
    let c = concl th in
    is_forall c &&
    (let v,b = dest_forall c in
     type_of v = pty && is_imp b &&
     (try fst(dest_const(fst(strip_comb(fst(dest_imp b))))) = "<"
      with Failure _ -> false)) in
  let ih = snd(find (fun (_,th) -> is_ih th) asl) in
  let vs = filter (fun v -> type_of v = pty) (frees w) in
  let ths = mapfilter (fun v -> let th1 = SPEC v ih in
                         MP th1 (prove(fst(dest_imp(concl th1)), TERM_TAC))) vs in
  MAP_EVERY ASSUME_TAC ths g;;

let WPROOF2AUX_SCT_TAC : tactic =
  MP_TAC(ISPEC `wl_prog_size (\x:A. 0)` WF_MEASURE) THEN
  REWRITE_TAC[WF_IND; MEASURE] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `prog:(A)wl_prog` THEN DISCH_TAC THEN
  CASES_ON `prog:(A)wl_prog` THEN TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  WPROOF2AUX_SCT_IH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ssa_cc_trans_def; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND; FST; SND];;

(* instances of the closure lemmas for a property q                          *)

let WPROOF2AUX_msi_inst (q:term) (ths:thm list) (closure:thm) : thm =
  let th = ISPEC q closure in
  let ant = fst(dest_imp(concl th)) in
  BETA_RULE (MP th (prove(ant, BETA_TAC THEN WPROOF2AUX_MSI_TAC ths)));;

(* the pieces of ssa_cc_trans for a property q: ssa_cc_trans_inst,          *)
(* fix_inconsistencies, loop_setup and ssa_reconcile                         *)

let WPROOF2AUX_sct_pieces (q:term) (ths:thm list) : thm list =
  map (WPROOF2AUX_msi_inst q ths)
      [WPROOF2AUX_scti_closed; WPROOF2AUX_fix_inconsistencies_closed;
       WPROOF2AUX_loop_setup_closed] @
  [let th = ISPEC q WPROOF2AUX_ssa_reconcile_closed in
   BETA_RULE (MP th (prove(fst(dest_imp(concl th)), BETA_TAC THEN WPROOF2AUX_MSI_TAC ths)))];;

(* finish a step of the induction: an equation, or an implication           *)

let WPROOF2AUX_SCT_FIN_TAC (ths:thm list) : tactic =
  REWRITE_TAC ths THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC ths THEN
  REPEAT (FIRST [COND_CASES_TAC; TOP_CASE_TAC] THEN
          CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND; FST; SND] THEN
          ASM_REWRITE_TAC ths);;

let WPROOF2AUX_SCT_FIN_IMP_TAC (ths:thm list) : tactic =
  REWRITE_TAC ths THEN CASE_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC ths THEN
  REPEAT (FIRST [COND_CASES_TAC; TOP_CASE_TAC] THEN
          CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND; FST; SND] THEN
          ASM_SIMP_TAC ths);;

let WPROOF2AUX_el_sct = prove
 (`!prog ssa na lt.
     wordConvs_extract_labels (FST (ssa_cc_trans prog ssa na lt)) =
     wordConvs_extract_labels (prog:(A)wl_prog)`,
  WPROOF2AUX_SCT_TAC THEN WPROOF2AUX_SCT_FIN_TAC
    ([wordConvs_extract_labels_def; WPROOF2AUX_lnvrm_FST; APPEND; APPEND_NIL] @
     WPROOF2AUX_sct_pieces `\p:(A)wl_prog. wordConvs_extract_labels p = []`
                           [wordConvs_extract_labels_def; APPEND]));;

let WPROOF2AUX_setup_ssa_FST = prove
 (`!n lim prog:(A)wl_prog.
     FST (setup_ssa n lim prog) =
     wl_Move 1 (ZIP (FST (list_next_var_rename (even_list n) LN lim)) (even_list n))`,
  REWRITE_TAC[setup_ssa_def; LET_DEF; LET_END_DEF; WPROOF2AUX_pair_CASE_FST_SND; FST]);;

let WPROOF2AUX_full_ssa_cc_trans = prove
 (`!n prog:(A)wl_prog.
     full_ssa_cc_trans n prog =
     wl_Seq (FST (setup_ssa n (limit_var prog) prog))
            (FST (ssa_cc_trans prog (FST (SND (setup_ssa n (limit_var prog) prog)))
                    (SND (SND (setup_ssa n (limit_var prog) prog))) []))`,
  REWRITE_TAC[full_ssa_cc_trans_def; LET_DEF; LET_END_DEF; WPROOF2AUX_pair_CASE_FST_SND]);;

let full_ssa_cc_trans_lab_pres = prove
 (`!prog:(A)wl_prog n.
     wordConvs_extract_labels prog = wordConvs_extract_labels (full_ssa_cc_trans n prog)`,
  REWRITE_TAC[WPROOF2AUX_full_ssa_cc_trans; WPROOF2AUX_setup_ssa_FST;
              wordConvs_extract_labels_def; WPROOF2AUX_el_sct; APPEND]);;

let WPROOF2AUX_ncs_pieces () =
  WPROOF2AUX_sct_pieces `not_created_subprogs (P:(A)wl_prog->bool)`
                        [not_created_subprogs_def];;

let ssa_cc_trans_inst_not_created_subprogs = prove
 (`ssa_cc_trans_inst (i:(A)inst) ssa na = (i',ssa',na') ==> not_created_subprogs P i'`,
  MESON_TAC[FST; hd (WPROOF2AUX_ncs_pieces ())]);;

let fake_moves_not_created_subprogs = prove
 (`fake_moves prio ls nL nR n = (prog1:(A)wl_prog, prog2, n', ssa, ssa') ==>
   not_created_subprogs P prog1 /\ not_created_subprogs P prog2`,
  MP_TAC(ISPEC `not_created_subprogs (P:(A)wl_prog->bool)`
               WPROOF2AUX_fake_moves_closed_eq) THEN
  ANTS_TAC THENL [WPROOF2AUX_MSI_TAC[not_created_subprogs_def]; MESON_TAC[]]);;

let fake_seq_not_created_subprogs = prove
 (`!ls. not_created_subprogs P (ITLIST wl_Seq (MAP (\r. fake_move r) ls) wl_Skip:(A)wl_prog)`,
  MP_TAC(ISPEC `not_created_subprogs (P:(A)wl_prog->bool)` WPROOF2AUX_fake_seq_closed) THEN
  ANTS_TAC THENL [WPROOF2AUX_MSI_TAC[not_created_subprogs_def]; MESON_TAC[]]);;

let loop_setup_not_created_subprogs = prove
 (`loop_setup names exit_names ssa na = (setup_prog:(A)wl_prog,ssa',na') ==>
   not_created_subprogs P setup_prog`,
  MP_TAC(ISPEC `not_created_subprogs (P:(A)wl_prog->bool)`
               WPROOF2AUX_loop_setup_closed_eq) THEN
  ANTS_TAC THENL [WPROOF2AUX_MSI_TAC[not_created_subprogs_def]; MESON_TAC[]]);;

let WPROOF2AUX_ncs_sct = prove
 (`!prog ssa na lt.
     not_created_subprogs P prog ==>
     not_created_subprogs P (FST (ssa_cc_trans (prog:(A)wl_prog) ssa na lt))`,
  WPROOF2AUX_SCT_TAC THEN WPROOF2AUX_SCT_FIN_IMP_TAC
    ([not_created_subprogs_def; WPROOF2AUX_lnvrm_FST] @ WPROOF2AUX_ncs_pieces ()));;

let ssa_cc_trans_not_created_subprogs = prove
 (`not_created_subprogs P (prog:(A)wl_prog) /\
   ssa_cc_trans prog ssa n lt = (prog', ssa', na) ==>
   not_created_subprogs P prog'`,
  MESON_TAC[WPROOF2AUX_ncs_sct; FST]);;

let setup_ssa_not_created_subprogs = prove
 (`not_created_subprogs P (prog:(A)wl_prog) /\
   setup_ssa n v prog = (mov, ssa, na) ==>
   not_created_subprogs P mov`,
  DISCH_THEN(MP_TAC o AP_TERM `FST:(A)wl_prog#num spt#num->(A)wl_prog` o CONJUNCT2) THEN
  REWRITE_TAC[WPROOF2AUX_setup_ssa_FST; FST] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[not_created_subprogs_def]);;

let full_ssa_cc_trans_not_created_subprogs = prove
 (`not_created_subprogs P (prog:(A)wl_prog) ==>
   not_created_subprogs P (full_ssa_cc_trans n prog)`,
  SIMP_TAC[WPROOF2AUX_full_ssa_cc_trans; WPROOF2AUX_setup_ssa_FST;
           not_created_subprogs_def; WPROOF2AUX_ncs_sct]);;
let word_get_code_labels_fake_moves = prove
 (`!a b c d (e:(A)wl_prog) f g h i.
     fake_moves prio a b c d = (e,f,g,h,i) ==>
     wordConvs_get_code_labels e = {} /\ wordConvs_get_code_labels f = {}`,
  MP_TAC(ISPEC `\p:(A)wl_prog. wordConvs_get_code_labels p = {}`
               WPROOF2AUX_fake_moves_closed_eq) THEN
  ANTS_TAC THENL [BETA_TAC THEN WPROOF2AUX_MSI_TAC[wordConvs_get_code_labels_def; UNION_EMPTY];
                  MESON_TAC[]]);;

let WPROOF2AUX_gcl_sct = prove
 (`!prog ssa na lt.
     wordConvs_get_code_labels (FST (ssa_cc_trans prog ssa na lt)) =
     wordConvs_get_code_labels (prog:(A)wl_prog)`,
  WPROOF2AUX_SCT_TAC THEN WPROOF2AUX_SCT_FIN_TAC
    ([wordConvs_get_code_labels_def; WPROOF2AUX_lnvrm_FST; UNION_EMPTY] @
     WPROOF2AUX_sct_pieces `\p:(A)wl_prog. wordConvs_get_code_labels p = {}`
                           [wordConvs_get_code_labels_def; UNION_EMPTY]));;

let word_get_code_labels_ssa_cc_trans = prove
 (`!(x:(A)wl_prog) y z lt a b c.
     ssa_cc_trans x y z lt = (a,b,c) ==>
     wordConvs_get_code_labels a = wordConvs_get_code_labels x`,
  MESON_TAC[WPROOF2AUX_gcl_sct; FST]);;

let word_get_code_labels_full_ssa_cc_trans = prove
 (`!m p:(A)wl_prog.
     wordConvs_get_code_labels (full_ssa_cc_trans m p) = wordConvs_get_code_labels p`,
  REWRITE_TAC[WPROOF2AUX_full_ssa_cc_trans; WPROOF2AUX_setup_ssa_FST;
              wordConvs_get_code_labels_def; WPROOF2AUX_gcl_sct; UNION_EMPTY]);;

let word_good_handlers_fake_moves = prove
 (`!a b c d (e:(A)wl_prog) f g h i.
     fake_moves prio a b c d = (e,f,g,h,i) ==>
     good_handlers n e /\ good_handlers n f`,
  MP_TAC(ISPEC `good_handlers n:(A)wl_prog->bool` WPROOF2AUX_fake_moves_closed_eq) THEN
  ANTS_TAC THENL [WPROOF2AUX_MSI_TAC[good_handlers_def]; MESON_TAC[]]);;

let WPROOF2AUX_gh_sct = prove
 (`!prog ssa na lt.
     good_handlers n (FST (ssa_cc_trans prog ssa na lt)) <=>
     good_handlers n (prog:(A)wl_prog)`,
  WPROOF2AUX_SCT_TAC THEN WPROOF2AUX_SCT_FIN_TAC
    ([good_handlers_def; WPROOF2AUX_lnvrm_FST] @
     WPROOF2AUX_sct_pieces `good_handlers n:(A)wl_prog->bool` [good_handlers_def]));;

let word_good_handlers_ssa_cc_trans = prove
 (`!(x:(A)wl_prog) y z lt a b c.
     ssa_cc_trans x y z lt = (a,b,c) ==>
     (good_handlers n a <=> good_handlers n x)`,
  MESON_TAC[WPROOF2AUX_gh_sct; FST]);;

let word_good_handlers_full_ssa_cc_trans = prove
 (`!m p:(A)wl_prog.
     good_handlers n (full_ssa_cc_trans m p) <=> good_handlers n p`,
  REWRITE_TAC[WPROOF2AUX_full_ssa_cc_trans; WPROOF2AUX_setup_ssa_FST;
              good_handlers_def; WPROOF2AUX_gh_sct]);;
(* split the variables of the expression of the ShareInst in the goal until *)
(* the definition of flat_exp_conventions applies                            *)

let rec WPROOF2AUX_FEC_SPLIT_TAC : tactic = fun g ->
  (REWRITE_TAC[flat_exp_conventions_def; distinctness "wl_exp"; injectivity "wl_exp";
               distinctness "binop"; NOT_CONS_NIL; CONS_11] THEN
   FIRST [MESON_TAC[] THEN NO_TAC;
          (fun (asl,w as g) ->
             let t = find_term (fun t -> is_comb t &&
                        (try fst(dest_const(rator t)) = "flat_exp_conventions"
                         with Failure _ -> false)) w in
             let e = rand(rand t) in
             let tys = [`:(A)wl_exp`; `:((A)wl_exp)list`; `:binop`] in
             let vs = filter (fun v -> mem (type_of v) tys) (frees e) in
             (CASES_ON (hd vs) THEN WPROOF2AUX_FEC_SPLIT_TAC) g)]) g;;

let flat_exp_conventions_ShareInst = prove
 (`flat_exp_conventions (ShareInst op v exp:(A)wl_prog) <=>
   (?v c. exp = wl_Op asm_Add [wl_Var v; wl_Const c]) \/ (?v. exp = wl_Var v)`,
  WPROOF2AUX_FEC_SPLIT_TAC);;

let flat_exp_conventions_fake_moves = prove
 (`!ls ssal ssar na (l:(A)wl_prog) r a b c (conf:C).
     fake_moves prio ls ssal ssar na = (l,r,a,b,c) ==>
     flat_exp_conventions l /\ flat_exp_conventions r`,
  MP_TAC(ISPEC `flat_exp_conventions:(A)wl_prog->bool` WPROOF2AUX_fake_moves_closed_eq) THEN
  ANTS_TAC THENL [WPROOF2AUX_MSI_TAC[flat_exp_conventions_def]; MESON_TAC[]]);;

let WPROOF2AUX_fec_Set = prove
 (`flat_exp_conventions (wl_Set n exp:(A)wl_prog) <=> ?r. exp = wl_Var r`,
  CASES_ON `exp:(A)wl_exp` THEN
  REWRITE_TAC[flat_exp_conventions_def; distinctness "wl_exp"; injectivity "wl_exp"] THEN
  MESON_TAC[]);;

let ssa_cc_trans_flat_exp_conventions = prove
 (`!prog:(A)wl_prog ssa na lt.
     flat_exp_conventions prog ==>
     flat_exp_conventions (FST (ssa_cc_trans prog ssa na lt))`,
  WPROOF2AUX_SCT_TAC THEN WPROOF2AUX_SCT_FIN_IMP_TAC
    ([flat_exp_conventions_def; flat_exp_conventions_ShareInst; WPROOF2AUX_fec_Set;
      ssa_cc_trans_exp_def; MAP; WPROOF2AUX_lnvrm_FST] @
     WPROOF2AUX_sct_pieces `flat_exp_conventions:(A)wl_prog->bool`
                           [flat_exp_conventions_def]) THEN
  ASM_MESON_TAC[]);;

let full_ssa_cc_trans_flat_exp_conventions = prove
 (`!prog:(A)wl_prog n.
     flat_exp_conventions prog ==> flat_exp_conventions (full_ssa_cc_trans n prog)`,
  SIMP_TAC[WPROOF2AUX_full_ssa_cc_trans; WPROOF2AUX_setup_ssa_FST;
           flat_exp_conventions_def; ssa_cc_trans_flat_exp_conventions]);;

let fake_moves_wf_cutsets = prove
 (`!ls A B C' (L:(A)wl_prog) R D E G.
     fake_moves prio ls A B C' = (L,R,D,E,G) ==> wf_cutsets L /\ wf_cutsets R`,
  MP_TAC(ISPEC `wf_cutsets:(A)wl_prog->bool` WPROOF2AUX_fake_moves_closed_eq) THEN
  ANTS_TAC THENL [WPROOF2AUX_MSI_TAC[wf_cutsets_def]; MESON_TAC[]]);;

let WPROOF2AUX_wf_cutsets_sct = prove
 (`!prog ssa na lt. wf_cutsets (FST (ssa_cc_trans (prog:(A)wl_prog) ssa na lt))`,
  WPROOF2AUX_SCT_TAC THEN WPROOF2AUX_SCT_FIN_TAC
    ([wf_cutsets_def; wf_names_def; apply_nummaps_key_def; apply_nummap_key_def;
      wf_fromAList; WPROOF2AUX_lnvrm_FST] @
     WPROOF2AUX_sct_pieces `wf_cutsets:(A)wl_prog->bool` [wf_cutsets_def]));;

let ssa_cc_trans_wf_cutsets = prove
 (`!prog:(A)wl_prog ssa na lt.
     let (prog',ssa',na') = ssa_cc_trans prog ssa na lt in
     wf_cutsets prog'`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC_ALL WPROOF2AUX_wf_cutsets_sct) THEN
  SPEC_TAC(`ssa_cc_trans (prog:(A)wl_prog) ssa na lt`,`x:(A)wl_prog#num spt#num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let full_ssa_cc_trans_wf_cutsets = prove
 (`!n prog:(A)wl_prog. wf_cutsets (full_ssa_cc_trans n prog)`,
  REWRITE_TAC[WPROOF2AUX_full_ssa_cc_trans; WPROOF2AUX_setup_ssa_FST;
              wf_cutsets_def; WPROOF2AUX_wf_cutsets_sct]);;
(* ------------------------------------------------------------------------- *)
(* remove_dead_prog                                                          *)
(* ------------------------------------------------------------------------- *)

(* WF induction on the program, one step of the definitions defs unfolded   *)

let WPROOF2AUX_PROG_STEP_TAC (defs:thm list) : tactic =
  MP_TAC(ISPEC `wl_prog_size (\x:A. 0)` WF_MEASURE) THEN
  REWRITE_TAC[WF_IND; MEASURE] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `prog:(A)wl_prog` THEN DISCH_TAC THEN
  CASES_ON `prog:(A)wl_prog` THEN TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  WPROOF2AUX_SCT_IH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC(defs @ [LET_DEF; LET_END_DEF]) THEN
  CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND; FST; SND];;

(* for every assumption t = wl_Skip (also inside conjunctions) with t not a *)
(* variable, assume f t = f wl_Skip rewritten with the quantified equations  *)
(* among the assumptions (the induction hypotheses) and ths                  *)

let WPROOF2AUX_SKIP_FACTS_TAC (f:term) (ths:thm list) : tactic = fun (asl,w as g) ->
  let all = flat (map (fun (_,th) -> CONJUNCTS th) asl) in
  let skips = filter (fun th -> let c = concl th in
                        is_eq c && is_const(rhs c) && fst(dest_const(rhs c)) = "wl_Skip" &&
                        not (is_var (lhs c))) all in
  let ihs = filter (fun th -> let c = concl th in
                      is_forall c && is_eq(snd(strip_forall c))) all in
  MAP_EVERY (fun th -> ASSUME_TAC (REWRITE_RULE (ihs @ ths) (AP_TERM f th))) skips g;;

let WPROOF2AUX_rd_el = prove
 (`!p live nlive lt.
     wordConvs_extract_labels (FST (remove_dead (p:(A)wl_prog) live nlive lt)) =
     wordConvs_extract_labels p`,
  WPROOF2AUX_PROG_STEP_TAC [remove_dead_def] THEN
  REPEAT COND_CASES_TAC THEN
  WPROOF2AUX_SKIP_FACTS_TAC `wordConvs_extract_labels:(A)wl_prog->(num#num)list`
    [wordConvs_extract_labels_def] THEN
  WPROOF2AUX_SCT_FIN_TAC [wordConvs_extract_labels_def; APPEND; APPEND_NIL]);;

let WPROOF2AUX_rd_fec = prove
 (`!p live nlive lt.
     flat_exp_conventions p ==>
     flat_exp_conventions (FST (remove_dead (p:(A)wl_prog) live nlive lt))`,
  WPROOF2AUX_PROG_STEP_TAC [remove_dead_def] THEN
  WPROOF2AUX_SCT_FIN_IMP_TAC [flat_exp_conventions_def]);;

let WPROOF2AUX_rd_fiol = prove
 (`!p live nlive lt.
     full_inst_ok_less c p ==>
     full_inst_ok_less c (FST (remove_dead (p:(A)wl_prog) live nlive lt))`,
  WPROOF2AUX_PROG_STEP_TAC [remove_dead_def] THEN
  WPROOF2AUX_SCT_FIN_IMP_TAC [full_inst_ok_less_def]);;

let WPROOF2AUX_rd_esv = prove
 (`!p live nlive lt.
     every_stack_var P p ==>
     every_stack_var P (FST (remove_dead (p:(A)wl_prog) live nlive lt))`,
  WPROOF2AUX_PROG_STEP_TAC [remove_dead_def] THEN
  WPROOF2AUX_SCT_FIN_IMP_TAC [every_stack_var_def]);;

let WPROOF2AUX_rd_cac = prove
 (`!p live nlive lt.
     call_arg_convention p ==>
     call_arg_convention (FST (remove_dead (p:(A)wl_prog) live nlive lt))`,
  WPROOF2AUX_PROG_STEP_TAC [remove_dead_def] THEN
  WPROOF2AUX_SCT_FIN_IMP_TAC [call_arg_convention_def] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let WPROOF2AUX_rd_every_inst = prove
 (`!p live nlive lt.
     every_inst P p ==> every_inst P (FST (remove_dead (p:(A)wl_prog) live nlive lt))`,
  WPROOF2AUX_PROG_STEP_TAC [remove_dead_def] THEN
  WPROOF2AUX_SCT_FIN_IMP_TAC [every_inst_def]);;

let WPROOF2AUX_rd_wf_cutsets = prove
 (`!p live nlive lt.
     wf_cutsets p ==> wf_cutsets (FST (remove_dead (p:(A)wl_prog) live nlive lt))`,
  WPROOF2AUX_PROG_STEP_TAC [remove_dead_def] THEN
  WPROOF2AUX_SCT_FIN_IMP_TAC [wf_cutsets_def]);;

let remove_dead_not_created_subprogs = prove
 (`!prog:(A)wl_prog q r lt.
     not_created_subprogs P prog ==>
     not_created_subprogs P (FST (remove_dead prog q r lt))`,
  WPROOF2AUX_PROG_STEP_TAC [remove_dead_def] THEN
  WPROOF2AUX_SCT_FIN_IMP_TAC [not_created_subprogs_def]);;

let remove_dead_prog_not_created_subprogs = prove
 (`not_created_subprogs P (prog:(A)wl_prog) ==>
   not_created_subprogs P (remove_dead_prog prog)`,
  REWRITE_TAC[remove_dead_prog_def; remove_dead_not_created_subprogs]);;

let remove_dead_conventions = prove
 (`!p:(A)wl_prog live nlive lt (c:(A)asm_config) (k:B).
     let comp = FST (remove_dead p live nlive lt) in
     (flat_exp_conventions p ==> flat_exp_conventions comp) /\
     (full_inst_ok_less c p ==> full_inst_ok_less c comp) /\
     (pre_alloc_conventions p ==> pre_alloc_conventions comp) /\
     (every_inst P p ==> every_inst P comp) /\
     (wf_cutsets p ==> wf_cutsets comp) /\
     (wordConvs_extract_labels p = wordConvs_extract_labels comp)`,
  REWRITE_TAC[LET_DEF; LET_END_DEF; pre_alloc_conventions_def] THEN
  SIMP_TAC[WPROOF2AUX_rd_fec; WPROOF2AUX_rd_fiol; WPROOF2AUX_rd_esv; WPROOF2AUX_rd_cac;
           WPROOF2AUX_rd_every_inst; WPROOF2AUX_rd_wf_cutsets; WPROOF2AUX_rd_el]);;

let remove_dead_prog_conventions = prove
 (`(flat_exp_conventions (p:(A)wl_prog) ==> flat_exp_conventions (remove_dead_prog p)) /\
   (full_inst_ok_less (c:(A)asm_config) p ==> full_inst_ok_less c (remove_dead_prog p)) /\
   (pre_alloc_conventions p ==> pre_alloc_conventions (remove_dead_prog p)) /\
   (every_inst P p ==> every_inst P (remove_dead_prog p)) /\
   (wf_cutsets p ==> wf_cutsets (remove_dead_prog p)) /\
   wordConvs_extract_labels p = wordConvs_extract_labels (remove_dead_prog p)`,
  MP_TAC(ISPECL [`p:(A)wl_prog`; `LN:1 spt`; `[]:store_name list`;
                 `[]:(1 spt#1 spt)list`; `c:(A)asm_config`; `0`]
                remove_dead_conventions) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; GSYM remove_dead_prog_def]);;

let word_get_code_labels_remove_dead = prove
 (`!ps:(A)wl_prog live nlive lt.
     wordConvs_get_code_labels (FST (remove_dead ps live nlive lt)) SUBSET
     wordConvs_get_code_labels ps`,
  WPROOF2AUX_PROG_STEP_TAC [remove_dead_def] THEN
  REWRITE_TAC[wordConvs_get_code_labels_def; SUBSET_REFL] THEN
  REPEAT (FIRST [COND_CASES_TAC; TOP_CASE_TAC] THEN
          CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND; FST; SND;
                           wordConvs_get_code_labels_def; SUBSET_REFL]) THEN
  ASM SET_TAC[]);;

let word_get_code_labels_remove_dead_prog = prove
 (`wordConvs_get_code_labels (remove_dead_prog (ps:(A)wl_prog)) SUBSET
   wordConvs_get_code_labels ps`,
  REWRITE_TAC[remove_dead_prog_def; word_get_code_labels_remove_dead]);;

let word_good_handlers_remove_dead = prove
 (`!ps:(A)wl_prog live nlive lt.
     good_handlers n (FST (remove_dead ps live nlive lt)) <=> good_handlers n ps`,
  WPROOF2AUX_PROG_STEP_TAC [remove_dead_def] THEN
  REPEAT COND_CASES_TAC THEN
  WPROOF2AUX_SKIP_FACTS_TAC `good_handlers n:(A)wl_prog->bool` [good_handlers_def] THEN
  WPROOF2AUX_SCT_FIN_TAC [good_handlers_def]);;

let word_good_handlers_remove_dead_prog = prove
 (`good_handlers n (remove_dead_prog (ps:(A)wl_prog)) <=> good_handlers n ps`,
  REWRITE_TAC[remove_dead_prog_def; word_good_handlers_remove_dead]);;
(* ------------------------------------------------------------------------- *)
(* word_common_subexp_elim                                                   *)
(* ------------------------------------------------------------------------- *)

(* word_cse replaces some instructions by moves                              *)

let WPROOF2AUX_atda_cases = prove
 (`!data r i (x:(A)wl_prog).
     SND (add_to_data_aux data r i x) = x \/
     ?pr ms. SND (add_to_data_aux data r i x) = wl_Move pr ms`,
  REPEAT GEN_TAC THEN REWRITE_TAC[add_to_data_aux_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (FIRST [COND_CASES_TAC; TOP_CASE_TAC]) THEN REWRITE_TAC[SND] THEN MESON_TAC[]);;

let WPROOF2AUX_atla_cases = prove
 (`!data r i (x:(A)wl_prog).
     SND (add_to_load_aux data r i x) = x \/
     ?pr ms. SND (add_to_load_aux data r i x) = wl_Move pr ms`,
  REPEAT GEN_TAC THEN REWRITE_TAC[add_to_load_aux_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (FIRST [COND_CASES_TAC; TOP_CASE_TAC]) THEN REWRITE_TAC[SND] THEN MESON_TAC[]);;

let WPROOF2AUX_cseInst_cases = prove
 (`!data (i:(A)inst).
     SND (word_cseInst data i) = wl_Inst i \/
     ?pr ms. SND (word_cseInst data i) = wl_Move pr ms`,
  MATCH_MP_TAC word_cseInst_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[word_cseInst_def; add_to_data_def; add_to_data_const_def;
              LET_DEF; LET_END_DEF] THEN
  REPEAT (FIRST [COND_CASES_TAC; TOP_CASE_TAC]) THEN REWRITE_TAC[SND] THEN
  MESON_TAC[WPROOF2AUX_atda_cases; WPROOF2AUX_atla_cases]);;

(* split the instruction results of word_cse in the goal                     *)

let WPROOF2AUX_CSE_LEAF_TAC : tactic = fun (asl,w as g) ->
  let is_leaf t =
    is_comb t &&
    (try fst(dest_const(rator t)) = "SND" with Failure _ -> false) &&
    (let h = fst(strip_comb(rand t)) in
     is_const h && mem (fst(dest_const h))
                       ["word_cseInst"; "add_to_data_aux"; "add_to_load_aux"]) in
  let t = find_term is_leaf w in
  let h,args = strip_comb(rand t) in
  let th = match fst(dest_const h) with
      "word_cseInst" -> WPROOF2AUX_cseInst_cases
    | "add_to_data_aux" -> WPROOF2AUX_atda_cases
    | _ -> WPROOF2AUX_atla_cases in
  (MP_TAC(ISPECL args th) THEN
   DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
     (X_CHOOSE_THEN `pr:num` (X_CHOOSE_THEN `ms:(num#num)list` SUBST1_TAC)))) g;;

let WPROOF2AUX_CSE_FIN_TAC (ths:thm list) : tactic =
  REWRITE_TAC ths THEN CASE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC ths THEN
  REPEAT (FIRST [COND_CASES_TAC; TOP_CASE_TAC; WPROOF2AUX_CSE_LEAF_TAC] THEN
          CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND; FST; SND] THEN ASM_SIMP_TAC ths);;

let WPROOF2AUX_wcse_SND = prove
 (`!prog:(A)wl_prog.
     word_common_subexp_elim prog = SND (word_cse empty_data prog)`,
  REWRITE_TAC[word_common_subexp_elim_def; LET_DEF; LET_END_DEF;
              WPROOF2AUX_pair_CASE_FST_SND]);;

let WPROOF2AUX_cse_el = prove
 (`!p data. wordConvs_extract_labels (SND (word_cse data (p:(A)wl_prog))) =
            wordConvs_extract_labels p`,
  WPROOF2AUX_PROG_STEP_TAC [word_cse_def] THEN
  WPROOF2AUX_CSE_FIN_TAC [wordConvs_extract_labels_def]);;

let word_cse_extract_labels = prove
 (`!p:(A)wl_prog d d1 p1.
     word_cse d p = (d1,p1) ==> wordConvs_extract_labels p1 = wordConvs_extract_labels p`,
  MESON_TAC[WPROOF2AUX_cse_el; SND]);;

let extract_labels_word_common_subexp_elim = prove
 (`wordConvs_extract_labels (word_common_subexp_elim (p:(A)wl_prog)) =
   wordConvs_extract_labels p`,
  REWRITE_TAC[WPROOF2AUX_wcse_SND; WPROOF2AUX_cse_el]);;

let word_cseInst_not_created_subprogs = prove
 (`!env (i:(A)inst). not_created_subprogs P (SND (word_cseInst env i))`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_THEN2 SUBST1_TAC (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
    (ISPECL [`env:knowledge`; `i:(A)inst`] WPROOF2AUX_cseInst_cases) THEN
  REWRITE_TAC[not_created_subprogs_def]);;

let word_cse_not_created_subprogs = prove
 (`!p:(A)wl_prog env.
     not_created_subprogs P p ==> not_created_subprogs P (SND (word_cse env p))`,
  WPROOF2AUX_PROG_STEP_TAC [word_cse_def] THEN
  WPROOF2AUX_CSE_FIN_TAC [not_created_subprogs_def]);;

let word_common_subexp_elim_not_created_subprogs = prove
 (`not_created_subprogs P (prog:(A)wl_prog) ==>
   not_created_subprogs P (word_common_subexp_elim prog)`,
  REWRITE_TAC[WPROOF2AUX_wcse_SND; word_cse_not_created_subprogs]);;

let WPROOF2AUX_cse_gh = prove
 (`!p data. good_handlers q (SND (word_cse data (p:(A)wl_prog))) <=> good_handlers q p`,
  WPROOF2AUX_PROG_STEP_TAC [word_cse_def] THEN
  WPROOF2AUX_CSE_FIN_TAC [good_handlers_def]);;

let word_good_handlers_word_common_subexp_elim = prove
 (`good_handlers q (word_common_subexp_elim (p:(A)wl_prog)) <=> good_handlers q p`,
  REWRITE_TAC[WPROOF2AUX_wcse_SND; WPROOF2AUX_cse_gh]);;

let WPROOF2AUX_cse_gcl = prove
 (`!p data. wordConvs_get_code_labels (SND (word_cse data (p:(A)wl_prog))) SUBSET
            wordConvs_get_code_labels p`,
  WPROOF2AUX_PROG_STEP_TAC [word_cse_def] THEN
  WPROOF2AUX_CSE_FIN_TAC [wordConvs_get_code_labels_def; SUBSET_REFL; EMPTY_SUBSET] THEN
  ASM SET_TAC[]);;

let word_cse_get_code_labels = prove
 (`!p data data' (q:(A)wl_prog).
     word_cse data p = (data',q) ==>
     wordConvs_get_code_labels q SUBSET wordConvs_get_code_labels p`,
  MESON_TAC[WPROOF2AUX_cse_gcl; SND]);;

let word_get_code_labels_word_common_subexp_elim = prove
 (`wordConvs_get_code_labels (word_common_subexp_elim (p:(A)wl_prog)) SUBSET
   wordConvs_get_code_labels p`,
  REWRITE_TAC[WPROOF2AUX_wcse_SND; WPROOF2AUX_cse_gcl]);;

let WPROOF2AUX_cse_fec = prove
 (`!p data. flat_exp_conventions p ==>
            flat_exp_conventions (SND (word_cse data (p:(A)wl_prog)))`,
  WPROOF2AUX_PROG_STEP_TAC [word_cse_def] THEN
  WPROOF2AUX_CSE_FIN_TAC [flat_exp_conventions_def] THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[]);;

let word_cse_flat_exp_conventions = prove
 (`!p data data' (q:(A)wl_prog).
     flat_exp_conventions p /\ word_cse data p = (data',q) ==> flat_exp_conventions q`,
  MESON_TAC[WPROOF2AUX_cse_fec; SND]);;

let flat_exp_conventions_word_common_subexp_elim = prove
 (`flat_exp_conventions (p:(A)wl_prog) ==>
   flat_exp_conventions (word_common_subexp_elim p)`,
  REWRITE_TAC[WPROOF2AUX_wcse_SND; WPROOF2AUX_cse_fec]);;

let WPROOF2AUX_cse_wf_cutsets = prove
 (`!p data. wf_cutsets p ==> wf_cutsets (SND (word_cse data (p:(A)wl_prog)))`,
  WPROOF2AUX_PROG_STEP_TAC [word_cse_def] THEN
  WPROOF2AUX_CSE_FIN_TAC [wf_cutsets_def] THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[]);;

let word_cse_wf_cutsets = prove
 (`!p data data' (q:(A)wl_prog).
     wf_cutsets p /\ word_cse data p = (data',q) ==> wf_cutsets q`,
  MESON_TAC[WPROOF2AUX_cse_wf_cutsets; SND]);;

let wf_cutsets_word_common_subexp_elim = prove
 (`wf_cutsets (p:(A)wl_prog) ==> wf_cutsets (word_common_subexp_elim p)`,
  REWRITE_TAC[WPROOF2AUX_wcse_SND; WPROOF2AUX_cse_wf_cutsets]);;
(* ------------------------------------------------------------------------- *)
(* copy_prop                                                                 *)
(* ------------------------------------------------------------------------- *)

(* HOL4 boring_tac (an ML tactic) is not ported: the WF induction tactics   *)
(* above are used instead                                                    *)

let WPROOF2AUX_cpi_cases = prove
 (`!(i:(A)inst) cs.
     FST (copy_prop_inst i cs) = wl_Skip \/ ?j. FST (copy_prop_inst i cs) = wl_Inst j`,
  MATCH_MP_TAC copy_prop_inst_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[copy_prop_inst_def; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND; FST; SND] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[FST; SND] THEN MESON_TAC[]);;

(* split the copy_prop_inst results in the goal                              *)

let WPROOF2AUX_CP_LEAF_TAC : tactic = fun (asl,w as g) ->
  let is_leaf t =
    is_comb t &&
    (try fst(dest_const(rator t)) = "FST" with Failure _ -> false) &&
    (let h = fst(strip_comb(rand t)) in
     is_const h && fst(dest_const h) = "copy_prop_inst") in
  let t = find_term is_leaf w in
  let _,args = strip_comb(rand t) in
  (MP_TAC(ISPECL args WPROOF2AUX_cpi_cases) THEN
   DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `j:(A)inst` SUBST1_TAC))) g;;

let WPROOF2AUX_CP_FIN_TAC (ths:thm list) : tactic =
  REWRITE_TAC ths THEN CASE_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC ths THEN
  REPEAT (FIRST [COND_CASES_TAC; TOP_CASE_TAC; WPROOF2AUX_CP_LEAF_TAC] THEN
          CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND; FST; SND] THEN ASM_SIMP_TAC ths);;

let wf_cutsets_copy_prop_aux = prove
 (`!p:(A)wl_prog cs. wf_cutsets p ==> wf_cutsets (FST (copy_prop_prog p cs))`,
  WPROOF2AUX_PROG_STEP_TAC [copy_prop_prog_def] THEN
  WPROOF2AUX_CP_FIN_TAC [wf_cutsets_def]);;

let wf_cutsets_copy_prop = prove
 (`wf_cutsets (p:(A)wl_prog) ==> wf_cutsets (copy_prop p)`,
  REWRITE_TAC[copy_prop_def; wf_cutsets_copy_prop_aux]);;

let WPROOF2AUX_cpi_dtr = prove
 (`!(i:(A)inst) cs.
     distinct_tar_reg i ==> every_inst distinct_tar_reg (FST (copy_prop_inst i cs))`,
  MATCH_MP_TAC copy_prop_inst_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[copy_prop_inst_def; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND; FST; SND] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[FST; SND; every_inst_def; distinct_tar_reg_def; injectivity "reg_imm"] THEN
  CASE_REWRITE_TAC[distinct_tar_reg_def] THEN ASM_MESON_TAC[]);;

let every_inst_distinct_tar_reg_copy_prop_aux = prove
 (`!p:(A)wl_prog cs.
     every_inst distinct_tar_reg p ==>
     every_inst distinct_tar_reg (FST (copy_prop_prog p cs))`,
  WPROOF2AUX_PROG_STEP_TAC [copy_prop_prog_def] THEN
  WPROOF2AUX_SCT_FIN_IMP_TAC [every_inst_def; distinct_tar_reg_def; WPROOF2AUX_cpi_dtr;
                              injectivity "reg_imm"] THEN
  ASM_MESON_TAC[]);;

let every_inst_distinct_tar_reg_copy_prop = prove
 (`every_inst distinct_tar_reg (p:(A)wl_prog) ==>
   every_inst distinct_tar_reg (copy_prop p)`,
  REWRITE_TAC[copy_prop_def; every_inst_distinct_tar_reg_copy_prop_aux]);;

let extract_labels_copy_prop_aux = prove
 (`!p:(A)wl_prog cs.
     wordConvs_extract_labels (FST (copy_prop_prog p cs)) = wordConvs_extract_labels p`,
  WPROOF2AUX_PROG_STEP_TAC [copy_prop_prog_def] THEN
  WPROOF2AUX_CP_FIN_TAC [wordConvs_extract_labels_def]);;

let extract_labels_copy_prop = prove
 (`wordConvs_extract_labels (copy_prop (p:(A)wl_prog)) = wordConvs_extract_labels p`,
  REWRITE_TAC[copy_prop_def; extract_labels_copy_prop_aux]);;

let flat_exp_conventions_copy_prop_aux = prove
 (`!p:(A)wl_prog cs.
     flat_exp_conventions p ==> flat_exp_conventions (FST (copy_prop_prog p cs))`,
  WPROOF2AUX_PROG_STEP_TAC [copy_prop_prog_def] THEN
  WPROOF2AUX_CP_FIN_TAC [flat_exp_conventions_def; flat_exp_conventions_ShareInst;
                         WPROOF2AUX_fec_Set; copy_prop_share_def] THEN
  CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[distinctness "wl_exp"; injectivity "wl_exp";
                              distinctness "binop"; NOT_CONS_NIL; CONS_11]) THEN
  ASM_MESON_TAC[]);;

let flat_exp_conventions_copy_prop = prove
 (`flat_exp_conventions (p:(A)wl_prog) ==> flat_exp_conventions (copy_prop p)`,
  REWRITE_TAC[copy_prop_def; flat_exp_conventions_copy_prop_aux]);;

let copy_prop_prog_not_alloc_var_aux1 = prove
 (`(!x. ~is_alloc_var x ==> lookup x (copy_state_to_eq cs) = NONE) ==>
   ~is_alloc_var x ==>
   lookup x (copy_state_to_eq (remove_eq cs y)) = NONE`,
  REWRITE_TAC[remove_eq_def] THEN TOP_CASE_TAC THEN
  REWRITE_TAC[empty_eq_def; copy_state_INFO.ri_accessors; lookup_def] THEN
  MESON_TAC[]);;

let copy_prop_prog_not_alloc_var_aux2 = prove
 (`!cs. (!x. ~is_alloc_var x ==> lookup x (copy_state_to_eq cs) = NONE) ==>
        ~is_alloc_var x ==>
        lookup x (copy_state_to_eq (remove_eqs cs yy)) = NONE`,
  SPEC_TAC(`yy:num list`,`yy:num list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[remove_eqs_def] THENL
   [MESON_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] copy_prop_prog_not_alloc_var_aux1) THEN
    ASM_REWRITE_TAC[]]);;

(* the copy state maps only alloc vars: its operations keep this            *)

let WPROOF2AUX_nav_empty = prove
 (`!x. lookup x (copy_state_to_eq empty_eq) = NONE`,
  REWRITE_TAC[empty_eq_def; copy_state_INFO.ri_accessors; lookup_def]);;

let WPROOF2AUX_nav_set_eq = prove
 (`!cs x y. (!v. ~is_alloc_var v ==> lookup v (copy_state_to_eq cs) = NONE) ==>
            (!v. ~is_alloc_var v ==> lookup v (copy_state_to_eq (set_eq cs x y)) = NONE)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[set_eq_def] THEN
  REPEAT (FIRST [COND_CASES_TAC; TOP_CASE_TAC]) THEN
  ASM_SIMP_TAC[copy_state_INFO.ri_accessors; lookup_insert] THEN
  REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let WPROOF2AUX_nav_set_store_eq = prove
 (`!cs s y. (!v. ~is_alloc_var v ==> lookup v (copy_state_to_eq cs) = NONE) ==>
            (!v. ~is_alloc_var v ==>
                 lookup v (copy_state_to_eq (set_store_eq cs s y)) = NONE)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[set_store_eq_def] THEN
  REPEAT (FIRST [COND_CASES_TAC; TOP_CASE_TAC]) THEN
  ASM_SIMP_TAC[copy_state_INFO.ri_accessors; copy_state_INFO.ri_accfupds;
               lookup_insert; WPROOF2AUX_nav_empty] THEN
  REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let WPROOF2AUX_nav_merge_eqs = prove
 (`!cs ds. (!v. ~is_alloc_var v ==> lookup v (copy_state_to_eq cs) = NONE) ==>
           (!v. ~is_alloc_var v ==> lookup v (copy_state_to_eq (merge_eqs cs ds)) = NONE)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[merge_eqs_def; copy_state_INFO.ri_accessors; lookup_inter_eq] THEN
  CASE_REWRITE_TAC[]);;

let WPROOF2AUX_nav_copy_prop_move = prove
 (`!xs cs. (!v. ~is_alloc_var v ==> lookup v (copy_state_to_eq cs) = NONE) ==>
           (!v. ~is_alloc_var v ==>
                lookup v (copy_state_to_eq (SND (copy_prop_move xs cs))) = NONE)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[copy_prop_move_def; SND] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[copy_prop_move_def; LET_DEF; LET_END_DEF; WPROOF2AUX_pair_CASE_FST_SND;
              SND] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] WPROOF2AUX_nav_set_eq) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] copy_prop_prog_not_alloc_var_aux1) THEN
  ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let WPROOF2AUX_nav_cpi = prove
 (`!(i:(A)inst) cs.
     (!v. ~is_alloc_var v ==> lookup v (copy_state_to_eq cs) = NONE) ==>
     (!v. ~is_alloc_var v ==> lookup v (copy_state_to_eq (SND (copy_prop_inst i cs))) = NONE)`,
  MATCH_MP_TAC copy_prop_inst_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[copy_prop_inst_def; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND; FST; SND] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[FST; SND] THEN
  MESON_TAC[GEN_ALL copy_prop_prog_not_alloc_var_aux1;
            GEN_ALL copy_prop_prog_not_alloc_var_aux2]);;

let copy_prop_prog_not_alloc_var = prove
 (`!p:(A)wl_prog cs.
     (!x. ~is_alloc_var x ==> lookup x (copy_state_to_eq cs) = NONE) ==>
     (!x. ~is_alloc_var x ==>
          lookup x (copy_state_to_eq (SND (copy_prop_prog p cs))) = NONE)`,
  let norm = REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] in
  WPROOF2AUX_PROG_STEP_TAC [copy_prop_prog_def] THEN
  REPEAT STRIP_TAC THEN
  REPEAT (FIRST [COND_CASES_TAC; TOP_CASE_TAC] THEN
          CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND; FST; SND]) THEN
  RULE_ASSUM_TAC(fun th -> if is_forall(concl th) then norm th else th) THEN
  ASM_MESON_TAC[norm copy_prop_prog_not_alloc_var_aux1;
                norm copy_prop_prog_not_alloc_var_aux2; WPROOF2AUX_nav_empty;
                norm WPROOF2AUX_nav_set_eq; norm WPROOF2AUX_nav_set_store_eq;
                norm WPROOF2AUX_nav_merge_eqs; norm WPROOF2AUX_nav_copy_prop_move;
                norm WPROOF2AUX_nav_cpi]);;

(* split the variables of type reg_imm of the goal                           *)

let WPROOF2AUX_SPLIT_RI_TAC : tactic = fun (asl,w as g) ->
  let vs = filter (fun v -> type_of v = `:(A)reg_imm`) (frees w) in
  MAP_EVERY (fun v -> CASES_ON v) vs g;;

let WPROOF2AUX_not_alloc_even = prove
 (`!n. ~is_alloc_var (2 * n)`,
  GEN_TAC THEN REWRITE_TAC[is_alloc_var_def] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`2 * n`; `4`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(MP_TAC o AP_TERM `EVEN` o CONJUNCT1) THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN]);;

let WPROOF2AUX_not_alloc_small = prove
 (`~is_alloc_var 0 /\ ~is_alloc_var 2 /\ ~is_alloc_var 6 /\ ~is_alloc_var 8`,
  REWRITE_TAC[is_alloc_var_def] THEN CONV_TAC NUM_REDUCE_CONV);;

let WPROOF2AUX_lookup_eq_nav = prove
 (`!cs v. (!x. ~is_alloc_var x ==> lookup x (copy_state_to_eq cs) = NONE) /\
          ~is_alloc_var v ==> lookup_eq cs v = v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lookup_eq_def] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[]);;

let WPROOF2AUX_cac_Return_MAP = prove
 (`!cs ys. (!x. ~is_alloc_var x ==> lookup x (copy_state_to_eq cs) = NONE) /\
           ys = list_of_seq (\x. 2 * (x + 1)) (LENGTH ys)
           ==> MAP (lookup_eq cs) ys =
               list_of_seq (\x. 2 * (x + 1)) (LENGTH (MAP (lookup_eq cs) ys))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LENGTH_MAP] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[MAP_LIST_OF_SEQ] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC WPROOF2AUX_lookup_eq_nav THEN
  ASM_REWRITE_TAC[WPROOF2AUX_not_alloc_even]);;

let WPROOF2AUX_cpi_cac = prove
 (`!(i:(A)inst) cs.
     (!x. ~is_alloc_var x ==> lookup x (copy_state_to_eq cs) = NONE) ==>
     inst_arg_convention i ==> call_arg_convention (FST (copy_prop_inst i cs))`,
  MATCH_MP_TAC copy_prop_inst_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  WPROOF2AUX_SPLIT_RI_TAC THEN
  REWRITE_TAC[copy_prop_inst_def; lookup_eq_imm_def; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND; FST; SND] THEN
  REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[inst_arg_convention_def]) THEN
  RVEQ_TAC THEN
  ASM_SIMP_TAC[WPROOF2AUX_lookup_eq_nav; WPROOF2AUX_not_alloc_small] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[FST; SND; call_arg_convention_def; inst_arg_convention_def;
                  injectivity "reg_imm"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "reg_imm"]) THEN ASM_MESON_TAC[]);;

let WPROOF2AUX_cp_esv = prove
 (`!p:(A)wl_prog cs.
     every_stack_var P p ==> every_stack_var P (FST (copy_prop_prog p cs))`,
  WPROOF2AUX_PROG_STEP_TAC [copy_prop_prog_def] THEN
  WPROOF2AUX_CP_FIN_TAC [every_stack_var_def]);;

let WPROOF2AUX_cp_cac = prove
 (`!p:(A)wl_prog cs.
     (!x. ~is_alloc_var x ==> lookup x (copy_state_to_eq cs) = NONE) ==>
     call_arg_convention p ==> call_arg_convention (FST (copy_prop_prog p cs))`,
  let norm = REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] in
  WPROOF2AUX_PROG_STEP_TAC [copy_prop_prog_def] THEN
  REPEAT STRIP_TAC THEN
  REPEAT (FIRST [COND_CASES_TAC; TOP_CASE_TAC] THEN
          CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND; FST; SND]) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[call_arg_convention_def]) THEN
  ASM_SIMP_TAC[call_arg_convention_def; WPROOF2AUX_lookup_eq_nav;
               WPROOF2AUX_not_alloc_small] THEN
  TRY (MATCH_MP_TAC (norm WPROOF2AUX_cpi_cac) THEN CONJ_TAC THEN
       FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  TRY (MATCH_MP_TAC WPROOF2AUX_cac_Return_MAP THEN CONJ_TAC THEN
       FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o norm) THEN ASM_REWRITE_TAC[WPROOF2AUX_nav_empty] THEN
  MATCH_MP_TAC copy_prop_prog_not_alloc_var THEN ASM_REWRITE_TAC[]);;

let pre_alloc_conventions_copy_prop_aux = prove
 (`!p:(A)wl_prog cs.
     (!x. ~is_alloc_var x ==> lookup x (copy_state_to_eq cs) = NONE) ==>
     pre_alloc_conventions p ==>
     pre_alloc_conventions (FST (copy_prop_prog p cs))`,
  REWRITE_TAC[pre_alloc_conventions_def] THEN
  MESON_TAC[WPROOF2AUX_cp_esv; WPROOF2AUX_cp_cac]);;

let pre_alloc_conventions_copy_prop = prove
 (`pre_alloc_conventions (p:(A)wl_prog) ==> pre_alloc_conventions (copy_prop p)`,
  REWRITE_TAC[copy_prop_def] THEN
  MESON_TAC[pre_alloc_conventions_copy_prop_aux; WPROOF2AUX_nav_empty]);;

let WPROOF2AUX_cpi_fiol = prove
 (`!(i:(A)inst) cs.
     inst_ok_less ac i ==> full_inst_ok_less ac (FST (copy_prop_inst i cs))`,
  MATCH_MP_TAC copy_prop_inst_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  WPROOF2AUX_SPLIT_RI_TAC THEN
  REWRITE_TAC[copy_prop_inst_def; lookup_eq_imm_def; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND; FST; SND] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[FST; SND; full_inst_ok_less_def; inst_ok_less_def;
                  injectivity "reg_imm"; distinctness "reg_imm"] THEN
  CASE_REWRITE_TAC[inst_ok_less_def] THEN ASM_MESON_TAC[]);;

(* split variables of expression types until the rewrites ths and the       *)
(* closing tactic fin apply                                                  *)

let rec WPROOF2AUX_EXP_SPLIT_TAC (ths:thm list) (fin:tactic) : tactic = fun g ->
  (CASE_REWRITE_TAC ths THEN
   FIRST [fin THEN NO_TAC;
          (fun (asl,w as g) ->
             let tys = [`:(A)wl_exp`; `:((A)wl_exp)list`; `:binop`] in
             let vs = filter (fun v -> mem (type_of v) tys) (frees w) in
             (CASES_ON (hd vs) THEN WPROOF2AUX_EXP_SPLIT_TAC ths fin) g)]) g;;

let WPROOF2AUX_fiol_ShareInst_cps = prove
 (`!op v (exp:(A)wl_exp) cs.
     full_inst_ok_less ac (ShareInst op v exp) ==>
     full_inst_ok_less ac (ShareInst op v (copy_prop_share exp cs))`,
  REPEAT GEN_TAC THEN
  WPROOF2AUX_EXP_SPLIT_TAC [full_inst_ok_less_def; copy_prop_share_def; exp_to_addr_def]
    (REWRITE_TAC[]));;

let full_inst_ok_less_copy_prop_aux = prove
 (`!p:(A)wl_prog cs.
     full_inst_ok_less ac p ==> full_inst_ok_less ac (FST (copy_prop_prog p cs))`,
  WPROOF2AUX_PROG_STEP_TAC [copy_prop_prog_def] THEN
  WPROOF2AUX_SCT_FIN_IMP_TAC [full_inst_ok_less_def; WPROOF2AUX_cpi_fiol;
                              WPROOF2AUX_fiol_ShareInst_cps]);;

let full_inst_ok_less_copy_prop = prove
 (`full_inst_ok_less ac (p:(A)wl_prog) ==> full_inst_ok_less ac (copy_prop p)`,
  REWRITE_TAC[copy_prop_def; full_inst_ok_less_copy_prop_aux]);;

let word_get_code_labels_copy_prop = prove
 (`wordConvs_get_code_labels (copy_prop (ps:(A)wl_prog)) = wordConvs_get_code_labels ps`,
  REWRITE_TAC[copy_prop_def] THEN
  SPEC_TAC(`empty_eq`,`cs:copy_state`) THEN SPEC_TAC(`ps:(A)wl_prog`,`ps:(A)wl_prog`) THEN
  WPROOF2AUX_PROG_STEP_TAC [copy_prop_prog_def] THEN
  WPROOF2AUX_CP_FIN_TAC [wordConvs_get_code_labels_def]);;

let word_good_handlers_copy_prop = prove
 (`good_handlers n (copy_prop (ps:(A)wl_prog)) <=> good_handlers n ps`,
  REWRITE_TAC[copy_prop_def] THEN
  SPEC_TAC(`empty_eq`,`cs:copy_state`) THEN SPEC_TAC(`ps:(A)wl_prog`,`ps:(A)wl_prog`) THEN
  WPROOF2AUX_PROG_STEP_TAC [copy_prop_prog_def] THEN
  WPROOF2AUX_CP_FIN_TAC [good_handlers_def]);;

let copy_prop_not_created_subprogs = prove
 (`not_created_subprogs P (prog:(A)wl_prog) ==>
   not_created_subprogs P (copy_prop prog)`,
  REWRITE_TAC[copy_prop_def] THEN
  SPEC_TAC(`empty_eq`,`cs:copy_state`) THEN SPEC_TAC(`prog:(A)wl_prog`,`prog:(A)wl_prog`) THEN
  WPROOF2AUX_PROG_STEP_TAC [copy_prop_prog_def] THEN
  WPROOF2AUX_CP_FIN_TAC [not_created_subprogs_def]);;
(* ------------------------------------------------------------------------- *)
(* three_to_two_reg_prog                                                     *)
(* ------------------------------------------------------------------------- *)

(* split the instruction and arithmetic variables of the goal                *)

let WPROOF2AUX_TTR_SPLIT_TAC : tactic = fun (asl,w as g) ->
  let vs = filter (fun v -> type_of v = `:(A)inst`) (frees w) in
  (MAP_EVERY CASES_ON vs THEN
   (fun (asl,w as g) ->
      let vs2 = filter (fun v -> type_of v = `:(A)asm_arith`) (frees w) in
      MAP_EVERY CASES_ON vs2 g)) g;;

let WPROOF2AUX_TTR_TAC : tactic =
  GEN_TAC THEN REWRITE_TAC[three_to_two_reg_prog_def] THEN
  ASM_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[] THEN
  WPROOF2AUX_PROG_STEP_TAC [three_to_two_reg_def] THEN
  WPROOF2AUX_TTR_SPLIT_TAC THEN REWRITE_TAC[three_to_two_reg_def; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[];;

let three_to_two_reg_prog_lab_pres = prove
 (`!prog:(A)wl_prog.
     wordConvs_extract_labels prog =
     wordConvs_extract_labels (three_to_two_reg_prog b prog)`,
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN SPEC_TAC(`b:bool`,`b:bool`) THEN
  WPROOF2AUX_TTR_TAC THEN WPROOF2AUX_CP_FIN_TAC [wordConvs_extract_labels_def; APPEND]);;

let three_to_two_reg_prog_not_created_subprogs = prove
 (`!prog:(A)wl_prog.
     not_created_subprogs P prog ==>
     not_created_subprogs P (three_to_two_reg_prog b prog)`,
  SPEC_TAC(`b:bool`,`b:bool`) THEN
  WPROOF2AUX_TTR_TAC THEN WPROOF2AUX_CP_FIN_TAC [not_created_subprogs_def]);;

let three_to_two_reg_prog_two_reg_inst = prove
 (`!prog:(A)wl_prog. b ==> every_inst two_reg_inst (three_to_two_reg_prog b prog)`,
  SPEC_TAC(`b:bool`,`b:bool`) THEN
  WPROOF2AUX_TTR_TAC THEN WPROOF2AUX_CP_FIN_TAC [every_inst_def; two_reg_inst_def]);;

let three_to_two_reg_prog_wf_cutsets = prove
 (`!prog:(A)wl_prog. wf_cutsets prog ==> wf_cutsets (three_to_two_reg_prog b prog)`,
  SPEC_TAC(`b:bool`,`b:bool`) THEN
  WPROOF2AUX_TTR_TAC THEN WPROOF2AUX_CP_FIN_TAC [wf_cutsets_def]);;

let three_to_two_reg_prog_pre_alloc_conventions = prove
 (`!prog:(A)wl_prog.
     pre_alloc_conventions prog ==>
     pre_alloc_conventions (three_to_two_reg_prog b prog)`,
  REWRITE_TAC[pre_alloc_conventions_def] THEN
  SUBGOAL_THEN `!prog:(A)wl_prog.
                  every_stack_var is_stack_var prog ==>
                  every_stack_var is_stack_var (three_to_two_reg_prog b prog)`
    (fun th -> SIMP_TAC[th]) THENL
   [SPEC_TAC(`b:bool`,`b:bool`) THEN
    WPROOF2AUX_TTR_TAC THEN WPROOF2AUX_CP_FIN_TAC [every_stack_var_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `!prog:(A)wl_prog.
                  call_arg_convention prog ==>
                  call_arg_convention (three_to_two_reg_prog b prog)`
    (fun th -> SIMP_TAC[th]) THEN
  SPEC_TAC(`b:bool`,`b:bool`) THEN
  WPROOF2AUX_TTR_TAC THEN
  WPROOF2AUX_CP_FIN_TAC [call_arg_convention_def; inst_arg_convention_def] THEN
  TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  WPROOF2AUX_SPLIT_RI_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[inst_arg_convention_def]) THEN
  ASM_SIMP_TAC[inst_arg_convention_def]);;

let three_to_two_reg_prog_flat_exp_conventions = prove
 (`!prog:(A)wl_prog.
     flat_exp_conventions prog ==>
     flat_exp_conventions (three_to_two_reg_prog b prog)`,
  SPEC_TAC(`b:bool`,`b:bool`) THEN
  WPROOF2AUX_TTR_TAC THEN WPROOF2AUX_CP_FIN_TAC [flat_exp_conventions_def]);;

let three_to_two_reg_prog_full_inst_ok_less = prove
 (`!prog:(A)wl_prog.
     full_inst_ok_less c prog ==> full_inst_ok_less c (three_to_two_reg_prog b prog)`,
  SPEC_TAC(`b:bool`,`b:bool`) THEN
  WPROOF2AUX_TTR_TAC THEN
  WPROOF2AUX_CP_FIN_TAC [full_inst_ok_less_def; inst_ok_less_def; every_inst_def] THEN
  WPROOF2AUX_SPLIT_RI_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[inst_ok_less_def]) THEN
  ASM_REWRITE_TAC[inst_ok_less_def]);;

let word_get_code_labels_three_to_two_reg_prog = prove
 (`!ps:(A)wl_prog.
     wordConvs_get_code_labels (three_to_two_reg_prog b ps) = wordConvs_get_code_labels ps`,
  SPEC_TAC(`b:bool`,`b:bool`) THEN
  WPROOF2AUX_TTR_TAC THEN WPROOF2AUX_CP_FIN_TAC [wordConvs_get_code_labels_def; UNION_EMPTY]);;

let word_good_handlers_three_to_two_reg_prog = prove
 (`!ps:(A)wl_prog.
     good_handlers n (three_to_two_reg_prog b ps) <=> good_handlers n ps`,
  SPEC_TAC(`b:bool`,`b:bool`) THEN
  WPROOF2AUX_TTR_TAC THEN WPROOF2AUX_CP_FIN_TAC [good_handlers_def]);;
(* ------------------------------------------------------------------------- *)
(* remove_unreach                                                            *)
(* ------------------------------------------------------------------------- *)

let WPROOF2AUX_dest_Seq_Move_SOME = prove
 (`!p:(A)wl_prog n l rest.
     dest_Seq_Move p = SOME (n,l,rest) ==>
     (p = wl_Move n l /\ rest = wl_Skip) \/ p = wl_Seq (wl_Move n l) rest`,
  MATCH_MP_TAC dest_Seq_Move_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[dest_Seq_Move_def; option_DISTINCT; option_INJ; PAIR_EQ] THEN
  MESON_TAC[]);;

(* the shapes of SimpSeq p1 p2                                                *)

let WPROOF2AUX_SimpSeq_cases = prove
 (`!p1 p2:(A)wl_prog.
     SimpSeq p1 p2 = p1 \/ SimpSeq p1 p2 = p2 \/ SimpSeq p1 p2 = wl_Seq p1 p2 \/
     ?n1 l1 n2 l2 rest l.
       p1 = wl_Move n1 l1 /\
       (p2 = wl_Move n2 l2 /\ rest = wl_Skip \/ p2 = wl_Seq (wl_Move n2 l2) rest) /\
       (SimpSeq p1 p2 = wl_Move (MAX n1 n2) l \/
        SimpSeq p1 p2 = wl_Seq (wl_Move (MAX n1 n2) l) rest)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SimpSeq_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  CASES_ON `p1:(A)wl_prog` THEN CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `dest_Seq_Move (p2:(A)wl_prog)`
               (nchotomy_of_type `:(num#(num#num)list#(A)wl_prog)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`a:num#(num#num)list#(A)wl_prog`,`a:num#(num#num)list#(A)wl_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WPROOF2AUX_dest_Seq_Move_SOME) THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let WPROOF2AUX_SimpSeq_closed = prove
 (`!(Q:(A)wl_prog->bool).
     Q wl_Skip /\ (!p q. Q (wl_Seq p q) <=> Q p /\ Q q) /\ (!n l. Q (wl_Move n l))
     ==> !p1 p2. Q p1 /\ Q p2 ==> Q (SimpSeq p1 p2)`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p1:(A)wl_prog`; `p2:(A)wl_prog`] WPROOF2AUX_SimpSeq_cases) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT (FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_var(lhs(concl th))))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
    `!p q. (Q:(A)wl_prog->bool) (wl_Seq p q) <=> Q p /\ Q q`]) THEN
  ASM_REWRITE_TAC[]);;

let WPROOF2AUX_SimpSeq_el = prove
 (`!p1 p2:(A)wl_prog.
     wordConvs_extract_labels (SimpSeq p1 p2) = wordConvs_extract_labels p1 \/
     wordConvs_extract_labels (SimpSeq p1 p2) = wordConvs_extract_labels p2 \/
     wordConvs_extract_labels (SimpSeq p1 p2) =
     APPEND (wordConvs_extract_labels p1) (wordConvs_extract_labels p2)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`p1:(A)wl_prog`; `p2:(A)wl_prog`] WPROOF2AUX_SimpSeq_cases) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[wordConvs_extract_labels_def; APPEND]);;

let WPROOF2AUX_SimpSeq_gcl = prove
 (`!p1 p2:(A)wl_prog.
     wordConvs_get_code_labels (SimpSeq p1 p2) = wordConvs_get_code_labels p1 \/
     wordConvs_get_code_labels (SimpSeq p1 p2) = wordConvs_get_code_labels p2 \/
     wordConvs_get_code_labels (SimpSeq p1 p2) =
     wordConvs_get_code_labels p1 UNION wordConvs_get_code_labels p2`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`p1:(A)wl_prog`; `p2:(A)wl_prog`] WPROOF2AUX_SimpSeq_cases) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[wordConvs_get_code_labels_def; UNION_EMPTY]);;
(* induction over Seq_assoc_right for a property closed under SimpSeq       *)

let WPROOF2AUX_SAR_TAC (simpseq_th:thm) (ths:thm list) : tactic =
  MATCH_MP_TAC word_unreach_Seq_assoc_right_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE ths) THEN
  POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[word_unreach_Seq_assoc_right_def] THEN CASE_REWRITE_TAC[] THEN
  TRY (MATCH_MP_TAC simpseq_th) THEN
  ASM_SIMP_TAC ths THEN CASE_REWRITE_TAC ths THEN ASM_SIMP_TAC ths THEN
  TRY (REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let word_get_code_labels_dest_Seq_Move = prove
 (`!p:(A)wl_prog.
     dest_Seq_Move p = SOME (x,y,z) ==>
     wordConvs_get_code_labels z = wordConvs_get_code_labels p`,
  GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP WPROOF2AUX_dest_Seq_Move_SOME) THEN
  ASM_REWRITE_TAC[wordConvs_get_code_labels_def; UNION_EMPTY]);;

let word_get_code_labels_SimpSeq = prove
 (`wordConvs_get_code_labels (SimpSeq p q:(A)wl_prog) SUBSET
   wordConvs_get_code_labels p UNION wordConvs_get_code_labels q`,
  MP_TAC(ISPECL [`p:(A)wl_prog`; `q:(A)wl_prog`] WPROOF2AUX_SimpSeq_gcl) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* add the instance of th (a statement about SimpSeq with its two         *)
(* arguments free or quantified) for the SimpSeq in the goal                 *)

let WPROOF2AUX_SIMPSEQ_INST_TAC (th:thm) : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> is_comb t && is_comb(rator t) &&
                       (try fst(dest_const(rator(rator t))) = "SimpSeq"
                        with Failure _ -> false)) w in
  let th' = SPEC_ALL th in
  let pat = find_term (fun t -> is_comb t && is_comb(rator t) &&
                         (try fst(dest_const(rator(rator t))) = "SimpSeq"
                          with Failure _ -> false)) (concl th') in
  let i = term_match [] pat t in
  MP_TAC(INSTANTIATE i th') g;;

let word_get_code_labels_Seq_assoc_right = prove
 (`!ps qs:(A)wl_prog.
     wordConvs_get_code_labels (Seq_assoc_right ps qs) SUBSET
     wordConvs_get_code_labels ps UNION wordConvs_get_code_labels qs`,
  MATCH_MP_TAC word_unreach_Seq_assoc_right_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[word_unreach_Seq_assoc_right_def] THEN CASE_REWRITE_TAC[] THEN
  TRY (WPROOF2AUX_SIMPSEQ_INST_TAC word_get_code_labels_SimpSeq) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[wordConvs_get_code_labels_def; UNION_EMPTY]) THEN
  CASE_REWRITE_TAC[wordConvs_get_code_labels_def; UNION_EMPTY] THEN
  ASM SET_TAC[]);;

let word_get_code_labels_remove_unreach = prove
 (`wordConvs_get_code_labels (remove_unreach (ps:(A)wl_prog)) SUBSET
   wordConvs_get_code_labels ps`,
  REWRITE_TAC[remove_unreach_def] THEN
  MP_TAC(ISPECL [`ps:(A)wl_prog`; `wl_Skip:(A)wl_prog`]
                word_get_code_labels_Seq_assoc_right) THEN
  REWRITE_TAC[wordConvs_get_code_labels_def; UNION_EMPTY]);;

let word_good_handlers_SimpSeq = prove
 (`good_handlers n ps /\ good_handlers n qs ==> good_handlers n (SimpSeq ps qs:(A)wl_prog)`,
  MP_TAC(ISPEC `good_handlers n:(A)wl_prog->bool` WPROOF2AUX_SimpSeq_closed) THEN
  REWRITE_TAC[good_handlers_def] THEN MESON_TAC[]);;

let word_good_handlers_Seq_assoc_right = prove
 (`good_handlers n ps /\ good_handlers n qs ==>
   good_handlers n (Seq_assoc_right ps qs:(A)wl_prog)`,
  SPEC_TAC(`qs:(A)wl_prog`,`qs:(A)wl_prog`) THEN SPEC_TAC(`ps:(A)wl_prog`,`ps:(A)wl_prog`) THEN
  WPROOF2AUX_SAR_TAC word_good_handlers_SimpSeq [good_handlers_def]);;

let word_good_handlers_remove_unreach = prove
 (`good_handlers n (ps:(A)wl_prog) ==> good_handlers n (remove_unreach ps)`,
  REWRITE_TAC[remove_unreach_def] THEN DISCH_TAC THEN
  MATCH_MP_TAC word_good_handlers_Seq_assoc_right THEN
  ASM_REWRITE_TAC[good_handlers_def]);;

let SimpSeq_not_created_subprogs = prove
 (`not_created_subprogs P ps /\ not_created_subprogs P qs ==>
   not_created_subprogs P (SimpSeq ps qs:(A)wl_prog)`,
  MP_TAC(ISPEC `not_created_subprogs P:(A)wl_prog->bool` WPROOF2AUX_SimpSeq_closed) THEN
  REWRITE_TAC[not_created_subprogs_def] THEN MESON_TAC[]);;

let wordConvsProof_Seq_assoc_right_not_created_subprogs = prove
 (`not_created_subprogs P ps /\ not_created_subprogs P qs ==>
   not_created_subprogs P (Seq_assoc_right ps qs:(A)wl_prog)`,
  SPEC_TAC(`qs:(A)wl_prog`,`qs:(A)wl_prog`) THEN SPEC_TAC(`ps:(A)wl_prog`,`ps:(A)wl_prog`) THEN
  WPROOF2AUX_SAR_TAC SimpSeq_not_created_subprogs [not_created_subprogs_def]);;

let remove_unreach_not_created_subprogs = prove
 (`not_created_subprogs P (prog:(A)wl_prog) ==>
   not_created_subprogs P (remove_unreach prog)`,
  REWRITE_TAC[remove_unreach_def] THEN DISCH_TAC THEN
  MATCH_MP_TAC wordConvsProof_Seq_assoc_right_not_created_subprogs THEN
  ASM_REWRITE_TAC[not_created_subprogs_def]);;
let extract_labels_SimpSeq = prove
 (`set_of_list (wordConvs_extract_labels (SimpSeq p1 p2:(A)wl_prog)) SUBSET
   set_of_list (wordConvs_extract_labels (wl_Seq p1 p2))`,
  MP_TAC(ISPECL [`p1:(A)wl_prog`; `p2:(A)wl_prog`] WPROOF2AUX_SimpSeq_el) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[wordConvs_extract_labels_def; SET_OF_LIST_APPEND] THEN SET_TAC[]);;

let WPROOF2AUX_labels_rel_NIL2 = prove
 (`!xs:A list. labels_rel xs []`,
  REWRITE_TAC[labels_rel_def; ALL_DISTINCT; set_of_list; EMPTY_SUBSET]);;

let WPROOF2AUX_lr_SimpSeq = prove
 (`!p1 p2:(A)wl_prog.
     labels_rel (APPEND (wordConvs_extract_labels p1) (wordConvs_extract_labels p2))
                (wordConvs_extract_labels (SimpSeq p1 p2))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`p1:(A)wl_prog`; `p2:(A)wl_prog`] WPROOF2AUX_SimpSeq_el) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[labels_rel_refl] THEN
  MESON_TAC[WPROOF2AUX_wc_labels_rel_app1; WPROOF2AUX_wc_labels_rel_app2; labels_rel_refl]);;

(* the labels of Seq_assoc_right p1 p2 are related to those of p1 and p2    *)

let WPROOF2AUX_lr_sar = prove
 (`!p1 p2:(A)wl_prog.
     labels_rel (APPEND (wordConvs_extract_labels p1) (wordConvs_extract_labels p2))
                (wordConvs_extract_labels (Seq_assoc_right p1 p2))`,
  MATCH_MP_TAC word_unreach_Seq_assoc_right_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN TRY WPROOF2AUX_wc_CALL_SPLIT_TAC THEN
  REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[wordConvs_extract_labels_def; APPEND_NIL]) THEN
  REWRITE_TAC[word_unreach_Seq_assoc_right_def] THEN CASE_REWRITE_TAC[] THEN
  FIRST
   [(* Skip *)
    REWRITE_TAC[wordConvs_extract_labels_def; APPEND; labels_rel_refl] THEN NO_TAC;
    (* Call NONE *)
    REWRITE_TAC[wordConvs_extract_labels_def] THEN
    CASE_REWRITE_TAC[WPROOF2AUX_labels_rel_NIL2] THEN NO_TAC;
    (* Seq *)
    MATCH_MP_TAC labels_rel_TRANS THEN
    EXISTS_TAC `APPEND (wordConvs_extract_labels (q1:(A)wl_prog))
                       (wordConvs_extract_labels (Seq_assoc_right q2 acc:(A)wl_prog))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[wordConvs_extract_labels_def; GSYM APPEND_ASSOC] THEN
      MATCH_MP_TAC labels_rel_APPEND THEN ASM_REWRITE_TAC[labels_rel_refl];
      FIRST_ASSUM ACCEPT_TAC] THEN NO_TAC;
    (* SimpSeq x acc *)
    W(fun (asl,w) ->
        let t = rand w in
        let x = rand(rator(rand t)) and acc = rand(rand t) in
        let el = `wordConvs_extract_labels:(A)wl_prog->(num#num)list` in
        MATCH_MP_TAC labels_rel_TRANS THEN
        EXISTS_TAC (mk_comb(mk_comb(`APPEND:(num#num)list->(num#num)list->(num#num)list`,
                                    mk_comb(el,x)), mk_comb(el,acc)))) THEN
    REWRITE_TAC[WPROOF2AUX_lr_SimpSeq] THEN
    MATCH_MP_TAC labels_rel_APPEND THEN REWRITE_TAC[labels_rel_refl] THEN
    REWRITE_TAC[wordConvs_extract_labels_def; LET_DEF; LET_END_DEF] THEN
    CASE_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    WPROOF2AUX_wc_LR_TAC]);;

let extract_labels_Seq_assoc_right_lemma = prove
 (`!p1 p2:(A)wl_prog.
     set_of_list (wordConvs_extract_labels (Seq_assoc_right p1 p2)) SUBSET
     set_of_list (wordConvs_extract_labels p1) UNION
     set_of_list (wordConvs_extract_labels p2)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`p1:(A)wl_prog`; `p2:(A)wl_prog`] WPROOF2AUX_lr_sar) THEN
  REWRITE_TAC[labels_rel_def; SET_OF_LIST_APPEND] THEN MESON_TAC[]);;

let extract_labels_remove_unreach = prove
 (`set_of_list (wordConvs_extract_labels (remove_unreach (p:(A)wl_prog))) SUBSET
   set_of_list (wordConvs_extract_labels p)`,
  REWRITE_TAC[remove_unreach_def] THEN
  MP_TAC(ISPECL [`p:(A)wl_prog`; `wl_Skip:(A)wl_prog`]
                extract_labels_Seq_assoc_right_lemma) THEN
  REWRITE_TAC[wordConvs_extract_labels_def; set_of_list; UNION_EMPTY]);;

let MEM_extract_labels_Seq_assoc_right_lemma = prove
 (`!p1 p2:(A)wl_prog x.
     MEM x (wordConvs_extract_labels (Seq_assoc_right p1 p2)) ==>
     MEM x (wordConvs_extract_labels p1) \/ MEM x (wordConvs_extract_labels p2)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`p1:(A)wl_prog`; `p2:(A)wl_prog`] extract_labels_Seq_assoc_right_lemma) THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_SET_OF_LIST] THEN MESON_TAC[]);;

let wordConvsProof_helper = prove
 (`!p1 p2:(A)wl_prog x.
     ~(MEM x (wordConvs_extract_labels p1) \/ MEM x (wordConvs_extract_labels p2)) ==>
     ~MEM x (wordConvs_extract_labels (Seq_assoc_right p1 p2))`,
  MESON_TAC[MEM_extract_labels_Seq_assoc_right_lemma]);;

let ALL_DISTINCT_extract_labels_Seq_assoc_right_lemma = prove
 (`!p1 p2:(A)wl_prog.
     ALL_DISTINCT (APPEND (wordConvs_extract_labels p1) (wordConvs_extract_labels p2)) ==>
     ALL_DISTINCT (wordConvs_extract_labels (Seq_assoc_right p1 p2))`,
  MESON_TAC[WPROOF2AUX_lr_sar; labels_rel_def]);;

let ALL_DISTINCT_extract_labels_remove_unreach = prove
 (`ALL_DISTINCT (wordConvs_extract_labels (p:(A)wl_prog)) ==>
   ALL_DISTINCT (wordConvs_extract_labels (remove_unreach p))`,
  REWRITE_TAC[remove_unreach_def] THEN
  MP_TAC(ISPECL [`p:(A)wl_prog`; `wl_Skip:(A)wl_prog`] WPROOF2AUX_lr_sar) THEN
  REWRITE_TAC[labels_rel_def; wordConvs_extract_labels_def; APPEND_NIL] THEN
  MESON_TAC[]);;

let labels_rel_remove_unreach = prove
 (`labels_rel (wordConvs_extract_labels (q:(A)wl_prog))
              (wordConvs_extract_labels (remove_unreach q))`,
  REWRITE_TAC[remove_unreach_def] THEN
  MP_TAC(ISPECL [`q:(A)wl_prog`; `wl_Skip:(A)wl_prog`] WPROOF2AUX_lr_sar) THEN
  REWRITE_TAC[wordConvs_extract_labels_def; APPEND_NIL]);;

let WPROOF2AUX_cac_SimpSeq = prove
 (`!p1 p2:(A)wl_prog.
     call_arg_convention p1 /\ call_arg_convention p2 ==>
     call_arg_convention (SimpSeq p1 p2)`,
  MP_TAC(ISPEC `call_arg_convention:(A)wl_prog->bool` WPROOF2AUX_SimpSeq_closed) THEN
  REWRITE_TAC[call_arg_convention_def] THEN MESON_TAC[]);;

let call_arg_convention_Seq_assoc_right_lemma = prove
 (`!p1 p2:(A)wl_prog.
     call_arg_convention p1 /\ call_arg_convention p2 ==>
     call_arg_convention (Seq_assoc_right p1 p2)`,
  WPROOF2AUX_SAR_TAC (SPEC_ALL WPROOF2AUX_cac_SimpSeq) [call_arg_convention_def]);;

let call_arg_convention_remove_unreach = prove
 (`call_arg_convention (p:(A)wl_prog) ==> call_arg_convention (remove_unreach p)`,
  REWRITE_TAC[remove_unreach_def] THEN DISCH_TAC THEN
  MATCH_MP_TAC call_arg_convention_Seq_assoc_right_lemma THEN
  ASM_REWRITE_TAC[call_arg_convention_def]);;

let WPROOF2AUX_esv_SimpSeq = prove
 (`!p1 p2:(A)wl_prog.
     every_stack_var P p1 /\ every_stack_var P p2 ==> every_stack_var P (SimpSeq p1 p2)`,
  MP_TAC(ISPEC `every_stack_var P:(A)wl_prog->bool` WPROOF2AUX_SimpSeq_closed) THEN
  REWRITE_TAC[every_stack_var_def] THEN MESON_TAC[]);;

let every_stack_var_is_stack_var_Seq_assoc_right_lemma = prove
 (`!p1 p2:(A)wl_prog.
     every_stack_var is_stack_var p1 /\ every_stack_var is_stack_var p2 ==>
     every_stack_var is_stack_var (Seq_assoc_right p1 p2)`,
  WPROOF2AUX_SAR_TAC (SPEC_ALL WPROOF2AUX_esv_SimpSeq) [every_stack_var_def]);;

let every_stack_var_is_stack_var_remove_unreach = prove
 (`every_stack_var is_stack_var (p:(A)wl_prog) ==>
   every_stack_var is_stack_var (remove_unreach p)`,
  REWRITE_TAC[remove_unreach_def] THEN DISCH_TAC THEN
  MATCH_MP_TAC every_stack_var_is_stack_var_Seq_assoc_right_lemma THEN
  ASM_REWRITE_TAC[every_stack_var_def]);;

let pre_alloc_conventions_remove_unreach = prove
 (`pre_alloc_conventions (p:(A)wl_prog) ==> pre_alloc_conventions (remove_unreach p)`,
  REWRITE_TAC[pre_alloc_conventions_def] THEN
  MESON_TAC[call_arg_convention_remove_unreach; every_stack_var_is_stack_var_remove_unreach]);;

let WPROOF2AUX_fiol_SimpSeq = prove
 (`!p1 p2:(A)wl_prog.
     full_inst_ok_less ac p1 /\ full_inst_ok_less ac p2 ==>
     full_inst_ok_less ac (SimpSeq p1 p2)`,
  MP_TAC(ISPEC `full_inst_ok_less ac:(A)wl_prog->bool` WPROOF2AUX_SimpSeq_closed) THEN
  REWRITE_TAC[full_inst_ok_less_def] THEN MESON_TAC[]);;

let full_inst_ok_less_Seq_assoc_right_lemma = prove
 (`!p1 p2:(A)wl_prog.
     full_inst_ok_less ac p1 /\ full_inst_ok_less ac p2 ==>
     full_inst_ok_less ac (Seq_assoc_right p1 p2)`,
  WPROOF2AUX_SAR_TAC (SPEC_ALL WPROOF2AUX_fiol_SimpSeq) [full_inst_ok_less_def]);;

let full_inst_ok_less_remove_unreach = prove
 (`full_inst_ok_less ac (p:(A)wl_prog) ==> full_inst_ok_less ac (remove_unreach p)`,
  REWRITE_TAC[remove_unreach_def] THEN DISCH_TAC THEN
  MATCH_MP_TAC full_inst_ok_less_Seq_assoc_right_lemma THEN
  ASM_REWRITE_TAC[full_inst_ok_less_def]);;

let wf_cutsets_SimpSeq = prove
 (`wf_cutsets p1 /\ wf_cutsets p2 ==> wf_cutsets (SimpSeq p1 p2:(A)wl_prog)`,
  MP_TAC(ISPEC `wf_cutsets:(A)wl_prog->bool` WPROOF2AUX_SimpSeq_closed) THEN
  REWRITE_TAC[wf_cutsets_def] THEN MESON_TAC[]);;

let wf_cutsets_Seq_assoc_right_lemma = prove
 (`!p1 p2:(A)wl_prog.
     wf_cutsets p1 /\ wf_cutsets p2 ==> wf_cutsets (Seq_assoc_right p1 p2)`,
  WPROOF2AUX_SAR_TAC wf_cutsets_SimpSeq [wf_cutsets_def]);;

let wf_cutsets_remove_unreach = prove
 (`wf_cutsets (p:(A)wl_prog) ==> wf_cutsets (remove_unreach p)`,
  REWRITE_TAC[remove_unreach_def] THEN DISCH_TAC THEN
  MATCH_MP_TAC wf_cutsets_Seq_assoc_right_lemma THEN ASM_REWRITE_TAC[wf_cutsets_def]);;

let every_inst_SimpSeq = prove
 (`every_inst P p1 /\ every_inst P p2 ==> every_inst P (SimpSeq p1 p2:(A)wl_prog)`,
  MP_TAC(ISPEC `every_inst P:(A)wl_prog->bool` WPROOF2AUX_SimpSeq_closed) THEN
  REWRITE_TAC[every_inst_def] THEN MESON_TAC[]);;

let every_inst_Seq_assoc_right_lemma = prove
 (`!p1 p2:(A)wl_prog.
     every_inst P p1 /\ every_inst P p2 ==> every_inst P (Seq_assoc_right p1 p2)`,
  WPROOF2AUX_SAR_TAC every_inst_SimpSeq [every_inst_def]);;

let every_inst_remove_unreach = prove
 (`every_inst P (p:(A)wl_prog) ==> every_inst P (remove_unreach p)`,
  REWRITE_TAC[remove_unreach_def] THEN DISCH_TAC THEN
  MATCH_MP_TAC every_inst_Seq_assoc_right_lemma THEN ASM_REWRITE_TAC[every_inst_def]);;

let flat_exp_conventions_SimpSeq = prove
 (`flat_exp_conventions p1 /\ flat_exp_conventions p2 ==>
   flat_exp_conventions (SimpSeq p1 p2:(A)wl_prog)`,
  MP_TAC(ISPEC `flat_exp_conventions:(A)wl_prog->bool` WPROOF2AUX_SimpSeq_closed) THEN
  REWRITE_TAC[flat_exp_conventions_def] THEN MESON_TAC[]);;

let flat_exp_conventions_Seq_assoc_right_lemma = prove
 (`!p1 p2:(A)wl_prog.
     flat_exp_conventions p1 /\ flat_exp_conventions p2 ==>
     flat_exp_conventions (Seq_assoc_right p1 p2)`,
  WPROOF2AUX_SAR_TAC flat_exp_conventions_SimpSeq [flat_exp_conventions_def]);;

let flat_exp_conventions_remove_unreach = prove
 (`flat_exp_conventions (p:(A)wl_prog) ==> flat_exp_conventions (remove_unreach p)`,
  REWRITE_TAC[remove_unreach_def] THEN DISCH_TAC THEN
  MATCH_MP_TAC flat_exp_conventions_Seq_assoc_right_lemma THEN
  ASM_REWRITE_TAC[flat_exp_conventions_def]);;
(* ------------------------------------------------------------------------- *)
(* word_alloc                                                                *)
(* ------------------------------------------------------------------------- *)

let apply_colour_lab_pres = prove
 (`!col prog:(A)wl_prog.
     wordConvs_extract_labels prog = wordConvs_extract_labels (apply_colour col prog)`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  WPROOF2AUX_PROG_STEP_TAC [apply_colour_def] THEN
  WPROOF2AUX_CP_FIN_TAC [wordConvs_extract_labels_def]);;

(* word_alloc is apply_colour or the identity                                *)

let WPROOF2AUX_oracle_colour_ok_SOME = prove
 (`!k col_opt tree (prog:(A)wl_prog) ls p.
     oracle_colour_ok k col_opt tree prog ls = SOME p ==> ?f. p = apply_colour f prog`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oracle_colour_ok_def; LET_DEF; LET_END_DEF] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;

let WPROOF2AUX_word_alloc_cases = prove
 (`!fc (c:(A)asm_config) alg k prog col_opt.
     word_alloc fc c alg k prog col_opt = prog \/
     ?f. word_alloc fc c alg k prog col_opt = apply_colour f prog`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_alloc_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPEC `oracle_colour_ok k col_opt (get_clash_tree (prog:(A)wl_prog) [])
                  prog (get_forced (c:(A)asm_config) prog [])`
               (nchotomy_of_type `:((A)wl_prog)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[WPROOF2AUX_pair_CASE_FST_SND] THENL
   [TOP_CASE_TAC THEN MESON_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP WPROOF2AUX_oracle_colour_ok_SOME) THEN MESON_TAC[]]);;

let word_alloc_lab_pres = prove
 (`wordConvs_extract_labels (prog:(A)wl_prog) =
   wordConvs_extract_labels (word_alloc fc c alg k prog col_opt)`,
  MP_TAC(ISPECL [`fc:num`; `c:(A)asm_config`; `alg:num`; `k:num`; `prog:(A)wl_prog`;
                 `col_opt:(num spt)option`] WPROOF2AUX_word_alloc_cases) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[GSYM apply_colour_lab_pres]);;

let word_alloc_flat_exp_conventions_lem = prove
 (`!f prog:(A)wl_prog.
     flat_exp_conventions prog ==> flat_exp_conventions (apply_colour f prog)`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  WPROOF2AUX_PROG_STEP_TAC [apply_colour_def] THEN
  WPROOF2AUX_CP_FIN_TAC [flat_exp_conventions_def; flat_exp_conventions_ShareInst;
                         WPROOF2AUX_fec_Set; apply_colour_exp_def; MAP] THEN
  CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[distinctness "wl_exp"; injectivity "wl_exp";
                              distinctness "binop"; NOT_CONS_NIL; CONS_11]) THEN
  ASM_MESON_TAC[]);;

let word_alloc_flat_exp_conventions = prove
 (`!fc c alg k prog:(A)wl_prog col_opt.
     flat_exp_conventions prog ==>
     flat_exp_conventions (word_alloc fc c alg k prog col_opt)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC_ALL WPROOF2AUX_word_alloc_cases) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[word_alloc_flat_exp_conventions_lem]);;

let WPROOF2AUX_aci_two_reg = prove
 (`(!f m r (a:(A)addr). two_reg_inst (apply_colour_inst f (Mem m r a))) /\
   (!f fp. two_reg_inst (apply_colour_inst f (FP fp:(A)inst)))`,
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [CASES_ON `m:memop` THEN CASES_ON `a:(A)addr`; CASES_ON `fp:fp`] THEN
  REWRITE_TAC[apply_colour_inst_def] THEN CASE_REWRITE_TAC[two_reg_inst_def]);;

let word_alloc_two_reg_inst_lem = prove
 (`!f prog:(A)wl_prog.
     every_inst two_reg_inst prog ==> every_inst two_reg_inst (apply_colour f prog)`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  WPROOF2AUX_PROG_STEP_TAC [apply_colour_def] THEN
  WPROOF2AUX_TTR_SPLIT_TAC THEN
  WPROOF2AUX_CP_FIN_TAC [every_inst_def; two_reg_inst_def; apply_colour_inst_def;
                         WPROOF2AUX_aci_two_reg] THEN
  CASE_REWRITE_TAC[two_reg_inst_def; apply_colour_inst_def] THEN
  ASM_REWRITE_TAC[]);;

let word_alloc_two_reg_inst = prove
 (`!fc c alg k prog:(A)wl_prog col_opt.
     every_inst two_reg_inst prog ==>
     every_inst two_reg_inst (word_alloc fc c alg k prog col_opt)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC_ALL WPROOF2AUX_word_alloc_cases) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[word_alloc_two_reg_inst_lem]);;

let apply_colour_not_created_subprogs = prove
 (`not_created_subprogs P (prog:(A)wl_prog) ==>
   not_created_subprogs P (apply_colour f prog)`,
  SPEC_TAC(`f:num->num`,`f:num->num`) THEN SPEC_TAC(`prog:(A)wl_prog`,`prog:(A)wl_prog`) THEN
  WPROOF2AUX_PROG_STEP_TAC [apply_colour_def] THEN
  WPROOF2AUX_CP_FIN_TAC [not_created_subprogs_def]);;

let word_alloc_not_created_subprogs = prove
 (`not_created_subprogs P (prog:(A)wl_prog) ==>
   not_created_subprogs P (word_alloc n c a r prog cl)`,
  MP_TAC(ISPECL [`n:num`; `c:(A)asm_config`; `a:num`; `r:num`; `prog:(A)wl_prog`;
                 `cl:(num spt)option`] WPROOF2AUX_word_alloc_cases) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[apply_colour_not_created_subprogs]);;

let word_get_code_labels_apply_colour = prove
 (`!col ps:(A)wl_prog.
     wordConvs_get_code_labels (apply_colour col ps) = wordConvs_get_code_labels ps`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  WPROOF2AUX_PROG_STEP_TAC [apply_colour_def] THEN
  WPROOF2AUX_CP_FIN_TAC [wordConvs_get_code_labels_def]);;

let word_good_handlers_apply_colour = prove
 (`!col ps:(A)wl_prog. good_handlers n (apply_colour col ps) <=> good_handlers n ps`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  WPROOF2AUX_PROG_STEP_TAC [apply_colour_def] THEN
  WPROOF2AUX_CP_FIN_TAC [good_handlers_def]);;

let word_get_code_labels_word_alloc = prove
 (`wordConvs_get_code_labels (word_alloc fc c alg k (prog:(A)wl_prog) col_opt) =
   wordConvs_get_code_labels prog`,
  MP_TAC(ISPECL [`fc:num`; `c:(A)asm_config`; `alg:num`; `k:num`; `prog:(A)wl_prog`;
                 `col_opt:(num spt)option`] WPROOF2AUX_word_alloc_cases) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[word_get_code_labels_apply_colour]);;

let word_good_handlers_word_alloc = prove
 (`good_handlers n (word_alloc fc c alg k (prog:(A)wl_prog) col_opt) <=>
   good_handlers n prog`,
  MP_TAC(ISPECL [`fc:num`; `c:(A)asm_config`; `alg:num`; `k:num`; `prog:(A)wl_prog`;
                 `col_opt:(num spt)option`] WPROOF2AUX_word_alloc_cases) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[word_good_handlers_apply_colour]);;
(* ------------------------------------------------------------------------- *)
(* remove_must_terminate                                                     *)
(* ------------------------------------------------------------------------- *)

(* HOL4 rmt_convs (an ML list of definitions) is not ported                 *)

let WPROOF2AUX_RMT_TAC (ths:thm list) : tactic =
  WPROOF2AUX_PROG_STEP_TAC [remove_must_terminate_def] THEN
  WPROOF2AUX_CP_FIN_TAC ths THEN TRY (REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let WPROOF2AUX_rmt_fec = prove
 (`!p:(A)wl_prog. flat_exp_conventions p ==> flat_exp_conventions (remove_must_terminate p)`,
  WPROOF2AUX_RMT_TAC [flat_exp_conventions_def]);;

let WPROOF2AUX_rmt_fiol = prove
 (`!p:(A)wl_prog. full_inst_ok_less c p ==> full_inst_ok_less c (remove_must_terminate p)`,
  WPROOF2AUX_RMT_TAC [full_inst_ok_less_def]);;

let WPROOF2AUX_rmt_ev = prove
 (`!p:(A)wl_prog. wl_every_var P p ==> wl_every_var P (remove_must_terminate p)`,
  WPROOF2AUX_RMT_TAC [wl_every_var_def]);;

let WPROOF2AUX_rmt_esv = prove
 (`!p:(A)wl_prog. every_stack_var P p ==> every_stack_var P (remove_must_terminate p)`,
  WPROOF2AUX_RMT_TAC [every_stack_var_def]);;

let WPROOF2AUX_rmt_cac = prove
 (`!p:(A)wl_prog. call_arg_convention p ==> call_arg_convention (remove_must_terminate p)`,
  WPROOF2AUX_RMT_TAC [call_arg_convention_def]);;

let WPROOF2AUX_rmt_every_inst = prove
 (`!p:(A)wl_prog. every_inst P p ==> every_inst P (remove_must_terminate p)`,
  WPROOF2AUX_RMT_TAC [every_inst_def]);;

let WPROOF2AUX_rmt_el = prove
 (`!p:(A)wl_prog.
     wordConvs_extract_labels (remove_must_terminate p) = wordConvs_extract_labels p`,
  WPROOF2AUX_RMT_TAC [wordConvs_extract_labels_def]);;

let remove_must_terminate_conventions = prove
 (`!p:(A)wl_prog (c:(A)asm_config) k.
     let comp = remove_must_terminate p in
     (flat_exp_conventions p ==> flat_exp_conventions comp) /\
     (full_inst_ok_less c p ==> full_inst_ok_less c comp) /\
     (post_alloc_conventions k p ==> post_alloc_conventions k comp) /\
     (every_inst P p ==> every_inst P comp) /\
     (wordConvs_extract_labels p = wordConvs_extract_labels comp)`,
  REWRITE_TAC[LET_DEF; LET_END_DEF; post_alloc_conventions_def] THEN
  SIMP_TAC[WPROOF2AUX_rmt_fec; WPROOF2AUX_rmt_fiol; WPROOF2AUX_rmt_ev; WPROOF2AUX_rmt_esv;
           WPROOF2AUX_rmt_cac; WPROOF2AUX_rmt_every_inst; WPROOF2AUX_rmt_el]);;

let word_get_code_labels_remove_must_terminate = prove
 (`!ps:(A)wl_prog.
     wordConvs_get_code_labels (remove_must_terminate ps) = wordConvs_get_code_labels ps`,
  WPROOF2AUX_RMT_TAC [wordConvs_get_code_labels_def]);;

let word_good_handlers_remove_must_terminate = prove
 (`!ps:(A)wl_prog. good_handlers n (remove_must_terminate ps) <=> good_handlers n ps`,
  WPROOF2AUX_RMT_TAC [good_handlers_def]);;
(* ------------------------------------------------------------------------- *)
(* word_to_word                                                              *)
(* ------------------------------------------------------------------------- *)

let compile_single_not_created_subprogs = prove
 (`not_created_subprogs P (SND (SND (FST (prog_opt:(num#num#(A)wl_prog)#((num spt)option))))) ==>
   not_created_subprogs P
     (SND (SND (word_to_word_compile_single two_reg_arith reg_count alg c prog_opt)))`,
  SPEC_TAC(`prog_opt:(num#num#(A)wl_prog)#((num spt)option)`,
           `prog_opt:(num#num#(A)wl_prog)#((num spt)option)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[word_to_word_compile_single_def; LET_DEF; LET_END_DEF; FST; SND] THEN
  MATCH_MP_TAC word_alloc_not_created_subprogs THEN
  MATCH_MP_TAC remove_dead_prog_not_created_subprogs THEN
  MATCH_MP_TAC remove_unreach_not_created_subprogs THEN
  MATCH_MP_TAC three_to_two_reg_prog_not_created_subprogs THEN
  MATCH_MP_TAC copy_prop_not_created_subprogs THEN
  MATCH_MP_TAC word_common_subexp_elim_not_created_subprogs THEN
  MATCH_MP_TAC remove_dead_prog_not_created_subprogs THEN
  MATCH_MP_TAC full_ssa_cc_trans_not_created_subprogs THEN
  MATCH_MP_TAC inst_select_not_created_subprogs THEN
  MATCH_MP_TAC compile_exp_not_created_subprogs THEN ASM_REWRITE_TAC[]);;

(* the components of full_compile_single                                     *)

let WPROOF2AUX_fcs_FST = prove
 (`!tra rc ralg (c:(A)asm_config) n m pp col.
     FST (full_compile_single tra rc ralg c ((n,m,pp),col)) = n /\
     FST (SND (full_compile_single tra rc ralg c ((n,m,pp),col))) = m`,
  REWRITE_TAC[full_compile_single_def; word_to_word_compile_single_def; LET_DEF; LET_END_DEF;
              WPROOF2AUX_pair_CASE_FST_SND; FST; SND]);;

let WPROOF2AUX_fcs_gh = prove
 (`!tra rc ralg (c:(A)asm_config) n m pp col.
     good_handlers n pp ==>
     good_handlers n (SND (SND (full_compile_single tra rc ralg c ((n,m,pp),col))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[full_compile_single_def; word_to_word_compile_single_def; LET_DEF; LET_END_DEF;
              WPROOF2AUX_pair_CASE_FST_SND; FST; SND] THEN
  REWRITE_TAC[word_good_handlers_remove_must_terminate; word_good_handlers_word_alloc;
              word_good_handlers_remove_dead_prog] THEN
  MATCH_MP_TAC word_good_handlers_remove_unreach THEN
  REWRITE_TAC[word_good_handlers_three_to_two_reg_prog; word_good_handlers_copy_prop;
              word_good_handlers_word_common_subexp_elim; word_good_handlers_remove_dead_prog;
              word_good_handlers_full_ssa_cc_trans; word_good_handlers_inst_select] THEN
  MATCH_MP_TAC word_good_handlers_word_simp THEN ASM_REWRITE_TAC[]);;

let word_good_handlers_word_to_word_incr_helper = prove
 (`!oracles.
     LENGTH (progs:(num#num#(A)wl_prog)list) = LENGTH oracles ==>
     ALL (\(n,m,pp). good_handlers n pp) progs ==>
     ALL (\(n,m,pp). good_handlers n pp)
       (MAP (full_compile_single tra reg_count1 ralg asm_c) (ZIP progs oracles))`,
  SPEC_TAC(`progs:(num#num#(A)wl_prog)list`,`progs:(num#num#(A)wl_prog)list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; ZIP; MAP; ALL; SUC_INJ] THEN
  SPEC_TAC(`h:num#num#(A)wl_prog`,`h:num#num#(A)wl_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`tra:bool`; `reg_count1:num`; `ralg:num`; `asm_c:(A)asm_config`;
                   `p1:num`; `p1':num`; `p2:(A)wl_prog`; `h':(num spt)option`]
                  WPROOF2AUX_fcs_gh) THEN
    MP_TAC(ISPECL [`tra:bool`; `reg_count1:num`; `ralg:num`; `asm_c:(A)asm_config`;
                   `p1:num`; `p1':num`; `p2:(A)wl_prog`; `h':(num spt)option`]
                  WPROOF2AUX_fcs_FST) THEN
    SPEC_TAC(`full_compile_single tra reg_count1 ralg (asm_c:(A)asm_config) ((p1,p1',p2),h')`,
             `x:num#num#(A)wl_prog`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN ASM_REWRITE_TAC[]]);;

let word_good_handlers_word_to_word_incr = prove
 (`ALL (\(n,m,pp). good_handlers n pp) (progs:(num#num#(A)wl_prog)list) ==>
   ALL (\(n,m,pp). good_handlers n pp)
     (MAP (\p. full_compile_single tra reg_count1 ralg asm_c (p, NONE)) progs)`,
  DISCH_TAC THEN
  MP_TAC(ISPEC `MAP (\p:num#num#(A)wl_prog. NONE:(num spt)option) progs`
               word_good_handlers_word_to_word_incr_helper) THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  SPEC_TAC(`progs:(num#num#(A)wl_prog)list`,`progs:(num#num#(A)wl_prog)list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ZIP]);;

let WPROOF2AUX_next_n_oracle_LENGTH = prove
 (`!n col. LENGTH (FST (next_n_oracle n col)) = n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[next_n_oracle_def] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[FST; LENGTH_TAKE; LENGTH_REPLICATE]);;

let WPROOF2AUX_w2w_SND = prove
 (`!wc (ac:(A)asm_config) progs.
     SND (word_to_word_compile wc ac progs) =
     MAP (full_compile_single (asm_config_two_reg_arith ac)
            (asm_config_reg_count ac - (5 + LENGTH (asm_config_avoid_regs ac)))
            (word_to_word_config_reg_alg wc) ac)
         (ZIP progs (FST (next_n_oracle (LENGTH progs) (word_to_word_config_col_oracle wc))))`,
  REWRITE_TAC[word_to_word_compile_def; LET_DEF; LET_END_DEF;
              WPROOF2AUX_pair_CASE_FST_SND; FST; SND]);;

let word_good_handlers_word_to_word = prove
 (`ALL (\(n,m,pp). good_handlers n pp) (progs:(num#num#(A)wl_prog)list) ==>
   ALL (\(n,m,pp). good_handlers n pp) (SND (word_to_word_compile wc ac progs))`,
  DISCH_TAC THEN REWRITE_TAC[WPROOF2AUX_w2w_SND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] word_good_handlers_word_to_word_incr_helper) THEN
  ASM_REWRITE_TAC[WPROOF2AUX_next_n_oracle_LENGTH]);;

let WPROOF2AUX_fcs_gcl = prove
 (`!tra rc ralg (c:(A)asm_config) n m pp col.
     wordConvs_get_code_labels
       (SND (SND (full_compile_single tra rc ralg c ((n,m,pp),col)))) SUBSET
     wordConvs_get_code_labels pp`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[full_compile_single_def; word_to_word_compile_single_def; LET_DEF; LET_END_DEF;
              WPROOF2AUX_pair_CASE_FST_SND; FST; SND] THEN
  REWRITE_TAC[word_get_code_labels_remove_must_terminate; word_get_code_labels_word_alloc] THEN
  REPEAT
   (FIRST
     [MATCH_ACCEPT_TAC word_get_code_labels_word_simp;
      W(fun (asl,w) ->
          let x = rand(rand(lhand w)) in
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC (mk_comb(`wordConvs_get_code_labels:(A)wl_prog->num->bool`, x)) THEN
          CONJ_TAC THENL
           [FIRST [MATCH_ACCEPT_TAC word_get_code_labels_remove_dead_prog;
                   MATCH_ACCEPT_TAC word_get_code_labels_remove_unreach;
                   MATCH_ACCEPT_TAC word_get_code_labels_word_common_subexp_elim;
                   REWRITE_TAC[word_get_code_labels_three_to_two_reg_prog;
                               word_get_code_labels_copy_prop;
                               word_get_code_labels_full_ssa_cc_trans;
                               word_get_code_labels_inst_select; SUBSET_REFL] THEN NO_TAC];
            ALL_TAC])]));;

let WPROOF2AUX_fcs_list = prove
 (`!(progs:(num#num#(A)wl_prog)list) oracles.
     LENGTH progs = LENGTH oracles ==>
     MAP FST (MAP (full_compile_single tra reg_count1 ralg asm_c) (ZIP progs oracles)) =
     MAP FST progs /\
     UNIONS (set_of_list (MAP (\(n,m,pp). wordConvs_get_code_labels pp)
               (MAP (full_compile_single tra reg_count1 ralg asm_c) (ZIP progs oracles))))
     SUBSET UNIONS (set_of_list (MAP (\(n,m,pp). wordConvs_get_code_labels pp) progs))`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; ZIP; MAP; SUC_INJ; set_of_list; UNIONS_INSERT; SUBSET_REFL] THEN
  SPEC_TAC(`h:num#num#(A)wl_prog`,`h:num#num#(A)wl_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t':((num spt)option)list` o
                check (fun th -> is_forall(concl th) &&
                                 can (find_term (fun x -> x = `t:(num#num#(A)wl_prog)list`))
                                     (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tra:bool`; `reg_count1:num`; `ralg:num`; `asm_c:(A)asm_config`;
                 `p1:num`; `p1':num`; `p2:(A)wl_prog`; `h':(num spt)option`]
                WPROOF2AUX_fcs_gcl) THEN
  MP_TAC(ISPECL [`tra:bool`; `reg_count1:num`; `ralg:num`; `asm_c:(A)asm_config`;
                 `p1:num`; `p1':num`; `p2:(A)wl_prog`; `h':(num spt)option`]
                WPROOF2AUX_fcs_FST) THEN
  SPEC_TAC(`full_compile_single tra reg_count1 ralg (asm_c:(A)asm_config) ((p1,p1',p2),h')`,
           `x:num#num#(A)wl_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[CONS_11] THEN ASM SET_TAC[]);;

let word_good_code_labels_word_to_word_incr_helper = prove
 (`!oracles.
     LENGTH (progs:(num#num#(A)wl_prog)list) = LENGTH oracles ==>
     wordConvs_good_code_labels progs elabs ==>
     wordConvs_good_code_labels
       (MAP (full_compile_single tra reg_count1 ralg asm_c) (ZIP progs oracles)) elabs`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[wordConvs_good_code_labels_def]) THEN
  REWRITE_TAC[wordConvs_good_code_labels_def] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] word_good_handlers_word_to_word_incr_helper) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`progs:(num#num#(A)wl_prog)list`; `oracles:((num spt)option)list`]
                 WPROOF2AUX_fcs_list) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let word_good_code_labels_word_to_word_incr = prove
 (`wordConvs_good_code_labels (progs:(num#num#(A)wl_prog)list) elabs ==>
   wordConvs_good_code_labels
     (MAP (\p. full_compile_single tra reg_count1 ralg asm_c (p, NONE)) progs) elabs`,
  DISCH_TAC THEN
  MP_TAC(ISPEC `MAP (\p:num#num#(A)wl_prog. NONE:(num spt)option) progs`
               word_good_code_labels_word_to_word_incr_helper) THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SPEC_TAC(`progs:(num#num#(A)wl_prog)list`,`progs:(num#num#(A)wl_prog)list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ZIP]);;

let word_good_code_labels_word_to_word = prove
 (`wordConvs_good_code_labels (progs:(num#num#(A)wl_prog)list) elabs ==>
   wordConvs_good_code_labels (SND (word_to_word_compile wc ac progs)) elabs`,
  DISCH_TAC THEN REWRITE_TAC[WPROOF2AUX_w2w_SND] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] word_good_code_labels_word_to_word_incr_helper) THEN
  ASM_REWRITE_TAC[WPROOF2AUX_next_n_oracle_LENGTH]);;
