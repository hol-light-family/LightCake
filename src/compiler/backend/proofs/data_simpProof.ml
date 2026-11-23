(* ========================================================================= *)
(* data_simpProof: port of HOL4 compiler/backend/proofs/                     *)
(* data_simpProofScript.sml (CakeML v3479).  Correctness proof for           *)
(* data_simp.  DATAPAUX_ names are local helpers (not HOL4 names).           *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/data_simp.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/dataProps.ml";;

type_invention_error := true;;

(* HOL4 [local] *)
let data_simpProof_evaluate_Seq_Skip = prove
 (`!c (s:(C,FFI)data_state).
     data_evaluate (data_Seq c data_Skip,s) = data_evaluate (c,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_evaluate_def] THEN
  MP_TAC(ISPEC `data_evaluate (c,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[data_evaluate_def]);;

(* HOL4 [local] *)
let evaluate_pSeq = prove
 (`!c1 c2 (s:(C,FFI)data_state).
     data_evaluate (pSeq c1 c2,s) = data_evaluate (data_Seq c1 c2,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pSeq_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[data_simpProof_evaluate_Seq_Skip]);;

(* HOL4 [local]: the Seq-with-Skip continuation is the identity on a result *)
(* pair (HOL4's paired lambda is the pair_CASE that unfolding evaluate of a *)
(* Seq gives here)                                                          *)
let lam_skip_id = prove
 (CASE_TERM
  `!x:((data_v list,data_v)result)option # (C,FFI)data_state.
     (match x with
        (res,s1) -> if res = NONE then data_evaluate (data_Skip,s1) else (res,s1)) = x`,
  GEN_TAC THEN
  MP_TAC(ISPEC `x:((data_v list,data_v)result)option # (C,FFI)data_state`
           PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[data_evaluate_def]);;

(* a statement !c s. body is proved by HOL4's recInduct on a pair-induction *)
(* theorem ind (conclusion !p. P p): body is stated for FST p and SND p     *)
let DATAPAUX_SIMP_PAIR_IND_TAC (ind:thm) : tactic = fun (asl,w as g) ->
  let c,w1 = dest_forall w in
  let s,b = dest_forall w1 in
  let p = variant (frees w) (mk_var("p",mk_type("prod",[type_of c;type_of s]))) in
  let fstp = mk_icomb(mk_const("FST",[]),p)
  and sndp = mk_icomb(mk_const("SND",[]),p) in
  let b' = vsubst [fstp,c; sndp,s] b in
  (SUBGOAL_THEN (mk_forall(p,b'))
     (fun th -> MATCH_ACCEPT_TAC (REWRITE_RULE[FORALL_PAIR_THM; FST; SND] th)) THEN
   MATCH_MP_TAC ind THEN REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC) g;;

let DATAPAUX_SIMP_Seq_not_NONE = prove
 (`!c c2 (s:(C,FFI)data_state).
     ~(FST (data_evaluate (c,s)) = NONE) ==>
     data_evaluate (data_Seq c c2,s) = data_evaluate (c,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_evaluate_def] THEN
  MP_TAC(ISPEC `data_evaluate (c,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE_def; FST] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let DATAPAUX_SIMP_Seq_cong = prove
 (`!c c' c2 (s:(C,FFI)data_state).
     data_evaluate (c,s) = data_evaluate (c',s) ==>
     data_evaluate (data_Seq c c2,s) = data_evaluate (data_Seq c' c2,s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[data_evaluate_def] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 [local] *)
let evaluate_simp = prove
 (`!c1 (s:(C,FFI)data_state) c2.
     data_evaluate (data_simp_simp c1 c2,s) = data_evaluate (data_Seq c1 c2,s)`,
  let pseq_tac = REPEAT STRIP_TAC THEN REWRITE_TAC[data_simp_simp_def; evaluate_pSeq] in
  let halt_tac =
    REPEAT GEN_TAC THEN REWRITE_TAC[data_simp_simp_def] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC DATAPAUX_SIMP_Seq_not_NONE THEN REWRITE_TAC[data_evaluate_def] THEN
    REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[FST; option_DISTINCT]) in
  DATAPAUX_SIMP_PAIR_IND_TAC data_evaluate_ind THENL
   [(* Skip *)
    REPEAT GEN_TAC THEN REWRITE_TAC[data_simp_simp_def; data_evaluate_def; pair_CASE_def];
    (* Move *) pseq_tac; (* Assign *) pseq_tac; (* Tick *) pseq_tac;
    (* MakeSpace *) pseq_tac; (* Raise *) halt_tac; (* Return *) halt_tac;
    (* Seq *)
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ih2")) THEN
    GEN_TAC THEN REWRITE_TAC[data_simp_simp_def] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[data_evaluate_def] THEN
    MP_TAC(ISPEC `data_evaluate (c1,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:((data_v list,data_v)result)option`
      (X_CHOOSE_THEN `s1:(C,FFI)data_state` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[pair_CASE] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN
    REMOVE_THEN "ih2" (MP_TAC o SPEC `s1:(C,FFI)data_state`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[data_evaluate_def];
    (* If *)
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    GEN_TAC THEN REWRITE_TAC[data_simp_simp_def; evaluate_pSeq] THEN
    MATCH_MP_TAC DATAPAUX_SIMP_Seq_cong THEN REWRITE_TAC[data_evaluate_def] THEN
    TOP_CASE_TAC THEN
    COND_CASES_TAC THENL
     [REMOVE_THEN "ih1" (MP_TAC o SPEC `a:data_v`);
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      REMOVE_THEN "ih2" (MP_TAC o SPEC `a:data_v`)] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th; data_simpProof_evaluate_Seq_Skip]);
    (* Force *) pseq_tac;
    (* Call *)
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "ih") ASSUME_TAC)) THEN GEN_TAC THEN
    CASES_ON `handler:(num#data_prog)option` THEN
    REWRITE_TAC[data_simp_simp_def; evaluate_pSeq] THEN
    MP_TAC(ISPEC `a:num#data_prog` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:num` (X_CHOOSE_THEN `h:data_prog` SUBST_ALL_TAC)) THEN
    REWRITE_TAC[data_simp_simp_def; evaluate_pSeq] THEN
    MATCH_MP_TAC DATAPAUX_SIMP_Seq_cong THEN
    REWRITE_TAC[data_evaluate_def; IS_SOME_DEF] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IS_SOME_DEF]) THEN
    REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[]) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM data_simpProof_evaluate_Seq_Skip] THEN
    REMOVE_THEN "ih" (MATCH_MP_TAC o REWRITE_RULE[RIGHT_IMP_FORALL_THM]) THEN
    ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN ASM_MESON_TAC[]]);;

let simp_correct = prove
 (`!c (s:(C,FFI)data_state). data_evaluate (data_simp_simp c data_Skip,s) = data_evaluate (c,s)`,
  REWRITE_TAC[evaluate_simp; data_simpProof_evaluate_Seq_Skip]);;

let get_code_labels_simp = prove
 (`!x y. data_get_code_labels (data_simp_simp x y) SUBSET
         data_get_code_labels x UNION data_get_code_labels y`,
  MATCH_MP_TAC data_simp_simp_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[data_simp_simp_def; pSeq_def] THEN
  REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[data_get_code_labels_def; option_CASE; pair_CASE] THEN
  ASM SET_TAC[]);;
