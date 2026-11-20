(* ========================================================================= *)
(* source_to_flatProof_p2: part 2 of 2 (HOL4 lines 2996-5968) of the port   *)
(* of HOL4 compiler/backend/proofs/source_to_flatProofScript.sml (CakeML     *)
(* v3479).  Correctness proof for source_to_flat.                            *)
(* The parts _p1 and _p2 are loaded one after the other (_p2 needs _p1);     *)
(* the notes on the rendering are in the header of _p1.                      *)
(* ========================================================================= *)

needs "compiler/backend/proofs/source_to_flatProof_p1.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 2: HOL4 lines 2996-5968 ===== *)

(* proof tools of this part (OCaml helpers, FLATP2AUX_)                      *)

(* FLATP2 proof helpers: split a conjunction into labelled assumptions; the  *)
(* labels of the conjuncts of invariant_def                                   *)
let rec FLATP2AUX_LABEL_CONJS (ls:string list) : thm_tactic = fun th ->
  match ls with
    [] -> ALL_TAC
  | [l] -> LABEL_TAC l th
  | l::rest -> let a,b = CONJ_PAIR th in
               LABEL_TAC l a THEN FLATP2AUX_LABEL_CONJS rest b;;

let FLATP2AUX_INV_LABELS =
  ["c_ok"; "tys_ok"; "s_rel"; "idx_range"; "src_orac"; "orac_rel"; "globals";
   "eval_ref"; "env_gen_inv"; "fin_idx"];;

let FLATP2AUX_INV_TAC (lab:string) : tactic =
  USE_THEN lab (FLATP2AUX_LABEL_CONJS FLATP2AUX_INV_LABELS o
                REWRITE_RULE[invariant_def]);;

(* nested X_CHOOSE_THEN with the given variables *)
let FLATP2AUX_CHOOSE_THEN (vs:term list) (ttac:thm_tactic) : thm_tactic =
  itlist (fun v t -> X_CHOOSE_THEN v t) vs ttac;;

(* rewriting with labelled assumptions (avoids the collapse of ASM_REWRITE) *)
let FLATP2AUX_LREWRITE_TAC (labs:string list) (thl:thm list) : tactic =
  fun (asl,w as gl) -> REWRITE_TAC (map (fun l -> assoc l asl) labs @ thl) gl;;

let FLATP2AUX_LSIMP_TAC (labs:string list) (thl:thm list) : tactic =
  fun (asl,w as gl) -> SIMP_TAC (map (fun l -> assoc l asl) labs @ thl) gl;;

(* the kit simplifier (simpset, no assumptions) with labelled assumptions *)
let FLATP2AUX_LKSIMP_TAC (labs:string list) (thl:thm list) : tactic =
  fun (asl,w as gl) ->
    CONV_TAC (CAKE_SIMP_CONV (map (fun l -> assoc l asl) labs @ thl)) gl;;

(* close a goal with a false assumption *)
let FLATP2AUX_F_TAC : tactic =
  FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`));;

let FLATP2AUX_LIST_SPLIT_TAC (l:term) (h:term) (t:term) : tactic =
  MP_TAC(ISPEC l list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN h (X_CHOOSE_THEN t SUBST1_TAC)));;

(* the conjuncts of invariant_def of assumption lab, labelled with prefix p *)
let FLATP2AUX_INV_TAC_P (lab:string) (p:string) : tactic =
  USE_THEN lab (FLATP2AUX_LABEL_CONJS (map (fun l -> p ^ l) FLATP2AUX_INV_LABELS) o
                REWRITE_RULE[invariant_def]);;
(* case split of a result variable r into Rval v / Rerr e (substituted) *)
let FLATP2AUX_RESULT_CASES_TAC (r:term) (v:term) (e:term) : tactic =
  MP_TAC(ISPEC r (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN v SUBST_ALL_TAC)
                              (X_CHOOSE_THEN e SUBST_ALL_TAC));;

(* split a pair-valued term p into (a,b) with label lab for p = (a,b) *)
let FLATP2AUX_PAIR_TAC (p:term) (a:term) (b:term) (lab:string) : tactic =
  MP_TAC(ISPEC p PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN a (X_CHOOSE_THEN b (LABEL_TAC lab)));;
(* instantiate an induction hypothesis: bound variables named in sub get the *)
(* given terms, the others keep their names (the variables of the goal); a *)
(* bound variable defined by an antecedent conjunct  v = X  is set to X     *)
let FLATP2AUX_INST_IH (sub:(string*term) list) (ih:thm) : thm =
  let vs,_ = strip_forall (concl ih) in
  let givens = map fst sub in
  let th0 = SPECL (map (fun v -> try assoc (fst(dest_var v)) sub with Failure _ -> v) vs) ih in
  if not (is_imp (concl th0)) then th0 else
  let ant = lhand (concl th0) in
  let defs = mapfilter (fun c ->
      let l,r = dest_eq c in
      if is_var l && mem l vs && not (mem (fst(dest_var l)) givens) && not (vfree_in l r)
      then (r,l) else failwith "") (conjuncts ant) in
  INST defs th0;;

let FLATP2AUX_IH_TAC (lab:string) (sub:(string*term) list) : tactic =
  USE_THEN lab (fun ih -> MP_TAC (FLATP2AUX_INST_IH sub ih));;

(* discharge the easy antecedent conjuncts: reflexivity and assumptions *)
let FLATP2AUX_ANTS_TAC : tactic =
  REPEAT CONJ_TAC THEN TRY(FIRST [REFL_TAC; FIRST_ASSUM ACCEPT_TAC]);;
(* the transitivity goals of compile_correct (orac_forward_rel, the SUBMAPs, *)
(* subglobals) through the intermediate eval state es1 and env genv1         *)
let FLATP2AUX_TRANS_TAC (es1:term) (genv1:term) : tactic =
  let mids = [es1; mk_icomb(`global_env_c`,genv1); mk_icomb(`global_env_tys`,genv1);
              mk_icomb(`global_env_v`,genv1)] in
  let step th = MATCH_MP_TAC th THEN
                FIRST (map (fun m -> EXISTS_TAC m THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC)
                           mids) in
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; step orac_forward_rel_trans; step SUBMAP_TRANS;
         step subglobals_trans];;
(* case split of an option-valued term into NONE / SOME x, substituting it *)
(* (the equation ot = NONE / ot = SOME x is kept, with label lab)            *)
let FLATP2AUX_OPTION_CASES_TAC (ot:term) (x:term) (lab:string) : tactic =
  MP_TAC(ISPEC ot (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> SUBST_ALL_TAC th THEN LABEL_TAC lab th)
    (X_CHOOSE_THEN x (fun th -> SUBST_ALL_TAC th THEN LABEL_TAC lab th)));;
(* parse a term in the context of a goal: its free variables (those of the   *)
(* conclusion and the assumptions) get their types from the goal             *)
let FLATP2AUX_PARSE_IN ((asl,w):goal) (s:string) : term =
  let fvs = itlist (fun (_,th) acc -> union (frees (concl th)) acc) asl (frees w) in
  let venv = map (fun v -> let n,ty = dest_var v in (n, pretype_of_type ty)) fvs in
  let ptm,rest = (parse_preterm o flat o map cake_wild_tokens o lex o explode) s in
  if rest <> [] then failwith "FLATP2AUX_PARSE_IN: unparsed input" else
  cases_of_matches (term_of_preterm (retypecheck venv ptm));;

let FLATP2AUX_SUBGOAL (s:string) (ttac:thm_tactic) : tactic =
  fun gl -> SUBGOAL_THEN (FLATP2AUX_PARSE_IN gl s) ttac gl;;

let FLATP2AUX_EXISTS (s:string) : tactic =
  fun gl -> EXISTS_TAC (FLATP2AUX_PARSE_IN gl s) gl;;

let FLATP2AUX_EXISTSL (ss:string list) : tactic = MAP_EVERY FLATP2AUX_EXISTS ss;;
let FLATP2AUX_ISPECL_TAC (ss:string list) (th:thm) : tactic =
  fun gl -> MP_TAC (ISPECL (map (FLATP2AUX_PARSE_IN gl) ss) th) gl;;
let FLATP2AUX_MAKE_VARLS_TAC (pre:string list) (post:string list) : tactic =
  fun (asl,w as gl) ->
    let tm = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "flat_evaluate" &&
                                     length(snd(strip_comb t)) = 3 with Failure _ -> false) w in
    let envt = hd(snd(strip_comb tm)) in
    MP_TAC (ISPECL (map (FLATP2AUX_PARSE_IN gl) pre @ [envt] @ map (FLATP2AUX_PARSE_IN gl) post)
              invariant_make_varls) gl;;
let FLATP2AUX_compile_exps_clauses =
  filter (fun th -> try fst(dest_const(fst(strip_comb(lhs(snd(strip_forall(concl th))))))) =
                        "source_to_flat_compile_exps" with Failure _ -> false)
    (CONJUNCTS source_to_flat_compile_exp_def);;
let FLATP2AUX_WITH_LABELS (labs:string list) (f:thm list -> tactic) : tactic =
  fun (asl,w as gl) -> f (map (fun l -> assoc l asl) labs) gl;;

(* HOL4 line 2996 *)
let compile_funs_dom2 = prove
 (`!t env funs.
     MAP FST (compile_funs t env funs) = MAP FST funs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_funs_map; MAP_MAP_o] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]);;

let FLATP2AUX_same_type_mix = prove
 (`!s1 s2 (t1:type_id) (t2:type_id).
     (same_type (ExnStamp 0) s1 <=> t1 = NONE) /\
     (same_type (ExnStamp 0) s2 <=> t2 = NONE) /\
     (~(t2 = NONE) ==> ~(t2 = t1)) /\
     (!s s' n. s2 = TypeStamp s n ==> ~(s1 = TypeStamp s' n))
     ==> (same_type s1 s2 <=> t1 = t2)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `s1:stamp` (cases "stamp")) THEN
  STRUCT_CASES_TAC (ISPEC `s2:stamp` (cases "stamp")) THEN
  REWRITE_TAC[same_type_def; distinctness "stamp"; injectivity "stamp"] THEN
  MESON_TAC[]);;

let FLATP2AUX_same_type_sym = prove
 (`!s1 s2. same_type s1 s2 <=> same_type s2 s1`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `s1:stamp` (cases "stamp")) THEN
  STRUCT_CASES_TAC (ISPEC `s2:stamp` (cases "stamp")) THEN
  REWRITE_TAC[same_type_def] THEN MESON_TAC[]);;

(* HOL4 line 3003 (semanticPrimitives' same_type, flatSem's ctor_same_type) *)
let genv_c_ok_extend = prove
 (`!c c_ext.
     genv_c_ok c /\
   (!cn arity stamp.
      FLOOKUP c_ext (cn, arity) = SOME stamp
      ==> (same_type (ExnStamp 0) stamp <=> SND cn = NONE) /\
          (!cn' arity' stamp'.
             FLOOKUP c_ext (cn', arity') = SOME stamp'
             ==> (same_type stamp stamp' <=> flat_ctor_same_type (SOME cn) (SOME cn')) /\
                 (stamp = stamp' ==> cn = cn' /\ arity = arity')) /\
          (!cn' arity' stamp'.
             FLOOKUP c (cn', arity') = SOME stamp'
             ==> ~(stamp = stamp') /\
                 (~(SND cn = NONE) ==> ~(SND cn = SND cn')) /\
                 (!s s' n. stamp = TypeStamp s n ==> ~(stamp' = TypeStamp s' n))))
   ==> genv_c_ok (FUNION c c_ext)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[genv_c_ok_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "bools")
    (CONJUNCTS_THEN2 (LABEL_TAC "exns") (CONJUNCTS_THEN2 (LABEL_TAC "lists")
      (CONJUNCTS_THEN2 (LABEL_TAC "same") (LABEL_TAC "inj"))))) (LABEL_TAC "ext")) THEN
  SUBGOAL_THEN
   `!cn arity stamp.
      FLOOKUP (c:((ctor_id # type_id) # num, stamp) fmap) (cn,arity) = SOME stamp
      ==> (same_type (ExnStamp 0) stamp <=> SND cn = NONE)`
  (LABEL_TAC "c0") THENL
   [MAP_EVERY X_GEN_TAC [`cn:ctor_id#type_id`; `arity:num`; `stamp:stamp`] THEN
    DISCH_TAC THEN USE_THEN "exns" (MP_TAC o REWRITE_RULE[has_exns_def]) THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    REMOVE_THEN "same" (MP_TAC o SPECL [`(div_tag,NONE):ctor_id#type_id`;
      `cn:ctor_id#type_id`; `0`; `arity:num`; `div_stamp`; `stamp:stamp`]) THEN
    ASM_REWRITE_TAC[ctor_same_type_def; option_CASE; div_stamp_def] THEN
    MP_TAC(ISPEC `cn:ctor_id#type_id` PAIR_SURJECTIVE) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[flat_ctor_same_type_def; SND] THEN
    STRUCT_CASES_TAC (ISPEC `stamp:stamp` (cases "stamp")) THEN
    REWRITE_TAC[same_type_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "bools" MP_TAC THEN
    SIMP_TAC[has_bools_def; FLOOKUP_FUNION; option_CASE];
    USE_THEN "exns" MP_TAC THEN
    SIMP_TAC[has_exns_def; FLOOKUP_FUNION; option_CASE];
    USE_THEN "lists" MP_TAC THEN
    SIMP_TAC[has_lists_def; FLOOKUP_FUNION; option_CASE];
    ALL_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FLOOKUP_FUNION] THEN
  REWRITE_TAC[option_case_eq; option_INJ] THEN SIMP[] THEN
  REWRITE_TAC[FORALL_PAIR_THM; flat_ctor_same_type_def; PAIR_EQ;
              ctor_same_type_def; option_CASE] THENL
   [MAP_EVERY X_GEN_TAC [`x1:ctor_id`; `t1:type_id`; `x2:ctor_id`; `t2:type_id`;
                         `l1:num`; `l2:num`; `stamp1:stamp`; `stamp2:stamp`] THEN
    STRIP_TAC THENL
     [REMOVE_THEN "ext" (MP_TAC o SPECL [`(x1,t1):ctor_id#type_id`; `l1:num`;
                                          `stamp1:stamp`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`(x2,t2):ctor_id#type_id`; `l2:num`; `stamp2:stamp`] o
                 CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[flat_ctor_same_type_def] THEN SIMP_TAC[];
      ONCE_REWRITE_TAC[FLATP2AUX_same_type_sym] THEN
      GEN_REWRITE_TAC RAND_CONV [EQ_SYM_EQ] THEN
      MATCH_MP_TAC FLATP2AUX_same_type_mix THEN
      REMOVE_THEN "c0" (MP_TAC o SPECL [`(x2,t2):ctor_id#type_id`; `l2:num`;
                                         `stamp2:stamp`]) THEN
      ASM_REWRITE_TAC[SND] THEN DISCH_THEN SUBST1_TAC THEN
      REMOVE_THEN "ext" (MP_TAC o SPECL [`(x1,t1):ctor_id#type_id`; `l1:num`;
                                          `stamp1:stamp`]) THEN
      ASM_REWRITE_TAC[SND] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`(x2,t2):ctor_id#type_id`; `l2:num`;
                                    `stamp2:stamp`]) THEN
      ASM_REWRITE_TAC[SND] THEN MESON_TAC[];
      MATCH_MP_TAC FLATP2AUX_same_type_mix THEN
      REMOVE_THEN "c0" (MP_TAC o SPECL [`(x1,t1):ctor_id#type_id`; `l1:num`;
                                         `stamp1:stamp`]) THEN
      ASM_REWRITE_TAC[SND] THEN DISCH_THEN SUBST1_TAC THEN
      REMOVE_THEN "ext" (MP_TAC o SPECL [`(x2,t2):ctor_id#type_id`; `l2:num`;
                                          `stamp2:stamp`]) THEN
      ASM_REWRITE_TAC[SND] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`(x1,t1):ctor_id#type_id`; `l1:num`;
                                    `stamp1:stamp`]) THEN
      ASM_REWRITE_TAC[SND] THEN MESON_TAC[];
      REMOVE_THEN "same" (MP_TAC o SPECL [`(x1,t1):ctor_id#type_id`;
        `(x2,t2):ctor_id#type_id`; `l1:num`; `l2:num`; `stamp1:stamp`; `stamp2:stamp`]) THEN
      ASM_REWRITE_TAC[ctor_same_type_def; option_CASE; flat_ctor_same_type_def]];
    MAP_EVERY X_GEN_TAC [`x1:ctor_id`; `t1:type_id`; `x2:ctor_id`; `t2:type_id`;
                         `l1:num`; `l2:num`; `stamp:stamp`] THEN
    STRIP_TAC THENL
     [REMOVE_THEN "ext" (MP_TAC o SPECL [`(x1,t1):ctor_id#type_id`; `l1:num`;
                                          `stamp:stamp`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`(x2,t2):ctor_id#type_id`; `l2:num`; `stamp:stamp`] o
                 CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[PAIR_EQ] THEN SIMP_TAC[];
      REMOVE_THEN "ext" (MP_TAC o SPECL [`(x1,t1):ctor_id#type_id`; `l1:num`;
                                          `stamp:stamp`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`(x2,t2):ctor_id#type_id`; `l2:num`; `stamp:stamp`] o
                 CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      REMOVE_THEN "ext" (MP_TAC o SPECL [`(x2,t2):ctor_id#type_id`; `l2:num`;
                                          `stamp:stamp`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`(x1,t1):ctor_id#type_id`; `l1:num`; `stamp:stamp`] o
                 CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      REMOVE_THEN "inj" (MP_TAC o SPECL [`(x1,t1):ctor_id#type_id`;
        `(x2,t2):ctor_id#type_id`; `l1:num`; `l2:num`; `stamp:stamp`]) THEN
      ASM_REWRITE_TAC[PAIR_EQ]]]);;

(* HOL4 line 3056 *)
let genv_c_tys_ok_extend = prove
 (`!c tys c_ext tys_ext.
     genv_c_tys_ok c tys /\ genv_c_tys_ok c_ext tys_ext /\
   DISJOINT (FDOM tys) (FDOM tys_ext)
   ==> genv_c_tys_ok (FUNION c c_ext) (FUNION tys tys_ext)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[genv_c_tys_ok_def; FDOM_FUNION; IN_UNION] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`cn:ctor_id`; `ty_id:num`; `arity:num`] THEN
  STRIP_TAC THEN RES_TAC THEN EXISTS_TAC `ctors:(ctor_id # num)list` THEN
  ASM_REWRITE_TAC[FLOOKUP_FUNION; option_CASE] THEN
  SUBGOAL_THEN `FLOOKUP (tys:(num,(ctor_id # num)list)fmap) ty_id = NONE`
    (fun th -> REWRITE_TAC[th; option_CASE] THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[flookup_thm] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flookup_thm; IN_DISJOINT]) THEN ASM_MESON_TAC[]);;

(* HOL4 line 3070 *)
let source_to_flatProof_maybe_all_list_SOME = prove
 (`!xs (ys:A list). maybe_all_list xs = SOME ys ==> xs = MAP SOME ys`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[maybe_all_list_def] THEN
  RW[] THEN EVERY_CASE_TAC THEN FS[] THEN RVEQ_TAC THEN FS[MAP]);;

(* HOL4 line 3080 *)
let some_f_inj_eq = prove
 (`!f y x.
     INJ (f:A->B) UNIV UNIV /\ y = f x ==> (some x. y = f x) = SOME x`,
  REWRITE_TAC[INJ; IN_UNIV] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[some_DEF] THEN COND_CASES_TAC THENL
   [AP_TERM_TAC THEN ASM_MESON_TAC[]; ASM_MESON_TAC[]]);;

let FLATP2AUX_v_to_word8_SOME = prove
 (`!v w. v_to_word8 v = SOME w <=> v = Litv (Word8 w)`,
  GEN_TAC THEN REWRITE_TAC[v_to_word8_def] THEN EVERY_CASE_TAC THEN
  SIMP[] THEN MESON_TAC[]);;

let FLATP2AUX_v_to_word64_SOME = prove
 (`!v w. v_to_word64 v = SOME w <=> v = Litv (Word64 w)`,
  GEN_TAC THEN REWRITE_TAC[v_to_word64_def] THEN EVERY_CASE_TAC THEN
  SIMP[] THEN MESON_TAC[]);;

let FLATP2AUX_v_to_word8_ALL2 = prove
 (`!xs vs2 bytes genv.
     ALL2 (source_to_flatProof_v_rel genv) xs vs2 /\
     MAP v_to_word8 xs = MAP SOME bytes
     ==> vs2 = MAP (flat_Litv o Word8) bytes`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `vs2:flat_v list` list_CASES) THEN
  STRUCT_CASES_TAC (ISPEC `bytes:(8 word)list` list_CASES) THEN
  REWRITE_TAC[ALL2; MAP; NOT_CONS_NIL; CONS_11; FLATP2AUX_v_to_word8_SOME] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  ASM_MESON_TAC[v_rel_eqns; o_THM]);;

let FLATP2AUX_v_to_word64_ALL2 = prove
 (`!xs vs2 words genv.
     ALL2 (source_to_flatProof_v_rel genv) xs vs2 /\
     MAP v_to_word64 xs = MAP SOME words
     ==> vs2 = MAP (flat_Litv o Word64) words`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `vs2:flat_v list` list_CASES) THEN
  STRUCT_CASES_TAC (ISPEC `words:(64 word)list` list_CASES) THEN
  REWRITE_TAC[ALL2; MAP; NOT_CONS_NIL; CONS_11; FLATP2AUX_v_to_word64_SOME] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  ASM_MESON_TAC[v_rel_eqns; o_THM]);;

let FLATP2AUX_INJ_MAP = prove
 (`!f:A->B. (!x y. f x = f y ==> x = y) ==> INJ (MAP f) UNIV UNIV`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INJ; IN_UNIV] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INJ_MAP_EQ THEN
  EXISTS_TAC `f:A->B` THEN ASM_REWRITE_TAC[INJ; IN_UNIV] THEN ASM_MESON_TAC[]);;

(* HOL4 line 3090 *)
let v_to_word8_list_rel = prove
 (`!bytes_v bytes genv v'.
     v_to_word8_list bytes_v = SOME bytes /\
   source_to_flatProof_v_rel genv bytes_v v' /\ genv_c_ok (global_env_c genv)
   ==> flat_v_to_bytes v' = SOME bytes`,
  REPEAT GEN_TAC THEN REWRITE_TAC[v_to_word8_list_def] THEN
  CASES_ON `v_to_list bytes_v` THEN SIMP[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `genv:global_env` source_to_flatProof_v_to_list) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`bytes_v:v`; `v':flat_v`; `a:v list`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP source_to_flatProof_maybe_all_list_SOME) THEN
  SUBGOAL_THEN `vs2 = MAP (flat_Litv o Word8) bytes` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[FLATP2AUX_v_to_word8_ALL2]; ALL_TAC] THEN
  ASM_REWRITE_TAC[flat_v_to_bytes_def; option_INJ] THEN
  MATCH_MP_TAC(REWRITE_RULE[] (ISPECL [`MAP (flat_Litv o Word8)`;
    `MAP (flat_Litv o Word8) bytes`; `bytes:(8 word)list`] some_f_inj_eq)) THEN
  MATCH_MP_TAC FLATP2AUX_INJ_MAP THEN
  REWRITE_TAC[o_THM; injectivity "flat_v"; injectivity "lit"]);;

(* HOL4 line 3112 *)
let v_to_word64_list_rel = prove
 (`!words_v words genv v'.
     v_to_word64_list words_v = SOME words /\
   source_to_flatProof_v_rel genv words_v v' /\ genv_c_ok (global_env_c genv)
   ==> flat_v_to_words v' = SOME words`,
  REPEAT GEN_TAC THEN REWRITE_TAC[v_to_word64_list_def] THEN
  CASES_ON `v_to_list words_v` THEN SIMP[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `genv:global_env` source_to_flatProof_v_to_list) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`words_v:v`; `v':flat_v`; `a:v list`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP source_to_flatProof_maybe_all_list_SOME) THEN
  SUBGOAL_THEN `vs2 = MAP (flat_Litv o Word64) words` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[FLATP2AUX_v_to_word64_ALL2]; ALL_TAC] THEN
  ASM_REWRITE_TAC[flat_v_to_words_def; option_INJ] THEN
  MATCH_MP_TAC(REWRITE_RULE[] (ISPECL [`MAP (flat_Litv o Word64)`;
    `MAP (flat_Litv o Word64) words`; `words:(64 word)list`] some_f_inj_eq)) THEN
  MATCH_MP_TAC FLATP2AUX_INJ_MAP THEN
  REWRITE_TAC[o_THM; injectivity "flat_v"; injectivity "lit"]);;

(* HOL4 line 3134 *)
let keep_glob_alloc = prove
 (`!calc next st.
     keep (calc:B spt) (glob_alloc next st)`,
  REWRITE_TAC[keep_def; glob_alloc_def; flat_elim_is_pure_def; ALL] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* HOL4 line 3140 *)
let inc_compile_prog_nonempty = prove
 (`!env_id st decs st' fdecs.
     inc_compile_prog env_id st decs = (st', fdecs) ==> ~(fdecs = [])`,
  RW[inc_compile_prog_def] THEN REPEAT PAIRARG_TAC THEN FS[] THEN
  RVEQ_TAC THEN FS[]);;

(* HOL4 line 3148 *)
let src_orac_env_invs_lookup_env = prove
 (`!es env_id env interp genv st_v decs.
     lookup_env es env_id = SOME env /\
   src_orac_env_invs (interp:(v->(source_to_flat_config#C)option)option) genv
     (SOME (EvalOracle es)) /\
   eval_oracle_state_oracle es 0 = (env_id, st_v, decs)
   ==> ?c x gen comp_map.
         (THE interp) st_v = SOME (c, x) /\
         lookup (FST env_id) (environment_store_env_gens (source_to_flat_config_envs c)) =
           SOME gen /\
         lookup (SND env_id) gen = SOME comp_map /\
         global_env_inv genv comp_map {} env`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `env_id:num#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `j:num` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[lookup_env_def; option_case_eq; oEL_EQ_EL; distinctness "option"] THEN
  REWRITE_TAC[src_orac_env_invs_def; src_orac_next_cfg_def] THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FST; SND] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `src_orac_next_cfg_inner (interp:(v->(source_to_flat_config#C)option)option)
                 (eval_oracle_state_oracle es 0) = SOME c` THEN
  ASM_REWRITE_TAC[src_orac_next_cfg_inner_def] THEN
  CASES_ON `interp:(v->(source_to_flat_config#C)option)option` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[THE_DEF] THEN
  CASES_ON `(a':v->(source_to_flat_config#C)option) st_v` THEN
  CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `a'':source_to_flat_config#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c':source_to_flat_config` (X_CHOOSE_THEN `x:C` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  MAP_EVERY EXISTS_TAC [`c:source_to_flat_config`; `x:C`] THEN ASM_MESON_TAC[]);;

(* HOL4 line 3171 *)
let source_to_flatProof_FST_SND_EQ_CASE = prove
 (`FST = (\(a:A,b:B). a) /\ SND = (\(a:A,b:B). b)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]);;

(* HOL4 line 3177 *)
let step_1 = prove
 (`!interp g es.
     src_orac_step_invs (interp:(v->(source_to_flat_config#C)option)option) g
     (SOME (EvalOracle es))
   ==> ?i_f env_id0 st_v0 decs0 fdecs0 c0 x0 env_id1 st_v1 decs1 c1 x1.
         interp = SOME i_f /\
         eval_oracle_state_oracle es 0 = (env_id0, st_v0, decs0) /\
         eval_oracle_state_oracle es 1 = (env_id1, st_v1, decs1) /\
         i_f st_v0 = SOME (c0, x0) /\
         i_f st_v1 = SOME (c1, x1) /\
         inc_compile_prog env_id0 c0 (g decs0) = (c1, fdecs0) /\
         src_orac_next_cfg (SOME i_f) (SOME (EvalOracle es)) = SOME c0`,
  REPEAT GEN_TAC THEN
  CASES_ON `interp:(v->(source_to_flat_config#C)option)option` THEN
  REWRITE_TAC[src_orac_step_invs_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; o_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dec") (LABEL_TAC "step")) THEN
  MAP_EVERY (fun k ->
    MP_TAC(ISPEC (mk_comb(`eval_oracle_state_oracle es`, mk_small_numeral k))
                 PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN (mk_var("e"^string_of_int k,`:num#num`))
      (X_CHOOSE_THEN (mk_var("p"^string_of_int k,`:v#dec list`)) ASSUME_TAC)) THEN
    MP_TAC(ISPEC (mk_var("p"^string_of_int k,`:v#dec list`)) PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN (mk_var("s"^string_of_int k,`:v`))
      (X_CHOOSE_THEN (mk_var("d"^string_of_int k,`:dec list`)) SUBST_ALL_TAC)))
    [0; 1] THEN
  SUBGOAL_THEN `eval_oracle_state_oracle es 0 = (e0:num#num),(s0:v),(d0:dec list) /\
                eval_oracle_state_oracle es 1 = (e1:num#num),(s1:v),(d1:dec list)`
    (CONJUNCTS_THEN (fun th -> LABEL_TAC "o" th THEN
       USE_THEN "dec" (STRIP_ASSUME_TAC o C MATCH_MP th))) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "step" (MP_TAC o C MATCH_MP (ASSUME
    `eval_oracle_state_oracle es 0 = (e0:num#num),(s0:v),(d0:dec list)`)) THEN
  ASM_REWRITE_TAC[ARITH_RULE `SUC 0 = 1`; THE_DEF; FST; SND] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`a:v->(source_to_flat_config#C)option`; `e0:num#num`; `s0:v`;
    `d0:dec list`; `SND (inc_compile_prog e0 c ((g:dec list->dec list) d0))`;
    `c:source_to_flat_config`; `x:C`; `e1:num#num`; `s1:v`; `d1:dec list`;
    `c':source_to_flat_config`; `x':C`] THEN
  ASM_REWRITE_TAC[src_orac_next_cfg_def; src_orac_next_cfg_inner_def] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[PAIR] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 3202 *)
let subglobals_add_NONE = prove
 (`!gs n.
     subglobals (gs:(A option)list) (APPEND gs (REPLICATE n NONE))`,
  SIMP_TAC[subglobals_def; LENGTH_APPEND; EL_APPEND; LE_ADD]);;

let FLATP2AUX_do_eval_oracle_SOME = prove
 (`!vs es env decs eval_state f g.
     do_eval vs (SOME (EvalOracle es)) = SOME (env,decs,eval_state) /\
     eval_oracle_state_custom_do_eval es = do_eval_oracle f g
     ==> ?env_id_v st_v decs_v st_v2 bs_v ws_v env_id st decs0 c_bs c_ws.
           vs = [env_id_v; st_v; decs_v; st_v2; bs_v; ws_v] /\
           eval_oracle_state_oracle es 0 = (env_id, st, decs0) /\
           f (env_id, st, decs0) =
             SOME (FST (SND (eval_oracle_state_oracle es 1)), c_bs, c_ws) /\
           v_to_word8_list bs_v = SOME c_bs /\ v_to_word64_list ws_v = SOME c_ws /\
           lookup_env es env_id = SOME env /\
           decs = g decs0 /\
           eval_state =
             SOME (EvalOracle (add_env_generation
               (eval_oracle_state_oracle_fupd
                  (K (shift_seq 1 (eval_oracle_state_oracle es))) es)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[do_eval_def] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST1_TAC) THEN
  REWRITE_TAC[do_eval_oracle_def] THEN
  FLATP2AUX_LIST_SPLIT_TAC `vs:v list` `v1:v` `t1:v list` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"] THEN
  FLATP2AUX_LIST_SPLIT_TAC `t1:v list` `v2:v` `t2:v list` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"] THEN
  FLATP2AUX_LIST_SPLIT_TAC `t2:v list` `v3:v` `t3:v list` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"] THEN
  FLATP2AUX_LIST_SPLIT_TAC `t3:v list` `v4:v` `t4:v list` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"] THEN
  FLATP2AUX_LIST_SPLIT_TAC `t4:v list` `v5:v` `t5:v list` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"] THEN
  FLATP2AUX_LIST_SPLIT_TAC `t5:v list` `v6:v` `t6:v list` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"] THEN
  FLATP2AUX_LIST_SPLIT_TAC `t6:v list` `v7:v` `t7:v list` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"] THEN
  REWRITE_TAC[option_case_eq; pair_case_eq; COND_CASE_EQ; distinctness "option";
              injectivity "option"; PAIR_EQ] THEN
  STRIP_TAC THEN GVS[PAIR_EQ] THEN
  MAP_EVERY EXISTS_TAC [`v1:v`; `v2:v`; `v3:v`; `v4:v`; `v5:v`; `v6:v`] THEN
  REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let FLATP2AUX_do_eval_NONE = prove
 (`!vs. do_eval vs NONE = NONE`,
  REWRITE_TAC[do_eval_def] THEN CASE_REWRITE_TAC[]);;

let FLATP2AUX_orac_rel_SOME = prove
 (`!interp g es0 fc.
     orac_rel (interp:(v->(source_to_flat_config#C)option)option) g (SOME es0) fc
     ==> ?dec es s_compiler. interp = SOME dec /\ es0 = EvalOracle es /\
           eval_oracle_state_custom_do_eval es = do_eval_oracle s_compiler g /\
           orac_rel_inner dec es s_compiler g fc`,
  REPEAT GEN_TAC THEN REWRITE_TAC[orac_rel_def] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `interp:(v->(source_to_flat_config#C)option)option` THEN
  CASE_REWRITE_TAC[] THEN CASES_ON `es0:eval_state` THEN CASE_REWRITE_TAC[] THEN
  MESON_TAC[]);;

let FLATP2AUX_flat_do_eval_SOME = prove
 (`!v1 v2 bs ws (ec:(C)install_config) st decs st'.
     flat_v_to_bytes v1 = SOME bs /\ flat_v_to_words v2 = SOME ws /\
     install_config_compile_oracle ec 0 = (st, decs) /\
     install_config_compile ec st decs = SOME (bs, ws, st') /\ ~(decs = []) /\
     FST (install_config_compile_oracle ec 1) = st'
     ==> flat_do_eval [v1; v2] ec =
         SOME (decs, install_config_compile_oracle_fupd
                       (K (shift_seq 1 (install_config_compile_oracle ec))) ec, Unitv)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[flat_do_eval_def] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[shift_seq_def; ADD_CLAUSES; ARITH_RULE `0 + 1 = 1`]);;

let FLATP2AUX_ALL2_6 = prove
 (`!R a1 a2 a3 a4 a5 a6 l.
     ALL2 (R:A->B->bool) [a1;a2;a3;a4;a5;a6] l <=>
     ?b1 b2 b3 b4 b5 b6. l = [b1;b2;b3;b4;b5;b6] /\ R a1 b1 /\ R a2 b2 /\ R a3 b3 /\
                         R a4 b4 /\ R a5 b5 /\ R a6 b6`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIST_REL_CONS1; LIST_REL_NIL] THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[CONS_11] THEN ASM_MESON_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[CONS_11]]);;

let FLATP2AUX_subspt_insert = prove
 (`!t n (x:A). domain t SUBSET count n ==> subspt t (insert n x t)`,
  REWRITE_TAC[subspt_lookup; lookup_insert; SUBSET; IN_COUNT] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(n:num) IN domain (t:A spt)` (fun th -> ASM_MESON_TAC[th; LT_REFL]) THEN
  REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[]);;

let FLATP2AUX_ALL_DISJOINT_4 = prove
 (`!a f b d x f' d'.
     ALL_DISJOINT [a; f; b; d:A->bool] /\ x SUBSET f /\ f' SUBSET (f DIFF x) /\
     d' SUBSET d
     ==> ALL_DISJOINT [x; f'; a UNION b; d']`,
  REWRITE_TAC[ALL_DISJOINT_CONS] THEN SET_TAC[]);;

let FLATP2AUX_idx_block_final = prove
 (`!i0 i1. idx_prev i0 i1
     ==> idx_block i0 i1 SUBSET idx_final_block i0 /\
         idx_final_block i1 SUBSET (idx_final_block i0 DIFF idx_block i0 i1)`,
  REWRITE_TAC[idx_prev_def; idx_block_def; idx_final_block_def] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_ELIM_THM; FORALL_PAIR_THM] THEN
  SIMP_NOASM[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  FS[distinctness "idx_types"] THEN ASM_ARITH_TAC);;

let FLATP2AUX_genv_allocated_idxs_NONE = prove
 (`!genv n. genv_allocated_idxs
              (global_env_v_fupd (K (APPEND (global_env_v genv) (REPLICATE n NONE))) genv)
            SUBSET genv_allocated_idxs genv`,
  REWRITE_TAC[genv_allocated_idxs_def; global_env_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM; LENGTH_APPEND; LENGTH_REPLICATE] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT `(a ==> a') ==> (a \/ b ==> a' \/ b)`) THEN
  STRIP_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(EL i (APPEND (global_env_v genv) (REPLICATE n NONE)) = (NONE:flat_v option))` THEN
  REWRITE_TAC[EL_APPEND] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[EL_REPLICATE; ARITH_RULE `~(i < l) /\ i < l + n ==> i - l < n`]);;

let FLATP2AUX_inc_compile_prog_eq = prove
 (`!env_id c p n0 next e gen p'.
     source_to_flat_compile_decs [] 1 (source_to_flat_config_next c)
       (lookup_env_id env_id (source_to_flat_config_envs c))
       (environment_generation_store_REC 0
          (environment_store_next (source_to_flat_config_envs c)) LN) p =
       (n0, next, e, gen, p')
     ==> inc_compile_prog env_id c p =
         (source_to_flat_config_next_fupd (K next)
            (source_to_flat_config_envs_fupd (K (environment_store_REC
               (environment_store_next (source_to_flat_config_envs c) + 1)
               (insert (environment_store_next (source_to_flat_config_envs c))
                  (insert (environment_generation_store_next gen)
                     (extend_env e (lookup_env_id env_id (source_to_flat_config_envs c)))
                     (environment_generation_store_envs gen))
                  (environment_store_env_gens (source_to_flat_config_envs c))))) c),
          CONS (glob_alloc next c)
            (APPEND p' [store_env_id (environment_generation_store_generation gen)
                                     (environment_generation_store_next gen)]))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[inc_compile_prog_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

(* HOL4 line 3208 (HOL4's unused existential fin_idx dropped) *)
let do_eval = prove
 (CASE_TERM `!vs' vs s env decs eval_state interp g gen genv idxs t.
     do_eval vs (state_eval_state s) = SOME (env, decs, eval_state) /\
         invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv idxs
           (s:(FFI)state) (t:(C,FFI)flat_state) /\
         ALL2 (source_to_flatProof_v_rel genv) vs vs'
         ==> ?genv' env_id c decs' eval_config' c' idx end_idx other.
               idxs = (idx, end_idx, other) /\
               flat_do_eval (DROP 4 vs') (flat_state_eval_config t) =
                 SOME (decs', eval_config', Unitv) /\
               LENGTH vs' = 6 /\
               inc_compile_prog env_id c decs = (c', decs') /\
               ~(decs' = []) /\
               invariant interp g
                 (environment_generation_store_REC 0
                    (environment_store_next (source_to_flat_config_envs c)) LN)
                 genv'
                 (source_to_flat_config_next c, source_to_flat_config_next c',
                  idx_block idx end_idx UNION other)
                 (state_eval_state_fupd (K eval_state) s)
                 (flat_state_eval_config_fupd (K eval_config')
                    (flat_state_globals_fupd
                       (K (APPEND (flat_state_globals t)
                             (REPLICATE (next_indices_vidx (source_to_flat_config_next c') -
                                         next_indices_vidx (source_to_flat_config_next c))
                                NONE))) t)) /\
               env_gen_rel
                 (environment_generation_store_REC 0
                    (environment_store_next (source_to_flat_config_envs c)) LN)
                 eval_state /\
               (match source_to_flat_compile_decs [] 1 (source_to_flat_config_next c)
                        (lookup_env_id env_id (source_to_flat_config_envs c))
                        (environment_generation_store_REC 0
                           (environment_store_next (source_to_flat_config_envs c)) LN)
                        decs with
                  (_, _, _, gen, _) -> env_gen_future_rel interp gen eval_state) /\
               global_env_inv genv' (lookup_env_id env_id (source_to_flat_config_envs c)) {}
                 env /\
               src_orac_next_cfg interp eval_state = SOME c' /\
               idx_prev end_idx (source_to_flat_config_next c') /\
               global_env_c genv SUBMAP global_env_c genv' /\
               global_env_tys genv SUBMAP global_env_tys genv' /\
               subglobals (global_env_v genv) (global_env_v genv') /\
               orac_config_envs_subspt interp (state_eval_state s) eval_state /\
               (match state_eval_state s with
                  SOME (EvalOracle s0) ->
                    ?s'. eval_state = SOME (EvalOracle s') /\
                         eval_oracle_state_envs s' =
                           eval_oracle_state_envs (add_env_generation s0) /\
                         eval_oracle_state_generation s' =
                           eval_oracle_state_generation (add_env_generation s0)
                | _ -> F)`,
X_GEN_TAC `vs':flat_v list` THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ev") (CONJUNCTS_THEN2 (LABEL_TAC "inv")
    (LABEL_TAC "vs"))) THEN
  FLATP2AUX_INV_TAC "inv" THEN
  SUBGOAL_THEN `?es0. state_eval_state (s:(FFI)state) = SOME es0` STRIP_ASSUME_TAC THENL
   [USE_THEN "ev" MP_TAC THEN CASES_ON `state_eval_state (s:(FFI)state)` THEN
    REWRITE_TAC[FLATP2AUX_do_eval_NONE; distinctness "option"] THEN MESON_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `state_eval_state (s:(FFI)state) = SOME es0`]) THEN
  REWRITE_TAC[ASSUME `state_eval_state (s:(FFI)state) = SOME es0`] THEN
  USE_THEN "orac_rel" (MP_TAC o MATCH_MP FLATP2AUX_orac_rel_SOME) THEN
  DISCH_THEN(X_CHOOSE_THEN `dec:v->(source_to_flat_config#C)option`
    (X_CHOOSE_THEN `es:eval_oracle_state` (X_CHOOSE_THEN `s_compiler:compiler_fun`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC
        (CONJUNCTS_THEN2 (LABEL_TAC "cde") (LABEL_TAC "inner"))))))) THEN
  USE_THEN "ev" (fun ev -> USE_THEN "cde" (fun cde ->
    MP_TAC (MATCH_MP FLATP2AUX_do_eval_oracle_SOME (CONJ ev cde)))) THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`env_id_v:v`; `st_v:v`; `decs_v:v`; `st_v2:v`;
    `bs_v:v`; `ws_v:v`; `env_id:num#num`; `st:v`; `decs0:dec list`;
    `c_bs:(8 word)list`; `c_ws:(64 word)list`]
     (FLATP2AUX_LABEL_CONJS ["vs6"; "or0"; "scomp"; "bs"; "ws"; "lookup_env";
                             "decs"; "es'"])) THEN
  USE_THEN "src_orac" (MP_TAC o MATCH_MP step_1 o CONJUNCT1 o
                       REWRITE_RULE[src_orac_invs_def]) THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`i_f:v->(source_to_flat_config#C)option`;
    `e0:num#num`; `sv0:v`; `d0:dec list`; `fdecs0:flat_exp list`;
    `c0:source_to_flat_config`; `x0:C`; `e1:num#num`; `sv1:v`; `d1:dec list`;
    `c1:source_to_flat_config`; `x1:C`]
    (FLATP2AUX_LABEL_CONJS ["s_if"; "s_or0"; "s_or1"; "s_dec0"; "s_dec1"; "s_inc";
                            "s_next"])) THEN
  REMOVE_THEN "s_if" (SUBST_ALL_TAC o SYM o REWRITE_RULE[injectivity "option"]) THEN
  REMOVE_THEN "s_or0" (MP_TAC o REWRITE_RULE[ASSUME
    `eval_oracle_state_oracle es 0 = (env_id:num#num),(st:v),(decs0:dec list)`]) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM)
    (SUBST_ALL_TAC o SYM))) THEN
  USE_THEN "inner" (MP_TAC o SPECL [`0`; `env_id:num#num`; `st:v`; `decs0:dec list`] o
    REWRITE_RULE[orac_rel_inner_def]) THEN
  FLATP2AUX_LREWRITE_TAC ["or0"; "s_dec0"; "scomp"; "s_inc"]
    [LET_DEF; LET_END_DEF; THE_DEF; FST; SND; distinctness "option";
     injectivity "option"; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "co0") (FLATP2AUX_CHOOSE_THEN
    [`bytes:(8 word)list`; `words:(64 word)list`; `f_st:C`; `st_v2':v`]
    (FLATP2AUX_LABEL_CONJS ["comp0"; "st_v2'"; "f_st"]))) THEN
  USE_THEN "inner" (MP_TAC o SPECL [`1`; `e1:num#num`; `sv1:v`; `d1:dec list`] o
    REWRITE_RULE[orac_rel_inner_def]) THEN
  FLATP2AUX_LREWRITE_TAC ["s_or1"; "s_dec1"]
    [LET_DEF; LET_END_DEF; THE_DEF; FST; SND; distinctness "option";
     injectivity "option"; PAIR_EQ] THEN
  DISCH_THEN(LABEL_TAC "co1" o CONJUNCT1) THEN
  REMOVE_THEN "st_v2'" (CONJUNCTS_THEN2 (MP_TAC o SYM)
    (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM))) THEN
  FLATP2AUX_LREWRITE_TAC ["s_or1"] [FST; SND] THEN DISCH_THEN SUBST_ALL_TAC THEN
  USE_THEN "f_st" (MP_TAC o SPEC `(c1:source_to_flat_config),(x1:C)`) THEN
  FLATP2AUX_LREWRITE_TAC ["s_dec1"] [SND] THEN DISCH_THEN SUBST_ALL_TAC THEN
  (* the flat values *)
  USE_THEN "vs" (MP_TAC o REWRITE_RULE[ASSUME
    `vs = [env_id_v:v; st_v; decs_v; st_v2; bs_v; ws_v]`]) THEN
  REWRITE_TAC[FLATP2AUX_ALL2_6] THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`w1:flat_v`; `w2:flat_v`; `w3:flat_v`; `w4:flat_v`;
    `w5:flat_v`; `w6:flat_v`] (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (FLATP2AUX_LABEL_CONJS ["r1"; "r2"; "r3"; "r4"; "r5"; "r6"]))) THEN
  SUBGOAL_THEN `flat_do_eval [w5; w6] (flat_state_eval_config (t:(C,FFI)flat_state)) =
      SOME (fdecs0, install_config_compile_oracle_fupd (K (shift_seq 1
        (install_config_compile_oracle (flat_state_eval_config t))))
        (flat_state_eval_config t), Unitv)` (LABEL_TAC "fde") THENL
   [MATCH_MP_TAC FLATP2AUX_flat_do_eval_SOME THEN
    MAP_EVERY EXISTS_TAC [`c_bs:(8 word)list`; `c_ws:(64 word)list`; `x0:C`; `f_st:C`] THEN
    FLATP2AUX_LREWRITE_TAC ["co0"; "comp0"; "co1"] [] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC v_to_word8_list_rel THEN
      MAP_EVERY EXISTS_TAC [`bs_v:v`; `genv:global_env`] THEN
      FLATP2AUX_LREWRITE_TAC ["bs"; "r5"; "c_ok"] [];
      MATCH_MP_TAC v_to_word64_list_rel THEN
      MAP_EVERY EXISTS_TAC [`ws_v:v`; `genv:global_env`] THEN
      FLATP2AUX_LREWRITE_TAC ["ws"; "r6"; "c_ok"] [];
      USE_THEN "s_inc" (ACCEPT_TAC o MATCH_MP inc_compile_prog_nonempty)];
    ALL_TAC] THEN
  SUBGOAL_THEN `src_orac_next_cfg (SOME (dec:v->(source_to_flat_config#C)option))
      (SOME (EvalOracle (add_env_generation (eval_oracle_state_oracle_fupd
        (K (shift_seq 1 (eval_oracle_state_oracle es))) es)))) = SOME c1`
    (LABEL_TAC "nc") THENL
   [REWRITE_TAC[src_orac_next_cfg_def; src_orac_next_cfg_inner_def; add_env_generation_def] THEN
    FLATP2AUX_LKSIMP_TAC ["s_or1"; "s_dec1"] [shift_seq_def];
    ALL_TAC] THEN
  USE_THEN "s_inc" (LABEL_TAC "idxp" o MATCH_MP inc_compile_prog_idx_prev) THEN
  MP_TAC(ISPEC `source_to_flat_compile_decs [] 1 (source_to_flat_config_next c0)
     (lookup_env_id env_id (source_to_flat_config_envs c0))
     (environment_generation_store_REC 0 (environment_store_next
        (source_to_flat_config_envs c0)) LN) ((g:dec list->dec list) decs0)`
     BASICAUX_TUPLE5) THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`n0:num`; `nx:next_indices`;
    `e1:source_to_flat_environment`; `gen1:environment_generation_store`;
    `p1:flat_exp list`] (LABEL_TAC "cd")) THEN
  USE_THEN "cd" (MP_TAC o MATCH_MP FLATP2AUX_inc_compile_prog_eq) THEN
  FLATP2AUX_LREWRITE_TAC ["s_inc"] [PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c1eq") (LABEL_TAC "fd_eq")) THEN
  USE_THEN "src_orac" (MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[src_orac_invs_def]) THEN
  REWRITE_TAC[src_orac_env_invs_def] THEN CASE_REWRITE_TAC[] THEN
  FLATP2AUX_LREWRITE_TAC ["s_next"] [injectivity "option"; UNWIND_THM1] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["esi"; "esn"; "eenv"]) THEN
  USE_THEN "idx_range" (MP_TAC o REWRITE_RULE[idx_range_rel_def]) THEN
  FLATP2AUX_LREWRITE_TAC ["s_next"] [] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`i1:next_indices`; `i2:next_indices`;
    `fin_idx:next_indices`; `ob:num#idx_types->bool`]
    (FLATP2AUX_LABEL_CONJS ["ir_eq"; "ir_fin"; "ir_prev"; "ir_disj"; "ir_ts"; "ir_en"])) THEN
  REMOVE_THEN "ir_fin" SUBST_ALL_TAC THEN REMOVE_THEN "ir_eq" SUBST_ALL_TAC THEN
  MAP_EVERY EXISTS_TAC [`global_env_v_fupd (K (APPEND (global_env_v genv)
      (REPLICATE (next_indices_vidx (source_to_flat_config_next c1) -
                  next_indices_vidx (source_to_flat_config_next c0)) NONE))) genv`;
    `env_id:num#num`; `c0:source_to_flat_config`; `fdecs0:flat_exp list`;
    `install_config_compile_oracle_fupd (K (shift_seq 1
        (install_config_compile_oracle (flat_state_eval_config (t:(C,FFI)flat_state)))))
        (flat_state_eval_config t)`;
    `c1:source_to_flat_config`; `i1:next_indices`; `i2:next_indices`;
    `ob:num#idx_types->bool`] THEN
  SUBGOAL_THEN `DROP 4 [w1:flat_v; w2; w3; w4; w5; w6] = [w5; w6]` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 = SUC(SUC(SUC(SUC 0)))`; DROP]; ALL_TAC] THEN
  FLATP2AUX_LREWRITE_TAC ["fde"; "decs"; "s_inc"; "es'"]
    [LENGTH; ARITH; invariant_def; ARITH_RULE `SUC 0 = 1`] THEN
  SIMP_NOASM[] THEN REPEAT CONJ_TAC THENL
   [(* 1 nonempty *)
    USE_THEN "s_inc" (ACCEPT_TAC o MATCH_MP inc_compile_prog_nonempty);
    (* 2 *) USE_THEN "c_ok" ACCEPT_TAC;
    (* 3 *) USE_THEN "tys_ok" ACCEPT_TAC;
    (* 4 s_rel *)
    USE_THEN "s_rel" MP_TAC THEN REWRITE_TAC[source_to_flatProof_s_rel_cases] THEN
    SIMP_NOASM[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LIST_REL_sv_rel_weak THEN EXISTS_TAC `genv:global_env` THEN
    ASM_REWRITE_TAC[] THEN SIMP_NOASM[SUBMAP_REFL; subglobals_add_NONE];
    (* 5 idx_range_rel *)
    REWRITE_TAC[idx_range_rel_def] THEN FLATP2AUX_LREWRITE_TAC ["nc"] [] THEN
    CASE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`source_to_flat_config_next c0`; `source_to_flat_config_next c1`;
      `source_to_flat_config_next c1`; `idx_block i1 i2 UNION ob`] THEN
    REWRITE_TAC[idx_prev_refl] THEN SIMP_NOASM[] THEN
    FLATP2AUX_LREWRITE_TAC ["ir_ts"; "ir_en"] [] THEN
    MATCH_MP_TAC FLATP2AUX_ALL_DISJOINT_4 THEN
    MAP_EVERY EXISTS_TAC [`idx_final_block (source_to_flat_config_next c0)`;
                          `genv_allocated_idxs genv`] THEN
    USE_THEN "idxp" (fun th -> REWRITE_TAC[MATCH_MP FLATP2AUX_idx_block_final th]) THEN
    FLATP2AUX_LREWRITE_TAC ["ir_disj"] [FLATP2AUX_genv_allocated_idxs_NONE];
    (* 6 src_orac_invs *)
    REWRITE_TAC[src_orac_invs_def] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "src_orac" (MP_TAC o CONJUNCT1 o REWRITE_RULE[src_orac_invs_def]) THEN
      REWRITE_TAC[src_orac_step_invs_def] THEN CASE_REWRITE_TAC[] THEN
      SIMP_NOASM[add_env_generation_def; shift_seq_def; LET_DEF; LET_END_DEF; o_THM] THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THEN
      REWRITE_TAC[ARITH_RULE `SUC k + 1 = SUC (k + 1)`] THEN ASM_MESON_TAC[];
      REWRITE_TAC[src_orac_env_invs_def] THEN CASE_REWRITE_TAC[] THEN
      FLATP2AUX_LREWRITE_TAC ["nc"] [injectivity "option"; UNWIND_THM1] THEN
      USE_THEN "s_inc" (fun th -> USE_THEN "esi" (fun th2 ->
        STRIP_ASSUME_TAC (MATCH_MP inc_compile_prog_env_submap (CONJ th th2)))) THEN
      ASM_REWRITE_TAC[] THEN
      FLATP2AUX_LKSIMP_TAC ["c1eq"; "esn"] [add_env_generation_def; LENGTH_APPEND; LENGTH;
        ARITH_RULE `SUC 0 = 1`] THEN
      MAP_EVERY X_GEN_TAC [`g_id:num`; `id:num`] THEN
      REWRITE_TAC[EL_APPEND] THEN ASM_CASES_TAC `g_id < LENGTH (eval_oracle_state_envs es)` THEN
      ASM_REWRITE_TAC[] THENL
       [STRIP_TAC THEN REMOVE_THEN "eenv" (MP_TAC o SPECL [`g_id:num`; `id:num`]) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        MAP_EVERY EXISTS_TAC [`comp_map_gen:(source_to_flat_environment)spt`;
                              `comp_map:source_to_flat_environment`] THEN
        ASM_SIMP_TAC[lookup_insert; ARITH_RULE `g < l ==> ~(g = l:num)`] THEN
        MATCH_MP_TAC global_env_inv_weak THEN
        EXISTS_TAC `genv:global_env` THEN ASM_REWRITE_TAC[] THEN
        SIMP_NOASM[SUBMAP_REFL] THEN
        FLATP2AUX_LREWRITE_TAC ["globals"] [subglobals_add_NONE];
        STRIP_TAC THEN
        SUBGOAL_THEN `g_id - LENGTH (eval_oracle_state_envs es) = 0`
          (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; EL; HD; LENGTH; LT])) THENL
         [ASM_ARITH_TAC; FLATP2AUX_F_TAC]];
      REWRITE_TAC[src_orac_gen_inv_def] THEN CASE_REWRITE_TAC[] THEN
      SIMP_NOASM[add_env_generation_def; LENGTH_APPEND; LENGTH] THEN ARITH_TAC];
    (* 7 orac_rel *)
    REWRITE_TAC[orac_rel_def] THEN CASE_REWRITE_TAC[] THEN
    EXISTS_TAC `s_compiler:compiler_fun` THEN
    SIMP_NOASM[add_env_generation_def] THEN
    FLATP2AUX_LREWRITE_TAC ["cde"] [orac_rel_inner_def] THEN
    SIMP_NOASM[shift_seq_def] THEN X_GEN_TAC `k:num` THEN
    USE_THEN "inner" (MP_TAC o SPEC `k + 1` o REWRITE_RULE[orac_rel_inner_def]) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[];
    (* 8 *) USE_THEN "globals" ACCEPT_TAC;
    (* 9 eval_ref_inv *)
    REMOVE_THEN "eval_ref" MP_TAC THEN
    MP_TAC(ISPEC `flat_state_globals (t:(C,FFI)flat_state)` list_CASES) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[eval_ref_inv_def; ARITH_RULE `1 = SUC 0`; TAKE; APPEND;
                                   TAKE_nil; NOT_CONS_NIL];
    (* 10 env_gen_inv *)
    SIMP_NOASM[env_gen_inv_def; domain_def; EMPTY_SUBSET];
    (* 11 fin_idx_match *)
    FLATP2AUX_LREWRITE_TAC ["nc"] [fin_idx_match_def] THEN CASE_REWRITE_TAC[] THEN
    USE_THEN "fin_idx" MP_TAC THEN
    FLATP2AUX_LREWRITE_TAC ["s_next"] [fin_idx_match_def] THEN CASE_REWRITE_TAC[] THEN
    USE_THEN "idxp" MP_TAC THEN REWRITE_TAC[idx_prev_def] THEN ARITH_TAC;
    (* 12 env_gen_rel *)
    REWRITE_TAC[env_gen_rel_def] THEN CASE_REWRITE_TAC[] THEN
    FLATP2AUX_LKSIMP_TAC ["esn"] [add_env_generation_def; LENGTH_APPEND; EL_APPEND;
      LT_REFL; SUB_REFL; LENGTH; ARITH_RULE `n < n + 1`; EL; HD];
    (* 13 compile_decs future rel *)
    FLATP2AUX_LREWRITE_TAC ["cd"] [] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[env_gen_future_rel_def] THEN FLATP2AUX_LREWRITE_TAC ["nc"] [] THEN
    CASE_REWRITE_TAC[] THEN
    USE_THEN "cd" (ASSUME_TAC o MATCH_MP compile_decs_generation) THEN
    USE_THEN "cd" (MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] compile_decs_env_gen_inv)) THEN
    ANTS_TAC THENL [SIMP_NOASM[env_gen_inv_def; domain_def; EMPTY_SUBSET]; STRIP_TAC] THEN
    FLATP2AUX_LKSIMP_TAC ["c1eq"] [lookup_insert] THEN
    ASM_REWRITE_TAC[] THEN SIMP_NOASM[] THEN
    MATCH_MP_TAC FLATP2AUX_subspt_insert THEN ASM_REWRITE_TAC[GSYM env_gen_inv_def];
    (* 14 global_env_inv *)
    MP_TAC(ISPECL [`es:eval_oracle_state`; `env_id:num#num`; `env:v sem_env`;
      `SOME (dec:v->(source_to_flat_config#C)option)`; `genv:global_env`; `st:v`;
      `decs0:dec list`] src_orac_env_invs_lookup_env) THEN
    USE_THEN "src_orac" (fun th -> FLATP2AUX_LREWRITE_TAC ["lookup_env"; "or0"]
      [CONJUNCT1 (CONJUNCT2 (REWRITE_RULE[src_orac_invs_def] th))]) THEN
    FLATP2AUX_LREWRITE_TAC ["s_dec0"] [THE_DEF; injectivity "option"; PAIR_EQ] THEN
    DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`cc:source_to_flat_config`; `xx:C`;
      `gg:(source_to_flat_environment)spt`; `cm:source_to_flat_environment`]
      (FLATP2AUX_LABEL_CONJS ["cx"; "lk1"; "lk2"; "gei"])) THEN
    REMOVE_THEN "cx" (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[lookup_env_id_def] THEN FLATP2AUX_LREWRITE_TAC ["lk1"] [] THEN
    CASE_REWRITE_TAC[] THEN FLATP2AUX_LREWRITE_TAC ["lk2"] [] THEN CASE_REWRITE_TAC[] THEN
    MATCH_MP_TAC global_env_inv_weak THEN EXISTS_TAC `genv:global_env` THEN
    FLATP2AUX_LREWRITE_TAC ["gei"] [] THEN SIMP_NOASM[SUBMAP_REFL] THEN
    FLATP2AUX_LREWRITE_TAC ["globals"] [subglobals_add_NONE];
    (* 15 *) USE_THEN "nc" ACCEPT_TAC;
    (* 16 idx_prev *)
    MATCH_MP_TAC idx_prev_trans THEN
    EXISTS_TAC `source_to_flat_config_next c0` THEN
    FLATP2AUX_LREWRITE_TAC ["ir_prev"; "idxp"] [];
    (* 17 *) REWRITE_TAC[subglobals_add_NONE];
    (* 18 orac_config_envs_subspt *)
    FLATP2AUX_LREWRITE_TAC ["nc"; "s_next"] [orac_config_envs_subspt_def; OPTREL_THM] THEN
    USE_THEN "s_inc" (fun th -> USE_THEN "esi" (fun th2 ->
      ACCEPT_TAC (CONJUNCT2 (MATCH_MP inc_compile_prog_env_submap (CONJ th th2)))));
    (* 19 *) SIMP_NOASM[add_env_generation_def];
    (* 20 *) SIMP_NOASM[add_env_generation_def]]);;

let FLATP2AUX_next_cfg_generation = prove
 (`!interp f s.
     src_orac_next_cfg (interp:(v->(source_to_flat_config#C)option)option)
       (SOME (EvalOracle (eval_oracle_state_generation_fupd f s))) =
     src_orac_next_cfg interp (SOME (EvalOracle s))`,
  REWRITE_TAC[src_orac_next_cfg_def] THEN CASE_REWRITE_TAC[] THEN SIMP_NOASM[]);;

let FLATP2AUX_ALL_DISJOINT_end = prove
 (`!a f f' b o' d.
     ALL_DISJOINT [a; f; b UNION o'; d:A->bool] /\ DISJOINT b o' /\ f' SUBSET f
     ==> ALL_DISJOINT [b; f'; o'; d]`,
  REWRITE_TAC[ALL_DISJOINT_CONS] THEN SET_TAC[]);;

let FLATP2AUX_ALL_DISJOINT_02 = prove
 (`!a b c d:A->bool. ALL_DISJOINT [a; b; c; d] ==> DISJOINT a c`,
  REWRITE_TAC[ALL_DISJOINT_CONS] THEN SET_TAC[]);;

let FLATP2AUX_invs_generation = prove
 (`!interp g genv f s fc.
     (src_orac_step_invs (interp:(v->(source_to_flat_config#C)option)option) g
        (SOME (EvalOracle (eval_oracle_state_generation_fupd f s))) <=>
      src_orac_step_invs interp g (SOME (EvalOracle s))) /\
     (src_orac_env_invs interp genv
        (SOME (EvalOracle (eval_oracle_state_generation_fupd f s))) <=>
      src_orac_env_invs interp genv (SOME (EvalOracle s))) /\
     (orac_rel interp g (SOME (EvalOracle (eval_oracle_state_generation_fupd f s))) fc <=>
      orac_rel interp g (SOME (EvalOracle s)) fc)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[src_orac_step_invs_def; src_orac_env_invs_def; orac_rel_def;
              FLATP2AUX_next_cfg_generation; orac_rel_inner_def] THEN
  CASE_REWRITE_TAC[] THEN SIMP_NOASM[]);;

(* HOL4 line 3409 *)
let invariant_end_eval = prove
 (CASE_TERM `!interp g gen' genv x end_idx1 idx end_idx other st st' gen prev_genv prev_st prev_st' begin_eval_state.
     invariant (interp:(v->(source_to_flat_config#C)option)option) g gen' genv
     (x, end_idx1, idx_block idx end_idx UNION other) (st:(FFI)state)
     (st':(C,FFI)flat_state) /\
   invariant interp g gen prev_genv (idx, end_idx, other) (prev_st:(FFI)state)
     (prev_st':(C,FFI)flat_state) /\
   orac_forward_rel interp begin_eval_state (state_eval_state st) /\
   idx_prev end_idx end_idx1 /\
   orac_config_envs_subspt interp (state_eval_state prev_st) begin_eval_state /\
   (match state_eval_state prev_st with
      SOME (EvalOracle s) ->
        ?s'. begin_eval_state = SOME (EvalOracle s') /\
             eval_oracle_state_envs s' = eval_oracle_state_envs (add_env_generation s) /\
             eval_oracle_state_generation s' =
               eval_oracle_state_generation (add_env_generation s)
    | _ -> F)
   ==> invariant interp g gen genv (idx, end_idx, other)
         (state_eval_state_fupd
            (K (reset_env_generation (state_eval_state prev_st) (state_eval_state st))) st)
         st' /\
       orac_forward_rel interp (state_eval_state prev_st)
         (reset_env_generation (state_eval_state prev_st) (state_eval_state st)) /\
       (env_gen_rel gen (state_eval_state prev_st)
        ==> env_gen_rel gen
              (reset_env_generation (state_eval_state prev_st) (state_eval_state st)))`,
REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["I1"; "I2"; "fwd"; "prev"; "sub"; "cs"]) THEN
  FLATP2AUX_INV_TAC_P "I1" "a_" THEN FLATP2AUX_INV_TAC_P "I2" "b_" THEN
  SUBGOAL_THEN `?s0. state_eval_state (prev_st:(FFI)state) = SOME (EvalOracle s0)`
    STRIP_ASSUME_TAC THENL
   [USE_THEN "cs" MP_TAC THEN CASES_ON `state_eval_state (prev_st:(FFI)state)` THEN
    CASE_REWRITE_TAC[] THEN CASES_ON `a:eval_state` THEN CASE_REWRITE_TAC[] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
    `state_eval_state (prev_st:(FFI)state) = SOME (EvalOracle s0)`]) THEN
  REWRITE_TAC[ASSUME `state_eval_state (prev_st:(FFI)state) = SOME (EvalOracle s0)`] THEN
  REMOVE_THEN "cs" (MP_TAC o CASE_REWRITE_RULE[]) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:eval_oracle_state` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "s1envs") (LABEL_TAC "s1gen")))) THEN
  USE_THEN "fwd" (MP_TAC o CONJUNCT2 o REWRITE_RULE[orac_forward_rel_def]) THEN
  REWRITE_TAC[eval_state_call_rel_def] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:eval_oracle_state` (CONJUNCTS_THEN2 (LABEL_TAC "s2eq")
    (FLATP2AUX_LABEL_CONJS ["s2gen"; "s2len"; "s2el"]))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
    `state_eval_state (st:(FFI)state) = SOME (EvalOracle s2)`]) THEN
  REWRITE_TAC[ASSUME `state_eval_state (st:(FFI)state) = SOME (EvalOracle s2)`] THEN
  REWRITE_TAC[reset_env_generation_def] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?dec. (interp:(v->(source_to_flat_config#C)option)option) = SOME dec`
    (X_CHOOSE_THEN `dec:v->(source_to_flat_config#C)option` SUBST_ALL_TAC) THENL
   [USE_THEN "b_src_orac" (MP_TAC o MATCH_MP step_1 o CONJUNCT1 o
                           REWRITE_RULE[src_orac_invs_def]) THEN MESON_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[add_env_generation_def; eval_oracle_state_INFO.ri_accfupds;
                              K_THM]) THEN
  USE_THEN "b_src_orac" (LABEL_TAC "b_gen" o CONJUNCT2 o CONJUNCT2 o
                         REWRITE_RULE[src_orac_invs_def; src_orac_gen_inv_def]) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  SUBGOAL_THEN `eval_oracle_state_generation s0 < LENGTH (eval_oracle_state_envs s2) /\
                !i. i <= eval_oracle_state_generation s0
                    ==> EL i (eval_oracle_state_envs s2) = EL i (eval_oracle_state_envs s0)`
    (CONJUNCTS_THEN2 (LABEL_TAC "g02") (LABEL_TAC "el02")) THENL
   [CONJ_TAC THENL
     [USE_THEN "s2len" MP_TAC THEN FLATP2AUX_LREWRITE_TAC ["s1envs"] [LENGTH_APPEND; LENGTH] THEN
      USE_THEN "b_gen" MP_TAC THEN ARITH_TAC;
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `i < LENGTH (eval_oracle_state_envs s0)` ASSUME_TAC THENL
       [USE_THEN "b_gen" MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "s2el" (MP_TAC o SPEC `i:num`) THEN
      FLATP2AUX_LREWRITE_TAC ["s1envs"; "s1gen"] [EL_APPEND] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* the invariant *)
    REWRITE_TAC[invariant_def; src_orac_invs_def] THEN
    SIMP_NOASM[FLATP2AUX_invs_generation; FLATP2AUX_next_cfg_generation] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "a_c_ok" ACCEPT_TAC;
      USE_THEN "a_tys_ok" ACCEPT_TAC;
      USE_THEN "a_s_rel" MP_TAC THEN REWRITE_TAC[source_to_flatProof_s_rel_cases] THEN
      SIMP_NOASM[];
      USE_THEN "a_idx_range" MP_TAC THEN
      REWRITE_TAC[idx_range_rel_def; FLATP2AUX_next_cfg_generation; PAIR_EQ] THEN
      DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`x':next_indices`; `e1':next_indices`;
        `fin_idx:next_indices`; `ob:num#idx_types->bool`]
        (FLATP2AUX_LABEL_CONJS ["ra_eq"; "ra_fin"; "ra_prev"; "ra_disj"; "ra_ts"; "ra_en"])) THEN
      REMOVE_THEN "ra_eq" (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM)
        (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM))) THEN
      MAP_EVERY EXISTS_TAC [`idx:next_indices`; `end_idx:next_indices`;
        `fin_idx:next_indices`; `other:num#idx_types->bool`] THEN
      FLATP2AUX_LREWRITE_TAC ["ra_fin"; "ra_ts"; "ra_en"] [] THEN CONJ_TAC THENL
       [MATCH_MP_TAC idx_prev_trans THEN EXISTS_TAC `end_idx1:next_indices` THEN
        FLATP2AUX_LREWRITE_TAC ["prev"; "ra_prev"] [];
        MATCH_MP_TAC FLATP2AUX_ALL_DISJOINT_end THEN
        MAP_EVERY EXISTS_TAC [`idx_block x end_idx1`; `idx_final_block fin_idx`] THEN
        FLATP2AUX_LREWRITE_TAC ["ra_disj"] [SUBSET_REFL] THEN
        USE_THEN "b_idx_range" (MP_TAC o REWRITE_RULE[idx_range_rel_def; PAIR_EQ]) THEN
        DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`i1:next_indices`; `i2:next_indices`;
          `f2:next_indices`; `o2:num#idx_types->bool`]
          (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 SUBST_ALL_TAC
            (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC))
          (MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2))) THEN
        MATCH_ACCEPT_TAC FLATP2AUX_ALL_DISJOINT_02];
      USE_THEN "a_src_orac" (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[src_orac_invs_def]);
      USE_THEN "a_src_orac" (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o
                             REWRITE_RULE[src_orac_invs_def]);
      REWRITE_TAC[src_orac_gen_inv_def] THEN CASE_REWRITE_TAC[] THEN SIMP_NOASM[] THEN
      FLATP2AUX_LREWRITE_TAC ["g02"] [];
      USE_THEN "a_orac_rel" ACCEPT_TAC;
      USE_THEN "a_globals" ACCEPT_TAC;
      USE_THEN "a_eval_ref" ACCEPT_TAC;
      USE_THEN "b_env_gen_inv" ACCEPT_TAC;
      USE_THEN "a_fin_idx" MP_TAC THEN REWRITE_TAC[fin_idx_match_def] THEN
      CASES_ON `src_orac_next_cfg (SOME (dec:v->(source_to_flat_config#C)option))
                  (SOME (EvalOracle s2))` THEN
      CASE_REWRITE_TAC[] THEN USE_THEN "prev" MP_TAC THEN REWRITE_TAC[idx_prev_def] THEN
      ARITH_TAC];
    (* forward rel *)
    REWRITE_TAC[orac_forward_rel_def] THEN CONJ_TAC THENL
     [REWRITE_TAC[orac_config_envs_subspt_def; FLATP2AUX_next_cfg_generation] THEN
      REWRITE_TAC[GSYM orac_config_envs_subspt_def] THEN
      MATCH_MP_TAC orac_config_envs_subspt_trans THEN
      EXISTS_TAC `SOME (EvalOracle s1)` THEN
      FLATP2AUX_LREWRITE_TAC ["sub"] [] THEN
      USE_THEN "fwd" (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[orac_forward_rel_def]);
      REWRITE_TAC[eval_state_call_rel_def] THEN CASE_REWRITE_TAC[] THEN SIMP_NOASM[] THEN
      CONJ_TAC THENL
       [USE_THEN "s2len" MP_TAC THEN FLATP2AUX_LREWRITE_TAC ["s1envs"] [LENGTH_APPEND; LENGTH] THEN
        ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "el02" MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    (* env_gen_rel *)
    REWRITE_TAC[env_gen_rel_def] THEN CASE_REWRITE_TAC[] THEN SIMP_NOASM[] THEN
    STRIP_TAC THEN FLATP2AUX_LREWRITE_TAC ["g02"] [] THEN
    USE_THEN "el02" (fun th -> REWRITE_TAC[REWRITE_RULE[LE_REFL]
      (SPEC `eval_oracle_state_generation s0` th)])]);;

(* HOL4 line 3490 *)
let alloc_tags1_imp = prove
 (`!ctors ns spt tag_list.
     alloc_tags1 ctors = (ns, spt, tag_list) /\ ALL_DISTINCT (MAP FST ctors)
     ==> ?cn_tags.
           ns = alist_to_ns (MAP (\(cn, tag, arity). (cn, tag)) cn_tags) /\
           set_of_list (MAP SND cn_tags) =
             {(tag, arity) | ?max. lookup arity spt = SOME max /\ tag < max} /\
           tag_list = MAP SND cn_tags /\
           ALL_DISTINCT tag_list /\
           ALL2 (\(cn, ts) (cn', _, arity). cn = cn' /\ arity = LENGTH ts) ctors cn_tags /\
           MAP FST ctors = MAP FST cn_tags`,
  MATCH_MP_TAC alloc_tags1_ind THEN CONJ_TAC THENL
   [REWRITE_TAC[alloc_tags1_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
    EXISTS_TAC `[]:(mlstring#num#num)list` THEN
    REWRITE_TAC[MAP; ALL2; ALL_DISTINCT; set_of_list; alist_to_ns_def; nsEmpty_def] THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    SIMP_NOASM[lookup_def];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`cn:mlstring`; `ts:ast_t list`; `ctors:(mlstring#ast_t list)list`] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`ns:(modN,conN,num)namespace`; `spt:num spt`;
    `tag_list:(num#num)list`] THEN
  REWRITE_TAC[alloc_tags1_def] THEN
  MP_TAC(ISPEC `alloc_tags1 ctors` (prove(`!x:A#B#C. ?a b c. x = (a,b,c)`,
    REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[]))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ns0:(modN,conN,num)namespace` (X_CHOOSE_THEN `cids:num spt`
    (X_CHOOSE_THEN `tl0:(num#num)list` (LABEL_TAC "at")))) THEN
  FLATP2AUX_LREWRITE_TAC ["at"] [] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ns0:(modN,conN,num)namespace`; `cids:num spt`;
    `tl0:(num#num)list`]) THEN
  FLATP2AUX_LREWRITE_TAC ["at"] [] THEN
  REWRITE_TAC[MAP; ALL_DISTINCT] THEN DISCH_THEN(fun ih -> DISCH_THEN(fun h ->
    MP_TAC(MATCH_MP ih (CONJUNCT2 (CONJUNCT2 h))) THEN LABEL_TAC "h" h)) THEN
  DISCH_THEN(X_CHOOSE_THEN `cn_tags:(mlstring#num#num)list`
    (FLATP2AUX_LABEL_CONJS ["ns0"; "set0"; "tl0"; "dist0"; "rel0"; "fst0"])) THEN
  REMOVE_THEN "h" (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "nmem" o CONJUNCT1)) THEN
  REWRITE_TAC[lookup_inc_def] THEN
  CASES_ON `lookup (LENGTH (ts:ast_t list)) (cids:num spt)` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM)
    (SUBST_ALL_TAC o SYM))) THENL
   [EXISTS_TAC `CONS (cn:mlstring,0,LENGTH (ts:ast_t list)) cn_tags`;
    EXISTS_TAC `CONS (cn:mlstring,a:num,LENGTH (ts:ast_t list)) cn_tags`] THEN
  FLATP2AUX_LREWRITE_TAC ["ns0"; "tl0"; "fst0"; "rel0"]
    [MAP; alist_to_ns_def; nsBind_def; set_of_list; ALL2; ALL_DISTINCT] THEN
  SIMP_NOASM[] THEN
  FLATP2AUX_LREWRITE_TAC ["set0"] [] THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_INSERT; IN_ELIM_THM; PAIR_EQ;
              lookup_insert] THEN
  SIMP_NOASM[] THEN
  REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN FLATP2AUX_LREWRITE_TAC ["set0"] [IN_ELIM_THM; PAIR_EQ] THEN
  USE_THEN "dist0" MP_TAC THEN FLATP2AUX_LREWRITE_TAC ["tl0"] [IN_SET_OF_LIST] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN SIMP_NOASM[] THEN
  (CONJ_TAC THENL
   [REPEAT GEN_TAC THEN ASM_CASES_TAC `p2 = LENGTH (ts:ast_t list)` THEN
    ASM_REWRITE_TAC[] THEN SIMP_NOASM[injectivity "option"; distinctness "option"] THEN
    ARITH_TAC;
    ASM_REWRITE_TAC[] THEN SIMP_NOASM[injectivity "option"; distinctness "option"]]));;

(* HOL4 line 3520 *)
let source_to_flatProof_ALOOKUP_MAP_3 = prove
 (`!x xs f.
     (!x. MEM x xs ==> FST ((f:A#B->A#C) x) = FST x)
   ==> ALOOKUP (MAP f xs) x = OPTION_MAP (\y. SND (f (x, y))) (ALOOKUP xs x)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ALOOKUP_THM; MEM; OPTION_MAP_DEF] THEN
  SIMP_NOASM[DISJ_IMP_THM; FORALL_AND_THM] THEN
  X_GEN_TAC `f:A#B->A#C` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `h:A#B` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:B` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `(f:A#B->A#C) (a,b)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a':A` (X_CHOOSE_THEN `c:C` (LABEL_TAC "fab"))) THEN
  SUBGOAL_THEN `a':A = a` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      not (is_forall (concl th)) && can (find_term ((=) `FST:A#B->A`)) (concl th))) THEN
    FLATP2AUX_LREWRITE_TAC ["fab"] [FST];
    ALL_TAC] THEN
  FLATP2AUX_LREWRITE_TAC ["fab"] [ALOOKUP_THM] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `a:A = x`)) THEN
    FLATP2AUX_LREWRITE_TAC ["fab"] [OPTION_MAP_DEF; SND];
    ASM_MESON_TAC[]]);;

let FLATP2AUX_s_rel_weak = prove
 (`!genv genv' (s:(FFI)state) (s1:(C,FFI)flat_state).
     source_to_flatProof_s_rel genv s s1 /\
     global_env_c genv SUBMAP global_env_c genv' /\
     global_env_tys genv SUBMAP global_env_tys genv' /\
     subglobals (global_env_v genv) (global_env_v genv')
     ==> source_to_flatProof_s_rel genv' s s1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[source_to_flatProof_s_rel_cases] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LIST_REL_sv_rel_weak THEN EXISTS_TAC `genv:global_env` THEN
  ASM_REWRITE_TAC[]);;

let FLATP2AUX_invariant_genv_ext = prove
 (`!interp g gen genv genv' idx idx' end_idx os (st:(FFI)state) st1 (s_i1:(C,FFI)flat_state).
     invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv
       (idx, end_idx, os) st s_i1 /\
     genv_c_ok (global_env_c genv') /\
     genv_c_tys_ok (global_env_c genv') (global_env_tys genv') /\
     global_env_c genv SUBMAP global_env_c genv' /\
     global_env_tys genv SUBMAP global_env_tys genv' /\
     global_env_v genv' = global_env_v genv /\
     state_refs st1 = state_refs st /\ state_clock st1 = state_clock st /\
     state_ffi st1 = state_ffi st /\ state_eval_state st1 = state_eval_state st /\
     idx_range_rel interp genv' (state_next_type_stamp st1) (state_next_exn_stamp st1)
       (state_eval_state st) (idx', end_idx, os)
     ==> invariant interp g gen genv' (idx', end_idx, os) st1 s_i1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inv")
    (FLATP2AUX_LABEL_CONJS ["cok"; "tok"; "sc"; "sy"; "sv"; "rf"; "cl"; "ff"; "es"; "ir"])) THEN
  FLATP2AUX_INV_TAC "inv" THEN
  REWRITE_TAC[invariant_def] THEN
  FLATP2AUX_LREWRITE_TAC ["cok"; "tok"; "es"; "ir"; "orac_rel"; "eval_ref"; "env_gen_inv"] [] THEN
  USE_THEN "sv" (fun th -> REWRITE_TAC[th]) THEN
  FLATP2AUX_LREWRITE_TAC ["globals"; "fin_idx"] [] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FLATP2AUX_s_rel_weak THEN EXISTS_TAC `genv:global_env` THEN
    FLATP2AUX_LREWRITE_TAC ["sc"; "sy"; "sv"] [subglobals_refl] THEN
    USE_THEN "s_rel" MP_TAC THEN REWRITE_TAC[source_to_flatProof_s_rel_cases] THEN
    FLATP2AUX_LREWRITE_TAC ["rf"; "cl"; "ff"] [];
    MATCH_MP_TAC src_orac_invs_weak THEN EXISTS_TAC `genv:global_env` THEN
    FLATP2AUX_LREWRITE_TAC ["src_orac"; "sc"; "sy"; "sv"] [subglobals_refl]]);;

let FLATP2AUX_idx_block_type = prove
 (`!idx end_idx.
     idx_block (next_indices_tidx_fupd (K (next_indices_tidx idx + 1)) idx) end_idx =
     idx_block idx end_idx DIFF {(next_indices_tidx idx, Idx_Type)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[idx_block_def; EXTENSION; IN_DIFF; IN_UNION; IN_SING;
    IN_ELIM_THM; FORALL_PAIR_THM; PAIR_EQ] THEN
  SIMP_NOASM[] THEN REPEAT GEN_TAC THEN
  CASES_ON `p2:idx_types` THEN REWRITE_TAC[distinctness "idx_types"] THEN ARITH_TAC);;

let FLATP2AUX_FRANGE_FUNION_IMP = prove
 (`!(a:(K,V)fmap) b x. x IN FRANGE (FUNION a b) ==> x IN FRANGE a \/ x IN FRANGE b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRANGE_FLOOKUP; FLOOKUP_FUNION] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:K` MP_TAC) THEN
  MP_TAC(ISPEC `FLOOKUP (a:(K,V)fmap) k` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th])
    (X_CHOOSE_THEN `y:V` (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "option"] THEN ASM_MESON_TAC[]);;

let FLATP2AUX_genv_alloc_type = prove
 (`!genv t c_ext tys_ext.
     FDOM tys_ext = {t} /\
     (!k. k IN FDOM c_ext ==> ?x a. k = ((x, SOME t), a))
     ==> genv_allocated_idxs (global_env_REC (global_env_v genv)
            (FUNION (global_env_c genv) c_ext) (FUNION (global_env_tys genv) tys_ext)) =
         genv_allocated_idxs genv UNION {(t, Idx_Type)}`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "td") (LABEL_TAC "cd")) THEN
  SUBGOAL_THEN `(!cn a p. ((cn, SOME p), a) IN FDOM (c_ext:((ctor_id#type_id)#num,stamp)fmap)
                          ==> p = t) /\
                (!x a. ~(((x, NONE), a) IN FDOM (c_ext:((ctor_id#type_id)#num,stamp)fmap)))`
    (CONJUNCTS_THEN2 (LABEL_TAC "c1") (LABEL_TAC "c2")) THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_THEN(fun th -> USE_THEN "cd" (MP_TAC o C MATCH_MP th)) THEN
    REWRITE_TAC[PAIR_EQ; injectivity "option"; distinctness "option"] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[genv_allocated_idxs_def; EXTENSION; IN_UNION; IN_SING; IN_ELIM_THM;
    FORALL_PAIR_THM; PAIR_EQ] THEN
  SIMP_NOASM[FDOM_FUNION; IN_UNION; IN_SING] THEN
  FLATP2AUX_LREWRITE_TAC ["td"; "c2"] [IN_SING] THEN
  REPEAT GEN_TAC THEN CASES_ON `p2:idx_types` THEN REWRITE_TAC[distinctness "idx_types"] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(DISJ1_TAC THEN DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`cn:ctor_id`; `a:num`] THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(DISJ2_TAC THEN USE_THEN "c1" (MATCH_MP_TAC) THEN
      MAP_EVERY EXISTS_TAC [`cn:ctor_id`; `a:num`] THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(DISJ1_TAC THEN DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`cn:ctor_id`; `a:num`] THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC));;

let FLATP2AUX_idx_range_type = prove
 (`!interp genv nts nes ev idx end_idx os c_ext tys_ext.
     idx_range_rel (interp:(v->(source_to_flat_config#C)option)option) genv nts nes ev
       (idx, end_idx, os) /\
     next_indices_tidx idx < next_indices_tidx end_idx /\
     FDOM tys_ext = {next_indices_tidx idx} /\
     (!k. k IN FDOM c_ext ==> ?x a. k = ((x, SOME (next_indices_tidx idx)), a)) /\
     (!s. s IN FRANGE c_ext ==> ?cn. s = TypeStamp cn nts)
     ==> idx_range_rel interp
           (global_env_REC (global_env_v genv) (FUNION (global_env_c genv) c_ext)
              (FUNION (global_env_tys genv) tys_ext))
           (nts + 1) nes ev
           (next_indices_tidx_fupd (K (next_indices_tidx idx + 1)) idx, end_idx, os)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[idx_range_rel_def; PAIR_EQ])
    (FLATP2AUX_LABEL_CONJS ["lt"; "td"; "cd"; "rg"])) THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`i0:next_indices`; `e0:next_indices`; `fin:next_indices`;
       `ob:num#idx_types->bool`]
       (FLATP2AUX_LABEL_CONJS ["eq"; "fin"; "prev"; "disj"; "ts"; "en"])) THEN
  REMOVE_THEN "eq" (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM)
         (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM))) THEN
  REWRITE_TAC[idx_range_rel_def; PAIR_EQ] THEN
  MAP_EVERY EXISTS_TAC [`next_indices_tidx_fupd (K (next_indices_tidx idx + 1)) idx`;
    `end_idx:next_indices`; `fin:next_indices`; `os:num#idx_types->bool`] THEN
  SUBGOAL_THEN `genv_allocated_idxs (global_env_REC (global_env_v genv)
            (FUNION (global_env_c genv) c_ext) (FUNION (global_env_tys genv) tys_ext)) =
         genv_allocated_idxs genv UNION {(next_indices_tidx idx, Idx_Type)}` SUBST1_TAC THENL
   [MATCH_MP_TAC FLATP2AUX_genv_alloc_type THEN FLATP2AUX_LREWRITE_TAC ["td"; "cd"] [];
    ALL_TAC] THEN
  FLATP2AUX_LREWRITE_TAC ["fin"; "prev"] [FLATP2AUX_idx_block_type] THEN
  REWRITE_TAC[global_env_INFO.ri_accessors] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ALL_DISJOINT_MOVE THEN
    MAP_EVERY EXISTS_TAC [`0`; `3`; `{(next_indices_tidx idx, Idx_Type)}`;
      `[idx_block idx end_idx; idx_final_block fin; os; genv_allocated_idxs genv]`] THEN
    FLATP2AUX_LREWRITE_TAC ["disj"] [LENGTH] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN
    REPEAT(CHANGED_TAC(REWRITE_TAC[LUPDATE_compute] THEN CONV_TAC NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[SING_SUBSET; idx_block_def; IN_UNION; IN_ELIM_THM; PAIR_EQ;
                distinctness "idx_types"] THEN
    USE_THEN "lt" MP_TAC THEN MESON_TAC[LE_REFL];
    MAP_EVERY X_GEN_TAC [`cn:mlstring`; `t:num`] THEN DISCH_THEN(LABEL_TAC "ge") THEN
    DISCH_THEN(DISJ_CASES_THEN2 (LABEL_TAC "inr") (LABEL_TAC "inx") o
               MATCH_MP FLATP2AUX_FRANGE_FUNION_IMP) THENL
     [USE_THEN "ts" (MP_TAC o SPECL [`cn:mlstring`; `t:num`]) THEN
      FLATP2AUX_LREWRITE_TAC ["inr"] [] THEN USE_THEN "ge" MP_TAC THEN ARITH_TAC;
      USE_THEN "inx" (fun th -> USE_THEN "rg" (MP_TAC o C MATCH_MP th)) THEN
      REWRITE_TAC[injectivity "stamp"] THEN USE_THEN "ge" MP_TAC THEN ARITH_TAC];
    X_GEN_TAC `cn:num` THEN DISCH_THEN(LABEL_TAC "ge") THEN
    DISCH_THEN(DISJ_CASES_THEN2 (LABEL_TAC "inr") (LABEL_TAC "inx") o
               MATCH_MP FLATP2AUX_FRANGE_FUNION_IMP) THENL
     [USE_THEN "en" (MP_TAC o SPEC `cn:num`) THEN FLATP2AUX_LREWRITE_TAC ["inr"; "ge"] [];
      USE_THEN "inx" (fun th -> USE_THEN "rg" (MP_TAC o C MATCH_MP th)) THEN
      REWRITE_TAC[distinctness "stamp"]]]);;

let FLATP2AUX_FLOOKUP_type_ext = prove
 (`!(t:num) nts (cn_tags:(mlstring#num#num)list) k s.
     FLOOKUP (alist_to_fmap (MAP (\(cn,tag,arity). (((tag, SOME t), arity), TypeStamp cn nts))
                               cn_tags)) k = SOME s
     ==> ?cn tag arity. MEM (cn, tag, arity) cn_tags /\ k = ((tag, SOME t), arity) /\
                        s = TypeStamp cn nts`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALOOKUP_EQ_FLOOKUP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

let FLATP2AUX_MEM_ALL_DISTINCT_FST = prove
 (`!(l:(A#B)list) k v v'.
     ALL_DISTINCT (MAP FST l) /\ MEM (k, v) l /\ MEM (k, v') l ==> v = v'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(A#B)list`; `k:A`; `v:B`] ALOOKUP_ALL_DISTINCT_MEM) THEN
  MP_TAC(ISPECL [`l:(A#B)list`; `k:A`; `v':B`] ALOOKUP_ALL_DISTINCT_MEM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[injectivity "option"] THEN MESON_TAC[]);;

let FLATP2AUX_genv_c_ok_type = prove
 (`!c (t:num) nts (cn_tags:(mlstring#num#num)list).
     genv_c_ok c /\ ALL_DISTINCT (MAP FST cn_tags) /\
     (!x a. ~(((x, SOME t), a) IN FDOM c)) /\
     (!cn. ~(TypeStamp cn nts IN FRANGE c))
     ==> genv_c_ok (FUNION c (alist_to_fmap
           (MAP (\(cn,tag,arity). (((tag, SOME t), arity), TypeStamp cn nts)) cn_tags)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["cok"; "dist"; "kf"; "sf"]) THEN
  MATCH_MP_TAC genv_c_ok_extend THEN FLATP2AUX_LREWRITE_TAC ["cok"] [] THEN
  MAP_EVERY X_GEN_TAC [`cn:ctor_id#type_id`; `arity:num`; `stamp:stamp`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FLATP2AUX_FLOOKUP_type_ext) THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`c0:mlstring`; `tag:num`; `ar:num`]
    (FLATP2AUX_LABEL_CONJS ["mem"; "keq"; "seq"])) THEN
  USE_THEN "keq" (MP_TAC o REWRITE_RULE[PAIR_EQ]) THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN REMOVE_THEN "seq" SUBST_ALL_TAC THEN
  REWRITE_TAC[same_type_def; SND; distinctness "option"] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`cn':ctor_id#type_id`; `arity':num`; `stamp':stamp`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP FLATP2AUX_FLOOKUP_type_ext) THEN
    DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`c1:mlstring`; `tag':num`; `ar':num`]
      (FLATP2AUX_LABEL_CONJS ["mem'"; "keq'"; "seq'"])) THEN
    USE_THEN "keq'" (MP_TAC o REWRITE_RULE[PAIR_EQ]) THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN REMOVE_THEN "seq'" SUBST_ALL_TAC THEN
    REWRITE_TAC[same_type_def; flat_ctor_same_type_def; injectivity "stamp"; PAIR_EQ] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    MP_TAC(ISPECL [`cn_tags:(mlstring#num#num)list`; `c0:mlstring`; `(tag:num),(ar:num)`;
                   `(tag':num),(ar':num)`] FLATP2AUX_MEM_ALL_DISTINCT_FST) THEN
    FLATP2AUX_LREWRITE_TAC ["dist"; "mem"; "mem'"] [PAIR_EQ];
    MAP_EVERY X_GEN_TAC [`cn':ctor_id#type_id`; `arity':num`; `stamp':stamp`] THEN
    DISCH_THEN(LABEL_TAC "fl") THEN
    SUBGOAL_THEN `stamp' IN FRANGE (c:((ctor_id#type_id)#num,stamp)fmap)` (LABEL_TAC "inr") THENL
     [REWRITE_TAC[FRANGE_FLOOKUP] THEN EXISTS_TAC `(cn':ctor_id#type_id),(arity':num)` THEN
      FLATP2AUX_LREWRITE_TAC ["fl"] [];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [DISCH_THEN(SUBST_ALL_TAC o SYM) THEN USE_THEN "sf" (MP_TAC o SPEC `c0:mlstring`) THEN
      FLATP2AUX_LREWRITE_TAC ["inr"] [];
      MP_TAC(ISPEC `cn':ctor_id#type_id` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `x:ctor_id` (X_CHOOSE_THEN `y:type_id` SUBST_ALL_TAC)) THEN
      REWRITE_TAC[SND] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      USE_THEN "kf" (MP_TAC o SPECL [`x:ctor_id`; `arity':num`]) THEN
      REWRITE_TAC[FDOM_FLOOKUP] THEN FLATP2AUX_LREWRITE_TAC ["fl"] [distinctness "option"];
      REWRITE_TAC[injectivity "stamp"] THEN REPEAT GEN_TAC THEN
      DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      DISCH_THEN SUBST_ALL_TAC THEN USE_THEN "sf" (MP_TAC o SPEC `s':mlstring`) THEN
      FLATP2AUX_LREWRITE_TAC ["inr"] []]]);;

let FLATP2AUX_FDOM_type_ext = prove
 (`!(t:num) nts (cn_tags:(mlstring#num#num)list) k.
     k IN FDOM (alist_to_fmap (MAP (\(cn,tag,arity). (((tag, SOME t), arity), TypeStamp cn nts))
                                 cn_tags))
     ==> ?cn tag arity. MEM (cn, tag, arity) cn_tags /\ k = ((tag, SOME t), arity)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FDOM_FLOOKUP] THEN
  MP_TAC(ISPEC `FLOOKUP (alist_to_fmap (MAP (\(cn,tag,arity). (((tag, SOME (t:num)), arity),
      TypeStamp cn nts)) (cn_tags:(mlstring#num#num)list))) k` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th])
    (X_CHOOSE_THEN `s:stamp` (fun th -> REWRITE_TAC[th; distinctness "option"] THEN
       MP_TAC(MATCH_MP FLATP2AUX_FLOOKUP_type_ext th)))) THEN
  MESON_TAC[]);;

let FLATP2AUX_genv_c_tys_ok_type = prove
 (`!c tys (t:num) nts (cn_tags:(mlstring#num#num)list).
     genv_c_tys_ok c tys /\ ~(t IN FDOM tys)
     ==> genv_c_tys_ok
           (FUNION c (alist_to_fmap
              (MAP (\(cn,tag,arity). (((tag, SOME t), arity), TypeStamp cn nts)) cn_tags)))
           (FUNION tys (alist_to_fmap [(t, MAP SND (REVERSE cn_tags))]))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC genv_c_tys_ok_extend THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[genv_c_tys_ok_def] THEN
    MAP_EVERY X_GEN_TAC [`cn:ctor_id`; `ty_id:num`; `arity:num`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP FLATP2AUX_FDOM_type_ext) THEN
    DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`c0:mlstring`; `tag:num`; `ar:num`]
      (CONJUNCTS_THEN2 (LABEL_TAC "mem") (MP_TAC o REWRITE_RULE[PAIR_EQ; injectivity "option"]))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN SUBST_ALL_TAC) SUBST_ALL_TAC) THEN
    EXISTS_TAC `MAP SND (REVERSE (cn_tags:(mlstring#num#num)list))` THEN
    REWRITE_TAC[alist_to_fmap_thm; FLOOKUP_UPDATE; FLOOKUP_EMPTY; MEM_MAP; MEM_REVERSE] THEN
    EXISTS_TAC `(c0:mlstring),(tag:num),(ar:num)` THEN FLATP2AUX_LREWRITE_TAC ["mem"] [SND];
    REWRITE_TAC[FDOM_alist_to_fmap; MAP; set_of_list; IN_DISJOINT; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[]]);;

let FLATP2AUX_MAP_FST_cn_tag = prove
 (`!(l:(mlstring#num#num)list). MAP FST (MAP (\(cn,tag,arity). (cn,tag)) l) = MAP FST l`,
  GEN_TAC THEN REWRITE_TAC[MAP_MAP_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]);;

let FLATP2AUX_nsLookup_alist_Short = prove
 (`!(l:(N#V)list) x. nsLookup (alist_to_ns l:(M,N,V)namespace) (Short x) = ALOOKUP l x`,
  REWRITE_TAC[alist_to_ns_def; nsLookup_def]);;

let FLATP2AUX_MAP_FST_kv = prove
 (CASE_TERM `!(f:V->W) (l:(K#V)list).
     MAP FST (MAP (\kv. match kv with (k,v) -> (k, f v)) l) = MAP FST l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  MP_TAC(ISPEC `h:K#V` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:K` (X_CHOOSE_THEN `b:V` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[FST]);;

let FLATP2AUX_global_env_inv_type = prove
 (`!genv (t:num) nts (ctors:(mlstring # ast_t list) list) (cn_tags:(mlstring#num#num)list).
     ALL2 (\(cn, ts) (cn', _, arity). cn = cn' /\ arity = LENGTH ts) (REVERSE ctors) cn_tags /\
     ALL_DISTINCT (MAP FST cn_tags) /\
     (!c0 tag ar. MEM (c0,tag,ar) cn_tags
                  ==> FLOOKUP (global_env_c genv) ((tag, SOME t), ar) = SOME (TypeStamp c0 nts)) /\
     FLOOKUP (global_env_tys genv) t = SOME (REVERSE (MAP SND cn_tags))
     ==> global_env_inv genv
           (source_to_flat_environment_REC
              (nsMap (\tag. (tag, SOME (t, REVERSE (MAP SND cn_tags))))
                 (alist_to_ns (MAP (\(cn,tag,arity). (cn,tag)) cn_tags))) nsEmpty) {}
           (sem_env_REC nsEmpty (alist_to_ns (REVERSE (build_constrs nts ctors))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(FLATP2AUX_LABEL_CONJS ["rel"; "dist"; "cf"; "tf"]) THEN
  REWRITE_TAC[v_rel_global_eqn] THEN
  SIMP_NOASM[nsLookup_nsEmpty; distinctness "option"] THEN
  MAP_EVERY X_GEN_TAC [`x:(modN,conN)id`; `arity:num`; `stamp:stamp`] THEN
  REWRITE_TAC[nsLookup_alist_to_ns_some] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:mlstring` (CONJUNCTS_THEN2 SUBST_ALL_TAC (LABEL_TAC "al"))) THEN
  USE_THEN "al" (MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
  REWRITE_TAC[MEM_REVERSE; build_constrs_def; MEM_MAP; EXISTS_PAIR_THM] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:mlstring` (X_CHOOSE_THEN `ts:ast_t list`
    (CONJUNCTS_THEN2 (LABEL_TAC "eqs") (LABEL_TAC "memc")))) THEN
  REMOVE_THEN "memc" (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
  MP_TAC(ISPECL [`REVERSE (ctors:(mlstring # ast_t list) list)`;
    `cn_tags:(mlstring#num#num)list`;
    `(\(cn, ts) (cn', _, arity). cn = cn' /\ arity = LENGTH ts):
       mlstring#ast_t list->mlstring#num#num->bool`;
    `(c1:mlstring),(ts:ast_t list)`] LIST_REL_MEM_IMP) THEN
  FLATP2AUX_LREWRITE_TAC ["rel"; "eqs"] [MEM_REVERSE] THEN
  REWRITE_TAC[EXISTS_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:mlstring` (X_CHOOSE_THEN `tag:num` (X_CHOOSE_THEN `ar:num`
    (CONJUNCTS_THEN2 (LABEL_TAC "memt") (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) SUBST_ALL_TAC))))) THEN
  MAP_EVERY EXISTS_TAC [`tag:num`;
    `SOME ((t:num), REVERSE (MAP SND (cn_tags:(mlstring#num#num)list)))`] THEN
  REWRITE_TAC[UNWIND_THM1; OPTION_MAP_DEF; injectivity "option"; PAIR_EQ] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN
    REWRITE_TAC[FLATP2AUX_MAP_FST_kv; FLATP2AUX_MAP_FST_cn_tag] THEN
    FLATP2AUX_LREWRITE_TAC ["dist"] [MEM_MAP; EXISTS_PAIR_THM] THEN
    MAP_EVERY EXISTS_TAC [`c1:mlstring`; `tag:num`] THEN CASE_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`c1:mlstring`; `tag:num`; `LENGTH (ts:ast_t list)`] THEN
    FLATP2AUX_LREWRITE_TAC ["memt"] [];
    CONJ_TAC THENL
     [USE_THEN "cf" MATCH_MP_TAC THEN FLATP2AUX_LREWRITE_TAC ["memt"] [];
      REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      FLATP2AUX_LREWRITE_TAC ["tf"] []]]);;

let FLATP2AUX_MAP_FST_build_constrs = prove
 (`!nts (ctors:(mlstring # ast_t list) list). MAP FST (build_constrs nts ctors) = MAP FST ctors`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; build_constrs_def] THEN
  MP_TAC(ISPEC `h:mlstring # ast_t list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:mlstring` (X_CHOOSE_THEN `b:ast_t list` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[build_constrs_def]) THEN
  ASM_REWRITE_TAC[FST]);;

let FLATP2AUX_env_domain_eq_type = prove
 (`!(data:type_group_id) nts (ctors:(mlstring # ast_t list) list) (cn_tags:(mlstring#num#num)list).
     MAP FST (REVERSE ctors) = MAP FST cn_tags
     ==> env_domain_eq
           (source_to_flat_environment_REC
              (nsMap (\tag. (tag, data))
                 (alist_to_ns (MAP (\(cn,tag,arity). (cn,tag)) cn_tags))) nsEmpty)
           (sem_env_REC (nsEmpty:(modN,varN,v)namespace)
              (alist_to_ns (REVERSE (build_constrs nts ctors))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[env_domain_eq_def; nsMap_alist_to_ns] THEN
  SIMP_NOASM[nsDom_alist_to_ns; nsDomMod_alist_to_ns] THEN
  REWRITE_TAC[GSYM MAP_MAP_o] THEN
  REWRITE_TAC[FLATP2AUX_MAP_FST_kv; FLATP2AUX_MAP_FST_cn_tag] THEN
  REWRITE_TAC[GSYM MAP_REVERSE; FLATP2AUX_MAP_FST_build_constrs] THEN
  REWRITE_TAC[MAP_REVERSE] THEN ASM_REWRITE_TAC[]);;

let FLATP2AUX_FLOOKUP_type_ext_MEM = prove
 (`!(t:num) nts (cn_tags:(mlstring#num#num)list) c0 tag ar.
     ALL_DISTINCT (MAP SND cn_tags) /\ MEM (c0, tag, ar) cn_tags
     ==> FLOOKUP (alist_to_fmap (MAP (\(cn,tag,arity). (((tag, SOME t), arity), TypeStamp cn nts))
                                  cn_tags)) ((tag, SOME t), ar) = SOME (TypeStamp c0 nts)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ALOOKUP_EQ_FLOOKUP] THEN
  MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN CONJ_TAC THENL
   [SUBGOAL_THEN `MAP FST (MAP (\(cn,tag,arity). (((tag, SOME (t:num)), arity), TypeStamp cn (nts:num)))
                    (cn_tags:(mlstring#num#num)list)) =
                  MAP (\(tag,arity). ((tag, SOME t), arity)) (MAP SND cn_tags)` SUBST1_TAC THENL
     [REWRITE_TAC[MAP_MAP_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM];
      ALL_TAC] THEN
    MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN ASM_REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN
    MESON_TAC[];
    REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN
    MAP_EVERY EXISTS_TAC [`c0:mlstring`; `tag:num`; `ar:num`] THEN ASM_REWRITE_TAC[]]);;

let FLATP2AUX_idx_range_type_fresh = prove
 (`!interp genv nts nes ev idx end_idx os.
     idx_range_rel (interp:(v->(source_to_flat_config#C)option)option) genv nts nes ev
       (idx, end_idx, os) /\
     next_indices_tidx idx < next_indices_tidx end_idx
     ==> (!x a. ~(((x, SOME (next_indices_tidx idx)), a) IN FDOM (global_env_c genv))) /\
         ~(next_indices_tidx idx IN FDOM (global_env_tys genv)) /\
         (!cn. ~(TypeStamp cn nts IN FRANGE (global_env_c genv)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[idx_range_rel_def; PAIR_EQ])
    (LABEL_TAC "lt")) THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`i0:next_indices`; `e0:next_indices`; `fin:next_indices`;
       `ob:num#idx_types->bool`]
       (FLATP2AUX_LABEL_CONJS ["eq"; "fin"; "prev"; "disj"; "ts"; "en"])) THEN
  REMOVE_THEN "eq" (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM)
         (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM))) THEN
  USE_THEN "disj" (MP_TAC o SPECL [`0`; `3`] o REWRITE_RULE[ALL_DISJOINT_DEF]) THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `(next_indices_tidx idx, Idx_Type)`) THEN
  REWRITE_TAC[idx_block_def; genv_allocated_idxs_def; IN_UNION; IN_ELIM_THM; PAIR_EQ;
              distinctness "idx_types"] THEN
  USE_THEN "lt" (fun th -> REWRITE_TAC[th; LE_REFL]) THEN
  DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN POP_ASSUM MP_TAC THEN USE_THEN "lt" MP_TAC THEN MESON_TAC[LE_REFL];
    POP_ASSUM MP_TAC THEN USE_THEN "lt" MP_TAC THEN MESON_TAC[LE_REFL];
    GEN_TAC THEN USE_THEN "ts" (MP_TAC o SPECL [`cn:mlstring`; `nts:num`]) THEN
    REWRITE_TAC[GE; LE_REFL]]);;

(* HOL4 line 3532 *)
let alloc_tags_invariant = prove
 (`!idx ctors ns cids interp g gen genv end_idx os st st' comp_map env.
     alloc_tags (next_indices_tidx idx) (ctors:(mlstring # ast_t list) list) = (ns, cids) /\
   invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv
     (idx, end_idx, os) (st:(FFI)state) (st':(C,FFI)flat_state) /\
   global_env_inv genv comp_map {} env /\
   ALL_DISTINCT (MAP FST ctors) /\
   next_indices_tidx idx + 1 <= next_indices_tidx end_idx
   ==> ?genv'.
         global_env_c genv SUBMAP global_env_c genv' /\
         global_env_tys genv SUBMAP global_env_tys genv' /\
         global_env_v genv' = global_env_v genv /\
         invariant interp g gen genv'
           (next_indices_tidx_fupd (K (next_indices_tidx idx + 1)) idx, end_idx, os)
           (state_next_type_stamp_fupd (K (state_next_type_stamp st + 1)) st) st' /\
         (let build_env = sem_env_REC nsEmpty
                            (alist_to_ns (REVERSE (build_constrs (state_next_type_stamp st)
                                                     ctors))) in
          global_env_inv genv' (source_to_flat_environment_REC ns nsEmpty) {} build_env /\
          env_domain_eq (source_to_flat_environment_REC ns nsEmpty) build_env)`,
(REPEAT GEN_TAC THEN DISCH_THEN(FLATP2AUX_LABEL_CONJS ["at"; "inv"; "gei"; "dist"; "tlt"]) THEN
  REMOVE_THEN "at" (MP_TAC o REWRITE_RULE[alloc_tags_def]) THEN
  MP_TAC(ISPEC `alloc_tags1 (REVERSE (ctors:(mlstring # ast_t list) list))`
    (prove(`!x:A#B#C. ?a b c. x = (a,b,c)`, REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[]))) THEN
  DISCH_THEN(X_CHOOSE_THEN `con_ns:(modN,conN,num)namespace` (X_CHOOSE_THEN `cid_spt:num spt`
    (X_CHOOSE_THEN `tag_list:(num#num)list` (LABEL_TAC "a1")))) THEN
  FLATP2AUX_LREWRITE_TAC ["a1"] [] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM))) THEN
  (SUBGOAL_THEN `ALL_DISTINCT (MAP FST (REVERSE (ctors:(mlstring # ast_t list) list)))`
    (LABEL_TAC "distr") THENL
   [REWRITE_TAC[GSYM MAP_REVERSE; ALL_DISTINCT_REVERSE] THEN FLATP2AUX_LREWRITE_TAC ["dist"] [];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP alloc_tags1_imp (CONJ (ASSUME `alloc_tags1 (REVERSE (ctors:(mlstring # ast_t list) list)) = con_ns,cid_spt,tag_list`)
     (ASSUME `ALL_DISTINCT (MAP FST (REVERSE (ctors:(mlstring # ast_t list) list)))`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `cn_tags:(mlstring#num#num)list`
    (FLATP2AUX_LABEL_CONJS ["ns0"; "set0"; "tl0"; "dist0"; "rel0"; "fst0"])) THEN
  REMOVE_THEN "ns0" SUBST_ALL_TAC THEN REMOVE_THEN "tl0" SUBST_ALL_TAC THEN
  FLATP2AUX_INV_TAC "inv") THEN
  (SUBGOAL_THEN `next_indices_tidx idx < next_indices_tidx end_idx` (LABEL_TAC "tlt'") THENL
   [USE_THEN "tlt" MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP FLATP2AUX_idx_range_type_fresh (CONJ
    (ASSUME `idx_range_rel (interp:(v->(source_to_flat_config#C)option)option) genv (state_next_type_stamp (st:(FFI)state))
               (state_next_exn_stamp st) (state_eval_state st) (idx,end_idx,os)`)
    (ASSUME `next_indices_tidx idx < next_indices_tidx end_idx`))) THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["kf"; "tf"; "sf"]) THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (cn_tags:(mlstring#num#num)list))` (LABEL_TAC "distc") THENL
   [USE_THEN "fst0" (SUBST1_TAC o SYM) THEN FLATP2AUX_LREWRITE_TAC ["distr"] []; ALL_TAC] THEN
  EXISTS_TAC `global_env_REC (global_env_v genv)
     (FUNION (global_env_c genv) (alist_to_fmap
        (MAP (\(cn,tag,arity). (((tag, SOME (next_indices_tidx idx)), arity),
                                TypeStamp cn (state_next_type_stamp (st:(FFI)state))))
           (cn_tags:(mlstring#num#num)list))))
     (FUNION (global_env_tys genv)
        (alist_to_fmap [(next_indices_tidx idx, MAP SND (REVERSE cn_tags))]))` THEN
  REWRITE_TAC[global_env_INFO.ri_accessors; SUBMAP_FUNION_ID] THEN
  REPEAT CONJ_TAC) THENL
  [(MATCH_MP_TAC FLATP2AUX_invariant_genv_ext THEN
  MAP_EVERY EXISTS_TAC [`genv:global_env`; `idx:next_indices`; `st:(FFI)state`] THEN
  REWRITE_TAC[global_env_INFO.ri_accessors; SUBMAP_FUNION_ID; state_INFO.ri_accfupds; K_THM] THEN
  FLATP2AUX_LREWRITE_TAC ["inv"] [] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FLATP2AUX_genv_c_ok_type THEN FLATP2AUX_LREWRITE_TAC ["c_ok"; "distc"; "kf"; "sf"] [];
    MATCH_MP_TAC FLATP2AUX_genv_c_tys_ok_type THEN FLATP2AUX_LREWRITE_TAC ["tys_ok"; "tf"] [];
    MATCH_MP_TAC FLATP2AUX_idx_range_type THEN
    FLATP2AUX_LREWRITE_TAC ["idx_range"; "tlt'"] [] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[FDOM_alist_to_fmap; MAP; set_of_list];
      GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP FLATP2AUX_FDOM_type_ext) THEN MESON_TAC[];
      GEN_TAC THEN REWRITE_TAC[FRANGE_FLOOKUP] THEN
      DISCH_THEN(X_CHOOSE_THEN `k:(ctor_id#type_id)#num`
        (MP_TAC o MATCH_MP FLATP2AUX_FLOOKUP_type_ext)) THEN MESON_TAC[]]]);
   (MATCH_MP_TAC FLATP2AUX_global_env_inv_type THEN REWRITE_TAC[global_env_INFO.ri_accessors] THEN
  FLATP2AUX_LREWRITE_TAC ["rel0"; "distc"] [] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`c0:mlstring`; `tag:num`; `ar:num`] THEN DISCH_TAC THEN
    REWRITE_TAC[FLOOKUP_FUNION] THEN
    USE_THEN "kf" (fun th -> REWRITE_TAC[REWRITE_RULE[GSYM flookup_thm]
      (SPECL [`tag:num`; `ar:num`] th)]) THEN
    CASE_REWRITE_TAC[] THEN MATCH_MP_TAC FLATP2AUX_FLOOKUP_type_ext_MEM THEN
    FLATP2AUX_LREWRITE_TAC ["dist0"] [] THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[FLOOKUP_FUNION] THEN
    USE_THEN "tf" (fun th -> REWRITE_TAC[REWRITE_RULE[GSYM flookup_thm] th]) THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[alist_to_fmap_thm; FLOOKUP_UPDATE; FLOOKUP_EMPTY; MAP_REVERSE]]);
   (MATCH_MP_TAC FLATP2AUX_env_domain_eq_type THEN FLATP2AUX_LREWRITE_TAC ["fst0"] [])]);;

(* HOL4 line 3672 *)
let nsAppend_foldl' = prove
 (`!l ns ns'.
     nsAppend (FOLDL (\ns (l,cids). nsAppend l ns) ns' (l:((A,B,C)namespace#D)list)) ns =
     FOLDL (\ns (l,cids). nsAppend l ns) (nsAppend ns' ns) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `h:(A,B,C)namespace#D` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:(A,B,C)namespace` (X_CHOOSE_THEN `b:D` SUBST1_TAC)) THEN
  SIMP_NOASM[nsAppend_assoc]);;

(* HOL4 line 3684 *)
let nsAppend_foldl = prove
 (`!l ns.
     FOLDL (\ns (l,cids). nsAppend l ns) ns (l:((A,B,C)namespace#D)list) =
     nsAppend (FOLDL (\ns (l,cids). nsAppend l ns) nsEmpty l) ns`,
  REWRITE_TAC[nsAppend_foldl'; nsAppend_nsEmpty]);;

(* HOL4 line 3693 *)
let build_tdefs_no_mod = prove
 (`!idx tdefs. nsDomMod (build_tdefs idx tdefs) = {[]}`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[build_tdefs_def; nsDomMod_alist_to_ns] THEN
  MP_TAC(ISPEC `h:(tvarN list # typeN # (conN # ast_t list) list)` (prove
   (`!x:A#B#C. ?a b c. x = (a,b,c)`, REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[]))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[build_tdefs_def] THEN
  GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `nsDomMod (alist_to_ns (REVERSE (build_constrs idx c)):(modN,conN,num # stamp)namespace)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC nsDomMod_nsAppend_flat THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[nsDomMod_alist_to_ns]]);;

(* HOL4 lines 3704-3710: extend_env_v_empty and extend_dec_env_v_empty are  *)
(* ML values (SIMP_CONV results), not stored theorems; they are stated here *)
(* for the port of the proofs that use them                                  *)
let extend_env_v_empty = prove
 (`!c c'.
     extend_env (source_to_flat_environment_REC c nsEmpty)
              (source_to_flat_environment_REC c' nsEmpty) =
   source_to_flat_environment_REC (nsAppend c c') nsEmpty`,
  SIMP_NOASM[extend_env_def; nsAppend_nsEmpty]);;

let extend_dec_env_v_empty = prove
 (`!c c'.
     extend_dec_env (sem_env_REC nsEmpty c) (sem_env_REC nsEmpty c') =
   sem_env_REC nsEmpty (nsAppend c c')`,
  SIMP_NOASM[extend_dec_env_def; nsAppend_nsEmpty]);;

(* HOL4 line 3712 *)
let nsLookup_nsBind_If = prove
 (`!n v e nm.
     nsLookup (nsBind (n:B) (v:C) (e:(A,B,C)namespace)) nm =
   (if nm = Short n then SOME v else nsLookup e nm)`,
  REPEAT GEN_TAC THEN CASES_ON `e:(A,B,C)namespace` THEN CASES_ON `nm:(A,B)id` THEN
  SIMP_NOASM[nsBind_def; nsLookup_def; ALOOKUP_THM] THEN MESON_TAC[]);;

(* HOL4 line 3721 *)
let invariant_IMP_s_rel = prove
 (`!interp g gen genv idx st st'.
     invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv idx
     (st:(FFI)state) (st':(C,FFI)flat_state)
   ==> source_to_flatProof_s_rel genv st st'`,
  SIMP_TAC[invariant_def]);;

(* HOL4 line 3727 *)
let source_to_flatProof_abort_def = cake_def
  `source_to_flatProof_abort (r:(A,B)result) <=>
     match r with
       Rerr (Rabort a) -> T
     | _ -> F`;;

(* HOL4 line 3732 *)
let not_abort_IMP_cases = prove
 (`!r P.
     (~source_to_flatProof_abort (r:(A,B)result) ==> P)
   ==> (?a. r = Rerr (Rabort a)) \/ (~source_to_flatProof_abort r /\ P)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[source_to_flatProof_abort_def] THEN
  EVERY_CASE_TAC THEN SIMP_NOASM[] THEN MESON_TAC[]);;

(* HOL4 line 3739 *)
let source_to_flatProof_abort_simps = prove
 (`!a e v.
     source_to_flatProof_abort (Rerr (Rabort a):(A,B)result) = T /\
   source_to_flatProof_abort (Rerr (Rraise e):(A,B)result) = F /\
   source_to_flatProof_abort (Rval v:(A,B)result) = F`,
  REWRITE_TAC[source_to_flatProof_abort_def] THEN CASE_REWRITE_TAC[]);;
let _ = cake_add_simps [source_to_flatProof_abort_simps];;

(* HOL4 line 3747: Theorem compile_correct, stated at its Finalise (HOL4   *)
(* line 5231) below, after the lemmas proved between its Resume blocks      *)


(* HOL4 lines 3869-4038: trans_thms (an ML list) and the Resume blocks seq,  *)
(* Raise, Handle, Con, Var, Fun of compile_correct (proof parts)             *)

(* HOL4 line 4040 *)
let invariant_change_eval_ref = prove
 (`!interp g gen genv idxs st st' y.
     invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv idxs
     (st:(FFI)state) (st':(C,FFI)flat_state)
   ==> invariant interp g gen genv idxs st
         (flat_state_refs_fupd (K (CONS (Refv y) (TL (flat_state_refs st')))) st')`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[invariant_def; source_to_flatProof_s_rel_cases; eval_ref_inv_def] THEN
  SIMP_NOASM[NULL; TL; TAKE_def; ARITH_RULE `~(1 = 0)`; ARITH_RULE `1 - 1 = 0`] THEN
  MESON_TAC[]);;

let FLATP2AUX_evaluate_store_env_id = prove
 (`!s:(C,FFI)flat_state xs v0 rs gen id.
     flat_state_globals s = CONS (SOME (flat_Loc T 0)) xs /\
     flat_state_refs s = CONS (Refv v0) rs
     ==> flat_evaluate_decs s [store_env_id gen id] =
         (flat_state_refs_fupd (K (CONS (Refv (flat_Conv NONE
            [flat_Litv (IntLit (&gen)); flat_Litv (IntLit (&id))])) rs)) s, NONE)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[store_env_id_def; env_id_tuple_def] THEN
  SIMP[flat_evaluate_def; REVERSE; APPEND; flat_do_app_def; HD; opt_bind_def; ALOOKUP_THM;
       store_assign_def; store_v_same_type_def; LUPDATE_def; LENGTH; EL; flat_Unitv_def;
       ARITH_RULE `0 < SUC n`; list_result_def] THEN
  REWRITE_TAC[flat_state_component_equality] THEN SIMP[]);;

let FLATP2AUX_invs_envs = prove
 (`!interp g f s fc.
     src_orac_next_cfg (interp:(v->(source_to_flat_config#C)option)option)
       (SOME (EvalOracle (eval_oracle_state_envs_fupd f s))) =
     src_orac_next_cfg interp (SOME (EvalOracle s)) /\
     (src_orac_step_invs interp g
        (SOME (EvalOracle (eval_oracle_state_envs_fupd f s))) <=>
      src_orac_step_invs interp g (SOME (EvalOracle s))) /\
     (orac_rel interp g (SOME (EvalOracle (eval_oracle_state_envs_fupd f s))) fc <=>
      orac_rel interp g (SOME (EvalOracle s)) fc)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[src_orac_step_invs_def; src_orac_next_cfg_def; orac_rel_def;
              orac_rel_inner_def] THEN
  CASE_REWRITE_TAC[] THEN SIMP_NOASM[]);;

let FLATP2AUX_eval_ref_inv_cons = prove
 (`!gs rs. eval_ref_inv (TAKE 1 gs) (TAKE 1 rs)
     ==> ?xs v0 rs'. gs = CONS (SOME (flat_Loc T 0)) xs /\ rs = CONS (Refv v0) rs'`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[eval_ref_inv_def; TAKE_def; TAKE_nil; ARITH_RULE `~(1 = 0)`; SUB_REFL;
              NOT_CONS_NIL; CONS_11; ARITH_RULE `1 - 1 = 0`] THEN
  MESON_TAC[]);;

(* HOL4 line 4050 *)
let declare_env_store_env_id = prove
 (CASE_TERM `!st env x es2 interp g gen genv idxs s_i1 gen_id id.
     declare_env (state_eval_state st) env = SOME (x, es2) /\
   invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv idxs
     (st:(FFI)state) (s_i1:(C,FFI)flat_state) /\
   env_gen_rel gen (state_eval_state st) /\
   gen_id = environment_generation_store_generation gen /\
   id = environment_generation_store_next gen /\
   (match src_orac_next_cfg interp (state_eval_state st) with
      NONE -> T
    | SOME c ->
        (match lookup gen_id (environment_store_env_gens (source_to_flat_config_envs c)) with
           NONE -> F
         | SOME gen' -> (match lookup id gen' with
                           NONE -> F
                         | SOME e -> global_env_inv genv e {} env)))
   ==> ?y. flat_evaluate_decs s_i1 [store_env_id gen_id id] =
             (flat_state_refs_fupd (K (CONS (Refv y) (TL (flat_state_refs s_i1)))) s_i1,
              NONE) /\
           invariant interp g
             (environment_generation_store_next_fupd
                (K (environment_generation_store_next gen + 1)) gen)
             genv idxs (state_eval_state_fupd (K es2) st) s_i1 /\
           (?xs. flat_state_globals s_i1 = CONS (SOME (flat_Loc T 0)) xs) /\
           source_to_flatProof_v_rel genv x y /\
           orac_forward_rel interp (state_eval_state st) es2`,
REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["de"; "inv"; "egr"; "gid"; "id"; "lk"]) THEN
  REMOVE_THEN "gid" SUBST_ALL_TAC THEN REMOVE_THEN "id" SUBST_ALL_TAC THEN
  FLATP2AUX_INV_TAC "inv" THEN
  SUBGOAL_THEN `?es. state_eval_state (st:(FFI)state) = SOME (EvalOracle es)`
    STRIP_ASSUME_TAC THENL
   [USE_THEN "orac_rel" MP_TAC THEN USE_THEN "de" MP_TAC THEN
    CASES_ON `state_eval_state (st:(FFI)state)` THEN REWRITE_TAC[declare_env_def] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"] THEN
    CASES_ON `a:eval_state` THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[orac_rel_def] THEN CASE_REWRITE_TAC[] THEN
    CASES_ON `interp:(v->(source_to_flat_config#C)option)option` THEN
    CASE_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
    `state_eval_state (st:(FFI)state) = SOME (EvalOracle es)`]) THEN
  REWRITE_TAC[ASSUME `state_eval_state (st:(FFI)state) = SOME (EvalOracle es)`] THEN
  SUBGOAL_THEN `?dec. (interp:(v->(source_to_flat_config#C)option)option) = SOME dec`
    (X_CHOOSE_THEN `dec:v->(source_to_flat_config#C)option` SUBST_ALL_TAC) THENL
   [USE_THEN "src_orac" (MP_TAC o MATCH_MP step_1 o CONJUNCT1 o
                         REWRITE_RULE[src_orac_invs_def]) THEN MESON_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "de" (MP_TAC o REWRITE_RULE[declare_env_def]) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[oEL_THM] THEN COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  USE_THEN "egr" (MP_TAC o REWRITE_RULE[env_gen_rel_def]) THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["eg1"; "eg2"; "eg3"]) THEN
  USE_THEN "eval_ref" (MP_TAC o MATCH_MP FLATP2AUX_eval_ref_inv_cons) THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`xs:(flat_v option)list`; `v0:flat_v`;
    `rs:(flat_v store_v)list`] (CONJUNCTS_THEN2 (LABEL_TAC "gl") (LABEL_TAC "rf"))) THEN
  EXISTS_TAC `flat_Conv NONE [flat_Litv (IntLit (&(environment_generation_store_generation gen)));
                              flat_Litv (IntLit (&(environment_generation_store_next gen)))]` THEN
  REPEAT CONJ_TAC THENL
   [(* the evaluation *)
    FLATP2AUX_LREWRITE_TAC ["rf"] [TL] THEN
    MATCH_MP_TAC FLATP2AUX_evaluate_store_env_id THEN
    MAP_EVERY EXISTS_TAC [`xs:(flat_v option)list`; `v0:flat_v`] THEN
    FLATP2AUX_LREWRITE_TAC ["gl"; "rf"] [];
    (* the invariant *)
    REWRITE_TAC[invariant_def; src_orac_invs_def] THEN
    SIMP_NOASM[FLATP2AUX_invs_envs] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "c_ok" ACCEPT_TAC;
      USE_THEN "tys_ok" ACCEPT_TAC;
      USE_THEN "s_rel" MP_TAC THEN REWRITE_TAC[source_to_flatProof_s_rel_cases] THEN
      SIMP_NOASM[];
      USE_THEN "idx_range" MP_TAC THEN REWRITE_TAC[idx_range_rel_def] THEN
      SIMP_NOASM[FLATP2AUX_invs_envs];
      USE_THEN "src_orac" (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[src_orac_invs_def]);
      USE_THEN "src_orac" (MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[src_orac_invs_def]) THEN
      REWRITE_TAC[src_orac_env_invs_def] THEN CASE_REWRITE_TAC[] THEN
      SIMP_NOASM[FLATP2AUX_invs_envs; LENGTH_LUPDATE] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:source_to_flat_config`
        (FLATP2AUX_LABEL_CONJS ["nc"; "esi"; "esn"; "eenv"])) THEN
      EXISTS_TAC `c:source_to_flat_config` THEN FLATP2AUX_LREWRITE_TAC ["nc"; "esi"; "esn"] [] THEN
      USE_THEN "lk" MP_TAC THEN FLATP2AUX_LREWRITE_TAC ["nc"; "eg1"; "eg3"] [] THEN
      CASE_REWRITE_TAC[] THEN
      CASES_ON `lookup (eval_oracle_state_generation es)
        (environment_store_env_gens (source_to_flat_config_envs c))` THEN
      CASE_REWRITE_TAC[] THEN REWRITE_TAC[] THEN
      CASES_ON `lookup (LENGTH (EL (eval_oracle_state_generation es)
                   (eval_oracle_state_envs es))) (a:(source_to_flat_environment)spt)` THEN
      CASE_REWRITE_TAC[] THEN REWRITE_TAC[] THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`g_id:num`; `i_d:num`] THEN REWRITE_TAC[EL_LUPDATE] THEN
      ASM_CASES_TAC `g_id = eval_oracle_state_generation es` THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH_APPEND; LENGTH; EL_APPEND] THEN STRIP_TAC THEN
        COND_CASES_TAC THENL
         [REMOVE_THEN "eenv" (MP_TAC o SPECL [`eval_oracle_state_generation es`; `i_d:num`]) THEN
          ASM_REWRITE_TAC[];
          SUBGOAL_THEN `i_d = LENGTH (EL (eval_oracle_state_generation es)
                                      (eval_oracle_state_envs es))` SUBST_ALL_TAC THENL
           [ASM_ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[SUB_REFL; EL; HD] THEN
          MAP_EVERY EXISTS_TAC [`a:(source_to_flat_environment)spt`;
                                `a':source_to_flat_environment`] THEN
          ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[] THEN
        REMOVE_THEN "eenv" (MP_TAC o SPECL [`g_id:num`; `i_d:num`]) THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[src_orac_gen_inv_def] THEN CASE_REWRITE_TAC[] THEN
      SIMP_NOASM[LENGTH_LUPDATE] THEN FLATP2AUX_LREWRITE_TAC ["eg2"] [];
      USE_THEN "orac_rel" ACCEPT_TAC;
      USE_THEN "globals" ACCEPT_TAC;
      USE_THEN "eval_ref" ACCEPT_TAC;
      USE_THEN "env_gen_inv" MP_TAC THEN
      SIMP_NOASM[env_gen_inv_def; SUBSET; IN_COUNT] THEN MESON_TAC[ARITH_RULE `x < n ==> x < n + 1`];
      USE_THEN "fin_idx" ACCEPT_TAC];
    (* globals *)
    USE_THEN "gl" (fun th -> MESON_TAC[th]);
    (* v_rel *)
    FLATP2AUX_LREWRITE_TAC ["eg1"; "eg3"] [nat_to_v_def] THEN
    SIMP_NOASM[v_rel_eqns; ALL2];
    (* forward *)
    REWRITE_TAC[orac_forward_rel_def; orac_config_envs_subspt_def; FLATP2AUX_invs_envs] THEN
    CONJ_TAC THENL
     [CASES_ON `src_orac_next_cfg (SOME (dec:v->(source_to_flat_config#C)option))
                  (SOME (EvalOracle es))` THEN REWRITE_TAC[OPTREL_THM; subspt_refl];
      REWRITE_TAC[eval_state_call_rel_def] THEN CASE_REWRITE_TAC[] THEN
      SIMP_NOASM[LENGTH_LUPDATE; EL_LUPDATE] THEN
      MESON_TAC[ARITH_RULE `i < n ==> ~(i = n)`]]]);;

let FLATP2AUX_LENGTH_6 = prove
 (`!l:A list. LENGTH l = 6 <=> ?a1 a2 a3 a4 a5 a6. l = [a1;a2;a3;a4;a5;a6]`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `6 = SUC(SUC(SUC(SUC(SUC(SUC 0)))))`; LENGTH_EQ_CONS;
                LENGTH_EQ_NIL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[CONS_11] THEN MESON_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC]);;

(* HOL4 line 4119 *)
let pmatch_rows_drop_4 = prove
 (`!vs b w exp st.
     LENGTH vs = 6
   ==> pmatch_rows [(flat_Pcon NONE [flat_Pany; flat_Pany; flat_Pany; flat_Pany;
                                     flat_Pvar b; flat_Pvar w], (exp:A))]
                   (st:(C,FFI)flat_state) (flat_Conv NONE vs) =
       Match ([(w, LAST vs); (b, EL 4 vs)],
              flat_Pcon NONE [flat_Pany; flat_Pany; flat_Pany; flat_Pany;
                              flat_Pvar b; flat_Pvar w], exp)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FLATP2AUX_LENGTH_6] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[pmatch_rows_def; flat_pmatch_def; pmatch_stamps_ok_cases; LENGTH;
                  OPTION_MAP_DEF] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LAST; NOT_CONS_NIL; ARITH_RULE `4 = SUC(SUC(SUC(SUC 0)))`; EL; HD; TL]);;

(* HOL4 line 4133 *)
let drop_4_via_el = prove
 (`!vs.
     LENGTH (vs:A list) = 6 ==> [EL 4 vs; LAST vs] = DROP 4 vs`,
  REWRITE_TAC[FLATP2AUX_LENGTH_6] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[LAST; NOT_CONS_NIL; ARITH_RULE `4 = SUC(SUC(SUC(SUC 0)))`; EL; HD; TL;
                  DROP]);;

(* HOL4 lines 4145-4706: the Resume blocks App, Log, If, Mat, Let, Letrec,  *)
(* pattern, empty_decs of compile_correct                                    *)

(* HOL4 line 4708 *)
let abort_compile_dec_result = prove
 (`!env r.
     source_to_flatProof_abort (combine_dec_result env (r:((v)sem_env,A)result)) =
   source_to_flatProof_abort r`,
  REPEAT GEN_TAC THEN CASES_ON `r:((v)sem_env,A)result` THEN
  REWRITE_TAC[combine_dec_result_def; source_to_flatProof_abort_def] THEN
  CASE_REWRITE_TAC[]);;

(* HOL4 line 4714 *)
let invariant_env_gen_inv = prove
 (`!interp g gen genv idx end_idx os s s_i1.
     invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv
     (idx,end_idx,os) (s:(FFI)state) (s_i1:(C,FFI)flat_state)
   ==> env_gen_inv gen`,
  SIMP_TAC[invariant_def]);;

(* HOL4 line 4722 *)
let compile_decs_future_rel = prove
 (`!t n next env envs ds n2 next2 env2 envs2 ds2 interp eval_state.
     source_to_flat_compile_decs t n next env envs ds = (n2, next2, env2, envs2, ds2) /\
   env_gen_future_rel (interp:(v->(source_to_flat_config#C)option)option) envs2
     eval_state /\
   env_gen_inv envs
   ==> env_gen_future_rel interp envs eval_state`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cd") (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "inv"))) THEN
  USE_THEN "cd" (ASSUME_TAC o MATCH_MP compile_decs_generation) THEN
  USE_THEN "cd" (fun th -> USE_THEN "inv" (fun th2 ->
    ASSUME_TAC (CONJUNCT2 (MATCH_MP compile_decs_env_gen_inv (CONJ th th2))))) THEN
  REWRITE_TAC[env_gen_future_rel_def] THEN
  CASES_ON `src_orac_next_cfg (interp:(v->(source_to_flat_config#C)option)option)
              eval_state` THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `gen_final:(source_to_flat_environment)spt` THEN
  ASM_MESON_TAC[subspt_trans]);;

(* HOL4 line 4737 *)
let env_gen_future_rel_forward = prove
 (`!interp envs eval_state eval_state2.
     env_gen_future_rel (interp:(v->(source_to_flat_config#C)option)option) envs
     eval_state /\
   orac_forward_rel interp eval_state eval_state2
   ==> env_gen_future_rel interp envs eval_state2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[env_gen_future_rel_def; orac_forward_rel_def; orac_config_envs_subspt_def] THEN
  CASES_ON `src_orac_next_cfg (interp:(v->(source_to_flat_config#C)option)option)
              eval_state` THEN
  CASES_ON `src_orac_next_cfg (interp:(v->(source_to_flat_config#C)option)option)
              eval_state2` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[OPTREL_THM] THEN
  REWRITE_TAC[subspt_lookup] THEN MESON_TAC[]);;

(* HOL4 lines 4751-5231: the Resume blocks cons_decs, Dlet, Dletrec, Dtype, *)
(* Dtabbrev, Denv, Dexn, Dmod, Dlocal and Finalise compile_correct           *)

(* the induction cases of compile_correct (HOL4 lines 3836-5230), one       *)
(* lemma per HOL4 Resume block, with their helper lemmas                    *)

(* the statement of compile_correct (HOL4 line 3747; proved at its Finalise *)
(* below) and the cases of its induction (the HOL4 suspend/Resume blocks):   *)
(* the goals of MATCH_MP_TAC full_evaluate_ind, one lemma per block          *)
let FLATP2AUX_cc_goal = `!interp g.
     (!(s:(FFI)state) env es s' r genv comp_map env_i1 (s_i1:(C,FFI)flat_state) es_i1
      locals t ts gen idxs.
      evaluate s env es = (s', r) /\
      invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv idxs
        s s_i1 /\
      env_all_rel genv comp_map env env_i1 locals /\
      LENGTH ts = LENGTH locals /\
      env_gen_rel gen (state_eval_state s) /\
      ~(r = Rerr (Rabort Rtype_error)) /\
      es_i1 = source_to_flat_compile_exps t
                (source_to_flat_environment_v_fupd
                   (K (bind_locals ts locals (source_to_flat_environment_v comp_map)))
                   comp_map) es
      ==> ?s'_i1 r_i1 genv'.
            flat_evaluate env_i1 s_i1 es_i1 = (s'_i1, r_i1) /\
            source_to_flatProof_result_rel (ALL2 o source_to_flatProof_v_rel) genv' r r_i1 /\
            source_to_flatProof_s_rel genv' s' s'_i1 /\
            (~source_to_flatProof_abort r
             ==> invariant interp g gen genv' idxs s' s'_i1 /\
                 env_gen_rel gen (state_eval_state s') /\
                 orac_forward_rel interp (state_eval_state s) (state_eval_state s') /\
                 global_env_c genv SUBMAP global_env_c genv' /\
                 global_env_tys genv SUBMAP global_env_tys genv' /\
                 subglobals (global_env_v genv) (global_env_v genv'))) /\
   (!(s:(FFI)state) env v pes err_v genv comp_map s' r env_i1 (s_i1:(C,FFI)flat_state)
      v_i1 pes_i1 err_v_i1 locals t ts gen idxs.
      evaluate_match s env v pes err_v = (s', r) /\
      invariant interp g gen genv idxs s s_i1 /\
      env_all_rel genv comp_map env env_i1 locals /\
      source_to_flatProof_v_rel genv v v_i1 /\
      LENGTH ts = LENGTH locals /\
      env_gen_rel gen (state_eval_state s) /\
      ~(r = Rerr (Rabort Rtype_error)) /\
      pes_i1 = compile_pes t
                 (source_to_flat_environment_v_fupd
                    (K (bind_locals ts locals (source_to_flat_environment_v comp_map)))
                    comp_map) pes /\
      ~(pmatch_rows pes_i1 s_i1 v_i1 = Match_type_error) /\
      source_to_flatProof_v_rel genv err_v err_v_i1
      ==> ?s'_i1 r_i1 genv'.
            flat_evaluate_match env_i1 s_i1 v_i1 pes_i1 err_v_i1 = (s'_i1, r_i1) /\
            source_to_flatProof_result_rel (ALL2 o source_to_flatProof_v_rel) genv' r r_i1 /\
            source_to_flatProof_s_rel genv' s' s'_i1 /\
            (~source_to_flatProof_abort r
             ==> invariant interp g gen genv' idxs s' s'_i1 /\
                 env_gen_rel gen (state_eval_state s') /\
                 orac_forward_rel interp (state_eval_state s) (state_eval_state s') /\
                 global_env_c genv SUBMAP global_env_c genv' /\
                 global_env_tys genv SUBMAP global_env_tys genv' /\
                 subglobals (global_env_v genv) (global_env_v genv'))) /\
   (!(s:(FFI)state) env ds s' r path t idx end_idx os comp_map
      (s_i1:(C,FFI)flat_state) idx' comp_map' ds_i1 t' genv gen gen'.
      evaluate_decs s env ds = (s', r) /\
      invariant interp g gen genv (idx, end_idx, os) s s_i1 /\
      source_to_flat_compile_decs path t idx comp_map gen ds =
        (t', idx', comp_map', gen', ds_i1) /\
      global_env_inv genv comp_map {} env /\
      ~(r = Rerr (Rabort Rtype_error)) /\
      env_gen_rel gen (state_eval_state s) /\
      env_gen_future_rel interp gen' (state_eval_state s) /\
      idx_prev idx' end_idx
      ==> ?(s1_i1:(C,FFI)flat_state) genv' r_i1.
            flat_evaluate_decs s_i1 ds_i1 = (s1_i1, r_i1) /\
            source_to_flatProof_s_rel genv' s' s1_i1 /\
            (~source_to_flatProof_abort r
             ==> invariant interp g gen' genv' (idx', end_idx, os) s' s1_i1 /\
                 orac_forward_rel interp (state_eval_state s) (state_eval_state s') /\
                 global_env_c genv SUBMAP global_env_c genv' /\
                 global_env_tys genv SUBMAP global_env_tys genv' /\
                 subglobals (global_env_v genv) (global_env_v genv')) /\
            (!env'. r = Rval env'
                    ==> r_i1 = NONE /\ env_domain_eq comp_map' env' /\
                        env_gen_rel gen' (state_eval_state s') /\
                        global_env_inv genv' comp_map' {} env') /\
            (!err. r = Rerr err
                   ==> ?err_i1. r_i1 = SOME err_i1 /\
                                source_to_flatProof_result_rel (\a b (c:A). T) genv'
                                  (Rerr err:((v)sem_env,v)result) (Rerr err_i1)))`;;

let FLATP2AUX_cc_gls =
  let _,gs,_ = (REPEAT GEN_TAC THEN MATCH_MP_TAC full_evaluate_ind THEN REPEAT CONJ_TAC)
                 ([],FLATP2AUX_cc_goal) in
  map snd gs;;

let FLATP2AUX_cc_case k = el k FLATP2AUX_cc_gls;;

let FLATP2AUX_flat_Handle = prove
 (CASE_TERM `!env (s:(C,FFI)flat_state) e s1 r tr pes.
     flat_evaluate env s [e] = (s1, r)
     ==> flat_evaluate env s [flat_Handle tr e pes] =
         (match r with
            Rerr (Rraise v) -> flat_evaluate_match env s1 v pes v
          | _ -> (s1, r))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[flat_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `r:(flat_v list,flat_v)result` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a:(flat_v)error_result` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[flat_evaluate_match_def]);;
let FLATP2AUX_env_all_rel_c = prove
 (`!genv comp_map env env' locals x arity stamp.
     env_all_rel genv comp_map env env' locals /\
     nsLookup (sem_env_c env) x = SOME (arity, stamp)
     ==> ?cn ty_gp.
           nsLookup (source_to_flat_environment_c comp_map) x = SOME (cn, ty_gp) /\
           FLOOKUP (global_env_c genv) ((cn, OPTION_MAP FST ty_gp), arity) = SOME stamp /\
           (!ty_id ctors. ty_gp = SOME (ty_id, ctors)
                          ==> FLOOKUP (global_env_tys genv) ty_id = SOME ctors)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[env_all_rel_cases] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[v_rel_global_eqn]) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  ASM_SIMP_TAC[sem_env_INFO.ri_accessors] THEN ASM_MESON_TAC[]);;
let FLATP2AUX_ALOOKUP_MAP2_Local = prove
 (`!locals ts x.
     LENGTH (ts:(tra)list) = LENGTH locals
     ==> (ALOOKUP (MAP2 (\t x. x, source_to_flat_Local t x) ts locals) x = NONE <=>
          ~MEM x locals) /\
         (MEM x locals
          ==> ?t'. ALOOKUP (MAP2 (\t x. x, source_to_flat_Local t x) ts locals) x =
                   SOME (source_to_flat_Local t' x))`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ts:(tra)list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; ARITH_RULE `~(0 = SUC n)`; MAP2; ALOOKUP_THM; MEM; SUC_INJ] THEN
  X_GEN_TAC `x:mlstring` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t':(tra)list`; `x:mlstring`]) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[distinctness "option"; injectivity "option"] THEN MESON_TAC[]);;
let FLATP2AUX_nsLookup_nsAppend_alist = prove
 (CASE_TERM `!(l:(B#C)list) (e:(A,B,C)namespace) (id:(A,B)id).
     nsLookup (nsAppend (alist_to_ns l) e) id =
     (match id with
        Short x -> (match ALOOKUP l x with NONE -> nsLookup e id | SOME v -> SOME v)
      | Long mn id' -> nsLookup e id)`,
  REPEAT GEN_TAC THEN CASES_ON `e:(A,B,C)namespace` THEN CASES_ON `id:(A,B)id` THEN
  REWRITE_TAC[alist_to_ns_def; nsAppend_def; nsLookup_def; ALOOKUP_APPEND; APPEND] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[ALOOKUP_THM] THEN CASE_REWRITE_TAC[]);;
let FLATP2AUX_flat_eval_global = prove
 (`!env (s:(C,FFI)flat_state) t n v.
     n < LENGTH (flat_state_globals s) /\ EL n (flat_state_globals s) = SOME v
     ==> flat_evaluate env s [flat_App t (GlobalVarLookup n) []] = (s, Rval [v])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[flat_evaluate_def; REVERSE] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "flat_op"] THEN
  ASM_REWRITE_TAC[flat_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[IS_SOME_DEF; THE_DEF] THEN CASE_REWRITE_TAC[] THEN
  SIMP_NOASM[REVERSE; list_result_def]);;
let FLATP2AUX_sem_env_v_fupd = prove
 (`!f (env:v sem_env). sem_env_v_fupd f env = sem_env_REC (f (sem_env_v env)) (sem_env_c env)`,
  REWRITE_TAC[(record_info "sem_env").ri_component_equality] THEN SIMP_NOASM[]);;

let FLATP2AUX_v_rel_closure = prove
 (`!genv comp_map env env_i1 locals ts t x e.
     env_all_rel genv comp_map env env_i1 locals /\ LENGTH ts = LENGTH locals
     ==> source_to_flatProof_v_rel genv (Closure env x e)
           (flat_Closure env_i1 x
             (source_to_flat_compile_exp t
               (source_to_flat_environment_v_fupd
                 (K (nsBind x (source_to_flat_Local backend_common_None x)
                       (bind_locals ts locals (source_to_flat_environment_v comp_map))))
                 comp_map) e))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[env_all_rel_cases] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (FLATP2AUX_CHOOSE_THEN [`evl:(modN,varN,v)namespace`;
    `env0:v sem_env`; `env1:(varN#flat_v)list`]
    (FLATP2AUX_LABEL_CONJS ["envq"; "ei1q"; "lq"; "gei"; "er"])) (LABEL_TAC "lts")) THEN
  REMOVE_THEN "envq" SUBST_ALL_TAC THEN REMOVE_THEN "ei1q" SUBST_ALL_TAC THEN
  REMOVE_THEN "lq" (X_CHOOSE_THEN `l:(varN#v)list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (LABEL_TAC "lfst"))) THEN
  REMOVE_THEN "lfst" (SUBST_ALL_TAC o SYM) THEN
  USE_THEN "er" (MP_TAC o MATCH_MP env_rel_dom) THEN
  DISCH_THEN(X_CHOOSE_THEN `l':(varN#v)list` (CONJUNCTS_THEN2 (LABEL_TAC "leq")
    (LABEL_TAC "lmap"))) THEN
  MP_TAC(ISPECL [`genv:global_env`; `comp_map:source_to_flat_environment`; `env0:v sem_env`;
    `(alist_to_ns (l:(varN#v)list)):(modN,varN,v)namespace`; `x:varN`; `e:exp`;
    `flat_environment_REC (env1:(varN#flat_v)list)`; `t:mlstring list`;
    `CONS backend_common_None (ts:(tra)list)`]
    (el 3 (CONJUNCTS source_to_flatProof_v_rel_rules))) THEN
  SUBGOAL_THEN `MAP FST (l:(varN#v)list) = MAP FST (env1:(varN#flat_v)list)` (LABEL_TAC "fst") THENL
   [USE_THEN "lmap" (SUBST1_TAC o SYM) THEN
    USE_THEN "leq" (MP_TAC o REWRITE_RULE[alist_to_ns_def; injectivity "namespace"]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FLATP2AUX_sem_env_v_fupd; K_THM; FLATP1AUX_bind_locals_CONS] THEN
  SIMP_NOASM[LENGTH] THEN FLATP2AUX_LREWRITE_TAC ["fst"] [] THEN
  DISCH_THEN MATCH_MP_TAC THEN FLATP2AUX_LREWRITE_TAC ["er"; "lts"; "fst"] [LENGTH_MAP] THEN
  CONJ_TAC THENL
   [USE_THEN "gei" (MP_TAC o REWRITE_RULE[]) THEN FLATP2AUX_LREWRITE_TAC ["fst"] [];
    USE_THEN "fst" (MP_TAC o AP_TERM `LENGTH:varN list->num`) THEN
    USE_THEN "lts" MP_TAC THEN REWRITE_TAC[LENGTH_MAP] THEN ARITH_TAC]);;
let FLATP2AUX_flat_If = prove
 (CASE_TERM `!env (s:(C,FFI)flat_state) e1 s1 r t e2 e3.
     flat_evaluate env s [e1] = (s1, r)
     ==> flat_evaluate env s [flat_If t e1 e2 e3] =
         (match r with
            Rval vs -> (match flat_do_if (HD vs) e2 e3 with
                          SOME e -> flat_evaluate env s1 [e]
                        | NONE -> (s1, Rerr (Rabort Rtype_error)))
          | Rerr e -> (s1, r))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[flat_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASES_ON `r:(flat_v list,flat_v)result` THEN CASE_REWRITE_TAC[]);;
let FLATP2AUX_flat_Mat = prove
 (CASE_TERM `!env (s:(C,FFI)flat_state) e s1 r t pes.
     flat_evaluate env s [e] = (s1, r)
     ==> flat_evaluate env s [flat_Mat t e pes] =
         (match r with
            Rval v -> flat_evaluate_match env s1 (HD v) pes flat_bind_exn_v
          | Rerr e -> (s1, r))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[flat_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASES_ON `r:(flat_v list,flat_v)result` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[flat_evaluate_match_def]);;
let FLATP2AUX_nsBind_alist = prove
 (`!x (v:C) (l:(B#C)list).
     nsBind x v (alist_to_ns l:(A,B,C)namespace) = alist_to_ns (CONS (x,v) l)`,
  REWRITE_TAC[alist_to_ns_def; nsBind_def]);;

let FLATP2AUX_nsBind_nsAppend_alist = prove
 (`!x (v:C) (l:(B#C)list) (e:(A,B,C)namespace).
     nsBind x v (nsAppend (alist_to_ns l) e) = nsAppend (alist_to_ns (CONS (x,v) l)) e`,
  REPEAT GEN_TAC THEN CASES_ON `e:(A,B,C)namespace` THEN
  REWRITE_TAC[alist_to_ns_def; nsBind_def; nsAppend_def; APPEND]);;

let FLATP2AUX_env_all_rel_bind = prove
 (`!genv comp_map env env_i1 locals x v v'.
     env_all_rel genv comp_map env env_i1 locals /\ source_to_flatProof_v_rel genv v v'
     ==> env_all_rel genv comp_map (sem_env_v_fupd (K (nsBind x v (sem_env_v env))) env)
           (flat_environment_v_fupd (K (CONS (x,v') (flat_environment_v env_i1))) env_i1)
           (CONS x locals)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[env_all_rel_cases] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (FLATP2AUX_CHOOSE_THEN [`evl:(modN,varN,v)namespace`;
    `env0:v sem_env`; `env1:(varN#flat_v)list`]
    (FLATP2AUX_LABEL_CONJS ["envq"; "ei1q"; "lq"; "gei"; "er"])) (LABEL_TAC "vr")) THEN
  REMOVE_THEN "envq" SUBST_ALL_TAC THEN REMOVE_THEN "ei1q" SUBST_ALL_TAC THEN
  REMOVE_THEN "lq" (X_CHOOSE_THEN `l:(varN#v)list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (LABEL_TAC "lfst"))) THEN
  MAP_EVERY EXISTS_TAC [`alist_to_ns (CONS (x:varN,v:v) l):(modN,varN,v)namespace`;
    `env0:v sem_env`; `CONS (x:varN,v':flat_v) env1`] THEN
  REWRITE_TAC[sem_env_INFO.ri_accessors; sem_env_INFO.ri_fupds; K_THM;
              flat_environment_INFO.ri_accessors; flat_environment_INFO.ri_fupds;
              FLATP2AUX_nsBind_nsAppend_alist] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `CONS (x:varN,v:v) l` THEN FLATP2AUX_LREWRITE_TAC ["lfst"] [MAP; FST];
    REWRITE_TAC[set_of_list] THEN ONCE_REWRITE_TAC[INSERT_SING_UNION] THEN
    MATCH_MP_TAC global_env_inv_add_locals THEN
    FLATP2AUX_LREWRITE_TAC ["gei"] [];
    REWRITE_TAC[GSYM FLATP2AUX_nsBind_alist] THEN
    MATCH_MP_TAC(el 9 (CONJUNCTS source_to_flatProof_v_rel_rules)) THEN
    FLATP2AUX_LREWRITE_TAC ["er"; "vr"] []]);;
let FLATP2AUX_flat_Let = prove
 (CASE_TERM `!env (s:(C,FFI)flat_state) e1 s1 r t n e2.
     flat_evaluate env s [e1] = (s1, r)
     ==> flat_evaluate env s [flat_Let t n e1 e2] =
         (match r with
            Rval vs -> flat_evaluate (flat_environment_v_fupd (opt_bind n (HD vs)) env) s1 [e2]
          | Rerr e -> (s1, r))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[flat_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASES_ON `r:(flat_v list,flat_v)result` THEN CASE_REWRITE_TAC[]);;

let FLATP2AUX_flat_env_v_fupd = prove
 (`!f (env:(flat_v)flat_environment).
     flat_environment_v_fupd f env = flat_environment_REC (f (flat_environment_v env))`,
  REWRITE_TAC[(record_info "flat_environment").ri_component_equality] THEN SIMP_NOASM[]);;
let FLATP2AUX_record_etas = prove
 (`(!env:v sem_env. sem_env_v_fupd (K (sem_env_v env)) env = env) /\
   (!env:(flat_v)flat_environment. flat_environment_v_fupd (\e. e) env = env) /\
   (!env:(flat_v)flat_environment. flat_environment_v_fupd I env = env)`,
  REWRITE_TAC[(record_info "sem_env").ri_component_equality;
              (record_info "flat_environment").ri_component_equality] THEN
  SIMP_NOASM[I_THM]);;

let FLATP2AUX_opt_bind_fun = prove
 (`(!v:A. opt_bind (NONE:(B)option) v = (\e. e)) /\
   (!(x:B) (v:A). opt_bind (SOME x) v = (\e. CONS (x,v) e))`,
  REWRITE_TAC[FUN_EQ_THM; opt_bind_def] THEN CASE_REWRITE_TAC[]);;
let FLATP2AUX_flat_env_REC_eta = prove
 (`!env:(flat_v)flat_environment. flat_environment_REC (flat_environment_v env) = env`,
  REWRITE_TAC[(record_info "flat_environment").ri_component_equality] THEN SIMP_NOASM[]);;

let FLATP2AUX_MAP_compile_funs = prove
 (CASE_TERM `!t cm funs (R:varN->A).
     MAP (\fne. match fne with (f,y) -> (match y with (n,e) -> (f, R f)))
         (compile_funs t cm funs) =
     MAP (\fne. match fne with (f,y) -> (match y with (n,e) -> (f, R f))) funs`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; source_to_flat_compile_exp_def] THEN GEN_TAC THEN
  MP_TAC(ISPEC `h:varN#varN#exp` (prove(`!x:A#B#C. ?a b c. x = (a,b,c)`,
    REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[]))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[source_to_flat_compile_exp_def; MAP] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let FLATP2AUX_env_rel_map = prove
 (CASE_TERM `!(fs:(varN#varN#exp)list) (A:varN->v) (B:varN->flat_v) genv.
     (!f. MEM f (MAP FST fs) ==> source_to_flatProof_v_rel genv (A f) (B f))
     ==> source_to_flatProof_env_rel genv
           (alist_to_ns (MAP (\fne. match fne with (f,y) -> (match y with (n,e) -> (f, A f))) fs))
           (MAP (\fne. match fne with (f,y) -> (match y with (n,e) -> (f, B f))) fs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM] THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM nsEmpty_def; alist_to_ns_def] THEN
    REWRITE_TAC[GSYM alist_to_ns_def] THEN
    MP_TAC(SPEC `genv:global_env` (el 8 (CONJUNCTS source_to_flatProof_v_rel_rules))) THEN
    REWRITE_TAC[nsEmpty_def; alist_to_ns_def];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `h:varN#varN#exp` (prove(`!x:A#B#C. ?a b c. x = (a,b,c)`,
    REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[]))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FST] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM FLATP2AUX_nsBind_alist] THEN
  MATCH_MP_TAC(el 9 (CONJUNCTS source_to_flatProof_v_rel_rules)) THEN
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ASM_MESON_TAC[]]);;

let FLATP2AUX_MAP_FST_rec = prove
 (CASE_TERM `!(funs:(varN#varN#exp)list) (R:varN->A).
     MAP FST (MAP (\fne. match fne with (f,y) -> (match y with (n,e) -> (f, R f))) funs) =
     MAP FST funs`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[MAP_MAP_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[FST]);;
let FLATP2AUX_env_all_rel_letrec = prove
 (CASE_TERM `!genv comp_map env env_i1 locals ts t funs.
   env_all_rel genv comp_map env env_i1 locals /\ LENGTH ts = LENGTH locals
   ==> env_all_rel genv comp_map
         (sem_env_v_fupd (K (build_rec_env funs env (sem_env_v env))) env)
         (flat_environment_v_fupd (K (flat_build_rec_env
             (compile_funs t (source_to_flat_environment_v_fupd
                (K (bind_locals (APPEND (REPLICATE (LENGTH funs) backend_common_None) ts)
                      (APPEND (MAP FST funs) locals) (source_to_flat_environment_v comp_map)))
                comp_map) funs)
             env_i1 (flat_environment_v env_i1))) env_i1)
         (APPEND (MAP FST funs) locals)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[env_all_rel_cases] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (FLATP2AUX_CHOOSE_THEN [`evl:(modN,varN,v)namespace`;
    `env0:v sem_env`; `env1:(varN#flat_v)list`]
    (FLATP2AUX_LABEL_CONJS ["envq"; "ei1q"; "lq"; "gei"; "er"])) (LABEL_TAC "lts")) THEN
  REMOVE_THEN "envq" SUBST_ALL_TAC THEN REMOVE_THEN "ei1q" SUBST_ALL_TAC THEN
  REMOVE_THEN "lq" (X_CHOOSE_THEN `l:(varN#v)list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (LABEL_TAC "lfst"))) THEN
  REMOVE_THEN "lfst" (SUBST_ALL_TAC o SYM) THEN
  USE_THEN "er" (MP_TAC o MATCH_MP env_rel_dom) THEN
  DISCH_THEN(X_CHOOSE_THEN `l':(varN#v)list` (CONJUNCTS_THEN2 (LABEL_TAC "l_eq")
    (LABEL_TAC "lmap"))) THEN
  REMOVE_THEN "l_eq" (SUBST_ALL_TAC o SYM o REWRITE_RULE[alist_to_ns_def; injectivity "namespace"]) THEN
  REWRITE_TAC[sem_env_INFO.ri_accessors; sem_env_INFO.ri_fupds; K_THM;
              flat_environment_INFO.ri_accessors; flat_environment_INFO.ri_fupds;
              build_rec_env_merge; flat_build_rec_env_merge; FLATP2AUX_MAP_compile_funs] THEN
  FLATP2AUX_EXISTSL [{|alist_to_ns (APPEND (MAP (\fne. match fne with (f,y) -> (match y with
      (n,e) -> (f, Recclosure (sem_env_REC (nsAppend (alist_to_ns l) (sem_env_v env0))
        (sem_env_c env0)) funs f))) funs) l):(modN,varN,v)namespace|}; {|env0:v sem_env|};
    {|APPEND (MAP (\fne. match fne with (f,y) -> (match y with
      (n,e) -> (f, flat_Recclosure (flat_environment_REC env1)
        (compile_funs t (source_to_flat_environment_v_fupd
          (K (bind_locals (APPEND (REPLICATE (LENGTH funs) backend_common_None) ts)
             (APPEND (MAP FST funs) (MAP FST l)) (source_to_flat_environment_v comp_map)))
          comp_map) funs) f))) funs) env1|}] THEN
  REWRITE_TAC[nsAppend_assoc; nsAppend_alist_to_ns] THEN REPEAT CONJ_TAC THENL
   [(fun (asl,w as gl) -> let _,bod = dest_exists w in
                           EXISTS_TAC (rand(lhand(lhand bod))) gl) THEN
    REWRITE_TAC[MAP_APPEND; FLATP2AUX_MAP_FST_rec];
    REWRITE_TAC[SET_OF_LIST_APPEND] THEN MATCH_MP_TAC global_env_inv_add_locals THEN
    FLATP2AUX_LREWRITE_TAC ["gei"] [];
    REWRITE_TAC[GSYM nsAppend_alist_to_ns] THEN
    MATCH_MP_TAC source_to_flatProof_env_rel_append THEN FLATP2AUX_LREWRITE_TAC ["er"] [] THEN
    MATCH_MP_TAC FLATP2AUX_env_rel_map THEN X_GEN_TAC `f:varN` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`genv:global_env`; `comp_map:source_to_flat_environment`; `env0:v sem_env`;
      `(alist_to_ns (l:(varN#v)list)):(modN,varN,v)namespace`; `funs:(varN#varN#exp)list`;
      `f:varN`; `flat_environment_REC (env1:(varN#flat_v)list)`; `t:mlstring list`;
      `APPEND (REPLICATE (LENGTH (funs:(varN#varN#exp)list)) backend_common_None) ts`]
      (el 4 (CONJUNCTS source_to_flatProof_v_rel_rules))) THEN
    REWRITE_TAC[flat_environment_INFO.ri_accessors; FLATP2AUX_sem_env_v_fupd; K_THM] THEN
    FLATP2AUX_LREWRITE_TAC ["er"; "lmap"] [] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [USE_THEN "gei" MP_TAC THEN FLATP2AUX_LREWRITE_TAC ["lmap"] [];
      USE_THEN "lmap" (MP_TAC o AP_TERM `LENGTH:varN list->num`) THEN
      USE_THEN "lts" MP_TAC THEN REWRITE_TAC[LENGTH_MAP; LENGTH_APPEND; LENGTH_REPLICATE] THEN
      ARITH_TAC]]);;
let FLATP2AUX_FST3_case = prove
 (CASE_TERM `(\xyz:A#B#C. match xyz with (x,y) -> (match y with (y',z) -> x)) = FST`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[FST]);;
let FLATP2AUX_env_all_rel_append = prove
 (`!genv comp_map env env_i1 locals env_v env2.
     env_all_rel genv comp_map env env_i1 locals /\
     source_to_flatProof_env_rel genv (alist_to_ns env_v) env2
     ==> env_all_rel genv comp_map
           (sem_env_v_fupd (K (nsAppend (alist_to_ns env_v) (sem_env_v env))) env)
           (flat_environment_v_fupd (K (APPEND env2 (flat_environment_v env_i1))) env_i1)
           (APPEND (MAP FST env_v) locals)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[env_all_rel_cases] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (FLATP2AUX_CHOOSE_THEN [`evl:(modN,varN,v)namespace`;
    `env0:v sem_env`; `env1:(varN#flat_v)list`]
    (FLATP2AUX_LABEL_CONJS ["envq"; "ei1q"; "lq"; "gei"; "er"])) (LABEL_TAC "er2")) THEN
  REMOVE_THEN "envq" SUBST_ALL_TAC THEN REMOVE_THEN "ei1q" SUBST_ALL_TAC THEN
  REMOVE_THEN "lq" (X_CHOOSE_THEN `l:(varN#v)list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (LABEL_TAC "lfst"))) THEN
  REMOVE_THEN "lfst" (SUBST_ALL_TAC o SYM) THEN
  MAP_EVERY EXISTS_TAC [`alist_to_ns (APPEND (env_v:(varN#v)list) l):(modN,varN,v)namespace`;
    `env0:v sem_env`; `APPEND (env2:(varN#flat_v)list) env1`] THEN
  REWRITE_TAC[sem_env_INFO.ri_accessors; sem_env_INFO.ri_fupds; K_THM;
              flat_environment_INFO.ri_accessors; flat_environment_INFO.ri_fupds;
              nsAppend_assoc; nsAppend_alist_to_ns] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `APPEND (env_v:(varN#v)list) l` THEN REWRITE_TAC[MAP_APPEND];
    REWRITE_TAC[SET_OF_LIST_APPEND] THEN MATCH_MP_TAC global_env_inv_add_locals THEN
    FLATP2AUX_LREWRITE_TAC ["gei"] [];
    REWRITE_TAC[GSYM nsAppend_alist_to_ns] THEN
    MATCH_MP_TAC source_to_flatProof_env_rel_append THEN FLATP2AUX_LREWRITE_TAC ["er"; "er2"] []]);;
let FLATP2AUX_flat_evaluate_match_cons = prove
 (`!env (s:(C,FFI)flat_state) v p e pes err_v env2.
     (flat_pmatch s p v [] = No_match
      ==> flat_evaluate_match env s v (CONS (p,e) pes) err_v =
          flat_evaluate_match env s v pes err_v) /\
     (flat_pmatch s p v [] = Match env2 /\ ~(pmatch_rows pes s v = Match_type_error) /\
      ALL_DISTINCT (flat_pat_bindings p)
      ==> flat_evaluate_match env s v (CONS (p,e) pes) err_v =
          flat_evaluate (flat_environment_v_fupd (K (APPEND env2 (flat_environment_v env))) env)
            s [e])`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[flat_evaluate_match_def; pmatch_rows_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `pmatch_rows (pes:(flat_pat#flat_exp)list) (s:(C,FFI)flat_state) v`
    (cases "match_result")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> if is_neg(concl th) then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[distinctness "match_result"]);;
let FLATP2AUX_compile_decs_cons = prove
 (CASE_TERM `!t n next env envs d d2 ds.
   source_to_flat_compile_decs t n next env envs (CONS d (CONS d2 ds)) =
   (match source_to_flat_compile_decs t n next env envs [d] with
      (n', next1, new_env1, envs1, d') ->
        (match source_to_flat_compile_decs t n' next1 (extend_env new_env1 env) envs1
                 (CONS d2 ds) with
           (n'', next2, new_env2, envs2, ds') ->
             (n'', next2, extend_env new_env2 new_env1, envs2, APPEND d' ds')))`,
  REPEAT GEN_TAC THEN CASES_ON `d:dec` THEN
  GEN_REWRITE_TAC LAND_CONV [source_to_flat_compile_decs_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;
let FLATP2AUX_lift_env_props = prove
 (`!genv cm (e:v sem_env) mn.
     (env_domain_eq cm e
      ==> env_domain_eq (lift_env mn cm) (sem_env_REC (nsLift mn (sem_env_v e))
                                                      (nsLift mn (sem_env_c e)))) /\
     (global_env_inv genv cm {} e
      ==> global_env_inv genv (lift_env mn cm) {} (sem_env_REC (nsLift mn (sem_env_v e))
                                                              (nsLift mn (sem_env_c e))))`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[env_domain_eq_def; lift_env_def; nsDom_nsLift; nsDomMod_nsLift;
                source_to_flat_environment_INFO.ri_accessors; sem_env_INFO.ri_accessors] THEN
    SIMP_TAC[];
    REWRITE_TAC[v_rel_global_eqn; lift_env_def; nsLookup_nsLift;
                source_to_flat_environment_INFO.ri_accessors; sem_env_INFO.ri_accessors;
                NOT_IN_EMPTY; IMAGE_CLAUSES] THEN
    STRIP_TAC THEN CONJ_TAC THEN GEN_TAC THEN CASES_ON `x:(modN,varN)id` THEN
    TRY(CASES_ON `x:(modN,conN)id`) THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "option"] THEN COND_CASES_TAC THEN
    REWRITE_TAC[distinctness "option"] THEN ASM_MESON_TAC[]]);;
let FLATP2AUX_simple_dlet_SOME = prove
 (`!p e pv vn. simple_dlet p e = SOME (pv, vn) <=> p = Pvar pv /\ e = Var vn`,
  REPEAT GEN_TAC THEN CASES_ON `p:pat` THEN REWRITE_TAC[simple_dlet_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"; distinctness "pat"] THEN
  CASES_ON `e:exp` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; distinctness "exp"; injectivity "option";
              injectivity "pat"; injectivity "exp"; PAIR_EQ]);;

let FLATP2AUX_result_rel_Rerr = prove
 (`!f genv e r. source_to_flatProof_result_rel (f:global_env->A->B->bool) genv
                  (Rerr e:(A,v)result) r
                ==> ?e'. r = Rerr e'`,
  REPEAT GEN_TAC THEN CASES_ON `e:(v)error_result` THEN
  REWRITE_TAC[result_rel_eqns] THEN MESON_TAC[]);;

let FLATP2AUX_result_rel_Rval = prove
 (`!f genv v r. source_to_flatProof_result_rel (f:global_env->A->B->bool) genv
                  (Rval v:(A,v)result) r
                ==> ?v'. r = Rval v' /\ f genv v v'`,
  REWRITE_TAC[result_rel_eqns] THEN MESON_TAC[]);;

let FLATP2AUX_env_all_rel_nil = prove
 (`!genv comp_map (env:v sem_env).
     global_env_inv genv comp_map {} env
     ==> env_all_rel genv comp_map env (flat_environment_REC [] :(flat_v)flat_environment) []`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[env_all_rel_cases] THEN
  MAP_EVERY EXISTS_TAC [`alist_to_ns [] :(modN,varN,v)namespace`; `env:v sem_env`;
                        `[]:(varN#flat_v)list`] THEN
  ASM_REWRITE_TAC[alist_to_ns_nil; nsAppend_nsEmpty; MAP; set_of_list;
                  source_to_flatProof_v_rel_rules] THEN
  REWRITE_TAC[(record_info "sem_env").ri_component_equality] THEN SIMP_NOASM[]);;

let FLATP2AUX_result_rel_Rerr_f = prove
 (`!f g genv e e'.
     source_to_flatProof_result_rel (f:global_env->X->Y->bool) genv
       (Rerr e:(X,v)result) (Rerr e':(Y,flat_v)result)
     ==> source_to_flatProof_result_rel (g:global_env->Z->W->bool) genv
           (Rerr e:(Z,v)result) (Rerr e':(W,flat_v)result)`,
  REPEAT GEN_TAC THEN CASES_ON `e:(v)error_result` THEN
  REWRITE_TAC[result_rel_eqns; injectivity "result"; distinctness "result";
              injectivity "error_result"; distinctness "error_result"] THEN
  MESON_TAC[]);;

let FLATP2AUX_bind_locals_nil = prove
 (`!comp_map. source_to_flat_environment_v_fupd
                (K (bind_locals [] [] (source_to_flat_environment_v comp_map))) comp_map =
              comp_map`,
  REWRITE_TAC[bind_locals_def; MAP2; nsBindList_def; ITLIST;
              (record_info "source_to_flat_environment").ri_component_equality] THEN
  SIMP_NOASM[]);;

let FLATP2AUX_flat_decs_sing = prove
 (CASE_TERM `!(s:(C,FFI)flat_state) d.
     flat_evaluate_decs s [d] =
     (match flat_evaluate (flat_environment_REC [] :(flat_v)flat_environment) s [d] with
        (s', Rval x) -> if x = [Unitv] then (s', NONE) else (s', SOME (Rabort Rtype_error))
      | (s', Rerr e) -> (s', SOME e))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flat_evaluate_def] THEN
  MP_TAC(ISPEC `flat_evaluate (flat_environment_REC [] :(flat_v)flat_environment) (s:(C,FFI)flat_state) [d]`
    PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(C,FFI)flat_state` (X_CHOOSE_THEN `r1:(flat_v list,flat_v)result`
    SUBST1_TAC)) THEN
  CASES_ON `r1:(flat_v list,flat_v)result` THEN CASE_REWRITE_TAC[] THEN
  TRY COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[flat_evaluate_def]);;

let FLATP2AUX_env_domain_eq_alist = prove
 (`!l1 (l2:(varN#A)list).
     set_of_list (MAP FST l1) = set_of_list (MAP FST l2)
     ==> env_domain_eq (source_to_flat_environment_REC nsEmpty (alist_to_ns l1))
                       (sem_env_REC (alist_to_ns l2) nsEmpty)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[env_domain_eq_def] THEN
  SIMP_NOASM[nsDom_alist_to_ns; nsDomMod_alist_to_ns] THEN
  REWRITE_TAC[MAP_o] THEN ONCE_REWRITE_TAC[SET_OF_LIST_MAP] THEN ASM_REWRITE_TAC[]);;

let FLATP2AUX_env_rel_dom_alist = prove
 (`!genv (l:(varN#v)list) env'.
     source_to_flatProof_env_rel genv (alist_to_ns l) env' ==> MAP FST l = MAP FST env'`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP env_rel_dom) THEN
  REWRITE_TAC[alist_to_ns_def; injectivity "namespace"] THEN MESON_TAC[]);;

let FLATP2AUX_MAP2_REPLICATE = prove
 (`!(f:A->B->C) c l. MAP2 f (REPLICATE (LENGTH l) c) l = MAP (f c) l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; REPLICATE; MAP2; MAP]);;
let FLATP2AUX_v_rel_Recclosure_top = prove
 (`!genv comp_map env funs t x.
     global_env_inv genv comp_map {} env
     ==> source_to_flatProof_v_rel genv (Recclosure env funs x)
           (flat_Recclosure (flat_environment_REC [] :(flat_v)flat_environment)
              (compile_funs t (source_to_flat_environment_v_fupd
                 (K (nsBindList (MAP (\x. (x, source_to_flat_Local backend_common_None x))
                                     (MAP FST funs))
                       (source_to_flat_environment_v comp_map))) comp_map) funs) x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`genv:global_env`; `comp_map:source_to_flat_environment`; `env:v sem_env`;
    `nsEmpty:(modN,varN,v)namespace`; `funs:(varN#varN#exp)list`; `x:varN`;
    `flat_environment_REC [] :(flat_v)flat_environment`; `t:mlstring list`;
    `REPLICATE (LENGTH (MAP FST (funs:(varN#varN#exp)list))) backend_common_None`]
    (el 4 (CONJUNCTS source_to_flatProof_v_rel_rules))) THEN
  REWRITE_TAC[flat_environment_INFO.ri_accessors; MAP; APPEND_NIL; set_of_list;
              nsAppend_nsEmpty; FLATP2AUX_record_etas; bind_locals_def;
              FLATP2AUX_MAP2_REPLICATE] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_REPLICATE; LENGTH_MAP; LENGTH; ADD_CLAUSES;
                  source_to_flatProof_v_rel_rules]);;

let FLATP2AUX_idx_block_exn = prove
 (`!idx end_idx.
     idx_block (next_indices_eidx_fupd (K (next_indices_eidx idx + 1)) idx) end_idx =
     idx_block idx end_idx DIFF {(next_indices_eidx idx, Idx_Exn)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[idx_block_def; EXTENSION; IN_DIFF; IN_UNION; IN_SING;
    IN_ELIM_THM; FORALL_PAIR_THM; PAIR_EQ] THEN
  SIMP_NOASM[] THEN REPEAT GEN_TAC THEN
  CASES_ON `p2:idx_types` THEN REWRITE_TAC[distinctness "idx_types"] THEN ARITH_TAC);;
let FLATP2AUX_genv_alloc_exn = prove
 (`!genv e a st.
     genv_allocated_idxs (global_env_c_fupd
        (K (FUNION (global_env_c genv) (FEMPTY |+ (((e, NONE), a), st)))) genv) =
     genv_allocated_idxs genv UNION {(e, Idx_Exn)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[genv_allocated_idxs_def; EXTENSION; IN_UNION; IN_SING;
    IN_ELIM_THM; FORALL_PAIR_THM; PAIR_EQ] THEN
  SIMP_NOASM[FDOM_FUNION; FDOM_FUPDATE; FDOM_FEMPTY; IN_UNION; IN_INSERT; NOT_IN_EMPTY;
             PAIR_EQ; distinctness "option"] THEN
  REPEAT GEN_TAC THEN CASES_ON `p2:idx_types` THEN REWRITE_TAC[distinctness "idx_types"] THEN
  MESON_TAC[]);;

let FLATP2AUX_FRANGE_FUNION_UPDATE = prove
 (`!(c:(A,B)fmap) k v x. x IN FRANGE (FUNION c (FEMPTY |+ (k, v))) ==> x IN FRANGE c \/ x = v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRANGE_FLOOKUP; FLOOKUP_FUNION; FLOOKUP_UPDATE; FLOOKUP_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `k':A` MP_TAC) THEN
  MP_TAC(ISPEC `FLOOKUP (c:(A,B)fmap) k'` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `y:B` (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
  CASE_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN MESON_TAC[];
    REWRITE_TAC[injectivity "option"] THEN ASM_MESON_TAC[]]);;

let FLATP2AUX_idx_range_exn = prove
 (`!interp genv nts nes ev idx end_idx os a.
     idx_range_rel (interp:(v->(source_to_flat_config#C)option)option) genv nts nes ev
       (idx, end_idx, os) /\
     next_indices_eidx idx < next_indices_eidx end_idx
     ==> idx_range_rel interp
           (global_env_c_fupd (K (FUNION (global_env_c genv)
              (FEMPTY |+ (((next_indices_eidx idx, NONE), a), ExnStamp nes)))) genv)
           nts (nes + 1) ev
           (next_indices_eidx_fupd (K (next_indices_eidx idx + 1)) idx, end_idx, os)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[idx_range_rel_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (FLATP2AUX_CHOOSE_THEN [`i0:next_indices`; `e0:next_indices`; `fin:next_indices`;
       `ob:num#idx_types->bool`]
       (FLATP2AUX_LABEL_CONJS ["eq"; "fin"; "prev"; "disj"; "ts"; "en"]))
    (LABEL_TAC "lt")) THEN
  REMOVE_THEN "eq" (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM)
         (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM))) THEN
  MAP_EVERY EXISTS_TAC [`next_indices_eidx_fupd (K (next_indices_eidx idx + 1)) idx`;
    `end_idx:next_indices`; `fin:next_indices`; `os:num#idx_types->bool`] THEN
  FLATP2AUX_LREWRITE_TAC ["fin"; "prev"] [FLATP2AUX_idx_block_exn; FLATP2AUX_genv_alloc_exn] THEN
  REWRITE_TAC[global_env_INFO.ri_accfupds; K_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ALL_DISJOINT_MOVE THEN
    MAP_EVERY EXISTS_TAC [`0`; `3`; `{(next_indices_eidx idx, Idx_Exn)}`;
      `[idx_block idx end_idx; idx_final_block fin; os; genv_allocated_idxs genv]`] THEN
    FLATP2AUX_LREWRITE_TAC ["disj"] [LENGTH] THEN
    CONV_TAC(DEPTH_CONV EL_CONV) THEN
    REPEAT(CHANGED_TAC(REWRITE_TAC[LUPDATE_compute] THEN CONV_TAC NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[SING_SUBSET; idx_block_def; IN_UNION; IN_ELIM_THM; PAIR_EQ;
                distinctness "idx_types"] THEN
    USE_THEN "lt" MP_TAC THEN MESON_TAC[LE_REFL];
    MAP_EVERY X_GEN_TAC [`cn:mlstring`; `t:num`] THEN DISCH_THEN(LABEL_TAC "ge") THEN
    DISCH_THEN(DISJ_CASES_THEN2 (LABEL_TAC "inr") (LABEL_TAC "eqs") o
               MATCH_MP FLATP2AUX_FRANGE_FUNION_UPDATE) THENL
     [USE_THEN "ts" (MP_TAC o SPECL [`cn:mlstring`; `t:num`]) THEN
      FLATP2AUX_LREWRITE_TAC ["ge"; "inr"] [];
      USE_THEN "eqs" MP_TAC THEN REWRITE_TAC[distinctness "stamp"]];
    X_GEN_TAC `cn:num` THEN DISCH_THEN(LABEL_TAC "ge") THEN
    DISCH_THEN(DISJ_CASES_THEN2 (LABEL_TAC "inr") (LABEL_TAC "eqs") o
               MATCH_MP FLATP2AUX_FRANGE_FUNION_UPDATE) THENL
     [USE_THEN "en" (MP_TAC o SPEC `cn:num`) THEN FLATP2AUX_LREWRITE_TAC ["inr"] [] THEN
      USE_THEN "ge" MP_TAC THEN ARITH_TAC;
      USE_THEN "eqs" MP_TAC THEN REWRITE_TAC[injectivity "stamp"] THEN
      USE_THEN "ge" MP_TAC THEN ARITH_TAC]]);;

let FLATP2AUX_genv_c_ok_exn = prove
 (`!c e a n.
     genv_c_ok c /\ ~(ExnStamp n IN FRANGE c)
     ==> genv_c_ok (FUNION c (FEMPTY |+ (((e, NONE), a), ExnStamp n)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC genv_c_ok_extend THEN
  ASM_REWRITE_TAC[FLOOKUP_UPDATE; FLOOKUP_EMPTY; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`cn:ctor_id#type_id`; `arity:num`; `stamp:stamp`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  POP_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[same_type_def; SND] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`cn':ctor_id#type_id`; `arity':num`; `stamp':stamp`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
    POP_ASSUM(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[same_type_def; flat_ctor_same_type_def];
    MAP_EVERY X_GEN_TAC [`cn':ctor_id#type_id`; `arity':num`; `stamp':stamp`] THEN
    DISCH_TAC THEN REWRITE_TAC[distinctness "stamp"] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[FRANGE_FLOOKUP] THEN ASM_MESON_TAC[]]);;
let FLATP2AUX_genv_c_tys_ok_exn = prove
 (`!c tys e a s.
     genv_c_tys_ok c tys ==> genv_c_tys_ok (FUNION c (FEMPTY |+ (((e, NONE), a), s))) tys`,
  REWRITE_TAC[genv_c_tys_ok_def; FDOM_FUNION; FDOM_FUPDATE; FDOM_FEMPTY; IN_UNION; IN_INSERT;
              NOT_IN_EMPTY; PAIR_EQ; distinctness "option"] THEN MESON_TAC[]);;
let FLATP2AUX_global_env_inv_exn = prove
 (`!genv cn e a n.
     FLOOKUP (global_env_c genv) ((e, NONE), a) = SOME (ExnStamp n)
     ==> global_env_inv genv (source_to_flat_environment_REC (nsSing cn (e, NONE)) nsEmpty) {}
           (sem_env_REC nsEmpty (nsSing cn (a, ExnStamp n)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[v_rel_global_eqn] THEN
  SIMP_NOASM[nsLookup_nsEmpty; nsLookup_nsSing; distinctness "option"] THEN
  FIRST_ASSUM ACCEPT_TAC);;
let FLATP2AUX_env_domain_eq_sing = prove
 (`!cn (x:num#type_group_id) (y:num#stamp).
     env_domain_eq (source_to_flat_environment_REC (nsSing cn x) nsEmpty)
                   (sem_env_REC (nsEmpty:(modN,varN,v)namespace) (nsSing cn y))`,
  REWRITE_TAC[env_domain_eq_def; nsDom_def; nsDomMod_def; EXTENSION; IN_ELIM_THM] THEN
  SIMP_NOASM[nsLookup_nsSing; nsLookupMod_nsSing; nsLookup_nsEmpty] THEN
  X_GEN_TAC `x:modN list` THEN STRUCT_CASES_TAC(ISPEC `x:modN list` list_CASES) THEN
  REWRITE_TAC[nsLookupMod_nsEmpty; nsLookupMod_def; nsEmpty_def; distinctness "option"] THEN
  MESON_TAC[]);;


let FLATP2AUX_alloc_tags_SUC = prove
 (`!t. (\tid (a:tvarN list,b:mlstring,constrs:(mlstring # ast_t list) list).
           alloc_tags (t + tid) constrs) o SUC =
       (\tid (a,b,constrs). alloc_tags ((t + 1) + tid) constrs)`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `t + SUC x = (t + 1) + x`]);;
let FLATP2AUX_next_indices_eta = prove
 (`!idx. next_indices_tidx_fupd (K (next_indices_tidx idx)) idx = idx`,
  REWRITE_TAC[(record_info "next_indices").ri_component_equality] THEN SIMP_NOASM[]);;
let FLATP2AUX_state_nts_eta = prove
 (`!st:(FFI)state. state_next_type_stamp_fupd (K (state_next_type_stamp st)) st = st`,
  REWRITE_TAC[(record_info "state").ri_component_equality] THEN SIMP_NOASM[]);;

let FLATP2AUX_dtype_ind = prove
 (`!interp g gen end_idx os s_i1 comp_map env tds idx (st:(FFI)state) genv.
     invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv
       (idx, end_idx, os) st (s_i1:(C,FFI)flat_state) /\
     global_env_inv genv comp_map {} env /\
     ALL check_dup_ctors tds /\
     next_indices_tidx idx + LENGTH tds <= next_indices_tidx end_idx
     ==> ?genv'.
           global_env_c genv SUBMAP global_env_c genv' /\
           global_env_tys genv SUBMAP global_env_tys genv' /\
           global_env_v genv' = global_env_v genv /\
           invariant interp g gen genv'
             (next_indices_tidx_fupd (K (next_indices_tidx idx + LENGTH tds)) idx, end_idx, os)
             (state_next_type_stamp_fupd (K (state_next_type_stamp st + LENGTH tds)) st) s_i1 /\
           global_env_inv genv'
             (source_to_flat_environment_REC
                (FOLDL (\ns (l,cids). nsAppend l ns) nsEmpty
                   (MAPi (\tid (a,b,constrs). alloc_tags (next_indices_tidx idx + tid) constrs)
                      tds)) nsEmpty) {}
             (sem_env_REC nsEmpty (build_tdefs (state_next_type_stamp st) tds)) /\
           env_domain_eq
             (source_to_flat_environment_REC
                (FOLDL (\ns (l,cids). nsAppend l ns) nsEmpty
                   (MAPi (\tid (a,b,constrs). alloc_tags (next_indices_tidx idx + tid) constrs)
                      tds)) nsEmpty)
             (sem_env_REC (nsEmpty:(modN,varN,v)namespace)
                (build_tdefs (state_next_type_stamp st) tds))`,
  (MAP_EVERY X_GEN_TAC [`interp:(v->(source_to_flat_config#C)option)option`;
    `g:dec list->dec list`; `gen:environment_generation_store`; `end_idx:next_indices`;
    `os:num#idx_types->bool`; `s_i1:(C,FFI)flat_state`; `comp_map:source_to_flat_environment`;
    `env:v sem_env`] THEN
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `genv:global_env` THEN
    REWRITE_TAC[SUBMAP_REFL; LENGTH; ADD_CLAUSES; FLATP2AUX_next_indices_eta;
                FLATP2AUX_state_nts_eta; MAPi_DEF; FOLDL; build_tdefs_def] THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_NOASM[v_rel_global_eqn; env_domain_eq_def; alist_to_ns_nil; nsLookup_nsEmpty;
               nsDom_nsEmpty; nsDomMod_nsEmpty; distinctness "option"];
    ALL_TAC]) THEN
  (POP_ASSUM(LABEL_TAC "ih") THEN
  MP_TAC(ISPEC `h:tvarN list # mlstring # (mlstring # ast_t list) list`
    (prove(`!x:A#B#C. ?a b c. x = (a,b,c)`, REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[]))) THEN
  DISCH_THEN(X_CHOOSE_THEN `tvs:tvarN list` (X_CHOOSE_THEN `tn:mlstring`
    (X_CHOOSE_THEN `ctors:(mlstring # ast_t list) list` SUBST_ALL_TAC))) THEN
  MAP_EVERY X_GEN_TAC [`idx:next_indices`; `st:(FFI)state`; `genv:global_env`] THEN
  REWRITE_TAC[ALL; LENGTH; source_evalProof_check_dup_ctors_thm] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["inv"; "gei"; "cd"; "tle"]) THEN
  REMOVE_THEN "cd" (CONJUNCTS_THEN2 (LABEL_TAC "dist") (LABEL_TAC "dall")) THEN
  REWRITE_TAC[MAPi_DEF; FOLDL; build_tdefs_def; ADD_CLAUSES] THEN CASE_REWRITE_TAC[] THEN
  FLATP2AUX_PAIR_TAC `alloc_tags (next_indices_tidx idx) (ctors:(mlstring # ast_t list) list)`
    `ns1:(modN,conN,num#type_group_id)namespace` `cids1:num spt` "at" THEN
  FLATP2AUX_LREWRITE_TAC ["at"] [] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[nsAppend_nsEmpty] THEN
  MP_TAC(ISPECL [`idx:next_indices`; `ctors:(mlstring # ast_t list) list`;
    `ns1:(modN,conN,num#type_group_id)namespace`; `cids1:num spt`;
    `interp:(v->(source_to_flat_config#C)option)option`; `g:dec list->dec list`;
    `gen:environment_generation_store`; `genv:global_env`; `end_idx:next_indices`;
    `os:num#idx_types->bool`; `st:(FFI)state`; `s_i1:(C,FFI)flat_state`;
    `comp_map:source_to_flat_environment`; `env:v sem_env`] alloc_tags_invariant) THEN
  ANTS_TAC THENL
   [FLATP2AUX_LREWRITE_TAC ["at"; "inv"; "gei"; "dist"] [] THEN USE_THEN "tle" MP_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `genv1:global_env`
    (FLATP2AUX_LABEL_CONJS ["sc1"; "sy1"; "sv1"; "inv1"; "bl1"])) THEN
  REMOVE_THEN "bl1" (CONJUNCTS_THEN2 (LABEL_TAC "gi1") (LABEL_TAC "ed1") o
                     CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  USE_THEN "ih" (MP_TAC o SPECL [`next_indices_tidx_fupd (K (next_indices_tidx idx + 1)) idx`;
    `state_next_type_stamp_fupd (K (state_next_type_stamp st + 1)) (st:(FFI)state)`;
    `genv1:global_env`]) THEN
  REWRITE_TAC[next_indices_INFO.ri_accfupds; next_indices_INFO.ri_fupdfupds;
              state_INFO.ri_accfupds; state_INFO.ri_fupdfupds; K_THM; K_o_THM] THEN
  ANTS_TAC THENL
   [FLATP2AUX_LREWRITE_TAC ["inv1"; "dall"] [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC global_env_inv_weak THEN EXISTS_TAC `genv:global_env` THEN
      FLATP2AUX_LREWRITE_TAC ["gei"; "sc1"; "sy1"; "sv1"] [subglobals_refl];
      USE_THEN "tle" MP_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `genv2:global_env`
    (FLATP2AUX_LABEL_CONJS ["sc2"; "sy2"; "sv2"; "inv2"; "gi2"; "ed2"])) THEN
  EXISTS_TAC `genv2:global_env` THEN
  REWRITE_TAC[ARITH_RULE `SUC (a + b) = (a + 1) + b`; FLATP2AUX_alloc_tags_SUC] THEN
  ONCE_REWRITE_TAC[nsAppend_foldl] THEN
  REWRITE_TAC[GSYM extend_env_v_empty; GSYM extend_dec_env_v_empty] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBMAP_TRANS THEN EXISTS_TAC `global_env_c genv1` THEN
    FLATP2AUX_LREWRITE_TAC ["sc1"; "sc2"] [];
    MATCH_MP_TAC SUBMAP_TRANS THEN EXISTS_TAC `global_env_tys genv1` THEN
    FLATP2AUX_LREWRITE_TAC ["sy1"; "sy2"] [];
    FLATP2AUX_LREWRITE_TAC ["sv1"; "sv2"] [];
    FLATP2AUX_LREWRITE_TAC ["inv2"] [];
    MATCH_MP_TAC global_env_inv_append THEN FLATP2AUX_LREWRITE_TAC ["ed2"; "gi2"] [] THEN
    MATCH_MP_TAC global_env_inv_weak THEN EXISTS_TAC `genv1:global_env` THEN
    FLATP2AUX_LREWRITE_TAC ["gi1"; "sc2"; "sy2"; "sv2"] [subglobals_refl];
    MATCH_MP_TAC env_domain_eq_append THEN FLATP2AUX_LREWRITE_TAC ["ed2"; "ed1"] []]));;

let FLATP2AUX_evaluate_global_init = prove
 (`!s:(C,FFI)flat_state n gen id.
     n < LENGTH (flat_state_globals s) /\ EL n (flat_state_globals s) = NONE
     ==> flat_evaluate_decs s [flat_App backend_common_None (GlobalVarInit n)
                                 [env_id_tuple gen id]] =
         (flat_state_globals_fupd (K (LUPDATE (SOME (flat_Conv NONE
            [flat_Litv (IntLit (&gen)); flat_Litv (IntLit (&id))])) n (flat_state_globals s))) s,
          NONE)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[env_id_tuple_def] THEN
  FS[flat_evaluate_def; REVERSE; APPEND; flat_do_app_def; HD; IS_NONE_DEF;
       flat_Unitv_def; list_result_def]);;

let FLATP2AUX_idx_block_var = prove
 (`!idx end_idx.
     idx_block (next_indices_vidx_fupd (K (next_indices_vidx idx + 1)) idx) end_idx =
     idx_block idx end_idx DIFF {(next_indices_vidx idx, Idx_Var)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[idx_block_def; EXTENSION; IN_DIFF; IN_UNION; IN_SING;
    IN_ELIM_THM; FORALL_PAIR_THM; PAIR_EQ] THEN
  SIMP_NOASM[] THEN REPEAT GEN_TAC THEN
  CASES_ON `p2:idx_types` THEN REWRITE_TAC[distinctness "idx_types"] THEN ARITH_TAC);;
let FLATP2AUX_genv_alloc_var = prove
 (`!genv i x.
     i < LENGTH (global_env_v genv)
     ==> genv_allocated_idxs (global_env_v_fupd (K (LUPDATE (SOME x) i (global_env_v genv))) genv) =
         genv_allocated_idxs genv UNION {(i, Idx_Var)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[genv_allocated_idxs_def; EXTENSION; IN_UNION; IN_SING; IN_ELIM_THM;
    FORALL_PAIR_THM; PAIR_EQ] THEN
  SIMP_NOASM[LENGTH_LUPDATE; EL_LUPDATE] THEN
  REPEAT GEN_TAC THEN CASES_ON `p2:idx_types` THEN REWRITE_TAC[distinctness "idx_types"] THEN
  ASM_CASES_TAC `p1:num = i` THEN ASM_REWRITE_TAC[distinctness "option"] THEN
  MESON_TAC[]);;
let FLATP2AUX_idx_range_var_fresh = prove
 (`!interp genv nts nes ev idx end_idx os len.
     idx_range_rel (interp:(v->(source_to_flat_config#C)option)option) genv nts nes ev
       (idx, end_idx, os) /\
     next_indices_vidx idx < next_indices_vidx end_idx /\
     fin_idx_match len end_idx (src_orac_next_cfg interp ev)
     ==> next_indices_vidx idx < len /\
         (next_indices_vidx idx < LENGTH (global_env_v genv)
          ==> EL (next_indices_vidx idx) (global_env_v genv) = NONE)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[idx_range_rel_def; PAIR_EQ])
    (CONJUNCTS_THEN2 (LABEL_TAC "lt") (LABEL_TAC "fm"))) THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`i0:next_indices`; `e0:next_indices`; `fin:next_indices`;
       `ob:num#idx_types->bool`]
       (FLATP2AUX_LABEL_CONJS ["eq"; "fin"; "prev"; "disj"; "ts"; "en"])) THEN
  REMOVE_THEN "eq" (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM)
         (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM))) THEN
  CONJ_TAC THENL
   [USE_THEN "fm" MP_TAC THEN USE_THEN "fin" MP_TAC THEN USE_THEN "prev" MP_TAC THEN
    REWRITE_TAC[fin_idx_match_def; idx_prev_def] THEN
    CASES_ON `src_orac_next_cfg (interp:(v->(source_to_flat_config#C)option)option) ev` THEN
    CASE_REWRITE_TAC[] THENL
     [USE_THEN "lt" MP_TAC THEN ARITH_TAC;
      DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN USE_THEN "lt" MP_TAC THEN
      POP_ASSUM MP_TAC THEN ARITH_TAC];
    DISCH_TAC THEN
    USE_THEN "disj" (MP_TAC o SPECL [`0`; `3`] o REWRITE_RULE[ALL_DISJOINT_DEF]) THEN
    REWRITE_TAC[LENGTH] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `(next_indices_vidx idx, Idx_Var)`) THEN
    REWRITE_TAC[idx_block_def; genv_allocated_idxs_def; IN_UNION; IN_ELIM_THM; PAIR_EQ;
                distinctness "idx_types"] THEN
    POP_ASSUM MP_TAC THEN USE_THEN "lt" MP_TAC THEN MESON_TAC[LE_REFL]]);;

let FLATP2AUX_idx_range_var = prove
 (`!interp genv nts nes ev ev' idx end_idx os x.
     idx_range_rel (interp:(v->(source_to_flat_config#C)option)option) genv nts nes ev
       (idx, end_idx, os) /\
     next_indices_vidx idx < next_indices_vidx end_idx /\
     next_indices_vidx idx < LENGTH (global_env_v genv) /\
     src_orac_next_cfg interp ev' = src_orac_next_cfg interp ev
     ==> idx_range_rel interp
           (global_env_v_fupd (K (LUPDATE (SOME x) (next_indices_vidx idx) (global_env_v genv)))
              genv) nts nes ev'
           (next_indices_vidx_fupd (K (next_indices_vidx idx + 1)) idx, end_idx, os)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[idx_range_rel_def; PAIR_EQ])
    (FLATP2AUX_LABEL_CONJS ["lt"; "lv"; "nc"])) THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`i0:next_indices`; `e0:next_indices`; `fin:next_indices`;
       `ob:num#idx_types->bool`]
       (FLATP2AUX_LABEL_CONJS ["eq"; "fin"; "prev"; "disj"; "ts"; "en"])) THEN
  REMOVE_THEN "eq" (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM)
         (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM))) THEN
  REWRITE_TAC[idx_range_rel_def; PAIR_EQ] THEN
  MAP_EVERY EXISTS_TAC [`next_indices_vidx_fupd (K (next_indices_vidx idx + 1)) idx`;
    `end_idx:next_indices`; `fin:next_indices`; `os:num#idx_types->bool`] THEN
  USE_THEN "lv" (fun th -> REWRITE_TAC[MATCH_MP FLATP2AUX_genv_alloc_var th]) THEN
  FLATP2AUX_LREWRITE_TAC ["nc"; "fin"; "prev"; "ts"; "en"] [FLATP2AUX_idx_block_var] THEN
  REWRITE_TAC[global_env_INFO.ri_accfupds] THEN
  FLATP2AUX_LREWRITE_TAC ["ts"; "en"] [] THEN
  MATCH_MP_TAC ALL_DISJOINT_MOVE THEN
  MAP_EVERY EXISTS_TAC [`0`; `3`; `{(next_indices_vidx idx, Idx_Var)}`;
    `[idx_block idx end_idx; idx_final_block fin; os; genv_allocated_idxs genv]`] THEN
  FLATP2AUX_LREWRITE_TAC ["disj"] [LENGTH] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REPEAT(CHANGED_TAC(REWRITE_TAC[LUPDATE_compute] THEN CONV_TAC NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[SING_SUBSET; idx_block_def; IN_UNION; IN_ELIM_THM; PAIR_EQ;
              distinctness "idx_types"] THEN
  USE_THEN "lt" MP_TAC THEN MESON_TAC[LE_REFL]);;

let FLATP2AUX_subglobals_LUPDATE_NONE = prove
 (`!(g:(A option)list) i x.
     i < LENGTH g /\ EL i g = NONE ==> subglobals g (LUPDATE (SOME x) i g)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "il") (LABEL_TAC "en")) THEN
  REWRITE_TAC[subglobals_def; LENGTH_LUPDATE; LE_REFL] THEN
  X_GEN_TAC `k:num` THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "kl") (LABEL_TAC "is")) THEN
  REWRITE_TAC[EL_LUPDATE] THEN ASM_CASES_TAC `k:num = i` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN USE_THEN "is" MP_TAC THEN
    FLATP2AUX_LREWRITE_TAC ["en"] [IS_SOME_DEF];
    ASM_REWRITE_TAC[]]);;
let FLATP2AUX_env_domain_eq_sing_v = prove
 (`!n (x:var_name) (y:v).
     env_domain_eq (source_to_flat_environment_REC nsEmpty (nsSing n x))
                   (sem_env_REC (nsSing n y) nsEmpty)`,
  REWRITE_TAC[env_domain_eq_def; nsDom_def; nsDomMod_def; EXTENSION; IN_ELIM_THM] THEN
  SIMP_NOASM[nsLookup_nsSing; nsLookupMod_nsSing; nsLookup_nsEmpty] THEN
  X_GEN_TAC `x':modN list` THEN STRUCT_CASES_TAC(ISPEC `x':modN list` list_CASES) THEN
  REWRITE_TAC[nsLookupMod_nsEmpty; nsLookupMod_def; nsEmpty_def; distinctness "option"] THEN
  MESON_TAC[]);;
let FLATP2AUX_eval_ref_inv_LUPDATE = prove
 (`!gs rs i (x:flat_v option).
     eval_ref_inv (TAKE 1 gs) (TAKE 1 rs) /\ ~(i = 0)
     ==> eval_ref_inv (TAKE 1 (LUPDATE x i gs)) (TAKE 1 rs)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `gs:(flat_v option)list` list_CASES) THEN
  STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[LUPDATE_def; NOT_SUC] THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; TAKE_def] THEN SIMP_NOASM[TAKE_def]);;

let FLATP2AUX_env_invs_declare = prove
 (`!interp genv genv' es (env:v sem_env) comp_map gen.
     src_orac_env_invs (interp:(v->(source_to_flat_config#C)option)option) genv
       (SOME (EvalOracle es)) /\
     env_gen_future_rel interp
       (environment_generation_store_envs_fupd
          (K (insert (environment_generation_store_next gen) comp_map
                (environment_generation_store_envs gen)))
          (environment_generation_store_next_fupd
             (K (environment_generation_store_next gen + 1)) gen))
       (SOME (EvalOracle es)) /\
     environment_generation_store_generation gen = eval_oracle_state_generation es /\
     eval_oracle_state_generation es < LENGTH (eval_oracle_state_envs es) /\
     environment_generation_store_next gen =
       LENGTH (EL (eval_oracle_state_generation es) (eval_oracle_state_envs es)) /\
     global_env_inv genv comp_map {} env /\
     global_env_c genv SUBMAP global_env_c genv' /\
     global_env_tys genv SUBMAP global_env_tys genv' /\
     subglobals (global_env_v genv) (global_env_v genv')
     ==> src_orac_env_invs interp genv'
           (SOME (EvalOracle (eval_oracle_state_envs_fupd
              (K (LUPDATE (APPEND (EL (eval_oracle_state_generation es)
                                      (eval_oracle_state_envs es)) [env])
                    (eval_oracle_state_generation es) (eval_oracle_state_envs es))) es)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ei"; "efr"; "eg1"; "eg2"; "eg3"; "gei"; "sc"; "sy"; "sg"]) THEN
  USE_THEN "ei" MP_TAC THEN REWRITE_TAC[src_orac_env_invs_def] THEN CASE_REWRITE_TAC[] THEN
  SIMP_NOASM[FLATP2AUX_invs_envs; LENGTH_LUPDATE] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:source_to_flat_config`
    (FLATP2AUX_LABEL_CONJS ["ncc"; "esi"; "esn"; "eenv"])) THEN
  EXISTS_TAC `c:source_to_flat_config` THEN FLATP2AUX_LREWRITE_TAC ["ncc"; "esi"; "esn"] [] THEN
  USE_THEN "efr" MP_TAC THEN REWRITE_TAC[env_gen_future_rel_def] THEN
  FLATP2AUX_LREWRITE_TAC ["ncc"] [] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[environment_generation_store_INFO.ri_accfupds; K_THM] THEN
  FLATP2AUX_LREWRITE_TAC ["eg1"] [] THEN
  DISCH_THEN(X_CHOOSE_THEN `gf:(source_to_flat_environment)spt`
    (CONJUNCTS_THEN2 (LABEL_TAC "lgf") (LABEL_TAC "sub"))) THEN
  MAP_EVERY X_GEN_TAC [`g_id:num`; `i_d:num`] THEN REWRITE_TAC[EL_LUPDATE] THEN
  FLATP2AUX_LREWRITE_TAC ["eg2"] [] THEN
  ASM_CASES_TAC `g_id = eval_oracle_state_generation es` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[LENGTH_APPEND; LENGTH; EL_APPEND] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gl") (LABEL_TAC "il")) THEN
    COND_CASES_TAC THENL
     [USE_THEN "eenv" (MP_TAC o SPECL [`eval_oracle_state_generation es`; `i_d:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `cmg:(source_to_flat_environment)spt`
        (X_CHOOSE_THEN `cm:source_to_flat_environment` (FLATP2AUX_LABEL_CONJS ["l1"; "l2"; "gi"]))) THEN
      MAP_EVERY EXISTS_TAC [`cmg:(source_to_flat_environment)spt`; `cm:source_to_flat_environment`] THEN
      FLATP2AUX_LREWRITE_TAC ["l1"; "l2"] [] THEN
      MATCH_MP_TAC global_env_inv_weak THEN EXISTS_TAC `genv:global_env` THEN
      FLATP2AUX_LREWRITE_TAC ["gi"; "sc"; "sy"; "sg"] [];
      SUBGOAL_THEN `i_d = LENGTH (EL (eval_oracle_state_generation es) (eval_oracle_state_envs es))`
        SUBST_ALL_TAC THENL
       [POP_ASSUM MP_TAC THEN USE_THEN "il" MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SUB_REFL; EL; HD] THEN
      MAP_EVERY EXISTS_TAC [`gf:(source_to_flat_environment)spt`; `comp_map:source_to_flat_environment`] THEN
      FLATP2AUX_LREWRITE_TAC ["lgf"] [] THEN CONJ_TAC THENL
       [USE_THEN "sub" (MP_TAC o REWRITE_RULE[subspt_lookup]) THEN
        DISCH_THEN MATCH_MP_TAC THEN FLATP2AUX_LREWRITE_TAC ["eg3"] [lookup_insert];
        MATCH_MP_TAC global_env_inv_weak THEN EXISTS_TAC `genv:global_env` THEN
        FLATP2AUX_LREWRITE_TAC ["gei"; "sc"; "sy"; "sg"] []]];
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "eenv" (MP_TAC o SPECL [`g_id:num`; `i_d:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `cmg:(source_to_flat_environment)spt`
      (X_CHOOSE_THEN `cm:source_to_flat_environment` (FLATP2AUX_LABEL_CONJS ["l1"; "l2"; "gi"]))) THEN
    MAP_EVERY EXISTS_TAC [`cmg:(source_to_flat_environment)spt`; `cm:source_to_flat_environment`] THEN
    FLATP2AUX_LREWRITE_TAC ["l1"; "l2"] [] THEN
    MATCH_MP_TAC global_env_inv_weak THEN EXISTS_TAC `genv:global_env` THEN
    FLATP2AUX_LREWRITE_TAC ["gi"; "sc"; "sy"; "sg"] []]);;

let FLATP2AUX_nsBind_nsEmpty_sing = prove
 (`!(n:N) (x:V). nsBind n x (nsEmpty:(M,N,V)namespace) = nsSing n x`,
  REWRITE_TAC[nsBind_def; nsEmpty_def; nsSing_def]);;

let FLATP2AUX_App_err = prove
 (`!(st:(FFI)state) env op es st1 err (env_i1:(flat_v)flat_environment) (s_i1:(C,FFI)flat_state)
     t cm s1_i1 err_i1.
     evaluate st env (REVERSE es) = (st1, Rerr err) /\
     flat_evaluate env_i1 s_i1 (source_to_flat_compile_exps t cm (REVERSE es)) =
       (s1_i1, Rerr err_i1)
     ==> evaluate st env [App op es] = (st1, Rerr err) /\
         flat_evaluate env_i1 s_i1 [source_to_flat_compile_exp t cm (App op es)] =
           (s1_i1, Rerr err_i1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ev") (LABEL_TAC "fe")) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[full_evaluate_def] THEN FLATP2AUX_LREWRITE_TAC ["ev"] [] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "fe" (LABEL_TAC "fe'" o REWRITE_RULE[compile_exps_reverse]) THEN
  REWRITE_TAC[source_to_flat_compile_exp_def] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC evaluate_foldr_let_err THEN FLATP2AUX_LREWRITE_TAC ["fe'"] []; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[flat_evaluate_def] THEN FLATP2AUX_LREWRITE_TAC ["fe'"] [] THEN
    CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MP_TAC(ISPEC `es:exp list` list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN `e1:exp` (X_CHOOSE_THEN `es1:exp list` SUBST_ALL_TAC))) THEN
    CASE_REWRITE_TAC[] THENL
     [USE_THEN "fe'" MP_TAC THEN
      REWRITE_TAC[source_to_flat_compile_exp_def; REVERSE] THEN
      REWRITE_TAC[flat_evaluate_def; PAIR_EQ; distinctness "result"];
      MP_TAC(ISPEC `es1:exp list` list_CASES) THEN
      DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
        (X_CHOOSE_THEN `e2:exp` (X_CHOOSE_THEN `es2:exp list` SUBST_ALL_TAC))) THEN
      CASE_REWRITE_TAC[] THENL
       [USE_THEN "fe'" MP_TAC THEN REWRITE_TAC[source_to_flat_compile_exp_def; REVERSE; APPEND] THEN
        CASE_REWRITE_TAC[];
        REWRITE_TAC[flat_evaluate_def] THEN FLATP2AUX_LREWRITE_TAC ["fe'"] [] THEN
        CASE_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[flat_evaluate_def] THEN FLATP2AUX_LREWRITE_TAC ["fe'"] [] THEN
  CASE_REWRITE_TAC[]);;

let FLATP2AUX_result_rel_list_result = prove
 (`!genv (r:(v,v)result) (r':(flat_v,flat_v)result).
     source_to_flatProof_result_rel source_to_flatProof_v_rel genv r r'
     ==> source_to_flatProof_result_rel (ALL2 o source_to_flatProof_v_rel) genv
           (list_result r) (list_result r')`,
  REPEAT GEN_TAC THEN CASES_ON `r:(v,v)result` THEN TRY(CASES_ON `a:(v)error_result`) THEN
  REWRITE_TAC[result_rel_eqns] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[list_result_def; result_rel_eqns; injectivity "result"; o_THM; ALL2] THEN
  FIRST [EXISTS_TAC `[v':flat_v]` THEN ASM_REWRITE_TAC[ALL2];
         EXISTS_TAC `v':flat_v` THEN ASM_REWRITE_TAC[]]);;

let FLATP2AUX_astOp_Src = prove
 (`!op x. astOp_to_flatOp op = Src x ==> x = op`,
  GEN_TAC THEN CASES_ON `op:op` THEN REWRITE_TAC[astOp_to_flatOp_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "flat_op"; distinctness "flat_op"] THEN
  MESON_TAC[]);;
let FLATP2AUX_astOp_simple = prove
 (`!op. getOpClass op = Simple
        ==> ~(astOp_to_flatOp op = Src Opapp) /\ ~(astOp_to_flatOp op = Src Eval) /\
            ~(astOp_to_flatOp op = Src (ThunkOp ForceThunk)) /\ ~(op = Eval) /\ ~(op = Opapp)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN
  TRY(DISCH_THEN(SUBST_ALL_TAC o SYM o MATCH_MP FLATP2AUX_astOp_Src)) THEN
  TRY(DISCH_THEN SUBST_ALL_TAC) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[getOpClass_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "op_class"]);;

let FLATP2AUX_App_simple = prove
 (`!interp g gen genv1 idxs (st:(FFI)state) env op es st1 vs
     (env_i1:(flat_v)flat_environment) (s_i1:(C,FFI)flat_state) t cm s1_i1 vs_i1 s' r.
     evaluate st env (REVERSE es) = (st1, Rval vs) /\
     evaluate st env [App op es] = (s', r) /\
     ~(r = Rerr (Rabort Rtype_error)) /\
     getOpClass op = Simple /\ ~(op = AallocEmpty) /\ ~(op = Env_id) /\
     flat_evaluate env_i1 s_i1 (source_to_flat_compile_exps t cm (REVERSE es)) =
       (s1_i1, Rval vs_i1) /\
     ALL2 (source_to_flatProof_v_rel genv1) vs vs_i1 /\
     invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv1 idxs st1 s1_i1
     ==> ?s'_i1 r_i1.
           flat_evaluate env_i1 s_i1 [source_to_flat_compile_exp t cm (App op es)] =
             (s'_i1, r_i1) /\
           source_to_flatProof_result_rel (ALL2 o source_to_flatProof_v_rel) genv1 r r_i1 /\
           source_to_flatProof_s_rel genv1 s' s'_i1 /\
           invariant interp g gen genv1 idxs s' s'_i1 /\
           state_eval_state s' = state_eval_state st1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev1"; "ev"; "nte"; "cls"; "na"; "ne"; "fe1"; "vr"; "inv"]) THEN
  REMOVE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  FLATP2AUX_LREWRITE_TAC ["ev1"; "cls"] [] THEN CASE_REWRITE_TAC[] THEN
  FLATP2AUX_OPTION_CASES_TAC `do_app (state_refs (st1:(FFI)state),state_ffi st1) op (REVERSE vs)`
    `res:((v store_v)list # (FFI)ffi_state) # (v,v)result` "da" THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THENL
   [DISCH_THEN(SUBST_ALL_TAC o SYM o CONJUNCT2) THEN USE_THEN "nte" MP_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `res:((v store_v)list # (FFI)ffi_state) # (v,v)result`
    (prove(`!x:(A#B)#C. ?a b c. x = ((a,b),c)`, REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[]))) THEN
  DISCH_THEN(X_CHOOSE_THEN `refs':(v store_v)list` (X_CHOOSE_THEN `ffi':(FFI)ffi_state`
    (X_CHOOSE_THEN `r0:(v,v)result` SUBST_ALL_TAC))) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  FLATP2AUX_INV_TAC "inv" THEN
  USE_THEN "s_rel" (FLATP2AUX_LABEL_CONJS ["nn"; "srf"; "scl"; "sff"] o
                    REWRITE_RULE[source_to_flatProof_s_rel_cases]) THEN
  MP_TAC(ISPECL [`genv1:global_env`; `(state_refs (st1:(FFI)state), state_ffi st1)`;
    `(refs':(v store_v)list, ffi':(FFI)ffi_state)`; `op:op`; `REVERSE (vs:v list)`;
    `r0:(v,v)result`; `s1_i1:(C,FFI)flat_state`; `REVERSE (vs_i1:flat_v list)`]
    source_to_flatProof_do_app) THEN
  ANTS_TAC THENL
   [FLATP2AUX_LREWRITE_TAC ["da"; "srf"; "nn"; "sff"; "c_ok"; "na"; "ne"] [FST; SND] THEN
    MATCH_MP_TAC EVERY2_REVERSE THEN FLATP2AUX_LREWRITE_TAC ["vr"] [];
    ALL_TAC] THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`r_i1:(flat_v,flat_v)result`; `s2_i1:(C,FFI)flat_state`]
    (FLATP2AUX_LABEL_CONJS ["srf2"; "nn2"; "sff2"; "gl2"; "tk2"; "rr"; "fda"])) THEN
  USE_THEN "cls" (FLATP2AUX_LABEL_CONJS ["n1"; "n2"; "n3"; "n4"; "n5"] o
                  MATCH_MP FLATP2AUX_astOp_simple) THEN
  EXISTS_TAC `s2_i1:(C,FFI)flat_state` THEN EXISTS_TAC `list_result (r_i1:(flat_v,flat_v)result)` THEN
  REWRITE_TAC[source_to_flat_compile_exp_def] THEN
  FLATP2AUX_LREWRITE_TAC ["na"; "n4"; "ne"] [] THEN
  REWRITE_TAC[flat_evaluate_def; GSYM compile_exps_reverse] THEN
  FLATP2AUX_LREWRITE_TAC ["fe1"] [] THEN CASE_REWRITE_TAC[] THEN
  FLATP2AUX_LREWRITE_TAC ["n1"; "n2"; "n3"; "fda"] [] THEN CASE_REWRITE_TAC[] THEN
  USE_THEN "rr" (fun th -> REWRITE_TAC[MATCH_MP FLATP2AUX_result_rel_list_result th]) THEN
  REWRITE_TAC[state_INFO.ri_accfupds] THEN
  SUBGOAL_THEN `source_to_flatProof_s_rel genv1
     (state_refs_fupd (K refs') (state_ffi_fupd (K ffi') (st1:(FFI)state))) (s2_i1:(C,FFI)flat_state)`
    (LABEL_TAC "sr2") THENL
   [REWRITE_TAC[source_to_flatProof_s_rel_cases; state_INFO.ri_accfupds; K_THM] THEN
    USE_THEN "srf2" (MP_TAC o REWRITE_RULE[FST]) THEN USE_THEN "sff2" (MP_TAC o REWRITE_RULE[SND]) THEN
    USE_THEN "fda" (MP_TAC o MATCH_MP flat_do_app_const) THEN
    FLATP2AUX_LREWRITE_TAC ["nn2"; "scl"] [] THEN MESON_TAC[];
    ALL_TAC] THEN
  FLATP2AUX_LREWRITE_TAC ["sr2"] [] THEN
  REWRITE_TAC[invariant_def; state_INFO.ri_accfupds] THEN
  USE_THEN "fda" (LABEL_TAC "dsu" o MATCH_MP do_app_state_unchanged) THEN
  FLATP2AUX_LREWRITE_TAC ["c_ok"; "tys_ok"; "sr2"; "idx_range"; "src_orac"; "env_gen_inv"] [] THEN
  USE_THEN "gl2" (fun th -> REWRITE_TAC[GSYM th]) THEN
  USE_THEN "tk2" (fun th -> REWRITE_TAC[GSYM th]) THEN
  FLATP2AUX_LREWRITE_TAC ["dsu"] [] THEN
  FLATP2AUX_LREWRITE_TAC ["orac_rel"; "globals"; "eval_ref"; "fin_idx"] []);;

let FLATP2AUX_getOpClass_cases = prove
 (`!op. (getOpClass op = FunApp <=> op = Opapp) /\
        (getOpClass op = EvalOp <=> op = Eval) /\
        (getOpClass op = Force <=> op = ThunkOp ForceThunk)`,
  GEN_TAC THEN CASES_ON `op:op` THEN REWRITE_TAC[getOpClass_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "op_class"; distinctness "op"; injectivity "op"] THEN
  TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "op_class"]);;

let FLATP2AUX_do_app_Env_id = prove
 (`!(s:(v store_v)list) (t:(FFI)ffi_state) vs res.
     do_app (s,t) Env_id vs = SOME res
     ==> (?env g i. vs = [Env env (g,i)]) \/
         (?g i. vs = [Conv NONE [g; i]] /\ res = ((s,t), Rval (Conv NONE [g; i])))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[do_app_def] THEN CASE_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN SIMP_NOASM[distinctness "option"; injectivity "option"] THEN
  MESON_TAC[]);;

let FLATP2AUX_state_refs_ffi_eta = prove
 (`!s:(FFI)state. state_refs_fupd (K (state_refs s)) (state_ffi_fupd (K (state_ffi s)) s) = s`,
  REWRITE_TAC[(record_info "state").ri_component_equality] THEN SIMP_NOASM[]);;

let FLATP2AUX_do_app_AallocEmpty = prove
 (`!(s:(v store_v)list) (t:(FFI)ffi_state) vs res.
     do_app (s,t) AallocEmpty vs = SOME res
     ==> vs = [Conv NONE []] /\ res = ((APPEND s [Varray []], t), Rval (Loc T (LENGTH s)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[store_alloc_def] THEN CASE_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN SIMP_NOASM[distinctness "option"; injectivity "option"] THEN
  MESON_TAC[]);;

let FLATP2AUX_flat_Aalloc_0 = prove
 (`!env (s:(C,FFI)flat_state).
     flat_evaluate env s [flat_App backend_common_None (Src Aalloc)
        [flat_Lit backend_common_None (IntLit (&0)); flat_Lit backend_common_None (IntLit (&0))]] =
     (flat_state_refs_fupd (K (APPEND (flat_state_refs s) [Varray []])) s,
      Rval [flat_Loc T (LENGTH (flat_state_refs s))])`,
  REPEAT GEN_TAC THEN
  FS[flat_evaluate_def; REVERSE; APPEND; flat_do_app_def; store_alloc_def; list_result_def;
     INT_ABS_NUM; NUM_OF_INT_OF_NUM; REPLICATE; INT_LT_REFL; INT_OF_NUM_LT] THEN
  REWRITE_TAC[INT_ARITH `~(&0:int < &0)`; INT_ABS_NUM; NUM_OF_INT_OF_NUM; REPLICATE] THEN
  CASE_REWRITE_TAC[] THEN SIMP_NOASM[]);;

let FLATP2AUX_s_rel_length = prove
 (`!genv (s:(FFI)state) (s1:(C,FFI)flat_state).
     source_to_flatProof_s_rel genv s s1
     ==> LENGTH (flat_state_refs s1) = LENGTH (state_refs s) + 1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[source_to_flatProof_s_rel_cases] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  STRUCT_CASES_TAC(ISPEC `flat_state_refs (s1:(C,FFI)flat_state)` list_CASES) THEN
  REWRITE_TAC[NULL; TL; LENGTH] THEN ARITH_TAC);;
let FLATP2AUX_TAKE1_APPEND = prove
 (`!(l:A list) x. ~NULL l ==> TAKE 1 (APPEND l x) = TAKE 1 l`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `l:A list` list_CASES) THEN
  REWRITE_TAC[NULL; APPEND; ONE; TAKE_def] THEN SIMP_NOASM[TAKE_def]);;
let FLATP2AUX_s_rel_alloc = prove
 (`!genv (s:(FFI)state) (s1:(C,FFI)flat_state).
     source_to_flatProof_s_rel genv s s1
     ==> source_to_flatProof_s_rel genv
           (state_refs_fupd (K (APPEND (state_refs s) [Varray []])) (state_ffi_fupd (K (state_ffi s)) s))
           (flat_state_refs_fupd (K (APPEND (flat_state_refs s1) [Varray []])) s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[source_to_flatProof_s_rel_cases] THEN
  REWRITE_TAC[state_INFO.ri_accfupds; flat_state_INFO.ri_accfupds; K_THM] THEN
  STRUCT_CASES_TAC(ISPEC `flat_state_refs (s1:(C,FFI)flat_state)` list_CASES) THEN
  REWRITE_TAC[NULL; TL; APPEND] THEN STRIP_TAC THEN ASM_REWRITE_TAC[NULL] THEN
  MATCH_MP_TAC LIST_REL_APPEND_suff THEN ASM_REWRITE_TAC[ALL2] THEN
  MATCH_MP_TAC(el 2 (CONJUNCTS source_to_flatProof_sv_rel_rules)) THEN REWRITE_TAC[ALL2]);;

let FLATP2AUX_App_alloc = prove
 (`!interp g gen genv1 idxs (st:(FFI)state) env es st1 vs
     (env_i1:(flat_v)flat_environment) (s_i1:(C,FFI)flat_state) t cm s1_i1 vs_i1 s' r.
     evaluate st env (REVERSE es) = (st1, Rval vs) /\
     evaluate st env [App AallocEmpty es] = (s', r) /\
     ~(r = Rerr (Rabort Rtype_error)) /\
     flat_evaluate env_i1 s_i1 (source_to_flat_compile_exps t cm (REVERSE es)) =
       (s1_i1, Rval vs_i1) /\
     ALL2 (source_to_flatProof_v_rel genv1) vs vs_i1 /\
     invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv1 idxs st1 s1_i1
     ==> ?s'_i1 r_i1.
           flat_evaluate env_i1 s_i1 [source_to_flat_compile_exp t cm (App AallocEmpty es)] =
             (s'_i1, r_i1) /\
           source_to_flatProof_result_rel (ALL2 o source_to_flatProof_v_rel) genv1 r r_i1 /\
           source_to_flatProof_s_rel genv1 s' s'_i1 /\
           invariant interp g gen genv1 idxs s' s'_i1 /\
           state_eval_state s' = state_eval_state st1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev1"; "ev"; "nte"; "fe1"; "vr"; "inv"]) THEN
  REMOVE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  FLATP2AUX_LREWRITE_TAC ["ev1"] [] THEN SIMP_NOASM[] THEN
  FLATP2AUX_OPTION_CASES_TAC `do_app (state_refs (st1:(FFI)state),state_ffi st1) AallocEmpty (REVERSE vs)`
    `res:((v store_v)list # (FFI)ffi_state) # (v,v)result` "da" THEN
  CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM o CONJUNCT2) THEN
    USE_THEN "nte" MP_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "da" (MP_TAC o MATCH_MP FLATP2AUX_do_app_AallocEmpty) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rvs") SUBST_ALL_TAC) THEN
  USE_THEN "rvs" (MP_TAC o AP_TERM `REVERSE:v list->v list`) THEN
  REWRITE_TAC[REVERSE_REVERSE; REVERSE; APPEND] THEN DISCH_THEN SUBST_ALL_TAC THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ; list_result_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  USE_THEN "ev1" (MP_TAC o SYM o MATCH_MP (CONJUNCT1 evaluate_length)) THEN
  REWRITE_TAC[LENGTH; LENGTH_REVERSE; ONE] THEN
  MP_TAC(ISPEC `es:exp list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `e1:exp` (X_CHOOSE_THEN `es1:exp list` SUBST_ALL_TAC))) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; LENGTH_EQ_NIL] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  USE_THEN "vr" (MP_TAC o REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
  DISCH_THEN(X_CHOOSE_THEN `v1':flat_v` (X_CHOOSE_THEN `tl1:flat_v list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 (LABEL_TAC "vr1") SUBST_ALL_TAC)))) THEN
  USE_THEN "fe1" (MP_TAC o REWRITE_RULE([REVERSE; APPEND] @ FLATP2AUX_compile_exps_clauses)) THEN
  DISCH_THEN(LABEL_TAC "fe1'") THEN
  REWRITE_TAC[source_to_flat_compile_exp_def] THEN
  REWRITE_TAC([REVERSE; APPEND; ITLIST] @ FLATP2AUX_compile_exps_clauses) THEN
  USE_THEN "fe1'" (fun th -> REWRITE_TAC[MATCH_MP FLATP2AUX_flat_Let th]) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[FLATP2AUX_opt_bind_fun; FLATP2AUX_record_etas] THEN
  REWRITE_TAC[FLATP2AUX_flat_Aalloc_0] THEN
  FLATP2AUX_EXISTSL [{|flat_state_refs_fupd (K (APPEND (flat_state_refs s1_i1) [Varray []])) s1_i1|};
    {|Rval [flat_Loc T (LENGTH (flat_state_refs s1_i1))]:(flat_v list,flat_v)result|}] THEN
  FLATP2AUX_INV_TAC "inv" THEN
  REWRITE_TAC[result_rel_eqns; o_THM; ALL2; v_rel_eqns; injectivity "result"; CONS_11] THEN
  USE_THEN "s_rel" (fun th -> REWRITE_TAC[MATCH_MP FLATP2AUX_s_rel_length th]) THEN
  SUBGOAL_THEN `source_to_flatProof_s_rel genv1
     (state_refs_fupd (K (APPEND (state_refs st1) [Varray []])) (state_ffi_fupd (K (state_ffi st1)) (st1:(FFI)state)))
     (flat_state_refs_fupd (K (APPEND (flat_state_refs s1_i1) [Varray []])) (s1_i1:(C,FFI)flat_state))`
    (LABEL_TAC "sr2") THENL
   [USE_THEN "s_rel" (ACCEPT_TAC o MATCH_MP FLATP2AUX_s_rel_alloc); ALL_TAC] THEN
  FLATP2AUX_LREWRITE_TAC ["sr2"] [state_INFO.ri_accfupds] THEN
  REWRITE_TAC[invariant_def; state_INFO.ri_accfupds; flat_state_INFO.ri_accfupds; K_THM] THEN
  FLATP2AUX_LREWRITE_TAC ["c_ok"; "tys_ok"; "sr2"; "idx_range"; "src_orac"; "orac_rel";
    "globals"; "env_gen_inv"; "fin_idx"] [] THEN
  USE_THEN "s_rel" (MP_TAC o CONJUNCT1 o REWRITE_RULE[source_to_flatProof_s_rel_cases]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP FLATP2AUX_TAKE1_APPEND th]) THEN
  FLATP2AUX_LREWRITE_TAC ["eval_ref"] [] THEN
  EXISTS_TAC `[flat_Loc T (LENGTH (state_refs (st1:(FFI)state)) + 1)]` THEN
  REWRITE_TAC[ALL2; v_rel_eqns]);;

let FLATP2AUX_dest_thunk_not_sing = prove
 (`(!(l:v list) st. ~(LENGTH l = 1) ==> dest_thunk l st = NotThunk) /\
   (!(l:flat_v list) st. ~(LENGTH l = 1) ==> flat_dest_thunk l st = flat_NotThunk)`,
  CONJ_TAC THEN GEN_TAC THEN GEN_TAC THENL
   [STRUCT_CASES_TAC(ISPEC `l:v list` list_CASES) THEN
    REWRITE_TAC[dest_thunk_def] THEN CASE_REWRITE_TAC[] THEN
    STRUCT_CASES_TAC(ISPEC `t:v list` list_CASES) THEN
    REWRITE_TAC[LENGTH; ONE] THEN CASES_ON `h:v` THEN
    REWRITE_TAC[dest_thunk_def] THEN CASE_REWRITE_TAC[];
    STRUCT_CASES_TAC(ISPEC `l:flat_v list` list_CASES) THEN
    REWRITE_TAC[flat_dest_thunk_def] THEN CASE_REWRITE_TAC[] THEN
    STRUCT_CASES_TAC(ISPEC `t:flat_v list` list_CASES) THEN
    REWRITE_TAC[LENGTH; ONE] THEN CASES_ON `h:flat_v` THEN
    REWRITE_TAC[flat_dest_thunk_def] THEN CASE_REWRITE_TAC[]]);;

let FLATP2AUX_v_rel_flat_Loc = prove
 (`!genv x b n. source_to_flatProof_v_rel genv x (flat_Loc b n) ==> ?n'. x = Loc b n' /\ n = n' + 1`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[source_to_flatProof_v_rel_cases] THEN
  REWRITE_TAC[distinctness "flat_v"; injectivity "flat_v"] THEN MESON_TAC[]);;
let FLATP2AUX_store_lookup_TL = prove
 (`!(refs':(A store_v)list) n. ~NULL refs' ==>
     store_lookup (n + 1) refs' = store_lookup n (TL refs')`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `refs':(A store_v)list` list_CASES) THEN
  REWRITE_TAC[NULL; TL; store_lookup_def; LENGTH; GSYM ADD1; LT_SUC; EL; TL]);;

let FLATP2AUX_dest_thunk_rel1 = prove
 (`!genv x x' refs refs'.
     source_to_flatProof_v_rel genv x x' /\
     ALL2 (source_to_flatProof_sv_rel genv) refs (TL refs') /\ ~NULL refs'
     ==> (dest_thunk [x] refs = BadRef ==> flat_dest_thunk [x'] refs' = flat_BadRef) /\
         (dest_thunk [x] refs = NotThunk ==> flat_dest_thunk [x'] refs' = flat_NotThunk) /\
         (!m v. dest_thunk [x] refs = IsThunk m v
                ==> ?v'. flat_dest_thunk [x'] refs' = flat_IsThunk m v' /\
                         source_to_flatProof_v_rel genv v v')`,
  (REPEAT GEN_TAC THEN DISCH_THEN(FLATP2AUX_LABEL_CONJS ["vr"; "rr"; "nn"]) THEN
  ASM_CASES_TAC `?b n. (x':flat_v) = flat_Loc b n` THENL
   [POP_ASSUM(FLATP2AUX_CHOOSE_THEN [`b:bool`; `n:num`] SUBST_ALL_TAC) THEN
    USE_THEN "vr" (FLATP2AUX_CHOOSE_THEN [`n0:num`] (CONJUNCTS_THEN SUBST_ALL_TAC) o
                   MATCH_MP FLATP2AUX_v_rel_flat_Loc) THEN
    REWRITE_TAC[dest_thunk_def; flat_dest_thunk_def] THEN
    USE_THEN "nn" (fun th -> REWRITE_TAC[MATCH_MP FLATP2AUX_store_lookup_TL th]) THEN
    REWRITE_TAC[store_lookup_def] THEN
    USE_THEN "rr" (fun th -> REWRITE_TAC[GSYM(MATCH_MP LIST_REL_LENGTH th)]) THEN
    COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
    USE_THEN "rr" (MP_TAC o SPEC `n0:num` o CONJUNCT2 o REWRITE_RULE[LIST_REL_EL_EQN]) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[source_to_flatProof_sv_rel_cases] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    CASES_ON `m:thunk_mode` THEN CASE_REWRITE_TAC[] THEN BOOL_CASES_TAC `b:bool` THEN
    REWRITE_TAC[distinctness "dest_thunk_ret"; injectivity "dest_thunk_ret";
                distinctness "flat_dest_thunk_ret"; injectivity "flat_dest_thunk_ret"] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC]) THEN
  (POP_ASSUM(LABEL_TAC "nl") THEN
  SUBGOAL_THEN `flat_dest_thunk [x':flat_v] refs' = flat_NotThunk` (LABEL_TAC "fn") THENL
   [USE_THEN "nl" MP_TAC THEN CASES_ON `x':flat_v` THEN
    REWRITE_TAC[flat_dest_thunk_def; injectivity "flat_v"; distinctness "flat_v"] THEN
    CASE_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dest_thunk [x:v] refs = NotThunk` (LABEL_TAC "sn") THENL
   [USE_THEN "nl" MP_TAC THEN USE_THEN "vr" MP_TAC THEN CASES_ON `x:v` THEN
    REWRITE_TAC[dest_thunk_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[v_rel_eqns] THEN MESON_TAC[];
    ALL_TAC] THEN
  FLATP2AUX_LREWRITE_TAC ["fn"; "sn"] [distinctness "dest_thunk_ret"]));;

let FLATP2AUX_dest_thunk_rel = prove
 (`!genv vs vs' refs refs'.
     ALL2 (source_to_flatProof_v_rel genv) vs vs' /\
     ALL2 (source_to_flatProof_sv_rel genv) refs (TL refs') /\ ~NULL refs'
     ==> (dest_thunk (REVERSE vs) refs = BadRef ==> flat_dest_thunk vs' refs' = flat_BadRef) /\
         (dest_thunk (REVERSE vs) refs = NotThunk ==> flat_dest_thunk vs' refs' = flat_NotThunk) /\
         (!m v. dest_thunk (REVERSE vs) refs = IsThunk m v
                ==> ?v'. flat_dest_thunk vs' refs' = flat_IsThunk m v' /\
                         source_to_flatProof_v_rel genv v v')`,
  REPEAT GEN_TAC THEN DISCH_THEN(FLATP2AUX_LABEL_CONJS ["vr"; "rr"; "nn"]) THEN
  ASM_CASES_TAC `LENGTH (vs:v list) = 1` THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:v` (X_CHOOSE_THEN `t0:v list`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC))) THEN
    USE_THEN "vr" (MP_TAC o REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
    DISCH_THEN(X_CHOOSE_THEN `x':flat_v` (X_CHOOSE_THEN `tl':flat_v list`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 (LABEL_TAC "xr") SUBST_ALL_TAC)))) THEN
    REWRITE_TAC[REVERSE; APPEND] THEN MATCH_MP_TAC FLATP2AUX_dest_thunk_rel1 THEN
    FLATP2AUX_LREWRITE_TAC ["xr"; "rr"; "nn"] [];
    SUBGOAL_THEN `dest_thunk (REVERSE vs) refs = NotThunk /\ flat_dest_thunk vs' refs' = flat_NotThunk`
      (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC (CONJUNCT1 FLATP2AUX_dest_thunk_not_sing);
        MATCH_MP_TAC (CONJUNCT2 FLATP2AUX_dest_thunk_not_sing)] THEN
      ASM_REWRITE_TAC[LENGTH_REVERSE] THEN
      USE_THEN "vr" (fun th -> REWRITE_TAC[GSYM(MATCH_MP LIST_REL_LENGTH th)]) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[distinctness "dest_thunk_ret"]]]);;

let FLATP2AUX_sv_rel_same_type = prove
 (`!genv a a' m w w'.
     source_to_flatProof_sv_rel genv a a' /\ store_v_same_type a (Thunk m w)
     ==> store_v_same_type a' (Thunk m (w':flat_v))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sv") MP_TAC) THEN
  USE_THEN "sv" MP_TAC THEN ONCE_REWRITE_TAC[source_to_flatProof_sv_rel_cases] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[store_v_same_type_def] THEN CASE_REWRITE_TAC[] THEN
  TRY(CASES_ON `m':thunk_mode` THEN CASE_REWRITE_TAC[]));;

let FLATP2AUX_update_thunk_rel = prove
 (`!genv vs vs' (refs:(v store_v)list) (refs':(flat_v store_v)list) ws ws' refs2.
     ALL2 (source_to_flatProof_v_rel genv) vs vs' /\
     ALL2 (source_to_flatProof_v_rel genv) ws ws' /\
     ALL2 (source_to_flatProof_sv_rel genv) refs (TL refs') /\ ~NULL refs' /\
     update_thunk (REVERSE vs) refs ws = SOME refs2
     ==> ?refs2'. flat_update_thunk vs' refs' ws' = SOME refs2' /\
                  ALL2 (source_to_flatProof_sv_rel genv) refs2 (TL refs2') /\
                  ~NULL refs2' /\ TAKE 1 refs2' = TAKE 1 refs'`,
  (REPEAT GEN_TAC THEN DISCH_THEN(FLATP2AUX_LABEL_CONJS ["vr"; "wr"; "rr"; "nn"; "ut"]) THEN
  ASM_CASES_TAC `LENGTH (vs:v list) = 1` THENL
   [ALL_TAC;
    USE_THEN "ut" MP_TAC THEN
    SUBGOAL_THEN `!l:v list. ~(LENGTH l = 1) ==> update_thunk l refs ws = NONE`
      (fun th -> REWRITE_TAC[MATCH_MP th (EQ_MP (SYM(AP_TERM `(~)`
                   (AP_THM (AP_TERM `(=):num->num->bool` (ISPEC `vs:v list` LENGTH_REVERSE)) `1`)))
                   (ASSUME `~(LENGTH (vs:v list) = 1)`))]) THENL
     [GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `l:v list` list_CASES) THEN
      REWRITE_TAC[update_thunk_def] THEN CASE_REWRITE_TAC[] THEN
      STRUCT_CASES_TAC(ISPEC `t:v list` list_CASES) THEN
      REWRITE_TAC[LENGTH; ONE] THEN CASES_ON `h:v` THEN
      REWRITE_TAC[update_thunk_def] THEN CASE_REWRITE_TAC[];
      REWRITE_TAC[distinctness "option"]]] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:v` (X_CHOOSE_THEN `t0:v list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC))) THEN
  USE_THEN "vr" (MP_TAC o REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x':flat_v` (X_CHOOSE_THEN `tl':flat_v list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 (LABEL_TAC "xr") SUBST_ALL_TAC)))) THEN
  USE_THEN "ut" MP_TAC THEN REWRITE_TAC[REVERSE; APPEND] THEN
  ASM_CASES_TAC `?b n. (x:v) = Loc b n` THENL
   [ALL_TAC;
    POP_ASSUM MP_TAC THEN CASES_ON `x:v` THEN REWRITE_TAC[update_thunk_def] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"; injectivity "v"] THEN
    MESON_TAC[]] THEN
  POP_ASSUM(FLATP2AUX_CHOOSE_THEN [`b:bool`; `n:num`] SUBST_ALL_TAC) THEN
  USE_THEN "xr" (SUBST_ALL_TAC o REWRITE_RULE[v_rel_eqns]) THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[update_thunk_def; flat_update_thunk_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"] THEN
  MP_TAC(ISPEC `ws:v list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `w:v` (X_CHOOSE_THEN `wt:v list` SUBST_ALL_TAC))) THEN
  REWRITE_TAC[update_thunk_def] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"] THEN
  MP_TAC(ISPEC `wt:v list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `w2:v` (X_CHOOSE_THEN `wt2:v list` SUBST_ALL_TAC))) THEN
  REWRITE_TAC[update_thunk_def] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"] THEN
  USE_THEN "wr" (MP_TAC o REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
  DISCH_THEN(X_CHOOSE_THEN `w':flat_v` (X_CHOOSE_THEN `wt':flat_v list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 (LABEL_TAC "wvr") SUBST_ALL_TAC)))) THEN
  REWRITE_TAC[flat_update_thunk_def] THEN CASE_REWRITE_TAC[] THEN
  ALL_TAC) THEN
  (MP_TAC(MATCH_MP FLATP2AUX_dest_thunk_rel1 (end_itlist CONJ
    [ASSUME `source_to_flatProof_v_rel genv w w'`;
     ASSUME `ALL2 (source_to_flatProof_sv_rel genv) refs (TL (refs':(flat_v store_v)list))`;
     ASSUME `~NULL (refs':(flat_v store_v)list)`])) THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["d1"; "d2"; "d3"])) THEN
  (MP_TAC(ISPEC `dest_thunk [w] refs` (cases "dest_thunk_ret")) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  TRY(FIRST_X_ASSUM(CHOOSE_THEN (CHOOSE_THEN ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"]) THEN
  (USE_THEN "d2" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `dest_thunk [w] refs = NotThunk`)]) THEN
  CASE_REWRITE_TAC[]) THEN
  (USE_THEN "nn" MP_TAC THEN USE_THEN "rr" MP_TAC THEN
  STRUCT_CASES_TAC(ISPEC `refs':(flat_v store_v)list` list_CASES) THEN
  REWRITE_TAC[NULL; TL] THEN DISCH_THEN(LABEL_TAC "rr'")) THEN
  (REWRITE_TAC[store_assign_def; LENGTH; GSYM ADD1; LT_SUC; EL; TL] THEN
  USE_THEN "rr'" (fun th -> REWRITE_TAC[GSYM(MATCH_MP LIST_REL_LENGTH th)])) THEN
  (COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  POP_ASSUM(CONJUNCTS_THEN2 (LABEL_TAC "nl") (LABEL_TAC "st")) THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM)) THEN
  (SUBGOAL_THEN `store_v_same_type (EL n t) (Thunk Evaluated (w':flat_v))` (LABEL_TAC "st'") THENL
   [MATCH_MP_TAC FLATP2AUX_sv_rel_same_type THEN
    MAP_EVERY EXISTS_TAC [`genv:global_env`; `EL n (refs:(v store_v)list)`; `w:v`] THEN
    FLATP2AUX_LREWRITE_TAC ["st"] [] THEN
    USE_THEN "rr'" (MP_TAC o SPEC `n:num` o CONJUNCT2 o REWRITE_RULE[LIST_REL_EL_EQN]) THEN
    FLATP2AUX_LREWRITE_TAC ["nl"] [];
    ALL_TAC]) THEN
  (FLATP2AUX_LREWRITE_TAC ["nl"; "st'"] []) THEN
  (EXISTS_TAC `CONS (h:flat_v store_v) (LUPDATE (Thunk Evaluated w') n t)` THEN
  REWRITE_TAC[LUPDATE_def; NULL; TL; TAKE_def; NOT_SUC; SUC_SUB1; TAKE_0] THEN
  MATCH_MP_TAC EVERY2_LUPDATE_same THEN FLATP2AUX_LREWRITE_TAC ["rr'"] [] THEN
  MATCH_MP_TAC(el 3 (CONJUNCTS source_to_flatProof_sv_rel_rules)) THEN
  FLATP2AUX_LREWRITE_TAC ["wvr"] []));;

let FLATP2AUX_flat_AppUnit = prove
 (CASE_TERM `!f (s:(C,FFI)flat_state).
     flat_evaluate (flat_environment_REC [(implode "f", f)]) s
       [flat_AppUnit (Var_local backend_common_None (implode "f"))] =
     (match flat_do_opapp [f; flat_Conv NONE []] with
        NONE -> (s, Rerr (Rabort Rtype_error))
      | SOME (env', e) ->
          if flat_state_clock s = 0 then (s, Rerr (Rabort Rtimeout_error))
          else flat_evaluate env' (flat_dec_clock s) [e])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flat_AppUnit_def] THEN
  FS[flat_evaluate_def; REVERSE; APPEND; ALOOKUP_THM; flat_environment_INFO.ri_accessors]);;

let FLATP2AUX_ALL2_v_rel_weak = prove
 (`!genv genv' vs vs'.
     ALL2 (source_to_flatProof_v_rel genv) vs vs' /\
     global_env_c genv SUBMAP global_env_c genv' /\
     global_env_tys genv SUBMAP global_env_tys genv' /\
     subglobals (global_env_v genv) (global_env_v genv')
     ==> ALL2 (source_to_flatProof_v_rel genv') vs vs'`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MONO_ALL2 THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC v_rel_weak THEN
  EXISTS_TAC `genv:global_env` THEN ASM_REWRITE_TAC[]);;
let FLATP2AUX_invariant_refs = prove
 (`!interp g gen genv idxs (st:(FFI)state) (s_i1:(C,FFI)flat_state) refs refs'.
     invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv idxs st s_i1 /\
     source_to_flatProof_s_rel genv (state_refs_fupd (K refs) st)
       (flat_state_refs_fupd (K refs') s_i1) /\
     TAKE 1 refs' = TAKE 1 (flat_state_refs s_i1)
     ==> invariant interp g gen genv idxs (state_refs_fupd (K refs) st)
           (flat_state_refs_fupd (K refs') s_i1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inv") (CONJUNCTS_THEN2 (LABEL_TAC "sr") (LABEL_TAC "tk"))) THEN
  FLATP2AUX_INV_TAC "inv" THEN
  REWRITE_TAC[invariant_def; state_INFO.ri_accfupds; flat_state_INFO.ri_accfupds; K_THM] THEN
  FLATP2AUX_LREWRITE_TAC ["tk"] [] THEN
  FLATP2AUX_LREWRITE_TAC ["c_ok"; "tys_ok"; "sr"; "idx_range"; "src_orac"; "orac_rel"; "globals";
    "eval_ref"; "env_gen_inv"; "fin_idx"] []);;

let FLATP2AUX_words_bytes = prove
 (`~(implode "words" = implode "bytes")`,
  REWRITE_TAC[injectivity "mlstring"; CONS_11; injectivity "char"]);;

let FLATP2AUX_flat_Eval_code = prove
 ((CASE_TERM `!env_i1 (s_i1:(C,FFI)flat_state) t cm es s1 vs' decs' ec'.
     flat_evaluate env_i1 s_i1 (REVERSE (source_to_flat_compile_exps t cm es)) = (s1, Rval vs') /\
     LENGTH vs' = 6 /\
     flat_do_eval (DROP 4 (REVERSE vs')) (flat_state_eval_config s1) = SOME (decs', ec', Unitv)
     ==> flat_evaluate env_i1 s_i1 [source_to_flat_compile_exp t cm (App Eval es)] =
         (if flat_state_clock s1 = 0
          then (flat_state_eval_config_fupd (K ec') s1, Rerr (Rabort Rtimeout_error))
          else (match flat_evaluate_decs (flat_dec_clock (flat_state_eval_config_fupd (K ec') s1)) decs'
                with (s2, NONE) ->
                       flat_evaluate (flat_environment_v_fupd (K (CONS (implode "words", LAST (REVERSE vs'))
                          (CONS (implode "bytes", EL 4 (REVERSE vs')) (flat_environment_v env_i1)))) env_i1) s2
                         [flat_Let backend_common_None (SOME (implode "r"))
                            (flat_App backend_common_None (GlobalVarLookup 0) [])
                            (flat_App backend_common_None (flat_El 0)
                               [Var_local backend_common_None (implode "r")])]
                   | (s2, SOME e) -> (s2, Rerr e)))`),
  REPEAT GEN_TAC THEN DISCH_THEN(FLATP2AUX_LABEL_CONJS ["fe"; "len"; "fde"]) THEN
  REWRITE_TAC[source_to_flat_compile_exp_def; distinctness "op"] THEN
  SUBGOAL_THEN `flat_evaluate env_i1 (s_i1:(C,FFI)flat_state)
      [flat_Con backend_common_None NONE (source_to_flat_compile_exps t cm es)] =
      (s1, Rval [flat_Conv NONE (REVERSE vs')])` (LABEL_TAC "fc") THENL
   [REWRITE_TAC[flat_evaluate_def] THEN FLATP2AUX_LREWRITE_TAC ["fe"] [] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "fc" (fun th -> REWRITE_TAC[MATCH_MP FLATP2AUX_flat_Mat th]) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD; flat_evaluate_match_def] THEN
  SUBGOAL_THEN `LENGTH (REVERSE (vs':flat_v list)) = 6` (LABEL_TAC "len'") THENL
   [FLATP2AUX_LREWRITE_TAC ["len"] [LENGTH_REVERSE]; ALL_TAC] THEN
  USE_THEN "len'" (fun th -> REWRITE_TAC[MATCH_MP pmatch_rows_drop_4 th]) THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[flat_pat_bindings_def; APPEND; ALL_DISTINCT; MEM; FLATP2AUX_words_bytes] THEN
  SUBGOAL_THEN `[EL 4 (REVERSE (vs':flat_v list)); LAST (REVERSE vs')] = DROP 4 (REVERSE vs')`
    (LABEL_TAC "d4") THENL
   [MATCH_MP_TAC drop_4_via_el THEN FLATP2AUX_LREWRITE_TAC ["len'"] []; ALL_TAC] THEN
  SUBGOAL_THEN (CASE_TERM `flat_evaluate (flat_environment_v_fupd (K
      (CONS (implode "words",LAST (REVERSE vs')) (CONS (implode "bytes",EL 4 (REVERSE vs'))
      (flat_environment_v env_i1)))) env_i1) (s1:(C,FFI)flat_state)
      [flat_App backend_common_None (Src Eval)
         (MAP (Var_local backend_common_None) [implode "bytes"; implode "words"])] =
      (if flat_state_clock s1 = 0
       then (flat_state_eval_config_fupd (K ec') s1, Rerr (Rabort Rtimeout_error))
       else (match flat_evaluate_decs (flat_dec_clock (flat_state_eval_config_fupd (K ec') s1)) decs'
             with (s2, NONE) -> (s2, Rval [Unitv])
                | (s2, SOME e) -> (s2, Rerr e)))`) (LABEL_TAC "fev") THENL
   [REWRITE_TAC[MAP; flat_evaluate_def; REVERSE; APPEND] THEN
    REWRITE_TAC[flat_environment_INFO.ri_accfupds; K_THM; APPEND; ALOOKUP_THM;
                FLATP2AUX_words_bytes; GSYM FLATP2AUX_words_bytes] THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "op"; injectivity "flat_op"; HD; REVERSE; APPEND] THEN
    FLATP2AUX_LREWRITE_TAC ["d4"; "fde"] [] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[flat_state_INFO.ri_accfupds];
    ALL_TAC] THEN
  REWRITE_TAC[APPEND] THEN
  ASM_CASES_TAC `flat_state_clock (s1:(C,FFI)flat_state) = 0` THEN POP_ASSUM(LABEL_TAC "c0") THEN
  USE_THEN "fev" MP_TAC THEN FLATP2AUX_LREWRITE_TAC ["c0"] [] THENL
   [DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP FLATP2AUX_flat_Let th]) THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  FLATP2AUX_PAIR_TAC `flat_evaluate_decs (flat_dec_clock (flat_state_eval_config_fupd (K ec')
      (s1:(C,FFI)flat_state))) decs'` `s2:(C,FFI)flat_state` `ro:((flat_v)error_result)option` "fd" THEN
  FLATP2AUX_LREWRITE_TAC ["fd"] [] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `ro:((flat_v)error_result)option` THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP FLATP2AUX_flat_Let th]) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[FLATP2AUX_opt_bind_fun; FLATP2AUX_record_etas]);;

let FLATP2AUX_flat_eval_ref_read = prove
 (`!env (s:(C,FFI)flat_state) xs y rs.
     flat_state_globals s = CONS (SOME (flat_Loc T 0)) xs /\
     flat_state_refs s = CONS (Refv y) rs
     ==> flat_evaluate env s
           [flat_Let backend_common_None (SOME (implode "r"))
              (flat_App backend_common_None (GlobalVarLookup 0) [])
              (flat_App backend_common_None (flat_El 0)
                 [Var_local backend_common_None (implode "r")])] = (s, Rval [y])`,
  REPEAT STRIP_TAC THEN
  FS[flat_evaluate_def; REVERSE; APPEND; flat_do_app_def; LENGTH; EL; HD; IS_SOME_DEF; THE_DEF;
     list_result_def; FLATP2AUX_opt_bind_fun; opt_bind_def; flat_environment_INFO.ri_accfupds;
     ALOOKUP_THM; store_lookup_def; ARITH_RULE `0 < SUC n`]);;

let FLATP2AUX_flat_glob_alloc = prove
 (`!(s:(C,FFI)flat_state) next c rest.
     flat_evaluate_decs s (CONS (glob_alloc next c) rest) =
     flat_evaluate_decs (flat_state_globals_fupd (K (APPEND (flat_state_globals s)
       (REPLICATE (next_indices_vidx next - next_indices_vidx (source_to_flat_config_next c))
          NONE))) s) rest`,
  REPEAT GEN_TAC THEN REWRITE_TAC[glob_alloc_def] THEN
  FS[flat_evaluate_def; REVERSE; APPEND; flat_do_app_def; list_result_def;
     FLATP2AUX_opt_bind_fun; flat_Unitv_def; FLATP2AUX_record_etas]);;

let FLATP2AUX_flat_state_comm = prove
 (`!(s:(C,FFI)flat_state) ec gl.
     flat_state_globals_fupd (K (APPEND (flat_state_globals
         (flat_dec_clock (flat_state_eval_config_fupd (K ec) s))) gl))
       (flat_dec_clock (flat_state_eval_config_fupd (K ec) s)) =
     flat_dec_clock (flat_state_eval_config_fupd (K ec)
       (flat_state_globals_fupd (K (APPEND (flat_state_globals s) gl)) s))`,
  REWRITE_TAC[(record_info "flat_state").ri_component_equality; flat_dec_clock_def] THEN
  SIMP_NOASM[]);;

let FLATP2AUX_cc_seq = prove
 (FLATP2AUX_cc_case 1,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "ear"; "lts"; "egr"; "nte"; "esi"]) THEN
  REMOVE_THEN "esi" SUBST_ALL_TAC THEN
  FLATP2AUX_PAIR_TAC `evaluate (st:(FFI)state) env [e1]` `st1:(FFI)state`
    `r1:(v list,v)result` "ev1" THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  FLATP2AUX_LREWRITE_TAC ["ev1"] [] THEN CASE_REWRITE_TAC[] THEN
  FLATP2AUX_RESULT_CASES_TAC `r1:(v list,v)result` `v1:v list` `err1:(v)error_result` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[source_to_flat_compile_exp_def] THENL
   [(* e1 evaluates to a value *)
    FLATP2AUX_PAIR_TAC `evaluate (st1:(FFI)state) env (CONS e2 es)` `st2:(FFI)state`
      `r2:(v list,v)result` "ev2" THEN
    FLATP2AUX_LREWRITE_TAC ["ev2"] [] THEN CASE_REWRITE_TAC[] THEN
    DISCH_THEN(LABEL_TAC "ev'") THEN
    FLATP2AUX_IH_TAC "ih1" [("s'",`st1:(FFI)state`); ("r",`Rval v1:(v list,v)result`)] THEN
    ANTS_TAC THENL
     [FLATP2AUX_ANTS_TAC THEN REWRITE_TAC[distinctness "result"; source_to_flat_compile_exp_def];
      ALL_TAC] THEN
    DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s1_i1:(C,FFI)flat_state`;
      `r1_i1:(flat_v list,flat_v)result`; `genv1:global_env`]
      (FLATP2AUX_LABEL_CONJS ["fe1"; "rr1"; "sr1"; "na1"])) THEN
    USE_THEN "rr1" (MP_TAC o MATCH_MP FLATP2AUX_result_rel_Rval) THEN
    DISCH_THEN(X_CHOOSE_THEN `v1':flat_v list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      (LABEL_TAC "vr1"))) THEN
    USE_THEN "na1" (MP_TAC o REWRITE_RULE[source_to_flatProof_abort_simps]) THEN
    DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i1"; "eg1"; "of1"; "sc1"; "sy1"; "sg1"]) THEN
    USE_THEN "ev1" (X_CHOOSE_THEN `x1:v` SUBST_ALL_TAC o MATCH_MP evaluate_sing) THEN
    USE_THEN "vr1" (MP_TAC o REWRITE_RULE[o_THM; LIST_REL_CONS1; LIST_REL_NIL]) THEN
    DISCH_THEN(X_CHOOSE_THEN `x1':flat_v` (X_CHOOSE_THEN `t1:flat_v list`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 (LABEL_TAC "xr1") SUBST_ALL_TAC)))) THEN
    USE_THEN "ev1" (fun ev1 -> USE_THEN "ih2" (fun ih2 -> LABEL_TAC "ih2'" (MATCH_MP ih2 ev1))) THEN
    SUBGOAL_THEN `env_all_rel genv1 comp_map env env_i1 locals` (LABEL_TAC "ear1") THENL
     [MATCH_MP_TAC env_all_rel_weak THEN EXISTS_TAC `genv:global_env` THEN
      FLATP2AUX_LREWRITE_TAC ["ear"; "sc1"; "sy1"; "sg1"] [];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(r2 = Rerr (Rabort Rtype_error):(v list,v)result)` (LABEL_TAC "nte2") THENL
     [DISCH_THEN SUBST_ALL_TAC THEN USE_THEN "nte" MP_TAC THEN USE_THEN "ev'" MP_TAC THEN
      CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
      ALL_TAC] THEN
    FLATP2AUX_IH_TAC "ih2'" [("s'",`st2:(FFI)state`); ("r",`r2:(v list,v)result`);
      ("genv",`genv1:global_env`); ("s_i1",`s1_i1:(C,FFI)flat_state`)] THEN
    ANTS_TAC THENL [FLATP2AUX_ANTS_TAC; ALL_TAC] THEN
    DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s2_i1:(C,FFI)flat_state`;
      `r2_i1:(flat_v list,flat_v)result`; `genv2:global_env`]
      (FLATP2AUX_LABEL_CONJS ["fe2"; "rr2"; "sr2"; "na2"])) THEN
    USE_THEN "fe1" (LABEL_TAC "fe1'" o REWRITE_RULE[source_to_flat_compile_exp_def]) THEN
    USE_THEN "fe2" (LABEL_TAC "fe2'" o REWRITE_RULE[source_to_flat_compile_exp_def]) THEN
    FLATP2AUX_RESULT_CASES_TAC `r2:(v list,v)result` `vs2:v list` `err2:(v)error_result` THEN
    REMOVE_THEN "ev'" (MP_TAC o CASE_REWRITE_RULE[]) THEN REWRITE_TAC[PAIR_EQ; HD] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THENL
     [USE_THEN "rr2" (MP_TAC o MATCH_MP FLATP2AUX_result_rel_Rval) THEN
      DISCH_THEN(X_CHOOSE_THEN `vs2':flat_v list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
        (LABEL_TAC "vr2"))) THEN
      MAP_EVERY EXISTS_TAC [`s2_i1:(C,FFI)flat_state`;
        `Rval (CONS x1' vs2'):(flat_v list,flat_v)result`; `genv2:global_env`] THEN
      REWRITE_TAC[flat_evaluate_def] THEN FLATP2AUX_LREWRITE_TAC ["fe1'"] [] THEN
      CASE_REWRITE_TAC[] THEN FLATP2AUX_LREWRITE_TAC ["fe2'"] [] THEN CASE_REWRITE_TAC[] THEN
      FLATP2AUX_LREWRITE_TAC ["sr2"] [HD; source_to_flatProof_abort_simps] THEN
      USE_THEN "na2" (MP_TAC o REWRITE_RULE[source_to_flatProof_abort_simps]) THEN
      DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i2"; "eg2"; "of2"; "sc2"; "sy2"; "sg2"]) THEN
      FLATP2AUX_LREWRITE_TAC ["i2"; "eg2"] [result_rel_eqns; injectivity "result"] THEN
      CONJ_TAC THENL
       [EXISTS_TAC `CONS x1' vs2':flat_v list` THEN REWRITE_TAC[o_THM; ALL2] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC v_rel_weak THEN EXISTS_TAC `genv1:global_env` THEN
          FLATP2AUX_LREWRITE_TAC ["xr1"; "sc2"; "sy2"; "sg2"] [];
          USE_THEN "vr2" (ACCEPT_TAC o REWRITE_RULE[o_THM])];
        FLATP2AUX_TRANS_TAC `state_eval_state (st1:(FFI)state)` `genv1:global_env`];
      USE_THEN "rr2" (X_CHOOSE_THEN `err2':(flat_v)error_result` SUBST_ALL_TAC o
                      MATCH_MP FLATP2AUX_result_rel_Rerr) THEN
      MAP_EVERY EXISTS_TAC [`s2_i1:(C,FFI)flat_state`;
        `Rerr err2':(flat_v list,flat_v)result`; `genv2:global_env`] THEN
      REWRITE_TAC[flat_evaluate_def] THEN FLATP2AUX_LREWRITE_TAC ["fe1'"] [] THEN
      CASE_REWRITE_TAC[] THEN FLATP2AUX_LREWRITE_TAC ["fe2'"] [] THEN CASE_REWRITE_TAC[] THEN
      FLATP2AUX_LREWRITE_TAC ["sr2"; "rr2"] [] THEN DISCH_TAC THEN
      USE_THEN "na2" (MP_TAC o C MP (ASSUME
        `~source_to_flatProof_abort (Rerr err2:(v list,v)result)`)) THEN
      DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i2"; "eg2"; "of2"; "sc2"; "sy2"; "sg2"]) THEN
      FLATP2AUX_LREWRITE_TAC ["i2"; "eg2"] [] THEN
      FLATP2AUX_TRANS_TAC `state_eval_state (st1:(FFI)state)` `genv1:global_env`];
    (* e1 raises an error *)
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
    FLATP2AUX_IH_TAC "ih1" [("r",`Rerr err1:(v list,v)result`)] THEN
    ANTS_TAC THENL [FLATP2AUX_ANTS_TAC THEN REWRITE_TAC[source_to_flat_compile_exp_def]; ALL_TAC] THEN
    DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s1_i1:(C,FFI)flat_state`;
      `r1_i1:(flat_v list,flat_v)result`; `genv1:global_env`]
      (FLATP2AUX_LABEL_CONJS ["fe1"; "rr1"; "sr1"; "na1"])) THEN
    USE_THEN "rr1" (X_CHOOSE_THEN `err1':(flat_v)error_result` SUBST_ALL_TAC o
                    MATCH_MP FLATP2AUX_result_rel_Rerr) THEN
    MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`;
      `Rerr err1':(flat_v list,flat_v)result`; `genv1:global_env`] THEN
    FLATP2AUX_LREWRITE_TAC ["rr1"; "sr1"; "na1"] [] THEN
    REWRITE_TAC[flat_evaluate_def] THEN
    USE_THEN "fe1" (MP_TAC o REWRITE_RULE[source_to_flat_compile_exp_def]) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CASE_REWRITE_TAC[]]);;

let FLATP2AUX_cc_Raise = prove
 (FLATP2AUX_cc_case 3,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih1") THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "ear"; "lts"; "egr"; "nte"; "esi"]) THEN
  REMOVE_THEN "esi" SUBST_ALL_TAC THEN
  FLATP2AUX_PAIR_TAC `evaluate (st:(FFI)state) env [e]` `st1:(FFI)state`
    `r1:(v list,v)result` "ev1" THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  FLATP2AUX_LREWRITE_TAC ["ev1"] [] THEN CASE_REWRITE_TAC[] THEN
  FLATP2AUX_RESULT_CASES_TAC `r1:(v list,v)result` `v1:v list` `err1:(v)error_result` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[source_to_flat_compile_exp_def; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THENL
   [FLATP2AUX_IH_TAC "ih1" [("r",`Rval v1:(v list,v)result`)] THEN
    ANTS_TAC THENL
     [FLATP2AUX_ANTS_TAC THEN REWRITE_TAC[distinctness "result"; source_to_flat_compile_exp_def];
      ALL_TAC] THEN
    DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s1_i1:(C,FFI)flat_state`;
      `r1_i1:(flat_v list,flat_v)result`; `genv1:global_env`]
      (FLATP2AUX_LABEL_CONJS ["fe1"; "rr1"; "sr1"; "na1"])) THEN
    USE_THEN "rr1" (MP_TAC o MATCH_MP FLATP2AUX_result_rel_Rval) THEN
    DISCH_THEN(X_CHOOSE_THEN `v1':flat_v list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      (LABEL_TAC "vr1"))) THEN
    USE_THEN "ev1" (X_CHOOSE_THEN `x1:v` SUBST_ALL_TAC o MATCH_MP evaluate_sing) THEN
    USE_THEN "vr1" (MP_TAC o REWRITE_RULE[o_THM; LIST_REL_CONS1; LIST_REL_NIL]) THEN
    DISCH_THEN(X_CHOOSE_THEN `x1':flat_v` (X_CHOOSE_THEN `t1:flat_v list`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 (LABEL_TAC "xr1") SUBST_ALL_TAC)))) THEN
    MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`;
      `Rerr (Rraise x1'):(flat_v list,flat_v)result`; `genv1:global_env`] THEN
    REWRITE_TAC[flat_evaluate_def] THEN
    USE_THEN "fe1" (MP_TAC o REWRITE_RULE[source_to_flat_compile_exp_def]) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CASE_REWRITE_TAC[] THEN
    FLATP2AUX_LREWRITE_TAC ["sr1"] [result_rel_eqns; HD; source_to_flatProof_abort_simps] THEN
    FLATP2AUX_LKSIMP_TAC ["xr1"] [] THEN
    USE_THEN "na1" (ACCEPT_TAC o REWRITE_RULE[source_to_flatProof_abort_simps]);
    FLATP2AUX_IH_TAC "ih1" [("r",`Rerr err1:(v list,v)result`)] THEN
    ANTS_TAC THENL [FLATP2AUX_ANTS_TAC THEN REWRITE_TAC[source_to_flat_compile_exp_def]; ALL_TAC] THEN
    DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s1_i1:(C,FFI)flat_state`;
      `r1_i1:(flat_v list,flat_v)result`; `genv1:global_env`]
      (FLATP2AUX_LABEL_CONJS ["fe1"; "rr1"; "sr1"; "na1"])) THEN
    USE_THEN "rr1" (X_CHOOSE_THEN `err1':(flat_v)error_result` SUBST_ALL_TAC o
                    MATCH_MP FLATP2AUX_result_rel_Rerr) THEN
    MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`;
      `Rerr err1':(flat_v list,flat_v)result`; `genv1:global_env`] THEN
    REWRITE_TAC[flat_evaluate_def] THEN
    USE_THEN "fe1" (MP_TAC o REWRITE_RULE[source_to_flat_compile_exp_def]) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CASE_REWRITE_TAC[] THEN
    FLATP2AUX_LREWRITE_TAC ["rr1"; "sr1"; "na1"] []]);;

let FLATP2AUX_cc_Handle = prove
 (FLATP2AUX_cc_case 4,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "ear"; "lts"; "egr"; "nte"; "esi"]) THEN
  REMOVE_THEN "esi" SUBST_ALL_TAC THEN
  FLATP2AUX_PAIR_TAC `evaluate (st:(FFI)state) env [e]` `st1:(FFI)state`
    `r1:(v list,v)result` "ev1" THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  FLATP2AUX_LREWRITE_TAC ["ev1"] [] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[source_to_flat_compile_exp_def] THEN DISCH_THEN(LABEL_TAC "ev'") THEN
  SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(v list,v)result)` (LABEL_TAC "nte1") THENL
   [DISCH_THEN SUBST_ALL_TAC THEN USE_THEN "ev'" MP_TAC THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    USE_THEN "nte" MP_TAC THEN MESON_TAC[];
    ALL_TAC] THEN
  FLATP2AUX_IH_TAC "ih1" [("s'",`st1:(FFI)state`); ("r",`r1:(v list,v)result`)] THEN
  ANTS_TAC THENL [FLATP2AUX_ANTS_TAC THEN REWRITE_TAC[source_to_flat_compile_exp_def]; ALL_TAC] THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s1_i1:(C,FFI)flat_state`;
    `r1_i1:(flat_v list,flat_v)result`; `genv1:global_env`]
    (FLATP2AUX_LABEL_CONJS ["fe1"; "rr1"; "sr1"; "na1"])) THEN
  USE_THEN "fe1" (MP_TAC o MATCH_MP FLATP2AUX_flat_Handle o
                  REWRITE_RULE[source_to_flat_compile_exp_def]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REMOVE_THEN "ev'" MP_TAC THEN
  FLATP2AUX_RESULT_CASES_TAC `r1:(v list,v)result` `v1:v list` `err1:(v)error_result` THENL
   [(* value: passes through *)
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
    USE_THEN "rr1" (MP_TAC o MATCH_MP FLATP2AUX_result_rel_Rval) THEN
    DISCH_THEN(X_CHOOSE_THEN `v1':flat_v list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      (LABEL_TAC "vr1"))) THEN
    MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`;
      `Rval v1':(flat_v list,flat_v)result`; `genv1:global_env`] THEN
    CASE_REWRITE_TAC[] THEN FLATP2AUX_LREWRITE_TAC ["rr1"; "sr1"; "na1"] [];
    ALL_TAC] THEN
  CASES_ON `err1:(v)error_result` THEN CASE_REWRITE_TAC[] THENL
   [(* raise *)
    USE_THEN "rr1" (MP_TAC o REWRITE_RULE[result_rel_eqns]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ev':flat_v` (CONJUNCTS_THEN2 (LABEL_TAC "evr")
      SUBST_ALL_TAC)) THEN
    CASE_REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[PAIR_EQ] THEN USE_THEN "nte" MP_TAC THEN MESON_TAC[]] THEN
    DISCH_THEN(LABEL_TAC "evm") THEN
    USE_THEN "na1" (MP_TAC o REWRITE_RULE[source_to_flatProof_abort_simps]) THEN
    DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i1"; "eg1"; "of1"; "sc1"; "sy1"; "sg1"]) THEN
    SUBGOAL_THEN `env_all_rel genv1 comp_map env env_i1 locals` (LABEL_TAC "ear1") THENL
     [MATCH_MP_TAC env_all_rel_weak THEN EXISTS_TAC `genv:global_env` THEN
      FLATP2AUX_LREWRITE_TAC ["ear"; "sc1"; "sy1"; "sg1"] [];
      ALL_TAC] THEN
    USE_THEN "ev1" (fun ev1 -> USE_THEN "ih2" (fun ih2 ->
      LABEL_TAC "ih2'" (MATCH_MP ih2 (CONJ ev1 (ASSUME
        `can_pmatch_all (sem_env_c (env:v sem_env)) (state_refs (st1:(FFI)state))
           (MAP FST (pes:(pat#exp)list)) (a:v)`))))) THEN
    FLATP2AUX_IH_TAC "ih2'" [("genv",`genv1:global_env`); ("s_i1",`s1_i1:(C,FFI)flat_state`);
      ("v_i1",`ev':flat_v`); ("err_v_i1",`ev':flat_v`)] THEN
    ANTS_TAC THENL
     [FLATP2AUX_ANTS_TAC THEN MATCH_MP_TAC can_pmatch_all_IMP_pmatch_rows THEN
      MAP_EVERY EXISTS_TAC [`env:v sem_env`; `st1:(FFI)state`; `a:v`; `interp:(v->(source_to_flat_config#C)option)option`;
        `g:dec list->dec list`; `gen:environment_generation_store`; `genv1:global_env`;
        `idxs:next_indices#next_indices#(num#idx_types->bool)`; `env_i1:(flat_v)flat_environment`] THEN
      FLATP2AUX_LREWRITE_TAC ["i1"; "ear1"; "evr"] [] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s2_i1:(C,FFI)flat_state`;
      `r2_i1:(flat_v list,flat_v)result`; `genv2:global_env`]
      (FLATP2AUX_LABEL_CONJS ["fe2"; "rr2"; "sr2"; "na2"])) THEN
    MAP_EVERY EXISTS_TAC [`s2_i1:(C,FFI)flat_state`;
      `r2_i1:(flat_v list,flat_v)result`; `genv2:global_env`] THEN
    FLATP2AUX_LREWRITE_TAC ["fe2"; "rr2"; "sr2"] [] THEN DISCH_TAC THEN
    USE_THEN "na2" (MP_TAC o C MP (ASSUME `~source_to_flatProof_abort (r:(v list,v)result)`)) THEN
    DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i2"; "eg2"; "of2"; "sc2"; "sy2"; "sg2"]) THEN
    FLATP2AUX_LREWRITE_TAC ["i2"; "eg2"] [] THEN
    FLATP2AUX_TRANS_TAC `state_eval_state (st1:(FFI)state)` `genv1:global_env`;
    (* abort: passes through *)
    REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
    USE_THEN "rr1" (SUBST_ALL_TAC o REWRITE_RULE[result_rel_eqns]) THEN
    MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`;
      `Rerr (Rabort a):(flat_v list,flat_v)result`; `genv1:global_env`] THEN
    CASE_REWRITE_TAC[] THEN FLATP2AUX_LREWRITE_TAC ["sr1"; "na1"] [result_rel_eqns]]);;

let FLATP2AUX_cc_Con = prove
 (FLATP2AUX_cc_case 5,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih0") THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "ear"; "lts"; "egr"; "nte"; "esi"]) THEN
  REMOVE_THEN "esi" SUBST_ALL_TAC THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  COND_CASES_TAC THENL
   [POP_ASSUM(LABEL_TAC "dcc"); REWRITE_TAC[PAIR_EQ] THEN USE_THEN "nte" MP_TAC THEN MESON_TAC[]] THEN
  USE_THEN "dcc" (fun c -> USE_THEN "ih0" (fun th -> LABEL_TAC "ih1" (MATCH_MP th c))) THEN
  FLATP2AUX_PAIR_TAC `evaluate (st:(FFI)state) env (REVERSE es)` `st1:(FFI)state`
    `r1:(v list,v)result` "ev1" THEN
  FLATP2AUX_LREWRITE_TAC ["ev1"] [] THEN CASE_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ev'") THEN
  SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(v list,v)result)` (LABEL_TAC "nte1") THENL
   [DISCH_THEN SUBST_ALL_TAC THEN USE_THEN "ev'" MP_TAC THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    USE_THEN "nte" MP_TAC THEN MESON_TAC[];
    ALL_TAC] THEN
  FLATP2AUX_IH_TAC "ih1" [("s'",`st1:(FFI)state`); ("r",`r1:(v list,v)result`)] THEN
  ANTS_TAC THENL [FLATP2AUX_ANTS_TAC; ALL_TAC] THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s1_i1:(C,FFI)flat_state`;
    `r1_i1:(flat_v list,flat_v)result`; `genv1:global_env`]
    (FLATP2AUX_LABEL_CONJS ["fe1"; "rr1"; "sr1"; "na1"])) THEN
  USE_THEN "fe1" (LABEL_TAC "fe1'" o REWRITE_RULE[compile_exps_reverse]) THEN
  REWRITE_TAC[source_to_flat_compile_exp_def] THEN
  REMOVE_THEN "ev'" MP_TAC THEN
  FLATP2AUX_RESULT_CASES_TAC `r1:(v list,v)result` `v1:v list` `err1:(v)error_result` THENL
   [ALL_TAC;
    (* error: passes through *)
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
    USE_THEN "rr1" (X_CHOOSE_THEN `err1':(flat_v)error_result` SUBST_ALL_TAC o
                    MATCH_MP FLATP2AUX_result_rel_Rerr) THEN
    MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`;
      `Rerr err1':(flat_v list,flat_v)result`; `genv1:global_env`] THEN
    CASES_ON `cn:((modN,conN)id)option` THEN
    REWRITE_TAC[OPTION_MAP_DEF; OPTION_JOIN_DEF; flat_evaluate_def; o_THM] THEN
    TRY(CASES_ON `type_group_id_type (nsLookup (source_to_flat_environment_c
      (source_to_flat_environment_v_fupd (K (bind_locals ts locals
        (source_to_flat_environment_v comp_map))) comp_map)) a)`) THEN
    REWRITE_TAC[OPTION_JOIN_DEF; flat_evaluate_def] THEN
    FLATP2AUX_LREWRITE_TAC ["fe1'"] [] THEN CASE_REWRITE_TAC[] THEN
    FLATP2AUX_LREWRITE_TAC ["rr1"; "sr1"; "na1"] []] THEN
  CASE_REWRITE_TAC[] THEN
  USE_THEN "rr1" (MP_TAC o MATCH_MP FLATP2AUX_result_rel_Rval) THEN
  DISCH_THEN(X_CHOOSE_THEN `v1':flat_v list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (LABEL_TAC "vr1"))) THEN
  USE_THEN "na1" (MP_TAC o REWRITE_RULE[source_to_flatProof_abort_simps]) THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i1"; "eg1"; "of1"; "sc1"; "sy1"; "sg1"]) THEN
  USE_THEN "vr1" (LABEL_TAC "vr1r" o MATCH_MP LIST_REL_REVERSE o REWRITE_RULE[o_THM]) THEN
  CASES_ON `cn:((modN,conN)id)option` THENL
   [REWRITE_TAC[build_conv_def] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`;
      `Rval [flat_Conv NONE (REVERSE v1')]:(flat_v list,flat_v)result`; `genv1:global_env`] THEN
    REWRITE_TAC[OPTION_MAP_DEF; OPTION_JOIN_DEF; flat_evaluate_def] THEN
    FLATP2AUX_LREWRITE_TAC ["fe1'"] [] THEN CASE_REWRITE_TAC[] THEN
    FLATP2AUX_LREWRITE_TAC ["sr1"; "i1"; "eg1"; "of1"; "sc1"; "sy1"; "sg1"]
      [result_rel_eqns; source_to_flatProof_abort_simps; o_THM; ALL2] THEN
    FLATP2AUX_LKSIMP_TAC ["vr1r"] [v_rel_eqns];
    ALL_TAC] THEN
  REWRITE_TAC[build_conv_def] THEN CASE_REWRITE_TAC[] THEN
  USE_THEN "dcc" (MP_TAC o REWRITE_RULE[do_con_check_def]) THEN CASE_REWRITE_TAC[] THEN
  FLATP2AUX_OPTION_CASES_TAC `nsLookup (sem_env_c (env:v sem_env)) (a:(modN,conN)id)`
    `ls:num#stamp` "lkenv" THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[] THEN
  MP_TAC(ISPEC `ls:num#stamp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `arity:num` (X_CHOOSE_THEN `stamp:stamp` SUBST_ALL_TAC)) THEN
  CASE_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "len") THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
  MP_TAC(ISPECL [`genv:global_env`; `comp_map:source_to_flat_environment`; `env:v sem_env`;
    `env_i1:(flat_v)flat_environment`; `locals:mlstring list`; `a:(modN,conN)id`;
    `arity:num`; `stamp:stamp`] FLATP2AUX_env_all_rel_c) THEN
  FLATP2AUX_LREWRITE_TAC ["ear"; "lkenv"] [] THEN
  DISCH_THEN(X_CHOOSE_THEN `cn':ctor_id` (X_CHOOSE_THEN `ty_gp:type_group_id`
    (FLATP2AUX_LABEL_CONJS ["lkc"; "flk"; "tys"]))) THEN
  MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`;
    `Rval [flat_Conv (SOME (cn', OPTION_MAP FST (ty_gp:type_group_id))) (REVERSE v1')]:
       (flat_v list,flat_v)result`; `genv1:global_env`] THEN
  SIMP_NOASM[OPTION_MAP_DEF; OPTION_JOIN_DEF; o_THM; type_group_id_type_MAP] THEN
  FLATP2AUX_LREWRITE_TAC ["lkc"] [OPTION_MAP_DEF; OPTION_JOIN_DEF; PAIR_MAP_THM; I_THM;
                                 flat_evaluate_def] THEN
  FLATP2AUX_LREWRITE_TAC ["fe1'"] [] THEN CASE_REWRITE_TAC[] THEN
  FLATP2AUX_LREWRITE_TAC ["sr1"; "i1"; "eg1"; "of1"; "sc1"; "sy1"; "sg1"]
    [result_rel_eqns; source_to_flatProof_abort_simps; o_THM; ALL2] THEN
  FLATP2AUX_LKSIMP_TAC ["vr1r"] [v_rel_eqns; LENGTH_REVERSE] THEN
  USE_THEN "ev1" (MP_TAC o MATCH_MP (CONJUNCT1 evaluate_length)) THEN
  REWRITE_TAC[LENGTH_REVERSE] THEN FLATP2AUX_LREWRITE_TAC ["len"] [] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC FLOOKUP_SUBMAP THEN
  EXISTS_TAC `global_env_c genv` THEN FLATP2AUX_LREWRITE_TAC ["sc1"; "flk"] []);;

let FLATP2AUX_cc_Var = prove
 (FLATP2AUX_cc_case 6,
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "ear"; "lts"; "egr"; "nte"; "esi"]) THEN
  REMOVE_THEN "esi" SUBST_ALL_TAC THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  FLATP2AUX_OPTION_CASES_TAC `nsLookup (sem_env_v (env:v sem_env)) n` `v:v` "lkv" THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THENL
   [USE_THEN "nte" MP_TAC THEN MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
  USE_THEN "ear" (MP_TAC o REWRITE_RULE[env_all_rel_cases]) THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`evl:(modN,varN,v)namespace`; `env0:v sem_env`;
    `env1:(varN#flat_v)list`] (FLATP2AUX_LABEL_CONJS ["envq"; "ei1q"; "lq"; "gei"; "er"])) THEN
  REMOVE_THEN "envq" SUBST_ALL_TAC THEN REMOVE_THEN "ei1q" SUBST_ALL_TAC THEN
  REMOVE_THEN "lq" (X_CHOOSE_THEN `l:(varN#v)list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (LABEL_TAC "lfst"))) THEN
  REMOVE_THEN "lfst" (SUBST_ALL_TAC o SYM) THEN
  USE_THEN "lkv" (MP_TAC o SIMP_RULE[sem_env_INFO.ri_accessors]) THEN
  REWRITE_TAC[FLATP2AUX_nsLookup_nsAppend_alist] THEN
  REWRITE_TAC[source_to_flat_compile_exp_def] THEN
  SIMP_NOASM[bind_locals_def; GSYM nsAppend_to_nsBindList; FLATP2AUX_nsLookup_nsAppend_alist] THEN
  USE_THEN "gei" (MP_TAC o CONJUNCT1 o REWRITE_RULE[v_rel_global_eqn]) THEN
  DISCH_THEN(LABEL_TAC "geiv") THEN
  FLATP2AUX_SUBGOAL
   {|!x. ~(x IN IMAGE Short (set_of_list (MAP FST (l:(varN#v)list)))) /\
        nsLookup (sem_env_v env0) x = SOME v
        ==> (?s'_i1 r_i1 genv'.
              flat_evaluate (flat_environment_REC env1) s_i1
               [compile_var backend_common_None
                  (THE (nsLookup (source_to_flat_environment_v comp_map) x))] =
               s'_i1,r_i1 /\
              source_to_flatProof_result_rel (ALL2 o source_to_flatProof_v_rel) genv'
                (Rval [v]) r_i1 /\
              source_to_flatProof_s_rel genv' s' s'_i1 /\
              invariant interp g gen genv' idxs s' s'_i1 /\
              env_gen_rel gen (state_eval_state s') /\
              orac_forward_rel interp (state_eval_state s') (state_eval_state s') /\
              global_env_c genv SUBMAP global_env_c genv' /\
              global_env_tys genv SUBMAP global_env_tys genv' /\
              subglobals (global_env_v genv) (global_env_v genv')) /\
            ?vn. nsLookup (source_to_flat_environment_v comp_map) x = SOME vn|}
    (LABEL_TAC "glob") THENL
   [X_GEN_TAC `x:(modN,varN)id` THEN STRIP_TAC THEN
    REMOVE_THEN "geiv" (MP_TAC o SPECL [`x:(modN,varN)id`; `v:v`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n':num` (X_CHOOSE_THEN `v':flat_v` (X_CHOOSE_THEN `tr:tra`
      (FLATP2AUX_LABEL_CONJS ["glk"; "nlt"; "gel"; "vr"])))) THEN
    FLATP2AUX_LREWRITE_TAC ["glk"] [THE_DEF; compile_var_def] THEN
    CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    MAP_EVERY EXISTS_TAC [`s_i1:(C,FFI)flat_state`; `Rval [v']:(flat_v list,flat_v)result`;
                          `genv:global_env`] THEN
    USE_THEN "inv" (ASSUME_TAC o MATCH_MP invariant_globals) THEN
    SUBGOAL_THEN `flat_evaluate (flat_environment_REC env1) (s_i1:(C,FFI)flat_state)
       [flat_App backend_common_None (GlobalVarLookup n') []] = (s_i1, Rval [v'])`
       SUBST1_TAC THENL
     [MATCH_MP_TAC FLATP2AUX_flat_eval_global THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FLATP2AUX_LREWRITE_TAC ["inv"; "egr"; "vr"]
      [SUBMAP_REFL; subglobals_refl; orac_forward_rel_refl; result_rel_eqns; o_THM; ALL2] THEN
    FLATP2AUX_LKSIMP_TAC ["vr"] [ALL2] THEN
    USE_THEN "inv" (ACCEPT_TAC o MATCH_MP invariant_IMP_s_rel);
    ALL_TAC] THEN
  CASES_ON `n:(modN,varN)id` THEN CASE_REWRITE_TAC[] THENL
   [FLATP2AUX_OPTION_CASES_TAC `ALOOKUP (l:(varN#v)list) a` `vl:v` "alk" THEN
    CASE_REWRITE_TAC[] THENL
     [DISCH_TAC THEN
      USE_THEN "alk" (LABEL_TAC "nmem" o REWRITE_RULE[ALOOKUP_NONE]) THEN
      MP_TAC(ISPECL [`MAP FST (l:(varN#v)list)`; `ts:(tra)list`; `a:varN`]
        FLATP2AUX_ALOOKUP_MAP2_Local) THEN
      FLATP2AUX_LREWRITE_TAC ["lts"; "nmem"] [] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      CASE_REWRITE_TAC[] THEN
      REMOVE_THEN "glob" (MP_TAC o SPEC `Short a:(modN,varN)id`) THEN
      ASM_REWRITE_TAC[IN_IMAGE; injectivity "id"; UNWIND_THM1; IN_SET_OF_LIST] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `vn:var_name` ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[THE_DEF; orac_forward_rel_refl] THEN CASE_REWRITE_TAC[];
      REWRITE_TAC[injectivity "option"] THEN DISCH_THEN SUBST_ALL_TAC THEN
      SUBGOAL_THEN `MEM (a:varN) (MAP FST (l:(varN#v)list))` (LABEL_TAC "mem") THENL
       [REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `(a:varN),(v:v)` THEN
        USE_THEN "alk" (fun th -> REWRITE_TAC[MATCH_MP ALOOKUP_MEM th; FST]);
        ALL_TAC] THEN
      MP_TAC(ISPECL [`MAP FST (l:(varN#v)list)`; `ts:(tra)list`; `a:varN`]
        FLATP2AUX_ALOOKUP_MAP2_Local) THEN
      FLATP2AUX_LREWRITE_TAC ["lts"; "mem"] [] THEN
      DISCH_THEN(X_CHOOSE_THEN `tr:tra` (fun th -> REWRITE_TAC[th]) o CONJUNCT2) THEN
      CASE_REWRITE_TAC[] THEN REWRITE_TAC[compile_var_def; flat_evaluate_def] THEN
      MP_TAC(ISPECL [`genv:global_env`; `l:(varN#v)list`; `a:varN`; `v:v`; `env1:(varN#flat_v)list`]
        env_rel_lookup) THEN
      FLATP2AUX_LREWRITE_TAC ["alk"; "er"] [] THEN
      DISCH_THEN(X_CHOOSE_THEN `v':flat_v` (CONJUNCTS_THEN2 (LABEL_TAC "vr") (LABEL_TAC "alk1"))) THEN
      FLATP2AUX_LREWRITE_TAC ["alk1"] [] THEN CASE_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`s_i1:(C,FFI)flat_state`; `Rval [v']:(flat_v list,flat_v)result`;
                            `genv:global_env`] THEN
      FLATP2AUX_LREWRITE_TAC ["inv"; "egr"]
        [SUBMAP_REFL; subglobals_refl; orac_forward_rel_refl; result_rel_eqns; o_THM; ALL2] THEN
      FLATP2AUX_LKSIMP_TAC ["vr"] [ALL2] THEN
      FLATP2AUX_LREWRITE_TAC ["alk1"] [] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[] THEN
      USE_THEN "inv" (ACCEPT_TAC o MATCH_MP invariant_IMP_s_rel)];
    DISCH_TAC THEN
    REMOVE_THEN "glob" (MP_TAC o SPEC `Long a0 a1:(modN,varN)id`) THEN
    ASM_REWRITE_TAC[IN_IMAGE; distinctness "id"] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `vn:var_name` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[THE_DEF; orac_forward_rel_refl] THEN CASE_REWRITE_TAC[]]);;

let FLATP2AUX_cc_Fun = prove
 (FLATP2AUX_cc_case 7,
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "ear"; "lts"; "egr"; "nte"; "esi"]) THEN
  REMOVE_THEN "esi" SUBST_ALL_TAC THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[source_to_flat_compile_exp_def; flat_evaluate_def] THEN
  MAP_EVERY EXISTS_TAC [`s_i1:(C,FFI)flat_state`;
    `Rval [flat_Closure env_i1 x (source_to_flat_compile_exp t
       (source_to_flat_environment_v_fupd
         (K (nsBind x (source_to_flat_Local backend_common_None x)
               (bind_locals ts locals (source_to_flat_environment_v comp_map))))
         comp_map) e)]:(flat_v list,flat_v)result`; `genv:global_env`] THEN
  SIMP_NOASM[] THEN
  FLATP2AUX_LREWRITE_TAC ["inv"; "egr"]
    [SUBMAP_REFL; subglobals_refl; orac_forward_rel_refl; result_rel_eqns; o_THM; ALL2;
     source_to_flatProof_abort_simps] THEN
  SIMP_NOASM[ALL2] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FLATP2AUX_v_rel_closure THEN
    FLATP2AUX_LREWRITE_TAC ["ear"; "lts"] [];
    USE_THEN "inv" (ACCEPT_TAC o MATCH_MP invariant_IMP_s_rel)]);;
let FLATP2AUX_cc_nil = prove
 (FLATP2AUX_cc_case 0,
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "ear"; "lts"; "egr"; "nte"; "esi"]) THEN
  REMOVE_THEN "esi" SUBST_ALL_TAC THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[source_to_flat_compile_exp_def; flat_evaluate_def] THEN
  MAP_EVERY EXISTS_TAC [`s_i1:(C,FFI)flat_state`; `Rval []:(flat_v list,flat_v)result`;
                        `genv:global_env`] THEN
  FLATP2AUX_LREWRITE_TAC ["inv"; "egr"]
    [SUBMAP_REFL; subglobals_refl; orac_forward_rel_refl; result_rel_eqns; o_THM; ALL2;
     source_to_flatProof_abort_simps] THEN
  SIMP_NOASM[ALL2] THEN USE_THEN "inv" (ACCEPT_TAC o MATCH_MP invariant_IMP_s_rel));;

let FLATP2AUX_cc_Lit = prove
 (FLATP2AUX_cc_case 2,
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "ear"; "lts"; "egr"; "nte"; "esi"]) THEN
  REMOVE_THEN "esi" SUBST_ALL_TAC THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[source_to_flat_compile_exp_def; flat_evaluate_def] THEN
  MAP_EVERY EXISTS_TAC [`s_i1:(C,FFI)flat_state`; `Rval [flat_Litv l]:(flat_v list,flat_v)result`;
                        `genv:global_env`] THEN
  FLATP2AUX_LREWRITE_TAC ["inv"; "egr"]
    [SUBMAP_REFL; subglobals_refl; orac_forward_rel_refl; result_rel_eqns; o_THM; ALL2;
     source_to_flatProof_abort_simps; v_rel_eqns] THEN
  SIMP_NOASM[ALL2; v_rel_eqns] THEN USE_THEN "inv" (ACCEPT_TAC o MATCH_MP invariant_IMP_s_rel));;

let FLATP2AUX_cc_Tannot = prove
 (FLATP2AUX_cc_case 14,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih1") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "ear"; "lts"; "egr"; "nte"; "esi"]) THEN
  REMOVE_THEN "esi" SUBST_ALL_TAC THEN
  USE_THEN "ev" (LABEL_TAC "ev'" o REWRITE_RULE[full_evaluate_def]) THEN
  REWRITE_TAC[source_to_flat_compile_exp_def] THEN
  FLATP2AUX_IH_TAC "ih1" [("t",`t':mlstring list`)] THEN
  ANTS_TAC THENL [FLATP2AUX_ANTS_TAC THEN REWRITE_TAC[source_to_flat_compile_exp_def];
                  REWRITE_TAC[source_to_flat_compile_exp_def]]);;

let FLATP2AUX_cc_Lannot = prove
 (FLATP2AUX_cc_case 15,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih1") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "ear"; "lts"; "egr"; "nte"; "esi"]) THEN
  REMOVE_THEN "esi" SUBST_ALL_TAC THEN
  USE_THEN "ev" (LABEL_TAC "ev'" o REWRITE_RULE[full_evaluate_def]) THEN
  CASES_ON `l:locs` THEN REWRITE_TAC[source_to_flat_compile_exp_def] THEN
  FLATP2AUX_IH_TAC "ih1" [] THEN
  ANTS_TAC THENL [FLATP2AUX_ANTS_TAC THEN REWRITE_TAC[source_to_flat_compile_exp_def];
                  REWRITE_TAC[source_to_flat_compile_exp_def]]);;

let FLATP2AUX_cc_match_nil = prove
 (FLATP2AUX_cc_case 16,
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "ear"; "vr"; "lts"; "egr"; "nte"; "pesi";
                                    "pmr"; "evr"]) THEN
  REMOVE_THEN "pesi" SUBST_ALL_TAC THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[source_to_flat_compile_exp_def; flat_evaluate_match_def; pmatch_rows_def] THEN
  CASE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`s_i1:(C,FFI)flat_state`;
    `Rerr (Rraise err_v_i1):(flat_v list,flat_v)result`; `genv:global_env`] THEN
  FLATP2AUX_LREWRITE_TAC ["inv"; "egr"; "evr"]
    [SUBMAP_REFL; subglobals_refl; orac_forward_rel_refl; result_rel_eqns;
     source_to_flatProof_abort_simps] THEN
  SIMP_NOASM[] THEN FLATP2AUX_LREWRITE_TAC ["evr"] [] THEN
  USE_THEN "inv" (ACCEPT_TAC o MATCH_MP invariant_IMP_s_rel));;

let FLATP2AUX_cc_Log = prove
 (FLATP2AUX_cc_case 9,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "ear"; "lts"; "egr"; "nte"; "esi"]) THEN
  REMOVE_THEN "esi" SUBST_ALL_TAC THEN
  FLATP2AUX_PAIR_TAC `evaluate (st:(FFI)state) env [e1]` `st1:(FFI)state`
    `r1:(v list,v)result` "ev1" THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  FLATP2AUX_LREWRITE_TAC ["ev1"] [] THEN CASE_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ev'") THEN
  SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(v list,v)result)` (LABEL_TAC "nte1") THENL
   [DISCH_THEN SUBST_ALL_TAC THEN USE_THEN "ev'" MP_TAC THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    USE_THEN "nte" MP_TAC THEN MESON_TAC[];
    ALL_TAC] THEN
  FLATP2AUX_IH_TAC "ih1" [("s'",`st1:(FFI)state`); ("r",`r1:(v list,v)result`)] THEN
  ANTS_TAC THENL [FLATP2AUX_ANTS_TAC THEN REWRITE_TAC[source_to_flat_compile_exp_def]; ALL_TAC] THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s1_i1:(C,FFI)flat_state`;
    `r1_i1:(flat_v list,flat_v)result`; `genv1:global_env`]
    (FLATP2AUX_LABEL_CONJS ["fe1"; "rr1"; "sr1"; "na1"])) THEN
  USE_THEN "fe1" (LABEL_TAC "fe1'" o REWRITE_RULE[source_to_flat_compile_exp_def]) THEN
  FLATP2AUX_SUBGOAL {|!tg e2 e3. flat_evaluate env_i1 s_i1 [flat_If tg
      (source_to_flat_compile_exp t
        (source_to_flat_environment_v_fupd
          (K (bind_locals ts locals (source_to_flat_environment_v comp_map))) comp_map) e1)
      e2 e3] =
      (match r1_i1 with
         Rval vs -> (match flat_do_if (HD vs) e2 e3 with
                       SOME e -> flat_evaluate env_i1 s1_i1 [e]
                     | NONE -> (s1_i1, Rerr (Rabort Rtype_error)))
       | Rerr e -> (s1_i1, r1_i1))|} (LABEL_TAC "fif") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC FLATP2AUX_flat_If THEN FLATP2AUX_LREWRITE_TAC ["fe1'"] [];
    ALL_TAC] THEN
  REWRITE_TAC[source_to_flat_compile_exp_def] THEN REMOVE_THEN "ev'" MP_TAC THEN
  FLATP2AUX_RESULT_CASES_TAC `r1:(v list,v)result` `v1:v list` `err1:(v)error_result` THENL
   [ALL_TAC;
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
    USE_THEN "rr1" (X_CHOOSE_THEN `err1':(flat_v)error_result` SUBST_ALL_TAC o
                    MATCH_MP FLATP2AUX_result_rel_Rerr) THEN
    MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`;
      `Rerr err1':(flat_v list,flat_v)result`; `genv1:global_env`] THEN
    CASES_ON `lop:lop` THEN CASE_REWRITE_TAC[] THEN
    FLATP2AUX_LREWRITE_TAC ["fif"] [] THEN CASE_REWRITE_TAC[] THEN
    FLATP2AUX_LREWRITE_TAC ["rr1"; "sr1"; "na1"] []] THEN
  USE_THEN "rr1" (MP_TAC o MATCH_MP FLATP2AUX_result_rel_Rval) THEN
  DISCH_THEN(X_CHOOSE_THEN `v1':flat_v list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (LABEL_TAC "vr1"))) THEN
  USE_THEN "na1" (MP_TAC o REWRITE_RULE[source_to_flatProof_abort_simps]) THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i1"; "eg1"; "of1"; "sc1"; "sy1"; "sg1"]) THEN
  USE_THEN "ev1" (X_CHOOSE_THEN `x1:v` SUBST_ALL_TAC o MATCH_MP evaluate_sing) THEN
  USE_THEN "vr1" (MP_TAC o REWRITE_RULE[o_THM; LIST_REL_CONS1; LIST_REL_NIL]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x1':flat_v` (X_CHOOSE_THEN `tl1:flat_v list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 (LABEL_TAC "xr1") SUBST_ALL_TAC)))) THEN
  USE_THEN "i1" (LABEL_TAC "cok1" o MATCH_MP invariant_genv_c_ok) THEN
  USE_THEN "i1" (LABEL_TAC "srl1" o MATCH_MP invariant_IMP_s_rel) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD; do_log_def] THEN
  ASM_CASES_TAC `x1 = Boolv T` THENL
   [ALL_TAC;
    ASM_CASES_TAC `x1 = Boolv F` THENL
     [ALL_TAC;
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
      USE_THEN "nte" MP_TAC THEN MESON_TAC[]]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  USE_THEN "cok1" (fun c -> USE_THEN "xr1" (fun xr ->
    SUBST_ALL_TAC (REWRITE_RULE[MATCH_MP v_rel_Bool_eqn c] xr))) THEN
  REWRITE_TAC[semanticPrimitivesProps_Boolv_11] THEN
  CASES_ON `lop:lop` THEN REWRITE_TAC[distinctness "lop"] THEN CASE_REWRITE_TAC[] THEN
  FLATP2AUX_LREWRITE_TAC ["fif"] [] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[HD; flat_do_if_def; source_to_flatProof_Boolv_11] THEN CASE_REWRITE_TAC[] THEN
  let exp_case (b:term) : tactic =
    DISCH_THEN(LABEL_TAC "ev2") THEN
    USE_THEN "ih2" (MP_TAC o SPECL [mk_list([mk_comb(`Boolv`,b)],`:v`); `st1:(FFI)state`;
                                    `e2:exp`]) THEN
    FLATP2AUX_LREWRITE_TAC ["ev1"] [HD; do_log_def; semanticPrimitivesProps_Boolv_11;
                                   distinctness "lop"] THEN
    DISCH_THEN(LABEL_TAC "ih2'") THEN
    FLATP2AUX_SUBGOAL {|env_all_rel genv1 comp_map env env_i1 locals|} (LABEL_TAC "ear1") THENL
     [MATCH_MP_TAC env_all_rel_weak THEN EXISTS_TAC `genv:global_env` THEN
      FLATP2AUX_LREWRITE_TAC ["ear"; "sc1"; "sy1"; "sg1"] [];
      ALL_TAC] THEN
    FLATP2AUX_IH_TAC "ih2'" [("genv",`genv1:global_env`); ("s_i1",`s1_i1:(C,FFI)flat_state`)] THEN
    ANTS_TAC THENL [FLATP2AUX_ANTS_TAC; ALL_TAC] THEN
    DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s2_i1:(C,FFI)flat_state`;
      `r2_i1:(flat_v list,flat_v)result`; `genv2:global_env`]
      (FLATP2AUX_LABEL_CONJS ["fe2"; "rr2"; "sr2"; "na2"])) THEN
    MAP_EVERY EXISTS_TAC [`s2_i1:(C,FFI)flat_state`; `r2_i1:(flat_v list,flat_v)result`;
                          `genv2:global_env`] THEN
    USE_THEN "fe2" (MP_TAC o REWRITE_RULE[source_to_flat_compile_exp_def]) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    FLATP2AUX_LREWRITE_TAC ["rr2"; "sr2"] [] THEN DISCH_TAC THEN
    USE_THEN "na2" (MP_TAC o C MP (ASSUME `~source_to_flatProof_abort (r:(v list,v)result)`)) THEN
    DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i2"; "eg2"; "of2"; "sc2"; "sy2"; "sg2"]) THEN
    FLATP2AUX_LREWRITE_TAC ["i2"; "eg2"] [] THEN
    FLATP2AUX_TRANS_TAC `state_eval_state (st1:(FFI)state)` `genv1:global_env` in
  let val_case (b:term) : tactic =
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`;
      mk_comb(`Rval:flat_v list->(flat_v list,flat_v)result`,
              mk_list([mk_comb(`flat_Boolv`,b)],`:flat_v`)); `genv1:global_env`] THEN
    USE_THEN "srl1" (fun sr -> USE_THEN "cok1" (fun c ->
      REWRITE_TAC[MATCH_MP source_to_flatProof_evaluate_Bool (CONJ sr c);
                  MATCH_MP v_rel_Bool_eqn c])) THEN
    FLATP2AUX_LREWRITE_TAC ["sr1"; "i1"; "eg1"; "of1"; "sc1"; "sy1"; "sg1"]
      [result_rel_eqns; source_to_flatProof_abort_simps; o_THM; ALL2] THEN
    USE_THEN "cok1" (fun c -> SIMP_NOASM[ALL2; MATCH_MP v_rel_Bool_eqn c]) in
  FIRST (map (fun tc -> tc THEN NO_TAC)
               [exp_case `T`; val_case `T`; val_case `F`; exp_case `F`]));;

let FLATP2AUX_cc_If = prove
 (FLATP2AUX_cc_case 10,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "ear"; "lts"; "egr"; "nte"; "esi"]) THEN
  REMOVE_THEN "esi" SUBST_ALL_TAC THEN
  FLATP2AUX_PAIR_TAC `evaluate (st:(FFI)state) env [e1]` `st1:(FFI)state`
    `r1:(v list,v)result` "ev1" THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  FLATP2AUX_LREWRITE_TAC ["ev1"] [] THEN CASE_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ev'") THEN
  SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(v list,v)result)` (LABEL_TAC "nte1") THENL
   [DISCH_THEN SUBST_ALL_TAC THEN USE_THEN "ev'" MP_TAC THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    USE_THEN "nte" MP_TAC THEN MESON_TAC[];
    ALL_TAC] THEN
  FLATP2AUX_IH_TAC "ih1" [("s'",`st1:(FFI)state`); ("r",`r1:(v list,v)result`)] THEN
  ANTS_TAC THENL [FLATP2AUX_ANTS_TAC THEN REWRITE_TAC[source_to_flat_compile_exp_def]; ALL_TAC] THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s1_i1:(C,FFI)flat_state`;
    `r1_i1:(flat_v list,flat_v)result`; `genv1:global_env`]
    (FLATP2AUX_LABEL_CONJS ["fe1"; "rr1"; "sr1"; "na1"])) THEN
  USE_THEN "fe1" (LABEL_TAC "fe1'" o REWRITE_RULE[source_to_flat_compile_exp_def]) THEN
  FLATP2AUX_SUBGOAL {|!tg e2 e3. flat_evaluate env_i1 s_i1 [flat_If tg
      (source_to_flat_compile_exp t
        (source_to_flat_environment_v_fupd
          (K (bind_locals ts locals (source_to_flat_environment_v comp_map))) comp_map) e1)
      e2 e3] =
      (match r1_i1 with
         Rval vs -> (match flat_do_if (HD vs) e2 e3 with
                       SOME e -> flat_evaluate env_i1 s1_i1 [e]
                     | NONE -> (s1_i1, Rerr (Rabort Rtype_error)))
       | Rerr e -> (s1_i1, r1_i1))|} (LABEL_TAC "fif") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC FLATP2AUX_flat_If THEN FLATP2AUX_LREWRITE_TAC ["fe1'"] [];
    ALL_TAC] THEN
  REWRITE_TAC[source_to_flat_compile_exp_def] THEN REMOVE_THEN "ev'" MP_TAC THEN
  FLATP2AUX_RESULT_CASES_TAC `r1:(v list,v)result` `v1:v list` `err1:(v)error_result` THENL
   [ALL_TAC;
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
    USE_THEN "rr1" (X_CHOOSE_THEN `err1':(flat_v)error_result` SUBST_ALL_TAC o
                    MATCH_MP FLATP2AUX_result_rel_Rerr) THEN
    MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`;
      `Rerr err1':(flat_v list,flat_v)result`; `genv1:global_env`] THEN
    FLATP2AUX_LREWRITE_TAC ["fif"] [] THEN CASE_REWRITE_TAC[] THEN
    FLATP2AUX_LREWRITE_TAC ["rr1"; "sr1"; "na1"] []] THEN
  USE_THEN "rr1" (MP_TAC o MATCH_MP FLATP2AUX_result_rel_Rval) THEN
  DISCH_THEN(X_CHOOSE_THEN `v1':flat_v list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (LABEL_TAC "vr1"))) THEN
  USE_THEN "na1" (MP_TAC o REWRITE_RULE[source_to_flatProof_abort_simps]) THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i1"; "eg1"; "of1"; "sc1"; "sy1"; "sg1"]) THEN
  USE_THEN "ev1" (X_CHOOSE_THEN `x1:v` SUBST_ALL_TAC o MATCH_MP evaluate_sing) THEN
  USE_THEN "vr1" (MP_TAC o REWRITE_RULE[o_THM; LIST_REL_CONS1; LIST_REL_NIL]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x1':flat_v` (X_CHOOSE_THEN `tl1:flat_v list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 (LABEL_TAC "xr1") SUBST_ALL_TAC)))) THEN
  USE_THEN "i1" (LABEL_TAC "cok1" o MATCH_MP invariant_genv_c_ok) THEN
  USE_THEN "i1" (LABEL_TAC "srl1" o MATCH_MP invariant_IMP_s_rel) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD; do_if_def] THEN
  ASM_CASES_TAC `x1 = Boolv T` THENL
   [ALL_TAC;
    ASM_CASES_TAC `x1 = Boolv F` THENL
     [ALL_TAC;
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
      USE_THEN "nte" MP_TAC THEN MESON_TAC[]]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  USE_THEN "cok1" (fun c -> USE_THEN "xr1" (fun xr ->
    SUBST_ALL_TAC (REWRITE_RULE[MATCH_MP v_rel_Bool_eqn c] xr))) THEN
  REWRITE_TAC[semanticPrimitivesProps_Boolv_11] THEN CASE_REWRITE_TAC[] THEN
  FLATP2AUX_LREWRITE_TAC ["fif"] [] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[HD; flat_do_if_def; source_to_flatProof_Boolv_11] THEN CASE_REWRITE_TAC[] THEN
  let exp_case (b:term) (e:term) : tactic =
    DISCH_THEN(LABEL_TAC "ev2") THEN
    USE_THEN "ih2" (MP_TAC o SPECL [mk_list([mk_comb(`Boolv`,b)],`:v`); `st1:(FFI)state`; e]) THEN
    FLATP2AUX_LREWRITE_TAC ["ev1"] [HD; do_if_def; semanticPrimitivesProps_Boolv_11] THEN
    DISCH_THEN(LABEL_TAC "ih2'") THEN
    FLATP2AUX_SUBGOAL {|env_all_rel genv1 comp_map env env_i1 locals|} (LABEL_TAC "ear1") THENL
     [MATCH_MP_TAC env_all_rel_weak THEN EXISTS_TAC `genv:global_env` THEN
      FLATP2AUX_LREWRITE_TAC ["ear"; "sc1"; "sy1"; "sg1"] [];
      ALL_TAC] THEN
    FLATP2AUX_IH_TAC "ih2'" [("genv",`genv1:global_env`); ("s_i1",`s1_i1:(C,FFI)flat_state`)] THEN
    ANTS_TAC THENL [FLATP2AUX_ANTS_TAC; ALL_TAC] THEN
    DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s2_i1:(C,FFI)flat_state`;
      `r2_i1:(flat_v list,flat_v)result`; `genv2:global_env`]
      (FLATP2AUX_LABEL_CONJS ["fe2"; "rr2"; "sr2"; "na2"])) THEN
    MAP_EVERY EXISTS_TAC [`s2_i1:(C,FFI)flat_state`; `r2_i1:(flat_v list,flat_v)result`;
                          `genv2:global_env`] THEN
    USE_THEN "fe2" (MP_TAC o REWRITE_RULE[source_to_flat_compile_exp_def]) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    FLATP2AUX_LREWRITE_TAC ["rr2"; "sr2"] [] THEN DISCH_TAC THEN
    USE_THEN "na2" (MP_TAC o C MP (ASSUME `~source_to_flatProof_abort (r:(v list,v)result)`)) THEN
    DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i2"; "eg2"; "of2"; "sc2"; "sy2"; "sg2"]) THEN
    FLATP2AUX_LREWRITE_TAC ["i2"; "eg2"] [] THEN
    FLATP2AUX_TRANS_TAC `state_eval_state (st1:(FFI)state)` `genv1:global_env` in
  FIRST (map (fun tc -> tc THEN NO_TAC) [exp_case `T` `e2:exp`; exp_case `F` `e3:exp`]));;

let FLATP2AUX_cc_Mat = prove
 (FLATP2AUX_cc_case 11,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "ear"; "lts"; "egr"; "nte"; "esi"]) THEN
  REMOVE_THEN "esi" SUBST_ALL_TAC THEN
  FLATP2AUX_PAIR_TAC `evaluate (st:(FFI)state) env [e]` `st1:(FFI)state`
    `r1:(v list,v)result` "ev1" THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  FLATP2AUX_LREWRITE_TAC ["ev1"] [] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[source_to_flat_compile_exp_def] THEN DISCH_THEN(LABEL_TAC "ev'") THEN
  SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(v list,v)result)` (LABEL_TAC "nte1") THENL
   [DISCH_THEN SUBST_ALL_TAC THEN USE_THEN "ev'" MP_TAC THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    USE_THEN "nte" MP_TAC THEN MESON_TAC[];
    ALL_TAC] THEN
  FLATP2AUX_IH_TAC "ih1" [("s'",`st1:(FFI)state`); ("r",`r1:(v list,v)result`)] THEN
  ANTS_TAC THENL [FLATP2AUX_ANTS_TAC THEN REWRITE_TAC[source_to_flat_compile_exp_def]; ALL_TAC] THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s1_i1:(C,FFI)flat_state`;
    `r1_i1:(flat_v list,flat_v)result`; `genv1:global_env`]
    (FLATP2AUX_LABEL_CONJS ["fe1"; "rr1"; "sr1"; "na1"])) THEN
  USE_THEN "fe1" (MP_TAC o MATCH_MP FLATP2AUX_flat_Mat o
                  REWRITE_RULE[source_to_flat_compile_exp_def]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REMOVE_THEN "ev'" MP_TAC THEN
  FLATP2AUX_RESULT_CASES_TAC `r1:(v list,v)result` `v1:v list` `err1:(v)error_result` THENL
   [ALL_TAC;
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
    USE_THEN "rr1" (X_CHOOSE_THEN `err1':(flat_v)error_result` SUBST_ALL_TAC o
                    MATCH_MP FLATP2AUX_result_rel_Rerr) THEN
    MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`;
      `Rerr err1':(flat_v list,flat_v)result`; `genv1:global_env`] THEN
    CASE_REWRITE_TAC[] THEN FLATP2AUX_LREWRITE_TAC ["rr1"; "sr1"; "na1"] []] THEN
  USE_THEN "rr1" (MP_TAC o MATCH_MP FLATP2AUX_result_rel_Rval) THEN
  DISCH_THEN(X_CHOOSE_THEN `v1':flat_v list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (LABEL_TAC "vr1"))) THEN
  USE_THEN "na1" (MP_TAC o REWRITE_RULE[source_to_flatProof_abort_simps]) THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i1"; "eg1"; "of1"; "sc1"; "sy1"; "sg1"]) THEN
  USE_THEN "ev1" (X_CHOOSE_THEN `x1:v` SUBST_ALL_TAC o MATCH_MP evaluate_sing) THEN
  USE_THEN "vr1" (MP_TAC o REWRITE_RULE[o_THM; LIST_REL_CONS1; LIST_REL_NIL]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x1':flat_v` (X_CHOOSE_THEN `tl1:flat_v list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 (LABEL_TAC "xr1") SUBST_ALL_TAC)))) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD] THEN COND_CASES_TAC THENL
   [POP_ASSUM(LABEL_TAC "cpa");
    REWRITE_TAC[PAIR_EQ] THEN USE_THEN "nte" MP_TAC THEN MESON_TAC[]] THEN
  DISCH_THEN(LABEL_TAC "evm") THEN
  FLATP2AUX_SUBGOAL {|env_all_rel genv1 comp_map env env_i1 locals|} (LABEL_TAC "ear1") THENL
   [MATCH_MP_TAC env_all_rel_weak THEN EXISTS_TAC `genv:global_env` THEN
    FLATP2AUX_LREWRITE_TAC ["ear"; "sc1"; "sy1"; "sg1"] [];
    ALL_TAC] THEN
  USE_THEN "ih2" (MP_TAC o SPECL [`st1:(FFI)state`; `[x1]:v list`]) THEN
  FLATP2AUX_LREWRITE_TAC ["ev1"; "cpa"] [HD] THEN DISCH_THEN(LABEL_TAC "ih2'") THEN
  FLATP2AUX_IH_TAC "ih2'" [("genv",`genv1:global_env`); ("s_i1",`s1_i1:(C,FFI)flat_state`);
    ("v_i1",`x1':flat_v`); ("err_v_i1",`flat_bind_exn_v`)] THEN
  ANTS_TAC THENL
   [FLATP2AUX_ANTS_TAC THENL
     [MATCH_MP_TAC can_pmatch_all_IMP_pmatch_rows THEN
      MAP_EVERY EXISTS_TAC [`env:v sem_env`; `st1:(FFI)state`; `x1:v`;
        `interp:(v->(source_to_flat_config#C)option)option`;
        `g:dec list->dec list`; `gen:environment_generation_store`; `genv1:global_env`;
        `idxs:next_indices#next_indices#(num#idx_types->bool)`;
        `env_i1:(flat_v)flat_environment`] THEN
      FLATP2AUX_LREWRITE_TAC ["i1"; "ear1"; "xr1"; "cpa"] [];
      USE_THEN "i1" (fun th -> REWRITE_TAC[MATCH_MP v_rel_lems (MATCH_MP invariant_genv_c_ok th)])];
    ALL_TAC] THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s2_i1:(C,FFI)flat_state`;
    `r2_i1:(flat_v list,flat_v)result`; `genv2:global_env`]
    (FLATP2AUX_LABEL_CONJS ["fe2"; "rr2"; "sr2"; "na2"])) THEN
  MAP_EVERY EXISTS_TAC [`s2_i1:(C,FFI)flat_state`;
    `r2_i1:(flat_v list,flat_v)result`; `genv2:global_env`] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD] THEN
  FLATP2AUX_LREWRITE_TAC ["fe2"; "rr2"; "sr2"] [] THEN DISCH_TAC THEN
  USE_THEN "na2" (MP_TAC o C MP (ASSUME `~source_to_flatProof_abort (r:(v list,v)result)`)) THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i2"; "eg2"; "of2"; "sc2"; "sy2"; "sg2"]) THEN
  FLATP2AUX_LREWRITE_TAC ["i2"; "eg2"] [] THEN
  FLATP2AUX_TRANS_TAC `state_eval_state (st1:(FFI)state)` `genv1:global_env`);;

let FLATP2AUX_cc_Let = prove
 (FLATP2AUX_cc_case 12,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "ear"; "lts"; "egr"; "nte"; "esi"]) THEN
  REMOVE_THEN "esi" SUBST_ALL_TAC THEN
  FLATP2AUX_PAIR_TAC `evaluate (st:(FFI)state) env [e1]` `st1:(FFI)state`
    `r1:(v list,v)result` "ev1" THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  FLATP2AUX_LREWRITE_TAC ["ev1"] [] THEN CASE_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ev'") THEN
  SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(v list,v)result)` (LABEL_TAC "nte1") THENL
   [DISCH_THEN SUBST_ALL_TAC THEN USE_THEN "ev'" MP_TAC THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    USE_THEN "nte" MP_TAC THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[source_to_flat_compile_exp_def] THEN
  CASES_ON `xo:(varN)option` THEN REWRITE_TAC[source_to_flat_compile_exp_def] THENL
  (let let_case (tr:term) (bindt:tactic) : tactic =
    FLATP2AUX_IH_TAC "ih1" [("s'",`st1:(FFI)state`); ("r",`r1:(v list,v)result`); ("t",tr)] THEN
    ANTS_TAC THENL [FLATP2AUX_ANTS_TAC THEN REWRITE_TAC[source_to_flat_compile_exp_def];
                    ALL_TAC] THEN
    DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s1_i1:(C,FFI)flat_state`;
      `r1_i1:(flat_v list,flat_v)result`; `genv1:global_env`]
      (FLATP2AUX_LABEL_CONJS ["fe1"; "rr1"; "sr1"; "na1"])) THEN
    USE_THEN "fe1" (MP_TAC o MATCH_MP FLATP2AUX_flat_Let o
                    REWRITE_RULE[source_to_flat_compile_exp_def]) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REMOVE_THEN "ev'" MP_TAC THEN
    FLATP2AUX_RESULT_CASES_TAC `r1:(v list,v)result` `v1:v list` `err1:(v)error_result` THENL
     [ALL_TAC;
      CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
      USE_THEN "rr1" (X_CHOOSE_THEN `err1':(flat_v)error_result` SUBST_ALL_TAC o
                      MATCH_MP FLATP2AUX_result_rel_Rerr) THEN
      MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`;
        `Rerr err1':(flat_v list,flat_v)result`; `genv1:global_env`] THEN
      CASE_REWRITE_TAC[] THEN FLATP2AUX_LREWRITE_TAC ["rr1"; "sr1"; "na1"] []] THEN
    USE_THEN "rr1" (MP_TAC o MATCH_MP FLATP2AUX_result_rel_Rval) THEN
    DISCH_THEN(X_CHOOSE_THEN `v1':flat_v list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      (LABEL_TAC "vr1"))) THEN
    USE_THEN "na1" (MP_TAC o REWRITE_RULE[source_to_flatProof_abort_simps]) THEN
    DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i1"; "eg1"; "of1"; "sc1"; "sy1"; "sg1"]) THEN
    USE_THEN "ev1" (X_CHOOSE_THEN `x1:v` SUBST_ALL_TAC o MATCH_MP evaluate_sing) THEN
    USE_THEN "vr1" (MP_TAC o REWRITE_RULE[o_THM; LIST_REL_CONS1; LIST_REL_NIL]) THEN
    DISCH_THEN(X_CHOOSE_THEN `x1':flat_v` (X_CHOOSE_THEN `tl1:flat_v list`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 (LABEL_TAC "xr1") SUBST_ALL_TAC)))) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD] THEN DISCH_THEN(LABEL_TAC "ev2") THEN
    FLATP2AUX_SUBGOAL {|env_all_rel genv1 comp_map env env_i1 locals|} (LABEL_TAC "ear1") THENL
     [MATCH_MP_TAC env_all_rel_weak THEN EXISTS_TAC `genv:global_env` THEN
      FLATP2AUX_LREWRITE_TAC ["ear"; "sc1"; "sy1"; "sg1"] [];
      ALL_TAC] THEN
    USE_THEN "ev1" (fun ev1 -> USE_THEN "ih2" (fun ih2 ->
      LABEL_TAC "ih2'" (REWRITE_RULE[HD] (MATCH_MP ih2 ev1)))) THEN
    bindt in
  let finish_tac : tactic =
    ANTS_TAC THENL [FLATP2AUX_ANTS_TAC; ALL_TAC] THEN
    DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s2_i1:(C,FFI)flat_state`;
      `r2_i1:(flat_v list,flat_v)result`; `genv2:global_env`]
      (FLATP2AUX_LABEL_CONJS ["fe2"; "rr2"; "sr2"; "na2"])) THEN
    MAP_EVERY EXISTS_TAC [`s2_i1:(C,FFI)flat_state`; `r2_i1:(flat_v list,flat_v)result`;
                          `genv2:global_env`] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD] THEN
    USE_THEN "fe2" (MP_TAC o REWRITE_RULE[source_to_flat_compile_exp_def]) THEN
    REWRITE_TAC[FLATP2AUX_opt_bind_fun; FLATP2AUX_record_etas; FLATP1AUX_bind_locals_CONS;
      source_to_flat_environment_INFO.ri_fupdfupds; source_to_flat_environment_INFO.ri_accfupds;
      K_o_THM; K_THM; FLATP2AUX_flat_env_v_fupd; FLATP2AUX_flat_env_REC_eta] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    FLATP2AUX_LREWRITE_TAC ["rr2"; "sr2"] [] THEN DISCH_TAC THEN
    USE_THEN "na2" (MP_TAC o C MP (ASSUME `~source_to_flatProof_abort (r:(v list,v)result)`)) THEN
    DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i2"; "eg2"; "of2"; "sc2"; "sy2"; "sg2"]) THEN
    FLATP2AUX_LREWRITE_TAC ["i2"; "eg2"] [] THEN
    FLATP2AUX_TRANS_TAC `state_eval_state (st1:(FFI)state)` `genv1:global_env` in
  let none_bind : tactic =
    REMOVE_THEN "ih2'" (LABEL_TAC "ih2n" o REWRITE_RULE[FLATP2AUX_record_etas] o
      CASE_REWRITE_RULE[] o REWRITE_RULE[nsOptBind_def]) THEN
    REMOVE_THEN "ev2" (LABEL_TAC "ev2n" o REWRITE_RULE[FLATP2AUX_record_etas] o
      CASE_REWRITE_RULE[] o REWRITE_RULE[nsOptBind_def]) THEN
    FLATP2AUX_IH_TAC "ih2n" [("genv",`genv1:global_env`); ("s_i1",`s1_i1:(C,FFI)flat_state`)] THEN
    finish_tac in
  let some_bind : tactic =
    REMOVE_THEN "ih2'" (LABEL_TAC "ih2n" o CASE_REWRITE_RULE[] o REWRITE_RULE[nsOptBind_def]) THEN
    REMOVE_THEN "ev2" (LABEL_TAC "ev2n" o CASE_REWRITE_RULE[] o REWRITE_RULE[nsOptBind_def]) THEN
    FLATP2AUX_SUBGOAL {|env_all_rel genv1 comp_map
        (sem_env_v_fupd (K (nsBind a x1 (sem_env_v env))) env)
        (flat_environment_v_fupd (K (CONS (a,x1') (flat_environment_v env_i1))) env_i1)
        (CONS a locals)|} (LABEL_TAC "ear2") THENL
     [MATCH_MP_TAC FLATP2AUX_env_all_rel_bind THEN FLATP2AUX_LREWRITE_TAC ["ear1"; "xr1"] [];
      ALL_TAC] THEN
    FLATP2AUX_IH_TAC "ih2n" [("genv",`genv1:global_env`); ("s_i1",`s1_i1:(C,FFI)flat_state`);
      ("env_i1",`flat_environment_v_fupd (K (CONS (a:varN,x1':flat_v)
                   (flat_environment_v (env_i1:(flat_v)flat_environment)))) env_i1`);
      ("locals",`CONS (a:varN) locals`); ("ts",`CONS backend_common_None ts`)] THEN
    FLATP2AUX_LREWRITE_TAC ["lts"] [LENGTH] THEN
    finish_tac in
  [let_case `t:mlstring list` none_bind; let_case `CONS (a:varN) t` some_bind]));;

let FLATP2AUX_cc_Letrec = prove
 (FLATP2AUX_cc_case 13,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih0") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "ear"; "lts"; "egr"; "nte"; "esi"]) THEN
  REMOVE_THEN "esi" SUBST_ALL_TAC THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  COND_CASES_TAC THENL
   [POP_ASSUM(LABEL_TAC "dist"); REWRITE_TAC[PAIR_EQ] THEN USE_THEN "nte" MP_TAC THEN MESON_TAC[]] THEN
  DISCH_THEN(LABEL_TAC "ev'") THEN
  USE_THEN "dist" (fun d -> USE_THEN "ih0" (fun ih -> LABEL_TAC "ih1" (MATCH_MP ih d))) THEN
  REWRITE_TAC[source_to_flat_compile_exp_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[flat_evaluate_def; compile_funs_dom2] THEN
  USE_THEN "dist" (fun th -> REWRITE_TAC[REWRITE_RULE[FLATP2AUX_FST3_case] th]) THEN
  REWRITE_TAC[GSYM nsAppend_to_nsBindList; source_to_flat_environment_INFO.ri_accfupds;
              K_THM; nsAppend_bind_locals] THEN
  REWRITE_TAC[source_to_flat_environment_INFO.ri_fupdfupds; K_o_THM] THEN
  FLATP2AUX_IH_TAC "ih1" [
    ("env_i1",`flat_environment_v_fupd (K (flat_build_rec_env
       (compile_funs t (source_to_flat_environment_v_fupd
          (K (bind_locals (APPEND (REPLICATE (LENGTH (funs:(varN#varN#exp)list))
                backend_common_None) ts)
             (APPEND (MAP FST funs) locals) (source_to_flat_environment_v comp_map)))
          comp_map) funs)
       env_i1 (flat_environment_v (env_i1:(flat_v)flat_environment)))) env_i1`);
    ("locals",`APPEND (MAP FST (funs:(varN#varN#exp)list)) locals`);
    ("ts",`APPEND (REPLICATE (LENGTH (funs:(varN#varN#exp)list)) backend_common_None) ts`)] THEN
  ANTS_TAC THENL
   [FLATP2AUX_ANTS_TAC THENL
     [MATCH_MP_TAC FLATP2AUX_env_all_rel_letrec THEN FLATP2AUX_LREWRITE_TAC ["ear"; "lts"] [];
      FLATP2AUX_LREWRITE_TAC ["lts"] [LENGTH_APPEND; LENGTH_REPLICATE; LENGTH_MAP]];
    REWRITE_TAC[source_to_flat_compile_exp_def]]);;

let FLATP2AUX_cc_pattern = prove
 (FLATP2AUX_cc_case 17,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihm") (LABEL_TAC "ihn")) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "ear"; "vr"; "lts"; "egr"; "nte"; "pesi";
                                    "pmr"; "evr"]) THEN
  REMOVE_THEN "pesi" SUBST_ALL_TAC THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  COND_CASES_TAC THENL
   [POP_ASSUM(LABEL_TAC "dist"); REWRITE_TAC[PAIR_EQ] THEN USE_THEN "nte" MP_TAC THEN MESON_TAC[]] THEN
  MP_TAC(ISPECL [`interp:(v->(source_to_flat_config#C)option)option`; `v:v`;
    `g:dec list->dec list`; `gen:environment_generation_store`; `genv:global_env`;
    `idxs:next_indices#next_indices#(num#idx_types->bool)`; `st:(FFI)state`;
    `s_i1:(C,FFI)flat_state`; `comp_map:source_to_flat_environment`; `env:v sem_env`;
    `env_i1:(flat_v)flat_environment`; `locals:mlstring list`;
    `source_to_flat_environment_v_fupd (K (bind_locals ts locals
       (source_to_flat_environment_v comp_map))) comp_map`; `v_i1:flat_v`; `p:pat`]
    pmatch_invariant) THEN
  FLATP2AUX_LREWRITE_TAC ["inv"; "ear"; "vr"] [source_to_flat_environment_INFO.ri_accfupds] THEN
  DISCH_THEN(LABEL_TAC "mrr") THEN
  USE_THEN "mrr" (MP_TAC o MATCH_MP match_result_rel_imp) THEN
  REWRITE_TAC[source_to_flat_compile_exp_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (LABEL_TAC "mte") (DISJ_CASES_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "nm1") (LABEL_TAC "nm2"))
    (X_CHOOSE_THEN `env_v:(varN#v)list` (X_CHOOSE_THEN `env2:(varN#flat_v)list`
      (CONJUNCTS_THEN2 (LABEL_TAC "m1") (LABEL_TAC "m2")))))) THENL
   [(* type error *)
    FLATP2AUX_LREWRITE_TAC ["mte"] [] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN USE_THEN "nte" MP_TAC THEN MESON_TAC[];
    (* no match *)
    FLATP2AUX_LREWRITE_TAC ["nm1"] [] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "nm2" (fun th -> REWRITE_TAC[MATCH_MP (CONJUNCT1 (SPEC_ALL
      FLATP2AUX_flat_evaluate_match_cons)) th]) THEN
    USE_THEN "dist" (fun d -> USE_THEN "nm1" (fun n -> USE_THEN "ihn" (fun ih ->
      LABEL_TAC "ihn'" (MATCH_MP ih (CONJ d n))))) THEN
    FLATP2AUX_IH_TAC "ihn'" [] THEN
    ANTS_TAC THENL
     [FLATP2AUX_ANTS_TAC THEN USE_THEN "pmr" MP_TAC THEN
      REWRITE_TAC[source_to_flat_compile_exp_def] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pmatch_rows_def] THEN
      FLATP2AUX_LREWRITE_TAC ["nm2"] [] THEN CASE_REWRITE_TAC[];
      REWRITE_TAC[]];
    (* match *)
    FLATP2AUX_LREWRITE_TAC ["m1"] [] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "mrr" (MP_TAC o REWRITE_RULE[source_to_flatProof_match_result_rel_def]) THEN
    FLATP2AUX_LREWRITE_TAC ["m1"; "m2"] [source_to_flatProof_match_result_rel_def; APPEND_NIL] THEN
    DISCH_THEN(X_CHOOSE_THEN `env_v':(varN#v)list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      (LABEL_TAC "er2"))) THEN
    FLATP2AUX_SUBGOAL {|~(pmatch_rows (compile_pes t
        (source_to_flat_environment_v_fupd
          (K (bind_locals ts locals (source_to_flat_environment_v comp_map))) comp_map) pes)
        s_i1 v_i1 = Match_type_error)|} (LABEL_TAC "pmr'") THENL
     [USE_THEN "pmr" MP_TAC THEN REWRITE_TAC[source_to_flat_compile_exp_def] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[pmatch_rows_def] THEN
      FLATP2AUX_LREWRITE_TAC ["m2"] [] THEN CASE_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `pmatch_rows (compile_pes t (source_to_flat_environment_v_fupd
        (K (bind_locals ts locals (source_to_flat_environment_v comp_map))) comp_map)
        (pes:(pat#exp)list)) (s_i1:(C,FFI)flat_state) v_i1` (cases "match_result")) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[distinctness "match_result"];
      ALL_TAC] THEN
    USE_THEN "dist" (LABEL_TAC "dist'" o REWRITE_RULE[GSYM (SPEC `source_to_flat_environment_v_fupd
      (K (bind_locals ts locals (source_to_flat_environment_v comp_map))) comp_map`
      pat_bindings_compile_pat)]) THEN
    USE_THEN "m2" (fun m2 -> USE_THEN "pmr'" (fun pr -> USE_THEN "dist'" (fun d ->
      REWRITE_TAC[MATCH_MP (GEN_ALL (CONJUNCT2 (SPEC_ALL FLATP2AUX_flat_evaluate_match_cons)))
                   (end_itlist CONJ [m2; pr; d])]))) THEN
    MP_TAC(ISPECL [`pat_bindings p`; `backend_common_None`; `ts:(tra)list`; `locals:mlstring list`;
      `source_to_flat_environment_v comp_map`] nsBindList_pat_tups_bind_locals) THEN
    DISCH_THEN(X_CHOOSE_THEN `tss:(tra)list` (CONJUNCTS_THEN2 (LABEL_TAC "nbl") (LABEL_TAC "ltss"))) THEN
    REWRITE_TAC[source_to_flat_environment_INFO.ri_accfupds; source_to_flat_environment_INFO.ri_fupdfupds;
                K_o_THM; K_THM] THEN FLATP2AUX_LREWRITE_TAC ["nbl"] [] THEN
    USE_THEN "m1" (MP_TAC o MATCH_MP (CONJUNCT1 pmatch_extend)) THEN
    REWRITE_TAC[APPEND_NIL] THEN
    DISCH_THEN(X_CHOOSE_THEN `envv:(varN#v)list` (CONJUNCTS_THEN2 (LABEL_TAC "eqv")
      (LABEL_TAC "mfst"))) THEN
    REMOVE_THEN "eqv" (SUBST_ALL_TAC o SYM) THEN
    USE_THEN "dist" (fun d -> USE_THEN "m1" (fun m -> USE_THEN "ihm" (fun ih ->
      LABEL_TAC "ihm'" (MATCH_MP ih (CONJ d m))))) THEN
    FLATP2AUX_IH_TAC "ihm'" [
      ("env_i1",`flat_environment_v_fupd (K (APPEND (env2:(varN#flat_v)list)
         (flat_environment_v (env_i1:(flat_v)flat_environment)))) env_i1`);
      ("locals",`APPEND (pat_bindings p) locals`); ("ts",`APPEND (tss:(tra)list) ts`)] THEN
    ANTS_TAC THENL
     [FLATP2AUX_ANTS_TAC THENL
       [USE_THEN "mfst" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC FLATP2AUX_env_all_rel_append THEN
        FLATP2AUX_LREWRITE_TAC ["ear"; "er2"] [];
        FLATP2AUX_LREWRITE_TAC ["lts"; "ltss"] [LENGTH_APPEND]];
      REWRITE_TAC[source_to_flat_compile_exp_def]]]);;
let FLATP2AUX_cc_empty_decs = prove
 (FLATP2AUX_cc_case 18,
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "cd"; "gei"; "nte"; "egr"; "efr"; "ip"]) THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
  USE_THEN "cd" (MP_TAC o REWRITE_RULE[source_to_flat_compile_decs_def]) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["e1"; "e2"; "e3"; "e4"; "e5"]) THEN
  MAP_EVERY (fun l -> REMOVE_THEN l (SUBST_ALL_TAC o SYM)) ["e1"; "e2"; "e3"; "e4"; "e5"] THEN
  MAP_EVERY EXISTS_TAC [`s_i1:(C,FFI)flat_state`; `genv:global_env`;
                        `NONE:((flat_v)error_result)option`] THEN
  REWRITE_TAC[flat_evaluate_def; distinctness "result"; injectivity "result"] THEN
  FLATP2AUX_LREWRITE_TAC ["inv"; "egr"] [SUBMAP_REFL; subglobals_refl; orac_forward_rel_refl] THEN
  CONJ_TAC THENL [USE_THEN "inv" (ACCEPT_TAC o MATCH_MP invariant_IMP_s_rel); ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[env_domain_eq_def; v_rel_global_eqn; source_to_flat_empty_env_def] THEN
  SIMP_NOASM[nsLookup_nsEmpty]);;

let FLATP2AUX_cc_cons_decs = prove
 (FLATP2AUX_cc_case 19,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "cd"; "gei"; "nte"; "egr"; "efr"; "ip"]) THEN
  MP_TAC(ISPEC `source_to_flat_compile_decs path t idx comp_map gen [d1]` BASICAUX_TUPLE5) THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`t1:num`; `idx1:next_indices`;
    `cm1:source_to_flat_environment`; `gen1:environment_generation_store`;
    `ds1:flat_exp list`] (LABEL_TAC "cd1")) THEN
  MP_TAC(ISPEC `source_to_flat_compile_decs path t1 idx1 (extend_env cm1 comp_map) gen1 (CONS d2 ds)`
    BASICAUX_TUPLE5) THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`t2:num`; `idx2:next_indices`;
    `cm2:source_to_flat_environment`; `gen2:environment_generation_store`;
    `ds2:flat_exp list`] (LABEL_TAC "cd2")) THEN
  REMOVE_THEN "cd" (MP_TAC o REWRITE_RULE[FLATP2AUX_compile_decs_cons]) THEN
  FLATP2AUX_LREWRITE_TAC ["cd1"] [] THEN
  CASE_REWRITE_TAC[] THEN FLATP2AUX_LREWRITE_TAC ["cd2"] [] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["e1"; "e2"; "e3"; "e4"; "e5"]) THEN
  MAP_EVERY (fun l -> REMOVE_THEN l (SUBST_ALL_TAC o SYM)) ["e1"; "e2"; "e3"; "e4"; "e5"] THEN
  USE_THEN "cd1" (LABEL_TAC "ip1" o MATCH_MP compile_decs_idx_prev) THEN
  USE_THEN "cd2" (LABEL_TAC "ip2" o MATCH_MP compile_decs_idx_prev) THEN
  USE_THEN "inv" (LABEL_TAC "egi" o MATCH_MP invariant_env_gen_inv) THEN
  USE_THEN "cd1" (fun cd -> USE_THEN "egi" (fun e ->
    LABEL_TAC "egi1" (CONJUNCT1 (MATCH_MP compile_decs_env_gen_inv (CONJ cd e))))) THEN
  USE_THEN "cd2" (fun cd -> USE_THEN "egi1" (fun e ->
    LABEL_TAC "egi2" (CONJUNCT1 (MATCH_MP compile_decs_env_gen_inv (CONJ cd e))))) THEN
  USE_THEN "cd2" (fun cd -> USE_THEN "efr" (fun f -> USE_THEN "egi1" (fun e ->
    LABEL_TAC "efr1" (MATCH_MP compile_decs_future_rel (end_itlist CONJ [cd; f; e]))))) THEN
  FLATP2AUX_PAIR_TAC `evaluate_decs (st:(FFI)state) env [d1]` `st1:(FFI)state`
    `r1:(v sem_env,v)result` "ev1" THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  FLATP2AUX_LREWRITE_TAC ["ev1"] [] THEN CASE_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ev'") THEN
  SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(v sem_env,v)result)` (LABEL_TAC "nte1") THENL
   [DISCH_THEN SUBST_ALL_TAC THEN USE_THEN "ev'" MP_TAC THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    USE_THEN "nte" MP_TAC THEN MESON_TAC[];
    ALL_TAC] THEN
  FLATP2AUX_IH_TAC "ih1" [("s'",`st1:(FFI)state`); ("r",`r1:(v sem_env,v)result`);
    ("idx'",`idx1:next_indices`); ("comp_map'",`cm1:source_to_flat_environment`);
    ("ds_i1",`ds1:flat_exp list`); ("t'",`t1:num`); ("gen'",`gen1:environment_generation_store`)] THEN
  ANTS_TAC THENL
   [FLATP2AUX_ANTS_TAC THEN MATCH_MP_TAC idx_prev_trans THEN EXISTS_TAC `idx2:next_indices` THEN
    FLATP2AUX_LREWRITE_TAC ["ip2"; "ip"] [];
    ALL_TAC] THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s1_i1:(C,FFI)flat_state`; `genv1:global_env`;
    `r1_i1:((flat_v)error_result)option`]
    (FLATP2AUX_LABEL_CONJS ["fe1"; "sr1"; "na1"; "okv1"; "oke1"])) THEN
  REMOVE_THEN "ev'" MP_TAC THEN
  FLATP2AUX_RESULT_CASES_TAC `r1:(v sem_env,v)result` `env1:v sem_env` `err1:(v)error_result` THENL
   [ALL_TAC;
    (* d1 raises *)
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
    USE_THEN "oke1" (MP_TAC o SPEC `err1:(v)error_result`) THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `err1':(flat_v)error_result` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      (LABEL_TAC "rre1"))) THEN
    MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`; `genv1:global_env`;
      `SOME err1':((flat_v)error_result)option`] THEN
    FLATP2AUX_LREWRITE_TAC ["fe1"; "sr1"; "rre1"] [flat_evaluate_decs_append;
      distinctness "result"; injectivity "result"] THEN
    CASE_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      USE_THEN "na1" (MP_TAC o C MP (ASSUME
        `~source_to_flatProof_abort (Rerr err1:(v sem_env,v)result)`)) THEN
      DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i1"; "of1"; "sc1"; "sy1"; "sg1"]) THEN
      FLATP2AUX_LREWRITE_TAC ["of1"; "sc1"; "sy1"; "sg1"] [] THEN
      MATCH_MP_TAC invariant_idx_range_shrink_gen THEN
      MAP_EVERY EXISTS_TAC [`gen1:environment_generation_store`; `idx1:next_indices`] THEN
      FLATP2AUX_LREWRITE_TAC ["i1"; "ip2"; "ip"; "egi2"] [];
      SIMP_NOASM[] THEN FLATP2AUX_LREWRITE_TAC ["rre1"] []]] THEN
  CASE_REWRITE_TAC[] THEN
  FLATP2AUX_PAIR_TAC `evaluate_decs (st1:(FFI)state) (extend_dec_env env1 env) (CONS d2 ds)`
    `st2:(FFI)state` `r2:(v sem_env,v)result` "ev2" THEN
  FLATP2AUX_LREWRITE_TAC ["ev2"] [] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
  USE_THEN "okv1" (MP_TAC o SPEC `env1:v sem_env`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["rn1"; "ede1"; "eg1"; "ge1"]) THEN
  REMOVE_THEN "rn1" SUBST_ALL_TAC THEN
  USE_THEN "na1" (MP_TAC o REWRITE_RULE[source_to_flatProof_abort_simps]) THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i1"; "of1"; "sc1"; "sy1"; "sg1"]) THEN
  USE_THEN "ev1" (fun ev1 -> USE_THEN "ih2" (fun ih2 -> LABEL_TAC "ih2'" (MATCH_MP ih2 ev1))) THEN
  SUBGOAL_THEN `~(r2 = Rerr (Rabort Rtype_error):(v sem_env,v)result)` (LABEL_TAC "nte2") THENL
   [DISCH_THEN SUBST_ALL_TAC THEN USE_THEN "nte" MP_TAC THEN
    REWRITE_TAC[combine_dec_result_def] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  FLATP2AUX_SUBGOAL {|global_env_inv genv1 (extend_env cm1 comp_map) {} (extend_dec_env env1 env)|}
    (LABEL_TAC "ge12") THENL
   [MATCH_MP_TAC global_env_inv_append THEN FLATP2AUX_LREWRITE_TAC ["ede1"; "ge1"] [] THEN
    MATCH_MP_TAC global_env_inv_weak THEN EXISTS_TAC `genv:global_env` THEN
    FLATP2AUX_LREWRITE_TAC ["gei"; "sc1"; "sy1"; "sg1"] [];
    ALL_TAC] THEN
  FLATP2AUX_SUBGOAL {|env_gen_future_rel interp gen2 (state_eval_state st1)|} (LABEL_TAC "efr2") THENL
   [MATCH_MP_TAC env_gen_future_rel_forward THEN EXISTS_TAC `state_eval_state (st:(FFI)state)` THEN
    FLATP2AUX_LREWRITE_TAC ["efr"; "of1"] [];
    ALL_TAC] THEN
  FLATP2AUX_IH_TAC "ih2'" [("r",`r2:(v sem_env,v)result`);
    ("t",`t1:num`); ("idx",`idx1:next_indices`);
    ("comp_map",`extend_env cm1 comp_map`); ("s_i1",`s1_i1:(C,FFI)flat_state`);
    ("idx'",`idx2:next_indices`); ("comp_map'",`cm2:source_to_flat_environment`);
    ("ds_i1",`ds2:flat_exp list`); ("t'",`t2:num`); ("genv",`genv1:global_env`);
    ("gen",`gen1:environment_generation_store`); ("gen'",`gen2:environment_generation_store`)] THEN
  ANTS_TAC THENL [FLATP2AUX_ANTS_TAC; ALL_TAC] THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s2_i1:(C,FFI)flat_state`; `genv2:global_env`;
    `r2_i1:((flat_v)error_result)option`]
    (FLATP2AUX_LABEL_CONJS ["fe2"; "sr2"; "na2"; "okv2"; "oke2"])) THEN
  MAP_EVERY EXISTS_TAC [`s2_i1:(C,FFI)flat_state`; `genv2:global_env`;
    `r2_i1:((flat_v)error_result)option`] THEN
  FLATP2AUX_LREWRITE_TAC ["fe1"] [flat_evaluate_decs_append] THEN CASE_REWRITE_TAC[] THEN
  FLATP2AUX_LREWRITE_TAC ["fe2"; "sr2"] [abort_compile_dec_result] THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    USE_THEN "na2" (MP_TAC o C MP (ASSUME
      `~source_to_flatProof_abort (r2:(v sem_env,v)result)`)) THEN
    DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i2"; "of2"; "sc2"; "sy2"; "sg2"]) THEN
    FLATP2AUX_LREWRITE_TAC ["i2"] [] THEN
    FLATP2AUX_TRANS_TAC `state_eval_state (st1:(FFI)state)` `genv1:global_env`;
    X_GEN_TAC `envr:v sem_env` THEN
    FLATP2AUX_RESULT_CASES_TAC `r2:(v sem_env,v)result` `env2:v sem_env` `err2:(v)error_result` THEN
    REWRITE_TAC[combine_dec_result_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[injectivity "result"; distinctness "result"] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    USE_THEN "okv2" (MP_TAC o SPEC `env2:v sem_env`) THEN REWRITE_TAC[] THEN
    DISCH_THEN(FLATP2AUX_LABEL_CONJS ["rn2"; "ede2"; "eg2"; "ge2"]) THEN
    USE_THEN "na2" (MP_TAC o REWRITE_RULE[source_to_flatProof_abort_simps]) THEN
    DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i2"; "of2"; "sc2"; "sy2"; "sg2"]) THEN
    REWRITE_TAC[GSYM extend_dec_env_def] THEN
    FLATP2AUX_LREWRITE_TAC ["rn2"; "eg2"] [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC env_domain_eq_append THEN FLATP2AUX_LREWRITE_TAC ["ede1"; "ede2"] [];
      MATCH_MP_TAC global_env_inv_append THEN FLATP2AUX_LREWRITE_TAC ["ede2"; "ge2"] [] THEN
      MATCH_MP_TAC global_env_inv_weak THEN EXISTS_TAC `genv1:global_env` THEN
      FLATP2AUX_LREWRITE_TAC ["ge1"; "sc2"; "sy2"; "sg2"] []];
    X_GEN_TAC `errr:(v)error_result` THEN
    FLATP2AUX_RESULT_CASES_TAC `r2:(v sem_env,v)result` `env2:v sem_env` `err2:(v)error_result` THEN
    REWRITE_TAC[combine_dec_result_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[injectivity "result"; distinctness "result"] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    USE_THEN "oke2" (MP_TAC o SPEC `err2:(v)error_result`) THEN REWRITE_TAC[]]);;
let FLATP2AUX_cc_Dtabbrev = prove
 (FLATP2AUX_cc_case 23,
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "cd"; "gei"; "nte"; "egr"; "efr"; "ip"]) THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
  USE_THEN "cd" (MP_TAC o REWRITE_RULE[source_to_flat_compile_decs_def]) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["e1"; "e2"; "e3"; "e4"; "e5"]) THEN
  MAP_EVERY (fun l -> REMOVE_THEN l (SUBST_ALL_TAC o SYM)) ["e1"; "e2"; "e3"; "e4"; "e5"] THEN
  MAP_EVERY EXISTS_TAC [`s_i1:(C,FFI)flat_state`; `genv:global_env`;
                        `NONE:((flat_v)error_result)option`] THEN
  REWRITE_TAC[flat_evaluate_def; distinctness "result"; injectivity "result"] THEN
  FLATP2AUX_LREWRITE_TAC ["inv"; "egr"] [SUBMAP_REFL; subglobals_refl; orac_forward_rel_refl] THEN
  CONJ_TAC THENL [USE_THEN "inv" (ACCEPT_TAC o MATCH_MP invariant_IMP_s_rel); ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[env_domain_eq_def; v_rel_global_eqn; source_to_flat_empty_env_def] THEN
  SIMP_NOASM[nsLookup_nsEmpty]);;

let FLATP2AUX_cc_Dmod = prove
 (FLATP2AUX_cc_case 26,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih1") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "cd"; "gei"; "nte"; "egr"; "efr"; "ip"]) THEN
  MP_TAC(ISPEC `source_to_flat_compile_decs (CONS mn path) t idx comp_map gen ds`
    BASICAUX_TUPLE5) THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`t1:num`; `idx1:next_indices`;
    `cm1:source_to_flat_environment`; `gen1:environment_generation_store`;
    `ds1:flat_exp list`] (LABEL_TAC "cd1")) THEN
  REMOVE_THEN "cd" (MP_TAC o REWRITE_RULE[source_to_flat_compile_decs_def]) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN FLATP2AUX_LREWRITE_TAC ["cd1"] [] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["e1"; "e2"; "e3"; "e4"; "e5"]) THEN
  MAP_EVERY (fun l -> REMOVE_THEN l (SUBST_ALL_TAC o SYM)) ["e1"; "e2"; "e3"; "e4"; "e5"] THEN
  FLATP2AUX_PAIR_TAC `evaluate_decs (st:(FFI)state) env ds` `st1:(FFI)state`
    `r1:(v sem_env,v)result` "ev1" THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  FLATP2AUX_LREWRITE_TAC ["ev1"] [] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
  SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(v sem_env,v)result)` (LABEL_TAC "nte1") THENL
   [DISCH_THEN SUBST_ALL_TAC THEN USE_THEN "nte" MP_TAC THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  FLATP2AUX_IH_TAC "ih1" [("r",`r1:(v sem_env,v)result`); ("path",`CONS (mn:modN) path`);
    ("idx'",`idx1:next_indices`); ("comp_map'",`cm1:source_to_flat_environment`);
    ("ds_i1",`ds1:flat_exp list`); ("t'",`t1:num`); ("gen'",`gen1:environment_generation_store`)] THEN
  ANTS_TAC THENL [FLATP2AUX_ANTS_TAC; ALL_TAC] THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s1_i1:(C,FFI)flat_state`; `genv1:global_env`;
    `r1_i1:((flat_v)error_result)option`]
    (FLATP2AUX_LABEL_CONJS ["fe1"; "sr1"; "na1"; "okv1"; "oke1"])) THEN
  MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`; `genv1:global_env`;
    `r1_i1:((flat_v)error_result)option`] THEN
  FLATP2AUX_LREWRITE_TAC ["fe1"; "sr1"] [] THEN
  FLATP2AUX_RESULT_CASES_TAC `r1:(v sem_env,v)result` `e1:v sem_env` `err1:(v)error_result` THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[source_to_flatProof_abort_simps; distinctness "result"; injectivity "result"] THENL
   [USE_THEN "na1" (MP_TAC o REWRITE_RULE[source_to_flatProof_abort_simps]) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    X_GEN_TAC `envr:v sem_env` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    USE_THEN "okv1" (MP_TAC o SPEC `e1:v sem_env`) THEN REWRITE_TAC[] THEN
    DISCH_THEN(FLATP2AUX_LABEL_CONJS ["rn1"; "ede1"; "eg1"; "ge1"]) THEN
    FLATP2AUX_LREWRITE_TAC ["rn1"; "eg1"] [] THEN
    USE_THEN "ede1" (fun d -> USE_THEN "ge1" (fun g -> REWRITE_TAC[
      MATCH_MP (CONJUNCT1 (SPEC_ALL FLATP2AUX_lift_env_props)) d;
      MATCH_MP (CONJUNCT2 (SPEC_ALL FLATP2AUX_lift_env_props)) g]));
    FLATP2AUX_LREWRITE_TAC ["na1"] [] THEN
    X_GEN_TAC `errr:(v)error_result` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    USE_THEN "oke1" (MP_TAC o SPEC `err1:(v)error_result`) THEN REWRITE_TAC[]]);;

let FLATP2AUX_cc_Dlocal = prove
 (FLATP2AUX_cc_case 27,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "cd"; "gei"; "nte"; "egr"; "efr"; "ip"]) THEN
  MP_TAC(ISPEC `source_to_flat_compile_decs path t idx comp_map gen lds` BASICAUX_TUPLE5) THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`t1:num`; `idx1:next_indices`;
    `cm1:source_to_flat_environment`; `gen1:environment_generation_store`;
    `ds1:flat_exp list`] (LABEL_TAC "cd1")) THEN
  MP_TAC(ISPEC `source_to_flat_compile_decs path t1 idx1 (extend_env cm1 comp_map) gen1 ds`
    BASICAUX_TUPLE5) THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`t2:num`; `idx2:next_indices`;
    `cm2:source_to_flat_environment`; `gen2:environment_generation_store`;
    `ds2:flat_exp list`] (LABEL_TAC "cd2")) THEN
  REMOVE_THEN "cd" (MP_TAC o REWRITE_RULE[source_to_flat_compile_decs_def]) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN FLATP2AUX_LREWRITE_TAC ["cd1"] [] THEN
  CASE_REWRITE_TAC[] THEN FLATP2AUX_LREWRITE_TAC ["cd2"] [] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["e1"; "e2"; "e3"; "e4"; "e5"]) THEN
  MAP_EVERY (fun l -> REMOVE_THEN l (SUBST_ALL_TAC o SYM)) ["e1"; "e2"; "e3"; "e4"; "e5"] THEN
  USE_THEN "cd1" (LABEL_TAC "ip1" o MATCH_MP compile_decs_idx_prev) THEN
  USE_THEN "cd2" (LABEL_TAC "ip2" o MATCH_MP compile_decs_idx_prev) THEN
  USE_THEN "inv" (LABEL_TAC "egi" o MATCH_MP invariant_env_gen_inv) THEN
  USE_THEN "cd1" (fun cd -> USE_THEN "egi" (fun e ->
    LABEL_TAC "egi1" (CONJUNCT1 (MATCH_MP compile_decs_env_gen_inv (CONJ cd e))))) THEN
  USE_THEN "cd2" (fun cd -> USE_THEN "egi1" (fun e ->
    LABEL_TAC "egi2" (CONJUNCT1 (MATCH_MP compile_decs_env_gen_inv (CONJ cd e))))) THEN
  USE_THEN "cd2" (fun cd -> USE_THEN "efr" (fun f -> USE_THEN "egi1" (fun e ->
    LABEL_TAC "efr1" (MATCH_MP compile_decs_future_rel (end_itlist CONJ [cd; f; e]))))) THEN
  FLATP2AUX_PAIR_TAC `evaluate_decs (st:(FFI)state) env lds` `st1:(FFI)state`
    `r1:(v sem_env,v)result` "ev1" THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  FLATP2AUX_LREWRITE_TAC ["ev1"] [] THEN CASE_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ev'") THEN
  SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(v sem_env,v)result)` (LABEL_TAC "nte1") THENL
   [DISCH_THEN SUBST_ALL_TAC THEN USE_THEN "ev'" MP_TAC THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    USE_THEN "nte" MP_TAC THEN MESON_TAC[];
    ALL_TAC] THEN
  FLATP2AUX_IH_TAC "ih1" [("s'",`st1:(FFI)state`); ("r",`r1:(v sem_env,v)result`);
    ("idx'",`idx1:next_indices`); ("comp_map'",`cm1:source_to_flat_environment`);
    ("ds_i1",`ds1:flat_exp list`); ("t'",`t1:num`); ("gen'",`gen1:environment_generation_store`)] THEN
  ANTS_TAC THENL
   [FLATP2AUX_ANTS_TAC THEN MATCH_MP_TAC idx_prev_trans THEN EXISTS_TAC `idx2:next_indices` THEN
    FLATP2AUX_LREWRITE_TAC ["ip2"; "ip"] [];
    ALL_TAC] THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s1_i1:(C,FFI)flat_state`; `genv1:global_env`;
    `r1_i1:((flat_v)error_result)option`]
    (FLATP2AUX_LABEL_CONJS ["fe1"; "sr1"; "na1"; "okv1"; "oke1"])) THEN
  REMOVE_THEN "ev'" MP_TAC THEN
  FLATP2AUX_RESULT_CASES_TAC `r1:(v sem_env,v)result` `env1:v sem_env` `err1:(v)error_result` THENL
   [ALL_TAC;
    (* d1 raises *)
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
    USE_THEN "oke1" (MP_TAC o SPEC `err1:(v)error_result`) THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `err1':(flat_v)error_result` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      (LABEL_TAC "rre1"))) THEN
    MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`; `genv1:global_env`;
      `SOME err1':((flat_v)error_result)option`] THEN
    FLATP2AUX_LREWRITE_TAC ["fe1"; "sr1"; "rre1"] [flat_evaluate_decs_append;
      distinctness "result"; injectivity "result"] THEN
    CASE_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      USE_THEN "na1" (MP_TAC o C MP (ASSUME
        `~source_to_flatProof_abort (Rerr err1:(v sem_env,v)result)`)) THEN
      DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i1"; "of1"; "sc1"; "sy1"; "sg1"]) THEN
      FLATP2AUX_LREWRITE_TAC ["of1"; "sc1"; "sy1"; "sg1"] [] THEN
      MATCH_MP_TAC invariant_idx_range_shrink_gen THEN
      MAP_EVERY EXISTS_TAC [`gen1:environment_generation_store`; `idx1:next_indices`] THEN
      FLATP2AUX_LREWRITE_TAC ["i1"; "ip2"; "ip"; "egi2"] [];
      SIMP_NOASM[] THEN FLATP2AUX_LREWRITE_TAC ["rre1"] []]] THEN
  CASE_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ev2") THEN
  USE_THEN "okv1" (MP_TAC o SPEC `env1:v sem_env`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["rn1"; "ede1"; "eg1"; "ge1"]) THEN
  REMOVE_THEN "rn1" SUBST_ALL_TAC THEN
  USE_THEN "na1" (MP_TAC o REWRITE_RULE[source_to_flatProof_abort_simps]) THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i1"; "of1"; "sc1"; "sy1"; "sg1"]) THEN
  USE_THEN "ev1" (fun ev1 -> USE_THEN "ih2" (fun ih2 -> LABEL_TAC "ih2'" (MATCH_MP ih2 ev1))) THEN

  FLATP2AUX_SUBGOAL {|global_env_inv genv1 (extend_env cm1 comp_map) {} (extend_dec_env env1 env)|}
    (LABEL_TAC "ge12") THENL
   [MATCH_MP_TAC global_env_inv_append THEN FLATP2AUX_LREWRITE_TAC ["ede1"; "ge1"] [] THEN
    MATCH_MP_TAC global_env_inv_weak THEN EXISTS_TAC `genv:global_env` THEN
    FLATP2AUX_LREWRITE_TAC ["gei"; "sc1"; "sy1"; "sg1"] [];
    ALL_TAC] THEN
  FLATP2AUX_SUBGOAL {|env_gen_future_rel interp gen2 (state_eval_state st1)|} (LABEL_TAC "efr2") THENL
   [MATCH_MP_TAC env_gen_future_rel_forward THEN EXISTS_TAC `state_eval_state (st:(FFI)state)` THEN
    FLATP2AUX_LREWRITE_TAC ["efr"; "of1"] [];
    ALL_TAC] THEN
  FLATP2AUX_IH_TAC "ih2'" [
    ("t",`t1:num`); ("idx",`idx1:next_indices`);
    ("comp_map",`extend_env cm1 comp_map`); ("s_i1",`s1_i1:(C,FFI)flat_state`);
    ("idx'",`idx2:next_indices`); ("comp_map'",`cm2:source_to_flat_environment`);
    ("ds_i1",`ds2:flat_exp list`); ("t'",`t2:num`); ("genv",`genv1:global_env`);
    ("gen",`gen1:environment_generation_store`); ("gen'",`gen2:environment_generation_store`)] THEN
  ANTS_TAC THENL [FLATP2AUX_ANTS_TAC; ALL_TAC] THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s2_i1:(C,FFI)flat_state`; `genv2:global_env`;
    `r2_i1:((flat_v)error_result)option`]
    (FLATP2AUX_LABEL_CONJS ["fe2"; "sr2"; "na2"; "okv2"; "oke2"])) THEN
  MAP_EVERY EXISTS_TAC [`s2_i1:(C,FFI)flat_state`; `genv2:global_env`;
    `r2_i1:((flat_v)error_result)option`] THEN
  FLATP2AUX_LREWRITE_TAC ["fe1"] [flat_evaluate_decs_append] THEN CASE_REWRITE_TAC[] THEN
  FLATP2AUX_LREWRITE_TAC ["fe2"; "sr2"; "okv2"; "oke2"] [] THEN
  DISCH_TAC THEN
  USE_THEN "na2" (MP_TAC o C MP (ASSUME `~source_to_flatProof_abort (r:(v sem_env,v)result)`)) THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["i2"; "of2"; "sc2"; "sy2"; "sg2"]) THEN
  FLATP2AUX_LREWRITE_TAC ["i2"] [] THEN
  FLATP2AUX_TRANS_TAC `state_eval_state (st1:(FFI)state)` `genv1:global_env`);;

let FLATP2AUX_cc_Dlet = prove
 (FLATP2AUX_cc_case 20,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih0") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "cd"; "gei"; "nte"; "egr"; "efr"; "ip"]) THEN
  FLATP2AUX_OPTION_CASES_TAC `simple_dlet p e` `pvv:varN#(modN,varN)id` "sd" THENL
   [(* not a simple dlet: HOL4 lines 4825-4888 *)
    REMOVE_THEN "cd" (MP_TAC o REWRITE_RULE[source_to_flat_compile_decs_def]) THEN
    FLATP2AUX_LREWRITE_TAC ["sd"] [] THEN CASE_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(FLATP2AUX_LABEL_CONJS ["e1"; "e2"; "e3"; "e4"; "e5"]) THEN
    MAP_EVERY (fun l -> REMOVE_THEN l (SUBST_ALL_TAC o SYM)) ["e1"; "e2"; "e3"; "e4"; "e5"] THEN
    SUBGOAL_THEN `ALL_DISTINCT (pat_bindings p) /\
                  every_exp (one_con_check (sem_env_c (env:v sem_env))) e`
      (LABEL_TAC "adee") THENL
     [REFUTE_THEN (LABEL_TAC "nadee") THEN USE_THEN "ev" MP_TAC THEN
      REWRITE_TAC[full_evaluate_def] THEN FLATP2AUX_LREWRITE_TAC ["nadee"] [PAIR_EQ] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM o CONJUNCT2) THEN USE_THEN "nte" MP_TAC THEN REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "adee" (fun a -> REMOVE_THEN "ih0" (LABEL_TAC "ih" o C MP a)) THEN
    FLATP2AUX_PAIR_TAC `evaluate (st:(FFI)state) env [e]` `st1:(FFI)state` `r1:(v list,v)result` "ev1" THEN
    REMOVE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
    FLATP2AUX_LREWRITE_TAC ["adee"; "ev1"] [] THEN CASE_REWRITE_TAC[] THEN
    DISCH_THEN(LABEL_TAC "ev'") THEN
    SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(v list,v)result)` (LABEL_TAC "nte1") THENL
     [DISCH_THEN SUBST_ALL_TAC THEN USE_THEN "ev'" MP_TAC THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM o CONJUNCT2) THEN
      USE_THEN "nte" MP_TAC THEN REWRITE_TAC[];
      ALL_TAC] THEN
    FLATP2AUX_IH_TAC "ih" [("s'", `st1:(FFI)state`); ("r", `r1:(v list,v)result`);
      ("genv", `genv:global_env`); ("comp_map", `comp_map:source_to_flat_environment`);
      ("env_i1", `flat_environment_REC [] :(flat_v)flat_environment`);
      ("s_i1", `s_i1:(C,FFI)flat_state`); ("locals", `[]:mlstring list`);
      ("t", `APPEND (REVERSE (pat_bindings p)) path`); ("ts", `[]:tra list`);
      ("gen", `gen:environment_generation_store`);
      ("idxs", `(idx,end_idx,os):next_indices#next_indices#(num#idx_types->bool)`)] THEN
    ANTS_TAC THENL
     [FLATP2AUX_ANTS_TAC THEN REWRITE_TAC[LENGTH] THEN
      USE_THEN "gei" (ACCEPT_TAC o MATCH_MP FLATP2AUX_env_all_rel_nil);
      ALL_TAC] THEN
    REWRITE_TAC[FLATP2AUX_bind_locals_nil; source_to_flat_compile_exp_def] THEN
    DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s1_i1:(C,FFI)flat_state`;
      `r1_i1:(flat_v list,flat_v)result`; `genv1:global_env`]
      (FLATP2AUX_LABEL_CONJS ["fe1"; "rr1"; "sr1"; "na1"])) THEN
    REWRITE_TAC[FLATP2AUX_flat_decs_sing] THEN
    USE_THEN "fe1" (fun th -> REWRITE_TAC[MATCH_MP FLATP2AUX_flat_Mat th]) THEN
    FLATP2AUX_RESULT_CASES_TAC `r1:(v list,v)result` `vs1:v list` `err1:(v)error_result` THENL
     [(* the expression returned a value *)
      USE_THEN "ev1" (X_CHOOSE_THEN `v1:v` SUBST_ALL_TAC o MATCH_MP evaluate_sing) THEN
      USE_THEN "rr1" (X_CHOOSE_THEN `vs1':flat_v list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
        (MP_TAC o REWRITE_RULE[o_THM; LIST_REL_CONS1; LIST_REL_NIL])) o
        MATCH_MP FLATP2AUX_result_rel_Rval) THEN
      DISCH_THEN(X_CHOOSE_THEN `v1':flat_v` (X_CHOOSE_THEN `tl1:flat_v list`
        (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 (LABEL_TAC "vr1") SUBST_ALL_TAC)))) THEN
      USE_THEN "ev'" MP_TAC THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ; HD] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (LABEL_TAC "req")) THEN
      USE_THEN "na1" (MP_TAC o REWRITE_RULE[source_to_flatProof_abort_simps]) THEN
      DISCH_THEN(FLATP2AUX_LABEL_CONJS ["inv1"; "eg1"; "of1"; "sc1"; "sy1"; "sg1"]) THEN
      SUBGOAL_THEN `env_all_rel genv1 comp_map env
                      (flat_environment_REC [] :(flat_v)flat_environment) []`
        (LABEL_TAC "ear1") THENL
       [MATCH_MP_TAC env_all_rel_weak THEN EXISTS_TAC `genv:global_env` THEN
        FLATP2AUX_LREWRITE_TAC ["sc1"; "sy1"; "sg1"] [] THEN
        USE_THEN "gei" (ACCEPT_TAC o MATCH_MP FLATP2AUX_env_all_rel_nil);
        ALL_TAC] THEN
      MP_TAC(SPEC `p:pat` (MATCH_MP pmatch_invariant (end_itlist CONJ
        [ASSUME `invariant interp g gen genv1 (idx,end_idx,os) (st1:(FFI)state)
                   (s1_i1:(C,FFI)flat_state)`;
         ASSUME `env_all_rel genv1 comp_map env
                   (flat_environment_REC [] :(flat_v)flat_environment) []`;
         REFL `source_to_flat_environment_c comp_map`;
         ASSUME `source_to_flatProof_v_rel genv1 v1 v1'`]))) THEN
      DISCH_THEN(LABEL_TAC "mrr") THEN REWRITE_TAC[flat_evaluate_match_def; pmatch_rows_def] THEN
      CASE_REWRITE_TAC[] THEN
      USE_THEN "mrr" (MP_TAC o MATCH_MP match_result_rel_imp) THEN
      DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2
        (CONJUNCTS_THEN SUBST_ALL_TAC)
        (X_CHOOSE_THEN `env1:(varN#v)list` (X_CHOOSE_THEN `env2:(varN#flat_v)list`
          (CONJUNCTS_THEN2 SUBST_ALL_TAC
            (fun th -> SUBST_ALL_TAC th THEN LABEL_TAC "m2eq" th)))))) THENL
       [(* Match_type_error *)
        USE_THEN "req" MP_TAC THEN CASE_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
        USE_THEN "nte" MP_TAC THEN REWRITE_TAC[];
        (* No_match *)
        USE_THEN "req" MP_TAC THEN CASE_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
        CASE_REWRITE_TAC[] THEN
        MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`; `genv1:global_env`;
                              `SOME (Rraise flat_bind_exn_v)`] THEN
        REWRITE_TAC[distinctness "result"; injectivity "result"; injectivity "option";
                    source_to_flatProof_abort_simps] THEN
        FLATP2AUX_LREWRITE_TAC ["sr1"; "of1"; "sc1"; "sy1"; "sg1"] [] THEN CONJ_TAC THENL
         [MATCH_MP_TAC invariant_idx_range_shrink THEN EXISTS_TAC `idx:next_indices` THEN
          FLATP2AUX_LREWRITE_TAC ["inv1"; "ip"] [] THEN REWRITE_TAC[idx_prev_def] THEN
          SIMP_NOASM[];
          X_GEN_TAC `err:(v)error_result` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
          EXISTS_TAC `Rraise flat_bind_exn_v` THEN REWRITE_TAC[result_rel_eqns] THEN
          EXISTS_TAC `flat_bind_exn_v` THEN REWRITE_TAC[] THEN
          USE_THEN "inv1" (MP_TAC o MATCH_MP invariant_genv_c_ok) THEN
          DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP v_rel_lems th])];
        (* Match *)
        USE_THEN "mrr" (MP_TAC o REWRITE_RULE[source_to_flatProof_match_result_rel_def]) THEN
        DISCH_THEN(X_CHOOSE_THEN `el:(varN#v)list`
          (CONJUNCTS_THEN2 SUBST_ALL_TAC (LABEL_TAC "er1"))) THEN
        USE_THEN "req" MP_TAC THEN CASE_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
        USE_THEN "m2eq" (LABEL_TAC "dom2" o
          REWRITE_RULE[MAP; APPEND_NIL; pat_bindings_compile_pat] o
          MATCH_MP (CONJUNCT1 pmatch_bindings)) THEN
        CASE_REWRITE_TAC[] THEN
        FLATP2AUX_LREWRITE_TAC ["adee"] [pat_bindings_compile_pat; APPEND_NIL] THEN
        SIMP_NOASM[] THEN
        FLATP2AUX_ISPECL_TAC ["interp"; "g"; "gen"; "genv1"; "idx"; "end_idx"; "os"; "st1";
          "s1_i1"; "next_indices_vidx idx"; "REVERSE (pat_bindings p)";
          "flat_environment_REC env2 :(flat_v)flat_environment"; "0"; "backend_common_None"]
          invariant_make_varls THEN
        ANTS_TAC THENL
         [SIMP_NOASM[] THEN FLATP2AUX_LREWRITE_TAC ["inv1"; "dom2"; "adee"] [] THEN
          USE_THEN "ip" (MP_TAC o REWRITE_RULE[idx_prev_def]) THEN
          SIMP_NOASM[LENGTH_REVERSE] THEN ARITH_TAC;
          ALL_TAC] THEN
        DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`genv2:global_env`; `st2:(C,FFI)flat_state`]
          (FLATP2AUX_LABEL_CONJS ["fe2"; "inv2"; "c2"; "t2"; "sg2"; "gi2"])) THEN
        MAP_EVERY EXISTS_TAC [`st2:(C,FFI)flat_state`; `genv2:global_env`] THEN
        FLATP2AUX_LREWRITE_TAC ["fe2"] [] THEN CASE_REWRITE_TAC[] THEN
        USE_THEN "inv2" (LABEL_TAC "inv2'" o REWRITE_RULE[LENGTH_REVERSE]) THEN
        FLATP2AUX_LREWRITE_TAC ["inv2'"; "of1"; "eg1"; "c2"; "t2"; "sc1"; "sy1"] [] THEN
        REPEAT CONJ_TAC THENL
         [USE_THEN "inv2" (ACCEPT_TAC o MATCH_MP invariant_IMP_s_rel);
          MATCH_MP_TAC subglobals_trans THEN EXISTS_TAC `global_env_v genv1` THEN
          FLATP2AUX_LREWRITE_TAC ["sg1"; "sg2"] [];
          MATCH_MP_TAC FLATP2AUX_env_domain_eq_alist THEN
          USE_THEN "er1" (fun th -> REWRITE_TAC[MATCH_MP FLATP2AUX_env_rel_dom_alist th]) THEN
          FLATP2AUX_LREWRITE_TAC ["dom2"] [fst_alloc_defs; LIST_TO_SET_REVERSE];
          USE_THEN "gi2" (MP_TAC o SPECL [`el:(varN#v)list`; `t + 4`]) THEN
          SIMP_NOASM[] THEN FLATP2AUX_LREWRITE_TAC ["dom2"] [] THEN DISCH_THEN MATCH_MP_TAC THEN
          MATCH_MP_TAC env_rel_weak THEN EXISTS_TAC `genv1:global_env` THEN
          FLATP2AUX_LREWRITE_TAC ["er1"; "c2"; "t2"; "sg2"] [SUBMAP_REFL]]];
      (* the expression raised or aborted *)
      USE_THEN "ev'" MP_TAC THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
      USE_THEN "rr1" (X_CHOOSE_THEN `e1':(flat_v)error_result` SUBST_ALL_TAC o
                      MATCH_MP FLATP2AUX_result_rel_Rerr) THEN
      CASE_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`; `genv1:global_env`;
                            `SOME (e1':(flat_v)error_result)`] THEN
      REWRITE_TAC[distinctness "result"; injectivity "result"; injectivity "option"] THEN
      FLATP2AUX_LREWRITE_TAC ["sr1"] [] THEN CONJ_TAC THENL
       [DISCH_THEN(fun th -> USE_THEN "na1" MP_TAC THEN ANTS_TAC THENL
         [MP_TAC th THEN REWRITE_TAC[source_to_flatProof_abort_def] THEN CASE_REWRITE_TAC[] THEN
          TRY(DISCH_THEN ACCEPT_TAC);
          ALL_TAC]) THEN
        DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inv1")
          (FLATP2AUX_LABEL_CONJS ["eg1"; "of1"; "sc1"; "sy1"; "sg1"])) THEN
        FLATP2AUX_LREWRITE_TAC ["of1"; "sc1"; "sy1"; "sg1"] [] THEN
        MATCH_MP_TAC invariant_idx_range_shrink THEN EXISTS_TAC `idx:next_indices` THEN
        FLATP2AUX_LREWRITE_TAC ["inv1"; "ip"] [] THEN REWRITE_TAC[idx_prev_def] THEN SIMP_NOASM[];
        X_GEN_TAC `err:(v)error_result` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
        EXISTS_TAC `e1':(flat_v)error_result` THEN REWRITE_TAC[] THEN
        USE_THEN "rr1" (MATCH_ACCEPT_TAC o MATCH_MP FLATP2AUX_result_rel_Rerr_f)]];
    (* a simple dlet: HOL4 lines 4805-4824 *)
    MP_TAC(ISPEC `pvv:varN#(modN,varN)id` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `pv:varN` (X_CHOOSE_THEN `vn:(modN,varN)id` SUBST_ALL_TAC)) THEN
    USE_THEN "sd" (MP_TAC o REWRITE_RULE[FLATP2AUX_simple_dlet_SOME]) THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    REMOVE_THEN "cd" (MP_TAC o REWRITE_RULE[source_to_flat_compile_decs_def]) THEN
    FLATP2AUX_LREWRITE_TAC ["sd"] [] THEN CASE_REWRITE_TAC[] THEN
    USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
    REWRITE_TAC[pat_bindings_def; ALL_DISTINCT; MEM; every_exp_def; one_con_check_def] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[full_evaluate_def] THEN
    FLATP2AUX_OPTION_CASES_TAC `nsLookup (sem_env_v (env:v sem_env)) vn` `v:v` "lkv" THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THENL
     [DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
      USE_THEN "nte" MP_TAC THEN REWRITE_TAC[];
      REWRITE_TAC[pmatch_def; HD] THEN CASE_REWRITE_TAC[] THEN
      USE_THEN "gei" (MP_TAC o SPECL [`vn:(modN,varN)id`; `v:v`] o CONJUNCT1 o
                      REWRITE_RULE[v_rel_global_eqn]) THEN
      FLATP2AUX_LREWRITE_TAC ["lkv"] [IMAGE_CLAUSES; NOT_IN_EMPTY] THEN
      DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`n':num`; `v':flat_v`; `tr:tra`]
        (FLATP2AUX_LABEL_CONJS ["glk"; "nlt"; "gel"; "vr"])) THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (SUBST_ALL_TAC o SYM)) THEN
      FLATP2AUX_LREWRITE_TAC ["glk"] [] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
      DISCH_THEN(FLATP2AUX_LABEL_CONJS ["e1"; "e2"; "e3"; "e4"; "e5"]) THEN
      MAP_EVERY (fun l -> REMOVE_THEN l (SUBST_ALL_TAC o SYM)) ["e1"; "e2"; "e3"; "e4"; "e5"] THEN
      MAP_EVERY EXISTS_TAC [`s_i1:(C,FFI)flat_state`; `genv:global_env`;
                            `NONE:((flat_v)error_result)option`] THEN
      REWRITE_TAC[flat_evaluate_def; distinctness "result"; injectivity "result"] THEN
      FLATP2AUX_LREWRITE_TAC ["inv"; "egr"]
        [SUBMAP_REFL; subglobals_refl; orac_forward_rel_refl] THEN
      CONJ_TAC THENL [USE_THEN "inv" (ACCEPT_TAC o MATCH_MP invariant_IMP_s_rel); ALL_TAC] THEN
      X_GEN_TAC `envr:v sem_env` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      REWRITE_TAC[env_domain_eq_def; v_rel_global_eqn] THEN
      SIMP_NOASM[nsLookup_nsEmpty; nsDom_alist_to_ns; nsDomMod_alist_to_ns] THEN
      REWRITE_TAC[nsLookup_nsBind_If; nsLookup_nsEmpty] THEN REPEAT GEN_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      MAP_EVERY EXISTS_TAC [`n':num`; `v':flat_v`; `tr:tra`] THEN
      FLATP2AUX_LREWRITE_TAC ["nlt"; "gel"; "vr"] []]]);;

let FLATP2AUX_cc_Dletrec = prove
 (FLATP2AUX_cc_case 21,
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "cd"; "gei"; "nte"; "egr"; "efr"; "ip"]) THEN
  REMOVE_THEN "cd" (MP_TAC o REWRITE_RULE[source_to_flat_compile_decs_def]) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["e1"; "e2"; "e3"; "e4"; "e5"]) THEN
  MAP_EVERY (fun l -> REMOVE_THEN l (SUBST_ALL_TAC o SYM)) ["e1"; "e2"; "e3"; "e4"; "e5"] THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  COND_CASES_TAC THENL
   [POP_ASSUM(LABEL_TAC "dist"); REWRITE_TAC[PAIR_EQ] THEN USE_THEN "nte" MP_TAC THEN MESON_TAC[]] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[FLATP2AUX_flat_decs_sing; flat_evaluate_def; compile_funs_dom2] THEN
  USE_THEN "dist" (fun th -> REWRITE_TAC[REWRITE_RULE[FLATP2AUX_FST3_case] (CONJUNCT1 th)]) THEN
  REWRITE_TAC[flat_environment_INFO.ri_accessors; flat_build_rec_env_merge; APPEND_NIL] THEN
  REWRITE_TAC[FLATP2AUX_MAP_compile_funs] THEN SIMP_NOASM[] THEN
  FLATP2AUX_MAKE_VARLS_TAC ["interp"; "g"; "gen"; "genv"; "idx"; "end_idx"; "os"; "st"; "s_i1";
    "next_indices_vidx idx"; "REVERSE (MAP FST (funs:(varN#varN#exp)list))"]
    ["0"; "backend_common_None"] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[flat_environment_INFO.ri_accessors; FLATP2AUX_MAP_FST_rec] THEN
    USE_THEN "dist" (fun th -> REWRITE_TAC[REWRITE_RULE[FLATP2AUX_FST3_case] (CONJUNCT1 th)]) THEN
    FLATP2AUX_LREWRITE_TAC ["inv"] [LENGTH_REVERSE; LENGTH_MAP] THEN
    USE_THEN "ip" (MP_TAC o REWRITE_RULE[idx_prev_def]) THEN SIMP_NOASM[] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`genv2:global_env`; `st2:(C,FFI)flat_state`]
    (FLATP2AUX_LABEL_CONJS ["fe2"; "inv2"; "c2"; "t2"; "sg2"; "gi2"])) THEN
  MAP_EVERY EXISTS_TAC [`st2:(C,FFI)flat_state`; `genv2:global_env`] THEN
  FLATP2AUX_LREWRITE_TAC ["fe2"] [] THEN CASE_REWRITE_TAC[] THEN
  USE_THEN "inv2" (LABEL_TAC "inv2'" o REWRITE_RULE[LENGTH_REVERSE; LENGTH_MAP]) THEN
  FLATP2AUX_LREWRITE_TAC ["inv2'"; "egr"; "c2"; "t2"; "sg2"]
    [SUBMAP_REFL; orac_forward_rel_refl; build_rec_env_merge; nsAppend_nsEmpty] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "inv2" (ACCEPT_TAC o MATCH_MP invariant_IMP_s_rel);
    MATCH_MP_TAC FLATP2AUX_env_domain_eq_alist THEN
    REWRITE_TAC[fst_alloc_defs; LIST_TO_SET_REVERSE; FLATP2AUX_MAP_FST_rec];
    USE_THEN "gi2" (MP_TAC o SPECL [CASE_TERM `MAP (\fne. match fne with (f,y) ->
        (match y with (n,e) -> (f, Recclosure env (funs:(varN#varN#exp)list) f))) funs`;
        `t + 1`]) THEN
    REWRITE_TAC[flat_environment_INFO.ri_accessors; FLATP2AUX_MAP_FST_rec] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FLATP2AUX_env_rel_map THEN X_GEN_TAC `f:varN` THEN DISCH_TAC THEN
    MATCH_MP_TAC FLATP2AUX_v_rel_Recclosure_top THEN
    MATCH_MP_TAC global_env_inv_weak THEN EXISTS_TAC `genv:global_env` THEN
    FLATP2AUX_LREWRITE_TAC ["gei"; "c2"; "t2"; "sg2"] [SUBMAP_REFL]]);;

let FLATP2AUX_cc_Dexn = prove
 (FLATP2AUX_cc_case 25,
  (REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "cd"; "gei"; "nte"; "egr"; "efr"; "ip"]) THEN
  REMOVE_THEN "cd" (MP_TAC o REWRITE_RULE[source_to_flat_compile_decs_def]) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["e1"; "e2"; "e3"; "e4"; "e5"]) THEN
  MAP_EVERY (fun l -> REMOVE_THEN l (SUBST_ALL_TAC o SYM)) ["e1"; "e2"; "e3"; "e4"; "e5"] THEN
  REMOVE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[flat_evaluate_def; distinctness "result"; injectivity "result"]) THEN
  (FLATP2AUX_INV_TAC "inv" THEN
  SUBGOAL_THEN `!a. ~(((next_indices_eidx idx, NONE), a) IN FDOM (global_env_c genv))`
    (LABEL_TAC "kfresh") THENL
   [X_GEN_TAC `a:num` THEN DISCH_TAC THEN
    USE_THEN "idx_range" (MP_TAC o REWRITE_RULE[idx_range_rel_def; PAIR_EQ]) THEN
    DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`i0:next_indices`; `e0:next_indices`; `fin:next_indices`;
       `ob:num#idx_types->bool`] (FLATP2AUX_LABEL_CONJS ["eq"; "f"; "p"; "dj"; "tsr"; "enr"])) THEN
    REMOVE_THEN "eq" (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM)
         (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM))) THEN
    USE_THEN "dj" (MP_TAC o SPECL [`0`; `3`] o REWRITE_RULE[ALL_DISJOINT_DEF]) THEN
    REWRITE_TAC[LENGTH] THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `(next_indices_eidx idx, Idx_Exn)`) THEN
    REWRITE_TAC[idx_block_def; genv_allocated_idxs_def; IN_UNION; IN_ELIM_THM; PAIR_EQ;
                distinctness "idx_types"] THEN
    USE_THEN "ip" (MP_TAC o REWRITE_RULE[idx_prev_def]) THEN SIMP_NOASM[] THEN
    ASM_MESON_TAC[LE_REFL; ARITH_RULE `e + 1 <= x ==> e < x`];
    ALL_TAC]) THEN
  (MAP_EVERY EXISTS_TAC [`s_i1:(C,FFI)flat_state`;
    `global_env_c_fupd (K (FUNION (global_env_c genv)
       (FEMPTY |+ (((next_indices_eidx idx, NONE), LENGTH (ts:ast_t list)),
                   ExnStamp (state_next_exn_stamp (st:(FFI)state)))))) genv`;
    `NONE:((flat_v)error_result)option`] THEN
  REWRITE_TAC[source_to_flatProof_abort_simps] THEN SIMP_NOASM[]) THEN
  (SUBGOAL_THEN `~(ExnStamp (state_next_exn_stamp (st:(FFI)state)) IN FRANGE (global_env_c genv))`
    (LABEL_TAC "exfresh") THENL
   [USE_THEN "idx_range" (MP_TAC o REWRITE_RULE[idx_range_rel_def]) THEN
    DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`i0:next_indices`; `e0:next_indices`; `fin:next_indices`;
       `ob:num#idx_types->bool`] (MP_TAC o last o CONJUNCTS)) THEN
    DISCH_THEN(MP_TAC o SPEC `state_next_exn_stamp (st:(FFI)state)`) THEN
    REWRITE_TAC[GE; LE_REFL];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FLATP2AUX_s_rel_weak THEN EXISTS_TAC `genv:global_env` THEN
    SIMP_NOASM[SUBMAP_FUNION_ID; SUBMAP_REFL; subglobals_refl] THEN
    USE_THEN "s_rel" MP_TAC THEN REWRITE_TAC[source_to_flatProof_s_rel_cases] THEN SIMP_NOASM[];
    MATCH_MP_TAC FLATP2AUX_invariant_genv_ext THEN
    MAP_EVERY EXISTS_TAC [`genv:global_env`; `idx:next_indices`; `st:(FFI)state`] THEN
    SIMP_NOASM[SUBMAP_FUNION_ID; SUBMAP_REFL] THEN FLATP2AUX_LREWRITE_TAC ["inv"] [] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FLATP2AUX_genv_c_ok_exn THEN FLATP2AUX_LREWRITE_TAC ["c_ok"; "exfresh"] [];
      MATCH_MP_TAC FLATP2AUX_genv_c_tys_ok_exn THEN FLATP2AUX_LREWRITE_TAC ["tys_ok"] [];
      MATCH_MP_TAC FLATP2AUX_idx_range_exn THEN FLATP2AUX_LREWRITE_TAC ["idx_range"] [] THEN
      USE_THEN "ip" (MP_TAC o REWRITE_RULE[idx_prev_def]) THEN SIMP_NOASM[] THEN ARITH_TAC];
    REWRITE_TAC[SUBMAP_FUNION_ID];
    REWRITE_TAC[subglobals_refl];
    MATCH_ACCEPT_TAC FLATP2AUX_env_domain_eq_sing;
    FLATP2AUX_LREWRITE_TAC ["egr"] [];
    MATCH_MP_TAC FLATP2AUX_global_env_inv_exn THEN
    SIMP_NOASM[FLOOKUP_FUNION; FLOOKUP_UPDATE; FLOOKUP_EMPTY] THEN
    USE_THEN "kfresh" (fun th -> REWRITE_TAC[REWRITE_RULE[GSYM flookup_thm] th]) THEN
    CASE_REWRITE_TAC[]]));;

let FLATP2AUX_cc_Dtype = prove
 (FLATP2AUX_cc_case 22,
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "cd"; "gei"; "nte"; "egr"; "efr"; "ip"]) THEN
  REMOVE_THEN "cd" (MP_TAC o REWRITE_RULE[source_to_flat_compile_decs_def]) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["e1"; "e2"; "e3"; "e4"; "e5"]) THEN
  MAP_EVERY (fun l -> REMOVE_THEN l (SUBST_ALL_TAC o SYM)) ["e1"; "e2"; "e3"; "e4"; "e5"] THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  COND_CASES_TAC THENL
   [POP_ASSUM(LABEL_TAC "dall"); REWRITE_TAC[PAIR_EQ] THEN USE_THEN "nte" MP_TAC THEN MESON_TAC[]] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  MP_TAC(ISPECL [`interp:(v->(source_to_flat_config#C)option)option`;
    `g:dec list->dec list`; `gen:environment_generation_store`; `end_idx:next_indices`;
    `os:num#idx_types->bool`; `s_i1:(C,FFI)flat_state`; `comp_map:source_to_flat_environment`;
    `env:v sem_env`; `tds:(tvarN list # mlstring # (mlstring # ast_t list) list) list`;
    `idx:next_indices`; `st:(FFI)state`; `genv:global_env`] FLATP2AUX_dtype_ind) THEN
  ANTS_TAC THENL
   [FLATP2AUX_LREWRITE_TAC ["inv"; "gei"; "dall"] [] THEN
    USE_THEN "ip" (MP_TAC o REWRITE_RULE[idx_prev_def]) THEN SIMP_NOASM[] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `genv':global_env`
    (FLATP2AUX_LABEL_CONJS ["sc"; "sy"; "sv"; "inv'"; "gi'"; "ed'"])) THEN
  MAP_EVERY EXISTS_TAC [`s_i1:(C,FFI)flat_state`; `genv':global_env`;
                        `NONE:((flat_v)error_result)option`] THEN
  REWRITE_TAC[flat_evaluate_def; distinctness "result"; injectivity "result"] THEN
  REWRITE_TAC[state_INFO.ri_accfupds; K_THM; orac_forward_rel_refl] THEN
  FLATP2AUX_LREWRITE_TAC ["inv'"; "sc"; "sy"; "sv"; "egr"] [subglobals_refl] THEN
  CONJ_TAC THENL
   [USE_THEN "inv'" (ACCEPT_TAC o MATCH_MP invariant_IMP_s_rel);
    X_GEN_TAC `envr:v sem_env` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    FLATP2AUX_LREWRITE_TAC ["gi'"; "ed'"] []]);;

let FLATP2AUX_cc_Denv = prove
 (FLATP2AUX_cc_case 24,
  (REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "cd"; "gei"; "nte"; "egr"; "efr"; "ip"]) THEN
  REMOVE_THEN "cd" (MP_TAC o REWRITE_RULE[source_to_flat_compile_decs_def]) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["e1"; "e2"; "e3"; "e4"; "e5"]) THEN
  MAP_EVERY (fun l -> REMOVE_THEN l (SUBST_ALL_TAC o SYM)) ["e1"; "e2"; "e3"; "e4"; "e5"] THEN
  REMOVE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  FLATP2AUX_OPTION_CASES_TAC `declare_env (state_eval_state (st:(FFI)state)) env`
    `xe:v#(eval_state)option` "de" THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM o CONJUNCT2) THEN
    USE_THEN "nte" MP_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  FLATP2AUX_PAIR_TAC `xe:v#(eval_state)option` `x:v` `es2:(eval_state)option` "xeq" THEN
  REMOVE_THEN "xeq" SUBST_ALL_TAC THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  FLATP2AUX_INV_TAC "inv") THEN
  (SUBGOAL_THEN `?es. state_eval_state (st:(FFI)state) = SOME (EvalOracle es)`
    STRIP_ASSUME_TAC THENL
   [USE_THEN "orac_rel" MP_TAC THEN USE_THEN "de" MP_TAC THEN
    CASES_ON `state_eval_state (st:(FFI)state)` THEN REWRITE_TAC[declare_env_def] THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "option"] THEN
    CASES_ON `a:eval_state` THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[orac_rel_def] THEN CASE_REWRITE_TAC[] THEN
    CASES_ON `interp:(v->(source_to_flat_config#C)option)option` THEN
    CASE_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
    `state_eval_state (st:(FFI)state) = SOME (EvalOracle es)`]) THEN
  REWRITE_TAC[ASSUME `state_eval_state (st:(FFI)state) = SOME (EvalOracle es)`] THEN
  USE_THEN "src_orac" (MP_TAC o MATCH_MP step_1 o CONJUNCT1 o REWRITE_RULE[src_orac_invs_def]) THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`dec:v->(source_to_flat_config#C)option`; `env_id0:num#num`;
    `st_v0:v`; `decs0:dec list`; `fdecs0:flat_exp list`; `c0:source_to_flat_config`; `x0:C`;
    `env_id1:num#num`; `st_v1:v`; `decs1:dec list`; `c1:source_to_flat_config`; `x1:C`]
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (MP_TAC o last o CONJUNCTS))) THEN
  DISCH_THEN(LABEL_TAC "nc") THEN
  REMOVE_THEN "de" (MP_TAC o REWRITE_RULE[declare_env_def]) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[oEL_THM] THEN COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  USE_THEN "egr" (MP_TAC o REWRITE_RULE[env_gen_rel_def]) THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["eg1"; "eg2"; "eg3"])) THEN
  (SUBGOAL_THEN `next_indices_vidx idx < next_indices_vidx end_idx` (LABEL_TAC "vlt") THENL
   [USE_THEN "ip" (MP_TAC o REWRITE_RULE[idx_prev_def]) THEN SIMP_NOASM[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `next_indices_vidx idx < LENGTH (flat_state_globals (s_i1:(C,FFI)flat_state)) /\
                EL (next_indices_vidx idx) (flat_state_globals s_i1) = NONE`
    (CONJUNCTS_THEN2 (LABEL_TAC "vl") (LABEL_TAC "vn")) THENL
   [MP_TAC(MATCH_MP FLATP2AUX_idx_range_var_fresh (end_itlist CONJ
      [ASSUME `idx_range_rel (SOME (dec:v->(source_to_flat_config#C)option)) genv
                 (state_next_type_stamp (st:(FFI)state)) (state_next_exn_stamp st)
                 (SOME (EvalOracle es)) (idx,end_idx,os)`;
       ASSUME `next_indices_vidx idx < next_indices_vidx end_idx`;
       ASSUME `fin_idx_match (LENGTH (flat_state_globals (s_i1:(C,FFI)flat_state))) end_idx
                 (src_orac_next_cfg (SOME (dec:v->(source_to_flat_config#C)option))
                    (SOME (EvalOracle es)))`])) THEN
    FLATP2AUX_LREWRITE_TAC ["globals"] [] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`s_i1:(C,FFI)flat_state`; `next_indices_vidx idx`;
    `environment_generation_store_generation gen`; `environment_generation_store_next gen`]
    FLATP2AUX_evaluate_global_init) THEN
  FLATP2AUX_LREWRITE_TAC ["vl"; "vn"] [] THEN DISCH_THEN SUBST1_TAC) THEN
  (FLATP2AUX_EXISTSL [{|flat_state_globals_fupd (K (LUPDATE (SOME (flat_Conv NONE
      [flat_Litv (IntLit (&(environment_generation_store_generation gen)));
       flat_Litv (IntLit (&(environment_generation_store_next gen)))]))
      (next_indices_vidx idx) (flat_state_globals s_i1))) s_i1|};
    {|global_env_v_fupd (K (LUPDATE (SOME (flat_Conv NONE
      [flat_Litv (IntLit (&(environment_generation_store_generation gen)));
       flat_Litv (IntLit (&(environment_generation_store_next gen)))]))
      (next_indices_vidx idx) (global_env_v genv))) genv|};
    {|NONE:((flat_v)error_result)option|}] THEN
  REWRITE_TAC[source_to_flatProof_abort_simps; injectivity "result"; distinctness "result"] THEN
  SUBGOAL_THEN `subglobals (global_env_v genv) (LUPDATE (SOME (flat_Conv NONE
      [flat_Litv (IntLit (&(environment_generation_store_generation gen)));
       flat_Litv (IntLit (&(environment_generation_store_next gen)))]))
      (next_indices_vidx idx) (global_env_v genv))` (LABEL_TAC "sgl") THENL
   [MATCH_MP_TAC FLATP2AUX_subglobals_LUPDATE_NONE THEN
    FLATP2AUX_LREWRITE_TAC ["globals"; "vl"; "vn"] [];
    ALL_TAC] THEN
  SUBGOAL_THEN `source_to_flatProof_s_rel (global_env_v_fupd (K (LUPDATE (SOME (flat_Conv NONE
      [flat_Litv (IntLit (&(environment_generation_store_generation gen)));
       flat_Litv (IntLit (&(environment_generation_store_next gen)))]))
      (next_indices_vidx idx) (global_env_v genv))) genv)
      (state_eval_state_fupd (K (SOME (EvalOracle (eval_oracle_state_envs_fupd
       (K (LUPDATE (APPEND (EL (eval_oracle_state_generation es) (eval_oracle_state_envs es)) [env])
            (eval_oracle_state_generation es) (eval_oracle_state_envs es))) es)))) (st:(FFI)state))
      (flat_state_globals_fupd (K (LUPDATE (SOME (flat_Conv NONE
      [flat_Litv (IntLit (&(environment_generation_store_generation gen)));
       flat_Litv (IntLit (&(environment_generation_store_next gen)))]))
      (next_indices_vidx idx) (flat_state_globals s_i1))) (s_i1:(C,FFI)flat_state))`
    (LABEL_TAC "sr'") THENL
   [MATCH_MP_TAC FLATP2AUX_s_rel_weak THEN EXISTS_TAC `genv:global_env` THEN
    REWRITE_TAC[global_env_INFO.ri_accfupds; K_THM; SUBMAP_REFL] THEN
    FLATP2AUX_LREWRITE_TAC ["sgl"] [] THEN
    USE_THEN "s_rel" MP_TAC THEN REWRITE_TAC[source_to_flatProof_s_rel_cases] THEN
    REWRITE_TAC[state_INFO.ri_accfupds; flat_state_INFO.ri_accfupds];
    ALL_TAC] THEN
  FLATP2AUX_LREWRITE_TAC ["sr'"] [] THEN
  REWRITE_TAC[global_env_INFO.ri_accfupds; K_THM; SUBMAP_REFL; state_INFO.ri_accfupds] THEN
  FLATP2AUX_LREWRITE_TAC ["sgl"] []) THEN
  CONJ_TAC THENL
  [CONJ_TAC THENL
   [(REWRITE_TAC[invariant_def; src_orac_invs_def] THEN
  REWRITE_TAC[global_env_INFO.ri_accfupds; K_THM; state_INFO.ri_accfupds;
              flat_state_INFO.ri_accfupds; FLATP2AUX_invs_envs] THEN
  FLATP2AUX_LREWRITE_TAC ["c_ok"; "tys_ok"; "sr'"; "orac_rel"] [] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FLATP2AUX_idx_range_var THEN EXISTS_TAC `SOME (EvalOracle es)` THEN
    FLATP2AUX_LREWRITE_TAC ["idx_range"; "vlt"; "globals"; "vl"] [FLATP2AUX_invs_envs];
    USE_THEN "src_orac" (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[src_orac_invs_def]);
    MATCH_MP_TAC FLATP2AUX_env_invs_declare THEN
    MAP_EVERY EXISTS_TAC [`genv:global_env`; `comp_map:source_to_flat_environment`;
                          `gen:environment_generation_store`] THEN
    REWRITE_TAC[global_env_INFO.ri_accfupds; K_THM; SUBMAP_REFL] THEN
    FLATP2AUX_LREWRITE_TAC ["efr"; "eg1"; "eg2"; "eg3"; "gei"; "sgl"] [] THEN
    USE_THEN "src_orac" (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[src_orac_invs_def]);
    REWRITE_TAC[src_orac_gen_inv_def] THEN CASE_REWRITE_TAC[] THEN
    SIMP_NOASM[LENGTH_LUPDATE] THEN FLATP2AUX_LREWRITE_TAC ["eg2"] [];
    FLATP2AUX_LREWRITE_TAC ["globals"] [];
    MATCH_MP_TAC FLATP2AUX_eval_ref_inv_LUPDATE THEN FLATP2AUX_LREWRITE_TAC ["eval_ref"] [] THEN
    DISCH_THEN(fun th -> USE_THEN "vn" (MP_TAC o REWRITE_RULE[th])) THEN
    USE_THEN "eval_ref" (MP_TAC o MATCH_MP FLATP2AUX_eval_ref_inv_cons) THEN
    DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`xs:(flat_v option)list`; `v0:flat_v`;
      `rs:(flat_v store_v)list`] (SUBST1_TAC o CONJUNCT1)) THEN
    REWRITE_TAC[EL; HD; distinctness "option"];
    USE_THEN "env_gen_inv" MP_TAC THEN
    SIMP_NOASM[env_gen_inv_def; SUBSET; IN_COUNT; domain_insert; IN_INSERT] THEN
    MESON_TAC[ARITH_RULE `x < n ==> x < n + 1`; ARITH_RULE `n < n + 1`];
    FLATP2AUX_LREWRITE_TAC ["fin_idx"] [LENGTH_LUPDATE]]);
    (REWRITE_TAC[orac_forward_rel_def; orac_config_envs_subspt_def; FLATP2AUX_invs_envs] THEN
  CONJ_TAC THENL
   [CASES_ON `src_orac_next_cfg (SOME (dec:v->(source_to_flat_config#C)option))
                (SOME (EvalOracle es))` THEN REWRITE_TAC[OPTREL_THM; subspt_refl];
    REWRITE_TAC[eval_state_call_rel_def] THEN CASE_REWRITE_TAC[] THEN
    SIMP_NOASM[LENGTH_LUPDATE; EL_LUPDATE] THEN
    MESON_TAC[ARITH_RULE `i < n ==> ~(i = n)`]])];
   (X_GEN_TAC `envr:v sem_env` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FLATP2AUX_nsBind_nsEmpty_sing; FLATP2AUX_env_domain_eq_sing_v];
    REWRITE_TAC[env_gen_rel_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[environment_generation_store_INFO.ri_accfupds;
                eval_oracle_state_INFO.ri_accfupds; K_THM; LENGTH_LUPDATE; EL_LUPDATE] THEN
    FLATP2AUX_LREWRITE_TAC ["eg1"; "eg2"; "eg3"] [LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
    REWRITE_TAC[v_rel_global_eqn] THEN
    SIMP_NOASM[nsLookup_nsSing; nsLookup_nsEmpty; FLATP2AUX_nsBind_nsEmpty_sing;
               distinctness "option"] THEN
    FLATP2AUX_EXISTS {|flat_Conv NONE
      [flat_Litv (IntLit (&(environment_generation_store_generation gen)));
       flat_Litv (IntLit (&(environment_generation_store_next gen)))]|} THEN
    REWRITE_TAC[EL_LUPDATE] THEN FLATP2AUX_LREWRITE_TAC ["globals"; "vl"] [] THEN
    FLATP2AUX_LREWRITE_TAC ["eg1"; "eg3"] [nat_to_v_def] THEN
    SIMP_NOASM[v_rel_eqns; ALL2]])]);;

let FLATP2AUX_cc_App = prove
 (FLATP2AUX_cc_case 8,
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ih0"; "ihf"; "ihe"; "iht"]) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["ev"; "inv"; "ear"; "lts"; "egr"; "nte"; "esi"]) THEN
  REMOVE_THEN "esi" SUBST_ALL_TAC THEN
  FLATP2AUX_PAIR_TAC `evaluate (st:(FFI)state) env (REVERSE es)` `st1:(FFI)state`
    `r1:(v list,v)result` "ev1" THEN
  USE_THEN "ev" (MP_TAC o REWRITE_RULE[full_evaluate_def]) THEN
  FLATP2AUX_LREWRITE_TAC ["ev1"] [] THEN CASE_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ev'") THEN
  SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(v list,v)result)` (LABEL_TAC "nte1") THENL
   [DISCH_THEN SUBST_ALL_TAC THEN USE_THEN "ev'" MP_TAC THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM o CONJUNCT2) THEN
    USE_THEN "nte" MP_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  FLATP2AUX_IH_TAC "ih0" [("s'", `st1:(FFI)state`); ("r", `r1:(v list,v)result`)] THEN
  ANTS_TAC THENL [FLATP2AUX_ANTS_TAC; ALL_TAC] THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s1_i1:(C,FFI)flat_state`;
    `r1_i1:(flat_v list,flat_v)result`; `genv1:global_env`]
    (FLATP2AUX_LABEL_CONJS ["fe1"; "rr1"; "sr1"; "na1"])) THEN
  REWRITE_TAC FLATP2AUX_compile_exps_clauses THEN
  FLATP2AUX_RESULT_CASES_TAC `r1:(v list,v)result` `vs:v list` `err1:(v)error_result` THENL
   [USE_THEN "rr1" (X_CHOOSE_THEN `vs1':flat_v list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      (LABEL_TAC "vr1" o REWRITE_RULE[o_THM])) o MATCH_MP FLATP2AUX_result_rel_Rval) THEN
    USE_THEN "na1" (MP_TAC o REWRITE_RULE[source_to_flatProof_abort_simps]) THEN
    DISCH_THEN(FLATP2AUX_LABEL_CONJS ["inv1"; "eg1"; "of1"; "sc1"; "sy1"; "sg1"]) THEN
    ASM_CASES_TAC `op = AallocEmpty` THENL
     [(* ALLOC *)
      FIRST_X_ASSUM(fun th -> if concl th = `op = AallocEmpty` then SUBST_ALL_TAC th
                              else failwith "") THEN
      FLATP2AUX_ISPECL_TAC ["interp"; "g"; "gen"; "genv1"; "idxs"; "st"; "env"; "es";
        "st1"; "vs"; "env_i1"; "s_i1"; "t";
        "source_to_flat_environment_v_fupd (K (bind_locals ts locals (source_to_flat_environment_v comp_map))) comp_map";
        "s1_i1"; "vs1'"; "s'"; "r"] FLATP2AUX_App_alloc THEN
      ANTS_TAC THENL
       [FLATP2AUX_LREWRITE_TAC ["ev1"; "ev"; "nte"; "fe1"; "vr1"; "inv1"] []; ALL_TAC] THEN
      DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s2_i1:(C,FFI)flat_state`;
        `r2_i1:(flat_v list,flat_v)result`] (FLATP2AUX_LABEL_CONJS ["fe2"; "rr2"; "sr2"; "inv2"; "es2"])) THEN
      MAP_EVERY EXISTS_TAC [`s2_i1:(C,FFI)flat_state`; `r2_i1:(flat_v list,flat_v)result`;
                            `genv1:global_env`] THEN
      FLATP2AUX_LREWRITE_TAC ["fe2"; "rr2"; "sr2"; "inv2"; "es2"; "eg1"; "of1"; "sc1"; "sy1"; "sg1"] [];
      ALL_TAC] THEN
    ASM_CASES_TAC `op = Env_id` THENL [(* ENVID *) (FIRST_X_ASSUM(fun th -> if concl th = `op = Env_id` then SUBST_ALL_TAC th else failwith "") THEN
  USE_THEN "ev'" MP_TAC THEN SIMP_NOASM[]) THEN
  (FLATP2AUX_OPTION_CASES_TAC `do_app (state_refs (st1:(FFI)state),state_ffi st1) Env_id (REVERSE vs)`
    `res:((v store_v)list # (FFI)ffi_state) # (v,v)result` "da" THEN
  CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM o CONJUNCT2) THEN
    USE_THEN "nte" MP_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "da" (MP_TAC o MATCH_MP FLATP2AUX_do_app_Env_id) THEN
  DISCH_THEN(DISJ_CASES_THEN2
    (FLATP2AUX_CHOOSE_THEN [`envx:v sem_env`; `gx:num`; `ix:num`] (LABEL_TAC "rvs"))
    (FLATP2AUX_CHOOSE_THEN [`gv:v`; `iv:v`] (CONJUNCTS_THEN2 (LABEL_TAC "rvs") SUBST_ALL_TAC))) THENL
   [USE_THEN "rvs" (MP_TAC o AP_TERM `REVERSE:v list->v list`) THEN
    REWRITE_TAC[REVERSE_REVERSE; REVERSE; APPEND] THEN DISCH_THEN SUBST_ALL_TAC THEN
    USE_THEN "vr1" (MP_TAC o REWRITE_RULE[LIST_REL_CONS1; v_rel_eqns]) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "rvs" (MP_TAC o AP_TERM `REVERSE:v list->v list`) THEN
  REWRITE_TAC[REVERSE_REVERSE; REVERSE; APPEND] THEN DISCH_THEN SUBST_ALL_TAC THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ; list_result_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  USE_THEN "ev1" (MP_TAC o SYM o MATCH_MP (CONJUNCT1 evaluate_length)) THEN
  REWRITE_TAC[LENGTH; LENGTH_REVERSE; ONE] THEN
  MP_TAC(ISPEC `es:exp list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `e1:exp` (X_CHOOSE_THEN `es1:exp list` SUBST_ALL_TAC))) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; LENGTH_EQ_NIL] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  REWRITE_TAC[FLATP2AUX_state_refs_ffi_eta] THEN
  REWRITE_TAC[source_to_flat_compile_exp_def; distinctness "op"] THEN CASE_REWRITE_TAC[] THEN
  USE_THEN "fe1" (MP_TAC o REWRITE_RULE([REVERSE; APPEND] @ FLATP2AUX_compile_exps_clauses)) THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`; `Rval vs1':(flat_v list,flat_v)result`;
                        `genv1:global_env`] THEN
  ASM_REWRITE_TAC[result_rel_eqns; o_THM] THEN
  FLATP2AUX_LREWRITE_TAC ["vr1"; "sr1"; "inv1"; "eg1"; "of1"; "sc1"; "sy1"; "sg1"] []); ALL_TAC] THEN
    (MP_TAC(ISPEC `getOpClass op` (cases "op_class")) THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (LABEL_TAC "cls")) THEN
    USE_THEN "cls" (fun th -> LABEL_TAC "opeq" (REWRITE_RULE[FLATP2AUX_getOpClass_cases] th)) THENL
     [(* EvalOp *)
      (USE_THEN "opeq" SUBST_ALL_TAC THEN
  USE_THEN "ev'" MP_TAC THEN SIMP_NOASM[do_eval_res_def]) THEN
      (FLATP2AUX_OPTION_CASES_TAC `do_eval (REVERSE vs) (state_eval_state (st1:(FFI)state))`
    `ddd:v sem_env # dec list # (eval_state)option` "de" THEN
  CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM o CONJUNCT2) THEN
    USE_THEN "nte" MP_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `ddd:v sem_env # dec list # (eval_state)option`
    (prove(`!x:A#B#C. ?a b c. x = (a,b,c)`, REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[]))) THEN
  DISCH_THEN(X_CHOOSE_THEN `env1:v sem_env` (X_CHOOSE_THEN `decs:dec list`
    (X_CHOOSE_THEN `es1:(eval_state)option` SUBST_ALL_TAC))) THEN
  CASE_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "evx") THEN
  MP_TAC(ISPECL [`REVERSE (vs1':flat_v list)`; `REVERSE (vs:v list)`; `st1:(FFI)state`;
    `env1:v sem_env`; `decs:dec list`; `es1:(eval_state)option`;
    `interp:(v->(source_to_flat_config#C)option)option`; `g:dec list->dec list`;
    `gen:environment_generation_store`; `genv1:global_env`;
    `idxs:next_indices#next_indices#(num#idx_types->bool)`; `s1_i1:(C,FFI)flat_state`] do_eval) THEN
  ANTS_TAC THENL
   [FLATP2AUX_LREWRITE_TAC ["de"; "inv1"] [] THEN MATCH_MP_TAC EVERY2_REVERSE THEN
    FLATP2AUX_LREWRITE_TAC ["vr1"] [];
    ALL_TAC] THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`genva:global_env`; `env_id:num#num`;
    `c:source_to_flat_config`; `decs':flat_exp list`; `ec':(C)install_config`;
    `c':source_to_flat_config`; `idx:next_indices`; `end_idx:next_indices`;
    `other:num#idx_types->bool`]
    (FLATP2AUX_LABEL_CONJS ["ix"; "fde"; "len6"; "icp"; "dne"; "inva"; "ega"; "efra"; "geia";
      "nca"; "ipa"; "sca"; "sya"; "sga"; "oca"; "esa"]))) THEN
      (USE_THEN "fe1" (fun fe -> USE_THEN "len6" (fun l6 -> USE_THEN "fde" (fun fd ->
    REWRITE_TAC[MATCH_MP FLATP2AUX_flat_Eval_code (end_itlist CONJ
      [REWRITE_RULE[compile_exps_reverse] fe; REWRITE_RULE[LENGTH_REVERSE] l6; fd])]))) THEN
  USE_THEN "sr1" (FLATP2AUX_LABEL_CONJS ["nn1"; "srf1"; "scl1"; "sff1"] o
                  REWRITE_RULE[source_to_flatProof_s_rel_cases]) THEN
  USE_THEN "scl1" (fun th -> REWRITE_TAC[GSYM th]) THEN
  USE_THEN "evx" (LABEL_TAC "evy" o REWRITE_RULE[state_INFO.ri_accfupds]) THEN
  ASM_CASES_TAC `state_clock (st1:(FFI)state) = 0` THEN POP_ASSUM(LABEL_TAC "c0") THEN
  FLATP2AUX_LREWRITE_TAC ["c0"] [] THENL
   [USE_THEN "evy" MP_TAC THEN FLATP2AUX_LREWRITE_TAC ["c0"] [PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`flat_state_eval_config_fupd (K ec') (s1_i1:(C,FFI)flat_state)`;
      `Rerr (Rabort Rtimeout_error):(flat_v list,flat_v)result`; `genv1:global_env`] THEN
    REWRITE_TAC[result_rel_eqns; source_to_flatProof_abort_simps] THEN
    REWRITE_TAC[source_to_flatProof_s_rel_cases; state_INFO.ri_accfupds;
                flat_state_INFO.ri_accfupds] THEN
    FLATP2AUX_LREWRITE_TAC ["nn1"; "srf1"; "scl1"; "sff1"] [];
    ALL_TAC]) THEN
      (USE_THEN "icp" (MP_TAC o REWRITE_RULE[inc_compile_prog_def]) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPEC `source_to_flat_compile_decs [] 1 (source_to_flat_config_next c)
      (lookup_env_id env_id (source_to_flat_config_envs c))
      (environment_generation_store_REC 0
         (environment_store_next (source_to_flat_config_envs c)) LN) decs`
    BASICAUX_TUPLE5) THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`n0:num`; `next1:next_indices`;
    `e1:source_to_flat_environment`; `gen1:environment_generation_store`; `p1:flat_exp list`]
    (LABEL_TAC "cdq")) THEN
  FLATP2AUX_LREWRITE_TAC ["cdq"] [] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c'eq") (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[FLATP2AUX_flat_glob_alloc; flat_evaluate_decs_append] THEN
  REWRITE_TAC[FLATP2AUX_flat_state_comm] THEN
  USE_THEN "c'eq" (LABEL_TAC "cnext" o REWRITE_RULE[source_to_flat_config_INFO.ri_accfupds; K_THM] o
                   AP_TERM `source_to_flat_config_next` o SYM) THEN
  REMOVE_THEN "cnext" (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN LABEL_TAC "cnext" th) THEN
  USE_THEN "inva" (LABEL_TAC "invad" o CONJUNCT2 o MATCH_MP invariant_dec_clock)) THEN
      (USE_THEN "evy" (LABEL_TAC "evz" o REWRITE_RULE[ASSUME `~(state_clock (st1:(FFI)state) = 0)`]) THEN
  FLATP2AUX_PAIR_TAC `evaluate_decs (dec_clock (state_eval_state_fupd (K es1) (st1:(FFI)state))) env1 decs`
    `st2:(FFI)state` `r2:(v sem_env,v)result` "ev4" THEN
  USE_THEN "evz" MP_TAC THEN FLATP2AUX_LREWRITE_TAC ["ev4"] [] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "ev5") THEN
  SUBGOAL_THEN `~(r2 = Rerr (Rabort Rtype_error):(v sem_env,v)result)` (LABEL_TAC "nte2") THENL
   [DISCH_THEN SUBST_ALL_TAC THEN USE_THEN "ev5" MP_TAC THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM o CONJUNCT2) THEN
    USE_THEN "nte" MP_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "ihe" (MP_TAC o SPECL [`vs:v list`; `st1:(FFI)state`;
    `state_eval_state_fupd (K es1) (st1:(FFI)state)`; `env1:v sem_env`; `decs:dec list`]) THEN
  ANTS_TAC THENL
   [FLATP2AUX_LREWRITE_TAC ["ev1"; "de"; "c0"] [getOpClass_def; do_eval_res_def;
      state_INFO.ri_accfupds] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "ihe'")) THEN
      (FLATP2AUX_IH_TAC "ihe'" [("s'", `st2:(FFI)state`); ("r", `r2:(v sem_env,v)result`);
    ("path", `[]:mlstring list`); ("t", `1`);
    ("idx", `source_to_flat_config_next c`); ("end_idx", `next1:next_indices`);
    ("os", `idx_block idx end_idx UNION (other:num#idx_types->bool)`);
    ("comp_map", `lookup_env_id env_id (source_to_flat_config_envs c)`);
    ("s_i1", `flat_dec_clock (flat_state_eval_config_fupd (K ec')
       (flat_state_globals_fupd (K (APPEND (flat_state_globals (s1_i1:(C,FFI)flat_state))
          (REPLICATE (next_indices_vidx next1 - next_indices_vidx (source_to_flat_config_next c))
             NONE))) s1_i1))`);
    ("idx'", `next1:next_indices`); ("comp_map'", `e1:source_to_flat_environment`);
    ("ds_i1", `p1:flat_exp list`); ("t'", `n0:num`); ("genv", `genva:global_env`);
    ("gen", `environment_generation_store_REC 0
       (environment_store_next (source_to_flat_config_envs c)) LN`);
    ("gen'", `gen1:environment_generation_store`)] THEN
  ANTS_TAC THENL
   [FLATP2AUX_LREWRITE_TAC ["ev4"; "invad"; "cdq"; "geia"; "nte2"] [idx_prev_refl] THEN
    REWRITE_TAC[dec_clock_def; state_INFO.ri_accfupds; K_THM] THEN
    FLATP2AUX_LREWRITE_TAC ["ega"] [] THEN
    USE_THEN "efra" MP_TAC THEN FLATP2AUX_LREWRITE_TAC ["cdq"] [] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s3_i1:(C,FFI)flat_state`; `genv3:global_env`;
    `r3_i1:((flat_v)error_result)option`] (FLATP2AUX_LABEL_CONJS ["fe3"; "sr3"; "na3"; "okv3"; "oke3"])) THEN
  FLATP2AUX_LREWRITE_TAC ["fe3"] [] THEN CASE_REWRITE_TAC[]) THEN
      (USE_THEN "ix" SUBST_ALL_TAC THEN
  FLATP2AUX_RESULT_CASES_TAC `r2:(v sem_env,v)result` `env2:v sem_env` `err2:(v)error_result`) THENL
      [(USE_THEN "okv3" (MP_TAC o SPEC `env2:v sem_env`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (FLATP2AUX_LABEL_CONJS ["ede2"; "egr2"; "gie2"])) THEN
  CASE_REWRITE_TAC[] THEN
  USE_THEN "na3" (MP_TAC o REWRITE_RULE[dec_clock_def; state_INFO.ri_accfupds; K_THM;
                                         source_to_flatProof_abort_simps]) THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["inv3"; "of3"; "sc3"; "sy3"; "sg3"]) THEN
  USE_THEN "ev5" MP_TAC THEN CASE_REWRITE_TAC[] THEN
  FLATP2AUX_OPTION_CASES_TAC `declare_env (state_eval_state (st2:(FFI)state)) (extend_dec_env env2 env1)`
    `xes:v # (eval_state)option` "dce" THEN
  CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM o CONJUNCT2) THEN
    USE_THEN "nte" MP_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  FLATP2AUX_PAIR_TAC `xes:v # (eval_state)option` `x:v` `es2:(eval_state)option` "xeq" THEN
  REMOVE_THEN "xeq" SUBST_ALL_TAC THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  USE_THEN "cdq" (LABEL_TAC "gen1g" o MATCH_MP compile_decs_generation) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[environment_generation_store_INFO.ri_accessors]) THEN
  FLATP2AUX_SUBGOAL {|match src_orac_next_cfg interp (state_eval_state st2) with
      NONE -> T
    | SOME cc -> (match lookup (environment_generation_store_generation gen1)
                          (environment_store_env_gens (source_to_flat_config_envs cc)) with
                    NONE -> F
                  | SOME gg -> (match lookup (environment_generation_store_next gen1) gg with
                                  NONE -> F
                                | SOME ee -> global_env_inv genv3 ee {} (extend_dec_env env2 env1)))|}
    (LABEL_TAC "lkc") THENL
   [USE_THEN "of3" (MP_TAC o CONJUNCT1 o REWRITE_RULE[orac_forward_rel_def]) THEN
    REWRITE_TAC[orac_config_envs_subspt_def] THEN FLATP2AUX_LREWRITE_TAC ["nca"] [OPTREL_SOME] THEN
    DISCH_THEN(X_CHOOSE_THEN `cc:source_to_flat_config` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
    CASE_REWRITE_TAC[] THEN
    USE_THEN "c'eq" (fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[source_to_flat_config_INFO.ri_accfupds; K_THM; environment_store_INFO.ri_accessors] THEN
    REWRITE_TAC[subspt_lookup] THEN
    DISCH_THEN(MP_TAC o SPEC `environment_store_next (source_to_flat_config_envs c)`) THEN
    REWRITE_TAC[lookup_insert] THEN
    DISCH_THEN(fun th -> FLATP2AUX_LREWRITE_TAC ["gen1g"] [MATCH_MP th (REFL `SOME (insert
       (environment_generation_store_next gen1)
       (extend_env e1 (lookup_env_id env_id (source_to_flat_config_envs c)))
       (environment_generation_store_envs gen1))`)]) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[lookup_insert] THEN CASE_REWRITE_TAC[] THEN
    MATCH_MP_TAC global_env_inv_append THEN FLATP2AUX_LREWRITE_TAC ["ede2"; "gie2"] [] THEN
    MATCH_MP_TAC global_env_inv_weak THEN EXISTS_TAC `genva:global_env` THEN
    FLATP2AUX_LREWRITE_TAC ["geia"; "sc3"; "sy3"; "sg3"] [];
    ALL_TAC]) THEN
       (FLATP2AUX_ISPECL_TAC ["st2"; "extend_dec_env env2 env1"; "x"; "es2"; "interp"; "g"; "gen1"; "genv3";
    "(next1, next1, idx_block idx end_idx UNION other):next_indices#next_indices#(num#idx_types->bool)";
    "s3_i1"; "environment_generation_store_generation gen1"; "environment_generation_store_next gen1"]
    declare_env_store_env_id THEN
  ANTS_TAC THENL
   [FLATP2AUX_LREWRITE_TAC ["dce"; "inv3"; "egr2"; "lkc"] []; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:flat_v` (FLATP2AUX_LABEL_CONJS ["fst"; "inv5"; "glx"; "vrx"; "ofx"])) THEN
  FLATP2AUX_LREWRITE_TAC ["fst"] [] THEN CASE_REWRITE_TAC[] THEN
  USE_THEN "glx" (X_CHOOSE_THEN `xs:(flat_v option)list` (LABEL_TAC "glx'")) THEN
  W(fun (asl,w) -> let tm = find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "flat_evaluate"
                                          with Failure _ -> false) w in
    MP_TAC(SPECL [rand(rator(rator tm)); rand(rator tm); `xs:(flat_v option)list`; `y:flat_v`;
                  `TL (flat_state_refs (s3_i1:(C,FFI)flat_state))`] FLATP2AUX_flat_eval_ref_read)) THEN
  REWRITE_TAC[flat_state_INFO.ri_accfupds; K_THM] THEN FLATP2AUX_LREWRITE_TAC ["glx'"] [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY EXISTS_TAC [`flat_state_refs_fupd (K (CONS (Refv y) (TL (flat_state_refs s3_i1))))
      (s3_i1:(C,FFI)flat_state)`; `Rval [y]:(flat_v list,flat_v)result`; `genv3:global_env`] THEN
  REWRITE_TAC[result_rel_eqns; o_THM; source_to_flatProof_abort_simps; injectivity "result"] THEN
  SUBGOAL_THEN `orac_forward_rel (interp:(v->(source_to_flat_config#C)option)option) es1
                  (state_eval_state (state_eval_state_fupd (K es2) (st2:(FFI)state)))`
    (LABEL_TAC "of5") THENL
   [REWRITE_TAC[state_INFO.ri_accfupds; K_THM] THEN MATCH_MP_TAC orac_forward_rel_trans THEN
    EXISTS_TAC `state_eval_state (st2:(FFI)state)` THEN FLATP2AUX_LREWRITE_TAC ["of3"; "ofx"] [];
    ALL_TAC] THEN
  FLATP2AUX_WITH_LABELS ["inv5"; "inv1"; "of5"; "ipa"; "oca"; "esa"]
    (fun ths -> MP_TAC(MATCH_MP invariant_end_eval (end_itlist CONJ ths))) THEN
  REWRITE_TAC[state_INFO.ri_accfupds; state_INFO.ri_fupdfupds; K_THM; K_o_THM] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["inv6"; "of6"; "eg6"]) THEN
  USE_THEN "inv6" (LABEL_TAC "inv7" o SPEC `y:flat_v` o MATCH_MP invariant_change_eval_ref) THEN
  FLATP2AUX_LREWRITE_TAC ["inv7"] [state_INFO.ri_accfupds; K_THM] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `[y:flat_v]` THEN FLATP2AUX_LREWRITE_TAC ["vrx"] [ALL2];
    USE_THEN "inv7" (ACCEPT_TAC o MATCH_MP invariant_IMP_s_rel);
    USE_THEN "eg1" (fun th -> USE_THEN "eg6" (ACCEPT_TAC o C MP th));
    MATCH_MP_TAC orac_forward_rel_trans THEN EXISTS_TAC `state_eval_state (st1:(FFI)state)` THEN
    FLATP2AUX_LREWRITE_TAC ["of1"; "of6"] [];
    MATCH_MP_TAC SUBMAP_TRANS THEN EXISTS_TAC `global_env_c genv1` THEN
    FLATP2AUX_LREWRITE_TAC ["sc1"] [] THEN
    MATCH_MP_TAC SUBMAP_TRANS THEN EXISTS_TAC `global_env_c genva` THEN
    FLATP2AUX_LREWRITE_TAC ["sca"; "sc3"] [];
    MATCH_MP_TAC SUBMAP_TRANS THEN EXISTS_TAC `global_env_tys genv1` THEN
    FLATP2AUX_LREWRITE_TAC ["sy1"] [] THEN
    MATCH_MP_TAC SUBMAP_TRANS THEN EXISTS_TAC `global_env_tys genva` THEN
    FLATP2AUX_LREWRITE_TAC ["sya"; "sy3"] [];
    MATCH_MP_TAC subglobals_trans THEN EXISTS_TAC `global_env_v genv1` THEN
    FLATP2AUX_LREWRITE_TAC ["sg1"] [] THEN
    MATCH_MP_TAC subglobals_trans THEN EXISTS_TAC `global_env_v genva` THEN
    FLATP2AUX_LREWRITE_TAC ["sga"; "sg3"] []]);
       (USE_THEN "oke3" (MP_TAC o SPEC `err2:(v)error_result`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ee3:(flat_v)error_result` (CONJUNCTS_THEN2 SUBST_ALL_TAC (LABEL_TAC "rre3"))) THEN
  CASE_REWRITE_TAC[] THEN
  USE_THEN "na3" (MP_TAC o REWRITE_RULE[dec_clock_def; state_INFO.ri_accfupds; K_THM]) THEN
  DISCH_THEN(LABEL_TAC "na3'") THEN
  USE_THEN "ev5" MP_TAC THEN CASES_ON `err2:(v)error_result` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  MAP_EVERY EXISTS_TAC [`s3_i1:(C,FFI)flat_state`; `Rerr ee3:(flat_v list,flat_v)result`;
                        `genv3:global_env`] THEN
  USE_THEN "rre3" (fun th -> REWRITE_TAC[MATCH_MP FLATP2AUX_result_rel_Rerr_f th]) THEN
  REWRITE_TAC[source_to_flatProof_abort_simps] THENL
   [ALL_TAC; FLATP2AUX_LREWRITE_TAC ["sr3"] []] THEN
  USE_THEN "na3'" (MP_TAC o REWRITE_RULE[source_to_flatProof_abort_simps]) THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["inv3"; "of3"; "sc3"; "sy3"; "sg3"]) THEN
  FLATP2AUX_WITH_LABELS ["inv3"; "inv1"; "of3"; "ipa"; "oca"; "esa"]
    (fun ths -> MP_TAC(MATCH_MP invariant_end_eval (end_itlist CONJ ths))) THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["inv4"; "of4"; "eg4"]) THEN
  REWRITE_TAC[state_INFO.ri_accfupds; K_THM] THEN
  FLATP2AUX_LREWRITE_TAC ["inv4"] [] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "sr3" MP_TAC THEN
    REWRITE_TAC[source_to_flatProof_s_rel_cases; state_INFO.ri_accfupds];
    USE_THEN "eg1" (fun th -> USE_THEN "eg4" (ACCEPT_TAC o C MP th));
    MATCH_MP_TAC orac_forward_rel_trans THEN EXISTS_TAC `state_eval_state (st1:(FFI)state)` THEN
    FLATP2AUX_LREWRITE_TAC ["of1"; "of4"] [];
    MATCH_MP_TAC SUBMAP_TRANS THEN EXISTS_TAC `global_env_c genv1` THEN
    FLATP2AUX_LREWRITE_TAC ["sc1"] [] THEN
    MATCH_MP_TAC SUBMAP_TRANS THEN EXISTS_TAC `global_env_c genva` THEN
    FLATP2AUX_LREWRITE_TAC ["sca"; "sc3"] [];
    MATCH_MP_TAC SUBMAP_TRANS THEN EXISTS_TAC `global_env_tys genv1` THEN
    FLATP2AUX_LREWRITE_TAC ["sy1"] [] THEN
    MATCH_MP_TAC SUBMAP_TRANS THEN EXISTS_TAC `global_env_tys genva` THEN
    FLATP2AUX_LREWRITE_TAC ["sya"; "sy3"] [];
    MATCH_MP_TAC subglobals_trans THEN EXISTS_TAC `global_env_v genv1` THEN
    FLATP2AUX_LREWRITE_TAC ["sg1"] [] THEN
    MATCH_MP_TAC subglobals_trans THEN EXISTS_TAC `global_env_v genva` THEN
    FLATP2AUX_LREWRITE_TAC ["sga"; "sg3"] []])];
      (* FunApp *)
      (USE_THEN "opeq" SUBST_ALL_TAC THEN
  USE_THEN "ev'" MP_TAC THEN SIMP_NOASM[] THEN
  FLATP2AUX_OPTION_CASES_TAC `do_opapp (REVERSE (vs:v list))` `ee:v sem_env # exp` "dop" THEN
  CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM o CONJUNCT2) THEN
    USE_THEN "nte" MP_TAC THEN REWRITE_TAC[];
    ALL_TAC]) THEN
  (FLATP2AUX_PAIR_TAC `ee:v sem_env # exp` `env':v sem_env` `e:exp` "eeq" THEN
  REMOVE_THEN "eeq" SUBST_ALL_TAC THEN CASE_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ev2")) THEN
  (MP_TAC(ISPECL [`genv1:global_env`; `REVERSE (vs:v list)`; `REVERSE (vs1':flat_v list)`;
    `env':v sem_env`; `e:exp`] do_opapp) THEN
  ANTS_TAC THENL
   [FLATP2AUX_LREWRITE_TAC ["dop"] [] THEN MATCH_MP_TAC EVERY2_REVERSE THEN
    FLATP2AUX_LREWRITE_TAC ["vr1"] [];
    ALL_TAC] THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`comp_map2:source_to_flat_environment`;
    `env_i2:(flat_v)flat_environment`; `locals2:mlstring list`; `t1:mlstring list`;
    `ts2:tra list`] (FLATP2AUX_LABEL_CONJS ["ear2"; "lts2"; "fdop"]))) THEN
  (REWRITE_TAC[source_to_flat_compile_exp_def; distinctness "op"] THEN
  REWRITE_TAC[astOp_to_flatOp_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[flat_evaluate_def; GSYM compile_exps_reverse] THEN
  FLATP2AUX_LREWRITE_TAC ["fe1"] [] THEN CASE_REWRITE_TAC[] THEN
  FLATP2AUX_LREWRITE_TAC ["fdop"] [] THEN CASE_REWRITE_TAC[]) THEN
  (USE_THEN "inv1" (CONJUNCTS_THEN2 (LABEL_TAC "clk") (LABEL_TAC "invd") o
                   MATCH_MP invariant_dec_clock) THEN
  USE_THEN "clk" (fun th -> REWRITE_TAC[GSYM th])) THEN
  (ASM_CASES_TAC `state_clock (st1:(FFI)state) = 0` THEN POP_ASSUM(LABEL_TAC "c0") THEN
  FLATP2AUX_LREWRITE_TAC ["c0"] [] THENL
   [USE_THEN "ev2" MP_TAC THEN FLATP2AUX_LREWRITE_TAC ["c0"] [PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`;
      `Rerr (Rabort Rtimeout_error):(flat_v list,flat_v)result`; `genv1:global_env`] THEN
    FLATP2AUX_LREWRITE_TAC ["sr1"] [result_rel_eqns; source_to_flatProof_abort_simps];
    ALL_TAC]) THEN
  (USE_THEN "ev2" (LABEL_TAC "ev3" o REWRITE_RULE[ASSUME `~(state_clock (st1:(FFI)state) = 0)`]) THEN
  USE_THEN "ihf" (MP_TAC o SPECL [`vs:v list`; `st1:(FFI)state`; `env':v sem_env`; `e:exp`]) THEN
  ANTS_TAC THENL
   [FLATP2AUX_LREWRITE_TAC ["ev1"; "dop"; "c0"] [getOpClass_def] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "ihf'")) THEN
  (FLATP2AUX_IH_TAC "ihf'" [("s'", `s':(FFI)state`); ("r", `r:(v list,v)result`);
    ("genv", `genv1:global_env`); ("comp_map", `comp_map2:source_to_flat_environment`);
    ("env_i1", `env_i2:(flat_v)flat_environment`);
    ("s_i1", `flat_dec_clock (s1_i1:(C,FFI)flat_state)`); ("locals", `locals2:mlstring list`);
    ("t", `t1:mlstring list`); ("ts", `ts2:tra list`); ("gen", `gen:environment_generation_store`);
    ("idxs", `idxs:next_indices#next_indices#(num#idx_types->bool)`)] THEN
  ANTS_TAC THENL
   [FLATP2AUX_ANTS_TAC THEN
    USE_THEN "eg1" MP_TAC THEN REWRITE_TAC[dec_clock_def; state_INFO.ri_accfupds];
    ALL_TAC] THEN
  REWRITE_TAC FLATP2AUX_compile_exps_clauses THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s2_i1:(C,FFI)flat_state`;
    `r2_i1:(flat_v list,flat_v)result`; `genv2:global_env`]
    (FLATP2AUX_LABEL_CONJS ["fe2"; "rr2"; "sr2"; "na2"])) THEN
  MAP_EVERY EXISTS_TAC [`s2_i1:(C,FFI)flat_state`; `r2_i1:(flat_v list,flat_v)result`;
                        `genv2:global_env`] THEN
  FLATP2AUX_LREWRITE_TAC ["fe2"; "rr2"; "sr2"] [] THEN
  DISCH_THEN(fun th -> USE_THEN "na2" (MP_TAC o C MP th)) THEN
  REWRITE_TAC[dec_clock_def; state_INFO.ri_accfupds] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["inv2"; "eg2"; "of2"; "sc2"; "sy2"; "sg2"]) THEN
  FLATP2AUX_LREWRITE_TAC ["inv2"; "eg2"] [] THEN
  FLATP2AUX_TRANS_TAC `state_eval_state (st1:(FFI)state)` `genv1:global_env`);
      (* Force *)
      (USE_THEN "opeq" SUBST_ALL_TAC THEN
  USE_THEN "ev'" MP_TAC THEN SIMP_NOASM[]) THEN
      (DISCH_THEN(LABEL_TAC "evf") THEN
  REWRITE_TAC[source_to_flat_compile_exp_def; distinctness "op"] THEN
  REWRITE_TAC[astOp_to_flatOp_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[flat_evaluate_def; GSYM compile_exps_reverse] THEN
  FLATP2AUX_LREWRITE_TAC ["fe1"] [] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "flat_op"; distinctness "op"; injectivity "op"; distinctness "thunk_op"] THEN
  FLATP2AUX_INV_TAC "inv1" THEN
  USE_THEN "s_rel" (FLATP2AUX_LABEL_CONJS ["nn"; "srf"; "scl"; "sff"] o
                    REWRITE_RULE[source_to_flatProof_s_rel_cases]) THEN
  MP_TAC(MATCH_MP FLATP2AUX_dest_thunk_rel (end_itlist CONJ
    [ASSUME `ALL2 (source_to_flatProof_v_rel genv1) vs vs1'`;
     ASSUME `ALL2 (source_to_flatProof_sv_rel genv1) (state_refs (st1:(FFI)state))
               (TL (flat_state_refs (s1_i1:(C,FFI)flat_state)))`;
     ASSUME `~NULL (flat_state_refs (s1_i1:(C,FFI)flat_state))`])) THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["d1"; "d2"; "d3"])) THEN
      (MP_TAC(ISPEC `dest_thunk (REVERSE vs) (state_refs (st1:(FFI)state))` (cases "dest_thunk_ret")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (LABEL_TAC "dt") (DISJ_CASES_THEN2 (LABEL_TAC "dt")
    (X_CHOOSE_THEN `m:thunk_mode` (X_CHOOSE_THEN `tv:v` (LABEL_TAC "dt"))))) THENL
   [USE_THEN "evf" MP_TAC THEN FLATP2AUX_LREWRITE_TAC ["dt"] [] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM o CONJUNCT2) THEN
    USE_THEN "nte" MP_TAC THEN REWRITE_TAC[];
    USE_THEN "evf" MP_TAC THEN FLATP2AUX_LREWRITE_TAC ["dt"] [] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM o CONJUNCT2) THEN
    USE_THEN "nte" MP_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "dt" (fun th -> USE_THEN "d3" (X_CHOOSE_THEN `tv':flat_v`
    (CONJUNCTS_THEN2 (LABEL_TAC "fdt") (LABEL_TAC "tvr")) o C MATCH_MP th)) THEN
  FLATP2AUX_LREWRITE_TAC ["fdt"] [] THEN CASE_REWRITE_TAC[] THEN
  USE_THEN "evf" MP_TAC THEN FLATP2AUX_LREWRITE_TAC ["dt"] [] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `m:thunk_mode` THEN CASE_REWRITE_TAC[]) THENL
      [(DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`; `Rval [tv']:(flat_v list,flat_v)result`;
                        `genv1:global_env`] THEN
  REWRITE_TAC[result_rel_eqns; o_THM; injectivity "result"] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `[tv':flat_v]` THEN FLATP2AUX_LREWRITE_TAC ["tvr"] [ALL2]; ALL_TAC] THEN
  FLATP2AUX_LREWRITE_TAC ["sr1"; "inv1"; "eg1"; "of1"; "sc1"; "sy1"; "sg1"] []);
       (FLATP2AUX_OPTION_CASES_TAC `do_opapp [tv; Conv NONE []]` `ee:v sem_env # exp` "dop" THEN
  CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM o CONJUNCT2) THEN
    USE_THEN "nte" MP_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  FLATP2AUX_PAIR_TAC `ee:v sem_env # exp` `env':v sem_env` `e:exp` "eeq" THEN
  REMOVE_THEN "eeq" SUBST_ALL_TAC THEN CASE_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ev2") THEN
  MP_TAC(ISPECL [`genv1:global_env`; `[tv; Conv NONE []]`; `[tv'; flat_Conv NONE []]`;
    `env':v sem_env`; `e:exp`] do_opapp) THEN
  ANTS_TAC THENL
   [FLATP2AUX_LREWRITE_TAC ["dop"; "tvr"] [ALL2] THEN
    MATCH_MP_TAC(el 2 (CONJUNCTS source_to_flatProof_v_rel_rules)) THEN REWRITE_TAC[ALL2];
    ALL_TAC] THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`comp_map2:source_to_flat_environment`;
    `env_i2:(flat_v)flat_environment`; `locals2:mlstring list`; `t1:mlstring list`;
    `ts2:tra list`] (FLATP2AUX_LABEL_CONJS ["ear2"; "lts2"; "fdop"])) THEN
  REWRITE_TAC[FLATP2AUX_flat_AppUnit] THEN FLATP2AUX_LREWRITE_TAC ["fdop"] [] THEN
  CASE_REWRITE_TAC[] THEN
  USE_THEN "inv1" (CONJUNCTS_THEN2 (LABEL_TAC "clk") (LABEL_TAC "invd") o
                   MATCH_MP invariant_dec_clock) THEN
  USE_THEN "clk" (fun th -> REWRITE_TAC[GSYM th])) THEN
       (ASM_CASES_TAC `state_clock (st1:(FFI)state) = 0` THEN POP_ASSUM(LABEL_TAC "c0") THEN
  FLATP2AUX_LREWRITE_TAC ["c0"] [] THEN CASE_REWRITE_TAC[] THENL
   [USE_THEN "ev2" MP_TAC THEN FLATP2AUX_LREWRITE_TAC ["c0"] [PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`;
      `Rerr (Rabort Rtimeout_error):(flat_v list,flat_v)result`; `genv1:global_env`] THEN
    FLATP2AUX_LREWRITE_TAC ["sr1"] [result_rel_eqns; source_to_flatProof_abort_simps];
    ALL_TAC]) THEN
       (USE_THEN "ev2" (LABEL_TAC "ev3" o REWRITE_RULE[ASSUME `~(state_clock (st1:(FFI)state) = 0)`]) THEN
  USE_THEN "iht" (MP_TAC o SPECL [`vs:v list`; `tv:v`; `st1:(FFI)state`; `env':v sem_env`; `e:exp`]) THEN
  ANTS_TAC THENL
   [FLATP2AUX_LREWRITE_TAC ["ev1"; "dop"; "c0"; "dt"] [getOpClass_def] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "iht'") THEN
  FLATP2AUX_PAIR_TAC `evaluate (dec_clock (st1:(FFI)state)) env' [e]` `st2:(FFI)state`
    `r2:(v list,v)result` "ev4" THEN
  USE_THEN "ev3" MP_TAC THEN FLATP2AUX_LREWRITE_TAC ["ev4"] [] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "ev5")) THEN
       (SUBGOAL_THEN `~(r2 = Rerr (Rabort Rtype_error):(v list,v)result)` (LABEL_TAC "nte2") THENL
   [DISCH_THEN SUBST_ALL_TAC THEN USE_THEN "ev5" MP_TAC THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM o CONJUNCT2) THEN
    USE_THEN "nte" MP_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  FLATP2AUX_IH_TAC "iht'" [("s'", `st2:(FFI)state`); ("r", `r2:(v list,v)result`);
    ("genv", `genv1:global_env`); ("comp_map", `comp_map2:source_to_flat_environment`);
    ("env_i1", `env_i2:(flat_v)flat_environment`);
    ("s_i1", `flat_dec_clock (s1_i1:(C,FFI)flat_state)`); ("locals", `locals2:mlstring list`);
    ("t", `t1:mlstring list`); ("ts", `ts2:tra list`); ("gen", `gen:environment_generation_store`);
    ("idxs", `idxs:next_indices#next_indices#(num#idx_types->bool)`)] THEN
  ANTS_TAC THENL
   [FLATP2AUX_ANTS_TAC THEN
    USE_THEN "eg1" MP_TAC THEN REWRITE_TAC[dec_clock_def; state_INFO.ri_accfupds];
    ALL_TAC] THEN
  REWRITE_TAC FLATP2AUX_compile_exps_clauses THEN
  DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s2_i1:(C,FFI)flat_state`;
    `r2_i1:(flat_v list,flat_v)result`; `genv2:global_env`]
    (FLATP2AUX_LABEL_CONJS ["fe2"; "rr2"; "sr2"; "na2"])) THEN
  FLATP2AUX_LREWRITE_TAC ["fe2"] [] THEN CASE_REWRITE_TAC[] THEN
  FLATP2AUX_RESULT_CASES_TAC `r2:(v list,v)result` `vs2:v list` `err2:(v)error_result`) THENL
       [(USE_THEN "rr2" (X_CHOOSE_THEN `vs2':flat_v list` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      (LABEL_TAC "vr2" o REWRITE_RULE[o_THM])) o MATCH_MP FLATP2AUX_result_rel_Rval) THEN
  CASE_REWRITE_TAC[] THEN
  USE_THEN "na2" (MP_TAC o REWRITE_RULE[source_to_flatProof_abort_simps]) THEN
  REWRITE_TAC[dec_clock_def; state_INFO.ri_accfupds] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["inv2"; "eg2"; "of2"; "sc2"; "sy2"; "sg2"]) THEN
  USE_THEN "ev5" MP_TAC THEN CASE_REWRITE_TAC[] THEN
  FLATP2AUX_OPTION_CASES_TAC `update_thunk (REVERSE vs) (state_refs (st2:(FFI)state)) vs2`
    `refs3:(v store_v)list` "ut" THEN
  CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM o CONJUNCT2) THEN
    USE_THEN "nte" MP_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  USE_THEN "inv2" (LABEL_TAC "sr2'" o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE[invariant_def]) THEN
  USE_THEN "sr2'" (FLATP2AUX_LABEL_CONJS ["nn2"; "srf2"; "scl2"; "sff2"] o
                   REWRITE_RULE[source_to_flatProof_s_rel_cases]) THEN
  MP_TAC(ISPECL [`genv2:global_env`; `vs:v list`; `vs1':flat_v list`;
    `state_refs (st2:(FFI)state)`; `flat_state_refs (s2_i1:(C,FFI)flat_state)`;
    `vs2:v list`; `vs2':flat_v list`; `refs3:(v store_v)list`] FLATP2AUX_update_thunk_rel) THEN
  ANTS_TAC THENL
   [FLATP2AUX_LREWRITE_TAC ["vr2"; "srf2"; "nn2"; "ut"] [] THEN
    MATCH_MP_TAC FLATP2AUX_ALL2_v_rel_weak THEN EXISTS_TAC `genv1:global_env` THEN
    FLATP2AUX_LREWRITE_TAC ["vr1"; "sc2"; "sy2"; "sg2"] [];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `refs3':(flat_v store_v)list`
    (FLATP2AUX_LABEL_CONJS ["fut"; "rr3"; "nn3"; "tk3"])) THEN
  FLATP2AUX_LREWRITE_TAC ["fut"] [] THEN CASE_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`flat_state_refs_fupd (K refs3') (s2_i1:(C,FFI)flat_state)`;
    `Rval vs2':(flat_v list,flat_v)result`; `genv2:global_env`] THEN
  SUBGOAL_THEN `source_to_flatProof_s_rel genv2 (state_refs_fupd (K refs3) (st2:(FFI)state))
                  (flat_state_refs_fupd (K refs3') (s2_i1:(C,FFI)flat_state))` (LABEL_TAC "sr3") THENL
   [REWRITE_TAC[source_to_flatProof_s_rel_cases; state_INFO.ri_accfupds;
                flat_state_INFO.ri_accfupds; K_THM] THEN
    FLATP2AUX_LREWRITE_TAC ["nn3"; "rr3"; "scl2"; "sff2"] [];
    ALL_TAC] THEN
  FLATP2AUX_LREWRITE_TAC ["sr3"; "rr2"] [] THEN
  REWRITE_TAC[source_to_flatProof_abort_simps; state_INFO.ri_accfupds] THEN
  FLATP2AUX_LREWRITE_TAC ["eg2"] [] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FLATP2AUX_invariant_refs THEN FLATP2AUX_LREWRITE_TAC ["inv2"; "sr3"; "tk3"] [];
    ALL_TAC] THEN
  FLATP2AUX_TRANS_TAC `state_eval_state (st1:(FFI)state)` `genv1:global_env`);
        (USE_THEN "rr2" (X_CHOOSE_THEN `e2':(flat_v)error_result` SUBST_ALL_TAC o
                  MATCH_MP FLATP2AUX_result_rel_Rerr) THEN
  CASE_REWRITE_TAC[] THEN
  USE_THEN "ev5" MP_TAC THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
  MAP_EVERY EXISTS_TAC [`s2_i1:(C,FFI)flat_state`; `Rerr e2':(flat_v list,flat_v)result`;
                        `genv2:global_env`] THEN
  FLATP2AUX_LREWRITE_TAC ["rr2"; "sr2"] [] THEN
  DISCH_THEN(fun th -> USE_THEN "na2" (MP_TAC o C MP th)) THEN
  REWRITE_TAC[dec_clock_def; state_INFO.ri_accfupds] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["inv2"; "eg2"; "of2"; "sc2"; "sy2"; "sg2"]) THEN
  FLATP2AUX_LREWRITE_TAC ["inv2"; "eg2"] [] THEN
  FLATP2AUX_TRANS_TAC `state_eval_state (st1:(FFI)state)` `genv1:global_env`)]];
      FLATP2AUX_ISPECL_TAC ["interp"; "g"; "gen"; "genv1"; "idxs"; "st"; "env"; "op"; "es";
        "st1"; "vs"; "env_i1"; "s_i1"; "t";
        "source_to_flat_environment_v_fupd (K (bind_locals ts locals (source_to_flat_environment_v comp_map))) comp_map";
        "s1_i1"; "vs1'"; "s'"; "r"] FLATP2AUX_App_simple THEN
      ANTS_TAC THENL
       [FLATP2AUX_LREWRITE_TAC ["ev1"; "ev"; "nte"; "cls"; "fe1"; "vr1"; "inv1"] [] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(FLATP2AUX_CHOOSE_THEN [`s2_i1:(C,FFI)flat_state`;
        `r2_i1:(flat_v list,flat_v)result`] (FLATP2AUX_LABEL_CONJS ["fe2"; "rr2"; "sr2"; "inv2"; "es2"])) THEN
      MAP_EVERY EXISTS_TAC [`s2_i1:(C,FFI)flat_state`; `r2_i1:(flat_v list,flat_v)result`;
                            `genv1:global_env`] THEN
      FLATP2AUX_LREWRITE_TAC ["fe2"; "rr2"; "sr2"; "inv2"; "es2"; "eg1"; "of1"; "sc1"; "sy1"; "sg1"] []]);
    USE_THEN "rr1" (X_CHOOSE_THEN `e1':(flat_v)error_result` SUBST_ALL_TAC o
                    MATCH_MP FLATP2AUX_result_rel_Rerr) THEN
    FLATP2AUX_ISPECL_TAC ["st"; "env"; "op"; "es"; "st1"; "err1"; "env_i1"; "s_i1"; "t";
      "source_to_flat_environment_v_fupd (K (bind_locals ts locals (source_to_flat_environment_v comp_map))) comp_map";
      "s1_i1"; "e1'"] FLATP2AUX_App_err THEN
    FLATP2AUX_LREWRITE_TAC ["ev1"; "fe1"] [] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "eva") (LABEL_TAC "fea")) THEN
    USE_THEN "ev" MP_TAC THEN FLATP2AUX_LREWRITE_TAC ["eva"] [PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC [`s1_i1:(C,FFI)flat_state`; `Rerr e1':(flat_v list,flat_v)result`;
                          `genv1:global_env`] THEN
    FLATP2AUX_LREWRITE_TAC ["fea"; "rr1"; "sr1"; "na1"] []]);;

(* HOL4 lines 3747-5231: compile_correct, the main simulation (Theorem at   *)
(* HOL4 line 3747, proved by the suspend/Resume blocks of HOL4 lines        *)
(* 3836-5230, Finalise at line 5231); interp and g are free in HOL4 (here *)
(* quantified first)                                                         *)
let source_to_flatProof_compile_correct = prove
 (`!interp g.
     (!(s:(FFI)state) env es s' r genv comp_map env_i1 (s_i1:(C,FFI)flat_state) es_i1
      locals t ts gen idxs.
      evaluate s env es = (s', r) /\
      invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv idxs
        s s_i1 /\
      env_all_rel genv comp_map env env_i1 locals /\
      LENGTH ts = LENGTH locals /\
      env_gen_rel gen (state_eval_state s) /\
      ~(r = Rerr (Rabort Rtype_error)) /\
      es_i1 = source_to_flat_compile_exps t
                (source_to_flat_environment_v_fupd
                   (K (bind_locals ts locals (source_to_flat_environment_v comp_map)))
                   comp_map) es
      ==> ?s'_i1 r_i1 genv'.
            flat_evaluate env_i1 s_i1 es_i1 = (s'_i1, r_i1) /\
            source_to_flatProof_result_rel (ALL2 o source_to_flatProof_v_rel) genv' r r_i1 /\
            source_to_flatProof_s_rel genv' s' s'_i1 /\
            (~source_to_flatProof_abort r
             ==> invariant interp g gen genv' idxs s' s'_i1 /\
                 env_gen_rel gen (state_eval_state s') /\
                 orac_forward_rel interp (state_eval_state s) (state_eval_state s') /\
                 global_env_c genv SUBMAP global_env_c genv' /\
                 global_env_tys genv SUBMAP global_env_tys genv' /\
                 subglobals (global_env_v genv) (global_env_v genv'))) /\
   (!(s:(FFI)state) env v pes err_v genv comp_map s' r env_i1 (s_i1:(C,FFI)flat_state)
      v_i1 pes_i1 err_v_i1 locals t ts gen idxs.
      evaluate_match s env v pes err_v = (s', r) /\
      invariant interp g gen genv idxs s s_i1 /\
      env_all_rel genv comp_map env env_i1 locals /\
      source_to_flatProof_v_rel genv v v_i1 /\
      LENGTH ts = LENGTH locals /\
      env_gen_rel gen (state_eval_state s) /\
      ~(r = Rerr (Rabort Rtype_error)) /\
      pes_i1 = compile_pes t
                 (source_to_flat_environment_v_fupd
                    (K (bind_locals ts locals (source_to_flat_environment_v comp_map)))
                    comp_map) pes /\
      ~(pmatch_rows pes_i1 s_i1 v_i1 = Match_type_error) /\
      source_to_flatProof_v_rel genv err_v err_v_i1
      ==> ?s'_i1 r_i1 genv'.
            flat_evaluate_match env_i1 s_i1 v_i1 pes_i1 err_v_i1 = (s'_i1, r_i1) /\
            source_to_flatProof_result_rel (ALL2 o source_to_flatProof_v_rel) genv' r r_i1 /\
            source_to_flatProof_s_rel genv' s' s'_i1 /\
            (~source_to_flatProof_abort r
             ==> invariant interp g gen genv' idxs s' s'_i1 /\
                 env_gen_rel gen (state_eval_state s') /\
                 orac_forward_rel interp (state_eval_state s) (state_eval_state s') /\
                 global_env_c genv SUBMAP global_env_c genv' /\
                 global_env_tys genv SUBMAP global_env_tys genv' /\
                 subglobals (global_env_v genv) (global_env_v genv'))) /\
   (!(s:(FFI)state) env ds s' r path t idx end_idx os comp_map
      (s_i1:(C,FFI)flat_state) idx' comp_map' ds_i1 t' genv gen gen'.
      evaluate_decs s env ds = (s', r) /\
      invariant interp g gen genv (idx, end_idx, os) s s_i1 /\
      source_to_flat_compile_decs path t idx comp_map gen ds =
        (t', idx', comp_map', gen', ds_i1) /\
      global_env_inv genv comp_map {} env /\
      ~(r = Rerr (Rabort Rtype_error)) /\
      env_gen_rel gen (state_eval_state s) /\
      env_gen_future_rel interp gen' (state_eval_state s) /\
      idx_prev idx' end_idx
      ==> ?(s1_i1:(C,FFI)flat_state) genv' r_i1.
            flat_evaluate_decs s_i1 ds_i1 = (s1_i1, r_i1) /\
            source_to_flatProof_s_rel genv' s' s1_i1 /\
            (~source_to_flatProof_abort r
             ==> invariant interp g gen' genv' (idx', end_idx, os) s' s1_i1 /\
                 orac_forward_rel interp (state_eval_state s) (state_eval_state s') /\
                 global_env_c genv SUBMAP global_env_c genv' /\
                 global_env_tys genv SUBMAP global_env_tys genv' /\
                 subglobals (global_env_v genv) (global_env_v genv')) /\
            (!env'. r = Rval env'
                    ==> r_i1 = NONE /\ env_domain_eq comp_map' env' /\
                        env_gen_rel gen' (state_eval_state s') /\
                        global_env_inv genv' comp_map' {} env') /\
            (!err. r = Rerr err
                   ==> ?err_i1. r_i1 = SOME err_i1 /\
                                source_to_flatProof_result_rel (\a b (c:A). T) genv'
                                  (Rerr err:((v)sem_env,v)result) (Rerr err_i1)))`,
REPEAT GEN_TAC THEN MATCH_MP_TAC full_evaluate_ind THEN REPEAT CONJ_TAC THEN
  FIRST (map ACCEPT_TAC [FLATP2AUX_cc_nil; FLATP2AUX_cc_seq; FLATP2AUX_cc_Lit; FLATP2AUX_cc_Raise;
    FLATP2AUX_cc_Handle; FLATP2AUX_cc_Con; FLATP2AUX_cc_Var; FLATP2AUX_cc_Fun; FLATP2AUX_cc_App;
    FLATP2AUX_cc_Log; FLATP2AUX_cc_If; FLATP2AUX_cc_Mat; FLATP2AUX_cc_Let; FLATP2AUX_cc_Letrec;
    FLATP2AUX_cc_Tannot; FLATP2AUX_cc_Lannot; FLATP2AUX_cc_match_nil; FLATP2AUX_cc_pattern;
    FLATP2AUX_cc_empty_decs; FLATP2AUX_cc_cons_decs; FLATP2AUX_cc_Dlet; FLATP2AUX_cc_Dletrec;
    FLATP2AUX_cc_Dtype; FLATP2AUX_cc_Dtabbrev; FLATP2AUX_cc_Denv; FLATP2AUX_cc_Dexn;
    FLATP2AUX_cc_Dmod; FLATP2AUX_cc_Dlocal]));;

(* HOL4 line 5233 *)
let init_eval_state_ok_def = sem1aux_def
  `(init_eval_state_ok (NONE:(eval_state)option) <=> T) /\
   (init_eval_state_ok (SOME (EvalDecs _)) <=> F) /\
   (init_eval_state_ok (SOME (EvalOracle s)) <=>
      eval_oracle_state_generation s = 0 /\ eval_oracle_state_envs s = [[]])`;;

(* HOL4 line 5240 *)
let init_genv_ty_els_def = cake_def
  `init_genv_ty_els =
     [(bool_id, [(false_tag, 0, TypeStamp (implode "False") bool_type_num);
                 (true_tag, 0, TypeStamp (implode "True") bool_type_num)]);
      (list_id, REVERSE [(cons_tag, 2, TypeStamp (implode "::") list_type_num);
                         (nil_tag, 0, TypeStamp (implode "[]") list_type_num)])]`;;

(* HOL4 line 5248 *)
let init_genv_els_def = cake_def
  `init_genv_els =
     APPEND (FLAT (MAP (\(id, xs). MAP (\(tag, arity, stamp). (((tag, SOME id), arity), stamp))
                                     xs)
                       init_genv_ty_els))
       [(((div_tag, NONE), 0), div_stamp);
        (((chr_tag, NONE), 0), chr_stamp);
        (((subscript_tag, NONE), 0), subscript_stamp);
        (((bind_tag, NONE), 0), bind_stamp)]`;;

(* HOL4 line 5258 *)
let init_genv_def = cake_def
  `init_genv =
     global_env_REC [] (FEMPTY |++ init_genv_els)
       (FEMPTY |++ MAP (I ## MAP (I ## FST)) init_genv_ty_els)`;;

(* local helpers for init_genv_ok, init_genv_tys_ok: init_genv_els computed, *)
(* and the lookups in the constructor map of init_genv *)
let FLATP2AUX_init_genv_els_eval = prove
 (`init_genv_els =
     [(((0, SOME 0), 0), TypeStamp (implode "False") 0);
      (((1, SOME 0), 0), TypeStamp (implode "True") 0);
      (((0, SOME 1), 0), TypeStamp (implode "[]") 1);
      (((0, SOME 1), 2), TypeStamp (implode "::") 1);
      (((2, NONE), 0), ExnStamp 2);
      (((1, NONE), 0), ExnStamp 1);
      (((3, NONE), 0), ExnStamp 3);
      (((0, NONE), 0), ExnStamp 0)]`,
  REWRITE_TAC[init_genv_els_def; init_genv_ty_els_def; REVERSE; APPEND; MAP; FLAT] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[MAP; FLAT; APPEND] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[APPEND; bool_id_def; list_id_def; true_tag_def; false_tag_def; cons_tag_def;
    nil_tag_def; div_tag_def; chr_tag_def; subscript_tag_def; bind_tag_def; div_stamp_def;
    chr_stamp_def; subscript_stamp_def; bind_stamp_def; bool_type_num_def;
    list_type_num_def]);;

let FLATP2AUX_init_genv_c_lookup = prove
 (`!k v. FLOOKUP (global_env_c init_genv) k = SOME v <=> MEM (k,v) init_genv_els`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[init_genv_def; global_env_INFO.ri_accessors; flookup_fupdate_list;
              FLOOKUP_EMPTY] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (REVERSE init_genv_els))` ASSUME_TAC THENL
   [REWRITE_TAC[FLATP2AUX_init_genv_els_eval; REVERSE; APPEND; MAP; ALL_DISTINCT; MEM;
      PAIR_EQ; option_INJ; option_DISTINCT; ARITH_EQ]; ALL_TAC] THEN
  MP_TAC(ISPEC `ALOOKUP (REVERSE init_genv_els) k` (cases "option")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN
  ASM_MESON_TAC[ALOOKUP_MEM; ALOOKUP_ALL_DISTINCT_MEM; MEM_REVERSE; option_INJ;
    option_DISTINCT]);;

(* HOL4 line 5263 *)
let init_genv_ok = prove
 (`genv_c_ok (global_env_c init_genv)`,
  REWRITE_TAC[genv_c_ok_def; has_bools_def; has_exns_def; has_lists_def;
              FLATP2AUX_init_genv_c_lookup; FLATP2AUX_init_genv_els_eval] THEN
  REWRITE_TAC[MEM; PAIR_EQ; true_tag_def; false_tag_def; bool_id_def; bool_type_num_def;
    cons_tag_def; nil_tag_def; list_id_def; list_type_num_def; div_tag_def; chr_tag_def;
    subscript_tag_def; bind_tag_def; div_stamp_def; chr_stamp_def; subscript_stamp_def;
    bind_stamp_def; ARITH_EQ; option_INJ; option_DISTINCT] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "stamp"; distinctness "stamp";
    GSYM (distinctness "stamp"); injectivity "mlstring"; ARITH_EQ]) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV STRING_EQ_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[ctor_same_type_def; same_type_def; flat_ctor_same_type_def; PAIR_EQ;
    option_INJ; option_DISTINCT; ARITH_EQ] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[same_type_def; ARITH_EQ; option_INJ]);;

(* HOL4 line 5274 *)
let init_genv_tys_ok = prove
 (`genv_c_tys_ok (global_env_c init_genv) (global_env_tys init_genv)`,
  REWRITE_TAC[genv_c_tys_ok_def; init_genv_def; global_env_INFO.ri_accessors;
    FDOM_FUPDATE_LIST; FDOM_FEMPTY] THEN
  REWRITE_TAC[FLATP2AUX_init_genv_els_eval; init_genv_ty_els_def; MAP; REVERSE; APPEND;
    FST; UNION_EMPTY; IN_SET_OF_LIST; MEM; PAIR_EQ; option_INJ; option_DISTINCT] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[flookup_fupdate_list; FLOOKUP_EMPTY; REVERSE; APPEND; MAP; PAIR_MAP_THM; I_THM;
    FST; ALOOKUP_THM; bool_id_def; list_id_def; ARITH_EQ] THEN
  REWRITE_TAC[option_CASE; option_INJ; UNWIND_THM1; MEM; PAIR_EQ; true_tag_def; false_tag_def;
    cons_tag_def; nil_tag_def; ARITH_EQ]);;

(* HOL4 line 5280 *)
let init_genv_next = cake_def
  `init_genv_next =
     next_indices_REC 0
       (SUC (MAX_LIST (MAP (\v. match SND v with TypeStamp _ i -> i | _ -> 0)
                         init_genv_els)))
       (SUC (MAX_LIST (MAP (\v. match SND v with ExnStamp i -> i | _ -> 0)
                         init_genv_els)))`;;

(* HOL4 line 5288 *)
let init_global_env_inv_def = cake_def
  `init_global_env_inv genv comp_map (env:(v)sem_env) <=>
     sem_env_v env = nsEmpty /\
     (match sem_env_c env with
        Bind ns ms ->
          ms = [] /\
          ALL (\(x, (arity, stamp)).
                 match nsLookup (source_to_flat_environment_c comp_map) (Short x) with
                   NONE -> F
                 | SOME (cn, ty_gp) ->
                     FLOOKUP (global_env_c genv) ((cn, OPTION_MAP FST ty_gp), arity) =
                       SOME stamp /\
                     (match ty_gp with
                        NONE -> T
                      | SOME (ty_id, ctors) ->
                          FLOOKUP (global_env_tys genv) ty_id = SOME ctors))
              ns)`;;

(* HOL4 line 5301 *)
let init_global_env_inv_imp = prove
 (`!genv comp_map env.
     init_global_env_inv genv comp_map env ==> global_env_inv genv comp_map {} env`,
  REPEAT GEN_TAC THEN REWRITE_TAC[init_global_env_inv_def] THEN
  MP_TAC(ISPEC `sem_env_c (env:v sem_env)` (CONJUNCT1 (cases "namespace"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ns:(mlstring#(num#stamp))list`
    (X_CHOOSE_THEN `ms:(mlstring#(mlstring,mlstring,num#stamp)namespace)list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST (mapfilter MATCH_MP_TAC (CONJUNCTS source_to_flatProof_v_rel_rules)) THEN
  ASM_REWRITE_TAC[nsEmpty_def; NOT_IN_EMPTY; IMAGE_CLAUSES] THEN CONJ_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPEC `x:(mlstring,mlstring)id` (cases "id")) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[nsLookup_def; ALOOKUP_THM; option_DISTINCT] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_DISTINCT];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `x:(mlstring,mlstring)id` (cases "id")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `n:mlstring` SUBST1_TAC)
    (X_CHOOSE_THEN `m:mlstring` (X_CHOOSE_THEN `i:(mlstring,mlstring)id` SUBST1_TAC))) THEN
  REWRITE_TAC[nsLookup_def; ALOOKUP_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP ALOOKUP_MEM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(n:mlstring, (arity:num, stamp:stamp))` o
    GEN_REWRITE_RULE I [GSYM ALL_MEM] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "ALL"
                     with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  (fun gl -> let tm = FLATP2AUX_PARSE_IN gl
                 "nsLookup (source_to_flat_environment_c comp_map) (Short n)" in
             SPEC_TAC(tm, mk_var("lk", type_of tm)) gl) THEN
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ; PAIR_EQ] THEN REPEAT GEN_TAC THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`p1:num`; `NONE:(num#(num#num)list)option`] THEN
  ASM_REWRITE_TAC[option_DISTINCT];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`p1:num`; `SOME (p1':num, p2:(num#num)list)`] THEN
  ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 5318 *)
let precondition1_def = cake_def
  `precondition1 (interp:(v->(source_to_flat_config#C)option)option) g (s1:(FFI)state)
                 env1 conf (eval_conf:(C)install_config) prog <=>
     src_orac_step_invs interp g (state_eval_state s1) /\
     orac_rel interp g (state_eval_state s1) eval_conf /\
     (match src_orac_next_cfg interp (state_eval_state s1) with
        NONE -> T
      | SOME cfg -> cfg = FST (source_to_flat_compile_prog conf prog)) /\
     next_indices_vidx (source_to_flat_config_next conf) = 0 /\
     state_refs s1 = [] /\
     init_global_env_inv init_genv (source_to_flat_config_mod_env conf) env1 /\
     init_eval_state_ok (state_eval_state s1) /\
     idx_prev init_genv_next (source_to_flat_config_next conf) /\
     ALL (\(x, stamp). match stamp with
                         TypeStamp cn t -> t < state_next_type_stamp s1
                       | ExnStamp cn -> cn < state_next_exn_stamp s1)
       init_genv_els /\
     source_to_flat_config_envs conf = source_to_flat_config_envs empty_config`;;

(* HOL4 line 5335 *)
let precondition1_change_clock = prove
 (`!interp g s1 env1 conf eval_conf prog k.
     precondition1 (interp:(v->(source_to_flat_config#C)option)option) g (s1:(FFI)state)
     env1 conf (eval_conf:(C)install_config) prog
   ==> precondition1 interp g (state_clock_fupd (K k) s1) env1 conf eval_conf prog`,
  REPEAT GEN_TAC THEN REWRITE_TAC[precondition1_def; state_INFO.ri_accfupds]);;

(* HOL4 line 5342 *)
let idx_block_union_final = prove
 (`!idx idx'.
     idx_prev idx idx'
   ==> idx_block idx idx' UNION idx_final_block idx' = idx_final_block idx`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[idx_prev_def; idx_block_def; idx_final_block_def; EXTENSION; IN_UNION;
              IN_ELIM_THM; FORALL_PAIR_THM; PAIR_EQ] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN
  CASES_ON `p2:idx_types` THEN REWRITE_TAC[distinctness "idx_types"] THEN
  SIMP_NOASM[] THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;

(* HOL4 line 5350 *)
let precondition_stamp_helper = prove
 (CASE_TERM `!type_stamp exn_stamp.
     ALL (\(x, stamp). match stamp with
                       TypeStamp cn t -> t < type_stamp
                     | ExnStamp cn -> cn < exn_stamp)
     init_genv_els
   ==> (!cn t. t >= type_stamp ==> ~(TypeStamp cn t IN FRANGE (global_env_c init_genv))) /\
       (!cn. cn >= exn_stamp ==> ~(ExnStamp cn IN FRANGE (global_env_c init_genv)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_TAC THEN
  REWRITE_TAC[FRANGE_FLOOKUP; FLATP2AUX_init_genv_c_lookup; GE; NOT_EXISTS_THM] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `k:(num#num option)#num` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun mem -> FIRST_X_ASSUM(fun all -> MP_TAC(MATCH_MP all mem))) THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN CASE_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* local helpers for invariant_begin_alloc_blanks: init_genv_next computed, the *)
(* allocated indices of the initial global env, the initial disjointness, and *)
(* the counters of compile_prog *)
let FLATP2AUX_init_genv_next_eval = prove
 (`init_genv_next = next_indices_REC 0 2 4`,
  REWRITE_TAC[init_genv_next; FLATP2AUX_init_genv_els_eval; MAP; SND] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[MAX_LIST; MAX] THEN CONV_TAC NUM_REDUCE_CONV);;

let FLATP2AUX_EL_init_globs = prove
 (`!i n (v:flat_v).
     i < SUC n /\ ~(EL i (CONS (SOME v) (REPLICATE n NONE)) = NONE) ==> i = 0`,
  INDUCT_TAC THEN REWRITE_TAC[EL; TL; NOT_SUC; LT_SUC] THEN
  MESON_TAC[EL_REPLICATE]);;

let FLATP2AUX_genv_allocated_init = prove
 (`!(v:flat_v) n x.
     x IN genv_allocated_idxs
            (global_env_v_fupd (K (CONS (SOME v) (REPLICATE n NONE))) init_genv)
     ==> x = (0, Idx_Var) \/ (?i. i < 2 /\ x = (i, Idx_Type)) \/
         (?i. i < 4 /\ x = (i, Idx_Exn))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[genv_allocated_idxs_def; global_env_INFO.ri_accfupds; K_THM; IN_UNION;
              IN_ELIM_THM] THEN
  REWRITE_TAC[init_genv_def; global_env_INFO.ri_accessors; FDOM_FUPDATE_LIST; FDOM_FEMPTY;
    UNION_EMPTY; IN_SET_OF_LIST; FLATP2AUX_init_genv_els_eval; init_genv_ty_els_def; MAP;
    FST; PAIR_MAP_THM; I_THM; MEM; PAIR_EQ; option_INJ; option_DISTINCT; bool_id_def;
    list_id_def; LENGTH; LENGTH_REPLICATE] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[PAIR_EQ; distinctness "idx_types"] THEN
  FIRST [MATCH_MP_TAC FLATP2AUX_EL_init_globs THEN ASM_MESON_TAC[];
         MESON_TAC[ARITH_RULE `0 < 2 /\ 1 < 2 /\ 0 < 4 /\ 1 < 4 /\ 2 < 4 /\ 3 < 4`]]);;

let FLATP2AUX_init_disjoint = prove
 (`!a b (v:flat_v) n.
     1 <= next_indices_vidx b /\ 2 <= next_indices_tidx a /\ 4 <= next_indices_eidx a /\
     next_indices_tidx a <= next_indices_tidx b /\ next_indices_eidx a <= next_indices_eidx b
     ==> ALL_DISJOINT [idx_block (next_indices_vidx_fupd (K 1) a) b; idx_final_block b; {};
                       genv_allocated_idxs (global_env_v_fupd
                         (K (CONS (SOME v) (REPLICATE n NONE))) init_genv)]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[FLATP1AUX_ALL_DISJOINT_CONS; FLATP1AUX_ALL_DISJOINT_NIL; ALL; DISJOINT_EMPTY] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; FORALL_PAIR_THM] THEN
  REPEAT CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`i:num`; `ty:idx_types`] THEN STRIP_TAC THEN
  TRY(FIRST_X_ASSUM(MP_TAC o MATCH_MP FLATP2AUX_genv_allocated_init)) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(rator(rator(concl th)))) = "IN" with Failure _ -> false))) THEN
  REWRITE_TAC[idx_block_def; idx_final_block_def; IN_UNION; IN_ELIM_THM; PAIR_EQ;
    next_indices_INFO.ri_accfupds; K_THM] THEN
  SIMP_NOASM[] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  FS[distinctness "idx_types"] THEN ASM_ARITH_TAC);;

let FLATP2AUX_compile_prog_cfg = prove
 (`!c p c' p'.
     source_to_flat_compile_prog c p = (c', p')
     ==> idx_prev (next_indices_vidx_fupd
                     (K (next_indices_vidx (source_to_flat_config_next c) + 1))
                     (source_to_flat_config_next c))
                  (source_to_flat_config_next c') /\
         environment_store_next (source_to_flat_config_envs c') =
           environment_store_next (source_to_flat_config_envs c) + 1 /\
         (env_store_inv (source_to_flat_config_envs c)
          ==> env_store_inv (source_to_flat_config_envs c'))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[source_to_flat_compile_prog_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[source_to_flat_config_INFO.ri_accfupds; K_THM;
              environment_store_INFO.ri_accessors] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[compile_decs_idx_prev]; ALL_TAC] THEN
  REWRITE_TAC[env_store_inv_def; environment_store_INFO.ri_accessors; domain_insert] THEN
  REWRITE_TAC[INSERT_SUBSET; count_DEF; IN_ELIM_THM; SUBSET] THEN
  MESON_TAC[ARITH_RULE `m < n ==> m < n + 1`; ARITH_RULE `n < n + 1`]);;

(* HOL4 line 5365 *)
let invariant_begin_alloc_blanks = prove
 (`!interp g s1 env1 cfg eval_conf prog cfg' init_globs.
     precondition1 (interp:(v->(source_to_flat_config#C)option)option) g (s1:(FFI)state)
     env1 cfg (eval_conf:(C)install_config) prog /\
   cfg' = FST (source_to_flat_compile_prog cfg prog) /\
   init_globs = CONS (SOME (flat_Loc T 0))
                  (REPLICATE (next_indices_vidx (source_to_flat_config_next cfg') - 1) NONE)
   ==> invariant interp g
         (environment_generation_store_REC 0
            (environment_store_next (source_to_flat_config_envs cfg)) LN)
         (global_env_v_fupd (K init_globs) init_genv)
         (next_indices_vidx_fupd (K 1) (source_to_flat_config_next cfg),
          source_to_flat_config_next cfg', {})
         s1
         (flat_state_refs_fupd (K [Refv (flat_Conv NONE [])])
            (flat_state_globals_fupd (K init_globs)
               (flat_initial_state (state_ffi s1) (state_clock s1) eval_conf)))`,
  REPEAT GEN_TAC THEN
  FLATP2AUX_PAIR_TAC `source_to_flat_compile_prog cfg prog` `c1:source_to_flat_config`
    `p1:flat_exp list` "cp" THEN
  FLATP2AUX_LREWRITE_TAC ["cp"] [FST] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cfg'") SUBST_ALL_TAC)) THEN
  REMOVE_THEN "cfg'" SUBST_ALL_TAC THEN
  REWRITE_TAC[precondition1_def] THEN FLATP2AUX_LREWRITE_TAC ["cp"] [FST] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["step"; "orac"; "next_cfg"; "vidx0"; "refs0"; "genv_inv";
    "es_ok"; "idx_prev0"; "stamps"; "envs0"]) THEN
  USE_THEN "cp" (MP_TAC o MATCH_MP FLATP2AUX_compile_prog_cfg) THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["prev1"; "envs_next1"; "envs_inv1"]) THEN
  SUBGOAL_THEN `1 <= next_indices_vidx (source_to_flat_config_next c1) /\
                2 <= next_indices_tidx (source_to_flat_config_next cfg) /\
                4 <= next_indices_eidx (source_to_flat_config_next cfg) /\
                next_indices_tidx (source_to_flat_config_next cfg) <=
                  next_indices_tidx (source_to_flat_config_next c1) /\
                next_indices_eidx (source_to_flat_config_next cfg) <=
                  next_indices_eidx (source_to_flat_config_next c1)`
    (FLATP2AUX_LABEL_CONJS ["v1"; "t2"; "e4"; "t12"; "e12"]) THENL
   [USE_THEN "idx_prev0" MP_TAC THEN USE_THEN "prev1" MP_TAC THEN
    REWRITE_TAC[idx_prev_def; FLATP2AUX_init_genv_next_eval; next_indices_INFO.ri_accessors;
      next_indices_INFO.ri_accfupds; K_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `env_store_inv (source_to_flat_config_envs c1) /\
                environment_store_next (source_to_flat_config_envs c1) = 1`
    (FLATP2AUX_LABEL_CONJS ["inv1"; "next1"]) THENL
   [CONJ_TAC THENL
     [REMOVE_THEN "envs_inv1" MATCH_MP_TAC THEN USE_THEN "envs0" SUBST1_TAC THEN
      REWRITE_TAC[env_store_inv_def; empty_config_def; source_to_flat_config_INFO.ri_accessors;
        environment_store_INFO.ri_accessors; domain_def; EMPTY_SUBSET];
      USE_THEN "envs_next1" SUBST1_TAC THEN USE_THEN "envs0" SUBST1_TAC THEN
      REWRITE_TAC[empty_config_def; source_to_flat_config_INFO.ri_accessors;
        environment_store_INFO.ri_accessors] THEN ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[invariant_def; global_env_INFO.ri_accfupds; K_THM; flat_state_INFO.ri_accfupds;
    flat_initial_state_def; flat_state_INFO.ri_accessors] THEN
  REWRITE_TAC[init_genv_ok; init_genv_tys_ok] THEN
  REPEAT CONJ_TAC THENL
   [(* s_rel *)
    REWRITE_TAC[source_to_flatProof_s_rel_cases; flat_state_INFO.ri_accfupds;
      flat_state_INFO.ri_accessors; K_THM; NULL; TL] THEN
    FLATP2AUX_LREWRITE_TAC ["refs0"] [ALL2];
    (* idx_range_rel *)
    REWRITE_TAC[idx_range_rel_def; PAIR_EQ] THEN
    MAP_EVERY EXISTS_TAC [`next_indices_vidx_fupd (K 1) (source_to_flat_config_next cfg)`;
      `source_to_flat_config_next c1`; `source_to_flat_config_next c1`;
      `{}:(num#idx_types)->bool`] THEN
    REWRITE_TAC[idx_prev_refl; global_env_INFO.ri_accfupds; K_THM] THEN
    CONJ_TAC THENL
     [USE_THEN "next_cfg" MP_TAC THEN
      (fun gl -> MP_TAC(ISPEC (FLATP2AUX_PARSE_IN gl
         "src_orac_next_cfg interp (state_eval_state s1)") (cases "option")) gl) THEN
      STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FLATP2AUX_init_disjoint THEN
      FLATP2AUX_LREWRITE_TAC ["v1"; "t2"; "e4"; "t12"; "e12"] [];
      USE_THEN "stamps" (ACCEPT_TAC o MATCH_MP precondition_stamp_helper)];
    (* src_orac_invs *)
    REWRITE_TAC[src_orac_invs_def] THEN USE_THEN "step" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "next_cfg" MP_TAC THEN USE_THEN "es_ok" MP_TAC THEN USE_THEN "step" MP_TAC THEN
      (fun gl -> MP_TAC(ISPEC (FLATP2AUX_PARSE_IN gl "state_eval_state s1") (cases "option")) gl) THEN
      DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `es:eval_state` SUBST1_TAC)) THEN
      REWRITE_TAC[src_orac_env_invs_def; src_orac_gen_inv_def] THEN CASE_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `es:eval_state` (cases "eval_state")) THEN
      DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `d:eval_decs_state` SUBST1_TAC)
        (X_CHOOSE_THEN `os:eval_oracle_state` SUBST1_TAC)) THEN
      REWRITE_TAC[init_eval_state_ok_def] THEN CASE_REWRITE_TAC[] THEN
      DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP step_1) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[LENGTH] THEN CASE_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
      EXISTS_TAC `c1:source_to_flat_config` THEN FLATP2AUX_LREWRITE_TAC ["inv1"; "next1"] [] THEN
      REWRITE_TAC[ONE; LT] THEN REPEAT GEN_TAC THEN
      DISCH_THEN(fun th -> MP_TAC(REWRITE_RULE[CONJUNCT1 th] (CONJUNCT2 th))) THEN
      REWRITE_TAC[EL; HD; LENGTH; LT];
    (* orac_rel *)
    USE_THEN "orac" ACCEPT_TAC;
    (* eval_ref_inv *)
    SIMP_TAC[eval_ref_inv_def; TAKE1; NOT_CONS_NIL; EL; HD] THEN MESON_TAC[];
    (* env_gen_inv *)
    REWRITE_TAC[env_gen_inv_def; environment_generation_store_INFO.ri_accessors; domain_def;
      EMPTY_SUBSET];
    (* fin_idx_match *)
    REWRITE_TAC[fin_idx_match_def; LENGTH; LENGTH_REPLICATE] THEN
    USE_THEN "next_cfg" MP_TAC THEN
    (fun gl -> MP_TAC(ISPEC (FLATP2AUX_PARSE_IN gl
       "src_orac_next_cfg interp (state_eval_state s1)") (cases "option")) gl) THEN
    STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
    TRY (DISCH_THEN SUBST1_TAC) THEN USE_THEN "v1" MP_TAC THEN ARITH_TAC]);;

(* local helpers for compile_prog_correct: the evaluation of the two first *)
(* declarations of compile_prog, and type errors of related results *)
let FLATP2AUX_flat_alloc_env_ref = prove
 (`!(s:(C,FFI)flat_state) rest.
     0 < LENGTH (flat_state_globals s) /\ EL 0 (flat_state_globals s) = NONE
     ==> flat_evaluate_decs s (CONS alloc_env_ref rest) =
         flat_evaluate_decs
           (flat_state_globals_fupd
              (K (LUPDATE (SOME (flat_Loc T (LENGTH (flat_state_refs s)))) 0
                    (flat_state_globals s)))
              (flat_state_refs_fupd
                 (K (APPEND (flat_state_refs s) [Refv (flat_Conv NONE [])])) s))
           rest`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[alloc_env_ref_def] THEN
  FS[flat_evaluate_def; REVERSE; APPEND; flat_do_app_def; list_result_def;
     store_alloc_def; FLATP2AUX_opt_bind_fun; flat_Unitv_def; FLATP2AUX_record_etas;
     flat_state_INFO.ri_accfupds; K_THM; IS_NONE_DEF]);;

let FLATP2AUX_compile_prog_prefix = prove
 (`!(ffi:(FFI)ffi_state) k (ec:(C)install_config) next c rest.
     1 <= next_indices_vidx next - next_indices_vidx (source_to_flat_config_next c)
     ==> flat_evaluate_decs (flat_initial_state ffi k ec)
           (CONS (glob_alloc next c) (CONS alloc_env_ref rest)) =
         flat_evaluate_decs
           (flat_state_refs_fupd (K [Refv (flat_Conv NONE [])])
              (flat_state_globals_fupd
                 (K (CONS (SOME (flat_Loc T 0))
                       (REPLICATE (next_indices_vidx next -
                                   next_indices_vidx (source_to_flat_config_next c) - 1)
                          NONE)))
                 (flat_initial_state ffi k ec)))
           rest`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `n = next_indices_vidx next - next_indices_vidx (source_to_flat_config_next c)` THEN
  DISCH_TAC THEN REWRITE_TAC[FLATP2AUX_flat_glob_alloc] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?m. n = SUC m` (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `n - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[FLATP2AUX_flat_alloc_env_ref; flat_state_INFO.ri_accfupds; K_THM;
    flat_initial_state_def; flat_state_INFO.ri_accessors; APPEND; LENGTH_REPLICATE; REPLICATE;
    EL; HD; LT_0; LENGTH] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[(record_info "flat_state").ri_component_equality; flat_state_INFO.ri_accfupds;
    flat_state_INFO.ri_accessors; K_THM; LUPDATE_def; LENGTH; SUC_SUB1]);;

let FLATP2AUX_result_rel_not_type_error = prove
 (`!f genv err err1.
     source_to_flatProof_result_rel (f:global_env->X->Y->bool) genv
       (Rerr err:(X,v)result) (Rerr err1:(Y,flat_v)result) /\
     ~(err = Rabort Rtype_error)
     ==> ~(err1 = Rabort Rtype_error)`,
  REPEAT GEN_TAC THEN CASES_ON `err:(v)error_result` THEN
  REWRITE_TAC[result_rel_eqns; injectivity "result"] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[injectivity "error_result"]) THEN
  ASM_REWRITE_TAC[distinctness "error_result"; injectivity "error_result"]);;

(* HOL4 line 5421 *)
let compile_prog_correct = prove
 (`!interp g s env cfg eval_conf ds cfg' ds' s' r.
     precondition1 (interp:(v->(source_to_flat_config#C)option)option) g (s:(FFI)state)
     env cfg (eval_conf:(C)install_config) ds /\
   source_to_flat_compile_prog cfg ds = (cfg', ds') /\
   evaluate_decs s env ds = (s', r) /\
   ~(r = Rerr (Rabort Rtype_error))
   ==> ?s_i1 s_i1' genv' r_i1.
         s_i1 = flat_initial_state (state_ffi s) (state_clock s) eval_conf /\
         flat_evaluate_decs s_i1 ds' = (s_i1', r_i1) /\
         source_to_flatProof_s_rel genv' s' s_i1' /\
         (!res. r = Rval res ==> r_i1 = NONE) /\
         (!err. r = Rerr err
                ==> ?err'. r_i1 = SOME err' /\ ~(err' = Rabort Rtype_error) /\
                           source_to_flatProof_result_rel (\a (b:1) (c:1). T) genv'
                             (Rerr err) (Rerr err'))`,
  REPEAT GEN_TAC THEN DISCH_THEN(FLATP2AUX_LABEL_CONJS ["pre"; "cp"; "ev"; "nt"]) THEN
  MP_TAC(ISPECL [`interp:(v->(source_to_flat_config#C)option)option`; `g:dec list->dec list`;
    `s:(FFI)state`; `env:v sem_env`; `cfg:source_to_flat_config`;
    `eval_conf:(C)install_config`; `ds:dec list`; `cfg':source_to_flat_config`;
    `CONS (SOME (flat_Loc T 0))
       (REPLICATE (next_indices_vidx (source_to_flat_config_next cfg') - 1) NONE)`]
    invariant_begin_alloc_blanks) THEN
  USE_THEN "pre" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "cp" (fun th -> REWRITE_TAC[th; FST]) THEN
  DISCH_THEN(LABEL_TAC "inv0") THEN
  FLATP2AUX_WITH_LABELS ["pre"; "cp"] (fun ths ->
    FLATP2AUX_LABEL_CONJS ["step"; "orac"; "next_cfg"; "vidx0"; "refs0"; "genv_inv";
      "es_ok"; "idx_prev0"; "stamps"; "envs0"]
      (REWRITE_RULE[precondition1_def; el 1 ths; FST] (el 0 ths))) THEN
  USE_THEN "cp" MP_TAC THEN
  REWRITE_TAC[source_to_flat_compile_prog_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cfg'") (SUBST_ALL_TAC o SYM)) THEN
  FIRST_X_ASSUM(LABEL_TAC "cd" o check (fun th -> is_eq(concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "source_to_flat_compile_decs"
     with Failure _ -> false))) THEN
  REMOVE_THEN "cfg'" (SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[source_to_flat_config_INFO.ri_accfupds; K_THM]) THEN
  USE_THEN "vidx0" (fun v0 -> REMOVE_THEN "cd" (LABEL_TAC "cd" o REWRITE_RULE[v0; ADD_CLAUSES])) THEN
  USE_THEN "cd" (LABEL_TAC "prev" o MATCH_MP compile_decs_idx_prev) THEN
  USE_THEN "cd" (LABEL_TAC "gen_eq" o MATCH_MP compile_decs_generation) THEN
  MP_TAC(ISPECL [`s:(FFI)state`; `env:v sem_env`; `ds:dec list`; `s':(FFI)state`;
    `r:((v)sem_env,v)result`; `[]:mlstring list`; `1`;
    `next_indices_vidx_fupd (K 1) (source_to_flat_config_next cfg)`; `next:next_indices`;
    `{}:(num#idx_types)->bool`; `source_to_flat_config_mod_env cfg`;
    `flat_state_refs_fupd (K [Refv (flat_Conv NONE [])])
       (flat_state_globals_fupd
         (K (CONS (SOME (flat_Loc T 0))
               (REPLICATE (next_indices_vidx (next:next_indices) - 1) NONE)))
         (flat_initial_state (state_ffi (s:(FFI)state)) (state_clock s)
            (eval_conf:(C)install_config)))`;
    `next:next_indices`; `e:source_to_flat_environment`; `p':flat_exp list`; `n0:num`;
    `global_env_v_fupd (K (CONS (SOME (flat_Loc T 0))
       (REPLICATE (next_indices_vidx (next:next_indices) - 1) NONE))) init_genv`;
    `environment_generation_store_REC 0
       (environment_store_next (source_to_flat_config_envs cfg)) LN`;
    `gen:environment_generation_store`]
    (last (CONJUNCTS (ISPECL [`interp:(v->(source_to_flat_config#C)option)option`;
       `g:dec list->dec list`] source_to_flatProof_compile_correct)))) THEN
  FLATP2AUX_LREWRITE_TAC ["ev"; "inv0"; "cd"; "nt"] [idx_prev_refl] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC global_env_inv_weak THEN EXISTS_TAC `init_genv` THEN
      CONJ_TAC THENL [USE_THEN "genv_inv" (ACCEPT_TAC o MATCH_MP init_global_env_inv_imp);
                      ALL_TAC] THEN
      REWRITE_TAC[global_env_INFO.ri_accfupds; K_THM; SUBMAP_REFL; subglobals_def;
        init_genv_def; global_env_INFO.ri_accessors; LENGTH; LE_0; LT];
      REWRITE_TAC[env_gen_rel_def] THEN USE_THEN "es_ok" MP_TAC THEN
      (fun gl -> MP_TAC(ISPEC (FLATP2AUX_PARSE_IN gl "state_eval_state s")
         (cases "option")) gl) THEN
      DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `es:eval_state` SUBST1_TAC)) THEN
      CASE_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `es:eval_state` (cases "eval_state")) THEN
      DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `d:eval_decs_state` SUBST1_TAC)
        (X_CHOOSE_THEN `os:eval_oracle_state` SUBST1_TAC)) THEN
      REWRITE_TAC[init_eval_state_ok_def] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[environment_generation_store_INFO.ri_accessors; LENGTH; EL; HD] THEN
      USE_THEN "envs0" SUBST1_TAC THEN
      REWRITE_TAC[empty_config_def; source_to_flat_config_INFO.ri_accessors;
        environment_store_INFO.ri_accessors] THEN ARITH_TAC;
      REWRITE_TAC[env_gen_future_rel_def] THEN USE_THEN "next_cfg" MP_TAC THEN
      (fun gl -> MP_TAC(ISPEC (FLATP2AUX_PARSE_IN gl
         "src_orac_next_cfg interp (state_eval_state s)") (cases "option")) gl) THEN
      STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[source_to_flat_config_INFO.ri_accfupds; K_THM;
        environment_store_INFO.ri_accessors] THEN
      USE_THEN "gen_eq" SUBST1_TAC THEN
      REWRITE_TAC[environment_generation_store_INFO.ri_accessors; lookup_insert] THEN
      EXISTS_TAC `environment_generation_store_envs gen` THEN REWRITE_TAC[subspt_refl]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1_i1:(C,FFI)flat_state` (X_CHOOSE_THEN `genv1:global_env`
    (X_CHOOSE_THEN `r_i1:((flat_v)error_result)option`
      (FLATP2AUX_LABEL_CONJS ["fev"; "srel"; "inv1"; "rval"; "rerr"])))) THEN
  MAP_EVERY EXISTS_TAC [`flat_initial_state (state_ffi (s:(FFI)state)) (state_clock s)
                           (eval_conf:(C)install_config)`;
    `s1_i1:(C,FFI)flat_state`; `genv1:global_env`; `r_i1:((flat_v)error_result)option`] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `1 <= next_indices_vidx next - next_indices_vidx (source_to_flat_config_next cfg)`
    (LABEL_TAC "one") THENL
   [USE_THEN "prev" MP_TAC THEN USE_THEN "vidx0" MP_TAC THEN
    REWRITE_TAC[idx_prev_def; next_indices_INFO.ri_accfupds; K_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "one" (fun th -> REWRITE_TAC[MATCH_MP FLATP2AUX_compile_prog_prefix th]) THEN
  USE_THEN "vidx0" (fun th -> REWRITE_TAC[th; SUB_0]) THEN
  FLATP2AUX_LREWRITE_TAC ["fev"; "srel"] [] THEN
  CONJ_TAC THENL [USE_THEN "rval" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  X_GEN_TAC `err:(v)error_result` THEN DISCH_TAC THEN
  USE_THEN "rerr" (fun th -> FIRST_ASSUM(fun eq -> MP_TAC(MATCH_MP th eq))) THEN
  DISCH_THEN(X_CHOOSE_THEN `err1:(flat_v)error_result` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `err1:(flat_v)error_result` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> MATCH_MP_TAC (MATCH_MP
      (REWRITE_RULE[IMP_CONJ] FLATP2AUX_result_rel_not_type_error) th)) THEN
    FIRST_ASSUM(fun eq -> if is_eq(concl eq) && lhs(concl eq) = `r:((v)sem_env,v)result`
      then USE_THEN "nt" (MP_TAC o REWRITE_RULE[eq; injectivity "result"]) else NO_TAC) THEN
    REWRITE_TAC[];
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP FLATP2AUX_result_rel_Rerr_f)]);;

(* HOL4 line 5479 *)
let SND_eq = prove
 (`!x y.
     SND (x:A#B) = y <=> ?a. x = (a,y)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

(* local helper for compile_prog_semantics: compile_prog_correct for each *)
(* clock, stated on the ffi states and the aborts of both sides *)
let FLATP2AUX_sem_clock = prove
 (`!interp g s1 env1 conf ec prog k.
     precondition1 (interp:(v->(source_to_flat_config#C)option)option) g (s1:(FFI)state)
       env1 conf (ec:(C)install_config) prog /\
     ~(SND (evaluate_decs (state_clock_fupd (K k) s1) env1 prog) = Rerr (Rabort Rtype_error))
     ==> state_ffi (FST (evaluate_decs (state_clock_fupd (K k) s1) env1 prog)) =
           flat_state_ffi (FST (flat_evaluate_decs (flat_initial_state (state_ffi s1) k ec)
                                  (SND (source_to_flat_compile_prog conf prog)))) /\
         (!a. SND (flat_evaluate_decs (flat_initial_state (state_ffi s1) k ec)
                     (SND (source_to_flat_compile_prog conf prog))) = SOME (Rabort a) <=>
              SND (evaluate_decs (state_clock_fupd (K k) s1) env1 prog) = Rerr (Rabort a))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pre") (LABEL_TAC "nt")) THEN
  USE_THEN "pre" (LABEL_TAC "prek" o SPEC `k:num` o MATCH_MP precondition1_change_clock) THEN
  FLATP2AUX_PAIR_TAC `evaluate_decs (state_clock_fupd (K k) (s1:(FFI)state)) env1 prog`
    `s':(FFI)state` `r:((v)sem_env,v)result` "ev" THEN
  FLATP2AUX_PAIR_TAC `source_to_flat_compile_prog conf prog` `c':source_to_flat_config`
    `p':flat_exp list` "cp" THEN
  FLATP2AUX_LREWRITE_TAC ["ev"; "cp"] [FST; SND] THEN
  USE_THEN "ev" (fun th -> REMOVE_THEN "nt" (LABEL_TAC "nt" o REWRITE_RULE[th; SND])) THEN
  MP_TAC(ISPECL [`interp:(v->(source_to_flat_config#C)option)option`; `g:dec list->dec list`;
    `state_clock_fupd (K k) (s1:(FFI)state)`; `env1:v sem_env`; `conf:source_to_flat_config`;
    `ec:(C)install_config`; `prog:dec list`; `c':source_to_flat_config`; `p':flat_exp list`;
    `s':(FFI)state`; `r:((v)sem_env,v)result`] compile_prog_correct) THEN
  FLATP2AUX_LREWRITE_TAC ["prek"; "cp"; "ev"; "nt"] [state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`s0:(C,FFI)flat_state`; `s2:(C,FFI)flat_state`; `genv2:global_env`;
    `r2:((flat_v)error_result)option`] THEN
  DISCH_THEN(FLATP2AUX_LABEL_CONJS ["s0"; "fev"; "srel"; "rv"; "re"]) THEN
  REMOVE_THEN "s0" SUBST_ALL_TAC THEN
  FLATP2AUX_LREWRITE_TAC ["fev"] [FST; SND] THEN
  CONJ_TAC THENL
   [USE_THEN "srel" MP_TAC THEN REWRITE_TAC[source_to_flatProof_s_rel_cases] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_TAC THEN
  MP_TAC(ISPEC `r:((v)sem_env,v)result` (cases "result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `v0:(v)sem_env` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `err:(v)error_result` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[distinctness "result"; injectivity "result"] THENL
   [USE_THEN "rv" (fun th -> REWRITE_TAC[MATCH_MP th (REFL `Rval (v0:(v)sem_env):((v)sem_env,v)result`)]) THEN
    REWRITE_TAC[distinctness "option"];
    ALL_TAC] THEN
  USE_THEN "re" (MP_TAC o C MATCH_MP (REFL `Rerr (err:(v)error_result):((v)sem_env,v)result`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `err2:(flat_v)error_result` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[injectivity "option"] THEN
  MP_TAC(ISPEC `err:(v)error_result` (cases "error_result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `x:v` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `b:abort` SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
    "source_to_flatProof_result_rel" with Failure _ -> false)) THEN
  REWRITE_TAC[result_rel_eqns; injectivity "result"] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[distinctness "error_result"; injectivity "error_result"]);;

let FLATP2AUX_SOME_INTRO_TAC : tactic = fun (asl,w as gl) ->
  let st = find_term (fun t -> is_comb t &&
             (try fst(dest_const(rator t)) = "some" with Failure _ -> false)) w in
  let p = rand st in
  let v = genvar (type_of st) in
  let q = mk_abs(v, subst [v,st] w) in
  let ty = hd(snd(dest_type(type_of st))) in
  let th1 = INST_TYPE [ty, `:A`] some_intro in
  let fvs = frees (concl th1) in
  let pv = find (fun x -> fst(dest_var x) = "P") fvs
  and qv = find (fun x -> fst(dest_var x) = "Q") fvs in
  MATCH_MP_TAC (BETA_RULE (INST [p, pv; q, qv] th1)) gl;;

let FLATP2AUX_ab_cases = prove
 (`!(rf:((flat_v)error_result)option) (rs:((v)sem_env,v)result).
     (!a. rf = SOME (Rabort a) <=> rs = Rerr (Rabort a))
     ==> (?b. rs = Rerr (Rabort b) /\ rf = SOME (Rabort b)) \/
         ((!b. ~(rs = Rerr (Rabort b))) /\ (rf = NONE \/ ?x. rf = SOME (Rraise x)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `rf:((flat_v)error_result)option` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `y:(flat_v)error_result` SUBST1_TAC)) THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  MP_TAC(ISPEC `y:(flat_v)error_result` (cases "error_result")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `x:flat_v` SUBST1_TAC)
    (X_CHOOSE_THEN `b:abort` SUBST1_TAC)) THEN
  REWRITE_TAC[distinctness "error_result"; injectivity "error_result"] THEN
  MESON_TAC[]);;

(* HOL4 line 5485 *)
let source_to_flatProof_compile_prog_semantics = prove
 (`!interp g s1 env1 conf eval_conf prog.
     precondition1 (interp:(v->(source_to_flat_config#C)option)option) g (s1:(FFI)state)
     env1 conf (eval_conf:(C)install_config) prog
   ==> ~semantics_prog s1 env1 prog Fail
   ==> semantics_prog s1 env1 prog
         (flat_semantics eval_conf (state_ffi s1)
            (SND (source_to_flat_compile_prog conf prog)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "pre") THEN
  REWRITE_TAC[semantics_prog_def; SEVPAUX_evaluate_prog_with_clock; NOT_EXISTS_THM] THEN
  DISCH_THEN(LABEL_TAC "nf") THEN
  SUBGOAL_THEN
   `!k. state_ffi (FST (evaluate_decs (state_clock_fupd (K k) s1) env1 prog)) =
        flat_state_ffi (FST (flat_evaluate_decs
          (flat_initial_state (state_ffi (s1:(FFI)state)) k (eval_conf:(C)install_config))
          (SND (source_to_flat_compile_prog conf prog)))) /\
        (!a. SND (flat_evaluate_decs (flat_initial_state (state_ffi s1) k eval_conf)
                    (SND (source_to_flat_compile_prog conf prog))) = SOME (Rabort a) <=>
             SND (evaluate_decs (state_clock_fupd (K k) s1) env1 prog) = Rerr (Rabort a))`
    (LABEL_TAC "ck") THENL
   [GEN_TAC THEN MATCH_MP_TAC FLATP2AUX_sem_clock THEN
    MAP_EVERY EXISTS_TAC [`interp:(v->(source_to_flat_config#C)option)option`;
                          `g:dec list->dec list`] THEN
    USE_THEN "pre" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "nf" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  REWRITE_TAC[flat_semantics_def] THEN
  SUBGOAL_THEN `~(?k. SND (flat_evaluate_decs
                  (flat_initial_state (state_ffi (s1:(FFI)state)) k (eval_conf:(C)install_config))
                  (SND (source_to_flat_compile_prog conf prog))) = SOME (Rabort Rtype_error))`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[NOT_EXISTS_THM] THEN GEN_TAC THEN
    USE_THEN "ck" (fun th -> REWRITE_TAC[CONJUNCT2 (SPEC_ALL th)]) THEN
    USE_THEN "nf" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  FLATP2AUX_SOME_INTRO_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `res:behaviour` THEN CASE_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `sf:(C,FFI)flat_state`
        (X_CHOOSE_THEN `rf:((flat_v)error_result)option` (X_CHOOSE_THEN `outcome:outcome`
          (FLATP2AUX_LABEL_CONJS ["fe"; "m"; "res"]))))) THEN
      REMOVE_THEN "res" SUBST1_TAC THEN
      FLATP2AUX_PAIR_TAC `evaluate_decs (state_clock_fupd (K k) (s1:(FFI)state)) env1 prog`
        `ss:(FFI)state` `rs:((v)sem_env,v)result` "se" THEN
      USE_THEN "ck" (MP_TAC o SPEC `k:num`) THEN FLATP2AUX_LREWRITE_TAC ["fe"; "se"] [FST; SND] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ffi") (LABEL_TAC "ab")) THEN
      USE_THEN "nf" (MP_TAC o SPEC `k:num`) THEN FLATP2AUX_LREWRITE_TAC ["se"] [SND] THEN
      DISCH_THEN(LABEL_TAC "nfk") THEN
      REWRITE_TAC[semantics_prog_def; SEVPAUX_evaluate_prog_with_clock] THEN
      MAP_EVERY EXISTS_TAC [`k:num`; `state_ffi (ss:(FFI)state)`; `rs:((v)sem_env,v)result`] THEN
      FLATP2AUX_LREWRITE_TAC ["se"; "ffi"; "nfk"] [FST; SND] THEN
    USE_THEN "ab" (DISJ_CASES_TAC o MATCH_MP FLATP2AUX_ab_cases) THENL
       [FIRST_X_ASSUM(X_CHOOSE_THEN `b:abort` (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
        REMOVE_THEN "m" MP_TAC THEN REMOVE_THEN "nfk" MP_TAC THEN
        MP_TAC(ISPEC `b:abort` (cases "abort")) THEN
        DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN2 SUBST1_TAC
          (X_CHOOSE_THEN `fev:final_event` SUBST1_TAC))) THEN
        CASE_REWRITE_TAC[] THEN REWRITE_TAC[];
        FIRST_X_ASSUM(CONJUNCTS_THEN2 (LABEL_TAC "na")
          (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `x:flat_v` SUBST_ALL_TAC))) THEN
        REMOVE_THEN "m" MP_TAC THEN CASE_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        MP_TAC(ISPEC `rs:((v)sem_env,v)result` (cases "result")) THEN
        DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `v0:(v)sem_env` SUBST_ALL_TAC)
          (X_CHOOSE_THEN `err:(v)error_result` SUBST_ALL_TAC)) THEN
        CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "result"] THEN
        MP_TAC(ISPEC `err:(v)error_result` (cases "error_result")) THEN
        DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `xv:v` SUBST_ALL_TAC)
          (X_CHOOSE_THEN `b:abort` SUBST_ALL_TAC)) THEN
        CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "result"; distinctness "error_result"] THEN
        USE_THEN "na" (MP_TAC o SPEC `b:abort`) THEN REWRITE_TAC[]];
    CASE_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "nt") THEN
      REWRITE_TAC[semantics_prog_def; SEVPAUX_evaluate_prog_with_clock; PAIR_EQ; UNWIND_THM1; FST] THEN
      CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN
          FLATP2AUX_PAIR_TAC `evaluate_decs (state_clock_fupd (K k) (s1:(FFI)state)) env1 prog`
            `ss:(FFI)state` `rs:((v)sem_env,v)result` "se" THEN
          FLATP2AUX_PAIR_TAC `flat_evaluate_decs (flat_initial_state (state_ffi (s1:(FFI)state)) k
              (eval_conf:(C)install_config)) (SND (source_to_flat_compile_prog conf prog))`
            `sf:(C,FFI)flat_state` `rf:((flat_v)error_result)option` "fe" THEN
          FLATP2AUX_LREWRITE_TAC ["se"] [SND] THEN
          USE_THEN "ck" (MP_TAC o SPEC `k:num`) THEN FLATP2AUX_LREWRITE_TAC ["fe"; "se"] [FST; SND] THEN
          DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ffi") (LABEL_TAC "ab")) THEN
          USE_THEN "nf" (MP_TAC o SPEC `k:num`) THEN FLATP2AUX_LREWRITE_TAC ["se"] [SND] THEN
          DISCH_THEN(LABEL_TAC "nfk") THEN
          REFUTE_THEN(LABEL_TAC "ntm") THEN
          USE_THEN "ab" (DISJ_CASES_TAC o MATCH_MP FLATP2AUX_ab_cases) THENL
           [FIRST_X_ASSUM(X_CHOOSE_THEN `b:abort` (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
            MP_TAC(ISPEC `b:abort` (cases "abort")) THEN
            DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (DISJ_CASES_THEN2 SUBST_ALL_TAC
              (X_CHOOSE_THEN `fev:final_event` SUBST_ALL_TAC))) THEN
            RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
            USE_THEN "nt" (MP_TAC o SPEC `Terminate (FFI_outcome fev)
              (ffi_state_io_events (flat_state_ffi (sf:(C,FFI)flat_state)))`) THEN
            REWRITE_TAC[] THEN
            MAP_EVERY EXISTS_TAC [`k:num`; `sf:(C,FFI)flat_state`;
              `SOME (Rabort (Rffi_error fev)):((flat_v)error_result)option`; `FFI_outcome fev`] THEN
            FLATP2AUX_LREWRITE_TAC ["fe"] [] THEN CASE_REWRITE_TAC[];
            FIRST_X_ASSUM(CONJUNCTS_THEN2 (LABEL_TAC "na")
              (DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `x:flat_v` SUBST_ALL_TAC))) THEN
            USE_THEN "nt" (MP_TAC o SPEC `Terminate Success
              (ffi_state_io_events (flat_state_ffi (sf:(C,FFI)flat_state)))`) THEN
            REWRITE_TAC[] THEN
            MAP_EVERY EXISTS_TAC [`k:num`; `sf:(C,FFI)flat_state`] THEN
            USE_THEN "fe" (fun th -> EXISTS_TAC (rand(rhs(concl th)))) THEN
            EXISTS_TAC `Success` THEN FLATP2AUX_LREWRITE_TAC ["fe"] [] THEN CASE_REWRITE_TAC[]];
      USE_THEN "ck" (fun th -> REWRITE_TAC[GSYM (CONJUNCT1 (SPEC_ALL th))]) THEN
          MATCH_MP_TAC build_lprefix_lub_thm THEN
          SUBGOAL_THEN
           `IMAGE (\k. llist_fromList (ffi_state_io_events (state_ffi
               (FST (evaluate_decs (state_clock_fupd (K k) (s1:(FFI)state)) env1 prog))))) (:num) =
            IMAGE llist_fromList (IMAGE (\k. ffi_state_io_events (state_ffi
               (FST (evaluate_decs (state_clock_fupd (K k) s1) env1 prog)))) (:num))`
            SUBST1_TAC THENL [REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
          MATCH_MP_TAC prefix_chain_lprefix_chain THEN
          REWRITE_TAC[prefix_chain_def; FORALL_IN_IMAGE_2; IN_UNIV] THEN
          MAP_EVERY X_GEN_TAC [`k1:num`; `k2:num`] THEN
          DISJ_CASES_TAC(SPECL [`k1:num`; `k2:num`] LE_CASES) THENL [DISJ1_TAC; DISJ2_TAC] THEN
          FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP (ISPECL [`k1:num`; `k2:num`; `s1:(FFI)state`;
             `env1:v sem_env`; `prog:dec list`] evaluate_decs_ffi_mono_clock) th) ORELSE
             MP_TAC(MATCH_MP (ISPECL [`k2:num`; `k1:num`; `s1:(FFI)state`;
             `env1:v sem_env`; `prog:dec list`] evaluate_decs_ffi_mono_clock) th)) THEN
          SIMP_TAC[io_events_mono_def]]]);;

(* connect semantics theorems of flat-to-flat passes *)

(* HOL4 line 5594 *)
let compile_flat_correct = prove
 (`!cfg ec1 ec2 ffi prog.
     install_conf_rel cfg (ec1:(C)install_config) ec2 /\
   ~(flat_semantics ec1 (ffi:(FFI)ffi_state) prog = Fail)
   ==> flat_semantics ec1 ffi prog = flat_semantics ec2 ffi (compile_flat cfg prog)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[compile_flat_def; o_THM] THEN
  SUBGOAL_THEN `flat_semantics (ec1:(C)install_config) (ffi:(FFI)ffi_state) prog =
                flat_semantics ec1 ffi (remove_flat_prog prog)` ASSUME_TAC THENL
   [MATCH_MP_TAC flat_remove_semantics THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM SUBST1_TAC THEN MATCH_MP_TAC (GEN_ALL compile_decs_semantics) THEN
  EXISTS_TAC `cfg:flat_pattern_config` THEN ASM_MESON_TAC[]);;

(* HOL4 line 5606 *)
let precondition_def = cake_def
  `precondition (interp:(v->(source_to_flat_config#C)option)option) (s:(FFI)state) env cfg
                (ec:(C)install_config) prog <=>
     ?ec1 g. precondition1 interp g s env cfg ec1 prog /\
             install_conf_rel (source_to_flat_config_pattern_cfg cfg) ec1 ec`;;

(* HOL4 line 5612 *)
let source_to_flatProof_compile_semantics = prove
 (`!interp s env cfg ec prog.
     precondition (interp:(v->(source_to_flat_config#C)option)option) (s:(FFI)state) env cfg
     (ec:(C)install_config) prog
   ==> ~semantics_prog s env prog Fail
   ==> semantics_prog s env prog
         (flat_semantics ec (state_ffi s) (SND (source_to_flat_compile cfg prog)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[precondition_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `ec1:(C)install_config` (X_CHOOSE_THEN `g:dec list->dec list`
    (CONJUNCTS_THEN2 (LABEL_TAC "pre1") (LABEL_TAC "icr")))) THEN
  DISCH_THEN(LABEL_TAC "nf") THEN
  FLATP2AUX_PAIR_TAC `source_to_flat_compile_prog cfg prog` `c1:source_to_flat_config`
    `p1:flat_exp list` "cp" THEN
  REWRITE_TAC[source_to_flat_compile_def] THEN FLATP2AUX_LREWRITE_TAC ["cp"] [] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `source_to_flat_config_pattern_cfg c1 = source_to_flat_config_pattern_cfg cfg`
    SUBST1_TAC THENL
   [USE_THEN "cp" MP_TAC THEN
    REWRITE_TAC[source_to_flat_compile_prog_def; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT PAIRARG_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[source_to_flat_config_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`interp:(v->(source_to_flat_config#C)option)option`; `g:dec list->dec list`;
    `s:(FFI)state`; `env:v sem_env`; `cfg:source_to_flat_config`; `ec1:(C)install_config`;
    `prog:dec list`] source_to_flatProof_compile_prog_semantics) THEN
  USE_THEN "pre1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "nf" (fun th -> REWRITE_TAC[th]) THEN
  FLATP2AUX_LREWRITE_TAC ["cp"] [SND] THEN DISCH_THEN(LABEL_TAC "sp") THEN
  SUBGOAL_THEN `~(flat_semantics (ec1:(C)install_config) (state_ffi (s:(FFI)state)) p1 = Fail)`
    (LABEL_TAC "nF") THENL
   [DISCH_THEN(fun th -> USE_THEN "sp" MP_TAC THEN REWRITE_TAC[th]) THEN
    USE_THEN "nf" ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`source_to_flat_config_pattern_cfg cfg`; `ec1:(C)install_config`;
    `ec:(C)install_config`; `state_ffi (s:(FFI)state)`; `p1:flat_exp list`]
    compile_flat_correct) THEN
  FLATP2AUX_LREWRITE_TAC ["icr"; "nF"] [] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  USE_THEN "sp" ACCEPT_TAC);;

(* esgc_free theorems for compile_exp *)

(* HOL4 line 5633 *)
let op_gbag_astOp_to_flatOp = prove
 (`!op.
     flat_op_gbag (astOp_to_flatOp op) = EMPTY_BAG`,
  GEN_TAC THEN CASES_ON `op:op` THEN REWRITE_TAC[astOp_to_flatOp_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[flat_op_gbag_def]);;

(* local helpers for compile_exp_esgc_free: the Let chain of the AallocEmpty *)
(* case, and the three shapes of a list *)
let FLATP2AUX_ITLIST_Let = prove
 (`!t xs b. (flat_esgc_free (ITLIST (flat_Let t NONE) xs b) <=>
             ALL flat_esgc_free xs /\ flat_esgc_free b) /\
            (flat_set_globals (ITLIST (flat_Let t NONE) xs b) = EMPTY_BAG <=>
             flat_elist_globals xs = EMPTY_BAG /\ flat_set_globals b = EMPTY_BAG)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITLIST; ALL; flat_esgc_free_def; flat_set_globals_def; BAG_UNION_EMPTY] THEN
  MESON_TAC[]);;

let FLATP2AUX_elist_globals_REVERSE = prove
 (`!l. flat_elist_globals (REVERSE l) = EMPTY_BAG <=> flat_elist_globals l = EMPTY_BAG`,
  REWRITE_TAC[elist_globals_eq_empty; MEM_REVERSE]);;

let FLATP2AUX_list_cases2 = prove
 (`!l:A list. l = [] \/ (?a. l = [a]) \/ (?a b r. l = CONS a (CONS b r))`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `l:A list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN MESON_TAC[list_CASES]);;

(* HOL4 line 5639 *)
let source_to_flatProof_compile_exp_esgc_free = prove
 (`(!tra env exp.
      flat_esgc_free (source_to_flat_compile_exp tra env exp) /\
      flat_set_globals (source_to_flat_compile_exp tra env exp) = EMPTY_BAG) /\
   (!tra env exps.
      ALL flat_esgc_free (source_to_flat_compile_exps tra env exps) /\
      flat_elist_globals (source_to_flat_compile_exps tra env exps) = EMPTY_BAG) /\
   (!tra env pes.
      ALL flat_esgc_free (MAP SND (compile_pes tra env pes)) /\
      flat_elist_globals (MAP SND (compile_pes tra env pes)) = EMPTY_BAG) /\
   (!tra env funs.
      ALL flat_esgc_free (MAP (SND o SND) (compile_funs tra env funs)) /\
      flat_elist_globals (MAP (SND o SND) (compile_funs tra env funs)) = EMPTY_BAG)`,
  MATCH_MP_TAC source_to_flat_compile_exp_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN REWRITE_TAC[source_to_flat_compile_exp_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[flat_esgc_free_def; flat_set_globals_def; BAG_UNION_EMPTY; flat_op_gbag_def;
    op_gbag_astOp_to_flatOp; flat_Bool_def; MAP; ALL; o_THM] THENL
   [(* Var *)
    (fun gl -> FLATP2AUX_OPTION_CASES_TAC
       (FLATP2AUX_PARSE_IN gl "nsLookup (source_to_flat_environment_v env) xid")
       `vn:var_name` "lk" gl) THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[flat_esgc_free_def; flat_set_globals_def] THEN
    STRUCT_CASES_TAC (ISPEC `vn:var_name` (cases "var_name")) THEN
    REWRITE_TAC[compile_var_def; flat_esgc_free_def; flat_set_globals_def; flat_op_gbag_def;
                ALL; BAG_UNION_EMPTY];
    (* App *)
    FLATP2AUX_SUBGOAL "ALL flat_esgc_free (source_to_flat_compile_exps t env es) /\\
                flat_elist_globals (source_to_flat_compile_exps t env es) = EMPTY_BAG"
      STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `es:exp list` FLATP2AUX_list_cases2) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `opn = AallocEmpty` THEN ASM_REWRITE_TAC[] THENL
     [ASM_REWRITE_TAC[FLATP2AUX_ITLIST_Let; EVERY_REVERSE; FLATP2AUX_elist_globals_REVERSE;
        flat_esgc_free_def; flat_set_globals_def; ALL; BAG_UNION_EMPTY; flat_op_gbag_def];
      ALL_TAC] THEN
    ASM_CASES_TAC `opn = Eval` THEN ASM_REWRITE_TAC[] THENL
     [ASM_REWRITE_TAC[flat_esgc_free_def; flat_set_globals_def; ALL; MAP; BAG_UNION_EMPTY;
        flat_op_gbag_def];
      ALL_TAC] THEN
    ASM_CASES_TAC `opn = Env_id` THEN ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPEC `es:exp list` FLATP2AUX_list_cases2) THEN STRIP_TAC THEN
      POP_ASSUM SUBST_ALL_TAC THEN CASE_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[source_to_flat_compile_exp_def; ALL; flat_set_globals_def;
        BAG_UNION_EMPTY]) THEN
      REWRITE_TAC[source_to_flat_compile_exp_def] THEN CASE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[flat_esgc_free_def; flat_set_globals_def; ALL; BAG_UNION_EMPTY;
        flat_op_gbag_def];
      ASM_REWRITE_TAC[flat_esgc_free_def; flat_set_globals_def; op_gbag_astOp_to_flatOp;
        BAG_UNION_EMPTY]];
    (* Log *)
    POP_ASSUM MP_TAC THEN STRUCT_CASES_TAC (ISPEC `lop:lop` (cases "lop")) THEN
    REWRITE_TAC[distinctness "lop"] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[flat_esgc_free_def; flat_set_globals_def; ALL; BAG_UNION_EMPTY]]);;

(* esgc_free theorems for compile_decs *)

(* HOL4 line 5675 *)
let set_globals_make_varls = prove
 (`!a b c d. flat_set_globals (make_varls a b c d) =
             LIST_TO_BAG (MAP ((+) c) (COUNT_LIST (LENGTH d)))`,
  MATCH_MP_TAC make_varls_ind THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[make_varls_def; flat_set_globals_def; flat_op_gbag_def; LENGTH;
                  COUNT_LIST_DEF; MAP; LIST_TO_BAG_def; BAG_UNION_EMPTY] THEN
  REWRITE_TAC[ADD_CLAUSES; MAP_MAP_o; o_DEF; BAG_INSERT_UNION] THEN
  REWRITE_TAC[ARITH_RULE `(c + 1) + x = c + SUC x`] THEN
  REWRITE_TAC[BAG_UNION_EMPTY; GSYM ADD1; ADD_CLAUSES]);;

(* HOL4 line 5690 *)
let make_varls_esgc_free = prove
 (`!n t idx xs. flat_esgc_free (make_varls n t idx xs)`,
  MATCH_MP_TAC make_varls_ind THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[make_varls_def; flat_esgc_free_def; ALL]);;

(* HOL4 line 5698 *)
let nsAll_extend_env = prove
 (`!P e1 e2.
     nsAll P (source_to_flat_environment_v e1) /\ nsAll P (source_to_flat_environment_v e2)
   ==> nsAll P (source_to_flat_environment_v (extend_env e1 e2))`,
  REWRITE_TAC[extend_env_def; source_to_flat_environment_INFO.ri_accessors] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC nsAll_nsAppend THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 5704 *)
let source_to_flatProof_compile_decs_esgc_free = prove
 (`!t n next env envs decs n' next' env' envs' decs'.
     source_to_flat_compile_decs t n next env envs decs = (n', next', env', envs', decs')
     ==> ALL flat_esgc_free decs'`,
  MATCH_MP_TAC source_to_flat_compile_decs_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC[source_to_flat_compile_decs_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ; option_case_eq; pair_case_eq; case_eq "var_name"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[ALL; ALL_APPEND; flat_esgc_free_def; MAP; env_id_tuple_def;
    make_varls_esgc_free; source_to_flatProof_compile_exp_esgc_free] THEN
  ASM_MESON_TAC[]);;

(* the source_to_flat compiler produces things which are esgc_free *)

(* HOL4 line 5722 *)
let source_to_flatProof_compile_prog_esgc_free = prove
 (`!c p c1 p1.
     source_to_flat_compile_prog c p = (c1, p1) ==> ALL flat_esgc_free p1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[source_to_flat_compile_prog_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[ALL; glob_alloc_def; alloc_env_ref_def; flat_esgc_free_def] THEN
  ASM_MESON_TAC[source_to_flatProof_compile_decs_esgc_free]);;

(* HOL4 line 5734 *)
let compile_flat_esgc_free = prove
 (`!cfg ds ds'.
     compile_flat cfg ds = ds' /\ ALL flat_esgc_free ds ==> ALL flat_esgc_free ds'`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THEN
  REWRITE_TAC[compile_flat_def; o_THM] THEN
  MATCH_MP_TAC flat_patternProof_compile_decs_esgc_free THEN
  MATCH_MP_TAC remove_flat_prog_esgc_free THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 5745 *)
let source_to_flatProof_compile_esgc_free = prove
 (`!c p.
     ALL flat_esgc_free (SND (source_to_flat_compile c p))`,
  REPEAT GEN_TAC THEN
  FLATP2AUX_PAIR_TAC `source_to_flat_compile_prog c p` `c1:source_to_flat_config`
    `p1:flat_exp list` "cp" THEN
  REWRITE_TAC[source_to_flat_compile_def] THEN FLATP2AUX_LREWRITE_TAC ["cp"] [] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  MATCH_MP_TAC compile_flat_esgc_free THEN
  MAP_EVERY EXISTS_TAC [`source_to_flat_config_pattern_cfg c1`; `p1:flat_exp list`] THEN
  REWRITE_TAC[] THEN ASM_MESON_TAC[source_to_flatProof_compile_prog_esgc_free]);;

(* HOL4 line 5753 *)
let inc_compile_prog_esgc_free = prove
 (`!env_id c p.
     ALL flat_esgc_free (SND (inc_compile_prog env_id c p))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[inc_compile_prog_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[ALL; ALL_APPEND; glob_alloc_def; store_env_id_def; env_id_tuple_def;
    flat_esgc_free_def] THEN
  ASM_MESON_TAC[source_to_flatProof_compile_decs_esgc_free]);;

(* HOL4 line 5763 *)
let inc_compile_esgc_free = prove
 (`!env_id c p.
     ALL flat_esgc_free (SND (inc_compile env_id c p))`,
  REPEAT GEN_TAC THEN
  FLATP2AUX_PAIR_TAC `inc_compile_prog env_id c p` `c1:source_to_flat_config`
    `p1:flat_exp list` "cp" THEN
  REWRITE_TAC[inc_compile_def] THEN FLATP2AUX_LREWRITE_TAC ["cp"] [] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  MATCH_MP_TAC flat_patternProof_compile_decs_esgc_free THEN
  MP_TAC(SPECL [`env_id:num#num`; `c:source_to_flat_config`; `p:dec list`]
    inc_compile_prog_esgc_free) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 5772 *)
let compile_no_Mat = prove
 (`!c prog.
     no_Mat_decs (SND (source_to_flat_compile c prog))`,
  REPEAT GEN_TAC THEN
  FLATP2AUX_PAIR_TAC `source_to_flat_compile_prog c prog` `c1:source_to_flat_config`
    `p1:flat_exp list` "cp" THEN
  REWRITE_TAC[source_to_flat_compile_def] THEN FLATP2AUX_LREWRITE_TAC ["cp"] [] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[compile_flat_def; o_THM] THEN REWRITE_TAC[compile_decs_no_Mat]);;

(* HOL4 line 5780 *)
let inc_compile_no_Mat = prove
 (`!env_id c prog.
     no_Mat_decs (SND (inc_compile env_id c prog))`,
  REPEAT GEN_TAC THEN
  FLATP2AUX_PAIR_TAC `inc_compile_prog env_id c prog` `c1:source_to_flat_config`
    `p1:flat_exp list` "cp" THEN
  REWRITE_TAC[inc_compile_def] THEN FLATP2AUX_LREWRITE_TAC ["cp"] [] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[compile_decs_no_Mat]);;

(* HOL4 line 5788 *)
let source_to_flatProof_mem_size_lemma = prove
 (`!sz xs N x.
     list_size (sz:A->num) xs < N ==> (MEM x xs ==> sz x < N)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[list_size; MEM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THENL
   [POP_ASSUM MP_TAC THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `x:A`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN POP_ASSUM_LIST(MP_TAC o el 1) THEN ARITH_TAC]);;

(* HOL4 line 5794 *)
let num_bindings_def = cake_def_wf
  `measure dec_size`
  TERM_TAC
  `(num_bindings (Dlet _ p e) =
      match simple_dlet p e with SOME _ -> 0 | _ -> LENGTH (pat_bindings p)) /\
   (num_bindings (Dletrec _ f) = LENGTH f) /\
   (num_bindings (Dmod _ ds) = SUM (MAP num_bindings ds)) /\
   (num_bindings (Dlocal lds ds) = SUM (MAP num_bindings lds) + SUM (MAP num_bindings ds)) /\
   (num_bindings (Denv _) = 1) /\
   (num_bindings _ = 0)`;;

let num_bindings_ind = cake_ind "num_bindings";;

(* HOL4 line 5807 *)
let compile_decs_num_bindings = prove
 (`!t n next env envs decs n' next' env' envs' decs'.
     source_to_flat_compile_decs t n next env envs decs = (n', next', env', envs', decs')
     ==> next_indices_vidx next <= next_indices_vidx next' /\
         SUM (MAP num_bindings decs) = next_indices_vidx next' - next_indices_vidx next`,
  MATCH_MP_TAC source_to_flat_compile_decs_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC[source_to_flat_compile_decs_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ; option_case_eq; pair_case_eq; case_eq "var_name"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV FORALL_UNWIND_CONV)) THEN
  REPEAT(FIRST_X_ASSUM(fun ih -> if is_forall(concl ih) then
     FIRST_ASSUM(fun eq -> MP_TAC(MATCH_MP ih eq)) else NO_TAC)) THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[num_bindings_def; MAP; SUM; next_indices_INFO.ri_accfupds; K_THM;
    LENGTH_REVERSE; ADD_CLAUSES; LE_REFL; SUB_REFL; LE_ADD; ADD_SUB2] THEN
  CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[num_bindings_def; MAP; SUM; ADD_CLAUSES]) THEN
  ASM_ARITH_TAC);;

(* HOL4 line 5824: val COUNT_LIST_ADD_SYM = COUNT_LIST_ADD |> CONV_RULE     *)
(* (SIMP_CONV bool_ss [Once ADD_SYM]), used by compile_decs_elist_globals:   *)
(* the first sum (on the left) is commuted *)
let COUNT_LIST_ADD_SYM = prove
 (`!n m. COUNT_LIST (m + n) =
         APPEND (COUNT_LIST n) (MAP (\n'. n' + n) (COUNT_LIST m))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [ADD_SYM] THEN
  REWRITE_TAC[COUNT_LIST_ADD]);;

(* HOL4 line 5827 *)
let MAPi_SNOC = prove
 (`!xs x (f:num->A->B). MAPi f (SNOC x xs) = SNOC (f (LENGTH xs) x) (MAPi f xs)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC; MAPi_DEF; LENGTH; o_THM]);;

(* local helpers for compile_decs_elist_globals: the globals of two *)
(* consecutive blocks of declarations *)
let FLATP2AUX_globals_bag_append = prove
 (`!v a b. BAG_UNION (LIST_TO_BAG (MAP ((+) v) (COUNT_LIST a)))
                     (LIST_TO_BAG (MAP ((+) (v + a)) (COUNT_LIST b))) =
           LIST_TO_BAG (MAP ((+) v) (COUNT_LIST (a + b)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COUNT_LIST_ADD; MAP_APPEND; LIST_TO_BAG_APPEND; MAP_MAP_o] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ARITH_TAC);;

let FLATP2AUX_globals_bag_append2 = prove
 (`!v v1 a b c. v1 = v + a /\ c = a + b ==>
     BAG_UNION (LIST_TO_BAG (MAP ((+) v) (COUNT_LIST a)))
               (LIST_TO_BAG (MAP ((+) v1) (COUNT_LIST b))) =
     LIST_TO_BAG (MAP ((+) v) (COUNT_LIST c))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[FLATP2AUX_globals_bag_append]);;

let FLATP2AUX_COUNT_LIST_1 = prove
 (`COUNT_LIST 1 = [0]`,
  REWRITE_TAC[ONE; COUNT_LIST_DEF; MAP]);;

(* HOL4 line 5833 *)
let source_to_flatProof_compile_decs_elist_globals = prove
 (`!t n next env envs decs n' next' env' envs' decs'.
     source_to_flat_compile_decs t n next env envs decs = (n', next', env', envs', decs')
     ==> flat_elist_globals decs' =
         LIST_TO_BAG (MAP ((+) (next_indices_vidx next))
                        (COUNT_LIST (SUM (MAP num_bindings decs))))`,
  MATCH_MP_TAC source_to_flat_compile_decs_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC[source_to_flat_compile_decs_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ; option_case_eq; pair_case_eq; case_eq "var_name"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV FORALL_UNWIND_CONV)) THEN
  REPEAT(FIRST_X_ASSUM(fun ih -> if is_forall(concl ih) then
     FIRST_ASSUM(fun eq -> MP_TAC(MATCH_MP ih eq)) else NO_TAC)) THEN
  REPEAT DISCH_TAC THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> TRY (fun g ->
    STRIP_ASSUME_TAC (MATCH_MP compile_decs_num_bindings th) g)) ths) THEN
  ASM_REWRITE_TAC[num_bindings_def; MAP; SUM; ADD_CLAUSES; flat_set_globals_def;
    flat_elist_globals_append; set_globals_make_varls; source_to_flatProof_compile_exp_esgc_free;
    LENGTH_REVERSE; LENGTH_MAP; BAG_UNION_EMPTY; env_id_tuple_def; flat_op_gbag_def;
    COUNT_LIST_DEF; LIST_TO_BAG_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[COUNT_LIST_DEF; MAP; LIST_TO_BAG_def] THEN
  TRY(MATCH_MP_TAC FLATP2AUX_globals_bag_append2 THEN
      RULE_ASSUM_TAC(REWRITE_RULE[num_bindings_def; MAP; SUM; ADD_CLAUSES]) THEN
      CONJ_TAC THEN ASM_ARITH_TAC) THEN
  REWRITE_TAC[FLATP2AUX_COUNT_LIST_1; MAP; LIST_TO_BAG_def; ADD_CLAUSES]);;

(* HOL4 line 5874 *)
let compile_flat_sub_bag = prove
 (`!cfg p.
     SUB_BAG (flat_elist_globals (compile_flat cfg p)) (flat_elist_globals p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_flat_def; o_THM] THEN
  MATCH_MP_TAC SUB_BAG_TRANS THEN
  EXISTS_TAC `flat_elist_globals (remove_flat_prog p)` THEN
  REWRITE_TAC[flat_patternProof_compile_decs_elist_globals; remove_flat_prog_sub_bag]);;

(* HOL4 line 5885 *)
let compile_flat_BAG_ALL_DISTINCT = prove
 (`!p cfg.
     BAG_ALL_DISTINCT (flat_elist_globals p)
   ==> BAG_ALL_DISTINCT (flat_elist_globals (compile_flat cfg p))`,
  MESON_TAC[BAG_ALL_DISTINCT_SUB_BAG; compile_flat_sub_bag]);;

(* HOL4 line 5889 *)
let compile_globals_BAG_ALL_DISTINCT = prove
 (`!c prog.
     BAG_ALL_DISTINCT (flat_elist_globals (SND (source_to_flat_compile c prog)))`,
  REPEAT GEN_TAC THEN
  FLATP2AUX_PAIR_TAC `source_to_flat_compile_prog c prog` `c1:source_to_flat_config`
    `p1:flat_exp list` "cp" THEN
  REWRITE_TAC[source_to_flat_compile_def] THEN FLATP2AUX_LREWRITE_TAC ["cp"] [] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  MATCH_MP_TAC compile_flat_BAG_ALL_DISTINCT THEN
  REMOVE_THEN "cp" MP_TAC THEN
  REWRITE_TAC[source_to_flat_compile_prog_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP source_to_flatProof_compile_decs_elist_globals) THEN
  ASM_REWRITE_TAC[flat_set_globals_def; glob_alloc_def; alloc_env_ref_def; flat_op_gbag_def;
    BAG_UNION_EMPTY; next_indices_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[BAG_ALL_DISTINCT_BAG_UNION; BAG_ALL_DISTINCT_THM; NOT_IN_EMPTY_BAG;
    BAG_DISJOINT_BAG_INSERT; BAG_DISJOINT_EMPTY; IN_LIST_TO_BAG; MEM_MAP;
    LIST_TO_BAG_DISTINCT] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN REWRITE_TAC[all_distinct_count_list] THEN
    REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[NOT_EXISTS_THM] THEN GEN_TAC THEN
    MATCH_MP_TAC(TAUT `~b ==> ~(a /\ b)`) THEN ARITH_TAC]);;

(* HOL4 line 5906 *)
let inc_compile_globals_BAG_ALL_DISTINCT = prove
 (`!env_id c prog.
     BAG_ALL_DISTINCT (flat_elist_globals (SND (inc_compile env_id c prog)))`,
  REPEAT GEN_TAC THEN
  FLATP2AUX_PAIR_TAC `inc_compile_prog env_id c prog` `c1:source_to_flat_config`
    `p1:flat_exp list` "cp" THEN
  REWRITE_TAC[inc_compile_def] THEN FLATP2AUX_LREWRITE_TAC ["cp"] [] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  MATCH_MP_TAC BAG_ALL_DISTINCT_SUB_BAG THEN
  EXISTS_TAC `flat_elist_globals p1` THEN
  REWRITE_TAC[flat_patternProof_compile_decs_elist_globals] THEN
  REMOVE_THEN "cp" MP_TAC THEN
  REWRITE_TAC[inc_compile_prog_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP source_to_flatProof_compile_decs_elist_globals) THEN
  ASM_REWRITE_TAC[flat_set_globals_def; flat_elist_globals_append; glob_alloc_def;
    store_env_id_def; env_id_tuple_def; flat_op_gbag_def; BAG_UNION_EMPTY] THEN
  REWRITE_TAC[LIST_TO_BAG_DISTINCT] THEN
  MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN REWRITE_TAC[all_distinct_count_list] THEN
  REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 5924 *)
let SUB_BAG_IMP = prove
 (`!B1 B2 x.
     SUB_BAG B1 (B2:A->num) ==> BAG_IN x B1 ==> BAG_IN x B2`,
  REWRITE_TAC[SUB_BAG; BAG_IN] THEN MESON_TAC[]);;

(* local helpers for monotonic_globals_state_co_compile: the globals set *)
(* by the compiled programs lie between the vidx counters *)
let FLATP2AUX_compile_globals_bound = prove
 (`!conf prog conf' p.
     source_to_flat_compile conf prog = (conf', p)
     ==> !x. BAG_IN x (flat_elist_globals p)
             ==> x < next_indices_vidx (source_to_flat_config_next conf')`,
  REPEAT GEN_TAC THEN
  FLATP2AUX_PAIR_TAC `source_to_flat_compile_prog conf prog` `c1:source_to_flat_config`
    `p1:flat_exp list` "cp" THEN
  REWRITE_TAC[source_to_flat_compile_def] THEN FLATP2AUX_LREWRITE_TAC ["cp"] [] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  X_GEN_TAC `x:num` THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MATCH_MP SUB_BAG_IMP
    (ISPECL [`source_to_flat_config_pattern_cfg c1`; `p1:flat_exp list`]
       compile_flat_sub_bag))) THEN
  REMOVE_THEN "cp" MP_TAC THEN
  REWRITE_TAC[source_to_flat_compile_prog_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP source_to_flatProof_compile_decs_elist_globals) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP compile_decs_num_bindings) THEN
  ASM_REWRITE_TAC[flat_set_globals_def; glob_alloc_def; alloc_env_ref_def; flat_op_gbag_def;
    BAG_UNION_EMPTY; BAG_IN_BAG_UNION; BAG_IN_BAG_INSERT; NOT_IN_EMPTY_BAG; IN_LIST_TO_BAG;
    MEM_MAP; MEM_COUNT_LIST; source_to_flat_config_INFO.ri_accfupds;
    next_indices_INFO.ri_accfupds; K_THM] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[source_to_flat_config_INFO.ri_accfupds; next_indices_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN STRIP_TAC THEN ASM_ARITH_TAC);;

let FLATP2AUX_inc_compile_globals_bound = prove
 (`!env_id c decs c' p.
     inc_compile env_id c decs = (c', p)
     ==> next_indices_vidx (source_to_flat_config_next c) <=
         next_indices_vidx (source_to_flat_config_next c') /\
         !x. BAG_IN x (flat_elist_globals p)
             ==> next_indices_vidx (source_to_flat_config_next c) <= x /\
                 x < next_indices_vidx (source_to_flat_config_next c')`,
  REPEAT GEN_TAC THEN
  FLATP2AUX_PAIR_TAC `inc_compile_prog env_id c decs` `c1:source_to_flat_config`
    `p1:flat_exp list` "cp" THEN
  REWRITE_TAC[inc_compile_def] THEN FLATP2AUX_LREWRITE_TAC ["cp"] [] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `!cfg x. BAG_IN x (flat_elist_globals (MAP (compile_dec cfg) p1))
                        ==> BAG_IN x (flat_elist_globals p1)` MP_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SUB_BAG_IMP THEN
    REWRITE_TAC[flat_patternProof_compile_decs_elist_globals]; ALL_TAC] THEN
  REMOVE_THEN "cp" MP_TAC THEN
  REWRITE_TAC[inc_compile_prog_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP source_to_flatProof_compile_decs_elist_globals) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP compile_decs_num_bindings) THEN
  ASM_REWRITE_TAC[flat_set_globals_def; flat_elist_globals_append; glob_alloc_def;
    store_env_id_def; env_id_tuple_def; flat_op_gbag_def; BAG_UNION_EMPTY;
    BAG_IN_BAG_UNION; NOT_IN_EMPTY_BAG; IN_LIST_TO_BAG; MEM_MAP; MEM_COUNT_LIST;
    source_to_flat_config_INFO.ri_accfupds; K_THM] THEN
  DISCH_TAC THEN TRY(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  X_GEN_TAC `x:num` THEN DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  STRIP_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 5934: not sure if this variant of the inc. compiler is the one  *)
(* we need (HOL4 comment) *)
let monotonic_globals_state_co_compile = prove
 (`!conf prog conf' p orac f.
     source_to_flat_compile conf prog = (conf', p) /\ FST (FST ((orac:num->(source_to_flat_config#C)#((num#num)#dec list)) 0)) = conf' /\
   is_state_oracle (\c (env_id, decs). inc_compile env_id c (f decs)) orac
   ==> oracle_monotonic (IMAGE SUC o SET_OF_BAG o flat_elist_globals o SND) (<)
         (0 INSERT IMAGE SUC (SET_OF_BAG (flat_elist_globals p)))
         (state_co (\c (env_id, decs). inc_compile env_id c (f decs)) orac)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (ISPEC `\c:source_to_flat_config. SUC (next_indices_vidx (source_to_flat_config_next c))` oracle_monotonic_state) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_INSERT; IN_IMAGE; IN_SET_OF_BAG] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP FLATP2AUX_compile_globals_bound) THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[LT_SUC; LT_0] THEN ASM_MESON_TAC[];
    REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP FLATP2AUX_inc_compile_globals_bound) THEN
    ASM_REWRITE_TAC[LE_SUC; o_THM; SND; IN_IMAGE; IN_SET_OF_BAG] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LE_SUC; LT_SUC] THEN ASM_MESON_TAC[]]);;
