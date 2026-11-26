(* ========================================================================= *)
(* word_copyProof: port of HOL4 compiler/backend/proofs/                     *)
(* word_copyProofScript.sml (CakeML v3479).                                  *)
(* Correctness proof for word_copy.                                          *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - copy_state fields cs.to_eq, cs.from_eq, cs.store_to_eq, cs.next are    *)
(*   copy_state_to_eq cs etc.; wordSem state fields s.locals etc. are       *)
(*   wl_state_locals s etc.                                                  *)
(* - Free variables of HOL4 statements stay free.                            *)
(* - remove_eq_model_insert': the HOL4 variable val is vv (val is a HOL      *)
(*   Light constant).                                                        *)
(* - The HOL4 ML tactic word_exp_cong_tac is not ported: copy_prop_inst_eval *)
(*   unfolds both evaluations and rewrites with CPstate_modelsD facts.       *)
(* - copy_prop_correct (HOL4: structural Induct) is proved by WF induction   *)
(*   on wl_prog_size, with one WPROOF2AUX_cpc_* lemma per program form.      *)
(* - remove_eq_model_sh_mem_set_var is commented out in HOL4 and not ported. *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/word_copy.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;

type_invention_error := true;;

let CPstate_inv_def = cake_def
  `CPstate_inv (cs:copy_state) <=>
     (!v c. lookup v (copy_state_to_eq cs) = SOME c ==> c < copy_state_next cs) /\
     (!c. c IN domain (copy_state_from_eq cs) ==> c < copy_state_next cs) /\
     (!s c. ALOOKUP (copy_state_store_to_eq cs) s = SOME c ==> c < copy_state_next cs) /\
     (!c v. lookup c (copy_state_from_eq cs) = SOME v ==>
            lookup v (copy_state_to_eq cs) = SOME c)`;;

(* As a corollary, different classes have different representatives (unused) *)

let unique_rep = prove
 (`CPstate_inv cs ==>
   c IN domain (copy_state_from_eq cs) /\
   c' IN domain (copy_state_from_eq cs) /\ ~(c = c') ==>
   ~(lookup c (copy_state_from_eq cs) = lookup c' (copy_state_from_eq cs))`,
  REWRITE_TAC[CPstate_inv_def; domain_lookup] THEN MESON_TAC[option_INJ]);;

let WPROOF2AUX_cs_acc = copy_state_INFO.ri_accessors;;

let empty_eq_inv = prove
 (`CPstate_inv empty_eq`,
  REWRITE_TAC[CPstate_inv_def; empty_eq_def; WPROOF2AUX_cs_acc; domain_lookup; lookup_def;
              ALOOKUP_THM; option_DISTINCT]);;

let remove_eq_inv = prove
 (`!cs v. CPstate_inv cs ==> CPstate_inv (remove_eq cs v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[remove_eq_def] THEN TOP_CASE_TAC THEN
  REWRITE_TAC[empty_eq_inv]);;

let remove_eqs_inv = prove
 (`!vv cs. CPstate_inv cs ==> CPstate_inv (remove_eqs cs vv)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[remove_eqs_def] THEN
  ASM_MESON_TAC[remove_eq_inv]);;

let n_lt_n1 = prove
 (`n:num < n + 1 /\ (x:num < y /\ y < z ==> x < z)`,
  ARITH_TAC);;

let set_eq_inv = prove
 (`CPstate_inv cs /\ lookup t (copy_state_to_eq cs) = NONE ==>
   CPstate_inv (set_eq cs t s)`,
  STRIP_TAC THEN REWRITE_TAC[set_eq_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `lookup s (copy_state_to_eq cs)` (nchotomy_of_type `:(num)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  TRY COND_CASES_TAC THEN CAKE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[CPstate_inv_def] o
                check (fun th -> can (find_term ((=) `CPstate_inv`)) (concl th))) THEN
  REWRITE_TAC[CPstate_inv_def; WPROOF2AUX_cs_acc; lookup_insert; domain_insert; IN_INSERT] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_INJ] THEN RVEQ_TAC THEN
  ASM_MESON_TAC[n_lt_n1; option_INJ; option_DISTINCT; domain_lookup]);;

let WPROOF2AUX_lookup_inter_eq_SOME = prove
 (`!m1 m2:A spt k v.
     lookup k (inter_eq m1 m2) = SOME v <=> lookup k m1 = SOME v /\ lookup k m2 = SOME v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_inter_eq] THEN
  MP_TAC(ISPEC `lookup k (m1:A spt)` (nchotomy_of_type `:(A)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[option_DISTINCT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  ASM_MESON_TAC[]);;

let WPROOF2AUX_ALOOKUP_FILTER = prove
 (`!P (l:(A#B)list) s c.
     ALOOKUP (FILTER P l) s = SOME c ==> P (s,c) /\ MEM (s,c) l`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
  REWRITE_TAC[MEM_FILTER]);;

let merge_eqs_inv = prove
 (`CPstate_inv cs1 /\ CPstate_inv cs2 ==> CPstate_inv (merge_eqs cs1 cs2)`,
  REWRITE_TAC[CPstate_inv_def; merge_eqs_def; WPROOF2AUX_cs_acc; domain_lookup;
              WPROOF2AUX_lookup_inter_eq_SOME] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `c < a ==> c < MAX a b`];
    ASM_MESON_TAC[ARITH_RULE `c < a ==> c < MAX a b`];
    DISCH_THEN(MP_TAC o MATCH_MP WPROOF2AUX_ALOOKUP_FILTER) THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    ASM_MESON_TAC[ARITH_RULE `c < a ==> c < MAX a b`];
    ASM_MESON_TAC[]]);;

let set_store_eq_inv = prove
 (`CPstate_inv cs ==> CPstate_inv (set_store_eq cs name e)`,
  STRIP_TAC THEN REWRITE_TAC[set_store_eq_def] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[empty_eq_inv] THEN
  MP_TAC(ISPEC `lookup e (copy_state_to_eq cs)` (nchotomy_of_type `:(num)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  TRY COND_CASES_TAC THEN CAKE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[CPstate_inv_def] o
                check (fun th -> can (find_term ((=) `CPstate_inv`)) (concl th))) THEN
  REWRITE_TAC[CPstate_inv_def; WPROOF2AUX_cs_acc; copy_state_INFO.ri_accfupds;
              lookup_insert; domain_insert; IN_INSERT; ALOOKUP_THM; K_THM] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_INJ] THEN RVEQ_TAC THEN
  ASM_MESON_TAC[n_lt_n1; option_INJ; option_DISTINCT; domain_lookup]);;

let same_classD = prove
 (`CPstate_inv cs /\ lookup_eq cs x = lookup_eq cs y ==>
   x = y \/
   (~(x = y) /\
    ?c rep. lookup x (copy_state_to_eq cs) = SOME c /\
            lookup y (copy_state_to_eq cs) = SOME c /\
            lookup c (copy_state_from_eq cs) = SOME rep)`,
  ASM_CASES_TAC `x:num = y` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[lookup_eq_def; CPstate_inv_def] THEN
  EVERY_CASE_TAC THEN STRIP_TAC THEN
  ASM_MESON_TAC[option_INJ; option_DISTINCT]);;

let same_classD' = prove
 (`CPstate_inv cs /\ lookup_store_eq cs x = SOME (lookup_eq cs y) ==>
   ?c rep. ALOOKUP (copy_state_store_to_eq cs) x = SOME c /\
           lookup y (copy_state_to_eq cs) = SOME c /\
           lookup c (copy_state_from_eq cs) = SOME rep`,
  REWRITE_TAC[lookup_store_eq_def; lookup_eq_def; CPstate_inv_def] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN STRIP_TAC THEN
  ASM_MESON_TAC[option_INJ; option_DISTINCT]);;

let lookup_eqI = prove
 (`!cs r v.
     (r = v /\ lookup v (copy_state_to_eq cs) = NONE) \/
     (?c. lookup v (copy_state_to_eq cs) = SOME c /\
          lookup c (copy_state_from_eq cs) = SOME r) ==>
     lookup_eq cs v = r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[lookup_eq_def] THEN
  CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

let both_alloc_vars_def = cake_def
  `both_alloc_vars (t,s) <=> is_alloc_var t /\ is_alloc_var s`;;

let lookup_eq_set_eq_not_alloc_var = prove
 (`~both_alloc_vars (t,s) ==> lookup_eq (set_eq cs t s) v = lookup_eq cs v`,
  REWRITE_TAC[set_eq_def; both_alloc_vars_def] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

(* the shapes of set_eq cs t s for alloc vars t and s                        *)

let WPROOF2AUX_set_eq_cases = prove
 (`!cs t s.
     is_alloc_var t /\ is_alloc_var s ==>
     ((lookup s (copy_state_to_eq cs) = NONE \/
       ?c. lookup s (copy_state_to_eq cs) = SOME c /\
           lookup c (copy_state_from_eq cs) = NONE) /\
      set_eq cs t s =
      copy_state_REC
        (insert t (copy_state_next cs) (insert s (copy_state_next cs) (copy_state_to_eq cs)))
        (insert (copy_state_next cs) t (copy_state_from_eq cs))
        (copy_state_store_to_eq cs) (copy_state_next cs + 1)) \/
     (?c r. lookup s (copy_state_to_eq cs) = SOME c /\
            lookup c (copy_state_from_eq cs) = SOME r /\
            set_eq cs t s =
            copy_state_REC (insert t c (copy_state_to_eq cs))
              (insert c t (copy_state_from_eq cs))
              (copy_state_store_to_eq cs) (copy_state_next cs))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[set_eq_def] THEN
  MP_TAC(ISPEC `lookup s (copy_state_to_eq cs)` (nchotomy_of_type `:(num)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN CAKE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[nchotomy_of_type `:(num)option`]);;

let WPROOF2AUX_lookup_eq_REC = prove
 (CASE_TERM
  `!t f st n v.
     lookup_eq (copy_state_REC t f st n) v =
     (match lookup v t with
        NONE -> v
      | SOME c -> (match lookup c f with NONE -> v | SOME v' -> v'))`,
  REWRITE_TAC[lookup_eq_def; WPROOF2AUX_cs_acc]);;

let WPROOF2AUX_lookup_eq_cases = prove
 (`!cs v.
     (lookup v (copy_state_to_eq cs) = NONE /\ lookup_eq cs v = v) \/
     (?c. lookup v (copy_state_to_eq cs) = SOME c /\
          lookup c (copy_state_from_eq cs) = NONE /\ lookup_eq cs v = v) \/
     (?c r. lookup v (copy_state_to_eq cs) = SOME c /\
            lookup c (copy_state_from_eq cs) = SOME r /\ lookup_eq cs v = r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_eq_def] THEN
  MP_TAC(ISPEC `lookup v (copy_state_to_eq cs)` (nchotomy_of_type `:(num)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN CAKE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `lookup a (copy_state_from_eq cs)` (nchotomy_of_type `:(num)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN CAKE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let WPROOF2AUX_inv_rep = prove
 (`!cs c r. CPstate_inv cs /\ lookup c (copy_state_from_eq cs) = SOME r ==>
            lookup r (copy_state_to_eq cs) = SOME c`,
  REWRITE_TAC[CPstate_inv_def] THEN MESON_TAC[]);;

let WPROOF2AUX_inv_class = prove
 (`!cs v c. CPstate_inv cs /\ lookup v (copy_state_to_eq cs) = SOME c ==>
            c < copy_state_next cs`,
  REWRITE_TAC[CPstate_inv_def] THEN MESON_TAC[]);;

(* lookup_eq after set_eq cs t s with t and s alloc vars and t unclassified *)

let WPROOF2AUX_lookup_eq_set_eq = prove
 (`CPstate_inv cs /\ is_alloc_var t /\ is_alloc_var s /\
   lookup t (copy_state_to_eq cs) = NONE ==>
   lookup_eq (set_eq cs t s) v =
   if v = t \/ lookup_eq cs v = lookup_eq cs s then t else lookup_eq cs v`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`cs:copy_state`; `t:num`; `s:num`] WPROOF2AUX_set_eq_cases) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[WPROOF2AUX_lookup_eq_REC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "set_eq"
     with Failure _ -> false))) THENL
   [    (SUBGOAL_THEN `lookup_eq cs s = s` ASSUME_TAC THENL
      [ASM_REWRITE_TAC[lookup_eq_def] THEN CAKE_REWRITE_TAC[] THEN
       ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `!x. ~(x = s) ==> ~(lookup_eq cs x = s)` ASSUME_TAC THENL
      [GEN_TAC THEN DISCH_TAC THEN
       MP_TAC(SPECL [`cs:copy_state`; `x:num`] WPROOF2AUX_lookup_eq_cases) THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
       FIRST_ASSUM(MP_TAC o MATCH_MP WPROOF2AUX_inv_rep o CONJ (ASSUME `CPstate_inv cs`)) THEN
       ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
       DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[option_DISTINCT];
       ALL_TAC] THEN
     ASM_CASES_TAC `v:num = t` THEN ASM_REWRITE_TAC[lookup_insert] THEN
     CAKE_REWRITE_TAC[] THEN
     ASM_CASES_TAC `v:num = s` THEN ASM_REWRITE_TAC[lookup_insert] THEN
     CAKE_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `v:num` o check (is_forall o concl)) THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[lookup_eq_def] THEN
     MP_TAC(ISPEC `lookup v (copy_state_to_eq cs)` (nchotomy_of_type `:(num)option`)) THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
     MP_TAC(SPECL [`cs:copy_state`; `v:num`; `a:num`] WPROOF2AUX_inv_class) THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
     SUBGOAL_THEN `~(a = copy_state_next cs)` (fun th -> REWRITE_TAC[th]) THEN
     POP_ASSUM MP_TAC THEN ARITH_TAC);
    (SUBGOAL_THEN `lookup_eq cs s = s` ASSUME_TAC THENL
      [ASM_REWRITE_TAC[lookup_eq_def] THEN CAKE_REWRITE_TAC[] THEN
       ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `!x. ~(x = s) ==> ~(lookup_eq cs x = s)` ASSUME_TAC THENL
      [GEN_TAC THEN DISCH_TAC THEN
       MP_TAC(SPECL [`cs:copy_state`; `x:num`] WPROOF2AUX_lookup_eq_cases) THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
       FIRST_ASSUM(MP_TAC o MATCH_MP WPROOF2AUX_inv_rep o CONJ (ASSUME `CPstate_inv cs`)) THEN
       ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
       DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[option_DISTINCT];
       ALL_TAC] THEN
     ASM_CASES_TAC `v:num = t` THEN ASM_REWRITE_TAC[lookup_insert] THEN
     CAKE_REWRITE_TAC[] THEN
     ASM_CASES_TAC `v:num = s` THEN ASM_REWRITE_TAC[lookup_insert] THEN
     CAKE_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `v:num` o check (is_forall o concl)) THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[lookup_eq_def] THEN
     MP_TAC(ISPEC `lookup v (copy_state_to_eq cs)` (nchotomy_of_type `:(num)option`)) THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
     MP_TAC(SPECL [`cs:copy_state`; `v:num`; `a:num`] WPROOF2AUX_inv_class) THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
     SUBGOAL_THEN `~(a = copy_state_next cs)` (fun th -> REWRITE_TAC[th]) THEN
     POP_ASSUM MP_TAC THEN ARITH_TAC);
    (SUBGOAL_THEN `lookup_eq cs s = r` ASSUME_TAC THENL
      [ASM_REWRITE_TAC[lookup_eq_def] THEN CAKE_REWRITE_TAC[] THEN
       ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `!x. lookup_eq cs x = r <=> lookup x (copy_state_to_eq cs) = SOME c`
       ASSUME_TAC THENL
      [GEN_TAC THEN EQ_TAC THENL
        [MP_TAC(SPECL [`cs:copy_state`; `x:num`] WPROOF2AUX_lookup_eq_cases) THEN
         STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
         MP_TAC(SPECL [`cs:copy_state`; `c:num`; `r:num`] WPROOF2AUX_inv_rep) THEN
         ASM_REWRITE_TAC[] THEN
         TRY (MP_TAC(SPECL [`cs:copy_state`; `c':num`; `r:num`] WPROOF2AUX_inv_rep) THEN
              ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
              REWRITE_TAC[option_INJ] THEN MESON_TAC[]);
         DISCH_TAC THEN ASM_REWRITE_TAC[lookup_eq_def] THEN CAKE_REWRITE_TAC[] THEN
         ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]];
       ALL_TAC] THEN
     ASM_REWRITE_TAC[lookup_insert] THEN
     ASM_CASES_TAC `v:num = t` THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[lookup_eq_def] THEN
     MP_TAC(ISPEC `lookup v (copy_state_to_eq cs)` (nchotomy_of_type `:(num)option`)) THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN CAKE_REWRITE_TAC[] THEN
     ASM_CASES_TAC `a:num = c` THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[])]);;

let lookup_eq_set_eq_is_alloc_var1 = prove
 (`CPstate_inv cs /\ both_alloc_vars (t,s) ==>
   lookup t (copy_state_to_eq cs) = NONE ==>
   lookup_eq cs s = lookup_eq cs v ==>
   lookup_eq (set_eq cs t s) v = t`,
  REWRITE_TAC[both_alloc_vars_def] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WPROOF2AUX_lookup_eq_set_eq]);;

let lookup_eq_set_eq_is_alloc_var2 = prove
 (`CPstate_inv cs /\ both_alloc_vars (t,s) ==>
   lookup t (copy_state_to_eq cs) = NONE ==>
   ~(v = t) ==>
   ~(lookup_eq cs s = lookup_eq cs v) ==>
   lookup_eq (set_eq cs t s) v = lookup_eq cs v`,
  REWRITE_TAC[both_alloc_vars_def] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WPROOF2AUX_lookup_eq_set_eq] THEN ASM_MESON_TAC[]);;

let lookup_eq_set_eq_t = prove
 (`CPstate_inv cs /\ both_alloc_vars (t,s) ==> lookup_eq (set_eq cs t s) t = t`,
  REWRITE_TAC[both_alloc_vars_def] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cs:copy_state`; `t:num`; `s:num`] WPROOF2AUX_set_eq_cases) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[WPROOF2AUX_lookup_eq_REC; lookup_insert] THEN CAKE_REWRITE_TAC[]);;

let lookup_eq_set_eq_s = prove
 (`CPstate_inv cs /\ both_alloc_vars (t,s) ==>
   lookup t (copy_state_to_eq cs) = NONE ==>
   lookup_eq (set_eq cs t s) s = t`,
  REWRITE_TAC[both_alloc_vars_def] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WPROOF2AUX_lookup_eq_set_eq]);;

(* a variable whose representative is an unclassified variable t is t       *)

let WPROOF2AUX_lookup_eq_unclassified = prove
 (`!cs v t. CPstate_inv cs /\ lookup t (copy_state_to_eq cs) = NONE /\
            lookup_eq cs v = t ==> v = t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cs:copy_state`; `v:num`] WPROOF2AUX_lookup_eq_cases) THEN
  STRIP_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cs:copy_state`; `c:num`; `r:num`] WPROOF2AUX_inv_rep) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `lookup_eq cs v = t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && rand(concl th) = `r:num` &&
                                                  is_comb(lhs(concl th)))) THEN
  ASM_REWRITE_TAC[option_DISTINCT]);;

let lookup_eq_set_eqD = prove
 (`CPstate_inv cs ==>
   lookup t (copy_state_to_eq cs) = NONE ==>
   lookup_eq (set_eq cs t s) v = r ==>
   (r = t ==> v = t \/ lookup_eq cs v = lookup_eq cs s) /\
   (~(r = t) ==> r = lookup_eq cs v)`,
  REPEAT DISCH_TAC THEN ASM_CASES_TAC `both_alloc_vars (t,s)` THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[both_alloc_vars_def]) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `lookup_eq (set_eq cs t s) v = r`)) THEN
    ASM_SIMP_TAC[WPROOF2AUX_lookup_eq_set_eq] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_MESON_TAC[WPROOF2AUX_lookup_eq_unclassified];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `lookup_eq (set_eq cs t s) v = r`)) THEN
    ASM_SIMP_TAC[lookup_eq_set_eq_not_alloc_var] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_MESON_TAC[WPROOF2AUX_lookup_eq_unclassified]]);;
let CPstate_models_def = cake_def
  `CPstate_models (cs:copy_state) (S:(A,C,FFI)wl_state) <=>
     (!v c vrep. lookup v (copy_state_to_eq cs) = SOME c ==>
                 lookup c (copy_state_from_eq cs) = SOME vrep ==>
                 lookup v (wl_state_locals S) = lookup vrep (wl_state_locals S)) /\
     (!s c vrep. ALOOKUP (copy_state_store_to_eq cs) s = SOME c ==>
                 lookup c (copy_state_from_eq cs) = SOME vrep ==>
                 FLOOKUP (wl_state_store S) s = lookup vrep (wl_state_locals S))`;;

let CPstate_models_with_const = prove
 (`CPstate_models cs (wl_state_locals_size_fupd (combin_K ls) (s:(A,C,FFI)wl_state)) =
     CPstate_models cs s /\
   CPstate_models cs (wl_state_fp_regs_fupd (combin_K fp) s) = CPstate_models cs s /\
   CPstate_models cs (wl_state_stack_fupd (combin_K xs) s) = CPstate_models cs s /\
   CPstate_models cs (wl_state_stack_limit_fupd (combin_K sl) s) = CPstate_models cs s /\
   CPstate_models cs (wl_state_stack_max_fupd (combin_K sm) s) = CPstate_models cs s /\
   CPstate_models cs (wl_state_stack_size_fupd (combin_K ssize) s) = CPstate_models cs s /\
   CPstate_models cs (wl_state_memory_fupd (combin_K m) s) = CPstate_models cs s /\
   CPstate_models cs (wl_state_mdomain_fupd (combin_K md) s) = CPstate_models cs s /\
   CPstate_models cs (wl_state_sh_mdomain_fupd (combin_K smd) s) = CPstate_models cs s /\
   CPstate_models cs (wl_state_permute_fupd (combin_K p) s) = CPstate_models cs s /\
   CPstate_models cs (wl_state_compile_fupd (combin_K c) s) = CPstate_models cs s /\
   CPstate_models cs (wl_state_compile_oracle_fupd (combin_K co) s) = CPstate_models cs s /\
   CPstate_models cs (wl_state_code_buffer_fupd (combin_K cb) s) = CPstate_models cs s /\
   CPstate_models cs (wl_state_data_buffer_fupd (combin_K db) s) = CPstate_models cs s /\
   CPstate_models cs (wl_state_gc_fun_fupd (combin_K g) s) = CPstate_models cs s /\
   CPstate_models cs (wl_state_handler_fupd (combin_K hd) s) = CPstate_models cs s /\
   CPstate_models cs (wl_state_clock_fupd (combin_K clk) s) = CPstate_models cs s /\
   CPstate_models cs (wl_state_termdep_fupd (combin_K tdep) s) = CPstate_models cs s /\
   CPstate_models cs (wl_state_code_fupd (combin_K cd) s) = CPstate_models cs s /\
   CPstate_models cs (wl_state_be_fupd (combin_K b) s) = CPstate_models cs s /\
   CPstate_models cs (wl_state_ffi_fupd (combin_K ffi) s) = CPstate_models cs s`,
  REWRITE_TAC[CPstate_models_def; wl_state_INFO.ri_accfupds]);;

let _ = cake_add_simps [CPstate_models_with_const];;

let CPstate_model = prove
 (`CPstate_models cs (st:(A,C,FFI)wl_state) ==>
   lookup (lookup_eq cs v) (wl_state_locals st) = lookup v (wl_state_locals st)`,
  REWRITE_TAC[CPstate_models_def] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cs:copy_state`; `v:num`] WPROOF2AUX_lookup_eq_cases) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
let CPstate_modelsI = prove
 (`CPstate_inv cs /\
   (!x y. lookup_eq cs x = lookup_eq cs y ==>
          lookup x (wl_state_locals (st:(A,C,FFI)wl_state)) = lookup y (wl_state_locals st)) /\
   (!x y. lookup_store_eq cs x = SOME (lookup_eq cs y) ==>
          FLOOKUP (wl_state_store st) x = lookup y (wl_state_locals st)) ==>
   CPstate_models cs st`,
  STRIP_TAC THEN REWRITE_TAC[CPstate_models_def] THEN CONJ_TAC THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP WPROOF2AUX_inv_rep
                                 (CONJ (ASSUME `CPstate_inv cs`) th))) THEN
  DISCH_TAC THEN
  (SUBGOAL_THEN `lookup_eq cs vrep = vrep` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[lookup_eq_def] THEN CAKE_REWRITE_TAC[] THEN
     ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]; ALL_TAC]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THENL
   [ASM_REWRITE_TAC[lookup_eq_def] THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[];
    ASM_REWRITE_TAC[lookup_store_eq_def] THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]]);;

let CPstate_modelsD = prove
 (`CPstate_inv cs /\ CPstate_models cs (st:(A,C,FFI)wl_state) ==>
   (!x y. lookup_eq cs x = lookup_eq cs y ==>
          lookup x (wl_state_locals st) = lookup y (wl_state_locals st)) /\
   (!x y. lookup_store_eq cs x = SOME (lookup_eq cs y) ==>
          FLOOKUP (wl_state_store st) x = lookup y (wl_state_locals st))`,
  STRIP_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [MP_TAC(INST [`x:num`,`x:num`; `y:num`,`y:num`] same_classD) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CPstate_models_def]) THEN ASM_MESON_TAC[];
    MP_TAC(INST [`x:num`,`x:num`; `y:num`,`y:num`] same_classD') THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CPstate_models_def]) THEN ASM_MESON_TAC[]]);;

let remove_eq_model = prove
 (`CPstate_models cs (st:(A,C,FFI)wl_state) ==> CPstate_models (remove_eq cs t) st`,
  REWRITE_TAC[remove_eq_def] THEN TOP_CASE_TAC THEN
  REWRITE_TAC[empty_eq_def; CPstate_models_def; WPROOF2AUX_cs_acc; lookup_def;
              ALOOKUP_THM; option_DISTINCT]);;

let remove_eq_model_insert' = prove
 (`CPstate_inv cs /\ CPstate_models cs (st:(A,B,C)wl_state) /\
   wl_state_locals (st':(A,B,C)wl_state) = insert t vv (wl_state_locals st) /\
   wl_state_store st' = wl_state_store st ==>
   CPstate_models (remove_eq cs t) st'`,
  REWRITE_TAC[remove_eq_def] THEN STRIP_TAC THEN TOP_CASE_TAC THEN
  REWRITE_TAC[empty_eq_def; CPstate_models_def; WPROOF2AUX_cs_acc; lookup_def;
              ALOOKUP_THM; option_DISTINCT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CPstate_models_def; CPstate_inv_def]) THEN
  ASM_REWRITE_TAC[lookup_insert] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[option_DISTINCT]);;
let remove_eq_model_insert = prove
 (`CPstate_inv cs ==>
   CPstate_models cs (st:(A,C,FFI)wl_state) ==>
   CPstate_models (remove_eq cs t)
     (wl_state_locals_fupd (combin_K (insert t vv (wl_state_locals st))) st)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC remove_eq_model_insert' THEN
  ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM]);;

let remove_eq_model_set_var = prove
 (`CPstate_inv cs /\ CPstate_models cs (st:(A,C,FFI)wl_state) ==>
   CPstate_models (remove_eq cs t) (wl_set_var t vv st)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wl_set_var_def] THEN
  ASM_SIMP_TAC[remove_eq_model_insert]);;

let CPstate_models_same = prove
 (`CPstate_models cs (st:(A,C,FFI)wl_state) /\
   wl_state_locals (st':(A,C,FFI)wl_state) = wl_state_locals st /\
   wl_state_store st' = wl_state_store st ==>
   CPstate_models cs st'`,
  REWRITE_TAC[CPstate_models_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let set_fp_var_model = prove
 (`CPstate_models cs (st:(A,C,FFI)wl_state) ==>
   CPstate_models cs (wl_set_fp_var t vv st)`,
  REWRITE_TAC[wl_set_fp_var_def; CPstate_models_with_const]);;

let merge_eqs_model1 = prove
 (`CPstate_models cs1 (st:(A,C,FFI)wl_state) ==>
   CPstate_models (merge_eqs cs1 cs2) st`,
  REWRITE_TAC[CPstate_models_def; merge_eqs_def; WPROOF2AUX_cs_acc;
              WPROOF2AUX_lookup_inter_eq_SOME] THEN
  STRIP_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP WPROOF2AUX_ALOOKUP_FILTER) THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[]]);;

let merge_eqs_model2 = prove
 (`CPstate_models cs2 (st:(A,C,FFI)wl_state) ==>
   CPstate_models (merge_eqs cs1 cs2) st`,
  REWRITE_TAC[CPstate_models_def; merge_eqs_def; WPROOF2AUX_cs_acc;
              WPROOF2AUX_lookup_inter_eq_SOME] THEN
  STRIP_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP WPROOF2AUX_ALOOKUP_FILTER) THEN
    CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[]]);;

let set_eq_store_to_eq = prove
 (`copy_state_store_to_eq (set_eq cs t s) = copy_state_store_to_eq cs`,
  REWRITE_TAC[set_eq_def] THEN REPEAT (FIRST [COND_CASES_TAC; TOP_CASE_TAC]) THEN
  REWRITE_TAC[WPROOF2AUX_cs_acc]);;

let _ = cake_add_simps [set_eq_store_to_eq];;

let lookup_eq_remove_eq_t = prove
 (`CPstate_inv cs /\ lookup_eq (remove_eq cs t) x = t ==> x = t`,
  REWRITE_TAC[remove_eq_def] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `lookup t (copy_state_to_eq cs)` (nchotomy_of_type `:(num)option`)) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
                     (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "lookup_eq"
                      with Failure _ -> false))) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THENL
   [DISCH_TAC THEN MATCH_MP_TAC WPROOF2AUX_lookup_eq_unclassified THEN
    EXISTS_TAC `cs:copy_state` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[empty_eq_def; WPROOF2AUX_lookup_eq_REC; lookup_def] THEN
    CAKE_REWRITE_TAC[]]);;

let WPROOF2AUX_lookup_store_eq_REC = prove
 (CASE_TERM
  `!t f st n v.
     lookup_store_eq (copy_state_REC t f st n) v =
     (match ALOOKUP st v with
        NONE -> NONE
      | SOME c -> (match lookup c f with NONE -> NONE | SOME v' -> SOME v'))`,
  REWRITE_TAC[lookup_store_eq_def; WPROOF2AUX_cs_acc]);;

(* a store class with representative t has t classified                      *)

let WPROOF2AUX_lookup_store_eq_unclassified = prove
 (`!cs v t. CPstate_inv cs /\ lookup t (copy_state_to_eq cs) = NONE ==>
            ~(lookup_store_eq cs v = SOME t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[lookup_store_eq_def] THEN
  MP_TAC(ISPEC `ALOOKUP (copy_state_store_to_eq cs) v` (nchotomy_of_type `:(num)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[option_DISTINCT] THEN
  MP_TAC(ISPEC `lookup a (copy_state_from_eq cs)` (nchotomy_of_type `:(num)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(SPECL [`cs:copy_state`; `a:num`; `t:num`] WPROOF2AUX_inv_rep) THEN
  ASM_REWRITE_TAC[option_DISTINCT]);;

(* close a goal whose assumptions contain some p and ~p                     *)

let WPROOF2AUX_ASM_CONTR_TAC : tactic = fun (asl,w as g) ->
  let negs = filter (fun (_,th) -> is_neg(concl th)) asl in
  let rec try_n = function
      [] -> failwith "WPROOF2AUX_ASM_CONTR_TAC"
    | (_,th)::t ->
        (try let p = rand(concl th) in
             let _,th2 = find (fun (_,th2) -> aconv (concl th2) p) asl in
             CONTR_TAC (MP (NOT_ELIM th) th2) g
         with Failure _ -> try_n t) in
  try_n negs;;
let WPROOF2AUX_lookup_store_eq_alt = prove
 (`!cs v a.
     ALOOKUP (copy_state_store_to_eq cs) v = SOME a ==>
     lookup_store_eq cs v = lookup a (copy_state_from_eq cs)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[lookup_store_eq_def] THEN CAKE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `lookup a (copy_state_from_eq cs)` (nchotomy_of_type `:(num)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

let WPROOF2AUX_lookup_store_eq_set_eq_alt = prove
 (`!cs v a t s.
     ALOOKUP (copy_state_store_to_eq cs) v = SOME a ==>
     lookup_store_eq (set_eq cs t s) v = lookup a (copy_state_from_eq (set_eq cs t s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WPROOF2AUX_lookup_store_eq_alt THEN
  ASM_REWRITE_TAC[set_eq_store_to_eq]);;

let lookup_store_eq_set_eqD = prove
 (`CPstate_inv cs ==>
   lookup t (copy_state_to_eq cs) = NONE ==>
   lookup_store_eq (set_eq cs t s) v = SOME r ==>
   (r = t ==> lookup_store_eq cs v = SOME (lookup_eq cs s)) /\
   (~(r = t) ==> lookup_store_eq cs v = SOME r)`,
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `~(lookup_store_eq cs v = SOME t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[WPROOF2AUX_lookup_store_eq_unclassified]; ALL_TAC] THEN
  ASM_CASES_TAC `both_alloc_vars (t,s)` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && rand(concl th) = `SOME (r:num)`)) THEN
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[both_alloc_vars_def]) THEN
    ASM_REWRITE_TAC[set_eq_def] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN WPROOF2AUX_ASM_CONTR_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[both_alloc_vars_def]) THEN
  MP_TAC(ISPEC `ALOOKUP (copy_state_store_to_eq cs) v` (nchotomy_of_type `:(num)option`)) THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && rand(concl th) = `SOME (r:num)`)) THEN
    ASM_REWRITE_TAC[lookup_store_eq_def; set_eq_store_to_eq] THEN
    CAKE_REWRITE_TAC[option_DISTINCT];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_lookup_store_eq_alt th]) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && rand(concl th) = `SOME (r:num)`)) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WPROOF2AUX_lookup_store_eq_set_eq_alt th]) THEN
  MP_TAC(SPECL [`cs:copy_state`; `t:num`; `s:num`] WPROOF2AUX_set_eq_cases) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[WPROOF2AUX_cs_acc; lookup_insert] THENL
   [SUBGOAL_THEN `a < copy_state_next cs` MP_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                  REWRITE_RULE[CPstate_inv_def] o check (fun th -> concl th = `CPstate_inv cs`)) THEN
      DISCH_THEN(MP_TAC o SPECL [`v:store_name`; `a:num`]) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP (ARITH_RULE `a < n ==> ~(a = n:num)`) th]) THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP WPROOF2AUX_lookup_store_eq_alt th)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN WPROOF2AUX_ASM_CONTR_TAC;
    SUBGOAL_THEN `a < copy_state_next cs` MP_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                  REWRITE_RULE[CPstate_inv_def] o check (fun th -> concl th = `CPstate_inv cs`)) THEN
      DISCH_THEN(MP_TAC o SPECL [`v:store_name`; `a:num`]) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP (ARITH_RULE `a < n ==> ~(a = n:num)`) th]) THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP WPROOF2AUX_lookup_store_eq_alt th)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN WPROOF2AUX_ASM_CONTR_TAC;
    ASM_CASES_TAC `a:num = c` THEN ASM_REWRITE_TAC[option_INJ] THENL
     [DISCH_THEN(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[] THEN
      REWRITE_TAC[lookup_eq_def] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[];
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP WPROOF2AUX_lookup_store_eq_alt th)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN WPROOF2AUX_ASM_CONTR_TAC]]);;

let WPROOF2AUX_remove_eq_t = prove
 (`!cs t. lookup t (copy_state_to_eq (remove_eq cs t)) = NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[remove_eq_def] THEN
  MP_TAC(ISPEC `lookup t (copy_state_to_eq cs)` (nchotomy_of_type `:(num)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[empty_eq_def; WPROOF2AUX_cs_acc; lookup_def]);;

let copy_prop_move_model_aux = prove
 (`CPstate_inv cs /\ CPstate_models cs (st:(A,C,FFI)wl_state) /\
   both_alloc_vars (t,s) /\ lookup s (wl_state_locals st) = SOME sval ==>
   CPstate_models (set_eq (remove_eq cs t) t s)
     (wl_state_locals_fupd (combin_K (insert t sval (wl_state_locals st))) st)`,
  REWRITE_TAC[both_alloc_vars_def] THEN STRIP_TAC THEN
  ABBREV_TAC `cs1 = remove_eq cs t` THEN
  SUBGOAL_THEN `CPstate_inv cs1` ASSUME_TAC THENL
   [EXPAND_TAC "cs1" THEN MATCH_MP_TAC remove_eq_inv THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lookup t (copy_state_to_eq cs1) = NONE` ASSUME_TAC THENL
   [EXPAND_TAC "cs1" THEN REWRITE_TAC[WPROOF2AUX_remove_eq_t]; ALL_TAC] THEN
  SUBGOAL_THEN `CPstate_models cs1 (st:(A,C,FFI)wl_state)` ASSUME_TAC THENL
   [EXPAND_TAC "cs1" THEN MATCH_MP_TAC remove_eq_model THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(INST [`cs1:copy_state`,`cs:copy_state`] (ISPEC `st:(A,C,FFI)wl_state`
           (GEN `st:(A,C,FFI)wl_state` CPstate_modelsD))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "D1") (LABEL_TAC "D2")) THEN
  SUBGOAL_THEN `!z. ~(z = t) ==> ~(lookup_eq cs1 z = t)` (LABEL_TAC "U") THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `~(z:num = t)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC WPROOF2AUX_lookup_eq_unclassified THEN
    EXISTS_TAC `cs1:copy_state` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. (z = t \/ lookup_eq cs1 z = lookup_eq cs1 s) ==>
                    (if z = t then SOME sval else lookup z (wl_state_locals (st:(A,C,FFI)wl_state))) =
                    SOME (sval:(A)word_loc)` (LABEL_TAC "P") THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "D1" (MP_TAC o SPECL [`z:num`; `s:num`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. lookup_eq (set_eq cs1 t s) z =
                    if z = t \/ lookup_eq cs1 z = lookup_eq cs1 s then t else lookup_eq cs1 z`
    (LABEL_TAC "C") THENL
   [GEN_TAC THEN MATCH_MP_TAC WPROOF2AUX_lookup_eq_set_eq THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CPstate_modelsI THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC set_eq_inv THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[ASSUME `!z. lookup_eq (set_eq cs1 t s) z =
                    if z = t \/ lookup_eq cs1 z = lookup_eq cs1 s then t else lookup_eq cs1 z`] THEN
    REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN
    ASM_CASES_TAC `x = t \/ lookup_eq cs1 x = lookup_eq cs1 s` THEN
    ASM_CASES_TAC `y = t \/ lookup_eq cs1 y = lookup_eq cs1 s` THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THENL
     [USE_THEN "P" (fun th ->
        REWRITE_TAC[MP (SPEC `x:num` th)
                       (ASSUME `x = t \/ lookup_eq cs1 x = lookup_eq cs1 s`);
                    MP (SPEC `y:num` th)
                       (ASSUME `y = t \/ lookup_eq cs1 y = lookup_eq cs1 s`)]);
      RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
      USE_THEN "U" (fun u -> ASSUME_TAC(MP (SPEC `y:num` u) (CONJUNCT1 (ASSUME
        `~(y = t) /\ ~(lookup_eq cs1 y = lookup_eq cs1 s)`)))) THEN
      ASM_MESON_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
      USE_THEN "U" (fun u -> ASSUME_TAC(MP (SPEC `x:num` u) (CONJUNCT1 (ASSUME
        `~(x = t) /\ ~(lookup_eq cs1 x = lookup_eq cs1 s)`)))) THEN
      ASM_MESON_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "D1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REPEAT GEN_TAC THEN REWRITE_TAC[ASSUME `!z. lookup_eq (set_eq cs1 t s) z =
                    if z = t \/ lookup_eq cs1 z = lookup_eq cs1 s then t else lookup_eq cs1 z`] THEN
    REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; lookup_insert] THEN
    ASM_CASES_TAC `y = t \/ lookup_eq cs1 y = lookup_eq cs1 s` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_IMP] lookup_store_eq_set_eqD) o
                CONJ (CONJ (ASSUME `CPstate_inv cs1`)
                           (ASSUME `lookup t (copy_state_to_eq cs1) = NONE`))) THEN
    ASM_REWRITE_TAC[] THENL
     [DISCH_TAC THEN
      USE_THEN "D2" (fun d2 -> USE_THEN "P" (fun pp ->
        REWRITE_TAC[MP (SPECL [`x:store_name`; `s:num`] d2)
                       (ASSUME `lookup_store_eq cs1 x = SOME (lookup_eq cs1 s)`);
                    MP (SPEC `y:num` pp)
                       (ASSUME `y = t \/ lookup_eq cs1 y = lookup_eq cs1 s`)])) THEN
      ASM_REWRITE_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
      USE_THEN "U" (fun u -> ASSUME_TAC(MP (SPEC `y:num` u) (CONJUNCT1 (ASSUME
        `~(y = t) /\ ~(lookup_eq cs1 y = lookup_eq cs1 s)`)))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      USE_THEN "D2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;
let set_eq_remove_eq_models = prove
 (`CPstate_inv cs /\ CPstate_models cs (st:(A,C,FFI)wl_state) /\
   lookup s (wl_state_locals st) = SOME sval ==>
   CPstate_models (set_eq (remove_eq cs t) t s)
     (wl_state_locals_fupd (combin_K (insert t sval (wl_state_locals st))) st)`,
  STRIP_TAC THEN ASM_CASES_TAC `both_alloc_vars (t,s)` THENL
   [MATCH_MP_TAC copy_prop_move_model_aux THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[both_alloc_vars_def]) THEN
    ASM_REWRITE_TAC[set_eq_def] THEN MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] remove_eq_model_insert) THEN
    ASM_REWRITE_TAC[]]);;

let lookup_eq_idempotent = prove
 (`CPstate_inv cs ==> lookup_eq cs (lookup_eq cs x) = lookup_eq cs x`,
  DISCH_TAC THEN
  MP_TAC(SPECL [`cs:copy_state`; `x:num`] WPROOF2AUX_lookup_eq_cases) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cs:copy_state`; `c:num`; `r:num`] WPROOF2AUX_inv_rep) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[lookup_eq_def] THEN
  CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

let CPstate_modelsD_get_var = prove
 (`CPstate_inv cs /\ CPstate_models cs (st:(A,C,FFI)wl_state) ==>
   wl_get_var (lookup_eq cs x) st = wl_get_var x st`,
  STRIP_TAC THEN REWRITE_TAC[wl_get_var_def] THEN MATCH_MP_TAC CPstate_model THEN
  ASM_REWRITE_TAC[]);;

let CPstate_modelsD_get_vars = prove
 (`CPstate_inv cs /\ CPstate_models cs (st:(A,C,FFI)wl_state) ==>
   wl_get_vars (MAP (lookup_eq cs) xs) st = wl_get_vars xs st`,
  STRIP_TAC THEN SPEC_TAC(`xs:num list`,`xs:num list`) THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[MAP; wl_get_vars_def; CPstate_modelsD_get_var]);;

let CPstate_modelsD_get_var_imm = prove
 (`CPstate_inv cs /\ CPstate_models cs (st:(A,C,FFI)wl_state) ==>
   wl_get_var_imm (lookup_eq_imm cs x) st = wl_get_var_imm x st`,
  STRIP_TAC THEN CASES_ON `x:(A)reg_imm` THEN
  REWRITE_TAC[lookup_eq_imm_def] THEN CAKE_REWRITE_TAC[wl_get_var_imm_def] THEN
  ASM_SIMP_TAC[CPstate_modelsD_get_var]);;

let CPstate_modelsD_Var = prove
 (`CPstate_inv cs /\ CPstate_models cs (st:(A,C,FFI)wl_state) ==>
   wl_word_exp st (wl_Var (lookup_eq cs x)) = wl_word_exp st (wl_Var x)`,
  STRIP_TAC THEN REWRITE_TAC[wl_word_exp_def] THEN ASM_SIMP_TAC[CPstate_modelsD_get_var]);;

let CPstate_modelsD_lookup_eq_imm = prove
 (CASE_TERM
  `CPstate_inv cs ==>
   CPstate_models cs (st:(A,C,FFI)wl_state) ==>
   wl_word_exp st (match lookup_eq_imm cs x with Reg r -> wl_Var r | Imm w -> wl_Const w) =
   wl_word_exp st (match x with Reg r -> wl_Var r | Imm w -> wl_Const w)`,
  REPEAT STRIP_TAC THEN CASES_ON `x:(A)reg_imm` THEN
  REWRITE_TAC[lookup_eq_imm_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_word_exp_def] THEN ASM_SIMP_TAC[CPstate_modelsD_get_var]);;

let MAP_get_var_eqD = prove
 (`MAP (\x. wl_get_var x (st:(A,C,FFI)wl_state)) xx = MAP (\x. wl_get_var x st) yy ==>
   wl_get_vars xx st = wl_get_vars yy st`,
  SPEC_TAC(`yy:num list`,`yy:num list`) THEN SPEC_TAC(`xx:num list`,`xx:num list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11] THEN STRIP_TAC THEN
  REWRITE_TAC[wl_get_vars_def] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t':num list` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let WPROOF2AUX_cp_FORALL_PAIR_EQ_IMP = prove
 (`!(t:A#B) (Q:A->B->bool). (!x y. t = (x,y) ==> Q x y) <=> Q (FST t) (SND t)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

let WPROOF2AUX_cpm_CONS = prove
 (`!x y xs cs.
     copy_prop_move (CONS (x,y) xs) cs =
     (CONS (x,lookup_eq cs y) (FST (copy_prop_move xs cs)),
      set_eq (remove_eq (SND (copy_prop_move xs cs)) x) x y)`,
  REWRITE_TAC[copy_prop_move_def; LET_DEF; LET_END_DEF; pair_CASE_def]);;

let copy_prop_move_eval_aux1 = prove
 (`CPstate_inv cs ==>
   CPstate_models cs (st:(A,C,FFI)wl_state) ==>
   !moves' cs'.
     copy_prop_move moves cs = (moves', cs') ==>
     MAP (\x. wl_get_var x st) (MAP SND moves') =
     MAP (\x. wl_get_var x st) (MAP SND moves)`,
  REPEAT DISCH_TAC THEN SPEC_TAC(`moves:(num#num)list`,`moves:(num#num)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[copy_prop_move_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[WPROOF2AUX_cpm_CONS; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  RVEQ_TAC THEN REWRITE_TAC[MAP; CONS_11] THEN
  ASM_SIMP_TAC[CPstate_modelsD_get_var] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `SND (copy_prop_move t cs)` THEN REWRITE_TAC[PAIR]);;

let copy_prop_move_get_vars = prove
 (`CPstate_inv cs ==>
   CPstate_models cs (st:(A,C,FFI)wl_state) ==>
   copy_prop_move moves cs = (moves', cs') ==>
   wl_get_vars (MAP SND moves') st = wl_get_vars (MAP SND moves) st`,
  REPEAT DISCH_TAC THEN MATCH_MP_TAC MAP_get_var_eqD THEN
  MP_TAC copy_prop_move_eval_aux1 THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `cs':copy_state` THEN ASM_REWRITE_TAC[]);;

let copy_prop_move_eval_aux2 = prove
 (`MAP FST moves1 = MAP FST moves2 ==>
   wl_get_vars (MAP SND moves1) st = wl_get_vars (MAP SND moves2) st ==>
   wl_evaluate (wl_Move pri moves1, st:(A,C,FFI)wl_state) =
   wl_evaluate (wl_Move pri moves2, st)`,
  REPEAT DISCH_TAC THEN REWRITE_TAC[wl_evaluate_def] THEN ASM_REWRITE_TAC[]);;

let copy_prop_move_eval_aux3 = prove
 (`!moves' cs'.
     copy_prop_move moves cs = (moves', cs') ==> MAP FST moves' = MAP FST moves`,
  SPEC_TAC(`moves:(num#num)list`,`moves:(num#num)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[copy_prop_move_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[WPROOF2AUX_cpm_CONS; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  RVEQ_TAC THEN REWRITE_TAC[MAP; CONS_11] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `SND (copy_prop_move t cs)` THEN REWRITE_TAC[PAIR]);;

let copy_prop_move_eval = prove
 (`CPstate_inv cs ==>
   CPstate_models cs (st:(A,C,FFI)wl_state) ==>
   copy_prop_move moves cs = (moves', cs') ==>
   wl_evaluate (wl_Move pri moves, st) = (err, st') ==>
   wl_evaluate (wl_Move pri moves', st) = (err, st')`,
  REPEAT DISCH_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] copy_prop_move_eval_aux2) THEN CONJ_TAC THENL
   [MATCH_MP_TAC copy_prop_move_eval_aux3 THEN EXISTS_TAC `cs':copy_state` THEN
    ASM_REWRITE_TAC[];
    MP_TAC(INST [`moves:(num#num)list`,`moves:(num#num)list`] copy_prop_move_get_vars) THEN
    ASM_REWRITE_TAC[]]);;

let lookup_alist_insert_same = prove
 (`~(s IN set_of_list tt) ==>
   lookup s (alist_insert tt values (locals:A spt)) = lookup s locals`,
  SPEC_TAC(`values:A list`,`values:A list`) THEN
  SPEC_TAC(`tt:num list`,`tt:num list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[alist_insert_def] THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `values:A list` list_CASES) THEN
  REWRITE_TAC[alist_insert_def; set_of_list; IN_INSERT; DE_MORGAN_THM; lookup_insert] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;
let copy_prop_move_inv = prove
 (`CPstate_inv cs ==> copy_prop_move moves cs = (moves', cs') ==> CPstate_inv cs'`,
  DISCH_TAC THEN SPEC_TAC(`cs':copy_state`,`cs':copy_state`) THEN
  SPEC_TAC(`moves':(num#num)list`,`moves':(num#num)list`) THEN
  SPEC_TAC(`moves:(num#num)list`,`moves:(num#num)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[copy_prop_move_def; PAIR_EQ] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[WPROOF2AUX_cpm_CONS; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  MATCH_MP_TAC set_eq_inv THEN REWRITE_TAC[WPROOF2AUX_remove_eq_t] THEN
  MATCH_MP_TAC remove_eq_inv THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `FST (copy_prop_move t cs)` THEN REWRITE_TAC[PAIR]);;

let copy_prop_inst_inv = prove
 (`CPstate_inv cs ==> copy_prop_inst (ins:(A)inst) cs = (prog', cs') ==> CPstate_inv cs'`,
  SUBGOAL_THEN `!(ins:(A)inst) cs. CPstate_inv cs ==> CPstate_inv (SND (copy_prop_inst ins cs))`
    (fun th -> MESON_TAC[th; SND]) THEN
  MATCH_MP_TAC copy_prop_inst_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[copy_prop_inst_def; LET_DEF; LET_END_DEF] THEN
  CAKE_REWRITE_TAC[pair_CASE_def; FST; SND] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[FST; SND] THEN
  MESON_TAC[remove_eq_inv; remove_eqs_inv]);;

let copy_prop_prog_inv = prove
 (`CPstate_inv cs /\ copy_prop_prog (prog:(A)wl_prog) cs = (prog', cs') ==>
   CPstate_inv cs'`,
  SUBGOAL_THEN `!(prog:(A)wl_prog) cs. CPstate_inv cs ==>
                  CPstate_inv (SND (copy_prop_prog prog cs))`
    (fun th -> MESON_TAC[th; SND]) THEN
  MATCH_MP_TAC copy_prop_prog_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WPROOF2AUX_cp_FORALL_PAIR_EQ_IMP]) THEN
  REWRITE_TAC[copy_prop_prog_def; LET_DEF; LET_END_DEF] THEN
  CAKE_REWRITE_TAC[pair_CASE_def; FST; SND] THEN
  REPEAT (FIRST [COND_CASES_TAC; TOP_CASE_TAC]) THEN
  CAKE_REWRITE_TAC[pair_CASE_def; FST; SND] THEN
  ASM_SIMP_TAC[empty_eq_inv; remove_eq_inv; remove_eqs_inv; set_store_eq_inv] THEN
  TRY (MATCH_MP_TAC merge_eqs_inv THEN ASM_SIMP_TAC[] THEN NO_TAC) THEN
  ASM_MESON_TAC[copy_prop_move_inv; copy_prop_inst_inv; PAIR]);;

let empty_eq_model = prove
 (`CPstate_models empty_eq (st:(A,C,FFI)wl_state)`,
  REWRITE_TAC[CPstate_models_def; empty_eq_def; WPROOF2AUX_cs_acc; lookup_def;
              ALOOKUP_THM; option_DISTINCT]);;
let WPROOF2AUX_get_vars_CONS = prove
 (`!v vs (st:(A,C,FFI)wl_state) values.
     wl_get_vars (CONS v vs) st = SOME values <=>
     ?x xs. values = CONS x xs /\ wl_get_var v st = SOME x /\ wl_get_vars vs st = SOME xs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wl_get_vars_def] THEN
  MP_TAC(ISPEC `wl_get_var v (st:(A,C,FFI)wl_state)` (nchotomy_of_type `:((A)word_loc)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN CAKE_REWRITE_TAC[option_DISTINCT] THEN
  MP_TAC(ISPEC `wl_get_vars vs (st:(A,C,FFI)wl_state)` (nchotomy_of_type `:(((A)word_loc)list)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN CAKE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;

let copy_prop_move_model = prove
 (`CPstate_inv cs ==>
   CPstate_models cs (st:(A,C,FFI)wl_state) ==>
   set_of_list (MAP FST moves) INTER set_of_list (MAP SND moves) = {} ==>
   copy_prop_move moves cs = (moves',cs') ==>
   wl_get_vars (MAP SND moves) st = SOME values ==>
   CPstate_models cs' (wl_set_vars (MAP FST moves) values st)`,
  REWRITE_TAC[IMP_IMP] THEN
  SPEC_TAC(`values:((A)word_loc)list`,`values:((A)word_loc)list`) THEN
  SPEC_TAC(`cs':copy_state`,`cs':copy_state`) THEN
  SPEC_TAC(`moves':(num#num)list`,`moves':(num#num)list`) THEN
  SPEC_TAC(`moves:(num#num)list`,`moves:(num#num)list`) THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAP; wl_get_vars_def; copy_prop_move_def; PAIR_EQ; option_INJ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[wl_set_vars_def; alist_insert_def] THEN
    MATCH_MP_TAC CPstate_models_same THEN
    ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  SPEC_TAC(`h:num#num`,`h:num#num`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`t0:num`; `s0:num`] THEN
  REWRITE_TAC[MAP; WPROOF2AUX_cpm_CONS; PAIR_EQ; WPROOF2AUX_get_vars_CONS] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`FST (copy_prop_move t cs)`; `SND (copy_prop_move t cs)`;
                                `xs:((A)word_loc)list`] o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[PAIR] THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `{}:num->bool`)) THEN
    REWRITE_TAC[set_of_list] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(s0 IN set_of_list (MAP FST (t:(num#num)list)))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `{}:num->bool`)) THEN
    REWRITE_TAC[set_of_list] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(INST [`SND (copy_prop_move t cs)`,`cs:copy_state`;
               `wl_set_vars (MAP FST (t:(num#num)list)) xs (st:(A,C,FFI)wl_state)`,
               `st:(A,C,FFI)wl_state`; `x:(A)word_loc`,`sval:(A)word_loc`;
               `t0:num`,`t:num`; `s0:num`,`s:num`]
              set_eq_remove_eq_models) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(INST [`t:(num#num)list`,`moves:(num#num)list`;
                    `FST (copy_prop_move t cs)`,`moves':(num#num)list`;
                    `SND (copy_prop_move t cs)`,`cs':copy_state`] copy_prop_move_inv) THEN
      ASM_REWRITE_TAC[PAIR];
      REWRITE_TAC[wl_set_vars_def; wl_state_INFO.ri_accfupds; K_THM] THEN
      ASM_SIMP_TAC[lookup_alist_insert_same] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[wl_set_vars_def; wl_state_INFO.ri_accfupds; K_THM;
              wl_state_INFO.ri_fupdfupds; o_THM; alist_insert_def] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; K_THM]);;

let EVERY_NOT_MEM_D = prove
 (`ALL (\t. ~MEM t ss) (tt:A list) ==> set_of_list tt INTER set_of_list ss = {}`,
  REWRITE_TAC[GSYM ALL_MEM; EXTENSION; IN_INTER; IN_SET_OF_LIST; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let copy_prop_move_correct = prove
 (`CPstate_inv cs /\
   CPstate_models cs (st:(A,C,FFI)wl_state) /\
   copy_prop_prog (wl_Move pri moves) cs = (prog', cs') /\
   wl_evaluate (wl_Move pri moves, st) = (err, st') ==>
   wl_evaluate (prog', st) = (err, st') /\
   (err = NONE ==> CPstate_models cs' st')`,
  REWRITE_TAC[copy_prop_prog_def; LET_DEF; LET_END_DEF] THEN
  CAKE_REWRITE_TAC[pair_CASE_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(INST [`FST (copy_prop_move moves cs)`,`moves':(num#num)list`;
                   `SND (copy_prop_move moves cs)`,`cs':copy_state`] copy_prop_move_eval) THEN
      ASM_REWRITE_TAC[PAIR];
      ALL_TAC] THEN
    DISCH_TAC THEN RVEQ_TAC THEN
    UNDISCH_TAC `wl_evaluate (wl_Move pri (moves:(num#num)list),st:(A,C,FFI)wl_state) = (NONE,st')` THEN
    REWRITE_TAC[wl_evaluate_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN
    MP_TAC(ISPEC `wl_get_vars (MAP SND (moves:(num#num)list)) (st:(A,C,FFI)wl_state)`
             (nchotomy_of_type `:(((A)word_loc)list)option`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(INST [`FST (copy_prop_move moves cs)`,`moves':(num#num)list`;
                 `SND (copy_prop_move moves cs)`,`cs':copy_state`;
                 `a:((A)word_loc)list`,`values:((A)word_loc)list`] copy_prop_move_model) THEN
    ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC EVERY_NOT_MEM_D THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[empty_eq_model]]);;

let word_exp_cong_Var = prove
 (`wl_get_var x' (st:(A,C,FFI)wl_state) = wl_get_var x st ==>
   wl_word_exp st (wl_Var x') = wl_word_exp st (wl_Var x)`,
  REWRITE_TAC[wl_word_exp_def]);;

let word_exp_cong_Load = prove
 (`wl_word_exp (st:(A,C,FFI)wl_state) addr' = wl_word_exp st addr ==>
   wl_word_exp st (wl_Load addr') = wl_word_exp st (wl_Load addr)`,
  SIMP_TAC[wl_word_exp_def]);;

let word_exp_cong_Op = prove
 (`MAP (wl_word_exp (st:(A,C,FFI)wl_state)) aa' = MAP (wl_word_exp st) aa ==>
   wl_word_exp st (wl_Op op aa') = wl_word_exp st (wl_Op op aa)`,
  SIMP_TAC[wl_word_exp_def]);;

let word_exp_cong_Shift = prove
 (`wl_word_exp (st:(A,C,FFI)wl_state) e' = wl_word_exp st e ==>
   wl_word_exp st e2' = wl_word_exp st e2 ==>
   wl_word_exp st (wl_Shift sh e' e2') = wl_word_exp st (wl_Shift sh e e2)`,
  SIMP_TAC[wl_word_exp_def]);;

let copy_prop_inst_eval = prove
 (`!ins cs (st:(A,C,FFI)wl_state) prog' cs'.
     CPstate_inv cs ==>
     CPstate_models cs st ==>
     (prog', cs') = copy_prop_inst ins cs ==>
     wl_evaluate (prog', st) = wl_evaluate (wl_Inst ins, st)`,
  MATCH_MP_TAC copy_prop_inst_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  (SUBGOAL_THEN `!x. wl_get_var (lookup_eq cs x) (st:(A,C,FFI)wl_state) = wl_get_var x st`
    ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CPstate_modelsD_get_var THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN (CASE_TERM `!x:(A)reg_imm. wl_word_exp (st:(A,C,FFI)wl_state)
       (match lookup_eq_imm cs x with Reg r -> wl_Var r | Imm w -> wl_Const w) =
     wl_word_exp st (match x with Reg r -> wl_Var r | Imm w -> wl_Const w)`) ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] CPstate_modelsD_lookup_eq_imm) THEN
    ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(MP_TAC o SYM) THEN
  REWRITE_TAC[copy_prop_inst_def; LET_DEF; LET_END_DEF] THEN
  CAKE_REWRITE_TAC[pair_CASE_def; FST; SND] THEN
  REPEAT COND_CASES_TAC THEN CAKE_REWRITE_TAC[FST; SND; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[wl_evaluate_def; wl_inst_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_assign_def; wl_word_exp_def; MAP; wl_get_vars_def] THEN
  ASM_REWRITE_TAC[]);;

let remove_eq_comm = prove
 (`remove_eq (remove_eq cs x) y = remove_eq (remove_eq cs y) x`,
  REWRITE_TAC[remove_eq_def] THEN
  MP_TAC(ISPEC `lookup x (copy_state_to_eq cs)` (nchotomy_of_type `:(num)option`)) THEN
  MP_TAC(ISPEC `lookup y (copy_state_to_eq cs)` (nchotomy_of_type `:(num)option`)) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[empty_eq_def; WPROOF2AUX_cs_acc; lookup_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

let WPROOF2AUX_models_mem = prove
 (`!f. CPstate_models cs (st:(A,C,FFI)wl_state) ==>
       CPstate_models cs (wl_state_memory_fupd f st)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CPstate_models_same THEN
  ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds]);;

let WPROOF2AUX_MODEL_TAC : tactic =
  REPEAT(FIRST
   [FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] remove_eq_model_set_var) THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC remove_eq_inv) THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC];
    MATCH_MP_TAC set_fp_var_model;
    MATCH_MP_TAC WPROOF2AUX_models_mem;
    MATCH_MP_TAC remove_eq_model]);;


let WPROOF2AUX_copy_prop_inst_model = prove
 (`!ins cs (st:(A,C,FFI)wl_state) st'.
     CPstate_inv cs ==> CPstate_models cs st ==>
     wl_inst ins st = SOME st' ==>
     CPstate_models (SND (copy_prop_inst ins cs)) st'`,
  MATCH_MP_TAC copy_prop_inst_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[copy_prop_inst_def; LET_DEF; LET_END_DEF] THEN
  CAKE_REWRITE_TAC[pair_CASE_def; FST; SND] THEN
  REWRITE_TAC[wl_inst_def; remove_eqs_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_assign_def; wl_mem_store_def] THEN DISCH_TAC THEN
  GVS(all_case_eqs()) THEN WPROOF2AUX_MODEL_TAC);;

let copy_prop_inst_correct = prove
 (`CPstate_inv cs /\
   CPstate_models cs (st:(A,C,FFI)wl_state) /\
   copy_prop_inst ins cs = (prog', cs') /\
   wl_evaluate (wl_Inst ins, st) = (err, st') ==>
   wl_evaluate (prog', st) = (err, st') /\
   (err = NONE ==> CPstate_models cs' st')`,
  STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`ins:(A)inst`; `cs:copy_state`; `st:(A,C,FFI)wl_state`;
                  `prog':(A)wl_prog`; `cs':copy_state`] copy_prop_inst_eval) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN RVEQ_TAC THEN
    UNDISCH_TAC `wl_evaluate (wl_Inst ins,st:(A,C,FFI)wl_state) = (NONE,st')` THEN
    REWRITE_TAC[wl_evaluate_def] THEN
    MP_TAC(ISPEC `wl_inst (ins:(A)inst) (st:(A,C,FFI)wl_state)`
             (nchotomy_of_type `:((A,C,FFI)wl_state)option`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(SPECL [`ins:(A)inst`; `cs:copy_state`; `st:(A,C,FFI)wl_state`;
                  `a:(A,C,FFI)wl_state`] WPROOF2AUX_copy_prop_inst_model) THEN
    ASM_REWRITE_TAC[SND]]);;

let remove_eq_model_unset_var = prove
 (`CPstate_inv cs ==>
   CPstate_models cs (st:(A,C,FFI)wl_state) ==>
   CPstate_models (remove_eq cs t) (wl_unset_var t st)`,
  REPEAT DISCH_TAC THEN REWRITE_TAC[remove_eq_def] THEN
  MP_TAC(ISPEC `lookup t (copy_state_to_eq cs)` (nchotomy_of_type `:(num)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[empty_eq_model] THEN
  UNDISCH_TAC `CPstate_models cs (st:(A,C,FFI)wl_state)` THEN
  UNDISCH_TAC `CPstate_inv cs` THEN
  REWRITE_TAC[CPstate_models_def; CPstate_inv_def; wl_unset_var_def;
              wl_state_INFO.ri_accfupds; K_THM; lookup_delete] THEN
  REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_MESON_TAC[option_DISTINCT]);;

let CPstate_modelsD_copy_prop_share = prove
 (`CPstate_inv cs ==>
   CPstate_models cs (st:(A,C,FFI)wl_state) ==>
   wl_word_exp st (copy_prop_share e cs) = wl_word_exp st e`,
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `!x. wl_get_var (lookup_eq cs x) (st:(A,C,FFI)wl_state) = wl_get_var x st`
    ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CPstate_modelsD_get_var THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[copy_prop_share_def] THEN EVERY_CASE_TAC THEN
  ASM_REWRITE_TAC[wl_word_exp_def; MAP]);;

let lookup_store_eq_SOME = prove
 (`CPstate_models cs (st:(A,C,FFI)wl_state) /\ lookup_store_eq cs s = SOME v ==>
   FLOOKUP (wl_state_store st) s = lookup v (wl_state_locals st)`,
  REWRITE_TAC[CPstate_models_def; lookup_store_eq_def] THEN
  MP_TAC(ISPEC `ALOOKUP (copy_state_store_to_eq cs) s` (nchotomy_of_type `:(num)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[option_DISTINCT] THEN
  MP_TAC(ISPEC `lookup a (copy_state_from_eq cs)` (nchotomy_of_type `:(num)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  ASM_MESON_TAC[]);;

let lookup_remove_eq = prove
 (`lookup n (copy_state_to_eq (remove_eq cs n)) = NONE`,
  REWRITE_TAC[remove_eq_def] THEN
  MP_TAC(ISPEC `lookup n (copy_state_to_eq cs)` (nchotomy_of_type `:(num)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[empty_eq_def; WPROOF2AUX_cs_acc; lookup_def]);;

let _ = cake_add_simps [lookup_remove_eq];;

let WPROOF2AUX_set_store_eq_cases = prove
 (`!cs s y.
     is_alloc_var y ==>
     ((lookup y (copy_state_to_eq cs) = NONE \/
       ?c. lookup y (copy_state_to_eq cs) = SOME c /\
           lookup c (copy_state_from_eq cs) = NONE) /\
      set_store_eq cs s y =
      copy_state_REC
        (insert y (copy_state_next cs) (copy_state_to_eq cs))
        (insert (copy_state_next cs) y (copy_state_from_eq cs))
        (CONS (s,copy_state_next cs) (copy_state_store_to_eq cs))
        (copy_state_next cs + 1)) \/
     (?c r. lookup y (copy_state_to_eq cs) = SOME c /\
            lookup c (copy_state_from_eq cs) = SOME r /\
            set_store_eq cs s y =
            copy_state_store_to_eq_fupd
              (combin_K (CONS (s,c) (copy_state_store_to_eq cs))) cs)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[set_store_eq_def] THEN
  MP_TAC(ISPEC `lookup y (copy_state_to_eq cs)` (nchotomy_of_type `:(num)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN CAKE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[nchotomy_of_type `:(num)option`]);;

let WPROOF2AUX_lookup_eq_store_fupd = prove
 (`!f cs y. lookup_eq (copy_state_store_to_eq_fupd f cs) y = lookup_eq cs y`,
  REWRITE_TAC[lookup_eq_def; copy_state_INFO.ri_accfupds]);;

let WPROOF2AUX_lookup_eq_fresh = prove
 (`!cs x st n y.
     CPstate_inv cs /\ lookup_eq cs x = x ==>
     lookup_eq (copy_state_REC (insert x (copy_state_next cs) (copy_state_to_eq cs))
                  (insert (copy_state_next cs) x (copy_state_from_eq cs)) st n) y =
     lookup_eq cs y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WPROOF2AUX_lookup_eq_REC; lookup_insert] THEN
  ASM_CASES_TAC `y:num = x` THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[lookup_eq_def] THEN
  MP_TAC(ISPEC `lookup y (copy_state_to_eq cs)` (nchotomy_of_type `:(num)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(a = copy_state_next cs)` (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[WPROOF2AUX_inv_class; LT_REFL]);;

let lookup_eq_set_store_eq = prove
 (`CPstate_inv cs /\ is_alloc_var x ==>
   lookup_eq (set_store_eq cs s x) y = lookup_eq cs y`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`cs:copy_state`; `s:store_name`; `x:num`] WPROOF2AUX_set_store_eq_cases) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[WPROOF2AUX_lookup_eq_store_fupd] THEN
  MATCH_MP_TAC WPROOF2AUX_lookup_eq_fresh THEN
  ASM_REWRITE_TAC[lookup_eq_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

let WPROOF2AUX_lookup_store_eq_store_fupd = prove
 (CASE_TERM
  `!l cs v.
     lookup_store_eq (copy_state_store_to_eq_fupd (combin_K l) cs) v =
     (match ALOOKUP l v with
        NONE -> NONE
      | SOME c -> (match lookup c (copy_state_from_eq cs) with
                     NONE -> NONE | SOME v' -> SOME v'))`,
  REWRITE_TAC[lookup_store_eq_def; copy_state_INFO.ri_accfupds; K_THM]);;

let lookup_store_eq_set_store_eq_1 = prove
 (`CPstate_inv cs /\ is_alloc_var x /\
   lookup_store_eq (set_store_eq cs s x) s = SOME y ==>
   lookup_eq cs x = lookup_eq cs y`,
  STRIP_TAC THEN
  UNDISCH_TAC `lookup_store_eq (set_store_eq cs s x) s = SOME y` THEN
  MP_TAC(SPECL [`cs:copy_state`; `s:store_name`; `x:num`] WPROOF2AUX_set_store_eq_cases) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[WPROOF2AUX_lookup_store_eq_REC; WPROOF2AUX_lookup_store_eq_store_fupd;
                  ALOOKUP_THM; lookup_insert] THEN
  CAKE_REWRITE_TAC[option_INJ] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `lookup r (copy_state_to_eq cs) = SOME c` ASSUME_TAC THENL
   [ASM_MESON_TAC[WPROOF2AUX_inv_rep]; ALL_TAC] THEN
  ASM_REWRITE_TAC[lookup_eq_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]);;

let lookup_store_eq_set_store_eq_2 = prove
 (`CPstate_inv cs /\ is_alloc_var x /\ ~(s = t) /\
   lookup_store_eq (set_store_eq cs s x) t = SOME y ==>
   lookup_store_eq cs t = SOME y`,
  STRIP_TAC THEN
  SUBGOAL_THEN `~(t:store_name = s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `lookup_store_eq (set_store_eq cs s x) t = SOME y` THEN
  MP_TAC(SPECL [`cs:copy_state`; `s:store_name`; `x:num`] WPROOF2AUX_set_store_eq_cases) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[WPROOF2AUX_lookup_store_eq_REC; WPROOF2AUX_lookup_store_eq_store_fupd;
                  ALOOKUP_THM] THEN
  REWRITE_TAC[lookup_store_eq_def] THEN
  MP_TAC(ISPEC `ALOOKUP (copy_state_store_to_eq cs) t` (nchotomy_of_type `:(num)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[option_DISTINCT] THEN
  SUBGOAL_THEN `~(a = copy_state_next cs)` (fun th -> REWRITE_TAC[th; lookup_insert]) THEN
  UNDISCH_TAC `CPstate_inv cs` THEN REWRITE_TAC[CPstate_inv_def] THEN
  ASM_MESON_TAC[LT_REFL]);;

let set_store_eq_model_set_store = prove
 (`CPstate_inv cs /\ CPstate_models cs (st:(A,C,FFI)wl_state) /\
   wl_get_var n st = SOME w ==>
   CPstate_models (set_store_eq cs s n) (wl_set_store s w st)`,
  STRIP_TAC THEN ASM_CASES_TAC `is_alloc_var n` THENL
   [ALL_TAC; ASM_REWRITE_TAC[set_store_eq_def; empty_eq_model]] THEN
  MP_TAC(INST [`st:(A,C,FFI)wl_state`,`st:(A,C,FFI)wl_state`] CPstate_modelsD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "D1") (LABEL_TAC "D2")) THEN
  MATCH_MP_TAC CPstate_modelsI THEN
  ASM_SIMP_TAC[set_store_eq_inv; lookup_eq_set_store_eq] THEN
  REWRITE_TAC[wl_set_store_def; wl_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE] THEN
  CONJ_TAC THENL [USE_THEN "D1" ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:store_name`; `y:num`] THEN
  ASM_CASES_TAC `s:store_name = x` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [MP_TAC(INST [`n:num`,`x:num`; `x:store_name`,`s:store_name`;
                 `lookup_eq cs y`,`y:num`] lookup_store_eq_set_store_eq_1) THEN
    ASM_SIMP_TAC[lookup_eq_idempotent] THEN DISCH_TAC THEN
    TRANS_TAC EQ_TRANS `lookup n (wl_state_locals (st:(A,C,FFI)wl_state))` THEN
    CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN ASM_REWRITE_TAC[];
      REMOVE_THEN "D1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REMOVE_THEN "D2" MATCH_MP_TAC THEN
    MATCH_MP_TAC(INST [`n:num`,`x:num`; `x:store_name`,`t:store_name`;
                       `lookup_eq cs y`,`y:num`] lookup_store_eq_set_store_eq_2) THEN
    ASM_REWRITE_TAC[]]);;

let lookup_eq_remove_t_same = prove
 (`lookup_eq (remove_eq cs t) t = t`,
  REWRITE_TAC[lookup_eq_def; lookup_remove_eq] THEN CAKE_REWRITE_TAC[]);;

let lookup_store_eq_set_store_eq_same = prove
 (`lookup x (copy_state_to_eq cs) = NONE /\ is_alloc_var x ==>
   lookup_store_eq (set_store_eq cs s x) s = SOME x`,
  STRIP_TAC THEN ASM_REWRITE_TAC[set_store_eq_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[WPROOF2AUX_lookup_store_eq_REC; ALOOKUP_THM; lookup_insert] THEN
  CAKE_REWRITE_TAC[]);;

let set_store_eq_model_set_var = prove
 (`CPstate_inv cs /\ CPstate_models cs (st:(A,C,FFI)wl_state) /\
   lookup_store_eq cs s = NONE /\ wl_get_store s st = SOME w ==>
   CPstate_models (set_store_eq (remove_eq cs n) s n) (wl_set_var n w st)`,
  STRIP_TAC THEN ASM_CASES_TAC `is_alloc_var n` THENL
   [ALL_TAC; ASM_REWRITE_TAC[set_store_eq_def; empty_eq_model]] THEN
  SUBGOAL_THEN `CPstate_inv (remove_eq cs n)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[remove_eq_inv]; ALL_TAC] THEN
  MP_TAC(INST [`n:num`,`t:num`; `w:(A)word_loc`,`vv:(A)word_loc`]
           remove_eq_model_set_var) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(INST [`remove_eq cs n`,`cs:copy_state`;
               `wl_set_var n (w:(A)word_loc) (st:(A,C,FFI)wl_state)`,`st:(A,C,FFI)wl_state`]
           CPstate_modelsD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "D1") (LABEL_TAC "D2")) THEN
  MATCH_MP_TAC CPstate_modelsI THEN
  ASM_SIMP_TAC[set_store_eq_inv; lookup_eq_set_store_eq] THEN
  CONJ_TAC THENL [USE_THEN "D1" ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:store_name`; `y:num`] THEN
  ASM_CASES_TAC `s:store_name = x` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:store_name = x`)) THEN
    MP_TAC(INST [`n:num`,`x:num`; `remove_eq cs n`,`cs:copy_state`; `x:store_name`,`s:store_name`]
             lookup_store_eq_set_store_eq_same) THEN
    ASM_REWRITE_TAC[lookup_remove_eq] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[option_INJ] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
    SUBGOAL_THEN `y:num = n` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC WPROOF2AUX_lookup_eq_unclassified THEN
      EXISTS_TAC `remove_eq cs n` THEN ASM_REWRITE_TAC[lookup_remove_eq];
      ALL_TAC] THEN
    UNDISCH_TAC `wl_get_store x (st:(A,C,FFI)wl_state) = SOME w` THEN
    REWRITE_TAC[wl_get_store_def; wl_set_var_def; wl_state_INFO.ri_accfupds; K_THM;
                lookup_insert] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    DISCH_TAC THEN REMOVE_THEN "D2" MATCH_MP_TAC THEN
    MATCH_MP_TAC(INST [`n:num`,`x:num`; `remove_eq cs n`,`cs:copy_state`;
                       `x:store_name`,`t:store_name`;
                       `lookup_eq (remove_eq cs n) y`,`y:num`] lookup_store_eq_set_store_eq_2) THEN
    ASM_REWRITE_TAC[]]);;

let WPROOF2AUX_cp_eval_clause (c:string) =
  find (fun th -> let l = lhs (snd (strip_forall (concl th))) in
                  let p = fst (dest_pair (rand l)) in
                  fst (dest_const (fst (strip_comb p))) = c)
       (CONJUNCTS wl_evaluate_def);;

let evaluate_Loop_body_cong_err = prove
 (`!(s:(A,C,FFI)wl_state) names c c' exit_names res s'.
     (!(v:(A,C,FFI)wl_state) res s'.
        wl_evaluate (c, v) = (res, s') /\ ~(res = SOME wl_Error) ==>
        wl_evaluate (c', v) = (res, s')) /\
     wl_evaluate (wl_Loop names c exit_names, s) = (res, s') /\
     ~(res = SOME wl_Error) ==>
     wl_evaluate (wl_Loop names c' exit_names, s) = (res, s')`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SPEC_TAC(`s':(A,C,FFI)wl_state`,`s1:(A,C,FFI)wl_state`) THEN
  SPEC_TAC(`res:((A)wl_result)option`,`res:((A)wl_result)option`) THEN
  SPEC_TAC(`s:(A,C,FFI)wl_state`,`s:(A,C,FFI)wl_state`) THEN
  SUBGOAL_THEN
   `!n (s:(A,C,FFI)wl_state) res s1. wl_state_clock s = n ==>
      wl_evaluate (wl_Loop names c exit_names, s) = (res, s1) /\
      ~(res = SOME wl_Error) ==>
      wl_evaluate (wl_Loop names c' exit_names, s) = (res, s1)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`s:(A,C,FFI)wl_state`; `res:((A)wl_result)option`;
                       `s1:(A,C,FFI)wl_state`] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[WPROOF2AUX_cp_eval_clause "wl_Loop"] THEN
  CASES_ON `wl_cut_state (names,LN) (s:(A,C,FFI)wl_state)` THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THENL [MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `wl_evaluate (c:(A)wl_prog,a:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)wl_result)option` (X_CHOOSE_THEN `t:(A,C,FFI)wl_state`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(r = SOME (wl_Error:(A)wl_result))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
    SIMP[wl_cont_loop_def; wl_exit_loop_def; PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wl_evaluate (c':(A)wl_prog,a:(A,C,FFI)wl_state) = (r,t)` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[pair_CASE] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_STOP_def] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `wl_state_clock (wl_dec_clock (t:(A,C,FFI)wl_state))` o
                check (fun th -> is_forall (concl th) &&
                                 type_of (fst (dest_forall (concl th))) = `:num`)) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `wl_state_clock (a:(A,C,FFI)wl_state) = wl_state_clock (s:(A,C,FFI)wl_state)`
      ASSUME_TAC THENL
     [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP cut_state_const) THEN ASM_REWRITE_TAC[] THEN
      SIMP[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP wl_evaluate_clock o
                check (fun th -> concl th = `wl_evaluate (c:(A)wl_prog,a:(A,C,FFI)wl_state) =
                                             (r,t)`)) THEN
    REWRITE_TAC[wl_dec_clock_def] THEN SIMP[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`wl_dec_clock (t:(A,C,FFI)wl_state)`;
                             `res:((A)wl_result)option`; `s1:(A,C,FFI)wl_state`]) THEN
  ASM_REWRITE_TAC[]);;

(* copy_prop_correct is proved by WF induction on the program size, one     *)
(* lemma per program form: WPROOF2AUX_cpc p is the statement for p          *)

let WPROOF2AUX_cpc (p:term) : term =
  vsubst [p,`prog:(A)wl_prog`]
   `!cs (st:(A,C,FFI)wl_state) prog' cs' err st'.
      CPstate_inv cs /\ CPstate_models cs st /\
      copy_prop_prog (prog:(A)wl_prog) cs = (prog', cs') /\
      ~(err = SOME wl_Error) /\ wl_evaluate (prog, st) = (err, st') ==>
      wl_evaluate (prog', st) = (err, st') /\ (err = NONE ==> CPstate_models cs' st')`;;

let WPROOF2AUX_cpc_id = prove
 (mk_imp(`!cs. copy_prop_prog (prog:(A)wl_prog) cs = (prog, empty_eq)`,
         WPROOF2AUX_cpc `prog:(A)wl_prog`),
  DISCH_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[empty_eq_model]);;

let WPROOF2AUX_cpc_trivial = prove
 (list_mk_conj (map WPROOF2AUX_cpc
   [`wl_Call ret dest args handler:(A)wl_prog`; `wl_Alloc r live:(A)wl_prog`;
    `wl_Install r1 r2 r3 r4 live:(A)wl_prog`; `wl_FFI i r1 r2 r3 r4 live:(A)wl_prog`;
    `wl_Assign v exp:(A)wl_prog`; `wl_Store exp v:(A)wl_prog`]),
  REPEAT CONJ_TAC THEN MATCH_MP_TAC WPROOF2AUX_cpc_id THEN
  REWRITE_TAC[copy_prop_prog_def]);;

let WPROOF2AUX_cpc_Skip = prove
 (WPROOF2AUX_cpc `wl_Skip:(A)wl_prog`,
  REWRITE_TAC[copy_prop_prog_def; wl_evaluate_def; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[wl_evaluate_def]);;

let WPROOF2AUX_cpc_Break_Continue = prove
 (mk_conj(WPROOF2AUX_cpc `wl_Break k:(A)wl_prog`, WPROOF2AUX_cpc `wl_Continue k:(A)wl_prog`),
  REWRITE_TAC[copy_prop_prog_def; wl_evaluate_def; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[wl_evaluate_def] THEN
  REWRITE_TAC[option_DISTINCT]);;

let WPROOF2AUX_cpc_Move = prove
 (WPROOF2AUX_cpc `wl_Move pri moves:(A)wl_prog`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC copy_prop_move_correct THEN
  ASM_REWRITE_TAC[]);;

let WPROOF2AUX_cpc_Inst = prove
 (WPROOF2AUX_cpc `wl_Inst i:(A)wl_prog`,
  REWRITE_TAC[copy_prop_prog_def] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(INST [`i:(A)inst`,`ins:(A)inst`] copy_prop_inst_correct) THEN
  ASM_REWRITE_TAC[]);;

(* substitute the outputs prog' and cs' of copy_prop_prog (RVEQ_TAC could  *)
(* eliminate cs instead of cs')                                             *)

let WPROOF2AUX_cp_SUBST_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    let c = concl th in
    is_eq c && is_var (rhs c) && mem (fst(dest_var(rhs c))) ["prog'"; "cs'"] &&
    not (is_var (lhs c) && mem (fst(dest_var(lhs c))) ["prog'"; "cs'"]))));;

let WPROOF2AUX_cpc_Return = prove
 (WPROOF2AUX_cpc `wl_Return v1 v2:(A)wl_prog`,
  REWRITE_TAC[copy_prop_prog_def; LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN WPROOF2AUX_cp_SUBST_TAC THEN
  SUBGOAL_THEN `wl_evaluate (wl_Return (lookup_eq cs v1) (MAP (lookup_eq cs) v2),
                             st:(A,C,FFI)wl_state) =
                wl_evaluate (wl_Return v1 v2, st)` SUBST1_TAC THENL
   [REWRITE_TAC[wl_evaluate_def] THEN
    ASM_SIMP_TAC[CPstate_modelsD_get_var; CPstate_modelsD_get_vars]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `wl_evaluate (wl_Return v1 v2,st:(A,C,FFI)wl_state) = (NONE,st')` THEN
  REWRITE_TAC[wl_evaluate_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ; option_DISTINCT]);;

let WPROOF2AUX_cpc_Raise = prove
 (WPROOF2AUX_cpc `wl_Raise v:(A)wl_prog`,
  REWRITE_TAC[copy_prop_prog_def; LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN WPROOF2AUX_cp_SUBST_TAC THEN
  SUBGOAL_THEN `wl_evaluate (wl_Raise (lookup_eq cs v), st:(A,C,FFI)wl_state) =
                wl_evaluate (wl_Raise v, st)` SUBST1_TAC THENL
   [REWRITE_TAC[wl_evaluate_def] THEN ASM_SIMP_TAC[CPstate_modelsD_get_var]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `wl_evaluate (wl_Raise v,st:(A,C,FFI)wl_state) = (NONE,st')` THEN
  REWRITE_TAC[wl_evaluate_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ; option_DISTINCT]);;

let WPROOF2AUX_cpc_Tick = prove
 (WPROOF2AUX_cpc `wl_Tick:(A)wl_prog`,
  REWRITE_TAC[copy_prop_prog_def; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN WPROOF2AUX_cp_SUBST_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `wl_evaluate (wl_Tick,st:(A,C,FFI)wl_state) = (NONE,st')` THEN
  REWRITE_TAC[wl_evaluate_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC CPstate_models_same THEN
  ASM_REWRITE_TAC[wl_dec_clock_def; wl_state_INFO.ri_accfupds]);;

let WPROOF2AUX_cpc_LocValue = prove
 (WPROOF2AUX_cpc `wl_LocValue r l1:(A)wl_prog`,
  REWRITE_TAC[copy_prop_prog_def; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN WPROOF2AUX_cp_SUBST_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `wl_evaluate (wl_LocValue r l1,st:(A,C,FFI)wl_state) = (NONE,st')` THEN
  REWRITE_TAC[wl_evaluate_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] remove_eq_model_set_var) THEN ASM_REWRITE_TAC[]);;

let WPROOF2AUX_cpc_BufferWrite = prove
 (mk_conj(WPROOF2AUX_cpc `wl_CodeBufferWrite r1 r2:(A)wl_prog`,
          WPROOF2AUX_cpc `wl_DataBufferWrite r1 r2:(A)wl_prog`),
  CONJ_TAC THEN
  REWRITE_TAC[copy_prop_prog_def; LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN WPROOF2AUX_cp_SUBST_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_comb(lhs(concl th)) &&
     fst(dest_const(fst(strip_comb(lhs(concl th))))) = "wl_evaluate")) THEN
  REWRITE_TAC[wl_evaluate_def] THEN ASM_SIMP_TAC[CPstate_modelsD_get_var] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  POP_ASSUM MP_TAC THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC CPstate_models_same THEN
  ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds]);;

let WPROOF2AUX_cpc_OpCurrHeap = prove
 (WPROOF2AUX_cpc `wl_OpCurrHeap b dst src:(A)wl_prog`,
  REWRITE_TAC[copy_prop_prog_def; LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN WPROOF2AUX_cp_SUBST_TAC THEN
  SUBGOAL_THEN
   `wl_evaluate (wl_OpCurrHeap b dst (if lookup_eq cs src = dst then src else lookup_eq cs src),
                 st:(A,C,FFI)wl_state) =
    wl_evaluate (wl_OpCurrHeap b dst src, st)` SUBST1_TAC THENL
   [REWRITE_TAC[wl_evaluate_def; wl_word_exp_def; MAP] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[CPstate_modelsD_get_var]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `wl_evaluate (wl_OpCurrHeap b dst src,st:(A,C,FFI)wl_state) = (NONE,st')` THEN
  REWRITE_TAC[wl_evaluate_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] remove_eq_model_set_var) THEN ASM_REWRITE_TAC[]);;

let WPROOF2AUX_storeconsts_model = prove
 (`CPstate_inv cs /\ CPstate_models cs (st:(A,C,FFI)wl_state) ==>
   CPstate_models (remove_eq (remove_eq (remove_eq (remove_eq cs a) b) c) d)
     (wl_set_var c w1 (wl_set_var d w2 (wl_unset_var a (wl_unset_var b st))))`,
  STRIP_TAC THEN ONCE_REWRITE_TAC[remove_eq_comm] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] remove_eq_model_set_var) THEN
  CONJ_TAC THENL [REPEAT(MATCH_MP_TAC remove_eq_inv) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] remove_eq_model_set_var) THEN
  CONJ_TAC THENL [REPEAT(MATCH_MP_TAC remove_eq_inv) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[remove_eq_comm] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] remove_eq_model_unset_var) THEN
  CONJ_TAC THENL [REPEAT(MATCH_MP_TAC remove_eq_inv) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] remove_eq_model_unset_var) THEN
  ASM_REWRITE_TAC[]);;

let WPROOF2AUX_cpc_StoreConsts = prove
 (WPROOF2AUX_cpc `wl_StoreConsts a b c d ws:(A)wl_prog`,
  REWRITE_TAC[copy_prop_prog_def; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN WPROOF2AUX_cp_SUBST_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `wl_evaluate (wl_StoreConsts a b c d ws,st:(A,C,FFI)wl_state) = (NONE,st')` THEN
  REWRITE_TAC[wl_evaluate_def; LET_DEF; LET_END_DEF] THEN EVERY_CASE_TAC THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[remove_eqs_def] THEN
  MATCH_MP_TAC WPROOF2AUX_storeconsts_model THEN
  ASM_SIMP_TAC[WPROOF2AUX_models_mem]);;

let WPROOF2AUX_cpc_Set_Var = prove
 (WPROOF2AUX_cpc `wl_Set name (wl_Var n):(A)wl_prog`,
  REWRITE_TAC[copy_prop_prog_def; LET_DEF; LET_END_DEF] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN WPROOF2AUX_cp_SUBST_TAC THEN
  SUBGOAL_THEN `wl_evaluate (wl_Set name (wl_Var (lookup_eq cs n)), st:(A,C,FFI)wl_state) =
                wl_evaluate (wl_Set name (wl_Var n), st)` SUBST1_TAC THENL
   [REWRITE_TAC[wl_evaluate_def; wl_word_exp_def] THEN
    ASM_SIMP_TAC[CPstate_modelsD_get_var]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `wl_evaluate (wl_Set name (wl_Var n),st:(A,C,FFI)wl_state) = (NONE,st')` THEN
  REWRITE_TAC[wl_evaluate_def; wl_word_exp_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN
  MP_TAC(ISPEC `wl_get_var n (st:(A,C,FFI)wl_state)` (nchotomy_of_type `:((A)word_loc)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC set_store_eq_model_set_store THEN ASM_REWRITE_TAC[]);;

let WPROOF2AUX_cpc_Set = prove
 (WPROOF2AUX_cpc `wl_Set name exp:(A)wl_prog`,
  ASM_CASES_TAC `?n. exp = wl_Var n:(A)wl_exp` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
    MATCH_ACCEPT_TAC WPROOF2AUX_cpc_Set_Var;
    MATCH_MP_TAC WPROOF2AUX_cpc_id THEN POP_ASSUM MP_TAC THEN
    CASES_ON `exp:(A)wl_exp` THEN REWRITE_TAC[copy_prop_prog_def] THEN
    CAKE_REWRITE_TAC[] THEN MESON_TAC[]]);;

let WPROOF2AUX_locals_fupd_id = prove
 (`!st:(A,C,FFI)wl_state. wl_state_locals_fupd (combin_K (wl_state_locals st)) st = st`,
  REWRITE_TAC[wl_state_INFO.ri_component_equality; wl_state_INFO.ri_accfupds; K_THM]);;

let WPROOF2AUX_cpc_Get = prove
 (WPROOF2AUX_cpc `wl_Get n name:(A)wl_prog`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?x. wl_get_store name (st:(A,C,FFI)wl_state) = SOME x /\
                    (err:((A)wl_result)option) = NONE /\
                    st' = wl_set_var n x st` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `wl_evaluate (wl_Get n name,st:(A,C,FFI)wl_state) = (err,st')` THEN
    UNDISCH_TAC `~(err = SOME (wl_Error:(A)wl_result))` THEN
    REWRITE_TAC[wl_evaluate_def] THEN
    MP_TAC(ISPEC `wl_get_store name (st:(A,C,FFI)wl_state)`
             (nchotomy_of_type `:((A)word_loc)option`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ; option_INJ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `err:((A)wl_result)option = NONE`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
     lhs(concl th) = `st':(A,C,FFI)wl_state`)) THEN
  REWRITE_TAC[] THEN
  UNDISCH_TAC `copy_prop_prog (wl_Get n name:(A)wl_prog) cs = (prog',cs')` THEN
  REWRITE_TAC[copy_prop_prog_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPEC `lookup_store_eq cs name` (nchotomy_of_type `:(num)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[pair_CASE_def] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN WPROOF2AUX_cp_SUBST_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC set_store_eq_model_set_var THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(INST [`name:store_name`,`s:store_name`; `a:num`,`v:num`]
           lookup_store_eq_SOME) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `wl_get_store name (st:(A,C,FFI)wl_state) = SOME x` THEN
  REWRITE_TAC[wl_get_store_def] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN WPROOF2AUX_cp_SUBST_TAC THENL
   [REWRITE_TAC[WPROOF2AUX_cpm_CONS] THEN
    REWRITE_TAC[copy_prop_move_def; FST; SND; wl_evaluate_def] THEN
    REWRITE_TAC[MAP; ALL_DISTINCT; MEM; wl_get_vars_def] THEN
    ASM_SIMP_TAC[CPstate_modelsD_get_var] THEN
    ASM_REWRITE_TAC[wl_get_var_def] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[wl_set_vars_def; wl_set_var_def; alist_insert_def] THEN
    MATCH_MP_TAC set_eq_remove_eq_models THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a:num = n`)) THEN
    SUBGOAL_THEN `wl_set_var n x (st:(A,C,FFI)wl_state) = st` SUBST1_TAC THENL
     [REWRITE_TAC[wl_set_var_def] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP insert_unchanged th]) THEN
      REWRITE_TAC[WPROOF2AUX_locals_fupd_id];
      ASM_REWRITE_TAC[wl_evaluate_def]]]);;

let WPROOF2AUX_sh_mem_set_var_NONE = prove
 (`!r v (st:(A,C,FFI)wl_state) st'.
     sh_mem_set_var r v st = (NONE:((A)wl_result)option, st') ==>
     ?w f. st' = wl_set_var v w (wl_state_ffi_fupd f st)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `r:((FFI)ffi_result)option` (nchotomy_of_type `:((FFI)ffi_result)option`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[sh_mem_set_var_def; PAIR_EQ; option_DISTINCT] THEN
  MP_TAC(ISPEC `a:(FFI)ffi_result` (nchotomy_of_type `:(FFI)ffi_result`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[sh_mem_set_var_def; PAIR_EQ; option_DISTINCT] THEN
  MESON_TAC[]);;

let WPROOF2AUX_sh_mem_store_NONE = prove
 (`(wl_sh_mem_store a w (st:(A,C,FFI)wl_state) = (NONE:((A)wl_result)option, st') ==>
    ?f. st' = wl_state_ffi_fupd f st) /\
   (wl_sh_mem_store_byte a w st = (NONE:((A)wl_result)option, st') ==>
    ?f. st' = wl_state_ffi_fupd f st) /\
   (wl_sh_mem_store16 a w st = (NONE:((A)wl_result)option, st') ==>
    ?f. st' = wl_state_ffi_fupd f st) /\
   (wl_sh_mem_store32 a w st = (NONE:((A)wl_result)option, st') ==>
    ?f. st' = wl_state_ffi_fupd f st)`,
  REWRITE_TAC[wl_sh_mem_store_def; wl_sh_mem_store_byte_def; wl_sh_mem_store16_def;
              wl_sh_mem_store32_def] THEN
  REPEAT CONJ_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN MESON_TAC[]);;

let WPROOF2AUX_share_inst_NONE = prove
 (`!op v ad (st:(A,C,FFI)wl_state) st'.
     share_inst op v ad st = (NONE:((A)wl_result)option, st') ==>
     (?w f. st' = wl_set_var v w (wl_state_ffi_fupd f st)) \/
     (?f. st' = wl_state_ffi_fupd f st)`,
  REPEAT GEN_TAC THEN CASES_ON `op:memop` THEN REWRITE_TAC[share_inst_def] THEN
  TRY(DISCH_THEN(MP_TAC o MATCH_MP WPROOF2AUX_sh_mem_set_var_NONE) THEN
      MESON_TAC[] THEN NO_TAC) THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN
  FIRST (map (fun th -> DISCH_THEN(MP_TAC o MATCH_MP (GEN_ALL th)) THEN MESON_TAC[])
             (CONJUNCTS WPROOF2AUX_sh_mem_store_NONE)));;

let WPROOF2AUX_cpc_ShareInst = prove
 (WPROOF2AUX_cpc `ShareInst op v exp:(A)wl_prog`,
  REWRITE_TAC[copy_prop_prog_def; LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN WPROOF2AUX_cp_SUBST_TAC THEN
  SUBGOAL_THEN `wl_evaluate (ShareInst op v (copy_prop_share exp cs), st:(A,C,FFI)wl_state) =
                wl_evaluate (ShareInst op v exp, st)` SUBST1_TAC THENL
   [REWRITE_TAC[wl_evaluate_def] THEN ASM_SIMP_TAC[CPstate_modelsD_copy_prop_share];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `wl_evaluate (ShareInst op v exp,st:(A,C,FFI)wl_state) = (NONE,st')` THEN
  REWRITE_TAC[wl_evaluate_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP WPROOF2AUX_share_inst_NONE) THEN
  ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] remove_eq_model_set_var) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CPstate_models_same THEN ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds];
    MATCH_MP_TAC remove_eq_model THEN
    MATCH_MP_TAC CPstate_models_same THEN ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds]]);;

let WPROOF2AUX_cpc_MustTerminate = prove
 (mk_imp(WPROOF2AUX_cpc `p1:(A)wl_prog`, WPROOF2AUX_cpc `MustTerminate p1:(A)wl_prog`),
  DISCH_TAC THEN
  REWRITE_TAC[copy_prop_prog_def; LET_DEF; LET_END_DEF] THEN
  CAKE_REWRITE_TAC[pair_CASE_def; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN WPROOF2AUX_cp_SUBST_TAC THEN
  UNDISCH_TAC `wl_evaluate (MustTerminate p1, st:(A,C,FFI)wl_state) = (err, st')` THEN
  REWRITE_TAC[wl_evaluate_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THENL [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `st1 = wl_state_clock_fupd (combin_K (MustTerminate_limit (:A)))
                      (wl_state_termdep_fupd (combin_K (wl_state_termdep st - 1))
                         (st:(A,C,FFI)wl_state))` THEN
  MP_TAC(ISPEC `wl_evaluate (p1:(A)wl_prog, st1:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)wl_result)option`
    (X_CHOOSE_THEN `t:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  COND_CASES_TAC THENL [REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `r:((A)wl_result)option = err`)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`cs:copy_state`; `st1:(A,C,FFI)wl_state`;
     `FST (copy_prop_prog (p1:(A)wl_prog) cs)`; `SND (copy_prop_prog (p1:(A)wl_prog) cs)`;
     `err:((A)wl_result)option`; `t:(A,C,FFI)wl_state`] o check (is_forall o concl)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PAIR] THEN MATCH_MP_TAC CPstate_models_same THEN
    EXPAND_TAC "st1" THEN ASM_REWRITE_TAC[wl_state_INFO.ri_accfupds];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `st':(A,C,FFI)wl_state`)) THEN
  MATCH_MP_TAC(INST [`t:(A,C,FFI)wl_state`,`st:(A,C,FFI)wl_state`] CPstate_models_same) THEN
  ASM_SIMP_TAC[wl_state_INFO.ri_accfupds]);;

let WPROOF2AUX_cpc_Seq = prove
 (mk_imp(mk_conj(WPROOF2AUX_cpc `p1:(A)wl_prog`, WPROOF2AUX_cpc `p2:(A)wl_prog`),
         WPROOF2AUX_cpc `wl_Seq p1 p2:(A)wl_prog`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
  REWRITE_TAC[copy_prop_prog_def; LET_DEF; LET_END_DEF] THEN
  CAKE_REWRITE_TAC[pair_CASE_def; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN WPROOF2AUX_cp_SUBST_TAC THEN
  UNDISCH_TAC `wl_evaluate (wl_Seq p1 p2, st:(A,C,FFI)wl_state) = (err, st')` THEN
  REWRITE_TAC[wl_evaluate_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPEC `wl_evaluate (p1:(A)wl_prog, st:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)wl_result)option`
    (X_CHOOSE_THEN `t:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      concl th = `r:((A)wl_result)option = NONE`)) THEN
    DISCH_TAC THEN
    REMOVE_THEN "IH1" (MP_TAC o SPECL [`cs:copy_state`; `st:(A,C,FFI)wl_state`;
      `FST (copy_prop_prog (p1:(A)wl_prog) cs)`; `SND (copy_prop_prog (p1:(A)wl_prog) cs)`;
      `NONE:((A)wl_result)option`; `t:(A,C,FFI)wl_state`]) THEN
    ASM_REWRITE_TAC[PAIR; option_DISTINCT] THEN STRIP_TAC THEN
    SUBGOAL_THEN `CPstate_inv (SND (copy_prop_prog (p1:(A)wl_prog) cs))` ASSUME_TAC THENL
     [MATCH_MP_TAC(INST [`p1:(A)wl_prog`,`prog:(A)wl_prog`;
                         `FST (copy_prop_prog (p1:(A)wl_prog) cs)`,`prog':(A)wl_prog`]
                        copy_prop_prog_inv) THEN
      ASM_REWRITE_TAC[PAIR];
      ALL_TAC] THEN
    REMOVE_THEN "IH2" (MP_TAC o SPECL [`SND (copy_prop_prog (p1:(A)wl_prog) cs)`;
      `t:(A,C,FFI)wl_state`;
      `FST (copy_prop_prog (p2:(A)wl_prog) (SND (copy_prop_prog (p1:(A)wl_prog) cs)))`;
      `SND (copy_prop_prog (p2:(A)wl_prog) (SND (copy_prop_prog (p1:(A)wl_prog) cs)))`;
      `err:((A)wl_result)option`; `st':(A,C,FFI)wl_state`]) THEN
    ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE];
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      concl th = `r:((A)wl_result)option = err`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      concl th = `t:(A,C,FFI)wl_state = st'`)) THEN
    REMOVE_THEN "IH1" (MP_TAC o SPECL [`cs:copy_state`; `st:(A,C,FFI)wl_state`;
      `FST (copy_prop_prog (p1:(A)wl_prog) cs)`; `SND (copy_prop_prog (p1:(A)wl_prog) cs)`;
      `err:((A)wl_result)option`; `st':(A,C,FFI)wl_state`]) THEN
    ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE]]);;

let WPROOF2AUX_cpc_If = prove
 (mk_imp(mk_conj(WPROOF2AUX_cpc `p1:(A)wl_prog`, WPROOF2AUX_cpc `p2:(A)wl_prog`),
         WPROOF2AUX_cpc `wl_If cmp r ri p1 p2:(A)wl_prog`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
  REWRITE_TAC[copy_prop_prog_def; LET_DEF; LET_END_DEF] THEN
  CAKE_REWRITE_TAC[pair_CASE_def; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN WPROOF2AUX_cp_SUBST_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o GSYM o check (fun th ->
    concl th = `~(err = SOME (wl_Error:(A)wl_result))`)) THEN
  UNDISCH_TAC `wl_evaluate (wl_If cmp r ri p1 p2, st:(A,C,FFI)wl_state) = (err, st')` THEN
  REWRITE_TAC[wl_evaluate_def] THEN
  SUBGOAL_THEN `!x. wl_get_var (lookup_eq cs x) (st:(A,C,FFI)wl_state) = wl_get_var x st`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC CPstate_modelsD_get_var THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:(A)reg_imm. wl_get_var_imm (lookup_eq_imm cs x) (st:(A,C,FFI)wl_state) =
                               wl_get_var_imm x st`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC CPstate_modelsD_get_var_imm THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EVERY_CASE_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_TAC THENL
   [REMOVE_THEN "IH1" (MP_TAC o SPECL [`cs:copy_state`; `st:(A,C,FFI)wl_state`;
      `FST (copy_prop_prog (p1:(A)wl_prog) cs)`; `SND (copy_prop_prog (p1:(A)wl_prog) cs)`;
      `err:((A)wl_result)option`; `st':(A,C,FFI)wl_state`]) THEN
    ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN MATCH_MP_TAC merge_eqs_model1 THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REMOVE_THEN "IH2" (MP_TAC o SPECL [`cs:copy_state`; `st:(A,C,FFI)wl_state`;
      `FST (copy_prop_prog (p2:(A)wl_prog) cs)`; `SND (copy_prop_prog (p2:(A)wl_prog) cs)`;
      `err:((A)wl_result)option`; `st':(A,C,FFI)wl_state`]) THEN
    ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN MATCH_MP_TAC merge_eqs_model2 THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let WPROOF2AUX_cpc_Loop = prove
 (mk_imp(WPROOF2AUX_cpc `c:(A)wl_prog`,
         WPROOF2AUX_cpc `wl_Loop names c exit_names:(A)wl_prog`),
  DISCH_TAC THEN
  REWRITE_TAC[copy_prop_prog_def; LET_DEF; LET_END_DEF] THEN
  CAKE_REWRITE_TAC[pair_CASE_def; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN WPROOF2AUX_cp_SUBST_TAC THEN
  REWRITE_TAC[empty_eq_model] THEN
  MATCH_MP_TAC evaluate_Loop_body_cong_err THEN EXISTS_TAC `c:(A)wl_prog` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`empty_eq`; `v:(A,C,FFI)wl_state`;
    `FST (copy_prop_prog (c:(A)wl_prog) empty_eq)`;
    `SND (copy_prop_prog (c:(A)wl_prog) empty_eq)`;
    `res:((A)wl_result)option`; `s':(A,C,FFI)wl_state`] o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[PAIR; empty_eq_inv; empty_eq_model] THEN MESON_TAC[]);;

(* the WF induction hypothesis instantiated for the subprograms of the goal *)

let WPROOF2AUX_cp_IH_TAC : tactic = fun (asl,w as g) ->
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

let copy_prop_correct = prove
 (`!prog cs (st:(A,C,FFI)wl_state) prog' cs' err st'.
     CPstate_inv cs /\ CPstate_models cs st /\
     copy_prop_prog (prog:(A)wl_prog) cs = (prog', cs') /\
     ~(err = SOME wl_Error) /\ wl_evaluate (prog, st) = (err, st') ==>
     wl_evaluate (prog', st) = (err, st') /\ (err = NONE ==> CPstate_models cs' st')`,
  MP_TAC(ISPEC `wl_prog_size (\x:A. 0)` WF_MEASURE) THEN
  REWRITE_TAC[WF_IND; MEASURE] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `prog:(A)wl_prog` THEN DISCH_TAC THEN
  CASES_ON `prog:(A)wl_prog` THEN WPROOF2AUX_cp_IH_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC
           (CONJUNCTS WPROOF2AUX_cpc_trivial @ CONJUNCTS WPROOF2AUX_cpc_Break_Continue @
            CONJUNCTS WPROOF2AUX_cpc_BufferWrite @
            [WPROOF2AUX_cpc_Skip; WPROOF2AUX_cpc_Move; WPROOF2AUX_cpc_Inst;
             WPROOF2AUX_cpc_Return; WPROOF2AUX_cpc_Raise; WPROOF2AUX_cpc_Tick;
             WPROOF2AUX_cpc_LocValue; WPROOF2AUX_cpc_OpCurrHeap; WPROOF2AUX_cpc_StoreConsts;
             WPROOF2AUX_cpc_Set; WPROOF2AUX_cpc_Get; WPROOF2AUX_cpc_ShareInst]) @
         map (fun th -> MATCH_MP_TAC th THEN REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC)
           [WPROOF2AUX_cpc_MustTerminate; WPROOF2AUX_cpc_Seq; WPROOF2AUX_cpc_If;
            WPROOF2AUX_cpc_Loop]));;

(* Main semantics result *)

let evaluate_copy_prop = prove
 (`~(FST (wl_evaluate (e, s:(A,C,FFI)wl_state)) = SOME wl_Error) ==>
   wl_evaluate (copy_prop (e:(A)wl_prog), s) = wl_evaluate (e, s)`,
  REWRITE_TAC[copy_prop_def] THEN
  MP_TAC(ISPEC `wl_evaluate (e:(A)wl_prog, s:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)wl_result)option`
    (X_CHOOSE_THEN `t:(A,C,FFI)wl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`e:(A)wl_prog`; `empty_eq`; `s:(A,C,FFI)wl_state`;
                `FST (copy_prop_prog (e:(A)wl_prog) empty_eq)`;
                `SND (copy_prop_prog (e:(A)wl_prog) empty_eq)`;
                `r:((A)wl_result)option`; `t:(A,C,FFI)wl_state`] copy_prop_correct) THEN
  ASM_REWRITE_TAC[PAIR; empty_eq_inv; empty_eq_model] THEN SIMP_TAC[]);;
