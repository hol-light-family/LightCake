(* ========================================================================= *)
(* flatProps: port of HOL4 compiler/backend/semantics/flatPropsScript.sml    *)
(* (CakeML v3479).  Properties about flatLang and its semantics.             *)
(* ========================================================================= *)

needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/semantics/flatSem.ml";;
needs "hol4/lprefix_lub.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;

type_invention_error := true;;
let ctor_same_type_OPTREL = prove
 (`!(c1:(A#B)option) (c2:(A#B)option).
     flat_ctor_same_type c1 c2 <=> OPTREL (inv_image (=) SND) c1 c2`,
  REWRITE_TAC[FORALL_OPTION_THM; FORALL_PAIR_THM] THEN
  REWRITE_TAC[flat_ctor_same_type_def; OPTREL_DEF; option_DISTINCT; option_INJ;
              inv_image_THM] THEN
  MESON_TAC[PAIR_EQ; SND]);;

let pats_bindings_FLAT_MAP = prove
 (`!ps. flat_pats_bindings ps =
        FLAT (REVERSE (MAP (\p. flat_pat_bindings p) ps))`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[flat_pat_bindings_def; MAP; REVERSE; FLAT; FLAT_APPEND;
                  APPEND_NIL]);;

(* HOL4's st and st' are states with independent 'c types *)

let pmatch_state = prove
 (`(!(st:(C,FFI)flat_state) p v l (st':(D,FFI)flat_state) res.
      flat_pmatch st p v l = res /\ flat_state_refs st = flat_state_refs st'
      ==> flat_pmatch st' p v l = res) /\
   (!(st:(C,FFI)flat_state) p vs l (st':(D,FFI)flat_state) res.
      flat_pmatch_list st p vs l = res /\ flat_state_refs st = flat_state_refs st'
      ==> flat_pmatch_list st' p vs l = res)`,
  MATCH_MP_TAC flat_pmatch_ind THEN RW[flat_pmatch_def] THEN
  EVERY_CASE_TAC THEN FS[] THEN RES_TAC THEN FS[]);;


(* a local helper: the existential of HOL4's simp with APPEND_11 *)
let FLATSEMAUX_ex_append = prove
 (`!(l:A list) e P. (?x. APPEND e l = APPEND x l /\ P x) <=> P e`,
  REWRITE_TAC[APPEND_RCANCEL] THEN MESON_TAC[]);;

(* HOL4 quantifies an unused env'' *)
let flat_pmatch_extend = prove
 (`(!(s:(C,FFI)flat_state) p v env env'.
      flat_pmatch s p v env = Match env'
      ==> ?env''. env' = APPEND env'' env /\ MAP FST env'' = flat_pat_bindings p) /\
   (!(s:(C,FFI)flat_state) ps vs env env'.
      flat_pmatch_list s ps vs env = Match env'
      ==> ?env''. env' = APPEND env'' env /\ MAP FST env'' = flat_pats_bindings ps)`,
  MATCH_MP_TAC flat_pmatch_ind THEN
  RW[flat_pat_bindings_def; flat_pmatch_def] THEN
  EVERY_CASE_TAC THEN FS[] THEN RW[] THEN RES_TAC THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC; FLATSEMAUX_ex_append] THEN
  FS[MAP_APPEND] THENL
   [EXISTS_TAC `[x,v']:(varN#flat_v)list` THEN
    REWRITE_TAC[APPEND; CONS_11] THEN MESON_TAC[FST];
    EXISTS_TAC `APPEND env'' [i,v]:(varN#flat_v)list` THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; MAP_APPEND; MAP]]);;

let pmatch_bindings = prove
 (`(!(s:(C,FFI)flat_state) p v env r.
      flat_pmatch s p v env = Match r
      ==> MAP FST r = APPEND (flat_pat_bindings p) (MAP FST env)) /\
   (!(s:(C,FFI)flat_state) ps vs env r.
      flat_pmatch_list s ps vs env = Match r
      ==> MAP FST r = APPEND (flat_pats_bindings ps) (MAP FST env))`,
  MATCH_MP_TAC flat_pmatch_ind THEN
  RW[flat_pmatch_def; flat_pat_bindings_def] THEN RW[] THEN
  EVERY_CASE_TAC THEN FS[] THEN
  ASM_MESON_TAC[APPEND; APPEND_ASSOC; CONS_APPEND]);;

let pmatch_length = prove
 (`!(s:(C,FFI)flat_state) p v env r.
     flat_pmatch s p v env = Match r
     ==> LENGTH r = LENGTH (flat_pat_bindings p) + LENGTH env`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:(mlstring)list->num` o
              MATCH_MP (CONJUNCT1 pmatch_bindings)) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_MAP]);;

let pmatch_any_match = prove
 (`(!(s:(C,FFI)flat_state) p v env env'.
      flat_pmatch s p v env = Match env' ==>
      !env. ?env'. flat_pmatch s p v env = Match env') /\
   (!(s:(C,FFI)flat_state) ps vs env env'.
      flat_pmatch_list s ps vs env = Match env' ==>
      !env. ?env'. flat_pmatch_list s ps vs env = Match env')`,
  MATCH_MP_TAC flat_pmatch_ind THEN RW[flat_pmatch_def] THEN FS[] THEN
  POP_ASSUM MP_TAC THEN EVERY_CASE_TAC THEN FS[] THEN RES_TAC THEN
  ASM_MESON_TAC[distinctness "match_result"; injectivity "match_result"]);;

(* forward reasoning: MATCH_MP of each theorem with each assumption, the     *)
(* results added as assumptions (IMP_RES_TAC with the theorem's conjuncts,   *)
(* for conclusions that IMP_RES_TAC does not canonicalise)                    *)
let FLATSEMAUX_FWD_TAC (thl:thm list) : tactic =
  ASSUM_LIST (fun asl ->
    MAP_EVERY ASSUME_TAC
      (flat (map (fun th -> mapfilter (MATCH_MP th) asl)
                 (flat (map CONJUNCTS thl)))));;

let pmatch_any_no_match = prove
 (`(!(s:(C,FFI)flat_state) p v env.
      flat_pmatch s p v env = No_match ==>
      !env. flat_pmatch s p v env = No_match) /\
   (!(s:(C,FFI)flat_state) ps vs env.
      flat_pmatch_list s ps vs env = No_match ==>
      !env. flat_pmatch_list s ps vs env = No_match)`,
  MATCH_MP_TAC flat_pmatch_ind THEN RW[flat_pmatch_def] THEN FS[] THEN
  POP_ASSUM MP_TAC THEN EVERY_CASE_TAC THEN FS[] THEN RES_TAC THEN
  FLATSEMAUX_FWD_TAC [pmatch_any_match] THEN
  ASM_METIS_TAC[distinctness "match_result"]);;

let pmatch_any_match_error = prove
 (`(!(s:(C,FFI)flat_state) p v env.
      flat_pmatch s p v env = Match_type_error ==>
      !env. flat_pmatch s p v env = Match_type_error) /\
   (!(s:(C,FFI)flat_state) ps vs env.
      flat_pmatch_list s ps vs env = Match_type_error ==>
      !env. flat_pmatch_list s ps vs env = Match_type_error)`,
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPEC `flat_pmatch (s:(C,FFI)flat_state) p v env'`
              (cases "match_result"));
    MP_TAC(ISPEC `flat_pmatch_list (s:(C,FFI)flat_state) ps vs env'`
              (cases "match_result"))] THEN
  ASM_MESON_TAC[distinctness "match_result"; pmatch_any_no_match;
                pmatch_any_match]);;

let pmatch_list_pairwise = prove
 (`!ps vs (s:(C,FFI)flat_state) env env'.
     flat_pmatch_list s ps vs env = Match env' ==>
     ALL2 (\p v. !env. ?env'. flat_pmatch s p v env = Match env') ps vs`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN CASES_ON `vs:flat_v list` THEN
  SIMP[flat_pmatch_def; ALL2] THEN
  REPEAT GEN_TAC THEN CASE_TAC THEN STRIP_TAC THEN
  FS[case_eq "match_result"] THEN RES_TAC THEN SIMP[] THEN
  ASM_MESON_TAC[pmatch_any_match]);;

let pmatch_list_snoc_nil = prove
 (`!p ps v vs (s:(C,FFI)flat_state) env.
     (flat_pmatch_list s [] (SNOC v vs) env = Match_type_error) /\
     (flat_pmatch_list s (SNOC p ps) [] env = Match_type_error)`,
  REPEAT GEN_TAC THEN CASES_ON `ps:flat_pat list` THEN
  CASES_ON `vs:flat_v list` THEN SIMP[flat_pmatch_def; SNOC]);;
let _ = cake_add_simps [pmatch_list_snoc_nil];;


(* local helpers: a type error of pmatch_list does not depend on the         *)
(* bindings; the case expression of pmatch_list_append as an if              *)
let FLATSEMAUX_pmatch_list_mte = prove
 (`!(s:(C,FFI)flat_state) ps vs e1 e2.
     flat_pmatch_list s ps vs e1 = Match_type_error <=>
     flat_pmatch_list s ps vs e2 = Match_type_error`,
  MESON_TAC[pmatch_any_match_error]);;

let FLATSEMAUX_nm_case = prove
 (CASE_TERM
  `!(x:A match_result).
     (match x with No_match -> No_match | Match_type_error -> Match_type_error
                 | Match a -> (No_match:B match_result)) =
     if x = Match_type_error then Match_type_error else No_match`,
  GEN_TAC THEN CASES_ON `x:A match_result` THEN
  REWRITE_TAC[case_def "match_result"; distinctness "match_result"]);;

let flat_pmatch_list_append = prove
 (CASE_TERM `!ps vs ps' vs' (s:(C,FFI)flat_state) env.
     LENGTH ps = LENGTH vs ==>
     flat_pmatch_list s (APPEND ps ps') (APPEND vs vs') env =
     match flat_pmatch_list s ps vs env with
       Match env' -> flat_pmatch_list s ps' vs' env'
     | Match_type_error -> Match_type_error
     | No_match ->
         (match flat_pmatch_list s ps' vs' env with
            Match_type_error -> Match_type_error
          | _ -> No_match)`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN CASES_ON `vs:flat_v list` THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; APPEND; flat_pmatch_def] THEN
  REWRITE_TAC[case_def "match_result"] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN
  CASES_ON `flat_pmatch (s:(C,FFI)flat_state) h a0 env` THEN
  REWRITE_TAC[case_def "match_result"] THEN
  CASES_ON `flat_pmatch_list (s:(C,FFI)flat_state) t a1 env` THEN
  REWRITE_TAC[case_def "match_result"; FLATSEMAUX_nm_case] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_MESON_TAC[FLATSEMAUX_pmatch_list_mte; distinctness "match_result"]);;

let pmatch_list_snoc = prove
 (CASE_TERM
  `!ps vs p v (s:(C,FFI)flat_state) env.
     LENGTH ps = LENGTH vs ==>
     flat_pmatch_list s (SNOC p ps) (SNOC v vs) env =
     match flat_pmatch_list s ps vs env with
       Match env' -> flat_pmatch s p v env'
     | Match_type_error -> Match_type_error
     | No_match ->
         (match flat_pmatch s p v env with
            Match_type_error -> Match_type_error
          | _ -> No_match)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SNOC_APPEND; flat_pmatch_list_append] THEN
  SUBGOAL_THEN `!e. flat_pmatch_list (s:(C,FFI)flat_state) [p] [v] e =
                    flat_pmatch s p v e` (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN REWRITE_TAC[flat_pmatch_def] THEN
  CASES_ON `flat_pmatch (s:(C,FFI)flat_state) p v e` THEN
  REWRITE_TAC[case_def "match_result"]);;

let map_match_eq_case = prove
 (CASE_TERM
  `!f (v:A match_result).
     map_match f v = match v with Match m -> Match (f m) | _ -> v`,
  GEN_TAC THEN GEN_TAC THEN CASES_ON `v:A match_result` THEN
  REWRITE_TAC[map_match_def; case_def "match_result"]);;

(* a local helper: HOL4's pmatch_append from left to right, proved first *)
let FLATSEMAUX_pmatch_append_rev = prove
 (`(!(s:(C,FFI)flat_state) p v env tail_env.
      flat_pmatch s p v (APPEND env tail_env) =
      map_match (flip APPEND tail_env) (flat_pmatch s p v env)) /\
   (!(s:(C,FFI)flat_state) ps vs env tail_env.
      flat_pmatch_list s ps vs (APPEND env tail_env) =
      map_match (flip APPEND tail_env) (flat_pmatch_list s ps vs env))`,
  MATCH_MP_TAC flat_pmatch_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[APPEND]) THEN
  REWRITE_TAC[flat_pmatch_def; map_match_def; flip_DEF; APPEND] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT (COND_CASES_TAC THEN ASM_SIMP_TAC[map_match_def; flip_DEF]) THEN
  ((CASES_ON `flat_pmatch (s:(C,FFI)flat_state) p v bindings` THEN
    ASM_SIMP_TAC[map_match_def; flip_DEF; case_def "match_result"] THEN
    CASES_ON `flat_pmatch_list (s:(C,FFI)flat_state) ps vs bindings` THEN
    ASM_SIMP_TAC[map_match_def; flip_DEF; case_def "match_result"] THEN NO_TAC) ORELSE
   (CASES_ON `store_lookup lnum (flat_state_refs (s:(C,FFI)flat_state))` THEN
    ASM_SIMP_TAC[map_match_def; flip_DEF; case_def "match_result"; option_CASE] THEN
    CASES_ON `a:flat_v store_v` THEN
    ASM_SIMP_TAC[map_match_def; flip_DEF; case_def "store_v"] THEN NO_TAC)));;

(* HOL4's combin$C is flip; HOL4 quantifies the unused pred_env and n and   *)
(* leaves tail_env free                                                      *)
let flat_pmatch_append = prove
 (`(!(s:(C,FFI)flat_state) p v env tail_env.
      map_match (flip APPEND tail_env) (flat_pmatch s p v env) =
      flat_pmatch s p v (APPEND env tail_env)) /\
   (!(s:(C,FFI)flat_state) ps vs env tail_env.
      map_match (flip APPEND tail_env) (flat_pmatch_list s ps vs env) =
      flat_pmatch_list s ps vs (APPEND env tail_env))`,
  REWRITE_TAC[FLATSEMAUX_pmatch_append_rev]);;

(* HOL4: pmatch_append with env := [] *)
let pmatch_nil = prove
 (`(!(s:(C,FFI)flat_state) p v tail_env.
      flat_pmatch s p v tail_env =
      map_match (flip APPEND tail_env) (flat_pmatch s p v [])) /\
   (!(s:(C,FFI)flat_state) ps vs tail_env.
      flat_pmatch_list s ps vs tail_env =
      map_match (flip APPEND tail_env) (flat_pmatch_list s ps vs []))`,
  MESON_TAC[FLATSEMAUX_pmatch_append_rev; APPEND]);;

let pmatch_ignore_clock = prove
 (`!(s:(C,FFI)flat_state) s' p v env ps vs.
     flat_pmatch (flat_state_clock_fupd (K s') s) p v env = flat_pmatch s p v env /\
     flat_pmatch_list (flat_state_clock_fupd (K s') s) ps vs env =
     flat_pmatch_list s ps vs env`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:(C,FFI)flat_state`; `p:flat_pat`; `v:flat_v`;
                   `env:(varN#flat_v)list`;
                   `flat_state_clock_fupd (K s') (s:(C,FFI)flat_state)`;
                   `flat_pmatch (s:(C,FFI)flat_state) p v env`]
                  (CONJUNCT1 pmatch_state));
    MP_TAC(ISPECL [`s:(C,FFI)flat_state`; `ps:flat_pat list`; `vs:flat_v list`;
                   `env:(varN#flat_v)list`;
                   `flat_state_clock_fupd (K s') (s:(C,FFI)flat_state)`;
                   `flat_pmatch_list (s:(C,FFI)flat_state) ps vs env`]
                  (CONJUNCT2 pmatch_state))] THEN
  REWRITE_TAC[flat_state_INFO.ri_accfupds]);;

let pmatch_rows_ignore_clock = prove
 (`!(pes:(flat_pat#A)list) (s:(C,FFI)flat_state) v c.
     pmatch_rows pes (flat_state_clock_fupd (K c) s) v = pmatch_rows pes s v`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[FORALL_PAIR_THM; pmatch_rows_def; pmatch_ignore_clock] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;
let _ = cake_add_simps [pmatch_rows_ignore_clock];;


let pmatch_rows_IMP_pmatch = prove
 (`!pes (s:(C,FFI)flat_state) v env' p' (e':A).
     pmatch_rows pes s v = Match (env',p',e') ==>
     flat_pmatch s p' v [] = Match env' /\ MEM (p',e') pes`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[FORALL_PAIR_THM; pmatch_rows_def; distinctness "match_result"] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  RW[case_eq "match_result"; MEM] THEN RES_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 [local] *)
let flat_build_rec_env_help_lem = prove
 (CASE_TERM
  `!(funs:(varN#A#B)list) (env:(flat_v)flat_environment) funs' env'.
     ITLIST (\fxe env'. match fxe with
                          (f,x,e) -> CONS (f,flat_Recclosure env funs' f) env')
            funs env' =
     APPEND (MAP (\fne. match fne with
                          (f,n,e) -> (f,flat_Recclosure env funs' f)) funs) env'`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[FORALL_PAIR_THM; ITLIST; MAP; APPEND; pair_CASE] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* Alternate definition for build_rec_env *)
let flat_build_rec_env_merge = prove
 (CASE_TERM
  `!funs (funs':A) env env'.
     flat_build_rec_env funs env env' =
     APPEND (MAP (\fne. match fne with
                          (f,n,e) -> (f,flat_Recclosure env funs f)) funs) env'`,
  REWRITE_TAC[flat_build_rec_env_def; flat_build_rec_env_help_lem]);;

(* a local helper: list_result in the GVS case splits *)
let FLATSEMAUX_list_result_eq = prove
 (`(!(r:(A,B)result) vs. list_result r = Rval vs <=> ?v. r = Rval v /\ vs = [v]) /\
   (!(r:(A,B)result) e. list_result r = Rerr e <=> r = Rerr e)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN CASES_ON `r:(A,B)result` THEN
  REWRITE_TAC[list_result_def; distinctness "result"; injectivity "result"] THEN
  MESON_TAC[]);;

let flat_evaluate_length = prove
 (`!env (s:(C,FFI)flat_state) ls s' vs.
     flat_evaluate env s ls = (s',Rval vs) ==> LENGTH vs = LENGTH ls`,
  MATCH_MP_TAC (REWRITE_RULE[]
    (ISPECL [`\env (s:(C,FFI)flat_state) ls. !s' vs.
                flat_evaluate env s ls = (s',Rval vs) ==> LENGTH vs = LENGTH ls`;
             `\(s:(C,FFI)flat_state) (d:flat_exp). T`;
             `\(s:(C,FFI)flat_state) (ds:flat_exp list). T`] flat_evaluate_ind)) THEN
  REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[flat_evaluate_def] THEN
  DISCH_TAC THEN GVS(FLATSEMAUX_clock_case_eqs @ [FLATSEMAUX_list_result_eq]) THEN
  RES_TAC THEN ASM_REWRITE_TAC[LENGTH]);;

let flat_evaluate_cons = prove
 (CASE_TERM `!env (s:(C,FFI)flat_state) e es.
     flat_evaluate env s (CONS e es) =
     match flat_evaluate env s [e] with
       (s1,Rval v) -> (match flat_evaluate env s1 es with
                          (s2,Rval vs) -> (s2,Rval (APPEND v vs))
                        | r -> r)
     | r -> r`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!s1 v. flat_evaluate env (s:(C,FFI)flat_state) [e] = (s1,Rval v) ==>
                       ?y. v = [y]` MP_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP flat_evaluate_length) THEN
    REWRITE_TAC[LENGTH; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN MESON_TAC[];
    ALL_TAC] THEN
  CASES_ON `es:flat_exp list` THEN REWRITE_TAC[flat_evaluate_def] THEN
  CASES_ON `flat_evaluate env (s:(C,FFI)flat_state) [e]` THEN
  ASM_REWRITE_TAC[pair_CASE] THEN
  CASES_ON `y:(flat_v list,flat_v)result` THEN
  REWRITE_TAC[case_def "result"; pair_CASE; APPEND_NIL; PAIR_EQ;
              injectivity "result"] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:(C,FFI)flat_state`; `a:flat_v list`]) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[HD; APPEND]);;

let flat_evaluate_sing = prove
 (`!env (s:(C,FFI)flat_state) e s' vs.
     flat_evaluate env s [e] = (s',Rval vs) ==> ?y. vs = [y]`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP flat_evaluate_length) THEN
  REWRITE_TAC[LENGTH; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN MESON_TAC[]);;

let flat_evaluate_append = prove
 (CASE_TERM `!env l1 (s:(C,FFI)flat_state) l2.
     flat_evaluate env s (APPEND l1 l2) =
     match flat_evaluate env s l1 with
       (s1,Rval v1) -> (match flat_evaluate env s1 l2 with
                          (s2,Rval v2) -> (s2,Rval (APPEND v1 v2))
                        | r -> r)
     | r -> r`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; flat_evaluate_def; pair_CASE; case_def "result"] THEN
    REPEAT GEN_TAC THEN CASES_ON `flat_evaluate env (s:(C,FFI)flat_state) l2` THEN
    CASES_ON `y:(flat_v list,flat_v)result` THEN
    REWRITE_TAC[pair_CASE; case_def "result"];
    REPEAT GEN_TAC THEN REWRITE_TAC[APPEND] THEN
    ONCE_REWRITE_TAC[flat_evaluate_cons] THEN ASM_REWRITE_TAC[] THEN
    EVERY_CASE_TAC THEN FS[APPEND_ASSOC]]);;

(* HOL4 quantifies an unused c *)
let do_app_state_unchanged = prove
 (`!(c:A) (s:(C,FFI)flat_state) op vs s' r.
     flat_do_app s op vs = SOME (s',r) ==>
     flat_state_eval_config s' = flat_state_eval_config s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flat_do_app_def] THEN DISCH_TAC THEN
  FLATSEMAUX_SPLIT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  REWRITE_TAC[flat_state_INFO.ri_accfupds]);;

(* HOL4 quantifies the unused s1, s2 and r *)
let flat_evaluate_decs_append = prove
 (CASE_TERM `!(s:(C,FFI)flat_state) ds1 (s1:(C,FFI)flat_state) (s2:(C,FFI)flat_state)
              (r:(flat_v error_result)option) ds2.
     flat_evaluate_decs s (APPEND ds1 ds2) =
     match flat_evaluate_decs s ds1 with
       (s1,NONE) -> flat_evaluate_decs s1 ds2
     | (s1,SOME err) -> (s1,SOME err)`,
  GEN_TAC THEN GEN_TAC THEN SPEC_TAC(`s:(C,FFI)flat_state`,`s:(C,FFI)flat_state`) THEN
  SPEC_TAC(`ds1:flat_exp list`,`ds1:flat_exp list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; flat_evaluate_def; pair_CASE; option_CASE] THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN SIMP[]);;

(* a local helper: do_app commutes with setting the clock *)
let FLATSEMAUX_do_app_clock = prove
 (`!(s:(C,FFI)flat_state) op es t r c.
     flat_do_app s op es = SOME (t,r) ==>
     flat_do_app (flat_state_clock_fupd (K c) s) op es =
     SOME (flat_state_clock_fupd (K c) t,r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flat_do_app_def] THEN DISCH_TAC THEN
  FLATSEMAUX_SPLIT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  SIMP[LET_DEF; LET_END_DEF] THEN FS[IS_NONE_EQ_NONE]);;

(* HOL4 [local] *)
let flat_do_app_add_to_clock = prove
 (`!(s:(C,FFI)flat_state) op es t r k.
     flat_do_app s op es = SOME (t,r) ==>
     flat_do_app (flat_state_clock_fupd (K (flat_state_clock s + k)) s) op es =
     SOME (flat_state_clock_fupd (K (flat_state_clock t + k)) t,r)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o MATCH_MP flat_do_app_const) THEN
  MATCH_MP_TAC FLATSEMAUX_do_app_clock THEN ASM_REWRITE_TAC[]);;

(* HOL4 [local] *)
let do_app_add_to_clock_NONE = prove
 (`!(s:(C,FFI)flat_state) op es k.
     flat_do_app s op es = NONE ==>
     flat_do_app (flat_state_clock_fupd (K (flat_state_clock s + k)) s) op es = NONE`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `flat_do_app (flat_state_clock_fupd (K (flat_state_clock s + k))
                               (s:(C,FFI)flat_state)) op es` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `a:(C,FFI)flat_state#(flat_v,flat_v)result` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(C,FFI)flat_state`
              (X_CHOOSE_THEN `r:(flat_v,flat_v)result` SUBST_ALL_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `flat_state_clock (s:(C,FFI)flat_state)` o
              MATCH_MP FLATSEMAUX_do_app_clock) THEN
  SUBGOAL_THEN `flat_state_clock_fupd (K (flat_state_clock s))
                  (flat_state_clock_fupd (K (flat_state_clock s + k))
                     (s:(C,FFI)flat_state)) = s` SUBST1_TAC THENL
   [REWRITE_TAC[flat_state_component_equality; flat_state_INFO.ri_accfupds; K_THM];
    ASM_REWRITE_TAC[option_DISTINCT]]);;

(* a local helper: dec_clock after adding to the clock *)
let FLATSEMAUX_dec_clock_add = prove
 (`!(s:(C,FFI)flat_state) n extra.
     flat_state_clock s = n /\ ~(n = 0) ==>
     flat_dec_clock (flat_state_clock_fupd (K (n + extra)) s) =
     flat_state_clock_fupd (K (flat_state_clock (flat_dec_clock s) + extra))
       (flat_dec_clock s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[flat_dec_clock_def] THEN
  REWRITE_TAC[flat_state_component_equality; flat_state_INFO.ri_accfupds; K_THM] THEN
  ASM_ARITH_TAC);;

(* HOL4 leaves extra free *)
let flat_evaluate_add_to_clock = prove
 (`(!env (s:(C,FFI)flat_state) es s' r extra.
      flat_evaluate env s es = (s',r) /\ ~(r = Rerr (Rabort Rtimeout_error)) ==>
      flat_evaluate env (flat_state_clock_fupd (K (flat_state_clock s + extra)) s) es =
      (flat_state_clock_fupd (K (flat_state_clock s' + extra)) s',r)) /\
   (!(s:(C,FFI)flat_state) d s' r extra.
      evaluate_dec s d = (s',r) /\ ~(r = SOME (Rabort Rtimeout_error)) ==>
      evaluate_dec (flat_state_clock_fupd (K (flat_state_clock s + extra)) s) d =
      (flat_state_clock_fupd (K (flat_state_clock s' + extra)) s',r)) /\
   (!(s:(C,FFI)flat_state) ds s' r extra.
      flat_evaluate_decs s ds = (s',r) /\ ~(r = SOME (Rabort Rtimeout_error)) ==>
      flat_evaluate_decs (flat_state_clock_fupd (K (flat_state_clock s + extra)) s) ds =
      (flat_state_clock_fupd (K (flat_state_clock s' + extra)) s',r))`,
  MATCH_MP_TAC flat_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN
  POP_ASSUM (fun nt -> POP_ASSUM (fun ev -> ASSUME_TAC nt THEN MP_TAC ev)) THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN DISCH_TAC THEN
  GVS(FLATSEMAUX_clock_case_eqs @ [FLATSEMAUX_list_result_eq]) THEN
  FLATSEMAUX_FWD_TAC [flat_do_app_add_to_clock] THEN
  ASM_SIMP_TAC[FLATSEMAUX_dec_clock_add; flat_state_INFO.ri_accfupds; K_THM;
               do_app_add_to_clock_NONE] THEN
  SIMP[]);;

let flat_evaluate_decs_add_to_clock = prove
 (`!decs (s:(C,FFI)flat_state) s' r extra.
     ~(r = SOME (Rabort Rtimeout_error)) /\ flat_evaluate_decs s decs = (s',r) ==>
     flat_evaluate_decs (flat_state_clock_fupd (K (flat_state_clock s + extra)) s) decs =
     (flat_state_clock_fupd (K (flat_state_clock s' + extra)) s',r)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (CONJUNCT2 (CONJUNCT2 flat_evaluate_add_to_clock)) THEN
  ASM_REWRITE_TAC[]);;


(* a local helper: call_FFI only extends the io_events *)
let FLATSEMAUX_call_FFI_io_events = prove
 (`!(st:(FFI)ffi_state) s conf bytes t' ws'.
     call_FFI st s conf bytes = FFI_return t' ws' ==>
     ffi_state_io_events st <<= ffi_state_io_events t'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[call_FFI_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[injectivity "ffi_result"] THENL
   [CASES_ON `ffi_state_oracle (st:(FFI)ffi_state) s (ffi_state_ffi_state st) conf bytes` THEN
    REWRITE_TAC[case_def "oracle_result"; distinctness "ffi_result"] THEN
    COND_CASES_TAC THEN REWRITE_TAC[distinctness "ffi_result"; injectivity "ffi_result"] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
    REWRITE_TAC[ffi_state_INFO.ri_accfupds; K_THM; IS_PREFIX_APPEND] THEN MESON_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN REWRITE_TAC[IS_PREFIX_REFL]]);;

let flat_do_app_io_events_mono = prove
 (`!(s:(C,FFI)flat_state) op vs t r.
     flat_do_app s op vs = SOME (t,r) ==>
     ffi_state_io_events (flat_state_ffi s) <<= ffi_state_io_events (flat_state_ffi t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flat_do_app_def] THEN DISCH_TAC THEN
  FLATSEMAUX_SPLIT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  REWRITE_TAC[flat_state_INFO.ri_accfupds; K_THM; IS_PREFIX_REFL] THEN
  FLATSEMAUX_FWD_TAC [FLATSEMAUX_call_FFI_io_events] THEN ASM_REWRITE_TAC[]);;

(* a local helper: evaluate_io_events_mono for the result state *)
let FLATSEMAUX_io_events_mono = prove
 (`(!env (s:(C,FFI)flat_state) es s' r.
      flat_evaluate env s es = (s',r) ==>
      ffi_state_io_events (flat_state_ffi s) <<= ffi_state_io_events (flat_state_ffi s')) /\
   (!(s:(C,FFI)flat_state) d s' r.
      evaluate_dec s d = (s',r) ==>
      ffi_state_io_events (flat_state_ffi s) <<= ffi_state_io_events (flat_state_ffi s')) /\
   (!(s:(C,FFI)flat_state) ds s' r.
      flat_evaluate_decs s ds = (s',r) ==>
      ffi_state_io_events (flat_state_ffi s) <<= ffi_state_io_events (flat_state_ffi s'))`,
  MATCH_MP_TAC flat_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[flat_evaluate_def] THEN
  DISCH_TAC THEN GVS(FLATSEMAUX_clock_case_eqs @ [flat_dec_clock_def; FLATSEMAUX_list_result_eq]) THEN
  FLATSEMAUX_FWD_TAC [flat_do_app_io_events_mono] THEN
  RES_TAC THEN RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_state_INFO.ri_accfupds; K_THM]) THEN
  REWRITE_TAC[flat_state_INFO.ri_accfupds; K_THM; IS_PREFIX_REFL] THEN
  ASM_MESON_TAC[isPREFIX_TRANS; IS_PREFIX_REFL]);;

let flat_evaluate_io_events_mono = prove
 (`(!env (s:(C,FFI)flat_state) es.
      ffi_state_io_events (flat_state_ffi s) <<=
      ffi_state_io_events (flat_state_ffi (FST (flat_evaluate env s es)))) /\
   (!(s:(C,FFI)flat_state) d.
      ffi_state_io_events (flat_state_ffi s) <<=
      ffi_state_io_events (flat_state_ffi (FST (evaluate_dec s d)))) /\
   (!(s:(C,FFI)flat_state) ds.
      ffi_state_io_events (flat_state_ffi s) <<=
      ffi_state_io_events (flat_state_ffi (FST (flat_evaluate_decs s ds))))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  MESON_TAC[FLATSEMAUX_io_events_mono; PAIR]);;

(* HOL4 leaves all variables free *)
let evaluate_io_events_mono_IMP = prove
 (`(!env (s:(C,FFI)flat_state) es s' r.
      flat_evaluate env s es = (s',r) ==>
      ffi_state_io_events (flat_state_ffi s) <<= ffi_state_io_events (flat_state_ffi s')) /\
   (!(s:(C,FFI)flat_state) d s' r'.
      evaluate_dec s d = (s',r') ==>
      ffi_state_io_events (flat_state_ffi s) <<= ffi_state_io_events (flat_state_ffi s')) /\
   (!(s:(C,FFI)flat_state) ds s' r''.
      flat_evaluate_decs s ds = (s',r'') ==>
      ffi_state_io_events (flat_state_ffi s) <<= ffi_state_io_events (flat_state_ffi s'))`,
  REWRITE_TAC[FLATSEMAUX_io_events_mono]);;

let flat_with_clock_ffi = prove
 (`!(s:(C,FFI)flat_state) k.
     flat_state_ffi (flat_state_clock_fupd (K k) s) = flat_state_ffi s`,
  REWRITE_TAC[flat_state_INFO.ri_accfupds]);;

(* local helpers for evaluate_add_to_clock_io_events_mono: evaluate_add_to_clock
   with curried hypotheses; the split of the assumptions of one of the two runs;
   a prefix chain closer *)

let FLATSEMAUX_atc_curried = prove
 (`(!env (s:(C,FFI)flat_state) es s' r.
      flat_evaluate env s es = (s',r) ==> ~(r = Rerr (Rabort Rtimeout_error)) ==>
      !extra.
      flat_evaluate env (flat_state_clock_fupd (K (flat_state_clock s + extra)) s) es =
      (flat_state_clock_fupd (K (flat_state_clock s' + extra)) s',r)) /\
   (!(s:(C,FFI)flat_state) d s' r.
      evaluate_dec s d = (s',r) ==> ~(r = SOME (Rabort Rtimeout_error)) ==>
      !extra.
      evaluate_dec (flat_state_clock_fupd (K (flat_state_clock s + extra)) s) d =
      (flat_state_clock_fupd (K (flat_state_clock s' + extra)) s',r)) /\
   (!(s:(C,FFI)flat_state) ds s' r.
      flat_evaluate_decs s ds = (s',r) ==> ~(r = SOME (Rabort Rtimeout_error)) ==>
      !extra.
      flat_evaluate_decs (flat_state_clock_fupd (K (flat_state_clock s + extra)) s) ds =
      (flat_state_clock_fupd (K (flat_state_clock s' + extra)) s',r))`,
  MESON_TAC[flat_evaluate_add_to_clock]);;

let FLATSEMAUX_SPLIT_ONE_P_TAC (p:term->bool) : tactic =
  FIRST_X_ASSUM (fun th ->
    if not (p (concl th)) then failwith "FLATSEMAUX_SPLIT_ONE_P_TAC" else
    let l,_ = dest_eq (concl th) in
    if is_case_app l then
      let c,_,_ = dest_case_app l in
      let ci = case_info_of_const c in
      STRIP_ASSUME_TAC
        (REWRITE_RULE (ci.ci_case_eq :: FLATSEMAUX_split_rewrites) th)
    else if is_cond l then
      STRIP_ASSUME_TAC (REWRITE_RULE (COND_CASE_EQ :: FLATSEMAUX_split_rewrites) th)
    else if is_let l then
      ASSUME_TAC (CONV_RULE (LAND_CONV let_CONV) th)
    else failwith "FLATSEMAUX_SPLIT_ONE_P_TAC");;

let FLATSEMAUX_has_extra t =
  can (find_term (fun u -> is_var u && fst(dest_var u) = "extra")) t;;

(* a local helper tactic: prove l <<= r from the isPREFIX assumptions by a  *)
(* chain of isPREFIX_TRANS steps (breadth-first search over the facts)      *)

let FLATSEMAUX_PREFIX_CHAIN_TAC : tactic = fun (asl,w as g) ->
  let is_pre t = try let f,args = strip_comb t in
                     is_const f && fst(dest_const f) = "isPREFIX" && length args = 2
                 with Failure _ -> false in
  if not (is_pre w) then failwith "FLATSEMAUX_PREFIX_CHAIN_TAC" else
  let l,r = match snd(strip_comb w) with [a;b] -> a,b | _ -> failwith "chain" in
  if aconv l r then ACCEPT_TAC (ISPEC l IS_PREFIX_REFL) g else
  let facts = filter (fun th -> is_pre (concl th)) (map snd asl) in
  let edges = map (fun th -> match snd(strip_comb(concl th)) with
                               [a;b] -> a,(b,th) | _ -> failwith "chain") facts in
  (* breadth-first search: proved maps a term t to a theorem l <<= t *)
  let rec bfs frontier visited =
    match frontier with
      [] -> failwith "FLATSEMAUX_PREFIX_CHAIN_TAC: no chain"
    | (t,th)::rest ->
        if aconv t r then th else
        let nexts = filter (fun (a,(b,_)) -> aconv a t &&
                                not (exists (aconv b) visited)) edges in
        let new_items = map (fun (_,(b,th2)) ->
                               b, MATCH_MP isPREFIX_TRANS (CONJ th th2)) nexts in
        bfs (rest @ new_items) (map fst new_items @ visited) in
  let start = filter (fun (a,_) -> aconv a l) edges in
  let init = map (fun (_,(b,th)) -> b,th) start in
  ACCEPT_TAC (bfs init (l :: map fst init)) g;;

(* a local helper: evaluate_add_to_clock_io_events_mono for the result states *)
let FLATSEMAUX_atc_io = prove
 (`(!env (s:(C,FFI)flat_state) es s1 r1 extra s2 r2.
      flat_evaluate env s es = (s1,r1) /\
      flat_evaluate env (flat_state_clock_fupd (K (flat_state_clock s + extra)) s) es =
      (s2,r2) ==>
      ffi_state_io_events (flat_state_ffi s1) <<= ffi_state_io_events (flat_state_ffi s2)) /\
   (!(s:(C,FFI)flat_state) d s1 r1 extra s2 r2.
      evaluate_dec s d = (s1,r1) /\
      evaluate_dec (flat_state_clock_fupd (K (flat_state_clock s + extra)) s) d =
      (s2,r2) ==>
      ffi_state_io_events (flat_state_ffi s1) <<= ffi_state_io_events (flat_state_ffi s2)) /\
   (!(s:(C,FFI)flat_state) ds s1 r1 extra s2 r2.
      flat_evaluate_decs s ds = (s1,r1) /\
      flat_evaluate_decs (flat_state_clock_fupd (K (flat_state_clock s + extra)) s) ds =
      (s2,r2) ==>
      ffi_state_io_events (flat_state_ffi s1) <<= ffi_state_io_events (flat_state_ffi s2))`,
  MATCH_MP_TAC flat_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN
  POP_ASSUM (fun e2 -> POP_ASSUM (fun e1 -> MP_TAC e1 THEN MP_TAC e2)) THEN
  ONCE_REWRITE_TAC[flat_evaluate_def] THEN REPEAT DISCH_TAC THEN
  REPEAT (FLATSEMAUX_SPLIT_ONE_P_TAC (not o FLATSEMAUX_has_extra)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
           check (fun th -> is_var(rhs(concl th)) && not(FLATSEMAUX_has_extra(concl th))))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o
           check (fun th -> is_var(lhs(concl th)) && not(FLATSEMAUX_has_extra(concl th))))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_state_INFO.ri_accfupds; K_THM]) THEN
  FLATSEMAUX_FWD_TAC [FLATSEMAUX_atc_curried; FLATSEMAUX_do_app_clock;
                      do_app_add_to_clock_NONE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[distinctness "result"; injectivity "result";
                              option_DISTINCT; option_INJ; distinctness "error_result";
                              injectivity "error_result"]) THEN
  (fun (asl,w as g) ->
     let ths = map snd asl in
     let is_eval_eq t =
       let t' = snd(strip_forall t) in
       is_eq t' && (try mem (fst(dest_const(fst(strip_comb(lhs t')))))
                          ["flat_evaluate"; "evaluate_dec"; "flat_evaluate_decs";
                           "flat_do_app"]
                    with Failure _ -> false) in
     let facts = filter (fun th -> let t = concl th in
                           (is_forall t && is_eval_eq t) ||
                           (not (is_forall t) && not (FLATSEMAUX_has_extra t))) ths in
     RULE_ASSUM_TAC (fun th ->
       if FLATSEMAUX_has_extra (concl th) && not (is_forall (concl th))
       then CAKE_SIMP_RULE (facts @ [pmatch_rows_ignore_clock; FLATSEMAUX_dec_clock_add;
                                     flat_state_INFO.ri_accfupds; K_THM]) th
       else th) g) THEN
  FLATSEMAUX_SPLIT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  REWRITE_TAC[flat_state_INFO.ri_accfupds; K_THM; IS_PREFIX_REFL] THEN
  FLATSEMAUX_FWD_TAC [evaluate_io_events_mono_IMP; flat_do_app_io_events_mono] THEN
  RES_TAC THEN RES_TAC THEN RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_dec_clock_def; flat_state_INFO.ri_accfupds; K_THM]) THEN
  REWRITE_TAC[flat_dec_clock_def; flat_state_INFO.ri_accfupds; K_THM] THEN
  TRY FLATSEMAUX_PREFIX_CHAIN_TAC THEN
  TRY (FS[] THEN NO_TAC));;

(* HOL4 leaves extra free *)
let flat_evaluate_add_to_clock_io_events_mono = prove
 (`(!env (s:(C,FFI)flat_state) es extra.
      ffi_state_io_events (flat_state_ffi (FST (flat_evaluate env s es))) <<=
      ffi_state_io_events (flat_state_ffi (FST (flat_evaluate env
        (flat_state_clock_fupd (K (flat_state_clock s + extra)) s) es)))) /\
   (!(s:(C,FFI)flat_state) d extra.
      ffi_state_io_events (flat_state_ffi (FST (evaluate_dec s d))) <<=
      ffi_state_io_events (flat_state_ffi (FST (evaluate_dec
        (flat_state_clock_fupd (K (flat_state_clock s + extra)) s) d)))) /\
   (!(s:(C,FFI)flat_state) ds extra.
      ffi_state_io_events (flat_state_ffi (FST (flat_evaluate_decs s ds))) <<=
      ffi_state_io_events (flat_state_ffi (FST (flat_evaluate_decs
        (flat_state_clock_fupd (K (flat_state_clock s + extra)) s) ds))))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN MESON_TAC[FLATSEMAUX_atc_io; PAIR]);;

let evaluate_dec_io_events_mono = prove
 (`!z (y:(C,FFI)flat_state).
     ffi_state_io_events (flat_state_ffi y) <<=
     ffi_state_io_events (flat_state_ffi (FST (evaluate_dec y z)))`,
  REWRITE_TAC[flat_evaluate_io_events_mono]);;

let evaluate_dec_add_to_clock_io_events_mono = prove
 (`!prog (s:(C,FFI)flat_state) extra.
     ffi_state_io_events (flat_state_ffi (FST (evaluate_dec s prog))) <<=
     ffi_state_io_events (flat_state_ffi (FST (evaluate_dec
       (flat_state_clock_fupd (K (flat_state_clock s + extra)) s) prog)))`,
  REWRITE_TAC[flat_evaluate_add_to_clock_io_events_mono]);;

let evaluate_decs_io_events_mono = prove
 (`!ds (s:(C,FFI)flat_state) s' y.
     flat_evaluate_decs s ds = (s',y) ==>
     ffi_state_io_events (flat_state_ffi s) <<= ffi_state_io_events (flat_state_ffi s')`,
  REWRITE_TAC[evaluate_io_events_mono_IMP]);;

let flat_evaluate_decs_add_to_clock_io_events_mono = prove
 (`!ds (s:(C,FFI)flat_state) extra.
     ffi_state_io_events (flat_state_ffi (FST (flat_evaluate_decs s ds))) <<=
     ffi_state_io_events (flat_state_ffi (FST (flat_evaluate_decs
       (flat_state_clock_fupd (K (flat_state_clock s + extra)) s) ds)))`,
  REWRITE_TAC[flat_evaluate_add_to_clock_io_events_mono]);;

(* HOL4 leaves env, xs, vs, s, t free *)
let evaluate_MAP_Var_local = prove
 (`!env (s:(C,FFI)flat_state) t xs vs.
     MAP (ALOOKUP (flat_environment_v env)) xs = MAP SOME vs ==>
     flat_evaluate env s (MAP (Var_local t) xs) = (s,Rval vs)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; flat_evaluate_def] THENL
   [MESON_TAC[MAP_EQ_NIL]; ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[flat_evaluate_cons] THEN
  ASM_REWRITE_TAC[flat_evaluate_def; option_CASE; pair_CASE; case_def "result"] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t'':flat_v list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[pair_CASE; case_def "result"; APPEND]);;

(* HOL4's MAP2 truncates; HOL Light's MAP2 is used with lists of equal       *)
(* lengths (the uses below have LENGTH ts = LENGTH ks)                        *)
let bind_locals_list_def = cake_def
  `bind_locals_list ts ks = MAP2 (\t x. Var_local t x) ts ks`;;

let evaluate_vars = prove
 (`!env (s:(C,FFI)flat_state) kvs env' ks vs ts.
     ALL_DISTINCT (MAP FST kvs) /\
     DISJOINT (set_of_list (MAP FST kvs)) (set_of_list (MAP FST env')) /\
     flat_environment_v env = APPEND env' kvs /\ ks = MAP FST kvs /\
     vs = MAP SND kvs /\ LENGTH ts = LENGTH ks
     ==> flat_evaluate env s (bind_locals_list ts ks) = (s,Rval vs)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[MAP; LENGTH] THEN REPEAT STRIP_TAC THEN
    FS[LENGTH_EQ_NIL; bind_locals_list_def; MAP2; flat_evaluate_def];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:varN`; `v:flat_v`; `kvs:(varN#flat_v)list`] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ts:tra list` list_CASES) THEN
  REWRITE_TAC[MAP; LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; ALL_DISTINCT] THEN
  STRIP_TAC THENL [FS[LENGTH; NOT_SUC]; ALL_TAC] THEN
  SUBGOAL_THEN `flat_evaluate env (s:(C,FFI)flat_state)
                  (bind_locals_list t (MAP FST kvs)) = (s,Rval (MAP SND kvs))`
    MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `APPEND env' [k,v]:(varN#flat_v)list` THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
    CONJ_TAC THENL [ALL_TAC; FS[LENGTH_MAP]] THEN
    REWRITE_TAC[MAP_APPEND; MAP; SET_OF_LIST_APPEND; set_of_list] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
      let t = concl th in
      can (find_term (fun u -> is_const u && fst(dest_const u) = "DISJOINT")) t ||
      (is_neg t && can (find_term (fun u -> is_const u && fst(dest_const u) = "MEM")) t)))) THEN
    REWRITE_TAC[MAP; set_of_list; GSYM IN_SET_OF_LIST] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[bind_locals_list_def; MAP2] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[flat_evaluate_cons] THEN ASM_REWRITE_TAC[flat_evaluate_def] THEN
  SUBGOAL_THEN `ALOOKUP (env':(varN#flat_v)list) k = NONE` ASSUME_TAC THENL
   [REWRITE_TAC[ALOOKUP_NONE; GSYM IN_SET_OF_LIST] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun u -> is_const u && fst(dest_const u) = "DISJOINT")) (concl th)))) THEN
    REWRITE_TAC[MAP; set_of_list] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ALOOKUP_APPEND; option_CASE; ALOOKUP_THM; pair_CASE;
                  case_def "result"; APPEND] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    can (find_term (fun t -> t = `MAP2:(tra->varN->flat_exp)->tra list->varN list->flat_exp list`)) (concl th))) THEN
  REWRITE_TAC[bind_locals_list_def] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[pair_CASE; case_def "result"; APPEND]);;

(* HOL4's ZIP (xs,vs) is ZIP xs vs (equal lengths); HOL4 leaves s free *)
let pmatch_list_MAP_Pvar = prove
 (`!(s:(C,FFI)flat_state) xs vs.
     LENGTH xs = LENGTH vs ==>
     flat_pmatch_list s (MAP flat_Pvar xs) vs [] = Match (REVERSE (ZIP xs vs))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; ZIP; REVERSE] THEN
  REWRITE_TAC[flat_pmatch_def; case_def "match_result"] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[pmatch_nil] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t':flat_v list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[map_match_def; flip_DEF; HD; TL]);;

(* HOL4 [local]; HOL4 leaves all variables free *)
let evaluate_decs_add_to_clock_initial_state = prove
 (`!(ffi:(FFI)ffi_state) k (ec:(C)install_config) decs s' r ck.
     ~(r = SOME (Rabort Rtimeout_error)) /\
     flat_evaluate_decs (flat_initial_state ffi k ec) decs = (s',r) ==>
     flat_evaluate_decs (flat_initial_state ffi (ck + k) ec) decs =
     (flat_state_clock_fupd (K (flat_state_clock s' + ck)) s',r)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `ck:num` o MATCH_MP (CONJUNCT2 (CONJUNCT2
    (REWRITE_RULE[IMP_CONJ] flat_evaluate_add_to_clock)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[flat_initial_state_def; flat_state_INFO.ri_fupds; flat_state_INFO.ri_accessors;
              K_THM; injectivity "flat_state"] THEN ARITH_TAC);;

(* HOL4 [local] *)
let evaluate_decs_add_to_clock_initial_state_io_events_mono = prove
 (`!(ffi:(FFI)ffi_state) k (ec:(C)install_config) prog s' r ck.
     flat_evaluate_decs (flat_initial_state ffi k ec) prog = (s',r) ==>
     ffi_state_io_events (flat_state_ffi s') <<=
     ffi_state_io_events (flat_state_ffi
       (FST (flat_evaluate_decs (flat_initial_state ffi (k + ck) ec) prog)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`prog:flat_exp list`; `flat_initial_state (ffi:(FFI)ffi_state) k
                    (ec:(C)install_config)`; `ck:num`]
           flat_evaluate_decs_add_to_clock_io_events_mono) THEN
  ASM_REWRITE_TAC[FST] THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[flat_initial_state_def; flat_state_INFO.ri_fupds; flat_state_INFO.ri_accessors;
              K_THM]);;

(* HOL4 [local] *)
let flat_initial_state_with_clock = prove
 (`!(ffi:(FFI)ffi_state) k (ec:(C)install_config) ck.
     flat_state_clock_fupd
       (K (flat_state_clock (flat_initial_state ffi k ec) + ck))
       (flat_initial_state ffi k ec) =
     flat_initial_state ffi (k + ck) ec`,
  REWRITE_TAC[flat_initial_state_def; flat_state_INFO.ri_fupds;
              flat_state_INFO.ri_accessors; K_THM]);;

(* HOL4 [local] *)
let SND_SND_lemma = prove
 (`!(x:A#B) y. SND x = y <=> ?y1. x = (y1,y)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; SND] THEN MESON_TAC[]);;

let flat_eval_sim_def = cake_def
  `flat_eval_sim (ffi:(FFI)ffi_state) ds1 ds2 (ec:(C)install_config)
                 (ec2:(D)install_config) rel allow_fail <=>
     !k res1 s2.
       flat_evaluate_decs (flat_initial_state ffi k ec) ds1 = (s2,res1) /\
       (allow_fail \/ ~(res1 = SOME (Rabort Rtype_error))) /\
       rel ds1 ds2
       ==>
       ?ck res2 t2.
         flat_evaluate_decs (flat_initial_state ffi (k + ck) ec2) ds2 = (t2,res2) /\
         flat_state_ffi s2 = flat_state_ffi t2 /\
         (res1 = NONE ==> res2 = NONE) /\
         (!v. res1 = SOME (Rraise v) ==> ?v1. res2 = SOME (Rraise v1)) /\
         (!a. res1 = SOME (Rabort a) ==> res2 = SOME (Rabort a))`;;

(* a local helper: the result relation of eval_sim determines the aborts *)
let FLATSEMAUX_res_match = prove
 (`!(r1:((flat_v)error_result)option) (r2:((flat_v)error_result)option).
     (r1 = NONE ==> r2 = NONE) /\
     (!v. r1 = SOME (Rraise v) ==> ?v1. r2 = SOME (Rraise v1)) /\
     (!a. r1 = SOME (Rabort a) ==> r2 = SOME (Rabort a))
     ==> (!a. r2 = SOME (Rabort a) ==> r1 = SOME (Rabort a)) /\
         (r2 = NONE ==> r1 = NONE) /\
         (!v. r2 = SOME (Rraise v) ==> ?v1. r1 = SOME (Rraise v1))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r1:((flat_v)error_result)option` (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THENL
   [MESON_TAC[option_DISTINCT]; ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `a:(flat_v)error_result` (cases "error_result")) THEN
  REWRITE_TAC[injectivity "error_result"; distinctness "error_result"] THEN
  MESON_TAC[option_DISTINCT; option_INJ; injectivity "error_result";
            distinctness "error_result"]);;

(* local helpers for IMP_semantics_eq *)

let FLATSEMAUX_term_case = prove
 (CASE_TERM
  `!(r:((flat_v)error_result)option) outcome.
     (match r with
        SOME (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
      | SOME (Rabort _) -> F
      | _ -> outcome = Success) <=>
     (r = NONE /\ outcome = Success) \/
     (?v. r = SOME (Rraise v) /\ outcome = Success) \/
     (?e. r = SOME (Rabort (Rffi_error e)) /\ outcome = FFI_outcome e)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:((flat_v)error_result)option` (cases "option")) THEN
  REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ] THEN
  STRUCT_CASES_TAC(ISPEC `a:(flat_v)error_result` (cases "error_result")) THEN
  REWRITE_TAC[case_def "error_result"; injectivity "error_result";
              distinctness "error_result"; UNWIND_THM1; EXISTS_REFL] THEN
  STRUCT_CASES_TAC(ISPEC `a':abort` (cases "abort")) THEN
  REWRITE_TAC[case_def "abort"; injectivity "abort"; distinctness "abort";
              UNWIND_THM1; EXISTS_REFL] THEN MESON_TAC[]);;

let FLATSEMAUX_decs_mono = prove
 (`!(ffi:(FFI)ffi_state) (ec:(C)install_config) ds k d.
     ffi_state_io_events (flat_state_ffi
       (FST (flat_evaluate_decs (flat_initial_state ffi k ec) ds))) <<=
     ffi_state_io_events (flat_state_ffi
       (FST (flat_evaluate_decs (flat_initial_state ffi (k + d) ec) ds)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM flat_initial_state_with_clock] THEN
  REWRITE_TAC[flat_evaluate_decs_add_to_clock_io_events_mono]);;

let FLATSEMAUX_chain = prove
 (`!(ffi:(FFI)ffi_state) (ec:(C)install_config) ds.
     lprefix_chain (IMAGE (\k. llist_fromList (ffi_state_io_events (flat_state_ffi
       (FST (flat_evaluate_decs (flat_initial_state ffi k ec) ds))))) (:num))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lprefix_chain_def; FORALL_IN_IMAGE_2; IN_UNIV] THEN
  REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE] THEN
  MAP_EVERY X_GEN_TAC [`k1:num`; `k2:num`] THEN
  DISJ_CASES_TAC(SPECL [`k1:num`; `k2:num`] LE_CASES) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[FLATSEMAUX_decs_mono]);;

(* HOL4's proof: the semantics of ds1 is not Fail, so no clock gives a type
   error; by eval_sim, neither does any clock for ds2; the terminating
   behaviours are the same; the diverging ones have equivalent chains of io
   events *)
let flat_IMP_semantics_eq = prove
 (`!(ffi:(FFI)ffi_state) ds1 ds2 (ec:(C)install_config) (ec2:(D)install_config) rel.
     flat_eval_sim ffi ds1 ds2 ec ec2 rel F /\ ~(flat_semantics ec ffi ds1 = Fail) ==>
     rel ds1 ds2 ==>
     flat_semantics ec ffi ds1 = flat_semantics ec2 ffi ds2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!k. ~(SND (flat_evaluate_decs (flat_initial_state (ffi:(FFI)ffi_state) k
                      (ec:(C)install_config)) ds1) = SOME (Rabort Rtype_error))`
    (LABEL_TAC "nt1") THENL
   [UNDISCH_TAC `~(flat_semantics (ec:(C)install_config) (ffi:(FFI)ffi_state) ds1 = Fail)` THEN
    REWRITE_TAC[flat_semantics_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k s1 r1. flat_evaluate_decs (flat_initial_state (ffi:(FFI)ffi_state) k
                (ec:(C)install_config)) ds1 = (s1,r1) ==>
     ?ck r2 t2. flat_evaluate_decs (flat_initial_state ffi (k + ck)
                  (ec2:(D)install_config)) ds2 = (t2,r2) /\
        flat_state_ffi s1 = flat_state_ffi t2 /\ (r1 = NONE ==> r2 = NONE) /\
        (!v. r1 = SOME (Rraise v) ==> ?v1. r2 = SOME (Rraise v1)) /\
        (!a. r1 = SOME (Rabort a) ==> r2 = SOME (Rabort a))` (LABEL_TAC "sim") THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `flat_eval_sim (ffi:(FFI)ffi_state) ds1 ds2 (ec:(C)install_config)
                   (ec2:(D)install_config) rel F` THEN
    REWRITE_TAC[flat_eval_sim_def] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. ~(SND (flat_evaluate_decs (flat_initial_state (ffi:(FFI)ffi_state) k
                      (ec2:(D)install_config)) ds2) = SOME (Rabort Rtype_error))`
    (LABEL_TAC "nt2") THENL
   [GEN_TAC THEN REWRITE_TAC[SND_SND_lemma; NOT_EXISTS_THM] THEN
    X_GEN_TAC `y1:(D,FFI)flat_state` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `flat_evaluate_decs (flat_initial_state (ffi:(FFI)ffi_state) k
                    (ec:(C)install_config)) ds1` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:(C,FFI)flat_state`
      (X_CHOOSE_THEN `r1:((flat_v)error_result)option` ASSUME_TAC)) THEN
    USE_THEN "sim" (fun th -> FIRST_ASSUM (MP_TAC o MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r2:((flat_v)error_result)option`
      (X_CHOOSE_THEN `t2:(D,FFI)flat_state` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `r2 = SOME (Rabort Rtype_error):((flat_v)error_result)option`
      SUBST_ALL_TAC THENL
     [MP_TAC(ISPECL [`ffi:(FFI)ffi_state`; `k:num`; `ec2:(D)install_config`;
                     `ds2:flat_exp list`; `y1:(D,FFI)flat_state`;
                     `SOME (Rabort Rtype_error):((flat_v)error_result)option`;
                     `ck:num`] evaluate_decs_add_to_clock_initial_state) THEN
      ASM_REWRITE_TAC[option_INJ; injectivity "error_result"; distinctness "abort"] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `r1 = SOME (Rabort Rtype_error):((flat_v)error_result)option` MP_TAC THENL
     [MP_TAC(ISPECL [`r1:((flat_v)error_result)option`;
                     `SOME (Rabort Rtype_error):((flat_v)error_result)option`]
               FLATSEMAUX_res_match) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      USE_THEN "nt1" (MP_TAC o SPEC `k:num`) THEN
      FIRST_ASSUM(fun th ->
        if is_eq(concl th) &&
           rhs(concl th) = `s1:(C,FFI)flat_state,r1:((flat_v)error_result)option`
        then REWRITE_TAC[th; SND] else failwith "")];
    ALL_TAC] THEN
  SUBGOAL_THEN (CASE_TERM
   `!res. (?k s r outcome.
             flat_evaluate_decs (flat_initial_state (ffi:(FFI)ffi_state) k (ec:(C)install_config))
               ds1 = (s,r) /\
             (match r with
                SOME (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
              | SOME (Rabort _) -> F
              | _ -> outcome = Success) /\
             res = Terminate outcome (ffi_state_io_events (flat_state_ffi s))) <=>
          (?k s r outcome.
             flat_evaluate_decs (flat_initial_state ffi k (ec2:(D)install_config)) ds2 = (s,r) /\
             (match r with
                SOME (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
              | SOME (Rabort _) -> F
              | _ -> outcome = Success) /\
             res = Terminate outcome (ffi_state_io_events (flat_state_ffi s)))`) (LABEL_TAC "teq") THENL
   [GEN_TAC THEN REWRITE_TAC[FLATSEMAUX_term_case] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `s1:(C,FFI)flat_state`
     (X_CHOOSE_THEN `r1:((flat_v)error_result)option`
       (X_CHOOSE_THEN `outcome:outcome` STRIP_ASSUME_TAC)))) THEN
  USE_THEN "sim" (fun th -> FIRST_ASSUM (MP_TAC o MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r2:((flat_v)error_result)option`
     (X_CHOOSE_THEN `t2:(D,FFI)flat_state` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`k + ck:num`; `t2:(D,FFI)flat_state`;
                        `r2:((flat_v)error_result)option`; `outcome:outcome`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `s2:(D,FFI)flat_state`
     (X_CHOOSE_THEN `r2:((flat_v)error_result)option`
       (X_CHOOSE_THEN `outcome:outcome` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPEC `flat_evaluate_decs (flat_initial_state (ffi:(FFI)ffi_state) k
                  (ec:(C)install_config)) ds1` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(C,FFI)flat_state`
    (X_CHOOSE_THEN `r1:((flat_v)error_result)option` ASSUME_TAC)) THEN
  USE_THEN "sim" (fun th -> FIRST_ASSUM (MP_TAC o MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r2':((flat_v)error_result)option`
     (X_CHOOSE_THEN `t2:(D,FFI)flat_state` STRIP_ASSUME_TAC))) THEN
  (SUBGOAL_THEN `t2 = flat_state_clock_fupd (K (flat_state_clock s2 + ck)) (s2:(D,FFI)flat_state) /\
                r2' = (r2:((flat_v)error_result)option)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ffi:(FFI)ffi_state`; `k:num`; `ec2:(D)install_config`;
                   `ds2:flat_exp list`; `s2:(D,FFI)flat_state`;
                   `r2:((flat_v)error_result)option`; `ck:num`]
                  evaluate_decs_add_to_clock_initial_state) THEN
    ASM_REWRITE_TAC[option_DISTINCT; option_INJ; injectivity "error_result";
                    distinctness "error_result"; distinctness "abort"] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `r2':((flat_v)error_result)option = r2`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `t2:(D,FFI)flat_state`)) THEN
  (SUBGOAL_THEN `(!a. (r2:((flat_v)error_result)option) = SOME (Rabort a) ==>
                    (r1:((flat_v)error_result)option) = SOME (Rabort a)) /\
                (r2 = NONE ==> r1 = NONE) /\
                (!v. r2 = SOME (Rraise v) ==>
                     ?v1. r1 = SOME (Rraise v1):((flat_v)error_result)option)`
    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC FLATSEMAUX_res_match THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC]) THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `s1:(C,FFI)flat_state`;
                        `r1:((flat_v)error_result)option`; `outcome:outcome`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flat_state_INFO.ri_accfupds]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    lhs(concl th) = `r2:((flat_v)error_result)option`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; option_DISTINCT; injectivity "error_result";
    distinctness "error_result"; injectivity "abort"; distinctness "abort"]) THEN
  FS[]];
    ALL_TAC] THEN
  USE_THEN "nt1" (fun nt1 -> USE_THEN "nt2" (fun nt2 ->
    REWRITE_TAC[flat_semantics_def; nt1; nt2; some_DEF])) THEN
  USE_THEN "teq" (fun th -> REWRITE_TAC[th]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_CASE; injectivity "behaviour"] THEN
  MATCH_MP_TAC IMP_build_lprefix_lub_EQ THEN
  REWRITE_TAC[FLATSEMAUX_chain] THEN
  REWRITE_TAC[lprefix_rel_def; FORALL_IN_IMAGE; IN_UNIV; EXISTS_IN_IMAGE] THEN
  REWRITE_TAC[LPREFIX_fromList; from_toList; option_CASE] THEN
  CONJ_TAC THEN X_GEN_TAC `k:num` THEN
  MP_TAC(ISPEC `flat_evaluate_decs (flat_initial_state (ffi:(FFI)ffi_state) k
                  (ec:(C)install_config)) ds1` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(C,FFI)flat_state`
    (X_CHOOSE_THEN `r1:((flat_v)error_result)option` ASSUME_TAC)) THEN
  USE_THEN "sim" (fun th -> FIRST_ASSUM (MP_TAC o MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `r2:((flat_v)error_result)option`
     (X_CHOOSE_THEN `t2:(D,FFI)flat_state` STRIP_ASSUME_TAC))) THENL
   [EXISTS_TAC `k + ck:num` THEN ASM_REWRITE_TAC[FST; IS_PREFIX_REFL];
    EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[FST] THEN
    MP_TAC(ISPECL [`ffi:(FFI)ffi_state`; `ec2:(D)install_config`; `ds2:flat_exp list`;
                   `k:num`; `ck:num`] FLATSEMAUX_decs_mono) THEN
    ASM_REWRITE_TAC[FST]]);;

let flat_op_gbag_def = cake_def
  `(flat_op_gbag (GlobalVarInit n) = BAG_INSERT n EMPTY_BAG) /\
   (flat_op_gbag _ = EMPTY_BAG)`;;

(* a local helper: the termination conditions of recursion through MAP SND *)
(* and MAP (SND o SND) (flatLang's exp_size_MAP at the lists of the goal)    *)
let FLATSEMAUX_MAP_SIZE_TAC : tactic = fun (asl,w as g) ->
  let maps = find_terms (fun t -> is_comb t && is_comb (rator t) &&
               (try fst(dest_const(rator(rator t))) = "MAP" with Failure _ -> false)) w in
  let lists = map rand maps in
  let ths = flat (map (fun l -> mapfilter (fun c -> ISPEC l c) (CONJUNCTS exp_size_MAP))
                      lists) in
  (MAP_EVERY MP_TAC ths THEN REWRITE_TAC[o_DEF] THEN ARITH_TAC) g;;

(* HOL4's infix bag union is left-associative; variables of different types *)
(* in different clauses are named apart (one quotation)                       *)
let flat_set_globals_def = cake_def_wf
  `measure (\a:flat_exp + flat_exp list.
              sum_CASE a (\e. flat_exp_size e) (\es. list_size flat_exp_size es))`
  (REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
   RVEQ_TAC THEN REWRITE_TAC[measure_THM; sum_CASE] THEN
   REWRITE_TAC[type_size_def "flat_exp"; list_size] THEN
   REWRITE_TAC (flat (map snd (!the_size_aux_eqs))) THEN
   FLATSEMAUX_MAP_SIZE_TAC)
  `(flat_set_globals (flat_Raise t e) = flat_set_globals e) /\
   (flat_set_globals (flat_Handle t e pes) =
      BAG_UNION (flat_set_globals e) (flat_elist_globals (MAP SND pes))) /\
   (flat_set_globals (flat_Con t id es) = flat_elist_globals es) /\
   (flat_set_globals (flat_Fun n x e) = flat_set_globals e) /\
   (flat_set_globals (flat_App t op es) =
      BAG_UNION (flat_elist_globals es) (flat_op_gbag op)) /\
   (flat_set_globals (flat_If t e1 e2 e3) =
      BAG_UNION (BAG_UNION (flat_set_globals e1) (flat_set_globals e2))
                (flat_set_globals e3)) /\
   (flat_set_globals (flat_Mat t e pes) =
      BAG_UNION (flat_set_globals e) (flat_elist_globals (MAP SND pes))) /\
   (flat_set_globals (flat_Let t xo e1 e2) =
      BAG_UNION (flat_set_globals e1) (flat_set_globals e2)) /\
   (flat_set_globals (flat_Letrec n fs e) =
      BAG_UNION (flat_set_globals e) (flat_elist_globals (MAP (SND o SND) fs))) /\
   (flat_set_globals _ = EMPTY_BAG) /\
   (flat_elist_globals [] = EMPTY_BAG) /\
   (flat_elist_globals (CONS e es) =
      BAG_UNION (flat_set_globals e) (flat_elist_globals es))`;;
let _ = cake_add_simps [flat_set_globals_def];;

let flat_set_globals_ind = cake_ind "flat_set_globals";;

let flat_esgc_free_def = cake_def_wf
  `measure flat_exp_size`
  (REWRITE_TAC[measure_THM; IMP_CONJ] THEN REPEAT STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[measure_THM; MEM_MAP; o_DEF]) THEN
   REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
   RVEQ_TAC THEN
   REWRITE_TAC[type_size_def "flat_exp"; list_size] THEN
   REWRITE_TAC (flat (map snd (!the_size_aux_eqs))) THEN
   ASSUM_LIST (fun ths ->
     MAP_EVERY MP_TAC (mapfilter (MATCH_MP (CONJUNCT1 flat_exp_size_MEM)) ths @
                       mapfilter (MATCH_MP (CONJUNCT2 (CONJUNCT2 flat_exp_size_MEM))) ths)) THEN
   ASM_ARITH_TAC)
  `(flat_esgc_free (flat_Raise t e) <=> flat_esgc_free e) /\
   (flat_esgc_free (flat_Handle t e pes) <=>
      flat_esgc_free e /\ ALL flat_esgc_free (MAP SND pes)) /\
   (flat_esgc_free (flat_Con t id es) <=> ALL flat_esgc_free es) /\
   (flat_esgc_free (flat_Fun n x e) <=> flat_set_globals e = EMPTY_BAG) /\
   (flat_esgc_free (flat_App t op es) <=> ALL flat_esgc_free es) /\
   (flat_esgc_free (flat_If t e1 e2 e3) <=>
      flat_esgc_free e1 /\ flat_esgc_free e2 /\ flat_esgc_free e3) /\
   (flat_esgc_free (flat_Mat t e pes) <=>
      flat_esgc_free e /\ ALL flat_esgc_free (MAP SND pes)) /\
   (flat_esgc_free (flat_Let t xo e1 e2) <=> flat_esgc_free e1 /\ flat_esgc_free e2) /\
   (flat_esgc_free (flat_Letrec n fs e) <=>
      flat_esgc_free e /\ flat_elist_globals (MAP (SND o SND) fs) = EMPTY_BAG) /\
   (flat_esgc_free _ <=> T)`;;
let _ = cake_add_simps [flat_esgc_free_def];;

let flat_esgc_free_ind = cake_ind "flat_esgc_free";;

let elist_globals_eq_empty = prove
 (`!l. flat_elist_globals l = EMPTY_BAG <=>
       !e. MEM e l ==> flat_set_globals e = EMPTY_BAG`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[flat_set_globals_def; MEM; BAG_UNION_EMPTY] THEN
  MESON_TAC[]);;

let flat_elist_globals_append = prove
 (`!xs ys. flat_elist_globals (APPEND xs ys) =
           BAG_UNION (flat_elist_globals xs) (flat_elist_globals ys)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; flat_set_globals_def; BAG_UNION_EMPTY; ASSOC_BAG_UNION]);;

(* HOL4's FOLDR f e l is ITLIST f l e *)
let flat_elist_globals_FOLDR = prove
 (`!es. flat_elist_globals es =
        ITLIST BAG_UNION (MAP flat_set_globals es) EMPTY_BAG`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[flat_set_globals_def; MAP; ITLIST]);;

let elist_globals_REVERSE = prove
 (`!es. flat_elist_globals (REVERSE es) = flat_elist_globals es`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REVERSE; flat_elist_globals_append; flat_set_globals_def;
                  BAG_UNION_EMPTY] THEN
  MATCH_ACCEPT_TAC COMM_BAG_UNION);;

(* HOL4 leaves the variables free *)
let flat_initial_state_clock = prove
 (`!(ffi:(FFI)ffi_state) k (ec:(C)install_config) k1.
     flat_state_clock (flat_initial_state ffi k ec) = k /\
     flat_state_clock_fupd (K k1) (flat_initial_state ffi k ec) =
     flat_initial_state ffi k1 ec`,
  REWRITE_TAC[flat_initial_state_def; flat_state_INFO.ri_accessors;
              flat_state_INFO.ri_fupds; K_THM]);;

let build_rec_env_eq_MAP = prove
 (CASE_TERM
  `!funs (cl_env:(flat_v)flat_environment) env.
     flat_build_rec_env funs cl_env env =
     APPEND (MAP (\fxe. match fxe with
                          (f,x,e) -> (f,flat_Recclosure cl_env funs f)) funs) env`,
  REWRITE_TAC[flat_build_rec_env_merge]);;

(* HOL4 leaves the variables free *)
let evaluate_decs_add_to_clock_io_events_mono_alt = prove
 (`!(s:(C,FFI)flat_state) ds s1 res extra s2 res2.
     flat_evaluate_decs s ds = (s1,res) /\
     flat_evaluate_decs (flat_state_clock_fupd (K (flat_state_clock s + extra)) s) ds =
     (s2,res2) ==>
     ffi_state_io_events (flat_state_ffi s1) <<= ffi_state_io_events (flat_state_ffi s2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ds:flat_exp list`; `s:(C,FFI)flat_state`; `extra:num`]
           flat_evaluate_decs_add_to_clock_io_events_mono) THEN
  ASM_REWRITE_TAC[FST]);;

(* generic proof support for most val_rel/state_rel examples *)

let isClosure_def = cake_def
  `isClosure exp <=>
     (?vs n x. exp = flat_Closure vs n x) \/ (?vs fs x. exp = flat_Recclosure vs fs x)`;;

(* HOL4: isClosure_def at each constructor of v (HOL4 [simp]) *)
let isClosure_simps = prove
 (`(!l. isClosure (flat_Litv l) <=> F) /\
   (!x y. isClosure (flat_Conv x y) <=> F) /\
   (!a b c. isClosure (flat_Closure a b c) <=> T) /\
   (!a b c. isClosure (flat_Recclosure a b c) <=> T) /\
   (!b n. isClosure (flat_Loc b n) <=> F) /\
   (!vs. isClosure (flat_Vectorv vs) <=> F)`,
  REWRITE_TAC[isClosure_def; distinctness "flat_v"; injectivity "flat_v"] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [isClosure_simps];;

let simple_basic_val_rel_def = cake_def
  `(simple_basic_val_rel (flat_Litv l) v <=> v = flat_Litv l) /\
   (simple_basic_val_rel (flat_Loc b i) v <=> v = flat_Loc b i) /\
   (simple_basic_val_rel (flat_Conv stmp vs1) v <=> ?vs2. v = flat_Conv stmp vs2) /\
   (simple_basic_val_rel (flat_Vectorv vs1) v <=> ?vs2. v = flat_Vectorv vs2) /\
   (simple_basic_val_rel (flat_Closure vs nm exp) v <=> F) /\
   (simple_basic_val_rel (flat_Recclosure vs exps nm) v <=> F)`;;
let _ = cake_add_simps [simple_basic_val_rel_def];;

let v_container_xs_def = cake_def
  `(v_container_xs (flat_Litv _) = []) /\
   (v_container_xs (flat_Loc _ _) = []) /\
   (v_container_xs (flat_Conv _ vs) = vs) /\
   (v_container_xs (flat_Vectorv vs) = vs) /\
   (v_container_xs (flat_Closure env nm exp) = []) /\
   (v_container_xs (flat_Recclosure env exps nm) = [])`;;
let _ = cake_add_simps [v_container_xs_def];;

let flat_simple_val_rel_def = cake_def
  `flat_simple_val_rel (vr:flat_v->flat_v->bool) <=>
     (!v1 v2. vr v1 v2 ==> (isClosure v1 <=> isClosure v2)) /\
     (!v1 v2. ~isClosure v1 ==>
              (vr v1 v2 <=> simple_basic_val_rel v1 v2 /\
                            ALL2 vr (v_container_xs v1) (v_container_xs v2)))`;;

(* HOL4: a theorem with the hypothesis simple_val_rel vr *)
let simple_val_rel_rew =
  CONJUNCT2 (REWRITE_RULE[flat_simple_val_rel_def]
               (ASSUME `flat_simple_val_rel (vr:flat_v->flat_v->bool)`));;

(* HOL4: simple_val_rel_rew at each non-closure constructor of v *)
let simple_val_rel_simps =
  let rew = simple_val_rel_rew in
  let inst t = DISCH_ALL (GEN_ALL (REWRITE_RULE[isClosure_simps] (SPEC t rew))) in
  end_itlist CONJ
    (map inst [`flat_Litv l`; `flat_Conv x y`; `flat_Loc b n`; `flat_Vectorv vs`]);;
let _ = cake_add_simps [simple_val_rel_simps];;

let simple_val_rel_isClosure = prove
 (`!(vr:flat_v->flat_v->bool) x y.
     flat_simple_val_rel vr /\ vr x y ==> (isClosure x <=> isClosure y)`,
  REWRITE_TAC[flat_simple_val_rel_def] THEN MESON_TAC[]);;

let flat_simple_state_rel_def = cake_def
  `flat_simple_state_rel (vr:flat_v->flat_v->bool)
     (sr:(C,FFI)flat_state->(D,FFI)flat_state->bool) <=>
     (!s t. sr s t ==> ALL2 (sv_rel vr) (flat_state_refs s) (flat_state_refs t)) /\
     (!s t srefs trefs. sr s t /\ ALL2 (sv_rel vr) srefs trefs
        ==> sr (flat_state_refs_fupd (K srefs) s) (flat_state_refs_fupd (K trefs) t)) /\
     (!s t. sr s t ==> ALL2 (OPTREL vr) (flat_state_globals s) (flat_state_globals t)) /\
     (!s t sglob tglob. sr s t /\ ALL2 (OPTREL vr) sglob tglob
        ==> sr (flat_state_globals_fupd (K sglob) s) (flat_state_globals_fupd (K tglob) t)) /\
     (!s t. sr s t ==> flat_state_ffi s = flat_state_ffi t) /\
     (!s t sffi tffi. sr s t /\ sffi = tffi
        ==> sr (flat_state_ffi_fupd (K sffi) s) (flat_state_ffi_fupd (K tffi) t))`;;

(* HOL4 leaves vr free *)
let simple_do_eq_thm_ind = prove
 (`!vr. (!x1 y1 x2 y2 b. flat_simple_val_rel vr /\
      flat_do_eq x1 y1 = Eq_val b /\ vr x1 x2 /\ vr y1 y2
      ==> flat_do_eq x2 y2 = Eq_val b) /\
   (!x1 y1 x2 y2 b. flat_simple_val_rel vr /\
      flat_do_eq_list x1 y1 = Eq_val b /\ ALL2 vr x1 x2 /\ ALL2 vr y1 y2
      ==> flat_do_eq_list x2 y2 = Eq_val b)`,
  GEN_TAC THEN MATCH_MP_TAC flat_do_eq_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN GVS[flat_do_eq_def] THEN
  FLATSEMAUX_FWD_TAC[LIST_REL_LENGTH] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    let t = concl th in is_eq t && is_comb (rhs t) && is_const (rator (rhs t)) &&
                        fst(dest_const(rator(rhs t))) = "LENGTH" &&
                        is_var (rand (rhs t))))) THEN
  REPEAT COND_CASES_TAC THEN GVS[] THEN RES_TAC THEN GVS[] THEN
  ASSUM_LIST(fun ths ->
    let sim = find (fun th -> try fst(dest_const(rator(concl th))) = "flat_simple_val_rel"
                              with Failure _ -> false) ths in
    MAP_EVERY (fun th -> try ASSUME_TAC (MATCH_MP simple_val_rel_isClosure (CONJ sim th))
                         with Failure _ -> ALL_TAC) ths) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[isClosure_simps]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[isClosure_def]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_exists (concl th) || is_disj (concl th)))) THEN
  ASM_REWRITE_TAC[flat_do_eq_def] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_case_app (lhs (concl th)))) THEN
  MP_TAC(ISPEC `flat_do_eq v1 v2` (cases "eq_result")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[case_def "eq_result"; distinctness "eq_result"] THEN
  RES_TAC THEN RES_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[case_def "eq_result"] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[case_def "eq_result"] THEN DISCH_TAC THEN
  RES_TAC THEN RES_TAC THEN RES_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[case_def "eq_result"]);;

let simple_do_eq_thm = GEN `vr:flat_v->flat_v->bool`
  (CONJUNCT1 (SPEC `vr:flat_v->flat_v->bool` simple_do_eq_thm_ind));;

(* HOL4 leaves the variables free *)
let simple_state_rel_store_assign = prove
 (`!vr (sr:(C,FFI)flat_state->(D,FFI)flat_state->bool) lnum x s srefs' t y.
     flat_simple_state_rel vr sr /\
     store_assign lnum x (flat_state_refs s) = SOME srefs' /\
     sr s t /\ sv_rel vr x y ==>
     ?trefs'. store_assign lnum y (flat_state_refs t) = SOME trefs' /\
              sr (flat_state_refs_fupd (K srefs') s) (flat_state_refs_fupd (K trefs') t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flat_simple_state_rel_def; store_assign_def] THEN
  REWRITE_TAC[COND_CASE_EQ; option_DISTINCT; option_INJ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ALL2 (sv_rel vr) (flat_state_refs (s:(C,FFI)flat_state))
                  (flat_state_refs (t:(D,FFI)flat_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  SUBGOAL_THEN `sv_rel vr (EL lnum (flat_state_refs (s:(C,FFI)flat_state)))
                  (EL lnum (flat_state_refs (t:(D,FFI)flat_state)))` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL2 (sv_rel vr) (flat_state_refs (s:(C,FFI)flat_state))
                  (flat_state_refs (t:(D,FFI)flat_state))` THEN
    REWRITE_TAC[LIST_REL_EL_EQN] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `store_v_same_type (EL lnum (flat_state_refs (t:(D,FFI)flat_state)))
                  (y:flat_v store_v)` ASSUME_TAC THENL
   [UNDISCH_TAC `store_v_same_type (EL lnum (flat_state_refs (s:(C,FFI)flat_state)))
                   (x:flat_v store_v)` THEN
    UNDISCH_TAC `sv_rel vr (EL lnum (flat_state_refs (s:(C,FFI)flat_state)))
                  (EL lnum (flat_state_refs (t:(D,FFI)flat_state)))` THEN
    UNDISCH_TAC `sv_rel vr (x:flat_v store_v) (y:flat_v store_v)` THEN
    SPEC_TAC(`EL lnum (flat_state_refs (t:(D,FFI)flat_state)):flat_v store_v`,
             `b2:flat_v store_v`) THEN
    SPEC_TAC(`EL lnum (flat_state_refs (s:(C,FFI)flat_state)):flat_v store_v`,
             `b1:flat_v store_v`) THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[sv_rel_cases] THEN REPEAT STRIP_TAC THEN
    RVEQ_TAC THEN FS[store_v_same_type_def] THEN
    TRY (CASES_ON `m:thunk_mode` THEN FS[store_v_same_type_def]) THEN
    TRY (CASES_ON `m':thunk_mode` THEN FS[store_v_same_type_def]);
    ALL_TAC] THEN
  EXISTS_TAC `LUPDATE (y:flat_v store_v) lnum (flat_state_refs (t:(D,FFI)flat_state))` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `lnum < LENGTH (flat_state_refs (t:(D,FFI)flat_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq (concl th) && rhs(concl th) = `srefs':(flat_v store_v)list`)) THEN
  FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN CONJ_TAC THENL
    [FIRST_ASSUM ACCEPT_TAC;
     MATCH_MP_TAC EVERY2_LUPDATE_same THEN ASM_REWRITE_TAC[]]));;

(* HOL4 leaves the variables free *)
let simple_state_rel_store_alloc = prove
 (`!vr (sr:(C,FFI)flat_state->(D,FFI)flat_state->bool) x s srefs' lnum t y.
     flat_simple_state_rel vr sr /\
     store_alloc x (flat_state_refs s) = (srefs',lnum) /\
     sr s t /\ sv_rel vr x y ==>
     ?trefs'. store_alloc y (flat_state_refs t) = (trefs',lnum) /\
              sr (flat_state_refs_fupd (K srefs') s) (flat_state_refs_fupd (K trefs') t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flat_simple_state_rel_def; store_alloc_def; PAIR_EQ] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ALL2 (sv_rel vr) (flat_state_refs (s:(C,FFI)flat_state))
                  (flat_state_refs (t:(D,FFI)flat_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  EXISTS_TAC `APPEND (flat_state_refs (t:(D,FFI)flat_state)) [y:flat_v store_v]` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq (concl th) && rhs(concl th) = `srefs':(flat_v store_v)list`))) THEN
  FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN CONJ_TAC THENL
    [FIRST_ASSUM ACCEPT_TAC;
     MATCH_MP_TAC LIST_REL_APPEND_suff THEN ASM_REWRITE_TAC[ALL2]]));;

(* HOL4 leaves the variables free *)
let simple_state_rel_store_lookup = prove
 (`!vr (sr:(C,FFI)flat_state->(D,FFI)flat_state->bool) lnum s x t.
     flat_simple_state_rel vr sr /\
     store_lookup lnum (flat_state_refs s) = SOME x /\ sr s t ==>
     ?y. store_lookup lnum (flat_state_refs t) = SOME y /\ sv_rel vr x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flat_simple_state_rel_def; store_lookup_def] THEN
  REWRITE_TAC[COND_CASE_EQ; option_DISTINCT; option_INJ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ALL2 (sv_rel vr) (flat_state_refs (s:(C,FFI)flat_state))
                  (flat_state_refs (t:(D,FFI)flat_state))` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LIST_REL_EL_EQN] THEN STRIP_TAC THEN
  EXISTS_TAC `EL lnum (flat_state_refs (t:(D,FFI)flat_state))` THEN
  ASM_MESON_TAC[]);;

let simple_v_to_char_list_v_rel = prove
 (`!vr. flat_simple_val_rel vr ==>
        !x y ls. vr x y /\ flat_v_to_char_list x = SOME ls ==>
                 flat_v_to_char_list y = SOME ls`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC flat_v_to_char_list_ind THEN
  REPEAT STRIP_TAC THEN GVS[flat_v_to_char_list_def; option_case_eq] THEN
  RES_TAC THEN ASM_REWRITE_TAC[flat_v_to_char_list_def; option_CASE]);;

let simple_v_to_list_v_rel = prove
 (`!vr. flat_simple_val_rel vr ==>
        !x y ls. vr x y /\ flat_v_to_list x = SOME ls ==>
                 ?ls'. flat_v_to_list y = SOME ls' /\ ALL2 vr ls ls'`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC flat_v_to_list_ind THEN
  REPEAT STRIP_TAC THEN GVS[flat_v_to_list_def; option_case_eq] THEN
  RES_TAC THEN ASM_REWRITE_TAC[flat_v_to_list_def; option_CASE; option_INJ; ALL2] THEN
  ASM_MESON_TAC[]);;

let simple_v_rel_list_to_v = prove
 (`!vr. flat_simple_val_rel vr ==>
        !x y. ALL2 vr x y ==> vr (flat_list_to_v x) (flat_list_to_v y)`,
  GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[flat_list_to_v_def] THEN
  ASM_SIMP_TAC[simple_val_rel_simps; simple_basic_val_rel_def; v_container_xs_def;
               ALL2; injectivity "flat_v"] THEN
  ASM_MESON_TAC[]);;

let simple_vs_to_string_v_rel = prove
 (`!vr. flat_simple_val_rel vr ==>
        !vs ws str. ALL2 vr vs ws /\ flat_vs_to_string vs = SOME str ==>
                    flat_vs_to_string ws = SOME str`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC flat_vs_to_string_ind THEN
  REPEAT STRIP_TAC THEN GVS[flat_vs_to_string_def; option_case_eq; LIST_REL_CONS1;
                             LIST_REL_NIL] THEN
  RES_TAC THEN ASM_REWRITE_TAC[flat_vs_to_string_def; option_CASE]);;

(* a local helper: values related to literals are those literals *)
let FLATSEMAUX_rel_lits = prove
 (`!vr. flat_simple_val_rel vr ==>
        !(f:A->lit) ns ls'. ALL2 vr (MAP (flat_Litv o f) ns) ls' ==>
                            ls' = MAP (flat_Litv o f) ns`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; LIST_REL_NIL; LIST_REL_CONS1; o_THM] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try is_var (rator(rator(concl th)))
                                          with Failure _ -> false)) THEN
  ASM_SIMP_TAC[simple_val_rel_simps; simple_basic_val_rel_def; v_container_xs_def] THEN
  ASM_REWRITE_TAC[CONS_11; o_THM] THEN MESON_TAC[]);;

let flat_simple_val_rel_v_to_words = prove
 (`!vr. flat_simple_val_rel vr ==>
        !x y ws. vr x y /\ flat_v_to_words x = SOME ws ==> flat_v_to_words y = SOME ws`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `flat_v_to_list y = flat_v_to_list x` (fun th ->
    ASM_REWRITE_TAC[flat_v_to_words_def; th] THEN
    ASM_REWRITE_TAC[GSYM flat_v_to_words_def]) THEN
  UNDISCH_TAC `flat_v_to_words x = SOME (ws:int64 list)` THEN
  REWRITE_TAC[flat_v_to_words_def; some_DEF] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `ns:int64 list`) THEN
  MP_TAC(SPEC `vr:flat_v->flat_v->bool` simple_v_to_list_v_rel) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:flat_v`; `y:flat_v`;
                             `MAP (flat_Litv o Word64) (ns:int64 list)`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
  FIRST_ASSUM(fun sim -> MATCH_MP_TAC (MATCH_MP FLATSEMAUX_rel_lits sim)) THEN
  ASM_REWRITE_TAC[]);;

let flat_simple_val_rel_v_to_bytes = prove
 (`!vr. flat_simple_val_rel vr ==>
        !x y ws. vr x y /\ flat_v_to_bytes x = SOME ws ==> flat_v_to_bytes y = SOME ws`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `flat_v_to_list y = flat_v_to_list x` (fun th ->
    ASM_REWRITE_TAC[flat_v_to_bytes_def; th] THEN
    ASM_REWRITE_TAC[GSYM flat_v_to_bytes_def]) THEN
  UNDISCH_TAC `flat_v_to_bytes x = SOME (ws:byte list)` THEN
  REWRITE_TAC[flat_v_to_bytes_def; some_DEF] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `ns:byte list`) THEN
  MP_TAC(SPEC `vr:flat_v->flat_v->bool` simple_v_to_list_v_rel) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:flat_v`; `y:flat_v`;
                             `MAP (flat_Litv o Word8) (ns:byte list)`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_INJ] THEN
  FIRST_ASSUM(fun sim -> MATCH_MP_TAC (MATCH_MP FLATSEMAUX_rel_lits sim)) THEN
  ASM_REWRITE_TAC[]);;

(* a local helper: the elementwise form of check_type_LIST_REL_same *)
let FLATSEMAUX_check_type_rel = prove
 (`!vr ty v1 v2. flat_simple_val_rel vr /\ check_type ty (flat_to_v v1) /\ vr v1 v2
                 ==> v2 = v1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(?l. v1 = flat_Litv l) \/ (?x. v1 = flat_Conv x [])` MP_TAC THENL
   [UNDISCH_TAC `check_type ty (flat_to_v v1)` THEN
    STRUCT_CASES_TAC(SPEC `ty:prim_type` prim_type_cases) THEN
    CASES_ON `v1:flat_v` THEN
    REWRITE_TAC[flat_to_v_def; check_type_def; injectivity "v"; distinctness "v";
                semanticPrimitives_Boolv_def; injectivity "flat_v";
                distinctness "flat_v"] THEN
    TRY (MESON_TAC[]) THEN
    REPEAT COND_CASES_TAC THEN
    REWRITE_TAC[injectivity "v"; distinctness "v"; semanticPrimitives_Boolv_def] THEN
    TRY COND_CASES_TAC THEN
    REWRITE_TAC[injectivity "v"; distinctness "v"; flat_Boolv_def; injectivity "flat_v"] THEN
    ASM_MESON_TAC[flat_Boolv_def; injectivity "flat_v"];
    ALL_TAC] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try rator(rator(concl th)) = `vr:flat_v->flat_v->bool`
                                          with Failure _ -> false)) THEN
  ASM_SIMP_TAC[simple_val_rel_simps; simple_basic_val_rel_def; v_container_xs_def;
               LIST_REL_NIL] THEN
  STRIP_TAC THEN RVEQ_TAC THEN FS[v_container_xs_def]);;

(* HOL4 [local]; HOL4 leaves the variables free *)
let check_type_LIST_REL_same = prove
 (`!vr vs1 vs2 ty.
     ALL2 vr vs1 vs2 /\ ALL (check_type ty) (MAP flat_to_v vs1) /\
     flat_simple_val_rel vr ==> vs2 = vs1`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1; MAP; ALL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[CONS_11] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[FLATSEMAUX_check_type_rel]; ASM_MESON_TAC[]]);;

(* simple_do_app_thm and its local helpers: the tests and results of do_app  *)
(* carried along related values (vr) and related states (sr)                 *)

(* forward chaining: MATCH_MP each theorem with the assumptions, repeatedly while the result *)
(* is an implication; the final results are added as assumptions                          *)
let FLATSEMAUX_FWD_CHAIN_TAC (thl:thm list) : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  let rec go acc n l = match l with
      [] -> acc
    | th::rest ->
        if n > 4 then go acc n rest else
        if is_imp (snd (strip_forall (concl th))) then
          go acc n (mapfilter (MATCH_MP th) ths @ rest)
        else go (th::acc) n rest in
  let res = go [] 0 (flat (map (fun th -> mapfilter (MATCH_MP th) ths) thl)) in
  MAP_EVERY ASSUME_TAC res g;;

(* forward reasoning with the implicational assumptions selected by p: MATCH_MP of each with
   each other assumption, results added *)
let FLATSEMAUX_ASM_FWD_TAC (p:thm->bool) : tactic =
  ASSUM_LIST (fun ths ->
    let imps = filter (fun th -> p th && is_imp (snd (strip_forall (concl th)))) ths in
    MAP_EVERY ASSUME_TAC
      (flat (map (fun i -> mapfilter (MATCH_MP i) ths) imps)));;

let FLATSEMAUX_check_type_flat = prove
 (`!vr ty v1 v2. flat_simple_val_rel vr /\ flat_check_type ty v1 /\ vr v1 v2
                 ==> v2 = v1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(?l. v1 = flat_Litv l) \/ (?x. v1 = flat_Conv x [])` MP_TAC THENL
   [UNDISCH_TAC `flat_check_type ty v1` THEN
    STRUCT_CASES_TAC(SPEC `ty:prim_type` prim_type_cases) THEN
    REWRITE_TAC[flat_check_type_def; flat_Boolv_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try rator(rator(concl th)) = `vr:flat_v->flat_v->bool`
                                          with Failure _ -> false)) THEN
  ASM_SIMP_TAC[simple_val_rel_simps; simple_basic_val_rel_def; v_container_xs_def;
               LIST_REL_NIL] THEN
  STRIP_TAC THEN RVEQ_TAC THEN FS[v_container_xs_def]);;

let FLATSEMAUX_lit_rel = prove
 (`!vr l v2. flat_simple_val_rel vr /\ vr (flat_Litv l) v2 ==> v2 = flat_Litv l`,
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  ASM_SIMP_TAC[simple_val_rel_simps; simple_basic_val_rel_def]);;

let FLATSEMAUX_dest_Litv_NONE = prove
 (`!v. (!l. ~(v = flat_Litv l)) ==> flat_dest_Litv v = NONE`,
  GEN_TAC THEN CASES_ON `v:flat_v` THEN
  REWRITE_TAC[flat_dest_Litv_def; injectivity "flat_v"; distinctness "flat_v"] THEN
  MESON_TAC[]);;

let FLATSEMAUX_do_test_rel = prove
 (`!vr t ty x1 y1 x2 y2 b.
     flat_simple_val_rel vr /\ flat_do_test t ty x1 y1 = Eq_val b /\
     vr x1 x2 /\ vr y1 y2 ==> flat_do_test t ty x2 y2 = Eq_val b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `x2:flat_v = x1 /\ y2:flat_v = y1` (fun th -> ASM_REWRITE_TAC[th]) THEN
  ASM_CASES_TAC `t = Equal` THENL
   [UNDISCH_TAC `flat_do_test t ty x1 y1 = Eq_val b` THEN
    ASM_REWRITE_TAC[flat_do_test_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[distinctness "eq_result"] THEN
    ASM_MESON_TAC[FLATSEMAUX_check_type_flat];
    ALL_TAC] THEN
  SUBGOAL_THEN `(?l. x1 = flat_Litv l) /\ (?l. y1 = flat_Litv l)` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `?l. x1 = flat_Litv l` THEN ASM_CASES_TAC `?l. y1 = flat_Litv l` THEN
    ASM_REWRITE_TAC[] THEN
    (SUBGOAL_THEN `flat_dest_Litv x1 = NONE \/ flat_dest_Litv y1 = NONE` MP_TAC THENL
      [ASM_MESON_TAC[FLATSEMAUX_dest_Litv_NONE]; ALL_TAC]) THEN
    UNDISCH_TAC `flat_do_test t ty x1 y1 = Eq_val b` THEN
    UNDISCH_TAC `~(t = Equal)` THEN
    STRUCT_CASES_TAC(ISPEC `t:test` (cases "test")) THEN
    REWRITE_TAC[flat_do_test_def; injectivity "test"; distinctness "test"] THEN
    STRUCT_CASES_TAC(SPEC `ty:prim_type` prim_type_cases) THEN
    REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN (fun th ->
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[th] o check (fun a ->
        is_eq (concl a) && rhs (concl a) = `Eq_val b`)))) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "eq_result"] THEN
    REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[distinctness "eq_result"]);
    ALL_TAC] THEN
  RVEQ_TAC THEN ASM_MESON_TAC[FLATSEMAUX_lit_rel]);;

let FLATSEMAUX_shape_rel = prove
 (`!vr v1 v2. flat_simple_val_rel vr /\ vr v1 v2 ==>
     (!l. v1 = flat_Litv l ==> v2 = flat_Litv l) /\
     (!b n. v1 = flat_Loc b n ==> v2 = flat_Loc b n) /\
     (!x y. v1 = flat_Conv x y ==> ?ys. v2 = flat_Conv x ys /\ ALL2 vr y ys) /\
     (!y. v1 = flat_Vectorv y ==> ?ys. v2 = flat_Vectorv ys /\ ALL2 vr y ys) /\
     (isClosure v1 ==> isClosure v2)`,
  REWRITE_TAC[flat_simple_val_rel_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~isClosure v1 ==> simple_basic_val_rel v1 v2 /\
                  ALL2 (vr:flat_v->flat_v->bool) (v_container_xs v1) (v_container_xs v2)`
    MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `isClosure v1 ==> isClosure v2` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  CASES_ON `v1:flat_v` THEN
  REWRITE_TAC[isClosure_simps; simple_basic_val_rel_def; v_container_xs_def;
              injectivity "flat_v"; distinctness "flat_v"] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  GVS[v_container_xs_def]);;

let FLATSEMAUX_dest_thunk_not_loc = prove
 (`!v (r:(flat_v store_v) list). (!b n. ~(v = flat_Loc b n)) ==>
     flat_dest_thunk [v] r = flat_NotThunk`,
  GEN_TAC THEN GEN_TAC THEN CASES_ON `v:flat_v` THEN
  REWRITE_TAC[flat_dest_thunk_def; injectivity "flat_v"; distinctness "flat_v"] THEN
  MESON_TAC[]);;

let FLATSEMAUX_dest_thunk_loc_rel = prove
 (`!vr r1 r2 b n. ALL2 (sv_rel vr) r1 r2 ==>
     (flat_dest_thunk [flat_Loc b n] r2 = flat_NotThunk <=>
      flat_dest_thunk [flat_Loc b n] r1 = flat_NotThunk)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[LIST_REL_EL_EQN]) THEN
  REWRITE_TAC[flat_dest_thunk_def; store_lookup_def] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n < LENGTH (r2:(flat_v store_v) list)` THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[sv_rel_cases] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  CASES_ON `m:thunk_mode` THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "flat_dest_thunk_ret"]);;

let FLATSEMAUX_bad_thunk_update_rel = prove
 (`!vr r1 r2 m v1 v2.
     flat_simple_val_rel vr /\ ALL2 (sv_rel vr) r1 r2 /\ vr v1 v2 ==>
     (flat_bad_thunk_update m v2 r2 <=> flat_bad_thunk_update m v1 r1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[flat_bad_thunk_update_def] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`vr:flat_v->flat_v->bool`; `v1:flat_v`; `v2:flat_v`] FLATSEMAUX_shape_rel) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `?b n. v1 = flat_Loc b n` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `b:bool` (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC)) THEN
    SUBGOAL_THEN `v2 = flat_Loc b n` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`vr:flat_v->flat_v->bool`; `r1:(flat_v store_v)list`;
                   `r2:(flat_v store_v)list`; `b:bool`; `n:num`]
                  FLATSEMAUX_dest_thunk_loc_rel) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!b n. ~(v2 = flat_Loc b n)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(?b n. v1 = flat_Loc b n)` THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall (concl th) || is_imp (concl th)))) THEN
    CASES_ON `v1:flat_v` THEN
    REWRITE_TAC[isClosure_simps; injectivity "flat_v"; distinctness "flat_v"] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_SIMP_TAC[FLATSEMAUX_dest_thunk_not_loc]);;

let FLATSEMAUX_v_to_flat_rel = prove
 (`!vr v. flat_simple_val_rel vr ==> vr (v_to_flat v) (v_to_flat v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(?l. v_to_flat v = flat_Litv l) \/ (?x. v_to_flat v = flat_Conv x []) \/
                v_to_flat v = flat_Vectorv []` MP_TAC THENL
   [CASES_ON `v:v` THEN REWRITE_TAC[v_to_flat_def] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[flat_Boolv_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[simple_val_rel_simps; simple_basic_val_rel_def; v_container_xs_def;
               LIST_REL_NIL] THEN
  MESON_TAC[]);;

let FLATSEMAUX_lit_refl = prove
 (`!vr l. flat_simple_val_rel vr ==> vr (flat_Litv l) (flat_Litv l)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[simple_val_rel_simps; simple_basic_val_rel_def; v_container_xs_def;
               LIST_REL_NIL]);;

let FLATSEMAUX_sim_tac (ttac:thm->tactic) : tactic = fun (asl,w as g) ->
  let sim = find (fun th -> try fst(dest_const(rator(concl th))) = "flat_simple_val_rel"
                            with Failure _ -> false) (map snd asl) in
  ttac sim g;;

let FLATSEMAUX_SR_TAC : tactic = fun (asl,w as g) ->
  let ssr = find (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                "flat_simple_state_rel" with Failure _ -> false) (map snd asl) in
  let cl = CONJUNCTS (REWRITE_RULE[flat_simple_state_rel_def] ssr) in
  let c2 = el 1 cl and c4 = el 3 cl and c6 = el 5 cl in
  (REPEAT ((MATCH_MP_TAC c2 ORELSE MATCH_MP_TAC c4 ORELSE MATCH_MP_TAC c6) THEN CONJ_TAC) THEN
   TRY (FIRST_ASSUM ACCEPT_TAC) THEN TRY REFL_TAC) g;;

let FLATSEMAUX_ALL2_TAC : tactic =
  REPEAT ((MATCH_MP_TAC EVERY2_LUPDATE_same ORELSE MATCH_MP_TAC LIST_REL_APPEND_suff) THEN
          CONJ_TAC) THEN
  REWRITE_TAC[ALL2; sv_rel_def; OPTREL_THM; LIST_REL_REPLICATE_same] THEN
  REPEAT ((MATCH_MP_TAC EVERY2_LUPDATE_same ORELSE MATCH_MP_TAC LIST_REL_APPEND_suff) THEN
          CONJ_TAC) THEN
  REPEAT DISCH_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC);;

let FLATSEMAUX_LIST_TO_V_TAC : tactic =
  FLATSEMAUX_sim_tac (fun sim -> MATCH_MP_TAC (MATCH_MP simple_v_rel_list_to_v sim)) THEN
  REPEAT (MATCH_MP_TAC LIST_REL_APPEND_suff THEN CONJ_TAC) THEN
  TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  MATCH_MP_TAC EVERY2_refl THEN REWRITE_TAC[MEM_MAP] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  FLATSEMAUX_sim_tac (fun sim -> MATCH_ACCEPT_TAC (MATCH_MP FLATSEMAUX_lit_refl sim));;

let FLATSEMAUX_EL_TAC : tactic = fun (asl,w as g) ->
  let alls = filter (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "ALL2"
                               with Failure _ -> false) (map snd asl) in
  let els = mapfilter (fun th -> CONJUNCT2 (REWRITE_RULE[LIST_REL_EL_EQN] th)) alls in
  FIRST (map (fun th -> MATCH_MP_TAC th THEN
                        (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC)) els) g;;

let FLATSEMAUX_ADD_LENGTHS_TAC : tactic = fun (asl,w as g) ->
  let alls = filter (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "ALL2"
                               with Failure _ -> false) (map snd asl) in
  MAP_EVERY ASSUME_TAC (mapfilter (MATCH_MP LIST_REL_LENGTH) alls) g;;

let FLATSEMAUX_BTU_TAC : tactic = fun (asl,w as g) ->
  if is_neg w && can (find_term (fun t -> try fst(dest_const t) = "flat_bad_thunk_update"
                                          with Failure _ -> false)) w
  then ASM_MESON_TAC[FLATSEMAUX_bad_thunk_update_rel] g else failwith "FLATSEMAUX_BTU_TAC";;

let FLATSEMAUX_CLOSE_TAC : tactic =
  REPEAT CONJ_TAC THEN
  TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  TRY (FLATSEMAUX_BTU_TAC) THEN
  TRY (FLATSEMAUX_FWD_CHAIN_TAC
         [REWRITE_RULE[IMP_CONJ] (SPEC `vr:flat_v->flat_v->bool` simple_vs_to_string_v_rel)] THEN
       GVS[] THEN NO_TAC) THEN
  TRY (FLATSEMAUX_SR_TAC THEN FLATSEMAUX_ALL2_TAC THEN NO_TAC) THEN
  TRY (FLATSEMAUX_sim_tac (fun sim -> MATCH_ACCEPT_TAC (MATCH_MP FLATSEMAUX_v_to_flat_rel sim))) THEN
  TRY (FLATSEMAUX_LIST_TO_V_TAC THEN NO_TAC) THEN
  TRY (FLATSEMAUX_EL_TAC THEN NO_TAC);;

(* HOL4: simple_do_app_thm; the HOL4 proof goes op by op, here one pass:   *)
(* unfold do_app, split, transfer each test along vr and sr, then close     *)
let simple_do_app_thm = prove
 (`!vr (sr:(C,FFI)flat_state->(D,FFI)flat_state->bool) op.
     flat_simple_val_rel vr /\ flat_simple_state_rel vr sr ==>
     !s1 vs1 t1 r1 s2 vs2.
       flat_do_app s1 op vs1 = SOME (t1,r1) ==>
       sr s1 s2 /\ ALL2 vr vs1 vs2 ==>
       ?t2 r2. result_rel vr vr r1 r2 /\ sr t1 t2 /\
               flat_do_app s2 op vs2 = SOME (t2,r2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ALL2 (sv_rel vr) (flat_state_refs (s1:(C,FFI)flat_state))
                  (flat_state_refs (s2:(D,FFI)flat_state)) /\
                ALL2 (OPTREL vr) (flat_state_globals s1) (flat_state_globals s2) /\
                flat_state_ffi s1 = flat_state_ffi s2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[flat_simple_state_rel_def]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (flat_state_refs (s1:(C,FFI)flat_state)) =
                  LENGTH (flat_state_refs (s2:(D,FFI)flat_state)) /\
                (!n. n < LENGTH (flat_state_refs s1) ==>
                     sv_rel vr (EL n (flat_state_refs s1)) (EL n (flat_state_refs s2))) /\
                LENGTH (flat_state_globals s1) = LENGTH (flat_state_globals s2) /\
                (!n. n < LENGTH (flat_state_globals s1) ==>
                     OPTREL vr (EL n (flat_state_globals s1)) (EL n (flat_state_globals s2)))`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_REL_EL_EQN]; ALL_TAC] THEN
  UNDISCH_TAC `flat_do_app (s1:(C,FFI)flat_state) op vs1 = SOME (t1,r1)` THEN
  REWRITE_TAC[flat_do_app_def; store_lookup_def; store_assign_def; store_alloc_def] THEN
  DISCH_TAC THEN FLATSEMAUX_SPLIT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  FLATSEMAUX_ASM_FWD_TAC (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "EL" with Failure _ -> false)) (concl th)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "EL" with Failure _ -> false)) (concl th)))) THEN
  GVS[LIST_REL_CONS1; LIST_REL_NIL; sv_rel_cases; OPTREL_DEF] THEN
  FLATSEMAUX_FWD_CHAIN_TAC
    (map (fun th -> REWRITE_RULE[IMP_CONJ] (SPEC `vr:flat_v->flat_v->bool` th))
      [simple_do_eq_thm; FLATSEMAUX_do_test_rel; FLATSEMAUX_check_type_rel;
       check_type_LIST_REL_same;
       simple_v_to_char_list_v_rel; simple_v_to_list_v_rel; simple_vs_to_string_v_rel]) THEN
  FLATSEMAUX_ADD_LENGTHS_TAC THEN
  GVS[store_v_same_type_def; subscript_exn_v_def; flat_div_exn_v_def; flat_chr_exn_v_def;
      flat_Unitv_def; flat_Boolv_def] THEN
  FLATSEMAUX_CLOSE_TAC);;

let flat_evaluate_match_def = cake_def
  `flat_evaluate_match (env:(flat_v)flat_environment) (s:(C,FFI)flat_state) v pes err_v =
     match pmatch_rows pes s v with
       Match_type_error -> (s,Rerr (Rabort Rtype_error))
     | No_match -> (s,Rerr (Rraise err_v))
     | Match (env',p',e') ->
         if ALL_DISTINCT (flat_pat_bindings p')
         then flat_evaluate (flat_environment_v_fupd
                               (K (APPEND env' (flat_environment_v env))) env) s [e']
         else (s,Rerr (Rabort Rtype_error))`;;

(* HOL4 leaves env, s, tra, e, pes free *)
let evaluate_Mat = prove
 (CASE_TERM
  `!env (s:(C,FFI)flat_state) tra e pes.
     flat_evaluate env s [flat_Mat tra e pes] =
     match flat_evaluate env s [e] with
       (s,Rval v) ->
         if ~(pmatch_rows pes s (HD v) = Match_type_error)
         then flat_evaluate_match env s (HD v) pes flat_bind_exn_v
         else (s,Rerr (Rabort Rtype_error))
     | res -> res`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flat_evaluate_def; flat_evaluate_match_def] THEN
  EVERY_CASE_TAC THEN FS[]);;

let evaluate_Handle = prove
 (CASE_TERM
  `!env (s:(C,FFI)flat_state) x e pes.
     flat_evaluate env s [flat_Handle x e pes] =
     match flat_evaluate env s [e] with
       (s,Rerr (Rraise v)) ->
         if ~(pmatch_rows pes s v = Match_type_error)
         then flat_evaluate_match env s v pes v
         else (s,Rerr (Rabort Rtype_error))
     | res -> res`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flat_evaluate_def; flat_evaluate_match_def] THEN
  EVERY_CASE_TAC THEN FS[]);;

let evaluate_match_NIL = prove
 (`!env (s:(C,FFI)flat_state) v err_v.
     flat_evaluate_match env s v [] err_v = (s,Rerr (Rraise err_v))`,
  REWRITE_TAC[flat_evaluate_match_def; pmatch_rows_def; case_def "match_result"]);;

let evaluate_match_CONS = prove
 (CASE_TERM
  `!env (s:(C,FFI)flat_state) v p e pes err_v.
     flat_evaluate_match env s v (CONS (p,e) pes) err_v =
     match flat_pmatch s p v [] with
       No_match -> flat_evaluate_match env s v pes err_v
     | Match_type_error -> (s,Rerr (Rabort Rtype_error))
     | Match env_v' ->
         if ALL_DISTINCT (flat_pat_bindings p) /\
            ~(pmatch_rows pes s v = Match_type_error)
         then flat_evaluate (flat_environment_v_fupd
                               (K (APPEND env_v' (flat_environment_v env))) env) s [e]
         else (s,Rerr (Rabort Rtype_error))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flat_evaluate_match_def; pmatch_rows_def] THEN
  EVERY_CASE_TAC THEN FS[]);;

let flatProps_flat_evaluate_def =
  let has c th = can (find_term (fun t -> is_const t && fst(dest_const t) = c)) (concl th) in
  end_itlist CONJ
    (filter (fun th -> not (has "flat_Mat" th) && not (has "flat_Handle" th))
            (CONJUNCTS flat_evaluate_def) @
     [evaluate_Handle; evaluate_Mat; evaluate_match_NIL; evaluate_match_CONS]);;

let flat_store_v_vs_def = cake_def
  `(flat_store_v_vs (Varray vs) = vs:A list) /\
   (flat_store_v_vs (Refv v) = [v]) /\
   (flat_store_v_vs (Thunk m v) = [v]) /\
   (flat_store_v_vs (W8array xs) = [])`;;
let _ = cake_add_simps [flat_store_v_vs_def];;

let result_vs_def = cake_def
  `(result_vs (Rval xs) = xs:A list) /\
   (result_vs (Rerr (Rraise x)) = [x]) /\
   (result_vs (Rerr (Rabort y)) = [])`;;
let _ = cake_add_simps [result_vs_def];;

(* HOL4's v1_size is flat_v_size_aux1 (on environments), v2_size is         *)
(* list_size (pair_size mlstring_size flat_v_size), v3_size is its element  *)
(* size and v4_size is list_size flat_v_size                                 *)
let v_size_aux = prove
 (`(!env. flat_v_size_aux1 env =
          1 + list_size (pair_size mlstring_size flat_v_size) (flat_environment_v env)) /\
   (!xs. list_size (pair_size mlstring_size flat_v_size) xs =
         LENGTH xs + SUM (MAP (pair_size mlstring_size flat_v_size) xs)) /\
   (!xs. list_size flat_v_size xs = LENGTH xs + SUM (MAP flat_v_size xs))`,
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN CASES_ON `env:(flat_v)flat_environment` THEN
    REWRITE_TAC[type_size_def "flat_v"; flat_environment_INFO.ri_accessors] THEN
    REWRITE_TAC(size_aux_eqs "flat_v");
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[list_size; LENGTH; MAP; SUM] THEN ARITH_TAC;
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[list_size; LENGTH; MAP; SUM] THEN ARITH_TAC]);;

(* HOL4's catch-all for Handle is written with a match *)
let no_Mat_def = cake_def_wf
  `measure flat_exp_size`
  (REWRITE_TAC[measure_THM; IMP_CONJ] THEN REPEAT STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[measure_THM; MEM_MAP; o_DEF]) THEN
   REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
   RVEQ_TAC THEN
   REWRITE_TAC[type_size_def "flat_exp"; list_size] THEN
   REWRITE_TAC (flat (map snd (!the_size_aux_eqs))) THEN
   ASSUM_LIST (fun ths ->
     MAP_EVERY MP_TAC (mapfilter (MATCH_MP (CONJUNCT1 flat_exp_size_MEM)) ths @
                       mapfilter (MATCH_MP (CONJUNCT1 (CONJUNCT2 flat_exp_size_MEM))) ths @
                       mapfilter (MATCH_MP (CONJUNCT2 (CONJUNCT2 flat_exp_size_MEM))) ths)) THEN
   ASM_ARITH_TAC)
  `(no_Mat (flat_Raise t e) <=> no_Mat e) /\
   (no_Mat (flat_Lit t l) <=> T) /\
   (no_Mat (Var_local t x) <=> T) /\
   (no_Mat (flat_Con t n es) <=> ALL no_Mat es) /\
   (no_Mat (flat_App t op es) <=> ALL no_Mat es) /\
   (no_Mat (flat_Fun n' x e) <=> no_Mat e) /\
   (no_Mat (flat_If t x1 x2 x3) <=> no_Mat x1 /\ no_Mat x2 /\ no_Mat x3) /\
   (no_Mat (flat_Let t vo e1 e2) <=> no_Mat e1 /\ no_Mat e2) /\
   (no_Mat (flat_Mat t e pes) <=> F) /\
   (no_Mat (flat_Handle t e pes) <=>
      no_Mat e /\ ALL no_Mat (MAP SND pes) /\
      (match pes with [(flat_Pvar _,_)] -> T | _ -> F)) /\
   (no_Mat (flat_Letrec n' funs e) <=> ALL no_Mat (MAP (SND o SND) funs) /\ no_Mat e)`;;
let _ = cake_add_simps [no_Mat_def];;

let no_Mat_ind = cake_ind "no_Mat";;

let no_Mat_decs_def = cake_def
  `(no_Mat_decs [] <=> T) /\
   (no_Mat_decs (CONS e xs) <=> no_Mat e /\ no_Mat_decs xs)`;;
let _ = cake_add_simps [no_Mat_decs_def];;

let mk_flat_install_conf_def = cake_def
  `mk_flat_install_conf (cc:C->flat_exp list->(byte list#int64 list#C)option) co =
     install_config_REC cc co`;;
