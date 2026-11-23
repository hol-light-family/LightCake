(* ========================================================================= *)
(* parmove: port of HOL4 compiler/backend/reg_alloc/parmoveScript.sml        *)
(* (CakeML v3479).  Compiling parallel moves: a formalisation of the JAR'08  *)
(* paper by Rideau, Serpette and Leroy, Tilting at windmills with Coq.       *)
(* ========================================================================= *)

needs "misc/misc.ml";;

(* Non-deterministic algorithm *)

(* The state is three lists of moves:                                        *)
(*   (to-process, being-processed, processed)                                *)
(* each step (roughly) shifts some move from left to right in the state.     *)
(* NONE is a temporary register; real registers are SOME x.                  *)
(* HOL4 overloads NoRead mu dn for ~MEM dn (MAP SND mu): expanded below.     *)
(* HOL4: step, an infix (also a triangle symbol), RTC step starred; here the *)
(* constant is parmove_step (as path and sem below are parmove_path and      *)
(* parmove_sem: these short names would hide variables in later files).     *)

let parmove_step_rules,parmove_step_ind,parmove_step_cases,parmove_step_strongind = cake_inductive
  `(!mu1 mu2 (r:A option) sigma tau.
      parmove_step (APPEND (APPEND mu1 [(r,r)]) mu2,sigma,tau)
           (APPEND mu1 mu2,sigma,tau)) /\
   (!mu1 mu2 d s tau.
      parmove_step (APPEND (APPEND mu1 [(d,s)]) mu2,[],tau)
           (APPEND mu1 mu2,[(d,s)],tau)) /\
   (!mu1 mu2 r d s sigma tau.
      parmove_step (APPEND (APPEND mu1 [(r,d)]) mu2,APPEND [(d,s)] sigma,tau)
           (APPEND mu1 mu2,APPEND [(r,d); (d,s)] sigma,tau)) /\
   (!mu sigma d s tau.
      parmove_step (mu,APPEND sigma [(d,s)],tau)
           (mu,APPEND sigma [(d,NONE)],APPEND [(NONE,s)] tau)) /\
   (!mu dn sn sigma d0 s0 tau.
      ~MEM dn (MAP SND mu) /\ ~(dn = s0)
      ==> parmove_step (mu,APPEND (APPEND [(dn,sn)] sigma) [(d0,s0)],tau)
               (mu,APPEND sigma [(d0,s0)],APPEND [(dn,sn)] tau)) /\
   (!mu d s tau.
      ~MEM d (MAP SND mu)
      ==> parmove_step (mu,[(d,s)],tau) (mu,[],APPEND [(d,s)] tau))`;;

(* invariant on states *)

let windmill_def = cake_def
  `windmill (moves:(A#A) list) = ALL_DISTINCT (MAP FST moves)`;;

let windmill_cons = prove
 (`!(x:A#A) ls. windmill (CONS x ls) <=> ~MEM (FST x) (MAP FST ls) /\ windmill ls`,
  RW[windmill_def; MAP; ALL_DISTINCT]);;

let parmove_path_def = cake_def
  `(parmove_path ([]:(A#A) list) <=> T) /\ (parmove_path [_] <=> T) /\
   (parmove_path (CONS (c,b') (CONS (b,a) p)) <=> b = b' /\ parmove_path (CONS (b,a) p))`;;
let _ = cake_add_simps [parmove_path_def];;

(* PARMOVEAUX_path_cons_cons: the third clause of parmove_path_def for any pairs *)
let PARMOVEAUX_path_cons_cons = prove
 (`!(x:A#A) y l. parmove_path (CONS x (CONS y l)) <=> FST y = SND x /\ parmove_path (CONS y l)`,
  REWRITE_TAC[FORALL_PAIR_THM; parmove_path_def; FST; SND]);;

let path_change_start = prove
 (`!y z (x:A#A). parmove_path (SNOC x y) /\ FST x = FST z ==> parmove_path (SNOC z y)`,
  REWRITE_TAC[SNOC_APPEND] THEN LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; parmove_path_def] THEN
  CASES_ON `t:(A#A)list` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[APPEND]) THEN
  REWRITE_TAC[APPEND; PARMOVEAUX_path_cons_cons; parmove_path_def] THEN
  ASM_MESON_TAC[]);;

let path_tail = prove
 (`!t (h:A#A). parmove_path (CONS h t) ==> parmove_path t`,
  LIST_INDUCT_TAC THEN SIMP_TAC[parmove_path_def; PARMOVEAUX_path_cons_cons]);;

let path_imp_mem = prove
 (`!(x:A#A) y. parmove_path (CONS x y) ==> ~NULL y ==> MEM (SND x) (MAP FST y)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[NULL; PARMOVEAUX_path_cons_cons; MAP; MEM] THEN MESON_TAC[]);;

let path_imp_mem2 = prove
 (`!x:(A#A) list. parmove_path x ==>
     !y. MEM y (MAP SND x) /\ ~(y = SND (LAST x)) ==> MEM y (MAP FST x)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM] THEN
  CASES_ON `t:(A#A)list` THEN
  REWRITE_TAC[MAP; MEM; LAST; NOT_CONS_NIL; PARMOVEAUX_path_cons_cons] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAP; MEM; LAST; NOT_CONS_NIL]) THEN
  ASM_MESON_TAC[]);;

let NoRead_path = prove
 (`!sigma:(A#A) list.
     parmove_path sigma /\ windmill sigma /\ LENGTH sigma >= 2 /\
     ~(FST (HD sigma) = SND (LAST sigma))
     ==> ~MEM (FST (HD sigma)) (MAP SND (TL sigma))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; HD; TL; LAST; windmill_cons] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `t:(A#A) list = []` THEN ASM_REWRITE_TAC[LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP path_tail) THEN
  DISCH_THEN(MP_TAC o SPEC `FST (h:A#A)` o MATCH_MP path_imp_mem2) THEN
  ASM_MESON_TAC[]);;

(* HOL4: wf (overloaded as a turnstile); renamed: a common word *)
let parmove_wf_def = cake_def
  `parmove_wf (mu,sigma,tau:B) <=>
     windmill (APPEND mu sigma) /\
     ALL IS_SOME (MAP FST mu) /\
     ALL IS_SOME (MAP SND (mu:(A option#A option) list)) /\
     (~NULL sigma ==> ALL IS_SOME (MAP SND (BUTLAST sigma))) /\
     ALL IS_SOME (MAP FST sigma) /\
     parmove_path sigma`;;

let wf_init = prove
 (`!mu:(A option#A option) list.
     windmill mu /\ ALL IS_SOME (MAP FST mu) /\ ALL IS_SOME (MAP SND mu)
     ==> parmove_wf (mu,[],[]:B list)`,
  RW[parmove_wf_def; parmove_path_def; APPEND_NIL; NULL; MAP; ALL]);;

(* The invariant is preserved *)

let wf_step = prove
 (`!s1 s2:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     parmove_step s1 s2 ==> parmove_wf s1 ==> parmove_wf s2`,
  MATCH_MP_TAC parmove_step_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[parmove_wf_def; windmill_def; MAP_APPEND; ALL_DISTINCT_APPEND; ALL_APPEND;
    MAP; ALL; MEM_APPEND; MEM; APPEND; NULL; NULL_APPEND; ALL_DISTINCT; BUTLAST_APPEND;
    BUTLAST; NOT_CONS_NIL; APPEND_NIL; parmove_path_def; FST; SND] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP; ALL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[path_tail; REWRITE_RULE[SNOC_APPEND] path_change_start; FST]);;

let wf_steps = prove
 (`!s1 s2:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     parmove_wf s1 /\ RTC parmove_step s1 s2 ==> parmove_wf s2`,
  MATCH_MP_TAC RTC_lifts_invariants THEN MESON_TAC[wf_step]);;

(* semantics of moves *)

let parsem_def = cake_def
  `parsem (mu:(A#A) list) (rho:A->B) = rho =++ ZIP (MAP FST mu) (MAP (rho o SND) mu)`;;

let parsem_nil = prove
 (`parsem ([]:(A#A) list) = (I:(A->B)->A->B)`,
  REWRITE_TAC[FUN_EQ_THM; parsem_def; MAP; ZIP; UPDATE_LIST_THM; I_THM]);;
let _ = cake_add_simps [parsem_nil];;

let PARMOVEAUX_ZIP_MAP_MAP = prove
 (`!(f:A->B) (g:A->C) l. ZIP (MAP f l) (MAP g l) = MAP (\x. f x,g x) l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ZIP]);;

let PARMOVEAUX_ALOOKUP_parsem_NONE = prove
 (`!(mu:(A#A) list) (rho:A->B) x.
     ALOOKUP (REVERSE (ZIP (MAP FST mu) (MAP (rho o SND) mu))) x = NONE <=>
     ~MEM x (MAP FST mu)`,
  REWRITE_TAC[ALOOKUP_FAILS; MEM_REVERSE; PARMOVEAUX_ZIP_MAP_MAP; MEM_MAP;
    EXISTS_PAIR_THM; FORALL_PAIR_THM; PAIR_EQ; o_THM] THEN MESON_TAC[]);;

let PARMOVEAUX_ALOOKUP_parsem = prove
 (`!(mu:(A#A) list) (rho:A->B) x.
     ~MEM x (MAP FST mu)
     ==> ALOOKUP (REVERSE (ZIP (MAP FST mu) (MAP (rho o SND) mu))) x = NONE`,
  REWRITE_TAC[PARMOVEAUX_ALOOKUP_parsem_NONE]);;

let parsem_cons = prove
 (`!x (y:A) mu (rho:A->B).
     ~MEM x (MAP FST mu)
     ==> parsem (CONS (x,y) mu) rho = (x =+ rho y) (parsem mu rho)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[parsem_def; MAP; ZIP; UPDATE_LIST_THM; FST; SND; o_THM] THEN
  REWRITE_TAC[FUN_EQ_THM; APPLY_UPDATE_LIST_ALOOKUP; APPLY_UPDATE_THM] THEN
  X_GEN_TAC `z:A` THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_SIMP_TAC[PARMOVEAUX_ALOOKUP_parsem; option_CASE]);;

let independence = prove
 (`!mu1 (s:A) d mu2 mu.
     windmill mu /\ mu = APPEND (APPEND mu1 [(d,s)]) mu2
     ==> parsem mu = (parsem (APPEND (APPEND [(d,s)] mu1) mu2):(A->B)->A->B)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND] THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST1_TAC) THEN
  SPEC_TAC(`h:A#A`,`h:A#A`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:A`; `r:A`] THEN
  REWRITE_TAC[windmill_cons; FST] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:A`; `d:A`; `mu2:(A#A)list`;
    `APPEND (APPEND t [(d:A,s:A)]) mu2`]) THEN
  ASM_REWRITE_TAC[APPEND] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(q:A = d) /\ ~MEM q (MAP FST (APPEND t mu2:(A#A)list)) /\
                ~MEM d (MAP FST (APPEND t mu2:(A#A)list))` STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[windmill_def; MAP_APPEND; MEM_APPEND;
      ALL_DISTINCT_APPEND; MAP; MEM; FST; ALL_DISTINCT]) THEN
    REWRITE_TAC[MAP_APPEND; MEM_APPEND] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `rho:A->B` THEN
  ASM_SIMP_TAC[parsem_cons; MAP; MEM; UPDATE_COMMUTES]);;

(* PARMOVEAUX_parsem_swap: the HOL4 proof of parsem_perm proves this inline *)
let PARMOVEAUX_parsem_swap = prove
 (`!x2 x1 x3:(A#A) list.
     windmill (APPEND (APPEND x1 x2) x3)
     ==> (parsem (APPEND (APPEND x1 x2) x3):(A->B)->A->B) =
         parsem (APPEND (APPEND x1 x3) x2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND_NIL] THEN
  SPEC_TAC(`h:A#A`,`h:A#A`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:A`; `r:A`; `x1:(A#A)list`; `x3:(A#A)list`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~MEM (q:A) (MAP FST (APPEND (APPEND x1 t) x3)) /\
                windmill (APPEND (APPEND x1 t) x3:(A#A)list) /\
                windmill (APPEND (APPEND x1 x3) t:(A#A)list)` STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[windmill_def; MAP_APPEND; MEM_APPEND;
      ALL_DISTINCT_APPEND; MAP; MEM; FST; ALL_DISTINCT]) THEN
    REWRITE_TAC[windmill_def; MAP_APPEND; MEM_APPEND; ALL_DISTINCT_APPEND] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x1:(A#A)list`; `r:A`; `q:A`; `APPEND t x3:(A#A)list`;
     `APPEND (APPEND x1 (CONS (q:A,r:A) t)) x3`] independence) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`APPEND x1 x3:(A#A)list`; `r:A`; `q:A`; `t:(A#A)list`;
     `APPEND (APPEND x1 x3) (CONS (q:A,r:A) t)`] independence) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]] THEN
    UNDISCH_TAC `windmill (APPEND (APPEND x1 (CONS (q:A,r:A) t)) x3)` THEN
    REWRITE_TAC[windmill_def; MAP_APPEND; MAP; ALL_DISTINCT_APPEND; ALL_DISTINCT;
      MEM_APPEND; MEM] THEN MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  SUBGOAL_THEN `~MEM (q:A) (MAP FST (APPEND x1 (APPEND x3 t):(A#A)list))` ASSUME_TAC THENL
   [UNDISCH_TAC `~MEM (q:A) (MAP FST (APPEND x1 (APPEND t x3):(A#A)list))` THEN
    REWRITE_TAC[MAP_APPEND; MEM_APPEND] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `rho:A->B` THEN ASM_SIMP_TAC[parsem_cons]);;

let parsem_perm = prove
 (`!l1 l2:(A#A) list.
     windmill l1 /\ PERM l1 l2 ==> (parsem l1:(A->B)->A->B) = parsem l2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\l:(A#A) list. if windmill l then (parsem l:(A->B)->A->B) else ARB`
    PERM_lifts_equalities) THEN
  ANTS_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `windmill (APPEND (APPEND x1 x2) x3:(A#A)list) <=>
                  windmill (APPEND (APPEND x1 x3) x2)` SUBST1_TAC THENL
     [REWRITE_TAC[windmill_def] THEN MATCH_MP_TAC ALL_DISTINCT_PERM THEN
      MATCH_MP_TAC PERM_MAP THEN
      REWRITE_TAC[GSYM APPEND_ASSOC; PERM_APPEND_IFF; PERM_APPEND];
      ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[PARMOVEAUX_parsem_swap];
    DISCH_THEN(MP_TAC o SPECL [`l1:(A#A)list`; `l2:(A#A)list`]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `windmill (l2:(A#A)list)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[windmill_def; ALL_DISTINCT_PERM; PERM_MAP]]);;

let parsem_untouched = prove
 (`!(rho:A->B) mu x. windmill mu /\ ~MEM x (MAP FST mu) ==> parsem mu rho x = rho x`,
  SIMP_TAC[parsem_def; APPLY_UPDATE_LIST_ALOOKUP; PARMOVEAUX_ALOOKUP_parsem;
           option_CASE]);;

let parsem_change_env = prove
 (`!(mu:(A#A) list) (rho1:A->B) rho2 x.
     (~MEM x (MAP FST mu) ==> rho1 x = rho2 x) /\
     MAP (rho1 o SND) mu = MAP (rho2 o SND) mu
     ==> parsem mu rho1 x = parsem mu rho2 x`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[parsem_def; APPLY_UPDATE_LIST_ALOOKUP] THEN
  MP_TAC(ISPECL [`mu:(A#A) list`; `rho2:A->B`; `x:A`]
    PARMOVEAUX_ALOOKUP_parsem_NONE) THEN
  SPEC_TAC(`ALOOKUP (REVERSE (ZIP (MAP FST mu) (MAP ((rho2:A->B) o SND) mu))) (x:A)`,
           `o1:B option`) THEN
  MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[option_CASE; option_DISTINCT] THEN ASM_MESON_TAC[]);;

let parsem_NoRead = prove
 (`!(x:A) y mu (rho:A->B).
     ~MEM x (MAP SND mu)
     ==> parsem (CONS (x,y) mu) rho = parsem mu ((x =+ rho y) rho)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[parsem_def; MAP; ZIP; UPDATE_LIST_THM; FST; SND; o_THM] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MAP_EQ_f; o_THM; APPLY_UPDATE_THM] THEN
  X_GEN_TAC `e:A#A` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[MEM_MAP]);;

let parsem_MAP_INJ = prove
 (`!(f:A->B) (r:B->C) ms.
     windmill ms /\ INJ f (set_of_list (APPEND (MAP FST ms) (MAP SND ms))) (:B)
     ==> !x. MEM x (MAP FST ms)
             ==> parsem (MAP (f ## f) ms) r (f x) = parsem ms (r o f) x`,
  GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[windmill_def] THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM] THEN
  SPEC_TAC(`h:A#A`,`h:A#A`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:A`; `p:A`] THEN
  REWRITE_TAC[ALL_DISTINCT; PAIR_MAP_THM; FST; SND; APPEND; set_of_list; INJ;
    IN_INSERT; IN_UNIV; IN_SET_OF_LIST; MEM_APPEND; MEM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~MEM ((f:A->B) q) (MAP FST (MAP ((f:A->B) ## f) t))` ASSUME_TAC THENL
   [REWRITE_TAC[MAP_MAP_o; o_PAIR_MAP] THEN REWRITE_TAC[GSYM MAP_MAP_o] THEN
    ONCE_REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[INJ; IN_UNIV; IN_SET_OF_LIST; MEM_APPEND] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[parsem_cons; APPLY_UPDATE_THM; o_THM] THEN
  SUBGOAL_THEN `~((f:A->B) q = f x) /\ ~(q:A = x)` (fun th -> ASM_SIMP_TAC[th]) THEN
  ASM_MESON_TAC[]);;

let seqsem_def = cake_def
  `(seqsem [] (rho:A->B) = rho) /\
   (seqsem (CONS (d,s) tau) rho = seqsem tau ((d =+ rho s) rho))`;;

let seqsem_ind = cake_ind "seqsem";;

let seqsem_append = prove
 (`!l1 l2:(A#A) list. (seqsem (APPEND l1 l2):(A->B)->A->B) = seqsem l2 o seqsem l1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FUN_EQ_THM; APPEND; seqsem_def; o_THM] THEN
  SPEC_TAC(`h:A#A`,`h:A#A`) THEN REWRITE_TAC[FORALL_PAIR_THM; seqsem_def] THEN
  ASM_REWRITE_TAC[o_THM]);;

let seqsem_move_unchanged = prove
 (`!(k:A) ms (r:A->B). ~MEM k (MAP FST ms) ==> seqsem ms r k = r k`,
  GEN_TAC THEN MATCH_MP_TAC seqsem_ind THEN
  SIMP_TAC[seqsem_def; APPLY_UPDATE_THM; MAP; MEM; FST] THEN MESON_TAC[]);;

(* semantics of the state *)

let parmove_sem_def = cake_def
  `parmove_sem (mu,sigma,tau) (rho:A->B) = parsem (APPEND mu sigma) (seqsem (REVERSE tau) rho)`;;

let sem_init = prove
 (`!mu:(A#A) list. (parmove_sem (mu,[],[]):(A->B)->A->B) = parsem mu`,
  REWRITE_TAC[FUN_EQ_THM; parmove_sem_def; APPEND_NIL; REVERSE; seqsem_def]);;

let sem_final = prove
 (`!tau:(A#A) list. (parmove_sem ([],[],tau):(A->B)->A->B) = seqsem (REVERSE tau)`,
  REWRITE_TAC[FUN_EQ_THM; parmove_sem_def; APPEND; parsem_nil; I_THM]);;

(* semantic preservation *)

(* HOL4 writes eqenv as an infix (a triple bar) *)
let eqenv_def = cake_def
  `eqenv (rho1:A option->B) rho2 <=> !r. IS_SOME r ==> rho1 r = rho2 r`;;

let eqenv_sym = prove
 (`!(p1:A option->B) p2. eqenv p1 p2 ==> eqenv p2 p1`,
  SIMP_TAC[eqenv_def]);;

(* PARMOVEAUX_PERM_TAC: PERM goals between appends of the same pieces *)
let PARMOVEAUX_LENGTH_COND = prove
 (`!p (h:A) l. LENGTH (if p then CONS h l else l) = (if p then 1 else 0) + LENGTH l`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

let PARMOVEAUX_PERM_TAC =
  REWRITE_TAC[PERM_alt; FILTER; FILTER_APPEND; LENGTH_APPEND; LENGTH;
              PARMOVEAUX_LENGTH_COND] THEN
  GEN_TAC THEN ARITH_TAC;;

let PARMOVEAUX_windmill_PERM = prove
 (`!l1 l2:(A#A) list. windmill l1 /\ PERM l1 l2 ==> windmill l2`,
  MESON_TAC[windmill_def; ALL_DISTINCT_PERM; PERM_MAP]);;

let PARMOVEAUX_seqsem_REVERSE_CONS = prove
 (`!(d:A) s tau (rho:A->B).
     seqsem (REVERSE (APPEND [(d,s)] tau)) rho =
     (d =+ seqsem (REVERSE tau) rho s) (seqsem (REVERSE tau) rho)`,
  REWRITE_TAC[APPEND; REVERSE; seqsem_append; o_THM; seqsem_def]);;

let PARMOVEAUX_step_sem1 = prove
 (`!mu1 mu2 (r:A) sigma (rho:A->B).
     windmill (APPEND (APPEND (APPEND mu1 [(r,r)]) mu2) sigma)
     ==> parsem (APPEND (APPEND (APPEND mu1 [(r,r)]) mu2) sigma) rho =
         parsem (APPEND (APPEND mu1 mu2) sigma) rho`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `PERM (APPEND (APPEND (APPEND mu1 [(r:A,r)]) mu2) sigma)
                     (CONS (r,r) (APPEND (APPEND mu1 mu2) sigma))` ASSUME_TAC THENL
   [PARMOVEAUX_PERM_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `windmill (CONS (r:A,r) (APPEND (APPEND mu1 mu2) sigma))` MP_TAC THENL
   [ASM_MESON_TAC[PARMOVEAUX_windmill_PERM]; ALL_TAC] THEN
  REWRITE_TAC[windmill_cons; FST] THEN STRIP_TAC THEN
  SUBGOAL_THEN `parsem (APPEND (APPEND (APPEND mu1 [(r:A,r)]) mu2) sigma) =
                (parsem (CONS (r,r) (APPEND (APPEND mu1 mu2) sigma)):(A->B)->A->B)`
    SUBST1_TAC THENL [MATCH_MP_TAC parsem_perm THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[parsem_cons; FUN_EQ_THM; APPLY_UPDATE_THM] THEN
  X_GEN_TAC `x:A` THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC parsem_untouched THEN ASM_REWRITE_TAC[]);;

let PARMOVEAUX_windmill_APPEND = prove
 (`!l1 l2:(A#A) list. windmill (APPEND l1 l2) ==> windmill l1 /\ windmill l2`,
  SIMP_TAC[windmill_def; MAP_APPEND; ALL_DISTINCT_APPEND]);;

let PARMOVEAUX_step_sem4 = prove
 (`!mu sigma (d:A option) s (rho:A option->B) r.
     windmill (APPEND mu (APPEND sigma [(d,s)])) /\
     ALL IS_SOME (MAP SND mu) /\ ALL IS_SOME (MAP SND sigma) /\ IS_SOME r
     ==> parsem (APPEND mu (APPEND sigma [(d,s)])) rho r =
         parsem (APPEND mu (APPEND sigma [(d,NONE)])) ((NONE =+ rho s) rho) r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!y:A option. PERM (APPEND mu (APPEND sigma [(d:A option,y)]))
                                 (CONS (d,y) (APPEND mu sigma))` ASSUME_TAC THENL
   [GEN_TAC THEN PARMOVEAUX_PERM_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y:A option. windmill (APPEND mu (APPEND sigma [(d:A option,y)]))`
    ASSUME_TAC THENL
   [UNDISCH_TAC `windmill (APPEND mu (APPEND sigma [(d:A option,s)]))` THEN
    REWRITE_TAC[windmill_def; MAP_APPEND; MAP; FST];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:A option. parsem (APPEND mu (APPEND sigma [(d:A option,y)])) =
                (parsem (CONS (d,y) (APPEND mu sigma)):(A option->B)->A option->B)`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC parsem_perm THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `windmill (CONS (d:A option,s) (APPEND mu sigma))` MP_TAC THENL
   [ASM_MESON_TAC[PARMOVEAUX_windmill_PERM]; ALL_TAC] THEN
  REWRITE_TAC[windmill_cons; FST] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[parsem_cons; APPLY_UPDATE_THM] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC parsem_change_env THEN
  SUBGOAL_THEN `~(r:A option = NONE)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IS_SOME_DEF]; ALL_TAC] THEN
  ASM_REWRITE_TAC[APPLY_UPDATE_THM; MAP_EQ_f; o_THM] THEN
  X_GEN_TAC `e:A option#A option` THEN REWRITE_TAC[MEM_APPEND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(SND (e:A option#A option) = NONE)` (fun th -> REWRITE_TAC[th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM; MEM_MAP]) THEN
  ASM_MESON_TAC[IS_SOME_DEF]);;

let PARMOVEAUX_step_sem5 = prove
 (`!mu (dn:A) sn sigma d0 s0 (rho:A->B).
     windmill (APPEND mu (APPEND (APPEND [(dn,sn)] sigma) [(d0,s0)])) /\
     ~MEM dn (MAP SND mu) /\ ~MEM dn (MAP SND sigma) /\ ~(dn = s0)
     ==> parsem (APPEND mu (APPEND (APPEND [(dn,sn)] sigma) [(d0,s0)])) rho =
         parsem (APPEND mu (APPEND sigma [(d0,s0)])) ((dn =+ rho sn) rho)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `PERM (APPEND mu (APPEND (APPEND [(dn:A,sn:A)] sigma) [(d0,s0)]))
                     (CONS (d0,s0) (CONS (dn,sn) (APPEND mu sigma))) /\
                PERM (APPEND mu (APPEND sigma [(d0:A,s0:A)]))
                     (CONS (d0,s0) (APPEND mu sigma))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN PARMOVEAUX_PERM_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `windmill (CONS (d0:A,s0) (CONS (dn,sn) (APPEND mu sigma)))` MP_TAC THENL
   [ASM_MESON_TAC[PARMOVEAUX_windmill_PERM]; ALL_TAC] THEN
  REWRITE_TAC[windmill_cons; FST; MAP; MEM; DE_MORGAN_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~MEM (d0:A) (MAP FST (CONS (dn,sn) (APPEND mu sigma:(A#A)list))) /\
                ~MEM (d0:A) (MAP FST (APPEND mu sigma:(A#A)list))` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MAP; MEM; FST; DE_MORGAN_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `windmill (APPEND mu (APPEND sigma [(d0:A,s0:A)]))` ASSUME_TAC THENL
   [UNDISCH_TAC `windmill (APPEND mu (APPEND (APPEND [(dn:A,sn:A)] sigma) [(d0,s0)]))` THEN
    REWRITE_TAC[windmill_def; MAP_APPEND; MAP; ALL_DISTINCT_APPEND; ALL_DISTINCT;
      MEM_APPEND; MEM; APPEND] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `parsem (APPEND mu (APPEND (APPEND [(dn:A,sn:A)] sigma) [(d0,s0)])) =
                (parsem (CONS (d0,s0) (CONS (dn,sn) (APPEND mu sigma))):(A->B)->A->B) /\
                parsem (APPEND mu (APPEND sigma [(d0:A,s0:A)])) =
                (parsem (CONS (d0,s0) (APPEND mu sigma)):(A->B)->A->B)`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC parsem_perm THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MATCH_MP parsem_cons (ASSUME
    `~MEM (d0:A) (MAP FST (CONS (dn,sn) (APPEND mu sigma:(A#A)list)))`)] THEN
  REWRITE_TAC[MATCH_MP parsem_cons (ASSUME
    `~MEM (d0:A) (MAP FST (APPEND mu sigma:(A#A)list))`)] THEN
  ASM_REWRITE_TAC[APPLY_UPDATE_THM] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC parsem_NoRead THEN
  ASM_REWRITE_TAC[MAP_APPEND; MEM_APPEND]);;

let PARMOVEAUX_step_sem6 = prove
 (`!mu (d:A) s (rho:A->B).
     windmill (APPEND mu [(d,s)]) /\ ~MEM d (MAP SND mu)
     ==> parsem (APPEND mu [(d,s)]) rho = parsem (APPEND mu []) ((d =+ rho s) rho)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `parsem (APPEND mu [(d:A,s:A)]) = (parsem (CONS (d,s) mu):(A->B)->A->B)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC parsem_perm THEN ASM_REWRITE_TAC[] THEN PARMOVEAUX_PERM_TAC;
    ASM_SIMP_TAC[parsem_NoRead; APPEND_NIL]]);;

let step_sem = prove
 (`!s1 s2:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     parmove_step s1 s2
     ==> parmove_wf s1
     ==> !rho:A option->B. eqenv (parmove_sem s1 rho) (parmove_sem s2 rho)`,
  MATCH_MP_TAC parmove_step_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[parmove_sem_def; eqenv_def; parmove_wf_def; PARMOVEAUX_seqsem_REVERSE_CONS] THENL
   [STRIP_TAC THEN ASM_SIMP_TAC[PARMOVEAUX_step_sem1];
    STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN
    MATCH_MP_TAC parsem_perm THEN ASM_REWRITE_TAC[] THEN PARMOVEAUX_PERM_TAC;
    STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN
    MATCH_MP_TAC parsem_perm THEN ASM_REWRITE_TAC[] THEN PARMOVEAUX_PERM_TAC;
    STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC PARMOVEAUX_step_sem4 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NULL_APPEND; NULL; BUTLAST_APPEND; NOT_CONS_NIL;
                                BUTLAST; APPEND_NIL]) THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN AP_THM_TAC THEN
    MATCH_MP_TAC PARMOVEAUX_step_sem5 THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `APPEND (APPEND [(dn:A option,sn:A option)] sigma) [(d0,s0)]`
      NoRead_path) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_MESON_TAC[PARMOVEAUX_windmill_APPEND];
        REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
        ASM_REWRITE_TAC[APPEND; HD; LAST_APPEND; NOT_CONS_NIL; LAST]];
      REWRITE_TAC[APPEND; HD; TL; FST; MAP_APPEND; MEM_APPEND; DE_MORGAN_THM] THEN
      MESON_TAC[]];
    STRIP_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN AP_THM_TAC THEN
    MATCH_MP_TAC PARMOVEAUX_step_sem6 THEN ASM_REWRITE_TAC[]]);;

let steps_sem = prove
 (`!s1 s2:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     RTC parmove_step s1 s2 /\ parmove_wf s1
     ==> !rho:A option->B. eqenv (parmove_sem s1 rho) (parmove_sem s2 rho)`,
  REWRITE_TAC[GSYM IMP_IMP] THEN MATCH_MP_TAC RTC_INDUCT_R THEN
  REWRITE_TAC[eqenv_def] THEN
  MESON_TAC[wf_step; REWRITE_RULE[eqenv_def] step_sem]);;

let steps_correct = prove
 (`!mu tau:(A option#A option) list.
     windmill mu /\ ALL IS_SOME (MAP FST mu) /\ ALL IS_SOME (MAP SND mu) /\
     RTC parmove_step (mu,[],[]) ([],[],tau)
     ==> !rho:A option->B. eqenv (parsem mu rho) (seqsem (REVERSE tau) rho)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
    [`(mu,[],[]):(A option#A option) list#(A option#A option) list#
                 (A option#A option) list`;
     `([],[],tau):(A option#A option) list#(A option#A option) list#
                  (A option#A option) list`] steps_sem) THEN
  ASM_SIMP_TAC[wf_init] THEN DISCH_THEN(MP_TAC o SPEC `rho:A option->B`) THEN
  REWRITE_TAC[parmove_sem_def; APPEND_NIL; APPEND; REVERSE; seqsem_def; parsem_nil; I_THM]);;

(* deterministic algorithm *)

(* HOL4 writes dstep as an infix (a hooked arrow) and RTC dstep starred *)
let dstep_rules,dstep_ind,dstep_cases,dstep_strongind = cake_inductive
  `(!(r:A option) mu tau.
      dstep (APPEND [(r,r)] mu,[],tau) (mu,[],tau)) /\
   (!s d mu tau.
      ~(s = d) ==> dstep (APPEND [(d,s)] mu,[],tau) (mu,[(d,s)],tau)) /\
   (!mu1 d r mu2 s sigma tau.
      ~MEM d (MAP SND mu1)
      ==> dstep (APPEND (APPEND mu1 [(r,d)]) mu2,APPEND [(d,s)] sigma,tau)
                (APPEND mu1 mu2,APPEND [(r,d); (d,s)] sigma,tau)) /\
   (!mu r s sigma d tau.
      ~MEM r (MAP SND mu)
      ==> dstep (mu,APPEND (APPEND [(r,s)] sigma) [(d,r)],tau)
                (mu,APPEND sigma [(d,NONE)],APPEND [(r,s); (NONE,r)] tau)) /\
   (!mu dn sn sigma d0 s0 tau.
      ~MEM dn (MAP SND mu) /\ ~(dn = s0)
      ==> dstep (mu,APPEND (APPEND [(dn,sn)] sigma) [(d0,s0)],tau)
                (mu,APPEND sigma [(d0,s0)],APPEND [(dn,sn)] tau)) /\
   (!mu d s tau.
      ~MEM d (MAP SND mu)
      ==> dstep (mu,[(d,s)],tau) (mu,[],APPEND [(d,s)] tau))`;;

(* HOL4: the condition parmove_wf s1 is not in the paper *)
let dstep_step = prove
 (`!s1 s2:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     dstep s1 s2 ==> parmove_wf s1 ==> RTC parmove_step s1 s2`,
  let rule k = el (k - 1) (CONJUNCTS parmove_step_rules) in
  MATCH_MP_TAC dstep_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC RTC_INC THEN
    MP_TAC(ISPECL [`[]:(A option#A option) list`; `mu:(A option#A option) list`;
                   `r:A option`; `[]:(A option#A option) list`;
                   `tau:(A option#A option) list`] (rule 1)) THEN
    REWRITE_TAC[APPEND];
    REPEAT DISCH_TAC THEN MATCH_MP_TAC RTC_INC THEN
    MP_TAC(ISPECL [`[]:(A option#A option) list`; `mu:(A option#A option) list`;
                   `d:A option`; `s:A option`;
                   `tau:(A option#A option) list`] (rule 2)) THEN
    REWRITE_TAC[APPEND];
    REPEAT DISCH_TAC THEN MATCH_MP_TAC RTC_INC THEN REWRITE_TAC[parmove_step_rules];
    REPEAT DISCH_TAC THEN MATCH_MP_TAC RTC_TRANS_L THEN
    EXISTS_TAC `(mu,APPEND (APPEND [(r,s)] sigma) [(d,NONE)],APPEND [(NONE,r)] tau):
      (A option#A option) list#(A option#A option) list#(A option#A option) list` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RTC_INC THEN REWRITE_TAC[parmove_step_rules];
      SUBGOAL_THEN `~(r:A option = NONE)` ASSUME_TAC THENL
       [UNDISCH_TAC `parmove_wf (mu,APPEND (APPEND [(r:A option,s:A option)] sigma)
                                [(d,r)],tau:(A option#A option) list)` THEN
        REWRITE_TAC[parmove_wf_def; MAP_APPEND; MAP; ALL_APPEND; ALL; APPEND] THEN
        MESON_TAC[IS_SOME_DEF];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`mu:(A option#A option) list`; `r:A option`; `s:A option`;
                     `sigma:(A option#A option) list`; `d:A option`;
                     `NONE:A option`; `APPEND [(NONE,r)] tau:(A option#A option) list`]
                    (rule 5)) THEN
      ASM_REWRITE_TAC[APPEND]];
    REPEAT DISCH_TAC THEN MATCH_MP_TAC RTC_INC THEN MATCH_MP_TAC (rule 5) THEN
    ASM_REWRITE_TAC[];
    REPEAT DISCH_TAC THEN MATCH_MP_TAC RTC_INC THEN MATCH_MP_TAC (rule 6) THEN
    ASM_REWRITE_TAC[]]);;

let dsteps_steps = prove
 (`!s1 s2:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     RTC dstep s1 s2 ==> parmove_wf s1 ==> RTC parmove_step s1 s2`,
  MATCH_MP_TAC RTC_INDUCT_R THEN
  MESON_TAC[dstep_step; wf_steps; RTC_REFL; RTC_TRANS]);;

(* functional algorithm *)

let fstep_def = cake_def
  `fstep (st:(A option#A option) list#(A option#A option) list#(A option#A option) list) =
   match st with
     ([],[],_) -> st
   | (CONS (d,s) t,[],l) -> if s = d then (t,[],l) else (t,[(d,s)],l)
   | (t,CONS (d,s) b,l) ->
       splitAtPki (\i p. SND p = d)
         (\t1 rt2. match rt2 with
             CONS rd t2 -> (APPEND t1 t2,CONS rd (CONS (d,s) b),l)
           | [] -> if NULL b then (t,[],CONS (d,s) l) else
                   match (BUTLAST b,LAST b) with
                     (b',(d',s')) ->
                       if s' = d
                       then (t,SNOC (d',NONE) b',CONS (d,s) (CONS (NONE,d) l))
                       else (t,b,CONS (d,s) l))
         t`;;

(* PARMOVEAUX_fstep_thm: the clauses of fstep_def for the three shapes of state *)
let PARMOVEAUX_fstep_thm = prove
 (CASE_TERM
  `(!l:(A option#A option) list. fstep ([],[],l) = ([],[],l)) /\
   (!(d:A option) s t l.
      fstep (CONS (d,s) t,[],l) = if s = d then (t,[],l) else (t,[(d,s)],l)) /\
   (!mu (d:A option) s b l.
      fstep (mu,CONS (d,s) b,l) =
      splitAtPki (\i p. SND p = d)
        (\t1 rt2. match rt2 with
            CONS rd t2 -> (APPEND t1 t2,CONS rd (CONS (d,s) b),l)
          | [] -> if NULL b then (mu,[],CONS (d,s) l) else
                  match LAST b with
                    (d',s') ->
                      if s' = d
                      then (mu,SNOC (d',NONE) (BUTLAST b),CONS (d,s) (CONS (NONE,d) l))
                      else (mu,b,CONS (d,s) l))
        mu)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY(CASES_ON `mu:(A option#A option) list`) THEN
  REWRITE_TAC[fstep_def; pair_CASE; list_CASE] THEN REWRITE_TAC[pair_CASE_def]);;

let PARMOVEAUX_OLEAST_SND = prove
 (`!(l:(A#B) list) d.
     (OLEAST i. i < LENGTH l /\ SND (EL i l) = d) = NONE <=> ~MEM d (MAP SND l)`,
  REWRITE_TAC[OLEAST_DEF] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_DISTINCT; MEM_MAP; MEM_EXISTS_EL] THEN ASM_MESON_TAC[]);;

let fstep_dstep = prove
 (`!s:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     (!tau. ~(s = ([],[],tau))) ==> dstep s (fstep s)`,
  let drule k = el (k - 1) (CONJUNCTS dstep_rules) in
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`mu:(A option#A option) list`; `sigma:(A option#A option) list`;
                       `tau:(A option#A option) list`] THEN
  STRUCT_CASES_TAC (ISPEC `sigma:(A option#A option) list` list_CASES) THENL
   [STRUCT_CASES_TAC (ISPEC `mu:(A option#A option) list` list_CASES) THEN
    REWRITE_TAC[NOT_CONS_NIL] THENL [MESON_TAC[]; ALL_TAC] THEN
    SPEC_TAC (`h:A option#A option`, `h:A option#A option`) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`d:A option`; `s:A option`] THEN
    REWRITE_TAC[PARMOVEAUX_fstep_thm] THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN
      MP_TAC(ISPECL [`d:A option`; `t:(A option#A option) list`;
                     `tau:(A option#A option) list`] (drule 1)) THEN
      REWRITE_TAC[APPEND];
      MP_TAC(ISPECL [`s:A option`; `d:A option`; `t:(A option#A option) list`;
                     `tau:(A option#A option) list`] (drule 2)) THEN
      ASM_REWRITE_TAC[APPEND]];
    ALL_TAC] THEN
  SPEC_TAC (`h:A option#A option`, `h:A option#A option`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; NOT_CONS_NIL] THEN
  MAP_EVERY X_GEN_TAC [`d:A option`; `s:A option`] THEN
  REWRITE_TAC[PARMOVEAUX_fstep_thm; splitAtPki_EQN] THEN
  CASES_ON `OLEAST i. i < LENGTH mu /\ SND (EL i mu:A option#A option) = d` THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[PARMOVEAUX_OLEAST_SND]) THEN
    REWRITE_TAC[option_CASE; list_CASE] THEN
    STRUCT_CASES_TAC (ISPEC `t:(A option#A option) list` SNOC_CASES) THEN
    REWRITE_TAC[NULL; NULL_EQ_NIL; SNOC_APPEND; APPEND_EQ_NIL; NOT_CONS_NIL] THENL
     [MP_TAC(ISPECL [`mu:(A option#A option) list`; `d:A option`; `s:A option`;
                     `tau:(A option#A option) list`] (drule 6)) THEN
      ASM_REWRITE_TAC[APPEND];
      ALL_TAC] THEN
    REWRITE_TAC[LAST_APPEND; BUTLAST_APPEND; NOT_CONS_NIL; LAST; BUTLAST; APPEND_NIL] THEN
    SPEC_TAC (`x:A option#A option`, `x:A option#A option`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; pair_CASE] THEN
    MAP_EVERY X_GEN_TAC [`d':A option`; `s':A option`] THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN
      MP_TAC(ISPECL [`mu:(A option#A option) list`; `d:A option`; `s:A option`;
                     `l':(A option#A option) list`; `d':A option`;
                     `tau:(A option#A option) list`] (drule 4)) THEN
      ASM_REWRITE_TAC[APPEND];
      MP_TAC(ISPECL [`mu:(A option#A option) list`; `d:A option`; `s:A option`;
                     `l':(A option#A option) list`; `d':A option`; `s':A option`;
                     `tau:(A option#A option) list`] (drule 5)) THEN
      ASM_REWRITE_TAC[APPEND] THEN ASM_MESON_TAC[]];
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP OLEAST_SOME_IMP) THEN
    RULE_ASSUM_TAC BETA_RULE THEN
    ASM_SIMP_TAC[option_CASE; DROP_CONS_EL; list_CASE] THEN
    SUBGOAL_THEN `(FST (EL a mu), d) = EL a (mu:(A option#A option) list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[PAIR]; ALL_TAC] THEN
    SUBGOAL_THEN `APPEND (APPEND (TAKE a mu) [EL a mu]) (DROP (SUC a) mu) =
                  mu:(A option#A option) list` ASSUME_TAC THENL
     [ASM_SIMP_TAC[GSYM APPEND_ASSOC; APPEND; GSYM DROP_CONS_EL; TAKE_DROP]; ALL_TAC] THEN
    MP_TAC(ISPECL [`TAKE a mu:(A option#A option) list`; `d:A option`;
      `FST (EL a mu:A option#A option)`; `DROP (SUC a) mu:(A option#A option) list`;
      `s:A option`; `t:(A option#A option) list`; `tau:(A option#A option) list`]
      (drule 3)) THEN
    ASM_REWRITE_TAC[APPEND] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `LENGTH (TAKE a mu:(A option#A option) list) = a` ASSUME_TAC THENL
     [MATCH_MP_TAC LENGTH_TAKE THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[MEM_MAP; MEM_EXISTS_EL] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_SIMP_TAC[EL_TAKE] THEN ASM_ARITH_TAC]);;

(* PARMOVEAUX_dstep_measure: every dstep decreases the termination measure of pmov *)
let PARMOVEAUX_dstep_measure = prove
 (`!s1 s2:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     dstep s1 s2
     ==> 2 * LENGTH (FST s2) + LENGTH (FST (SND s2)) <
         2 * LENGTH (FST s1) + LENGTH (FST (SND s1))`,
  MATCH_MP_TAC dstep_ind THEN REWRITE_TAC[LENGTH; LENGTH_APPEND; FST; SND] THEN ARITH_TAC);;

(* HOL4 Termination: measure of (mu,sigma,tau) = twice LENGTH mu plus LENGTH sigma *)
let pmov_def = cake_def_wf
  `MEASURE (\s:(A option#A option) list#(A option#A option) list#(A option#A option) list.
              2 * LENGTH (FST s) + LENGTH (FST (SND s)))`
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   MATCH_MP_TAC PARMOVEAUX_dstep_measure THEN MATCH_MP_TAC fstep_dstep THEN
   REWRITE_TAC[PAIR_EQ; NOT_CONS_NIL])
  `pmov (s:(A option#A option) list#(A option#A option) list#(A option#A option) list) =
   match s with ([],[],_) -> s | _ -> pmov (fstep s)`;;

let pmov_ind = cake_ind "pmov";;

let PARMOVEAUX_pmov_thm = prove
 (`!s:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     pmov s = if ?tau. s = ([],[],tau) then s else pmov (fstep s)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`mu:(A option#A option) list`; `sigma:(A option#A option) list`;
                       `tau:(A option#A option) list`] THEN
  GEN_REWRITE_TAC LAND_CONV [pmov_def] THEN
  STRUCT_CASES_TAC (ISPEC `mu:(A option#A option) list` list_CASES) THEN
  STRUCT_CASES_TAC (ISPEC `sigma:(A option#A option) list` list_CASES) THEN
  REWRITE_TAC[pair_CASE; list_CASE; PAIR_EQ; NOT_CONS_NIL;
              MESON[] `!a:A option#A option. ?x. a = x`;
              MESON[] `!a:(A option#A option) list. ?x. a = x`]);;

let PARMOVEAUX_state_cases = prove
 (`!s:(A#B) list#(C#D) list#E.
     (?tau. s = ([],[],tau)) \/ (?a0 a1 y. s = ([],CONS a0 a1,y)) \/
     (?a0 a1 y. s = (CONS a0 a1,y))`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`mu:(A#B) list`; `sigma:(C#D) list`; `tau:E`] THEN
  STRUCT_CASES_TAC (ISPEC `mu:(A#B) list` list_CASES) THEN
  STRUCT_CASES_TAC (ISPEC `sigma:(C#D) list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN MESON_TAC[PAIR_SURJECTIVE]);;

let pmov_dsteps = prove
 (`!s:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     RTC dstep s (pmov s)`,
  MATCH_MP_TAC pmov_ind THEN
  X_GEN_TAC `s:(A option#A option) list#(A option#A option) list#(A option#A option) list` THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[PARMOVEAUX_pmov_thm] THEN
  COND_CASES_TAC THEN REWRITE_TAC[RTC_REFL] THEN
  MATCH_MP_TAC RTC_TRANS_R THEN
  EXISTS_TAC `fstep (s:(A option#A option) list#(A option#A option) list#
                       (A option#A option) list)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC fstep_dstep THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[PARMOVEAUX_state_cases]]);;

let pmov_final = prove
 (`!s:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     ?tau. pmov s = ([],[],tau)`,
  MATCH_MP_TAC pmov_ind THEN
  X_GEN_TAC `s:(A option#A option) list#(A option#A option) list#(A option#A option) list` THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[PARMOVEAUX_pmov_thm] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[PARMOVEAUX_state_cases]);;

(* The top-level parallel move compiler *)

(* HOL4: MAP (\(x,y). (SOME x,SOME y)) xs *)
let parmove_def = cake_def
  `parmove (xs:(A#A) list) =
     REVERSE (SND (SND (pmov (MAP (\xy. match xy with (x,y) -> (SOME x,SOME y)) xs,
                              [],[]))))`;;

let PARMOVEAUX_MAP_SOME = prove
 (CASE_TERM `!xs:(A#B) list.
     MAP FST (MAP (\xy. match xy with (x,y) -> (SOME x,SOME y)) xs) =
     MAP SOME (MAP FST xs) /\
     MAP SND (MAP (\xy. match xy with (x,y) -> (SOME x,SOME y)) xs) =
     MAP SOME (MAP SND xs)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; pair_CASE]);;

let PARMOVEAUX_wf_parmove = prove
 (CASE_TERM `!xs:(A#A) list.
     windmill xs
     ==> windmill (MAP (\xy. match xy with (x,y) -> (SOME x,SOME y)) xs) /\
         ALL IS_SOME (MAP FST (MAP (\xy. match xy with (x,y) -> (SOME x,SOME y)) xs)) /\
         ALL IS_SOME (MAP SND (MAP (\xy. match xy with (x,y) -> (SOME x,SOME y)) xs)) /\
         parmove_wf (MAP (\xy. match xy with (x,y) -> (SOME x,SOME y)) xs,[],
                     []:(A option#A option) list)`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(a /\ b /\ c) /\ (a /\ b /\ c ==> d) ==> a /\ b /\ c /\ d`) THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[wf_init]] THEN
  REWRITE_TAC[windmill_def; PARMOVEAUX_MAP_SOME] THEN
  REWRITE_TAC[ALL_MAP; o_DEF; IS_SOME_DEF; ALL_T] THEN
  MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN
  RULE_ASSUM_TAC(REWRITE_RULE[windmill_def]) THEN ASM_SIMP_TAC[option_INJ]);;

let parmove_correct = prove
 (CASE_TERM `!xs:(A#A) list.
     windmill xs
     ==> !rho:A option->B.
           eqenv (seqsem (parmove xs) rho)
                 (parsem (MAP (\xy. match xy with (x,y) -> (SOME x,SOME y)) xs) rho)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC eqenv_sym THEN REWRITE_TAC[parmove_def] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PARMOVEAUX_wf_parmove) THEN
  MP_TAC(ISPEC `(MAP (\xy:A#A. pair_CASE xy (\x y. (SOME x,SOME y))) xs,[],[]):
     (A option#A option) list#(A option#A option) list#(A option#A option) list`
     pmov_final) THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:(A option#A option) list` ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN SPEC_TAC(`rho:A option->B`,`rho:A option->B`) THEN
  MATCH_MP_TAC steps_correct THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] dsteps_steps) THEN ASM_REWRITE_TAC[pmov_dsteps]);;

(* the compiler does not invent new moves *)

(* PARMOVEAUX_dsteps_MEM: a SOME register of a later state is a register of *)
(* the earlier one, as a destination and as a source (the HOL4 proofs of    *)
(* the two theorems below unfold pmov and fstep instead)                    *)
let PARMOVEAUX_dstep_MEM = prove
 (`!s1 s2:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     dstep s1 s2
     ==> !x. (MEM (SOME x) (MAP FST (APPEND (APPEND (FST s2) (FST (SND s2))) (SND (SND s2))))
              ==> MEM (SOME x)
                    (MAP FST (APPEND (APPEND (FST s1) (FST (SND s1))) (SND (SND s1))))) /\
             (MEM (SOME x) (MAP SND (APPEND (APPEND (FST s2) (FST (SND s2))) (SND (SND s2))))
              ==> MEM (SOME x)
                    (MAP SND (APPEND (APPEND (FST s1) (FST (SND s1))) (SND (SND s1)))))`,
  MATCH_MP_TAC dstep_ind THEN
  REWRITE_TAC[MAP_APPEND; MEM_APPEND; MAP; MEM; FST; SND; distinctness "option"] THEN
  MESON_TAC[]);;

let PARMOVEAUX_dsteps_MEM = prove
 (`!s1 s2:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     RTC dstep s1 s2
     ==> !x. (MEM (SOME x) (MAP FST (APPEND (APPEND (FST s2) (FST (SND s2))) (SND (SND s2))))
              ==> MEM (SOME x)
                    (MAP FST (APPEND (APPEND (FST s1) (FST (SND s1))) (SND (SND s1))))) /\
             (MEM (SOME x) (MAP SND (APPEND (APPEND (FST s2) (FST (SND s2))) (SND (SND s2))))
              ==> MEM (SOME x)
                    (MAP SND (APPEND (APPEND (FST s1) (FST (SND s1))) (SND (SND s1)))))`,
  MATCH_MP_TAC RTC_INDUCT_R THEN MESON_TAC[PARMOVEAUX_dstep_MEM]);;

let MEM_MAP_FST_SND_SND_pmov = prove
 (`!p:(A option#A option) list#(A option#A option) list#(A option#A option) list.
   !x. MEM (SOME x) (MAP FST (SND (SND (pmov p))))
       ==> MEM (SOME x) (MAP FST (APPEND (APPEND (FST p) (FST (SND p))) (SND (SND p))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(CONJUNCT1(SPEC `x:A` (MATCH_MP PARMOVEAUX_dsteps_MEM (SPEC
    `p:(A option#A option) list#(A option#A option) list#(A option#A option) list`
    pmov_dsteps)))) THEN
  ASM_REWRITE_TAC[MAP_APPEND; MEM_APPEND]);;

let MEM_MAP_FST_parmove = prove
 (`!(x:A) mvs. MEM (SOME x) (MAP FST (parmove mvs)) ==> MEM x (MAP FST mvs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[parmove_def; rich_list_MAP_REVERSE; MEM_REVERSE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEM_MAP_FST_SND_SND_pmov) THEN
  REWRITE_TAC[FST; SND; APPEND_NIL; PARMOVEAUX_MAP_SOME] THEN
  REWRITE_TAC[MEM_MAP; option_INJ] THEN
  MESON_TAC[]);;

let MEM_MAP_SND_SND_SND_pmov = prove
 (`!p:(A option#A option) list#(A option#A option) list#(A option#A option) list.
   !x. MEM (SOME x) (MAP SND (SND (SND (pmov p))))
       ==> MEM (SOME x) (MAP SND (APPEND (APPEND (FST p) (FST (SND p))) (SND (SND p))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(CONJUNCT2(SPEC `x:A` (MATCH_MP PARMOVEAUX_dsteps_MEM (SPEC
    `p:(A option#A option) list#(A option#A option) list#(A option#A option) list`
    pmov_dsteps)))) THEN
  ASM_REWRITE_TAC[MAP_APPEND; MEM_APPEND]);;

let MEM_MAP_SND_parmove = prove
 (`!(x:A) mvs. MEM (SOME x) (MAP SND (parmove mvs)) ==> MEM x (MAP SND mvs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[parmove_def; rich_list_MAP_REVERSE; MEM_REVERSE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEM_MAP_SND_SND_SND_pmov) THEN
  REWRITE_TAC[FST; SND; APPEND_NIL; PARMOVEAUX_MAP_SOME] THEN
  REWRITE_TAC[MEM_MAP; option_INJ] THEN
  MESON_TAC[]);;

(* the compiler does not use uninitialised temporaries *)

let not_use_temp_before_assign_def = cake_def
  `(not_use_temp_before_assign ([]:(A option#B option) list) <=> T) /\
   (not_use_temp_before_assign (CONS (d,NONE) ls) <=> F) /\
   (not_use_temp_before_assign (CONS (NONE,s) ls) <=> T) /\
   (not_use_temp_before_assign (CONS (d,s) ls) <=> not_use_temp_before_assign ls)`;;

let not_use_temp_before_assign_ind = cake_ind "not_use_temp_before_assign";;
let _ = cake_add_simps [not_use_temp_before_assign_def];;

let not_use_temp_before_assign_append = prove
 (`!l1 l2:(A option#B option) list.
     not_use_temp_before_assign (APPEND l1 l2) <=>
     not_use_temp_before_assign l1 /\
     (ALL IS_SOME (MAP FST l1) ==> not_use_temp_before_assign l2)`,
  MATCH_MP_TAC not_use_temp_before_assign_ind THEN
  ASM_REWRITE_TAC[not_use_temp_before_assign_def; APPEND; MAP; ALL; IS_SOME_DEF; FST]);;

let not_use_temp_before_assign_insert = prove
 (`!(x:A) (y:B) l1 l2.
     not_use_temp_before_assign (APPEND l1 l2)
     ==> not_use_temp_before_assign (APPEND (APPEND l1 [(SOME x,SOME y)]) l2)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC not_use_temp_before_assign_ind THEN
  ASM_REWRITE_TAC[not_use_temp_before_assign_def; APPEND] THEN
  ASM_SIMP_TAC[GSYM APPEND_ASSOC; APPEND; not_use_temp_before_assign_def]);;

let not_use_temp_before_assign_thm = prove
 (`!ls:(A option#B option) list.
     not_use_temp_before_assign ls <=>
     !i. find_index NONE (MAP SND ls) 0 = SOME i
         ==> ?j. find_index NONE (MAP FST ls) 0 = SOME j /\ j < i`,
  MATCH_MP_TAC not_use_temp_before_assign_ind THEN
  REWRITE_TAC[not_use_temp_before_assign_def; MAP; find_index_def; FST; SND;
              distinctness "option"; option_INJ; ARITH] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FORALL_UNWIND_THM1; LT];
    REPEAT STRIP_TAC THEN EXISTS_TAC `0` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP find_index_LESS_LENGTH) THEN ARITH_TAC;
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GEN_ALL(INST [`1`,`k:num`] (SPEC_ALL find_index_shift_0))] THEN
    SPEC_TAC(`find_index NONE (MAP SND (ls:(A option#B option) list)) 0`, `o1:num option`) THEN
    SPEC_TAC(`find_index NONE (MAP FST (ls:(A option#B option) list)) 0`, `o2:num option`) THEN
    MATCH_MP_TAC option_INDUCT THEN CONJ_TAC THENL [ALL_TAC; GEN_TAC] THEN
    MATCH_MP_TAC option_INDUCT THEN
    REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ; FORALL_UNWIND_THM1;
                UNWIND_THM1] THEN
    (ARITH_TAC ORELSE MESON_TAC[])]);;

let PARMOVEAUX_nutba_cons_snoc = prove
 (`!(x:A option#B option) l a b.
     not_use_temp_before_assign (CONS x (APPEND l [(SOME a,SOME b)])) <=>
     not_use_temp_before_assign (CONS x l)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`CONS (x:A option#B option) l`; `[(SOME (a:A),SOME (b:B))]`]
    not_use_temp_before_assign_append) THEN
  REWRITE_TAC[APPEND; not_use_temp_before_assign_def] THEN SIMP_TAC[]);;

let step_not_use_temp_before_assign = prove
 (`!s1 s2:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     parmove_step s1 s2
     ==> parmove_wf s1 /\
         not_use_temp_before_assign (REVERSE (APPEND (FST (SND s1)) (SND (SND s1))))
         ==> not_use_temp_before_assign (REVERSE (APPEND (FST (SND s2)) (SND (SND s2))))`,
  MATCH_MP_TAC parmove_step_ind THEN
  REWRITE_TAC[FST; SND; parmove_wf_def; REVERSE_APPEND; REVERSE; APPEND; APPEND_NIL;
              not_use_temp_before_assign_append; MAP_APPEND; ALL_APPEND; MAP; ALL;
              rich_list_MAP_REVERSE; EVERY_REVERSE] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[IS_SOME_EXISTS] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[not_use_temp_before_assign_def];
    REPEAT GEN_TAC THEN REWRITE_TAC[IS_SOME_EXISTS] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[not_use_temp_before_assign_def] THEN ASM_MESON_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[IS_SOME_DEF] THEN
    STRUCT_CASES_TAC (ISPEC `s:A option` option_CASES) THEN
    REWRITE_TAC[IS_SOME_EXISTS] THEN STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[not_use_temp_before_assign_def] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[not_use_temp_before_assign_def]) THEN
    ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[NULL; BUTLAST; BUTLAST_APPEND; APPEND_EQ_NIL; NOT_CONS_NIL; BUTLAST;
                APPEND_NIL; MAP; ALL] THEN
    REWRITE_TAC[IS_SOME_EXISTS] THEN STRIP_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PARMOVEAUX_nutba_cons_snoc]) THEN
    ASM_REWRITE_TAC[not_use_temp_before_assign_def] THEN ASM_MESON_TAC[];
    MESON_TAC[]]);;

let steps_not_use_temp_before_assign = prove
 (`!s1 s2:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     (\s1. parmove_wf s1 /\
           not_use_temp_before_assign (REVERSE (APPEND (FST (SND s1)) (SND (SND s1))))) s1 /\
     RTC parmove_step s1 s2
     ==> (\s1. parmove_wf s1 /\
               not_use_temp_before_assign (REVERSE (APPEND (FST (SND s1)) (SND (SND s1)))))
         s2`,
  MATCH_MP_TAC RTC_lifts_invariants THEN REWRITE_TAC[] THEN
  MESON_TAC[wf_step; step_not_use_temp_before_assign]);;

let pmov_not_use_temp_before_assign = prove
 (`!(p:(A option#A option) list#(A option#A option) list#(A option#A option) list)
    (i:B).
     parmove_wf p /\
     not_use_temp_before_assign (REVERSE (APPEND (FST (SND p)) (SND (SND p))))
     ==> not_use_temp_before_assign
           (REVERSE (APPEND (FST (SND (pmov p))) (SND (SND (pmov p)))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:(A option#A option) list#(A option#A option) list#
                  (A option#A option) list`;
                `pmov (p:(A option#A option) list#(A option#A option) list#
                        (A option#A option) list)`] steps_not_use_temp_before_assign) THEN
  ASM_SIMP_TAC[REWRITE_RULE[IMP_IMP] dsteps_steps; pmov_dsteps]);;

let parmove_not_use_temp_before_assign = prove
 (CASE_TERM `!mvs:(A#A) list.
    windmill mvs
    ==> match find_index NONE (MAP SND (parmove mvs)) 0 with
          NONE -> T
        | SOME i -> (match find_index NONE (MAP FST (parmove mvs)) 0 with
                       NONE -> F
                     | SOME j -> ~(i <= j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `not_use_temp_before_assign (parmove (mvs:(A#A) list))` MP_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PARMOVEAUX_wf_parmove) THEN
    MP_TAC(ISPEC `(MAP (\xy:A#A. pair_CASE xy (\x y. (SOME x,SOME y))) mvs,[],[]):
       (A option#A option) list#(A option#A option) list#(A option#A option) list`
       pmov_final) THEN
    DISCH_THEN(X_CHOOSE_TAC `tau:(A option#A option) list`) THEN
    MP_TAC(ISPECL [`(MAP (\xy:A#A. pair_CASE xy (\x y. (SOME x,SOME y))) mvs,[],[]):
       (A option#A option) list#(A option#A option) list#(A option#A option) list`;
       `ARB:num`] pmov_not_use_temp_before_assign) THEN
    ASM_REWRITE_TAC[parmove_def; FST; SND; APPEND; REVERSE;
                    not_use_temp_before_assign_def];
    REWRITE_TAC[not_use_temp_before_assign_thm] THEN
    SPEC_TAC(`find_index NONE (MAP SND (parmove (mvs:(A#A) list))) 0`, `o1:num option`) THEN
    SPEC_TAC(`find_index NONE (MAP FST (parmove (mvs:(A#A) list))) 0`, `o2:num option`) THEN
    MATCH_MP_TAC option_INDUCT THEN CONJ_TAC THENL [ALL_TAC; GEN_TAC] THEN
    MATCH_MP_TAC option_INDUCT THEN
    REWRITE_TAC[option_CASE; option_DISTINCT; option_INJ; FORALL_UNWIND_THM1;
                UNWIND_THM1] THEN
    (ARITH_TAC ORELSE MESON_TAC[])]);;

(* the compiler preserves all-distinct variables *)

let ALL_DISTINCT_step = prove
 (`!s1 s2:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     parmove_step s1 s2
     ==> ALL_DISTINCT (FILTER IS_SOME
           (MAP FST (APPEND (APPEND (FST s1) (FST (SND s1))) (SND (SND s1)))))
     ==> ALL_DISTINCT (FILTER IS_SOME
           (MAP FST (APPEND (APPEND (FST s2) (FST (SND s2))) (SND (SND s2)))))`,
  MATCH_MP_TAC parmove_step_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[FST; SND; MAP_APPEND; FILTER_APPEND; MAP; FILTER; IS_SOME_DEF; APPEND;
              APPEND_NIL] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[ALL_DISTINCT_APPEND; ALL_DISTINCT; MEM_APPEND; MEM; APPEND; APPEND_NIL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let ALL_DISTINCT_steps = prove
 (`!s1 s2:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     (\s1. ALL_DISTINCT (FILTER IS_SOME
             (MAP FST (APPEND (APPEND (FST s1) (FST (SND s1))) (SND (SND s1)))))) s1 /\
     RTC parmove_step s1 s2
     ==> (\s1. ALL_DISTINCT (FILTER IS_SOME
             (MAP FST (APPEND (APPEND (FST s1) (FST (SND s1))) (SND (SND s1)))))) s2`,
  MATCH_MP_TAC RTC_lifts_invariants THEN REWRITE_TAC[] THEN
  MESON_TAC[ALL_DISTINCT_step]);;

let ALL_DISTINCT_pmov = prove
 (`!p:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     parmove_wf p /\
     ALL_DISTINCT (FILTER IS_SOME
       (MAP FST (APPEND (APPEND (FST p) (FST (SND p))) (SND (SND p)))))
     ==> ALL_DISTINCT (FILTER IS_SOME
           (MAP FST (APPEND (APPEND (FST (pmov p)) (FST (SND (pmov p))))
                            (SND (SND (pmov p))))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:(A option#A option) list#(A option#A option) list#
                  (A option#A option) list`;
                `pmov (p:(A option#A option) list#(A option#A option) list#
                        (A option#A option) list)`] ALL_DISTINCT_steps) THEN
  ASM_SIMP_TAC[REWRITE_RULE[IMP_IMP] dsteps_steps; pmov_dsteps]);;

let ALL_DISTINCT_parmove = prove
 (`!mvs:(A#A) list.
     ALL_DISTINCT (MAP FST mvs)
     ==> ALL_DISTINCT (FILTER IS_SOME (MAP FST (parmove mvs)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[parmove_def; rich_list_MAP_REVERSE; FILTER_REVERSE; ALL_DISTINCT_REVERSE] THEN
  SUBGOAL_THEN `windmill (mvs:(A#A) list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[windmill_def]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PARMOVEAUX_wf_parmove) THEN
  MP_TAC(ISPEC `(MAP (\xy:A#A. pair_CASE xy (\x y. (SOME x,SOME y))) mvs,[],[]):
     (A option#A option) list#(A option#A option) list#(A option#A option) list`
     pmov_final) THEN
  DISCH_THEN(X_CHOOSE_TAC `tau:(A option#A option) list`) THEN
  MP_TAC(ISPEC `(MAP (\xy:A#A. pair_CASE xy (\x y. (SOME x,SOME y))) mvs,[],[]):
     (A option#A option) list#(A option#A option) list#(A option#A option) list`
     ALL_DISTINCT_pmov) THEN
  ASM_REWRITE_TAC[FST; SND; APPEND; APPEND_NIL; MAP; FILTER] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[PARMOVEAUX_MAP_SOME] THEN
  SUBGOAL_THEN `!l:A list. FILTER IS_SOME (MAP SOME l) = MAP SOME l`
    (fun th -> REWRITE_TAC[th]) THENL
   [LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; FILTER; IS_SOME_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN ASM_SIMP_TAC[option_INJ]);;

(* the compiler retains all non-trivial moves *)

let state_to_list_def = cake_def
  `state_to_list (p:A list#A list#A list) = APPEND (APPEND (FST p) (FST (SND p))) (SND (SND p))`;;

let step_preserves_moves = prove
 (`!s1 s2:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     parmove_step s1 s2
     ==> !x. (?y. MEM (x,y) (state_to_list s1) /\ ~(x = y))
             ==> (?y. MEM (x,y) (state_to_list s2) /\ ~(x = y))`,
  MATCH_MP_TAC parmove_step_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[state_to_list_def; FST; SND; MEM_APPEND; MEM; PAIR_EQ] THEN
  MESON_TAC[]);;

let steps_preserves_moves = prove
 (`!(x:A option) s1 s2:(A option#A option) list#(A option#A option) list#
                       (A option#A option) list.
     (\s1. ?y. MEM (x,y) (state_to_list s1) /\ ~(x = y)) s1 /\ RTC parmove_step s1 s2
     ==> (\s1. ?y. MEM (x,y) (state_to_list s1) /\ ~(x = y)) s2`,
  GEN_TAC THEN MATCH_MP_TAC RTC_lifts_invariants THEN REWRITE_TAC[] THEN
  MESON_TAC[step_preserves_moves]);;

let pmov_preserves_moves = prove
 (`!(p:(A option#A option) list#(A option#A option) list#(A option#A option) list)
    x y.
     parmove_wf p /\ MEM (x,y) (state_to_list p) /\ ~(x = y)
     ==> MEM x (MAP FST (state_to_list (pmov p)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:A option`;
                `p:(A option#A option) list#(A option#A option) list#
                   (A option#A option) list`;
                `pmov (p:(A option#A option) list#(A option#A option) list#
                        (A option#A option) list)`] steps_preserves_moves) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REWRITE_RULE[IMP_IMP] dsteps_steps; pmov_dsteps] THEN ASM_MESON_TAC[];
    REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN MESON_TAC[FST]]);;

let parmove_preserves_moves = prove
 (`!moves (x:A) y.
     windmill moves /\ MEM (x,y) moves /\ ~(x = y)
     ==> MEM (SOME x) (MAP FST (parmove moves))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[parmove_def; rich_list_MAP_REVERSE; MEM_REVERSE] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PARMOVEAUX_wf_parmove) THEN
  MP_TAC(ISPEC `(MAP (\xy:A#A. pair_CASE xy (\x y. (SOME x,SOME y))) moves,[],[]):
     (A option#A option) list#(A option#A option) list#(A option#A option) list`
     pmov_final) THEN
  DISCH_THEN(X_CHOOSE_TAC `tau:(A option#A option) list`) THEN
  MP_TAC(ISPECL [`(MAP (\xy:A#A. pair_CASE xy (\x y. (SOME x,SOME y))) moves,[],[]):
     (A option#A option) list#(A option#A option) list#(A option#A option) list`;
     `SOME (x:A)`; `SOME (y:A)`] pmov_preserves_moves) THEN
  ASM_REWRITE_TAC[state_to_list_def; FST; SND; APPEND; APPEND_NIL; option_INJ] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[MEM_MAP] THEN
  EXISTS_TAC `(x:A,y:A)` THEN ASM_REWRITE_TAC[pair_CASE]);;

(* mapping an injective function over compiled moves *)

let map_state_def = cake_def
  `map_state (f:A->B) = let m = MAP (f ## f) in m ## m ## m`;;

let inj_on_state_def = cake_def
  `inj_on_state (f:A option->B option)
     (p:(A option#A option) list#(A option#A option) list#(A option#A option) list) <=>
     let ls0 = state_to_list p in
     let ls = APPEND (MAP FST ls0) (MAP SND ls0) in
     (!x y. MEM x ls /\ MEM y ls /\ f x = f y ==> x = y) /\
     (!x. f x = NONE <=> x = NONE)`;;

let PARMOVEAUX_map_state = prove
 (`!(f:A->B) a b c.
     map_state f (a,b,c) = (MAP (f ## f) a,MAP (f ## f) b,MAP (f ## f) c)`,
  REWRITE_TAC[map_state_def; LET_DEF; LET_END_DEF; PAIR_MAP_THM]);;

let PARMOVEAUX_inj_on_state = prove
 (`!(f:A option->B option) p.
     inj_on_state f p <=>
     (!x y. MEM x (APPEND (MAP FST (state_to_list p)) (MAP SND (state_to_list p))) /\
            MEM y (APPEND (MAP FST (state_to_list p)) (MAP SND (state_to_list p))) /\
            f x = f y ==> x = y) /\
     (!x. f x = NONE <=> x = NONE)`,
  REWRITE_TAC[inj_on_state_def; LET_DEF; LET_END_DEF]);;

let PARMOVEAUX_inj_on_state_mono = prove
 (`!(f:A option->B option) s1 s2.
     inj_on_state f s1
     ==> (!x. MEM x (APPEND (MAP FST (state_to_list s2)) (MAP SND (state_to_list s2)))
              ==> MEM x (APPEND (MAP FST (state_to_list s1)) (MAP SND (state_to_list s1))) \/
                  x = NONE)
     ==> inj_on_state f s2`,
  REWRITE_TAC[PARMOVEAUX_inj_on_state] THEN MESON_TAC[]);;

let step_inj_on_state = prove
 (`!(f:A option->B option)
    s1 s2:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     parmove_step s1 s2 ==> inj_on_state f s1 ==> inj_on_state f s2`,
  GEN_TAC THEN MATCH_MP_TAC parmove_step_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP PARMOVEAUX_inj_on_state_mono) THEN
  REWRITE_TAC[state_to_list_def; MAP_APPEND; MEM_APPEND; MAP; MEM; FST; SND] THEN
  MESON_TAC[]);;

let steps_inj_on_state = prove
 (`!(f:A option->B option)
    s1 s2:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     inj_on_state f s1 /\ RTC parmove_step s1 s2 ==> inj_on_state f s2`,
  GEN_TAC THEN MATCH_MP_TAC RTC_lifts_invariants THEN MESON_TAC[step_inj_on_state]);;

let step_MAP_INJ = prove
 (`!(f:A option->B option)
    s1 s2:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     parmove_step s1 s2 ==> inj_on_state f s1 ==> parmove_step (map_state f s1) (map_state f s2)`,
  let srule k = el (k - 1) (CONJUNCTS parmove_step_rules) in
  let INJ_UNFOLD_TAC =
    RULE_ASSUM_TAC(REWRITE_RULE[PARMOVEAUX_inj_on_state; state_to_list_def; FST; SND;
      MAP_APPEND; MEM_APPEND; MAP; MEM; APPEND]) in
  GEN_TAC THEN MATCH_MP_TAC parmove_step_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[PARMOVEAUX_map_state; MAP_APPEND; MAP; PAIR_MAP_THM] THEN
  REWRITE_TAC[parmove_step_rules] THENL
   [DISCH_TAC THEN SUBGOAL_THEN `(f:A option->B option) NONE = NONE` SUBST1_TAC THENL
     [INJ_UNFOLD_TAC THEN ASM_REWRITE_TAC[]; REWRITE_TAC[parmove_step_rules]];
    STRIP_TAC THEN DISCH_TAC THEN MATCH_MP_TAC (srule 5) THEN
    REWRITE_TAC[MAP_MAP_o; o_PAIR_MAP] THEN REWRITE_TAC[GSYM MAP_MAP_o] THEN
    ONCE_REWRITE_TAC[MEM_MAP] THEN INJ_UNFOLD_TAC THEN ASM_MESON_TAC[];
    REPEAT DISCH_TAC THEN MATCH_MP_TAC (srule 6) THEN
    REWRITE_TAC[MAP_MAP_o; o_PAIR_MAP] THEN REWRITE_TAC[GSYM MAP_MAP_o] THEN
    ONCE_REWRITE_TAC[MEM_MAP] THEN INJ_UNFOLD_TAC THEN ASM_MESON_TAC[]]);;

let steps_MAP_INJ = prove
 (`!(f:A option->B option)
    s1 s2:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     RTC parmove_step s1 s2
     ==> inj_on_state f s1 ==> RTC parmove_step (map_state f s1) (map_state f s2)`,
  GEN_TAC THEN MATCH_MP_TAC RTC_INDUCT_R THEN
  MESON_TAC[RTC_REFL; RTC_TRANS_R; step_MAP_INJ; step_inj_on_state]);;

let fstep_MAP_INJ = prove
 (`!(f:A option->B option)
    p:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     inj_on_state f p ==> fstep (map_state f p) = map_state f (fstep p)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`mu:(A option#A option) list`; `sigma:(A option#A option) list`;
                       `tau:(A option#A option) list`] THEN
  REWRITE_TAC[PARMOVEAUX_inj_on_state] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:A option->B option) NONE = NONE` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[state_to_list_def; FST; SND; MAP_APPEND; MEM_APPEND] THEN
  STRUCT_CASES_TAC (ISPEC `sigma:(A option#A option) list` list_CASES) THENL
   [STRUCT_CASES_TAC (ISPEC `mu:(A option#A option) list` list_CASES) THEN
    REWRITE_TAC[PARMOVEAUX_map_state; MAP; PARMOVEAUX_fstep_thm] THEN
    SPEC_TAC (`h:A option#A option`, `h:A option#A option`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM; MAP; MEM; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`d:A option`; `s:A option`] THEN
    REWRITE_TAC[PARMOVEAUX_fstep_thm] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:A option->B option) s = f d <=> s = d` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[PARMOVEAUX_map_state; MAP; PAIR_MAP_THM];
    ALL_TAC] THEN
  SPEC_TAC (`h:A option#A option`, `h:A option#A option`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; MAP; MEM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`d:A option`; `s:A option`] THEN DISCH_TAC THEN
  REWRITE_TAC[PARMOVEAUX_map_state; MAP; PAIR_MAP_THM; PARMOVEAUX_fstep_thm;
              splitAtPki_EQN; LENGTH_MAP] THEN
  SUBGOAL_THEN
   `(\i. i < LENGTH mu /\ SND (EL i (MAP ((f:A option->B option) ## f) mu)) = f d) =
    (\i. i < LENGTH mu /\ SND (EL i mu) = d)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `i < LENGTH (mu:(A option#A option) list)` THEN
    (* only the case assumption: the injectivity assumption, whose conclusion *)
    (* is an equation of variables, makes ASM_SIMP_TAC slow *)
    POP_ASSUM(fun th -> SIMP_TAC[EL_MAP; PAIR_MAP; th] THEN ASSUME_TAC th) THEN
    SUBGOAL_THEN `MEM (SND (EL i mu:A option#A option)) (MAP SND mu)` ASSUME_TAC THENL
     [REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `EL i mu:A option#A option` THEN
      ASM_SIMP_TAC[MEM_EL];
      ALL_TAC] THEN
    EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC);
    ALL_TAC] THEN
  CASES_ON `OLEAST i. i < LENGTH mu /\ SND (EL i mu:A option#A option) = d` THEN
  REWRITE_TAC[option_CASE; list_CASE] THENL
   [DISJ_CASES_THEN STRIP_ASSUME_TAC (ISPEC `t:(A option#A option) list` SNOC_CASES) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[MAP; NULL; PARMOVEAUX_map_state; PAIR_MAP_THM; MAP_SNOC; NULL_EQ_NIL;
                NOT_SNOC_NIL; LAST_SNOC; FRONT_SNOC] THEN
    X_CHOOSE_THEN `d':A option` (X_CHOOSE_THEN `s':A option` SUBST_ALL_TAC)
      (ISPEC `x:A option#A option` PAIR_SURJECTIVE) THEN
    REWRITE_TAC[PAIR_MAP_THM; pair_CASE] THEN
    SUBGOAL_THEN `(f:A option->B option) s' = f d <=> s' = d` SUBST1_TAC THENL
     [EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN
        ASM_REWRITE_TAC[SNOC_APPEND; MAP_APPEND; MEM_APPEND; MAP; MEM] THEN NO_TAC);
      COND_CASES_TAC THEN
      ASM_REWRITE_TAC[PARMOVEAUX_map_state; MAP_SNOC; MAP; PAIR_MAP_THM]];
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o BETA_RULE o MATCH_MP OLEAST_SOME_IMP) THEN
    SIMP_TAC[GSYM MAP_DROP; GSYM MAP_TAKE; DROP_CONS_EL; MAP; list_CASE;
             PARMOVEAUX_map_state; MAP_APPEND; PAIR_MAP_THM]]);;

let PARMOVEAUX_map_state_final = prove
 (`!(f:A->B) p:(A#A) list#(A#A) list#(A#A) list.
     (?tau. map_state f p = ([],[],tau)) <=> (?tau. p = ([],[],tau))`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; PARMOVEAUX_map_state; PAIR_EQ; MAP_EQ_NIL] THEN
  MESON_TAC[]);;

let pmov_MAP_INJ = prove
 (`!(f:A option->B option)
    p:(A option#A option) list#(A option#A option) list#(A option#A option) list.
     parmove_wf p /\ inj_on_state f p
     ==> pmov (map_state f p) = map_state f (pmov p)`,
  GEN_TAC THEN MATCH_MP_TAC pmov_ind THEN
  X_GEN_TAC `p:(A option#A option) list#(A option#A option) list#(A option#A option) list` THEN
  DISCH_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[PARMOVEAUX_pmov_thm] THEN
  REWRITE_TAC[PARMOVEAUX_map_state_final] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `RTC parmove_step p (fstep p:(A option#A option) list#(A option#A option) list#
                                     (A option#A option) list)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] dsteps_steps) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RTC_INC THEN MATCH_MP_TAC fstep_dstep THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[fstep_MAP_INJ] THEN
  SUBGOAL_THEN `parmove_wf (fstep p:(A option#A option) list#(A option#A option) list#
                                    (A option#A option) list) /\
                inj_on_state (f:A option->B option) (fstep p)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wf_steps; steps_inj_on_state]; ALL_TAC] THEN
  ASM_MESON_TAC[PARMOVEAUX_state_cases]);;

let parmove_MAP_INJ = prove
 (`!ls (f:A->B).
     (let ls1 = APPEND (MAP FST ls) (MAP SND ls) in
      !x y. MEM x ls1 /\ MEM y ls1 /\ f x = f y ==> x = y) /\
     windmill ls
     ==> parmove (MAP (f ## f) ls) = MAP (OPTION_MAP f ## OPTION_MAP f) (parmove ls)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
  REWRITE_TAC[parmove_def] THEN
  SUBGOAL_THEN
   `(MAP (\xy:B#B. pair_CASE xy (\x y. (SOME x,SOME y))) (MAP ((f:A->B) ## f) ls),[],[]):
      (B option#B option) list#(B option#B option) list#(B option#B option) list =
    map_state (OPTION_MAP f)
      (MAP (\xy:A#A. pair_CASE xy (\x y. (SOME x,SOME y))) ls,[],[])`
    SUBST1_TAC THENL
   [REWRITE_TAC[PARMOVEAUX_map_state; MAP; MAP_MAP_o; PAIR_EQ] THEN
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM;
      pair_CASE; PAIR_MAP_THM; OPTION_MAP_DEF];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PARMOVEAUX_wf_parmove) THEN
  MP_TAC(ISPECL [`OPTION_MAP (f:A->B)`;
                 `(MAP (\xy:A#A. pair_CASE xy (\x y. (SOME x,SOME y))) ls,[],[]):
                  (A option#A option) list#(A option#A option) list#
                  (A option#A option) list`] pmov_MAP_INJ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PARMOVEAUX_inj_on_state; state_to_list_def; FST; SND; APPEND_NIL;
                    PARMOVEAUX_MAP_SOME] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM MAP_APPEND; MEM_MAP] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[OPTION_MAP_DEF; option_INJ]) THEN
      REWRITE_TAC[option_INJ] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT]];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPEC `(MAP (\xy:A#A. pair_CASE xy (\x y. (SOME x,SOME y))) ls,[],[]):
     (A option#A option) list#(A option#A option) list#(A option#A option) list`
     pmov_final) THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:(A option#A option) list` SUBST1_TAC) THEN
  REWRITE_TAC[PARMOVEAUX_map_state; MAP; MAP_REVERSE]);;
