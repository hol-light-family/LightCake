(* ========================================================================= *)
(* pan_itreeProps: port of HOL4 pancake/semantics/pan_itreePropsScript.sml  *)
(* (CakeML v3479).  Misc lemmas for the Pancake itree semantics and the     *)
(* correspondence proof.                                                     *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's types ptree and fst are written out (HOL Light abbreviations    *)
(*   cannot have parameters): ptree is                                       *)
(*     ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,          *)
(*      (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree        *)
(*   and fst is (ffiname->B->byte list->byte list->(B)oracle_result)#B.      *)
(* - FUNPOW Tau n t is ITER n Tau t; HOL4 div is pan_itreeSem_div.           *)
(* - Local helpers that are not HOL4 theorems are PITRAUX_.                  *)
(* ========================================================================= *)

needs "hol4/llist.ml";;
needs "hol4/libext.ml";;
needs "hol4/itreeTau.ml";;
needs "pancake/semantics/pan_itreeSem.ml";;

prioritize_num();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* ltree, comp_ffi and divergence.                                           *)
(* ------------------------------------------------------------------------- *)

let ltree_FUNPOW_Tau = prove
 (`!n (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
      (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
     ltree fs (ITER n Tau t) = ITER n Tau (ltree fs t)`,
  INDUCT_TAC THEN SIMP[ITER]);;
let _ = cake_add_simps [ltree_FUNPOW_Tau];;

let ltree_not_Vis = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) n e k.
     ~(ltree fs t = ITER n Tau (Vis e k))`,
  SUBGOAL_THEN
   `!n (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
       (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
           (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) e k.
      ~(ltree fs t = ITER n Tau (Vis e k))`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN GEN_TAC THEN GEN_TAC THEN QCASES_ON "t" THEN
  TRY(RENAME1 "Vis e0 g0" THEN PAIR_CASES_ON `e0:ev`) THEN
  SIMP[ITER] THEN REPEAT(CASE_TAC THEN SIMP[ITER]) THEN SIMP[]);;
let _ = cake_add_simps [ltree_not_Vis];;

let ltree_spin = prove
 (`!fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B.
     ltree fs spin =
     (spin:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
            (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[itree_bisimulation] THEN
  QEXISTS_TAC "\\x y. x = ltree fs spin /\\ y = spin" THEN REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[spin]) THEN FS[] THEN
  REWRITE_TAC[GSYM spin]);;

let comp_ffi_FUNPOW_Tau = prove
 (`!n (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
      (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
     comp_ffi fs (ITER n Tau t) = comp_ffi fs t`,
  INDUCT_TAC THEN SIMP[ITER]);;
let _ = cake_add_simps [comp_ffi_FUNPOW_Tau];;

let PITRAUX_ltree_bind_Vis = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) e
    (g:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
       ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) k.
     ?(F:(ffiname->B->byte list->byte list->(B)oracle_result)#B) G.
       ltree fs (itree_bind (Vis e g) k) = Tau (ltree F (itree_bind G k)) /\
           itree_bind (ltree fs (Vis e g))
             (ltree (FST fs,SND (comp_ffi fs (Vis e g))) o k) =
           Tau (itree_bind (ltree F G) (ltree (FST F,SND (comp_ffi F G)) o k))`,
  REPEAT GEN_TAC THEN PAIR_CASES_ON `e:ev` THEN
  REWRITE_TAC[itree_bind_thm; ltree_simps; comp_ffi_simps] THEN
  QCASES_ON "FST (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) e0 (SND fs) e1 e2" THEN
  SIMP[] THEN TRY COND_CASES_TAC THEN SIMP[] THEN MESON_TAC[FST]);;
let ltree_bind = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) k.
     ltree fs (itree_bind t k) =
     itree_bind (ltree fs t) (ltree (FST fs,SND (comp_ffi fs t)) o k)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[itree_strong_bisimulation] THEN
  QEXISTS_TAC
   "\\x y. ?(fs':(ffiname->B->byte list->byte list->(B)oracle_result)#B) t'.
            x = ltree fs' (itree_bind t' k) /\\
            y = itree_bind (ltree fs' t') (ltree (FST fs',SND (comp_ffi fs' t')) o k)" THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `fs1:(ffiname->B->byte list->byte list->(B)oracle_result)#B`
    (X_CHOOSE_THEN `t1:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree` STRIP_ASSUME_TAC)) THEN
  (NAMED_CASES_ON "t1" ["r0"; "u0"; "e0 g0"] THENL
   [FS[o_THM; PAIR] THEN ASM_MESON_TAC[];
    FS[o_THM; PAIR] THEN ASM_MESON_TAC[];
    MP_TAC(ISPECL [`fs1:(ffiname->B->byte list->byte list->(B)oracle_result)#B`;
                   `e0:ev`;
                   `g0:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
                       ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`;
                   `k:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
                       ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`]
                  PITRAUX_ltree_bind_Vis) THEN
    STRIP_TAC THEN FS[] THEN ASM_MESON_TAC[]]));;

let _ = cake_add_simps [ltree_bind];;

let comp_ffi_bind = prove
 (`!n (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
      (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) k r.
     ltree fs t = ITER n Tau (itree_Ret r) ==>
     comp_ffi fs (itree_bind t k) = comp_ffi (FST fs,SND (comp_ffi fs t)) (k r)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN QCASES_ON "t" THEN
  TRY(RENAME1 "Vis e0 g0" THEN PAIR_CASES_ON `e0:ev`) THEN
  SIMP[ITER; PAIR] THEN REPEAT(CASE_TAC THEN SIMP[ITER]) THEN ASM_MESON_TAC[]);;
let _ = cake_add_simps [comp_ffi_bind];;

let div_FUNPOW_Tau = prove
 (`!n (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
      (X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
     pan_itreeSem_div fs (ITER n Tau X) <=> pan_itreeSem_div fs X`,
  INDUCT_TAC THEN SIMP[ITER; div_Tau]);;
let _ = cake_add_simps [div_FUNPOW_Tau];;

(* div_imp_spin comes before ltree_div_bind here (HOL4 has it after         *)
(* div_bind_cases): ltree_div_bind is then a consequence of ltree_bind      *)

let PITRAUX_ltree_Vis = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) e
    (g:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
       ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
     ?(F:(ffiname->B->byte list->byte list->(B)oracle_result)#B) G.
       ltree fs (Vis e g) = Tau (ltree F G)`,
  REPEAT GEN_TAC THEN PAIR_CASES_ON `e:ev` THEN REWRITE_TAC[ltree_simps] THEN
  QCASES_ON "FST (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) e0 (SND fs) e1 e2" THEN
  SIMP[] THEN TRY COND_CASES_TAC THEN SIMP[] THEN MESON_TAC[]);;

let PITRAUX_div_Tau_ltree = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) X
    (F:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (G:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
     ltree fs X = Tau (ltree F G)
     ==> (pan_itreeSem_div fs X <=> pan_itreeSem_div F G)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[pan_itreeSem_div_def; PITRAUX_Tau_FUNPOW_Ret] THEN
  MESON_TAC[]);;

let div_imp_spin = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
     pan_itreeSem_div fs t ==> ltree fs t = spin`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_SYM THEN
  ONCE_REWRITE_TAC[itree_bisimulation] THEN
  QEXISTS_TAC
   "\\x y. x = spin /\\
          ?(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) t.
            y = ltree fs t /\\ pan_itreeSem_div fs t" THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o ONCE_REWRITE_RULE[spin])
    (X_CHOOSE_THEN `fs1:(ffiname->B->byte list->byte list->(B)oracle_result)#B`
      (X_CHOOSE_THEN `t1:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`
        STRIP_ASSUME_TAC))) THEN
  SIMP[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  NAMED_CASES_ON "t1" ["r0"; "u0"; "e0 g0"] THEN FS[] THENL
   [ASM_MESON_TAC[];
    MP_TAC(ISPECL [`fs1:(ffiname->B->byte list->byte list->(B)oracle_result)#B`;
                   `e0:ev`;
                   `g0:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
                       ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`]
                  PITRAUX_ltree_Vis) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[itree_11] THEN
    ASM_MESON_TAC[PITRAUX_div_Tau_ltree]]);;

let ltree_div_bind = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) k.
     pan_itreeSem_div fs X ==> ltree fs (itree_bind X k) = ltree fs X`,
  SIMP[ltree_bind; div_imp_spin; spin_bind]);;
let _ = cake_add_simps [ltree_div_bind];;

let div_bind1 = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) Y.
     pan_itreeSem_div fs X ==> pan_itreeSem_div fs (itree_bind X Y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> MP_TAC th THEN
    REWRITE_TAC[pan_itreeSem_div_def; MATCH_MP ltree_div_bind th]));;
let _ = cake_add_simps [div_bind1];;

let div_bind2 = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) Y n r.
     ltree fs X = ITER n Tau (itree_Ret r) ==>
     (pan_itreeSem_div fs (itree_bind X Y) <=>
      pan_itreeSem_div (FST fs,SND (comp_ffi fs X)) (Y r))`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[pan_itreeSem_div_def; ltree_bind; FUNPOW_Tau_bind;
                  itree_bind_thm; o_THM; FUNPOW_Ret_simp] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`n + n':num`; `r':(ffi_outcome+byte list)+
                                    ((A)pan_result)option#(A)bstate`]) THEN
    ASM_REWRITE_TAC[LE_ADD; ADD_SUB2];
    ASM_MESON_TAC[]]);;
let _ = cake_add_simps [div_bind2];;

let div_bind_cases = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) k.
     pan_itreeSem_div fs (itree_bind X k) <=>
     pan_itreeSem_div fs X \/
     (?n r. ltree fs X = ITER n Tau (itree_Ret r) /\
            pan_itreeSem_div (FST fs,SND (comp_ffi fs X)) (k r))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC
   `pan_itreeSem_div (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
      (X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree)` THEN
  SIMP[div_bind1] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[nondiv_eq_Ret]) THEN
  SIMP[div_bind2] THEN ASM_MESON_TAC[FUNPOW_Tau_Ret_eq_simp]);;

let div_eq_ltree_spin = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
     pan_itreeSem_div fs t <=> ltree fs t = spin`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[div_imp_spin] THEN
  SIMP[pan_itreeSem_div_def] THEN MESON_TAC[FUNPOW_Ret_spin_F]);;

let nondiv_ltree_bind_lemma = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) k n r.
     itree_bind (ltree fs t) (ltree (FST fs,SND (comp_ffi fs t)) o k) =
     ITER n Tau (itree_Ret r)
     ==> ?n' r'. ltree fs t = ITER n' Tau (itree_Ret r') /\
                 ?n''. ltree (FST fs,SND (comp_ffi fs t)) (k r') =
                       ITER n'' Tau (itree_Ret r) /\ n' + n'' = n`,
  REWRITE_TAC[PITRAUX_bind_FUNPOW_Ret; o_THM] THEN MESON_TAC[]);;

let nondiv_ltree_bind_lemma' = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) fs' k n r.
     itree_bind (ltree fs t) (ltree fs' o k) = ITER n Tau (itree_Ret r) /\
     fs' = (FST fs,SND (comp_ffi fs t))
     ==> ?n' r'. ltree fs t = ITER n' Tau (itree_Ret r') /\
                 ?n''. ltree (FST fs,SND (comp_ffi fs t)) (k r') =
                       ITER n'' Tau (itree_Ret r) /\ n' + n'' = n`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_MESON_TAC[nondiv_ltree_bind_lemma]);;

(* ------------------------------------------------------------------------- *)
(* Results of the oracle-run semantics are INR.                              *)
(* ------------------------------------------------------------------------- *)

let PITRAUX_ltree_bind_FUNPOW_Ret = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) k n x.
     ltree fs (itree_bind t k) = ITER n Tau (itree_Ret x) <=>
     ?r n' m. ltree fs t = ITER n' Tau (itree_Ret r) /\
              ltree (FST fs,SND (comp_ffi fs t)) (k r) = ITER m Tau (itree_Ret x) /\
              n = n' + m`,
  REWRITE_TAC[ltree_bind; PITRAUX_bind_FUNPOW_Ret; o_THM]);;

(* the rules that decompose an equation  ltree fs t = ITER n Tau (Ret r)   *)

let PITRAUX_NONDIV_RULES () =
  [PITRAUX_Tau_FUNPOW_Ret; PITRAUX_ltree_bind_FUNPOW_Ret; PITRAUX_bind_FUNPOW_Ret;
   o_THM; mrec_h_handle_call_ret_lemma; mrec_h_handle_deccall_ret_lemma;
   COND_CASE_EQ] @ all_case_eqs();;

(* HOL4 proves nondiv_INR by induction on n and on the program; here by     *)
(* induction on n with the simp rules of pan_itreeSem (as                   *)
(* mrec_FUNPOW_Ret_INR there)                                               *)

let nondiv_INR = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) p (s:(A)bstate) n r.
     ltree fs (mrec h_prog (h_prog (p,s))) = ITER n Tau (itree_Ret r)
     ==> ?x. r = INR x`,
  SUBGOAL_THEN
   `!n (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) p (s:(A)bstate) r.
      ltree fs (mrec h_prog (h_prog (p,s))) = ITER n Tau (itree_Ret r)
      ==> ?x. r = INR x`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  GEN_TAC THEN GEN_TAC THEN QCASES_ON "p" THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[mrec_prog_nonrec; mrec_If; mrec_ExtCall] THEN
  TRY(GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [mrec_While]) THEN
  REPEAT(TOP_CASE_TAC THEN SIMP[]) THEN REPEAT STRIP_TAC THEN
  GVS_ASM (PITRAUX_NONDIV_RULES()) THEN
  REPEAT(FULL_CASE_TAC THEN GVS_ASM (PITRAUX_NONDIV_RULES())) THEN SIMP[] THEN
  ASM_MESON_TAC[ARITH_RULE `!a b. b <= SUC (a + b)`]);;

(* ------------------------------------------------------------------------- *)
(* Traces (trace_prefix).                                                    *)
(* ------------------------------------------------------------------------- *)

(* HOL4: move to HOL - llistTheory? *)

let lnil_def = cake_def
 `lnil:(A llist)llist = LUNFOLD (\u:1. SOME (one,LNIL:A llist)) one`;;

let lnil = prove
 (`LCONS LNIL lnil = lnil:(A llist)llist`,
  REWRITE_TAC[lnil_def] THEN
  GEN_REWRITE_TAC RAND_CONV [LUNFOLD] THEN SIMP[]);;

(* every element of a flattened unfold of a spinning tree is LNIL *)

let PITRAUX_every_lnil = prove
 (`!ll:(A llist)llist. ll = lnil ==> every ((=) LNIL) ll`,
  MATCH_MP_TAC every_coind THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM lnil] THEN
  SIMP[LCONS_11]);;

let trace_prefix_spin = prove
 (`!fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B.
     trace_prefix fs
       (spin:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
              (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) = LNIL`,
  GEN_TAC THEN REWRITE_TAC[trace_prefix_def; LFLATTEN_EQ_NIL] THEN
  MATCH_MP_TAC PITRAUX_every_lnil THEN REWRITE_TAC[lnil_def] THEN
  MATCH_GOALSUB_ABBREV_TAC "LUNFOLD ff (SND fs,spin)" THEN
  QBY "!st:B. ff (st,spin) = SOME ((st,spin),LNIL)"
    (GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [spin] THEN
     EXPAND_TAC "ff" THEN SIMP[]) THEN
  ONCE_REWRITE_TAC[LUNFOLD_BISIMULATION] THEN
  QEXISTS_TAC "\\(y1:B#((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                    (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree)
                (y2:1). SND y1 = spin" THEN
  SIMP[FORALL_PAIR_THM]);;

let trace_prefix_bind_append = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) k r.
     (?n. ltree fs t = ITER n Tau (itree_Ret r)) ==>
     trace_prefix fs (itree_bind t k) =
     LAPPEND (trace_prefix fs t) (trace_prefix (FST fs,SND (comp_ffi fs t)) (k r))`,
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  SUBGOAL_THEN
   `!n (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
       (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
           (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) k r.
      ltree fs t = ITER n Tau (itree_Ret r) ==>
      trace_prefix fs (itree_bind t k) =
      LAPPEND (trace_prefix fs t) (trace_prefix (FST fs,SND (comp_ffi fs t)) (k r))`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN QCASES_ON "t" THEN
  TRY(RENAME1 "Vis e0 g0" THEN PAIR_CASES_ON `e0:ev`) THEN
  SIMP[ITER; PAIR] THEN REPEAT(CASE_TAC THEN SIMP[ITER]) THEN
  ASM_MESON_TAC[FST; SND]);;

let trace_prefix_FUNPOW_Tau = prove
 (`!n (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
      (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
          (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
     trace_prefix fs (ITER n Tau t) = trace_prefix fs t`,
  INDUCT_TAC THEN SIMP[ITER]);;
let _ = cake_add_simps [trace_prefix_FUNPOW_Tau];;

let trace_prefix_bind_div = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) k.
     pan_itreeSem_div fs t ==> trace_prefix fs (itree_bind t k) = trace_prefix fs t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[trace_prefix_def] THEN DISCH_TAC THEN AP_TERM_TAC THEN
  MATCH_GOALSUB_ABBREV_TAC "LUNFOLD ff (SND fs,itree_bind t k)" THEN
  ONCE_REWRITE_TAC[LUNFOLD_BISIMULATION] THEN
  QEXISTS_TAC "\\y1 y2. FST y1 = FST y2 /\\ SND y1 = itree_bind (SND y2) k /\\
                      pan_itreeSem_div (FST fs,FST y2) (SND y2)" THEN
  ASM_REWRITE_TAC[PAIR] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`st1:B`; `x1:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                  (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`;
    `st2:B`; `x2:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                  (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  NAMED_CASES_ON "x2" ["r0"; "u0"; "e0 g0"] THEN TRY(PAIR_CASES_ON `e0:ev`) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN FS[] THEN REPEAT(CASE_TAC THEN RFS[]) THEN
  QPAT_X_ASSUM "pan_itreeSem_div _ (Vis _ _)" MP_TAC THEN
  REWRITE_TAC[pan_itreeSem_div_def] THEN SIMP[PITRAUX_Tau_FUNPOW_Ret] THEN
  MESON_TAC[]);;

let trace_prefix0_spin = prove
 (`!fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B.
     trace_prefix0 fs (spin:(ffi_outcome+byte list,ev,R)itree) = LNIL`,
  GEN_TAC THEN REWRITE_TAC[trace_prefix0_def; LFLATTEN_EQ_NIL] THEN
  MATCH_MP_TAC PITRAUX_every_lnil THEN REWRITE_TAC[lnil_def] THEN
  MATCH_GOALSUB_ABBREV_TAC "LUNFOLD ff (SND fs,spin)" THEN
  QBY "!st:B. ff (st,spin) = SOME ((st,spin),LNIL)"
    (GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [spin] THEN
     EXPAND_TAC "ff" THEN SIMP[]) THEN
  ONCE_REWRITE_TAC[LUNFOLD_BISIMULATION] THEN
  QEXISTS_TAC "\\(y1:B#(ffi_outcome+byte list,ev,R)itree) (y2:1). SND y1 = spin" THEN
  SIMP[FORALL_PAIR_THM]);;

let trace_prefix0_FUNPOW_Tau = prove
 (`!n (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
      (t:(ffi_outcome+byte list,ev,R)itree).
     trace_prefix0 fs (ITER n Tau t) = trace_prefix0 fs t`,
  INDUCT_TAC THEN SIMP[ITER]);;
let _ = cake_add_simps [trace_prefix0_FUNPOW_Tau];;

(* HOL4: move to itreeTauTheory *)

let itree_unfold_spin = prove
 (`!f:(A,E,R)itree->(B,C,D,(A,E,R)itree)itree_next.
     (!u. f (Tau u) = Tau' u) ==> itree_unfold f spin = spin`,
  REPEAT STRIP_TAC THEN
  QBY "itree_unfold f spin = Tau (itree_unfold f spin)"
    (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [spin] THEN
     GEN_REWRITE_TAC LAND_CONV [itree_unfold] THEN SIMP[]) THEN
  QPAT_X_ASSUM "itree_unfold f spin = _" (fun eq ->
    ONCE_REWRITE_TAC[itree_bisimulation] THEN
    QEXISTS_TAC "\\x y. x = itree_unfold f spin /\\ y = spin" THEN
    REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[eq]) THEN FS[] THEN REWRITE_TAC[GSYM spin]));;

let trace_eq_lemma = prove(CASE_TERM
 `!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (a:((A)pan_result)option#(A)bstate)
    (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
    trace_prefix0 fs
      (itree_unfold (\x. match x with
                           itree_Ret r -> Ret' (match r with INL l -> a | INR r -> r)
                         | Tau t -> Tau' t
                         | Vis e f -> Vis' e (\x. f (INL x))) t) =
    trace_prefix fs t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[trace_prefix0_def; trace_prefix_def] THEN
  AP_TERM_TAC THEN MATCH_GOALSUB_ABBREV_TAC "itree_unfold uf t" THEN
  QBY "!u. itree_unfold uf (Tau u) = Tau (itree_unfold uf u)"
    (GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [itree_unfold] THEN
     EXPAND_TAC "uf" THEN SIMP[]) THEN
  QBY "!e g. itree_unfold uf (Vis e g) = Vis e (\\x. itree_unfold uf (g (INL x)))"
    (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [itree_unfold] THEN
     EXPAND_TAC "uf" THEN SIMP[o_DEF]) THEN
  QBY "!r. ?v. itree_unfold uf (itree_Ret r) = itree_Ret v"
    (GEN_TAC THEN GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV) [itree_unfold] THEN
     EXPAND_TAC "uf" THEN SIMP[] THEN MESON_TAC[]) THEN
  ONCE_REWRITE_TAC[LUNFOLD_BISIMULATION] THEN
  QEXISTS_TAC "\\y1 y2. FST y1 = FST y2 /\\ SND y1 = itree_unfold uf (SND y2)" THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC
   [`st1:B`; `x1:(ffi_outcome+byte list,ev,((A)pan_result)option#(A)bstate)itree`;
    `st2:B`; `x2:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                  (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree`] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  NAMED_CASES_ON "x2" ["r0"; "u0"; "e0 g0"] THEN TRY(PAIR_CASES_ON `e0:ev`) THEN
  TRY(FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `r0:(ffi_outcome+byte list)+
        ((A)pan_result)option#(A)bstate`)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP[] THEN
  REPEAT(CASE_TAC THEN SIMP[]));;

(* HOL4 proves trace_prefix0_eq_trace_prefix by cases on strip_tau; the     *)
(* bisimulation of trace_eq_lemma covers all the cases at once             *)

let trace_prefix0_eq_trace_prefix = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) p (s:(A)bstate).
     trace_prefix0 fs (itree_evaluate (p,s)) =
     trace_prefix fs (mrec h_prog (h_prog (p,s)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[itree_evaluate_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[trace_eq_lemma]);;
