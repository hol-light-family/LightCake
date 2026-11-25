(* ========================================================================= *)
(* compute_syntaxProof: port of HOL4 candle/prover/compute/                   *)
(* compute_syntaxProofScript.sml (CakeML v3479).  Proofs related to term      *)
(* embeddings for the Candle compute primitive.                               *)
(*                                                                            *)
(* Notes on the rendering:                                                    *)
(* - The overloads of compute_syntax (_ADD, _CEXP_NUM, Cexp, Fun, ...) are    *)
(*   read by its parser extension (compute_overloads_on, see the header of    *)
(*   compute_syntax.ml), switched on below and off at the end of the file.    *)
(*   HOL4's term_ok is hol_term_ok, sigof thy is FST thy and tysof thy is     *)
(*   FST (FST thy) (holSyntax.ml).                                            *)
(* - HOL4 proves the many theorems that instantiate an equation of           *)
(*   bool_thy_ok, numeral_thy_ok or compute_thy_ok by proves_INST, each the   *)
(*   same four steps (qpat_x_assum, dxrule_at_then, simp); here the tactic    *)
(*   CMPSYNPAUX_INST_TAC does them.                                           *)
(* - MK_COMB_simple and the replace theorems are HOL4's (MK_COMB_simple is    *)
(*   proves_MK_COMB for empty hypotheses, with welltyped (Comb l1 l2)         *)
(*   simplified as HOL4's SIMP_RULE does).                                    *)
(* - Local helpers that are not HOL4 theorems are CMPSYNPAUX_.               *)
(* ========================================================================= *)

needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/prover/compute/compute_syntax.ml";;

prioritize_num();;
type_invention_error := true;;

compute_overloads_on ();;

(* ------------------------------------------------------------------------- *)
(* Support                                                                   *)
(* ------------------------------------------------------------------------- *)

let trans_equation_simple = prove
 (`!thy a b c.
     (thy,[]) |- a === b /\
     (thy,[]) |- b === c ==>
       (thy,[]) |- a === c`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  MP_TAC (ISPECL [`thy:thy`; `[]:hol_term list`; `[]:hol_term list`; `a:hol_term`;
                  `b:hol_term`; `b:hol_term`; `c:hol_term`] trans_equation) THEN
  ASM_REWRITE_TAC[ACONV_REFL; term_union_idem]);;

let MK_COMB_simple = prove
 (`!l1 l2 r1 r2 thy rty.
     (thy,[]) |- l1 === r1 /\
     (thy,[]) |- l2 === r2 /\
     welltyped l1 /\ welltyped l2 /\ typeof l1 = Fun (typeof l2) rty
     ==> (thy,[]) |- hol_Comb l1 l2 === hol_Comb r1 r2`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`[]:hol_term list`; `[]:hol_term list`; `l1:hol_term`; `l2:hol_term`;
                  `r1:hol_term`; `r2:hol_term`; `thy:thy`] proves_MK_COMB) THEN
  ASM_REWRITE_TAC[term_union_idem; WELLTYPED_CLAUSES] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* the facts a proved equation gives about its sides *)
let CMPSYNPAUX_proves_eq_ok = prove
 (`!thy x y.
     (thy,[]) |- x === y
     ==> theory_ok thy /\ hol_term_ok (FST thy) x /\ hol_term_ok (FST thy) y /\
         typeof y = typeof x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `theory_ok thy` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP hol_proves_theory_ok) THEN REWRITE_TAC[FST];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP proves_term_ok) THEN
  REWRITE_TAC[FST; SND; ALL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `is_std_sig (FST (thy:thy))` ASSUME_TAC THENL
   [ASM_MESON_TAC[theory_ok_def]; ALL_TAC] THEN
  UNDISCH_TAC `hol_term_ok (FST (thy:thy)) (x === y)` THEN
  ASM_SIMP_TAC[term_ok_equation]);;

(* congruence in one position of an application *)
let CMPSYNPAUX_cong_fun = prove
 (`!thy x y a.
     (thy,[]) |- x === y /\ hol_term_ok (FST thy) a /\ welltyped (hol_Comb x a)
     ==> (thy,[]) |- hol_Comb x a === hol_Comb y a`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPSYNPAUX_proves_eq_ok) THEN
  MP_TAC (ISPECL [`[]:hol_term list`; `[]:hol_term list`; `x:hol_term`; `a:hol_term`;
                  `y:hol_term`; `a:hol_term`; `thy:thy`] proves_MK_COMB) THEN
  ASM_SIMP_TAC[term_union_idem; proves_REFL]);;

let CMPSYNPAUX_cong_arg = prove
 (`!thy x y f.
     (thy,[]) |- x === y /\ hol_term_ok (FST thy) f /\ welltyped (hol_Comb f x)
     ==> (thy,[]) |- hol_Comb f x === hol_Comb f y`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPSYNPAUX_proves_eq_ok) THEN
  MP_TAC (ISPECL [`[]:hol_term list`; `[]:hol_term list`; `f:hol_term`; `x:hol_term`;
                  `f:hol_term`; `y:hol_term`; `thy:thy`] proves_MK_COMB) THEN
  ASM_SIMP_TAC[term_union_idem; proves_REFL]);;

(* welltyped and hol_term_ok of the parts of an application *)
let CMPSYNPAUX_term_ok_Comb = prove
 (`!sig s t.
   hol_term_ok sig (hol_Comb s t) <=>
     hol_term_ok sig s /\ hol_term_ok sig t /\
     ?rty. typeof s = Fun (typeof t) rty`,
  REWRITE_TAC[hol_term_ok_def; WELLTYPED_CLAUSES] THEN
  MESON_TAC[term_ok_welltyped]);;

(* an argument of an application replaced by one of the same type *)
let CMPSYNPAUX_welltyped_arg = prove
 (`!f x y. welltyped (hol_Comb f x) /\ welltyped y /\ typeof y = typeof x
           ==> welltyped (hol_Comb f y)`,
  REWRITE_TAC[WELLTYPED_CLAUSES] THEN MESON_TAC[]);;

(* the function of an application replaced by one of the same type *)
let CMPSYNPAUX_welltyped_fun = prove
 (`!f g x. welltyped (hol_Comb f x) /\ welltyped g /\ typeof g = typeof f
           ==> welltyped (hol_Comb g x)`,
  REWRITE_TAC[WELLTYPED_CLAUSES] THEN MESON_TAC[]);;

let CMPSYNPAUX_typeof_Comb_arg = prove
 (`!f x y. typeof (hol_Comb f y) = typeof (hol_Comb f x)`,
  REWRITE_TAC[typeof_def]);;

(* hol_term_ok and the type of the sides of an equation in an equation  *)
let CMPSYNPAUX_proves_Comb_ok = prove
 (`!thy f x z.
     (thy,[]) |- hol_Comb f x === z
     ==> theory_ok thy /\ hol_term_ok (FST thy) f /\ hol_term_ok (FST thy) x /\
         welltyped (hol_Comb f x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP CMPSYNPAUX_proves_eq_ok) THEN
  ASM_MESON_TAC[hol_term_ok_def]);;

let replaceL1 = prove
 (`!thy x y f r z.
     (thy,[]) |- x === y /\
     (thy,[]) |- hol_Comb (hol_Comb f x) r === z ==>
       (thy,[]) |- hol_Comb (hol_Comb f y) r === z`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPSYNPAUX_proves_Comb_ok) THEN
  MP_TAC (MATCH_MP CMPSYNPAUX_proves_eq_ok (ASSUME `(thy,[]) |- x === y`)) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC trans_equation_simple THEN
  EXISTS_TAC `hol_Comb (hol_Comb f x) r` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CMPSYNPAUX_cong_fun THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `welltyped (hol_Comb f y)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPSYNPAUX_welltyped_arg THEN EXISTS_TAC `x:hol_term` THEN
    ASM_MESON_TAC[term_ok_welltyped; WELLTYPED_CLAUSES; hol_term_ok_def];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMPSYNPAUX_cong_arg THEN ASM_MESON_TAC[sym_equation; hol_term_ok_def];
    MATCH_MP_TAC CMPSYNPAUX_welltyped_fun THEN
    EXISTS_TAC `hol_Comb f x` THEN ASM_REWRITE_TAC[CMPSYNPAUX_typeof_Comb_arg]]);;

let replaceL2 = prove
 (`!thy x y f z.
     (thy,[]) |- x === y /\
     (thy,[]) |- hol_Comb f x === z ==>
       (thy,[]) |- hol_Comb f y === z`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPSYNPAUX_proves_Comb_ok) THEN
  MP_TAC (MATCH_MP CMPSYNPAUX_proves_eq_ok (ASSUME `(thy,[]) |- x === y`)) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC trans_equation_simple THEN
  EXISTS_TAC `hol_Comb f x` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CMPSYNPAUX_cong_arg THEN
  ASM_MESON_TAC[sym_equation; CMPSYNPAUX_welltyped_arg; term_ok_welltyped]);;

let replaceL3 = prove
 (`!thy x y f s t z.
     (thy,[]) |- x === y /\
     (thy,[]) |- hol_Comb (hol_Comb (hol_Comb f x) s) t === z ==>
       (thy,[]) |- hol_Comb (hol_Comb (hol_Comb f y) s) t === z`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPSYNPAUX_proves_Comb_ok) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CMPSYNPAUX_term_ok_Comb]) THEN
  MP_TAC (MATCH_MP CMPSYNPAUX_proves_eq_ok (ASSUME `(thy,[]) |- x === y`)) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC trans_equation_simple THEN
  EXISTS_TAC `hol_Comb (hol_Comb (hol_Comb f x) s) t` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `welltyped (hol_Comb f y)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPSYNPAUX_welltyped_arg THEN EXISTS_TAC `x:hol_term` THEN
    ASM_MESON_TAC[term_ok_welltyped; WELLTYPED_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `welltyped (hol_Comb (hol_Comb f y) s)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPSYNPAUX_welltyped_fun THEN
    EXISTS_TAC `hol_Comb f x` THEN
    ASM_REWRITE_TAC[CMPSYNPAUX_typeof_Comb_arg] THEN
    ASM_MESON_TAC[term_ok_welltyped; WELLTYPED_CLAUSES];
    ALL_TAC] THEN
  MATCH_MP_TAC CMPSYNPAUX_cong_fun THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMPSYNPAUX_cong_fun THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CMPSYNPAUX_cong_arg THEN ASM_MESON_TAC[sym_equation];
    MATCH_MP_TAC CMPSYNPAUX_welltyped_fun THEN
    EXISTS_TAC `hol_Comb (hol_Comb f x) s` THEN
    ASM_REWRITE_TAC[typeof_def]]);;

let replaceL_eq1 = prove
 (`!thy x x' y r.
     (thy,[]) |- (x === x') /\
     (thy,[]) |- (x === y) === r ==>
       (thy,[]) |- (x' === y) === r`,
  REPEAT STRIP_TAC THEN
  MP_TAC (MATCH_MP CMPSYNPAUX_proves_eq_ok (ASSUME `(thy,[]) |- x === x'`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(x' === y) = hol_Comb (hol_Comb (Equal (typeof x)) x') y`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[equation_def]; ALL_TAC] THEN
  MATCH_MP_TAC replaceL1 THEN EXISTS_TAC `x:hol_term` THEN
  ASM_REWRITE_TAC[GSYM equation_def]);;

let replaceL_eq2 = prove
 (`!thy x x' y r.
     (thy,[]) |- (x === x') /\
     (thy,[]) |- (y === x) === r ==>
       (thy,[]) |- (y === x') === r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(y === x') = hol_Comb (hol_Comb (Equal (typeof y)) y) x'`
    SUBST1_TAC THENL [REWRITE_TAC[equation_def]; ALL_TAC] THEN
  MATCH_MP_TAC replaceL2 THEN EXISTS_TAC `x:hol_term` THEN
  ASM_REWRITE_TAC[GSYM equation_def]);;

let replaceR1 = GEN_ALL (DISCH_ALL (MATCH_MP sym_equation (UNDISCH (SPEC_ALL replaceL1))));;
let replaceR2 = GEN_ALL (DISCH_ALL (MATCH_MP sym_equation (UNDISCH (SPEC_ALL replaceL2))));;
let replaceR3 = GEN_ALL (DISCH_ALL (MATCH_MP sym_equation (UNDISCH (SPEC_ALL replaceL3))));;
let replaceR_eq1 =
  GEN_ALL (DISCH_ALL (MATCH_MP sym_equation (UNDISCH (SPEC_ALL replaceL_eq1))));;
let replaceR_eq2 =
  GEN_ALL (DISCH_ALL (MATCH_MP sym_equation (UNDISCH (SPEC_ALL replaceL_eq2))));;

let DEDUCT_ANTISYM_simple = prove
 (`!thy a b. (thy,[]) |- a /\ (thy,[]) |- b ==> (thy,[]) |- a === b`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`a:hol_term`; `b:hol_term`; `[]:hol_term list`; `[]:hol_term list`;
                  `thy:thy`] proves_DEDUCT_ANTISYM) THEN
  ASM_REWRITE_TAC[term_remove_nil; term_union_idem]);;

(* ------------------------------------------------------------------------- *)
(* Local tools: well-typedness by rewriting, and the instances of axioms.    *)
(* ------------------------------------------------------------------------- *)

(* existential-free forms of the typing rules of an application *)
let CMPSYNPAUX_welltyped_Comb = prove
 (`!s t. welltyped (hol_Comb s t) <=>
         welltyped s /\ welltyped t /\ typeof s = Fun (typeof t) (codomain (typeof s))`,
  REWRITE_TAC[WELLTYPED_CLAUSES] THEN MESON_TAC[codomain_def]);;

let CMPSYNPAUX_term_ok_Comb_alt = prove
 (`!sig s t. hol_term_ok sig (hol_Comb s t) <=>
             hol_term_ok sig s /\ hol_term_ok sig t /\
             typeof s = Fun (typeof t) (codomain (typeof s))`,
  REWRITE_TAC[hol_term_ok_def; CMPSYNPAUX_welltyped_Comb] THEN
  MESON_TAC[term_ok_welltyped]);;

let CMPSYNPAUX_has_type = prove
 (`!t ty. t has_type ty <=> welltyped t /\ typeof t = ty`,
  MESON_TAC[WELLTYPED; WELLTYPED_LEMMA]);;

let CMPSYNPAUX_term_ok_Abs_Var = prove
 (`!sig n ty t. hol_term_ok sig (hol_Abs (hol_Var n ty) t) <=>
                type_ok (FST sig) ty /\ hol_term_ok sig t`,
  REWRITE_TAC[hol_term_ok_def; injectivity "hol_term"] THEN MESON_TAC[]);;

let CMPSYNPAUX_has_type_welltyped = prove
 (`!t ty. t has_type ty ==> welltyped t`,
  MESON_TAC[welltyped_def]);;

let CMPSYNPAUX_welltyped_equation = prove
 (`!s t. welltyped (s === t) <=> welltyped s /\ welltyped t /\ typeof s = typeof t`,
  REWRITE_TAC[welltyped_equation; EQUATION_HAS_TYPE_BOOL]);;

let CMPSYNPAUX_welltyped_Abs_Var = prove
 (`!n ty t. welltyped (hol_Abs (hol_Var n ty) t) <=> welltyped t`,
  REWRITE_TAC[WELLTYPED_CLAUSES] THEN MESON_TAC[]);;

let CMPSYNPAUX_typeof_equation = prove
 (`!s t. typeof (s === t) = Bool`,
  REWRITE_TAC[equation_def; typeof_def; codomain_def]);;

(* decides equations between string and character literals *)
let CMPSYNPAUX_LIT_EQ_CONV tm =
  let l,_ = dest_eq tm in
  if type_of l = `:string` then STRING_EQ_CONV tm
  else if type_of l = `:char` then CHAR_EQ_CONV tm
  else failwith "CMPSYNPAUX_LIT_EQ_CONV";;

(* rules ok thy ==> hol_term_ok (FST thy) c /\ ... for the constants of the *)
(* theories; extended below as they are proved                              *)
let CMPSYNPAUX_ok_rules = ref ([]:thm list);;

(* implications between the ok predicates (numeral_thy_ok thy ==>          *)
(* bool_thy_ok thy, ...); extended below as they are proved                 *)
let CMPSYNPAUX_ok_impls = ref ([]:thm list);;

(* the assumptions and the ok facts they imply (two rounds) *)
let CMPSYNPAUX_ASM_OKS (asl:(string*thm)list) : thm list =
  let ths = map snd asl in
  let step l = l @ List.concat (map (fun r -> mapfilter (MATCH_MP r) l) !CMPSYNPAUX_ok_impls) in
  step (step ths);;

(* unconditional typing rewrites (typeof, welltyped, has_type of the       *)
(* embeddings); extended below as they are proved                          *)
let CMPSYNPAUX_wt_thms = ref ([]:thm list);;

(* HOL4's cj n th (n from 1): the n-th conjunct of the conclusion of th *)
let CMPSYNPAUX_cj (n:int) (th:thm) : thm =
  GEN_ALL (DISCH_ALL (el (n - 1) (CONJUNCTS (UNDISCH (SPEC_ALL th)))));;

(* proves goals hol_term_ok (FST thy) t, t has_type ty, welltyped t and     *)
(* typeof t = ty for terms t built from the constants of the theories and  *)
(* from variables whose types and hol_term_ok facts are assumptions         *)
let CMPSYNPAUX_WT_TAC : tactic =
  fun (asl,w as g) ->
    let ths = CMPSYNPAUX_ASM_OKS asl in
    let tys = mapfilter (MATCH_MP WELLTYPED_LEMMA) ths in
    let wts = mapfilter (MATCH_MP term_ok_welltyped) ths @
              mapfilter (MATCH_MP CMPSYNPAUX_has_type_welltyped) ths in
    let oks = List.concat (map (fun r ->
                List.concat (mapfilter (fun th -> CONJUNCTS (MATCH_MP r th)) ths))
                (!CMPSYNPAUX_ok_rules)) in
    let stds = mapfilter (fun th -> MATCH_MP term_ok_equation
                 (CONJUNCT2 (CONJUNCT2 (EQ_MP (SPEC_ALL theory_ok_def) th)))) ths in
    (REPEAT CONJ_TAC THEN
     REWRITE_TAC(oks @ stds @ ths @ !CMPSYNPAUX_wt_thms @
       [CMPSYNPAUX_term_ok_Comb_alt; CMPSYNPAUX_has_type; CMPSYNPAUX_welltyped_Comb;
        CMPSYNPAUX_welltyped_equation; CMPSYNPAUX_typeof_equation;
        CONJUNCT1 WELLTYPED_CLAUSES; CONJUNCT1 (CONJUNCT2 WELLTYPED_CLAUSES);
        CMPSYNPAUX_welltyped_Abs_Var; CMPSYNPAUX_term_ok_Abs_Var;
        CONJUNCT1 hol_term_ok_def; typeof_def; codomain_def]) THEN
     REWRITE_TAC(tys @ wts @ oks @ ths @ !CMPSYNPAUX_wt_thms @
       [injectivity "hol_type"; injectivity "mlstring"; CONS_11; NOT_CONS_NIL; NOT_NIL_CONS]) THEN
     CONV_TAC(DEPTH_CONV CMPSYNPAUX_LIT_EQ_CONV) THEN
     REWRITE_TAC[]) g;;

(* proves_INST for empty hypotheses, with the substitution given as       *)
(* (term, name, type) triples                                               *)
let CMPSYNPAUX_proves_INST = prove
 (`!thy c ilist.
     (thy,[]) |- c /\
     ALL (\(s',x,ty). s' has_type ty /\ hol_term_ok (FST thy) s') ilist
     ==> (thy,[]) |- VSUBST (MAP (\(s',x,ty). (s',hol_Var x ty)) ilist) c`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`c:hol_term`; `[]:hol_term list`;
                  `MAP (\(s',x,ty). (s',hol_Var x ty)) (ilist:(hol_term#mlstring#hol_type)list)`;
                  `thy:thy`] proves_INST) THEN
  ASM_REWRITE_TAC[term_image_nil] THEN DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `ALL (\(s',x,ty). s' has_type ty /\ hol_term_ok (FST (thy:thy)) s')
                   (ilist:(hol_term#mlstring#hol_type)list)` THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PROD; MEM_MAP; EXISTS_PROD; PAIR_EQ] THEN
  REWRITE_TAC[PAIR_EQ; LEFT_IMP_EXISTS_THM] THEN MESON_TAC[]);;

(* HOL4: rw [ok_def] \\ qpat_x_assum `ax` assume_tac                       *)
(*   \\ dxrule_at_then (Pos (el 2)) (qspec_then ilist mp_tac) proves_INST  *)
(*   \\ simp [VSUBST_def, equation_def, REV_ASSOCD_def]                     *)
(* The goal (thy,[]) |- c' is the instance by the substitution ilist (a    *)
(* string, read in the goal's context) of an equation (thy,[]) |- c of the *)
(* definition okdef of an assumption ok thy.                                *)
let CMPSYNPAUX_INST_TAC (okdef:thm) (ilists:string) : tactic =
  fun (asl,w as g) ->
    let ilist = kit_parse_typed (kit_goal_frees g) `:(hol_term#hol_term)list` ilists in
    let thyh,c' = dest_comb w in
    let thy = fst (dest_pair (rand thyh)) in
    let okc = fst (strip_comb (lhs (snd (strip_forall (concl okdef))))) in
    let okth = snd (find (fun (_,th) -> try fst (strip_comb (concl th)) = okc
                                        with Failure _ -> false) asl) in
    let axs = CONJUNCTS (EQ_MP (SPEC thy okdef) okth) in
    let pairs = map dest_pair (dest_list ilist) in
    let is_ax th = try let tm = concl th in
                       fst (strip_comb tm) = `proves` &&
                       aconv (subst pairs (rand tm)) c'
                   with Failure _ -> false in
    let ax = try find is_ax axs with Failure _ -> failwith "CMPSYNPAUX_INST_TAC: no axiom" in
    let triple (s',s) = let _,[x;ty] = strip_comb s in mk_pair(s',mk_pair(x,ty)) in
    let tl = mk_list (map triple pairs, `:hol_term#mlstring#hol_type`) in
    let side = mk_comb (mk_comb (`ALL:(hol_term#mlstring#hol_type->bool)->
                                      (hol_term#mlstring#hol_type)list->bool`,
                 vsubst [thy,`thy:thy`]
                   `\(s',x:mlstring,ty). s' has_type ty /\ hol_term_ok (FST (thy:thy)) s'`),
                 tl) in
    let typeths = mapfilter (fun (_,th) -> MATCH_MP WELLTYPED_LEMMA th) asl in
    (SUBGOAL_THEN side ASSUME_TAC THENL
      [REWRITE_TAC[ALL] THEN CMPSYNPAUX_WT_TAC;
       MP_TAC (MATCH_MP CMPSYNPAUX_proves_INST (CONJ ax (ASSUME side))) THEN
       REWRITE_TAC[MAP] THEN
       MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
       REWRITE_TAC[equation_def; VSUBST_def; REV_ASSOCD_def; typeof_def; codomain_def] THEN
       REWRITE_TAC typeths THEN
       REWRITE_TAC[injectivity "hol_term"; injectivity "hol_type"; injectivity "mlstring";
                   CONS_11] THEN
       CONV_TAC (DEPTH_CONV CMPSYNPAUX_LIT_EQ_CONV) THEN
       REWRITE_TAC[]]) g;;

(* the hol_term_ok facts of the subterms (through hol_Comb and ===) *)
let CMPSYNPAUX_comb_parts_ok = prove
 (`!sig s t. hol_term_ok sig (hol_Comb s t) ==> hol_term_ok sig s /\ hol_term_ok sig t`,
  SIMP_TAC[hol_term_ok_def]);;

let rec CMPSYNPAUX_SUBTERMS_OK (th:thm) : thm list =
  let th' = try CONV_RULE (RAND_CONV (REWR_CONV equation_def)) th with Failure _ -> th in
  th :: (try let a,b = CONJ_PAIR (MATCH_MP CMPSYNPAUX_comb_parts_ok th') in
             CMPSYNPAUX_SUBTERMS_OK a @ CMPSYNPAUX_SUBTERMS_OK b
         with Failure _ -> []);;

(* the hol_term_ok facts of the subterms of the equations of ok thy *)
let CMPSYNPAUX_AXIOMS_OK (okdef:thm) (okth:thm) : thm list =
  let thy = rand (concl okth) in
  let axs = filter (fun th -> try fst (strip_comb (concl th)) = `proves`
                              with Failure _ -> false)
                   (CONJUNCTS (EQ_MP (SPEC thy okdef) okth)) in
  List.concat (map (fun ax ->
    let _,th2 = CONJ_PAIR (MATCH_MP CMPSYNPAUX_proves_eq_ok ax) in
    let tl,th3 = CONJ_PAIR th2 in
    let tr,_ = CONJ_PAIR th3 in
    CMPSYNPAUX_SUBTERMS_OK tl @ CMPSYNPAUX_SUBTERMS_OK tr) axs);;

(* ------------------------------------------------------------------------- *)
(* Booleans                                                                  *)
(* ------------------------------------------------------------------------- *)

(* the equations of COND *)
let bool_thy_ok_def = cake_def
  `bool_thy_ok thy <=>
     theory_ok thy /\
     (thy,[]) |- _COND _TRUE _M _N === _M /\
     (thy,[]) |- _COND _FALSE _M _N === _N /\
     (thy,[]) |- _IF _TRUE _X _Y === _X /\
     (thy,[]) |- _IF _FALSE _X _Y === _Y`;;

let bool_thy_ok_terms_ok = prove
 (`!thy. bool_thy_ok thy ==>
     hol_term_ok (FST thy) _TRUE /\
     hol_term_ok (FST thy) _FALSE /\
     hol_term_ok (FST thy) _COND_TM /\
     hol_term_ok (FST thy) _IF_TM`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC (CMPSYNPAUX_AXIOMS_OK bool_thy_ok_def (ASSUME `bool_thy_ok thy`)));;

let bool_thy_ok_theory_ok = prove
 (`!thy. bool_thy_ok thy ==> theory_ok thy`,
  SIMP_TAC[bool_thy_ok_def]);;
let _ = cake_add_simps [bool_thy_ok_theory_ok];;

CMPSYNPAUX_ok_rules := [bool_thy_ok_terms_ok];;

(* ------------------------------------------------------------------------- *)
(* Natural numbers                                                           *)
(* ------------------------------------------------------------------------- *)

(* All the necessary constants defined with the right types and with the  *)
(* right defining equations (and some lemmas): NUMERAL; BIT0, BIT1; ADD;    *)
(* SUB; MUL; DIV, MOD; LESS; EQ.                                            *)
let numeral_thy_ok_def = cake_def
  `numeral_thy_ok thy <=>
     bool_thy_ok thy /\
     (thy,[]) |- _NUMERAL _N === _N /\
     (thy,[]) |- _BIT0 _N === _ADD _N _N /\
     (thy,[]) |- _BIT1 _N === _SUC (_ADD _N _N) /\
     (thy,[]) |- _ADD (_NUMERAL _0) _N === _N /\
     (thy,[]) |- _ADD (_SUC _M) _N === _SUC (_ADD _M _N) /\
     (thy,[]) |- _SUB (_NUMERAL _0) _N === _NUMERAL _0 /\
     (thy,[]) |- _SUB _M (_NUMERAL _0) === _M /\
     (thy,[]) |- _SUB (_SUC _M) (_SUC _N) === _SUB _M _N /\
     (thy,[]) |- _MUL (_NUMERAL _0) _N === _NUMERAL _0 /\
     (thy,[]) |- _MUL (_SUC _M) _N === _ADD _N (_MUL _M _N) /\
     (thy,[]) |- _DIV _M _N ===
                 _COND (_N === _NUMERAL _0) (_NUMERAL _0)
                       (_COND (_LESS _M _N) (_NUMERAL _0)
                              (_SUC (_DIV (_SUB _M _N) _N))) /\
     (thy,[]) |- _MOD _M _N ===
                 _COND (_N === _NUMERAL _0) _M
                       (_COND (_LESS _M _N) _M
                              (_MOD (_SUB _M _N) _N)) /\
     (thy,[]) |- _LESS _M (_NUMERAL _0) === _FALSE /\
     (thy,[]) |- _LESS (_NUMERAL _0) (_SUC _N) === _TRUE /\
     (thy,[]) |- _LESS (_SUC _M) (_SUC _N) === _LESS _M _N /\
     (thy,[]) |- (_NUMERAL _0 === _NUMERAL _0) === _TRUE /\
     (thy,[]) |- (_NUMERAL _0 === _SUC _N) === _FALSE /\
     (thy,[]) |- (_SUC _M === _NUMERAL _0) === _FALSE /\
     (thy,[]) |- (_SUC _M === _SUC _N) === (_M === _N)`;;

let numeral_thy_ok_theory_ok = prove
 (`!thy. numeral_thy_ok thy ==> theory_ok thy`,
  SIMP_TAC[numeral_thy_ok_def; bool_thy_ok_def]);;
let _ = cake_add_simps [numeral_thy_ok_theory_ok];;

let numeral_thy_ok_bool_thy_ok = prove
 (`!thy. numeral_thy_ok thy ==> bool_thy_ok thy`,
  SIMP_TAC[numeral_thy_ok_def]);;
let _ = cake_add_simps [numeral_thy_ok_bool_thy_ok];;

let numeral_thy_ok_terms_ok = prove
 (`!thy. numeral_thy_ok thy ==>
     hol_term_ok (FST thy) _TRUE /\
     hol_term_ok (FST thy) _FALSE /\
     hol_term_ok (FST thy) _COND_TM /\
     hol_term_ok (FST thy) _IF_TM /\
     hol_term_ok (FST thy) _ADD_TM /\
     hol_term_ok (FST thy) _SUB_TM /\
     hol_term_ok (FST thy) _MUL_TM /\
     hol_term_ok (FST thy) _DIV_TM /\
     hol_term_ok (FST thy) _MOD_TM /\
     hol_term_ok (FST thy) _LESS_TM /\
     hol_term_ok (FST thy) _0 /\
     hol_term_ok (FST thy) _SUC_TM /\
     hol_term_ok (FST thy) _BIT0_TM /\
     hol_term_ok (FST thy) _BIT1_TM /\
     hol_term_ok (FST thy) _NUMERAL_TM`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (MATCH_MP bool_thy_ok_terms_ok
           (MATCH_MP numeral_thy_ok_bool_thy_ok (ASSUME `numeral_thy_ok thy`))) THEN
  SIMP_TAC (CMPSYNPAUX_AXIOMS_OK numeral_thy_ok_def (ASSUME `numeral_thy_ok thy`)));;

CMPSYNPAUX_ok_rules := [bool_thy_ok_terms_ok; numeral_thy_ok_terms_ok];;
CMPSYNPAUX_ok_impls := [bool_thy_ok_theory_ok; numeral_thy_ok_theory_ok;
                        numeral_thy_ok_bool_thy_ok];;

(* HOL4's irule th followed by simp of the side conditions *)
let CMPSYNPAUX_EQN_TAC (th:thm) : tactic =
  MATCH_MP_TAC th THEN CMPSYNPAUX_WT_TAC;;

let term_ok_NUMERAL = prove
 (`!thy N. numeral_thy_ok thy ==>
     (hol_term_ok (FST thy) (_NUMERAL N) <=>
      hol_term_ok (FST thy) N /\ N has_type Num)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_WT_TAC THEN MESON_TAC[term_ok_welltyped]);;
let _ = cake_add_simps [term_ok_NUMERAL];;

let NUMERAL_has_type = prove
 (`!N. _NUMERAL N has_type Num <=> N has_type Num`,
  GEN_TAC THEN CMPSYNPAUX_WT_TAC THEN MESON_TAC[]);;
let _ = cake_add_simps [NUMERAL_has_type];;

let has_type_0 = prove
 (`_0 has_type Num`,
  REWRITE_TAC[has_type_rules]);;
let _ = cake_add_simps [has_type_0];;

let term_ok_SUC = prove
 (`!thy N. numeral_thy_ok thy ==>
     (hol_term_ok (FST thy) (_SUC N) <=>
      hol_term_ok (FST thy) N /\ N has_type Num)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_WT_TAC THEN MESON_TAC[term_ok_welltyped]);;
let _ = cake_add_simps [term_ok_SUC];;

let SUC_has_type = prove
 (`!N. _SUC N has_type Num <=> N has_type Num`,
  GEN_TAC THEN CMPSYNPAUX_WT_TAC THEN MESON_TAC[]);;
let _ = cake_add_simps [SUC_has_type];;

(* The numeral_thy_ok theorems with object variables replaced with meta   *)
(* variables.                                                              *)

let NUMERAL_eqn = prove
 (`!thy n. numeral_thy_ok thy /\
           hol_term_ok (FST thy) n /\ n has_type Num ==>
             (thy,[]) |- _NUMERAL n === n`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC numeral_thy_ok_def "[n,_N]");;

let BIT0_eqn = prove
 (`!thy n. numeral_thy_ok thy /\
           hol_term_ok (FST thy) n /\ n has_type Num ==>
             (thy,[]) |- _BIT0 n === _ADD n n`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC numeral_thy_ok_def "[n,_N]");;

let BIT1_eqn = prove
 (`!thy n. numeral_thy_ok thy /\
           hol_term_ok (FST thy) n /\ n has_type Num ==>
             (thy,[]) |- _BIT1 n === _SUC (_ADD n n)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC numeral_thy_ok_def "[n,_N]");;

let ADD_eqn = prove
 (`!thy m n.
     numeral_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) n /\
     m has_type Num /\ n has_type Num ==>
       (thy,[]) |- _ADD (_NUMERAL _0) n === n /\
       (thy,[]) |- _ADD (_SUC m) n === _SUC (_ADD m n)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC numeral_thy_ok_def "[m,_M; n,_N]");;

let SUB_eqn = prove
 (`!thy m n.
     numeral_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) n /\
     m has_type Num /\ n has_type Num ==>
       (thy,[]) |- _SUB (_NUMERAL _0) n === _NUMERAL _0 /\
       (thy,[]) |- _SUB m (_NUMERAL _0) === m /\
       (thy,[]) |- _SUB (_SUC m) (_SUC n) === _SUB m n`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC numeral_thy_ok_def "[m,_M; n,_N]");;

let MUL_eqn = prove
 (`!thy m n.
     numeral_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) n /\
     m has_type Num /\ n has_type Num ==>
       (thy,[]) |- _MUL (_NUMERAL _0) n === _NUMERAL _0 /\
       (thy,[]) |- _MUL (_SUC m) n === _ADD n (_MUL m n)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC numeral_thy_ok_def "[m,_M; n,_N]");;

let LESS_eqn = prove
 (`!thy m n.
     numeral_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) n /\
     m has_type Num /\ n has_type Num ==>
       (thy,[]) |- _LESS m (_NUMERAL _0) === _FALSE /\
       (thy,[]) |- _LESS (_NUMERAL _0) (_SUC n) === _TRUE /\
       (thy,[]) |- _LESS (_SUC m) (_SUC n) === _LESS m n`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC numeral_thy_ok_def "[m,_M; n,_N]");;

let EQ_eqn1 = prove
 (`!thy. numeral_thy_ok thy ==>
     (thy,[]) |- (_NUMERAL _0 === _NUMERAL _0) === _TRUE`,
  SIMP_TAC[numeral_thy_ok_def]);;

let EQ_eqn2 = prove
 (`!thy n.
     numeral_thy_ok thy /\
     hol_term_ok (FST thy) n /\ n has_type Num ==>
       (thy,[]) |- (_NUMERAL _0 === _SUC n) === _FALSE`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC numeral_thy_ok_def "[n,_N]");;

let EQ_eqn3 = prove
 (`!thy m.
     numeral_thy_ok thy /\
     hol_term_ok (FST thy) m /\ m has_type Num ==>
       (thy,[]) |- (_SUC m === _NUMERAL _0) === _FALSE`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC numeral_thy_ok_def "[m,_M]");;

let EQ_eqn4 = prove
 (`!thy m n.
     numeral_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) n /\
     m has_type Num /\ n has_type Num ==>
       (thy,[]) |- (_SUC m === _SUC n) === (m === n)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC numeral_thy_ok_def "[m,_M; n,_N]");;

let COND_eqn = prove
 (`!thy m n.
     bool_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) n /\
     m has_type Num /\ n has_type Num ==>
       (thy,[]) |- _COND _TRUE m n === m /\
       (thy,[]) |- _COND _FALSE m n === n`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC bool_thy_ok_def "[m,_M; n,_N]");;

let IF_eqn = prove
 (`!thy x y.
     bool_thy_ok thy /\
     hol_term_ok (FST thy) x /\ hol_term_ok (FST thy) y /\
     x has_type Bool /\ y has_type Bool ==>
       (thy,[]) |- _IF _TRUE x y === x /\
       (thy,[]) |- _IF _FALSE x y === y`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC bool_thy_ok_def "[x,_X; y,_Y]");;

let DIV_eqn = prove
 (`!thy m n.
     numeral_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) n /\
     m has_type Num /\ n has_type Num ==>
       (thy,[]) |- _DIV m n ===
                   _COND (n === _NUMERAL _0) (_NUMERAL _0)
                         (_COND (_LESS m n) (_NUMERAL _0)
                                (_SUC (_DIV (_SUB m n) n)))`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC numeral_thy_ok_def "[n,_N; m,_M]");;

let MOD_eqn = prove
 (`!thy m n.
     numeral_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) n /\
     m has_type Num /\ n has_type Num ==>
       (thy,[]) |- _MOD m n ===
                   _COND (n === _NUMERAL _0) m
                         (_COND (_LESS m n) m
                                (_MOD (_SUB m n) n))`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC numeral_thy_ok_def "[n,_N; m,_M]");;

let COND_has_type = prove
 (`!p m n. _COND p m n has_type Num <=>
           p has_type Bool /\ m has_type Num /\ n has_type Num`,
  REPEAT GEN_TAC THEN CMPSYNPAUX_WT_TAC THEN MESON_TAC[]);;
let _ = cake_add_simps [COND_has_type];;

let LESS_has_type = prove
 (`!m n. _LESS m n has_type Bool <=> m has_type Num /\ n has_type Num`,
  REPEAT GEN_TAC THEN CMPSYNPAUX_WT_TAC THEN MESON_TAC[]);;
let _ = cake_add_simps [LESS_has_type];;

let SUB_has_type = prove
 (`!m n. _SUB m n has_type Num <=> m has_type Num /\ n has_type Num`,
  REPEAT GEN_TAC THEN CMPSYNPAUX_WT_TAC THEN MESON_TAC[]);;
let _ = cake_add_simps [SUB_has_type];;

let MOD_has_type = prove
 (`!m n. _MOD m n has_type Num <=> m has_type Num /\ n has_type Num`,
  REPEAT GEN_TAC THEN CMPSYNPAUX_WT_TAC THEN MESON_TAC[]);;
let _ = cake_add_simps [MOD_has_type];;

let DIV_has_type = prove
 (`!m n. _DIV m n has_type Num <=> m has_type Num /\ n has_type Num`,
  REPEAT GEN_TAC THEN CMPSYNPAUX_WT_TAC THEN MESON_TAC[]);;
let _ = cake_add_simps [DIV_has_type];;

let MOD_eqn1 = prove
 (`!thy m.
     numeral_thy_ok thy /\
     hol_term_ok (FST thy) m /\ m has_type Num ==>
       (thy,[]) |- _MOD m (_NUMERAL _0) === m`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC trans_equation_simple THEN
  EXISTS_TAC `_COND (_NUMERAL _0 === _NUMERAL _0) m
                (_COND (_LESS m (_NUMERAL _0)) m
                       (_MOD (_SUB m (_NUMERAL _0)) (_NUMERAL _0)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOD_eqn THEN ASM_REWRITE_TAC[] THEN CMPSYNPAUX_WT_TAC;
    MATCH_MP_TAC replaceL3 THEN EXISTS_TAC `(_TRUE)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC sym_equation THEN ASM_SIMP_TAC[EQ_eqn1];
      MATCH_MP_TAC (CMPSYNPAUX_cj 1 COND_eqn) THEN
      ASM_SIMP_TAC[numeral_thy_ok_bool_thy_ok] THEN CMPSYNPAUX_WT_TAC]]);;

let DIV_eqn1 = prove
 (`!thy m.
     numeral_thy_ok thy /\
     hol_term_ok (FST thy) m /\ m has_type Num ==>
       (thy,[]) |- _DIV m (_NUMERAL _0) === _NUMERAL _0`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC trans_equation_simple THEN
  EXISTS_TAC `_COND (_NUMERAL _0 === _NUMERAL _0) (_NUMERAL _0)
                (_COND (_LESS m (_NUMERAL _0)) (_NUMERAL _0)
                       (_SUC (_DIV (_SUB m (_NUMERAL _0)) (_NUMERAL _0))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DIV_eqn THEN ASM_REWRITE_TAC[] THEN CMPSYNPAUX_WT_TAC;
    MATCH_MP_TAC replaceL3 THEN EXISTS_TAC `(_TRUE)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC sym_equation THEN ASM_SIMP_TAC[EQ_eqn1];
      MATCH_MP_TAC (CMPSYNPAUX_cj 1 COND_eqn) THEN
      ASM_SIMP_TAC[numeral_thy_ok_bool_thy_ok] THEN CMPSYNPAUX_WT_TAC]]);;

let compute_BIT0_0 = prove
 (`!thy. numeral_thy_ok thy ==>
     (thy,[]) |- _BIT0 _0 === _0`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC trans_equation_simple THEN EXISTS_TAC `_ADD _0 _0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC BIT0_eqn THEN ASM_REWRITE_TAC[] THEN CMPSYNPAUX_WT_TAC;
    MATCH_MP_TAC replaceL1 THEN EXISTS_TAC `_NUMERAL _0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC NUMERAL_eqn THEN ASM_REWRITE_TAC[] THEN CMPSYNPAUX_WT_TAC;
      MATCH_MP_TAC (CMPSYNPAUX_cj 1 ADD_eqn) THEN EXISTS_TAC `(_0)` THEN
      ASM_REWRITE_TAC[] THEN CMPSYNPAUX_WT_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* num2term, num2bit                                                         *)
(* ------------------------------------------------------------------------- *)

let num2term_typeof = prove
 (`!n. typeof (num2term n) = Num`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[num2term_def; typeof_def; codomain_def]);;
let _ = cake_add_simps [num2term_typeof];;

let num2term_has_type = prove
 (`!n. num2term n has_type Num`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[num2term_def; has_type_rules] THEN
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 has_type_rules))) THEN
  EXISTS_TAC `(Num)` THEN ASM_REWRITE_TAC[has_type_rules]);;
let _ = cake_add_simps [num2term_has_type];;

let num2term_welltyped = prove
 (`!n. welltyped (num2term n)`,
  MESON_TAC[welltyped_def; num2term_has_type]);;
let _ = cake_add_simps [num2term_welltyped];;

CMPSYNPAUX_wt_thms := [num2term_typeof; num2term_welltyped; num2term_has_type];;

let num2term_term_ok = prove
 (`!thy n. numeral_thy_ok thy ==> hol_term_ok (FST thy) (num2term n)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[num2term_def] THEN CMPSYNPAUX_WT_TAC);;

let num2term_VSUBST = prove
 (`!ilist n. VSUBST ilist (num2term n) = num2term n`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[num2term_def; VSUBST_def]);;
let _ = cake_add_simps [num2term_VSUBST];;

let num2bit_typeof = prove
 (`!n. typeof (num2bit n) = Num`,
  MATCH_MP_TAC num2bit_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[num2bit_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[typeof_def; codomain_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[typeof_def; codomain_def]);;
let _ = cake_add_simps [num2bit_typeof];;

let num2bit_has_type = prove
 (`!n. num2bit n has_type Num`,
  MATCH_MP_TAC num2bit_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[num2bit_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[has_type_rules] THEN
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 has_type_rules))) THEN
  EXISTS_TAC `(Num)` THEN ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN
  REWRITE_TAC[has_type_rules]);;
let _ = cake_add_simps [num2bit_has_type];;

let num2bit_welltyped = prove
 (`!n. welltyped (num2bit n)`,
  MESON_TAC[welltyped_def; num2bit_has_type]);;
let _ = cake_add_simps [num2bit_welltyped];;

CMPSYNPAUX_wt_thms := !CMPSYNPAUX_wt_thms @
                      [num2bit_typeof; num2bit_welltyped; num2bit_has_type];;

let num2bit_term_ok = prove
 (`!thy n. numeral_thy_ok thy ==> hol_term_ok (FST thy) (num2bit n)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC num2bit_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[num2bit_def] THEN COND_CASES_TAC THENL
   [CMPSYNPAUX_WT_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN COND_CASES_TAC THEN CMPSYNPAUX_WT_TAC);;

let num2bit_VSUBST = prove
 (`!ilist n. VSUBST ilist (num2bit n) = num2bit n`,
  GEN_TAC THEN MATCH_MP_TAC num2bit_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[num2bit_def] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[VSUBST_def] THEN COND_CASES_TAC THEN REWRITE_TAC[VSUBST_def]);;
let _ = cake_add_simps [num2bit_VSUBST];;

CMPSYNPAUX_ok_rules := [bool_thy_ok_terms_ok; numeral_thy_ok_terms_ok;
                        num2term_term_ok; num2bit_term_ok];;

let num2term_ADD = prove
 (`!thy m n. numeral_thy_ok thy ==>
     (thy,[]) |- num2term (m + n) === _ADD (num2term m) (num2term n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC sym_equation THEN
  SPEC_TAC(`m:num`,`m:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; num2term_def] THENL
   [MATCH_MP_TAC replaceL1 THEN EXISTS_TAC `_NUMERAL _0` THEN CONJ_TAC THENL
     [CMPSYNPAUX_EQN_TAC NUMERAL_eqn;
      MATCH_MP_TAC (CMPSYNPAUX_cj 1 ADD_eqn) THEN EXISTS_TAC `(_0)` THEN
      CMPSYNPAUX_WT_TAC];
    MATCH_MP_TAC replaceR2 THEN EXISTS_TAC `_ADD (num2term m) (num2term n)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC sym_equation THEN
    CMPSYNPAUX_EQN_TAC (CMPSYNPAUX_cj 2 ADD_eqn)]);;

let ADD_num2term = GEN_ALL (DISCH_ALL (MATCH_MP sym_equation (UNDISCH (SPEC_ALL num2term_ADD))));;

let num2term_SUB = prove
 (`!thy m n. numeral_thy_ok thy ==>
     (thy,[]) |- num2term (m - n) === _SUB (num2term m) (num2term n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC sym_equation THEN
  SPEC_TAC(`n:num`,`n:num`) THEN SPEC_TAC(`m:num`,`m:num`) THEN
  INDUCT_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[SUB_0; num2term_def] THEN
    MATCH_MP_TAC replaceL1 THEN EXISTS_TAC `_NUMERAL _0` THEN CONJ_TAC THENL
     [CMPSYNPAUX_EQN_TAC NUMERAL_eqn; ALL_TAC] THEN
    MATCH_MP_TAC trans_equation_simple THEN EXISTS_TAC `_NUMERAL _0` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC (CMPSYNPAUX_cj 1 SUB_eqn) THEN EXISTS_TAC `(_0)` THEN
      CMPSYNPAUX_WT_TAC;
      CMPSYNPAUX_EQN_TAC NUMERAL_eqn];
    INDUCT_TAC THEN REWRITE_TAC[SUB_0; SUB_SUC; num2term_def] THENL
     [MATCH_MP_TAC replaceL2 THEN EXISTS_TAC `_NUMERAL _0` THEN CONJ_TAC THENL
       [CMPSYNPAUX_EQN_TAC NUMERAL_eqn;
        MATCH_MP_TAC (CMPSYNPAUX_cj 2 SUB_eqn) THEN EXISTS_TAC `(_0)` THEN
        CMPSYNPAUX_WT_TAC];
      MATCH_MP_TAC trans_equation_simple THEN
      EXISTS_TAC `_SUB (num2term m) (num2term n)` THEN
      ASM_REWRITE_TAC[] THEN CMPSYNPAUX_EQN_TAC (CMPSYNPAUX_cj 3 SUB_eqn)]]);;

let SUB_num2term = GEN_ALL (DISCH_ALL (MATCH_MP sym_equation (UNDISCH (SPEC_ALL num2term_SUB))));;

let num2term_MUL = prove
 (`!thy m n. numeral_thy_ok thy ==>
     (thy,[]) |- num2term (m * n) === _MUL (num2term m) (num2term n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC sym_equation THEN
  SPEC_TAC(`m:num`,`m:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; num2term_def] THEN
    MATCH_MP_TAC replaceL1 THEN EXISTS_TAC `_NUMERAL _0` THEN CONJ_TAC THENL
     [CMPSYNPAUX_EQN_TAC NUMERAL_eqn; ALL_TAC] THEN
    MATCH_MP_TAC trans_equation_simple THEN EXISTS_TAC `_NUMERAL _0` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC (CMPSYNPAUX_cj 1 MUL_eqn) THEN EXISTS_TAC `(_0)` THEN
      CMPSYNPAUX_WT_TAC;
      CMPSYNPAUX_EQN_TAC NUMERAL_eqn];
    REWRITE_TAC[num2term_def; ARITH_RULE `SUC m * n = n + m * n`] THEN
    MATCH_MP_TAC trans_equation_simple THEN
    EXISTS_TAC `_ADD (num2term n) (num2term (m * n))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC replaceR2 THEN EXISTS_TAC `_MUL (num2term m) (num2term n)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC sym_equation THEN
      CMPSYNPAUX_EQN_TAC (CMPSYNPAUX_cj 2 MUL_eqn);
      CMPSYNPAUX_EQN_TAC ADD_num2term]]);;

let MUL_num2term = GEN_ALL (DISCH_ALL (MATCH_MP sym_equation (UNDISCH (SPEC_ALL num2term_MUL))));;

let bool2term_LESS_num2term = prove
 (`!thy m n. numeral_thy_ok thy ==>
     (thy,[]) |- bool2term (m < n) === _LESS (num2term m) (num2term n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC sym_equation THEN
  SPEC_TAC(`n:num`,`n:num`) THEN SPEC_TAC(`m:num`,`m:num`) THEN
  INDUCT_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[num2term_def; LT_REFL; LT_0; LT; LT_SUC; NOT_SUC; bool2term_def] THENL
   [MATCH_MP_TAC replaceL2 THEN EXISTS_TAC `_NUMERAL _0` THEN CONJ_TAC THENL
     [CMPSYNPAUX_EQN_TAC NUMERAL_eqn; CMPSYNPAUX_EQN_TAC (CMPSYNPAUX_cj 1 LESS_eqn)] THEN
    EXISTS_TAC `(_0)` THEN CMPSYNPAUX_WT_TAC;
    MATCH_MP_TAC replaceL1 THEN EXISTS_TAC `_NUMERAL _0` THEN CONJ_TAC THENL
     [CMPSYNPAUX_EQN_TAC NUMERAL_eqn; MATCH_MP_TAC (CMPSYNPAUX_cj 2 LESS_eqn)] THEN
    EXISTS_TAC `(_0)` THEN CMPSYNPAUX_WT_TAC;
    MATCH_MP_TAC replaceL2 THEN EXISTS_TAC `_NUMERAL _0` THEN CONJ_TAC THENL
     [CMPSYNPAUX_EQN_TAC NUMERAL_eqn; ALL_TAC] THEN
    MATCH_MP_TAC (CMPSYNPAUX_cj 1 LESS_eqn) THEN EXISTS_TAC `(_0)` THEN
    CMPSYNPAUX_WT_TAC;
    MATCH_MP_TAC trans_equation_simple THEN
    EXISTS_TAC `_LESS (num2term m) (num2term n)` THEN
    ASM_REWRITE_TAC[] THEN CMPSYNPAUX_EQN_TAC (CMPSYNPAUX_cj 3 LESS_eqn)]);;

let LESS_bool2term_num2term =
  GEN_ALL (DISCH_ALL (MATCH_MP sym_equation (UNDISCH (SPEC_ALL bool2term_LESS_num2term))));;

let bool2term_EQ_num2term = prove
 (`!thy m n. numeral_thy_ok thy ==>
     (thy,[]) |- bool2term (m = n) === (num2term m === num2term n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC sym_equation THEN
  SPEC_TAC(`n:num`,`n:num`) THEN SPEC_TAC(`m:num`,`m:num`) THEN
  INDUCT_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[num2term_def; NOT_SUC; GSYM NOT_SUC; SUC_INJ; bool2term_def] THENL
   [MATCH_MP_TAC replaceL_eq1 THEN EXISTS_TAC `_NUMERAL _0` THEN CONJ_TAC THENL
     [CMPSYNPAUX_EQN_TAC NUMERAL_eqn; ALL_TAC] THEN
    MATCH_MP_TAC replaceL_eq2 THEN EXISTS_TAC `_NUMERAL _0` THEN CONJ_TAC THENL
     [CMPSYNPAUX_EQN_TAC NUMERAL_eqn; CMPSYNPAUX_EQN_TAC EQ_eqn1];
    MATCH_MP_TAC replaceL_eq1 THEN EXISTS_TAC `_NUMERAL _0` THEN CONJ_TAC THENL
     [CMPSYNPAUX_EQN_TAC NUMERAL_eqn; CMPSYNPAUX_EQN_TAC EQ_eqn2];
    MATCH_MP_TAC replaceL_eq2 THEN EXISTS_TAC `_NUMERAL _0` THEN CONJ_TAC THENL
     [CMPSYNPAUX_EQN_TAC NUMERAL_eqn; CMPSYNPAUX_EQN_TAC EQ_eqn3];
    MATCH_MP_TAC trans_equation_simple THEN
    EXISTS_TAC `num2term m === num2term n` THEN
    ASM_REWRITE_TAC[] THEN CMPSYNPAUX_EQN_TAC EQ_eqn4]);;

let EQ_bool2term_num2term =
  GEN_ALL (DISCH_ALL (MATCH_MP sym_equation (UNDISCH (SPEC_ALL bool2term_EQ_num2term))));;

let SUB_DIV = prove
 (`!m n. 0 < n /\ n <= m ==> SUC ((m - n) DIV n) = m DIV n`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `(m - n) MOD n` THEN
  MP_TAC (SPECL [`m - n:num`; `n:num`] DIVISION) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC);;

(* the two COND steps of the DIV and MOD proofs *)
let CMPSYNPAUX_COND_T = prove
 (`!thy c a b.
     bool_thy_ok thy /\ (thy,[]) |- c === _TRUE /\
     hol_term_ok (FST thy) a /\ hol_term_ok (FST thy) b /\
     a has_type Num /\ b has_type Num ==>
       (thy,[]) |- _COND c a b === a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC replaceL3 THEN EXISTS_TAC `(_TRUE)` THEN
  ASM_SIMP_TAC[sym_equation] THEN CMPSYNPAUX_EQN_TAC (CMPSYNPAUX_cj 1 COND_eqn));;

let CMPSYNPAUX_COND_F = prove
 (`!thy c a b.
     bool_thy_ok thy /\ (thy,[]) |- c === _FALSE /\
     hol_term_ok (FST thy) a /\ hol_term_ok (FST thy) b /\
     a has_type Num /\ b has_type Num ==>
       (thy,[]) |- _COND c a b === b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC replaceL3 THEN EXISTS_TAC `(_FALSE)` THEN
  ASM_SIMP_TAC[sym_equation] THEN CMPSYNPAUX_EQN_TAC (CMPSYNPAUX_cj 2 COND_eqn));;

(* side conditions: the hol_term_ok and typing conjuncts *)
let CMPSYNPAUX_SIDE_TAC : tactic =
  REPEAT CONJ_TAC THEN TRY (CMPSYNPAUX_WT_TAC THEN NO_TAC);;

(* HOL4's irule trans_equation_simple \\ irule_at Any th: the goal a === c *)
(* becomes b === c, where th proves a === b                                 *)
let CMPSYNPAUX_TRANS_TAC (th:thm) : tactic =
  MATCH_MP_TAC trans_equation_simple THEN IRULE_AT (Pos hd) th THEN
  CMPSYNPAUX_SIDE_TAC;;

let CMPSYNPAUX_0_EQ_NUMERAL_0 = prove
 (`!thy. numeral_thy_ok thy ==> (thy,[]) |- (_0 === _NUMERAL _0) === _TRUE`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC replaceL_eq1 THEN
  EXISTS_TAC `_NUMERAL _0` THEN CONJ_TAC THENL
   [CMPSYNPAUX_EQN_TAC NUMERAL_eqn; CMPSYNPAUX_EQN_TAC EQ_eqn1]);;

(* cases n = 0, n = SUC k (k a new name), everywhere *)
let CMPSYNPAUX_NUM_CASES_TAC (n:term) (k:term) : tactic =
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN k SUBST_ALL_TAC) (SPEC n num_CASES);;

let DIV_num2term = prove
 (`!thy m n. numeral_thy_ok thy ==>
     (thy,[]) |- _DIV (num2term m) (num2term n) === num2term (m SAFEDIV n)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN
  CMPSYNPAUX_NUM_CASES_TAC `m:num` `k:num` THEN
  CMPSYNPAUX_NUM_CASES_TAC `n:num` `l:num` THEN
  REWRITE_TAC[SAFEDIV_def; NOT_SUC; DIV_0; num2term_def] THENL
   [(* 0, 0 *)
    MATCH_MP_TAC replaceL1 THEN EXISTS_TAC `_NUMERAL _0` THEN CONJ_TAC THENL
     [CMPSYNPAUX_EQN_TAC NUMERAL_eqn; ALL_TAC] THEN
    MATCH_MP_TAC replaceL2 THEN EXISTS_TAC `_NUMERAL _0` THEN CONJ_TAC THENL
     [CMPSYNPAUX_EQN_TAC NUMERAL_eqn; ALL_TAC] THEN
    CMPSYNPAUX_TRANS_TAC DIV_eqn1 THEN CMPSYNPAUX_EQN_TAC NUMERAL_eqn;
    (* 0, SUC l *)
    MATCH_MP_TAC replaceL1 THEN EXISTS_TAC `_NUMERAL _0` THEN CONJ_TAC THENL
     [CMPSYNPAUX_EQN_TAC NUMERAL_eqn; ALL_TAC] THEN
    CMPSYNPAUX_TRANS_TAC DIV_eqn THEN
    CMPSYNPAUX_TRANS_TAC CMPSYNPAUX_COND_F THENL
     [CMPSYNPAUX_EQN_TAC EQ_eqn3; ALL_TAC] THEN
    CMPSYNPAUX_TRANS_TAC CMPSYNPAUX_COND_T THENL
     [CMPSYNPAUX_EQN_TAC (CMPSYNPAUX_cj 2 LESS_eqn) THEN
      EXISTS_TAC `(_0)` THEN CMPSYNPAUX_WT_TAC;
      CMPSYNPAUX_EQN_TAC NUMERAL_eqn];
    (* SUC k, 0 *)
    MATCH_MP_TAC replaceL2 THEN EXISTS_TAC `_NUMERAL _0` THEN CONJ_TAC THENL
     [CMPSYNPAUX_EQN_TAC NUMERAL_eqn; ALL_TAC] THEN
    CMPSYNPAUX_TRANS_TAC DIV_eqn1 THEN CMPSYNPAUX_EQN_TAC NUMERAL_eqn;
    (* SUC k, SUC l *)
    ALL_TAC] THEN
  CMPSYNPAUX_TRANS_TAC DIV_eqn THEN
  CMPSYNPAUX_TRANS_TAC CMPSYNPAUX_COND_F THENL
   [CMPSYNPAUX_EQN_TAC EQ_eqn3; ALL_TAC] THEN
  ASM_CASES_TAC `k < l:num` THENL
   [CMPSYNPAUX_TRANS_TAC CMPSYNPAUX_COND_T THENL
     [MP_TAC (SPECL [`thy:thy`; `SUC k`; `SUC l`] LESS_bool2term_num2term) THEN
      ASM_REWRITE_TAC[num2term_def; LT_SUC; bool2term_def];
      ASM_SIMP_TAC[DIV_LT; LT_SUC; num2term_def] THEN CMPSYNPAUX_EQN_TAC NUMERAL_eqn];
    ALL_TAC] THEN
  CMPSYNPAUX_TRANS_TAC CMPSYNPAUX_COND_F THENL
   [MP_TAC (SPECL [`thy:thy`; `SUC k`; `SUC l`] LESS_bool2term_num2term) THEN
    ASM_REWRITE_TAC[num2term_def; LT_SUC; bool2term_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `SUC k DIV SUC l = SUC ((SUC k - SUC l) DIV SUC l)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUB_DIV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[num2term_def] THEN
  MATCH_MP_TAC CMPSYNPAUX_cong_arg THEN CONJ_TAC THENL
   [ALL_TAC; CMPSYNPAUX_WT_TAC] THEN
  MATCH_MP_TAC replaceL1 THEN EXISTS_TAC `num2term (SUC k - SUC l)` THEN
  CONJ_TAC THENL
   [MP_TAC (SPECL [`thy:thy`; `SUC k`; `SUC l`] num2term_SUB) THEN
    ASM_REWRITE_TAC[num2term_def];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC k - SUC l`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o SPEC `SUC l`)] THEN
  REWRITE_TAC[SAFEDIV_def; NOT_SUC; num2term_def]);;

let num2term_DIV = GEN_ALL (DISCH_ALL (MATCH_MP sym_equation (UNDISCH (SPEC_ALL DIV_num2term))));;

let MOD_num2term = prove
 (`!thy m n. numeral_thy_ok thy ==>
     (thy,[]) |- _MOD (num2term m) (num2term n) === num2term (m SAFEMOD n)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN
  CMPSYNPAUX_NUM_CASES_TAC `m:num` `k:num` THEN
  CMPSYNPAUX_NUM_CASES_TAC `n:num` `l:num` THEN
  REWRITE_TAC[SAFEMOD_def; NOT_SUC; MOD_0; num2term_def] THENL
   [(* 0, 0 *)
    MATCH_MP_TAC replaceL2 THEN EXISTS_TAC `_NUMERAL _0` THEN CONJ_TAC THENL
     [CMPSYNPAUX_EQN_TAC NUMERAL_eqn; CMPSYNPAUX_EQN_TAC MOD_eqn1];
    (* 0, SUC l *)
    MATCH_MP_TAC replaceL1 THEN EXISTS_TAC `_NUMERAL _0` THEN CONJ_TAC THENL
     [CMPSYNPAUX_EQN_TAC NUMERAL_eqn; ALL_TAC] THEN
    CMPSYNPAUX_TRANS_TAC MOD_eqn THEN
    CMPSYNPAUX_TRANS_TAC CMPSYNPAUX_COND_F THENL
     [CMPSYNPAUX_EQN_TAC EQ_eqn3; ALL_TAC] THEN
    CMPSYNPAUX_TRANS_TAC CMPSYNPAUX_COND_T THENL
     [CMPSYNPAUX_EQN_TAC (CMPSYNPAUX_cj 2 LESS_eqn) THEN
      EXISTS_TAC `(_0)` THEN CMPSYNPAUX_WT_TAC;
      CMPSYNPAUX_EQN_TAC NUMERAL_eqn];
    (* SUC k, 0 *)
    MATCH_MP_TAC replaceL2 THEN EXISTS_TAC `_NUMERAL _0` THEN CONJ_TAC THENL
     [CMPSYNPAUX_EQN_TAC NUMERAL_eqn; CMPSYNPAUX_EQN_TAC MOD_eqn1];
    (* SUC k, SUC l *)
    ALL_TAC] THEN
  CMPSYNPAUX_TRANS_TAC MOD_eqn THEN
  CMPSYNPAUX_TRANS_TAC CMPSYNPAUX_COND_F THENL
   [CMPSYNPAUX_EQN_TAC EQ_eqn3; ALL_TAC] THEN
  ASM_CASES_TAC `k < l:num` THENL
   [CMPSYNPAUX_TRANS_TAC CMPSYNPAUX_COND_T THENL
     [MP_TAC (SPECL [`thy:thy`; `SUC k`; `SUC l`] LESS_bool2term_num2term) THEN
      ASM_REWRITE_TAC[num2term_def; LT_SUC; bool2term_def];
      ASM_SIMP_TAC[MOD_LT; LT_SUC; num2term_def] THEN CMPSYNPAUX_EQN_TAC proves_REFL];
    ALL_TAC] THEN
  CMPSYNPAUX_TRANS_TAC CMPSYNPAUX_COND_F THENL
   [MP_TAC (SPECL [`thy:thy`; `SUC k`; `SUC l`] LESS_bool2term_num2term) THEN
    ASM_REWRITE_TAC[num2term_def; LT_SUC; bool2term_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `SUC k MOD SUC l = (SUC k - SUC l) MOD SUC l` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUB_MOD THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC replaceL1 THEN EXISTS_TAC `num2term (SUC k - SUC l)` THEN
  CONJ_TAC THENL
   [MP_TAC (SPECL [`thy:thy`; `SUC k`; `SUC l`] num2term_SUB) THEN
    ASM_REWRITE_TAC[num2term_def];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC k - SUC l`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o SPEC `SUC l`)] THEN
  REWRITE_TAC[SAFEMOD_def; NOT_SUC; num2term_def]);;

let num2term_MOD = GEN_ALL (DISCH_ALL (MATCH_MP sym_equation (UNDISCH (SPEC_ALL MOD_num2term))));;

let num2bit_num2term = prove
 (`!thy. numeral_thy_ok thy ==>
     !n. (thy,[]) |- num2bit n === num2term n`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC num2bit_ind THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[num2bit_def] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[num2term_def] THEN CMPSYNPAUX_EQN_TAC proves_REFL; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC (SPECL [`n:num`; `2`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  STRIP_TAC THEN
  COND_CASES_TAC THENL
   [(* even: _BIT0 *)
    MATCH_MP_TAC trans_equation_simple THEN
    EXISTS_TAC `_BIT0 (num2term (n DIV 2))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMPSYNPAUX_cong_arg THEN ASM_REWRITE_TAC[] THEN CMPSYNPAUX_WT_TAC;
      ALL_TAC] THEN
    CMPSYNPAUX_TRANS_TAC BIT0_eqn THEN
    SUBGOAL_THEN `n = n DIV 2 + n DIV 2`
      (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [th])
    THENL [ASM_ARITH_TAC; CMPSYNPAUX_EQN_TAC ADD_num2term];
    (* odd: _BIT1 *)
    MATCH_MP_TAC trans_equation_simple THEN
    EXISTS_TAC `_BIT1 (num2term (n DIV 2))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMPSYNPAUX_cong_arg THEN ASM_REWRITE_TAC[] THEN CMPSYNPAUX_WT_TAC;
      ALL_TAC] THEN
    CMPSYNPAUX_TRANS_TAC BIT1_eqn THEN
    SUBGOAL_THEN `n = SUC (n DIV 2 + n DIV 2)`
      (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [th])
    THENL [ASM_ARITH_TAC; REWRITE_TAC[num2term_def]] THEN
    MATCH_MP_TAC CMPSYNPAUX_cong_arg THEN CONJ_TAC THENL
     [CMPSYNPAUX_EQN_TAC ADD_num2term; CMPSYNPAUX_WT_TAC]]);;

(* HOL4's proofs of num2bit_ADD ..: the arguments num2bit m, num2bit n of an *)
(* operation replaced by num2term m, num2term n (replaceR1, replaceL2), then *)
(* the num2term theorem th                                                    *)
let CMPSYNPAUX_NUM2BIT_TAC (th:thm) : tactic =
  MATCH_MP_TAC replaceR1 THEN EXISTS_TAC `num2term m` THEN CONJ_TAC THENL
   [MATCH_MP_TAC sym_equation THEN ASM_SIMP_TAC[num2bit_num2term]; ALL_TAC] THEN
  MATCH_MP_TAC replaceL2 THEN EXISTS_TAC `num2term n` THEN CONJ_TAC THENL
   [MATCH_MP_TAC sym_equation THEN ASM_SIMP_TAC[num2bit_num2term];
    ASM_SIMP_TAC[th]];;

let num2bit_ADD = prove
 (`!thy m n. numeral_thy_ok thy ==>
     (thy,[]) |- num2bit (m + n) === _ADD (num2bit m) (num2bit n)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_TRANS_TAC num2bit_num2term THEN
  CMPSYNPAUX_NUM2BIT_TAC ADD_num2term);;

let ADD_num2bit = GEN_ALL (DISCH_ALL (MATCH_MP sym_equation (UNDISCH (SPEC_ALL num2bit_ADD))));;

let num2bit_SUB = prove
 (`!thy m n. numeral_thy_ok thy ==>
     (thy,[]) |- num2bit (m - n) === _SUB (num2bit m) (num2bit n)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_TRANS_TAC num2bit_num2term THEN
  CMPSYNPAUX_NUM2BIT_TAC SUB_num2term);;

let SUB_num2bit = GEN_ALL (DISCH_ALL (MATCH_MP sym_equation (UNDISCH (SPEC_ALL num2bit_SUB))));;

let num2bit_MUL = prove
 (`!thy m n. numeral_thy_ok thy ==>
     (thy,[]) |- num2bit (m * n) === _MUL (num2bit m) (num2bit n)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_TRANS_TAC num2bit_num2term THEN
  CMPSYNPAUX_NUM2BIT_TAC MUL_num2term);;

let MUL_num2bit = GEN_ALL (DISCH_ALL (MATCH_MP sym_equation (UNDISCH (SPEC_ALL num2bit_MUL))));;

let num2bit_DIV = prove
 (`!thy m n. numeral_thy_ok thy ==>
     (thy,[]) |- num2bit (m SAFEDIV n) === _DIV (num2bit m) (num2bit n)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_TRANS_TAC num2bit_num2term THEN
  CMPSYNPAUX_NUM2BIT_TAC DIV_num2term);;

let DIV_num2bit = GEN_ALL (DISCH_ALL (MATCH_MP sym_equation (UNDISCH (SPEC_ALL num2bit_DIV))));;

let num2bit_MOD = prove
 (`!thy m n. numeral_thy_ok thy ==>
     (thy,[]) |- num2bit (m SAFEMOD n) === _MOD (num2bit m) (num2bit n)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_TRANS_TAC num2bit_num2term THEN
  CMPSYNPAUX_NUM2BIT_TAC MOD_num2term);;

let MOD_num2bit = GEN_ALL (DISCH_ALL (MATCH_MP sym_equation (UNDISCH (SPEC_ALL num2bit_MOD))));;

let bool2term_LESS_num2bit = prove
 (`!thy m n. numeral_thy_ok thy ==>
     (thy,[]) |- bool2term (m < n) === _LESS (num2bit m) (num2bit n)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_NUM2BIT_TAC LESS_bool2term_num2term);;

let LESS_bool2term_num2bit =
  GEN_ALL (DISCH_ALL (MATCH_MP sym_equation (UNDISCH (SPEC_ALL bool2term_LESS_num2bit))));;

let bool2term_EQ_num2bit = prove
 (`!thy m n. numeral_thy_ok thy ==>
     (thy,[]) |- bool2term (m = n) === (num2bit m === num2bit n)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC replaceR_eq1 THEN EXISTS_TAC `num2term m` THEN CONJ_TAC THENL
   [MATCH_MP_TAC sym_equation THEN ASM_SIMP_TAC[num2bit_num2term]; ALL_TAC] THEN
  MATCH_MP_TAC replaceL_eq2 THEN EXISTS_TAC `num2term n` THEN CONJ_TAC THENL
   [MATCH_MP_TAC sym_equation THEN ASM_SIMP_TAC[num2bit_num2term];
    ASM_SIMP_TAC[EQ_bool2term_num2term]]);;

let EQ_bool2term_num2bit =
  GEN_ALL (DISCH_ALL (MATCH_MP sym_equation (UNDISCH (SPEC_ALL bool2term_EQ_num2bit))));;

(* ------------------------------------------------------------------------- *)
(* Compute values                                                            *)
(* ------------------------------------------------------------------------- *)

let cexp_consts_def = cake_def
  `(cexp_consts (compute_Num n) = {}:(mlstring#num)->bool) /\
   (cexp_consts (compute_Var s) = {}) /\
   (cexp_consts (compute_Pair p q) = cexp_consts p UNION cexp_consts q) /\
   (cexp_consts (compute_Uop uop p) = cexp_consts p) /\
   (cexp_consts (compute_Binop bop p q) = cexp_consts p UNION cexp_consts q) /\
   (cexp_consts (compute_If p q r) =
      (cexp_consts p UNION cexp_consts q) UNION cexp_consts r) /\
   (cexp_consts (compute_Let s p q) = cexp_consts p UNION cexp_consts q) /\
   (cexp_consts (compute_App s cs) =
      {(s,LENGTH cs)} UNION UNIONS (set_of_list (MAP cexp_consts cs)))`;;

let cexp_consts_ind = cake_ind "cexp_consts";;

let cexp_vars_def = cake_def
  `(cexp_vars (compute_Num n) = {}:mlstring->bool) /\
   (cexp_vars (compute_Var s) = {s}) /\
   (cexp_vars (compute_Pair p q) = cexp_vars p UNION cexp_vars q) /\
   (cexp_vars (compute_Uop uop p) = cexp_vars p) /\
   (cexp_vars (compute_Binop bop p q) = cexp_vars p UNION cexp_vars q) /\
   (cexp_vars (compute_If p q r) =
      (cexp_vars p UNION cexp_vars q) UNION cexp_vars r) /\
   (cexp_vars (compute_Let s p q) = cexp_vars p UNION (cexp_vars q DIFF {s})) /\
   (cexp_vars (compute_App s cs) = UNIONS (set_of_list (MAP cexp_vars cs)))`;;

let cexp_vars_ind = cake_ind "cexp_vars";;

(* The semantics of 'ill-typed' operations on the compute_exp type is to   *)
(* return the number 0 (i.e. Num 0).                                        *)

(* the equations of Cexp_add, Cexp_sub, Cexp_mul, Cexp_div, Cexp_mod,   *)
(* Cexp_less, Cexp_if, Cexp_fst, Cexp_snd, Cexp_ispair, Cexp_eq and LET *)
let compute_thy_ok_def = cake_def
  `compute_thy_ok thy <=>
     numeral_thy_ok thy /\
     (thy,[]) |- _CEXP_ADD (_CEXP_NUM _M) (_CEXP_NUM _N) ===
                 _CEXP_NUM (_ADD _M _N) /\
     (thy,[]) |- _CEXP_ADD (_CEXP_NUM _M) (_CEXP_PAIR _P1 _Q1) ===
                 _CEXP_NUM _M /\
     (thy,[]) |- _CEXP_ADD (_CEXP_PAIR _P1 _Q1) (_CEXP_NUM _N) ===
                 _CEXP_NUM _N /\
     (thy,[]) |- _CEXP_ADD (_CEXP_PAIR _P1 _Q1) (_CEXP_PAIR _P2 _Q2) ===
                 _CEXP_NUM (_NUMERAL _0) /\
     (thy,[]) |- _CEXP_SUB (_CEXP_NUM _M) (_CEXP_NUM _N) ===
                 _CEXP_NUM (_SUB _M _N) /\
     (thy,[]) |- _CEXP_SUB (_CEXP_NUM _M) (_CEXP_PAIR _P1 _Q1) ===
                 _CEXP_NUM _M /\
     (thy,[]) |- _CEXP_SUB (_CEXP_PAIR _P1 _Q1) (_CEXP_NUM _N) ===
                 _CEXP_NUM (_NUMERAL _0) /\
     (thy,[]) |- _CEXP_SUB (_CEXP_PAIR _P1 _Q1) (_CEXP_PAIR _P2 _Q2) ===
                 _CEXP_NUM (_NUMERAL _0) /\
     (thy,[]) |- _CEXP_MUL (_CEXP_NUM _M) (_CEXP_NUM _N) ===
                 _CEXP_NUM (_MUL _M _N) /\
     (thy,[]) |- _CEXP_MUL (_CEXP_NUM _M) (_CEXP_PAIR _P1 _Q1) ===
                 _CEXP_NUM (_NUMERAL _0) /\
     (thy,[]) |- _CEXP_MUL (_CEXP_PAIR _P1 _Q1) (_CEXP_NUM _N) ===
                 _CEXP_NUM (_NUMERAL _0) /\
     (thy,[]) |- _CEXP_MUL (_CEXP_PAIR _P1 _Q1) (_CEXP_PAIR _P2 _Q2) ===
                 _CEXP_NUM (_NUMERAL _0) /\
     (thy,[]) |- _CEXP_DIV (_CEXP_NUM _M) (_CEXP_NUM _N) ===
                 _CEXP_NUM (_DIV _M _N) /\
     (thy,[]) |- _CEXP_DIV (_CEXP_NUM _M) (_CEXP_PAIR _P1 _Q1) ===
                 _CEXP_NUM (_NUMERAL _0) /\
     (thy,[]) |- _CEXP_DIV (_CEXP_PAIR _P1 _Q1) (_CEXP_NUM _N) ===
                 _CEXP_NUM (_NUMERAL _0) /\
     (thy,[]) |- _CEXP_DIV (_CEXP_PAIR _P1 _Q1) (_CEXP_PAIR _P2 _Q2) ===
                 _CEXP_NUM (_NUMERAL _0) /\
     (thy,[]) |- _CEXP_MOD (_CEXP_NUM _M) (_CEXP_NUM _N) ===
                 _CEXP_NUM (_MOD _M _N) /\
     (thy,[]) |- _CEXP_MOD (_CEXP_NUM _M) (_CEXP_PAIR _P1 _Q1) ===
                 _CEXP_NUM _M /\
     (thy,[]) |- _CEXP_MOD (_CEXP_PAIR _P1 _Q1) (_CEXP_NUM _N) ===
                 _CEXP_NUM (_NUMERAL _0) /\
     (thy,[]) |- _CEXP_MOD (_CEXP_PAIR _P1 _Q1) (_CEXP_PAIR _P2 _Q2) ===
                 _CEXP_NUM (_NUMERAL _0) /\
     (thy,[]) |- _CEXP_LESS (_CEXP_NUM _M) (_CEXP_NUM _N) ===
                 _CEXP_NUM (_COND (_LESS _M _N) (_SUC (_NUMERAL _0))
                 (_NUMERAL _0)) /\
     (thy,[]) |- _CEXP_LESS (_CEXP_NUM _M) (_CEXP_PAIR _P1 _Q1) ===
                 _CEXP_NUM (_NUMERAL _0) /\
     (thy,[]) |- _CEXP_LESS (_CEXP_PAIR _P1 _Q1) (_CEXP_NUM _N) ===
                 _CEXP_NUM (_NUMERAL _0) /\
     (thy,[]) |- _CEXP_LESS (_CEXP_PAIR _P1 _Q1) (_CEXP_PAIR _P2 _Q2) ===
                 _CEXP_NUM (_NUMERAL _0) /\
     (thy,[]) |- _CEXP_IF (_CEXP_NUM (_SUC _M)) _P1 _Q1 === _P1 /\
     (thy,[]) |- _CEXP_IF (_CEXP_PAIR _P2 _Q2) _P1 _Q1 === _Q1 /\
     (thy,[]) |- _CEXP_IF (_CEXP_NUM (_NUMERAL _0)) _P1 _Q1 === _Q1 /\
     (thy,[]) |- _CEXP_FST (_CEXP_PAIR _P1 _Q1) === _P1 /\
     (thy,[]) |- _CEXP_FST (_CEXP_NUM _M) === _CEXP_NUM (_NUMERAL _0) /\
     (thy,[]) |- _CEXP_SND (_CEXP_PAIR _P1 _Q1) === _Q1 /\
     (thy,[]) |- _CEXP_SND (_CEXP_NUM _M) === _CEXP_NUM (_NUMERAL _0) /\
     (thy,[]) |- _CEXP_ISPAIR (_CEXP_PAIR _P1 _Q1) ===
                 _CEXP_NUM (_SUC (_NUMERAL _0)) /\
     (thy,[]) |- _CEXP_ISPAIR (_CEXP_NUM _M) ===
                 _CEXP_NUM (_NUMERAL _0) /\
     (thy,[]) |- _CEXP_EQ _P1 _Q1 ===
                 _CEXP_NUM (_COND (_P1 === _Q1)(_SUC (_NUMERAL _0))
                 (_NUMERAL _0)) /\
     (thy,[]) |- (_CEXP_PAIR _P1 _Q1 === _CEXP_PAIR _P2 _Q2) ===
                 (_IF (_P1 === _P2) (_Q1 === _Q2) _FALSE) /\
     (thy,[]) |- (_CEXP_NUM _M === _CEXP_NUM _N) === (_M === _N) /\
     (thy,[]) |- (_CEXP_NUM _M === _CEXP_PAIR _P1 _Q1) === _FALSE /\
     (thy,[]) |- (_CEXP_PAIR _P1 _Q1 === _CEXP_NUM _N) === _FALSE /\
     (thy,[]) |- _LET _F _P1 === hol_Comb _F _P1`;;


let LET_eqn = prove
 (`!thy p1 f.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) f /\ hol_term_ok (FST thy) p1 /\
     f has_type (Fun Cexp Cexp) /\ p1 has_type Cexp ==>
     (thy,[]) |- _LET f p1 === hol_Comb f p1`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; f,_F]");;

let CEXP_IF_eqn1 = prove
 (`!thy m p1 q1.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     m has_type Num /\ p1 has_type Cexp /\ q1 has_type Cexp ==>
     (thy,[]) |- _CEXP_IF (_CEXP_NUM (_SUC m)) p1 q1 === p1`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1; m,_M]");;

let CEXP_IF_eqn2 = prove
 (`!thy p1 q1 p2 q2.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     hol_term_ok (FST thy) p2 /\ hol_term_ok (FST thy) q2 /\
     p1 has_type Cexp /\ q1 has_type Cexp /\
     p2 has_type Cexp /\ q2 has_type Cexp ==>
     (thy,[]) |- _CEXP_IF (_CEXP_PAIR p2 q2) p1 q1 === q1`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1; p2,_P2; q2,_Q2]");;

let CEXP_IF_eqn3 = prove
 (`!thy p1 q1.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     p1 has_type Cexp /\ q1 has_type Cexp ==>
     (thy,[]) |- _CEXP_IF (_CEXP_NUM (_NUMERAL _0)) p1 q1 === q1`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1]");;

let CEXP_ADD_eqn1 = prove
 (`!thy m n.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) n /\
     m has_type Num /\ n has_type Num ==>
     (thy,[]) |- _CEXP_ADD (_CEXP_NUM m) (_CEXP_NUM n) === _CEXP_NUM (_ADD m n)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[n,_N; m,_M]");;

let CEXP_ADD_eqn2 = prove
 (`!thy m p1 q1.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     m has_type Num /\ p1 has_type Cexp /\ q1 has_type Cexp ==>
     (thy,[]) |- _CEXP_ADD (_CEXP_NUM m) (_CEXP_PAIR p1 q1) === _CEXP_NUM m`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1; m,_M]");;

let CEXP_ADD_eqn3 = prove
 (`!thy n p1 q1.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) n /\ hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     n has_type Num /\ p1 has_type Cexp /\ q1 has_type Cexp ==>
     (thy,[]) |- _CEXP_ADD (_CEXP_PAIR p1 q1) (_CEXP_NUM n) === _CEXP_NUM n`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1; n,_N]");;

let CEXP_ADD_eqn4 = prove
 (`!thy p1 q1 p2 q2.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     hol_term_ok (FST thy) p2 /\ hol_term_ok (FST thy) q2 /\
     p1 has_type Cexp /\ q1 has_type Cexp /\
     p2 has_type Cexp /\ q2 has_type Cexp ==>
     (thy,[]) |- _CEXP_ADD (_CEXP_PAIR p1 q1) (_CEXP_PAIR p2 q2) ===
     _CEXP_NUM (_NUMERAL _0)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1; p2,_P2; q2,_Q2]");;

let CEXP_SUB_eqn1 = prove
 (`!thy m n.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) n /\
     m has_type Num /\ n has_type Num ==>
     (thy,[]) |- _CEXP_SUB (_CEXP_NUM m) (_CEXP_NUM n) === _CEXP_NUM (_SUB m n)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[n,_N; m,_M]");;

let CEXP_SUB_eqn2 = prove
 (`!thy m p1 q1.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     m has_type Num /\ p1 has_type Cexp /\ q1 has_type Cexp ==>
     (thy,[]) |- _CEXP_SUB (_CEXP_NUM m) (_CEXP_PAIR p1 q1) === _CEXP_NUM m`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1; m,_M]");;

let CEXP_SUB_eqn3 = prove
 (`!thy n p1 q1.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) n /\ hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     n has_type Num /\ p1 has_type Cexp /\ q1 has_type Cexp ==>
     (thy,[]) |- _CEXP_SUB (_CEXP_PAIR p1 q1) (_CEXP_NUM n) ===
     _CEXP_NUM (_NUMERAL _0)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1; n,_N]");;

let CEXP_SUB_eqn4 = prove
 (`!thy p1 q1 p2 q2.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     hol_term_ok (FST thy) p2 /\ hol_term_ok (FST thy) q2 /\
     p1 has_type Cexp /\ q1 has_type Cexp /\
     p2 has_type Cexp /\ q2 has_type Cexp ==>
     (thy,[]) |- _CEXP_SUB (_CEXP_PAIR p1 q1) (_CEXP_PAIR p2 q2) ===
     _CEXP_NUM (_NUMERAL _0)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1; p2,_P2; q2,_Q2]");;

let CEXP_MUL_eqn1 = prove
 (`!thy m n.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) n /\
     m has_type Num /\ n has_type Num ==>
     (thy,[]) |- _CEXP_MUL (_CEXP_NUM m) (_CEXP_NUM n) === _CEXP_NUM (_MUL m n)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[n,_N; m,_M]");;

let CEXP_MUL_eqn2 = prove
 (`!thy m p1 q1.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     m has_type Num /\ p1 has_type Cexp /\ q1 has_type Cexp ==>
     (thy,[]) |- _CEXP_MUL (_CEXP_NUM m) (_CEXP_PAIR p1 q1) ===
     _CEXP_NUM (_NUMERAL _0)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1; m,_M]");;

let CEXP_MUL_eqn3 = prove
 (`!thy n p1 q1.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) n /\ hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     n has_type Num /\ p1 has_type Cexp /\ q1 has_type Cexp ==>
     (thy,[]) |- _CEXP_MUL (_CEXP_PAIR p1 q1) (_CEXP_NUM n) ===
     _CEXP_NUM (_NUMERAL _0)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1; n,_N]");;

let CEXP_MUL_eqn4 = prove
 (`!thy p1 q1 p2 q2.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     hol_term_ok (FST thy) p2 /\ hol_term_ok (FST thy) q2 /\
     p1 has_type Cexp /\ q1 has_type Cexp /\
     p2 has_type Cexp /\ q2 has_type Cexp ==>
     (thy,[]) |- _CEXP_MUL (_CEXP_PAIR p1 q1) (_CEXP_PAIR p2 q2) ===
     _CEXP_NUM (_NUMERAL _0)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1; p2,_P2; q2,_Q2]");;

let CEXP_DIV_eqn1 = prove
 (`!thy m n.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) n /\
     m has_type Num /\ n has_type Num ==>
     (thy,[]) |- _CEXP_DIV (_CEXP_NUM m) (_CEXP_NUM n) === _CEXP_NUM (_DIV m n)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[n,_N; m,_M]");;

let CEXP_DIV_eqn2 = prove
 (`!thy m p1 q1.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     m has_type Num /\ p1 has_type Cexp /\ q1 has_type Cexp ==>
     (thy,[]) |- _CEXP_DIV (_CEXP_NUM m) (_CEXP_PAIR p1 q1) ===
     _CEXP_NUM (_NUMERAL _0)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1; m,_M]");;

let CEXP_DIV_eqn3 = prove
 (`!thy n p1 q1.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) n /\ hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     n has_type Num /\ p1 has_type Cexp /\ q1 has_type Cexp ==>
     (thy,[]) |- _CEXP_DIV (_CEXP_PAIR p1 q1) (_CEXP_NUM n) ===
     _CEXP_NUM (_NUMERAL _0)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1; n,_N]");;

let CEXP_DIV_eqn4 = prove
 (`!thy p1 q1 p2 q2.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     hol_term_ok (FST thy) p2 /\ hol_term_ok (FST thy) q2 /\
     p1 has_type Cexp /\ q1 has_type Cexp /\
     p2 has_type Cexp /\ q2 has_type Cexp ==>
     (thy,[]) |- _CEXP_DIV (_CEXP_PAIR p1 q1) (_CEXP_PAIR p2 q2) ===
     _CEXP_NUM (_NUMERAL _0)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1; p2,_P2; q2,_Q2]");;

let CEXP_MOD_eqn1 = prove
 (`!thy m n.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) n /\
     m has_type Num /\ n has_type Num ==>
     (thy,[]) |- _CEXP_MOD (_CEXP_NUM m) (_CEXP_NUM n) === _CEXP_NUM (_MOD m n)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[n,_N; m,_M]");;

let CEXP_MOD_eqn2 = prove
 (`!thy m p1 q1.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     m has_type Num /\ p1 has_type Cexp /\ q1 has_type Cexp ==>
     (thy,[]) |- _CEXP_MOD (_CEXP_NUM m) (_CEXP_PAIR p1 q1) ===
     _CEXP_NUM m`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1; m,_M]");;

let CEXP_MOD_eqn3 = prove
 (`!thy n p1 q1.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) n /\ hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     n has_type Num /\ p1 has_type Cexp /\ q1 has_type Cexp ==>
     (thy,[]) |- _CEXP_MOD (_CEXP_PAIR p1 q1) (_CEXP_NUM n) ===
     _CEXP_NUM (_NUMERAL _0)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1; n,_N]");;

let CEXP_MOD_eqn4 = prove
 (`!thy p1 q1 p2 q2.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     hol_term_ok (FST thy) p2 /\ hol_term_ok (FST thy) q2 /\
     p1 has_type Cexp /\ q1 has_type Cexp /\
     p2 has_type Cexp /\ q2 has_type Cexp ==>
     (thy,[]) |- _CEXP_MOD (_CEXP_PAIR p1 q1) (_CEXP_PAIR p2 q2) ===
     _CEXP_NUM (_NUMERAL _0)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1; p2,_P2; q2,_Q2]");;

let CEXP_LESS_eqn1 = prove
 (`!thy m n.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) n /\
     m has_type Num /\ n has_type Num ==>
     (thy,[]) |- _CEXP_LESS (_CEXP_NUM m) (_CEXP_NUM n) ===
     _CEXP_NUM (_COND (_LESS m n) (_SUC (_NUMERAL _0))
     (_NUMERAL _0))`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[n,_N; m,_M]");;

let CEXP_LESS_eqn2 = prove
 (`!thy m p1 q1.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) m /\ hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     m has_type Num /\ p1 has_type Cexp /\ q1 has_type Cexp ==>
     (thy,[]) |- _CEXP_LESS (_CEXP_NUM m) (_CEXP_PAIR p1 q1) ===
     _CEXP_NUM (_NUMERAL _0)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1; m,_M]");;

let CEXP_LESS_eqn3 = prove
 (`!thy n p1 q1.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) n /\ hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     n has_type Num /\ p1 has_type Cexp /\ q1 has_type Cexp ==>
     (thy,[]) |- _CEXP_LESS (_CEXP_PAIR p1 q1) (_CEXP_NUM n) ===
     _CEXP_NUM (_NUMERAL _0)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1; n,_N]");;

let CEXP_LESS_eqn4 = prove
 (`!thy p1 q1 p2 q2.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     hol_term_ok (FST thy) p2 /\ hol_term_ok (FST thy) q2 /\
     p1 has_type Cexp /\ q1 has_type Cexp /\
     p2 has_type Cexp /\ q2 has_type Cexp ==>
     (thy,[]) |- _CEXP_LESS (_CEXP_PAIR p1 q1) (_CEXP_PAIR p2 q2) ===
     _CEXP_NUM (_NUMERAL _0)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1; p2,_P2; q2,_Q2]");;

let CEXP_FST_eqn1 = prove
 (`!thy p1 q1.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     p1 has_type Cexp /\ q1 has_type Cexp ==>
     (thy,[]) |- _CEXP_FST (_CEXP_PAIR p1 q1) === p1`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1]");;

let CEXP_FST_eqn2 = prove
 (`!thy m.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) m /\ m has_type Num ==>
     (thy,[]) |- _CEXP_FST (_CEXP_NUM m) === _CEXP_NUM (_NUMERAL _0)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[m,_M]");;

let CEXP_SND_eqn1 = prove
 (`!thy p1 q1.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     p1 has_type Cexp /\ q1 has_type Cexp ==>
     (thy,[]) |- _CEXP_SND (_CEXP_PAIR p1 q1) === q1`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1]");;

let CEXP_SND_eqn2 = prove
 (`!thy m.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) m /\ m has_type Num ==>
     (thy,[]) |- _CEXP_SND (_CEXP_NUM m) === _CEXP_NUM (_NUMERAL _0)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[m,_M]");;

let CEXP_ISPAIR_eqn1 = prove
 (`!thy p1 q1.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) p1 /\ hol_term_ok (FST thy) q1 /\
     p1 has_type Cexp /\ q1 has_type Cexp ==>
     (thy,[]) |- _CEXP_ISPAIR (_CEXP_PAIR p1 q1) ===
     _CEXP_NUM (_SUC (_NUMERAL _0))`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1; q1,_Q1]");;

let CEXP_ISPAIR_eqn2 = prove
 (`!thy m.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) m /\ m has_type Num ==>
     (thy,[]) |- _CEXP_ISPAIR (_CEXP_NUM m) === _CEXP_NUM (_NUMERAL _0)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[m,_M]");;

let CEXP_EQ_eqn1 = prove
 (`!thy p1 q1.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) p1 /\ p1 has_type Cexp /\
     hol_term_ok (FST thy) q1 /\ q1 has_type Cexp ==>
     (thy,[]) |- _CEXP_EQ p1 q1 ===
     _CEXP_NUM (_COND (p1 === q1)(_SUC (_NUMERAL _0))
     (_NUMERAL _0))`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1;q1,_Q1]");;

let CEXP_EQ_eqn2 = prove
 (`!thy p1 q1 p2 q2.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) p1 /\ p1 has_type Cexp /\
     hol_term_ok (FST thy) q1 /\ q1 has_type Cexp /\
     hol_term_ok (FST thy) p2 /\ p2 has_type Cexp /\
     hol_term_ok (FST thy) q2 /\ q2 has_type Cexp ==>
     (thy,[]) |- (_CEXP_PAIR p1 q1 === _CEXP_PAIR p2 q2) ===
     (_IF (p1 === p2) (q1 === q2) _FALSE)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[p1,_P1;q1,_Q1;p2,_P2;q2,_Q2]");;

let CEXP_EQ_eqn3 = prove
 (`!thy m n.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) n /\ n has_type Num /\
     hol_term_ok (FST thy) m /\ m has_type Num ==>
     (thy,[]) |- (_CEXP_NUM m === _CEXP_NUM n) === (m === n)`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[n,_N;m,_M]");;

let CEXP_EQ_eqn4 = prove
 (`!thy m p1 q1.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) m /\ m has_type Num /\
     hol_term_ok (FST thy) p1 /\ p1 has_type Cexp /\
     hol_term_ok (FST thy) q1 /\ q1 has_type Cexp ==>
     (thy,[]) |- (_CEXP_NUM m === _CEXP_PAIR p1 q1) === _FALSE`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[m,_M;p1,_P1;q1,_Q1]");;

let CEXP_EQ_eqn5 = prove
 (`!thy n p1 q1.
     compute_thy_ok thy /\
     hol_term_ok (FST thy) n /\ n has_type Num /\
     hol_term_ok (FST thy) p1 /\ p1 has_type Cexp /\
     hol_term_ok (FST thy) q1 /\ q1 has_type Cexp ==>
     (thy,[]) |- (_CEXP_PAIR p1 q1 === _CEXP_NUM n) === _FALSE`,
  REPEAT STRIP_TAC THEN CMPSYNPAUX_INST_TAC compute_thy_ok_def "[n,_N;p1,_P1;q1,_Q1]");;


let compute_thy_ok_terms_ok = prove
 (`!thy. compute_thy_ok thy ==>
     hol_term_ok (FST thy) _TRUE /\
     hol_term_ok (FST thy) _FALSE /\
     hol_term_ok (FST thy) _COND_TM /\
     hol_term_ok (FST thy) _IF_TM /\
     hol_term_ok (FST thy) _ADD_TM /\
     hol_term_ok (FST thy) _SUB_TM /\
     hol_term_ok (FST thy) _MUL_TM /\
     hol_term_ok (FST thy) _DIV_TM /\
     hol_term_ok (FST thy) _MOD_TM /\
     hol_term_ok (FST thy) _LESS_TM /\
     hol_term_ok (FST thy) _0 /\
     hol_term_ok (FST thy) _SUC_TM /\
     hol_term_ok (FST thy) _BIT0_TM /\
     hol_term_ok (FST thy) _BIT1_TM /\
     hol_term_ok (FST thy) _NUMERAL_TM /\
     hol_term_ok (FST thy) _CEXP_ADD_TM /\
     hol_term_ok (FST thy) _CEXP_SUB_TM /\
     hol_term_ok (FST thy) _CEXP_MUL_TM /\
     hol_term_ok (FST thy) _CEXP_DIV_TM /\
     hol_term_ok (FST thy) _CEXP_MOD_TM /\
     hol_term_ok (FST thy) _CEXP_LESS_TM /\
     hol_term_ok (FST thy) _CEXP_NUM_TM /\
     hol_term_ok (FST thy) _CEXP_IF_TM /\
     hol_term_ok (FST thy) _CEXP_PAIR_TM /\
     hol_term_ok (FST thy) _CEXP_FST_TM /\
     hol_term_ok (FST thy) _CEXP_SND_TM /\
     hol_term_ok (FST thy) _CEXP_ISPAIR_TM /\
     hol_term_ok (FST thy) _CEXP_EQ_TM /\
     hol_term_ok (FST thy) _LET_TM /\
     type_ok (FST (FST thy)) Cexp`,
  GEN_TAC THEN DISCH_TAC THEN
  (fun g ->
     let okth = ASSUME `compute_thy_ok thy` in
     let ths = CMPSYNPAUX_AXIOMS_OK compute_thy_ok_def okth @
               CONJUNCTS (MATCH_MP numeral_thy_ok_terms_ok
                 (CONJUNCT1 (EQ_MP (SPEC `thy:thy` compute_thy_ok_def) okth))) in
     let numth = find (fun th -> concl th = `hol_term_ok (FST (thy:thy)) _CEXP_NUM_TM`) ths in
     (REPEAT CONJ_TAC THEN TRY (FIRST (map ACCEPT_TAC ths)) THEN
      MP_TAC numth THEN REWRITE_TAC[hol_term_ok_def; type_ok_def; ALL] THEN
      MESON_TAC[]) g));;

let compute_thy_ok_theory_ok = prove
 (`!thy. compute_thy_ok thy ==> theory_ok thy`,
  SIMP_TAC[compute_thy_ok_def; numeral_thy_ok_def; bool_thy_ok_def]);;
let _ = cake_add_simps [compute_thy_ok_theory_ok];;

let compute_thy_ok_numeral_thy_ok = prove
 (`!thy. compute_thy_ok thy ==> numeral_thy_ok thy`,
  SIMP_TAC[compute_thy_ok_def]);;
let _ = cake_add_simps [compute_thy_ok_numeral_thy_ok];;

let compute_thy_ok_bool_thy_ok = prove
 (`!thy. compute_thy_ok thy ==> bool_thy_ok thy`,
  SIMP_TAC[compute_thy_ok_def; numeral_thy_ok_def]);;
let _ = cake_add_simps [compute_thy_ok_bool_thy_ok];;

CMPSYNPAUX_ok_rules := !CMPSYNPAUX_ok_rules @ [compute_thy_ok_terms_ok];;
CMPSYNPAUX_ok_impls := !CMPSYNPAUX_ok_impls @
  [compute_thy_ok_theory_ok; compute_thy_ok_numeral_thy_ok; compute_thy_ok_bool_thy_ok];;

(* the operations and the applications of cexp2term *)
let CMPSYNPAUX_bop2term_typeof = prove
 (`!bop t1 t2. typeof (bop2term bop t1 t2) = Cexp`,
  MATCH_MP_TAC compute_binop_INDUCT THEN
  REWRITE_TAC[bop2term_def; typeof_def; codomain_def]);;

let CMPSYNPAUX_uop2term_typeof = prove
 (`!uop t. typeof (uop2term uop t) = Cexp`,
  MATCH_MP_TAC uop_INDUCT THEN REWRITE_TAC[uop2term_def; typeof_def; codomain_def]);;

let CMPSYNPAUX_bop2term_has_type = prove
 (`!bop t1 t2. bop2term bop t1 t2 has_type Cexp <=>
               t1 has_type Cexp /\ t2 has_type Cexp`,
  MATCH_MP_TAC compute_binop_INDUCT THEN REWRITE_TAC[bop2term_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN CMPSYNPAUX_WT_TAC THEN MESON_TAC[]);;

let CMPSYNPAUX_uop2term_has_type = prove
 (`!uop t. uop2term uop t has_type Cexp <=> t has_type Cexp`,
  MATCH_MP_TAC uop_INDUCT THEN REWRITE_TAC[uop2term_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN CMPSYNPAUX_WT_TAC THEN MESON_TAC[]);;

let CMPSYNPAUX_FOLDL_typeof = prove
 (`!cs tm (g:compute_exp->hol_term).
     typeof tm = app_type (LENGTH cs)
     ==> typeof (FOLDL hol_Comb tm (MAP g cs)) = Cexp`,
  LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[FOLDL; MAP; LENGTH; app_type; typeof_def; codomain_def]);;

let CMPSYNPAUX_FOLDL_has_type = prove
 (`!cs tm (g:compute_exp->hol_term).
     tm has_type app_type (LENGTH cs) /\
     (!c. MEM c cs ==> g c has_type Cexp)
     ==> FOLDL hol_Comb tm (MAP g cs) has_type Cexp`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL; MAP; LENGTH; app_type; MEM] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 has_type_rules))) THEN
  EXISTS_TAC `(Cexp)` THEN ASM_SIMP_TAC[]);;

let CMPSYNPAUX_FOLDL_term_ok = prove
 (`!cs tm (g:compute_exp->hol_term) sig.
     hol_term_ok sig tm /\ tm has_type app_type (LENGTH cs) /\
     (!c. MEM c cs ==> hol_term_ok sig (g c) /\ g c has_type Cexp)
     ==> hol_term_ok sig (FOLDL hol_Comb tm (MAP g cs))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL; MAP; LENGTH; app_type; MEM] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `hol_term_ok sig ((g:compute_exp->hol_term) h) /\ g h has_type Cexp`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CMPSYNPAUX_term_ok_Comb_alt] THEN ASM_REWRITE_TAC[] THEN
    IMP_RES_TAC WELLTYPED_LEMMA THEN ASM_REWRITE_TAC[codomain_def];
    MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 has_type_rules))) THEN
    EXISTS_TAC `(Cexp)` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

let cexp2term_typeof = prove
 (`!cv. typeof (cexp2term cv) = Cexp`,
  MATCH_MP_TAC cexp2term_ind THEN
  REWRITE_TAC[cexp2term_def; typeof_def; codomain_def; CMPSYNPAUX_bop2term_typeof;
              CMPSYNPAUX_uop2term_typeof] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPSYNPAUX_FOLDL_typeof THEN
  REWRITE_TAC[typeof_def]);;
let _ = cake_add_simps [cexp2term_typeof];;

let cexp2term_has_type = prove
 (`!cv. cexp2term cv has_type Cexp`,
  MATCH_MP_TAC cexp2term_ind THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[cexp2term_def; CMPSYNPAUX_bop2term_has_type;
              CMPSYNPAUX_uop2term_has_type] THEN
  ASM_REWRITE_TAC[] THEN TRY (CMPSYNPAUX_WT_TAC THEN NO_TAC) THEN
  MATCH_MP_TAC CMPSYNPAUX_FOLDL_has_type THEN ASM_REWRITE_TAC[has_type_rules]);;
let _ = cake_add_simps [cexp2term_has_type];;

let cexp2term_welltyped = prove
 (`!cv. welltyped (cexp2term cv)`,
  MESON_TAC[welltyped_def; cexp2term_has_type]);;
let _ = cake_add_simps [cexp2term_welltyped];;

CMPSYNPAUX_wt_thms := !CMPSYNPAUX_wt_thms @
  [cexp2term_typeof; cexp2term_has_type; cexp2term_welltyped;
   CMPSYNPAUX_bop2term_typeof; CMPSYNPAUX_uop2term_typeof];;

let bop2term_term_ok = prove
 (`!thy bop tm1 tm2.
     compute_thy_ok thy ==>
       typeof tm1 = Cexp /\ typeof tm2 = Cexp /\
       hol_term_ok (FST thy) tm1 /\ hol_term_ok (FST thy) tm2 ==>
         hol_term_ok (FST thy) (bop2term bop tm1 tm2)`,
  GEN_TAC THEN MATCH_MP_TAC compute_binop_INDUCT THEN REWRITE_TAC[bop2term_def] THEN
  REPEAT STRIP_TAC THEN CMPSYNPAUX_WT_TAC);;

let uop2term_term_ok = prove
 (`!thy uop tm.
     compute_thy_ok thy ==>
       typeof tm = Cexp /\
       hol_term_ok (FST thy) tm ==>
         hol_term_ok (FST thy) (uop2term uop tm)`,
  GEN_TAC THEN MATCH_MP_TAC uop_INDUCT THEN REWRITE_TAC[uop2term_def] THEN
  REPEAT STRIP_TAC THEN CMPSYNPAUX_WT_TAC);;

let cexp2term_term_ok = prove
 (`!thy. compute_thy_ok thy ==>
     !cv. (!c n. (c,n) IN cexp_consts cv ==>
                 hol_term_ok (FST thy) (hol_Const c (app_type n))) ==>
          hol_term_ok (FST thy) (cexp2term cv)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC cexp2term_ind THEN
  REWRITE_TAC[cexp2term_def; cexp_consts_def; IN_UNION; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN
  REPEAT (FIRST_X_ASSUM (MP_TAC o check (is_imp o concl)) THEN
          ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC]) THEN
  TRY (CMPSYNPAUX_WT_TAC THEN NO_TAC) THENL
   [IRULE uop2term_term_ok THEN CMPSYNPAUX_WT_TAC;
    IRULE bop2term_term_ok THEN CMPSYNPAUX_WT_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CMPSYNPAUX_FOLDL_term_ok THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_SING];
    REWRITE_TAC[has_type_rules];
    X_GEN_TAC `c:compute_exp` THEN DISCH_TAC THEN REWRITE_TAC[cexp2term_has_type] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:compute_exp` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_UNIONS; IN_SET_OF_LIST; MEM_MAP] THEN ASM_MESON_TAC[]]);;

let bool2term_term_ok = prove
 (`!thy b. bool_thy_ok thy ==> hol_term_ok (FST thy) (bool2term b)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[bool2term_def] THEN
  SIMP_TAC[bool_thy_ok_terms_ok]);;
let _ = cake_add_simps [bool2term_term_ok];;

let cexp_value_no_consts = prove
 (`!v. cexp_value v ==> cexp_consts v = {}`,
  MATCH_MP_TAC cexp_value_ind THEN
  SIMP_TAC[cexp_value_def; cexp_consts_def; UNION_EMPTY]);;

(* the values are numbers and pairs of values *)
let CMPSYNPAUX_cexp_value_cases = prove
 (`!q. cexp_value q ==>
       (?m. q = compute_Num m) \/
       (?a b. q = compute_Pair a b /\ cexp_value a /\ cexp_value b)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `q:compute_exp` (CONJUNCT1 (cases "compute_exp"))) THEN
  REWRITE_TAC[cexp_value_def; injectivity "compute_exp"; distinctness "compute_exp"] THEN
  MESON_TAC[]);;

let CMPSYNPAUX_value_term_ok = prove
 (`!thy v. compute_thy_ok thy /\ cexp_value v ==> hol_term_ok (FST thy) (cexp2term v)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP cexp2term_term_ok) THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[cexp_value_no_consts; NOT_IN_EMPTY]);;

let CMPSYNPAUX_EQ_cexpterm = prove
 (`!thy. compute_thy_ok thy ==>
     !p q. cexp_value p /\ cexp_value q ==>
       (thy,[]) |- (cexp2term p === cexp2term q) === bool2term (p = q)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC cexp2term_ind THEN
  REWRITE_TAC[cexp_value_def] THEN CONJ_TAC THENL
   [(* Num n *)
    X_GEN_TAC `n:num` THEN X_GEN_TAC `q:compute_exp` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o MATCH_MP CMPSYNPAUX_cexp_value_cases) THEN
    ASM_REWRITE_TAC[cexp2term_def; injectivity "compute_exp";
                    distinctness "compute_exp"; bool2term_def] THENL
     [CMPSYNPAUX_TRANS_TAC CEXP_EQ_eqn3 THEN
      MATCH_MP_TAC replaceL_eq1 THEN EXISTS_TAC `num2bit n` THEN CONJ_TAC THENL
       [MATCH_MP_TAC sym_equation THEN CMPSYNPAUX_EQN_TAC NUMERAL_eqn; ALL_TAC] THEN
      MATCH_MP_TAC replaceL_eq2 THEN EXISTS_TAC `num2bit m` THEN CONJ_TAC THENL
       [MATCH_MP_TAC sym_equation THEN CMPSYNPAUX_EQN_TAC NUMERAL_eqn;
        CMPSYNPAUX_EQN_TAC EQ_bool2term_num2bit];
      SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (cexp2term a) /\
                    hol_term_ok (FST thy) (cexp2term b)` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[CMPSYNPAUX_value_term_ok]; ALL_TAC] THEN
      CMPSYNPAUX_EQN_TAC CEXP_EQ_eqn4];
    ALL_TAC] THEN
  (* Pair p q *)
  MAP_EVERY X_GEN_TAC [`p:compute_exp`; `q:compute_exp`] THEN
  STRIP_TAC THEN X_GEN_TAC `r:compute_exp` THEN STRIP_TAC THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (cexp2term p) /\
                hol_term_ok (FST thy) (cexp2term q)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CMPSYNPAUX_value_term_ok]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o MATCH_MP CMPSYNPAUX_cexp_value_cases o
                check (fun th -> concl th = `cexp_value r`)) THEN
  ASM_REWRITE_TAC[cexp2term_def; injectivity "compute_exp";
                  distinctness "compute_exp"; bool2term_def] THENL
   [CMPSYNPAUX_EQN_TAC CEXP_EQ_eqn5; ALL_TAC] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (cexp2term a) /\
                hol_term_ok (FST thy) (cexp2term b)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CMPSYNPAUX_value_term_ok]; ALL_TAC] THEN
  CMPSYNPAUX_TRANS_TAC CEXP_EQ_eqn2 THEN
  MATCH_MP_TAC replaceL3 THEN EXISTS_TAC `bool2term ((p:compute_exp) = a)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC sym_equation THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `cexp2term p`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC replaceL1 THEN EXISTS_TAC `bool2term ((q:compute_exp) = b)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC sym_equation THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `cexp2term q`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `p:compute_exp = a` THEN ASM_CASES_TAC `q:compute_exp = b` THEN
  ASM_REWRITE_TAC[bool2term_def] THEN
  FIRST [CMPSYNPAUX_EQN_TAC (CMPSYNPAUX_cj 1 IF_eqn) THEN NO_TAC;
         CMPSYNPAUX_EQN_TAC (CMPSYNPAUX_cj 2 IF_eqn) THEN NO_TAC]);;

let bool2term_EQ_cexpterm = prove
 (`!thy p q.
     compute_thy_ok thy ==>
       cexp_value p /\ cexp_value q ==>
       (thy,[]) |- bool2term (p = q) === (cexp2term p === cexp2term q)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC sym_equation THEN
  ASM_SIMP_TAC[CMPSYNPAUX_EQ_cexpterm]);;

let EQ_bool2term_cexpterm = prove
 (`!thy p q.
     compute_thy_ok thy ==>
       cexp_value p /\ cexp_value q ==>
       (thy,[]) |- (cexp2term p === cexp2term q) === bool2term (p = q)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC sym_equation THEN
  ASM_SIMP_TAC[bool2term_EQ_cexpterm]);;

compute_overloads_off ();;
