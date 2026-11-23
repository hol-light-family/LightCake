(* ========================================================================= *)
(* holBool: port of HOL4 candle/standard/semantics/holBoolScript.sml         *)
(* (CakeML v3479).  Semantics for the Boolean operations, and proofs that    *)
(* the definitions of holBoolSyntax are correct.                             *)
(* ========================================================================= *)

needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/standard/syntax/holBoolSyntax.ml";;
needs "candle/standard/semantics/holSemantics.ml";;
needs "candle/standard/semantics/holSemanticsExtra.ml";;
needs "candle/set-theory/setSpec.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - As in holSemantics.ml (see its header): HOL4's X0 ^mem constants with   *)
(*   Overload X = X0 ^mem are written with their mem argument (Boolrel R is  *)
(*   Boolrel0 mem R, is_bool_interpretation i is is_bool_interpretation0 mem *)
(*   i, termsem is termsem0 mem, ...); the setSpec overloads as in setSpec.ml *)
(*   (x <: s is mem x s, boolset is setSpec_two mem, True and False are setSpec_true *)
(*   mem and setSpec_false mem, Boolean is boolean mem, Abstract is abstract *)
(*   mem, f ' x is setSpec_apply mem f x, Holds is setSpec_holds mem); tyaof, tmaof, tyvof,  *)
(*   tmvof are FST and SND; the HOL4 type abbreviations with U are written   *)
(*   out; HOL4's Greek variables are tau, sigma, gamma.                      *)
(* - The syntax overloads (True, And, Forall, ... of holBoolSyntax and the   *)
(*   local p, q, ...) are written out as in holBoolSyntax.ml.               *)
(* - Local helpers that are not HOL4 theorems are CBOOLAUX_.                 *)

(* HOL4: val sigs, the list of the signature definitions, is holBoolSyntax's *)
(* CBOOLAUX_sigs; the type variables of the constant types are computed by  *)
(* rewriting (HOL4: EVAL_TAC).                                               *)

let CBOOLAUX_TYVARS_THMS =
  [hol_tyvars_def; ITLIST; LIST_UNION_def; LIST_INSERT_def; MEM; STRING_SORT_def;
   INORDER_INSERT_def; FILTER; APPEND; MAP; explode_implode];;

let bool_sig_instances = prove
 (`is_bool_sig sig ==>
   instance (SND sig) (i:(mlstring->U list->U)#(mlstring->U list->U)) (implode "T")
     (Tyapp (implode "bool") []) = K (SND i (implode "T") []) /\
   instance (SND sig) i (implode "F")
     (Tyapp (implode "bool") []) = K (SND i (implode "F") []) /\
   instance (SND sig) i (implode "==>")
     (Tyapp (implode "fun") [Tyapp (implode "bool") [];
        Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]) =
     K (SND i (implode "==>") []) /\
   instance (SND sig) i (implode "/\\")
     (Tyapp (implode "fun") [Tyapp (implode "bool") [];
        Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]) =
     K (SND i (implode "/\\") []) /\
   instance (SND sig) i (implode "\\/")
     (Tyapp (implode "fun") [Tyapp (implode "bool") [];
        Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]) =
     K (SND i (implode "\\/") []) /\
   instance (SND sig) i (implode "~")
     (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]) =
     K (SND i (implode "~") []) /\
   instance (SND sig) i (implode "!")
     (Tyapp (implode "fun")
        [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
         Tyapp (implode "bool") []]) =
     (\tau. SND i (implode "!") [tau (implode "A")]) /\
   instance (SND sig) i (implode "?")
     (Tyapp (implode "fun")
        [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
         Tyapp (implode "bool") []]) =
     (\tau. SND i (implode "?") [tau (implode "A")])`,
  REWRITE_TAC(is_bool_sig_def :: CBOOLAUX_sigs) THEN STRIP_TAC THEN
  ASM_SIMP_TAC[identity_instance] THEN REWRITE_TAC[FUN_EQ_THM; K_THM] THEN
  REWRITE_TAC CBOOLAUX_TYVARS_THMS);;
(* HOL4: Definition Boolrel_def (Overload Boolrel = Boolrel0 ^mem) *)
let holBool_Boolrel0_def = cake_def
  `Boolrel0 (mem:U->U->bool) R =
     abstract mem (setSpec_two mem) (setSpec_funspace mem (setSpec_two mem) (setSpec_two mem))
       (\p. abstract mem (setSpec_two mem) (setSpec_two mem)
              (\q. boolean mem (R (p = setSpec_true mem) (q = setSpec_true mem))))`;;

(* HOL4: Definition is_true_interpretation_def *)
let is_true_interpretation0_def = cake_def
  `is_true_interpretation0 (mem:U->U->bool) (gamma:mlstring->U list->U) <=>
     interprets0 mem gamma (implode "T") [] (K (setSpec_true mem))`;;

(* HOL4: Definition is_and_interpretation_def *)
let is_and_interpretation0_def = cake_def
  `is_and_interpretation0 (mem:U->U->bool) (gamma:mlstring->U list->U) <=>
     interprets0 mem gamma (implode "/\\") [] (K (Boolrel0 mem (/\)))`;;

(* HOL4: Definition is_implies_interpretation_def *)
let is_implies_interpretation0_def = cake_def
  `is_implies_interpretation0 (mem:U->U->bool) (gamma:mlstring->U list->U) <=>
     interprets0 mem gamma (implode "==>") [] (K (Boolrel0 mem (==>)))`;;

(* HOL4: Definition is_forall_interpretation_def *)
let is_forall_interpretation0_def = cake_def
  `is_forall_interpretation0 (mem:U->U->bool) (gamma:mlstring->U list->U) <=>
     interprets0 mem gamma (implode "!") [implode "A"]
       (\l. abstract mem (setSpec_funspace mem (HD l) (setSpec_two mem)) (setSpec_two mem)
              (\P. boolean mem (!x. mem x (HD l) ==> setSpec_holds mem P x)))`;;

(* HOL4: Definition is_exists_interpretation_def *)
let is_exists_interpretation0_def = cake_def
  `is_exists_interpretation0 (mem:U->U->bool) (gamma:mlstring->U list->U) <=>
     interprets0 mem gamma (implode "?") [implode "A"]
       (\l. abstract mem (setSpec_funspace mem (HD l) (setSpec_two mem)) (setSpec_two mem)
              (\P. boolean mem (?x. mem x (HD l) /\ setSpec_holds mem P x)))`;;

(* HOL4: Definition is_or_interpretation_def *)
let is_or_interpretation0_def = cake_def
  `is_or_interpretation0 (mem:U->U->bool) (gamma:mlstring->U list->U) <=>
     interprets0 mem gamma (implode "\\/") [] (K (Boolrel0 mem (\/)))`;;

(* HOL4: Definition is_false_interpretation_def *)
let is_false_interpretation0_def = cake_def
  `is_false_interpretation0 (mem:U->U->bool) (gamma:mlstring->U list->U) <=>
     interprets0 mem gamma (implode "F") [] (K (setSpec_false mem))`;;

(* HOL4: Definition is_not_interpretation_def *)
let is_not_interpretation0_def = cake_def
  `is_not_interpretation0 (mem:U->U->bool) (gamma:mlstring->U list->U) <=>
     interprets0 mem gamma (implode "~") []
       (K (abstract mem (setSpec_two mem) (setSpec_two mem)
             (\p. boolean mem (~(p = setSpec_true mem)))))`;;

(* HOL4: val ints (an ML list) *)
let CBOOLAUX_ints =
  [is_true_interpretation0_def; is_and_interpretation0_def;
   is_implies_interpretation0_def; is_forall_interpretation0_def;
   is_exists_interpretation0_def; is_or_interpretation0_def;
   is_false_interpretation0_def; is_not_interpretation0_def];;

(* HOL4: Definition is_bool_interpretation_def *)
let is_bool_interpretation0_def = cake_def
  `is_bool_interpretation0 (mem:U->U->bool)
                           (i:(mlstring->U list->U)#(mlstring->U list->U)) <=>
     is_std_interpretation0 mem i /\
     is_true_interpretation0 mem (SND i) /\
     is_and_interpretation0 mem (SND i) /\
     is_implies_interpretation0 mem (SND i) /\
     is_forall_interpretation0 mem (SND i) /\
     is_exists_interpretation0 mem (SND i) /\
     is_or_interpretation0 mem (SND i) /\
     is_false_interpretation0 mem (SND i) /\
     is_not_interpretation0 mem (SND i)`;;

let boolrel_in_funspace = prove
 (`is_set_theory (mem:U->U->bool)
   ==> mem (Boolrel0 mem R)
           (setSpec_funspace mem (setSpec_two mem) (setSpec_funspace mem (setSpec_two mem) (setSpec_two mem)))`,
  DISCH_TAC THEN REWRITE_TAC[holBool_Boolrel0_def] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP abstract_in_funspace) THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP abstract_in_funspace) THEN
  ASM_SIMP_TAC[boolean_in_boolset]);;
let _ = cake_add_simps [boolrel_in_funspace];;

(* HOL4's ML values Defs, init_tac and apply_abstract_tac are replaced by    *)
(* the lemmas and tactics before bool_has_bool_interpretation below.        *)

let apply_boolrel = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !b1 b2 b3.
     mem b1 (setSpec_two mem) /\ mem b2 (setSpec_two mem) /\
     b3 = boolean mem (R (b1 = setSpec_true mem) (b2 = setSpec_true mem))
     ==> setSpec_apply mem (setSpec_apply mem (Boolrel0 mem R) b1) b2 = b3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `setSpec_apply mem (Boolrel0 mem R) b1 =
    abstract mem (setSpec_two mem) (setSpec_two mem)
      (\b2. boolean mem (R (b1 = setSpec_true mem) (b2 = setSpec_true (mem:U->U->bool))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[holBool_Boolrel0_def] THEN MATCH_MP_TAC apply_abstract_matchable THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP abstract_in_funspace) THEN
    ASM_SIMP_TAC[boolean_in_boolset];
    MATCH_MP_TAC apply_abstract_matchable THEN ASM_SIMP_TAC[boolean_in_boolset]]);;

(* The semantics of the Boolean connectives (HOL4 proves termsem_implies,    *)
(* termsem_forall, termsem_exists, termsem_and and termsem_not after         *)
(* extends_is_bool_interpretation; here they come first, since the proof of  *)
(* bool_has_bool_interpretation uses them).                                   *)

let CBOOLAUX_termsem_in_boolset = prove
 (`!(mem:U->U->bool) s i v p.
     is_set_theory mem /\
     is_valuation0 mem (FST s) (FST i) v /\
     is_interpretation0 mem s i /\
     is_std_type_assignment0 mem (FST i) /\
     hol_term_ok s p /\ typeof p = Tyapp (implode "bool") []
     ==> mem (termsem0 mem (SND s) i v p) (setSpec_two mem)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o ISPECL [`s:sig`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
    `p:hol_term`; `v:(mlstring->U)#(mlstring#hol_type->U)`;
    `FST(i:(mlstring->U list->U)#(mlstring->U list->U))`;
    `FST(v:(mlstring->U)#(mlstring#hol_type->U))`; `SND(s:sig)`; `setSpec_two(mem:U->U->bool)`] o
    MATCH_MP termsem_typesem_matchable) THEN
  ASM_SIMP_TAC[typesem_Bool]);;

let CBOOLAUX_interp_nil_value = prove
 (`!(mem:U->U->bool) gamma name f.
     is_set_theory mem /\ interprets0 mem gamma name [] f ==> gamma name [] = f []`,
  MESON_TAC[DISCH_ALL interprets_nil]);;

let CBOOLAUX_is_valuation_update = prove
 (`!(mem:U->U->bool) tys dl v x ty m.
     is_valuation0 mem tys dl v /\ mem m (typesem dl (FST v) ty)
     ==> is_valuation0 mem tys dl (FST v, ((x,ty) =+ m) (SND v))`,
  REWRITE_TAC[is_valuation0_def; is_term_valuation0_def; FST; SND; APPLY_UPDATE_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN ASM_MESON_TAC[]);;

let CBOOLAUX_is_valuation_update2 = prove
 (`!(mem:U->U->bool) tys dl tau sigma x ty m.
     is_valuation0 mem tys dl (tau,sigma) /\ mem m (typesem dl tau ty)
     ==> is_valuation0 mem tys dl (tau, ((x,ty) =+ m) sigma)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`mem:U->U->bool`; `tys:tysig`; `dl:mlstring->U list->U`;
                 `(tau:mlstring->U,sigma:mlstring#hol_type->U)`; `x:mlstring`; `ty:hol_type`;
                 `m:U`] CBOOLAUX_is_valuation_update) THEN
  ASM_REWRITE_TAC[FST; SND]);;

(* the instance of a constant of type (A -> bool) -> bool at y *)
let CBOOLAUX_instance_quant = prove
 (`!tmsig (i:(mlstring->U list->U)#(mlstring->U list->U)) c y tau.
     FLOOKUP tmsig c =
     SOME (Tyapp (implode "fun")
             [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
              Tyapp (implode "bool") []])
     ==> instance tmsig i c
           (Tyapp (implode "fun") [Tyapp (implode "fun") [y; Tyapp (implode "bool") []];
                                   Tyapp (implode "bool") []]) tau =
         SND i c [typesem (FST i) tau y]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tmsig:tmsig`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                 `c:mlstring`;
                 `Tyapp (implode "fun") [Tyapp (implode "fun") [y; Tyapp (implode "bool") []];
                                         Tyapp (implode "bool") []]`;
                 `Tyapp (implode "fun")
                    [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
                     Tyapp (implode "bool") []]`;
                 `[(y:hol_type,Tyvar (implode "A"))]`] instance_def) THEN
  ASM_REWRITE_TAC[TYPE_SUBST_def; MAP; REV_ASSOCD] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC(o_THM :: TYPE_SUBST_def :: REV_ASSOCD :: typesem_def :: CBOOLAUX_TYVARS_THMS));;

(* termsem_implies, termsem_and, termsem_not: the constant is interpreted    *)
(* by its value at [], the arguments are in boolset.                         *)
let CBOOLAUX_CONN_SEM_TAC sig_def int_def : tactic =
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[sig_def; int_def]) THEN
  ASM_SIMP_TAC[termsem0_def; identity_instance] THEN
  REWRITE_TAC CBOOLAUX_TYVARS_THMS THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[REWRITE_RULE[K_THM]
    (MATCH_MP CBOOLAUX_interp_nil_value (CONJ (ASSUME `is_set_theory (mem:U->U->bool)`) th))]) THEN
  TRY (FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP apply_boolrel) THEN
       REWRITE_TAC[] THEN CONJ_TAC) THEN
  TRY (MATCH_MP_TAC apply_abstract_matchable THEN ASM_SIMP_TAC[boolean_in_boolset]) THEN
  MATCH_MP_TAC CBOOLAUX_termsem_in_boolset THEN ASM_REWRITE_TAC[];;

let termsem_implies = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !s i v p1 p2.
     is_valuation0 mem (FST s) (FST i) v /\
     is_interpretation0 mem s i /\
     is_std_type_assignment0 mem (FST i) /\
     hol_term_ok s p1 /\ hol_term_ok s p2 /\
     typeof p1 = Tyapp (implode "bool") [] /\ typeof p2 = Tyapp (implode "bool") [] /\
     is_implies_sig (SND s) /\ is_implies_interpretation0 mem (SND i)
     ==> termsem0 mem (SND s) i v
           (hol_Comb (hol_Comb (hol_Const (implode "==>")
              (Tyapp (implode "fun") [Tyapp (implode "bool") [];
                 Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                        Tyapp (implode "bool") []]])) p1) p2) =
         boolean mem (termsem0 mem (SND s) i v p1 = setSpec_true mem ==>
                      termsem0 mem (SND s) i v p2 = setSpec_true mem)`,
  CBOOLAUX_CONN_SEM_TAC is_implies_sig_def is_implies_interpretation0_def);;

(* termsem_forall, termsem_exists: the constant is interpreted at           *)
(* typesem y, and the Abs is a function of funspace (typesem y) boolset.     *)
let CBOOLAUX_QUANT_TAC sig_def int_def : tactic =
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[sig_def; int_def; interprets_one]) THEN
  ASM_SIMP_TAC[termsem0_def; CBOOLAUX_instance_quant] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP is_std_interpretation_is_type) THEN
  SUBGOAL_THEN
   `?x. (mem:U->U->bool) x
          (typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))
                   (FST (v:(mlstring->U)#(mlstring#hol_type->U))) y)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP typesem_inhabited) THEN
    EXISTS_TAC `FST (s:sig)` THEN ASM_MESON_TAC[is_valuation0_def; is_interpretation0_def];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HD; typesem_Bool] THEN
  SUBGOAL_THEN
   `!m. mem m (typesem (FST (i:(mlstring->U list->U)#(mlstring->U list->U)))
                       (FST (v:(mlstring->U)#(mlstring#hol_type->U))) y)
        ==> mem (termsem0 (mem:U->U->bool) (SND (s:sig)) i
                   (FST v,((f,y) =+ m) (SND v)) b) (setSpec_two mem)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CBOOLAUX_termsem_in_boolset THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CBOOLAUX_is_valuation_update THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC apply_abstract_matchable THEN
  ASM_SIMP_TAC[boolean_in_boolset; abstract_in_funspace] THEN
  AP_TERM_TAC THEN REWRITE_TAC[setSpec_holds_def] THEN AP_TERM_TAC THEN ABS_TAC THEN
  FIRST [MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> ((a ==> b) <=> (a ==> c))`);
         MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`)] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[apply_abstract];;

let termsem_forall = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !s i v f y b.
     is_valuation0 mem (FST s) (FST i) v /\
     is_interpretation0 mem s i /\
     is_std_interpretation0 mem i /\
     type_ok (FST s) y /\ hol_term_ok s b /\ typeof b = Tyapp (implode "bool") [] /\
     is_forall_sig (SND s) /\ is_forall_interpretation0 mem (SND i)
     ==> termsem0 mem (SND s) i v
           (hol_Comb (hol_Const (implode "!")
              (Tyapp (implode "fun") [Tyapp (implode "fun") [y; Tyapp (implode "bool") []];
                                      Tyapp (implode "bool") []]))
              (hol_Abs (hol_Var f y) b)) =
         boolean mem (!x. mem x (typesem (FST i) (FST v) y)
                          ==> termsem0 mem (SND s) i (FST v, ((f,y) =+ x) (SND v)) b =
                              setSpec_true mem)`,
  CBOOLAUX_QUANT_TAC is_forall_sig_def is_forall_interpretation0_def);;

let termsem_exists = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !s i v f y b.
     is_valuation0 mem (FST s) (FST i) v /\
     is_interpretation0 mem s i /\
     is_std_interpretation0 mem i /\
     type_ok (FST s) y /\ hol_term_ok s b /\ typeof b = Tyapp (implode "bool") [] /\
     is_exists_sig (SND s) /\ is_exists_interpretation0 mem (SND i)
     ==> termsem0 mem (SND s) i v
           (hol_Comb (hol_Const (implode "?")
              (Tyapp (implode "fun") [Tyapp (implode "fun") [y; Tyapp (implode "bool") []];
                                      Tyapp (implode "bool") []]))
              (hol_Abs (hol_Var f y) b)) =
         boolean mem (?x. mem x (typesem (FST i) (FST v) y) /\
                          termsem0 mem (SND s) i (FST v, ((f,y) =+ x) (SND v)) b =
                          setSpec_true mem)`,
  CBOOLAUX_QUANT_TAC is_exists_sig_def is_exists_interpretation0_def);;

let termsem_and = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !s i v p1 p2.
     is_valuation0 mem (FST s) (FST i) v /\
     is_interpretation0 mem s i /\
     is_std_type_assignment0 mem (FST i) /\
     hol_term_ok s p1 /\ hol_term_ok s p2 /\
     typeof p1 = Tyapp (implode "bool") [] /\ typeof p2 = Tyapp (implode "bool") [] /\
     is_and_sig (SND s) /\ is_and_interpretation0 mem (SND i)
     ==> termsem0 mem (SND s) i v
           (hol_Comb (hol_Comb (hol_Const (implode "/\\")
              (Tyapp (implode "fun") [Tyapp (implode "bool") [];
                 Tyapp (implode "fun") [Tyapp (implode "bool") [];
                                        Tyapp (implode "bool") []]])) p1) p2) =
         boolean mem (termsem0 mem (SND s) i v p1 = setSpec_true mem /\
                      termsem0 mem (SND s) i v p2 = setSpec_true mem)`,
  CBOOLAUX_CONN_SEM_TAC is_and_sig_def is_and_interpretation0_def);;

let termsem_not = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !s i v p1.
     is_valuation0 mem (FST s) (FST i) v /\
     is_interpretation0 mem s i /\
     is_std_type_assignment0 mem (FST i) /\
     hol_term_ok s p1 /\
     typeof p1 = Tyapp (implode "bool") [] /\
     is_not_sig (SND s) /\ is_not_interpretation0 mem (SND i)
     ==> termsem0 mem (SND s) i v
           (hol_Comb (hol_Const (implode "~")
              (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]))
              p1) =
         boolean mem (~(termsem0 mem (SND s) i v p1 = setSpec_true mem))`,
  CBOOLAUX_CONN_SEM_TAC is_not_sig_def is_not_interpretation0_def);;

(* The proof of bool_has_bool_interpretation.  HOL4 proves the eight         *)
(* interpretations in order in one proof (init_tac, apply_abstract_tac);     *)
(* here each is a lemma about a model i of a theory thy with a Boolean       *)
(* signature that has the defining axiom of the constant (and the earlier    *)
(* interpretations): the axiom says that the constant means the termsem of   *)
(* its definition, which is computed by rewriting, with the termsem lemmas   *)
(* above for the connectives that the definition uses.                       *)

(* small facts of set theory *)

let CBOOLAUX_apply_boolrel = prove
 (`!(mem:U->U->bool) R b1 b2.
     is_set_theory mem /\ mem b1 (setSpec_two mem) /\ mem b2 (setSpec_two mem)
     ==> setSpec_apply mem (setSpec_apply mem (Boolrel0 mem R) b1) b2 =
         boolean mem (R (b1 = setSpec_true mem) (b2 = setSpec_true mem))`,
  MESON_TAC[apply_boolrel]);;

let CBOOLAUX_true_in_boolset = prove
 (`!(mem:U->U->bool). is_set_theory mem ==> mem (setSpec_true mem) (setSpec_two mem)`,
  MESON_TAC[mem_boolset]);;

let CBOOLAUX_false_in_boolset = prove
 (`!(mem:U->U->bool). is_set_theory mem ==> mem (setSpec_false mem) (setSpec_two mem)`,
  MESON_TAC[mem_boolset]);;

let CBOOLAUX_abstract_eq2 = prove
 (`!(mem:U->U->bool) s t f g.
     is_set_theory mem /\ (!x. mem x s ==> mem (g x) t /\ f x = g x)
     ==> abstract mem s t f = abstract mem s t g`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP abstract_eq) THEN
  ASM_MESON_TAC[]);;

(* AndDef: two functions of funspace boolset (funspace boolset boolset) are  *)
(* equal iff they agree on Boolrel (/\)                                       *)
let CBOOLAUX_and_sem = prove
 (`!(mem:U->U->bool) b1 b2.
     is_set_theory mem /\ mem b1 (setSpec_two mem) /\ mem b2 (setSpec_two mem)
     ==> (abstract mem (setSpec_funspace mem (setSpec_two mem) (setSpec_funspace mem (setSpec_two mem) (setSpec_two mem))) (setSpec_two mem)
            (\ff. setSpec_apply mem (setSpec_apply mem ff b1) b2) =
          abstract mem (setSpec_funspace mem (setSpec_two mem) (setSpec_funspace mem (setSpec_two mem) (setSpec_two mem))) (setSpec_two mem)
            (\ff. setSpec_apply mem (setSpec_apply mem ff (setSpec_true mem)) (setSpec_true mem)) <=>
          b1 = setSpec_true mem /\ b2 = setSpec_true mem)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(MP_TAC o C AP_THM `Boolrel0 (mem:U->U->bool) (/\)` o
             AP_TERM `setSpec_apply (mem:U->U->bool)`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CBOOLAUX_true_in_boolset) THEN
  SUBGOAL_THEN
   `!c1 c2. mem c1 (setSpec_two mem) /\ mem c2 (setSpec_two (mem:U->U->bool))
            ==> setSpec_apply mem (abstract mem (setSpec_funspace mem (setSpec_two mem) (setSpec_funspace mem (setSpec_two mem) (setSpec_two mem)))
                     (setSpec_two mem) (\ff. setSpec_apply mem (setSpec_apply mem ff c1) c2)) (Boolrel0 mem (/\)) =
                boolean mem (c1 = setSpec_true mem /\ c2 = setSpec_true mem)`
   (fun th -> ASM_SIMP_TAC[th]) THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC apply_abstract_matchable THEN
    ASM_SIMP_TAC[boolrel_in_funspace; CBOOLAUX_apply_boolrel; boolean_in_boolset];
    REWRITE_TAC[boolean_def] THEN ASM_MESON_TAC[true_neq_false]]);;

(* ImpliesDef *)
let CBOOLAUX_implies_sem = prove
 (`!(mem:U->U->bool) b1 b2.
     is_set_theory mem /\ mem b1 (setSpec_two mem) /\ mem b2 (setSpec_two mem)
     ==> (boolean mem (b1 = setSpec_true mem /\ b2 = setSpec_true mem) = b1 <=>
          (b1 = setSpec_true mem ==> b2 = setSpec_true mem))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `b1 = setSpec_true mem \/ b1 = setSpec_false (mem:U->U->bool)` MP_TAC
  THENL [ASM_MESON_TAC[mem_boolset]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[boolean_def] THEN ASM_MESON_TAC[true_neq_false]);;

(* ForallDef *)
let CBOOLAUX_forall_sem = prove
 (`!(mem:U->U->bool) s pp.
     is_set_theory mem /\ mem pp (setSpec_funspace mem s (setSpec_two mem))
     ==> (pp = abstract mem s (setSpec_two mem) (\x. setSpec_true mem) <=>
          !x. mem x s ==> setSpec_holds mem pp x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP in_funspace_abstract) THEN
  DISCH_THEN(MP_TAC o SPECL [`pp:U`; `s:U`; `setSpec_two (mem:U->U->bool)`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[setSpec_holds_def] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CBOOLAUX_true_in_boolset) THEN
  ASM_SIMP_TAC[apply_abstract] THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `x:U` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C AP_THM `x:U` o AP_TERM `setSpec_apply (mem:U->U->bool)`) THEN
    ASM_SIMP_TAC[apply_abstract];
    DISCH_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP abstract_eq) THEN
    ASM_SIMP_TAC[]]);;

(* syntax *)

let CBOOLAUX_VSUBST_id = prove
 (`!tm ilist. (!s' s. MEM (s',s) ilist ==> ~VFREE_IN s tm) ==> VSUBST ilist tm = tm`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[VSUBST_def] THEN
    MP_TAC(ISPECL [`ilist:(hol_term#hol_term)list`; `hol_Var a0 a1`; `hol_Var a0 a1`]
      REV_ASSOCD_MEM) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPECL
      [`REV_ASSOCD (hol_Var a0 a1) ilist (hol_Var a0 a1)`; `hol_Var a0 a1`]) THEN
    ASM_REWRITE_TAC[VFREE_IN_def];
    REWRITE_TAC[VSUBST_def];
    REWRITE_TAC[VSUBST_def; VFREE_IN_def; DE_MORGAN_THM; injectivity "hol_term"] THEN
    MESON_TAC[];
    DISCH_THEN(fun ih -> GEN_TAC THEN DISCH_TAC THEN MP_TAC (CONJUNCT2 ih)) THEN
    REWRITE_TAC[VSUBST_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `!s' s. MEM (s',s) (FILTER (\(s',s). ~(s = a0:hol_term))
                               (ilist:(hol_term#hol_term)list))
             ==> ~VFREE_IN s (a1:hol_term)`
    ASSUME_TAC THENL
     [REWRITE_TAC[MEM_FILTER] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`s':hol_term`; `s:hol_term`]) THEN
      ASM_REWRITE_TAC[VFREE_IN_def] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~EX (\(s',s). VFREE_IN (a0:hol_term) s' /\ VFREE_IN s (a1:hol_term))
                      (FILTER (\(s',s). ~(s = a0)) (ilist:(hol_term#hol_term)list))`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[NOT_EX; GSYM ALL_MEM; FORALL_PAIR_THM] THEN
      CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]]]);;

(* the axiom of a constant definition with a closed term *)
let CBOOLAUX_conexts_ConstDef = prove
 (`!n D. CLOSED D
         ==> conexts_of_upd (hol_ConstSpec [(n,D)] (hol_Var n (typeof D) === D)) =
             [hol_Const n (typeof D) === D]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[conexts_of_upd_def; MAP] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CONS_11] THEN
  SUBGOAL_THEN `VSUBST [hol_Const n (typeof D),hol_Var n (typeof D)] D = D` MP_TAC THENL
   [MATCH_MP_TAC CBOOLAUX_VSUBST_id THEN REWRITE_TAC[MEM; PAIR_EQ] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CLOSED_def]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[equation_def; VSUBST_def; REV_ASSOCD; typeof_def] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(* semantics *)

let CBOOLAUX_termsem_equation = prove
 (`!(mem:U->U->bool) sig i v s t.
     is_set_theory mem /\ is_structure0 mem sig i v /\ hol_term_ok sig (s === t)
     ==> termsem0 mem (SND sig) i v (s === t) =
         boolean mem (termsem0 mem (SND sig) i v s = termsem0 mem (SND sig) i v t)`,
  MESON_TAC[termsem_equation]);;

let CBOOLAUX_structure = prove
 (`!(mem:U->U->bool) thy i v.
     theory_ok thy /\ models0 mem i thy /\ is_valuation0 mem (FST (FST thy)) (FST i) v
     ==> is_structure0 mem (FST thy) i v`,
  SIMP_TAC[is_structure0_def; models0_def] THEN MESON_TAC[theory_ok_sig]);;

let CBOOLAUX_std_type_facts = prove
 (`!(mem:U->U->bool) i.
     is_std_interpretation0 mem i
     ==> (!dom rng. FST i (implode "fun") [dom; rng] = setSpec_funspace mem dom rng) /\
         FST i (implode "bool") [] = setSpec_two mem`,
  SIMP_TAC[is_std_interpretation0_def; is_std_type_assignment0_def]);;

(* a constant of a model: its value is the termsem of its definition *)
let CBOOLAUX_axiom_termsem = prove
 (`!(mem:U->U->bool) thy i v c ty D.
     is_set_theory mem /\ theory_ok thy /\ models0 mem i thy /\
     (hol_Const c ty === D) IN SND thy /\
     is_valuation0 mem (FST (FST thy)) (FST i) v
     ==> termsem0 mem (SND (FST thy)) i v (hol_Const c ty) =
         termsem0 mem (SND (FST thy)) i v D`,
  REPEAT STRIP_TAC THEN
  QPAT_ASSUM "models0 _ _ _" (STRIP_ASSUME_TAC o REWRITE_RULE[models0_def]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `hol_Const c ty === D`) THEN
  ASM_REWRITE_TAC[satisfies0_def; ALL] THEN
  DISCH_THEN(MP_TAC o SPEC `v:(mlstring->U)#(mlstring#hol_type->U)`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `hol_term_ok (FST (thy:thy)) (hol_Const c ty === D)` ASSUME_TAC THENL
   [ASM_MESON_TAC[theory_ok_def]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`FST (thy:thy)`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
     `v:(mlstring->U)#(mlstring#hol_type->U)`; `hol_Const c ty`; `D:hol_term`;
     `SND (FST (thy:thy))`] o MATCH_MP termsem_equation) THEN
  ASM_REWRITE_TAC[is_structure0_def] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[theory_ok_sig]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[boolean_eq_true]);;

let CBOOLAUX_interp_from_def = prove
 (`!(mem:U->U->bool) thy i n ty D f.
     is_set_theory mem /\ theory_ok thy /\ models0 mem i thy /\
     (hol_Const n ty === D) IN SND thy /\
     FLOOKUP (SND (FST thy)) n = SOME ty /\
     (!v. is_valuation0 mem (FST (FST thy)) (FST i) v
          ==> termsem0 mem (SND (FST thy)) i v D =
              f (MAP (FST v) (MAP implode (STRING_SORT (MAP explode (hol_tyvars ty))))))
     ==> interprets0 mem (SND i) n (MAP implode (STRING_SORT (MAP explode (hol_tyvars ty)))) f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[interprets0_def] THEN
  X_GEN_TAC `tau:mlstring->U` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?sigma. is_valuation0 (mem:U->U->bool) (FST (FST (thy:thy)))
                  (FST (i:(mlstring->U list->U)#(mlstring->U list->U))) (tau,sigma)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP term_valuation_exists) THEN
    ASM_MESON_TAC[models0_def; is_interpretation0_def];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(tau:mlstring->U,sigma:mlstring#hol_type->U)`) THEN
  ASM_REWRITE_TAC[FST] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`mem:U->U->bool`; `thy:thy`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                 `(tau:mlstring->U,sigma:mlstring#hol_type->U)`; `n:mlstring`; `ty:hol_type`;
                 `D:hol_term`] CBOOLAUX_axiom_termsem) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[termsem0_def; identity_instance; FST]);;

(* tactics *)

let CBOOLAUX_STRING_THMS =
  [injectivity "mlstring"; injectivity "char"; CONS_11; NOT_CONS_NIL; GSYM NOT_CONS_NIL;
   PAIR_EQ; injectivity "hol_type"];;

let CBOOLAUX_EVAL_SEM_THMS =
  [termsem0_def; typesem_def; MAP; typeof_def; codomain_def; CSYNAUX_typeof_equation;
   FST; SND; APPLY_UPDATE_THM; K_THM; HD] @ CBOOLAUX_STRING_THMS;;

(* hol_term_ok in a Boolean signature (the assumption is_bool_sig sig) *)
let CBOOLAUX_TERM_OK_TAC : tactic =
  FIRST_ASSUM(fun th ->
    let bt = MATCH_MP bool_term_ok th in
    let cl = MATCH_MP term_ok_clauses (MATCH_MP is_bool_sig_std th) in
    REWRITE_TAC[bt; cl; typeof_def; codomain_def; CSYNAUX_typeof_equation]) THEN
  ASM_REWRITE_TAC[];;

(* the facts of a model of a theory with a Boolean signature, as assumptions *)
let CBOOLAUX_SETUP_TAC : tactic =
  QPAT_ASSUM "models0 _ _ _" (STRIP_ASSUME_TAC o REWRITE_RULE[models0_def]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CBOOLAUX_std_type_facts o
              check (fun th -> can (term_match [] `is_std_interpretation0 (mem:U->U->bool) i`)
                                   (concl th))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP is_std_interpretation_is_type o
              check (fun th -> can (term_match [] `is_std_interpretation0 (mem:U->U->bool) i`)
                                   (concl th))) THEN
  QPAT_ASSUM "is_bool_sig _" (fun th ->
    ASSUME_TAC (MATCH_MP bool_sig_instances th) THEN
    STRIP_ASSUME_TAC (REWRITE_RULE[is_bool_sig_def] th));;

(* for a goal termsem0 mem tmenv i vv tm = _ : vv is a valuation and tm is ok *)
let CBOOLAUX_VAL_OK_TAC : tactic =
  W(fun (asl,w) ->
     let tm = rand(lhs w) in
     let vv = rand(rator(lhs w)) in
     SUBGOAL_THEN (list_mk_comb(`is_valuation0 (mem:U->U->bool)`,
                    [`FST (FST (thy:thy))`;
                     `FST (i:(mlstring->U list->U)#(mlstring->U list->U))`; vv]))
       ASSUME_TAC THENL
      [ASM_SIMP_TAC[CBOOLAUX_is_valuation_update2; PAIR; typesem_def; MAP];
       SUBGOAL_THEN (mk_comb(`hol_term_ok (FST (thy:thy))`, tm)) ASSUME_TAC THENL
        [CBOOLAUX_TERM_OK_TAC THEN REWRITE_TAC[WELLTYPED_CLAUSES; typeof_def; codomain_def] THEN
         REWRITE_TAC CBOOLAUX_STRING_THMS THEN MESON_TAC[];
         ALL_TAC]]);;

(* the termsem lemmas of the connectives, with their side conditions *)
let CBOOLAUX_SEM_SIMP_TAC thl : tactic =
  W(fun (asl,w) ->
    let st = find (fun th -> can (term_match [] `is_set_theory (mem:U->U->bool)`) (concl th))
                  (map snd asl) in
    let bs = find (fun th -> can (term_match [] `is_bool_sig (sig:sig)`) (concl th))
                  (map snd asl) in
    let cl = MATCH_MP term_ok_clauses (MATCH_MP is_bool_sig_std bs) in
    let bt = MATCH_MP bool_term_ok bs in
    let sems = map (fun th -> MATCH_MP th st)
                 [termsem_and; termsem_implies; termsem_forall; termsem_exists; termsem_not] in
    ASM_SIMP_TAC(sems @ [cl; bt; typeof_def; codomain_def; CSYNAUX_typeof_equation;
                         WELLTYPED_CLAUSES; injectivity "hol_type"; CONS_11;
                         RIGHT_EXISTS_AND_THM; CBOOLAUX_EXISTS_REFL; UNWIND_THM1] @ thl));;

let CBOOLAUX_BOOLEAN_TAC : tactic =
  W(fun (asl,w) ->
    let st = find (fun th -> can (term_match [] `is_set_theory (mem:U->U->bool)`) (concl th))
                  (map snd asl) in
    REWRITE_TAC[MATCH_MP boolean_eq_true st]);;

(* the logic at the end of the proofs for ?, \/, F, ~: a quantified Boolean *)
(* variable ranges over True and False                                      *)
let CBOOLAUX_TRUTH_TAC : tactic =
  FIRST_ASSUM(fun st -> if can (term_match [] `is_set_theory (mem:U->U->bool)`) (concl st)
    then ASSUME_TAC (MATCH_MP CBOOLAUX_false_in_boolset st) THEN
         ASSUME_TAC (MATCH_MP CBOOLAUX_true_in_boolset st) THEN
         ASSUME_TAC (MATCH_MP true_neq_false st)
    else failwith "CBOOLAUX_TRUTH_TAC") THEN
  ASM_MESON_TAC[];;

(* the start of the proofs for each constant n of type ty defined by d and   *)
(* interpreted as f: the goal becomes termsem0 mem (SND (FST thy)) i v d =   *)
(* f [..] for a valuation v, with the assumptions of CBOOLAUX_SETUP_TAC      *)
let CBOOLAUX_CONN_START_TAC n ty d f sigdef intdef : tactic =
  REPEAT STRIP_TAC THEN REWRITE_TAC[intdef] THEN
  MP_TAC(ISPECL [`mem:U->U->bool`; `thy:thy`; `i:(mlstring->U list->U)#(mlstring->U list->U)`;
                 n; ty; d; f] CBOOLAUX_interp_from_def) THEN
  REWRITE_TAC CBOOLAUX_TYVARS_THMS THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[K_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[is_bool_sig_def; sigdef]; ALL_TAC] THEN
  X_GEN_TAC `v:(mlstring->U)#(mlstring#hol_type->U)` THEN DISCH_TAC THEN
  CBOOLAUX_SETUP_TAC;;

(* the value of a constant interpreted as K c *)
let CBOOLAUX_VALUE_TAC name c intdef : tactic =
  SUBGOAL_THEN (mk_eq(mk_comb(mk_comb(`SND (i:(mlstring->U list->U)#(mlstring->U list->U))`,
                  name), `[]:U list`), c)) ASSUME_TAC THENL
   [MP_TAC(ISPECL [`mem:U->U->bool`; `SND (i:(mlstring->U list->U)#(mlstring->U list->U))`;
                   name; mk_comb(mk_const("K",[`:U`,`:A`; `:U list`,`:B`]), c)]
      CBOOLAUX_interp_nil_value) THEN
    ASM_REWRITE_TAC[GSYM intdef; K_THM];
    ALL_TAC];;

(* the eight constants *)

let CBOOLAUX_true_interp = prove
 (`!(mem:U->U->bool) thy i.
     is_set_theory mem /\ theory_ok thy /\ models0 mem i thy /\ is_bool_sig (FST thy) /\
     (hol_Const (implode "T") (Tyapp (implode "bool") []) === TrueDef) IN SND thy
     ==> is_true_interpretation0 mem (SND i)`,
  CBOOLAUX_CONN_START_TAC `implode "T"` `Tyapp (implode "bool") []`
    `TrueDef` `K (setSpec_true (mem:U->U->bool)):U list->U`
    is_true_sig_def is_true_interpretation0_def THEN
  REWRITE_TAC[TrueDef_def] THEN CBOOLAUX_VAL_OK_TAC THEN
  ASM_SIMP_TAC[CBOOLAUX_termsem_equation; CBOOLAUX_structure] THEN
  REWRITE_TAC[boolean_def]);;

let CBOOLAUX_and_interp = prove
 (`!(mem:U->U->bool) thy i.
     is_set_theory mem /\ theory_ok thy /\ models0 mem i thy /\ is_bool_sig (FST thy) /\
     is_true_interpretation0 mem (SND i) /\
     (hol_Const (implode "/\\")
        (Tyapp (implode "fun") [Tyapp (implode "bool") [];
           Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])
      === AndDef) IN SND thy
     ==> is_and_interpretation0 mem (SND i)`,
  CBOOLAUX_CONN_START_TAC `implode "/\\"`
    `Tyapp (implode "fun") [Tyapp (implode "bool") [];
       Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]`
    `AndDef` `K (Boolrel0 (mem:U->U->bool) (/\)):U list->U`
    is_and_sig_def is_and_interpretation0_def THEN
  CBOOLAUX_VALUE_TAC `implode "T"` `setSpec_true (mem:U->U->bool)`
    is_true_interpretation0_def THEN
  REWRITE_TAC[AndDef_def; holBool_Boolrel0_def] THEN
  ASM_REWRITE_TAC[termsem0_def; typesem_def; MAP; typeof_def; codomain_def;
                  CSYNAUX_typeof_equation] THEN
  MATCH_MP_TAC CBOOLAUX_abstract_eq2 THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `b1:U` THEN DISCH_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[abstract_in_funspace; boolean_in_boolset] THEN
  MATCH_MP_TAC CBOOLAUX_abstract_eq2 THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `b2:U` THEN DISCH_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[boolean_in_boolset] THEN CBOOLAUX_VAL_OK_TAC THEN
  ASM_SIMP_TAC[CBOOLAUX_termsem_equation; CBOOLAUX_structure] THEN
  ASM_REWRITE_TAC CBOOLAUX_EVAL_SEM_THMS THEN
  ASM_SIMP_TAC[CBOOLAUX_and_sem]);;

let CBOOLAUX_implies_interp = prove
 (`!(mem:U->U->bool) thy i.
     is_set_theory mem /\ theory_ok thy /\ models0 mem i thy /\ is_bool_sig (FST thy) /\
     is_and_interpretation0 mem (SND i) /\
     (hol_Const (implode "==>")
        (Tyapp (implode "fun") [Tyapp (implode "bool") [];
           Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])
      === ImpliesDef) IN SND thy
     ==> is_implies_interpretation0 mem (SND i)`,
  CBOOLAUX_CONN_START_TAC `implode "==>"`
    `Tyapp (implode "fun") [Tyapp (implode "bool") [];
       Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]`
    `ImpliesDef` `K (Boolrel0 (mem:U->U->bool) (==>)):U list->U`
    is_implies_sig_def is_implies_interpretation0_def THEN
  REWRITE_TAC[ImpliesDef_def; holBool_Boolrel0_def] THEN
  ASM_REWRITE_TAC CBOOLAUX_EVAL_SEM_THMS THEN
  MATCH_MP_TAC CBOOLAUX_abstract_eq2 THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `b1:U` THEN DISCH_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[abstract_in_funspace; boolean_in_boolset] THEN
  MATCH_MP_TAC CBOOLAUX_abstract_eq2 THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `b2:U` THEN DISCH_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[boolean_in_boolset] THEN CBOOLAUX_VAL_OK_TAC THEN
  ASM_SIMP_TAC[CBOOLAUX_termsem_equation; CBOOLAUX_structure] THEN
  CBOOLAUX_SEM_SIMP_TAC [] THEN
  ASM_REWRITE_TAC CBOOLAUX_EVAL_SEM_THMS THEN ASM_SIMP_TAC[CBOOLAUX_implies_sem]);;

let CBOOLAUX_forall_interp = prove
 (`!(mem:U->U->bool) thy i.
     is_set_theory mem /\ theory_ok thy /\ models0 mem i thy /\ is_bool_sig (FST thy) /\
     is_true_interpretation0 mem (SND i) /\
     (hol_Const (implode "!")
        (Tyapp (implode "fun")
           [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
            Tyapp (implode "bool") []])
      === ForallDef) IN SND thy
     ==> is_forall_interpretation0 mem (SND i)`,
  CBOOLAUX_CONN_START_TAC `implode "!"`
    `Tyapp (implode "fun")
       [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
        Tyapp (implode "bool") []]`
    `ForallDef`
    `\l. abstract (mem:U->U->bool) (setSpec_funspace mem (HD l) (setSpec_two mem)) (setSpec_two mem)
           (\P. boolean mem (!x. mem x (HD l) ==> setSpec_holds mem P x))`
    is_forall_sig_def is_forall_interpretation0_def THEN
  CBOOLAUX_VALUE_TAC `implode "T"` `setSpec_true (mem:U->U->bool)`
    is_true_interpretation0_def THEN
  REWRITE_TAC[ForallDef_def] THEN
  ASM_REWRITE_TAC CBOOLAUX_EVAL_SEM_THMS THEN
  MATCH_MP_TAC CBOOLAUX_abstract_eq2 THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `pp:U` THEN DISCH_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[boolean_in_boolset] THEN CBOOLAUX_VAL_OK_TAC THEN
  ASM_SIMP_TAC[CBOOLAUX_termsem_equation; CBOOLAUX_structure] THEN
  ASM_REWRITE_TAC CBOOLAUX_EVAL_SEM_THMS THEN
  AP_TERM_TAC THEN MATCH_MP_TAC CBOOLAUX_forall_sem THEN ASM_REWRITE_TAC[]);;
let CBOOLAUX_exists_interp = prove
 (`!(mem:U->U->bool) thy i.
     is_set_theory mem /\ theory_ok thy /\ models0 mem i thy /\ is_bool_sig (FST thy) /\
     is_implies_interpretation0 mem (SND i) /\ is_forall_interpretation0 mem (SND i) /\
     (hol_Const (implode "?")
        (Tyapp (implode "fun")
           [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
            Tyapp (implode "bool") []])
      === ExistsDef) IN SND thy
     ==> is_exists_interpretation0 mem (SND i)`,
  CBOOLAUX_CONN_START_TAC `implode "?"`
    `Tyapp (implode "fun")
       [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
        Tyapp (implode "bool") []]`
    `ExistsDef`
    `\l. abstract (mem:U->U->bool) (setSpec_funspace mem (HD l) (setSpec_two mem)) (setSpec_two mem)
           (\P. boolean mem (?x. mem x (HD l) /\ setSpec_holds mem P x))`
    is_exists_sig_def is_exists_interpretation0_def THEN
  REWRITE_TAC[ExistsDef_def] THEN ONCE_REWRITE_TAC[termsem0_def] THEN
  ASM_REWRITE_TAC [typesem_def; MAP; typeof_def; codomain_def; HD] THEN
  MATCH_MP_TAC CBOOLAUX_abstract_eq2 THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `pp:U` THEN DISCH_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[boolean_in_boolset] THEN CBOOLAUX_VAL_OK_TAC THEN
  CBOOLAUX_SEM_SIMP_TAC [CBOOLAUX_is_valuation_update2; typesem_def; MAP] THEN
  CBOOLAUX_BOOLEAN_TAC THEN ASM_REWRITE_TAC CBOOLAUX_EVAL_SEM_THMS THEN
  AP_TERM_TAC THEN REWRITE_TAC[setSpec_holds_def] THEN CBOOLAUX_TRUTH_TAC);;

let CBOOLAUX_or_interp = prove
 (`!(mem:U->U->bool) thy i.
     is_set_theory mem /\ theory_ok thy /\ models0 mem i thy /\ is_bool_sig (FST thy) /\
     is_implies_interpretation0 mem (SND i) /\ is_forall_interpretation0 mem (SND i) /\
     (hol_Const (implode "\\/")
        (Tyapp (implode "fun") [Tyapp (implode "bool") [];
           Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])
      === OrDef) IN SND thy
     ==> is_or_interpretation0 mem (SND i)`,
  CBOOLAUX_CONN_START_TAC `implode "\\/"`
    `Tyapp (implode "fun") [Tyapp (implode "bool") [];
       Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]]`
    `OrDef` `K (Boolrel0 (mem:U->U->bool) (\/)):U list->U`
    is_or_sig_def is_or_interpretation0_def THEN
  REWRITE_TAC[OrDef_def; holBool_Boolrel0_def] THEN ONCE_REWRITE_TAC[termsem0_def] THEN
  ASM_REWRITE_TAC [typesem_def; MAP; typeof_def; codomain_def; HD] THEN
  MATCH_MP_TAC CBOOLAUX_abstract_eq2 THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `b1:U` THEN DISCH_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[abstract_in_funspace; boolean_in_boolset] THEN
  ONCE_REWRITE_TAC[termsem0_def] THEN
  ASM_REWRITE_TAC [typesem_def; MAP; typeof_def; codomain_def; HD] THEN
  MATCH_MP_TAC CBOOLAUX_abstract_eq2 THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `b2:U` THEN DISCH_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[boolean_in_boolset] THEN CBOOLAUX_VAL_OK_TAC THEN
  CBOOLAUX_SEM_SIMP_TAC [CBOOLAUX_is_valuation_update2; typesem_def; MAP] THEN
  CBOOLAUX_BOOLEAN_TAC THEN ASM_REWRITE_TAC CBOOLAUX_EVAL_SEM_THMS THEN
  AP_TERM_TAC THEN CBOOLAUX_TRUTH_TAC);;

let CBOOLAUX_false_interp = prove
 (`!(mem:U->U->bool) thy i.
     is_set_theory mem /\ theory_ok thy /\ models0 mem i thy /\ is_bool_sig (FST thy) /\
     is_forall_interpretation0 mem (SND i) /\
     (hol_Const (implode "F") (Tyapp (implode "bool") []) === FalseDef) IN SND thy
     ==> is_false_interpretation0 mem (SND i)`,
  CBOOLAUX_CONN_START_TAC `implode "F"` `Tyapp (implode "bool") []`
    `FalseDef` `K (setSpec_false (mem:U->U->bool)):U list->U`
    is_false_sig_def is_false_interpretation0_def THEN
  REWRITE_TAC[FalseDef_def] THEN
  CBOOLAUX_SEM_SIMP_TAC [CBOOLAUX_is_valuation_update2; typesem_def; MAP] THEN
  ASM_REWRITE_TAC CBOOLAUX_EVAL_SEM_THMS THEN
  REWRITE_TAC[boolean_def] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN CBOOLAUX_TRUTH_TAC);;

let CBOOLAUX_not_interp = prove
 (`!(mem:U->U->bool) thy i.
     is_set_theory mem /\ theory_ok thy /\ models0 mem i thy /\ is_bool_sig (FST thy) /\
     is_implies_interpretation0 mem (SND i) /\ is_false_interpretation0 mem (SND i) /\
     (hol_Const (implode "~")
        (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []])
      === NotDef) IN SND thy
     ==> is_not_interpretation0 mem (SND i)`,
  CBOOLAUX_CONN_START_TAC `implode "~"`
    `Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]`
    `NotDef`
    `K (abstract (mem:U->U->bool) (setSpec_two mem) (setSpec_two mem)
          (\p. boolean mem (~(p = setSpec_true mem)))):U list->U`
    is_not_sig_def is_not_interpretation0_def THEN
  CBOOLAUX_VALUE_TAC `implode "F"` `setSpec_false (mem:U->U->bool)`
    is_false_interpretation0_def THEN
  REWRITE_TAC[NotDef_def] THEN ONCE_REWRITE_TAC[termsem0_def] THEN
  ASM_REWRITE_TAC [typesem_def; MAP; typeof_def; codomain_def; HD] THEN
  MATCH_MP_TAC CBOOLAUX_abstract_eq2 THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `b:U` THEN DISCH_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[boolean_in_boolset] THEN CBOOLAUX_VAL_OK_TAC THEN
  CBOOLAUX_SEM_SIMP_TAC [CBOOLAUX_is_valuation_update2; typesem_def; MAP] THEN
  ASM_REWRITE_TAC CBOOLAUX_EVAL_SEM_THMS THEN
  AP_TERM_TAC THEN CBOOLAUX_TRUTH_TAC);;

let CBOOLAUX_bool_interp_thy = prove
 (`!(mem:U->U->bool) thy i.
     is_set_theory mem /\ theory_ok thy /\ models0 mem i thy /\ is_bool_sig (FST thy) /\
     (hol_Const (implode "T") (Tyapp (implode "bool") []) === TrueDef) IN SND thy /\
     (hol_Const (implode "/\\")
        (Tyapp (implode "fun") [Tyapp (implode "bool") [];
           Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])
      === AndDef) IN SND thy /\
     (hol_Const (implode "==>")
        (Tyapp (implode "fun") [Tyapp (implode "bool") [];
           Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])
      === ImpliesDef) IN SND thy /\
     (hol_Const (implode "!")
        (Tyapp (implode "fun")
           [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
            Tyapp (implode "bool") []])
      === ForallDef) IN SND thy /\
     (hol_Const (implode "?")
        (Tyapp (implode "fun")
           [Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []];
            Tyapp (implode "bool") []])
      === ExistsDef) IN SND thy /\
     (hol_Const (implode "\\/")
        (Tyapp (implode "fun") [Tyapp (implode "bool") [];
           Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []]])
      === OrDef) IN SND thy /\
     (hol_Const (implode "F") (Tyapp (implode "bool") []) === FalseDef) IN SND thy /\
     (hol_Const (implode "~")
        (Tyapp (implode "fun") [Tyapp (implode "bool") []; Tyapp (implode "bool") []])
      === NotDef) IN SND thy
     ==> is_bool_interpretation0 mem i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[is_bool_interpretation0_def] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[models0_def]; ALL_TAC] THEN
  MAP_EVERY (fun th ->
    SUBGOAL_THEN (rand(snd(strip_forall(concl th)))) ASSUME_TAC THENL
     [MATCH_MP_TAC th THEN EXISTS_TAC `thy:thy` THEN ASM_REWRITE_TAC[]; ALL_TAC])
   [CBOOLAUX_true_interp; CBOOLAUX_and_interp; CBOOLAUX_implies_interp;
    CBOOLAUX_forall_interp; CBOOLAUX_exists_interp; CBOOLAUX_or_interp;
    CBOOLAUX_false_interp; CBOOLAUX_not_interp] THEN
  ASM_REWRITE_TAC[]);;

let CBOOLAUX_defs_CLOSED = prove
 (`CLOSED TrueDef /\ CLOSED AndDef /\ CLOSED ImpliesDef /\ CLOSED ForallDef /\
   CLOSED ExistsDef /\ CLOSED OrDef /\ CLOSED FalseDef /\ CLOSED NotDef`,
  REPEAT CONJ_TAC THEN CBOOLAUX_CLOSED_TAC);;

let CBOOLAUX_bool_ctxt_std_sig = prove
 (`!ctxt. is_std_sig (alist_to_fmap (FLAT (MAP types_of_upd (mk_bool_ctxt ctxt))),
                      alist_to_fmap (FLAT (MAP consts_of_upd (mk_bool_ctxt ctxt))))
          ==> is_std_sig (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                          alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))`,
  GEN_TAC THEN REWRITE_TAC[is_std_sig_def; mk_bool_ctxt_def; FST; SND] THEN
  CBOOLAUX_EVAL CBOOLAUX_TERM_THMS);;

let bool_has_bool_interpretation = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !ctxt i.
     theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd (mk_bool_ctxt ctxt))),
                 alist_to_fmap (FLAT (MAP consts_of_upd (mk_bool_ctxt ctxt)))),
                set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                     (conexts_of_upd upd))
                                       (mk_bool_ctxt ctxt)))) /\
     models0 mem i
       ((alist_to_fmap (FLAT (MAP types_of_upd (mk_bool_ctxt ctxt))),
         alist_to_fmap (FLAT (MAP consts_of_upd (mk_bool_ctxt ctxt)))),
        set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                               (mk_bool_ctxt ctxt))))
     ==> is_bool_interpretation0 mem i`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CBOOLAUX_bool_interp_thy THEN
  EXISTS_TAC
   `(alist_to_fmap (FLAT (MAP types_of_upd (mk_bool_ctxt ctxt))),
     alist_to_fmap (FLAT (MAP consts_of_upd (mk_bool_ctxt ctxt)))),
    set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                           (mk_bool_ctxt ctxt)))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[FST] THEN MATCH_MP_TAC bool_has_bool_sig THEN
    MATCH_MP_TAC CBOOLAUX_bool_ctxt_std_sig THEN
    FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[FST] o MATCH_MP theory_ok_sig);
    ALL_TAC] THEN
  REWRITE_TAC([SND; mk_bool_ctxt_def; MAP; FLAT; APPEND; axexts_of_upd_def;
               IN_SET_OF_LIST; MEM_APPEND; MEM] @
              map (MATCH_MP CBOOLAUX_conexts_ConstDef) (CONJUNCTS CBOOLAUX_defs_CLOSED)) THEN
  REWRITE_TAC(CBOOLAUX_defs @ [typeof_def; codomain_def; CSYNAUX_typeof_equation]));;

let extends_is_bool_interpretation = prove
 (`is_set_theory (mem:U->U->bool) /\
   ctxt2 extends (mk_bool_ctxt ctxt) /\
   theory_ok ((alist_to_fmap (FLAT (MAP types_of_upd (mk_bool_ctxt ctxt))),
               alist_to_fmap (FLAT (MAP consts_of_upd (mk_bool_ctxt ctxt)))),
              set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                   (conexts_of_upd upd))
                                     (mk_bool_ctxt ctxt)))) /\
   models0 mem i
     ((alist_to_fmap (FLAT (MAP types_of_upd ctxt2)),
       alist_to_fmap (FLAT (MAP consts_of_upd ctxt2))),
      set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                             ctxt2)))
   ==> is_bool_interpretation0 mem i`,
  STRIP_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP bool_has_bool_interpretation) THEN
  EXISTS_TAC `ctxt:update list` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP models_reduce) THEN
  MAP_EVERY EXISTS_TAC
   [`alist_to_fmap (FLAT (MAP types_of_upd ctxt2))`;
    `alist_to_fmap (FLAT (MAP consts_of_upd ctxt2))`;
    `set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd upd))
                            ctxt2))`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP extends_sub) THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[FST] o MATCH_MP theory_ok_sig);
    RULE_ASSUM_TAC(REWRITE_RULE[theory_ok_def; FST; SND]) THEN ASM_MESON_TAC[]]);;
