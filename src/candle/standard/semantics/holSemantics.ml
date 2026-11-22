(* ========================================================================= *)
(* holSemantics: port of HOL4 candle/standard/semantics/holSemanticsScript   *)
(* .sml (CakeML v3479).  Semantics of HOL sequents, in particular the notion *)
(* of entailment, i.e. valid sequents, which are those satisfied by any      *)
(* model of the theory context.                                              *)
(*                                                                           *)
(* Notes on the rendering (also for the files that load this one):           *)
(* - HOL4 defines X0 ^mem ... with Overload X = X0 ^mem, for a variable      *)
(*   mem : U -> U -> bool.  HOL Light has no overloads with a variable: the  *)
(*   constants are written with their mem argument.  So HOL4's               *)
(*     is_type_assignment, is_type_valuation, is_term_assignment,           *)
(*     is_term_valuation, is_valuation, termsem, satisfies, is_interpretation, *)
(*     is_std_type_assignment, interprets, is_std_interpretation, models,     *)
(*     |= (entails), is_structure                                            *)
(*   are is_type_assignment0 mem, ..., termsem0 mem, satisfies0 mem, ...,    *)
(*   models0 mem, entails0 mem, is_structure0 mem.  HOL4's infix forms are   *)
(*   written as applications: i satisfies (sig,h,c) is                      *)
(*   satisfies0 mem i (sig,h,c), i models thy is models0 mem i thy,          *)
(*   (thy,h) |= c is entails0 mem (thy,h) c, and                             *)
(*   g interprets name on vs as f is interprets0 mem g name vs f.            *)
(* - The other HOL4 overloads are written out: inhabited s is ?x. mem x s;  *)
(*   tyaof i, tmaof i are FST i, SND i; tyvof v, tmvof v are FST v, SND v;   *)
(*   the setSpec ones as in setSpec.ml (x <: s is mem x s, Funspace s t is   *)
(*   funspace mem s t, boolset is two mem, True is setSpec_true mem,         *)
(*   Boolean b is boolean mem b, Abstract is abstract mem, f ' x is          *)
(*   apply mem f x, Holds s x is holds mem s x, s suchthat P is              *)
(*   setSpec_sub mem s P); the holSyntax ones as in holSyntax.ml (Fun, Bool, *)
(*   Equal, tysof, tmsof, sigof, axsof, ...); mlstring literals are          *)
(*   implode "...".                                                          *)
(* - The type abbreviations tyass, tyval, tmass, tmval, interpretation and   *)
(*   valuation have the type variable U, which HOL Light abbreviations       *)
(*   cannot have: they are written out at each use:                         *)
(*     tyass = tmass = mlstring -> U list -> U, tyval = mlstring -> U,       *)
(*     tmval = mlstring # hol_type -> U, interpretation = tyass # tmass,     *)
(*     valuation = tyval # tmval.                                            *)
(* - HOL4's Greek variable names: delta is dl (delta is a constant of the    *)
(*   library), tau, gamma, sigma; Gamma is G.                                *)
(* - Local helpers that are not HOL4 theorems are CSEMAUX_.                  *)
(* ========================================================================= *)

needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/set-theory/setSpec.ml";;

prioritize_num();;
type_invention_error := true;;

(* A type assignment is a map from type operator names to semantic functions.
   Each function takes a list of sets representing the meanings of the
   arguments and returns the meaning of the applied operator. The assignment is
   with respect to a type signature, and is only constrained for defined type
   operators applied to the right number of non-empty arguments. *)

(* HOL4: Definition is_type_assignment_def *)
let is_type_assignment0_def = cake_def
  `is_type_assignment0 (mem:U->U->bool) (tysig:tysig) (dl:mlstring->U list->U) <=>
     FEVERY (\(name,arity).
               !ls. LENGTH ls = arity /\ ALL (\s. ?x. mem x s) ls
                    ==> ?x. mem x (dl name ls))
            tysig`;;

(* A type valuation is a map from type variable names to non-empty sets. *)

(* HOL4: Definition is_type_valuation_def *)
let is_type_valuation0_def = cake_def
  `is_type_valuation0 (mem:U->U->bool) (tau:mlstring->U) <=> !x. ?y. mem y (tau x)`;;

(* Semantics of types. Simply applies the valuation and assignment. *)

let typesem_def = cake_def
  `(typesem (dl:mlstring->U list->U) (tau:mlstring->U) (Tyvar s) = tau s) /\
   (typesem dl tau (Tyapp name args) = dl name (MAP (typesem dl tau) args))`;;

let typesem_ind = cake_ind "typesem";;

(* A term assignment is a map from a constant name and a list of values for the
   free type variables to a value for the constant. The assignment is with
   respect to a signature and is only constrained for defined constants. *)

(* HOL4: Definition is_term_assignment_def *)
let is_term_assignment0_def = cake_def
  `is_term_assignment0 (mem:U->U->bool) (tmsig:tmsig) (dl:mlstring->U list->U)
                       (gamma:mlstring->U list->U) <=>
     FEVERY (\(name,ty).
               !tau. is_type_valuation0 mem tau
                     ==> mem (gamma name
                                (MAP tau (MAP implode (STRING_SORT (MAP explode (tyvars ty))))))
                             (typesem dl tau ty))
            tmsig`;;

(* A term valuation is a map from a variable to an element of its type. The
   result is not polymorphic: term valuations are specialised for particular
   type valuations. *)

(* HOL4: Definition is_term_valuation_def *)
let is_term_valuation0_def = cake_def
  `is_term_valuation0 (mem:U->U->bool) (tysig:tysig) (dl:mlstring->U list->U)
                      (tau:mlstring->U) (sigma:mlstring#hol_type->U) <=>
     !v ty. type_ok tysig ty ==> mem (sigma (v,ty)) (typesem dl tau ty)`;;

(* An interpretation is a pair of assignments.
   A valuation is a pair of valuations. *)

(* HOL4: Definition is_valuation_def *)
let is_valuation0_def = cake_def
  `is_valuation0 (mem:U->U->bool) (tysig:tysig) (dl:mlstring->U list->U)
                 (v:(mlstring->U)#(mlstring#hol_type->U)) <=>
     is_type_valuation0 mem (FST v) /\
     is_term_valuation0 mem tysig dl (FST v) (SND v)`;;

(* term assignment for instances of constants *)

(* The existence theorem of HOL4's new_specification instance_def.  The     *)
(* witness chooses the instantiation with Hilbert's choice; the value does  *)
(* not depend on the choice (TYPE_SUBST_tyvars).                            *)
let CSEMAUX_instance_exists = prove
 (`?f. !(tmsig:tmsig) (i:(mlstring->U list->U)#(mlstring->U list->U)) name ty ty0 tyin.
     FLOOKUP tmsig name = SOME ty0 /\ ty = TYPE_SUBST tyin ty0
     ==> f tmsig i name ty =
         \tau. SND i name
                 (MAP (typesem (FST i) tau o TYPE_SUBST tyin o Tyvar)
                      (MAP implode (STRING_SORT (MAP explode (tyvars ty0)))))`,
  EXISTS_TAC
   `\(tmsig:tmsig) (i:(mlstring->U list->U)#(mlstring->U list->U)) name ty (tau:mlstring->U).
      SND i name
        (MAP (typesem (FST i) tau o
              TYPE_SUBST (@tyin. ty = TYPE_SUBST tyin (THE (FLOOKUP tmsig name))) o Tyvar)
             (MAP implode (STRING_SORT (MAP explode (tyvars (THE (FLOOKUP tmsig name)))))))` THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[THE_DEF] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `tau:mlstring->U` THEN
  AP_TERM_TAC THEN REWRITE_TAC[MAP_EQ_f; o_THM] THEN
  X_GEN_TAC `x:mlstring` THEN
  REWRITE_TAC[GSYM IN_SET_OF_LIST; set_MAP_implode_STRING_SORT_MAP_explode] THEN
  REWRITE_TAC[IN_SET_OF_LIST] THEN DISCH_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[TYPE_SUBST_def] THEN
  SUBGOAL_THEN
   `TYPE_SUBST tyin ty0 =
    TYPE_SUBST (@tyin'. TYPE_SUBST tyin ty0 = TYPE_SUBST tyin' ty0) ty0`
   MP_TAC THENL
   [CONV_TAC SELECT_CONV THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[TYPE_SUBST_tyvars] THEN ASM_MESON_TAC[]);;

let instance_def = new_specification ["instance"] CSEMAUX_instance_exists;;

(* Semantics of terms. *)

(* HOL4: Definition termsem_def *)
let termsem0_def = cake_def
  `(termsem0 (mem:U->U->bool) (tmsig:tmsig)
             (i:(mlstring->U list->U)#(mlstring->U list->U))
             (v:(mlstring->U)#(mlstring#hol_type->U)) (hol_Var x ty) =
      SND v (x,ty)) /\
   (termsem0 mem tmsig i v (hol_Const name ty) = instance tmsig i name ty (FST v)) /\
   (termsem0 mem tmsig i v (hol_Comb t1 t2) =
      apply mem (termsem0 mem tmsig i v t1) (termsem0 mem tmsig i v t2)) /\
   (termsem0 mem tmsig i v (hol_Abs (hol_Var x ty) b) =
      abstract mem (typesem (FST i) (FST v) ty) (typesem (FST i) (FST v) (typeof b))
        (\m. termsem0 mem tmsig i (FST v, ((x,ty) =+ m) (SND v)) b))`;;

(* Satisfaction of sequents. *)

(* HOL4: Definition satisfies_def (HOL4 infix satisfies) *)
let satisfies0_def = cake_def
  `satisfies0 (mem:U->U->bool) (i:(mlstring->U list->U)#(mlstring->U list->U))
              ((sig:sig),(h:hol_term list),(c:hol_term)) <=>
     !v. is_valuation0 mem (FST sig) (FST i) v /\
         ALL (\t. termsem0 mem (SND sig) i v t = setSpec_true mem) h
         ==> termsem0 mem (SND sig) i v c = setSpec_true mem`;;

(* A interpretation of a theory is a pair of assignments to the constants and
   types in the theory. *)

(* HOL4: Definition is_interpretation_def *)
let is_interpretation0_def = cake_def
  `is_interpretation0 (mem:U->U->bool) (sig:sig)
                      (int:(mlstring->U list->U)#(mlstring->U list->U)) <=>
     is_type_assignment0 mem (FST sig) (FST int) /\
     is_term_assignment0 mem (SND sig) (FST int) (SND int)`;;

(* The assignments are standard if they interpret fun, bool, and = according
   to the standard model. *)

(* HOL4: Definition is_std_type_assignment_def *)
let is_std_type_assignment0_def = cake_def
  `is_std_type_assignment0 (mem:U->U->bool) (dl:mlstring->U list->U) <=>
     (!dom rng. dl (implode "fun") [dom; rng] = funspace mem dom rng) /\
     (dl (implode "bool") [] = two mem)`;;

(* HOL4: Definition interprets_def (HOL4 notation                            *)
(* gamma interprets name on vs as f)                                         *)
let interprets0_def = cake_def
  `interprets0 (mem:U->U->bool) (gamma:mlstring->U list->U) name vs f <=>
     !tau. is_type_valuation0 mem tau ==> gamma name (MAP tau vs) = f (MAP tau vs)`;;

(* HOL4: Definition is_std_interpretation_def *)
let is_std_interpretation0_def = cake_def
  `is_std_interpretation0 (mem:U->U->bool)
                          (i:(mlstring->U list->U)#(mlstring->U list->U)) <=>
     is_std_type_assignment0 mem (FST i) /\
     interprets0 mem (SND i) (implode "=") [implode "A"]
       (\l. abstract mem (HD l) (funspace mem (HD l) (two mem))
              (\x. abstract mem (HD l) (two mem) (\y. boolean mem (x = y))))`;;

(* A model of a theory is a standard interpretation that satisfies all the
   axioms. *)

(* HOL4: Definition models_def (HOL4 infix models) *)
let models0_def = cake_def
  `models0 (mem:U->U->bool) (i:(mlstring->U list->U)#(mlstring->U list->U)) (thy:thy) <=>
     is_interpretation0 mem (FST thy) i /\
     is_std_interpretation0 mem i /\
     !p. p IN SND thy ==> satisfies0 mem i (FST thy,[],p)`;;

(* Validity of sequents. *)

(* HOL4: Definition entails_def (HOL4 infix |=) *)
let entails0_def = cake_def
  `entails0 (mem:U->U->bool) ((thy:thy),(h:hol_term list)) (c:hol_term) <=>
     theory_ok thy /\
     ALL (hol_term_ok (FST thy)) (CONS c h) /\
     ALL (\p. p has_type Tyapp (implode "bool") []) (CONS c h) /\
     hypset_ok h /\
     !i. models0 mem i thy ==> satisfies0 mem i (FST thy,h,c)`;;

(* Collect standard signature, standard interpretation and valuation up in one
   predicate *)

(* HOL4: Definition is_structure_def (HOL4 variables sig int val; val is a   *)
(* constant here: v)                                                         *)
let is_structure0_def = cake_def
  `is_structure0 (mem:U->U->bool) (sig:sig)
                 (int:(mlstring->U list->U)#(mlstring->U list->U))
                 (v:(mlstring->U)#(mlstring#hol_type->U)) <=>
     is_std_sig sig /\
     is_std_interpretation0 mem int /\
     is_interpretation0 mem sig int /\
     is_valuation0 mem (FST sig) (FST int) v`;;
