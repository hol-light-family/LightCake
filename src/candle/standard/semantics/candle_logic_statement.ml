(* ========================================================================= *)
(* The headline statements of the logic part of Candle in the HOL Light     *)
(* port of CakeML v3479 (HOL in HOL: the syntax and semantics of HOL, its   *)
(* soundness and the consistency of its theories), HOL4                     *)
(*   proves_sound          candle/standard/semantics/holSoundnessScript.sml  *)
(*   extends_consistent    candle/standard/semantics/holExtensionScript.sml  *)
(*   hol_consistent        candle/standard/semantics/holConsistencyScript.sml *)
(*   hol_light_consistent  candle/standard/semantics/                        *)
(*                         holLightConsistencyScript.sml                     *)
(* bound as the OCaml terms proves_sound_statement,                          *)
(* extends_consistent_statement, hol_consistent_statement and               *)
(* hol_light_consistent_statement.  This file is loaded after the files      *)
(* that prove the four theorems (holSoundness.ml, holExtension.ml,          *)
(* holConsistency.ml, holLightConsistency.ml) and checks at its end,        *)
(* failing loudly otherwise, that each theorem has no hypotheses and that    *)
(* its conclusion is alpha-equivalent to the term here.                      *)
(*                                                                           *)
(* The statements are HOL4's, with HOL4's overloads written out as the port *)
(* writes them everywhere (headers of holSyntax.ml and holSemantics.ml):     *)
(*   thyof ctxt  ((tysof ctxt, tmsof ctxt), axsof ctxt), where               *)
(*     tysof ctxt  alist_to_fmap (FLAT (MAP types_of_upd ctxt))              *)
(*     tmsof ctxt  alist_to_fmap (FLAT (MAP consts_of_upd ctxt))             *)
(*     axsof ctxt  set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)  *)
(*                   (conexts_of_upd upd)) ctxt))                            *)
(*   sigof ctxt  (tysof ctxt, tmsof ctxt)                                    *)
(*   i models thy, thyh |= c   models0 mem i thy, entails0 mem thyh c       *)
(*   thyh |- c   the inductive relation proves, with HOL4's infix |-         *)
(*   NewAxiom p  hol_NewAxiom p                                              *)
(* HOL4's ^mem is the variable mem : U -> U -> bool (HOL4's 'U is U), the    *)
(* membership relation of a model of set theory; HOL4's V_mem has the type   *)
(* 'a V -> 'a V -> bool, here A V -> A V -> bool.  The type variables stay   *)
(* free in the theorems, as in HOL4.  HOL4's bound variable inf (a HOL      *)
(* Light constant) is inf' here.                                             *)
(*                                                                           *)
(* Notions used, with the files of the port that define them (paths under   *)
(* src/):                                                                    *)
(*   is_set_theory, is_infinite: candle/set-theory/setSpec.ml               *)
(*   V, V_mem: candle/set-theory/setModel.ml                                 *)
(*   hol_term, update (constructor hol_NewAxiom), types_of_upd,              *)
(*     consts_of_upd, axexts_of_upd, conexts_of_upd, updates, extends,       *)
(*     theory_ok, proves (|-), init_ctxt: candle/standard/syntax/holSyntax.ml *)
(*   models0, entails0 (and below them satisfies0, termsem0,                 *)
(*     is_interpretation0, is_std_interpretation0, is_valuation0):            *)
(*     candle/standard/semantics/holSemantics.ml                             *)
(*   equal_on: candle/standard/semantics/holSemanticsExtra.ml               *)
(*   consistent_theory, hol_ctxt (and below it fhol_ctxt):                   *)
(*     candle/standard/semantics/holConsistency.ml, with mk_bool_ctxt        *)
(*     (candle/standard/syntax/holBoolSyntax.ml) and mk_eta_ctxt,            *)
(*     mk_select_ctxt, mk_infinity_ctxt                                      *)
(*     (candle/standard/syntax/holAxiomsSyntax.ml)                           *)
(*   hol_light_ctxt (and below it mk_eta_ctxt_cl, mk_select_ctxt_cl,         *)
(*     mk_infinity_ctxt_hl): candle/standard/semantics/                      *)
(*     holLightConsistency.ml                                                *)
(*   alist_to_fmap: hol4/alist.ml; FLAT, MAP, APPEND, MEM, set_of_list:      *)
(*     HOL Light's lists.ml                                                  *)
(* ========================================================================= *)

needs "candle/set-theory/setSpec.ml";;
needs "candle/set-theory/setModel.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/semantics/holSemantics.ml";;
needs "candle/standard/semantics/holSemanticsExtra.ml";;
needs "candle/standard/semantics/holSoundness.ml";;
needs "candle/standard/semantics/holExtension.ml";;
needs "candle/standard/semantics/holConsistency.ml";;
needs "candle/standard/semantics/holLightConsistency.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4 proves_sound (holSoundnessScript.sml): soundness of the inference   *)
(* system: every provable sequent is valid                                   *)
let proves_sound_statement =
  `is_set_theory (mem:U->U->bool) ==> !thyh c. thyh |- c ==> entails0 mem thyh c`;;

(* HOL4 extends_consistent (holExtensionScript.sml): a model of a good      *)
(* theory extends to a model of any extension that adds no axiom            *)
let extends_consistent_statement =
  `is_set_theory (mem:U->U->bool)
   ==> !ctxt1 ctxt2.
         ctxt2 extends ctxt1
         ==> !i. theory_ok
                   ((alist_to_fmap (FLAT (MAP types_of_upd ctxt1)),
                     alist_to_fmap (FLAT (MAP consts_of_upd ctxt1))),
                    set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                         (conexts_of_upd upd)) ctxt1))) /\
                 models0 mem i
                   ((alist_to_fmap (FLAT (MAP types_of_upd ctxt1)),
                     alist_to_fmap (FLAT (MAP consts_of_upd ctxt1))),
                    set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                         (conexts_of_upd upd)) ctxt1))) /\
                 (!p. MEM (hol_NewAxiom p) ctxt2 ==> MEM (hol_NewAxiom p) ctxt1)
                 ==> ?i'. equal_on (alist_to_fmap (FLAT (MAP types_of_upd ctxt1)),
                                    alist_to_fmap (FLAT (MAP consts_of_upd ctxt1))) i i' /\
                          models0 mem i'
                            ((alist_to_fmap (FLAT (MAP types_of_upd ctxt2)),
                              alist_to_fmap (FLAT (MAP consts_of_upd ctxt2))),
                             set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                                  (conexts_of_upd upd))
                                                    ctxt2)))`;;

(* HOL4 hol_consistent (holConsistencyScript.sml): with an infinite set,    *)
(* every extension of hol_ctxt (booleans, ETA_AX, SELECT_AX, INFINITY_AX)    *)
(* that adds no further axiom is consistent                                  *)
let hol_consistent_statement =
  `is_set_theory (mem:U->U->bool) /\ (?inf'. is_infinite mem inf')
   ==> !ctxt. ctxt extends hol_ctxt /\
              (!p. MEM (hol_NewAxiom p) ctxt ==> MEM (hol_NewAxiom p) hol_ctxt)
              ==> consistent_theory
                    ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                      alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                     set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                          (conexts_of_upd upd)) ctxt)))`;;

(* HOL4 hol_light_consistent (holLightConsistencyScript.sml): in the model  *)
(* of setModel, with an infinite set, every extension of init_ctxt of the   *)
(* shape a HOL Light session builds (hol_light_ctxt) is consistent           *)
let hol_light_consistent_statement =
  `(?inf'. is_infinite (V_mem:A V->A V->bool) inf')
   ==> !ctxt. ctxt extends init_ctxt /\ hol_light_ctxt ctxt
              ==> consistent_theory
                    ((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                      alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
                     set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                                          (conexts_of_upd upd)) ctxt)))`;;

(* the headline checks: each theorem is the statement of this file *)
let () =
  if hyp proves_sound = [] && aconv (concl proves_sound) proves_sound_statement
  then () else failwith "proves_sound is not the headline statement";;

let () =
  if hyp extends_consistent = [] &&
     aconv (concl extends_consistent) extends_consistent_statement
  then () else failwith "extends_consistent is not the headline statement";;

let () =
  if hyp hol_consistent = [] && aconv (concl hol_consistent) hol_consistent_statement
  then () else failwith "hol_consistent is not the headline statement";;

let () =
  if hyp hol_light_consistent = [] &&
     aconv (concl hol_light_consistent) hol_light_consistent_statement
  then () else failwith "hol_light_consistent is not the headline statement";;
