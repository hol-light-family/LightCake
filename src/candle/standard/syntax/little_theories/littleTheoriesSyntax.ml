(* ========================================================================= *)
(* littleTheoriesSyntax: port of HOL4 candle/standard/syntax/little_theories *)
(* /littleTheoriesSyntaxScript.sml (CakeML v3479).  Defines the HOL          *)
(* inference system extended with the little theories module system.         *)
(*                                                                           *)
(* Notes on the rendering (also for the files that load this one):           *)
(* - Names as notes/naming/names.tsv says: try is little_try, env_ok is      *)
(*   little_env_ok, the update' constructors ConstSpec, TypeDefn, NewType,   *)
(*   NewConst, NewAxiom are little_ConstSpec, ...; the symbolic relations    *)
(*   |-' and |n- are proves' and nproves, written prefix: (thy, es, h) |-' c *)
(*   is proves' (thy,es,h) c.  updates' and extends' are infixes.            *)
(* - HOL4 variables: sigma (the Greek letter) is sigma, theta is theta; abs  *)
(*   and rep (HOL Light interface names) are abs_name and rep_name.          *)
(* - HOL4 record notation: thy.tms is ethy_tms thy, ...; the fields added    *)
(*   with add_record_field, thy.ctys, thy.ctms and thy.sig, are ctys thy,    *)
(*   ctms thy and sigof' thy; r with <| f1 := x; f2 := y |> is               *)
(*   ethy_f1_fupd (K x) (ethy_f2_fupd (K y) r).                              *)
(* - HOL4 Overloads are notation only (HOL4 stores the expanded terms), so   *)
(*   they are written out here and in the files that load this one, as in    *)
(*   holSyntax.ml (see its header for Fun, Bool, Equal, is_instance, tysof,  *)
(*   tmsof, sigof, axsof, thyof):                                            *)
(*     type_list' ctxt, const_list' ctxt   FLAT (MAP types_of_upd' ctxt),    *)
(*                                         FLAT (MAP consts_of_upd' ctxt)    *)
(*     tysof' ctxt, tmsof' ctxt    alist_to_fmap (type_list' ctxt), ..       *)
(*     etype_list ctxt, econst_list ctxt  FLAT (MAP etypes_of_upd' ctxt), .. *)
(*     etysof ctxt, etmsof ctxt    alist_to_fmap (etype_list ctxt), ..       *)
(*     eaxexts' ctxt, eaxsof ctxt         FLAT (MAP eaxexts_of_upd' ctxt),   *)
(*                                         set_of_list (eaxexts' ctxt)       *)
(*     axexts' ctxt, conexts' ctxt        FLAT (MAP axexts_of_upd' ctxt), .. *)
(*     axioms_of_upd' upd   APPEND (axexts_of_upd' upd)                      *)
(*                                 (conexts_of_upd' upd)                     *)
(*     axiom_list' ctxt       FLAT (MAP (\upd. axioms_of_upd' upd) ctxt)     *)
(*     axsof' ctxt            set_of_list (axiom_list' ctxt)                 *)
(*     ethyof ctxt   ethy_REC (tmsof' ctxt) (tysof' ctxt) (axsof' ctxt)      *)
(*                     (etmsof ctxt) (etysof ctxt) (eaxsof ctxt)             *)
(*     is_monomorphic ty      tyvars ty = []                                 *)
(*   with the inner overloads expanded too.  The type abbreviation SIG is a  *)
(*   HOL Light one (the same type as holSyntax.ml's sig).                    *)
(* - HOL4 do-notation of the error monad is written with errorMonad_bind and *)
(*   errorMonad_return; x <<- e; m is let x = e in m.                        *)
(* - HOL4's ZIP truncates the longer list, HOL Light's has the length of its *)
(*   first list: ty_esubst takes the first LENGTH params types (TAKE), which *)
(*   is HOL4's list for all lengths; CLITAUX_ty_esubst_Tyapp states the      *)
(*   clause without TAKE for at most LENGTH params arguments.                *)
(* - The rules of the inductive relations quantify their variables in HOL4's *)
(*   order (by name; sigma, a Greek letter in HOL4, comes last).             *)
(* - Local helpers that are not HOL4 theorems are CLITAUX_.                  *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;
needs "hol4/toto.ml";;
needs "hol4/errorMonad.ml";;
needs "hol4/libext.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;

prioritize_num();;
type_invention_error := true;;

(* In this theory we describe an extended Candle kernel that allows abstract
   theorems to be written about parameterised types (e.g., a type M that
   obeys a certain set of axioms), then interpreted under a concrete theory
   after showing it respects those axioms.  This file defines this extended
   theory type, and an extended Candle kernel through the proves' relation
   (a copy of the proves relation + 3 new inference rules).  We also define
   the new substitution functions enabling the interpretation of the
   abstract components of a theory under concrete terms/types. *)

(* A theory is a signature together with a set of axioms. It is well-formed
   if the types of the constants are all ok, the axioms are all ok terms of
   type bool, and the signature is standard. *)

let ethy_INFO = cake_record "ethy"
  ["tms","(mlstring,hol_type)fmap";
   "tys","(mlstring,num)fmap";
   "axs","hol_term->bool";
   "etms","(mlstring,hol_type)fmap";
   "etys","(mlstring,num)fmap";
   "eaxs","hol_term->bool"];;

(* HOL4 thy.ctys, thy.ctms and thy.sig (add_record_field) are ctys thy,     *)
(* ctms thy and sigof' thy.                                                  *)

let ctys_def = cake_def
  `ctys thy = FUNION (ethy_tys thy) (ethy_etys thy)`;;

let ctms_def = cake_def
  `ctms thy = FUNION (ethy_tms thy) (ethy_etms thy)`;;

let sigof'_def = cake_def
  `sigof' thy = (ethy_tys thy,ethy_tms thy)`;;

(* term_ok' has to check if types are valid through both the types and
   eliminable types.  As for hol_term_ok (holSyntax.ml), the recursive call
   of the Abs clause is outside the existential in the definition, and
   term_ok'_def states HOL4's clauses. *)
let CLITAUX_term_ok'_raw = cake_def
  `(term_ok' thy' (hol_Var x ty) <=> type_ok (ctys thy') ty) /\
   (term_ok' thy' (hol_Const name ty) <=>
      ?ty0. FLOOKUP (ctms thy') name = SOME ty0 /\
            type_ok (ctys thy') ty /\
            (?i. ty = TYPE_SUBST i ty0)) /\
   (term_ok' thy' (hol_Comb tm1 tm2) <=>
      term_ok' thy' tm1 /\
      term_ok' thy' tm2 /\
      welltyped (hol_Comb tm1 tm2)) /\
   (term_ok' thy' (hol_Abs v tm) <=>
      (?x ty. v = hol_Var x ty /\ type_ok (ctys thy') ty) /\
      term_ok' thy' tm)`;;

let term_ok'_def = prove
 (`(!thy' x ty. term_ok' thy' (hol_Var x ty) <=> type_ok (ctys thy') ty) /\
   (!thy' name ty.
      term_ok' thy' (hol_Const name ty) <=>
      ?ty0. FLOOKUP (ctms thy') name = SOME ty0 /\
            type_ok (ctys thy') ty /\
            (?i. ty = TYPE_SUBST i ty0)) /\
   (!thy' tm1 tm2.
      term_ok' thy' (hol_Comb tm1 tm2) <=>
      term_ok' thy' tm1 /\
      term_ok' thy' tm2 /\
      welltyped (hol_Comb tm1 tm2)) /\
   (!thy' v tm.
      term_ok' thy' (hol_Abs v tm) <=>
      ?x ty.
        v = hol_Var x ty /\
        type_ok (ctys thy') ty /\
        term_ok' thy' tm)`,
  REWRITE_TAC[CLITAUX_term_ok'_raw] THEN MESON_TAC[]);;

(* theory_ok' and axioms_ok are defined after no_var_collapse and esubsts_ok' *)

(* Sequents provable from a theory *)

(* ty_esubst maps a type to its subtituted counterpart.  we recursively map
   the substitution over types.  in the SOME case, we ensure polymorphic
   substitutions are applied correctly:
   e.g., ty_esubst ('a M |-> 'a list) (num M) = num list.
   HOL4's ZIP (MAP (ty_esubst sigma) ts, MAP Tyvar params) truncates the
   longer list; HOL Light's ZIP has the length of its first list (HD and TL
   of the second), so the definition takes the first LENGTH params types:
   the same list for all lengths. *)
let ty_esubst_def = cake_def_wf
  `measure (\(sigma:(mlstring,mlstring list#hol_type)fmap#A,ty:hol_type).
              hol_type_size ty)` TERM_TAC
  `(ty_esubst (_:(mlstring,mlstring list#hol_type)fmap#A) (Tyvar n) = Tyvar n) /\
   (ty_esubst sigma (Tyapp n ts) =
      match FLOOKUP (FST sigma) n with
        NONE -> Tyapp n (MAP (ty_esubst sigma) ts)
      | SOME (params,body) ->
          TYPE_SUBST (ZIP (TAKE (LENGTH params) (MAP (ty_esubst sigma) ts))
                          (MAP Tyvar params)) body)`;;

let ty_esubst_ind = cake_ind "ty_esubst";;

(* The Tyapp clause when the type has at most as many arguments as the
   substitution has parameters (equal lengths for a type_ok type): HOL Light's
   ZIP, without the TAKE. *)
let CLITAUX_ty_esubst_Tyapp = prove
 (`!(sigma:(mlstring,mlstring list#hol_type)fmap#A) n ts params body.
     FLOOKUP (FST sigma) n = SOME (params,body) /\ LENGTH ts <= LENGTH params
     ==> ty_esubst sigma (Tyapp n ts) =
         TYPE_SUBST (ZIP (MAP (ty_esubst sigma) ts) (MAP Tyvar params)) body`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ty_esubst_def; option_CASE; pair_CASE] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC TAKE_LENGTH_TOO_LONG THEN ASM_REWRITE_TAC[LENGTH_MAP]);;

let esubst_sig_def = cake_def
  `esubst_sig (sigma:(mlstring,mlstring list#hol_type)fmap#A)
              (tys:(mlstring,num)fmap,tms:(mlstring,hol_type)fmap) =
     (tys,ty_esubst sigma o_f tms)`;;

(* HOL4: try (errorMonad's try has the same definition) *)
let little_try_def = cake_def
  `(little_try (errorMonad_return v:(A,E1)error) (f:E1->(A,E2)error) =
      errorMonad_return v) /\
   (little_try (errorMonad_error e) f = f e)`;;

let tm_names_def = cake_def
  `(tm_names (hol_Var n _) = [n]) /\
   (tm_names (hol_Const _ _) = []) /\
   (tm_names (hol_Comb t1 t2) = APPEND (tm_names t1) (tm_names t2)) /\
   (tm_names (hol_Abs v body) = APPEND (tm_names v) (tm_names body))`;;
let _ = cake_add_simps [tm_names_def];;

(* termination of nvar_aux: the names at least as long as n get fewer *)
let CLITAUX_strlen_prime = prove
 (`!n. strlen (strcat n (implode "'")) = strlen n + 1`,
  REWRITE_TAC[strcat_thm; strlen_def; explode_thm; LENGTH_APPEND] THEN
  GEN_TAC THEN QCASES_ON "n" THEN
  REWRITE_TAC[explode_thm; strlen_def; LENGTH; ONE]);;

let CLITAUX_nvar_aux_lt = prove
 (`!nms n. MEM n nms ==>
     LENGTH (FILTER (\e. strlen n + 1 <= strlen e) nms) <
     LENGTH (FILTER (\e. strlen n <= strlen e) nms)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; FILTER] THEN GEN_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[ARITH_RULE `~(n + 1 <= n)`; LE_REFL; LENGTH] THEN
    MATCH_MP_TAC(ARITH_RULE `x <= y ==> x < SUC y`) THEN
    MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] LENGTH_FILTER_LEQ_MONO) THEN
    REWRITE_TAC[] THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `n:mlstring`) THEN ASM_REWRITE_TAC[] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ASM_ARITH_TAC]);;

let nvar_aux = cake_def_wf
  `measure (\(nms:mlstring list,n:mlstring).
              LENGTH (FILTER (\e. strlen n <= strlen e) nms))`
  (REWRITE_TAC[measure_THM] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
   REWRITE_TAC[CLITAUX_strlen_prime] THEN MESON_TAC[CLITAUX_nvar_aux_lt; LT_TRANS])
  `nvar_aux nms n = if MEM n nms then nvar_aux nms (strcat n (implode "'")) else n`;;

let nvar_aux_ind = cake_ind "nvar_aux";;

let NVARIANT = cake_def
  `NVARIANT n avds tm = nvar_aux (APPEND (tm_names tm) avds) n`;;

(* analog of INST_CORE.  HOL4's do-notation of the error monad is written
   with errorMonad_bind and errorMonad_return; x <<- e; m is let x = e in m. *)
let esubst_ty0_def = cake_def_wf
  `measure (\(env:(hol_term#hol_term)list,
              sigma:(mlstring,mlstring list#hol_type)fmap#
                    (mlstring,hol_term#hol_type)fmap,
              avds:mlstring list,tm:hol_term). sizeof tm)`
  (REWRITE_TAC[measure_THM] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[sizeof_def; CSYNAUX_SIZEOF_VSUBST_VAR] THEN ARITH_TAC)
  `(esubst_ty0 env (sigma:(mlstring,mlstring list#hol_type)fmap#
                         (mlstring,hol_term#hol_type)fmap) avds (hol_Var n ty) =
      let tm = hol_Var n ty in
      let tm' = hol_Var n (ty_esubst sigma ty) in
      if REV_ASSOCD tm' env tm = tm then errorMonad_return tm'
      else errorMonad_error tm') /\
   (esubst_ty0 env sigma avds (hol_Const n ty) =
      errorMonad_return (hol_Const n (ty_esubst sigma ty))) /\
   (esubst_ty0 env sigma avds (hol_Comb t1 t2) =
      errorMonad_bind (esubst_ty0 env sigma avds t1) (\t1'.
      errorMonad_bind (esubst_ty0 env sigma avds t2) (\t2'.
      errorMonad_return (hol_Comb t1' t2')))) /\
   (esubst_ty0 env sigma avds (hol_Abs v body) =
      let (n,ty) = dest_var v in
      let ty' = ty_esubst sigma ty in
      let v' = hol_Var n ty' in
      little_try
        (errorMonad_bind (esubst_ty0 (CONS (v,v') env) sigma avds body) (\body'.
         errorMonad_return (hol_Abs v' body')))
        (\bad_v.
           if ~(bad_v = v') then errorMonad_error bad_v
           else
             errorMonad_bind (esubst_ty0 [] sigma avds body) (\body1.
             let n' = NVARIANT n avds body1 in
             let body' = VSUBST [(hol_Var n' ty,hol_Var n ty)] body in
             let env'' = CONS (hol_Var n' ty,hol_Var n' ty') env in
             errorMonad_bind (esubst_ty0 env'' sigma avds body') (\body''.
             errorMonad_return (hol_Abs (hol_Var n' ty') body'')))))`;;

let esubst_ty0_ind = cake_ind "esubst_ty0";;

let esubst_ty_def = cake_def
  `esubst_ty sigma avds tm =
     match esubst_ty0 [] sigma avds tm with
       errorMonad_return v -> v
     | errorMonad_error e -> ARB`;;

(* substitute eliminable consts, correcting any type variables that appear
   to fit where they appear in the same way as ty_esubst *)
let esubst_tm_def = cake_def
  `(esubst_tm (sigma:(mlstring,mlstring list#hol_type)fmap#
                     (mlstring,hol_term#hol_type)fmap) (hol_Var n ty) =
      hol_Var n ty) /\
   (esubst_tm sigma (hol_Abs v t) = hol_Abs v (esubst_tm sigma t)) /\
   (esubst_tm sigma (hol_Comb t1 t2) =
      hol_Comb (esubst_tm sigma t1) (esubst_tm sigma t2)) /\
   (esubst_tm sigma (hol_Const n ty) =
      match FLOOKUP (SND sigma) n with
        NONE -> hol_Const n ty
      | SOME (repl,decl_ty) ->
          match match_type (ty_esubst sigma decl_ty) ty with
            NONE -> ARB
          | SOME tyin -> INST tyin repl)`;;

let esubst_def = cake_def
  `esubst sigma avds tm = esubst_tm sigma (esubst_ty sigma avds tm)`;;

let esubst_thy_def = cake_def
  `esubst_thy sigma thy =
     ethy_axs_fupd (K (IMAGE (esubst sigma []) (ethy_axs thy)))
      (ethy_etms_fupd (K (ty_esubst sigma o_f ethy_etms thy))
        (ethy_eaxs_fupd (K (IMAGE (esubst sigma []) (ethy_eaxs thy))) thy))`;;

let vsubst_tys_ok_def = cake_def
  `vsubst_tys_ok ilist <=>
     (!s s'. MEM (s',s) ilist ==> ?x ty. s = hol_Var x ty /\ s' has_type ty)`;;

let little_env_ok_def = cake_def
  `little_env_ok env <=>
     (!v1 v2. MEM (v1,v2) env ==> ?n t1 t2. v1 = hol_Var n t1 /\ v2 = hol_Var n t2)`;;

let env_ok_ext = prove
 (`!env x t1 t2.
     little_env_ok env ==> little_env_ok (CONS (hol_Var x t1,hol_Var x t2) env)`,
  RW[little_env_ok_def; MEM; PAIR_EQ] THEN ASM_MESON_TAC[]);;

let env_ok_nil = prove
 (`little_env_ok []`,
  RW[little_env_ok_def; MEM]);;
let _ = cake_add_simps [env_ok_nil];;

let FVs_def = cake_def
  `(FVs (hol_Var n ty) = {(n,ty)}) /\
   (FVs (hol_Const _ _) = {}) /\
   (FVs (hol_Comb t1 t2) = FVs t1 UNION FVs t2) /\
   (FVs (hol_Abs v body) = FVs body DIFF FVs v)`;;
let _ = cake_add_simps [FVs_def];;

let free_names = cake_def
  `free_names tm = {n | ?ty. (n,ty) IN FVs tm}`;;

let free_names_var = prove
 (`!n ty. free_names (hol_Var n ty) = {n}`,
  RW[free_names; FVs_def; EXTENSION; IN_ELIM_THM; IN_SING; PAIR_EQ] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [free_names_var];;

let alist_to_fm_def = cake_def
  `(alist_to_fm ([]:(B#A)list) = (FEMPTY:(A,B)fmap)) /\
   (alist_to_fm (CONS (v,k) rest) = alist_to_fm rest |+ (k,v))`;;
let _ = cake_add_simps [alist_to_fm_def];;

let VSUBSTfm = cake_def
  `(VSUBSTfm fm (hol_Var x ty) =
      match FLOOKUP fm (hol_Var x ty) with
        NONE -> hol_Var x ty
      | SOME t -> t) /\
   (VSUBSTfm fm (hol_Const x ty) = hol_Const x ty) /\
   (VSUBSTfm fm (hol_Comb t1 t2) = hol_Comb (VSUBSTfm fm t1) (VSUBSTfm fm t2)) /\
   (VSUBSTfm fm (hol_Abs v t) =
      let fm' = fm \\ v in
      let t' = VSUBSTfm fm' t in
      if ?k w. FLOOKUP fm' k = SOME w /\ VFREE_IN v w /\ VFREE_IN k t
      then let (x,ty) = dest_var v in
           let z = hol_Var (VARIANT t' (explode x) ty) ty in
           let fm'' = fm' |+ (v,z) in
           hol_Abs z (VSUBSTfm fm'' t)
      else hol_Abs v t')`;;

(* HOL4 Overload is_monomorphic ty = (tyvars ty = []): written out. *)

let tycons_def = cake_def_wf `measure hol_type_size`
  (REWRITE_TAC[IN_SET_OF_LIST] THEN TERM_TAC)
  `(tycons (Tyvar _) = {}) /\
   (tycons (Tyapp n ts) = {n} UNION UNIONS (IMAGE tycons (set_of_list ts)))`;;

new_type_abbrev("SIG",`:(mlstring,num)fmap#(mlstring,hol_type)fmap`);;

let esubsts_ok_def = cake_def
  `esubsts_ok (sig:SIG) (sigma:(mlstring,mlstring list#hol_type)fmap,
                         theta:(mlstring,hol_term#hol_type)fmap) <=>
     ~(implode "=" IN FDOM theta) /\
     ~(implode "bool" IN FDOM sigma) /\
     ~(implode "fun" IN FDOM sigma) /\
     (!tynm. tynm IN FDOM sigma
             ==> ?a params body.
                   FLOOKUP (FST sig) tynm = SOME a /\
                   FAPPLY sigma tynm = (params,body) /\
                   LENGTH params = a /\
                   set_of_list (tyvars body) SUBSET set_of_list params /\
                   type_ok (FST sig) body /\
                   DISJOINT (tycons body) (FDOM sigma)) /\
     (!tmnm. tmnm IN FDOM theta
             ==> ?ty repl decl_ty.
                   FLOOKUP (SND sig) tmnm = SOME ty /\
                   FAPPLY theta tmnm = (repl,decl_ty) /\
                   decl_ty = ty /\
                   CLOSED repl /\
                   set_of_list (tvars repl) SUBSET set_of_list (tyvars (typeof repl)) /\
                   hol_term_ok (esubst_sig (sigma,theta) sig) repl /\
                   typeof repl = ty_esubst (sigma,theta) ty)`;;

let esubsts_ok'_def = cake_def
  `esubsts_ok' (thy:ethy) (sigma:(mlstring,mlstring list#hol_type)fmap,
                           theta:(mlstring,hol_term#hol_type)fmap) <=>
     ~(implode "=" IN FDOM theta) /\
     ~(implode "bool" IN FDOM sigma) /\
     ~(implode "fun" IN FDOM sigma) /\
     FDOM sigma SUBSET FDOM (ethy_etys thy) /\
     (!tynm. tynm IN FDOM sigma
             ==> ?params body.
                   FAPPLY sigma tynm = (params,body) /\
                   LENGTH params = FAPPLY (ethy_etys thy) tynm /\
                   set_of_list (tyvars body) SUBSET set_of_list params /\
                   type_ok (ctys thy) body /\
                   DISJOINT (tycons body) (FDOM sigma)) /\
     FDOM theta SUBSET FDOM (ethy_etms thy) /\
     (!tmnm. tmnm IN FDOM theta
             ==> ?repl decl_ty.
                   FAPPLY theta tmnm = (repl,decl_ty) /\
                   decl_ty = FAPPLY (ethy_etms thy) tmnm /\
                   CLOSED repl /\
                   set_of_list (tvars repl) SUBSET set_of_list (tyvars (typeof repl)) /\
                   term_ok' (esubst_thy (sigma,theta) thy) repl /\
                   typeof repl = ty_esubst (sigma,theta) decl_ty)`;;

(* Standard signature includes the minimal type operators and constants *)
let esubst_sig_is_std_sig = prove
 (`!sig sigma. esubsts_ok sig sigma /\ is_std_sig sig
               ==> is_std_sig (esubst_sig sigma sig)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`tys:(mlstring,num)fmap`; `tms:(mlstring,hol_type)fmap`;
    `sigma:(mlstring,mlstring list#hol_type)fmap`;
    `theta:(mlstring,hol_term#hol_type)fmap`] THEN
  RW[esubsts_ok_def; esubst_sig_def; is_std_sig_def] THEN
  RW[FLOOKUP_o_f; ty_esubst_def] THEN
  GVS[FLOOKUP_DEF]);;

let esubsts_total_def = cake_def
  `esubsts_total (thy:ethy) (sigma:(mlstring,mlstring list#hol_type)fmap,
                             theta:(mlstring,hol_term#hol_type)fmap) <=>
     (!tyn. tyn IN FDOM sigma <=> tyn IN FDOM (ethy_etys thy)) /\
     (!tmn. tmn IN FDOM theta <=> tmn IN FDOM (ethy_etms thy))`;;

let no_var_collapse = cake_def
  `no_var_collapse (sigma:(mlstring,mlstring list#hol_type)fmap#
                          (mlstring,hol_term#hol_type)fmap) tm <=>
     !x ty1 ty2.
       VFREE_IN (hol_Var x ty1) tm /\ VFREE_IN (hol_Var x ty2) tm /\ ~(ty1 = ty2)
       ==> ~(ty_esubst sigma ty1 = ty_esubst sigma ty2)`;;

let axioms_ok_def = cake_def
  `axioms_ok (thy:ethy) axs <=>
     !sigma p. esubsts_ok' thy sigma /\ p IN axs ==> no_var_collapse sigma p`;;

let theory_ok'_def = cake_def
  `theory_ok' (thy:ethy) <=>
     (!ty. ty IN FRANGE (ethy_tms thy) ==> type_ok (ethy_tys thy) ty) /\
     (!ty. ty IN FRANGE (ethy_etms thy) ==> type_ok (ctys thy) ty) /\
     DISJOINT (FDOM (ethy_tys thy)) (FDOM (ethy_etys thy)) /\
     DISJOINT (FDOM (ethy_tms thy)) (FDOM (ethy_etms thy)) /\
     (!p. p IN ethy_axs thy
          ==> term_ok' thy p /\ p has_type Tyapp (implode "bool") []) /\
     (!p. p IN ethy_eaxs thy
          ==> term_ok' thy p /\ p has_type Tyapp (implode "bool") []) /\
     is_std_sig (sigof' thy)`;;

(* HOL4: the infix |-' (the relation proves'): (thy, es, h) |-' c is
   proves' (thy,es,h) c.  The rules quantify their variables in HOL4's
   order (by name; HOL4's sigma sorts after the ASCII names). *)
let proves'_rules,proves'_ind,proves'_cases,proves'_strongind = cake_inductive
  `(!es h l r thy ty x.
      ~(EX (VFREE_IN (hol_Var x ty)) h) /\ type_ok (ctys thy) ty /\
      proves' (thy,es,h) (l === r)
      ==> proves' (thy,es,h) (hol_Abs (hol_Var x ty) l === hol_Abs (hol_Var x ty) r)) /\
   (!p thy.
      theory_ok' thy /\ p has_type Tyapp (implode "bool") [] /\ term_ok' thy p
      ==> proves' (thy,{},[p]) p) /\
   (!t thy ty x.
      theory_ok' thy /\ type_ok (ctys thy) ty /\ term_ok' thy t
      ==> proves' (thy,{},[]) (hol_Comb (hol_Abs (hol_Var x ty) t) (hol_Var x ty) === t)) /\
   (!c1 c2 es1 es2 h1 h2 thy.
      proves' (thy,es1,h1) c1 /\
      proves' (thy,es2,h2) c2
      ==> proves' (thy,es1 UNION es2,term_union (term_remove c2 h1) (term_remove c1 h2))
                  (c1 === c2)) /\
   (!es1 es2 h1 h2 p p' q thy.
      proves' (thy,es1,h1) (p === q) /\
      proves' (thy,es2,h2) p' /\ ACONV p p'
      ==> proves' (thy,es1 UNION es2,term_union h1 h2) q) /\
   (!c es h ilist thy.
      (!s s'. MEM (s',s) ilist
              ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\ term_ok' thy s') /\
      proves' (thy,es,h) c
      ==> proves' (thy,es,term_image (VSUBST ilist) h) (VSUBST ilist c)) /\
   (!c es h thy tyin.
      ALL (type_ok (ctys thy)) (MAP FST tyin) /\
      proves' (thy,es,h) c
      ==> proves' (thy,es,term_image (INST tyin) h) (INST tyin c)) /\
   (!es1 es2 h1 h2 l1 l2 r1 r2 thy.
      proves' (thy,es1,h1) (l1 === r1) /\
      proves' (thy,es2,h2) (l2 === r2) /\
      welltyped (hol_Comb l1 l2)
      ==> proves' (thy,es1 UNION es2,term_union h1 h2) (hol_Comb l1 l2 === hol_Comb r1 r2)) /\
   (!t thy.
      theory_ok' thy /\ term_ok' thy t
      ==> proves' (thy,{},[]) (t === t)) /\
   (!c thy.
      theory_ok' thy /\ c IN ethy_axs thy
      ==> proves' (thy,{},[]) c) /\
   (!c1 c2 es1 es2 h2 thy.
      proves' (thy,es1,[]) c1 /\ proves' (thy,es2,h2) c2
      ==> proves' (thy,(es2 DIFF {c1}) UNION es1,h2) c2) /\
   (!c es h thy sigma.
      proves' (thy,es,h) c /\
      theory_ok' thy /\
      esubsts_ok' thy sigma /\
      axioms_ok thy (ethy_axs thy) /\
      axioms_ok thy (ethy_eaxs thy) /\
      (!ax. ax IN es ==> no_var_collapse sigma ax)
      ==> proves' (esubst_thy sigma thy,IMAGE (esubst sigma []) es,
                   term_image (esubst sigma []) h)
                  (esubst sigma (FLAT (MAP tm_names h)) c)) /\
   (!c thy.
      theory_ok' thy /\ c IN ethy_eaxs thy
      ==> proves' (thy,{c},[]) c)`;;

let proves'_ABS,proves'_ASSUME,proves'_BETA,proves'_DEDUCT_ANTISYM,proves'_EQ_MP,
    proves'_INST,proves'_INST_TYPE,proves'_MK_COMB,proves'_REFL,proves'_axioms,
    proves'_elim_discharge,proves'_elim_inst,proves'_elim_axioms =
  match CONJUNCTS proves'_rules with
    [a;b;c;d;e;f;g;h;i;j;k;l;m] -> a,b,c,d,e,f,g,h,i,j,k,l,m
  | _ -> failwith "proves'_rules";;

let lift_thy_def = cake_def
  `lift_thy (thy:thy) =
     ethy_REC (SND (FST thy)) (FST (FST thy)) (SND thy) FEMPTY FEMPTY {}`;;

let tmsof_lift_thy = prove
 (`!thy. ethy_tms (lift_thy thy) = SND (FST thy)`,
  SIMP[lift_thy_def]);;
let _ = cake_add_simps [tmsof_lift_thy];;

let tysof_lift_thy = prove
 (`!thy. ethy_tys (lift_thy thy) = FST (FST thy)`,
  SIMP[lift_thy_def]);;
let _ = cake_add_simps [tysof_lift_thy];;

let axsof_lift_thy = prove
 (`!thy. ethy_axs (lift_thy thy) = SND thy`,
  SIMP[lift_thy_def]);;
let _ = cake_add_simps [axsof_lift_thy];;

let eaxsof_lift_thy = prove
 (`!thy. ethy_eaxs (lift_thy thy) = {}`,
  SIMP[lift_thy_def]);;
let _ = cake_add_simps [eaxsof_lift_thy];;

let etmsof_lift_thy = prove
 (`!thy. ethy_etms (lift_thy thy) = FEMPTY`,
  SIMP[lift_thy_def]);;
let _ = cake_add_simps [etmsof_lift_thy];;

let etysof_lift_thy = prove
 (`!thy. ethy_etys (lift_thy thy) = FEMPTY`,
  SIMP[lift_thy_def]);;
let _ = cake_add_simps [etysof_lift_thy];;

(* HOL4: (lift_thy thy).sig = sigof thy *)
let sigof_lift_thy = prove
 (`!thy. sigof' (lift_thy thy) = FST thy`,
  SIMP[lift_thy_def; sigof'_def]);;
let _ = cake_add_simps [sigof_lift_thy];;

let ctys_lift_thy = prove
 (`!thy. ctys (lift_thy thy) = FST (FST thy)`,
  SIMP[lift_thy_def; ctys_def; FUNION_FEMPTY_2]);;
let _ = cake_add_simps [ctys_lift_thy];;

let ctms_lift_thy = prove
 (`!thy. ctms (lift_thy thy) = SND (FST thy)`,
  SIMP[lift_thy_def; ctms_def; FUNION_FEMPTY_2]);;
let _ = cake_add_simps [ctms_lift_thy];;

let term_ok'_lift_thy = prove
 (`!thy tm. term_ok' (lift_thy thy) tm <=> hol_term_ok (FST thy) tm`,
  GEN_TAC THEN MATCH_MP_TAC hol_term_INDUCT THEN
  RW[hol_term_ok_def; term_ok'_def; ctys_lift_thy; ctms_lift_thy]);;
let _ = cake_add_simps [term_ok'_lift_thy];;

let drop_thy = cake_def
  `drop_thy used_eaxs thy' =
     (((ctys thy',ctms thy'),ethy_axs thy' UNION used_eaxs):thy)`;;

let sigof_drop_thy = prove
 (`!es thy. FST (drop_thy es thy) = (ctys thy,ctms thy)`,
  RW[drop_thy]);;
let _ = cake_add_simps [sigof_drop_thy];;

let axsof_drop_thy = prove
 (`!es thy. ethy_axs thy SUBSET SND (drop_thy es thy)`,
  RW[drop_thy] THEN SET_TAC[]);;

(* HOL4: the infix |n- (the relation nproves): (thy, h, n) |n- c is
   nproves (thy,h,n) c; HOL4's n + m + 1 is (n + m) + 1. *)
let nproves_rules,nproves_ind,nproves_cases,nproves_strongind = cake_inductive
  `(!h l n r thy ty x.
      ~(EX (VFREE_IN (hol_Var x ty)) h) /\ type_ok (FST (FST thy)) ty /\
      nproves (thy,h,n) (l === r)
      ==> nproves (thy,h,n + 1) (hol_Abs (hol_Var x ty) l === hol_Abs (hol_Var x ty) r)) /\
   (!p thy.
      theory_ok thy /\ p has_type Tyapp (implode "bool") [] /\ hol_term_ok (FST thy) p
      ==> nproves (thy,[p],0) p) /\
   (!t thy ty x.
      theory_ok thy /\ type_ok (FST (FST thy)) ty /\ hol_term_ok (FST thy) t
      ==> nproves (thy,[],0) (hol_Comb (hol_Abs (hol_Var x ty) t) (hol_Var x ty) === t)) /\
   (!c1 c2 h1 h2 m n thy.
      nproves (thy,h1,n) c1 /\
      nproves (thy,h2,m) c2
      ==> nproves (thy,term_union (term_remove c2 h1) (term_remove c1 h2),(n + m) + 1)
                  (c1 === c2)) /\
   (!h1 h2 m n p p' q thy.
      nproves (thy,h1,n) (p === q) /\
      nproves (thy,h2,m) p' /\ ACONV p p'
      ==> nproves (thy,term_union h1 h2,(n + m) + 1) q) /\
   (!c h ilist n thy.
      (!s s'. MEM (s',s) ilist
              ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\ hol_term_ok (FST thy) s') /\
      nproves (thy,h,n) c
      ==> nproves (thy,term_image (VSUBST ilist) h,n + 1) (VSUBST ilist c)) /\
   (!c h n thy tyin.
      ALL (type_ok (FST (FST thy))) (MAP FST tyin) /\
      nproves (thy,h,n) c
      ==> nproves (thy,term_image (INST tyin) h,n + 1) (INST tyin c)) /\
   (!h1 h2 l1 l2 m n r1 r2 thy.
      nproves (thy,h1,n) (l1 === r1) /\
      nproves (thy,h2,m) (l2 === r2) /\
      welltyped (hol_Comb l1 l2)
      ==> nproves (thy,term_union h1 h2,(n + m) + 1) (hol_Comb l1 l2 === hol_Comb r1 r2)) /\
   (!t thy.
      theory_ok thy /\ hol_term_ok (FST thy) t
      ==> nproves (thy,[],0) (t === t)) /\
   (!c thy.
      theory_ok thy /\ c IN SND thy
      ==> nproves (thy,[],0) c)`;;

let nproves_ABS,nproves_ASSUME,nproves_BETA,nproves_DEDUCT_ANTISYM,nproves_EQ_MP,
    nproves_INST,nproves_INST_TYPE,nproves_MK_COMB,nproves_REFL,nproves_axioms =
  match CONJUNCTS nproves_rules with
    [a;b;c;d;e;f;g;h;i;j] -> a,b,c,d,e,f,g,h,i,j
  | _ -> failwith "nproves_rules";;

(* A context is a sequence of updates.  little_ConstSpec witnesses
   proposition: definition of new constants by specification;
   little_TypeDefn name predicate abs_name rep_name: definition of a new type
   operator; little_NewType name arity; NewEliminableType name arity;
   little_NewConst name type; NewEliminableConst name type; little_NewAxiom
   proposition; NewEliminableAxiom proposition. *)
let update'_INDUCT,update'_RECURSION = cake_type
  "update' = little_ConstSpec ((mlstring#hol_term) list) hol_term
           | little_TypeDefn mlstring hol_term mlstring mlstring
           | little_NewType mlstring num
           | NewEliminableType mlstring num
           | little_NewConst mlstring hol_type
           | NewEliminableConst mlstring hol_type
           | little_NewAxiom hol_term
           | NewEliminableAxiom hol_term";;

(* Projecting out pieces of the context *)

(* Types and constants introduced by an update *)
let types_of_upd'_def = cake_def
  `(types_of_upd' (little_ConstSpec _ _) = []) /\
   (types_of_upd' (little_TypeDefn name pred _ _) = [(name,LENGTH (tvars pred))]) /\
   (types_of_upd' (little_NewType name arity) = [(name,arity)]) /\
   (types_of_upd' (NewEliminableType name arity) = []) /\
   (types_of_upd' _ = [])`;;

let consts_of_upd'_def = cake_def
  `(consts_of_upd' (little_ConstSpec eqs prop) = MAP (\(s,t). (s,typeof t)) eqs) /\
   (consts_of_upd' (little_TypeDefn name pred abs_name rep_name) =
      let rep_type = hol_domain (typeof pred) in
      let abs_type =
        Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
      [(abs_name,Tyapp (implode "fun") [rep_type; abs_type]);
       (rep_name,Tyapp (implode "fun") [abs_type; rep_type])]) /\
   (consts_of_upd' (little_NewConst name type) = [(name,type)]) /\
   (consts_of_upd' (NewEliminableConst name type) = []) /\
   (consts_of_upd' _ = [])`;;

(* HOL4 Overloads type_list', tysof', const_list', tmsof' on contexts:
   written out (header). *)

(* Eliminable types, constants, and axioms *)
let etypes_of_upd'_def = cake_def
  `(etypes_of_upd' (NewEliminableType name arity) = [(name,arity)]) /\
   (etypes_of_upd' _ = [])`;;

let econsts_of_upd'_def = cake_def
  `(econsts_of_upd' (NewEliminableConst name type) = [(name,type)]) /\
   (econsts_of_upd' _ = [])`;;

let eaxexts_of_upd'_def = cake_def
  `(eaxexts_of_upd' (NewEliminableAxiom prop) = [prop]) /\
   (eaxexts_of_upd' _ = [])`;;

(* HOL4 Overloads etype_list, etysof, econst_list, etmsof, eaxexts', eaxsof:
   written out (header). *)

(* Axioms: we divide them into axiomatic extensions and conservative
   extensions, we will prove that the latter preserve consistency *)
let axexts_of_upd'_def = cake_def
  `(axexts_of_upd' (little_NewAxiom prop) = [prop]) /\
   (axexts_of_upd' _ = [])`;;

let conexts_of_upd'_def = cake_def
  `(conexts_of_upd' (little_ConstSpec eqs prop) =
      let ilist = MAP (\(s,t). let ty = typeof t in (hol_Const s ty,hol_Var s ty)) eqs in
      [VSUBST ilist prop]) /\
   (conexts_of_upd' (little_TypeDefn name pred abs_name rep_name) =
      let abs_type =
        Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
      let rep_type = hol_domain (typeof pred) in
      let abs_tm = hol_Const abs_name (Tyapp (implode "fun") [rep_type; abs_type]) in
      let rep_tm = hol_Const rep_name (Tyapp (implode "fun") [abs_type; rep_type]) in
      let a = hol_Var (implode "a") abs_type in
      let r = hol_Var (implode "r") rep_type in
      [hol_Comb abs_tm (hol_Comb rep_tm a) === a;
       hol_Comb pred r === (hol_Comb rep_tm (hol_Comb abs_tm r) === r)]) /\
   (conexts_of_upd' (NewEliminableAxiom prop) = []) /\
   (conexts_of_upd' _ = [])`;;

(* HOL4 Overloads axexts', conexts', axioms_of_upd', axiom_list', axsof' and
   ethyof: written out (header). *)

let _ = cake_add_simps [types_of_upd'_def; consts_of_upd'_def; etypes_of_upd'_def;
                        econsts_of_upd'_def; eaxexts_of_upd'_def; axexts_of_upd'_def];;

(* Principles for extending the context *)

parse_as_infix("updates'",(12,"right"));;

(* The rules, in order (HOL4's comments): a new axiom, a new constant, a new
   specification, a new type, a new type definition, a new eliminable type, a
   new eliminable constant, a new eliminable axiom. *)
let updates'_rules,updates'_ind,updates'_cases,updates'_strongind = cake_inductive
  `(!ctxt prop.
      prop has_type Tyapp (implode "bool") [] /\
      hol_term_ok (alist_to_fmap (FLAT (MAP types_of_upd' ctxt)),alist_to_fmap (FLAT
        (MAP consts_of_upd' ctxt))) prop
      ==> (little_NewAxiom prop) updates' ctxt) /\
   (!ctxt name ty.
      ~(name IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt)))) /\
      ~(name IN FDOM (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt)))) /\
      type_ok (alist_to_fmap (FLAT (MAP types_of_upd' ctxt))) ty
      ==> (little_NewConst name ty) updates' ctxt) /\
   (!ctxt eqs prop.
      proves' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt))) (alist_to_fmap (FLAT
        (MAP types_of_upd' ctxt))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
        (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt)))
        (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt))) (set_of_list (FLAT
        (MAP eaxexts_of_upd' ctxt))),{},MAP (\(s,t). hol_Var s (typeof t) === t) eqs) prop /\
      ALL (\t. CLOSED t /\ (!v. MEM v (tvars t) ==> MEM v (tyvars (typeof t))))
          (MAP SND eqs) /\
      (!x ty. VFREE_IN (hol_Var x ty) prop ==>
              MEM (x,ty) (MAP (\(s,t). (s,typeof t)) eqs)) /\
      (!s. MEM s (MAP FST eqs) ==> ~(s IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt))))) /\
      (!s. MEM s (MAP FST eqs) ==> ~(s IN FDOM (alist_to_fmap (FLAT
        (MAP econsts_of_upd' ctxt))))) /\
      ALL_DISTINCT (MAP FST eqs) /\
      (!s t. MEM (s,t) eqs ==> type_ok (alist_to_fmap (FLAT (MAP types_of_upd' ctxt))) (typeof t))
      ==> (little_ConstSpec eqs prop) updates' ctxt) /\
   (!arity ctxt name.
      ~(name IN FDOM (alist_to_fmap (FLAT (MAP types_of_upd' ctxt)))) /\
      ~(name IN FDOM (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt))))
      ==> (little_NewType name arity) updates' ctxt) /\
   (!abs_name ctxt name pred rep_name witness.
      proves' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt))) (alist_to_fmap (FLAT
        (MAP types_of_upd' ctxt))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
        (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt)))
        (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt))) (set_of_list (FLAT
        (MAP eaxexts_of_upd' ctxt))),{},[]) (hol_Comb pred witness) /\
      CLOSED pred /\
      ~(name IN FDOM (alist_to_fmap (FLAT (MAP types_of_upd' ctxt)))) /\
      ~(name IN FDOM (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt)))) /\
      ~(abs_name IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt)))) /\
      ~(abs_name IN FDOM (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt)))) /\
      ~(rep_name IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt)))) /\
      ~(rep_name IN FDOM (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt)))) /\
      ~(abs_name = rep_name) /\
      type_ok (alist_to_fmap (FLAT (MAP types_of_upd' ctxt))) (typeof witness)
      ==> (little_TypeDefn name pred abs_name rep_name) updates' ctxt) /\
   (!arity ctxt name.
      ~(name IN FDOM (alist_to_fmap (FLAT (MAP types_of_upd' ctxt)))) /\
      ~(name IN FDOM (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt))))
      ==> (NewEliminableType name arity) updates' ctxt) /\
   (!ctxt name ty.
      ~(name IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt)))) /\
      ~(name IN FDOM (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt)))) /\
      type_ok (FUNION (alist_to_fmap (FLAT (MAP types_of_upd' ctxt))) (alist_to_fmap (FLAT
        (MAP etypes_of_upd' ctxt)))) ty
      ==> (NewEliminableConst name ty) updates' ctxt) /\
   (!ctxt prop.
      prop has_type Tyapp (implode "bool") [] /\
      term_ok' (ethy_REC (alist_to_fmap (FLAT (MAP consts_of_upd' ctxt))) (alist_to_fmap (FLAT
        (MAP types_of_upd' ctxt))) (set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd' upd)
        (conexts_of_upd' upd)) ctxt))) (alist_to_fmap (FLAT (MAP econsts_of_upd' ctxt)))
        (alist_to_fmap (FLAT (MAP etypes_of_upd' ctxt))) (set_of_list (FLAT
        (MAP eaxexts_of_upd' ctxt)))) prop /\
      (!x ty1 ty2.
         VFREE_IN (hol_Var x ty1) prop /\ VFREE_IN (hol_Var x ty2) prop ==> ty1 = ty2)
      ==> (NewEliminableAxiom prop) updates' ctxt)`;;

parse_as_infix("extends'",(12,"right"));;

let extends'_def = cake_def
  `(extends') = RTC (\ctxt2 ctxt1. ?upd. ctxt2 = CONS upd ctxt1 /\ upd updates' ctxt1)`;;

(* Initial theory context *)

let init_ectxt_def = cake_def
  `init_ectxt =
     [little_NewConst (implode "=")
        (Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "fun") [Tyvar
          (implode "A"); Tyapp (implode "bool") []]]);
      little_NewType (implode "bool") 0;
      little_NewType (implode "fun") 2]`;;
