(* ========================================================================= *)
(* holSyntax: port of HOL4 candle/standard/syntax/holSyntaxScript.sml        *)
(* (CakeML v3479).  Defines the HOL inference system: types, terms, typing,  *)
(* alpha-equivalence, substitution, type instantiation, the proof relation   *)
(* and the context updates.                                                  *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: the HOL4 types type and term are           *)
(*   hol_type (constructors Tyvar, Tyapp) and hol_term (hol_Var, hol_Const,  *)
(*   hol_Comb, hol_Abs); domain is hol_domain, term_ok is hol_term_ok, the   *)
(*   update constructors are hol_ConstSpec, hol_TypeDefn, hol_NewType,       *)
(*   hol_NewConst, hol_NewAxiom.  HOL4's === is the constant equation and    *)
(*   HOL4's |- the inductive relation proves; both keep HOL4's infix         *)
(*   notation (=== and |-, through the interface, as in HOL Light's own      *)
(*   Model/syntax.ml); has_type, updates and extends are infixes too.        *)
(* - HOL4 Overloads are notation only (HOL4 stores the expanded terms), so   *)
(*   they are written out here, and in the files that load this one:         *)
(*     Fun s t        Tyapp (implode "fun") [s; t]                           *)
(*     Bool           Tyapp (implode "bool") []                              *)
(*     Equal ty       hol_Const (implode "=") (Fun ty (Fun ty Bool))         *)
(*     is_instance ty0 ty   ?i. ty = TYPE_SUBST i ty0                        *)
(*     tysof sig, tmsof sig       FST sig, SND sig                           *)
(*     sigof thy, axsof thy       FST thy, SND thy                           *)
(*     tysof thy, tmsof thy       FST (FST thy), SND (FST thy)               *)
(*                                (HOL4: (FST o FST) thy, (SND o FST) thy)   *)
(*     type_list ctxt, const_list ctxt                                       *)
(*                    FLAT (MAP types_of_upd ctxt), FLAT (MAP consts_of_upd  *)
(*                    ctxt)                                                  *)
(*     tysof ctxt     alist_to_fmap (FLAT (MAP types_of_upd ctxt))           *)
(*     tmsof ctxt     alist_to_fmap (FLAT (MAP consts_of_upd ctxt))          *)
(*     sigof ctxt     (tysof ctxt, tmsof ctxt)                               *)
(*     axexts ctxt, conexts ctxt  FLAT (MAP axexts_of_upd ctxt), ..          *)
(*     axioms_of_upd upd  APPEND (axexts_of_upd upd) (conexts_of_upd upd)    *)
(*     axiom_list ctxt    FLAT (MAP (\upd. axioms_of_upd upd) ctxt)          *)
(*     axsof ctxt         set_of_list (axiom_list ctxt)                      *)
(*     thyof ctxt         (sigof ctxt, axsof ctxt)                           *)
(*   with the inner overloads expanded too.                                  *)
(* - mlstring literals are implode "..."; EVERY is ALL, EXISTS is EX, FOLDR  *)
(*   f e l is ITLIST f l e, GENLIST f n is list_of_seq f n, #"'" is CHR 39;  *)
(*   the type abbreviations tysig, tmsig, sig, thy are HOL Light ones.       *)
(* - The variable abs of HOL4 (a HOL Light interface name) is abs_name, and  *)
(*   rep beside it rep_name.                                                 *)
(* - The rules of the inductive definitions quantify their variables in      *)
(*   HOL4's order (Inductive generalises the free variables of a rule in the *)
(*   order of their names), so the rule and cases theorems match HOL4's.     *)
(* - HOL4 [mono] theorems LEX_MONO and LLEX_MONO (pair and list theories),   *)
(*   which the inductive definitions type_lt and term_lt need, are the local *)
(*   CSYNAUX_LEX_MONO and CSYNAUX_LLEX_MONO.                                 *)
(* - Local helpers that are not HOL4 theorems are CSYNAUX_.                  *)
(* - HOL4 tyvars is hol_tyvars (a short or common word), with the theorems   *)
(*   renamed alike (tyvars_def is hol_tyvars_def, ...).                      *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;
needs "hol4/toto.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL types *)

let hol_type_INDUCT,hol_type_RECURSION =
  cake_type "hol_type = Tyvar mlstring | Tyapp mlstring (hol_type list)";;

(* HOL4: Definition domain_raw *)
let hol_domain_raw = cake_def
  `hol_domain ty = match ty with Tyapp n (CONS x xs) -> x | _ -> ty`;;

let hol_domain_def = prove
 (`!t s. hol_domain (Tyapp (implode "fun") [s; t]) = s`,
  SIMP[hol_domain_raw]);;
let _ = cake_add_simps [hol_domain_def];;

let codomain_raw = cake_def
  `codomain ty = match ty with Tyapp n (CONS y (CONS x xs)) -> x | _ -> ty`;;

let codomain_def = prove
 (`!t s. codomain (Tyapp (implode "fun") [s; t]) = t`,
  SIMP[codomain_raw]);;
let _ = cake_add_simps [codomain_def];;

(* HOL4 type_rec_tac (an ML termination tactic) is TERM_TAC here. *)

(* HOL terms *)

let hol_term_INDUCT,hol_term_RECURSION =
  cake_type "hol_term = hol_Var mlstring hol_type | hol_Const mlstring hol_type |
                        hol_Comb hol_term hol_term | hol_Abs hol_term hol_term";;

let dest_var_def = cake_def
  `dest_var (hol_Var x ty) = (x,ty)`;;
let _ = cake_add_simps [dest_var_def];;

(* Assignment of types to terms (where possible) *)

parse_as_infix("has_type",(12,"right"));;

let has_type_rules,has_type_ind,has_type_cases,has_type_strongind = cake_inductive
  `(!n ty. (hol_Var n ty) has_type ty) /\
   (!n ty. (hol_Const n ty) has_type ty) /\
   (!dty rty s t.
      s has_type (Tyapp (implode "fun") [dty; rty]) /\
      t has_type dty
      ==> (hol_Comb s t) has_type rty) /\
   (!dty n rty t.
      t has_type rty
      ==> (hol_Abs (hol_Var n dty) t) has_type (Tyapp (implode "fun") [dty; rty]))`;;

(* A term is welltyped if it has a type. typeof calculates it. *)

let welltyped_def = cake_def
  `welltyped tm <=> ?ty. tm has_type ty`;;

let typeof_def = cake_def
  `(typeof (hol_Var n ty) = ty) /\
   (typeof (hol_Const n ty) = ty) /\
   (typeof (hol_Comb s t) = codomain (typeof s)) /\
   (typeof (hol_Abs v t) = Tyapp (implode "fun") [typeof v; typeof t])`;;
let _ = cake_add_simps [typeof_def];;

(* Auxiliary relation used to define alpha-equivalence. This relation is
   parameterised by the lists of variables bound above the terms. *)

let RACONV_rules,RACONV_ind,RACONV_cases,RACONV_strongind = cake_inductive
  `(!env ty1 ty2 x1 x2.
      ALPHAVARS env (hol_Var x1 ty1,hol_Var x2 ty2)
      ==> RACONV env (hol_Var x1 ty1,hol_Var x2 ty2)) /\
   (!env ty x. RACONV env (hol_Const x ty,hol_Const x ty)) /\
   (!env s1 s2 t1 t2.
      RACONV env (s1,s2) /\ RACONV env (t1,t2)
      ==> RACONV env (hol_Comb s1 t1,hol_Comb s2 t2)) /\
   (!env t1 t2 v1 v2.
      typeof v1 = typeof v2 /\ RACONV (CONS (v1,v2) env) (t1,t2)
      ==> RACONV env (hol_Abs v1 t1,hol_Abs v2 t2))`;;

(* Alpha-equivalence. *)

let ACONV_def = cake_def
  `ACONV t1 t2 <=> RACONV [] (t1,t2)`;;

(* Term ordering, respecting alpha-equivalence *)

(* HOL4 [mono] theorems of the pair and list theories *)
let CSYNAUX_LEX_MONO = prove
 (`(!x y. (R1:A->A->bool) x y ==> R2 x y) /\
   (!x y. (R3:B->B->bool) x y ==> R4 x y)
   ==> (R1 LEX R3) x y ==> (R2 LEX R4) x y`,
  REWRITE_TAC[LEX_DEF] THEN MESON_TAC[]);;

let CSYNAUX_LLEX_MONO = prove
 (`(!x y. (R1:A->A->bool) x y ==> R2 x y) ==> LLEX R1 x y ==> LLEX R2 x y`,
  DISCH_TAC THEN SPEC_TAC(`y:A list`,`y:A list`) THEN
  SPEC_TAC(`x:A list`,`x:A list`) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LLEX_def; list_CASE; NOT_CONS_NIL] THEN ASM_MESON_TAC[]);;

let () = monotonicity_theorems :=
  [CSYNAUX_LEX_MONO; CSYNAUX_LLEX_MONO] @ !monotonicity_theorems;;

let type_lt_rules,type_lt_ind,type_lt_cases,type_lt_strongind = cake_inductive
  `(!x1 x2. mlstring_lt x1 x2 ==> type_lt (Tyvar x1) (Tyvar x2)) /\
   (!args2 x1 x2. type_lt (Tyvar x1) (Tyapp x2 args2)) /\
   (!args1 args2 x1 x2.
      (mlstring_lt LEX LLEX type_lt) (x1,args1) (x2,args2)
      ==> type_lt (Tyapp x1 args1) (Tyapp x2 args2))`;;

let term_lt_rules,term_lt_ind,term_lt_cases,term_lt_strongind = cake_inductive
  `(!ty1 ty2 x1 x2.
      (mlstring_lt LEX type_lt) (x1,ty1) (x2,ty2)
      ==> term_lt (hol_Var x1 ty1) (hol_Var x2 ty2)) /\
   (!ty1 ty2 x1 x2. term_lt (hol_Var x1 ty1) (hol_Const x2 ty2)) /\
   (!t1 t2 ty1 x1. term_lt (hol_Var x1 ty1) (hol_Comb t1 t2)) /\
   (!t1 t2 ty1 x1. term_lt (hol_Var x1 ty1) (hol_Abs t1 t2)) /\
   (!ty1 ty2 x1 x2.
      (mlstring_lt LEX type_lt) (x1,ty1) (x2,ty2)
      ==> term_lt (hol_Const x1 ty1) (hol_Const x2 ty2)) /\
   (!t1 t2 ty1 x1. term_lt (hol_Const x1 ty1) (hol_Comb t1 t2)) /\
   (!t1 t2 ty1 x1. term_lt (hol_Const x1 ty1) (hol_Abs t1 t2)) /\
   (!s1 s2 t1 t2.
      (term_lt LEX term_lt) (s1,s2) (t1,t2)
      ==> term_lt (hol_Comb s1 s2) (hol_Comb t1 t2)) /\
   (!s1 s2 t1 t2. term_lt (hol_Comb s1 s2) (hol_Abs t1 t2)) /\
   (!s1 s2 t1 t2.
      (term_lt LEX term_lt) (s1,s2) (t1,t2)
      ==> term_lt (hol_Abs s1 s2) (hol_Abs t1 t2))`;;

let term_cmp_def = cake_def
  `term_cmp = TO_of_LinearOrder term_lt`;;

let type_cmp_def = cake_def
  `type_cmp = TO_of_LinearOrder type_lt`;;

let ordav_def = cake_def
  `(ordav [] x1 x2 = term_cmp x1 x2) /\
   (ordav (CONS (t1,t2) env) x1 x2 =
      if x1 = t1 then
        if x2 = t2 then EQUAL
        else LESS
      else if x2 = t2 then GREATER
      else ordav env x1 x2)`;;

let ordav_ind = cake_ind "ordav";;

let orda_def = cake_def
  `orda env t1 t2 =
     if t1 = t2 /\ env = [] then EQUAL else
       match (t1,t2) with
         (hol_Var _ _, hol_Var _ _) -> ordav env t1 t2
       | (hol_Const _ _, hol_Const _ _) -> term_cmp t1 t2
       | (hol_Comb s1 t1, hol_Comb s2 t2) ->
           (let c = orda env s1 s2 in
              if ~(c = EQUAL) then c else orda env t1 t2)
       | (hol_Abs s1 t1, hol_Abs s2 t2) ->
           (let c = type_cmp (typeof s1) (typeof s2) in
              if ~(c = EQUAL) then c else orda (CONS (s1,s2) env) t1 t2)
       | (hol_Var _ _, _) -> LESS
       | (_, hol_Var _ _) -> GREATER
       | (hol_Const _ _, _) -> LESS
       | (_, hol_Const _ _) -> GREATER
       | (hol_Comb _ _, _) -> LESS
       | (_, hol_Comb _ _) -> GREATER`;;

let orda_ind = cake_ind "orda";;

let term_union_def = cake_def
  `term_union l1 l2 =
     match (l1,l2) with
       ([],l2) -> l2
     | (l1,[]) -> l1
     | (CONS h1 t1, CONS h2 t2) ->
         let c = orda [] h1 h2 in
         if c = EQUAL then CONS h1 (term_union t1 t2)
         else if c = LESS then CONS h1 (term_union t1 l2)
         else CONS h2 (term_union (CONS h1 t1) t2)`;;

let term_remove_def = cake_def
  `term_remove t l =
     match l with
       [] -> l
     | CONS s ss ->
         let c = orda [] t s in
         if c = GREATER then
           let ss' = term_remove t ss in
           if ss' = ss then l else CONS s ss'
         else if c = EQUAL then ss else l`;;

let term_image_def = cake_def
  `term_image f l =
     match l with
       [] -> l
     | CONS h t ->
         let h' = f h in
         let t' = term_image f t in
         if h' = h /\ t' = t then l
         else term_union [h'] t'`;;

(* Whether a variables (or constant) occurs free in a term. *)

let VFREE_IN_def = cake_def
  `(VFREE_IN v (hol_Var x ty) <=> hol_Var x ty = v) /\
   (VFREE_IN v (hol_Const x ty) <=> hol_Const x ty = v) /\
   (VFREE_IN v (hol_Comb s t) <=> VFREE_IN v s \/ VFREE_IN v t) /\
   (VFREE_IN v (hol_Abs w t) <=> ~(w = v) /\ VFREE_IN v t)`;;
let _ = cake_add_simps [VFREE_IN_def];;

(* Closed terms: those with no free variables. *)

let CLOSED_def = cake_def
  `CLOSED tm <=> !x ty. ~(VFREE_IN (hol_Var x ty) tm)`;;

(* Producing a variant of a variable, guaranteed
   to not be free in a given term. *)

let VFREE_IN_FINITE = prove
 (`!t. FINITE {x | VFREE_IN x t}`,
  MATCH_MP_TAC hol_term_INDUCT THEN
  REWRITE_TAC[VFREE_IN_def; SING_GSPEC; FINITE_SING] THEN
  REWRITE_TAC[SET_RULE `{x:hol_term | P x \/ Q x} = {x | P x} UNION {x | Q x}`;
              FINITE_UNION] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x | VFREE_IN x a1}` THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let VFREE_IN_FINITE_ALT = prove
 (`!t ty. FINITE {x | VFREE_IN (hol_Var (implode x) ty) t}`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\x. hol_Var (implode x) ty`; `{x | VFREE_IN x t}`]
    FINITE_IMAGE_INJ) THEN
  REWRITE_TAC[VFREE_IN_FINITE; IN_ELIM_THM; injectivity "hol_term";
              injectivity "mlstring"] THEN
  MESON_TAC[]);;

let PRIMED_NAME_EXISTS = prove
 (`?n. ~(VFREE_IN (hol_Var (implode (APPEND x (list_of_seq (combin_K (CHR 39)) n))) ty) t)`,
  REWRITE_TAC[GSYM NOT_FORALL_THM] THEN DISCH_TAC THEN
  MP_TAC PRIMED_INFINITE THEN REWRITE_TAC[INFINITE] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x | VFREE_IN (hol_Var (implode x) ty) t}` THEN
  REWRITE_TAC[VFREE_IN_FINITE_ALT; SUBSET; IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

(* HOL4: LEAST_EXISTS [local] *)
let hol_LEAST_EXISTS = prove
 (`(?n:num. P n) ==> ?k. P k /\ !m. m < k ==> ~(P m)`,
  MESON_TAC[num_WOP]);;

let VARIANT_PRIMES_def = new_specification ["VARIANT_PRIMES"]
 (prove
   (`?f. !t x ty.
       ~VFREE_IN (hol_Var (implode (APPEND x (list_of_seq (combin_K (CHR 39))
                                              (f t x ty)))) ty) t /\
       !m. m < f t x ty
           ==> VFREE_IN (hol_Var (implode (APPEND x (list_of_seq (combin_K (CHR 39))
                                                   m))) ty) t`,
    REWRITE_TAC[GSYM SKOLEM_THM] THEN REPEAT GEN_TAC THEN
    MP_TAC(MATCH_MP hol_LEAST_EXISTS PRIMED_NAME_EXISTS) THEN
    REWRITE_TAC[]));;

let VARIANT_def = cake_def
  `VARIANT t x ty =
     implode (APPEND x (list_of_seq (combin_K (CHR 39)) (VARIANT_PRIMES t x ty)))`;;

let VARIANT_THM = prove
 (`!t x ty. ~VFREE_IN (hol_Var (VARIANT t x ty) ty) t`,
  MESON_TAC[VARIANT_def; VARIANT_PRIMES_def]);;

(* Substitution for type variables in a type. *)

(* The third HOL4 clause (Fun ty1 ty2, a Tyapp) is an instance of the        *)
(* second: the definition has two clauses, TYPE_SUBST_def all three.        *)
let CSYNAUX_TYPE_SUBST_raw =
  cake_def_wf `MEASURE (\(i:(hol_type#hol_type)list,ty). hol_type_size ty)`
  TERM_TAC
  `(TYPE_SUBST i (Tyvar v) = REV_ASSOCD (Tyvar v) i (Tyvar v)) /\
   (TYPE_SUBST i (Tyapp v tys) = Tyapp v (MAP (TYPE_SUBST i) tys))`;;

let TYPE_SUBST_def = prove
 (`(!i v. TYPE_SUBST i (Tyvar v) = REV_ASSOCD (Tyvar v) i (Tyvar v)) /\
   (!i v tys. TYPE_SUBST i (Tyapp v tys) = Tyapp v (MAP (TYPE_SUBST i) tys)) /\
   (!i ty1 ty2.
      TYPE_SUBST i (Tyapp (implode "fun") [ty1; ty2]) =
      Tyapp (implode "fun") [TYPE_SUBST i ty1; TYPE_SUBST i ty2])`,
  REWRITE_TAC[CSYNAUX_TYPE_SUBST_raw; MAP]);;
let _ = cake_add_simps [TYPE_SUBST_def];;

let TYPE_SUBST_ind = cake_ind "TYPE_SUBST";;

(* Substitution for term variables in a term. *)

let VSUBST_def = cake_def
  `(VSUBST ilist (hol_Var x ty) = REV_ASSOCD (hol_Var x ty) ilist (hol_Var x ty)) /\
   (VSUBST ilist (hol_Const x ty) = hol_Const x ty) /\
   (VSUBST ilist (hol_Comb s t) = hol_Comb (VSUBST ilist s) (VSUBST ilist t)) /\
   (VSUBST ilist (hol_Abs v t) =
      let ilist' = FILTER (\(s',s). ~(s = v)) ilist in
      let t' = VSUBST ilist' t in
      if EX (\(s',s). VFREE_IN v s' /\ VFREE_IN s t) ilist'
      then let (x,ty) = dest_var v in
           let z = hol_Var (VARIANT t' (explode x) ty) ty in
           let ilist'' = CONS (z,v) ilist' in
           hol_Abs z (VSUBST ilist'' t)
      else hol_Abs v t')`;;

(* A measure on terms, used in proving
   termination of type instantiation. *)

let sizeof_def = cake_def
  `(sizeof (hol_Var x ty) = 1) /\
   (sizeof (hol_Const x ty) = 1) /\
   (sizeof (hol_Comb s t) = 1 + sizeof s + sizeof t) /\
   (sizeof (hol_Abs v t) = 2 + sizeof t)`;;
let _ = cake_add_simps [sizeof_def];;

let SIZEOF_VSUBST = prove
 (`!t ilist. (!s' s. MEM (s',s) ilist ==> ?x ty. s' = hol_Var x ty)
             ==> sizeof (VSUBST ilist t) = sizeof t`,
  MATCH_MP_TAC hol_term_INDUCT THEN REWRITE_TAC[VSUBST_def; sizeof_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`ilist:(hol_term#hol_term)list`; `hol_Var a0 a1`;
                   `hol_Var a0 a1`] REV_ASSOCD_MEM) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[sizeof_def] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`REV_ASSOCD (hol_Var a0 a1) ilist (hol_Var a0 a1)`; `hol_Var a0 a1`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[sizeof_def];
    ASM_SIMP_TAC[];
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN COND_CASES_TAC THEN
    TRY(PAIR_CASES_ON `dest_var a0`) THEN SIMP[sizeof_def; EQ_ADD_LCANCEL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[MEM; MEM_FILTER; PAIR_EQ] THEN ASM_MESON_TAC[]]);;

let sizeof_positive = prove
 (`!t. 0 < sizeof t`,
  MATCH_MP_TAC hol_term_INDUCT THEN REWRITE_TAC[sizeof_def] THEN ARITH_TAC);;

(* Instantiation of type variables in terms *)

(* the renaming in the Abs case keeps the size (for termination) *)
let CSYNAUX_SIZEOF_VSUBST_VAR = prove
 (`!x ty y ty' t. sizeof (VSUBST [hol_Var x ty,hol_Var y ty'] t) = sizeof t`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SIZEOF_VSUBST THEN
  REWRITE_TAC[MEM; PAIR_EQ] THEN MESON_TAC[]);;

let INST_CORE_def = cake_def_wf
  `MEASURE (\(env:(hol_term#hol_term)list,tyin:(hol_type#hol_type)list,tm).
              sizeof tm)`
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[sizeof_def; CSYNAUX_SIZEOF_VSUBST_VAR]) THEN
   ASM_REWRITE_TAC[sizeof_def; CSYNAUX_SIZEOF_VSUBST_VAR] THEN ASM_ARITH_TAC)
  `(INST_CORE env tyin (hol_Var x ty) =
      let tm = hol_Var x ty in
      let tm' = hol_Var x (TYPE_SUBST tyin ty) in
      if REV_ASSOCD tm' env tm = tm then hol_Result tm' else Clash tm') /\
   (INST_CORE env tyin (hol_Const x ty) =
      hol_Result (hol_Const x (TYPE_SUBST tyin ty))) /\
   (INST_CORE env tyin (hol_Comb s t) =
      let sres = INST_CORE env tyin s in
      if IS_CLASH sres then sres else
      let tres = INST_CORE env tyin t in
      if IS_CLASH tres then tres else
      let s' = RESULT sres and t' = RESULT tres in
      hol_Result (hol_Comb s' t')) /\
   (INST_CORE env tyin (hol_Abs v t) =
      let (x,ty) = dest_var v in
      let ty' = TYPE_SUBST tyin ty in
      let v' = hol_Var x ty' in
      let env' = CONS (v,v') env in
      let tres = INST_CORE env' tyin t in
      if IS_RESULT tres then hol_Result (hol_Abs v' (RESULT tres)) else
      let w = CLASH tres in
      if ~(w = v') then tres else
      let x' = VARIANT (RESULT (INST_CORE [] tyin t)) (explode x) ty' in
      let t' = VSUBST [hol_Var x' ty,hol_Var x ty] t in
      let ty' = TYPE_SUBST tyin ty in
      let env' = CONS (hol_Var x' ty,hol_Var x' ty') env in
      let tres = INST_CORE env' tyin t' in
      if IS_RESULT tres then hol_Result (hol_Abs (hol_Var x' ty') (RESULT tres))
      else tres)`;;

let INST_CORE_ind = cake_ind "INST_CORE";;

let INST_def = cake_def
  `INST tyin tm = RESULT (INST_CORE [] tyin tm)`;;

(* Type variables in a type. *)

let hol_tyvars_def = cake_def_wf `MEASURE hol_type_size` TERM_TAC
  `(hol_tyvars (Tyvar v) = [v]) /\
   (hol_tyvars (Tyapp v tys) = ITLIST (\x y. LIST_UNION (hol_tyvars x) y) tys [])`;;

let hol_tyvars_ind = cake_ind "hol_tyvars";;

(* Type variables in a term. *)

let tvars_def = cake_def
  `(tvars (hol_Var n ty) = hol_tyvars ty) /\
   (tvars (hol_Const n ty) = hol_tyvars ty) /\
   (tvars (hol_Comb s t) = LIST_UNION (tvars s) (tvars t)) /\
   (tvars (hol_Abs v t) = LIST_UNION (tvars v) (tvars t))`;;

(* Syntax for equations *)

(* HOL4: the infix ===, here the constant equation with the infix === *)
let equation_def = cake_def
  `equation s t =
     hol_Comb (hol_Comb (hol_Const (implode "=")
       (Tyapp (implode "fun") [typeof s;
          Tyapp (implode "fun") [typeof s; Tyapp (implode "bool") []]])) s) t`;;

parse_as_infix("===",(18,"right"));;
override_interface("===",`equation:hol_term->hol_term->hol_term`);;

(* Signature of a theory: indicates the defined type operators, with arities,
   and defined constants, with types. *)

new_type_abbrev("tysig",`:(mlstring,num)fmap`);;
new_type_abbrev("tmsig",`:(mlstring,hol_type)fmap`);;
new_type_abbrev("sig",`:tysig#tmsig`);;

(* Well-formedness of types/terms with respect to a signature *)

let type_ok_def = cake_def_wf
  `MEASURE (\(tysig:(mlstring,num)fmap,ty). hol_type_size ty)` TERM_TAC
  `(type_ok tysig (Tyvar _) <=> T) /\
   (type_ok tysig (Tyapp name args) <=>
      FLOOKUP tysig name = SOME (LENGTH args) /\
      ALL (type_ok tysig) args)`;;

let type_ok_ind = cake_ind "type_ok";;

(* HOL4: term_ok.  The recursive call of the Abs clause is under ?x ty in  *)
(* HOL4 (TFL does not mind: the call does not depend on x and ty); HOL      *)
(* Light's recursion analysis needs it outside, so the definition has it    *)
(* there and hol_term_ok_def states HOL4's clauses.                         *)
let CSYNAUX_hol_term_ok_raw = cake_def_wf
  `MEASURE (\(sig:sig,tm). hol_term_size tm)` TERM_TAC
  `(hol_term_ok (sig:sig) (hol_Var x ty) <=> type_ok (FST sig) ty) /\
   (hol_term_ok sig (hol_Const name ty) <=>
      ?ty0. FLOOKUP (SND sig) name = SOME ty0 /\
            type_ok (FST sig) ty /\
            (?i. ty = TYPE_SUBST i ty0)) /\
   (hol_term_ok sig (hol_Comb tm1 tm2) <=>
      hol_term_ok sig tm1 /\
      hol_term_ok sig tm2 /\
      welltyped (hol_Comb tm1 tm2)) /\
   (hol_term_ok sig (hol_Abs v tm) <=>
      (?x ty. v = hol_Var x ty /\ type_ok (FST sig) ty) /\
      hol_term_ok sig tm)`;;

let hol_term_ok_def = prove
 (`(!sig x ty. hol_term_ok (sig:sig) (hol_Var x ty) <=> type_ok (FST sig) ty) /\
   (!sig name ty.
      hol_term_ok sig (hol_Const name ty) <=>
      ?ty0. FLOOKUP (SND sig) name = SOME ty0 /\
            type_ok (FST sig) ty /\
            (?i. ty = TYPE_SUBST i ty0)) /\
   (!sig tm1 tm2.
      hol_term_ok sig (hol_Comb tm1 tm2) <=>
      hol_term_ok sig tm1 /\
      hol_term_ok sig tm2 /\
      welltyped (hol_Comb tm1 tm2)) /\
   (!sig v tm.
      hol_term_ok sig (hol_Abs v tm) <=>
      ?x ty.
        v = hol_Var x ty /\
        type_ok (FST sig) ty /\
        hol_term_ok sig tm)`,
  REWRITE_TAC[CSYNAUX_hol_term_ok_raw] THEN MESON_TAC[]);;

(* Well-formed sets of hypotheses, represented as lists,
   are strictly sorted up to alpha-equivalence *)

let alpha_lt_def = cake_def
  `alpha_lt t1 t2 <=> orda [] t1 t2 = LESS`;;

let hypset_ok_def = cake_def
  `hypset_ok ls <=> SORTED alpha_lt ls`;;

(* A theory is a signature together with a set of axioms. It is well-formed if
   the types of the constants are all ok, the axioms are all ok terms of type
   bool, and the signature is standard. *)

new_type_abbrev("thy",`:sig#(hol_term->bool)`);;

(* Standard signature includes the minimal type operators and constants *)

let is_std_sig_def = cake_def
  `is_std_sig (sig:sig) <=>
     FLOOKUP (FST sig) (implode "fun") = SOME 2 /\
     FLOOKUP (FST sig) (implode "bool") = SOME 0 /\
     FLOOKUP (SND sig) (implode "=") =
       SOME (Tyapp (implode "fun") [Tyvar (implode "A");
               Tyapp (implode "fun") [Tyvar (implode "A");
                 Tyapp (implode "bool") []]])`;;

let theory_ok_def = cake_def
  `theory_ok (thy:thy) <=>
     (!ty. ty IN FRANGE (SND (FST thy)) ==> type_ok (FST (FST thy)) ty) /\
     (!p. p IN (SND thy) ==>
          hol_term_ok (FST thy) p /\ p has_type Tyapp (implode "bool") []) /\
     is_std_sig (FST thy)`;;

(* Sequents provable from a theory *)

(* HOL4: the infix |-, here the relation proves with the infix |- (below) *)
let proves_rules,proves_ind,proves_cases,proves_strongind = cake_inductive
  `(!h l r thy ty x.
      ~(EX (VFREE_IN (hol_Var x ty)) h) /\ type_ok (FST (FST thy)) ty /\
      proves (thy,h) (l === r)
      ==> proves (thy,h) (hol_Abs (hol_Var x ty) l === hol_Abs (hol_Var x ty) r)) /\
   (!p thy.
      theory_ok thy /\ p has_type Tyapp (implode "bool") [] /\
      hol_term_ok (FST thy) p
      ==> proves (thy,[p]) p) /\
   (!t thy ty x.
      theory_ok thy /\ type_ok (FST (FST thy)) ty /\ hol_term_ok (FST thy) t
      ==> proves (thy,[]) (hol_Comb (hol_Abs (hol_Var x ty) t) (hol_Var x ty) === t)) /\
   (!c1 c2 h1 h2 thy.
      proves (thy,h1) c1 /\
      proves (thy,h2) c2
      ==> proves (thy,term_union (term_remove c2 h1) (term_remove c1 h2))
                 (c1 === c2)) /\
   (!h1 h2 p p' q thy.
      proves (thy,h1) (p === q) /\
      proves (thy,h2) p' /\ ACONV p p'
      ==> proves (thy,term_union h1 h2) q) /\
   (!c h ilist thy.
      (!s s'. MEM (s',s) ilist
              ==> ?x ty. s = hol_Var x ty /\ s' has_type ty /\
                         hol_term_ok (FST thy) s') /\
      proves (thy,h) c
      ==> proves (thy,term_image (VSUBST ilist) h) (VSUBST ilist c)) /\
   (!c h thy tyin.
      ALL (type_ok (FST (FST thy))) (MAP FST tyin) /\
      proves (thy,h) c
      ==> proves (thy,term_image (INST tyin) h) (INST tyin c)) /\
   (!h1 h2 l1 l2 r1 r2 thy.
      proves (thy,h1) (l1 === r1) /\
      proves (thy,h2) (l2 === r2) /\
      welltyped (hol_Comb l1 l2)
      ==> proves (thy,term_union h1 h2) (hol_Comb l1 l2 === hol_Comb r1 r2)) /\
   (!t thy.
      theory_ok thy /\ hol_term_ok (FST thy) t
      ==> proves (thy,[]) (t === t)) /\
   (!c thy.
      theory_ok thy /\ c IN (SND thy)
      ==> proves (thy,[]) c)`;;

parse_as_infix("|-",(11,"right"));;
override_interface("|-",`proves:thy#(hol_term)list->hol_term->bool`);;

let proves_ABS,proves_ASSUME,proves_BETA,proves_DEDUCT_ANTISYM,proves_EQ_MP,
    proves_INST,proves_INST_TYPE,proves_MK_COMB,proves_REFL,proves_axioms =
  match CONJUNCTS proves_rules with
    [a;b;c;d;e;f;g;h;i;j] -> a,b,c,d,e,f,g,h,i,j
  | _ -> failwith "proves_rules";;

(* A context is a sequence of updates *)

(* hol_ConstSpec witnesses proposition: definition of new constants by    *)
(* specification; hol_TypeDefn name predicate abs_name rep_name: definition *)
(* of a new type operator; hol_NewType name arity; hol_NewConst name type;  *)
(* hol_NewAxiom proposition.                                                *)
let update_INDUCT,update_RECURSION = cake_type
  "update = hol_ConstSpec ((mlstring#hol_term) list) hol_term
          | hol_TypeDefn mlstring hol_term mlstring mlstring
          | hol_NewType mlstring num
          | hol_NewConst mlstring hol_type
          | hol_NewAxiom hol_term";;

(* Projecting out pieces of the context *)

(* Types and constants introduced by an update *)
let types_of_upd_def = cake_def
  `(types_of_upd (hol_ConstSpec _ _) = []) /\
   (types_of_upd (hol_TypeDefn name pred _ _) = [(name,LENGTH (tvars pred))]) /\
   (types_of_upd (hol_NewType name arity) = [(name,arity)]) /\
   (types_of_upd (hol_NewConst _ _) = []) /\
   (types_of_upd (hol_NewAxiom _) = [])`;;
let _ = cake_add_simps [types_of_upd_def];;

let consts_of_upd_def = cake_def
  `(consts_of_upd (hol_ConstSpec eqs prop) = MAP (\(s,t). (s,typeof t)) eqs) /\
   (consts_of_upd (hol_TypeDefn name pred abs_name rep_name) =
      let rep_type = hol_domain (typeof pred) in
      let abs_type =
        Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
      [(abs_name, Tyapp (implode "fun") [rep_type; abs_type]);
       (rep_name, Tyapp (implode "fun") [abs_type; rep_type])]) /\
   (consts_of_upd (hol_NewType _ _) = []) /\
   (consts_of_upd (hol_NewConst name type) = [(name,type)]) /\
   (consts_of_upd (hol_NewAxiom _) = [])`;;
let _ = cake_add_simps [consts_of_upd_def];;

(* HOL4 Overloads type_list, tysof, const_list, tmsof, sigof on contexts:   *)
(* written out (header).                                                     *)

(* Axioms: we divide them into axiomatic extensions and conservative
   extensions, we will prove that the latter preserve consistency *)
let axexts_of_upd_def = cake_def
  `(axexts_of_upd (hol_NewAxiom prop) = [prop]) /\
   (axexts_of_upd _ = [])`;;
let _ = cake_add_simps [axexts_of_upd_def];;

let conexts_of_upd_def = cake_def
  `(conexts_of_upd (hol_ConstSpec eqs prop) =
      let ilist = MAP (\(s,t). let ty = typeof t in (hol_Const s ty,hol_Var s ty)) eqs in
      [VSUBST ilist prop]) /\
   (conexts_of_upd (hol_TypeDefn name pred abs_name rep_name) =
      let abs_type =
        Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
      let rep_type = hol_domain (typeof pred) in
      let abs_tm = hol_Const abs_name (Tyapp (implode "fun") [rep_type; abs_type]) in
      let rep_tm = hol_Const rep_name (Tyapp (implode "fun") [abs_type; rep_type]) in
      let a = hol_Var (implode "a") abs_type in
      let r = hol_Var (implode "r") rep_type in
      [hol_Comb abs_tm (hol_Comb rep_tm a) === a;
       hol_Comb pred r === (hol_Comb rep_tm (hol_Comb abs_tm r) === r)]) /\
   (conexts_of_upd _ = [])`;;

(* HOL4 Overloads axexts, conexts, axioms_of_upd, axiom_list, axsof, thyof: *)
(* written out (header).                                                     *)

(* Principles for extending the context *)

parse_as_infix("updates",(12,"right"));;

(* The rules, in order (HOL4's comments): a new axiom, a new constant, a    *)
(* new specification, a new type, a new type definition.                    *)

let updates_rules,updates_ind,updates_cases,updates_strongind = cake_inductive
  `(!ctxt prop.
      prop has_type Tyapp (implode "bool") [] /\
      hol_term_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
                   alist_to_fmap (FLAT (MAP consts_of_upd ctxt))) prop
      ==> (hol_NewAxiom prop) updates ctxt) /\
   (!ctxt name ty.
      ~(name IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))) /\
      type_ok (alist_to_fmap (FLAT (MAP types_of_upd ctxt))) ty
      ==> (hol_NewConst name ty) updates ctxt) /\
   (!ctxt eqs prop.
      ((((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
          alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
         set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                              (conexts_of_upd upd)) ctxt))),
        MAP (\(s,t). hol_Var s (typeof t) === t) eqs) |- prop) /\
      ALL (\t. CLOSED t /\ (!v. MEM v (tvars t) ==> MEM v (hol_tyvars (typeof t))))
          (MAP SND eqs) /\
      (!x ty. VFREE_IN (hol_Var x ty) prop ==>
              MEM (x,ty) (MAP (\(s,t). (s,typeof t)) eqs)) /\
      (!s. MEM s (MAP FST eqs) ==>
           ~(s IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt))))) /\
      ALL_DISTINCT (MAP FST eqs)
      ==> (hol_ConstSpec eqs prop) updates ctxt) /\
   (!arity ctxt name.
      ~(name IN FDOM (alist_to_fmap (FLAT (MAP types_of_upd ctxt))))
      ==> (hol_NewType name arity) updates ctxt) /\
   (!abs_name ctxt name pred rep_name witness.
      ((((alist_to_fmap (FLAT (MAP types_of_upd ctxt)),
          alist_to_fmap (FLAT (MAP consts_of_upd ctxt))),
         set_of_list (FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
                                              (conexts_of_upd upd)) ctxt))),
        []) |- hol_Comb pred witness) /\
      CLOSED pred /\
      ~(name IN FDOM (alist_to_fmap (FLAT (MAP types_of_upd ctxt)))) /\
      ~(abs_name IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))) /\
      ~(rep_name IN FDOM (alist_to_fmap (FLAT (MAP consts_of_upd ctxt)))) /\
      ~(abs_name = rep_name)
      ==> (hol_TypeDefn name pred abs_name rep_name) updates ctxt)`;;

parse_as_infix("extends",(12,"right"));;

let extends_def = cake_def
  `(extends) = RTC (\ctxt2 ctxt1. ?upd. ctxt2 = CONS upd ctxt1 /\ upd updates ctxt1)`;;

(* Initial theory context *)

let init_ctxt_def = cake_def
  `init_ctxt =
     [hol_NewConst (implode "=")
        (Tyapp (implode "fun") [Tyvar (implode "A");
           Tyapp (implode "fun") [Tyvar (implode "A"); Tyapp (implode "bool") []]]);
      hol_NewType (implode "bool") 0;
      hol_NewType (implode "fun") 2]`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas used by several later files.                                       *)
(* ------------------------------------------------------------------------- *)

(* typeof (s === t) for any s and t (typeof_equation without its hypothesis) *)
let CSYNAUX_typeof_equation = prove
 (`!s t. typeof (s === t) = Tyapp (implode "bool") []`,
  REWRITE_TAC[equation_def; typeof_def; codomain_def]);;
