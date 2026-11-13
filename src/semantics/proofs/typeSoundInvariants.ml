(* ========================================================================= *)
(* typeSoundInvariants: port of HOL4                                         *)
(* semantics/proofs/typeSoundInvariantsScript.sml (CakeML v3479).            *)
(* A type system for values, and the invariants that are used for type       *)
(* soundness.                                                                *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
needs "semantics/proofs/namespaceProps.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Notes on the rendering:                                                   *)
(* - HOL4's Type abbreviations tenv_store and ctMap are HOL Light type       *)
(*   abbreviations (new_type_abbrev).                                        *)
(* - Record fields: tenv.v is type_env_v tenv, env.c is sem_env_c env,       *)
(*   st.refs is state_refs st, st.next_type_stamp is state_next_type_stamp   *)
(*   st (sem_env and state of semanticPrimitives, type_env of typeSystem).   *)
(* - EVERY is ALL, LIST_REL is ALL2, FUPDATE_LIST FEMPTY l is FEMPTY |++ l,  *)
(*   ZIP (l1,l2) is ZIP l1 l2 (the only ZIP has the hypothesis               *)
(*   LENGTH tvs' = LENGTH ts' next to it).                                   *)
(* - HOL4's paired lambdas (\(a,b). t) are (\p. match p with (a,b) -> t);    *)
(*   for the premises of type_v the monotonicity theorem of pair_CASE        *)
(*   TYSYS2AUX_MONO_pair_CASE is added to monotonicity_theorems first.       *)
(* - The mlstring literal of x is implode "x".                               *)
(* ------------------------------------------------------------------------- *)

let store_t_INDUCT,store_t_RECURSION = cake_type
  "store_t = Ref_t t
           | W8array_t
           | Varray_t t";;

(* Store typing *)

new_type_abbrev("tenv_store",`:(num,store_t)fmap`);;

(* Check that the type names map to valid types *)

let tenv_abbrev_ok_def = cake_def
  `tenv_abbrev_ok (tenvT:tenv_abbrev) <=>
     nsAll (\id p. match p with (tvs,t) -> check_freevars 0 tvs t) tenvT`;;

let tenv_ctor_ok_def = cake_def
  `tenv_ctor_ok (tenvC:tenv_ctor) <=>
     nsAll (\id p. match p with (tvs,ts,tn) -> ALL (check_freevars 0 tvs) ts)
           tenvC`;;

let tenv_val_ok_def = cake_def
  `tenv_val_ok (tenvV:tenv_val) <=>
     nsAll (\id p. match p with (tvs,t) -> check_freevars tvs [] t) tenvV`;;

let tenv_ok_def = cake_def
  `tenv_ok (tenv:type_env) <=>
     tenv_val_ok (type_env_v tenv) /\
     tenv_ctor_ok (type_env_c tenv) /\
     tenv_abbrev_ok (type_env_t tenv)`;;

let tenv_val_exp_ok_def = cake_def
  `(tenv_val_exp_ok Empty <=> T) /\
   (tenv_val_exp_ok (Bind_tvar n tenv) <=> tenv_val_exp_ok tenv) /\
   (tenv_val_exp_ok (Bind_name x tvs t tenv) <=>
      check_freevars (tvs + num_tvs tenv) [] t /\
      tenv_val_exp_ok tenv)`;;

(* Global constructor type environments keyed by constructor name and type *)
(* stamp.  Contains the type variables, the type of the arguments, and the *)
(* identity of the type.                                                    *)

new_type_abbrev("ctMap",`:(stamp,(tvarN list # t list # type_ident))fmap`);;

(* FEVERY: no free variables in the range; exceptions have type exception, *)
(* and no type variables; primitive, non-constructor types are not mapped; *)
(* if type identities are equal then the stamps are from the same type.    *)

let ctMap_ok_def = cake_def
  `ctMap_ok (ctMap:ctMap) <=>
     FEVERY (\p. match p with
                   (stamp,(tvs,ts,_)) -> ALL (check_freevars 0 tvs) ts) ctMap /\
     (!ex tvs ts ti. FLOOKUP ctMap (ExnStamp ex) = SOME (tvs,ts,ti)
        ==> tvs = [] /\ ti = Texn_num) /\
     (!cn x tvs ts ti. FLOOKUP ctMap (TypeStamp cn x) = SOME (tvs,ts,ti)
        ==> ~MEM ti prim_type_nums) /\
     (!stamp1 tvs1 ts1 ti stamp2 tvs2 ts2.
        FLOOKUP ctMap stamp1 = SOME (tvs1,ts1,ti) /\
        FLOOKUP ctMap stamp2 = SOME (tvs2,ts2,ti)
        ==> same_type stamp1 stamp2)`;;

(* Check that a constructor type environment is consistent with a runtime  *)
(* type enviroment, using the full type keyed constructor type environment *)
(* to ensure that the correct types are used.                              *)

let type_ctor_def = cake_def
  `type_ctor (ctMap:ctMap) (_:A) (n,stamp) (tvs,ts,ti) <=>
     FLOOKUP ctMap stamp = SOME (tvs,ts,ti) /\
     LENGTH ts = n`;;

let add_tenvE_def = cake_def
  `(add_tenvE Empty (tenvV:tenv_val) = tenvV) /\
   (add_tenvE (Bind_tvar _ tenvE) tenvV = add_tenvE tenvE tenvV) /\
   (add_tenvE (Bind_name x tvs t tenvE) tenvV =
      nsBind x (tvs,t) (add_tenvE tenvE tenvV))`;;

(* monotonicity of pair_CASE, for the paired lambdas in the premises of    *)
(* type_v (HOL4's inductive package handles UNCURRY by itself)              *)

let TYSYS2AUX_MONO_pair_CASE = prove
 (`(!(a:A) (b:B). P a b ==> Q a b) ==>
   pair_CASE (x:A#B) P ==> (pair_CASE x Q:bool)`,
  SPEC_TAC(`x:A#B`,`x:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM; pair_CASE] THEN
  MESON_TAC[]);;

let () = monotonicity_theorems :=
  TYSYS2AUX_MONO_pair_CASE :: !monotonicity_theorems;;

let type_v_rules,type_v_ind,type_v_cases,type_v_strongind = cake_inductive
  `(!tvs (ctMap:ctMap) (tenvS:tenv_store) n.
      type_v tvs ctMap tenvS (Litv (IntLit n)) Tint) /\
   (!tvs (ctMap:ctMap) (tenvS:tenv_store) c.
      type_v tvs ctMap tenvS (Litv (Char c)) Tchar) /\
   (!tvs (ctMap:ctMap) (tenvS:tenv_store) s.
      type_v tvs ctMap tenvS (Litv (StrLit s)) Tstring) /\
   (!tvs (ctMap:ctMap) (tenvS:tenv_store) w.
      type_v tvs ctMap tenvS (Litv (Word8 w)) Tword8) /\
   (!tvs (ctMap:ctMap) (tenvS:tenv_store) w.
      type_v tvs ctMap tenvS (Litv (Word64 w)) Tword64) /\
   (!tvs (ctMap:ctMap) (tenvS:tenv_store) w.
      type_v tvs ctMap tenvS (Litv (Float64 w)) Tdouble) /\
   (!tvs (ctMap:ctMap) (tenvS:tenv_store) vs tvs' stamp ts' ts ti.
      ALL (check_freevars tvs []) ts' /\
      LENGTH tvs' = LENGTH ts' /\
      ALL2 (type_v tvs ctMap tenvS)
        vs (MAP (type_subst (FEMPTY |++ REVERSE (ZIP tvs' ts'))) ts) /\
      FLOOKUP ctMap stamp = SOME (tvs',ts,ti)
      ==> type_v tvs ctMap tenvS (Conv (SOME stamp) vs) (Tapp ts' ti)) /\
   (!tvs (ctMap:ctMap) (tenvS:tenv_store) vs ts.
      ALL2 (type_v tvs ctMap tenvS) vs ts
      ==> type_v tvs ctMap tenvS (Conv NONE vs) (Ttup ts)) /\
   (!tvs (ctMap:ctMap) (tenvS:tenv_store) env tenv tenvE n e t1 t2.
      tenv_ok tenv /\
      tenv_val_exp_ok tenvE /\
      num_tvs tenvE = 0 /\
      nsAll2 (type_ctor ctMap) (sem_env_c env) (type_env_c tenv) /\
      nsAll2 (\i v p. match p with (tvs,t) -> type_v tvs ctMap tenvS v t)
        (sem_env_v env) (add_tenvE tenvE (type_env_v tenv)) /\
      check_freevars tvs [] t1 /\
      type_e tenv (Bind_name n 0 t1 (bind_tvar tvs tenvE)) e t2
      ==> type_v tvs ctMap tenvS (Closure env n e) (Tfn t1 t2)) /\
   (!tvs (ctMap:ctMap) (tenvS:tenv_store) env funs n t tenv tenvE bindings.
      tenv_ok tenv /\
      tenv_val_exp_ok tenvE /\
      num_tvs tenvE = 0 /\
      nsAll2 (type_ctor ctMap) (sem_env_c env) (type_env_c tenv) /\
      nsAll2 (\i v p. match p with (tvs,t) -> type_v tvs ctMap tenvS v t)
        (sem_env_v env) (add_tenvE tenvE (type_env_v tenv)) /\
      type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE))
        funs bindings /\
      ALOOKUP bindings n = SOME t /\
      ALL_DISTINCT (MAP FST funs) /\
      MEM n (MAP FST funs)
      ==> type_v tvs ctMap tenvS (Recclosure env funs n) t) /\
   (!tvs (ctMap:ctMap) (tenvS:tenv_store) n t.
      check_freevars 0 [] t /\
      FLOOKUP tenvS n = SOME (Ref_t t)
      ==> type_v tvs ctMap tenvS (Loc T n) (Tref t)) /\
   (!tvs (ctMap:ctMap) (tenvS:tenv_store) n.
      FLOOKUP tenvS n = SOME W8array_t
      ==> type_v tvs ctMap tenvS (Loc T n) Tword8array) /\
   (!tvs (ctMap:ctMap) (tenvS:tenv_store) n t.
      check_freevars 0 [] t /\
      FLOOKUP tenvS n = SOME (Varray_t t)
      ==> type_v tvs ctMap tenvS (Loc T n) (Tarray t)) /\
   (!tvs (ctMap:ctMap) (tenvS:tenv_store) vs t.
      check_freevars 0 [] t /\
      ALL (\v. type_v tvs ctMap tenvS v t) vs
      ==> type_v tvs ctMap tenvS (Vectorv vs) (Tvector t))`;;

(* the clauses are parsed separately: v is a value in the first and a byte *)
(* list in the second                                                       *)

let type_sv_def = cake_def_clauses
  [`type_sv (ctMap:ctMap) (tenvS:tenv_store) (Refv v) (Ref_t t) <=>
      type_v 0 ctMap tenvS v t`;
   `type_sv (ctMap:ctMap) (tenvS:tenv_store) (W8array v:v store_v) W8array_t <=> T`;
   `type_sv (ctMap:ctMap) (tenvS:tenv_store) (Varray vs) (Varray_t t) <=>
      ALL (\v. type_v 0 ctMap tenvS v t) vs`;
   `type_sv (_:ctMap) (_:tenv_store) (_:v store_v) (_:store_t) <=> F`];;

(* The type of the store *)

let type_s_def = cake_def
  `type_s (ctMap:ctMap) (envS:(v store_v)list) (tenvS:tenv_store) <=>
     (!l.
       ((?st. FLOOKUP tenvS l = SOME st) <=>
        (?v. store_lookup l envS = SOME v)) /\
       (!st sv.
          FLOOKUP tenvS l = SOME st /\ store_lookup l envS = SOME sv
          ==> type_sv ctMap tenvS sv st))`;;

(* The global constructor type environment has the primitive exceptions in *)
(* it                                                                       *)

let ctMap_has_exns_def = cake_def
  `ctMap_has_exns (ctMap:ctMap) <=>
     FLOOKUP ctMap bind_stamp = SOME ([],[],Texn_num) /\
     FLOOKUP ctMap chr_stamp = SOME ([],[],Texn_num) /\
     FLOOKUP ctMap div_stamp = SOME ([],[],Texn_num) /\
     FLOOKUP ctMap subscript_stamp = SOME ([],[],Texn_num)`;;

(* The global constructor type environment has the list primitives in it *)

let ctMap_has_lists_def = cake_def
  `ctMap_has_lists (ctMap:ctMap) <=>
     FLOOKUP ctMap (TypeStamp (implode "[]") list_type_num) =
       SOME ([implode "'a"],[],Tlist_num) /\
     FLOOKUP ctMap (TypeStamp (implode "::") list_type_num) =
       SOME ([implode "'a"],
             [Tvar (implode "'a"); Tlist (Tvar (implode "'a"))],Tlist_num) /\
     (!cn. ~(cn = implode "::") /\ ~(cn = implode "[]")
           ==> FLOOKUP ctMap (TypeStamp cn list_type_num) = NONE)`;;

(* The global constructor type environment has the bool primitives in it *)

let ctMap_has_bools_def = cake_def
  `ctMap_has_bools (ctMap:ctMap) <=>
     FLOOKUP ctMap (TypeStamp (implode "True") bool_type_num) =
       SOME ([],[],Tbool_num) /\
     FLOOKUP ctMap (TypeStamp (implode "False") bool_type_num) =
       SOME ([],[],Tbool_num) /\
     (!cn. ~(cn = implode "True") /\ ~(cn = implode "False")
           ==> FLOOKUP ctMap (TypeStamp cn bool_type_num) = NONE)`;;

let good_ctMap_def = cake_def
  `good_ctMap (ctMap:ctMap) <=>
     ctMap_ok ctMap /\
     ctMap_has_bools ctMap /\
     ctMap_has_exns ctMap /\
     ctMap_has_lists ctMap`;;

(* HOL4 keeps (commented out) weak_decls_only_mods, consistent_decls and   *)
(* decls_ok of the module system.                                           *)

let consistent_ctMap_def = cake_def
  `consistent_ctMap (st:(FFI)state) (type_ids:num->bool) (ctMap:ctMap) <=>
     DISJOINT type_ids (FRANGE ((SND o SND) o_f ctMap)) /\
     !cn id.
       (TypeStamp cn id IN FDOM ctMap ==> id < state_next_type_stamp st) /\
       (ExnStamp id IN FDOM ctMap ==> id < state_next_exn_stamp st)`;;

let type_all_env_def = cake_def
  `type_all_env (ctMap:ctMap) (tenvS:tenv_store) (env:(v)sem_env)
                (tenv:type_env) <=>
     nsAll2 (type_ctor ctMap) (sem_env_c env) (type_env_c tenv) /\
     nsAll2 (\i v p. match p with (tvs,t) -> type_v tvs ctMap tenvS v t)
            (sem_env_v env) (type_env_v tenv)`;;

let type_sound_invariant_def = cake_def
  `type_sound_invariant (st:(FFI)state) (env:(v)sem_env) (ctMap:ctMap)
                        (tenvS:tenv_store) (type_idents:num->bool)
                        (tenv:type_env) <=>
     tenv_ok tenv /\
     good_ctMap ctMap /\
     consistent_ctMap st type_idents ctMap /\
     type_all_env ctMap tenvS env tenv /\
     type_s ctMap (state_refs st) tenvS`;;
