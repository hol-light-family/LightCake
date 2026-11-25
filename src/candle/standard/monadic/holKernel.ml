(* ========================================================================= *)
(* holKernel: port of HOL4 candle/standard/monadic/holKernelScript.sml       *)
(* (CakeML v3479).  The Candle kernel as shallowly embedded functions in HOL *)
(* in a monadic style, to pass around the state and propagate exceptions.    *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: every constant of the theory has *)
(*   the prefix holKernel_ (holKernel_mk_comb, holKernel_REFL, ...), and so  *)
(*   have the constructors Failure and Clash of hol_exn; the HOL4 types term *)
(*   and type are holSyntax's hol_term and hol_type (constructors hol_Var,   *)
(*   hol_Const, hol_Comb, hol_Abs, Tyvar, Tyapp), the update constructors    *)
(*   are hol_ConstSpec, hol_TypeDefn, hol_NewType, hol_NewConst,             *)
(*   hol_NewAxiom; holSyntaxExtra's frees and union are hol_frees and        *)
(*   hol_union.  HOL4's tyvars in this theory is holKernel_tyvars (holSyntax *)
(*   tyvars is hol_tyvars).                                                  *)
(* - HOL4's Type M = :(hol_refs, 'a, hol_exn) M (an abbreviation with a type *)
(*   variable, impossible in HOL Light) is written out:                      *)
(*   hol_refs->(A,hol_exn)exc#hol_refs.                                      *)
(* - The do-notation of the monad st_ex is written with the constants of     *)
(*   translator/monadic/monad_base/ml_monadBase.ml, as in infer.ml:          *)
(*   do x <- m; r od is st_ex_bind m (\x. r), do (a,b) <- m; r od is         *)
(*   st_ex_bind m (\p. match p with (a,b) -> r), do m; r od is               *)
(*   st_ex_ignore_bind m r, return x is st_ex_return x, m ++ m' is           *)
(*   m otherwise m'; HOL4 can is ml_monadBase_can.  HOL4 () is one.         *)
(* - The functions that HOL4 makes with ML automation (ml_monadBaseLib) are *)
(*   defined here with HOL4's equations, as in reg_alloc.ml:                 *)
(*   define_monad_access_funs: get_f = \state. (M_success state.f,state)    *)
(*     and set_f x = \state. (M_success one,state with f := x) for the four  *)
(*     fields of hol_refs (their exception type is a type variable, as in    *)
(*     HOL4);                                                                *)
(*   define_monad_exception_functions: raise_E and handle_E for the two      *)
(*     constructors E of hol_exn.                                            *)
(*   HOL4's local overloads failwith, raise_clash and handle_clash are       *)
(*   written out (holKernel_raise_Failure, holKernel_raise_Clash,            *)
(*   holKernel_handle_Clash).                                                *)
(* - mlstring literals are implode "..."; HOL4's s1 ^ s2 is strcat s1 s2     *)
(*   (left associative); EVERY is ALL, EXISTS is EX.                         *)
(* - A match on a literal mlstring (HOL4 patterns Tyapp <<fun>> [ty;_] and   *)
(*   Const <<=>> _) is written as a match on a variable and an equality test *)
(*   of it (the kit would compile the literal into a test of every bit of    *)
(*   every character); the definitions mean the same as HOL4's.              *)
(* - HOL4's paired lambdas \(t,x). e are HOL Light's paired lambdas.         *)
(* - The variables abs and rep of new_basic_type_definition are abs_tm and   *)
(*   rep_tm (abs is a HOL Light interface name).                             *)
(* - Local helpers that are not HOL4 theorems are HOLKAUX_.                  *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;
needs "basis/pure/mllist.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

prioritize_num();;
type_invention_error := true;;

(* we reuse the datatypes of types and terms from the inference system *)

(*
  type thm = Sequent of (term list * term)
*)

let thm_INDUCT,thm_RECURSION = cake_type "thm = Sequent (hol_term list) hol_term";;

(*
  We define a record that holds the state, i.e.

  let the_type_constants = ref ["bool",0; "fun",2]

  let the_term_constants =
     ref [("=", mk_fun_ty aty (mk_fun_ty aty bool_ty))]

  let the_axioms = ref ([]:thm list)

  The context is the global theory context tracked by the inference system,
  and subsumes the above references.  But we use them instead for efficiency
  (and to be close to HOL Light).
*)

let hol_refs_INFO = cake_record "hol_refs"
  ["the_type_constants","(mlstring#num)list";
   "the_term_constants","(mlstring#hol_type)list";
   "the_axioms","thm list";
   "the_context","update list"];;

let hol_refs_component_equality = hol_refs_INFO.ri_component_equality;;

(* the state-exception monad *)

let hol_exn_INDUCT,hol_exn_RECURSION = cake_type
  "hol_exn = holKernel_Failure mlstring | holKernel_Clash hol_term";;

(* HOL4: Type M = ``: (hol_refs, 'a, hol_exn) M``, written out *)

(* deref/ref functions (HOL4 define_monad_access_funs ``:hol_refs``) *)

let holKernel_get_the_type_constants_def = cake_def
  `(holKernel_get_the_type_constants:
      hol_refs->((mlstring#num)list,C)exc#hol_refs) =
     \state. (M_success (hol_refs_the_type_constants state),state)`;;

let holKernel_set_the_type_constants_def = cake_def
  `(holKernel_set_the_type_constants:
      (mlstring#num)list->hol_refs->(1,C)exc#hol_refs) x =
     \state. (M_success one,hol_refs_the_type_constants_fupd (K x) state)`;;

let holKernel_get_the_term_constants_def = cake_def
  `(holKernel_get_the_term_constants:
      hol_refs->((mlstring#hol_type)list,C)exc#hol_refs) =
     \state. (M_success (hol_refs_the_term_constants state),state)`;;

let holKernel_set_the_term_constants_def = cake_def
  `(holKernel_set_the_term_constants:
      (mlstring#hol_type)list->hol_refs->(1,C)exc#hol_refs) x =
     \state. (M_success one,hol_refs_the_term_constants_fupd (K x) state)`;;

let holKernel_get_the_axioms_def = cake_def
  `(holKernel_get_the_axioms:hol_refs->(thm list,C)exc#hol_refs) =
     \state. (M_success (hol_refs_the_axioms state),state)`;;

let holKernel_set_the_axioms_def = cake_def
  `(holKernel_set_the_axioms:thm list->hol_refs->(1,C)exc#hol_refs) x =
     \state. (M_success one,hol_refs_the_axioms_fupd (K x) state)`;;

let holKernel_get_the_context_def = cake_def
  `(holKernel_get_the_context:hol_refs->(update list,C)exc#hol_refs) =
     \state. (M_success (hol_refs_the_context state),state)`;;

let holKernel_set_the_context_def = cake_def
  `(holKernel_set_the_context:update list->hol_refs->(1,C)exc#hol_refs) x =
     \state. (M_success one,hol_refs_the_context_fupd (K x) state)`;;

(* failwith (HOL4 define_monad_exception_functions ``:hol_exn``            *)
(* ``:hol_refs``)                                                            *)

let holKernel_raise_Failure_def = cake_def
  `holKernel_raise_Failure (e1:mlstring) =
     \state:hol_refs. (M_failure (holKernel_Failure e1):(A,hol_exn)exc,state)`;;

let holKernel_raise_Clash_def = cake_def
  `holKernel_raise_Clash (e1:hol_term) =
     \state:hol_refs. (M_failure (holKernel_Clash e1):(A,hol_exn)exc,state)`;;

let holKernel_handle_Failure_def = cake_def
  `holKernel_handle_Failure (x:hol_refs->(A,hol_exn)exc#hol_refs)
                            (f:mlstring->hol_refs->(A,hol_exn)exc#hol_refs) =
     \state. match x state with
               (res,state) ->
                 (match res with
                    M_success y -> (M_success y,state)
                  | M_failure e ->
                      (match e with
                         holKernel_Failure e1 -> f e1 state
                       | holKernel_Clash e1 ->
                           (M_failure (holKernel_Clash e1),state)))`;;

let holKernel_handle_Clash_def = cake_def
  `holKernel_handle_Clash (x:hol_refs->(A,hol_exn)exc#hol_refs)
                          (f:hol_term->hol_refs->(A,hol_exn)exc#hol_refs) =
     \state. match x state with
               (res,state) ->
                 (match res with
                    M_success y -> (M_success y,state)
                  | M_failure e ->
                      (match e with
                         holKernel_Failure e1 ->
                           (M_failure (holKernel_Failure e1),state)
                       | holKernel_Clash e1 -> f e1 state))`;;

(* others *)

let holKernel_try_def = cake_def
  `holKernel_try (f:B->hol_refs->(A,hol_exn)exc#hol_refs) (x:B) msg =
     (f x otherwise holKernel_raise_Failure msg)`;;

(* define failing lookup function *)

let holKernel_assoc_def = cake_def
  `holKernel_assoc (s:A) (l:(A#B)list) =
     match l with
       [] -> holKernel_raise_Failure (implode "not in list")
     | CONS (x,y) xs -> if s = x then st_ex_return y else holKernel_assoc s xs`;;

let holKernel_assoc_ind = cake_ind "holKernel_assoc";;

let holKernel_map_def = cake_def
  `holKernel_map (f:A->B->(C,D)exc#B) l =
     match l with
       [] -> st_ex_return []
     | CONS h t -> st_ex_bind (f h) (\h.
                   st_ex_bind (holKernel_map f t) (\t.
                   st_ex_return (CONS h t)))`;;

let holKernel_map_ind = cake_ind "holKernel_map";;

(*
Definition app_def:
  app f l =
    pmatch l of
      [] => return ()
    | (h::t) => do f h ; app f t od
End

Definition first_def:
  first p l =
    pmatch l of
      [] => NONE
    | (h::t) => if p h then SOME h else first p t
End
*)

let holKernel_forall_def = cake_def
  `holKernel_forall (p:A->B->(bool,D)exc#B) l =
     match l with
       [] -> st_ex_return T
     | CONS h t -> st_ex_bind (p h) (\ok.
                   if ok then holKernel_forall p t else st_ex_return F)`;;

let holKernel_forall_ind = cake_ind "holKernel_forall";;

let holKernel_subset_def = cake_def
  `holKernel_subset (l1:A list) l2 = ALL (\t. MEM t l2) l1`;;

(*
  let types() = !the_type_constants
*)

let holKernel_types_def = cake_def
  `holKernel_types one =
     (holKernel_get_the_type_constants:
        hol_refs->((mlstring#num)list,C)exc#hol_refs)`;;

(*
  let get_type_arity s = assoc s (!the_type_constants)
*)

let holKernel_get_type_arity_def = cake_def
  `holKernel_get_type_arity s =
     st_ex_bind holKernel_get_the_type_constants (\l. holKernel_assoc s l)`;;

(*
  let new_type(name,arity) =
    if can get_type_arity name then
      failwith ("new_type: type "^name^" has already been declared")
    else the_type_constants := (name,arity)::(!the_type_constants)
*)

let holKernel_add_def_def = cake_def
  `holKernel_add_def d =
     st_ex_bind (holKernel_get_the_context:hol_refs->(update list,C)exc#hol_refs)
       (\defs. holKernel_set_the_context (CONS d defs))`;;

let holKernel_add_type_def = cake_def
  `holKernel_add_type (name,arity) =
     st_ex_bind (ml_monadBase_can holKernel_get_type_arity name) (\ok.
     if ok then holKernel_raise_Failure
                  (strcat (strcat (implode "new_type: ") name)
                          (implode " has already been declared"))
     else st_ex_bind holKernel_get_the_type_constants (\ts.
          holKernel_set_the_type_constants (CONS (name,arity) ts)))`;;

let holKernel_new_type_def = cake_def
  `holKernel_new_type (name,arity) =
     st_ex_ignore_bind (holKernel_add_type (name,arity))
       (holKernel_add_def (hol_NewType name arity))`;;

(*
  let mk_type(tyop,args) =
    let arity = try get_type_arity tyop with Failure _ ->
      failwith ("mk_type: type "^tyop^" has not been defined") in
    if arity = length args then
      Tyapp(tyop,args)
    else failwith ("mk_type: wrong number of arguments to "^tyop)
*)

let holKernel_mk_type_def = cake_def
  `holKernel_mk_type (tyop,args) =
     st_ex_bind
       (holKernel_try holKernel_get_type_arity tyop
          (strcat (strcat (implode "mk_type: type ") tyop)
                  (implode " has not been defined")))
       (\arity.
          if arity = LENGTH args then st_ex_return (Tyapp tyop args)
          else holKernel_raise_Failure
                 (strcat (implode "mk_type: wrong number of arguments to ") tyop))`;;

(*
  let mk_vartype v = Tyvar(v)
*)

let holKernel_mk_vartype_def = cake_def
  `holKernel_mk_vartype v = Tyvar v`;;

(*
  let dest_type =
    function
        (Tyapp (s,ty)) -> s,ty
      | (Tyvar _) -> failwith "dest_type: type variable not a constructor"
*)

let holKernel_dest_type_def = cake_def
  `holKernel_dest_type t =
     match t with
       Tyapp s ty -> st_ex_return (s,ty)
     | Tyvar _ -> holKernel_raise_Failure
                    (implode "dest_type: type variable not a constructor")`;;

(*
  let dest_vartype =
    function
        (Tyapp(_,_)) -> failwith "dest_vartype: type constructor not a variable"
      | (Tyvar s) -> s
*)

let holKernel_dest_vartype_def = cake_def
  `holKernel_dest_vartype t =
     match t with
       Tyapp _ _ -> holKernel_raise_Failure
                      (implode "dest_vartype: type constructor not a variable")
     | Tyvar s -> st_ex_return s`;;

(*
  let is_type = can dest_type
*)

let holKernel_is_type_def = cake_def
  `holKernel_is_type t = match t with Tyapp s ty -> T | _ -> F`;;

(*
  let is_vartype = can dest_vartype

  We optimise this by making it perform the pattern match directly.
*)

let holKernel_is_vartype_def = cake_def
  `holKernel_is_vartype t = match t with Tyvar _ -> T | _ -> F`;;

(*
  let rec tyvars =
      function
          (Tyapp(_,args)) -> itlist (union o tyvars) args []
        | (Tyvar v as tv) -> [tv]
*)

let holKernel_tyvars_def = cake_def_wf `MEASURE hol_type_size` TERM_TAC
  `holKernel_tyvars x =
     match x with
       Tyapp _ args -> itlist hol_union (MAP holKernel_tyvars args) []
     | Tyvar tv -> [tv]`;;

let holKernel_tyvars_ind = cake_ind "holKernel_tyvars";;

(*
  let rec type_subst i ty =
    match ty with
      Tyapp(tycon,args) ->
          let args' = qmap (type_subst i) args in
          if args' == args then ty else Tyapp(tycon,args')
      | _ -> rev_assocd ty i ty
*)

let holKernel_rev_assocd_def = cake_def
  `holKernel_rev_assocd (a:A) (l:(B#A)list) (d:B) =
     match l with
       [] -> d
     | CONS (x,y) l -> if y = a then x else holKernel_rev_assocd a l d`;;

let holKernel_type_subst_def =
  cake_def_wf `MEASURE (\(i:(hol_type#hol_type)list,ty). hol_type_size ty)`
  TERM_TAC
  `holKernel_type_subst i ty =
     match ty with
       Tyapp tycon args ->
         let args' = MAP (holKernel_type_subst i) args in
         if args' = args then ty else Tyapp tycon args'
     | _ -> holKernel_rev_assocd ty i ty`;;

let holKernel_type_subst_ind = cake_ind_tidy (cake_ind "holKernel_type_subst");;

(*
  let bool_ty = mk_type("bool",[]);;
  let mk_fun_ty ty1 ty2 = mk_type("fun",[ty1; ty2]);;
  let aty = mk_vartype "A";;
  let bty = mk_vartype "B";;
*)

let holKernel_bool_ty_def = cake_def
  `holKernel_bool_ty = Tyapp (implode "bool") []`;;

let holKernel_mk_fun_ty_def = cake_def
  `holKernel_mk_fun_ty ty1 ty2 = Tyapp (implode "fun") [ty1; ty2]`;;

let holKernel_aty_def = cake_def
  `holKernel_aty = Tyvar (implode "A")`;;

let holKernel_bty_def = cake_def
  `holKernel_bty = Tyvar (implode "B")`;;

(*
  let constants() = !the_term_constants
*)

let holKernel_constants_def = cake_def
  `holKernel_constants one =
     (holKernel_get_the_term_constants:
        hol_refs->((mlstring#hol_type)list,C)exc#hol_refs)`;;

(*
  let get_const_type s = assoc s (!the_term_constants)
*)

let holKernel_get_const_type_def = cake_def
  `holKernel_get_const_type s =
     st_ex_bind holKernel_get_the_term_constants (\l. holKernel_assoc s l)`;;

(*
  let rec type_of tm =
    match tm with
      Var(_,ty) -> ty
    | Const(_,ty) -> ty
    | Comb(s,_) -> hd(tl(snd(dest_type(type_of s))))
    | Abs(Var(_,ty),t) -> mk_fun_ty ty (type_of t)
*)

let holKernel_type_of_def = cake_def
  `holKernel_type_of tm =
     match tm with
       hol_Var _ ty -> st_ex_return ty
     | hol_Const _ ty -> st_ex_return ty
     | hol_Comb s _ ->
         st_ex_bind (holKernel_type_of s) (\ty.
         st_ex_bind (holKernel_dest_type ty) (\x.
         match x with
           (_,CONS _ (CONS ty1 _)) -> st_ex_return ty1
         | _ -> holKernel_raise_Failure (implode "match")))
     | hol_Abs (hol_Var _ ty) t ->
         st_ex_bind (holKernel_type_of t) (\x.
         st_ex_return (holKernel_mk_fun_ty ty x))
     | _ -> holKernel_raise_Failure (implode "match")`;;

let holKernel_type_of_ind = cake_ind "holKernel_type_of";;

(*
  let aconv =
    let rec alphavars env tm1 tm2 =
      match env with
        [] -> tm1 = tm2
      | (t1,t2)::oenv ->
            (t1 = tm1 & t2 = tm2) or
            (t1 <> tm1 & t2 <> tm2 & alphavars oenv tm1 tm2) in
    let rec raconv env tm1 tm2 =
      (tm1 == tm2 & env = []) or
      match (tm1,tm2) with
        Var(_,_),Var(_,_) -> alphavars env tm1 tm2
      | Const(_,_),Const(_,_) -> tm1 = tm2
      | Comb(s1,t1),Comb(s2,t2) -> raconv env s1 s2 & raconv env t1 t2
      | Abs(Var(_,ty1) as x1,t1),Abs(Var(_,ty2) as x2,t2) ->
                ty1 = ty2 & raconv ((x1,x2)::env) t1 t2
      | _ -> false in
    fun tm1 tm2 -> raconv [] tm1 tm2
*)

let holKernel_alphavars_def = cake_def
  `holKernel_alphavars env (tm1:hol_term) tm2 =
     match env with
       [] -> tm1 = tm2
     | CONS (t1,t2) oenv ->
         if t1 = tm1 then t2 = tm2
         else if t2 = tm2 then F
         else holKernel_alphavars oenv tm1 tm2`;;

let holKernel_raconv_def = cake_def
  `holKernel_raconv env tm1 tm2 =
     match (tm1,tm2) with
       (hol_Var _ _, hol_Var _ _) -> holKernel_alphavars env tm1 tm2
     | (hol_Const _ _, hol_Const _ _) -> tm1 = tm2
     | (hol_Comb s1 t1, hol_Comb s2 t2) ->
         holKernel_raconv env s1 s2 /\ holKernel_raconv env t1 t2
     | (hol_Abs v1 t1, hol_Abs v2 t2) ->
         (match (v1,v2) with
            (hol_Var n1 ty1, hol_Var n2 ty2) ->
              ty1 = ty2 /\ holKernel_raconv (CONS (v1,v2) env) t1 t2
          | _ -> F)
     | _ -> F`;;

let holKernel_aconv_def = cake_def
  `holKernel_aconv tm1 tm2 = holKernel_raconv [] tm1 tm2`;;

(*
  let is_var = function (Var(_,_)) -> true | _ -> false
  let is_const = function (Const(_,_)) -> true | _ -> false
  let is_abs = function (Abs(_,_)) -> true | _ -> false
  let is_comb = function (Comb(_,_)) -> true | _ -> false
*)

let holKernel_is_var_def = cake_def
  `holKernel_is_var x = match x with hol_Var _ _ -> T | _ -> F`;;

let holKernel_is_const_def = cake_def
  `holKernel_is_const x = match x with hol_Const _ _ -> T | _ -> F`;;

let holKernel_is_abs_def = cake_def
  `holKernel_is_abs x = match x with hol_Abs _ _ -> T | _ -> F`;;

let holKernel_is_comb_def = cake_def
  `holKernel_is_comb x = match x with hol_Comb _ _ -> T | _ -> F`;;

(*
  let mk_var(v,ty) = Var(v,ty)
*)

let holKernel_mk_var_def = cake_def
  `holKernel_mk_var (v,ty) = hol_Var v ty`;;

(*
  let mk_const(name,theta) =
    let uty = try get_const_type name with Failure _ ->
      failwith "mk_const: not a constant name" in
    Const(name,type_subst theta uty)
*)

let holKernel_mk_const_def = cake_def
  `holKernel_mk_const (name,theta) =
     st_ex_bind
       (holKernel_try holKernel_get_const_type name
          (implode "mk_const: not a constant name"))
       (\uty. st_ex_return (hol_Const name (holKernel_type_subst theta uty)))`;;

(*
  let mk_abs(bvar,bod) =
    match bvar with
      Var(_,_) -> Abs(bvar,bod)
    | _ -> failwith "mk_abs: not a variable"
*)

let holKernel_mk_abs_def = cake_def
  `holKernel_mk_abs (bvar,bod) =
     match bvar with
       hol_Var n ty -> st_ex_return (hol_Abs bvar bod)
     | _ -> holKernel_raise_Failure (implode "mk_abs: not a variable")`;;

(*
  let mk_comb(f,a) =
    match type_of f with
      Tyapp("fun",[ty;_]) when ty = type_of a -> Comb(f,a)
    | _ -> failwith "mk_comb: types do not agree"
*)

let holKernel_mk_comb_def = cake_def
  `holKernel_mk_comb (f,a) =
     st_ex_bind (holKernel_type_of f) (\tyf.
     st_ex_bind (holKernel_type_of a) (\tya.
     match tyf with
       Tyapp nm [ty; _] ->
         if nm = implode "fun" then
           (if tya = ty then st_ex_return (hol_Comb f a)
            else holKernel_raise_Failure (implode "mk_comb: types do not agree"))
         else holKernel_raise_Failure (implode "mk_comb: types do not agree")
     | _ -> holKernel_raise_Failure (implode "mk_comb: types do not agree")))`;;

(*
  let dest_var =
    function (Var(s,ty)) -> s,ty | _ -> failwith "dest_var: not a variable"

  let dest_const =
    function (Const(s,ty)) -> s,ty | _ -> failwith "dest_const: not a constant"

  let dest_comb =
    function (Comb(f,x)) -> f,x | _ -> failwith "dest_comb: not a combination"

  let dest_abs =
    function (Abs(v,b)) -> v,b | _ -> failwith "dest_abs: not an abstraction"
*)

let holKernel_dest_var_def = cake_def
  `holKernel_dest_var tm =
     match tm with
       hol_Var s ty -> st_ex_return (s,ty)
     | _ -> holKernel_raise_Failure (implode "dest_var: not a variable")`;;

let holKernel_dest_const_def = cake_def
  `holKernel_dest_const tm =
     match tm with
       hol_Const s ty -> st_ex_return (s,ty)
     | _ -> holKernel_raise_Failure (implode "dest_const: not a constant")`;;

let holKernel_dest_comb_def = cake_def
  `holKernel_dest_comb tm =
     match tm with
       hol_Comb f x -> st_ex_return (f,x)
     | _ -> holKernel_raise_Failure (implode "dest_comb: not a combination")`;;

let holKernel_dest_abs_def = cake_def
  `holKernel_dest_abs tm =
     match tm with
       hol_Abs v b -> st_ex_return (v,b)
     | _ -> holKernel_raise_Failure (implode "dest_abs: not an abstraction")`;;

(*
  let rec frees tm =
    match tm with
      Var(_,_) -> [tm]
    | Const(_,_) -> []
    | Abs(bv,bod) -> subtract (frees bod) [bv]
    | Comb(s,t) -> union (frees s) (frees t)
*)

(*
  let freesl tml = itlist (union o frees) tml []
*)

let holKernel_freesl_def = cake_def
  `holKernel_freesl tml = itlist (hol_union o hol_frees) tml []`;;

(*
  let rec freesin acc tm =
    match tm with
      Var(_,_) -> mem tm acc
    | Const(_,_) -> true
    | Abs(bv,bod) -> freesin (bv::acc) bod
    | Comb(s,t) -> freesin acc s & freesin acc t
*)

let holKernel_freesin_def = cake_def
  `holKernel_freesin acc tm =
     match tm with
       hol_Var _ _ -> MEM tm acc
     | hol_Const _ _ -> T
     | hol_Abs bv bod -> holKernel_freesin (CONS bv acc) bod
     | hol_Comb s t -> holKernel_freesin acc s /\ holKernel_freesin acc t`;;

(*
  let rec vfree_in v tm =
    match tm with
      Abs(bv,bod) -> v <> bv & vfree_in v bod
    | Comb(s,t) -> vfree_in v s or vfree_in v t
    | _ -> tm = v
*)

(*
  let rec type_vars_in_term tm =
    match tm with
      Var(_,ty)        -> tyvars ty
    | Const(_,ty)      -> tyvars ty
    | Comb(s,t)        -> union (type_vars_in_term s) (type_vars_in_term t)
    | Abs(Var(_,ty),t) -> union (tyvars ty) (type_vars_in_term t)

  The Abs pmatch is modified slightly.
*)

let holKernel_type_vars_in_term_def = cake_def
  `holKernel_type_vars_in_term tm =
     match tm with
       hol_Var _ ty -> holKernel_tyvars ty
     | hol_Const _ ty -> holKernel_tyvars ty
     | hol_Comb s t ->
         hol_union (holKernel_type_vars_in_term s) (holKernel_type_vars_in_term t)
     | hol_Abs v t ->
         hol_union (holKernel_type_vars_in_term v) (holKernel_type_vars_in_term t)`;;

(*
  let rec variant avoid v =
    if not(exists (vfree_in v) avoid) then v else
    match v with
      Var(s,ty) -> variant avoid (Var(s^"'",ty))
    | _ -> failwith "variant: not a variable"

  This function requires a non-trivial terminiation proof. We make
  this a non-failing function to make it pure.
*)

(* HOL4: EXISTS_IMP [local] *)
let holKernel_EXISTS_IMP = prove
 (`!xs (p:A->bool). EX p xs ==> ?x. MEM x xs /\ p x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[EX; MEM] THEN ASM_MESON_TAC[]);;

(* HOL4: MEM_subtract [local] *)
let holKernel_MEM_subtract = prove
 (`!y z (x:A). MEM x (subtract y z) <=> MEM x y /\ ~MEM x z`,
  REWRITE_TAC[subtract_def; MEM_FILTER] THEN MESON_TAC[]);;

let vfree_in_IMP = prove
 (`!(t:hol_term) x v ty. vfree_in (hol_Var v ty) x ==> MEM (hol_Var v ty) (hol_frees x)`,
  GEN_TAC THEN MATCH_MP_TAC hol_term_INDUCT THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[vfree_in_def; hol_frees_def] THEN
  CASE_REWRITE_TAC[MEM; MEM_union; holKernel_MEM_subtract; injectivity "hol_term";
                   distinctness "hol_term"] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]);;

(*
  let vsubst =
    let rec vsubst ilist tm =
      match tm with
        Var(_,_) -> rev_assocd tm ilist tm
      | Const(_,_) -> tm
      | Comb(s,t) -> let s' = vsubst ilist s and t' = vsubst ilist t in
                     if s' == s & t' == t then tm else Comb(s',t')
      | Abs(v,s) -> let ilist' = filter (fun (t,x) -> x <> v) ilist in
                    if ilist' = [] then tm else
                    let s' = vsubst ilist' s in
                    if s' == s then tm else
                    if exists (fun (t,x) -> vfree_in v t & vfree_in x s) ilist'
                    then let v' = variant [s'] v in
                         Abs(v',vsubst ((v',v)::ilist') s)
                    else Abs(v,s') in
    fun theta ->
      if theta = [] then (fun tm -> tm) else
      if forall (fun (t,x) -> type_of t = snd(dest_var x)) theta
      then vsubst theta else failwith "vsubst: Bad substitution list"
*)

(* HOL4 leaves out HOL Light's test of s' = s here: it does not seem to fit *)
(* Harrison's formalisation (HOL4's comment).                               *)
let holKernel_vsubst_aux_def = cake_def
  `holKernel_vsubst_aux ilist tm =
     match tm with
       hol_Var _ _ -> holKernel_rev_assocd tm ilist tm
     | hol_Const _ _ -> tm
     | hol_Comb s t ->
         let s' = holKernel_vsubst_aux ilist s in
         let t' = holKernel_vsubst_aux ilist t in
         hol_Comb s' t'
     | hol_Abs v s ->
         if ~holKernel_is_var v then tm else
         let ilist' = FILTER (\(t,x). ~(x = v)) ilist in
         if ilist' = [] then tm else
         let s' = holKernel_vsubst_aux ilist' s in
         if EX (\(t,x). vfree_in v t /\ vfree_in x s) ilist'
         then let v' = variant [s'] v in
              hol_Abs v' (holKernel_vsubst_aux (CONS (v',v) ilist') s)
         else hol_Abs v s'`;;

let holKernel_vsubst_def = cake_def
  `holKernel_vsubst theta tm =
     if theta = [] then st_ex_return tm else
     st_ex_bind
       (holKernel_forall (\(t,x). st_ex_bind (holKernel_type_of t) (\ty.
                                  st_ex_bind (holKernel_dest_var x) (\vty.
                                  st_ex_return (ty = SND vty)))) theta)
       (\ok. if ok then st_ex_return (holKernel_vsubst_aux theta tm)
             else holKernel_raise_Failure
                    (implode "vsubst: Bad substitution list"))`;;

(*
  let inst =
    let rec inst env tyin tm =
      match tm with
        Var(n,ty)   -> let ty' = type_subst tyin ty in
                       let tm' = if ty' == ty then tm else Var(n,ty') in
                       if rev_assocd tm' env tm = tm then tm'
                       else raise (Clash tm')
      | Const(c,ty) -> let ty' = type_subst tyin ty in
                       if ty' == ty then tm else Const(c,ty')
      | Comb(f,x)   -> let f' = inst env tyin f and x' = inst env tyin x in
                       if f' == f & x' == x then tm else Comb(f',x')
      | Abs(y,t)    -> let y' = inst [] tyin y in
                       let env' = (y,y')::env in
                       try let t' = inst env' tyin t in
                           if y' == y & t' == t then tm else Abs(y',t')
                       with (Clash(w') as ex) ->
                       if w' <> y' then raise ex else
                       let ifrees = map (inst [] tyin) (frees t) in
                       let y'' = variant ifrees y' in
                       let z = Var(fst(dest_var y''),snd(dest_var y)) in
                       inst env tyin (Abs(z,vsubst[z,y] t)) in
      fun tyin -> if tyin = [] then fun tm -> tm else inst [] tyin
*)

let holKernel_my_term_size_def = cake_def
  `(holKernel_my_term_size (hol_Var _ _) = 1) /\
   (holKernel_my_term_size (hol_Const _ _) = 1) /\
   (holKernel_my_term_size (hol_Comb s1 s2) =
      1 + holKernel_my_term_size s1 + holKernel_my_term_size s2) /\
   (holKernel_my_term_size (hol_Abs s1 s2) =
      1 + holKernel_my_term_size s1 + holKernel_my_term_size s2)`;;

let my_term_size_variant = prove
 (`!avoid t. holKernel_my_term_size (variant avoid t) = holKernel_my_term_size t`,
  MATCH_MP_TAC variant_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [variant_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC(SPEC `v:hol_term` (cases "hol_term")) THEN
  CASE_REWRITE_TAC[injectivity "hol_term"; distinctness "hol_term"] THEN
  DISCH_THEN(MP_TAC o SPECL [`a0:mlstring`; `a1:hol_type`]) THEN
  SIMP_TAC[holKernel_my_term_size_def]);;

let is_var_variant = prove
 (`!avoid t. holKernel_is_var (variant avoid t) <=> holKernel_is_var t`,
  MATCH_MP_TAC variant_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [variant_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC(SPEC `v:hol_term` (cases "hol_term")) THEN
  CASE_REWRITE_TAC[injectivity "hol_term"; distinctness "hol_term"] THEN
  DISCH_THEN(MP_TAC o SPECL [`a0:mlstring`; `a1:hol_type`]) THEN
  SIMP[holKernel_is_var_def]);;

(* the size of a variable is 1, and so is that of what rev_assocd finds in a *)
(* list of pairs whose first components are variables                       *)
let HOLKAUX_is_var_size = prove
 (`!x. holKernel_is_var x ==> holKernel_my_term_size x = 1`,
  MATCH_MP_TAC hol_term_INDUCT THEN SIMP[holKernel_is_var_def; holKernel_my_term_size_def]);;

let HOLKAUX_my_term_size_rev_assocd = prove
 (`!xs (a:hol_term) d.
     ALL (\x. holKernel_is_var (FST x)) xs /\ holKernel_my_term_size d = 1
     ==> holKernel_my_term_size (holKernel_rev_assocd a xs d) = 1`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[holKernel_rev_assocd_def] THEN
  CASE_REWRITE_TAC[ALL] THEN REPEAT GEN_TAC THEN
  PAIR_CASES_ON `h:hol_term#hol_term` THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[HOLKAUX_is_var_size]);;

(* HOL4: my_term_size_vsubst_aux (a val, Q.prove), before and after its     *)
(* specialisation to one pair                                               *)
let HOLKAUX_my_term_size_vsubst_aux_gen = prove
 (`!t xs. ALL (\x. holKernel_is_var (FST x)) xs
          ==> holKernel_my_term_size (holKernel_vsubst_aux xs t) =
              holKernel_my_term_size t`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[holKernel_vsubst_aux_def] THEN CASE_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THENL
   [REWRITE_TAC[holKernel_my_term_size_def] THEN
    MATCH_MP_TAC HOLKAUX_my_term_size_rev_assocd THEN
    ASM_REWRITE_TAC[holKernel_my_term_size_def];
    ASM_SIMP_TAC[holKernel_my_term_size_def];
    SUBGOAL_THEN `ALL (\x. holKernel_is_var (FST x))
                    (FILTER (\(t,x). ~(x = a0)) (xs:(hol_term#hol_term)list))`
      ASSUME_TAC THENL
     [UNDISCH_TAC `ALL (\x. holKernel_is_var (FST x)) (xs:(hol_term#hol_term)list)` THEN
      REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN MESON_TAC[];
      ALL_TAC] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ALL; is_var_variant; my_term_size_variant;
                 holKernel_my_term_size_def]]);;

let HOLKAUX_my_term_size_vsubst_aux = prove
 (`!t v ty x. holKernel_my_term_size (holKernel_vsubst_aux [(hol_Var v ty,x)] t) =
              holKernel_my_term_size t`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOLKAUX_my_term_size_vsubst_aux_gen THEN
  REWRITE_TAC[ALL; holKernel_is_var_def] THEN CASE_REWRITE_TAC[]);;

let ZERO_LT_term_size = prove
 (`!t. 0 < holKernel_my_term_size t`,
  MATCH_MP_TAC hol_term_INDUCT THEN REWRITE_TAC[holKernel_my_term_size_def] THEN
  ARITH_TAC);;

let holKernel_inst_aux_def = cake_def_wf
  `MEASURE (\(env:(hol_term#hol_term)list,tyin:(hol_type#hol_type)list,tm:hol_term).
              holKernel_my_term_size tm)`
  (REWRITE_TAC[measure_THM] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[holKernel_my_term_size_def; HOLKAUX_my_term_size_vsubst_aux] THEN
   ARITH_TAC)
  `holKernel_inst_aux (env:(hol_term#hol_term)list) tyin tm =
     match tm with
       hol_Var n ty ->
         let ty' = holKernel_type_subst tyin ty in
         let tm' = if ty' = ty then tm else hol_Var n ty' in
         if holKernel_rev_assocd tm' env tm = tm then st_ex_return tm'
         else holKernel_raise_Clash tm'
     | hol_Const c ty ->
         let ty' = holKernel_type_subst tyin ty in
         if ty' = ty then st_ex_return tm else st_ex_return (hol_Const c ty')
     | hol_Comb f x ->
         st_ex_bind (holKernel_inst_aux env tyin f) (\f'.
         st_ex_bind (holKernel_inst_aux env tyin x) (\x'.
         if f = f' /\ x = x' then st_ex_return tm
         else st_ex_return (hol_Comb f' x')))
     | hol_Abs y t ->
         st_ex_bind (holKernel_inst_aux [] tyin y) (\y'.
         st_ex_bind (st_ex_return (CONS (y,y') env)) (\env'.
         holKernel_handle_Clash
           (st_ex_bind (holKernel_inst_aux env' tyin t) (\t'.
            if y = y' /\ t = t' then st_ex_return tm
            else st_ex_return (hol_Abs y' t')))
           (\w'.
              if ~(w' = y') then holKernel_raise_Clash w' else
              st_ex_bind (holKernel_inst_aux [] tyin t) (\temp.
              st_ex_bind (st_ex_return (variant (hol_frees temp) y')) (\y'.
              st_ex_bind (holKernel_dest_var y') (\vt.
              match vt with
                (v1,ty') ->
                  st_ex_bind (holKernel_dest_var y) (\vt'.
                  match vt' with
                    (v2,ty) ->
                      st_ex_bind
                        (holKernel_inst_aux (CONS (hol_Var v1 ty,hol_Var v1 ty') env)
                           tyin (holKernel_vsubst_aux [(hol_Var v1 ty,y)] t))
                        (\t'. st_ex_return (hol_Abs y' t')))))))))`;;
let holKernel_inst_aux_ind = cake_ind "holKernel_inst_aux";;
let holKernel_inst_def = cake_def
  `holKernel_inst tyin tm =
     if tyin = [] then st_ex_return tm else holKernel_inst_aux [] tyin tm`;;

(*
  let rator tm =
    match tm with
      Comb(l,r) -> l
    | _ -> failwith "rator: Not a combination";;

  let rand tm =
    match tm with
      Comb(l,r) -> r
    | _ -> failwith "rand: Not a combination";;
*)

let holKernel_rator_def = cake_def
  `holKernel_rator tm =
     match tm with
       hol_Comb l r -> st_ex_return l
     | _ -> holKernel_raise_Failure (implode "rator: Not a combination")`;;

let holKernel_rand_def = cake_def
  `holKernel_rand tm =
     match tm with
       hol_Comb l r -> st_ex_return r
     | _ -> holKernel_raise_Failure (implode "rand: Not a combination")`;;

(*
  let safe_mk_eq l r =
    let ty = type_of l in
    Comb(Comb(Const("=",Tyapp("fun",[ty;Tyapp("fun",[ty;bool_ty])])),l),r)
*)

let holKernel_safe_mk_eq_def = cake_def
  `holKernel_safe_mk_eq l r =
     st_ex_bind (holKernel_type_of l) (\ty.
     st_ex_return
       (hol_Comb (hol_Comb (hol_Const (implode "=")
          (Tyapp (implode "fun") [ty; Tyapp (implode "fun") [ty; holKernel_bool_ty]]))
          l) r))`;;

(*
  let mk_eq =
    let eq = mk_const("=",[]) in
    fun (l,r) ->
      try let ty = type_of l in
          let eq_tm = inst [ty,aty] eq in
          mk_comb(mk_comb(eq_tm,l),r)
      with Failure _ -> failwith "mk_eq";;
*)

let holKernel_mk_eq_def = cake_def
  `holKernel_mk_eq (l,r) =
     holKernel_try
       (\(l,r). st_ex_bind (holKernel_type_of l) (\ty.
                st_ex_bind (holKernel_mk_const (implode "=",[])) (\eq.
                st_ex_bind (holKernel_inst [(ty,holKernel_aty)] eq) (\eq_tm.
                st_ex_bind (holKernel_mk_comb (eq_tm,l)) (\t.
                st_ex_bind (holKernel_mk_comb (t,r)) (\t.
                st_ex_return t))))))
       (l,r) (implode "mk_eq")`;;

(*
  let dest_eq tm =
    match tm with
      Comb(Comb(Const("=",_),l),r) -> l,r
    | _ -> failwith "dest_eq";;

  let is_eq tm =
    match tm with
      Comb(Comb(Const("=",_),_),_) -> true
    | _ -> false;;
*)

let holKernel_dest_eq_def = cake_def
  `holKernel_dest_eq tm =
     match tm with
       hol_Comb (hol_Comb (hol_Const nm _) l) r ->
         if nm = implode "=" then st_ex_return (l,r)
         else holKernel_raise_Failure (implode "dest_eq")
     | _ -> holKernel_raise_Failure (implode "dest_eq")`;;

let holKernel_is_eq_def = cake_def
  `holKernel_is_eq tm =
     match tm with
       hol_Comb (hol_Comb (hol_Const nm _) l) r -> nm = implode "="
     | _ -> F`;;

(*
  let dest_thm (Sequent(asl,c)) = (asl,c)

  let hyp (Sequent(asl,c)) = asl

  let concl (Sequent(asl,c)) = c
*)

let holKernel_dest_thm_def = cake_def
  `holKernel_dest_thm (Sequent asl c) = (asl,c)`;;

let holKernel_hyp_def = cake_def
  `holKernel_hyp (Sequent asl c) = asl`;;

let holKernel_concl_def = cake_def
  `holKernel_concl (Sequent asl c) = c`;;

(*
  let REFL tm =
    Sequent([],safe_mk_eq tm tm)
*)

let holKernel_REFL_def = cake_def
  `holKernel_REFL tm =
     st_ex_bind (holKernel_safe_mk_eq tm tm) (\eq. st_ex_return (Sequent [] eq))`;;

(*
  let TRANS (Sequent(asl1,c1)) (Sequent(asl2,c2)) =
    match (c1,c2) with
      Comb((Comb(Const("=",_),_) as eql),m1),Comb(Comb(Const("=",_),m2),r)
        when alphaorder m1 m2 = 0 -> Sequent(term_union asl1 asl2,Comb(eql,r))
    | _ -> failwith "TRANS"
*)

let holKernel_TRANS_def = cake_def
  `holKernel_TRANS (Sequent asl1 c1) (Sequent asl2 c2) =
     match (c1,c2) with
       (hol_Comb eql m1, hol_Comb (hol_Comb (hol_Const nm _) m2) r) ->
         if nm = implode "=" then
           (match eql with
              hol_Comb (hol_Const nm' _) l ->
                if nm' = implode "=" then
                  (if holKernel_aconv m1 m2
                   then st_ex_return (Sequent (term_union asl1 asl2) (hol_Comb eql r))
                   else holKernel_raise_Failure (implode "TRANS"))
                else holKernel_raise_Failure (implode "TRANS")
            | _ -> holKernel_raise_Failure (implode "TRANS"))
         else holKernel_raise_Failure (implode "TRANS")
     | _ -> holKernel_raise_Failure (implode "TRANS")`;;

(* some in-kernel but derivable rules (TRANS is also in this category) *)

let holKernel_SYM_def = cake_def
  `holKernel_SYM (Sequent asl eq) =
     match eq with
       hol_Comb (hol_Comb (hol_Const nm t) l) r ->
         if nm = implode "=" then
           st_ex_return
             (Sequent asl (hol_Comb (hol_Comb (hol_Const (implode "=") t) r) l))
         else holKernel_raise_Failure (implode "SYM")
     | _ -> holKernel_raise_Failure (implode "SYM")`;;

let holKernel_PROVE_HYP_def = cake_def
  `holKernel_PROVE_HYP (Sequent asl1 c1) (Sequent asl2 c2) =
     (st_ex_return (Sequent (term_union asl2 (term_remove c2 asl1)) c1)
        :A->(thm,B)exc#A)`;;

let holKernel_list_to_hypset_def = cake_def
  `(holKernel_list_to_hypset [] a = a) /\
   (holKernel_list_to_hypset (CONS h hs) a =
      holKernel_list_to_hypset hs (term_union [h] a))`;;

let holKernel_ALPHA_THM_def = cake_def
  `holKernel_ALPHA_THM (Sequent h c) (h',c') =
     if holKernel_aconv c c' then
       let h' = holKernel_list_to_hypset h' [] in
       if ALL (\x. EX (holKernel_aconv x) h') h then
         st_ex_bind (holKernel_map holKernel_type_of h') (\tys.
         if ALL (\ty. ty = holKernel_bool_ty) tys
         then st_ex_return (Sequent h' c')
         else holKernel_raise_Failure (implode "ALPHA_THM"))
       else holKernel_raise_Failure (implode "ALPHA_THM")
     else holKernel_raise_Failure (implode "ALPHA_THM")`;;

(* HOL4 makes ALPHA_THM_ind for the patterns of the definition *)
let holKernel_ALPHA_THM_ind = prove
 (`!P:thm->hol_term list#hol_term->bool.
     (!h c h' c'. P (Sequent h c) (h',c')) ==> !v v1. P v v1`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MATCH_MP_TAC thm_INDUCT THEN ASM_REWRITE_TAC[]);;
(*
  let MK_COMB(Sequent(asl1,c1),Sequent(asl2,c2)) =
     match (c1,c2) with
       Comb(Comb(Const("=",_),l1),r1),Comb(Comb(Const("=",_),l2),r2) ->
        (match type_of r1 with
           Tyapp("fun",[ty;_]) when compare ty (type_of r2) = 0
             -> Sequent(term_union asl1 asl2,
                        safe_mk_eq (Comb(l1,l2)) (Comb(r1,r2)))
         | _ -> failwith "MK_COMB: types do not agree")
     | _ -> failwith "MK_COMB: not both equations"
*)

let holKernel_MK_COMB_def = cake_def
  `holKernel_MK_COMB (Sequent asl1 c1,Sequent asl2 c2) =
     match (c1,c2) with
       (hol_Comb (hol_Comb (hol_Const nm1 _) l1) r1,
        hol_Comb (hol_Comb (hol_Const nm2 _) l2) r2) ->
         if nm1 = implode "=" /\ nm2 = implode "=" then
           st_ex_bind (holKernel_type_of r1) (\r1_ty.
           match r1_ty with
             Tyapp nm [ty; _] ->
               if nm = implode "fun" then
                 st_ex_bind (holKernel_type_of r2) (\r2_ty.
                 if r2_ty = ty then
                   st_ex_bind (holKernel_safe_mk_eq (hol_Comb l1 l2) (hol_Comb r1 r2))
                     (\eq. st_ex_return (Sequent (term_union asl1 asl2) eq))
                 else holKernel_raise_Failure (implode "MK_COMB: types do not agree"))
               else holKernel_raise_Failure (implode "MK_COMB: types do not agree")
           | _ -> holKernel_raise_Failure (implode "MK_COMB: types do not agree"))
         else holKernel_raise_Failure (implode "MK_COMB: not both equations")
     | _ -> holKernel_raise_Failure (implode "MK_COMB: not both equations")`;;

(*
  let ABS v (Sequent(asl,c)) =
    match (v,c) with
      Var(_,_),Comb(Comb(Const("=",_),l),r) when not(exists (vfree_in v) asl)
         -> Sequent(asl,safe_mk_eq (Abs(v,l)) (Abs(v,r)))
    | _ -> failwith "ABS";;
*)

let holKernel_ABS_def = cake_def
  `holKernel_ABS v (Sequent asl c) =
     match (v,c) with
       (hol_Var _ _, hol_Comb (hol_Comb (hol_Const nm _) l) r) ->
         if nm = implode "=" then
           (if EX (vfree_in v) asl
            then holKernel_raise_Failure
                   (implode "ABS: variable is free in assumptions")
            else st_ex_bind (holKernel_safe_mk_eq (hol_Abs v l) (hol_Abs v r)) (\eq.
                 st_ex_return (Sequent asl eq)))
         else holKernel_raise_Failure (implode "ABS: not an equation")
     | _ -> holKernel_raise_Failure (implode "ABS: not an equation")`;;

(*
  let BETA tm =
    match tm with
      Comb(Abs(v,bod),arg) when compare arg v = 0
        -> Sequent([],safe_mk_eq tm bod)
    | _ -> failwith "BETA: not a trivial beta-redex"
*)

let holKernel_BETA_def = cake_def
  `holKernel_BETA tm =
     match tm with
       hol_Comb (hol_Abs v bod) arg ->
         if arg = v then
           st_ex_bind (holKernel_safe_mk_eq tm bod) (\eq. st_ex_return (Sequent [] eq))
         else holKernel_raise_Failure (implode "BETA: not a trivial beta-redex")
     | _ -> holKernel_raise_Failure (implode "BETA: not a trivial beta-redex")`;;

(*
  let ASSUME tm =
    if type_of tm = bool_ty then Sequent([tm],tm)
    else failwith "ASSUME: not a proposition"
*)

let holKernel_ASSUME_def = cake_def
  `holKernel_ASSUME tm =
     st_ex_bind (holKernel_type_of tm) (\ty.
     if ty = holKernel_bool_ty then st_ex_return (Sequent [tm] tm)
     else holKernel_raise_Failure (implode "ASSUME: not a proposition"))`;;

(*
  let EQ_MP (Sequent(asl1,eq)) (Sequent(asl2,c)) =
    match eq with
      Comb(Comb(Const("=",_),l),r) when aconv l c
        -> Sequent(term_union asl1 asl2,r)
    | _ -> failwith "EQ_MP"
*)

let holKernel_EQ_MP_def = cake_def
  `holKernel_EQ_MP (Sequent asl1 eq) (Sequent asl2 c) =
     match eq with
       hol_Comb (hol_Comb (hol_Const nm _) l) r ->
         if nm = implode "=" then
           (if holKernel_aconv l c then st_ex_return (Sequent (term_union asl1 asl2) r)
            else holKernel_raise_Failure (implode "EQ_MP"))
         else holKernel_raise_Failure (implode "EQ_MP")
     | _ -> holKernel_raise_Failure (implode "EQ_MP")`;;

(*
  let DEDUCT_ANTISYM_RULE (Sequent(asl1,c1)) (Sequent(asl2,c2)) =
    let asl1' = term_remove c2 asl1 and asl2' = term_remove c1 asl2 in
    Sequent(term_union asl1' asl2',safe_mk_eq c1 c2)
*)

let holKernel_DEDUCT_ANTISYM_RULE_def = cake_def
  `holKernel_DEDUCT_ANTISYM_RULE (Sequent asl1 c1) (Sequent asl2 c2) =
     let asl1' = term_remove c2 asl1 in
     let asl2' = term_remove c1 asl2 in
     st_ex_bind (holKernel_safe_mk_eq c1 c2) (\eq.
     st_ex_return (Sequent (term_union asl1' asl2') eq))`;;

let holKernel_image_def = cake_def
  `holKernel_image (f:hol_term->A->(hol_term,B)exc#A) l =
     match l with
       [] -> st_ex_return l
     | CONS h t -> st_ex_bind (f h) (\h'.
                   st_ex_bind (holKernel_image f t) (\t'.
                   st_ex_return (if h' = h /\ t' = t then l
                                 else term_union [h'] t')))`;;

let holKernel_image_ind = cake_ind "holKernel_image";;

(*
  let INST_TYPE theta (Sequent(asl,c)) =
    let inst_fun = inst theta in
    Sequent(map inst_fun asl,inst_fun c)
*)

let holKernel_INST_TYPE_def = cake_def
  `holKernel_INST_TYPE theta (Sequent asl c) =
     let inst_fun = holKernel_inst theta in
     st_ex_bind (holKernel_image inst_fun asl) (\l.
     st_ex_bind (inst_fun c) (\x.
     st_ex_return (Sequent l x)))`;;

(*
  let INST theta (Sequent(asl,c)) =
    let inst_fun = vsubst theta in
    Sequent(map inst_fun asl,inst_fun c)
*)

let holKernel_INST_def = cake_def
  `holKernel_INST theta (Sequent asl c) =
     let inst_fun = holKernel_vsubst theta in
     st_ex_bind (holKernel_image inst_fun asl) (\l.
     st_ex_bind (inst_fun c) (\x.
     st_ex_return (Sequent l x)))`;;

(*
  let axioms() = !the_axioms
*)

let holKernel_axioms_def = cake_def
  `holKernel_axioms one =
     (holKernel_get_the_axioms:hol_refs->(thm list,C)exc#hol_refs)`;;

(*
  let new_axiom tm =
    if fst(dest_type(type_of tm)) = "bool" then
      let th = Sequent([],tm) in
       (the_axioms := th::(!the_axioms); th)
    else failwith "new_axiom: Not a proposition"
*)

let holKernel_new_axiom_def = cake_def
  `holKernel_new_axiom tm =
     st_ex_bind (holKernel_type_of tm) (\ty.
     if ty = holKernel_bool_ty then
       st_ex_bind (st_ex_return (Sequent [] tm)) (\th.
       st_ex_bind holKernel_get_the_axioms (\ax.
       st_ex_ignore_bind (holKernel_set_the_axioms (CONS th ax))
       (st_ex_ignore_bind (holKernel_add_def (hol_NewAxiom tm))
       (st_ex_return th))))
     else holKernel_raise_Failure (implode "new_axiom: Not a proposition"))`;;

let holKernel_first_dup_def = cake_def
  `holKernel_first_dup (ls:A list) acc =
     match ls with
       [] -> NONE
     | CONS h t -> if MEM h acc then SOME h
                   else holKernel_first_dup t (CONS h acc)`;;

let holKernel_add_constants_def = cake_def
  `holKernel_add_constants ls =
     st_ex_bind holKernel_get_the_term_constants (\cs.
     match holKernel_first_dup (MAP FST ls) (MAP FST cs) with
       SOME name ->
         holKernel_raise_Failure
           (strcat (strcat (implode "add_constants: ") name)
                   (implode " appears twice or has already been declared"))
     | NONE -> holKernel_set_the_term_constants (APPEND ls cs))`;;

let holKernel_new_specification_def = cake_def
  `holKernel_new_specification (Sequent eqs p) =
     st_ex_bind
       (holKernel_map (\e.
          st_ex_bind (holKernel_dest_eq e) (\lr.
          match lr with
            (l,r) ->
              st_ex_bind (holKernel_dest_var l) (\sty.
              match sty with
                (s,ty) ->
                  if ~holKernel_freesin [] r then
                    holKernel_raise_Failure
                      (strcat (strcat (implode "new_specification: witness for ") s)
                              (implode " not closed"))
                  else if ~holKernel_subset (holKernel_type_vars_in_term r)
                                            (holKernel_tyvars ty) then
                    holKernel_raise_Failure
                      (strcat (strcat (implode "new_specification: type variables for ") s)
                              (implode " not contained in the type"))
                  else st_ex_return ((s,ty),r)))) eqs)
       (\eqs.
          let vars = MAP FST eqs in
          if ~holKernel_freesin (MAP (UNCURRY hol_Var) vars) p then
            holKernel_raise_Failure
              (implode "new_specification: specification not closed by the definitions")
          else
            st_ex_ignore_bind (holKernel_add_constants vars)
            (st_ex_ignore_bind
               (holKernel_add_def (hol_ConstSpec (MAP (\((s,ty),r). (s,r)) eqs) p))
            (let ilist = MAP (\(s,ty). (hol_Const s ty,hol_Var s ty)) vars in
             let p = holKernel_vsubst_aux ilist p in
             st_ex_return (Sequent [] p))))`;;

(*
  let new_constant(name,ty) =
    if can get_const_type name then
      failwith ("new_constant: constant "^name^" has already been declared")
    else the_term_constants := (name,ty)::(!the_term_constants)
*)

let holKernel_new_constant_def = cake_def
  `holKernel_new_constant (name,ty) =
     st_ex_ignore_bind (holKernel_add_constants [(name,ty)])
       (holKernel_add_def (hol_NewConst name ty))`;;

let holKernel_new_basic_definition_def = cake_def
  `holKernel_new_basic_definition tm =
     st_ex_bind (holKernel_ASSUME tm) (\th. holKernel_new_specification th)`;;
(*
  let new_basic_definition tm =
    let l,r = dest_eq tm in
    let cname,ty = dest_var l in
    if not(freesin [] r) then failwith "new_definition: term not closed" else
    if not (subset (type_vars_in_term r) (tyvars ty))
    then failwith "new_definition: Type variables not reflected in constant"
    else
      let c = new_constant(cname,ty); mk_const(cname,[]) in
      Sequent([],mk_eq(c,r))
*)

(*
  let new_basic_type_definition tyname (absname,repname) (Sequent(asl,c)) =
    if exists (can get_const_type) [absname; repname] then
      failwith "new_basic_type_definition: Constant(s) already in use" else
    if not (asl = []) then
      failwith "new_basic_type_definition: Assumptions in theorem" else
    let P,x = try dest_comb c
              with Failure _ ->
                failwith "new_basic_type_definition: Not a combination" in
    if not(freesin [] P) then
      failwith "new_basic_type_definition: Predicate is not closed" else
    let tyvars = sort (<=) (type_vars_in_term P) in
    let _ = try new_type(tyname,length tyvars)
            with Failure _ ->
                failwith "new_basic_type_definition: Type already defined" in
    let aty = mk_type(tyname,tyvars)
    and rty = type_of x in
    let abs = new_constant(absname,mk_fun_ty rty aty); mk_const(absname,[])
    and rep = new_constant(repname,mk_fun_ty aty rty); mk_const(repname,[]) in
    let a = mk_var("a",aty) and r = mk_var("r",rty) in
    Sequent([],mk_eq(mk_comb(abs,mk_comb(rep,a)),a)),
    Sequent([],mk_eq(mk_comb(P,r),mk_eq(mk_comb(rep,mk_comb(abs,r)),r)))
*)

let holKernel_new_basic_type_definition_def = cake_def
  `holKernel_new_basic_type_definition (tyname,absname,repname,thm) =
     match thm with
       Sequent asl c ->
         st_ex_bind (ml_monadBase_can holKernel_get_type_arity tyname) (\ok0.
         st_ex_bind (ml_monadBase_can holKernel_get_const_type absname) (\ok1.
         st_ex_bind (ml_monadBase_can holKernel_get_const_type repname) (\ok2.
         if ok0 then holKernel_raise_Failure
           (implode "new_basic_type_definition: Type already defined") else
         if ok1 \/ ok2 then holKernel_raise_Failure
           (implode "new_basic_type_definition: Constant(s) already in use") else
         if absname = repname then holKernel_raise_Failure
           (implode "new_basic_type_definition: Constants must be distinct") else
         if ~(asl = []) then holKernel_raise_Failure
           (implode "new_basic_type_definition: Assumptions in theorem") else
         st_ex_bind
           (holKernel_try holKernel_dest_comb c
              (implode "new_basic_type_definition: Not a combination")) (\px.
         match px with
           (P,x) ->
             if ~holKernel_freesin [] P then holKernel_raise_Failure
               (implode "new_basic_type_definition: Predicate is not closed") else
             let tyvars = MAP Tyvar (MAP implode (sort string_le
                            (MAP explode (holKernel_type_vars_in_term P)))) in
             st_ex_bind (holKernel_type_of x) (\rty.
             st_ex_ignore_bind (holKernel_add_type (tyname,LENGTH tyvars))
             (st_ex_bind (holKernel_mk_type (tyname,tyvars)) (\aty.
              st_ex_ignore_bind
                (holKernel_add_constants
                   [(absname,holKernel_mk_fun_ty rty aty);
                    (repname,holKernel_mk_fun_ty aty rty)])
              (st_ex_ignore_bind
                 (holKernel_add_def (hol_TypeDefn tyname P absname repname))
              (st_ex_bind (holKernel_mk_const (repname,[])) (\rep_tm.
               st_ex_bind (holKernel_mk_const (absname,[])) (\abs_tm.
               st_ex_bind (st_ex_return (holKernel_mk_var (implode "a",aty))) (\a.
               st_ex_bind (st_ex_return (holKernel_mk_var (implode "r",rty))) (\r.
               st_ex_bind (holKernel_mk_comb (rep_tm,a)) (\x1.
               st_ex_bind (holKernel_safe_mk_eq (hol_Comb abs_tm x1) a) (\eq1.
               st_ex_bind (holKernel_mk_comb (abs_tm,r)) (\y1.
               st_ex_bind (holKernel_mk_comb (rep_tm,y1)) (\y2.
               st_ex_bind (holKernel_safe_mk_eq y2 r) (\eq2.
               st_ex_bind (holKernel_safe_mk_eq (hol_Comb P r) eq2) (\eq3.
               st_ex_return (Sequent [] eq1,Sequent [] eq3))))))))))))))))))))`;;

let holKernel_context_def = cake_def
  `holKernel_context one =
     (holKernel_get_the_context:hol_refs->(update list,C)exc#hol_refs)`;;
