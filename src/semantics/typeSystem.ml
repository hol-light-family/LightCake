(* ========================================================================= *)
(* typeSystem: port of HOL4 semantics/typeSystemScript.sml (CakeML v3479).   *)
(* Specification of CakeML's type system.                                    *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/semanticPrimitives.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Notes on the rendering:                                                   *)
(* - HOL4's Type abbreviations (type_ident, tenv_abbrev, tenv_ctor,          *)
(*   tenv_val) are HOL Light type abbreviations (new_type_abbrev).           *)
(* - Record fields: tenv.v is type_env_v tenv, tenv.c is type_env_c tenv,    *)
(*   tenv.t is type_env_t tenv; a literal <| v := a; c := b; t := c |> is    *)
(*   type_env_REC a b c.                                                     *)
(* - EVERY is ALL, EVERY2 is ALL2, LIST_TO_SET is set_of_list, ZIP (l1,l2)   *)
(*   is ZIP l1 l2 (HOL Light's: for equal lengths), MAP2 is HOL Light's.     *)
(* - HOL4's paired lambdas (\(a,b). t) are (\p. match p with (a,b) -> t).    *)
(* - The restricted quantifier !((p,e) :: LIST_TO_SET pes). P of the rules   *)
(*   for Handle and Mat is written !p e. MEM (p,e) pes ==> P.                *)
(* - Lem's trivial premises T ==> of the inductive rules are left out.      *)
(* - The definition theorems of the names Tarray_num ... Tdouble (capital    *)
(*   then lower case, which OCaml cannot bind) are typeSystem_NAME_def.      *)
(* ------------------------------------------------------------------------- *)

new_type_abbrev("type_ident",`:num`);;

(* Types: Tvar, the type variables that the user writes down ('a, 'b, etc.); *)
(* Tvar_db, deBruijn indexed type variables; Tapp, a type constructor        *)
(* application (the number is the identity of the type constructor).       *)

let t_INDUCT,t_RECURSION = cake_type
  "t = Tvar tvarN
     | Tvar_db num
     | Tapp (t list) type_ident";;

(* Some abbreviations *)

let typeSystem_Tarray_num_def = cake_def
  `Tarray_num = 0`;;
let typeSystem_Tbool_num_def = cake_def
  `Tbool_num = 1`;;
let typeSystem_Tchar_num_def = cake_def
  `Tchar_num = 2`;;
let typeSystem_Texn_num_def = cake_def
  `Texn_num = 3`;;
let typeSystem_Tfn_num_def = cake_def
  `Tfn_num = 4`;;
let typeSystem_Tint_num_def = cake_def
  `Tint_num = 5`;;
let typeSystem_Tlist_num_def = cake_def
  `Tlist_num = 6`;;
let typeSystem_Tref_num_def = cake_def
  `Tref_num = 7`;;
let typeSystem_Tstring_num_def = cake_def
  `Tstring_num = 8`;;
let typeSystem_Ttup_num_def = cake_def
  `Ttup_num = 9`;;
let typeSystem_Tvector_num_def = cake_def
  `Tvector_num = 10`;;
let typeSystem_Tword64_num_def = cake_def
  `Tword64_num = 11`;;
let typeSystem_Tword8_num_def = cake_def
  `Tword8_num = 12`;;
let typeSystem_Tword8array_num_def = cake_def
  `Tword8array_num = 13`;;
let typeSystem_Tdouble_num_def = cake_def
  `Tdouble_num = 14`;;

(* The numbers for the primitive types *)

let prim_type_nums_def = cake_def
  `prim_type_nums =
     [Tarray_num; Tchar_num; Texn_num; Tfn_num; Tint_num; Tref_num; Tstring_num;
      Ttup_num; Tvector_num; Tword64_num; Tword8_num; Tword8array_num;
      Tdouble_num]`;;

let typeSystem_Tarray_def = cake_def
  `Tarray (t:t) = Tapp [t] Tarray_num`;;
let typeSystem_Tbool_def = cake_def
  `Tbool = Tapp [] Tbool_num`;;
let typeSystem_Tchar_def = cake_def
  `Tchar = Tapp [] Tchar_num`;;
let typeSystem_Texn_def = cake_def
  `Texn = Tapp [] Texn_num`;;
let typeSystem_Tfn_def = cake_def
  `Tfn (t1:t) (t2:t) = Tapp [t1; t2] Tfn_num`;;
let typeSystem_Tint_def = cake_def
  `Tint = Tapp [] Tint_num`;;
let typeSystem_Tlist_def = cake_def
  `Tlist (t:t) = Tapp [t] Tlist_num`;;
let typeSystem_Tref_def = cake_def
  `Tref (t:t) = Tapp [t] Tref_num`;;
let typeSystem_Tstring_def = cake_def
  `Tstring = Tapp [] Tstring_num`;;
let typeSystem_Ttup_def = cake_def
  `Ttup (ts:t list) = Tapp ts Ttup_num`;;
let typeSystem_Tvector_def = cake_def
  `Tvector (t:t) = Tapp [t] Tvector_num`;;
let typeSystem_Tword64_def = cake_def
  `Tword64 = Tapp [] Tword64_num`;;
let typeSystem_Tword8_def = cake_def
  `Tword8 = Tapp [] Tword8_num`;;
let typeSystem_Tword8array_def = cake_def
  `Tword8array = Tapp [] Tword8array_num`;;
let typeSystem_Tdouble_def = cake_def
  `Tdouble = Tapp [] Tdouble_num`;;

(* Check that the free type variables are in the given list.  Every        *)
(* deBruijn variable must be smaller than the first argument.  So if it is  *)
(* 0, no deBruijn indices are permitted.                                    *)

let check_freevars_def = cake_def
  `(check_freevars (dbmax:num) (tvs:mlstring list) (Tvar tv) <=> MEM tv tvs) /\
   (check_freevars dbmax tvs (Tapp ts tn) <=> ALL (check_freevars dbmax tvs) ts) /\
   (check_freevars dbmax tvs (Tvar_db n) <=> n < dbmax)`;;

let check_freevars_ind = cake_ind "check_freevars";;

let check_freevars_ast_def = cake_def
  `(check_freevars_ast (tvs:mlstring list) (Atvar tv) <=> MEM tv tvs) /\
   (check_freevars_ast tvs (Attup ts) <=> ALL (check_freevars_ast tvs) ts) /\
   (check_freevars_ast tvs (Atfun t1 t2) <=>
      check_freevars_ast tvs t1 /\ check_freevars_ast tvs t2) /\
   (check_freevars_ast tvs (Atapp ts tn) <=> ALL (check_freevars_ast tvs) ts)`;;

let check_freevars_ast_ind = cake_ind "check_freevars_ast";;

(* Simultaneous substitution of types for type variables in a type *)

let type_subst_def = cake_def
  `(type_subst (s:(mlstring,t)fmap) (Tvar tv) =
      match FLOOKUP s tv with
        NONE -> Tvar tv
      | SOME t -> t) /\
   (type_subst s (Tapp ts tn) = Tapp (MAP (type_subst s) ts) tn) /\
   (type_subst s (Tvar_db n) = Tvar_db n)`;;

let type_subst_ind = cake_ind "type_subst";;

(* Increment the deBruijn indices in a type by n levels, skipping all       *)
(* levels less than skip.                                                   *)

let deBruijn_inc_def = cake_def
  `(deBruijn_inc (skip:num) (n:num) (Tvar tv) = Tvar tv) /\
   (deBruijn_inc skip n (Tvar_db m) =
      if m < skip then Tvar_db m else Tvar_db (m + n)) /\
   (deBruijn_inc skip n (Tapp ts tn) = Tapp (MAP (deBruijn_inc skip n) ts) tn)`;;

let deBruijn_inc_ind = cake_ind "deBruijn_inc";;

(* skip the lowest given indices and replace the next (LENGTH ts) with the  *)
(* given types and reduce all the higher ones                               *)

let deBruijn_subst_def = cake_def
  `(deBruijn_subst (skip:num) (ts:t list) (Tvar tv) = Tvar tv) /\
   (deBruijn_subst skip ts (Tvar_db n) =
      if ~(n < skip) /\ n < LENGTH ts + skip then EL (n - skip) ts
      else if ~(n < skip) then Tvar_db (n - LENGTH ts)
      else Tvar_db n) /\
   (deBruijn_subst skip ts (Tapp ts' tn) =
      Tapp (MAP (deBruijn_subst skip ts) ts') tn)`;;

let deBruijn_subst_ind = cake_ind "deBruijn_subst";;

(* Type environments: Bind_tvar binds several de Bruijn type variables;     *)
(* in Bind_name the number is how many de Bruijn type variables the         *)
(* typescheme binds.                                                        *)

let tenv_val_exp_INDUCT,tenv_val_exp_RECURSION = cake_type
  "tenv_val_exp = Empty
                | Bind_tvar num tenv_val_exp
                | Bind_name varN num t tenv_val_exp";;

let bind_tvar_def = cake_def
  `bind_tvar (tvs:num) (tenvE:tenv_val_exp) =
     if tvs = 0 then tenvE else Bind_tvar tvs tenvE`;;

let opt_bind_name_def = cake_def
  `opt_bind_name (n:mlstring option) (tvs:num) (t:t) (tenvE:tenv_val_exp) =
     match n with
       NONE -> tenvE
     | SOME n' -> Bind_name n' tvs t tenvE`;;

let tveLookup_def = cake_def
  `(tveLookup (n:mlstring) (inc:num) Empty = NONE:(num#t)option) /\
   (tveLookup n inc (Bind_tvar tvs tenvE) = tveLookup n (inc + tvs) tenvE) /\
   (tveLookup n inc (Bind_name n' tvs t tenvE) =
      if n' = n then SOME (tvs,deBruijn_inc tvs inc t)
      else tveLookup n inc tenvE)`;;

new_type_abbrev("tenv_abbrev",`:(modN,typeN,tvarN list # t)namespace`);;
new_type_abbrev("tenv_ctor",`:(modN,conN,tvarN list # t list # type_ident)namespace`);;
new_type_abbrev("tenv_val",`:(modN,varN,num # t)namespace`);;

let type_env_INFO = cake_record "type_env"
  ["v","tenv_val";
   "c","tenv_ctor";
   "t","tenv_abbrev"];;

let type_env_component_equality = type_env_INFO.ri_component_equality;;

let extend_dec_tenv_def = cake_def
  `extend_dec_tenv (tenv':type_env) (tenv:type_env) =
     type_env_REC (nsAppend (type_env_v tenv') (type_env_v tenv))
                  (nsAppend (type_env_c tenv') (type_env_c tenv))
                  (nsAppend (type_env_t tenv') (type_env_t tenv))`;;

let lookup_varE_def = cake_def
  `lookup_varE (id:(mlstring,mlstring)id) (tenvE:tenv_val_exp) =
     match id with
       Short x -> tveLookup x 0 tenvE
     | _ -> NONE`;;

let lookup_var_def = cake_def
  `lookup_var (id:(modN,varN)id) (tenvE:tenv_val_exp) (tenv:type_env) =
     match lookup_varE id tenvE with
       SOME x -> SOME x
     | NONE -> nsLookup (type_env_v tenv) id`;;

let num_tvs_def = cake_def
  `(num_tvs Empty = 0) /\
   (num_tvs (Bind_tvar tvs tenvE) = tvs + num_tvs tenvE) /\
   (num_tvs (Bind_name n tvs t tenvE) = num_tvs tenvE)`;;

let bind_var_list_def = cake_def
  `(bind_var_list (tvs:num) ([]:(mlstring#t)list) tenvE = tenvE) /\
   (bind_var_list tvs (CONS (n,t) binds) tenvE =
      Bind_name n tvs t (bind_var_list tvs binds tenvE))`;;

let bind_var_list_ind = cake_ind "bind_var_list";;

(* type_p tvs tenv p t bindings: a pattern matches values of a certain type *)
(* and extends the type environment with the pattern's binders; tvs is the  *)
(* maximum deBruijn type variable allowed.  type_e tenv tenvE e t: an       *)
(* expression has a type; type_es: a list of expressions has a list of     *)
(* types; type_funs: a mutually recursive bundle of functions (unlike       *)
(* pattern typing, the resulting environment does not extend the input      *)
(* environment, but just represents the functions).  type_d extra_checks    *)
(* tenv d decls tenv': a declaration is checked and the top-level           *)
(* environments updated; the arguments are whether to do extra checks, the *)
(* type environment, the declaration, the set of type identity stamps      *)
(* defined here, the environment of new stuff declared here.               *)

let t_of_def = cake_def
  `(t_of BoolT = Tbool) /\
   (t_of IntT = Tint) /\
   (t_of CharT = Tchar) /\
   (t_of StrT = Tstring) /\
   (t_of (WordT W8) = Tword8) /\
   (t_of (WordT W64) = Tword64) /\
   (t_of Float64T = Tdouble)`;;
let _ = cake_add_simps [t_of_def];;

let supported_test_def = cake_def
  `(supported_test Equal ty <=> T) /\
   (supported_test (Compare _) ty <=> MEM ty [IntT; CharT; WordT W8; Float64T; StrT]) /\
   (supported_test _ ty <=> ty = StrT)`;;
let _ = cake_add_simps [supported_test_def];;

let supported_arith_def = cake_def
  `(supported_arith a IntT =
      if MEM a [Add; Sub; Mul; Div; Mod] then SOME (2:num) else NONE) /\
   (supported_arith a Float64T =
      if MEM a [Abs; Neg; Sqrt] then SOME 1 else
      if MEM a [Add; Sub; Mul; Div] then SOME 2 else
      if MEM a [FMA] then SOME 3 else NONE) /\
   (supported_arith a (WordT _) =
      if MEM a [Add; Sub; And; Or; Xor] then SOME 2 else NONE) /\
   (supported_arith a BoolT =
      if MEM a [Not] then SOME 1 else NONE) /\
   (supported_arith a (ty:prim_type) = NONE)`;;
let _ = cake_add_simps [supported_arith_def];;

(* Word to Int, Int to Word, Char/Int, Char/Word8 and Float64/Word64       *)
(* conversions                                                             *)

let supported_conversion_def = sem1aux_def
  `(supported_conversion (WordT W8) IntT <=> T) /\
   (supported_conversion (WordT W64) IntT <=> T) /\
   (supported_conversion IntT (WordT W8) <=> T) /\
   (supported_conversion IntT (WordT W64) <=> T) /\
   (supported_conversion CharT IntT <=> T) /\
   (supported_conversion IntT CharT <=> T) /\
   (supported_conversion CharT (WordT W8) <=> T) /\
   (supported_conversion (WordT W8) CharT <=> T) /\
   (supported_conversion Float64T (WordT W64) <=> T) /\
   (supported_conversion (WordT W64) Float64T <=> T) /\
   (supported_conversion (from_ty:prim_type) (to_ty:prim_type) <=> F)`;;
let _ = cake_add_simps [supported_conversion_def];;

(* Check that the operator can have type (t1 -> ... -> tn -> t) *)

let type_op_def = cake_def
  `type_op (op:op) (ts:t list) (t:t) <=>
     match (op,ts) with
       (Opapp,[t1; t2]) -> t1 = Tfn t2 t
     | (Shift W8 _ _,[t1]) -> t1 = Tword8 /\ t = Tword8
     | (Shift W64 _ _,[t1]) -> t1 = Tword64 /\ t = Tword64
     | (Equality,[t1; t2]) -> t1 = t2 /\ t = Tbool
     | (Arith a ty,ts) -> ALL (\arg. arg = t_of ty) ts /\ t = t_of ty /\
                          supported_arith a ty = SOME (LENGTH ts)
     | (FromTo ty1 ty2,[t1]) -> t1 = t_of ty1 /\ t = t_of ty2 /\
                                supported_conversion ty1 ty2
     | (Test test ty,[t1; t2]) -> t1 = t2 /\ t = Tbool /\ t1 = t_of ty /\
                                  supported_test test ty
     | (Opassign,[t1; t2]) -> t1 = Tref t2 /\ t = Ttup []
     | (Opref,[t1]) -> t = Tref t1
     | (Opderef,[t1]) -> t1 = Tref t
     | (Aw8alloc,[t1; t2]) -> t1 = Tint /\ t2 = Tword8 /\ t = Tword8array
     | (Aw8sub,[t1; t2]) -> t1 = Tword8array /\ t2 = Tint /\ t = Tword8
     | (Aw8length,[t1]) -> t1 = Tword8array /\ t = Tint
     | (Aw8update,[t1; t2; t3]) ->
         t1 = Tword8array /\ t2 = Tint /\ t3 = Tword8 /\ t = Ttup []
     | (CopyStrStr,[t1; t2; t3]) ->
         t1 = Tstring /\ t2 = Tint /\ t3 = Tint /\ t = Tstring
     | (CopyStrAw8,[t1; t2; t3; t4; t5]) ->
         t1 = Tstring /\ t2 = Tint /\ t3 = Tint /\ t4 = Tword8array /\
         t5 = Tint /\ t = Ttup []
     | (CopyAw8Str,[t1; t2; t3]) ->
         t1 = Tword8array /\ t2 = Tint /\ t3 = Tint /\ t = Tstring
     | (CopyAw8Aw8,[t1; t2; t3; t4; t5]) ->
         t1 = Tword8array /\ t2 = Tint /\ t3 = Tint /\ t4 = Tword8array /\
         t5 = Tint /\ t = Ttup []
     | (Implode,[t1]) -> t1 = Tlist Tchar /\ t = Tstring
     | (Explode,[t1]) -> t1 = Tstring /\ t = Tlist Tchar
     | (Strsub,[t1; t2]) -> t1 = Tstring /\ t2 = Tint /\ t = Tchar
     | (Strlen,[t1]) -> t1 = Tstring /\ t = Tint
     | (Strcat,[t1]) -> t1 = Tlist Tstring /\ t = Tstring
     | (VfromList,[Tapp [t1] ctor]) -> ctor = Tlist_num /\ t = Tvector t1
     | (Vsub,[t1; t2]) -> t2 = Tint /\ Tvector t = t1
     | (Vlength,[Tapp [t1] ctor]) -> ctor = Tvector_num /\ t = Tint
     | (Aalloc,[t1; t2]) -> t1 = Tint /\ t = Tarray t2
     | (AallocEmpty,[t1]) -> t1 = Ttup [] /\ (?t2. t = Tarray t2)
     | (Asub,[t1; t2]) -> t2 = Tint /\ Tarray t = t1
     | (Alength,[Tapp [t1] ctor]) -> ctor = Tarray_num /\ t = Tint
     | (Aupdate,[t1; t2; t3]) -> t1 = Tarray t3 /\ t2 = Tint /\ t = Ttup []
     | (ConfigGC,[t1; t2]) -> t1 = Tint /\ t2 = Tint /\ t = Ttup []
     | (FFI n,[t1; t2]) -> t1 = Tstring /\ t2 = Tword8array /\ t = Ttup []
     | (ListAppend,[Tapp [t1] ctor; t2]) ->
         ctor = Tlist_num /\ t2 = Tapp [t1] ctor /\ t = t2
     | _ -> F`;;

let check_type_names_def = cake_def
  `(check_type_names (tenvT:(mlstring,mlstring,mlstring list#t)namespace)
      (Atvar tv) <=> T) /\
   (check_type_names tenvT (Attup ts) <=> ALL (check_type_names tenvT) ts) /\
   (check_type_names tenvT (Atfun t1 t2) <=>
      check_type_names tenvT t1 /\ check_type_names tenvT t2) /\
   (check_type_names tenvT (Atapp ts tn) <=>
      (match nsLookup tenvT tn with
         SOME (tvs,_) -> LENGTH tvs = LENGTH ts
       | NONE -> F) /\
      ALL (check_type_names tenvT) ts)`;;

let check_type_names_ind = cake_ind "check_type_names";;

(* Substitution of type names for the type they abbreviate (the NONE case  *)
(* can't happen, for a type that passes the check).  HOL4's ZIP (tvs,args) *)
(* truncates the longer list; HOL Light's ZIP tvs args agrees with it when *)
(* LENGTH tvs <= LENGTH args, so in particular for every type that passes  *)
(* check_type_names.                                                       *)

let type_name_subst_def = cake_def
  `(type_name_subst (tenvT:(mlstring,mlstring,mlstring list#t)namespace)
      (Atvar tv) = Tvar tv) /\
   (type_name_subst tenvT (Attup ts) = Ttup (MAP (type_name_subst tenvT) ts)) /\
   (type_name_subst tenvT (Atfun t1 t2) =
      Tfn (type_name_subst tenvT t1) (type_name_subst tenvT t2)) /\
   (type_name_subst tenvT (Atapp ts tc) =
      let args = MAP (type_name_subst tenvT) ts in
      match nsLookup tenvT tc with
        SOME (tvs,t) -> type_subst (alist_to_fmap (ZIP tvs args)) t
      | NONE -> Ttup args)`;;

(* HOL4's type_name_subst_ind: the calls in the let-bound MAP have the      *)
(* context MEM y ts only (HOL4's LET_CONG); the kit's induction theorem      *)
(* (cake_ind before the update below) also splits on the case under the let *)

let type_name_subst_ind = prove
 (`!P:(mlstring,mlstring,mlstring list#t)namespace->ast_t->bool.
     (!tenvT tv. P tenvT (Atvar tv)) /\
     (!tenvT ts. (!y. MEM y ts ==> P tenvT y) ==> P tenvT (Attup ts)) /\
     (!tenvT t1 t2. P tenvT t2 /\ P tenvT t1 ==> P tenvT (Atfun t1 t2)) /\
     (!tenvT ts tc. (!y. MEM y ts ==> P tenvT y) ==> P tenvT (Atapp ts tc))
     ==> (!x1 x2. P x1 x2)`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC (cake_ind "type_name_subst") THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[MESON[cases "option"; PAIR]
    `!x:(mlstring list#t)option. x = NONE \/ ?a b. x = SOME (a,b)`]);;

cake_ind_store := ("type_name_subst",type_name_subst_ind) :: !cake_ind_store;;

(* Check that a type definition defines no already defined types or        *)
(* duplicate constructors, and that the free type variables of each        *)
(* constructor argument type are included in the type's type parameters.   *)
(* Also check that all of the types mentioned are in scope.                *)

let check_ctor_tenv_def = cake_def
  `(check_ctor_tenv (tenvT:(modN,typeN,tvarN list#t)namespace)
      ([]:(tvarN list # mlstring # (conN # ast_t list) list) list) <=> T) /\
   (check_ctor_tenv tenvT (CONS (tvs,tn,ctors) tds) <=>
      check_dup_ctors (tvs,tn,ctors) /\
      ALL_DISTINCT tvs /\
      ALL (\cnts. match cnts with
                    (cn,ts) -> ALL (check_freevars_ast tvs) ts /\
                               ALL (check_type_names tenvT) ts)
          ctors /\
      ~MEM tn (MAP (\p. match p with (_,tn,_) -> tn) tds) /\
      check_ctor_tenv tenvT tds)`;;

let check_ctor_tenv_ind = cake_ind "check_ctor_tenv";;

(* HOL4 gives build_ctor_tenv its most general type (no annotation) *)

let build_ctor_tenv_def = cake_def
  `(build_ctor_tenv (tenvT:(mlstring,mlstring,mlstring list#t)namespace)
      ([]:(C # D # (B # ast_t list) list) list) ([]:E list) =
      alist_to_ns []:(A,B,C # t list # E)namespace) /\
   (build_ctor_tenv tenvT (CONS (tvs,tn,ctors) tds) (CONS id ids) =
      nsAppend (build_ctor_tenv tenvT tds ids)
        (alist_to_ns
          (REVERSE
            (MAP (\cnts. match cnts with
                           (cn,ts) -> (cn,(tvs,MAP (type_name_subst tenvT) ts,id)))
                 ctors)))) /\
   (build_ctor_tenv tenvT _ _ = alist_to_ns [])`;;

let build_ctor_tenv_ind = cake_ind "build_ctor_tenv";;

(* For the value restriction on let-based polymorphism *)

let is_value_def = sem1aux_def
  `(is_value (Lit _) <=> T) /\
   (is_value (Con _ es) <=> ALL is_value es) /\
   (is_value (Var _) <=> T) /\
   (is_value (Fun _ _) <=> T) /\
   (is_value (Tannot e _) <=> is_value e) /\
   (is_value (Lannot e _) <=> is_value e) /\
   (is_value _ <=> F)`;;

let is_value_ind = cake_ind "is_value";;

let type_p_rules,type_p_ind,type_p_cases,type_p_strongind = cake_inductive
  `(!tvs tenv t.
      check_freevars tvs [] t
      ==> type_p tvs tenv Pany t []) /\
   (!tvs tenv n t.
      check_freevars tvs [] t
      ==> type_p tvs tenv (Pvar n) t [(n,t)]) /\
   (!tvs tenv n.
      type_p tvs tenv (Plit (IntLit n)) Tint []) /\
   (!tvs tenv c.
      type_p tvs tenv (Plit (Char c)) Tchar []) /\
   (!tvs tenv s.
      type_p tvs tenv (Plit (StrLit s)) Tstring []) /\
   (!tvs tenv w.
      type_p tvs tenv (Plit (Word8 w)) Tword8 []) /\
   (!tvs tenv w.
      type_p tvs tenv (Plit (Word64 w)) Tword64 []) /\
   (!tvs tenv cn ps ts tvs' tn ts' bindings.
      ALL (check_freevars tvs []) ts' /\
      LENGTH ts' = LENGTH tvs' /\
      type_ps tvs tenv ps (MAP (type_subst (alist_to_fmap (ZIP tvs' ts'))) ts)
        bindings /\
      nsLookup (type_env_c tenv) cn = SOME (tvs',ts,tn)
      ==> type_p tvs tenv (Pcon (SOME cn) ps) (Tapp ts' tn) bindings) /\
   (!tvs tenv ps ts bindings.
      type_ps tvs tenv ps ts bindings
      ==> type_p tvs tenv (Pcon NONE ps) (Ttup ts) bindings) /\
   (!tvs tenv p t bindings.
      type_p tvs tenv p t bindings
      ==> type_p tvs tenv (Pref p) (Tref t) bindings) /\
   (!tvs tenv pat v t bindings.
      type_p tvs tenv pat t bindings
      ==> type_p tvs tenv (Pas pat v) t (APPEND bindings [(v,t)])) /\
   (!tvs tenv p t bindings.
      check_freevars_ast [] t /\
      check_type_names (type_env_t tenv) t /\
      type_p tvs tenv p (type_name_subst (type_env_t tenv) t) bindings
      ==> type_p tvs tenv (Ptannot p t) (type_name_subst (type_env_t tenv) t)
            bindings) /\
   (!tvs tenv.
      type_ps tvs tenv [] [] []) /\
   (!tvs tenv p ps t ts bindings bindings'.
      type_p tvs tenv p t bindings /\
      type_ps tvs tenv ps ts bindings'
      ==> type_ps tvs tenv (CONS p ps) (CONS t ts) (APPEND bindings' bindings))`;;

(* HOL4 keeps a commented-out rule for Letrec with type generalisation      *)
(* (bind_tvar tvs tenvE); the rule below is the one in force.               *)

let type_e_rules,type_e_ind,type_e_cases,type_e_strongind = cake_inductive
  `(!tenv tenvE n.
      type_e tenv tenvE (Lit (IntLit n)) Tint) /\
   (!tenv tenvE c.
      type_e tenv tenvE (Lit (Char c)) Tchar) /\
   (!tenv tenvE s.
      type_e tenv tenvE (Lit (StrLit s)) Tstring) /\
   (!tenv tenvE w.
      type_e tenv tenvE (Lit (Word8 w)) Tword8) /\
   (!tenv tenvE w.
      type_e tenv tenvE (Lit (Word64 w)) Tword64) /\
   (!tenv tenvE w.
      type_e tenv tenvE (Lit (Float64 w)) Tdouble) /\
   (!tenv tenvE e t.
      check_freevars (num_tvs tenvE) [] t /\
      type_e tenv tenvE e Texn
      ==> type_e tenv tenvE (Raise e) t) /\
   (!tenv tenvE e pes t.
      type_e tenv tenvE e t /\ ~(pes = []) /\
      (!p e. MEM (p,e) pes
             ==> ?bindings.
                   ALL_DISTINCT (pat_bindings p) /\
                   type_p (num_tvs tenvE) tenv p Texn bindings /\
                   type_e tenv (bind_var_list 0 bindings tenvE) e t)
      ==> type_e tenv tenvE (Handle e pes) t) /\
   (!tenv tenvE cn es tvs tn ts' ts.
      ALL (check_freevars (num_tvs tenvE) []) ts' /\
      LENGTH tvs = LENGTH ts' /\
      type_es tenv tenvE es (MAP (type_subst (alist_to_fmap (ZIP tvs ts'))) ts) /\
      nsLookup (type_env_c tenv) cn = SOME (tvs,ts,tn)
      ==> type_e tenv tenvE (Con (SOME cn) es) (Tapp ts' tn)) /\
   (!tenv tenvE es ts.
      type_es tenv tenvE es ts
      ==> type_e tenv tenvE (Con NONE es) (Ttup ts)) /\
   (!tenv tenvE n t targs tvs.
      tvs = LENGTH targs /\
      ALL (check_freevars (num_tvs tenvE) []) targs /\
      lookup_var n tenvE tenv = SOME (tvs,t)
      ==> type_e tenv tenvE (Var n) (deBruijn_subst 0 targs t)) /\
   (!tenv tenvE n e t1 t2.
      check_freevars (num_tvs tenvE) [] t1 /\
      type_e tenv (Bind_name n 0 t1 tenvE) e t2
      ==> type_e tenv tenvE (Fun n e) (Tfn t1 t2)) /\
   (!tenv tenvE op es ts t.
      type_es tenv tenvE es ts /\
      type_op op ts t /\
      check_freevars (num_tvs tenvE) [] t
      ==> type_e tenv tenvE (App op es) t) /\
   (!tenv tenvE l e1 e2.
      type_e tenv tenvE e1 Tbool /\
      type_e tenv tenvE e2 Tbool
      ==> type_e tenv tenvE (Log l e1 e2) Tbool) /\
   (!tenv tenvE e1 e2 e3 t.
      type_e tenv tenvE e1 Tbool /\
      type_e tenv tenvE e2 t /\
      type_e tenv tenvE e3 t
      ==> type_e tenv tenvE (If e1 e2 e3) t) /\
   (!tenv tenvE e pes t1 t2.
      type_e tenv tenvE e t1 /\ ~(pes = []) /\
      (!p e. MEM (p,e) pes
             ==> ?bindings.
                   ALL_DISTINCT (pat_bindings p) /\
                   type_p (num_tvs tenvE) tenv p t1 bindings /\
                   type_e tenv (bind_var_list 0 bindings tenvE) e t2)
      ==> type_e tenv tenvE (Mat e pes) t2) /\
   (!tenv tenvE n e1 e2 t1 t2.
      type_e tenv tenvE e1 t1 /\
      type_e tenv (opt_bind_name n 0 t1 tenvE) e2 t2
      ==> type_e tenv tenvE (Let n e1 e2) t2) /\
   (!tenv tenvE funs e t bindings.
      type_funs tenv (bind_var_list 0 bindings tenvE) funs bindings /\
      type_e tenv (bind_var_list 0 bindings tenvE) e t
      ==> type_e tenv tenvE (Letrec funs e) t) /\
   (!tenv tenvE e t.
      check_freevars_ast [] t /\
      check_type_names (type_env_t tenv) t /\
      type_e tenv tenvE e (type_name_subst (type_env_t tenv) t)
      ==> type_e tenv tenvE (Tannot e t) (type_name_subst (type_env_t tenv) t)) /\
   (!tenv tenvE e l t.
      type_e tenv tenvE e t
      ==> type_e tenv tenvE (Lannot e l) t) /\
   (!tenv tenvE.
      type_es tenv tenvE [] []) /\
   (!tenv tenvE e es t ts.
      type_e tenv tenvE e t /\
      type_es tenv tenvE es ts
      ==> type_es tenv tenvE (CONS e es) (CONS t ts)) /\
   (!tenv tenvE.
      type_funs tenv tenvE [] []) /\
   (!tenv tenvE fn n e funs bindings t1 t2.
      check_freevars (num_tvs tenvE) [] (Tfn t1 t2) /\
      type_e tenv (Bind_name n 0 t1 tenvE) e t2 /\
      type_funs tenv tenvE funs bindings /\
      ALOOKUP bindings fn = NONE
      ==> type_funs tenv tenvE (CONS (fn,n,e) funs) (CONS (fn,Tfn t1 t2) bindings))`;;

let tenv_add_tvs_def = cake_def
  `tenv_add_tvs (tvs:num) (bindings:(mlstring#t)list) =
     MAP (\nt. match nt with (n,t) -> (n,(tvs,t))) bindings`;;

let type_pe_determ_def = cake_def
  `type_pe_determ (tenv:type_env) (tenvE:tenv_val_exp) (p:pat) (e:exp) <=>
     !t1 tenv1 t2 tenv2.
       type_p 0 tenv p t1 tenv1 /\ type_e tenv tenvE e t1 /\
       type_p 0 tenv p t2 tenv2 /\ type_e tenv tenvE e t2
       ==> tenv1 = tenv2`;;

let tscheme_inst_def = cake_def
  `tscheme_inst ((tvs_spec:num),(t_spec:t)) ((tvs_impl:num),(t_impl:t)) <=>
     ?subst.
       LENGTH subst = tvs_impl /\
       check_freevars tvs_impl [] t_impl /\
       ALL (check_freevars tvs_spec []) subst /\
       deBruijn_subst 0 subst t_impl = t_spec`;;

let tenvLift_def = cake_def
  `tenvLift (mn:mlstring) (tenv:type_env) =
     type_env_REC (nsLift mn (type_env_v tenv)) (nsLift mn (type_env_c tenv))
                  (nsLift mn (type_env_t tenv))`;;

(* In the second rule for Dlet, the premise under extra_checks makes sure   *)
(* that when the value restriction prohibits generalisation, a type error   *)
(* is given rather than picking an arbitrary instantiation; the check is    *)
(* only done when the extra_checks argument asks for it.                    *)

let type_d_rules,type_d_ind,type_d_cases,type_d_strongind = cake_inductive
  `(!extra_checks tvs tenv p e t bindings locs.
      is_value e /\
      ALL_DISTINCT (pat_bindings p) /\
      type_p tvs tenv p t bindings /\
      type_e tenv (bind_tvar tvs Empty) e t /\
      (extra_checks ==>
         (!tvs' bindings' t'.
            type_p tvs' tenv p t' bindings' /\
            type_e tenv (bind_tvar tvs' Empty) e t'
            ==> ALL2 tscheme_inst (MAP SND (tenv_add_tvs tvs' bindings'))
                                  (MAP SND (tenv_add_tvs tvs bindings))))
      ==> type_d extra_checks tenv (Dlet locs p e) {}
            (type_env_REC (alist_to_ns (tenv_add_tvs tvs bindings)) nsEmpty
                          nsEmpty)) /\
   (!extra_checks tenv p e t bindings locs.
      (extra_checks ==> ~is_value e /\ type_pe_determ tenv Empty p e) /\
      ALL_DISTINCT (pat_bindings p) /\
      type_p 0 tenv p t bindings /\
      type_e tenv Empty e t
      ==> type_d extra_checks tenv (Dlet locs p e) {}
            (type_env_REC (alist_to_ns (tenv_add_tvs 0 bindings)) nsEmpty
                          nsEmpty)) /\
   (!extra_checks tenv funs bindings tvs locs.
      type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs Empty)) funs
        bindings /\
      (extra_checks ==>
         (!tvs' bindings'.
            type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs' Empty))
              funs bindings'
            ==> ALL2 tscheme_inst (MAP SND (tenv_add_tvs tvs' bindings'))
                                  (MAP SND (tenv_add_tvs tvs bindings))))
      ==> type_d extra_checks tenv (Dletrec locs funs) {}
            (type_env_REC (alist_to_ns (tenv_add_tvs tvs bindings)) nsEmpty
                          nsEmpty)) /\
   (!extra_checks tenv tdefs type_identities tenvT locs.
      ALL_DISTINCT type_identities /\
      DISJOINT (set_of_list type_identities)
               (set_of_list (CONS Tlist_num (CONS Tbool_num prim_type_nums))) /\
      check_ctor_tenv (nsAppend tenvT (type_env_t tenv)) tdefs /\
      LENGTH type_identities = LENGTH tdefs /\
      tenvT = alist_to_ns
                (MAP2 (\tdef i. match tdef with
                                  (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i)))
                      tdefs type_identities)
      ==> type_d extra_checks tenv (Dtype locs tdefs) (set_of_list type_identities)
            (type_env_REC nsEmpty
               (build_ctor_tenv (nsAppend tenvT (type_env_t tenv)) tdefs
                  type_identities)
               tenvT)) /\
   (!extra_checks tenv tvs tn t locs.
      check_freevars_ast tvs t /\
      check_type_names (type_env_t tenv) t /\
      ALL_DISTINCT tvs
      ==> type_d extra_checks tenv (Dtabbrev locs tvs tn t) {}
            (type_env_REC nsEmpty nsEmpty
               (nsSing tn (tvs,type_name_subst (type_env_t tenv) t)))) /\
   (!extra_checks tenv cn ts locs.
      ALL (check_freevars_ast []) ts /\
      ALL (check_type_names (type_env_t tenv)) ts
      ==> type_d extra_checks tenv (Dexn locs cn ts) {}
            (type_env_REC nsEmpty
               (nsSing cn ([],MAP (type_name_subst (type_env_t tenv)) ts,Texn_num))
               nsEmpty)) /\
   (!extra_checks tenv mn ds decls tenv'.
      type_ds extra_checks tenv ds decls tenv'
      ==> type_d extra_checks tenv (Dmod mn ds) decls (tenvLift mn tenv')) /\
   (!extra_checks tenv lds ds tenv1 tenv2 decls1 decls2.
      type_ds extra_checks tenv lds decls1 tenv1 /\
      type_ds extra_checks (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 /\
      DISJOINT decls1 decls2
      ==> type_d extra_checks tenv (Dlocal lds ds) (decls1 UNION decls2) tenv2) /\
   (!extra_checks tenv.
      type_ds extra_checks tenv [] {} (type_env_REC nsEmpty nsEmpty nsEmpty)) /\
   (!extra_checks tenv d ds tenv1 tenv2 decls1 decls2.
      type_d extra_checks tenv d decls1 tenv1 /\
      type_ds extra_checks (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 /\
      DISJOINT decls1 decls2
      ==> type_ds extra_checks tenv (CONS d ds) (decls1 UNION decls2)
            (extend_dec_tenv tenv2 tenv1))`;;

(* HOL4 keeps (commented out) Lem's type_specs, weak_decls, weak_tenvT,     *)
(* check_signature, type_top and type_prog of the module system.            *)

let tscheme_inst2_def = cake_def
  `tscheme_inst2 (_:A) (ts1:num#t) (ts2:num#t) <=> tscheme_inst ts1 ts2`;;

let weak_tenv_def = cake_def
  `weak_tenv (tenv_impl:type_env) (tenv_spec:type_env) <=>
     nsSub tscheme_inst2 (type_env_v tenv_spec) (type_env_v tenv_impl) /\
     nsSub (\i x y. match (i,x,y) with (_,x,y) -> x = y)
           (type_env_c tenv_spec) (type_env_c tenv_impl)`;;
