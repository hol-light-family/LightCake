(* ========================================================================= *)
(* infer_t: port of HOL4 compiler/inference/infer_tScript.sml (CakeML        *)
(* v3479).  The infer_t datatype and various to_string functions.            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;
needs "basis/pure/mlint.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Notes on the rendering:                                                   *)
(* - The mlstring literal of x is implode "x"; s1 ^ s2 is strcat s1 s2 (left *)
(*   associative); concat is mlstring_concat; mlint$toString is toString;    *)
(*   #"a" is CHR 97; l1 ++ l2 is APPEND l1 l2 (left associative).            *)
(* - commas is infer_t_commas (doc/names.tsv).                               *)
(* - HOL4 gives get_tyname, type_ident_to_string and inf_type_to_string_rec  *)
(*   their most general types: the namespaces have values of type A # t.   *)
(* ------------------------------------------------------------------------- *)

let infer_t_INDUCT,infer_t_RECURSION = cake_type
  "infer_t = Infer_Tvar_db num
           | Infer_Tapp (infer_t list) type_ident
           | Infer_Tuvar num";;

(* HOL4: infer_t_induction specialised to P and EVERY P, first conjunct,   *)
(* EVERY_MEM                                                                *)

let infer_t_ind = prove
 (`!P. (!n. P (Infer_Tvar_db n)) /\
       (!l. (!e. MEM e l ==> P e) ==> !t. P (Infer_Tapp l t)) /\
       (!n. P (Infer_Tuvar n))
       ==> !i. P i`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`P:infer_t->bool`; `ALL (P:infer_t->bool)`] infer_t_INDUCT) THEN
  ASM_SIMP_TAC[ALL; GSYM ALL_MEM]);;

let id_to_string_def = cake_def
  `(id_to_string (Short s:(mlstring,mlstring)id) = s) /\
   (id_to_string (Long x id) =
      mlstring_concat [x; implode "."; id_to_string id])`;;

(* the clauses are parsed separately (xs and m have different types in the *)
(* second and the third clause)                                             *)

let get_tyname_def = cake_def_clauses
  [`get_tyname (n:num) (Bind [] [] :(mlstring,mlstring,A#t)namespace) =
      NONE:mlstring option`;
   `get_tyname (n:num) (Bind [] (CONS (m,ys) xs) :(mlstring,mlstring,A#t)namespace) =
      match get_tyname n ys with
        NONE -> get_tyname n (Bind [] xs)
      | SOME x -> SOME (strcat (strcat m (implode ".")) x)`;
   `get_tyname (n:num) (Bind (CONS (tyname,_,t) xs) m :(mlstring,mlstring,A#t)namespace) =
      if (match t with Tapp _ m -> m = n | _ -> F) then
        SOME tyname
      else get_tyname n (Bind xs m)`];;

let get_tyname_ind = cake_ind "get_tyname";;

let type_ident_to_string_def = cake_def
  `type_ident_to_string (tys:(mlstring,mlstring,A#t)namespace) (ti:num) =
     if ti = Tarray_num then
       implode "Array.array"
     else if ti = Tbool_num then
       implode "bool"
     else if ti = Tchar_num then
       implode "char"
     else if ti = Texn_num then
       implode "exn"
     else if ti = Tint_num then
       implode "int"
     else if ti = Tlist_num then
       implode "list"
     else if ti = Tref_num then
       implode "ref"
     else if ti = Tstring_num then
       implode "string"
     else if ti = Tvector_num then
       implode "Vector.vector"
     else if ti = Tword64_num then
       implode "Word64.word"
     else if ti = Tword8_num then
       implode "Word8.word"
     else if ti = Tword8array_num then
       implode "byte_array"
     else if ti = Tdouble_num then
       implode "Double.double"
     else
       match get_tyname ti tys with
         NONE -> toString (&ti)
       | SOME s -> s`;;

let ty_var_name_def = cake_def
  `ty_var_name (n:num) =
     if n < 28 then implode (APPEND "'" [CHR (n + ORD (CHR 97))])
     else mlstring_concat [implode "'"; toString (&n)]`;;

let infer_t_commas_def = cake_def
  `(infer_t_commas (c:A) [] = []) /\
   (infer_t_commas c [x] = [x]) /\
   (infer_t_commas c (CONS x ys) = CONS x (CONS c (infer_t_commas c ys)))`;;

let infer_t_commas_ind = cake_ind "infer_t_commas";;

(* HOL4's argument name threshold is a constant of the session (from     *)
(* binary_ieee): written thresh                                            *)

let add_parens_def = cake_def
  `add_parens (thresh:num) (x,n:num) =
     if thresh < n then mlstring_concat [implode "("; x; implode ")"]
     else x`;;

let inf_type_to_string_rec_def = cake_def_wf
  `MEASURE (\x:(mlstring,mlstring,A#t)namespace#infer_t +
                (mlstring,mlstring,A#t)namespace#(infer_t list).
              match x with
                INL (_,t) -> infer_t_size t
              | INR (_,ts) -> list_size infer_t_size ts)`
  TERM_TAC
  `(inf_type_to_string_rec (tys:(mlstring,mlstring,A#t)namespace)
      (Infer_Tuvar n) =
      (mlstring_concat [implode "_"; toString (&n)],0)) /\
   (inf_type_to_string_rec tys (Infer_Tvar_db n) =
      (mlstring_concat [ty_var_name n],0)) /\
   (inf_type_to_string_rec tys (Infer_Tapp ts ti) =
      if ti = Tfn_num then
        (match ts with
           [t1; t2] ->
             (mlstring_concat [add_parens 2 (inf_type_to_string_rec tys t1);
                               implode " -> ";
                               add_parens 3 (inf_type_to_string_rec tys t2)],3)
         | _ -> (implode "<bad function type>",0))
      else if ti = Ttup_num then
        (match ts with
           [] -> (implode "unit",0)
         | [t] -> inf_type_to_string_rec tys t
         | _ -> (mlstring_concat (infer_t_commas (implode " * ")
                   (MAP (add_parens 1) (inf_type_to_string_rec_list tys ts))),2))
      else
        match ts with
          [] -> (type_ident_to_string tys ti,0)
        | [t] ->
            (mlstring_concat [add_parens 1 (inf_type_to_string_rec tys t);
                              implode " ";
                              type_ident_to_string tys ti],1)
        | _ ->
            (mlstring_concat
               (APPEND
                  (APPEND [implode "("]
                     (infer_t_commas (implode ", ")
                        (MAP (add_parens 5)
                           (inf_type_to_string_rec_list tys ts))))
                  [implode ") "; type_ident_to_string tys ti]),1)) /\
   (inf_type_to_string_rec_list tys [] = []) /\
   (inf_type_to_string_rec_list tys (CONS t ts) =
      CONS (inf_type_to_string_rec tys t)
           (inf_type_to_string_rec_list tys ts))`;;

let inf_type_to_string_rec_ind = cake_ind "inf_type_to_string_rec";;

let inf_type_to_string_def = cake_def
  `inf_type_to_string (tys:(mlstring,mlstring,A#t)namespace) (t:infer_t) =
     FST (inf_type_to_string_rec tys t)`;;
