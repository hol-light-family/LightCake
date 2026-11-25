(* ========================================================================= *)
(* typeDecToPP: port of HOL4 compiler/printing/typeDecToPPScript.sml         *)
(* (CakeML v3479).  Maps a Dtype or Dtabbrev declaration (the ast syntax)    *)
(* to the default pretty-printer function definition for it (also as ast     *)
(* syntax).                                                                  *)
(*                                                                           *)
(* Used by the compiler (in add-pp mode) to set up default pretty-printers   *)
(* for user types and by the basis translation to set up default             *)
(* pretty-printers for some basis types.                                     *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The mlstring literal of HOL4 (written with French quotes) is            *)
(*   implode "..." (basis/pure/mlstring.ml); s1 ^ s2 is strcat s1 s2 (left   *)
(*   associative in HOL4); mlint toString is toString; GENLIST f n is        *)
(*   list_of_seq f n; FOLDR f e l is ITLIST f l e; HOL4 h :: t ++ l is       *)
(*   APPEND (CONS h t) l (:: binds tighter than ++ in HOL4).                 *)
(* - HOL4 paired lambdas (\(v, exp). t) are written                          *)
(*   (\p. match p with (v,exp) -> t), as in semantics/ast.ml.                *)
(* - The clauses of a HOL Light definition share their variables, so a name  *)
(*   used with two types gets a second name: pp_prefix (Long m id) for HOL4  *)
(*   pp_prefix (Long nm id), pp_of_ast_t fixes (Atvar tv) for HOL4           *)
(*   pp_of_ast_t fixes (Atvar nm).                                           *)
(* - HOL4's variable tvars is tvs (holSyntax has a constant tvars).          *)
(* ========================================================================= *)

needs "semantics/ast.ml";;
needs "basis/pure/mlstring.ml";;
needs "basis/pure/mlint.ml";;

type_invention_error := true;;

let pppre_def = cake_def
  `pppre nm = strcat (implode "pp_") nm`;;

let pp_prefix_def = cake_def
  `(pp_prefix (Short nm:(A,mlstring)id) = Short (pppre nm)) /\
   (pp_prefix (Long m id) = Long m (pp_prefix id))`;;

(* FIXME: is this elsewhere? *)

let mk_list_exp_def = cake_def
  `(mk_list_exp [] = Con (SOME (Short (implode "[]"))) []) /\
   (mk_list_exp (CONS x xs) =
      Con (SOME (Short (implode "::"))) [x; mk_list_exp xs])`;;

let con_x_i_pat_def = cake_def
  `con_x_i_pat cname n =
     Pcon cname
       (list_of_seq (\i. Pvar (strcat (implode "x") (toString (&i:int)))) n)`;;

let x_i_list_f_apps_def = cake_def
  `x_i_list_f_apps fs =
     mk_list_exp
       (MAPi (\i f. App Opapp [f; Var (Short (strcat (implode "x")
                                                     (toString (&i:int))))])
             fs)`;;

let mod_pp_def = cake_def
  `mod_pp (nm:(mlstring,A)id) = Long (implode "PrettyPrinter") nm`;;

let id_to_str_def = cake_def
  `(id_to_str (Short s) = s) /\
   (id_to_str (Long mnm id) =
      strcat (strcat mnm (implode ".")) (id_to_str id))`;;

(* Avoids MAP (pp_of_ast_t fixes) so it is possible to use cv_trans *)

let pp_of_ast_t_def = cake_def
  `(pp_of_ast_t fixes (Atvar tv) = Var (pp_prefix (Short tv))) /\
   (pp_of_ast_t fixes (Atfun _ _) =
      Fun (implode "x") (Var (Short (implode "pp_fun")))) /\
   (pp_of_ast_t fixes (Atapp xs nm) =
      match nsLookup fixes nm with
        NONE -> Apps (Var (pp_prefix nm)) (pp_of_ast_ts fixes xs)
      | SOME NONE ->
          Fun (implode "x")
            (App Opapp [Var (mod_pp (Short (implode "unprintable")));
                        Lit (StrLit (id_to_str nm))])
      | SOME (SOME nm2) -> Apps (Var (pp_prefix nm2)) (pp_of_ast_ts fixes xs)) /\
   (pp_of_ast_t fixes (Attup ts) =
      Fun (implode "x")
        (App Opapp [Var (mod_pp (Short (implode "tuple")));
                    Mat (Var (Short (implode "x")))
                      [(con_x_i_pat NONE (LENGTH ts),
                        x_i_list_f_apps (pp_of_ast_ts fixes ts))]])) /\
   (pp_of_ast_ts fixes [] = []) /\
   (pp_of_ast_ts fixes (CONS h tl) =
      CONS (pp_of_ast_t fixes h) (pp_of_ast_ts fixes tl))`;;

let mk_pps_for_type_def = cake_def
  `mk_pps_for_type fixes (tvs,nm,conss) =
     let (v,exp) =
       ITLIST (\nm p. match p with (v,exp) -> (pppre nm, Fun v exp)) tvs
         (implode "x",
          Mat (Var (Short (implode "x")))
            (MAP (\p. match p with
                        (conN,ts) ->
                          (con_x_i_pat (SOME (Short conN)) (LENGTH ts),
                           Apps (Var (mod_pp (Short (implode "app_block"))))
                             [Lit (StrLit conN);
                              x_i_list_f_apps (MAP (pp_of_ast_t fixes) ts)]))
                 conss)) in
     (pppre nm,v,exp)`;;

let mk_pp_type_def = cake_def
  `mk_pp_type fixes (funs:type_def) =
     Dletrec unknown_loc (MAP (mk_pps_for_type fixes) funs)`;;

(* the Fun x is an eta-expansion to avoid value restriction violations *)

let mk_pp_tabbrev_def = cake_def
  `mk_pp_tabbrev fixes tvs nm ast_t =
     let body = ITLIST (\nm exp. Fun (pppre nm) exp) tvs
                       (pp_of_ast_t fixes ast_t) in
     Dlet unknown_loc (Pvar (pppre nm))
       (Fun (implode "x") (App Opapp [body; Var (Short (implode "x"))]))`;;

let pps_for_dec_def = cake_def
  `(pps_for_dec fixes (Dtype locs type_def) = [mk_pp_type fixes type_def]) /\
   (pps_for_dec fixes (Dtabbrev locs tvs nm ast_t) =
      [mk_pp_tabbrev fixes tvs nm ast_t]) /\
   (pps_for_dec _ dec = [])`;;

let add_pp_decs_def = cake_def_wf
  `MEASURE (\p:((mlstring,mlstring,((mlstring,mlstring)id)option)namespace)#
               (dec list). list_size dec_size (SND p))`
  TERM_TAC
  `(add_pp_decs fixes [] = []) /\
   (add_pp_decs fixes (CONS (Dmod modN decs) decs2) =
      CONS (Dmod modN (add_pp_decs fixes decs)) (add_pp_decs fixes decs2)) /\
   (add_pp_decs fixes (CONS (Dlocal ldecs decs) decs2) =
      CONS (Dlocal (add_pp_decs fixes ldecs) (add_pp_decs fixes decs))
           (add_pp_decs fixes decs2)) /\
   (add_pp_decs fixes (CONS d decs) =
      APPEND (CONS d (pps_for_dec fixes d)) (add_pp_decs fixes decs))`;;

let add_pp_decs_ind = cake_ind "add_pp_decs";;
