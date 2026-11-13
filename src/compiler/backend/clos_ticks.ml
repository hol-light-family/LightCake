(* ========================================================================= *)
(* clos_ticks: port of HOL4 compiler/backend/clos_ticksScript.sml (CakeML    *)
(* v3479).                                                                   *)
(* This simple compiler phase removes all Tick operations. Tick operations  *)
(* appear as a side effect of function inlining, and can be removed because *)
(* they have no observable behaviour. It is a good idea to remove them      *)
(* because they get in the way of pattern matching done by several          *)
(* optimisations.                                                            *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The clauses of a HOL Light definition share their variables, so a name *)
(*   used with two types gets a second name: the names of clos_Letrec and Fn *)
(*   (HOL4 t) are nms and nm, and the list of remove_ticks_let is rest.      *)
(* - HOL4's paired lambdas (\(num_args,x). t) are written                    *)
(*   (\p. match p with (num_args,x) -> t).                                   *)
(* - The definitions are made with sem1aux_def_wf (semantics/sem1aux_tfl.ml) *)
(*   and, for the three mutually recursive functions, il1aux_def_wf          *)
(*   (compiler/backend/il1aux_mutual.ml), which also gives their induction  *)
(*   theorem; the relations are HOL4's automatic size measures.             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/closLang.ml";;
needs "semantics/sem1aux_tfl.ml";;
needs "compiler/backend/il1aux_mutual.ml";;

type_invention_error := true;;

(* HOL4: remove_ticks *)

let clos_ticks_remove_ticks_def = sem1aux_def_wf
  `measure (\es:clos_exp list. list_size clos_exp_size es)`
  SEM1AUX_TC_TAC
  `(clos_ticks_remove_ticks [] = []) /\
   (clos_ticks_remove_ticks (CONS (x:clos_exp) (CONS y xs)) =
      CONS (HD (clos_ticks_remove_ticks [x]))
           (clos_ticks_remove_ticks (CONS y xs))) /\
   (clos_ticks_remove_ticks [clos_Var t v] = [clos_Var t v]) /\
   (clos_ticks_remove_ticks [clos_If t x1 x2 x3] =
      [clos_If t (HD (clos_ticks_remove_ticks [x1]))
                 (HD (clos_ticks_remove_ticks [x2]))
                 (HD (clos_ticks_remove_ticks [x3]))]) /\
   (clos_ticks_remove_ticks [clos_Let t xs x2] =
      [clos_Let t (clos_ticks_remove_ticks xs)
                  (HD (clos_ticks_remove_ticks [x2]))]) /\
   (clos_ticks_remove_ticks [clos_Raise t x1] =
      [clos_Raise t (HD (clos_ticks_remove_ticks [x1]))]) /\
   (clos_ticks_remove_ticks [clos_Handle t x1 x2] =
      [clos_Handle t (HD (clos_ticks_remove_ticks [x1]))
                     (HD (clos_ticks_remove_ticks [x2]))]) /\
   (clos_ticks_remove_ticks [clos_Op t op xs] =
      [clos_Op t op (clos_ticks_remove_ticks xs)]) /\
   (clos_ticks_remove_ticks [clos_Tick t x1] = clos_ticks_remove_ticks [x1]) /\
   (clos_ticks_remove_ticks [clos_Call t ticks dest xs] =
      [clos_Call t 0 dest (clos_ticks_remove_ticks xs)]) /\
   (clos_ticks_remove_ticks [clos_App t loc_opt x1 xs] =
      [clos_App t loc_opt (HD (clos_ticks_remove_ticks [x1]))
                (clos_ticks_remove_ticks xs)]) /\
   (clos_ticks_remove_ticks [clos_Letrec nms loc_opt vs fns x1] =
      let new_fns =
        MAP (\p. match p with
                   (num_args,x) -> (num_args, HD (clos_ticks_remove_ticks [x])))
            fns in
      [clos_Letrec nms loc_opt vs new_fns (HD (clos_ticks_remove_ticks [x1]))]) /\
   (clos_ticks_remove_ticks [Fn nm loc_opt vs num_args x1] =
      [Fn nm loc_opt vs num_args (HD (clos_ticks_remove_ticks [x1]))])`;;

let clos_ticks_remove_ticks_ind = cake_ind "clos_ticks_remove_ticks";;

(* HOL4: remove_ticks_sing, remove_ticks_list, remove_ticks_let *)

let clos_ticks_remove_ticks_sing_def = il1aux_def_wf
  `measure
     (\x:clos_exp + clos_exp list + (num # clos_exp) list.
        sum_CASE x (\e. clos_exp_size e)
          (\y. sum_CASE y (\es. list_size clos_exp_size es)
                 (\fns. list_size (pair_size (\x. x) clos_exp_size) fns)))`
  SEM1AUX_TC_TAC
  `(clos_ticks_remove_ticks_sing (clos_Var t v) = clos_Var t v) /\
   (clos_ticks_remove_ticks_sing (clos_If t x1 x2 x3) =
      clos_If t (clos_ticks_remove_ticks_sing x1)
                (clos_ticks_remove_ticks_sing x2)
                (clos_ticks_remove_ticks_sing x3)) /\
   (clos_ticks_remove_ticks_sing (clos_Let t xs x2) =
      clos_Let t (clos_ticks_remove_ticks_list xs)
                 (clos_ticks_remove_ticks_sing x2)) /\
   (clos_ticks_remove_ticks_sing (clos_Raise t x1) =
      clos_Raise t (clos_ticks_remove_ticks_sing x1)) /\
   (clos_ticks_remove_ticks_sing (clos_Handle t x1 x2) =
      clos_Handle t (clos_ticks_remove_ticks_sing x1)
                    (clos_ticks_remove_ticks_sing x2)) /\
   (clos_ticks_remove_ticks_sing (clos_Op t op xs) =
      clos_Op t op (clos_ticks_remove_ticks_list xs)) /\
   (clos_ticks_remove_ticks_sing (clos_Tick t x1) =
      clos_ticks_remove_ticks_sing x1) /\
   (clos_ticks_remove_ticks_sing (clos_Call t ticks dest xs) =
      clos_Call t 0 dest (clos_ticks_remove_ticks_list xs)) /\
   (clos_ticks_remove_ticks_sing (clos_App t loc_opt x1 xs) =
      clos_App t loc_opt (clos_ticks_remove_ticks_sing x1)
               (clos_ticks_remove_ticks_list xs)) /\
   (clos_ticks_remove_ticks_sing (clos_Letrec nms loc_opt vs fns x1) =
      let new_fns = remove_ticks_let fns in
      clos_Letrec nms loc_opt vs new_fns (clos_ticks_remove_ticks_sing x1)) /\
   (clos_ticks_remove_ticks_sing (Fn nm loc_opt vs num_args x1) =
      Fn nm loc_opt vs num_args (clos_ticks_remove_ticks_sing x1)) /\
   (clos_ticks_remove_ticks_list [] = []) /\
   (clos_ticks_remove_ticks_list (CONS (x:clos_exp) xs) =
      CONS (clos_ticks_remove_ticks_sing x) (clos_ticks_remove_ticks_list xs)) /\
   (remove_ticks_let [] = []) /\
   (remove_ticks_let (CONS (num_args,x) rest) =
      CONS (num_args, clos_ticks_remove_ticks_sing x) (remove_ticks_let rest))`;;

let clos_ticks_remove_ticks_sing_ind = cake_ind "clos_ticks_remove_ticks_sing";;

(* HOL4: LENGTH_remove_ticks *)

let clos_ticks_LENGTH_remove_ticks = prove
 (`!es:clos_exp list. LENGTH (clos_ticks_remove_ticks es) = LENGTH es`,
  MATCH_MP_TAC clos_ticks_remove_ticks_ind THEN
  FS[clos_ticks_remove_ticks_def; LENGTH]);;

let remove_ticks_sing_eq = prove
 (CASE_TERM
  `(!e. clos_ticks_remove_ticks [e] = [clos_ticks_remove_ticks_sing e]) /\
   (!es. clos_ticks_remove_ticks es = clos_ticks_remove_ticks_list es) /\
   (!fns.
      remove_ticks_let fns =
      MAP (\p. match p with
                 (num_args,x) -> (num_args, HD (clos_ticks_remove_ticks [x])))
          fns)`,
  MATCH_MP_TAC clos_ticks_remove_ticks_sing_ind THEN
  RW[clos_ticks_remove_ticks_def; clos_ticks_remove_ticks_sing_def] THEN
  TRY (FS[] THEN NO_TAC) THEN
  CASES_ON `xs:clos_exp list` THEN
  FS[clos_ticks_remove_ticks_def; clos_ticks_remove_ticks_sing_def]);;

(* HOL4: compile_inc *)

let clos_ticks_compile_inc_def = cake_def
  `clos_ticks_compile_inc (e,xs:A) = (clos_ticks_remove_ticks e, []:B list)`;;
