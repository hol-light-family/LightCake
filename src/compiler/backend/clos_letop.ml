(* ========================================================================= *)
(* clos_letop: port of HOL4 compiler/backend/clos_letopScript.sml (CakeML    *)
(* v3479).                                                                   *)
(* This simple compiler phase tidies up after function inlining, in         *)
(* particular it turns Let [x0; x1; ...] (Op op [Var 0; Var 1; ...]) into    *)
(* Op op [x0; x1; ...], which enables further optimisation later, e.g. in    *)
(* bvi_tailrec.                                                              *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The clauses of a HOL Light definition share their variables, so a name *)
(*   used with two types gets a second name: the names of clos_Letrec and Fn *)
(*   (HOL4 t) are nms and nm, and the list of let_op_let is rest.            *)
(* - HOL4's paired lambdas (\(num_args,x). t) are written                    *)
(*   (\p. match p with (num_args,x) -> t).                                   *)
(* - The definitions are made with sem1aux_def(_wf) (semantics/              *)
(*   sem1aux_tfl.ml) and, for the three mutually recursive functions,        *)
(*   il1aux_def_wf (compiler/backend/il1aux_mutual.ml), which also gives     *)
(*   their induction theorem; where HOL4's termination is automatic, the     *)
(*   relation is its size measure.                                           *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/closLang.ml";;
needs "semantics/sem1aux_tfl.ml";;
needs "compiler/backend/il1aux_mutual.ml";;

type_invention_error := true;;

(* let_op: a function that optimises Let [...] (Op op [Var ...]) *)

(* HOL4: var_list *)

let clos_letop_var_list_def = sem1aux_def_wf
  `MEASURE (\p:num # clos_exp list # A list. list_size clos_exp_size (FST (SND p)))`
  SEM1AUX_TC_TAC
  `(clos_letop_var_list n [] ([]:A list) <=> T) /\
   (clos_letop_var_list n (CONS (clos_Var t m) xs) (CONS y ys) <=>
      m = n /\ clos_letop_var_list (n + 1) xs ys) /\
   (clos_letop_var_list _ _ _ <=> F)`;;

let clos_letop_var_list_ind = cake_ind "clos_letop_var_list";;

(* HOL4: dest_op *)

let clos_letop_dest_op_def = sem1aux_def
  `(clos_letop_dest_op (clos_Op t op xs) (args:A list) =
      if clos_letop_var_list 0 xs args then SOME op else NONE) /\
   (clos_letop_dest_op _ _ = NONE)`;;

(* HOL4: let_op *)

let clos_letop_let_op_def = sem1aux_def_wf
  `MEASURE (\es:clos_exp list. list_size clos_exp_size es)`
  SEM1AUX_TC_TAC
  `(clos_letop_let_op [] = []) /\
   (clos_letop_let_op (CONS (x:clos_exp) (CONS y xs)) =
      CONS (HD (clos_letop_let_op [x])) (clos_letop_let_op (CONS y xs))) /\
   (clos_letop_let_op [clos_Var t v] = [clos_Var t v]) /\
   (clos_letop_let_op [clos_If t x1 x2 x3] =
      [clos_If t (HD (clos_letop_let_op [x1]))
                 (HD (clos_letop_let_op [x2]))
                 (HD (clos_letop_let_op [x3]))]) /\
   (clos_letop_let_op [clos_Let t xs x2] =
      let xs = clos_letop_let_op xs in
      let x2 = HD (clos_letop_let_op [x2]) in
        match clos_letop_dest_op x2 xs with
          SOME op -> [clos_Op t op xs]
        | NONE -> [clos_Let t xs x2]) /\
   (clos_letop_let_op [clos_Raise t x1] =
      [clos_Raise t (HD (clos_letop_let_op [x1]))]) /\
   (clos_letop_let_op [clos_Handle t x1 x2] =
      [clos_Handle t (HD (clos_letop_let_op [x1]))
                     (HD (clos_letop_let_op [x2]))]) /\
   (clos_letop_let_op [clos_Op t op xs] =
      [clos_Op t op (clos_letop_let_op xs)]) /\
   (clos_letop_let_op [clos_Tick t x] =
      [clos_Tick t (HD (clos_letop_let_op [x]))]) /\
   (clos_letop_let_op [clos_Call t ticks dest xs] =
      [clos_Call t ticks dest (clos_letop_let_op xs)]) /\
   (clos_letop_let_op [clos_App t loc_opt x1 xs] =
      [clos_App t loc_opt (HD (clos_letop_let_op [x1]))
                (clos_letop_let_op xs)]) /\
   (clos_letop_let_op [clos_Letrec nms loc_opt vs fns x1] =
      let new_fns =
        MAP (\p. match p with
                   (num_args,x) -> (num_args, HD (clos_letop_let_op [x])))
            fns in
      [clos_Letrec nms loc_opt vs new_fns (HD (clos_letop_let_op [x1]))]) /\
   (clos_letop_let_op [Fn nm loc_opt vs num_args x1] =
      [Fn nm loc_opt vs num_args (HD (clos_letop_let_op [x1]))])`;;

let clos_letop_let_op_ind = cake_ind "clos_letop_let_op";;

(* HOL4: LENGTH_let_op *)

let clos_letop_LENGTH_let_op = prove
 (`!xs. LENGTH (clos_letop_let_op xs) = LENGTH xs`,
  MATCH_MP_TAC clos_letop_let_op_ind THEN
  RW[clos_letop_let_op_def; LENGTH] THEN CASE_TAC THEN SIMP[LENGTH]);;

(* HOL4: let_op_sing, let_op_list, let_op_let *)

let clos_letop_let_op_sing_def = il1aux_def_wf
  `MEASURE
     (\x:clos_exp + clos_exp list + (num # clos_exp) list.
        sum_CASE x (\e. clos_exp_size e)
          (\y. sum_CASE y (\es. list_size clos_exp_size es)
                 (\fns. list_size (pair_size (\x. x) clos_exp_size) fns)))`
  SEM1AUX_TC_TAC
  `(clos_letop_let_op_sing (clos_Var t v) = clos_Var t v) /\
   (clos_letop_let_op_sing (clos_If t x1 x2 x3) =
      clos_If t (clos_letop_let_op_sing x1)
                (clos_letop_let_op_sing x2)
                (clos_letop_let_op_sing x3)) /\
   (clos_letop_let_op_sing (clos_Let t xs x2) =
      let xs = clos_letop_let_op_list xs in
      let x2 = clos_letop_let_op_sing x2 in
        match clos_letop_dest_op x2 xs with
          SOME op -> clos_Op t op xs
        | NONE -> clos_Let t xs x2) /\
   (clos_letop_let_op_sing (clos_Raise t x1) =
      clos_Raise t (clos_letop_let_op_sing x1)) /\
   (clos_letop_let_op_sing (clos_Handle t x1 x2) =
      clos_Handle t (clos_letop_let_op_sing x1) (clos_letop_let_op_sing x2)) /\
   (clos_letop_let_op_sing (clos_Op t op xs) =
      clos_Op t op (clos_letop_let_op_list xs)) /\
   (clos_letop_let_op_sing (clos_Tick t x) =
      clos_Tick t (clos_letop_let_op_sing x)) /\
   (clos_letop_let_op_sing (clos_Call t ticks dest xs) =
      clos_Call t ticks dest (clos_letop_let_op_list xs)) /\
   (clos_letop_let_op_sing (clos_App t loc_opt x1 xs) =
      clos_App t loc_opt (clos_letop_let_op_sing x1)
               (clos_letop_let_op_list xs)) /\
   (clos_letop_let_op_sing (clos_Letrec nms loc_opt vs fns x1) =
      let new_fns = let_op_let fns in
      clos_Letrec nms loc_opt vs new_fns (clos_letop_let_op_sing x1)) /\
   (clos_letop_let_op_sing (Fn nm loc_opt vs num_args x1) =
      Fn nm loc_opt vs num_args (clos_letop_let_op_sing x1)) /\
   (clos_letop_let_op_list [] = []) /\
   (clos_letop_let_op_list (CONS (x:clos_exp) xs) =
      CONS (clos_letop_let_op_sing x) (clos_letop_let_op_list xs)) /\
   (let_op_let [] = []) /\
   (let_op_let (CONS (num_args,x:clos_exp) rest) =
      CONS (num_args, clos_letop_let_op_sing x) (let_op_let rest))`;;

let clos_letop_let_op_sing_ind = cake_ind "clos_letop_let_op_sing";;

(* HOL4: let_op_sing_eq *)

let clos_letop_let_op_sing_eq = prove
 (CASE_TERM
  `(!e. clos_letop_let_op [e] = [clos_letop_let_op_sing e]) /\
   (!es. clos_letop_let_op es = clos_letop_let_op_list es) /\
   (!fns.
      let_op_let fns =
      MAP (\p. match p with
                 (num_args,x) -> (num_args, HD (clos_letop_let_op [x])))
          fns)`,
  MATCH_MP_TAC clos_letop_let_op_sing_ind THEN
  RW[clos_letop_let_op_def; clos_letop_let_op_sing_def] THEN
  TRY (FS[] THEN NO_TAC) THEN
  TRY (CASES_ON `xs:clos_exp list` THEN
       FS[clos_letop_let_op_def; clos_letop_let_op_sing_def] THEN NO_TAC) THEN
  REPEAT (TOP_CASE_TAC THEN GVS[]));;

(* HOL4: compile_inc *)

let clos_letop_compile_inc_def = cake_def
  `clos_letop_compile_inc (e,xs:A) = (clos_letop_let_op e, []:B list)`;;
