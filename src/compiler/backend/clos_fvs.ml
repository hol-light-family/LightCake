(* ========================================================================= *)
(* clos_fvs: port of HOL4 compiler/backend/clos_fvsScript.sml (CakeML v3479).*)
(* Replaces free variables with constant type errors.                        *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The clauses of a HOL Light definition share their variables, so a name *)
(*   used with two types gets a second name: the names of clos_Letrec and Fn *)
(*   (HOL4 t) are nms and nm, and the list of remove_fvs_let is rest.        *)
(* - HOL4's paired lambdas (\(num_args,x). t) are written                    *)
(*   (\p. match p with (num_args,x) -> t).                                   *)
(* - The definitions are made with sem1aux_def_wf (semantics/sem1aux_tfl.ml) *)
(*   and, for the three mutually recursive functions, il1aux_def_wf          *)
(*   (compiler/backend/il1aux_mutual.ml), which also gives their induction  *)
(*   theorem.                                                                *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/closLang.ml";;
needs "semantics/sem1aux_tfl.ml";;
needs "compiler/backend/il1aux_mutual.ml";;

type_invention_error := true;;

(* termination: HOL4's automatic proof, by the size of the expression list *)

let remove_fvs_def = sem1aux_def_wf
  `measure (\p:num # clos_exp list. list_size clos_exp_size (SND p))`
  SEM1AUX_TC_TAC
  `(remove_fvs fvs [] = []) /\
   (remove_fvs fvs (CONS (x:clos_exp) (CONS y xs)) =
      CONS (HD (remove_fvs fvs [x])) (remove_fvs fvs (CONS y xs))) /\
   (remove_fvs fvs [clos_Var t v] =
      if v < fvs then [clos_Var t v]
      else [clos_Op t (MemOp clos_El) []]) /\
   (remove_fvs fvs [clos_If t x1 x2 x3] =
      [clos_If t (HD (remove_fvs fvs [x1]))
                 (HD (remove_fvs fvs [x2]))
                 (HD (remove_fvs fvs [x3]))]) /\
   (remove_fvs fvs [clos_Let t xs x2] =
      let xs = remove_fvs fvs xs in
      let n = LENGTH xs in
      let x2 = HD (remove_fvs (fvs + n) [x2]) in
        [clos_Let t xs x2]) /\
   (remove_fvs fvs [clos_Raise t x1] =
      [clos_Raise t (HD (remove_fvs fvs [x1]))]) /\
   (remove_fvs fvs [clos_Handle t x1 x2] =
      [clos_Handle t (HD (remove_fvs fvs [x1]))
                     (HD (remove_fvs (fvs + 1) [x2]))]) /\
   (remove_fvs fvs [clos_Op t op xs] =
      [clos_Op t op (remove_fvs fvs xs)]) /\
   (remove_fvs fvs [clos_Tick t x] = [clos_Tick t (HD (remove_fvs fvs [x]))]) /\
   (remove_fvs fvs [clos_Call t ticks dest xs] =
      [clos_Call t ticks dest (remove_fvs fvs xs)]) /\
   (remove_fvs fvs [clos_App t loc_opt x1 xs] =
      [clos_App t loc_opt (HD (remove_fvs fvs [x1])) (remove_fvs fvs xs)]) /\
   (remove_fvs fvs [clos_Letrec nms loc_opt vs fns x1] =
      let m = LENGTH fns in
      let new_fvs = (match vs with NONE -> fvs | SOME x -> LENGTH x) in
      let new_fns =
        MAP (\p. match p with
                   (num_args,x) ->
                     (num_args, HD (remove_fvs (num_args + m + new_fvs) [x])))
            fns in
      [clos_Letrec nms loc_opt vs new_fns (HD (remove_fvs (m + fvs) [x1]))]) /\
   (remove_fvs fvs [Fn nm loc_opt vs num_args x1] =
      let fvs = (match vs with NONE -> fvs | SOME x -> LENGTH x) in
      [Fn nm loc_opt vs num_args (HD (remove_fvs (num_args + fvs) [x1]))])`;;

let remove_fvs_ind = cake_ind "remove_fvs";;

let remove_fvs_sing_def = il1aux_def_wf
  `measure
     (\x:(num # clos_exp) + (num # clos_exp list) +
         (num # num # (num # clos_exp) list).
        sum_CASE x (\p. clos_exp_size (SND p))
          (\y. sum_CASE y (\p. list_size clos_exp_size (SND p))
                 (\p. list_size (pair_size (\x. x) clos_exp_size)
                        (SND (SND p)))))`
  SEM1AUX_TC_TAC
  `(remove_fvs_sing fvs (clos_Var t v) =
      if v < fvs then clos_Var t v
      else clos_Op t (MemOp clos_El) []) /\
   (remove_fvs_sing fvs (clos_If t x1 x2 x3) =
      clos_If t (remove_fvs_sing fvs x1)
                (remove_fvs_sing fvs x2)
                (remove_fvs_sing fvs x3)) /\
   (remove_fvs_sing fvs (clos_Let t xs x2) =
      let xs = remove_fvs_list fvs xs in
      let n = LENGTH xs in
      let x2 = remove_fvs_sing (fvs + n) x2 in
        clos_Let t xs x2) /\
   (remove_fvs_sing fvs (clos_Raise t x1) =
      clos_Raise t (remove_fvs_sing fvs x1)) /\
   (remove_fvs_sing fvs (clos_Handle t x1 x2) =
      clos_Handle t (remove_fvs_sing fvs x1)
                    (remove_fvs_sing (fvs + 1) x2)) /\
   (remove_fvs_sing fvs (clos_Op t op xs) =
      clos_Op t op (remove_fvs_list fvs xs)) /\
   (remove_fvs_sing fvs (clos_Tick t x) = clos_Tick t (remove_fvs_sing fvs x)) /\
   (remove_fvs_sing fvs (clos_Call t ticks dest xs) =
      clos_Call t ticks dest (remove_fvs_list fvs xs)) /\
   (remove_fvs_sing fvs (clos_App t loc_opt x1 xs) =
      clos_App t loc_opt (remove_fvs_sing fvs x1) (remove_fvs_list fvs xs)) /\
   (remove_fvs_sing fvs (clos_Letrec nms loc_opt vs fns x1) =
      let m = LENGTH fns in
      let new_fvs = (match vs with NONE -> fvs | SOME x -> LENGTH x) in
      let new_fns = remove_fvs_let m new_fvs fns in
      clos_Letrec nms loc_opt vs new_fns (remove_fvs_sing (m + fvs) x1)) /\
   (remove_fvs_sing fvs (Fn nm loc_opt vs num_args x1) =
      let fvs = (match vs with NONE -> fvs | SOME x -> LENGTH x) in
      Fn nm loc_opt vs num_args (remove_fvs_sing (num_args + fvs) x1)) /\
   (remove_fvs_list fvs [] = []) /\
   (remove_fvs_list fvs (CONS (x:clos_exp) xs) =
      CONS (remove_fvs_sing fvs x) (remove_fvs_list fvs xs)) /\
   (remove_fvs_let m fvs [] = []) /\
   (remove_fvs_let m new_fvs (CONS (num_args,x) rest) =
      CONS (num_args, remove_fvs_sing (num_args + m + new_fvs) x)
           (remove_fvs_let m new_fvs rest))`;;

let remove_fvs_sing_ind = cake_ind "remove_fvs_sing";;

let remove_fvs_sing_eq = prove
 (CASE_TERM
  `(!fvs e. remove_fvs fvs [e] = [remove_fvs_sing fvs e]) /\
   (!fvs es. remove_fvs fvs es = remove_fvs_list fvs es) /\
   (!m new_fvs fns.
      remove_fvs_let m new_fvs fns =
      MAP (\p. match p with
                 (num_args,x) ->
                   (num_args, HD (remove_fvs (num_args + m + new_fvs) [x])))
          fns)`,
  MATCH_MP_TAC remove_fvs_sing_ind THEN
  RW[remove_fvs_def; remove_fvs_sing_def] THEN TRY (FS[] THEN NO_TAC) THEN
  CASES_ON `xs:clos_exp list` THEN FS[remove_fvs_def; remove_fvs_sing_def]);;

(* HOL4: compile *)

let clos_fvs_compile_def = cake_def
  `clos_fvs_compile exps = remove_fvs 0 exps`;;

(* HOL4: compile_eq *)

let clos_fvs_compile_eq = prove
 (`!exps. clos_fvs_compile exps = remove_fvs_list 0 exps`,
  REWRITE_TAC[clos_fvs_compile_def; remove_fvs_sing_eq]);;

(* HOL4: compile_inc *)

let clos_fvs_compile_inc_def = cake_def
  `clos_fvs_compile_inc (e,xs:A) = (clos_fvs_compile e, []:B list)`;;

(* HOL4: LENGTH_remove_fvs *)

let clos_fvs_LENGTH_remove_fvs = prove
 (`!fvs xs. LENGTH (remove_fvs fvs xs) = LENGTH xs`,
  MATCH_MP_TAC remove_fvs_ind THEN RW[remove_fvs_def; LENGTH]);;
