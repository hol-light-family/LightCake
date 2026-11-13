(* ========================================================================= *)
(* clos_number: port of HOL4 compiler/backend/clos_numberScript.sml (CakeML  *)
(* v3479).                                                                   *)
(* This simple compiler phase walks the program and gives each closure a    *)
(* unique numeric name.                                                      *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's paired lets let (n,x) = e in t are HOL Light's paired lets (the *)
(*   kit turns them into pair_CASE); ZIP (l1,l2) is ZIP l1 l2.               *)
(* - The clauses of a HOL Light definition share their variables, so a name *)
(*   used with two types gets a second name: the names of Fn and clos_Letrec *)
(*   (HOL4 t) are nm and nms, the arguments of clos_App (HOL4 x2) xs.        *)
(* - renumber_code_locs_list and renumber_code_locs are defined with         *)
(*   sem1aux_def_wf (semantics/sem1aux_tfl.ml).                              *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/closLang.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* add fresh code locations *)

(* the termination condition of clos_Letrec needs the size of MAP SND fns,  *)
(* as in HOL4 (list_size_pair_size_MAP_FST_SND of misc)                     *)

let renumber_code_locs_def = sem1aux_def_wf
  `inv_image (<)
     (\x:(num # clos_exp list) + (num # clos_exp).
        sum_CASE x (\p. list_size clos_exp_size (SND p))
                   (\p. clos_exp_size (SND p)))`
  (SEM1AUX_TC_TAC ORELSE
   (REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    RVEQ_TAC THEN
    REWRITE_TAC(WF_REL_THMS @ [sum_CASE; type_size_def "clos_exp"] @
                size_aux_eqs "clos_exp") THEN
    REWRITE_TAC[list_size_pair_size_MAP_FST_SND] THEN ARITH_TAC))
  `(renumber_code_locs_list n [] = (n,[])) /\
   (renumber_code_locs_list n (CONS x xs) =
      let (n,x) = renumber_code_locs n x in
      let (n,xs) = renumber_code_locs_list n xs in
      (n, CONS x xs)) /\
   (renumber_code_locs n (clos_Var t v) = (n,clos_Var t v)) /\
   (renumber_code_locs n (clos_If t x1 x2 x3) =
      let (n,x1) = renumber_code_locs n x1 in
      let (n,x2) = renumber_code_locs n x2 in
      let (n,x3) = renumber_code_locs n x3 in
        (n,clos_If t x1 x2 x3)) /\
   (renumber_code_locs n (clos_Let t xs x2) =
      let (n,xs) = renumber_code_locs_list n xs in
      let (n,x2) = renumber_code_locs n x2 in
        (n,clos_Let t xs x2)) /\
   (renumber_code_locs n (clos_Raise t x1) =
      let (n,x1) = renumber_code_locs n x1 in
        (n,clos_Raise t x1)) /\
   (renumber_code_locs n (clos_Tick t x1) =
      let (n,x1) = renumber_code_locs n x1 in
        (n,clos_Tick t x1)) /\
   (renumber_code_locs n (clos_Op t op xs) =
      let (n,xs) = renumber_code_locs_list n xs in
        (n,clos_Op t op xs)) /\
   (renumber_code_locs n (clos_App t loc_opt x1 xs) =
      let (n,x1) = renumber_code_locs n x1 in
      let (n,xs) = renumber_code_locs_list n xs in
        (n,clos_App t NONE x1 xs)) /\
   (renumber_code_locs n (Fn nm loc vs num_args x1) =
      let (n,x1) = renumber_code_locs n x1 in
        (n + 2,Fn nm (SOME n) vs num_args x1)) /\
   (renumber_code_locs n (clos_Letrec nms loc vs fns x1) =
      let (m,fns') = renumber_code_locs_list n (MAP SND fns) in
      let (n,x1) = renumber_code_locs (m + 2 * LENGTH fns') x1 in
        (n,clos_Letrec nms (SOME m) vs (ZIP (MAP FST fns) fns') x1)) /\
   (renumber_code_locs n (clos_Handle t x1 x2) =
      let (n,x1) = renumber_code_locs n x1 in
      let (n,x2) = renumber_code_locs n x2 in
        (n,clos_Handle t x1 x2)) /\
   (renumber_code_locs n (clos_Call t ticks dest xs) =
      let (n,xs) = renumber_code_locs_list n xs in
        (n,clos_Op t (IntOp clos_Add) xs))`;;

(* the last case cannot occur *)

let renumber_code_locs_ind = cake_ind "renumber_code_locs_list";;

let renumber_code_locs_length = prove
 (`(!x y. LENGTH (SND (renumber_code_locs_list x y)) = LENGTH y) /\
   (!(x:num) (y:clos_exp). T)`,
  MATCH_MP_TAC renumber_code_locs_ind THEN
  REWRITE_TAC[renumber_code_locs_def] THEN REPEAT STRIP_TAC THEN
  REPEAT PAIRARG_TAC THEN GVS[LENGTH]);;

(* HOL4: compile_inc.  Leave space in the naming for the daisy chaining of  *)
(* clos_to_bvl; embed the name of the first free slot (n) in the code (no   *)
(* code will be generated for this pure Const expression).                  *)

let clos_number_compile_inc_def = cake_def
  `clos_number_compile_inc n xs =
     let n1 = make_even (n + MAX (LENGTH xs) 1) in
     let (m,ys) = renumber_code_locs_list n1 xs in
       (m, CONS (clos_Op backend_common_None (IntOp (clos_Const (&n))) []) ys)`;;

let ignore_table_def = cake_def
  `ignore_table (f:A->B->C#D) (st:A) (code:B,aux:E) =
     let (st',code') = f st code in (st',(code',aux))`;;
