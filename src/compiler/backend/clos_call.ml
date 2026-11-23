(* ========================================================================= *)
(* clos_call: port of HOL4 compiler/backend/clos_callScript.sml (CakeML      *)
(* v3479).                                                                   *)
(* This compiler phase moves code from closures into a separate code table  *)
(* and tries to change calls to known closures into fast C-style function   *)
(* calls.                                                                    *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The constructors of db_var_set are db_vars_Empty, db_vars_Var,          *)
(*   db_vars_Shift, db_vars_Union; HOL4 t SECTION n (an overload of          *)
(*   backend_common mk_cons) is mk_cons t n; the mlstring literal of the     *)
(*   empty string is implode ""; EVERY2 is ALL2; ZIP (l1,l2) is ZIP l1 l2;   *)
(*   () is one; HOL4 isEmpty t is t = LN; exp3_size is                       *)
(*   list_size clos_exp_size and exp1_size is                                *)
(*   list_size (pair_size (\x. x) clos_exp_size).                            *)
(* - The clauses of a HOL Light definition share their variables, so a name *)
(*   used with two types gets a second name: the names of Fn and clos_Letrec *)
(*   (HOL4 t) are nm and nms.                                                *)
(* - HOL4's paired lambdas (\(n,x). t) are written                           *)
(*   (\p. match p with (n,x) -> t).                                          *)
(* - The definitions are made with sem1aux_def_wf (semantics/sem1aux_tfl.ml);*)
(*   where HOL4's termination is automatic, the relation is its size measure.*)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/db_vars.ml";;
needs "semantics/sem1aux_tfl.ml";;
needs "compiler/backend/il1aux_mutual.ml";;

type_invention_error := true;;

(* HOL4: free *)

let clos_call_free_def = sem1aux_def_wf
  `MEASURE (\es:clos_exp list. list_size clos_exp_size es)`
  SEM1AUX_TC_TAC
  `(clos_call_free [] = ([],db_vars_Empty)) /\
   (clos_call_free (CONS (x:clos_exp) (CONS y xs)) =
      let (c1,l1) = clos_call_free [x] in
      let (c2,l2) = clos_call_free (CONS y xs) in
        (APPEND c1 c2, mk_Union l1 l2)) /\
   (clos_call_free [clos_Var t v] = ([clos_Var t v], db_vars_Var v)) /\
   (clos_call_free [clos_If t x1 x2 x3] =
      let (c1,l1) = clos_call_free [x1] in
      let (c2,l2) = clos_call_free [x2] in
      let (c3,l3) = clos_call_free [x3] in
        ([clos_If t (HD c1) (HD c2) (HD c3)], mk_Union l1 (mk_Union l2 l3))) /\
   (clos_call_free [clos_Let t xs x2] =
      let (c1,l1) = clos_call_free xs in
      let (c2,l2) = clos_call_free [x2] in
        ([clos_Let t c1 (HD c2)],
         mk_Union l1 (db_vars_Shift (LENGTH xs) l2))) /\
   (clos_call_free [clos_Raise t x1] =
      let (c1,l1) = clos_call_free [x1] in
        ([clos_Raise t (HD c1)], l1)) /\
   (clos_call_free [clos_Tick t x1] =
      let (c1,l1) = clos_call_free [x1] in
        ([clos_Tick t (HD c1)], l1)) /\
   (clos_call_free [clos_Op t op xs] =
      let (c1,l1) = clos_call_free xs in
        ([clos_Op t op c1], l1)) /\
   (clos_call_free [clos_App t loc_opt x1 xs2] =
      let (c1,l1) = clos_call_free [x1] in
      let (c2,l2) = clos_call_free xs2 in
        ([clos_App t loc_opt (HD c1) c2], mk_Union l1 l2)) /\
   (clos_call_free [Fn nm loc _ num_args x1] =
      let (c1,l1) = clos_call_free [x1] in
      let l2 = db_vars_Shift num_args l1 in
        ([Fn nm loc (SOME (vars_to_list l2)) num_args (HD c1)], l2)) /\
   (clos_call_free [clos_Letrec nms loc _ fns x1] =
      let m = LENGTH fns in
      let res = MAP (\p. match p with
                           (n,x) ->
                             let (c,l) = clos_call_free [x] in
                               ((n, HD c), db_vars_Shift (n + m) l)) fns in
      let c1 = MAP FST res in
      let l1 = list_mk_Union (MAP SND res) in
      let (c2,l2) = clos_call_free [x1] in
        ([clos_Letrec nms loc (SOME (vars_to_list l1)) c1 (HD c2)],
         mk_Union l1 (db_vars_Shift (LENGTH fns) l2))) /\
   (clos_call_free [clos_Handle t x1 x2] =
      let (c1,l1) = clos_call_free [x1] in
      let (c2,l2) = clos_call_free [x2] in
        ([clos_Handle t (HD c1) (HD c2)], mk_Union l1 (db_vars_Shift 1 l2))) /\
   (clos_call_free [clos_Call t ticks dest xs] =
      let (c1,l1) = clos_call_free xs in
        ([clos_Call t ticks dest c1], l1))`;;

let clos_call_free_ind = cake_ind "clos_call_free";;

let free_sing_def = sem1aux_def_wf
  `MEASURE (\x:clos_exp + clos_exp list.
              sum_CASE x clos_exp_size (list_size clos_exp_size))`
  SEM1AUX_TC_TAC
  `(free_sing (clos_Var t v) = (clos_Var t v, db_vars_Var v)) /\
   (free_sing (clos_If t x1 x2 x3) =
      let (c1,l1) = free_sing x1 in
      let (c2,l2) = free_sing x2 in
      let (c3,l3) = free_sing x3 in
        (clos_If t c1 c2 c3, mk_Union l1 (mk_Union l2 l3))) /\
   (free_sing (clos_Let t xs x2) =
      let (c1,l1) = free_list xs in
      let (c2,l2) = free_sing x2 in
        (clos_Let t c1 c2, mk_Union l1 (db_vars_Shift (LENGTH xs) l2))) /\
   (free_sing (clos_Raise t x1) =
      let (c1,l1) = free_sing x1 in (clos_Raise t c1, l1)) /\
   (free_sing (clos_Tick t x1) =
      let (c1,l1) = free_sing x1 in (clos_Tick t c1, l1)) /\
   (free_sing (clos_Op t op xs) =
      let (c1,l1) = free_list xs in (clos_Op t op c1, l1)) /\
   (free_sing (clos_App t loc_opt x1 xs2) =
      let (c1,l1) = free_sing x1 in
      let (c2,l2) = free_list xs2 in
        (clos_App t loc_opt c1 c2, mk_Union l1 l2)) /\
   (free_sing (Fn nm loc _ num_args x1) =
      let (c1,l1) = free_sing x1 in
      let l2 = db_vars_Shift num_args l1 in
        (Fn nm loc (SOME (vars_to_list l2)) num_args c1, l2)) /\
   (free_sing (clos_Letrec nms loc _ fns x1) =
      let m = LENGTH fns in
      let res = MAP (\p. match p with
                           (n,x) ->
                             let (c,l) = free_sing x in
                               ((n,c), db_vars_Shift (n + m) l)) fns in
      let c1 = MAP FST res in
      let l1 = list_mk_Union (MAP SND res) in
      let (c2,l2) = free_sing x1 in
        (clos_Letrec nms loc (SOME (vars_to_list l1)) c1 c2,
         mk_Union l1 (db_vars_Shift (LENGTH fns) l2))) /\
   (free_sing (clos_Handle t x1 x2) =
      let (c1,l1) = free_sing x1 in
      let (c2,l2) = free_sing x2 in
        (clos_Handle t c1 c2, mk_Union l1 (db_vars_Shift 1 l2))) /\
   (free_sing (clos_Call t ticks dest xs) =
      let (c1,l1) = free_list xs in (clos_Call t ticks dest c1, l1)) /\
   (free_list [] = ([],db_vars_Empty)) /\
   (free_list (CONS (x:clos_exp) xs) =
      let (c1,l1) = free_sing x in
      let (c2,l2) = free_list xs in
        (CONS c1 c2, mk_Union l1 l2))`;;

let free_sing_ind = cake_ind "free_sing";;
let IL1AUX_FREE_MAP = prove
 (CASE_TERM
  `!fns. (!n x. MEM (n,x) fns ==>
                clos_call_free [x] = (match free_sing x with (e,vs) -> ([e],vs)))
         ==> !m. MAP (\p. match p with
                            (n,x) -> (match clos_call_free [x] with
                                        (c,l) -> ((n,HD c), db_vars_Shift (n + m) l)))
                     fns =
                 MAP (\p. match p with
                            (n,x) -> (match free_sing x with
                                        (c,l) -> ((n,c), db_vars_Shift (n + m) l)))
                     fns`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM; CONS_11] THEN
  DISCH_TAC THEN X_GEN_TAC `m:num` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `?a b. h = (a:num,b:clos_exp)` STRIP_ASSUME_TAC THENL
     [MESON_TAC[PAIR]; ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`a:num`; `b:clos_exp`]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `?e0 vs0. free_sing b = (e0,vs0)` STRIP_ASSUME_TAC THENL
     [MESON_TAC[PAIR]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SIMP[HD];
    FIRST_X_ASSUM (MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN (fun th -> REWRITE_TAC[th])]]);;

let free_sing_eq = prove
 (CASE_TERM
  `(!e. clos_call_free [e] =
        (\p. match p with (e,vs) -> ([e],vs)) (free_sing e)) /\
   (!es. clos_call_free es = free_list es)`,
  MATCH_MP_TAC free_sing_ind THEN RW[clos_call_free_def; free_sing_def] THEN
  REPEAT (PAIRARG_TAC THEN GVS[]) THEN
  TRY (FIRST_X_ASSUM (fun th -> REWRITE_TAC[MATCH_MP IL1AUX_FREE_MAP th]) THEN
       NO_TAC) THEN
  CASES_ON `xs:clos_exp list` THEN
  GVS[clos_call_free_def; free_sing_def; mk_Union_Empty; APPEND]);;

(* HOL4's free_LENGTH_LEMMA (an ML binding) is folded into free_LENGTH *)

let free_LENGTH = prove
 (`!xs ys l. clos_call_free xs = (ys,l) ==> LENGTH ys = LENGTH xs`,
  REWRITE_TAC[free_sing_eq] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[free_sing_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  REPEAT PAIRARG_TAC THEN GVS[LENGTH] THEN RES_TAC);;

let free_SING = prove
 (`!x ys l. clos_call_free [x] = (ys,l) ==> ?y. ys = [y]`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC free_LENGTH THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`ys:clos_exp list`,`ys:clos_exp list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

let LENGTH_FST_free = prove
 (`!fns. LENGTH (FST (clos_call_free fns)) = LENGTH fns`,
  GEN_TAC THEN MP_TAC (ISPEC `clos_call_free fns` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FST] THEN IMP_RES_TAC free_LENGTH THEN
  ASM_REWRITE_TAC[]);;

let HD_FST_free = prove
 (`!x1. [HD (FST (clos_call_free [x1]))] = FST (clos_call_free [x1])`,
  GEN_TAC THEN MP_TAC (ISPEC `clos_call_free [x1]` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FST] THEN IMP_RES_TAC free_SING THEN
  ASM_REWRITE_TAC[HD]);;

let free_CONS = prove
 (`!x xs. FST (clos_call_free (CONS x xs)) =
          CONS (HD (FST (clos_call_free [x]))) (FST (clos_call_free xs))`,
  REWRITE_TAC[free_sing_eq] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[free_sing_def] THEN REPEAT PAIRARG_TAC THEN SIMP[HD]);;

(* HOL4: closed *)

let clos_call_closed_def = cake_def
  `clos_call_closed x <=> db_to_set (SND (clos_call_free [x])) = LN`;;

let closed_eq = prove
 (`!x. clos_call_closed x <=> db_to_set (SND (free_sing x)) = LN`,
  REWRITE_TAC[clos_call_closed_def; free_sing_eq] THEN GEN_TAC THEN
  PAIRARG_TAC THEN SIMP[]);;

(* HOL4: EL_MEM_LEMMA *)

let clos_call_EL_MEM_LEMMA = prove
 (`!xs i (x:A). i < LENGTH xs /\ x = EL i xs ==> MEM x xs`,
  MESON_TAC[MEM_EL]);;

let insert_each_def = cake_def_wf
  `MEASURE (\x:num # num # (num_set # A). FST (SND x))` TERM_TAC
  `(insert_each p 0 (g:num_set # A) = g) /\
   (insert_each p (SUC n) (g1,g2) = insert_each (p + 2) n (insert p one g1,g2))`;;

let insert_each_ind = cake_ind "insert_each";;

(* HOL4 writes loc+2n: the numeral 2 of type num *)

let clos_call_code_list_def = cake_def
  `(clos_call_code_list loc [] (g:B # (num # num # A) list) = g) /\
   (clos_call_code_list loc (CONS (n,p) xs) (g1,g2) =
      clos_call_code_list (loc + 2) xs (g1,CONS (loc + 1,n,p) g2))`;;

let clos_call_code_list_ind = cake_ind "clos_call_code_list";;

let GENLIST_Var_def = cake_def
  `GENLIST_Var t (i:num) n =
     if n = 0 then [] else
       APPEND (GENLIST_Var t (i + 1) (n - 1:num)) [clos_Var t (n - 1)]`;;

let calls_list_def = cake_def
  `(calls_list t (i:num) loc ([]:(num # A) list) = []) /\
   (calls_list t i loc (CONS (n,_) xs) =
      CONS (n,clos_Call t 0 (loc + 1) (GENLIST_Var t 1 n))
           (calls_list t (i + 1) (loc + 2) xs))`;;

let exp3_size_MAP_SND = prove
 (`!fns. list_size clos_exp_size (MAP SND fns) <=
         list_size (pair_size (\x:num. x) clos_exp_size) fns`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; list_size; pair_size; LE_REFL] THEN
  ASM_ARITH_TAC);;

(* termination of calls, calls_sing: as HOL4, with the size of MAP SND fns *)
(* (list_size_pair_size_MAP_FST_SND of misc)                               *)

let IL1AUX_CLOS_TC_TAC : tactic =
  SEM1AUX_TC_TAC ORELSE
  (REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
   RVEQ_TAC THEN
   REPEAT (FIRST_X_ASSUM (K ALL_TAC o check (fun th ->
     is_neg (concl th) && is_exists (dest_neg (concl th))))) THEN
   REWRITE_TAC(WF_REL_THMS @ [sum_CASE; FST; SND; list_size;
                              type_size_def "clos_exp"] @
               size_aux_eqs "clos_exp") THEN
   REWRITE_TAC[list_size_pair_size_MAP_FST_SND] THEN ARITH_TAC);;

let clos_call_calls_def = sem1aux_def_wf
  `MEASURE (\p:clos_exp list # (num_set # (num # num # clos_exp) list).
              list_size clos_exp_size (FST p))`
  IL1AUX_CLOS_TC_TAC
  `(clos_call_calls [] g = ([],g)) /\
   (clos_call_calls (CONS (x:clos_exp) (CONS y xs)) g =
      let (e1,g) = clos_call_calls [x] g in
      let (e2,g) = clos_call_calls (CONS y xs) g in
        (APPEND e1 e2,g)) /\
   (clos_call_calls [clos_Var t v] g = ([clos_Var t v],g)) /\
   (clos_call_calls [clos_If t x1 x2 x3] g =
      let (e1,g) = clos_call_calls [x1] g in
      let (e2,g) = clos_call_calls [x2] g in
      let (e3,g) = clos_call_calls [x3] g in
      let e1 = HD e1 in
      let e2 = HD e2 in
      let e3 = HD e3 in
        ([clos_If t e1 e2 e3],g)) /\
   (clos_call_calls [clos_Let t xs x2] g =
      let (e1,g) = clos_call_calls xs g in
      let (e2,g) = clos_call_calls [x2] g in
      let e2 = HD e2 in
        ([clos_Let t e1 e2],g)) /\
   (clos_call_calls [clos_Raise t x1] g =
      let (e1,g) = clos_call_calls [x1] g in
      let e1 = HD e1 in
        ([clos_Raise t e1],g)) /\
   (clos_call_calls [clos_Tick t x1] g =
      let (e1,g) = clos_call_calls [x1] g in
      let e1 = HD e1 in
        ([clos_Tick t e1],g)) /\
   (clos_call_calls [clos_Handle t x1 x2] g =
      let (e1,g) = clos_call_calls [x1] g in
      let (e2,g) = clos_call_calls [x2] g in
      let e1 = HD e1 in
      let e2 = HD e2 in
        ([clos_Handle t e1 e2],g)) /\
   (clos_call_calls [clos_Call t ticks dest xs] g =
      let (xs,g) = clos_call_calls xs g in
        ([clos_Call t ticks dest xs],g)) /\
   (clos_call_calls [clos_Op t op xs] g =
      let (e1,g) = clos_call_calls xs g in
        ([clos_Op t op e1],g)) /\
   (clos_call_calls [clos_App t loc_opt x xs] g =
      let (es,g) = clos_call_calls xs g in
      let (e1,g) = clos_call_calls [x] g in
      let e1 = HD e1 in
      let loc = (match loc_opt with SOME loc -> loc | NONE -> 0) in
        if IS_SOME loc_opt /\ IS_SOME (lookup loc (FST g)) then
          (if pure x then ([clos_Call t (LENGTH es) (loc + 1) es],g) else
             ([clos_Let (mk_cons t 0) (SNOC e1 es)
                 (clos_Call (mk_cons t 1) (LENGTH es) (loc + 1)
                    (GENLIST_Var backend_common_None 2 (LENGTH es)))],g))
        else ([clos_App t loc_opt e1 es],g)) /\
   (clos_call_calls [Fn nm loc_opt ws num_args x1] g =
      let loc = (match loc_opt with SOME loc -> loc | NONE -> 0) in
      let new_g = insert_each loc 1 g in
      let (e1,new_g) = clos_call_calls [x1] new_g in
      let new_g = (FST new_g,CONS (loc + 1,num_args,HD e1) (SND new_g)) in
        if clos_call_closed (Fn nm loc_opt ws num_args (HD e1)) then
          ([Fn nm loc_opt ws num_args
              (clos_Call backend_common_None 0 (loc + 1)
                 (GENLIST_Var backend_common_None 1 num_args))],new_g)
        else
          let (e1,g) = clos_call_calls [x1] g in
            ([Fn nm loc_opt ws num_args (HD e1)],g)) /\
   (clos_call_calls [clos_Letrec nms loc_opt ws fns x1] g =
      let loc = (match loc_opt with SOME loc -> loc | NONE -> 0) in
      let new_g = insert_each loc (LENGTH fns) g in
      let (fns1,new_g) = clos_call_calls (MAP SND fns) new_g in
        if ALL2 (\np p. match np with
                          (n,_) -> clos_call_closed (Fn (implode "") NONE NONE n p))
                fns fns1 then
          let new_g = clos_call_code_list loc (ZIP (MAP FST fns) fns1) new_g in
          let (e1,g) = clos_call_calls [x1] new_g in
            ([clos_Letrec nms loc_opt ws (calls_list backend_common_None 1 loc fns)
                (HD e1)],g)
        else
          let (fns1,g) = clos_call_calls (MAP SND fns) g in
          let (e1,g) = clos_call_calls [x1] g in
            ([clos_Letrec nms loc_opt ws (ZIP (MAP FST fns) fns1) (HD e1)],g))`;;

let clos_call_calls_ind = cake_ind "clos_call_calls";;

let calls_sing_def = sem1aux_def_wf
  `MEASURE
     (\x:(clos_exp # (num_set # (num # num # clos_exp) list)) +
         (clos_exp list # (num_set # (num # num # clos_exp) list)).
        sum_CASE x (\p. clos_exp_size (FST p))
                   (\p. list_size clos_exp_size (FST p)))`
  IL1AUX_CLOS_TC_TAC
  `(calls_sing (clos_Var t v) g = (clos_Var t v,g)) /\
   (calls_sing (clos_If t x1 x2 x3) g =
      let (e1,g) = calls_sing x1 g in
      let (e2,g) = calls_sing x2 g in
      let (e3,g) = calls_sing x3 g in
        (clos_If t e1 e2 e3,g)) /\
   (calls_sing (clos_Let t xs x2) g =
      let (e1,g) = calls_sing_list xs g in
      let (e2,g) = calls_sing x2 g in
        (clos_Let t e1 e2,g)) /\
   (calls_sing (clos_Raise t x1) g =
      let (e1,g) = calls_sing x1 g in
        (clos_Raise t e1,g)) /\
   (calls_sing (clos_Tick t x1) g =
      let (e1,g) = calls_sing x1 g in
        (clos_Tick t e1,g)) /\
   (calls_sing (clos_Handle t x1 x2) g =
      let (e1,g) = calls_sing x1 g in
      let (e2,g) = calls_sing x2 g in
        (clos_Handle t e1 e2,g)) /\
   (calls_sing (clos_Call t ticks dest xs) g =
      let (xs,g) = calls_sing_list xs g in
        (clos_Call t ticks dest xs,g)) /\
   (calls_sing (clos_Op t op xs) g =
      let (e1,g) = calls_sing_list xs g in
        (clos_Op t op e1,g)) /\
   (calls_sing (clos_App t loc_opt x xs) g =
      let (es,g) = calls_sing_list xs g in
      let (e1,g) = calls_sing x g in
      let loc = (match loc_opt with SOME loc -> loc | NONE -> 0) in
        if IS_SOME loc_opt /\ IS_SOME (lookup loc (FST g)) then
          (if pure x then (clos_Call t (LENGTH es) (loc + 1) es,g) else
             (clos_Let (mk_cons t 0) (SNOC e1 es)
                (clos_Call (mk_cons t 1) (LENGTH es) (loc + 1)
                   (GENLIST_Var backend_common_None 2 (LENGTH es))),g))
        else (clos_App t loc_opt e1 es,g)) /\
   (calls_sing (Fn nm loc_opt ws num_args x1) g =
      let loc = (match loc_opt with SOME loc -> loc | NONE -> 0) in
      let new_g = insert_each loc 1 g in
      let (e1,new_g) = calls_sing x1 new_g in
      let new_g = (FST new_g,CONS (loc + 1,num_args,e1) (SND new_g)) in
        if clos_call_closed (Fn nm loc_opt ws num_args e1) then
          (Fn nm loc_opt ws num_args
             (clos_Call backend_common_None 0 (loc + 1)
                (GENLIST_Var backend_common_None 1 num_args)),new_g)
        else
          let (e1,g) = calls_sing x1 g in
            (Fn nm loc_opt ws num_args e1,g)) /\
   (calls_sing (clos_Letrec nms loc_opt ws fns x1) g =
      let loc = (match loc_opt with SOME loc -> loc | NONE -> 0) in
      let new_g = insert_each loc (LENGTH fns) g in
      let (fns1,new_g) = calls_sing_list (MAP SND fns) new_g in
        if ALL2 (\np p. match np with
                          (n,_) -> clos_call_closed (Fn (implode "") NONE NONE n p))
                fns fns1 then
          let new_g = clos_call_code_list loc (ZIP (MAP FST fns) fns1) new_g in
          let (e1,g) = calls_sing x1 new_g in
            (clos_Letrec nms loc_opt ws (calls_list backend_common_None 1 loc fns)
               e1,g)
        else
          let (fns1,g) = calls_sing_list (MAP SND fns) g in
          let (e1,g) = calls_sing x1 g in
            (clos_Letrec nms loc_opt ws (ZIP (MAP FST fns) fns1) e1,g)) /\
   (calls_sing_list [] g = ([],g)) /\
   (calls_sing_list (CONS (x:clos_exp) xs) g =
      let (e1,g) = calls_sing x g in
      let (e2,g) = calls_sing_list xs g in
        (CONS e1 e2,g))`;;

let calls_sing_ind = cake_ind "calls_sing";;


let calls_sing_eq = prove
 (CASE_TERM
  `(!e g. clos_call_calls [e] g =
          (\p. match p with (e,rest) -> ([e],rest)) (calls_sing e g)) /\
   (!es g. clos_call_calls es g = calls_sing_list es g)`,
  MATCH_MP_TAC calls_sing_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN RW[clos_call_calls_def; calls_sing_def] THEN
  REPEAT (IL1AUX_PAIRARG_TAC THEN GVS[]) THEN REPEAT (TOP_CASE_TAC THEN GVS[]) THEN
  TRY (RES_TAC THEN GVS[HD] THEN NO_TAC) THEN
  CASES_ON `xs:clos_exp list` THEN GVS[clos_call_calls_def; APPEND]);;

(* HOL4: compile *)

let clos_call_compile_def = cake_def
  `(clos_call_compile F x = (x,(LN:num_set,[]:(num # num # clos_exp) list))) /\
   (clos_call_compile T x = let (xs,g) = clos_call_calls x (LN,[]) in (xs,g))`;;

(* HOL4: compile_inc *)

let clos_call_compile_inc_def = cake_def
  `clos_call_compile_inc d (e,xs:A) =
     let (ea,d1,new_code) = clos_call_calls e (d,[]) in (d1,ea,new_code)`;;

(* HOL4: compile_eq *)

let clos_call_compile_eq = prove
 (CASE_TERM
  `!x. clos_call_compile F x = (x,(LN,[])) /\
       clos_call_compile T x = let (xs,g) = calls_sing_list x (LN,[]) in (xs,g)`,
  REWRITE_TAC[clos_call_compile_def; calls_sing_eq]);;

(* HOL4: compile_inc_eq *)

let clos_call_compile_inc_eq = prove
 (CASE_TERM
  `!d e xs:A.
     clos_call_compile_inc d (e,xs) =
     let (ea,d1,new_code) = calls_sing_list e (d,[]) in (d1,ea,new_code)`,
  REWRITE_TAC[clos_call_compile_inc_def; calls_sing_eq]);;

let cond_call_compile_inc_def = cake_def
  `cond_call_compile_inc do_it =
     if do_it
     then (clos_call_compile_inc:
             num_set -> clos_exp list # (num # num # clos_exp) list ->
             num_set # clos_exp list # (num # num # clos_exp) list)
     else CURRY I`;;

let calls_length = prove
 (`!xs g0 ys g. clos_call_calls xs g0 = (ys,g) ==> LENGTH ys = LENGTH xs`,
  REWRITE_TAC[calls_sing_eq] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[calls_sing_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  REPEAT (IL1AUX_PAIRARG_TAC THEN GVS[LENGTH]) THEN GVS[LENGTH] THEN
  RES_TAC THEN ASM_REWRITE_TAC[]);;

let calls_sing = prove
 (`!x g0 ys g. clos_call_calls [x] g0 = (ys,g) ==> ?y. ys = [y]`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC calls_length THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`ys:clos_exp list`,`ys:clos_exp list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

(* HOL4: compile_LENGTH *)

let clos_call_compile_LENGTH = prove
 (`!x y a b. clos_call_compile x y = (a,b) ==> LENGTH y = LENGTH a`,
  GEN_TAC THEN CASES_ON `x:bool` THEN REWRITE_TAC[clos_call_compile_def] THEN
  REPEAT GEN_TAC THEN TRY (IL1AUX_PAIRARG_TAC) THEN REWRITE_TAC[PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[] THEN
  IMP_RES_TAC calls_length THEN ASM_REWRITE_TAC[]);;

(* HOL4: compile_nil *)

let clos_call_compile_nil = prove
 (`!x a g b. clos_call_compile x [] = (a,g,b) ==> a = [] /\ g = LN /\ b = []`,
  GEN_TAC THEN CASES_ON `x:bool` THEN
  REWRITE_TAC[clos_call_compile_def; clos_call_calls_def] THEN
  SIMP[PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4: selftest (an EVAL test of compile) is not ported *)
