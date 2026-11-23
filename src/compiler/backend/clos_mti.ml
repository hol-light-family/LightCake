(* ========================================================================= *)
(* clos_mti: port of HOL4 compiler/backend/clos_mtiScript.sml (CakeML        *)
(* v3479).                                                                   *)
(* This compiler phase introduces multi-argument function applications and  *)
(* function closures. This phase enables subsequent compiler phases to make *)
(* use of closLang's support for true multi-argument functions. This phase  *)
(* is vital for good performance.                                            *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The clauses of a HOL Light definition share their variables, so a name *)
(*   used with two types gets a second name: in intro_multi the names of Fn  *)
(*   and clos_Letrec (HOL4 t) are nm and nms, the location of               *)
(*   clos_Letrec t (SOME loc) is l and the free variables of                 *)
(*   clos_Letrec t NONE (SOME fvs) are vs.                                   *)
(* - HOL4 exp3_size is list_size clos_exp_size; HOL4's paired lambdas are    *)
(*   written (\p. match p with (num_args,e) -> t).                           *)
(* - Definitions with overlapping clauses are made with sem1aux_def(_wf)     *)
(*   (semantics/sem1aux_tfl.ml); where HOL4's termination is automatic, the  *)
(*   relation is its size measure.                                           *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/closLang.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

let collect_args_def = sem1aux_def_wf
  `MEASURE (\p:num # num # clos_exp. clos_exp_size (SND (SND p)))`
  SEM1AUX_TC_TAC
  `(collect_args max_app num_args (Fn t NONE NONE num_args' e) =
      if num_args + num_args' <= max_app then
        collect_args max_app (num_args + num_args') e
      else
        (num_args, Fn t NONE NONE num_args' e)) /\
   (collect_args max_app num_args e = (num_args, e))`;;

let collect_args_ind = cake_ind "collect_args";;

let collect_args_size = prove
 (`!max_app num_args e num_args' e'.
     (num_args', e') = collect_args max_app num_args e ==>
     num_args' + clos_exp_size e' <= num_args + clos_exp_size e`,
  MATCH_MP_TAC collect_args_ind THEN
  RW[collect_args_def; type_size_def "clos_exp"] THEN
  FS[PAIR_EQ] THEN RES_TAC THEN ASM_ARITH_TAC);;

let collect_args_more = prove
 (`!max_app num_args e num_args' e'.
     (num_args', e') = collect_args max_app num_args e ==>
     num_args <= num_args'`,
  MATCH_MP_TAC collect_args_ind THEN RW[collect_args_def] THEN
  FS[PAIR_EQ] THEN RES_TAC THEN ASM_ARITH_TAC);;

let collect_args_zero = prove
 (`!max_app num_args e e'.
     collect_args max_app num_args e = (0, e') ==> num_args = 0`,
  MATCH_MP_TAC collect_args_ind THEN RW[collect_args_def] THEN
  FS[PAIR_EQ] THEN RES_TAC THEN ASM_ARITH_TAC);;

let collect_apps_def = sem1aux_def_wf
  `MEASURE (\p:num # clos_exp list # clos_exp. clos_exp_size (SND (SND p)))`
  SEM1AUX_TC_TAC
  `(collect_apps max_app args (clos_App tra NONE e es) =
      if LENGTH args + LENGTH es <= max_app then
        collect_apps max_app (APPEND args es) e
      else
        (args, clos_App tra NONE e es)) /\
   (collect_apps max_app args e = (args, e))`;;

let collect_apps_ind = cake_ind "collect_apps";;

let exp3_size_append = prove
 (`!es1 es2. list_size clos_exp_size (APPEND es1 es2) =
             list_size clos_exp_size es1 + list_size clos_exp_size es2`,
  REWRITE_TAC[list_size_append]);;

let collect_apps_more = prove
 (`!max_app args e args' e'.
     (args', e') = collect_apps max_app args e ==>
     LENGTH args <= LENGTH args'`,
  MATCH_MP_TAC collect_apps_ind THEN RW[collect_apps_def] THEN
  FS[PAIR_EQ; LENGTH_APPEND] THEN RES_TAC THEN ASM_ARITH_TAC);;

let collect_apps_size = prove
 (`!max_app args e args' e'.
     (args', e') = collect_apps max_app args e ==>
     list_size clos_exp_size args' + clos_exp_size e' <=
     list_size clos_exp_size args + clos_exp_size e`,
  MATCH_MP_TAC collect_apps_ind THEN
  RW[collect_apps_def; type_size_def "clos_exp"; option_size] THEN
  FS[PAIR_EQ] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`args':clos_exp list`; `e':clos_exp`]) THEN
  ASM_REWRITE_TAC[list_size_append] THEN REWRITE_TAC(size_aux_eqs "clos_exp") THEN
  ARITH_TAC);;

(* termination of intro_multi: HOL4's relation and proof steps (the size    *)
(* lemmas of collect_args and collect_apps, the size of a member of funs)   *)

let IL1AUX_MTI_TC_TAC : tactic =
  SEM1AUX_TC_TAC ORELSE
  (REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
   RVEQ_TAC THEN
   REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP collect_apps_size o SYM)) THEN
   REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP collect_args_size o SYM)) THEN
   REPEAT (FIRST_X_ASSUM (K ALL_TAC o check (fun th ->
     is_neg (concl th) && is_exists (dest_neg (concl th))))) THEN
   TERM_TAC);;

let intro_multi_def = sem1aux_def_wf
  `MEASURE (\p:num # clos_exp list. list_size clos_exp_size (SND p))`
  IL1AUX_MTI_TC_TAC
  `(intro_multi max_app [] = []) /\
   (intro_multi max_app (CONS e1 (CONS e2 es)) =
      CONS (HD (intro_multi max_app [e1]))
           (CONS (HD (intro_multi max_app [e2])) (intro_multi max_app es))) /\
   (intro_multi max_app [clos_Var t n] = [clos_Var t n]) /\
   (intro_multi max_app [clos_If t e1 e2 e3] =
      [clos_If t (HD (intro_multi max_app [e1]))
                 (HD (intro_multi max_app [e2]))
                 (HD (intro_multi max_app [e3]))]) /\
   (intro_multi max_app [clos_Let t es e] =
      [clos_Let t (intro_multi max_app es) (HD (intro_multi max_app [e]))]) /\
   (intro_multi max_app [clos_Raise t e] =
      [clos_Raise t (HD (intro_multi max_app [e]))]) /\
   (intro_multi max_app [clos_Handle t e1 e2] =
      [clos_Handle t (HD (intro_multi max_app [e1]))
                     (HD (intro_multi max_app [e2]))]) /\
   (intro_multi max_app [clos_Tick t e] =
      [clos_Tick t (HD (intro_multi max_app [e]))]) /\
   (intro_multi max_app [clos_Call t ticks n es] =
      [clos_Call t ticks n (intro_multi max_app es)]) /\
   (intro_multi max_app [clos_App t NONE e es] =
      let (es',e') = collect_apps max_app es e in
        [clos_App t NONE (HD (intro_multi max_app [e']))
                  (intro_multi max_app es')]) /\
   (intro_multi max_app [clos_App t (SOME l) e es] =
      [clos_App t (SOME l) (HD (intro_multi max_app [e]))
                (intro_multi max_app es)]) /\
   (intro_multi max_app [Fn nm NONE NONE num_args e] =
      let (num_args',e') = collect_args max_app num_args e in
        [Fn nm NONE NONE num_args' (HD (intro_multi max_app [e']))]) /\
   (intro_multi max_app [Fn nm loc fvs num_args e] =
      [Fn nm loc fvs num_args (HD (intro_multi max_app [e]))]) /\
   (intro_multi max_app [clos_Letrec nms NONE NONE funs e] =
      [clos_Letrec nms NONE NONE
         (MAP (\p. match p with
                     (num_args,e) ->
                       let (num_args',e') = collect_args max_app num_args e in
                         (num_args', HD (intro_multi max_app [e'])))
              funs)
         (HD (intro_multi max_app [e]))]) /\
   (intro_multi max_app [clos_Letrec nms (SOME l) fvs funs e] =
      [clos_Letrec nms (SOME l) fvs funs (HD (intro_multi max_app [e]))]) /\
   (intro_multi max_app [clos_Letrec nms NONE (SOME vs) funs e] =
      [clos_Letrec nms NONE (SOME vs) funs (HD (intro_multi max_app [e]))]) /\
   (intro_multi max_app [clos_Op t op es] =
      [clos_Op t op (intro_multi max_app es)])`;;

let intro_multi_ind = cake_ind "intro_multi";;

let intro_multi_length = prove
 (`!max_app es. LENGTH (intro_multi max_app es) = LENGTH es`,
  MATCH_MP_TAC intro_multi_ind THEN RW[intro_multi_def; LENGTH] THEN
  REPEAT PAIRARG_TAC THEN FS[LENGTH]);;

(* HOL4 proves this by cases on e; it is also intro_multi_length at [e] *)

let intro_multi_sing = prove
 (`!e max_app. ?e'. intro_multi max_app [e] = [e']`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPECL [`max_app:num`; `[e:clos_exp]`] intro_multi_length) THEN
  SPEC_TAC (`intro_multi max_app [e]`,`l:clos_exp list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

(* the cases of the option arguments of the goal (HOL4: Cases_on loc ...) *)

let IL1AUX_OPT_CASES_TAC : tactic = fun (asl,w as g) ->
  let vs = filter (fun v -> match dest_type(type_of v) with
                              "option",_ -> true | _ -> false
                            | exception Failure _ -> false) (frees w) in
  EVERY (map (fun v -> CASES_ON v) vs) g;;

let collect_args_idem = prove
 (`!max_app num_args e num_args' e'.
     collect_args max_app num_args e = (num_args', e') ==>
     collect_args max_app num_args' (HD (intro_multi max_app [e'])) =
     (num_args', HD (intro_multi max_app [e']))`,
  MATCH_MP_TAC collect_args_ind THEN RW[collect_args_def; intro_multi_def] THEN
  REPEAT PAIRARG_TAC THEN FS[collect_args_def; HD] THEN
  TRY (FIRST_ASSUM(ASSUME_TAC o MATCH_MP collect_args_more o SYM) THEN
       COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC THEN NO_TAC) THEN
  IL1AUX_OPT_CASES_TAC THEN RW[intro_multi_def; collect_args_def] THEN
  REPEAT PAIRARG_TAC THEN FS[collect_args_def; HD]);;

let collect_apps_idem = prove
 (`!max_app args e args' e'.
     collect_apps max_app args e = (args', e') ==>
     collect_apps max_app (intro_multi max_app args')
       (HD (intro_multi max_app [e'])) =
     (intro_multi max_app args', HD (intro_multi max_app [e']))`,
  MATCH_MP_TAC collect_apps_ind THEN RW[collect_apps_def; intro_multi_def] THEN
  REPEAT PAIRARG_TAC THEN FS[collect_apps_def; HD; intro_multi_length] THEN
  TRY (FIRST_ASSUM(ASSUME_TAC o MATCH_MP collect_apps_more o SYM) THEN
       COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC THEN NO_TAC) THEN
  IL1AUX_OPT_CASES_TAC THEN RW[intro_multi_def; collect_apps_def] THEN
  REPEAT PAIRARG_TAC THEN FS[collect_apps_def; HD]);;

(* an induction hypothesis of intro_multi_idem at [x], for HD (... [x]) *)

let IL1AUX_IM_HD = prove
 (`!max_app x.
     intro_multi max_app (intro_multi max_app [x]) = intro_multi max_app [x]
     ==> intro_multi max_app [HD (intro_multi max_app [x])] =
         intro_multi max_app [x]`,
  REPEAT GEN_TAC THEN
  X_CHOOSE_THEN `x':clos_exp` SUBST1_TAC
    (SPECL [`x:clos_exp`; `max_app:num`] intro_multi_sing) THEN
  REWRITE_TAC[HD]);;

let intro_multi_idem = prove
 (`!max_app e.
     intro_multi max_app (intro_multi max_app e) = intro_multi max_app e`,
  MATCH_MP_TAC intro_multi_ind THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC (fun th -> try MATCH_MP IL1AUX_IM_HD th with Failure _ -> th) THEN
  ASM_REWRITE_TAC[intro_multi_def] THEN
  FIRST
   [(* clos_App t NONE, Fn nm NONE NONE: collect_apps_idem, collect_args_idem *)
    PAIRARG_TAC THEN GVS[] THEN
    RULE_ASSUM_TAC (fun th -> try MATCH_MP IL1AUX_IM_HD th with Failure _ -> th) THEN
    TRY (IMP_RES_TAC collect_apps_idem) THEN
    TRY (IMP_RES_TAC collect_args_idem) THEN
    SIMP[intro_multi_def] THEN NO_TAC;
    (* clos_Letrec nms NONE NONE: the functions one by one *)
    REWRITE_TAC[CONS_11; injectivity "clos_exp"; GSYM MAP_o] THEN
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:num`; `b:clos_exp`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `?n' e''. collect_args max_app a b = (n',e'')`
      STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`a:num`; `b:clos_exp`; `n':num`;
                                   `e'':clos_exp`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN (ASSUME_TAC o MATCH_MP IL1AUX_IM_HD) THEN
    IMP_RES_TAC collect_args_idem THEN SIMP[]]);;

(* HOL4: compile *)

let clos_mti_compile_def = cake_def
  `(clos_mti_compile F max_app (exps:clos_exp list) = exps) /\
   (clos_mti_compile T max_app exps = intro_multi max_app exps)`;;

(* HOL4: compile_inc *)

let clos_mti_compile_inc_def = cake_def
  `clos_mti_compile_inc max_app (e,es:A) = (intro_multi max_app e, []:B list)`;;

let cond_mti_compile_inc_def = cake_def
  `cond_mti_compile_inc do_it max_app =
     if do_it
     then (clos_mti_compile_inc max_app:clos_exp list # B list ->
                                        clos_exp list # B list)
     else I`;;

(* HOL4: compile_nil *)

let clos_mti_compile_nil = prove
 (`!do_mti max_app. clos_mti_compile do_mti max_app [] = []`,
  GEN_TAC THEN CASES_ON `do_mti:bool` THEN
  REWRITE_TAC[clos_mti_compile_def; intro_multi_def]);;
let _ = cake_add_simps [clos_mti_compile_nil];;
