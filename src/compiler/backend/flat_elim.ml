(* ========================================================================= *)
(* flat_elim: port of HOL4 compiler/backend/flat_elimScript.sml (CakeML      *)
(* v3479).                                                                   *)
(* Implementation for flatLang dead-code elimination.                       *)
(*                                                                           *)
(* Analyses code to give a next-step function as a num_set num_map. Closes  *)
(* this next-step function to give a set of reachable globals. Removes      *)
(* unreachable globals from the code.                                        *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - EVERY is ALL, EXISTS is EX, HOL4 isEmpty t is t = LN, () is one.        *)
(* - The clauses of a HOL Light definition share their variables, so a name *)
(*   used with two types gets a second name: the names of flat_Fun and       *)
(*   flat_Letrec (HOL4 t) are nm, the arguments of flat_App in is_hidden      *)
(*   (HOL4 l) es.                                                            *)
(* - HOL4's size functions of the nested types of flatLang exp are their    *)
(*   list_size / pair_size forms (see flatLang.ml): exp6_size is             *)
(*   list_size flat_exp_size, exp3_size is                                   *)
(*   list_size (pair_size flat_pat_size flat_exp_size), exp1_size is         *)
(*   list_size (pair_size mlstring_size (pair_size mlstring_size             *)
(*   flat_exp_size)).                                                        *)
(* - Definitions with catch-all clauses or several mutually recursive       *)
(*   functions are made with sem1aux_def(_wf) (semantics/sem1aux_tfl.ml) or, *)
(*   for three or more functions, il1aux_def_wf                              *)
(*   (compiler/backend/il1aux_mutual.ml); where HOL4's termination is        *)
(*   automatic, the relation is its size measure.                            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/spt_closure.ml";;
needs "compiler/backend/flatLang.ml";;
needs "hol4/sptree.ml";;
needs "semantics/sem1aux_tfl.ml";;
needs "compiler/backend/il1aux_mutual.ml";;

type_invention_error := true;;

(* ANALYSIS FUNCTIONS *)

(* is_hidden exp = T means there is no direct execution of GlobalVarLookup.  *)
(* The clauses: raise exception, exception handler, literal, constructor,   *)
(* local var, function abstraction, function application, GlobalVarInit,    *)
(* GlobalVarLookup, if expression, SINGLE pattern match, let-expression,    *)
(* local def of mutually recursive funs.                                     *)

let is_hidden_def = sem1aux_def_wf
  `measure flat_exp_size`
  SEM1AUX_TC_TAC
  `(is_hidden (flat_Raise t e) <=> is_hidden e) /\
   (is_hidden (flat_Handle t e pes) <=> F) /\
   (is_hidden (flat_Lit t l) <=> T) /\
   (is_hidden (flat_Con t id_option es) <=> ALL is_hidden es) /\
   (is_hidden (Var_local t str) <=> T) /\
   (is_hidden (flat_Fun nm name body) <=> T) /\
   (is_hidden (flat_App t (Src Opapp) es) <=> F) /\
   (is_hidden (flat_App t (GlobalVarInit g) [e]) <=> is_hidden e) /\
   (is_hidden (flat_App t (GlobalVarLookup g) [e]) <=> F) /\
   (is_hidden (flat_If t e1 e2 e3) <=> is_hidden e1 /\ is_hidden e2 /\ is_hidden e3) /\
   (is_hidden (flat_Mat t e1 [p,e2]) <=> is_hidden e1 /\ is_hidden e2) /\
   (is_hidden (flat_Let t opt e1 e2) <=> is_hidden e1 /\ is_hidden e2) /\
   (is_hidden (flat_Letrec nm funs e) <=> is_hidden e) /\
   (is_hidden _ <=> F)`;;

let is_hidden_ind = cake_ind "is_hidden";;

let total_pat_def = sem1aux_def
  `(total_pat flat_Pany <=> T) /\
   (total_pat (flat_Pvar _) <=> T) /\
   (total_pat (flat_Pcon NONE xs) <=> total_pat_list xs) /\
   (total_pat (flat_Pas p _) <=> total_pat p) /\
   (total_pat _ <=> F) /\
   (total_pat_list [] <=> T) /\
   (total_pat_list (CONS p ps) <=> total_pat p /\ total_pat_list ps)`;;

let total_pat_ind = cake_ind "total_pat";;

(* the termination conditions of recursive calls on the expressions of a    *)
(* (pat # exp) list or (varN # varN # exp) list, MAP SND pes or              *)
(* MAP (SND o SND) funs: as HOL4, by list_size_pair_size_MAP_FST_SND (misc)  *)

let IL1AUX_FLAT_TC_TAC : tactic =
  SEM1AUX_TC_TAC ORELSE
  (REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
   RVEQ_TAC THEN
   REWRITE_TAC(WF_REL_THMS @ [sum_CASE; type_size_def "flat_exp"] @
               size_aux_eqs "flat_exp") THEN
   REWRITE_TAC[list_size_pair_size_MAP_FST_SND; MAP_o] THEN
   MEM_SIZE_TAC THEN ASM_ARITH_TAC);;

(* check if expression is pure in that it does not make any visible changes *)
(* (other than writing to globals)                                          *)

(* HOL4: is_pure *)

let flat_elim_is_pure_def = sem1aux_def_wf
  `measure flat_exp_size`
  IL1AUX_FLAT_TC_TAC
  `(flat_elim_is_pure (flat_Handle t e pes) <=> flat_elim_is_pure e) /\
   (flat_elim_is_pure (flat_Lit t l) <=> T) /\
   (flat_elim_is_pure (flat_Con t id_option es) <=>
      ALL flat_elim_is_pure es) /\
   (flat_elim_is_pure (Var_local t str) <=> T) /\
   (flat_elim_is_pure (flat_Fun nm name body) <=> T) /\
   (flat_elim_is_pure (flat_App t (GlobalVarInit g) es) <=>
      ALL flat_elim_is_pure es) /\
   (flat_elim_is_pure (flat_If t e1 e2 e3) <=>
      flat_elim_is_pure e1 /\ flat_elim_is_pure e2 /\ flat_elim_is_pure e3) /\
   (flat_elim_is_pure (flat_Mat t e1 pes) <=>
      flat_elim_is_pure e1 /\ ALL flat_elim_is_pure (MAP SND pes) /\
      EX total_pat (MAP FST pes)) /\
   (flat_elim_is_pure (flat_Let t opt e1 e2) <=>
      flat_elim_is_pure e1 /\ flat_elim_is_pure e2) /\
   (flat_elim_is_pure (flat_Letrec nm funs e) <=> flat_elim_is_pure e) /\
   (flat_elim_is_pure _ <=> F)`;;

let flat_elim_is_pure_ind = cake_ind "flat_elim_is_pure";;

let is_pure_def1 = CONV_RULE (DEPTH_CONV ETA_CONV) flat_elim_is_pure_def;;

let has_Eval_def = il1aux_def_wf
  `measure
     (\x:flat_exp + flat_exp list + (flat_pat # flat_exp) list +
         (varN # varN # flat_exp) list.
        sum_CASE x flat_exp_size
          (\y. sum_CASE y (list_size flat_exp_size)
                 (\z. sum_CASE z
                        (list_size (pair_size flat_pat_size flat_exp_size))
                        (list_size (pair_size mlstring_size
                                      (pair_size mlstring_size
                                         flat_exp_size))))))`
  SEM1AUX_TC_TAC
  `(has_Eval (flat_App t op es) <=> op = Src Eval \/ has_Eval_list es) /\
   (has_Eval (flat_Mat _ e pes) <=> has_Eval e \/ has_Eval_pats pes) /\
   (has_Eval (flat_Letrec _ funs e) <=> has_Eval e \/ has_Eval_funs funs) /\
   (has_Eval (flat_Raise _ e) <=> has_Eval e) /\
   (has_Eval (flat_Handle _ e pes) <=> has_Eval e \/ has_Eval_pats pes) /\
   (has_Eval (flat_Con _ _ es) <=> has_Eval_list es) /\
   (has_Eval (flat_Fun _ _ e) <=> has_Eval e) /\
   (has_Eval (flat_If _ e1 e2 e3) <=> has_Eval e1 \/ has_Eval e2 \/ has_Eval e3) /\
   (has_Eval (flat_Let _ _ e1 e2) <=> has_Eval e1 \/ has_Eval e2) /\
   (has_Eval _ <=> F) /\
   (has_Eval_list [] <=> F) /\
   (has_Eval_list (CONS e es) <=> has_Eval e \/ has_Eval_list es) /\
   (has_Eval_pats [] <=> F) /\
   (has_Eval_pats (CONS (p,e) pes) <=> has_Eval e \/ has_Eval_pats pes) /\
   (has_Eval_funs [] <=> F) /\
   (has_Eval_funs (CONS (_,_,e) fs) <=> has_Eval e \/ has_Eval_funs fs)`;;

let has_Eval_ind = cake_ind "has_Eval";;

let dest_GlobalVarInit_def = sem1aux_def
  `(dest_GlobalVarInit (GlobalVarInit n) = SOME n) /\
   (dest_GlobalVarInit _ = NONE)`;;

let dest_GlobalVarLookup_def = sem1aux_def
  `(dest_GlobalVarLookup (GlobalVarLookup n) = SOME n) /\
   (dest_GlobalVarLookup _ = NONE)`;;

let exp_size_map_snd = prove
 (`!p_es. list_size flat_exp_size (MAP SND p_es) <=
          list_size (pair_size flat_pat_size flat_exp_size) p_es`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; list_size; pair_size; LE_REFL] THEN
  ASM_ARITH_TAC);;

let exp_size_map_snd_snd = prove
 (`!vv_es. list_size flat_exp_size (MAP (\x. SND (SND x)) vv_es) <=
           list_size (pair_size mlstring_size
                        (pair_size mlstring_size flat_exp_size)) vv_es`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; list_size; pair_size; LE_REFL] THEN
  ASM_ARITH_TAC);;

let find_loc_def = sem1aux_def_wf
  `measure (\x:flat_exp + flat_exp list.
              sum_CASE x flat_exp_size (list_size flat_exp_size))`
  IL1AUX_FLAT_TC_TAC
  `(find_loc (flat_Raise _ er) = find_loc er) /\
   (find_loc (flat_Handle _ eh p_es) =
      union (find_loc eh) (find_locL (MAP SND p_es))) /\
   (find_loc (flat_Lit _ _) = LN:num_set) /\
   (find_loc (flat_Con _ _ es) = find_locL es) /\
   (find_loc (Var_local _ _) = LN) /\
   (find_loc (flat_Fun _ _ ef) = find_loc ef) /\
   (find_loc (flat_App _ op es) =
      match dest_GlobalVarInit op with
        SOME n -> insert n one (find_locL es)
      | NONE -> find_locL es) /\
   (find_loc (flat_If _ ei1 ei2 ei3) =
      union (find_loc ei1) (union (find_loc ei2) (find_loc ei3))) /\
   (find_loc (flat_Mat _ em p_es) =
      union (find_loc em) (find_locL (MAP SND p_es))) /\
   (find_loc (flat_Let _ _ el1 el2) = union (find_loc el1) (find_loc el2)) /\
   (find_loc (flat_Letrec _ vv_es elr1) =
      union (find_locL (MAP (SND o SND) vv_es)) (find_loc elr1)) /\
   (find_locL [] = LN) /\
   (find_locL (CONS e es) = union (find_loc e) (find_locL es))`;;

let find_loc_ind = cake_ind "find_loc";;

let find_lookups_def = sem1aux_def_wf
  `measure (\x:flat_exp + flat_exp list.
              sum_CASE x flat_exp_size (list_size flat_exp_size))`
  IL1AUX_FLAT_TC_TAC
  `(find_lookups (flat_Raise _ er) = find_lookups er) /\
   (find_lookups (flat_Handle _ eh p_es) =
      union (find_lookups eh) (find_lookupsL (MAP SND p_es))) /\
   (find_lookups (flat_Lit _ _) = LN:num_set) /\
   (find_lookups (flat_Con _ _ es) = find_lookupsL es) /\
   (find_lookups (Var_local _ _) = LN) /\
   (find_lookups (flat_Fun _ _ ef) = find_lookups ef) /\
   (find_lookups (flat_App _ op es) =
      match dest_GlobalVarLookup op with
        SOME n -> insert n one (find_lookupsL es)
      | NONE -> find_lookupsL es) /\
   (find_lookups (flat_If _ ei1 ei2 ei3) =
      union (find_lookups ei1)
            (union (find_lookups ei2) (find_lookups ei3))) /\
   (find_lookups (flat_Mat _ em p_es) =
      union (find_lookups em) (find_lookupsL (MAP SND p_es))) /\
   (find_lookups (flat_Let _ _ el1 el2) =
      union (find_lookups el1) (find_lookups el2)) /\
   (find_lookups (flat_Letrec _ vv_es elr1) =
      union (find_lookupsL (MAP (SND o SND) vv_es)) (find_lookups elr1)) /\
   (find_lookupsL [] = LN) /\
   (find_lookupsL (CONS e es) = union (find_lookups e) (find_lookupsL es))`;;

let find_lookups_ind = cake_ind "find_lookups";;

let analyse_exp_def = cake_def
  `analyse_exp e =
     let locs = find_loc e in
     let lookups = find_lookups e in
     if flat_elim_is_pure e then
       (if is_hidden e then (LN:num_set, map (K lookups) locs)
        else (locs, map (K lookups) locs))
     else (union locs lookups, map (K (LN:num_set)) (union locs lookups))`;;

let code_analysis_union_def = cake_def
  `code_analysis_union (r1:A spt,t1) (r2,t2) =
     (union r1 r2, num_set_tree_union t1 t2)`;;

let analyse_code_def = cake_def
  `(analyse_code [] = (LN:num_set, LN:num_set spt)) /\
   (analyse_code (CONS e cs) =
      code_analysis_union (analyse_exp e) (analyse_code cs))`;;

(* REMOVAL FUNCTIONS *)

(* if none of the global variables that e may assign to are in the          *)
(* reachable set, then e is candidate for removal; if any are in, then keep *)
(* e; however if e is not pure (can have side-effects), then it must be     *)
(* kept                                                                      *)

let keep_def = cake_def
  `keep (reachable:B spt) e <=>
     if inter (find_loc e) reachable = LN then ~(flat_elim_is_pure e) else T`;;

let remove_unreachable_def = cake_def
  `remove_unreachable (reachable:B spt) l = FILTER (keep reachable) l`;;

let has_Eval_dec_def = cake_def
  `has_Eval_dec e <=> has_Eval e`;;

let remove_flat_prog_def = cake_def
  `remove_flat_prog code =
     if EX has_Eval_dec code then code
     else
       let (r,t) = analyse_code code in
       let reachable = closure_spt r t in
       remove_unreachable reachable code`;;
