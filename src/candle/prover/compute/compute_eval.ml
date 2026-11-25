(* ========================================================================= *)
(* compute_eval: port of HOL4 candle/prover/compute/compute_evalScript.sml   *)
(* (CakeML v3479).  Interpreter function for the Candle compute primitive.   *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The overloads of compute_syntax (_0, _BIT0_TM, Cexp, ...) are read by   *)
(*   its parser extension (see the header of compute_syntax.ml).             *)
(* - Names as doc/names.tsv says: dest_num is compute_dest_num (a            *)
(*   HOL Light name), and its family dest_numeral, dest_numeral_opt,         *)
(*   dest_binary, dest_cexp; mapOption, map, check, option, subst and the    *)
(*   do_ functions take the prefix compute_ too.  The mutual partners of     *)
(*   compute_eval and compute_eval_ind keep HOL4's names compute_eval_list   *)
(*   and compute_eval_ind_list.                                              *)
(* - The do-notation of the monad st_ex is written with the constants of     *)
(*   ml_monadBase.ml, as in holKernel.ml: do x <- m; r od is st_ex_bind m    *)
(*   (\x. r), do (a,b) <- m; r od is st_ex_bind m (\p. match p with (a,b)    *)
(*   -> r), do m; r od is st_ex_ignore_bind m r.  HOL4's local overloads     *)
(*   return, failwith, error and timeout are st_ex_return,                   *)
(*   holKernel_raise_Failure, holKernel_raise_Failure (implode "error") and  *)
(*   holKernel_raise_Failure (implode "timeout").  The functions that only   *)
(*   return (compute_do_arith, ..., compute_map) are polymorphic in the      *)
(*   state and exception types, as in HOL4.                                  *)
(* - HOL4's ZIP (args,cs) is ZIP args cs: the lengths are checked equal      *)
(*   before (compute_check), so the truncation of HOL4's ZIP does not        *)
(*   matter (the evaluated list has the length of the original one).        *)
(* - HOL4's compute_eval_ind_def (a second definition, whose induction       *)
(*   theorem compute_eval_ind_ind is used by compute_execProof) is defined   *)
(*   as in HOL4; HOL4 then deletes the binding of its definition theorem,    *)
(*   here it stays (HOL Light cannot delete constants).                      *)
(* - mapOption_CONG and map_CONG (HOL4 [defncong]) are theorems here; no     *)
(*   later definition recurses through compute_mapOption or compute_map.     *)
(* - Local helpers that are not HOL4 theorems are CMPEVAUX_.                 *)
(* ========================================================================= *)

needs "candle/standard/monadic/holKernel.ml";;
needs "candle/prover/compute/compute_syntax.ml";;

prioritize_num();;
type_invention_error := true;;

compute_overloads_on ();;

(* the induction theorem (a case analysis) that HOL4's TFL makes for a      *)
(* non-recursive definition by patterns: one case per clause of the         *)
(* definition theorem def (the completed clauses); the recipe of wordLang's *)
(* IL2AUX_case_ind                                                          *)
let CMPEVAUX_case_ind (def:thm) : thm =
  let cls = map (fun cl -> let vs,eq = strip_forall cl in
                           let c,args = strip_comb(lhs eq) in vs,c,args)
                (conjuncts(concl def)) in
  let _,c,args0 = hd cls in
  let tty = mk_tuple_ty (map type_of args0) in
  let wfth = ISPEC (mk_abs(mk_var("x",tty),`0`)) WF_MEASURE in
  derive_induction c (map (fun (vs,_,args) -> vs,args) cls) [] wfth;;

(* ------------------------------------------------------------------------- *)
(* Destructuring                                                             *)
(* ------------------------------------------------------------------------- *)

let compute_dest_num_def = cake_def
  `compute_dest_num tm =
     match tm with
       hol_Const n t -> if tm = _0 then SOME 0 else NONE
     | hol_Comb (hol_Const nm t) r ->
         (match compute_dest_num r with
            NONE -> NONE
          | SOME n -> if hol_Const nm t = _BIT0_TM then SOME (2 * n)
                      else if hol_Const nm t = _BIT1_TM then SOME (2 * n + 1)
                      else NONE)
     | _ -> NONE`;;

let compute_dest_num_ind = cake_ind "compute_dest_num";;

let compute_dest_numeral_def = cake_def
  `compute_dest_numeral tm =
     match tm with
       hol_Comb (hol_Const n t) r ->
         if hol_Const n t = _NUMERAL_TM then
           (match compute_dest_num r with
              NONE -> holKernel_raise_Failure (implode "dest_numeral")
            | SOME n -> st_ex_return n)
         else
           holKernel_raise_Failure (implode "dest_numeral")
     | _ -> holKernel_raise_Failure (implode "dest_numeral")`;;

let compute_dest_numeral_opt_def = cake_def
  `compute_dest_numeral_opt tm =
     match tm with
       hol_Comb (hol_Const n t) r ->
         if hol_Const n t = _NUMERAL_TM then
           (match compute_dest_num r with
              NONE -> NONE
            | SOME n -> SOME n)
         else
           NONE
     | _ -> NONE`;;

let compute_dest_binary_def = cake_def
  `compute_dest_binary tm' tm =
     match tm with
       hol_Comb (hol_Comb (hol_Const n t) l) r ->
         if tm' = hol_Const n t then st_ex_return (l,r)
         else holKernel_raise_Failure (implode "dest_binary")
     | _ -> holKernel_raise_Failure (implode "dest_binary")`;;

let list_dest_comb_def = cake_def
  `(list_dest_comb sofar (hol_Comb f x) = list_dest_comb (CONS x sofar) f) /\
   (list_dest_comb sofar tm = CONS tm sofar)`;;

let list_dest_comb_ind = cake_ind "list_dest_comb";;

let list_dest_comb_not_nil = prove
 (`!sofar tm. ~(list_dest_comb sofar tm = [])`,
  MATCH_MP_TAC list_dest_comb_ind THEN
  REWRITE_TAC[list_dest_comb_def; NOT_CONS_NIL]);;
let _ = cake_add_simps [list_dest_comb_not_nil];;

let list_dest_comb_folds_back = prove
 (`!sofar tm h t.
     list_dest_comb sofar tm = CONS h t ==>
       ?xs. t = APPEND xs sofar /\
            FOLDL hol_Comb h xs = tm`,
  MATCH_MP_TAC list_dest_comb_ind THEN
  REWRITE_TAC[list_dest_comb_def; CONS_11] THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`h:hol_term`; `t:hol_term list`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `xs:hol_term list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `APPEND xs [x:hol_term]` THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; FOLDL_APPEND; FOLDL];
    EXISTS_TAC `[]:hol_term list` THEN ASM_REWRITE_TAC[APPEND; FOLDL];
    EXISTS_TAC `[]:hol_term list` THEN ASM_REWRITE_TAC[APPEND; FOLDL];
    EXISTS_TAC `[]:hol_term list` THEN ASM_REWRITE_TAC[APPEND; FOLDL]]);;

let term_size_alt_def = cake_def
  `(term_size_alt (hol_Comb s t) = term_size_alt s + term_size_alt t) /\
   (term_size_alt (hol_Abs s t) = term_size_alt s + term_size_alt t) /\
   (term_size_alt _ = 1)`;;

let list_term_size_alt_def = cake_def
  `(list_term_size_alt [] = 0) /\
   (list_term_size_alt (CONS x xs) = term_size_alt x + list_term_size_alt xs)`;;

let list_dest_comb_term_size = prove
 (`!sofar tm res.
     list_dest_comb sofar tm = res ==>
       list_term_size_alt res = list_term_size_alt sofar + term_size_alt tm`,
  MATCH_MP_TAC list_dest_comb_ind THEN
  REWRITE_TAC[list_dest_comb_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_SIMP_TAC[list_term_size_alt_def; term_size_alt_def] THEN ARITH_TAC);;

let list_term_size_MEM = prove
 (`!x xs. MEM x xs ==> term_size_alt x <= list_term_size_alt xs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; list_term_size_alt_def] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `a:num <= a + b`] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let compute_mapOption_def = cake_def
  `(compute_mapOption (f:A->(B)option) [] = SOME []) /\
   (compute_mapOption f (CONS x xs) =
      match f x with
        NONE -> NONE
      | SOME y ->
          (match compute_mapOption f xs with
             NONE -> NONE
           | SOME ys -> SOME (CONS y ys)))`;;

let mapOption_CONG = prove
 (`!xs ys (f:A->(B)option) g.
     xs = ys /\
     (!x. MEM x xs ==> f x = g x) ==>
       compute_mapOption f xs = compute_mapOption g ys`,
  LIST_INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[compute_mapOption_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MEM]) THEN
  SUBGOAL_THEN `(f:A->(B)option) h = g h` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `compute_mapOption (f:A->(B)option) t = compute_mapOption g t`
    SUBST1_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[]]);;

let mapOption_LENGTH = prove
 (`!xs ys (f:A->(B)option).
     compute_mapOption f xs = SOME ys ==> LENGTH xs = LENGTH ys`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[compute_mapOption_def] THEN
  REPEAT GEN_TAC THENL
   [MESON_TAC[injectivity "option"; LENGTH]; ALL_TAC] THEN
  REPEAT (TOP_CASE_TAC THEN REWRITE_TAC[distinctness "option"]) THEN
  REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[LENGTH; SUC_INJ] THEN ASM_MESON_TAC[]);;

(* HOL4: Termination wf_rel_tac measure term_size_alt (with                *)
(* list_dest_comb_term_size and list_term_size_MEM)                         *)
let CMPEVAUX_DEST_CEXP_TERM_TAC : tactic =
  REWRITE_TAC[MEASURE] THEN REPEAT STRIP_TAC THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_var (lhs (concl th)) then SUBST_ALL_TAC th
                                   else failwith "")) THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP list_dest_comb_term_size o
    check (fun th -> can (find_term (fun t -> t = `list_dest_comb`)) (concl th))) THEN
  REWRITE_TAC[list_term_size_alt_def; term_size_alt_def] THEN
  TRY (FIRST_ASSUM (MP_TAC o MATCH_MP list_term_size_MEM)) THEN
  ARITH_TAC;;

let compute_dest_cexp_def = cake_def_wf `MEASURE term_size_alt` CMPEVAUX_DEST_CEXP_TERM_TAC
  `compute_dest_cexp tm =
     match list_dest_comb [] tm with
       [hol_Var n ty] -> if ty = Cexp then SOME (compute_Var n) else NONE
     | CONS (hol_Const n ty) args ->
         (if hol_Const n ty = _LET_TM then
            (match args with
               [hol_Abs (hol_Var s ty) y; x] ->
                 if ty = Cexp then
                   (match compute_dest_cexp x with
                      NONE -> NONE
                    | SOME p ->
                        (match compute_dest_cexp y with
                           NONE -> NONE
                         | SOME q -> SOME (compute_Let s p q)))
                 else NONE
             | _ -> NONE)
          else let vs = MAP compute_dest_cexp args in
            (match vs with
               [arg] ->
                 if hol_Const n ty = _CEXP_NUM_TM then
                   (match compute_dest_numeral_opt (HD args) with
                      NONE -> NONE
                    | SOME n -> SOME (compute_Num n))
                 else if ty = Fun Cexp Cexp then
                   (match arg with
                      NONE -> NONE
                    | SOME cv ->
                        if hol_Const n ty = _CEXP_FST_TM then
                          SOME (compute_Uop compute_Fst cv)
                        else if hol_Const n ty = _CEXP_SND_TM then
                          SOME (compute_Uop compute_Snd cv)
                        else if hol_Const n ty = _CEXP_ISPAIR_TM then
                          SOME (compute_Uop compute_Ispair cv)
                        else
                          SOME (compute_App n [cv]))
                 else
                   NONE
             | [SOME p; SOME q] ->
                 if hol_Const n ty = _CEXP_PAIR_TM then
                   SOME (compute_Pair p q)
                 else if hol_Const n ty = _CEXP_ADD_TM then
                   SOME (compute_Binop compute_Add p q)
                 else if hol_Const n ty = _CEXP_SUB_TM then
                   SOME (compute_Binop compute_Sub p q)
                 else if hol_Const n ty = _CEXP_MUL_TM then
                   SOME (compute_Binop compute_Mul p q)
                 else if hol_Const n ty = _CEXP_DIV_TM then
                   SOME (compute_Binop compute_Div p q)
                 else if hol_Const n ty = _CEXP_MOD_TM then
                   SOME (compute_Binop compute_Mod p q)
                 else if hol_Const n ty = _CEXP_LESS_TM then
                   SOME (compute_Binop compute_Less p q)
                 else if hol_Const n ty = _CEXP_EQ_TM then
                   SOME (compute_Binop compute_Eq p q)
                 else if ty = Fun Cexp (Fun Cexp Cexp) then
                   SOME (compute_App n [p; q])
                 else
                   NONE
             | [SOME p; SOME q; SOME r] ->
                 if hol_Const n ty = _CEXP_IF_TM then
                   SOME (compute_If p q r)
                 else if ty = Fun Cexp (Fun Cexp (Fun Cexp Cexp)) then
                   SOME (compute_App n [p; q; r])
                 else
                   NONE
             | args ->
                 (match compute_mapOption I args with
                    NONE -> NONE
                  | SOME cvs ->
                      if ty = app_type (LENGTH cvs) then
                        SOME (compute_App n cvs)
                      else NONE)))
     | _ -> NONE`;;

let compute_dest_cexp_ind = cake_ind "compute_dest_cexp";;

(* TODO use term_size and list_size as measure instead (HOL4's comment) *)

let compute_do_arith_def = cake_def
  `(compute_do_arith (opn:num->num->num) (compute_Num m) (compute_Num n) =
      (st_ex_return (compute_Num (opn m n)):A->(compute_exp,B)exc#A)) /\
   (compute_do_arith opn (compute_Num m) _ =
      (st_ex_return (compute_Num (opn m 0)):A->(compute_exp,B)exc#A)) /\
   (compute_do_arith opn _ (compute_Num n) =
      (st_ex_return (compute_Num (opn 0 n)):A->(compute_exp,B)exc#A)) /\
   (compute_do_arith opn _ _ =
      (st_ex_return (compute_Num 0):A->(compute_exp,B)exc#A))`;;

let compute_do_arith_ind = CMPEVAUX_case_ind compute_do_arith_def;;

let compute_do_reln_def = cake_def
  `(compute_do_reln (opn:num->num->bool) (compute_Num m) (compute_Num n) =
      (st_ex_return (compute_Num (if opn m n then SUC 0 else 0))
         :A->(compute_exp,B)exc#A)) /\
   (compute_do_reln opn _ _ =
      (st_ex_return (compute_Num 0):A->(compute_exp,B)exc#A))`;;

let compute_do_reln_ind = CMPEVAUX_case_ind compute_do_reln_def;;

let compute_do_eq_def = cake_def
  `compute_do_eq (p:compute_exp) q =
     (st_ex_return (compute_Num (if p = q then SUC 0 else 0)):A->(compute_exp,B)exc#A)`;;

let compute_do_binop_def = cake_def
  `(compute_do_binop compute_Add p q =
      (compute_do_arith (+) p q:A->(compute_exp,B)exc#A)) /\
   (compute_do_binop compute_Sub p q =
      (compute_do_arith (-) p q:A->(compute_exp,B)exc#A)) /\
   (compute_do_binop compute_Mul p q =
      (compute_do_arith ( * ) p q:A->(compute_exp,B)exc#A)) /\
   (compute_do_binop compute_Div p q =
      (compute_do_arith (SAFEDIV) p q:A->(compute_exp,B)exc#A)) /\
   (compute_do_binop compute_Mod p q =
      (compute_do_arith (SAFEMOD) p q:A->(compute_exp,B)exc#A)) /\
   (compute_do_binop compute_Less p q =
      (compute_do_reln (<) p q:A->(compute_exp,B)exc#A)) /\
   (compute_do_binop compute_Eq p q =
      (compute_do_eq p q:A->(compute_exp,B)exc#A))`;;

let compute_do_fst_def = cake_def
  `(compute_do_fst (compute_Pair p q) = (st_ex_return p:A->(compute_exp,B)exc#A)) /\
   (compute_do_fst _ = (st_ex_return (compute_Num 0):A->(compute_exp,B)exc#A))`;;

let compute_do_snd_def = cake_def
  `(compute_do_snd (compute_Pair p q) = (st_ex_return q:A->(compute_exp,B)exc#A)) /\
   (compute_do_snd _ = (st_ex_return (compute_Num 0):A->(compute_exp,B)exc#A))`;;

let compute_do_ispair_def = cake_def
  `(compute_do_ispair (compute_Pair p q) =
      (st_ex_return (compute_Num 1):A->(compute_exp,B)exc#A)) /\
   (compute_do_ispair _ = (st_ex_return (compute_Num 0):A->(compute_exp,B)exc#A))`;;

let compute_do_uop_def = cake_def
  `(compute_do_uop compute_Fst p = (compute_do_fst p:A->(compute_exp,B)exc#A)) /\
   (compute_do_uop compute_Snd p = (compute_do_snd p:A->(compute_exp,B)exc#A)) /\
   (compute_do_uop compute_Ispair p = (compute_do_ispair p:A->(compute_exp,B)exc#A))`;;

let compute_map_def = cake_def
  `(compute_map (f:A->S->(B,E)exc#S) [] = (st_ex_return []:S->(B list,E)exc#S)) /\
   (compute_map (f:A->S->(B,E)exc#S) (CONS x xs) =
      st_ex_bind (f x) (\y.
      st_ex_bind (compute_map f xs) (\ys.
      (st_ex_return (CONS y ys):S->(B list,E)exc#S))))`;;

let map_CONG = prove
 (`!xs ys (f:A->S->(B,E)exc#S) g.
     xs = ys /\
     (!x. MEM x xs ==> f x = g x) ==>
       compute_map f xs = compute_map g ys`,
  LIST_INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[compute_map_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MEM]) THEN
  SUBGOAL_THEN `(f:A->S->(B,E)exc#S) h = g h` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `compute_map (f:A->S->(B,E)exc#S) t = compute_map g t`
    SUBST1_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[]]);;

let map_LENGTH = prove
 (`!xs (f:A->S->(B,E)exc#S) ys s s'.
     compute_map f xs s = (M_success ys,s') ==>
       LENGTH xs = LENGTH ys`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[compute_map_def; ml_monadBase_st_ex_bind_success;
              ml_monadBase_st_ex_return_success; injectivity "exc"] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH; SUC_INJ] THEN
  ASM_MESON_TAC[]);;

let map_thm = prove
 (`!xs (f:A->S->(B,E)exc#S) ys s s'.
     compute_map f xs s = (M_success ys,s') ==>
       LENGTH xs = LENGTH ys /\
       !n. n < LENGTH xs ==> ?r r'. f (EL n xs) r = (M_success (EL n ys),r')`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[compute_map_def; ml_monadBase_st_ex_bind_success;
              ml_monadBase_st_ex_return_success; injectivity "exc"] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(MP_TAC o MATCH_MP ih)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[SUC_INJ] THEN
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[EL; HD; TL; LT_SUC] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Interpreter for compute values                                            *)
(* ------------------------------------------------------------------------- *)

let compute_check_def = cake_def
  `compute_check P =
     if P then st_ex_return one else holKernel_raise_Failure (implode "error")`;;

let compute_option_def = cake_def
  `compute_option (f:A->(B)option) x =
     match f x with
       SOME r -> st_ex_return r
     | _ -> holKernel_raise_Failure (implode "error")`;;

(* HOL4: Termination wf_rel_tac measure (compute_exp_size o SND) *)
let compute_subst_def = cake_def_clauses
  [`compute_subst (env:(mlstring#compute_exp)list) (compute_Var n) =
      match ALOOKUP env n with
        NONE -> compute_Var n
      | SOME cv -> cv`;
   `compute_subst (env:(mlstring#compute_exp)list) (compute_Num n) = compute_Num n`;
   `compute_subst (env:(mlstring#compute_exp)list) (compute_Pair p q) =
      compute_Pair (compute_subst env p) (compute_subst env q)`;
   `compute_subst (env:(mlstring#compute_exp)list) (compute_Uop uop p) =
      compute_Uop uop (compute_subst env p)`;
   `compute_subst (env:(mlstring#compute_exp)list) (compute_Binop bop p q) =
      compute_Binop bop (compute_subst env p) (compute_subst env q)`;
   `compute_subst (env:(mlstring#compute_exp)list) (compute_App f cs) =
      compute_App f (MAP (compute_subst env) cs)`;
   `compute_subst (env:(mlstring#compute_exp)list) (compute_If p q r) =
      compute_If (compute_subst env p) (compute_subst env q) (compute_subst env r)`;
   `compute_subst (env:(mlstring#compute_exp)list) (compute_Let s x y) =
      compute_Let s (compute_subst env x)
                    (compute_subst (FILTER (\(n,x). ~(n = s)) env) y)`];;

let compute_subst_ind = cake_ind "compute_subst";;

let subst_empty = prove
 (`!x. compute_subst [] x = x`,
  SUBGOAL_THEN `!xs x. xs = [] ==> compute_subst xs x = x`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC compute_subst_ind THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FILTER]) THEN
  ASM_SIMP_TAC[compute_subst_def; ALOOKUP_THM; FILTER] THEN
  TRY (CASE_REWRITE_TAC[]) THEN REWRITE_TAC[injectivity "compute_exp"] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM MAP_ID] THEN
  MATCH_MP_TAC MAP_EQ THEN ASM_SIMP_TAC[GSYM ALL_MEM]);;
let _ = cake_add_simps [subst_empty];;

(* HOL4: Termination wf_rel_tac inv_image ($< LEX $<) (the clock, then the *)
(* size of the expression or list)                                         *)
let compute_eval_def = cake_def_wf
  `inv_image ((<) LEX (<))
     (\x. match x with
            INL (ck,(ceqs:(mlstring#mlstring list#compute_exp)list),cv) ->
              (ck,compute_exp_size cv)
          | INR (ck,(ceqs:(mlstring#mlstring list#compute_exp)list),cvs) ->
              (ck,list_size compute_exp_size cvs))`
  TERM_TAC
  `(compute_eval ck (ceqs:(mlstring#mlstring list#compute_exp)list) (compute_Var s) =
      holKernel_raise_Failure (implode "error")) /\
   (compute_eval ck ceqs (compute_Num n) = st_ex_return (compute_Num n)) /\
   (compute_eval ck ceqs (compute_Pair p q) =
      st_ex_bind (compute_eval ck ceqs p) (\x.
      st_ex_bind (compute_eval ck ceqs q) (\y.
      st_ex_return (compute_Pair x y)))) /\
   (compute_eval ck ceqs (compute_Uop uop p) =
      st_ex_bind (compute_eval ck ceqs p) (\x. compute_do_uop uop x)) /\
   (compute_eval ck ceqs (compute_Binop bop p q) =
      st_ex_bind (compute_eval ck ceqs p) (\x.
      st_ex_bind (compute_eval ck ceqs q) (\y.
      compute_do_binop bop x y))) /\
   (compute_eval ck ceqs (compute_App f cs) =
      if ck = 0 then holKernel_raise_Failure (implode "timeout") else
      st_ex_bind (compute_option (ALOOKUP ceqs) f) (\p.
      match p with
        (args,exp) ->
          st_ex_ignore_bind (compute_check (LENGTH args = LENGTH cs))
          (st_ex_bind (compute_eval_list ck ceqs cs) (\cs.
           compute_eval (ck - 1) ceqs (compute_subst (ZIP args cs) exp))))) /\
   (compute_eval ck ceqs (compute_If p q r) =
      st_ex_bind (compute_eval ck ceqs p) (\x.
      match x with
        compute_Num 0 -> compute_eval ck ceqs r
      | compute_Num _ -> compute_eval ck ceqs q
      | compute_Pair _ _ -> compute_eval ck ceqs r
      | _ -> holKernel_raise_Failure (implode "error"))) /\
   (compute_eval ck ceqs (compute_Let s p q) =
      if ck = 0 then holKernel_raise_Failure (implode "timeout") else
      st_ex_bind (compute_eval ck ceqs p) (\x.
      compute_eval (ck - 1) ceqs (compute_subst [s,x] q))) /\
   (compute_eval_list ck ceqs [] = st_ex_return []) /\
   (compute_eval_list ck ceqs (CONS c cs) =
      st_ex_bind (compute_eval ck ceqs c) (\x.
      st_ex_bind (compute_eval_list ck ceqs cs) (\xs.
      st_ex_return (CONS x xs))))`;;

let compute_eval_ind = cake_ind "compute_eval";;

(* Let and App cases are modified below to get a more useful ind theorem *)
let compute_eval_ind_def = cake_def_wf
  `inv_image ((<) LEX (<))
     (\x. match x with
            INL (ck,(ceqs:(mlstring#mlstring list#compute_exp)list),cv) ->
              (ck,compute_exp_size cv)
          | INR (ck,(ceqs:(mlstring#mlstring list#compute_exp)list),cvs) ->
              (ck,list_size compute_exp_size cvs))`
  TERM_TAC
  `(compute_eval_ind ck (ceqs:(mlstring#mlstring list#compute_exp)list) (compute_Var s) =
      holKernel_raise_Failure (implode "error")) /\
   (compute_eval_ind ck ceqs (compute_Num n) = st_ex_return (compute_Num n)) /\
   (compute_eval_ind ck ceqs (compute_Pair p q) =
      st_ex_bind (compute_eval_ind ck ceqs p) (\x.
      st_ex_bind (compute_eval_ind ck ceqs q) (\y.
      st_ex_return (compute_Pair x y)))) /\
   (compute_eval_ind ck ceqs (compute_Uop uop p) =
      st_ex_bind (compute_eval_ind ck ceqs p) (\x. compute_do_uop uop x)) /\
   (compute_eval_ind ck ceqs (compute_Binop bop p q) =
      st_ex_bind (compute_eval_ind ck ceqs p) (\x.
      st_ex_bind (compute_eval_ind ck ceqs q) (\y.
      compute_do_binop bop x y))) /\
   (compute_eval_ind ck ceqs (compute_App f cs) =
      if ck = 0 then holKernel_raise_Failure (implode "timeout") else
      st_ex_bind (compute_option (ALOOKUP ceqs) f) (\p.
      match p with
        (args,exp) ->
          st_ex_ignore_bind (compute_check (LENGTH args = LENGTH cs))
          (st_ex_bind (compute_eval_ind_list ck ceqs cs) (\cs.
           compute_eval_ind (ck - 1) ceqs exp)))) /\
   (compute_eval_ind ck ceqs (compute_If p q r) =
      st_ex_bind (compute_eval_ind ck ceqs p) (\x.
      match x with
        compute_Num 0 -> compute_eval_ind ck ceqs r
      | compute_Num _ -> compute_eval_ind ck ceqs q
      | compute_Pair _ _ -> compute_eval_ind ck ceqs r
      | _ -> holKernel_raise_Failure (implode "error"))) /\
   (compute_eval_ind ck ceqs (compute_Let s p q) =
      if ck = 0 then holKernel_raise_Failure (implode "timeout") else
      st_ex_bind (compute_eval_ind ck ceqs p) (\x.
      compute_eval_ind (ck - 1) ceqs q)) /\
   (compute_eval_ind_list ck ceqs [] = st_ex_return []) /\
   (compute_eval_ind_list ck ceqs (CONS c cs) =
      st_ex_bind (compute_eval_ind ck ceqs c) (\x.
      st_ex_bind (compute_eval_ind_list ck ceqs cs) (\xs.
      st_ex_return (CONS x xs))))`;;

let compute_eval_ind_ind = cake_ind "compute_eval_ind";;

(* HOL4: val _ = Theory.delete_binding "compute_eval_ind_def" (kept here) *)

compute_overloads_off ();;
