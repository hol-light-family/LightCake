(* ========================================================================= *)
(* infer: port of HOL4 compiler/inference/inferScript.sml (CakeML v3479).    *)
(* Definition of CakeML's type inferencer.                                   *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/typeSystem.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/unify.ml";;
needs "semantics/primTypes.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Notes on the rendering:                                                   *)
(* - The state-and-exception monad of ml_monadBase: do x <- m; r od is       *)
(*   st_ex_bind m (\x. r), do (a,b) <- m; r od is                            *)
(*   st_ex_bind m (\p. match p with (a,b) -> r), () <- m; r is               *)
(*   st_ex_bind m (\u. r), do m; r od is st_ex_ignore_bind m r, return x is  *)
(*   st_ex_return x.  HOL4 () is one.                                        *)
(* - Records: l.loc is loc_err_info_loc l, s.next_uvar is                    *)
(*   infer_st_next_uvar s, ienv.inf_v is inf_env_inf_v ienv; r with f := v  *)
(*   is R_f_fupd (K v) r (several fields: the first field outermost); record *)
(*   literals are R_REC with the fields in declaration order.               *)
(* - Names (doc/names.tsv): HOL4 read, write, guard and init_config          *)
(*   are infer_read, infer_write, infer_guard and infer_init_config.         *)
(* - The mlstring literal of x is implode "x"; concat is mlstring_concat;   *)
(*   mlint$toString is toString (on int), toString on num is num_to_str;     *)
(*   GENLIST f n is list_of_seq f n; set is set_of_list; EVERY is ALL.      *)
(* - HOL4 type_name_check_sub is defined with the state as an explicit       *)
(*   argument (TYSYS2AUX_type_name_check_sub_curried) and HOL4's equations   *)
(*   type_name_check_sub_def are derived.                                    *)
(* - Not ported (only used by infer_cv, the cv translation of the           *)
(*   inferencer, outside the compile_correct closure): infer_p_expand,       *)
(*   constrain_op_case_def (the [compute] form of constrain_op_def made by    *)
(*   PMATCH_ELIM_CONV; here constrain_op_def has case constants already),    *)
(*   constrain_op_expand, infer_e_expand, infer_d_expand.  The other cv      *)
(*   rewrites (type_name_check_sub_def, to_type_name_check_sub, ...,         *)
(*   check_type_definition_expand) are ported.                              *)
(* - Helper lemmas that are not HOL4 theorems are TYSYS2AUX_.                *)
(* ------------------------------------------------------------------------- *)


(* HOL4: Type err_var = (type_of ``primTypes$prim_tenv.t``) *)
new_type_abbrev("err_var",`:(modN,typeN,tvarN list # t)namespace`);;

let loc_err_info_INFO = cake_record "loc_err_info"
  ["loc","locs option";
   "err","err_var"];;

let loc_err_info_component_equality = loc_err_info_INFO.ri_component_equality;;

let failwith_def = cake_def
  `failwith (l:loc_err_info) (msg:A) =
     (\s:B. (M_failure (loc_err_info_loc l,msg):(C,locs option#A)exc,s))`;;

let infer_guard_def = cake_def
  `infer_guard P (l:loc_err_info) (msg:A) =
     if P then (st_ex_return one:B->(1,locs option#A)exc#B) else failwith l msg`;;

let infer_read_def = cake_def
  `(infer_read:A->(A,B)exc#A) = \s. (M_success s,s)`;;

let infer_write_def = cake_def
  `infer_write (v:A) = \s:A. (M_success one:(1,B)exc,v)`;;

let lookup_st_ex_def = cake_def
  `lookup_st_ex (l:loc_err_info) (err:mlstring) (id:(mlstring,mlstring)id)
                (ienv:(mlstring,mlstring,V)namespace) (st:S) =
     match nsLookup ienv id with
       NONE -> (M_failure (loc_err_info_loc l,
                           mlstring_concat [implode "Undefined "; err; implode ": ";
                                            id_to_string id]),st)
     | SOME v -> (M_success v,st)`;;

let infer_st_INFO = cake_record "infer_st"
  ["next_uvar","num";
   "subst","(type_ident,infer_t)fmap";
   "next_id","num"];;

let infer_st_component_equality = infer_st_INFO.ri_component_equality;;
let fresh_uvar_def = cake_def
  `(fresh_uvar:infer_st->(infer_t,A)exc#infer_st) =
     \s. (M_success (Infer_Tuvar (infer_st_next_uvar s)),
          infer_st_next_uvar_fupd (K (infer_st_next_uvar s + 1)) s)`;;

let n_fresh_uvar_def = cake_def
  `n_fresh_uvar (n:num) =
     if n = 0 then
       (st_ex_return []:infer_st->((infer_t)list,A)exc#infer_st)
     else
       st_ex_bind fresh_uvar (\v.
       st_ex_bind (n_fresh_uvar (n - 1)) (\vs.
       st_ex_return (CONS v vs)))`;;

let n_fresh_uvar_ind = cake_ind "n_fresh_uvar";;

let n_fresh_id_def = cake_def
  `n_fresh_id (n:num) =
     \s:infer_st. (M_success (list_of_seq (\x. infer_st_next_id s + x) n):(num list,A)exc,
          infer_st_next_id_fupd (K (infer_st_next_id s + n)) s)`;;

(* Doesn't reset the ID component *)

let init_infer_state_def = cake_def
  `init_infer_state (st:infer_st) =
     infer_st_next_uvar_fupd (K 0) (infer_st_subst_fupd (K FEMPTY) st)`;;

let init_state_def = cake_def
  `init_state = \st:infer_st. (M_success one:(1,A)exc,init_infer_state st)`;;
let add_constraint_def = cake_def
  `add_constraint (l:loc_err_info) t1 t2 =
     \st:infer_st.
       match t_unify (infer_st_subst st) t1 t2 with
         NONE ->
           (M_failure (loc_err_info_loc l,
                       mlstring_concat
                         [implode "Type mismatch between ";
                          inf_type_to_string (loc_err_info_err l)
                            (t_walkstar (infer_st_subst st) t1);
                          implode " and ";
                          inf_type_to_string (loc_err_info_err l)
                            (t_walkstar (infer_st_subst st) t2)]):(1,locs option#mlstring)exc,
            st)
       | SOME s -> (M_success one,infer_st_subst_fupd (K s) st)`;;

let add_constraints_def = cake_def
  `(add_constraints (l:loc_err_info) [] [] =
      (st_ex_return one:infer_st->(1,locs option#mlstring)exc#infer_st)) /\
   (add_constraints l (CONS t1 ts1) (CONS t2 ts2) =
      st_ex_bind (add_constraint l t1 t2) (\u.
      st_ex_bind (add_constraints l ts1 ts2) (\u.
      st_ex_return one))) /\
   (add_constraints l _ _ =
      failwith l (implode "Internal error: Bad call to add_constraints"))`;;

let add_constraints_ind = cake_ind "add_constraints";;

let get_next_uvar_def = cake_def
  `get_next_uvar = \st:infer_st. (M_success (infer_st_next_uvar st):(num,A)exc,st)`;;

let apply_subst_def = cake_def
  `apply_subst t =
     st_ex_bind (infer_read:infer_st->(infer_st,A)exc#infer_st) (\st.
     st_ex_return (t_walkstar (infer_st_subst st) t))`;;

let apply_subst_list_def = cake_def
  `apply_subst_list ts =
     st_ex_bind (infer_read:infer_st->(infer_st,A)exc#infer_st) (\st.
     st_ex_return (MAP (t_walkstar (infer_st_subst st)) ts))`;;
let inf_env_INFO = cake_record "inf_env"
  ["inf_v","(modN,varN,num # infer_t)namespace";
   "inf_c","tenv_ctor";
   "inf_t","tenv_abbrev"];;

let inf_env_component_equality = inf_env_INFO.ri_component_equality;;

(* Generalise the unification variables greater than m, starting at       *)
(* deBruijn index n.  Return how many were generalised, the generalised    *)
(* type, and a substitution that describes the generalisation.            *)

let generalise_def = cake_def_wf
  `MEASURE (\x:num#num#(num,num)fmap#infer_t + num#num#(num,num)fmap#(infer_t list).
              match x with INL (_,_,_,t) -> infer_t_size t
                         | INR (_,_,_,ts) -> list_size infer_t_size ts)`
  TERM_TAC
  `(generalise (m:num) (n:num) (s:(num,num)fmap) (Infer_Tapp ts tc) =
      let (num_gen,s',ts') = generalise_list m n s ts in
      (num_gen,s',Infer_Tapp ts' tc)) /\
   (generalise m n s (Infer_Tuvar uv) =
      match FLOOKUP s uv with
        SOME n -> (0,s,Infer_Tvar_db n)
      | NONE ->
          if m <= uv then (1,s |+ (uv,n),Infer_Tvar_db n)
          else (0,s,Infer_Tuvar uv)) /\
   (generalise m n s (Infer_Tvar_db k) = (0,s,Infer_Tvar_db k)) /\
   (generalise_list m n s [] = (0,s,[])) /\
   (generalise_list m n s (CONS t ts) =
      let (num_gen,s',t') = generalise m n s t in
      let (num_gen',s'',ts') = generalise_list m (num_gen + n) s' ts in
      (num_gen + num_gen',s'',CONS t' ts'))`;;

let generalise_ind = cake_ind "generalise";;
let infer_type_subst_def = cake_def
  `(infer_type_subst (s:(mlstring#infer_t)list) (Tvar tv) =
      match ALOOKUP s tv with
        SOME t -> t
      | NONE -> Infer_Tvar_db 0) /\
   (infer_type_subst s (Tvar_db n) = Infer_Tvar_db n) /\
   (infer_type_subst s (Tapp ts tn) = Infer_Tapp (infer_type_subst_list s ts) tn) /\
   (infer_type_subst_list s [] = []) /\
   (infer_type_subst_list s (CONS x xs) =
      CONS (infer_type_subst s x) (infer_type_subst_list s xs))`;;

let infer_type_subst_alt = prove
 (CASE_TERM `(!(s:(mlstring#infer_t)list) tv.
     infer_type_subst s (Tvar tv) =
       match ALOOKUP s tv with SOME t -> t | NONE -> Infer_Tvar_db 0) /\
   (!(s:(mlstring#infer_t)list) n. infer_type_subst s (Tvar_db n) = Infer_Tvar_db n) /\
   (!(s:(mlstring#infer_t)list) ts tn.
     infer_type_subst s (Tapp ts tn) = Infer_Tapp (MAP (infer_type_subst s) ts) tn)`,
  REWRITE_TAC[infer_type_subst_def] THEN REPEAT GEN_TAC THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN SPEC_TAC(`ts:t list`,`ts:t list`) THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[infer_type_subst_def; MAP]);;

let infer_deBruijn_subst_def = cake_def
  `(infer_deBruijn_subst (s:infer_t list) (Infer_Tvar_db n) =
      if n < LENGTH s then EL n s
      else Infer_Tvar_db (n - LENGTH s)) /\
   (infer_deBruijn_subst s (Infer_Tapp ts tn) =
      Infer_Tapp (infer_deBruijn_subst_list s ts) tn) /\
   (infer_deBruijn_subst s (Infer_Tuvar n) = Infer_Tuvar n) /\
   (infer_deBruijn_subst_list s [] = []) /\
   (infer_deBruijn_subst_list s (CONS t ts) =
      CONS (infer_deBruijn_subst s t) (infer_deBruijn_subst_list s ts))`;;

let infer_deBruijn_subst_alt = prove
 (`(!(s:infer_t list) n.
     infer_deBruijn_subst s (Infer_Tvar_db n) =
       if n < LENGTH s then EL n s else Infer_Tvar_db (n - LENGTH s)) /\
   (!(s:infer_t list) ts tn.
     infer_deBruijn_subst s (Infer_Tapp ts tn) =
       Infer_Tapp (MAP (infer_deBruijn_subst s) ts) tn) /\
   (!(s:infer_t list) n. infer_deBruijn_subst s (Infer_Tuvar n) = Infer_Tuvar n)`,
  REWRITE_TAC[infer_deBruijn_subst_def] THEN REPEAT GEN_TAC THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN SPEC_TAC(`ts:infer_t list`,`ts:infer_t list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[infer_deBruijn_subst_def; MAP]);;
let type_name_check_subst_def = cake_def_wf
  `MEASURE (\x:loc_err_info#(mlstring->mlstring)#(mlstring,mlstring,mlstring list#t)namespace#
                (mlstring list)#ast_t +
              loc_err_info#(mlstring->mlstring)#(mlstring,mlstring,mlstring list#t)namespace#
                (mlstring list)#(ast_t list).
              match x with INL (_,_,_,_,t) -> ast_t_size t
                         | INR (_,_,_,_,ts) -> list_size ast_t_size ts)`
  TERM_TAC
  `(type_name_check_subst (l:loc_err_info) (err_string_f:mlstring->mlstring)
      (tenvT:(mlstring,mlstring,mlstring list#t)namespace) (fvs:mlstring list)
      (Atvar tv) =
      st_ex_ignore_bind (infer_guard (MEM tv fvs) l (err_string_f tv))
        (st_ex_return (Tvar tv):S->(t,locs option#mlstring)exc#S)) /\
   (type_name_check_subst l f tenvT fvs (Attup ts) =
      st_ex_bind (type_name_check_subst_list l f tenvT fvs ts) (\ts'.
      st_ex_return (Ttup ts'))) /\
   (type_name_check_subst l f tenvT fvs (Atfun t1 t2) =
      st_ex_bind (type_name_check_subst l f tenvT fvs t1) (\t1'.
      st_ex_bind (type_name_check_subst l f tenvT fvs t2) (\t2'.
      st_ex_return (Tfn t1' t2')))) /\
   (type_name_check_subst l f tenvT fvs (Atapp ts tc) =
      st_ex_bind (type_name_check_subst_list l f tenvT fvs ts) (\ts'.
      st_ex_bind (lookup_st_ex l (implode "type constructor") tc tenvT) (\p.
        match p with
          (tvs',t') ->
            st_ex_ignore_bind
              (infer_guard (LENGTH tvs' = LENGTH ts) l
                 (mlstring_concat [implode "Type constructor "; id_to_string tc;
                                   implode " given "; toString (&(LENGTH ts));
                                   implode " arguments, but expected ";
                                   toString (&(LENGTH tvs'))]))
              (st_ex_return (type_subst (alist_to_fmap (ZIP tvs' ts')) t'))))) /\
   (type_name_check_subst_list l f tenvT fvs [] = st_ex_return []) /\
   (type_name_check_subst_list l f tenvT fvs (CONS t ts) =
      st_ex_bind (type_name_check_subst l f tenvT fvs t) (\t'.
      st_ex_bind (type_name_check_subst_list l f tenvT fvs ts) (\ts'.
      st_ex_return (CONS t' ts'))))`;;

let type_name_check_subst_ind = cake_ind "type_name_check_subst";;
let bind_guard = prove
 (`!b (l:loc_err_info) (x:A) (g:1->S->(B,locs option#A)exc#S).
     st_ex_bind (infer_guard b l x) g =
     \s. if b then g one s else (M_failure (loc_err_info_loc l,x),s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  REWRITE_TAC[st_ex_bind_def; infer_guard_def; st_ex_return_def; failwith_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[case_def "exc"; pair_CASE]);;

let ignore_bind_guard = prove
 (`!b (l:loc_err_info) (x:A) (g:S->(B,locs option#A)exc#S).
     st_ex_ignore_bind (infer_guard b l x) g =
     \s. if b then g s else (M_failure (loc_err_info_loc l,x),s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  REWRITE_TAC[st_ex_ignore_bind_def; infer_guard_def; st_ex_return_def; failwith_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[case_def "exc"; pair_CASE]);;

let st_ex_bind_pair = prove
 (CASE_TERM `!(x:S->(A#B,E)exc#S) (f:A#B->S->(C,E)exc#S).
     st_ex_bind x f =
     (\s. match x s with
            (M_success (y,z),s) -> f (y,z) s
          | (M_failure x,s) -> (M_failure x,s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; st_ex_bind_def] THEN
  X_GEN_TAC `s:S` THEN
  MP_TAC(ISPEC `(x:S->(A#B,E)exc#S) s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(A#B,E)exc` (X_CHOOSE_THEN `s1:S` SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE] THEN CASES_ON `r:(A#B,E)exc` THEN
  REWRITE_TAC[case_def "exc"] THEN
  MP_TAC(ISPEC `a:A#B` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` (X_CHOOSE_THEN `z:B` SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE]);;

let st_ex_bind_triple = prove
 (CASE_TERM `!(x:S->(A#B#C,E)exc#S) (f:A#B#C->S->(D,E)exc#S).
     st_ex_bind x f =
     (\s. match x s with
            (M_success (y,z,q),s) -> f (y,z,q) s
          | (M_failure x,s) -> (M_failure x,s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; st_ex_bind_def] THEN
  X_GEN_TAC `s:S` THEN
  MP_TAC(ISPEC `(x:S->(A#B#C,E)exc#S) s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(A#B#C,E)exc` (X_CHOOSE_THEN `s1:S` SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE] THEN CASES_ON `r:(A#B#C,E)exc` THEN
  REWRITE_TAC[case_def "exc"] THEN
  MP_TAC(ISPEC `a:A#B#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` (X_CHOOSE_THEN `zq:B#C` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `zq:B#C` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:B` (X_CHOOSE_THEN `q:C` SUBST1_TAC)) THEN
  REWRITE_TAC[pair_CASE]);;
(* HOL4 defines type_name_check_sub l tenvT fvs t = \s. ... with the        *)
(* recursive calls applied to the lambda's variable; the kit's recursion    *)
(* package needs the state as an argument (TYSYS2AUX_..._curried), and      *)
(* HOL4's equations are derived from those.                                 *)

let TYSYS2AUX_type_name_check_sub_curried = cake_def_wf
  `MEASURE (\x:loc_err_info#(mlstring,mlstring,mlstring list#t)namespace#
                (mlstring list)#ast_t#S +
              loc_err_info#(mlstring,mlstring,mlstring list#t)namespace#
                (mlstring list)#(ast_t list)#S.
              match x with INL (_,_,_,t,_) -> ast_t_size t
                         | INR (_,_,_,ts,_) -> list_size ast_t_size ts)`
  TERM_TAC
  `(type_name_check_sub (l:loc_err_info)
      (tenvT:(mlstring,mlstring,mlstring list#t)namespace) (fvs:mlstring list)
      (Atvar tv) (s:S) =
      if MEM tv fvs then (M_success (Tvar tv),s)
      else (M_failure (loc_err_info_loc l,INR tv:mlstring+mlstring),s)) /\
   (type_name_check_sub l tenvT fvs (Attup ts) s =
      match type_name_check_sub_list l tenvT fvs ts s with
        (M_success ts',s) -> (M_success (Ttup ts'),s)
      | (M_failure x,s) -> (M_failure x,s)) /\
   (type_name_check_sub l tenvT fvs (Atfun t1 t2) s =
      match type_name_check_sub l tenvT fvs t1 s with
        (M_success t1',s) ->
          (match type_name_check_sub l tenvT fvs t2 s with
             (M_success t2',s) -> (M_success (Tfn t1' t2'),s)
           | (M_failure x,s) -> (M_failure x,s))
      | (M_failure x,s) -> (M_failure x,s)) /\
   (type_name_check_sub l tenvT fvs (Atapp ts tc) s =
      match type_name_check_sub_list l tenvT fvs ts s with
        (M_success ts',s) ->
          (match
             (match nsLookup tenvT tc with
                NONE ->
                  (M_failure
                     (loc_err_info_loc l,
                      INL (mlstring_concat
                             [implode "Undefined "; implode "type constructor";
                              implode ": "; id_to_string tc])),s)
              | SOME v -> (M_success v,s))
           with
             (M_success (y,z),s) ->
               if LENGTH y = LENGTH ts then
                 (M_success (type_subst (alist_to_fmap (ZIP y ts')) z),s)
               else
                 (M_failure
                    (loc_err_info_loc l,
                     INL (mlstring_concat
                            [implode "Type constructor "; id_to_string tc;
                             implode " given "; num_to_str (LENGTH ts);
                             implode " arguments, but expected ";
                             num_to_str (LENGTH y)])),s)
           | (M_failure x,s) -> (M_failure x,s))
      | (M_failure x,s) -> (M_failure x,s)) /\
   (type_name_check_sub_list l tenvT fvs [] s = (M_success [],s)) /\
   (type_name_check_sub_list l tenvT fvs (CONS t ts) s =
      match type_name_check_sub l tenvT fvs t s with
        (M_success t',s) ->
          (match type_name_check_sub_list l tenvT fvs ts s with
             (M_success ts',s) -> (M_success (CONS t' ts'),s)
           | (M_failure x,s) -> (M_failure x,s))
      | (M_failure x,s) -> (M_failure x,s))`;;
let type_name_check_sub_def = prove
 (CASE_TERM `(type_name_check_sub (l:loc_err_info)
      (tenvT:(mlstring,mlstring,mlstring list#t)namespace) (fvs:mlstring list)
      (Atvar tv) =
      (\s:S. if MEM tv fvs then (M_success (Tvar tv),s)
      else (M_failure (loc_err_info_loc l,INR tv:mlstring+mlstring),s))) /\
   (type_name_check_sub l tenvT fvs (Attup ts) =
      (\s:S. match type_name_check_sub_list l tenvT fvs ts s with
        (M_success ts',s) -> (M_success (Ttup ts'),s)
      | (M_failure x,s) -> (M_failure x,s))) /\
   (type_name_check_sub l tenvT fvs (Atfun t1 t2) =
      (\s:S. match type_name_check_sub l tenvT fvs t1 s with
        (M_success t1',s) ->
          (match type_name_check_sub l tenvT fvs t2 s with
             (M_success t2',s) -> (M_success (Tfn t1' t2'),s)
           | (M_failure x,s) -> (M_failure x,s))
      | (M_failure x,s) -> (M_failure x,s))) /\
   (type_name_check_sub l tenvT fvs (Atapp ts tc) =
      (\s:S. match type_name_check_sub_list l tenvT fvs ts s with
        (M_success ts',s) ->
          (match
             (match nsLookup tenvT tc with
                NONE ->
                  (M_failure
                     (loc_err_info_loc l,
                      INL (mlstring_concat
                             [implode "Undefined "; implode "type constructor";
                              implode ": "; id_to_string tc])),s)
              | SOME v -> (M_success v,s))
           with
             (M_success (y,z),s) ->
               if LENGTH y = LENGTH ts then
                 (M_success (type_subst (alist_to_fmap (ZIP y ts')) z),s)
               else
                 (M_failure
                    (loc_err_info_loc l,
                     INL (mlstring_concat
                            [implode "Type constructor "; id_to_string tc;
                             implode " given "; num_to_str (LENGTH ts);
                             implode " arguments, but expected ";
                             num_to_str (LENGTH y)])),s)
           | (M_failure x,s) -> (M_failure x,s))
      | (M_failure x,s) -> (M_failure x,s))) /\
   (type_name_check_sub_list l tenvT fvs [] =
      (\s:S. (M_success [],s))) /\
   (type_name_check_sub_list l tenvT fvs (CONS t ts) =
      (\s:S. match type_name_check_sub l tenvT fvs t s with
        (M_success t',s) ->
          (match type_name_check_sub_list l tenvT fvs ts s with
             (M_success ts',s) -> (M_success (CONS t' ts'),s)
           | (M_failure x,s) -> (M_failure x,s))
      | (M_failure x,s) -> (M_failure x,s)))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `s:S` THEN
  GEN_REWRITE_TAC LAND_CONV [TYSYS2AUX_type_name_check_sub_curried] THEN
  REWRITE_TAC[]);;
(* error mapping of the sub-form (helper for to_type_name_check_sub)       *)

let TYSYS2AUX_map_err_def = new_definition (CASE_TERM
  `TYSYS2AUX_map_err (f:mlstring->mlstring) (p:(B,locs option#(mlstring+mlstring))exc#S) =
     match p with
       (M_failure (x,INR r),s) -> (M_failure (x,f r):(B,locs option#mlstring)exc,s)
     | (M_failure (x,INL r),s) -> (M_failure (x,r),s)
     | (M_success y,s) -> (M_success y,s)`);;

let TYSYS2AUX_map_err_thms = prove
 (`(!(f:mlstring->mlstring) (y:B) (s:S).
      TYSYS2AUX_map_err f (M_success y,s) = (M_success y,s)) /\
   (!(f:mlstring->mlstring) x r (s:S).
      TYSYS2AUX_map_err f (M_failure (x,INR r):(B,locs option#(mlstring+mlstring))exc,s) =
      (M_failure (x,f r),s)) /\
   (!(f:mlstring->mlstring) x r (s:S).
      TYSYS2AUX_map_err f (M_failure (x,INL r):(B,locs option#(mlstring+mlstring))exc,s) =
      (M_failure (x,r),s))`,
  REWRITE_TAC[TYSYS2AUX_map_err_def; pair_CASE; case_def "exc"; case_def "sum"]);;

let TYSYS2AUX_bind_map_err = prove
 (CASE_TERM `!(f:mlstring->mlstring) (m:S->(A,locs option#(mlstring+mlstring))exc#S)
    (k:A->S->(B,locs option#(mlstring+mlstring))exc#S).
     st_ex_bind (\s. TYSYS2AUX_map_err f (m s)) (\y s. TYSYS2AUX_map_err f (k y s)) =
     (\s. TYSYS2AUX_map_err f
            (match m s with
               (M_success y,s) -> k y s
             | (M_failure x,s) -> (M_failure x,s)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; st_ex_bind_def] THEN
  X_GEN_TAC `s:S` THEN
  MP_TAC(ISPEC `(m:S->(A,locs option#(mlstring+mlstring))exc#S) s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(A,locs option#(mlstring+mlstring))exc`
    (X_CHOOSE_THEN `s1:S` SUBST1_TAC)) THEN
  CASES_ON `r:(A,locs option#(mlstring+mlstring))exc` THEN
  REWRITE_TAC[pair_CASE; case_def "exc"; TYSYS2AUX_map_err_thms] THEN
  MP_TAC(ISPEC `a:locs option#(mlstring+mlstring)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:locs option` (X_CHOOSE_THEN `e:mlstring+mlstring`
    SUBST1_TAC)) THEN
  CASES_ON `e:mlstring+mlstring` THEN
  REWRITE_TAC[TYSYS2AUX_map_err_thms; pair_CASE; case_def "exc"]);;

let TYSYS2AUX_return_map_err = prove
 (`!(f:mlstring->mlstring) (x:B).
     (st_ex_return x:S->(B,locs option#mlstring)exc#S) =
     (\s. TYSYS2AUX_map_err f (M_success x,s))`,
  REWRITE_TAC[FUN_EQ_THM; st_ex_return_def; TYSYS2AUX_map_err_thms]);;

let TYSYS2AUX_CASE_RATOR = prove
 (`(!(p:A#B) (f:A->B->C->D) x. pair_CASE p f x = pair_CASE p (\a b. f a b x)) /\
   (!(o1:A option) (n:C->D) (sf:A->C->D) x.
      option_CASE o1 n sf x = option_CASE o1 (n x) (\a. sf a x)) /\
   (!(e:(A,B)exc) (f:A->C->D) (g:B->C->D) x.
      exc_CASE e f g x = exc_CASE e (\a. f a x) (\b. g b x))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [MP_TAC(ISPEC `p:A#B` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[pair_CASE];
    CASES_ON `o1:A option` THEN REWRITE_TAC[option_CASE];
    CASES_ON `e:(A,B)exc` THEN REWRITE_TAC[case_def "exc"]]);;

let TYSYS2AUX_to_sub_map_err = prove
 (`(!t (l:loc_err_info) (f:mlstring->mlstring)
      (tenvT:(mlstring,mlstring,mlstring list#t)namespace) fvs.
     type_name_check_subst l f tenvT fvs t =
     (\s:S. TYSYS2AUX_map_err f (type_name_check_sub l tenvT fvs t s))) /\
   (!t (l:loc_err_info) (f:mlstring->mlstring)
      (tenvT:(mlstring,mlstring,mlstring list#t)namespace) fvs.
     type_name_check_subst_list l f tenvT fvs t =
     (\s:S. TYSYS2AUX_map_err f (type_name_check_sub_list l tenvT fvs t s)))`,
  MATCH_MP_TAC ast_t_INDUCT THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `s:S` THEN
  REWRITE_TAC[type_name_check_subst_def] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[TYSYS2AUX_type_name_check_sub_curried] THEN
  FIRST
   [REWRITE_TAC[TYSYS2AUX_return_map_err] THEN
    REWRITE_TAC[TYSYS2AUX_bind_map_err] THEN REWRITE_TAC[] THEN NO_TAC;
    REWRITE_TAC[st_ex_return_def; TYSYS2AUX_map_err_thms] THEN NO_TAC;
    REWRITE_TAC[st_ex_bind_def; st_ex_return_def; st_ex_ignore_bind_def; infer_guard_def;
                failwith_def; lookup_st_ex_def] THEN
    REPEAT(CASE_TAC THEN
           ASM_REWRITE_TAC[TYSYS2AUX_map_err_thms; pair_CASE; case_def "exc";
                           case_def "sum"]) THEN NO_TAC;
    REWRITE_TAC[st_ex_bind_def; st_ex_ignore_bind_def; st_ex_return_def; infer_guard_def;
                failwith_def; lookup_st_ex_def; COND_RATOR; TYSYS2AUX_CASE_RATOR] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    MP_TAC(ISPEC `type_name_check_sub_list l tenvT fvs a0 (s:S)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:(t list,locs option#(mlstring+mlstring))exc`
      (X_CHOOSE_THEN `s1:S` SUBST1_TAC)) THEN
    CASES_ON `r:(t list,locs option#(mlstring+mlstring))exc` THEN
    REWRITE_TAC[pair_CASE; case_def "exc"; TYSYS2AUX_map_err_thms] THENL
     [CASES_ON `nsLookup (tenvT:(mlstring,mlstring,mlstring list#t)namespace) a1` THEN
      REWRITE_TAC[option_CASE; pair_CASE; case_def "exc"; TYSYS2AUX_map_err_thms] THEN
      MP_TAC(ISPEC `a':mlstring list#t` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `y:mlstring list` (X_CHOOSE_THEN `z:t` SUBST1_TAC)) THEN
      REWRITE_TAC[pair_CASE] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      COND_CASES_TAC THEN
      REWRITE_TAC[pair_CASE; case_def "exc"; TYSYS2AUX_map_err_thms; num_to_str_def];
      MP_TAC(ISPEC `a:locs option#(mlstring+mlstring)` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `x:locs option` (X_CHOOSE_THEN `e:mlstring+mlstring`
        SUBST1_TAC)) THEN
      CASES_ON `e:mlstring+mlstring` THEN
      REWRITE_TAC[pair_CASE; case_def "exc"; TYSYS2AUX_map_err_thms]]]);;

let to_type_name_check_sub = prove
 (CASE_TERM `(!t (l:loc_err_info) (f:mlstring->mlstring)
      (tenvT:(mlstring,mlstring,mlstring list#t)namespace) fvs.
     type_name_check_subst l f tenvT fvs t =
     (\s:S. match type_name_check_sub l tenvT fvs t s with
              (M_failure (x,INR r),s) -> (M_failure (x,f r),s)
            | (M_failure (x,INL r),s) -> (M_failure (x,r),s)
            | (M_success y,s) -> (M_success y,s))) /\
   (!t (l:loc_err_info) (f:mlstring->mlstring)
      (tenvT:(mlstring,mlstring,mlstring list#t)namespace) fvs.
     type_name_check_subst_list l f tenvT fvs t =
     (\s:S. match type_name_check_sub_list l tenvT fvs t s with
              (M_failure (x,INR r),s) -> (M_failure (x,f r),s)
            | (M_failure (x,INL r),s) -> (M_failure (x,r),s)
            | (M_success y,s) -> (M_success y,s)))`,
  REWRITE_TAC[TYSYS2AUX_to_sub_map_err; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[TYSYS2AUX_map_err_def]);;


let bind_type_name_check_subst = prove
 (CASE_TERM `(!(l:loc_err_info) (f:mlstring->mlstring)
      (tenvT:(mlstring,mlstring,mlstring list#t)namespace) fvs t
      (g:t->S->(B,locs option#mlstring)exc#S).
     st_ex_bind (type_name_check_subst l f tenvT fvs t) g =
     (\s:S. match type_name_check_sub l tenvT fvs t s with
              (M_failure (x,INR r),s) -> (M_failure (x,f r),s)
            | (M_failure (x,INL r),s) -> (M_failure (x,r),s)
            | (M_success y,s) -> g y s)) /\
   (!(l:loc_err_info) (f:mlstring->mlstring)
      (tenvT:(mlstring,mlstring,mlstring list#t)namespace) fvs ts
      (gs:t list->S->(B,locs option#mlstring)exc#S).
     st_ex_bind (type_name_check_subst_list l f tenvT fvs ts) gs =
     (\s:S. match type_name_check_sub_list l tenvT fvs ts s with
              (M_failure (x,INR r),s) -> (M_failure (x,f r),s)
            | (M_failure (x,INL r),s) -> (M_failure (x,r),s)
            | (M_success y,s) -> gs y s))`,
  REWRITE_TAC[TYSYS2AUX_to_sub_map_err; st_ex_bind_def; FUN_EQ_THM] THEN
  REPEAT STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THENL
   [(MP_TAC(ISPEC `type_name_check_sub l tenvT fvs t (x:S)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:(t,locs option#(mlstring+mlstring))exc`
      (X_CHOOSE_THEN `s1:S` SUBST1_TAC)) THEN
    CASES_ON `r:(t,locs option#(mlstring+mlstring))exc` THEN
    REWRITE_TAC[pair_CASE; case_def "exc"; TYSYS2AUX_map_err_thms] THEN
    MP_TAC(ISPEC `a:locs option#(mlstring+mlstring)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `x':locs option` (X_CHOOSE_THEN `e:mlstring+mlstring`
      SUBST1_TAC)) THEN
    CASES_ON `e:mlstring+mlstring` THEN
    REWRITE_TAC[pair_CASE; case_def "exc"; case_def "sum"; TYSYS2AUX_map_err_thms]);
    (MP_TAC(ISPEC `type_name_check_sub_list l tenvT fvs ts (x:S)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:(t list,locs option#(mlstring+mlstring))exc`
      (X_CHOOSE_THEN `s1:S` SUBST1_TAC)) THEN
    CASES_ON `r:(t list,locs option#(mlstring+mlstring))exc` THEN
    REWRITE_TAC[pair_CASE; case_def "exc"; TYSYS2AUX_map_err_thms] THEN
    MP_TAC(ISPEC `a:locs option#(mlstring+mlstring)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `x':locs option` (X_CHOOSE_THEN `e:mlstring+mlstring`
      SUBST1_TAC)) THEN
    CASES_ON `e:mlstring+mlstring` THEN
    REWRITE_TAC[pair_CASE; case_def "exc"; case_def "sum"; TYSYS2AUX_map_err_thms])]);;


let ignore_bind_type_name_check_subst = prove
 (CASE_TERM `(!(l:loc_err_info) (f:mlstring->mlstring)
      (tenvT:(mlstring,mlstring,mlstring list#t)namespace) fvs t
      (g:S->(B,locs option#mlstring)exc#S).
     st_ex_ignore_bind (type_name_check_subst l f tenvT fvs t) g =
     (\s:S. match type_name_check_sub l tenvT fvs t s with
              (M_failure (x,INR r),s) -> (M_failure (x,f r),s)
            | (M_failure (x,INL r),s) -> (M_failure (x,r),s)
            | (M_success y,s) -> g s)) /\
   (!(l:loc_err_info) (f:mlstring->mlstring)
      (tenvT:(mlstring,mlstring,mlstring list#t)namespace) fvs ts
      (gs:S->(B,locs option#mlstring)exc#S).
     st_ex_ignore_bind (type_name_check_subst_list l f tenvT fvs ts) gs =
     (\s:S. match type_name_check_sub_list l tenvT fvs ts s with
              (M_failure (x,INR r),s) -> (M_failure (x,f r),s)
            | (M_failure (x,INL r),s) -> (M_failure (x,r),s)
            | (M_success y,s) -> gs s))`,
  REWRITE_TAC[TYSYS2AUX_to_sub_map_err; st_ex_ignore_bind_def; FUN_EQ_THM] THEN
  REPEAT STRIP_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THENL
   [(MP_TAC(ISPEC `type_name_check_sub l tenvT fvs t (x:S)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:(t,locs option#(mlstring+mlstring))exc`
      (X_CHOOSE_THEN `s1:S` SUBST1_TAC)) THEN
    CASES_ON `r:(t,locs option#(mlstring+mlstring))exc` THEN
    REWRITE_TAC[pair_CASE; case_def "exc"; TYSYS2AUX_map_err_thms] THEN
    MP_TAC(ISPEC `a:locs option#(mlstring+mlstring)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `x':locs option` (X_CHOOSE_THEN `e:mlstring+mlstring`
      SUBST1_TAC)) THEN
    CASES_ON `e:mlstring+mlstring` THEN
    REWRITE_TAC[pair_CASE; case_def "exc"; case_def "sum"; TYSYS2AUX_map_err_thms]);
    (MP_TAC(ISPEC `type_name_check_sub_list l tenvT fvs ts (x:S)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:(t list,locs option#(mlstring+mlstring))exc`
      (X_CHOOSE_THEN `s1:S` SUBST1_TAC)) THEN
    CASES_ON `r:(t list,locs option#(mlstring+mlstring))exc` THEN
    REWRITE_TAC[pair_CASE; case_def "exc"; TYSYS2AUX_map_err_thms] THEN
    MP_TAC(ISPEC `a:locs option#(mlstring+mlstring)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `x':locs option` (X_CHOOSE_THEN `e:mlstring+mlstring`
      SUBST1_TAC)) THEN
    CASES_ON `e:mlstring+mlstring` THEN
    REWRITE_TAC[pair_CASE; case_def "exc"; case_def "sum"; TYSYS2AUX_map_err_thms])]);;

let find_dup_def = cake_def
  `(find_dup ([]:A list) = NONE) /\
   (find_dup (CONS x xs) = if MEM x xs then SOME x else find_dup xs)`;;

let check_dups_def = cake_def
  `(check_dups (l:loc_err_info) (f:A->B) [] =
      (st_ex_return one:S->(1,locs option#B)exc#S)) /\
   (check_dups l f (CONS h t) =
      if MEM h t then failwith l (f h) else check_dups l f t)`;;

let check_dups_eq_find_dup = prove
 (CASE_TERM `!(l:loc_err_info) (f:A->B) (g:S->(C,locs option#B)exc#S) xs.
     st_ex_ignore_bind (check_dups l f xs) g =
     (\s. match find_dup xs with
            NONE -> g s
          | SOME x -> (M_failure (loc_err_info_loc l,f x),s))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[check_dups_def; find_dup_def; option_CASE] THENL
   [REWRITE_TAC[st_ex_ignore_bind_def; st_ex_return_def; FUN_EQ_THM] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE; case_def "exc"] THEN
    REWRITE_TAC[ETA_AX];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[option_CASE] THEN
    REWRITE_TAC[st_ex_ignore_bind_def; failwith_def; FUN_EQ_THM] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE; case_def "exc"]]);;

let check_ctor_types_def = cake_def
  `(check_ctor_types (l:loc_err_info)
      (tenvT:(mlstring,mlstring,mlstring list#t)namespace) (tvs:mlstring list)
      ([]:(mlstring#ast_t list)list) =
      (st_ex_return one:S->(1,locs option#mlstring)exc#S)) /\
   (check_ctor_types l tenvT tvs (CONS (cn,ts) ctors) =
      st_ex_ignore_bind
        (type_name_check_subst_list l
           (\tv. mlstring_concat [implode "Unbound type variable "; tv;
                                  implode " in type definition with constructor ";
                                  cn])
           tenvT tvs ts)
        (check_ctor_types l tenvT tvs ctors))`;;

(* HOL4: check_ctor_types_def |> SRULE [ignore_bind_type_name_check_subst,  *)
(* FUN_EQ_THM, st_ex_return_def]                                            *)

let check_ctor_types_expand = prove
 (CASE_TERM `(!(l:loc_err_info)
      (tenvT:(mlstring,mlstring,mlstring list#t)namespace) (tvs:mlstring list) (s:S).
     check_ctor_types l tenvT tvs [] s = (M_success one,s)) /\
   (!(l:loc_err_info)
      (tenvT:(mlstring,mlstring,mlstring list#t)namespace) (tvs:mlstring list)
      cn ts ctors (s:S).
     check_ctor_types l tenvT tvs (CONS (cn,ts) ctors) s =
     match type_name_check_sub_list l tenvT tvs ts s with
       (M_failure (x,INR r),s) ->
         (M_failure (x,mlstring_concat
                         [implode "Unbound type variable "; r;
                          implode " in type definition with constructor "; cn]),s)
     | (M_failure (x,INL r),s) -> (M_failure (x,r),s)
     | (M_success y,s) -> check_ctor_types l tenvT tvs ctors s)`,
  REWRITE_TAC[check_ctor_types_def; ignore_bind_type_name_check_subst;
              st_ex_return_def] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[]);;

let check_ctors_def = cake_def
  `(check_ctors (l:loc_err_info)
      (tenvT:(mlstring,mlstring,mlstring list#t)namespace)
      ([]:(mlstring list#mlstring#(mlstring#ast_t list)list)list) =
      (st_ex_return one:S->(1,locs option#mlstring)exc#S)) /\
   (check_ctors l tenvT (CONS (tvs,tn,ctors) tds) =
      st_ex_ignore_bind
        (check_dups l
           (\n. mlstring_concat [implode "Duplicate constructor "; n;
                                 implode " in the definition of type "; tn])
           (MAP FST ctors))
      (st_ex_ignore_bind
        (check_dups l
           (\n. mlstring_concat [implode "Duplicate type variable binding "; n;
                                 implode " in the definition of type "; tn])
           tvs)
      (st_ex_ignore_bind (check_ctor_types l tenvT tvs ctors)
        (check_ctors l tenvT tds))))`;;

let check_ctors_expand = prove
 (CASE_TERM `(!(l:loc_err_info)
      (tenvT:(mlstring,mlstring,mlstring list#t)namespace) (s:S).
     check_ctors l tenvT [] s = (M_success one,s)) /\
   (!(l:loc_err_info)
      (tenvT:(mlstring,mlstring,mlstring list#t)namespace) tvs tn ctors tds (s:S).
     check_ctors l tenvT (CONS (tvs,tn,ctors) tds) s =
     match find_dup (MAP FST ctors) with
       NONE ->
         (match find_dup tvs with
            NONE ->
              (match check_ctor_types l tenvT tvs ctors s with
                 (M_success y,s) -> check_ctors l tenvT tds s
               | (M_failure x,s) -> (M_failure x,s))
          | SOME x ->
              (M_failure (loc_err_info_loc l,
                          mlstring_concat [implode "Duplicate type variable binding "; x;
                                           implode " in the definition of type "; tn]),s))
     | SOME x ->
         (M_failure (loc_err_info_loc l,
                     mlstring_concat [implode "Duplicate constructor "; x;
                                      implode " in the definition of type "; tn]),s))`,
  REWRITE_TAC[check_ctors_def; check_dups_eq_find_dup; st_ex_return_def] THEN
  REPEAT GEN_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[st_ex_ignore_bind_def] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[]);;

let check_type_definition_def = cake_def
  `check_type_definition (l:loc_err_info)
     (tenvT:(mlstring,mlstring,mlstring list#t)namespace)
     (tds:(mlstring list#mlstring#(mlstring#ast_t list)list)list) =
     st_ex_ignore_bind
       (check_dups l
          (\n. mlstring_concat [implode "Duplicate type constructor "; n;
                                implode " in a mutually recursive type definition"])
          (MAP (FST o SND) tds))
       (check_ctors l tenvT tds:S->(1,locs option#mlstring)exc#S)`;;

let check_type_definition_expand = prove
 (CASE_TERM `!(l:loc_err_info)
      (tenvT:(mlstring,mlstring,mlstring list#t)namespace)
      (tds:(mlstring list#mlstring#(mlstring#ast_t list)list)list) (s:S).
     check_type_definition l tenvT tds s =
     match find_dup (MAP (FST o SND) tds) with
       NONE -> check_ctors l tenvT tds s
     | SOME x ->
         (M_failure (loc_err_info_loc l,
                     mlstring_concat [implode "Duplicate type constructor "; x;
                                      implode " in a mutually recursive type definition"]),
          s)`,
  REWRITE_TAC[check_type_definition_def; check_dups_eq_find_dup] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[]);;

let infer_p_def = cake_def_wf
  `MEASURE (\x:loc_err_info#inf_env#pat + loc_err_info#inf_env#(pat list).
              match x with INL (_,_,p) -> pat_size p
                         | INR (_,_,ps) -> list_size pat_size ps)`
  TERM_TAC
  `(infer_p (l:loc_err_info) (ienv:inf_env) (Pvar n) =
      st_ex_bind fresh_uvar (\t.
      (st_ex_return (t,[(n,t)]):
         infer_st->(infer_t#(mlstring#infer_t)list,locs option#mlstring)exc#infer_st))) /\
   (infer_p l ienv Pany =
      st_ex_bind fresh_uvar (\t. st_ex_return (t,[]))) /\
   (infer_p l ienv (Plit (IntLit i)) = st_ex_return (Infer_Tapp [] Tint_num,[])) /\
   (infer_p l ienv (Plit (Char c)) = st_ex_return (Infer_Tapp [] Tchar_num,[])) /\
   (infer_p l ienv (Plit (StrLit s)) = st_ex_return (Infer_Tapp [] Tstring_num,[])) /\
   (infer_p l ienv (Plit (Word8 w)) = st_ex_return (Infer_Tapp [] Tword8_num,[])) /\
   (infer_p l ienv (Plit (Word64 w')) = st_ex_return (Infer_Tapp [] Tword64_num,[])) /\
   (infer_p l ienv (Plit (Float64 f)) =
      failwith l (implode "Floats cannot be used in patterns")) /\
   (infer_p l ienv (Pcon cn_opt ps) =
      match cn_opt with
        NONE ->
          st_ex_bind (infer_ps l ienv ps) (\p. match p with
            (ts,tenv) -> st_ex_return (Infer_Tapp ts Ttup_num,tenv))
      | SOME cn ->
          st_ex_bind (lookup_st_ex l (implode "constructor") cn (inf_env_inf_c ienv))
            (\q. match q with
               (tvs',ts,tn) ->
                 st_ex_bind (infer_ps l ienv ps) (\p. match p with
                   (ts'',tenv) ->
                     st_ex_bind (n_fresh_uvar (LENGTH tvs')) (\ts'.
                     st_ex_ignore_bind
                       (infer_guard (LENGTH ts'' = LENGTH ts) l
                          (mlstring_concat
                             [implode "Constructor "; id_to_string cn; implode " given ";
                              toString (&(LENGTH ts''));
                              implode " arguments, but expected ";
                              toString (&(LENGTH ts))]))
                     (st_ex_bind
                        (add_constraints l ts'' (MAP (infer_type_subst (ZIP tvs' ts')) ts))
                        (\u. st_ex_return (Infer_Tapp ts' tn,tenv))))))) /\
   (infer_p l ienv (Pref p) =
      st_ex_bind (infer_p l ienv p) (\q. match q with
        (t,tenv) -> st_ex_return (Infer_Tapp [t] Tref_num,tenv))) /\
   (infer_p l ienv (Pas p v) =
      st_ex_bind (infer_p l ienv p) (\q. match q with
        (t,tenv) -> st_ex_return (t,APPEND tenv [(v,t)]))) /\
   (infer_p l ienv (Ptannot p t) =
      st_ex_bind (infer_p l ienv p) (\q. match q with
        (t',tenv) ->
          st_ex_bind
            (type_name_check_subst l
               (\tv. mlstring_concat [implode "Type variable "; tv;
                                      implode " found in type annotation. ";
                                      implode "Type variables are not supported in type annotations."])
               (inf_env_inf_t ienv) [] t) (\t''.
          st_ex_bind (add_constraint l t' (infer_type_subst [] t'')) (\u.
          st_ex_return (t',tenv))))) /\
   (infer_ps l ienv [] = st_ex_return ([],[])) /\
   (infer_ps l ienv (CONS p ps) =
      st_ex_bind (infer_p l ienv p) (\q. match q with
        (t,tenv) ->
          st_ex_bind (infer_ps l ienv ps) (\r. match r with
            (ts,tenv') -> st_ex_return (CONS t ts,APPEND tenv' tenv))))`;;

let infer_p_ind = cake_ind "infer_p";;

let option_case_rand = prove
 (CASE_TERM `!(x:A option) (y:S->B) (f:A->S->B) s.
     (match x with NONE -> y | SOME a -> f a) s =
     (match x with NONE -> y s | SOME a -> f a s)`,
  REPEAT GEN_TAC THEN CASES_ON `x:A option` THEN REWRITE_TAC[option_CASE]);;

let word_tc_def = cake_def
  `(word_tc W8 = Tword8_num) /\
   (word_tc W64 = Tword64_num)`;;


let op_to_string_def = cake_def
  `(op_to_string (Shift (_:word_size) (_:shift) (_:num)) = (implode "Shift",1)) /\
   (op_to_string Equality = (implode "Equality",2)) /\
   (op_to_string (Arith a ty) =
      (implode "Arith",
       match supported_arith a ty with SOME n -> (n:num) | NONE -> 0)) /\
   (op_to_string (FromTo (_:prim_type) (_:prim_type)) = (implode "FromTo",1)) /\
   (op_to_string (Test (_:test) (_:prim_type)) = (implode "Test",2)) /\
   (op_to_string Opapp = (implode "Opapp",2)) /\
   (op_to_string Opassign = (implode "Opassign",2)) /\
   (op_to_string Opref = (implode "Opref",1)) /\
   (op_to_string Opderef = (implode "Opderef",1)) /\
   (op_to_string Aw8alloc = (implode "Aw8alloc",2)) /\
   (op_to_string Aw8sub = (implode "Aw8sub",2)) /\
   (op_to_string Aw8length = (implode "Aw8length",1)) /\
   (op_to_string Aw8update = (implode "Aw8update",3)) /\
   (op_to_string Aw8sub_unsafe = (implode "Aw8sub_unsafe",2)) /\
   (op_to_string Aw8update_unsafe = (implode "Aw8update_unsafe",3)) /\
   (op_to_string XorAw8Str_unsafe = (implode "XorAw8Str_unsafe",2)) /\
   (op_to_string CopyStrStr = (implode "CopyStrStr",3)) /\
   (op_to_string CopyStrAw8 = (implode "CopyStrAw8",5)) /\
   (op_to_string CopyAw8Str = (implode "CopyAw8Str",3)) /\
   (op_to_string CopyAw8Aw8 = (implode "CopyAw8Aw8",5)) /\
   (op_to_string Strsub = (implode "Strsub",2)) /\
   (op_to_string Implode = (implode "Implode",1)) /\
   (op_to_string Explode = (implode "Explode",1)) /\
   (op_to_string Strlen = (implode "Strlen",1)) /\
   (op_to_string Strcat = (implode "Strcat",1)) /\
   (op_to_string VfromList = (implode "VfromList",1)) /\
   (op_to_string Vsub = (implode "Vsub",2)) /\
   (op_to_string Vsub_unsafe = (implode "Vsub_unsafe",2)) /\
   (op_to_string Vlength = (implode "Vlength",1)) /\
   (op_to_string Aalloc = (implode "Aalloc",2)) /\
   (op_to_string AallocEmpty = (implode "AallocEmpty",1)) /\
   (op_to_string AallocFixed = (implode "AallocFixed",1)) /\
   (op_to_string Asub = (implode "Asub",2)) /\
   (op_to_string Alength = (implode "Alength",1)) /\
   (op_to_string Aupdate = (implode "Aupdate",3)) /\
   (op_to_string Asub_unsafe = (implode "Asub_unsafe",2)) /\
   (op_to_string Aupdate_unsafe = (implode "Aupdate_unsafe",3)) /\
   (op_to_string ConfigGC = (implode "ConfigGC",2)) /\
   (op_to_string Eval = (implode "Eval",6)) /\
   (op_to_string Env_id = (implode "Env_id",1)) /\
   (op_to_string ListAppend = (implode "ListAppend",2)) /\
   (op_to_string (FFI (_:mlstring)) = (implode "FFI",2)) /\
   (op_to_string (ThunkOp ForceThunk) = (implode "ForceThunk",1)) /\
   (op_to_string (ThunkOp (AllocThunk (_:thunk_mode))) = (implode "AllocThunk",1)) /\
   (op_to_string (ThunkOp (UpdateThunk (_:thunk_mode))) = (implode "UpdateThunk",2))`;;

(* HOL4: Overload Tem[local,inferior] = ``Infer_Tapp []`` (written out) *)

let t_num_of_def = cake_def
  `(t_num_of BoolT = Tbool_num) /\
   (t_num_of IntT = Tint_num) /\
   (t_num_of CharT = Tchar_num) /\
   (t_num_of StrT = Tstring_num) /\
   (t_num_of (WordT W8) = Tword8_num) /\
   (t_num_of (WordT W64) = Tword64_num) /\
   (t_num_of Float64T = Tdouble_num)`;;
let _ = cake_add_simps [t_num_of_def];;

let op_simple_constraints_def = cake_def
  `op_simple_constraints (op:op) =
     match op with
       Arith a ty ->
         (match supported_arith a ty with
            NONE -> (F,[],Infer_Tapp [] Tbool_num)
          | SOME arity ->
              (T,REPLICATE arity (Infer_Tapp [] (t_num_of ty)),
               Infer_Tapp [] (t_num_of ty)))
     | FromTo ty1 ty2 ->
         (supported_conversion ty1 ty2,[Infer_Tapp [] (t_num_of ty1)],
          Infer_Tapp [] (t_num_of ty2))
     | Test test ty ->
         (supported_test test ty,
          [Infer_Tapp [] (t_num_of ty); Infer_Tapp [] (t_num_of ty)],
          Infer_Tapp [] Tbool_num)
     | Shift wz _ _ -> (T,[Infer_Tapp [] (word_tc wz)],Infer_Tapp [] (word_tc wz))
     | Aw8alloc ->
         (T,[Infer_Tapp [] Tint_num; Infer_Tapp [] Tword8_num],
          Infer_Tapp [] Tword8array_num)
     | Aw8sub ->
         (T,[Infer_Tapp [] Tword8array_num; Infer_Tapp [] Tint_num],
          Infer_Tapp [] Tword8_num)
     | Aw8length -> (T,[Infer_Tapp [] Tword8array_num],Infer_Tapp [] Tint_num)
     | Aw8update ->
         (T,[Infer_Tapp [] Tword8array_num; Infer_Tapp [] Tint_num;
             Infer_Tapp [] Tword8_num],
          Infer_Tapp [] Ttup_num)
     | CopyStrStr ->
         (T,[Infer_Tapp [] Tstring_num; Infer_Tapp [] Tint_num; Infer_Tapp [] Tint_num],
          Infer_Tapp [] Tstring_num)
     | CopyStrAw8 ->
         (T,[Infer_Tapp [] Tstring_num; Infer_Tapp [] Tint_num; Infer_Tapp [] Tint_num;
             Infer_Tapp [] Tword8array_num; Infer_Tapp [] Tint_num],
          Infer_Tapp [] Ttup_num)
     | CopyAw8Str ->
         (T,[Infer_Tapp [] Tword8array_num; Infer_Tapp [] Tint_num;
             Infer_Tapp [] Tint_num],
          Infer_Tapp [] Tstring_num)
     | CopyAw8Aw8 ->
         (T,[Infer_Tapp [] Tword8array_num; Infer_Tapp [] Tint_num; Infer_Tapp [] Tint_num;
             Infer_Tapp [] Tword8array_num; Infer_Tapp [] Tint_num],
          Infer_Tapp [] Ttup_num)
     | Strsub ->
         (T,[Infer_Tapp [] Tstring_num; Infer_Tapp [] Tint_num],Infer_Tapp [] Tchar_num)
     | Strlen -> (T,[Infer_Tapp [] Tstring_num],Infer_Tapp [] Tint_num)
     | ConfigGC ->
         (T,[Infer_Tapp [] Tint_num; Infer_Tapp [] Tint_num],Infer_Tapp [] Ttup_num)
     | FFI _ ->
         (T,[Infer_Tapp [] Tstring_num; Infer_Tapp [] Tword8array_num],
          Infer_Tapp [] Ttup_num)
     | Implode ->
         (T,[Infer_Tapp [Infer_Tapp [] Tchar_num] Tlist_num],Infer_Tapp [] Tstring_num)
     | Explode ->
         (T,[Infer_Tapp [] Tstring_num],
          Infer_Tapp [Infer_Tapp [] Tchar_num] Tlist_num)
     | Strcat ->
         (T,[Infer_Tapp [Infer_Tapp [] Tstring_num] Tlist_num],Infer_Tapp [] Tstring_num)
     | _ -> (F,[],Infer_Tapp [] Tbool_num)`;;

let op_n_args_msg_def = cake_def
  `op_n_args_msg (op:op) (n:num) =
     let (ops,args) = op_to_string op in
     mlstring_concat [implode "Primitive "; ops; implode " given ";
                      toString (&n); implode " arguments, but expects ";
                      toString (&args)]`;;

let constrain_op_def = cake_def
  `constrain_op (l:loc_err_info) (op:op) (ts:infer_t list) (s:infer_st) =
     let (simple,op_arg_ts,op_ret_t) = op_simple_constraints op in
     if simple then
       if ~(LENGTH ts = LENGTH op_arg_ts)
       then failwith l (op_n_args_msg op (LENGTH ts)) s
       else st_ex_bind (add_constraints l ts (MAP I op_arg_ts)) (\u.
            st_ex_return op_ret_t) s
     else
       match (op,ts) with
         (Equality,[t1; t2]) ->
           st_ex_bind (add_constraint l t1 t2) (\u.
           st_ex_return (Infer_Tapp [] Tbool_num)) s
       | (Opapp,[t1; t2]) ->
           st_ex_bind fresh_uvar (\uvar.
           st_ex_bind (add_constraint l t1 (Infer_Tapp [t2; uvar] Tfn_num)) (\u.
           st_ex_return uvar)) s
       | (Opassign,[t1; t2]) ->
           st_ex_bind (add_constraint l t1 (Infer_Tapp [t2] Tref_num)) (\u.
           st_ex_return (Infer_Tapp [] Ttup_num)) s
       | (Opref,[t]) -> st_ex_return (Infer_Tapp [t] Tref_num) s
       | (Opderef,[t]) ->
           st_ex_bind fresh_uvar (\uvar.
           st_ex_bind (add_constraint l t (Infer_Tapp [uvar] Tref_num)) (\u.
           st_ex_return uvar)) s
       | (VfromList,[t]) ->
           st_ex_bind fresh_uvar (\uvar.
           st_ex_bind (add_constraint l t (Infer_Tapp [uvar] Tlist_num)) (\u.
           st_ex_return (Infer_Tapp [uvar] Tvector_num))) s
       | (Vsub,[t1; t2]) ->
           st_ex_bind fresh_uvar (\uvar.
           st_ex_bind (add_constraint l t1 (Infer_Tapp [uvar] Tvector_num)) (\u.
           st_ex_bind (add_constraint l t2 (Infer_Tapp [] Tint_num)) (\u.
           st_ex_return uvar))) s
       | (Vlength,[t]) ->
           st_ex_bind fresh_uvar (\uvar.
           st_ex_bind (add_constraint l t (Infer_Tapp [uvar] Tvector_num)) (\u.
           st_ex_return (Infer_Tapp [] Tint_num))) s
       | (Aalloc,[t1; t2]) ->
           st_ex_bind (add_constraint l t1 (Infer_Tapp [] Tint_num)) (\u.
           st_ex_return (Infer_Tapp [t2] Tarray_num)) s
       | (AallocEmpty,[t1]) ->
           st_ex_bind fresh_uvar (\uvar.
           st_ex_bind (add_constraint l t1 (Infer_Tapp [] Ttup_num)) (\u.
           st_ex_return (Infer_Tapp [uvar] Tarray_num))) s
       | (Asub,[t1; t2]) ->
           st_ex_bind fresh_uvar (\uvar.
           st_ex_bind (add_constraint l t1 (Infer_Tapp [uvar] Tarray_num)) (\u.
           st_ex_bind (add_constraint l t2 (Infer_Tapp [] Tint_num)) (\u.
           st_ex_return uvar))) s
       | (Alength,[t]) ->
           st_ex_bind fresh_uvar (\uvar.
           st_ex_bind (add_constraint l t (Infer_Tapp [uvar] Tarray_num)) (\u.
           st_ex_return (Infer_Tapp [] Tint_num))) s
       | (Aupdate,[t1; t2; t3]) ->
           st_ex_bind (add_constraint l t1 (Infer_Tapp [t3] Tarray_num)) (\u.
           st_ex_bind (add_constraint l t2 (Infer_Tapp [] Tint_num)) (\u.
           st_ex_return (Infer_Tapp [] Ttup_num))) s
       | (ListAppend,[t1; t2]) ->
           st_ex_bind fresh_uvar (\uvar.
           st_ex_bind (add_constraint l t1 (Infer_Tapp [uvar] Tlist_num)) (\u.
           st_ex_bind (add_constraint l t2 (Infer_Tapp [uvar] Tlist_num)) (\u.
           st_ex_return (Infer_Tapp [uvar] Tlist_num)))) s
       | (Vsub_unsafe,_) -> failwith l (implode "Unsafe ops do not have a type") s
       | (Asub_unsafe,_) -> failwith l (implode "Unsafe ops do not have a type") s
       | (Aupdate_unsafe,_) -> failwith l (implode "Unsafe ops do not have a type") s
       | (Aw8sub_unsafe,_) -> failwith l (implode "Unsafe ops do not have a type") s
       | (Aw8update_unsafe,_) -> failwith l (implode "Unsafe ops do not have a type") s
       | (XorAw8Str_unsafe,_) -> failwith l (implode "Unsafe ops do not have a type") s
       | (AallocFixed,_) -> failwith l (implode "Unsafe ops do not have a type") s
       | (Eval,_) -> failwith l (implode "Unsafe ops do not have a type") s
       | (Env_id,_) -> failwith l (implode "Unsafe ops do not have a type") s
       | (ThunkOp _,_) -> failwith l (implode "Thunk ops do not have a type") s
       | (Arith _ _,_) -> failwith l (implode "Type mismatch") s
       | (FromTo _ _,_) -> failwith l (implode "Type mismatch") s
       | (Test _ _,_) -> failwith l (implode "Type mismatch") s
       | _ -> failwith l (op_n_args_msg op (LENGTH ts)) s`;;

let st_ex_bind_failure = prove
 (`!(f:S->(A,E)exc#S) (g:A->S->(B,E)exc#S) s r s'.
     st_ex_bind f g s = (M_failure r,s') <=>
     f s = (M_failure r,s') \/
     (?x st. f s = (M_success x,st) /\ g x st = (M_failure r,s'))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[st_ex_bind_def] THEN
  MP_TAC(ISPEC `(f:S->(A,E)exc#S) s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(A,E)exc` (X_CHOOSE_THEN `s1:S` SUBST1_TAC)) THEN
  CASES_ON `q:(A,E)exc` THEN
  REWRITE_TAC[pair_CASE; case_def "exc"; PAIR_EQ; injectivity "exc";
              distinctness "exc"] THEN
  MESON_TAC[]);;

(* helpers for constrain_op_error_msg_sanity *)

let TYSYS2AUX_add_constraint_fail = prove
 (`!(l:loc_err_info) t1 t2 s l' msg s'.
     add_constraint l t1 t2 s = (M_failure (l',msg),s')
     ==> IS_PREFIX (explode msg) "Type mismatch"`,
  REPEAT GEN_TAC THEN REWRITE_TAC[add_constraint_def] THEN
  CASES_ON `t_unify (infer_st_subst s) t1 t2` THEN
  REWRITE_TAC[option_CASE; PAIR_EQ; injectivity "exc"; distinctness "exc"] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o CONJUNCT2 o REWRITE_RULE[PAIR_EQ])
    (K ALL_TAC)) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[concat_thm; explode_thm; MAP; FLAT; APPEND; IS_PREFIX_DEF;
              GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[isPREFIX; APPEND; list_CASE]);;

let TYSYS2AUX_add_constraints_fail = prove
 (`!ts1 ts2 (l:loc_err_info) s l' msg s'.
     LENGTH ts1 = LENGTH ts2 /\
     add_constraints l ts1 ts2 s = (M_failure (l',msg),s')
     ==> IS_PREFIX (explode msg) "Type mismatch"`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; add_constraints_def; st_ex_return_def;
              PAIR_EQ; distinctness "exc"] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[st_ex_bind_failure; st_ex_return_def; PAIR_EQ; distinctness "exc"] THEN
  STRIP_TAC THENL
   [ASM_MESON_TAC[TYSYS2AUX_add_constraint_fail];
    ASM_MESON_TAC[]]);;

let TYSYS2AUX_add_constraints_fail' = prove
 (`!ts1 ts2 (l:loc_err_info) s l' msg s'.
     add_constraints l ts1 ts2 s = (M_failure (l',msg),s')
     ==> LENGTH ts1 = LENGTH ts2 ==> IS_PREFIX (explode msg) "Type mismatch"`,
  MESON_TAC[TYSYS2AUX_add_constraints_fail]);;
let TYSYS2AUX_LENGTH_EQ_NUM = prove
 (`(!l:A list. LENGTH l = 0 <=> l = []) /\
   (!l:A list. LENGTH l = 1 <=> ?a. l = [a]) /\
   (!l:A list. LENGTH l = 2 <=> ?a b. l = [a; b]) /\
   (!l:A list. LENGTH l = 3 <=> ?a b c. l = [a; b; c]) /\
   (!l:A list. LENGTH l = 5 <=> ?a b c d e. l = [a; b; c; d; e]) /\
   (!l:A list. LENGTH l = 6 <=> ?a b c d e f. l = [a; b; c; d; e; f])`,
  REWRITE_TAC[LENGTH_EQ_NIL; num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`;
              num_CONV `2`; num_CONV `1`; LENGTH_EQ_CONS] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[CONS_11] THEN MESON_TAC[]);;

let TYSYS2AUX_SANITY_TAC =
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[TYSYS2AUX_LENGTH_EQ_NUM] th) ORELSE
               ASSUME_TAC th) MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[LENGTH; MAP; I_THM] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[failwith_def] THEN
  REPEAT(CHANGED_TAC(REWRITE_TAC[st_ex_bind_failure; fresh_uvar_def; st_ex_return_def;
                                 PAIR_EQ; injectivity "exc"; distinctness "exc"] THEN
                     CONV_TAC(DEPTH_CONV BETA_CONV))) THEN
  REPEAT STRIP_TAC THEN
  FIRST
   [REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
    REWRITE_TAC[explode_thm; IS_PREFIX_DEF; isPREFIX; list_CASE] THEN NO_TAC;
    FIRST_X_ASSUM(MP_TAC o MATCH_MP TYSYS2AUX_add_constraint_fail) THEN SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP TYSYS2AUX_add_constraints_fail') THEN
    ASM_REWRITE_TAC[LENGTH; LENGTH_MAP; LENGTH_REPLICATE] THEN SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[LENGTH_REPLICATE; LENGTH_MAP]];;
let TYSYS2AUX_SPLIT_ARITH_TAC : tactic = fun (asl,w as g) ->
  let is_sa t = try fst(dest_const(fst(strip_comb t))) = "supported_arith" &&
                    length(snd(strip_comb t)) = 2 with Failure _ -> false in
  match find_terms is_sa w with
    t::_ -> (CASES_ON t THEN ASM_REWRITE_TAC[option_CASE; pair_CASE]) g
  | [] -> ALL_TAC g;;
let constrain_op_error_msg_sanity = prove
 (`!(l:loc_err_info) op args s l' s' msg.
     LENGTH args = SND (op_to_string op) /\
     constrain_op l op args s = (M_failure (l',msg),s')
     ==> IS_PREFIX (explode msg) "Type mismatch" \/
         IS_PREFIX (explode msg) "Unsafe" \/
         IS_PREFIX (explode msg) "Thunk"`,
  REPEAT GEN_TAC THEN CASES_ON `op:op` THEN
  REWRITE_TAC[op_to_string_def; SND] THEN
  REWRITE_TAC[constrain_op_def; op_simple_constraints_def] THEN
  CASE_REWRITE_TAC[] THEN TYSYS2AUX_SPLIT_ARITH_TAC THEN TYSYS2AUX_SANITY_TAC);;

(* defined with sem1aux_def_wf (semantics/sem1aux_tfl.ml): the kit's        *)
(* casewise recursion package needs a very long time for the 25 clauses of  *)
(* the four functions                                                        *)

let infer_e_def = sem1aux_def_wf
  `MEASURE (\x:loc_err_info#inf_env#exp +
                loc_err_info#inf_env#(exp list) +
                loc_err_info#inf_env#((pat#exp)list)#infer_t#infer_t +
                loc_err_info#inf_env#((varN#varN#exp)list).
              match x with
                INL (_,_,e) -> exp_size e
              | INR (INL (_,_,es)) -> list_size exp_size es
              | INR (INR (INL (_,_,pes,_,_))) ->
                  list_size (pair_size pat_size exp_size) pes
              | INR (INR (INR (_,_,funs))) ->
                  list_size (pair_size mlstring_size
                               (pair_size mlstring_size exp_size)) funs)`
  SEM1AUX_TC_TAC
  `(infer_e (l:loc_err_info) (ienv:inf_env) (Raise e) =
      st_ex_bind (infer_e l ienv e) (\t2.
      st_ex_bind (add_constraint l t2 (Infer_Tapp [] Texn_num)) (\u.
      st_ex_bind fresh_uvar (\t1.
      st_ex_return t1)))) /\
   (infer_e l ienv (Handle e pes) =
      if pes = [] then failwith l (implode "No patterns in handle")
      else
        st_ex_bind (infer_e l ienv e) (\t1.
        st_ex_bind (infer_pes l ienv pes (Infer_Tapp [] Texn_num) t1) (\u.
        st_ex_return t1))) /\
   (infer_e l ienv (Lit (IntLit i)) = st_ex_return (Infer_Tapp [] Tint_num)) /\
   (infer_e l ienv (Lit (Char c)) = st_ex_return (Infer_Tapp [] Tchar_num)) /\
   (infer_e l ienv (Lit (StrLit s)) = st_ex_return (Infer_Tapp [] Tstring_num)) /\
   (infer_e l ienv (Lit (Word8 w)) = st_ex_return (Infer_Tapp [] Tword8_num)) /\
   (infer_e l ienv (Lit (Word64 _)) = st_ex_return (Infer_Tapp [] Tword64_num)) /\
   (infer_e l ienv (Lit (Float64 _)) = st_ex_return (Infer_Tapp [] Tdouble_num)) /\
   (infer_e l ienv (Var id) =
      st_ex_bind (lookup_st_ex l (implode "variable") id (inf_env_inf_v ienv))
        (\p. match p with
           (tvs,t) ->
             st_ex_bind (n_fresh_uvar tvs) (\uvs.
             st_ex_return (infer_deBruijn_subst uvs t)))) /\
   (infer_e l ienv (Con cn_opt es) =
      match cn_opt with
        NONE ->
          st_ex_bind (infer_es l ienv es) (\ts.
          st_ex_return (Infer_Tapp ts Ttup_num))
      | SOME cn ->
          st_ex_bind (lookup_st_ex l (implode "constructor") cn (inf_env_inf_c ienv))
            (\q. match q with
               (tvs',ts,tn) ->
                 st_ex_bind (infer_es l ienv es) (\ts''.
                 st_ex_bind (n_fresh_uvar (LENGTH tvs')) (\ts'.
                 st_ex_ignore_bind
                   (infer_guard (LENGTH ts'' = LENGTH ts) l
                      (mlstring_concat
                         [implode "Constructor "; id_to_string cn; implode " given ";
                          toString (&(LENGTH ts''));
                          implode " arguments, but expected ";
                          toString (&(LENGTH ts))]))
                 (st_ex_bind
                    (add_constraints l ts'' (MAP (infer_type_subst (ZIP tvs' ts')) ts))
                    (\u. st_ex_return (Infer_Tapp ts' tn))))))) /\
   (infer_e l ienv (Fun x e) =
      st_ex_bind fresh_uvar (\t1.
      st_ex_bind
        (infer_e l (inf_env_inf_v_fupd (K (nsBind x (0,t1) (inf_env_inf_v ienv))) ienv) e)
        (\t2. st_ex_return (Infer_Tapp [t1; t2] Tfn_num)))) /\
   (infer_e l ienv (App op es) =
      st_ex_bind (infer_es l ienv es) (\ts.
      st_ex_bind (constrain_op l op ts) (\t.
      st_ex_return t))) /\
   (infer_e l ienv (Log lop e1 e2) =
      st_ex_bind (infer_e l ienv e1) (\t1.
      st_ex_bind (infer_e l ienv e2) (\t2.
      st_ex_bind (add_constraint l t1 (Infer_Tapp [] Tbool_num)) (\u.
      st_ex_bind (add_constraint l t2 (Infer_Tapp [] Tbool_num)) (\u.
      st_ex_return (Infer_Tapp [] Tbool_num)))))) /\
   (infer_e l ienv (If e1 e2 e3) =
      st_ex_bind (infer_e l ienv e1) (\t1.
      st_ex_bind (add_constraint l t1 (Infer_Tapp [] Tbool_num)) (\u.
      st_ex_bind (infer_e l ienv e2) (\t2.
      st_ex_bind (infer_e l ienv e3) (\t3.
      st_ex_bind (add_constraint l t2 t3) (\u.
      st_ex_return t2)))))) /\
   (infer_e l ienv (Mat e pes) =
      if pes = [] then failwith l (implode "No patterns in case")
      else
        st_ex_bind (infer_e l ienv e) (\t1.
        st_ex_bind fresh_uvar (\t2.
        st_ex_bind (infer_pes l ienv pes t1 t2) (\u.
        st_ex_return t2)))) /\
   (infer_e l ienv (Let xo e1 e2) =
      st_ex_bind (infer_e l ienv e1) (\t1.
      st_ex_bind
        (infer_e l (inf_env_inf_v_fupd (K (nsOptBind xo (0,t1) (inf_env_inf_v ienv))) ienv)
           e2)
        (\t2. st_ex_return t2))) /\
   (infer_e l ienv (Letrec funs e) =
      st_ex_ignore_bind
        (check_dups l
           (\n. mlstring_concat [implode "Duplicate function name "; n;
                                 implode " in mutually recursive function definition"])
           (MAP FST funs))
      (st_ex_bind (n_fresh_uvar (LENGTH funs)) (\uvars.
       st_ex_bind
         (st_ex_return
            (nsAppend
               (alist_to_ns
                  (MAP2 (\fxe uvar. match fxe with (f,x,e) -> (f,(0,uvar))) funs uvars))
               (inf_env_inf_v ienv)))
         (\env'.
       st_ex_bind (infer_funs l (inf_env_inf_v_fupd (K env') ienv) funs) (\funs_ts.
       st_ex_bind (add_constraints l uvars funs_ts) (\u.
       st_ex_bind (infer_e l (inf_env_inf_v_fupd (K env') ienv) e) (\t.
       st_ex_return t))))))) /\
   (infer_e l ienv (Tannot e t) =
      st_ex_bind (infer_e l ienv e) (\t'.
      st_ex_bind
        (type_name_check_subst l
           (\tv. mlstring_concat [implode "Type variable "; tv;
                                  implode " found in type annotation. ";
                                  implode "Type variables are not supported in type annotations."])
           (inf_env_inf_t ienv) [] t) (\t''.
      st_ex_bind (add_constraint l t' (infer_type_subst [] t'')) (\u.
      st_ex_return t')))) /\
   (infer_e l ienv (Lannot e new_l) =
      infer_e (loc_err_info_loc_fupd (K (SOME new_l)) l) ienv e) /\
   (infer_es l ienv [] = st_ex_return []) /\
   (infer_es l ienv (CONS e es) =
      st_ex_bind (infer_e l ienv e) (\t.
      st_ex_bind (infer_es l ienv es) (\ts.
      st_ex_return (CONS t ts)))) /\
   (infer_pes l ienv [] t1 t2 = st_ex_return one) /\
   (infer_pes l ienv (CONS (p,e) pes) t1 t2 =
      st_ex_bind (infer_p l ienv p) (\q. match q with
        (t1',env') ->
          st_ex_ignore_bind
            (check_dups l
               (\n. mlstring_concat [implode "Duplicate variable "; n;
                                     implode " in pattern"])
               (MAP FST env'))
          (st_ex_bind (add_constraint l t1 t1') (\u.
           st_ex_bind
             (infer_e l
                (inf_env_inf_v_fupd
                   (K (nsAppend
                         (alist_to_ns (MAP (\nt. match nt with (n,t) -> (n,(0,t))) env'))
                         (inf_env_inf_v ienv))) ienv) e)
             (\t2'.
           st_ex_bind (add_constraint l t2 t2') (\u.
           st_ex_bind (infer_pes l ienv pes t1 t2) (\u.
           st_ex_return one))))))) /\
   (infer_funs l ienv [] = st_ex_return []) /\
   (infer_funs l ienv (CONS (f,x,e) funs) =
      st_ex_bind fresh_uvar (\uvar.
      st_ex_bind
        (infer_e l (inf_env_inf_v_fupd (K (nsBind x (0,uvar) (inf_env_inf_v ienv))) ienv) e)
        (\t.
      st_ex_bind (infer_funs l ienv funs) (\ts.
      st_ex_return (CONS (Infer_Tapp [uvar; t] Tfn_num) ts)))))`;;

let infer_e_ind = cake_ind "infer_e";;

let FUN_EQ_THM_state = prove
 (`!(f:S->B) g. f = g <=> !s. f s = g s`,
  REWRITE_TAC[FUN_EQ_THM]);;

let extend_dec_ienv_def = cake_def
  `extend_dec_ienv (ienv':inf_env) (ienv:inf_env) =
     inf_env_REC (nsAppend (inf_env_inf_v ienv') (inf_env_inf_v ienv))
                 (nsAppend (inf_env_inf_c ienv') (inf_env_inf_c ienv))
                 (nsAppend (inf_env_inf_t ienv') (inf_env_inf_t ienv))`;;

let lift_ienv_def = cake_def
  `lift_ienv (mn:mlstring) (ienv:inf_env) =
     inf_env_REC (nsLift mn (inf_env_inf_v ienv))
                 (nsLift mn (inf_env_inf_c ienv))
                 (nsLift mn (inf_env_inf_t ienv))`;;

(* HOL4's bound variable num_tvs (in Dlet) is the name of typeSystem's      *)
(* constant num_tvs: written ntvs                                           *)

let infer_d_def = sem1aux_def_wf
  `MEASURE (\x:inf_env#dec + inf_env#(dec list).
              match x with INL (_,d) -> dec_size d
                         | INR (_,ds) -> list_size dec_size ds)`
  SEM1AUX_TC_TAC
  `(infer_d (ienv:inf_env) (Dlet locs p e) =
      st_ex_bind init_state (\u.
      st_ex_bind get_next_uvar (\n.
      st_ex_bind (infer_e (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)) ienv e)
        (\t1.
      st_ex_bind (infer_p (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)) ienv p)
        (\q. match q with
           (t2,env') ->
             st_ex_ignore_bind
               (check_dups (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv))
                  (\n. mlstring_concat [implode "Duplicate variable "; n;
                                        implode " in the left-hand side of a definition"])
                  (MAP FST env'))
             (st_ex_bind
                (add_constraint (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)) t1 t2)
                (\u.
              st_ex_bind (apply_subst_list (MAP SND env')) (\ts.
              st_ex_bind (st_ex_return (generalise_list n 0 FEMPTY ts)) (\r.
                match r with
                  (ntvs,s,ts') ->
                    st_ex_bind
                      (infer_guard (ntvs = 0 \/ is_value e)
                         (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv))
                         (implode "Value restriction violated"))
                      (\u.
                    st_ex_return
                      (inf_env_REC
                         (alist_to_ns (ZIP (MAP FST env') (MAP (\t. (ntvs,t)) ts')))
                         nsEmpty nsEmpty))))))))))) /\
   (infer_d ienv (Dletrec locs funs) =
      st_ex_ignore_bind
        (check_dups (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv))
           (\n. mlstring_concat [implode "Duplicate function name "; n;
                                 implode " a mutually recursive function definition"])
           (MAP FST funs))
      (st_ex_bind init_state (\u.
       st_ex_bind get_next_uvar (\next.
       st_ex_bind (n_fresh_uvar (LENGTH funs)) (\uvars.
       st_ex_bind
         (st_ex_return
            (nsAppend
               (alist_to_ns
                  (MAP2 (\fxe uvar. match fxe with (f,x,e) -> (f,(0,uvar))) funs uvars))
               (inf_env_inf_v ienv)))
         (\env'.
       st_ex_bind
         (infer_funs (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv))
            (inf_env_inf_v_fupd (K env') ienv) funs) (\funs_ts.
       st_ex_bind
         (add_constraints (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv)) uvars funs_ts)
         (\u.
       st_ex_bind (apply_subst_list uvars) (\ts.
       st_ex_bind (st_ex_return (generalise_list next 0 FEMPTY ts)) (\r.
         match r with
           (num_gen,s,ts') ->
             st_ex_return
               (inf_env_REC
                  (alist_to_ns
                     (MAP2 (\fxe t. match fxe with (f,x,e) -> (f,(num_gen,t))) funs ts'))
                  nsEmpty nsEmpty))))))))))) /\
   (infer_d ienv (Dtype locs tdefs) =
      st_ex_bind (n_fresh_id (LENGTH tdefs)) (\tids.
      st_ex_bind
        (st_ex_return
           (alist_to_ns
              (MAP2 (\tvtnc i. match tvtnc with
                       (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i)))
                    tdefs tids)))
        (\ienvT1.
      st_ex_bind (st_ex_return (nsAppend ienvT1 (inf_env_inf_t ienv))) (\ienvT2.
      st_ex_ignore_bind
        (check_type_definition (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv))
           ienvT2 tdefs)
        (st_ex_return
           (inf_env_REC nsEmpty (build_ctor_tenv ienvT2 tdefs tids) ienvT1)))))) /\
   (infer_d ienv (Dtabbrev locs tvs tn t) =
      st_ex_ignore_bind
        (check_dups (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv))
           (\n. mlstring_concat [implode "Duplicate type variable bindings for "; n;
                                 implode " in type abbreviation "; tn])
           tvs)
      (st_ex_bind
         (type_name_check_subst (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv))
            (\tv. mlstring_concat [implode "Unbound type variable "; tv;
                                   implode " in type abbreviation "; tn])
            (inf_env_inf_t ienv) tvs t)
         (\t'. st_ex_return (inf_env_REC nsEmpty nsEmpty (nsSing tn (tvs,t')))))) /\
   (infer_d ienv (Dexn locs cn ts) =
      st_ex_bind
        (type_name_check_subst_list (loc_err_info_REC (SOME locs) (inf_env_inf_t ienv))
           (\tv. mlstring_concat [implode "Type variable "; tv;
                                  implode " found in declaration of exception "; cn;
                                  implode ". Type variables are not allowed in exception declarations."])
           (inf_env_inf_t ienv) [] ts)
        (\ts'. st_ex_return (inf_env_REC nsEmpty (nsSing cn ([],ts',Texn_num)) nsEmpty))) /\
   (infer_d ienv (Denv n) =
      failwith (loc_err_info_REC NONE (inf_env_inf_t ienv))
        (implode "Env declaration (Denv) is not supported.")) /\
   (infer_d ienv (Dmod mn ds) =
      st_ex_bind (infer_ds ienv ds) (\ienv'.
      st_ex_return (lift_ienv mn ienv'))) /\
   (infer_d ienv (Dlocal lds ds) =
      st_ex_bind (infer_ds ienv lds) (\ienv'.
      infer_ds (extend_dec_ienv ienv' ienv) ds)) /\
   (infer_ds ienv [] = st_ex_return (inf_env_REC nsEmpty nsEmpty nsEmpty)) /\
   (infer_ds ienv (CONS d ds) =
      st_ex_bind (infer_d ienv d) (\ienv'.
      st_ex_bind (infer_ds (extend_dec_ienv ienv' ienv) ds) (\ienv''.
      st_ex_return (extend_dec_ienv ienv'' ienv'))))`;;

let infer_d_ind = cake_ind "infer_d";;

(* The starting Id should be greater than Tlist_num :: (Tbool_num ::        *)
(* prim_type_nums).  HOL4 defines it as the value of an EVAL of             *)
(* FOLDR MAX 0 (Tlist_num :: Tbool_num :: prim_type_nums) + 1, which is 15  *)
(* (TYSYS2AUX_start_type_id_eval).                                          *)

let start_type_id_def = cake_def
  `start_type_id = 15`;;

let TYSYS2AUX_start_type_id_eval = prove
 (`start_type_id =
   ITLIST MAX (CONS Tlist_num (CONS Tbool_num prim_type_nums)) 0 + 1`,
  REWRITE_TAC[start_type_id_def; prim_type_nums_def; ITLIST;
              typeSystem_Tarray_num_def; typeSystem_Tbool_num_def;
              typeSystem_Tchar_num_def; typeSystem_Texn_num_def;
              typeSystem_Tfn_num_def; typeSystem_Tint_num_def;
              typeSystem_Tlist_num_def; typeSystem_Tref_num_def;
              typeSystem_Tstring_num_def; typeSystem_Ttup_num_def;
              typeSystem_Tvector_num_def; typeSystem_Tword64_num_def;
              typeSystem_Tword8_num_def; typeSystem_Tword8array_num_def;
              typeSystem_Tdouble_num_def; MAX] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let infertype_prog_def = cake_def
  `infertype_prog (ienv:inf_env) prog =
     match FST (infer_ds ienv prog
                  (init_infer_state (infer_st_REC 0 FEMPTY start_type_id))) with
       M_success new_ienv -> M_success (extend_dec_ienv new_ienv ienv)
     | M_failure x -> (M_failure x:(inf_env,locs option#mlstring)exc)`;;

(* HOL4's partial record literal <| next_id := next_id |> is              *)
(* infer_st_next_id_fupd (K next_id) ARB                                    *)

let infertype_prog_inc_def = cake_def
  `infertype_prog_inc (ienv:inf_env,next_id:num) prog =
     match infer_ds ienv prog
             (init_infer_state (infer_st_next_id_fupd (K next_id) ARB)) with
       (M_success new_ienv,st) ->
         M_success (extend_dec_ienv new_ienv ienv,infer_st_next_id st)
     | (M_failure x,_) -> (M_failure x:(inf_env#num,locs option#mlstring)exc)`;;

let infer_init_config_def = cake_def
  `infer_init_config =
     inf_env_REC nsEmpty (type_env_c prim_tenv) (type_env_t prim_tenv)`;;

(* The following aren't needed to run the inferencer, but are useful in the *)
(* proofs about it                                                          *)

let infer_deBruijn_inc_def = cake_def
  `(infer_deBruijn_inc (n:num) (Infer_Tvar_db m) = Infer_Tvar_db (m + n)) /\
   (infer_deBruijn_inc n (Infer_Tapp ts tn) =
      Infer_Tapp (MAP (infer_deBruijn_inc n) ts) tn) /\
   (infer_deBruijn_inc n (Infer_Tuvar m) = Infer_Tuvar m)`;;

let infer_deBruijn_inc_ind = cake_ind "infer_deBruijn_inc";;

let infer_subst_def = cake_def
  `(infer_subst (s:(num,num)fmap) (Infer_Tvar_db n) = Infer_Tvar_db n) /\
   (infer_subst s (Infer_Tapp ts tc) = Infer_Tapp (MAP (infer_subst s) ts) tc) /\
   (infer_subst s (Infer_Tuvar n) =
      match FLOOKUP s n with
        NONE -> Infer_Tuvar n
      | SOME m -> Infer_Tvar_db m)`;;

let infer_subst_ind = cake_ind "infer_subst";;

let pure_add_constraints_def = cake_def
  `(pure_add_constraints (s:(num,infer_t)fmap) [] s' <=> s = s') /\
   (pure_add_constraints s1 (CONS (t1,t2) rest) s' <=>
      ?s2. t_unify s1 t1 t2 = SOME s2 /\ pure_add_constraints s2 rest s')`;;

let check_t_def = cake_def
  `(check_t (n:num) (uvars:num->bool) (Infer_Tuvar v) <=> v IN uvars) /\
   (check_t n uvars (Infer_Tvar_db n') <=> n' < n) /\
   (check_t n uvars (Infer_Tapp ts tc) <=> ALL (check_t n uvars) ts)`;;

let check_t_ind = cake_ind "check_t";;

let ienv_val_ok_def = cake_def
  `ienv_val_ok (uvars:num->bool) (env:(mlstring,mlstring,num#infer_t)namespace) <=>
     nsAll (\x p. match p with (tvs,t) -> check_t tvs uvars t) env`;;

let check_s_def = cake_def
  `check_s (tvs:num) (uvs:num->bool) (s:(num,infer_t)fmap) <=>
     !uv. uv IN FDOM s ==> check_t tvs uvs (FAPPLY s uv)`;;

(* Adding the constraints extra_constraints moves the constraint set from  *)
(* s1 to s2, and s2 is required to be complete in that it assigns to (at   *)
(* least) all the uvars <= next_uvar, and when we apply it to any uvar, we *)
(* get back a type without any uvars in it.                                 *)

let sub_completion_def = cake_def
  `sub_completion (tvs:num) (next_uvar:num) (s1:(num,infer_t)fmap)
                  extra_constraints s2 <=>
     pure_add_constraints s1 extra_constraints s2 /\
     pred_set_count next_uvar SUBSET FDOM s2 /\
     (!uv. uv IN FDOM s2 ==> check_t tvs {} (t_walkstar s2 (Infer_Tuvar uv)))`;;

(* printing of types *)

let alist_nub_def = cake_def_wf
  `MEASURE (\l:(A#B)list. LENGTH l)`
  (REWRITE_TAC[measure_THM; LENGTH] THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC(ARITH_RULE `m <= n ==> m < SUC n`) THEN
   REWRITE_TAC[LENGTH_FILTER])
  `(alist_nub ([]:(A#B)list) = []) /\
   (alist_nub (CONS (x,y) xs) =
      CONS (x,y) (alist_nub (FILTER (\t. ~(x = FST t)) xs)))`;;

let alist_nub_ind = cake_ind "alist_nub";;

let ns_nub_def = cake_def
  `(ns_nub (Bind xs ys:(A,B,C)namespace) =
      Bind (alist_nub xs) (alist_nub (inner_ns_nubs ys))) /\
   (inner_ns_nubs [] = []) /\
   (inner_ns_nubs (CONS (x,y) tl) = CONS (x,ns_nub y) (inner_ns_nubs tl))`;;

let ns_nub_ind = cake_ind "ns_nub";;

let ns_to_alist_def = cake_def_clauses
  [`ns_to_alist (Bind [] [] :(mlstring,mlstring,V)namespace) = []:(mlstring#V)list`;
   `(ns_to_alist (Bind [] (CONS (n,x) ms) :(mlstring,mlstring,V)namespace)
      :(mlstring#V)list) =
      APPEND (MAP (\p. match p with (x,y) -> (strcat (strcat n (implode ".")) x,y))
                  (ns_to_alist x))
             (ns_to_alist (Bind [] ms))`;
   `(ns_to_alist (Bind (CONS (s,x) xs) m :(mlstring,mlstring,V)namespace)
      :(mlstring#V)list) =
      CONS (s,x) (ns_to_alist (Bind xs m))`];;

let ns_to_alist_ind = cake_ind "ns_to_alist";;

let inf_env_to_types_string_def = cake_def
  `inf_env_to_types_string (s:inf_env) =
     let l = ns_to_alist (ns_nub (inf_env_inf_v s)) in
     let xs = MAP (\p. match p with
                         (n,_,t) -> mlstring_concat [n; implode ": ";
                                                     inf_type_to_string (inf_env_inf_t s) t;
                                                     implode "\n"]) l in
     REVERSE xs`;;
