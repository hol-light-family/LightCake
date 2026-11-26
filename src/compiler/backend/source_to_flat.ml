(* ========================================================================= *)
(* source_to_flat: port of HOL4 compiler/backend/source_to_flatScript.sml    *)
(* (CakeML v3479).                                                           *)
(* This is the compiler phase that translates the CakeML source language     *)
(* into flatLang.                                                            *)
(*                                                                           *)
(* The translator to flatLang keeps two mappings, one mapping module paths  *)
(* to indices into the genv, and the other mapping module paths to          *)
(* constructor ids.  All variable references are replaced with global       *)
(* references to the genv index if they are in the mappings.  This includes *)
(* top-level letrec names which are all put into the mapping before         *)
(* translating any of the let rec functions.  This enables the semantics of *)
(* let rec to just create Closures rather than Recclosures.                 *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's traces None and Cons are backend_common_None and                 *)
(*   backend_common_Cons, mlstring literals are implode "...", FOLDR f e l  *)
(*   is ITLIST f l e, EXISTS is EX; records are cake_record types (literals *)
(*   rec_REC in field order, r with f := x is rec_f_fupd (K x) r).          *)
(* - HOL4's ast$pat1_size (the size of a pattern list) is list_size         *)
(*   pat_size.                                                               *)
(* - A clause variable whose name HOL4 uses with two types in one           *)
(*   definition gets a second name: Var xid, the found variable vn and the  *)
(*   compiled list ce ces of compile_exp; in compile_decs the Glob trace gt, *)
(*   the types tds of Dtype and the type ty of Dtabbrev; the unused first   *)
(*   result of compile_decs in compile_prog and inc_compile_prog is n0.     *)
(* - type_group_id_type_ind is HOL4's induction theorem (a case split).     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "compiler/backend/flatLang.ml";;
needs "semantics/evaluate.ml";;
needs "compiler/backend/flat_elim.ml";;
needs "compiler/backend/flat_pattern.ml";;
needs "hol4/sptree.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

let var_name_INDUCT,var_name_RECURSION = cake_type
  "var_name = Glob tra num | source_to_flat_Local tra mlstring";;

let source_to_flat_environment_INFO = cake_record "source_to_flat_environment"
  ["c","(modN,conN,ctor_id#type_group_id)namespace";
   "v","(modN,varN,var_name)namespace"];;

let environment_generation_store_INFO = cake_record "environment_generation_store"
  ["next","num";
   "generation","num";
   "envs","source_to_flat_environment spt"];;

let environment_store_INFO = cake_record "environment_store"
  ["next","num";
   "env_gens","(source_to_flat_environment spt) spt"];;

let compile_var_def = cake_def
  `(compile_var t (Glob _ i) = flat_App t (GlobalVarLookup i) []) /\
   (compile_var t (source_to_flat_Local _ s) = Var_local t s)`;;

(* HOL4 ast$pat1_size is list_size pat_size *)

let ast_pat1_size = prove
 (`!xs. list_size ast_pat_size xs = LENGTH xs + SUM (MAP ast_pat_size xs)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[list_size; LENGTH; MAP; SUM] THEN
  ARITH_TAC);;

let compile_pat_def = cake_def_wf
  `MEASURE ((ast_pat_size o SND):source_to_flat_environment # pat -> num)`
  (REWRITE_TAC(WF_REL_THMS @ [o_THM; SND]) THEN REPEAT STRIP_TAC THEN
   (TERM_TAC ORELSE
    (REWRITE_TAC[type_size_def "pat"] THEN ASM_ARITH_TAC)))
  `(compile_pat env (Pvar v) = flat_Pvar v) /\
   (compile_pat env Pany = flat_Pany) /\
   (compile_pat env (Plit l) = flat_Plit l) /\
   (compile_pat env (Pcon id ps) =
      flat_Pcon
        (OPTION_JOIN (OPTION_MAP (nsLookup (source_to_flat_environment_c env)) id))
        (MAP (compile_pat env) ps)) /\
   (compile_pat env (Pref p) = flat_Pref (compile_pat env p)) /\
   (compile_pat env (Pas p i) = flat_Pas (compile_pat env p) i) /\
   (compile_pat env (Ptannot p t) = compile_pat env p)`;;

let compile_pat_ind = cake_ind "compile_pat";;

let pat_tups_def = cake_def
  `(pat_tups t [] = []) /\
   (pat_tups t (CONS x xs) =
      let t' = mk_cons t (LENGTH xs + 1) in
      CONS (x, source_to_flat_Local t' x) (pat_tups t xs))`;;

let astOp_to_flatOp_def = cake_def
  `astOp_to_flatOp (opn:op) : flat_op =
     match opn with
       Opderef -> flat_El 0
     | _ -> Src opn`;;

let type_group_id_type_def = cake_def
  `(type_group_id_type (NONE:(num # (num # (num # num) list) option) option) = NONE) /\
   (type_group_id_type (SOME (cn, NONE)) = SOME (cn, NONE)) /\
   (type_group_id_type (SOME (cn, (SOME (ty_id, ctors)))) = SOME (cn, SOME ty_id))`;;

let type_group_id_type_ind = prove
 (`!P. P NONE /\ (!cn. P (SOME (cn,NONE))) /\
       (!cn ty_id ctors. P (SOME (cn,SOME (ty_id,ctors))))
       ==> !v:(num # (num # (num # num) list) option) option. P v`,
  GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `v:(num # (num # (num # num) list) option) option`
                      (nchotomy_of_type `:(num # (num # (num # num) list) option) option`)) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT IL1AUX_SPLIT_TAC THEN ASM_REWRITE_TAC[]);;

let type_group_id_type_MAP = prove
 (`type_group_id_type = OPTION_MAP (I ## OPTION_MAP FST)`,
  REWRITE_TAC[FUN_EQ_THM] THEN MATCH_MP_TAC type_group_id_type_ind THEN
  REWRITE_TAC[type_group_id_type_def; OPTION_MAP_DEF; PAIR_MAP_THM; I_THM]);;

let str_sep_def = cake_def
  `str_sep = implode "_"`;;

let join_all_names_aux_def = cake_def
  `(join_all_names_aux [] ys = ys) /\
   (join_all_names_aux (CONS x xs) ys =
      match ys with
        [] -> join_all_names_aux xs (CONS x ys)
      | _ -> join_all_names_aux xs (CONS x (CONS str_sep ys)))`;;

let join_all_names_def = cake_def
  `join_all_names xs =
     match xs with
       [x] -> x
     | _ -> mlstring_concat (join_all_names_aux xs [])`;;

let source_to_flat_compile_exp_def = sem1aux_def_wf
  `inv_image (<)
     (\x:(mlstring list # source_to_flat_environment # exp) +
         (mlstring list # source_to_flat_environment # exp list) +
         (mlstring list # source_to_flat_environment # (pat # exp) list) +
         (mlstring list # source_to_flat_environment # (varN # varN # exp) list).
        sum_CASE x (\p. exp_size (SND (SND p)))
          (\y. sum_CASE y (\p. list_size exp_size (SND (SND p)))
                 (\z. sum_CASE z
                        (\p. list_size (pair_size ast_pat_size exp_size) (SND (SND p)))
                        (\p. list_size (pair_size mlstring_size
                                          (pair_size mlstring_size exp_size))
                                       (SND (SND p))))))`
  SEM1AUX_TC_TAC
  `(source_to_flat_compile_exp (t:mlstring list) (env:source_to_flat_environment)
      (Raise e) =
      flat_Raise backend_common_None (source_to_flat_compile_exp t env e)) /\
   (source_to_flat_compile_exp t env (Handle e pes) =
      flat_Handle backend_common_None (source_to_flat_compile_exp t env e)
        (compile_pes t env pes)) /\
   (source_to_flat_compile_exp t env (Lit l) = flat_Lit backend_common_None l) /\
   (source_to_flat_compile_exp t env (Con cn es) =
      flat_Con backend_common_None
        (OPTION_JOIN (OPTION_MAP (type_group_id_type o
                                  nsLookup (source_to_flat_environment_c env)) cn))
        (source_to_flat_compile_exps t env es)) /\
   (source_to_flat_compile_exp t env (Var xid) =
      match nsLookup (source_to_flat_environment_v env) xid with
        NONE -> Var_local backend_common_None (implode "")
      | SOME vn -> compile_var backend_common_None vn) /\
   (source_to_flat_compile_exp t env (Fun x e) =
      flat_Fun (join_all_names t) x
        (source_to_flat_compile_exp t
           (source_to_flat_environment_v_fupd
              (combin_K (nsBind x (source_to_flat_Local backend_common_None x)
                    (source_to_flat_environment_v env))) env) e)) /\
   (source_to_flat_compile_exp t env (App opn es) =
      if opn = AallocEmpty then
        ITLIST (flat_Let backend_common_None NONE)
          (REVERSE (source_to_flat_compile_exps t env es))
          (flat_App backend_common_None (Src Aalloc)
             [flat_Lit backend_common_None (IntLit (&0));
              flat_Lit backend_common_None (IntLit (&0))])
      else if opn = Eval then
        flat_Mat backend_common_None
          (flat_Con backend_common_None NONE (source_to_flat_compile_exps t env es))
          [(flat_Pcon NONE [flat_Pany; flat_Pany; flat_Pany; flat_Pany;
                            flat_Pvar (implode "bytes"); flat_Pvar (implode "words")],
            flat_Let backend_common_None NONE
              (flat_App backend_common_None (Src Eval)
                 (MAP (Var_local backend_common_None)
                      [implode "bytes"; implode "words"]))
              (flat_Let backend_common_None (SOME (implode "r"))
                 (flat_App backend_common_None (GlobalVarLookup 0) [])
                 (flat_App backend_common_None (flat_El 0)
                    [Var_local backend_common_None (implode "r")])))]
      else if opn = Env_id then
        (match es with
           [_] -> (match source_to_flat_compile_exps t env es with
                     CONS ce ces -> ce
                   | _ -> Var_local backend_common_None (implode ""))
         | _ -> flat_App backend_common_None (flat_El 0)
                  (source_to_flat_compile_exps t env es))
      else
        flat_App backend_common_None (astOp_to_flatOp opn)
          (source_to_flat_compile_exps t env es)) /\
   (source_to_flat_compile_exp t env (Log lop e1 e2) =
      match lop with
        Andalso ->
          flat_If backend_common_None
            (source_to_flat_compile_exp t env e1)
            (source_to_flat_compile_exp t env e2)
            (flat_Bool backend_common_None F)
      | Orelse ->
          flat_If backend_common_None
            (source_to_flat_compile_exp t env e1)
            (flat_Bool backend_common_None T)
            (source_to_flat_compile_exp t env e2)) /\
   (source_to_flat_compile_exp t env (If e1 e2 e3) =
      flat_If backend_common_None
        (source_to_flat_compile_exp t env e1)
        (source_to_flat_compile_exp t env e2)
        (source_to_flat_compile_exp t env e3)) /\
   (source_to_flat_compile_exp t env (Mat e pes) =
      flat_Mat backend_common_None (source_to_flat_compile_exp t env e)
        (compile_pes t env pes)) /\
   (source_to_flat_compile_exp t env (Let (SOME x) e1 e2) =
      flat_Let backend_common_None (SOME x)
        (source_to_flat_compile_exp (CONS x t) env e1)
        (source_to_flat_compile_exp t
           (source_to_flat_environment_v_fupd
              (combin_K (nsBind x (source_to_flat_Local backend_common_None x)
                    (source_to_flat_environment_v env))) env) e2)) /\
   (source_to_flat_compile_exp t env (Let NONE e1 e2) =
      flat_Let backend_common_None NONE
        (source_to_flat_compile_exp t env e1)
        (source_to_flat_compile_exp t env e2)) /\
   (source_to_flat_compile_exp t env (Letrec funs e) =
      let fun_names = MAP FST funs in
      let new_env = nsBindList (MAP (\x. (x, source_to_flat_Local backend_common_None x))
                                    fun_names)
                               (source_to_flat_environment_v env) in
      flat_Letrec (join_all_names t)
        (compile_funs t (source_to_flat_environment_v_fupd (combin_K new_env) env) funs)
        (source_to_flat_compile_exp t
           (source_to_flat_environment_v_fupd (combin_K new_env) env) e)) /\
   (source_to_flat_compile_exp t env (Tannot e _) =
      source_to_flat_compile_exp t env e) /\
   (source_to_flat_compile_exp t env (Lannot e (Locs st en)) =
      source_to_flat_compile_exp t env e) /\
   (source_to_flat_compile_exps t env [] = []) /\
   (source_to_flat_compile_exps t env (CONS e es) =
      CONS (source_to_flat_compile_exp t env e)
           (source_to_flat_compile_exps t env es)) /\
   (compile_pes t env [] = []) /\
   (compile_pes t env (CONS (p,e) pes) =
      let pbs = pat_bindings p in
      let pts = pat_tups backend_common_None pbs in
      CONS (compile_pat env p,
            source_to_flat_compile_exp t
              (source_to_flat_environment_v_fupd
                 (combin_K (nsBindList pts (source_to_flat_environment_v env))) env) e)
           (compile_pes t env pes)) /\
   (compile_funs t env [] = []) /\
   (compile_funs t env (CONS (f,x,e) funs) =
      CONS (f, x,
            source_to_flat_compile_exp (CONS f t)
              (source_to_flat_environment_v_fupd
                 (combin_K (nsBind x (source_to_flat_Local backend_common_None x)
                       (source_to_flat_environment_v env))) env) e)
           (compile_funs t env funs))`;;

let source_to_flat_compile_exp_ind = cake_ind "source_to_flat_compile_exp";;

let compile_exps_append = prove
 (`!env es es'.
     source_to_flat_compile_exps t env (APPEND es es') =
     APPEND (source_to_flat_compile_exps t env es)
            (source_to_flat_compile_exps t env es')`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; source_to_flat_compile_exp_def]);;

let compile_exps_reverse = prove
 (`!env es.
     source_to_flat_compile_exps t env (REVERSE es) =
     REVERSE (source_to_flat_compile_exps t env es)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REVERSE; source_to_flat_compile_exp_def; compile_exps_append;
                  APPEND]);;

let compile_funs_map = prove
 (`!env funs.
     compile_funs t env funs =
     MAP (\(f,x,e). (f,x,source_to_flat_compile_exp (CONS f t)
                           (source_to_flat_environment_v_fupd
                              (combin_K (nsBind x (source_to_flat_Local backend_common_None x)
                                    (source_to_flat_environment_v env))) env) e))
         funs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; source_to_flat_compile_exp_def] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`h:varN # varN # exp`,`h:varN # varN # exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; source_to_flat_compile_exp_def] THEN
  SIMP_TAC[CONS_11]);;

let compile_funs_dom = prove
 (`!funs. MAP (\(x,y,z). x) funs =
          MAP (\(x,y,z). x) (compile_funs t env funs)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; source_to_flat_compile_exp_def] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`h:varN # varN # exp`,`h:varN # varN # exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; source_to_flat_compile_exp_def; MAP] THEN
  SIMP_TAC[CONS_11]);;

let om_tra_def = cake_def
  `om_tra = backend_common_Cons orphan_trace 1`;;

let alloc_defs_def = cake_def
  `(alloc_defs n next [] = []:(A # var_name) list) /\
   (alloc_defs n next (CONS (x:A) xs) =
      CONS (x, Glob om_tra next) (alloc_defs (n + 1) (next + 1) xs))`;;

let fst_alloc_defs = prove
 (`!n next (l:A list). MAP FST (alloc_defs n next l) = l`,
  SUBGOAL_THEN `!(l:A list) n next. MAP FST (alloc_defs n next l) = l`
    (fun th -> REWRITE_TAC[th]) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[alloc_defs_def; MAP]);;

let alloc_defs_append = prove
 (`!m n (l1:A list) l2.
     alloc_defs m n (APPEND l1 l2) =
     APPEND (alloc_defs m n l1) (alloc_defs (m + LENGTH l1) (n + LENGTH l1) l2)`,
  SUBGOAL_THEN `!(l1:A list) m n l2.
     alloc_defs m n (APPEND l1 l2) =
     APPEND (alloc_defs m n l1) (alloc_defs (m + LENGTH l1) (n + LENGTH l1) l2)`
    (fun th -> REWRITE_TAC[th]) THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; alloc_defs_def; LENGTH; ADD_CLAUSES] THEN
  REWRITE_TAC[ADD1; ADD_AC]);;

let make_varls_def = cake_def
  `(make_varls n t idx [] = flat_Con backend_common_None NONE []) /\
   (make_varls n t idx [x] =
      flat_App backend_common_None (GlobalVarInit idx)
        [Var_local backend_common_None x]) /\
   (make_varls n (t:tra) idx (CONS x xs) =
      (flat_Let backend_common_None NONE
         (flat_App backend_common_None (GlobalVarInit idx)
            [Var_local backend_common_None x])
         (make_varls (n + 1) backend_common_None (idx + 1) xs):flat_exp))`;;

let make_varls_ind = cake_ind "make_varls";;

let source_to_flat_empty_env_def = cake_def
  `source_to_flat_empty_env = source_to_flat_environment_REC nsEmpty nsEmpty`;;

let extend_env_def = cake_def
  `extend_env e1 e2 =
     source_to_flat_environment_REC
       (nsAppend (source_to_flat_environment_c e1) (source_to_flat_environment_c e2))
       (nsAppend (source_to_flat_environment_v e1) (source_to_flat_environment_v e2))`;;

let lift_env_def = cake_def
  `lift_env mn e =
     source_to_flat_environment_REC
       (nsLift mn (source_to_flat_environment_c e))
       (nsLift mn (source_to_flat_environment_v e))`;;

let next_indices_INFO = cake_record "next_indices"
  ["vidx","num"; "tidx","num"; "eidx","num"];;

let lookup_inc_def = cake_def
  `lookup_inc i t =
     match lookup i t with
       NONE -> (0, insert i 1 t)
     | SOME n -> (n, insert i (n + 1) t)`;;

let alloc_tags1_def = cake_def
  `(alloc_tags1 [] = ((nsEmpty:(modN,conN,num)namespace), (LN:num spt), []:(num # num) list)) /\
   (alloc_tags1 (CONS (cn, ts:ast_t list) ctors) =
      let (ns, cids, tag_list) = alloc_tags1 ctors in
      let arity = LENGTH ts in
      let (tag, new_cids) = lookup_inc arity cids in
      (nsBind cn tag ns, new_cids, CONS (tag, arity) tag_list))`;;

let alloc_tags1_ind = cake_ind "alloc_tags1";;

let alloc_tags_def = cake_def
  `alloc_tags (tid:num) ctors =
     let (con_ns, cid_spt, tag_list) = alloc_tags1 (REVERSE ctors) in
     let data = SOME (tid, REVERSE tag_list) in
     (nsMap (\tag. (tag, data)) con_ns, cid_spt)`;;

let env_id_tuple_def = cake_def
  `env_id_tuple gen id =
     flat_Con backend_common_None NONE
       [flat_Lit backend_common_None (IntLit (&gen));
        flat_Lit backend_common_None (IntLit (&id))]`;;

let simple_dlet_def = cake_def
  `simple_dlet p e =
     match p with
       Pvar pv -> (match e with Var v -> SOME (pv,v) | _ -> NONE)
     | _ -> NONE`;;

let source_to_flat_compile_decs_def = sem1aux_def_wf
  `MEASURE ((list_size dec_size o SND o SND o SND o SND o SND):
            mlstring list # num # next_indices # source_to_flat_environment #
            environment_generation_store # dec list -> num)`
  (SEM1AUX_TC_TAC ORELSE
   (REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    RVEQ_TAC THEN REWRITE_TAC(WF_REL_THMS @ [o_THM; FST; SND]) THEN
    REWRITE_TAC[list_size; type_size_def "dec"] THEN
    REWRITE_TAC(size_aux_eqs "dec") THEN ARITH_TAC))
  `(source_to_flat_compile_decs (t:mlstring list) n next env envs [Dlet locs p e] =
      match simple_dlet p e with
        SOME (pv,v) ->
          (match nsLookup (source_to_flat_environment_v env) v with
             SOME (Glob gt i) ->
               (n, next,
                source_to_flat_environment_REC nsEmpty
                  (alist_to_ns [(pv, Glob gt i)]),
                envs, [])
           | _ -> (n, next, source_to_flat_environment_REC nsEmpty nsEmpty, envs, []))
      | NONE ->
          let n' = n + 4 in
          let xs = REVERSE (pat_bindings p) in
          let e' = source_to_flat_compile_exp (APPEND xs t) env e in
          let l = LENGTH xs in
          let n'' = n' + l in
          (n'', next_indices_vidx_fupd (combin_K (next_indices_vidx next + l)) next,
           source_to_flat_environment_REC nsEmpty
             (alist_to_ns (alloc_defs n' (next_indices_vidx next) xs)),
           envs,
           [flat_Mat backend_common_None e'
              [(compile_pat env p,
                make_varls 0 backend_common_None (next_indices_vidx next) xs)]])) /\
   (source_to_flat_compile_decs t n next env envs [Dletrec locs funs] =
      let fun_names = MAP FST funs in
      let new_env = nsBindList (MAP (\x. (x, source_to_flat_Local backend_common_None x))
                                    fun_names)
                               (source_to_flat_environment_v env) in
      let flat_funs = compile_funs t (source_to_flat_environment_v_fupd (combin_K new_env) env)
                        funs in
      let n' = n + 1 in
      let env' = source_to_flat_environment_REC nsEmpty
                   (alist_to_ns (alloc_defs n' (next_indices_vidx next)
                                   (REVERSE fun_names))) in
      (n' + LENGTH funs,
       next_indices_vidx_fupd (combin_K (next_indices_vidx next + LENGTH funs)) next,
       env', envs,
       [flat_Letrec (join_all_names t) flat_funs
          (make_varls 0 backend_common_None (next_indices_vidx next)
             (REVERSE fun_names))])) /\
   (source_to_flat_compile_decs t n next env envs [Dtype locs tds] =
      let new_env = MAPi (\tid (a,b,constrs). alloc_tags (next_indices_tidx next + tid)
                                                constrs) tds in
      (n, next_indices_tidx_fupd (combin_K (next_indices_tidx next + LENGTH tds)) next,
       source_to_flat_environment_REC
         (FOLDL (\ns (l,cids). nsAppend l ns) nsEmpty new_env) nsEmpty,
       envs, [])) /\
   (source_to_flat_compile_decs t n next env envs [Dtabbrev locs tvs tn ty] =
      (n, next, source_to_flat_empty_env, envs, [])) /\
   (source_to_flat_compile_decs t n next env envs [Dexn locs cn ts] =
      (n, next_indices_eidx_fupd (combin_K (next_indices_eidx next + 1)) next,
       source_to_flat_environment_REC (nsSing cn (next_indices_eidx next, NONE))
         nsEmpty,
       envs, [])) /\
   (source_to_flat_compile_decs t n next env envs [Dmod mn ds] =
      let (n', next', new_env, envs', ds') =
        source_to_flat_compile_decs (CONS mn t) n next env envs ds in
      (n', next', lift_env mn new_env, envs', ds')) /\
   (source_to_flat_compile_decs t n next env envs [Dlocal lds ds] =
      let (n', next1, new_env1, envs', lds') =
        source_to_flat_compile_decs t n next env envs lds in
      let (n'', next2, new_env2, envs'', ds') =
        source_to_flat_compile_decs t n' next1 (extend_env new_env1 env) envs' ds in
      (n'', next2, new_env2, envs'', APPEND lds' ds')) /\
   (source_to_flat_compile_decs t n next env envs [Denv nenv] =
      (n + 1, next_indices_vidx_fupd (combin_K (next_indices_vidx next + 1)) next,
       source_to_flat_environment_REC nsEmpty
         (nsBind nenv (Glob backend_common_None (next_indices_vidx next)) nsEmpty),
       environment_generation_store_envs_fupd
         (combin_K (insert (environment_generation_store_next envs) env
                    (environment_generation_store_envs envs)))
         (environment_generation_store_next_fupd
            (combin_K (environment_generation_store_next envs + 1)) envs),
       [flat_App backend_common_None (GlobalVarInit (next_indices_vidx next))
          [env_id_tuple (environment_generation_store_generation envs)
                        (environment_generation_store_next envs)]])) /\
   (source_to_flat_compile_decs t n next env envs [] =
      (n, next, source_to_flat_empty_env, envs, [])) /\
   (source_to_flat_compile_decs t n next env envs (CONS d ds) =
      let (n', next1, new_env1, envs1, d') =
        source_to_flat_compile_decs t n next env envs [d] in
      let (n'', next2, new_env2, envs2, ds') =
        source_to_flat_compile_decs t n' next1 (extend_env new_env1 env) envs1 ds in
      (n'', next2, extend_env new_env2 new_env1, envs2, APPEND d' ds'))`;;

let source_to_flat_compile_decs_ind = cake_ind "source_to_flat_compile_decs";;

let source_to_flat_config_INFO = cake_record "source_to_flat_config"
  ["next","next_indices";
   "mod_env","source_to_flat_environment";
   "pattern_cfg","flat_pattern_config";
   "envs","environment_store"];;

let empty_config_def = cake_def
  `empty_config =
     source_to_flat_config_REC (next_indices_REC 0 0 0) source_to_flat_empty_env
       (flat_pattern_init_config 0) (environment_store_REC 0 LN)`;;

let compile_flat_def = cake_def
  `compile_flat pcfg = MAP (compile_dec pcfg) o remove_flat_prog`;;

let glob_alloc_def = cake_def
  `glob_alloc next c =
     flat_Let om_tra NONE
       (flat_App om_tra
          (GlobalVarAlloc (next_indices_vidx next -
                           next_indices_vidx (source_to_flat_config_next c))) [])
       (flat_Con om_tra NONE [])`;;

let alloc_env_ref_def = cake_def
  `alloc_env_ref =
     flat_App backend_common_None (GlobalVarInit 0)
       [flat_App backend_common_None (Src Opref) [flat_Con backend_common_None NONE []]]`;;

let source_to_flat_compile_prog_def = cake_def
  `source_to_flat_compile_prog c p =
     let next = next_indices_vidx_fupd
                  (combin_K (next_indices_vidx (source_to_flat_config_next c) + 1))
                  (source_to_flat_config_next c) in
     let envs = environment_generation_store_REC 0
                  (environment_store_next (source_to_flat_config_envs c)) LN in
     let (n0,next,e,gen,p') =
       source_to_flat_compile_decs [] 1 next (source_to_flat_config_mod_env c) envs p in
     let envs2 = environment_store_REC
                   (environment_store_next (source_to_flat_config_envs c) + 1)
                   (insert (environment_store_next (source_to_flat_config_envs c))
                      (environment_generation_store_envs gen)
                      (environment_store_env_gens (source_to_flat_config_envs c))) in
     (source_to_flat_config_next_fupd (combin_K next)
        (source_to_flat_config_envs_fupd (combin_K envs2)
           (source_to_flat_config_mod_env_fupd (combin_K e) c)),
      CONS (glob_alloc next c) (CONS alloc_env_ref p'))`;;

let lookup_env_id_def = cake_def
  `lookup_env_id env_id envs =
     match lookup (FST env_id) (environment_store_env_gens envs) with
       NONE -> source_to_flat_empty_env
     | SOME gen -> (match lookup (SND env_id) gen with
                      NONE -> source_to_flat_empty_env
                    | SOME env -> env)`;;

let store_env_id_def = cake_def
  `store_env_id gen id =
     flat_Let backend_common_None (SOME (implode "r"))
       (flat_App backend_common_None (GlobalVarLookup 0) [])
       (flat_App backend_common_None (Src Opassign)
          [Var_local backend_common_None (implode "r"); env_id_tuple gen id])`;;

let inc_compile_prog_def = cake_def
  `inc_compile_prog env_id c p =
     let env = lookup_env_id env_id (source_to_flat_config_envs c) in
     let envs = environment_generation_store_REC 0
                  (environment_store_next (source_to_flat_config_envs c)) LN in
     let (n0,next,e,gen,p') =
       source_to_flat_compile_decs [] 1 (source_to_flat_config_next c) env envs p in
     let gen_envs = insert (environment_generation_store_next gen) (extend_env e env)
                      (environment_generation_store_envs gen) in
     let envs2 = environment_store_REC
                   (environment_store_next (source_to_flat_config_envs c) + 1)
                   (insert (environment_store_next (source_to_flat_config_envs c))
                      gen_envs
                      (environment_store_env_gens (source_to_flat_config_envs c))) in
     (source_to_flat_config_next_fupd (combin_K next)
        (source_to_flat_config_envs_fupd (combin_K envs2) c),
      CONS (glob_alloc next c)
        (APPEND p' [store_env_id (environment_generation_store_generation gen)
                                 (environment_generation_store_next gen)]))`;;

let source_to_flat_compile_def = cake_def
  `source_to_flat_compile c p =
     let (c', p') = source_to_flat_compile_prog c p in
     let p' = compile_flat (source_to_flat_config_pattern_cfg c') p' in
     (c', p')`;;

(* note that flat_elim is always disabled in the eval/incremental case *)

let inc_compile_def = cake_def
  `inc_compile env_id c p =
     let (c', p') = inc_compile_prog env_id c p in
     let p' = MAP (compile_dec (source_to_flat_config_pattern_cfg c')) p' in
     (c', p')`;;
