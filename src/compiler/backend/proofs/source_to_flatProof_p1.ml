(* ========================================================================= *)
(* source_to_flatProof_p1: part 1 of 2 (HOL4 lines 1-2995) of the port of   *)
(* HOL4 compiler/backend/proofs/source_to_flatProofScript.sml (CakeML        *)
(* v3479).  Correctness proof for source_to_flat.                            *)
(* The parts _p1 and _p2 are loaded one after the other (_p2 needs _p1).    *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as in names.tsv: source_to_flat's compile_exp is                  *)
(*   source_to_flat_compile_exp (compile_exps, compile_pes, compile_funs),   *)
(*   its environment record source_to_flat_environment (fields c and v),     *)
(*   the variable names Glob and source_to_flat_Local; this script's v_rel,  *)
(*   env_rel, result_rel, sv_rel, s_rel are source_to_flatProof_v_rel ...   *)
(* - semanticPrimitives values are v (Litv, Conv, Closure, Recclosure, Loc,  *)
(*   Vectorv, Env), flatSem values flat_v (flat_Litv, ...); r with f := x   *)
(*   is r_f_fupd (K x) r; mlstring literals are implode "...".               *)
(* - Library: EVERY = ALL, LIST_REL = ALL2, set = set_of_list, FOLDR f e l = *)
(*   ITLIST f l e, x (+) y (FUNION) = FUNION x y.                            *)
(* - HOL4's v_rel_eqns, v_rel_more_eqns and v_rel_global_eqn are computed by *)
(*   SIMP_CONV with v_rel_cases; here they are stated (one conjunct per      *)
(*   pattern of the HOL4 list).                                              *)
(* - source_evalProof (an ancestor) contributes only do_eval_oracle to the *)
(*   statements; it is loaded with needs.                                    *)
(* - The derived theorem result_rel_imp (HOL4 RES_CANON of result_rel_cases) *)
(*   is stated and proved.                                                   *)
(* - Vacuous binders of HOL4 statements are dropped (v_rel_weakening2's !gc, *)
(*   result_rel_eqns' third v, do_app_rec_help's env_v_top); HOL4 leaves the *)
(*   EvalDecs case of src_orac_gen_inv unspecified (ARB here).               *)
(* - Free variables are quantified: HOL4's explicit binders first, then the  *)
(*   other free variables in order of occurrence.                            *)
(* - The interpreter of the oracle states (HOL4 interp, ci) has the type     *)
(*   (v->(source_to_flat_config#C)option)option; the states of a statement  *)
(*   are (FFI)state and (C,FFI)flat_state.                                   *)
(* - Helper lemmas and tactics that are not HOL4 theorems are FLATP1AUX_.  *)
(*   The HOL4 [simp] theorems pat_bindings_compile_pat and                   *)
(*   orac_forward_rel_refl are registered with cake_add_simps.               *)
(* - HOL4 invariant is source_to_flatProof_invariant (a short or common      *)
(*   word), and invariant_def is source_to_flatProof_invariant_def.          *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/lprefix_lub.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/semantics.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/source_to_flat.ml";;
needs "compiler/backend/semantics/flatSem.ml";;
needs "compiler/backend/semantics/flatProps.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/proofs/source_evalProof.ml";;
needs "compiler/backend/proofs/flat_elimProof.ml";;
needs "compiler/backend/proofs/flat_patternProof.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 1: HOL4 lines 1-2995 ===== *)

(* HOL4 lines 15-20: simpset settings; build_rec_env_merge is flatProps'    *)
(* flat_build_rec_env_merge                                                  *)

(* HOL4 line 22 *)
let compile_exps_length = prove
 (`!t m es.
     LENGTH (source_to_flat_compile_exps t m es) = LENGTH es`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[source_to_flat_compile_exp_def; LENGTH]);;

(* HOL4 line 29 *)
let mapi_map = prove
 (`!(f:num->B->C) (g:A->B) l. MAPi f (MAP g l) = MAPi (\i x. f i (g x)) l`,
  SUBGOAL_THEN `!l (f:num->B->C) (g:A->B). MAPi f (MAP g l) = MAPi (\i x. f i (g x)) l`
    (fun th -> REWRITE_TAC[th]) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; MAPi_DEF; CONS_11; o_DEF]);;

(* HOL4 line 36 *)
let source_to_flatProof_fst_lem = prove
 (`(\(p1:A,p1':B,p2:C). p1) = FST`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST]);;

(* HOL4 line 44 *)
let funion_submap = prove
 (`!x y z.
     FUNION x y SUBMAP (z:(A,B)fmap) /\ DISJOINT (FDOM x) (FDOM y) ==> y SUBMAP z`,
  REWRITE_TAC[SUBMAP_FLOOKUP_EQN; FLOOKUP_FUNION; DISJOINT; EXTENSION; IN_INTER;
              NOT_IN_EMPTY; FDOM_FLOOKUP] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x':A`) THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[option_CASE]);;

(* HOL4 line 51 *)
let flookup_funion_submap = prove
 (`!x y z k v.
     FUNION x y SUBMAP (z:(A,B)fmap) /\ FLOOKUP (FUNION x y) k = SOME v
   ==> FLOOKUP z k = SOME v`,
  MESON_TAC[FLOOKUP_SUBMAP]);;

(* HOL4 line 61 *)
let FILTER_MAPi_ID = prove
 (`!ls (f:num->A->B) P. FILTER P (MAPi f ls) = MAPi f ls <=>
                      (!n. n < LENGTH ls ==> P (f n (EL n ls)))`,
  SIMP_TAC[FILTER_EQ_ID; EVERY_EL; LENGTH_MAPi; EL_MAPi]);;

(* HOL4 line 87: bind locals with an arbitrary trace *)
let bind_locals_def = cake_def
  `bind_locals ts locals (comp_map:(modN,varN,var_name)namespace) =
     nsBindList (MAP2 (\t x. (x, source_to_flat_Local t x)) ts locals) comp_map`;;

(* HOL4 line 92 *)
let nsAppend_bind_locals = prove
 (`!funs:(varN#varN#exp)list. !t ts locals comp_map.
     nsAppend (alist_to_ns (MAP (\x. (x, source_to_flat_Local t x)) (MAP FST funs)))
       (bind_locals ts locals comp_map) =
     bind_locals (APPEND (REPLICATE (LENGTH funs) t) ts) (APPEND (MAP FST funs) locals)
       comp_map`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; LENGTH; REPLICATE; APPEND; alist_to_ns_nil; nsAppend_nsEmpty;
                  alist_to_ns_cons; nsAppend_nsBind] THEN
  REWRITE_TAC[bind_locals_def; MAP2; nsBindList_def; ITLIST] THEN
  CASE_REWRITE_TAC[]);;

let FLATP1AUX_nsBindList_CONS = prove
 (`!(x:N) (v:V) l (e:(M,N,V)namespace).
     nsBindList (CONS (x,v) l) e = nsBind x v (nsBindList l e)`,
  REWRITE_TAC[nsBindList_def; ITLIST] THEN CASE_REWRITE_TAC[]);;

let FLATP1AUX_bind_locals_CONS = prove
 (`!t ts x locals comp_map.
     bind_locals (CONS t ts) (CONS x locals) comp_map =
     nsBind x (source_to_flat_Local t x) (bind_locals ts locals comp_map)`,
  REWRITE_TAC[bind_locals_def; MAP2; FLATP1AUX_nsBindList_CONS]);;

(* HOL4 line 100 *)
let nsBindList_pat_tups_bind_locals = prove
 (`!ls t ts locals comp_map. ?tss. nsBindList (pat_tups t ls) (bind_locals ts locals comp_map) =
              bind_locals (APPEND tss ts) (APPEND ls locals) comp_map /\
              LENGTH tss = LENGTH ls`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THENL
  [EXISTS_TAC `[]:tra list` THEN
   REWRITE_TAC[pat_tups_def; APPEND; LENGTH; nsBindList_def; ITLIST];
   FIRST_X_ASSUM(X_CHOOSE_THEN `tss:tra list` STRIP_ASSUME_TAC o
     SPECL [`t':tra`; `ts:tra list`; `locals:mlstring list`;
            `comp_map:(modN,varN,var_name)namespace`]) THEN
   EXISTS_TAC `CONS (mk_cons t' (LENGTH (t:mlstring list) + 1)) tss` THEN
   ASM_REWRITE_TAC[pat_tups_def; APPEND; LENGTH; LET_DEF; LET_END_DEF;
                   FLATP1AUX_nsBindList_CONS; FLATP1AUX_bind_locals_CONS]]);;

(* HOL4 line 111 *)
let global_env_INFO = cake_record "global_env"
  ["v","(flat_v option) list";
   "c","((ctor_id # type_id) # num, stamp) fmap";
   "tys","(num, (ctor_id # num) list) fmap"];;

(* HOL4 line 117 *)
let submap_distinct_fupdate_flookup = prove
 (`!x f y g.
     ~(x IN FDOM f) ==>
   ((f |+ (x:A,y:B)) SUBMAP g <=> FLOOKUP g x = SOME y /\ f SUBMAP g)`,
  REWRITE_TAC[SUBMAP_FLOOKUP_EQN; FLOOKUP_UPDATE; FDOM_FLOOKUP] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:B`]) THEN REWRITE_TAC[];
   FIRST_X_ASSUM(MP_TAC o SPECL [`x':A`; `y':B`]) THEN
   COND_CASES_TAC THEN ASM_MESON_TAC[option_DISTINCT];
   POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[option_INJ]]);;

(* HOL4 line 128 *)
let submap_fupdate_flookup = prove
 (`!f x y g.
     (f |+ (x:A,y:B)) SUBMAP g <=> FLOOKUP g x = SOME y /\ (f \\ x) SUBMAP g`,
  REWRITE_TAC[SUBMAP_FLOOKUP_EQN; FLOOKUP_UPDATE; DOMSUB_FLOOKUP_THM] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:B`]) THEN REWRITE_TAC[];
   FIRST_X_ASSUM(MP_TAC o SPECL [`x':A`; `y':B`]) THEN
   POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[option_DISTINCT];
   POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[option_INJ]]);;

(* HOL4 line 137 *)
let has_bools_def = cake_def
  `has_bools (genv:((ctor_id # type_id) # num, stamp) fmap) <=>
     FLOOKUP genv ((true_tag, SOME bool_id), 0) =
       SOME (TypeStamp (implode "True") bool_type_num) /\
     FLOOKUP genv ((false_tag, SOME bool_id), 0) =
       SOME (TypeStamp (implode "False") bool_type_num)`;;

(* HOL4 line 143 *)
let has_lists_def = cake_def
  `has_lists (genv:((ctor_id # type_id) # num, stamp) fmap) <=>
     FLOOKUP genv ((cons_tag, SOME list_id), 2) =
       SOME (TypeStamp (implode "::") list_type_num) /\
     FLOOKUP genv ((nil_tag, SOME list_id), 0) =
       SOME (TypeStamp (implode "[]") list_type_num)`;;

(* HOL4 line 149 *)
let has_exns_def = cake_def
  `has_exns (genv:((ctor_id # type_id) # num, stamp) fmap) <=>
     FLOOKUP genv ((div_tag, NONE), 0) = SOME div_stamp /\
     FLOOKUP genv ((chr_tag, NONE), 0) = SOME chr_stamp /\
     FLOOKUP genv ((subscript_tag, NONE), 0) = SOME subscript_stamp /\
     FLOOKUP genv ((bind_tag, NONE), 0) = SOME bind_stamp`;;

(* HOL4 line 157 *)
let genv_c_ok_def = cake_def
  `genv_c_ok (genv_c:((ctor_id # type_id) # num, stamp) fmap) <=>
     has_bools genv_c /\ has_exns genv_c /\ has_lists genv_c /\
     (!cn1 cn2 l1 l2 stamp1 stamp2.
        FLOOKUP genv_c (cn1,l1) = SOME stamp1 /\
        FLOOKUP genv_c (cn2,l2) = SOME stamp2
        ==> (ctor_same_type (SOME stamp1) (SOME stamp2) <=>
             flat_ctor_same_type (SOME cn1) (SOME cn2))) /\
     (!cn1 cn2 l1 l2 stamp.
        FLOOKUP genv_c (cn1,l1) = SOME stamp /\
        FLOOKUP genv_c (cn2,l2) = SOME stamp
        ==> cn1 = cn2 /\ l1 = l2)`;;

(* HOL4 line 174 *)
let genv_c_tys_ok_def = cake_def
  `genv_c_tys_ok (genv_c:((ctor_id # type_id) # num, stamp) fmap)
                 (genv_tys:(num, (ctor_id # num) list) fmap) <=>
     !cn ty_id arity.
       ((cn, SOME ty_id), arity) IN FDOM genv_c
       ==> ?ctors. FLOOKUP genv_tys ty_id = SOME ctors /\ MEM (cn, arity) ctors`;;

(* HOL4 line 182: the value relation; env_rel and global_env_inv are       *)
(* defined with it                                                           *)
let source_to_flatProof_v_rel_rules,source_to_flatProof_v_rel_ind,
    source_to_flatProof_v_rel_cases,source_to_flatProof_v_rel_strongind =
  cake_inductive
  `(!genv lit.
      source_to_flatProof_v_rel genv (Litv lit) (flat_Litv lit)) /\
   (!genv cn cn' vs vs'.
      ALL2 (source_to_flatProof_v_rel genv) vs vs' /\
      FLOOKUP (global_env_c genv) (cn', LENGTH vs) = SOME cn
      ==> source_to_flatProof_v_rel genv (Conv (SOME cn) vs) (flat_Conv (SOME cn') vs')) /\
   (!genv vs vs'.
      ALL2 (source_to_flatProof_v_rel genv) vs vs'
      ==> source_to_flatProof_v_rel genv (Conv NONE vs) (flat_Conv NONE vs')) /\
   (!genv comp_map env env_v_local x e env_v_local' t ts.
      source_to_flatProof_env_rel genv env_v_local (flat_environment_v env_v_local') /\
      global_env_inv genv comp_map
        (set_of_list (MAP FST (flat_environment_v env_v_local'))) env /\
      LENGTH ts = LENGTH (flat_environment_v env_v_local') + 1
      ==> source_to_flatProof_v_rel genv
            (Closure (sem_env_v_fupd (K (nsAppend env_v_local (sem_env_v env))) env) x e)
            (flat_Closure env_v_local' x
              (source_to_flat_compile_exp t
                 (source_to_flat_environment_v_fupd
                    (K (bind_locals ts (CONS x (MAP FST (flat_environment_v env_v_local')))
                          (source_to_flat_environment_v comp_map))) comp_map)
                 e))) /\
   (!genv comp_map env env_v_local funs x env_v_local' t ts.
      source_to_flatProof_env_rel genv env_v_local (flat_environment_v env_v_local') /\
      global_env_inv genv comp_map
        (set_of_list (MAP FST (flat_environment_v env_v_local'))) env /\
      LENGTH ts = LENGTH funs + LENGTH (flat_environment_v env_v_local')
      ==> source_to_flatProof_v_rel genv
            (Recclosure (sem_env_v_fupd (K (nsAppend env_v_local (sem_env_v env))) env)
               funs x)
            (flat_Recclosure env_v_local'
              (compile_funs t
                 (source_to_flat_environment_v_fupd
                    (K (bind_locals ts (APPEND (MAP FST funs)
                                         (MAP FST (flat_environment_v env_v_local')))
                          (source_to_flat_environment_v comp_map))) comp_map)
                 funs)
              x)) /\
   (!genv comp_map env funs flat_env x y e new_vars t1 t2.
      MAP FST new_vars = MAP FST (REVERSE funs) /\
      global_env_inv genv comp_map {} env /\
      flat_environment_v flat_env = [] /\
      find_recfun x funs = SOME (y, e) /\
      (!x. x IN set_of_list (MAP FST funs)
           ==> ?n y e tr1 t2' tr3.
                 ALOOKUP new_vars x = SOME (Glob tr1 n) /\
                 n < LENGTH (global_env_v genv) /\
                 find_recfun x funs = SOME (y,e) /\
                 EL n (global_env_v genv) =
                   SOME (flat_Closure flat_env y
                          (source_to_flat_compile_exp t2'
                             (source_to_flat_environment_v_fupd
                                (K (nsBindList (CONS (y, source_to_flat_Local tr3 y) new_vars)
                                      (source_to_flat_environment_v comp_map))) comp_map)
                             e)))
      ==> source_to_flatProof_v_rel genv
            (Recclosure env funs x)
            (flat_Closure flat_env y
              (source_to_flat_compile_exp t1
                 (source_to_flat_environment_v_fupd
                    (K (nsBindList (CONS (y, source_to_flat_Local t2 y) new_vars)
                          (source_to_flat_environment_v comp_map))) comp_map)
                 e))) /\
   (!genv loc b.
      source_to_flatProof_v_rel genv (Loc b loc) (flat_Loc b (loc + 1))) /\
   (!genv vs vs'.
      ALL2 (source_to_flatProof_v_rel genv) vs vs'
      ==> source_to_flatProof_v_rel genv (Vectorv vs) (flat_Vectorv vs')) /\
   (!genv.
      source_to_flatProof_env_rel genv nsEmpty []) /\
   (!genv x v env env' v'.
      source_to_flatProof_env_rel genv env env' /\ source_to_flatProof_v_rel genv v v'
      ==> source_to_flatProof_env_rel genv (nsBind x v env) (CONS (x,v') env')) /\
   (!genv comp_map shadowers env.
      (!x v. ~(x IN IMAGE Short shadowers) /\ nsLookup (sem_env_v env) x = SOME v
             ==> ?n v' t. nsLookup (source_to_flat_environment_v comp_map) x =
                            SOME (Glob t n) /\
                          n < LENGTH (global_env_v genv) /\
                          EL n (global_env_v genv) = SOME v' /\
                          source_to_flatProof_v_rel genv v v') /\
      (!x arity stamp.
         nsLookup (sem_env_c env) x = SOME (arity, stamp)
         ==> ?cn ty_gp.
               nsLookup (source_to_flat_environment_c comp_map) x = SOME (cn, ty_gp) /\
               FLOOKUP (global_env_c genv) ((cn, OPTION_MAP FST ty_gp), arity) =
                 SOME stamp /\
               (!ty_id ctors. ty_gp = SOME (ty_id, ctors)
                              ==> FLOOKUP (global_env_tys genv) ty_id = SOME ctors))
      ==> global_env_inv genv comp_map shadowers env)`;;

(* HOL4 line 336: v_rel_eqns (computed by SIMP_CONV with v_rel_cases; stated *)
(* here) *)
let v_rel_eqns = prove
 (`(!genv l v. source_to_flatProof_v_rel genv (Litv l) v <=> v = flat_Litv l) /\
   (!genv cn vs v.
      source_to_flatProof_v_rel genv (Conv cn vs) v <=>
      (?cn1 cn2 vs'. cn = SOME cn1 /\ v = flat_Conv (SOME cn2) vs' /\
                     ALL2 (source_to_flatProof_v_rel genv) vs vs' /\
                     FLOOKUP (global_env_c genv) (cn2, LENGTH vs) = SOME cn1) \/
      (?vs'. cn = NONE /\ v = flat_Conv NONE vs' /\
             ALL2 (source_to_flatProof_v_rel genv) vs vs')) /\
   (!genv b l v. source_to_flatProof_v_rel genv (Loc b l) v <=> v = flat_Loc b (l + 1)) /\
   (!genv vs v.
      source_to_flatProof_v_rel genv (Vectorv vs) v <=>
      ?vs'. v = flat_Vectorv vs' /\ ALL2 (source_to_flatProof_v_rel genv) vs vs') /\
   (!genv env'. source_to_flatProof_env_rel genv nsEmpty env' <=> env' = []) /\
   (!genv x v env env'.
      source_to_flatProof_env_rel genv (nsBind x v env) env' <=>
      ?v' env''. env' = CONS (x,v') env'' /\
                 source_to_flatProof_env_rel genv env env'' /\
                 source_to_flatProof_v_rel genv v v') /\
   (!genv e id v. source_to_flatProof_v_rel genv (Env e id) v <=> F)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [source_to_flatProof_v_rel_cases] THEN
  REWRITE_TAC[distinctness "v"; injectivity "v"; nsBind_nsEmpty; GSYM nsBind_nsEmpty;
              nsBind_11] THEN
  MESON_TAC[]);;

(* HOL4 line 345: v_rel_more_eqns (v_rel_eqns and the closure cases) *)
let v_rel_more_eqns = prove
 (`(!genv env nm exp v.
      source_to_flatProof_v_rel genv (Closure env nm exp) v <=>
      ?comp_map env0 env_v_local env_v_local' t ts.
        env = sem_env_v_fupd (K (nsAppend env_v_local (sem_env_v env0))) env0 /\
        v = flat_Closure env_v_local' nm
              (source_to_flat_compile_exp t
                 (source_to_flat_environment_v_fupd
                    (K (bind_locals ts (CONS nm (MAP FST (flat_environment_v env_v_local')))
                          (source_to_flat_environment_v comp_map))) comp_map)
                 exp) /\
        source_to_flatProof_env_rel genv env_v_local (flat_environment_v env_v_local') /\
        global_env_inv genv comp_map
          (set_of_list (MAP FST (flat_environment_v env_v_local'))) env0 /\
        LENGTH ts = LENGTH (flat_environment_v env_v_local') + 1) /\
   (!genv env funs x v.
      source_to_flatProof_v_rel genv (Recclosure env funs x) v <=>
      (?comp_map env0 env_v_local env_v_local' t ts.
         env = sem_env_v_fupd (K (nsAppend env_v_local (sem_env_v env0))) env0 /\
         v = flat_Recclosure env_v_local'
               (compile_funs t
                  (source_to_flat_environment_v_fupd
                     (K (bind_locals ts (APPEND (MAP FST funs)
                                          (MAP FST (flat_environment_v env_v_local')))
                           (source_to_flat_environment_v comp_map))) comp_map)
                  funs) x /\
         source_to_flatProof_env_rel genv env_v_local (flat_environment_v env_v_local') /\
         global_env_inv genv comp_map
           (set_of_list (MAP FST (flat_environment_v env_v_local'))) env0 /\
         LENGTH ts = LENGTH funs + LENGTH (flat_environment_v env_v_local')) \/
      (?comp_map flat_env y e new_vars t1 t2.
         v = flat_Closure flat_env y
               (source_to_flat_compile_exp t1
                  (source_to_flat_environment_v_fupd
                     (K (nsBindList (CONS (y, source_to_flat_Local t2 y) new_vars)
                           (source_to_flat_environment_v comp_map))) comp_map)
                  e) /\
         MAP FST new_vars = MAP FST (REVERSE funs) /\
         global_env_inv genv comp_map {} env /\
         flat_environment_v flat_env = [] /\
         find_recfun x funs = SOME (y, e) /\
         (!x. x IN set_of_list (MAP FST funs)
              ==> ?n y e tr1 t2' tr3.
                    ALOOKUP new_vars x = SOME (Glob tr1 n) /\
                    n < LENGTH (global_env_v genv) /\
                    find_recfun x funs = SOME (y,e) /\
                    EL n (global_env_v genv) =
                      SOME (flat_Closure flat_env y
                             (source_to_flat_compile_exp t2'
                                (source_to_flat_environment_v_fupd
                                   (K (nsBindList
                                         (CONS (y, source_to_flat_Local tr3 y) new_vars)
                                         (source_to_flat_environment_v comp_map)))
                                   comp_map)
                                e))))) /\
   (!genv l v. source_to_flatProof_v_rel genv (Litv l) v <=> v = flat_Litv l) /\
   (!genv cn vs v.
      source_to_flatProof_v_rel genv (Conv cn vs) v <=>
      (?cn1 cn2 vs'. cn = SOME cn1 /\ v = flat_Conv (SOME cn2) vs' /\
                     ALL2 (source_to_flatProof_v_rel genv) vs vs' /\
                     FLOOKUP (global_env_c genv) (cn2, LENGTH vs) = SOME cn1) \/
      (?vs'. cn = NONE /\ v = flat_Conv NONE vs' /\
             ALL2 (source_to_flatProof_v_rel genv) vs vs')) /\
   (!genv b l v. source_to_flatProof_v_rel genv (Loc b l) v <=> v = flat_Loc b (l + 1)) /\
   (!genv vs v.
      source_to_flatProof_v_rel genv (Vectorv vs) v <=>
      ?vs'. v = flat_Vectorv vs' /\ ALL2 (source_to_flatProof_v_rel genv) vs vs') /\
   (!genv env'. source_to_flatProof_env_rel genv nsEmpty env' <=> env' = []) /\
   (!genv x v env env'.
      source_to_flatProof_env_rel genv (nsBind x v env) env' <=>
      ?v' env''. env' = CONS (x,v') env'' /\
                 source_to_flatProof_env_rel genv env env'' /\
                 source_to_flatProof_v_rel genv v v') /\
   (!genv e id v. source_to_flatProof_v_rel genv (Env e id) v <=> F)`,
  REWRITE_TAC[v_rel_eqns] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [source_to_flatProof_v_rel_cases] THEN SIMP[]);;

(* HOL4 line 353 *)
let v_rel_global_eqn = prove
 (`!genv comp_map shadowers env.
     global_env_inv genv comp_map shadowers env <=>
   (!x v. ~(x IN IMAGE Short shadowers) /\ nsLookup (sem_env_v env) x = SOME v
          ==> ?n v' t. nsLookup (source_to_flat_environment_v comp_map) x =
                         SOME (Glob t n) /\
                       n < LENGTH (global_env_v genv) /\
                       EL n (global_env_v genv) = SOME v' /\
                       source_to_flatProof_v_rel genv v v') /\
   (!x arity stamp.
      nsLookup (sem_env_c env) x = SOME (arity, stamp)
      ==> ?cn ty_gp.
            nsLookup (source_to_flat_environment_c comp_map) x = SOME (cn, ty_gp) /\
            FLOOKUP (global_env_c genv) ((cn, OPTION_MAP FST ty_gp), arity) = SOME stamp /\
            (!ty_id ctors. ty_gp = SOME (ty_id, ctors)
                           ==> FLOOKUP (global_env_tys genv) ty_id = SOME ctors))`,
  MATCH_ACCEPT_TAC (CONJUNCT2(CONJUNCT2 source_to_flatProof_v_rel_cases)));;

(* HOL4 line 356 *)
let env_rel_LIST_REL = prove
 (`!xs ys genv. source_to_flatProof_env_rel genv (alist_to_ns xs) ys <=>
           ALL2 (\x y. FST x = FST y /\ source_to_flatProof_v_rel genv (SND x) (SND y))
             xs ys`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC[alist_to_ns_nil; v_rel_eqns; LIST_REL_NIL];
   SPEC_TAC(`h:varN#v`,`h:varN#v`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
   ASM_REWRITE_TAC[alist_to_ns_cons; v_rel_eqns; LIST_REL_CONS1; EXISTS_PAIR_THM;
                   PAIR_EQ; FST; SND] THEN
   SIMP[CONJ_ACI]]);;

(* HOL4 line 367 *)
let env_rel_dom = prove
 (`!genv env env'.
     source_to_flatProof_env_rel genv env env'
     ==> ?l. env = alist_to_ns l /\ MAP FST l = MAP FST env'`,
  GEN_TAC THEN GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [source_to_flatProof_v_rel_cases] THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN STRIP_TAC THEN RVEQ_TAC THENL
  [EXISTS_TAC `[]:(varN#v)list` THEN REWRITE_TAC[alist_to_ns_nil; MAP];
   FIRST_X_ASSUM(MP_TAC o SPEC `env':(modN,varN,v)namespace`) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
   EXISTS_TAC `CONS (x:varN,v:v) l` THEN
   ASM_REWRITE_TAC[alist_to_ns_cons; MAP]]);;

(* HOL4 line 382 *)
let env_rel_lookup = prove
 (`!genv env x v env'.
     ALOOKUP env x = SOME v /\ source_to_flatProof_env_rel genv (alist_to_ns env) env'
     ==> ?v'. source_to_flatProof_v_rel genv v v' /\ ALOOKUP env' x = SOME v'`,
  REWRITE_TAC[env_rel_LIST_REL] THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALOOKUP_THM; option_DISTINCT] THEN
  SPEC_TAC(`h:varN#v`,`h:varN#v`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[ALOOKUP_THM; LIST_REL_CONS1; EXISTS_PAIR_THM] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[ALOOKUP_THM] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THEN DISCH_TAC THEN RVEQ_TAC THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 405 *)
let source_to_flatProof_env_rel_append = prove
 (`!genv env1 env2 env1' env2'.
     source_to_flatProof_env_rel genv env1 env1' /\
     source_to_flatProof_env_rel genv env2 env2'
     ==> source_to_flatProof_env_rel genv (nsAppend env1 env2) (APPEND env1' env2')`,
  SUBGOAL_THEN `!genv env1' env1 env2 env2'.
     source_to_flatProof_env_rel genv env1 env1' /\
     source_to_flatProof_env_rel genv env2 env2'
     ==> source_to_flatProof_env_rel genv (nsAppend env1 env2) (APPEND env1' env2')`
    (fun th -> MESON_TAC[th]) THEN
  GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [source_to_flatProof_v_rel_cases] THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[nsAppend_nsEmpty; APPEND; nsAppend_nsBind; v_rel_eqns; CONS_11] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 424 *)
let env_rel_one = prove
 (`!genv a b xs.
     source_to_flatProof_env_rel genv (nsBind a b nsEmpty) xs <=>
   ?v. xs = [(a, v)] /\ source_to_flatProof_v_rel genv b v`,
  SIMP[v_rel_eqns]);;

(* HOL4 line 434: env_rel_append at nsBind a b nsEmpty and [(c,d)],       *)
(* simplified with env_rel_one *)
let env_rel_bind_one = prove
 (`!genv a b env2 c d env2'.
     c = a /\ source_to_flatProof_v_rel genv b d /\
     source_to_flatProof_env_rel genv env2 env2'
     ==> source_to_flatProof_env_rel genv (nsAppend (nsBind a b nsEmpty) env2)
           (CONS (c,d) env2')`,
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[nsAppend_nsBind; nsAppend_nsEmpty; v_rel_eqns; CONS_11] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 439 *)
let source_to_flatProof_env_rel_el = prove
 (`!genv env env_i1.
     source_to_flatProof_env_rel genv (alist_to_ns env) env_i1 <=>
     LENGTH env = LENGTH env_i1 /\
     !n. n < LENGTH env
         ==> FST (EL n env) = FST (EL n env_i1) /\
             source_to_flatProof_v_rel genv (SND (EL n env)) (SND (EL n env_i1))`,
  REWRITE_TAC[env_rel_LIST_REL; LIST_REL_EL_EQN]);;

(* HOL4 line 469 *)
let subglobals_def = cake_def
  `subglobals (g1:(A option)list) g2 <=>
     LENGTH g1 <= LENGTH g2 /\
     !n. n < LENGTH g1 /\ IS_SOME (EL n g1) ==> EL n g1 = EL n g2`;;

(* HOL4 line 475 *)
let subglobals_refl = prove
 (`!g:(A option)list. subglobals g g`,
  REWRITE_TAC[subglobals_def; LE_REFL]);;

(* HOL4 line 481 *)
let subglobals_trans = prove
 (`!g1 g2 g3:(A option)list. subglobals g1 g2 /\ subglobals g2 g3 ==> subglobals g1 g3`,
  REWRITE_TAC[subglobals_def] THEN REPEAT STRIP_TAC THENL
  [ASM_ARITH_TAC;
   SUBGOAL_THEN `EL n (g1:(A option)list) = EL n g2` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]]]);;

(* HOL4 line 489 *)
let subglobals_refl_append = prove
 (`!g1 g2 g3:(A option)list.
     subglobals (APPEND g1 g2) (APPEND g1 g3) = subglobals g2 g3 /\
     (LENGTH g2 = LENGTH g3
      ==> subglobals (APPEND g2 g1) (APPEND g3 g1) = subglobals g2 g3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[subglobals_def; LENGTH_APPEND; EL_APPEND] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[LE_ADD_LCANCEL] THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `n:num` THENL
   [STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n + LENGTH (g1:(A option)list)`) THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(n + l < l:num)`; ADD_SUB] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
   DISCH_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN EQ_TAC THEN DISCH_TAC THEN
   X_GEN_TAC `n:num` THENL
   [STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let FLATP1AUX_RULES_TAC (rules:thm) : tactic =
  FIRST (map (fun th -> MATCH_ACCEPT_TAC th ORELSE (fun g -> MATCH_MP_TAC th g))
             (CONJUNCTS rules));;

let FLATP1AUX_subglobals_EL = prove
 (`!g1 g2 n (x:A). subglobals g1 g2 /\ n < LENGTH g1 /\ EL n g1 = SOME x
                   ==> n < LENGTH g2 /\ EL n g2 = SOME x`,
  REWRITE_TAC[subglobals_def] THEN REPEAT STRIP_TAC THENL
  [ASM_ARITH_TAC;
   FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[IS_SOME_DEF] THEN
   MESON_TAC[]]);;

(* HOL4 line 514 *)
let v_rel_weakening = prove
 (`(!genv v v'.
      source_to_flatProof_v_rel genv v v'
      ==> !genv'. global_env_c genv = global_env_c genv' /\
                  global_env_tys genv = global_env_tys genv' /\
                  subglobals (global_env_v genv) (global_env_v genv')
                  ==> source_to_flatProof_v_rel genv' v v') /\
   (!genv env env'.
      source_to_flatProof_env_rel genv env env'
      ==> !genv'. global_env_c genv = global_env_c genv' /\
                  global_env_tys genv = global_env_tys genv' /\
                  subglobals (global_env_v genv) (global_env_v genv')
                  ==> source_to_flatProof_env_rel genv' env env') /\
   (!genv comp_map shadowers env.
      global_env_inv genv comp_map shadowers env
      ==> !genv'. global_env_c genv = global_env_c genv' /\
                  global_env_tys genv = global_env_tys genv' /\
                  subglobals (global_env_v genv) (global_env_v genv')
                  ==> global_env_inv genv' comp_map shadowers env)`,
  MATCH_MP_TAC source_to_flatProof_v_rel_ind THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FLATP1AUX_RULES_TAC source_to_flatProof_v_rel_rules THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_EL_EQN]) THEN REWRITE_TAC[LIST_REL_EL_EQN] THEN
  REPEAT CONJ_TAC THEN ASM_MESON_TAC[FLATP1AUX_subglobals_EL]);;

(* HOL4 line 563 (HOL4's vacuous !gc dropped; genv' free as in HOL4) *)
let v_rel_weakening2 = prove
 (`!genv'.
     (!genv v v'.
      source_to_flatProof_v_rel genv v v'
      ==> global_env_c genv SUBMAP global_env_c genv' /\
          global_env_tys genv SUBMAP global_env_tys genv' /\
          global_env_v genv = global_env_v genv'
          ==> source_to_flatProof_v_rel genv' v v') /\
   (!genv env env'.
      source_to_flatProof_env_rel genv env env'
      ==> global_env_c genv SUBMAP global_env_c genv' /\
          global_env_tys genv SUBMAP global_env_tys genv' /\
          global_env_v genv = global_env_v genv'
          ==> source_to_flatProof_env_rel genv' env env') /\
   (!genv comp_map shadowers env.
      global_env_inv genv comp_map shadowers env
      ==> global_env_c genv SUBMAP global_env_c genv' /\
          global_env_tys genv SUBMAP global_env_tys genv' /\
          global_env_v genv = global_env_v genv'
          ==> global_env_inv genv' comp_map shadowers env)`,
  GEN_TAC THEN MATCH_MP_TAC source_to_flatProof_v_rel_ind THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FLATP1AUX_RULES_TAC source_to_flatProof_v_rel_rules THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_EL_EQN]) THEN REWRITE_TAC[LIST_REL_EL_EQN] THEN
  REPEAT CONJ_TAC THEN ASM_MESON_TAC[FLOOKUP_SUBMAP]);;

(* HOL4 line 601 *)
let drestrict_lem = prove
 (`!f1 f2.
     f1 SUBMAP (f2:(A,B)fmap) ==> FUNION (DRESTRICT f2 (COMPL (FDOM f1))) f1 = f2`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FUNION; FLOOKUP_DRESTRICT; SUBMAP_FLOOKUP_EQN;
              FDOM_FLOOKUP; FMAPAUX_IN_COMPL] THEN
  REPEAT STRIP_TAC THEN CASES_ON `FLOOKUP (f1:(A,B)fmap) x` THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN CASE_REWRITE_TAC[] THENL
  [CASES_ON `FLOOKUP (f2:(A,B)fmap) x` THEN CASE_REWRITE_TAC[];
   ASM_MESON_TAC[]]);;

let FLATP1AUX_WEAK_TAC (n:int) : tactic =
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP]
    (el n (CONJUNCTS (SPEC `genv':global_env` v_rel_weakening2)))) THEN
  EXISTS_TAC `global_env_v_fupd (K (global_env_v genv')) genv` THEN
  REWRITE_TAC[global_env_INFO.ri_accfupds; K_THM] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
    (el n (CONJUNCTS v_rel_weakening))) THEN
  EXISTS_TAC `genv:global_env` THEN
  ASM_REWRITE_TAC[global_env_INFO.ri_accfupds; K_THM];;

(* HOL4 line 609 *)
let v_rel_weak = prove
 (`!genv v v' genv'.
     source_to_flatProof_v_rel genv v v' /\
     global_env_c genv SUBMAP global_env_c genv' /\
     global_env_tys genv SUBMAP global_env_tys genv' /\
     subglobals (global_env_v genv) (global_env_v genv')
     ==> source_to_flatProof_v_rel genv' v v'`,
  FLATP1AUX_WEAK_TAC 0);;

(* HOL4 line 627 *)
let env_rel_weak = prove
 (`!genv env env' genv'.
     source_to_flatProof_env_rel genv env env' /\
     global_env_c genv SUBMAP global_env_c genv' /\
     global_env_tys genv SUBMAP global_env_tys genv' /\
     subglobals (global_env_v genv) (global_env_v genv')
     ==> source_to_flatProof_env_rel genv' env env'`,
  FLATP1AUX_WEAK_TAC 1);;

(* HOL4 line 645 *)
let global_env_inv_weak = prove
 (`!genv comp_map shadowers env genv'.
     global_env_inv genv comp_map shadowers env /\
     global_env_c genv SUBMAP global_env_c genv' /\
     global_env_tys genv SUBMAP global_env_tys genv' /\
     subglobals (global_env_v genv) (global_env_v genv')
     ==> global_env_inv genv' comp_map shadowers env`,
  FLATP1AUX_WEAK_TAC 2);;

(* HOL4 line 663 *)
let source_to_flatProof_result_rel_rules,source_to_flatProof_result_rel_ind,
    source_to_flatProof_result_rel_cases,source_to_flatProof_result_rel_strongind =
  cake_inductive
  `(!genv v v'.
      (f:global_env->A->B->bool) genv v v'
      ==> source_to_flatProof_result_rel f genv (Rval v) (Rval v')) /\
   (!genv v v'.
      source_to_flatProof_v_rel genv v v'
      ==> source_to_flatProof_result_rel f genv (Rerr (Rraise v)) (Rerr (Rraise v'))) /\
   (!genv a.
      source_to_flatProof_result_rel f genv (Rerr (Rabort a)) (Rerr (Rabort a)))`;;

(* HOL4 line 676 (the vacuous v of the third conjunct dropped) *)
let result_rel_eqns = prove
 (`!f.
     (!genv v r.
      source_to_flatProof_result_rel (f:global_env->A->B->bool) genv (Rval v) r <=>
      ?v'. f genv v v' /\ r = Rval v') /\
   (!genv v r.
      source_to_flatProof_result_rel (f:global_env->A->B->bool) genv (Rerr (Rraise v)) r <=>
      ?v'. source_to_flatProof_v_rel genv v v' /\ r = Rerr (Rraise v')) /\
   (!genv r a.
      source_to_flatProof_result_rel (f:global_env->A->B->bool) genv
        (Rerr (Rabort a):(A,v)result) r <=>
      r = Rerr (Rabort a))`,
  GEN_TAC THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [source_to_flatProof_result_rel_cases] THEN SIMP[] THEN
  MESON_TAC[]);;

(* HOL4 line 691 *)
let source_to_flatProof_sv_rel_rules,source_to_flatProof_sv_rel_ind,
    source_to_flatProof_sv_rel_cases,source_to_flatProof_sv_rel_strongind =
  cake_inductive
  `(!genv v v'.
      source_to_flatProof_v_rel genv v v'
      ==> source_to_flatProof_sv_rel genv (Refv v) (Refv v')) /\
   (!genv w.
      source_to_flatProof_sv_rel genv (W8array w) (W8array w)) /\
   (!genv vs vs'.
      ALL2 (source_to_flatProof_v_rel genv) vs vs'
      ==> source_to_flatProof_sv_rel genv (Varray vs) (Varray vs')) /\
   (!genv m v v'.
      source_to_flatProof_v_rel genv v v'
      ==> source_to_flatProof_sv_rel genv (Thunk m v) (Thunk m v'))`;;

(* HOL4 line 708 *)
let sv_rel_weak = prove
 (`!genv sv sv' genv'.
     source_to_flatProof_sv_rel genv sv sv' /\
     global_env_c genv SUBMAP global_env_c genv' /\
     global_env_tys genv SUBMAP global_env_tys genv' /\
     subglobals (global_env_v genv) (global_env_v genv')
     ==> source_to_flatProof_sv_rel genv' sv sv'`,
  ONCE_REWRITE_TAC[source_to_flatProof_sv_rel_cases] THEN REPEAT STRIP_TAC THEN
  RVEQ_TAC THEN REWRITE_TAC[injectivity "store_v"; distinctness "store_v"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_EL_EQN]) THEN REWRITE_TAC[LIST_REL_EL_EQN] THEN
  ASM_MESON_TAC[v_rel_weak]);;

(* HOL4 line 721 *)
let source_to_flatProof_s_rel_rules,source_to_flatProof_s_rel_ind,
    source_to_flatProof_s_rel_cases,source_to_flatProof_s_rel_strongind =
  cake_inductive
  `(!genv (s:(FFI)state) (s':(C,FFI)flat_state).
      ~NULL (flat_state_refs s') /\
      ALL2 (source_to_flatProof_sv_rel genv) (state_refs s) (TL (flat_state_refs s')) /\
      state_clock s = flat_state_clock s' /\
      state_ffi s = flat_state_ffi s'
      ==> source_to_flatProof_s_rel genv s s')`;;

(* HOL4 line 731 *)
let env_all_rel_rules,env_all_rel_ind,env_all_rel_cases,env_all_rel_strongind =
  cake_inductive
  `(!genv map env_v_local env env' locals.
      (?l. env_v_local = alist_to_ns l /\ MAP FST l = locals) /\
      global_env_inv genv map (set_of_list locals) env /\
      source_to_flatProof_env_rel genv env_v_local env'
      ==> env_all_rel genv map
            (sem_env_REC (nsAppend env_v_local (sem_env_v env)) (sem_env_c env))
            (flat_environment_REC env')
            locals)`;;

(* HOL4 line 743 *)
let env_all_rel_weak = prove
 (`!genv map locals env env' genv'.
     env_all_rel genv map env env' locals /\
     global_env_c genv SUBMAP global_env_c genv' /\
     global_env_tys genv SUBMAP global_env_tys genv' /\
     subglobals (global_env_v genv) (global_env_v genv')
     ==> env_all_rel genv' map env env' locals`,
  REWRITE_TAC[env_all_rel_cases] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`env_v_local:(modN,varN,v)namespace`; `env'':(v)sem_env`;
                        `env''':(varN#flat_v)list`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[env_rel_weak; global_env_inv_weak]);;

(* HOL4 line 760 *)
let source_to_flatProof_match_result_rel_def = sem1aux_def
  `(source_to_flatProof_match_result_rel genv env' (Match env) (Match env_i1) <=>
      ?env''. env = APPEND env'' env' /\
              source_to_flatProof_env_rel genv (alist_to_ns env'') env_i1) /\
   (source_to_flatProof_match_result_rel genv env' No_match No_match <=> T) /\
   (source_to_flatProof_match_result_rel genv env' Match_type_error _ <=> T) /\
   (source_to_flatProof_match_result_rel genv env' _ _ <=> F)`;;

(* HOL4 line 768 *)
let match_result_rel_imp = prove
 (`!genv env m1 m2.
     source_to_flatProof_match_result_rel genv env m1 m2
   ==> m1 = Match_type_error \/ (m1 = No_match /\ m2 = No_match) \/
       (?env1 env2. m1 = Match env1 /\ m2 = Match env2)`,
  REPEAT GEN_TAC THEN
  CASES_ON `m1:((varN#v)list)match_result` THEN
  CASES_ON `m2:((varN#flat_v)list)match_result` THEN
  REWRITE_TAC[source_to_flatProof_match_result_rel_def; distinctness "match_result";
              injectivity "match_result"] THEN MESON_TAC[]);;

(* semantic functions respect relation *)

let FLATP1AUX_flat_ctor_same_type = prove
 (`(!x y. flat_ctor_same_type (SOME (x:A#B)) (SOME (y:C#B)) <=> SND x = SND y) /\
   (!x. flat_ctor_same_type (SOME (x:A#B)) (NONE:(C#B)option) <=> F) /\
   (!y. flat_ctor_same_type (NONE:(A#B)option) (SOME (y:C#B)) <=> F) /\
   (flat_ctor_same_type (NONE:(A#B)option) (NONE:(C#B)option) <=> T)`,
  REWRITE_TAC[FORALL_PAIR_THM; flat_ctor_same_type_def]);;

let FLATP1AUX_do_eq_Conv = prove
 (`!(gc:((ctor_id#type_id)#num,stamp)fmap) c1 c2 s1 s2 (vs1:v list) (vs2:v list)
    (ws1:flat_v list) (ws2:flat_v list) X Y.
     (!cn1 cn2 l1 l2 stamp1 stamp2.
        FLOOKUP gc (cn1,l1) = SOME stamp1 /\ FLOOKUP gc (cn2,l2) = SOME stamp2
        ==> (same_type stamp1 stamp2 <=> SND cn1 = SND cn2)) /\
     (!cn1 cn2 l1 l2 stamp.
        FLOOKUP gc (cn1,l1) = SOME stamp /\ FLOOKUP gc (cn2,l2) = SOME stamp
        ==> cn1 = cn2 /\ l1 = l2) /\
     FLOOKUP gc (c1,LENGTH vs1) = SOME s1 /\ FLOOKUP gc (c2,LENGTH vs2) = SOME s2 /\
     LENGTH vs1 = LENGTH ws1 /\ LENGTH vs2 = LENGTH ws2 /\
     (s1 = s2 /\ LENGTH vs1 = LENGTH vs2 ==> X = Y)
     ==> (if c1 = c2 /\ LENGTH ws1 = LENGTH ws2 then X
          else if SND c1 = SND c2 then Eq_val F else Eq_type_error) =
         (if s1 = s2 /\ LENGTH ws1 = LENGTH ws2 then Y
          else if same_type s1 s2 then Eq_val F else Eq_type_error)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c1:ctor_id#type_id) = c2 /\ LENGTH (ws1:flat_v list) = LENGTH (ws2:flat_v list)
                <=> (s1:stamp) = s2 /\ LENGTH ws1 = LENGTH ws2` SUBST1_TAC THENL
  [ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
  SUBGOAL_THEN `same_type s1 s2 <=> SND (c1:ctor_id#type_id) = SND (c2:ctor_id#type_id)`
    SUBST1_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[]);;

let FLATP1AUX_do_eq = prove
 (`!genv. genv_c_ok (global_env_c genv)
     ==> (!v1 v2 v1_i1 v2_i1.
            source_to_flatProof_v_rel genv v1 v1_i1 /\
            source_to_flatProof_v_rel genv v2 v2_i1
            ==> flat_do_eq v1_i1 v2_i1 = do_eq v1 v2) /\
         (!vs1 vs2 vs1_i1 vs2_i1.
            ALL2 (source_to_flatProof_v_rel genv) vs1 vs1_i1 /\
            ALL2 (source_to_flatProof_v_rel genv) vs2 vs2_i1
            ==> flat_do_eq_list vs1_i1 vs2_i1 = do_eq_list vs1 vs2)`,
  GEN_TAC THEN REWRITE_TAC[genv_c_ok_def] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[ctor_same_type_def; FLATP1AUX_flat_ctor_same_type]) THEN
  MATCH_MP_TAC do_eq_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[v_rel_more_eqns; LIST_REL_NIL; LIST_REL_CONS1]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> let c = concl th in
    if is_exists c || is_conj c || is_disj c then CAKE_STRIP_ASSUME_TAC th else NO_TAC)) THEN
  RVEQ_TAC THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  REWRITE_TAC[do_eq_def; flat_do_eq_def] THEN
  IMP_RES_TAC LIST_REL_LENGTH THEN
  ASM_SIMP_TAC[EQ_ADD_RCANCEL; option_INJ; distinctness "option"; ctor_same_type_def;
               FLATP1AUX_flat_ctor_same_type] THEN
  CASE_REWRITE_TAC[] THEN
  TRY(REPEAT COND_CASES_TAC THEN
      ASM_REWRITE_TAC[distinctness "eq_result"; injectivity "eq_result"] THEN NO_TAC) THENL
  [MATCH_MP_TAC FLATP1AUX_do_eq_Conv THEN
   MAP_EVERY EXISTS_TAC [`global_env_c genv`; `vs1:v list`; `vs2:v list`] THEN
   REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_MESON_TAC[option_INJ];
   CASES_ON `do_eq v1 v2` THEN CASE_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* HOL4 line 778 *)
let source_to_flatProof_do_eq = prove
 (`!genv. genv_c_ok (global_env_c genv)
     ==> (!v1 v2 r v1_i1 v2_i1.
            do_eq v1 v2 = r /\
            source_to_flatProof_v_rel genv v1 v1_i1 /\
            source_to_flatProof_v_rel genv v2 v2_i1
            ==> flat_do_eq v1_i1 v2_i1 = r) /\
         (!vs1 vs2 r vs1_i1 vs2_i1.
            do_eq_list vs1 vs2 = r /\
            ALL2 (source_to_flatProof_v_rel genv) vs1 vs1_i1 /\
            ALL2 (source_to_flatProof_v_rel genv) vs2 vs2_i1
            ==> flat_do_eq_list vs1_i1 vs2_i1 = r)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP FLATP1AUX_do_eq) THEN MESON_TAC[]);;

(* HOL4 line 808 *)
let genv_lookup_nil = prove
 (`!genv_c cn.
     genv_c_ok genv_c
   ==> (FLOOKUP genv_c cn = SOME (TypeStamp (implode "[]") list_type_num) <=>
        cn = ((nil_tag, SOME list_id), 0))`,
  REWRITE_TAC[FORALL_PAIR_THM; genv_c_ok_def; has_lists_def; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PAIR_EQ]);;

(* HOL4 line 818 *)
let genv_lookup_cons = prove
 (`!genv_c cn.
     genv_c_ok genv_c
   ==> (FLOOKUP genv_c cn = SOME (TypeStamp (implode "::") list_type_num) <=>
        cn = ((cons_tag, SOME list_id), 2))`,
  REWRITE_TAC[FORALL_PAIR_THM; genv_c_ok_def; has_lists_def; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PAIR_EQ]);;

let FLATP1AUX_VREL_TAC (thl:thm list) : tactic =
  REPEAT(CHANGED_TAC(
    RULE_ASSUM_TAC(REWRITE_RULE([v_rel_eqns; LIST_REL_CONS1; LIST_REL_NIL; LENGTH;
                                 option_INJ; option_DISTINCT; PAIR_EQ] @ thl)) THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    SEVPAUX_STRIPS_TAC THEN TRY RVEQ_TAC)) THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`)));;

(* HOL4 line 828 *)
let source_to_flatProof_v_to_char_list = prove
 (`!genv. genv_c_ok (global_env_c genv)
     ==> !v1 v2 vs1. source_to_flatProof_v_rel genv v1 v2 /\ v_to_char_list v1 = SOME vs1
                     ==> flat_v_to_char_list v2 = SOME vs1`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC v_to_char_list_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[v_to_char_list_def; option_DISTINCT] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[COND_CASE_EQ; option_case_eq; option_DISTINCT;
                                             option_INJ]) THEN
  FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP genv_lookup_nil th;
                                                    MATCH_MP genv_lookup_cons th])) THEN
  FLATP1AUX_VREL_TAC [] THEN
  FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP genv_lookup_nil th;
                                                    MATCH_MP genv_lookup_cons th])) THEN
  FLATP1AUX_VREL_TAC [] THEN
  ASM_SIMP_TAC[flat_v_to_char_list_def] THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

(* HOL4 line 847 *)
let source_to_flatProof_v_to_list = prove
 (`!genv. genv_c_ok (global_env_c genv)
     ==> !v1 v2 vs1. source_to_flatProof_v_rel genv v1 v2 /\ v_to_list v1 = SOME vs1
                     ==> ?vs2. flat_v_to_list v2 = SOME vs2 /\
                               ALL2 (source_to_flatProof_v_rel genv) vs1 vs2`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC v_to_list_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[v_to_list_def; option_DISTINCT] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[COND_CASE_EQ; option_case_eq; option_DISTINCT;
                                             option_INJ]) THEN
  FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP genv_lookup_nil th;
                                                    MATCH_MP genv_lookup_cons th])) THEN
  FLATP1AUX_VREL_TAC [] THEN
  FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP genv_lookup_nil th;
                                                    MATCH_MP genv_lookup_cons th])) THEN
  FLATP1AUX_VREL_TAC [] THEN
  ASM_SIMP_TAC[flat_v_to_list_def; LIST_REL_NIL] THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[option_INJ] THEN ASM_REWRITE_TAC[UNWIND_THM1; LIST_REL_CONS1] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 871 *)
let source_to_flatProof_vs_to_string = prove
 (`!v1 v2 s genv. ALL2 (source_to_flatProof_v_rel genv) v1 v2
             ==> vs_to_string v1 = SOME s ==> flat_vs_to_string v2 = SOME s`,
  MATCH_MP_TAC vs_to_string_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[vs_to_string_def; option_DISTINCT] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[COND_CASE_EQ; option_case_eq; option_DISTINCT;
                                             option_INJ]) THEN
  FLATP1AUX_VREL_TAC [] THEN
  REWRITE_TAC[flat_vs_to_string_def] THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[option_INJ]);;

(* HOL4 line 885 *)
let v_rel_lems = prove
 (`!genv. genv_c_ok (global_env_c genv)
     ==> (!b. source_to_flatProof_v_rel genv (Boolv b) (flat_Boolv b)) /\
         source_to_flatProof_v_rel genv div_exn_v flat_div_exn_v /\
         source_to_flatProof_v_rel genv chr_exn_v flat_chr_exn_v /\
         source_to_flatProof_v_rel genv bind_exn_v flat_bind_exn_v /\
         source_to_flatProof_v_rel genv sub_exn_v subscript_exn_v`,
  GEN_TAC THEN REWRITE_TAC[genv_c_ok_def; has_exns_def; has_bools_def] THEN STRIP_TAC THEN
  REWRITE_TAC[semanticPrimitives_Boolv_def; flat_Boolv_def; div_exn_v_def; flat_div_exn_v_def;
              chr_exn_v_def; flat_chr_exn_v_def; bind_exn_v_def; flat_bind_exn_v_def;
              sub_exn_v_def; subscript_exn_v_def] THEN
  REPEAT CONJ_TAC THEN TRY(GEN_TAC THEN BOOL_CASES_TAC `b:bool`) THEN
  REWRITE_TAC[v_rel_eqns; LENGTH; LIST_REL_NIL; option_INJ; distinctness "option"] THEN
  SIMP[] THEN ASM_REWRITE_TAC[]);;

let FLATP1AUX_v_rel_Boolv = prove
 (`!genv b v. genv_c_ok (global_env_c genv)
     ==> (source_to_flatProof_v_rel genv (Boolv b) v <=> v = flat_Boolv b)`,
  REWRITE_TAC[genv_c_ok_def; has_bools_def] THEN REPEAT STRIP_TAC THEN
  BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[semanticPrimitives_Boolv_def; flat_Boolv_def; v_rel_eqns; LENGTH; LIST_REL_NIL;
              option_INJ; distinctness "option"] THEN
  SIMP[] THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  RVEQ_TAC THEN REWRITE_TAC[injectivity "flat_v"; option_INJ] THEN ASM_MESON_TAC[PAIR_EQ]);;

(* HOL4 line 903 *)
let source_to_flatProof_list_to_v_v_rel = prove
 (`!xs ys genv. has_lists (global_env_c genv) /\ ALL2 (source_to_flatProof_v_rel genv) xs ys
           ==> source_to_flatProof_v_rel genv (list_to_v xs) (flat_list_to_v ys)`,
  REWRITE_TAC[has_lists_def] THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[list_to_v_def; flat_list_to_v_def; v_rel_eqns; LENGTH; LIST_REL_NIL;
              LIST_REL_CONS1; option_INJ; distinctness "option"] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 914 *)
let LIST_REL_IMP_EL2 = prove
 (`!P (xs:A list) (ys:B list).
     ALL2 P xs ys ==> !i. i < LENGTH ys ==> P (EL i xs) (EL i ys)`,
  REWRITE_TAC[LIST_REL_EL_EQN] THEN MESON_TAC[]);;

(* HOL4 line 920 *)
let LIST_REL_IMP_EL = prove
 (`!P (xs:A list) (ys:B list).
     ALL2 P xs ys ==> !i. i < LENGTH xs ==> P (EL i xs) (EL i ys)`,
  SIMP_TAC[LIST_REL_EL_EQN]);;

(* HOL4 line 926 *)
let NOT_NULL_EQ = prove
 (`!xs.
     ~NULL (xs:A list) <=> ?y ys. xs = CONS y ys`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]);;

(* HOL4 line 932 *)
let source_to_flatProof_v_rel_check_type = prove
 (`!genv v1 w1 ty.
     source_to_flatProof_v_rel genv v1 w1 /\ genv_c_ok (global_env_c genv) /\
   check_type ty v1 ==> flat_check_type ty w1`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `ty:prim_type` prim_type_cases) THEN
  REWRITE_TAC[check_type_def; flat_check_type_def] THEN STRIP_TAC THEN
  ASM_MESON_TAC[FLATP1AUX_v_rel_Boolv; v_rel_eqns]);;

let FLATP1AUX_dest_Litv = prove
 (`!genv v w. source_to_flatProof_v_rel genv v w ==> flat_dest_Litv w = dest_Litv v`,
  REPEAT GEN_TAC THEN CASES_ON `v:v` THEN REWRITE_TAC[v_rel_more_eqns] THEN STRIP_TAC THEN
  RVEQ_TAC THEN REWRITE_TAC[flat_dest_Litv_def; dest_Litv_def]);;

(* HOL4 line 942 *)
let do_test_lemma = prove
 (`!test ty v1 v2 b genv w1 w2.
     do_test test ty v1 v2 = Eq_val b /\ genv_c_ok (global_env_c genv) /\
   source_to_flatProof_v_rel genv v1 w1 /\ source_to_flatProof_v_rel genv v2 w2
   ==> flat_do_test test ty w1 w2 = Eq_val b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `flat_dest_Litv w1 = dest_Litv v1 /\ flat_dest_Litv w2 = dest_Litv v2`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[FLATP1AUX_dest_Litv]; ALL_TAC] THEN
  POP_ASSUM_LIST(MAP_EVERY MP_TAC) THEN
  CASES_ON `test:test` THEN REWRITE_TAC[do_test_def; flat_do_test_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) && is_cond (lhs (concl th)))) THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "eq_result"] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  SUBGOAL_THEN `flat_check_type ty w1 /\ flat_check_type ty w2` ASSUME_TAC THENL
  [ASM_MESON_TAC[source_to_flatProof_v_rel_check_type]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
  [RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[check_type_def]) THEN
   SEVPAUX_STRIPS_TAC THEN RVEQ_TAC THEN FLATP1AUX_VREL_TAC [] THEN
   REWRITE_TAC[the_Litv_Float64_def; flat_the_Litv_Float64_def];
   ASM_MESON_TAC[source_to_flatProof_do_eq]]);;

let FLATP1AUX_v_to_flat_Boolv = prove
 (`!b. v_to_flat (Boolv b) = flat_Boolv b`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [semanticPrimitives_Boolv_def] THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[v_to_flat_def] THENL
  [SUBGOAL_THEN `Conv (SOME (TypeStamp (implode "True") bool_type_num)) [] = Boolv T`
     SUBST1_TAC THENL [REWRITE_TAC[semanticPrimitives_Boolv_def]; ALL_TAC];
   SUBGOAL_THEN `Conv (SOME (TypeStamp (implode "False") bool_type_num)) [] = Boolv F`
     SUBST1_TAC THENL [REWRITE_TAC[semanticPrimitives_Boolv_def]; ALL_TAC]] THEN
  REWRITE_TAC[semanticPrimitivesProps_Boolv_11]);;

let FLATP1AUX_flat_Boolv_11 = prove
 (`!b b'. flat_Boolv b = flat_Boolv b' <=> b = b'`,
  REPEAT GEN_TAC THEN MAP_EVERY BOOL_CASES_TAC [`b:bool`; `b':bool`] THEN
  REWRITE_TAC[flat_Boolv_def; injectivity "flat_v"; option_INJ; PAIR_EQ; true_tag_def;
              false_tag_def] THEN ARITH_TAC);;

let FLATP1AUX_flat_to_v_Boolv = prove
 (`!b. flat_to_v (flat_Boolv b) = Boolv b`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [flat_Boolv_def] THEN
  REWRITE_TAC[flat_to_v_def; GSYM flat_Boolv_def; FLATP1AUX_flat_Boolv_11] THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;

(* HOL4 line 967 *)
let check_type_IMP_v_rel = prove
 (`!ty v genv.
     check_type ty v /\ genv_c_ok (global_env_c genv)
   ==> source_to_flatProof_v_rel genv v (v_to_flat v)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `ty:prim_type` prim_type_cases) THEN
  REWRITE_TAC[check_type_def] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_SIMP_TAC[FLATP1AUX_v_to_flat_Boolv; v_rel_lems; v_to_flat_def; v_rel_eqns]);;

(* HOL4 line 978 *)
let check_type_v_rel_flat_to_v = prove
 (`!ty v genv y.
     check_type ty v /\ source_to_flatProof_v_rel genv v y /\ genv_c_ok (global_env_c genv)
   ==> flat_to_v y = v`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `ty:prim_type` prim_type_cases) THEN
  REWRITE_TAC[check_type_def] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[v_rel_eqns]) THEN
  ASM_MESON_TAC[FLATP1AUX_v_rel_Boolv; FLATP1AUX_flat_to_v_Boolv; flat_to_v_def]);;

(* HOL4 line 990 *)
let check_type_v_rel_MAP_flat_to_v = prove
 (`!v y ty genv. ALL (check_type ty) v /\ ALL2 (source_to_flatProof_v_rel genv) v y /\
         genv_c_ok (global_env_c genv)
         ==> MAP flat_to_v y = v`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1; ALL] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[MAP; CONS_11] THEN
  ASM_MESON_TAC[check_type_v_rel_flat_to_v]);;

let FLATP1AUX_do_arith_INL = prove
 (`!a ty vs exn. do_arith a ty vs = SOME (INL exn) ==> exn = div_exn_v`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `ty:prim_type` prim_type_cases) THEN
  REWRITE_TAC[do_arith_def] THEN
  GVS([COND_CASE_EQ; pair_case_eq; option_case_eq; list_case_eq; sum_case_eq] @
      map case_eq ["arith"]) THEN MESON_TAC[]);;

(* HOL4 line 999 *)
let do_arith_INL = prove
 (`!ty vs genv vs_i1 a exn.
     ALL (check_type ty) vs /\ genv_c_ok (global_env_c genv) /\
   ALL2 (source_to_flatProof_v_rel genv) vs vs_i1 /\
   do_arith a ty vs = SOME (INL exn)
   ==> exn = div_exn_v /\ ALL (check_type ty) (MAP flat_to_v vs_i1) /\
       ?e. do_arith a ty (MAP flat_to_v vs_i1) = SOME (INL e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `MAP flat_to_v vs_i1 = vs` SUBST1_TAC THENL
  [MATCH_MP_TAC check_type_v_rel_MAP_flat_to_v THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [ASM_MESON_TAC[FLATP1AUX_do_arith_INL]; EXISTS_TAC `exn:v` THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 1013 *)
let do_arith_INR = prove
 (`!ty vs genv vs_i1 a r.
     ALL (check_type ty) vs /\ genv_c_ok (global_env_c genv) /\
   ALL2 (source_to_flatProof_v_rel genv) vs vs_i1 /\
   do_arith a ty vs = SOME (INR r)
   ==> ALL (check_type ty) (MAP flat_to_v vs_i1) /\
       ?r'. do_arith a ty (MAP flat_to_v vs_i1) = SOME (INR r') /\
            source_to_flatProof_v_rel genv r (v_to_flat r')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `MAP flat_to_v vs_i1 = vs` SUBST1_TAC THENL
  [MATCH_MP_TAC check_type_v_rel_MAP_flat_to_v THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `r:v` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[check_type_IMP_v_rel; do_arith_check_type]);;

let FLATP1AUX_do_conversion_INL = prove
 (`!v ty1 ty2 exn. do_conversion v ty1 ty2 = SOME (INL exn) ==> exn = chr_exn_v`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `ty2:prim_type` prim_type_cases) THEN
  STRUCT_CASES_TAC(SPEC `ty1:prim_type` prim_type_cases) THEN
  REWRITE_TAC[do_conversion_def] THEN GVS[COND_CASE_EQ] THEN MESON_TAC[]);;

(* HOL4 line 1030 *)
let do_conversion_INL = prove
 (`!ty1 v genv v_i1 ty2 exn.
     check_type ty1 v /\ genv_c_ok (global_env_c genv) /\
   source_to_flatProof_v_rel genv v v_i1 /\
   do_conversion v ty1 ty2 = SOME (INL exn)
   ==> exn = chr_exn_v /\ check_type ty1 (flat_to_v v_i1) /\
       ?e. do_conversion (flat_to_v v_i1) ty1 ty2 = SOME (INL e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `flat_to_v v_i1 = v` SUBST1_TAC THENL
  [MATCH_MP_TAC check_type_v_rel_flat_to_v THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [ASM_MESON_TAC[FLATP1AUX_do_conversion_INL]; EXISTS_TAC `exn:v` THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 1044 *)
let do_conversion_INR = prove
 (`!ty1 v genv v_i1 ty2 r.
     check_type ty1 v /\ genv_c_ok (global_env_c genv) /\
   source_to_flatProof_v_rel genv v v_i1 /\
   do_conversion v ty1 ty2 = SOME (INR r)
   ==> check_type ty1 (flat_to_v v_i1) /\
       ?r'. do_conversion (flat_to_v v_i1) ty1 ty2 = SOME (INR r') /\
            source_to_flatProof_v_rel genv r (v_to_flat r')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `flat_to_v v_i1 = v` SUBST1_TAC THENL
  [MATCH_MP_TAC check_type_v_rel_flat_to_v THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `r:v` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[check_type_IMP_v_rel; do_conversion_check_type]);;

let FLATP1AUX_store_lookup_rel = prove
 (`!genv refs (y:flat_v store_v) ys n sv.
     ALL2 (source_to_flatProof_sv_rel genv) refs ys /\ store_lookup n refs = SOME sv
     ==> ?sv'. store_lookup (n + 1) (CONS y ys) = SOME sv' /\
               source_to_flatProof_sv_rel genv sv sv'`,
  REWRITE_TAC[store_lookup_def; LENGTH; LIST_REL_EL_EQN; GSYM ADD1; LT_SUC; EL; TL] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[]);;

let FLATP1AUX_store_lookup_NONE = prove
 (`!genv refs (y:flat_v store_v) ys n.
     ALL2 (source_to_flatProof_sv_rel genv) refs ys /\ store_lookup n refs = NONE
     ==> store_lookup (n + 1) (CONS y ys) = NONE`,
  REWRITE_TAC[store_lookup_def; LENGTH; LIST_REL_EL_EQN; GSYM ADD1; LT_SUC] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  ASM_MESON_TAC[]);;

let FLATP1AUX_sv_rel_same_type = prove
 (`!genv a a' b b'. source_to_flatProof_sv_rel genv a a' /\
                    source_to_flatProof_sv_rel genv b b'
                    ==> (store_v_same_type a b <=> store_v_same_type a' b')`,
  REWRITE_TAC[source_to_flatProof_sv_rel_cases] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[store_v_same_type_def] THEN CASE_REWRITE_TAC[] THEN
  TRY(CASES_ON `m:thunk_mode`) THEN CASE_REWRITE_TAC[]);;

let FLATP1AUX_store_assign_rel = prove
 (`!genv refs (y:flat_v store_v) ys n sv sv' refs2.
     ALL2 (source_to_flatProof_sv_rel genv) refs ys /\
     store_assign n sv refs = SOME refs2 /\ source_to_flatProof_sv_rel genv sv sv'
     ==> ?ys2. store_assign (n + 1) sv' (CONS y ys) = SOME (CONS y ys2) /\
               ALL2 (source_to_flatProof_sv_rel genv) refs2 ys2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[store_assign_def; LENGTH; GSYM ADD1; LT_SUC; EL; TL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  IMP_RES_TAC LIST_REL_LENGTH THEN
  SUBGOAL_THEN `source_to_flatProof_sv_rel genv (EL n refs) (EL n ys)` ASSUME_TAC THENL
  [ASM_MESON_TAC[LIST_REL_EL_EQN]; ALL_TAC] THEN
  SUBGOAL_THEN `store_v_same_type (EL n ys) (sv':flat_v store_v)` ASSUME_TAC THENL
  [ASM_MESON_TAC[FLATP1AUX_sv_rel_same_type]; ALL_TAC] THEN
  SUBGOAL_THEN `n < LENGTH (ys:(flat_v store_v)list)` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LUPDATE_def; option_INJ; CONS_11; UNWIND_THM1] THEN
  MATCH_MP_TAC EVERY2_LUPDATE_same THEN ASM_REWRITE_TAC[]);;

let FLATP1AUX_dest_thunk_rel = prove
 (`!genv refs (y:flat_v store_v) ys v w.
     source_to_flatProof_v_rel genv v w /\ ALL2 (source_to_flatProof_sv_rel genv) refs ys
     ==> (dest_thunk [v] refs = NotThunk <=>
          flat_dest_thunk [w] (CONS y ys) = flat_NotThunk)`,
  REPEAT GEN_TAC THEN CASES_ON `v:v` THEN REWRITE_TAC[v_rel_more_eqns] THEN STRIP_TAC THEN
  RVEQ_TAC THEN REWRITE_TAC[dest_thunk_def; flat_dest_thunk_def] THEN
  CASES_ON `store_lookup a1 (refs:(v store_v)list)` THENL
  [IMP_RES_TAC FLATP1AUX_store_lookup_NONE THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
   IMP_RES_TAC FLATP1AUX_store_lookup_rel THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `sv':flat_v store_v` STRIP_ASSUME_TAC o
     SPEC `y:flat_v store_v` o
     check (fun th -> is_forall (concl th) && is_exists (snd (dest_forall (concl th))))) THEN
   ASM_REWRITE_TAC[] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[source_to_flatProof_sv_rel_cases]) THEN
   SEVPAUX_STRIPS_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[] THEN
   TRY(CASES_ON `m:thunk_mode`) THEN CASE_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN CASE_REWRITE_TAC[]]);;

let FLATP1AUX_DA_SPLIT_TAC : tactic =
  REPEAT GEN_TAC THEN
  SPEC_TAC(`s1:(v store_v)list # (FFI)ffi_state`,`s1:(v store_v)list # (FFI)ffi_state`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`refs:(v store_v)list`; `ffi:(FFI)ffi_state`] THEN
  MP_TAC(ISPEC `s1_i1:(C,FFI)flat_state` (nchotomy_of_type `:(C,FFI)flat_state`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `fck:num` (X_CHOOSE_THEN `frefs:(flat_v store_v)list`
    (X_CHOOSE_THEN `fffi:(FFI)ffi_state` (X_CHOOSE_THEN `fglob:(flat_v option)list`
    (X_CHOOSE_THEN `fcfg:(C)install_config` SUBST1_TAC))))) THEN
  REWRITE_TAC[flat_state_INFO.ri_accessors; FST; SND; NOT_NULL_EQ; IMP_CONJ] THEN
  DISCH_THEN(CAKE_STRIP_ASSUME_TAC o REWRITE_RULE[do_app_cases]) THEN
  REPEAT DISCH_TAC THEN SEVPAUX_STRIPS_TAC THEN RVEQ_TAC;;

let FLATP1AUX_DA_PREP_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[distinctness "op"; PAIR_EQ; store_alloc_def; TL; o_DEF;
                              case_eq "ffi_result"; option_case_eq; sum_case_eq;
                              option_INJ; option_DISTINCT]) THEN
  TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  SEVPAUX_STRIPS_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN SEVPAUX_STRIPS_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[thunk_op_def]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE([pair_case_eq; option_case_eq; list_case_eq; COND_CASE_EQ;
                               case_eq "thunk_op"; case_eq "v"; PAIR_EQ; option_INJ;
                               option_DISTINCT; store_alloc_def])) THEN
  SEVPAUX_STRIPS_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN SEVPAUX_STRIPS_TAC THEN RVEQ_TAC THEN
  FLATP1AUX_VREL_TAC [];;

let FLATP1AUX_bad_thunk_update_rel = prove
 (`!genv refs (y:flat_v store_v) ys v w m.
     source_to_flatProof_v_rel genv v w /\ ALL2 (source_to_flatProof_sv_rel genv) refs ys
     ==> (bad_thunk_update m v refs <=> flat_bad_thunk_update m w (CONS y ys))`,
  REWRITE_TAC[bad_thunk_update_def; flat_bad_thunk_update_def] THEN
  MESON_TAC[FLATP1AUX_dest_thunk_rel]);;

let FLATP1AUX_sv_rel_eqns = prove
 (`(!genv v x. source_to_flatProof_sv_rel genv (Refv v) x <=>
               ?v'. x = Refv v' /\ source_to_flatProof_v_rel genv v v') /\
   (!genv w x. source_to_flatProof_sv_rel genv (W8array w) x <=> x = W8array w) /\
   (!genv vs x. source_to_flatProof_sv_rel genv (Varray vs) x <=>
                ?vs'. x = Varray vs' /\ ALL2 (source_to_flatProof_v_rel genv) vs vs') /\
   (!genv m v x. source_to_flatProof_sv_rel genv (Thunk m v) x <=>
                 ?v'. x = Thunk m v' /\ source_to_flatProof_v_rel genv v v')`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [source_to_flatProof_sv_rel_cases] THEN SIMP[] THEN
  MESON_TAC[]);;

let FLATP1AUX_flat_refs_head (w:term) =
  let t = find_term (fun t -> let h,args = strip_comb t in
                       is_const h && fst(dest_const h) = "flat_state_REC" &&
                       length args = 5) w in
  let _,args = strip_comb t in el 1 args;;

let FLATP1AUX_LOOKUP_TAC : tactic = fun (asl,w as gl) ->
  let cyy = FLATP1AUX_flat_refs_head w in
  let y = lhand cyy in
  (IMP_RES_TAC FLATP1AUX_store_lookup_rel THEN
   REPEAT(FIRST_X_ASSUM(fun th -> let c = concl th in
     if is_forall c && type_of (fst(dest_forall c)) = type_of y &&
        is_exists (snd (dest_forall c))
     then CAKE_STRIP_ASSUME_TAC (SPEC y th) else NO_TAC)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[FLATP1AUX_sv_rel_eqns]) THEN
   SEVPAUX_STRIPS_TAC THEN RVEQ_TAC) gl;;

let FLATP1AUX_shift_lookup = prove
 (`(!sh. shift8_lookup sh = shift_lookup sh) /\ (!sh. shift64_lookup sh = shift_lookup sh)`,
  CONJ_TAC THEN GEN_TAC THEN CASES_ON `sh:shift` THEN
  REWRITE_TAC[shift8_lookup_def; shift64_lookup_def; shift_lookup_def] THEN
  CASE_REWRITE_TAC[]);;

let FLATP1AUX_DA_GOAL_TAC : tactic =
  REWRITE_TAC[astOp_to_flatOp_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[flat_do_app_def; store_alloc_def; LET_DEF; LET_END_DEF; I_THM; do_shift_def;
              FLATP1AUX_shift_lookup; flat_state_INFO.ri_accessors;
              flat_state_INFO.ri_accfupds; K_THM; o_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]));;

let FLATP1AUX_genv_c_ok_has_lists = prove
 (`!gc. genv_c_ok gc ==> has_lists gc`,
  SIMP_TAC[genv_c_ok_def]);;

let FLATP1AUX_v_rel_EL = prove
 (`!genv xs ys i. ALL2 (source_to_flatProof_v_rel genv) xs ys /\ i < LENGTH xs
                  ==> source_to_flatProof_v_rel genv (EL i xs) (EL i ys)`,
  MESON_TAC[LIST_REL_IMP_EL]);;

let FLATP1AUX_BAD_THUNK_TAC : tactic = fun (asl,w as gl) ->
  let cyy = FLATP1AUX_flat_refs_head w in
  let y = lhand cyy in
  let is_c n t = let h,_ = strip_comb t in is_const h && fst(dest_const h) = n in
  let all2s = filter (fun th -> let c = concl th in is_c "ALL2" c &&
                        (let h,args = strip_comb c in is_c "source_to_flatProof_sv_rel"
                                                         (hd args))) (map snd asl) in
  let vrels = filter (fun th -> is_c "source_to_flatProof_v_rel" (concl th)) (map snd asl) in
  let eqs = flat (map (fun a -> mapfilter (fun vr ->
               ISPEC y (MATCH_MP FLATP1AUX_bad_thunk_update_rel (CONJ vr a))) vrels) all2s) in
  RULE_ASSUM_TAC(REWRITE_RULE eqs) gl;;

let FLATP1AUX_DA_REL_TAC : tactic =
  FIRST_ASSUM(fun gc ->
    if concl gc <> `genv_c_ok (global_env_c genv)` then NO_TAC else
    let veq = MATCH_MP FLATP1AUX_do_eq gc in
    IMP_RES_TAC (MATCH_MP source_to_flatProof_v_to_list gc) THEN
    IMP_RES_TAC (MATCH_MP source_to_flatProof_v_to_char_list gc) THEN
    IMP_RES_TAC (CONJUNCT1 veq) THEN
    ASSUME_TAC (MATCH_MP v_rel_lems gc)) THEN
  IMP_RES_TAC do_test_lemma THEN
  IMP_RES_TAC do_arith_INL THEN IMP_RES_TAC do_arith_INR THEN
  IMP_RES_TAC do_conversion_INL THEN IMP_RES_TAC do_conversion_INR THEN
  IMP_RES_TAC source_to_flatProof_vs_to_string THEN
  IMP_RES_TAC FLATP1AUX_genv_c_ok_has_lists THEN
  SEVPAUX_STRIPS_TAC THEN RVEQ_TAC THEN FLATP1AUX_BAD_THUNK_TAC;;

let FLATP1AUX_STORE_ASSIGN_TAC : tactic = fun (asl,w as gl) ->
  let is_sa t = let h,args = strip_comb t in
                is_const h && fst(dest_const h) = "store_assign" && length args = 3 in
  let gts = find_terms (fun t -> is_sa t && (let _,args = strip_comb t in is_cons (el 2 args))) w in
  let ths = filter (fun th -> let c = concl th in is_eq c && is_sa (lhs c)) (map snd asl) in
  let try_pair t th =
    let _,targs = strip_comb t in
    let n1 = el 0 targs and sv' = el 1 targs and cyy = el 2 targs in
    let _,aargs = strip_comb (lhs (concl th)) in
    let n0 = el 0 aargs and sv = el 1 aargs and refs = el 2 aargs in
    if n1 <> mk_binop `(+):num->num->num` n0 `1` then failwith "STORE_ASSIGN" else
    let refs2 = rand (rhs (concl th)) in
    let y = lhand cyy and ys = rand cyy in
    let lem = ISPECL [`genv:global_env`; refs; y; ys; n0; sv; sv'; refs2]
                FLATP1AUX_store_assign_rel in
    MP_TAC lem THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[FLATP1AUX_sv_rel_eqns; injectivity "store_v"; UNWIND_THM1;
                      UNWIND_THM2] THEN
      TRY(MATCH_MP_TAC EVERY2_LUPDATE_same THEN ASM_REWRITE_TAC[]) THEN NO_TAC;
      DISCH_THEN CAKE_STRIP_ASSUME_TAC] in
  FIRST (flat (map (fun t -> map (try_pair t) ths) gts)) gl;;

let FLATP1AUX_ALL2_MAP_Char = prove
 (`!genv l. ALL2 (source_to_flatProof_v_rel genv) (MAP (\c. Litv (Char c)) l)
                 (MAP (\c. flat_Litv (Char c)) l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ALL2; v_rel_eqns]);;

let FLATP1AUX_DA_FIN_TAC : tactic =
  SEVPAUX_LEN_TAC THEN SEVPAUX_GE_FACTS_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  TRY FLATP1AUX_STORE_ASSIGN_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ; PAIR_EQ; GSYM CONJ_ASSOC] THEN
  REPEAT SEVPAUX_EX_WITNESS_TAC THEN
  ASM_REWRITE_TAC[flat_state_INFO.ri_accessors; flat_state_INFO.ri_accfupds; K_THM; TL;
                  result_rel_eqns; NOT_CONS_NIL; CONS_11; UNWIND_THM1; UNWIND_THM2;
                  flat_Unitv_def; injectivity "result"; injectivity "error_result";
                  PURE1AUX_strsub_EL] THEN
  REWRITE_TAC[TAKE_def; ARITH_RULE `~(1 = 0)`; ARITH_RULE `1 - 1 = 0`; CONS_11; TAKE_0] THEN
  SIMP[v_rel_eqns; LIST_REL_NIL; LIST_REL_CONS1; FLATP1AUX_sv_rel_eqns; ADD1;
       LIST_REL_REPLICATE_same; FLATP1AUX_v_rel_EL; source_to_flatProof_list_to_v_v_rel;
       FLATP1AUX_ALL2_MAP_Char; LIST_REL_APPEND_suff];;

(* HOL4 line 1064 (HOL4's s1_i1 has the type ('f_orac_st,'ffi) flatSem$state) *)
let source_to_flatProof_do_app = prove
 (`!genv s1 s2 op vs r (s1_i1:(C,FFI)flat_state) vs_i1.
     do_app s1 op vs = SOME (s2, r) /\
     ALL2 (source_to_flatProof_sv_rel genv) (FST s1) (TL (flat_state_refs s1_i1)) /\
     ~NULL (flat_state_refs s1_i1) /\
     ALL2 (source_to_flatProof_v_rel genv) vs vs_i1 /\
     SND s1 = flat_state_ffi s1_i1 /\
     genv_c_ok (global_env_c genv) /\
     ~(op = AallocEmpty) /\ ~(op = Env_id)
     ==> ?r_i1 s2_i1.
           ALL2 (source_to_flatProof_sv_rel genv) (FST s2) (TL (flat_state_refs s2_i1)) /\
           ~NULL (flat_state_refs s2_i1) /\
           SND s2 = flat_state_ffi s2_i1 /\
           flat_state_globals s1_i1 = flat_state_globals s2_i1 /\
           TAKE 1 (flat_state_refs s1_i1) = TAKE 1 (flat_state_refs s2_i1) /\
           source_to_flatProof_result_rel source_to_flatProof_v_rel genv r r_i1 /\
           flat_do_app s1_i1 (astOp_to_flatOp op) vs_i1 = SOME (s2_i1, r_i1)`,
  FLATP1AUX_DA_SPLIT_TAC THEN FLATP1AUX_DA_PREP_TAC THEN
  FLATP1AUX_LOOKUP_TAC THEN FLATP1AUX_DA_REL_TAC THEN FLATP1AUX_DA_GOAL_TAC THEN
  FLATP1AUX_DA_FIN_TAC);;

(* HOL4 line 1510 *)
let find_recfun = prove
 (`!x funs e comp_map y t.
     find_recfun x funs = SOME (y,e)
     ==> find_recfun x (compile_funs t comp_map funs) =
         SOME (y, source_to_flat_compile_exp (CONS x t)
                    (source_to_flat_environment_v_fupd
                       (K (nsBind y (source_to_flat_Local backend_common_None y)
                             (source_to_flat_environment_v comp_map))) comp_map) e)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
  [ONCE_REWRITE_TAC[find_recfun_def] THEN CASE_REWRITE_TAC[option_DISTINCT];
   ALL_TAC] THEN
  SPEC_TAC(`h:varN#varN#exp`,`h:varN#varN#exp`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:varN`; `a:varN`; `b:exp`] THEN
  REWRITE_TAC[source_to_flat_compile_exp_def] THEN
  ONCE_REWRITE_TAC[find_recfun_def] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let FLATP1AUX_ITLIST_nsBind = prove
 (`!l (e0:(M,N,V)namespace). ITLIST (\(x,v) e. nsBind x v e) l e0 = nsBindList l e0`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; nsBindList_def] THEN
  SPEC_TAC(`h:N#V`,`h:N#V`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  ASM_REWRITE_TAC[GSYM nsBindList_def] THEN REWRITE_TAC[nsBindList_def; ITLIST] THEN
  CASE_REWRITE_TAC[]);;

(* HOL4 line 1525 (HOL4's unused env_v_top dropped; env', ts and funs' free  *)
(* as in HOL4) *)
let do_app_rec_help = prove
 (`!genv comp_map env_v_local env_v_local' (funs:(varN#varN#exp)list) t env' ts funs'.
     source_to_flatProof_env_rel genv env_v_local (flat_environment_v env_v_local') /\
     global_env_inv genv comp_map
       (set_of_list (MAP FST (flat_environment_v env_v_local'))) env' /\
     LENGTH ts = LENGTH funs' + LENGTH (flat_environment_v env_v_local')
     ==> source_to_flatProof_env_rel genv
           (alist_to_ns
              (MAP (\(f,n,e). (f, Recclosure
                                    (sem_env_v_fupd
                                       (K (nsAppend env_v_local (sem_env_v env'))) env')
                                    funs' f)) funs))
           (MAP (\(fn,n,e).
                   (fn, flat_Recclosure env_v_local'
                          (compile_funs t
                             (source_to_flat_environment_v_fupd
                                (K (ITLIST (\(x,v) e. nsBind x v e)
                                      (MAP2 (\t x. (x, source_to_flat_Local t x)) ts
                                         (APPEND (MAP FST funs')
                                            (MAP FST (flat_environment_v env_v_local'))))
                                      (source_to_flat_environment_v comp_map)))
                                comp_map) funs')
                          fn))
                (compile_funs t
                   (source_to_flat_environment_v_fupd
                      (K (ITLIST (\(x,v) e. nsBind x v e)
                            (MAP2 (\t x. (x, source_to_flat_Local t x)) ts
                               (APPEND (MAP FST funs')
                                  (MAP FST (flat_environment_v env_v_local'))))
                            (source_to_flat_environment_v comp_map)))
                      comp_map) funs))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FLATP1AUX_ITLIST_nsBind; GSYM bind_locals_def] THEN
  STRIP_TAC THEN
  SPEC_TAC(`funs:(varN#varN#exp)list`,`funs:(varN#varN#exp)list`) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; source_to_flat_compile_exp_def; alist_to_ns_nil; v_rel_eqns] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`h:varN#varN#exp`,`h:varN#varN#exp`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[source_to_flat_compile_exp_def; MAP] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[alist_to_ns_cons; v_rel_eqns; CONS_11; PAIR_EQ] THEN
  DISCH_TAC THEN SIMP[] THEN
  FLATP1AUX_RULES_TAC source_to_flatProof_v_rel_rules THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 1566 *)
let global_env_inv_add_locals = prove
 (`!genv comp_map locals1 locals2 env.
     global_env_inv genv comp_map locals1 env
     ==> global_env_inv genv comp_map (locals2 UNION locals1) env`,
  REWRITE_TAC[v_rel_global_eqn; IMAGE_UNION; IN_UNION; DE_MORGAN_THM] THEN MESON_TAC[]);;

let FLATP1AUX_nsLookup_alist_NONE = prove
 (`!(l:(N#V)list) (x:(M,N)id).
     ~(x IN set_of_list (MAP (Short o FST) l))
     ==> nsLookup (alist_to_ns l:(M,N,V)namespace) x = NONE`,
  REWRITE_TAC[nsLookup_alist_to_ns_none; IN_SET_OF_LIST; MEM_MAP; o_THM; ALOOKUP_NONE] THEN
  MESON_TAC[]);;

let FLATP1AUX_nsLookupMod_alist_NONE = prove
 (`!(l:(N#V)list) (p:M list).
     ~(p = []) ==> nsLookupMod (alist_to_ns l:(M,N,V)namespace) p = NONE`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; nsLookupMod_alist_to_ns]);;

(* HOL4 line 1576 *)
let global_env_inv_extend2 = prove
 (`!genv comp_map env new_vars env' locals env_c.
     set_of_list (MAP (Short o FST) new_vars) = nsDom env' /\
     global_env_inv genv comp_map locals env /\
     global_env_inv genv
       (source_to_flat_environment_v_fupd (K (alist_to_ns new_vars)) comp_map) locals
       (sem_env_REC env' env_c)
     ==> global_env_inv genv
           (source_to_flat_environment_v_fupd
              (K (nsBindList new_vars (source_to_flat_environment_v comp_map))) comp_map)
           locals
           (sem_env_v_fupd (K (nsAppend env' (sem_env_v env))) env)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[v_rel_global_eqn; GSYM nsAppend_to_nsBindList; sem_env_INFO.ri_accessors;
              sem_env_INFO.ri_accfupds; source_to_flat_environment_INFO.ri_accfupds;
              K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:(modN,varN)id`; `v:v`] THEN
  REWRITE_TAC[nsLookup_nsAppend_some] THEN STRIP_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPECL [`x:(modN,varN)id`; `v:v`] o
     check (fun th -> is_forall (concl th) &&
                      free_in `env':(modN,varN,v)namespace` (concl th))) THEN
   ASM_REWRITE_TAC[] THEN MESON_TAC[];
   SUBGOAL_THEN `nsLookup (alist_to_ns new_vars:(modN,varN,var_name)namespace) x = NONE`
     ASSUME_TAC THENL
   [MATCH_MP_TAC FLATP1AUX_nsLookup_alist_NONE THEN ASM_REWRITE_TAC[nsLookup_nsDom] THEN
    ASM_REWRITE_TAC[option_DISTINCT; NOT_EXISTS_THM];
    ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`x:(modN,varN)id`; `v:v`] o
     check (fun th -> is_forall (concl th) &&
                      free_in `sem_env_v (env:(v)sem_env)` (concl th))) THEN
   ASM_REWRITE_TAC[] THEN MESON_TAC[FLATP1AUX_nsLookupMod_alist_NONE]]);;

(* HOL4 line 1610 *)
let lookup_build_rec_env_lem = prove
 (`!x cl_env funs' funs v.
     ALOOKUP (MAP (\(fn,n,e). (fn, Recclosure cl_env funs' fn))
                (funs:(varN#varN#exp)list)) x = SOME v
     ==> v = Recclosure cl_env funs' x`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ALOOKUP_THM; option_DISTINCT] THEN
  SPEC_TAC(`h:varN#varN#exp`,`h:varN#varN#exp`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[ALOOKUP_THM] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[]);;

(* HOL4 line 1624 *)
let sem_env_eq_lemma = prove
 (`!(env:(A)sem_env) x. sem_env_v_fupd (K x) env = sem_env_REC x (sem_env_c env)`,
  REWRITE_TAC[sem_env_component_equality; sem_env_INFO.ri_accessors; sem_env_INFO.ri_accfupds;
              K_THM]);;

let FLATP1AUX_do_opapp_Closure = prove
 (`!genv env'' n e v2 w1 w2.
     source_to_flatProof_v_rel genv (Closure env'' n e) w1 /\
     source_to_flatProof_v_rel genv v2 w2
     ==> ?comp_map env_i1 locals t1 ts.
           env_all_rel genv comp_map
             (sem_env_v_fupd (K (nsBind n v2 (sem_env_v env''))) env'') env_i1 locals /\
           LENGTH ts = LENGTH locals /\
           flat_do_opapp [w1; w2] =
             SOME (env_i1, source_to_flat_compile_exp t1
                             (source_to_flat_environment_v_fupd
                                (K (bind_locals ts locals
                                      (source_to_flat_environment_v comp_map))) comp_map)
                             e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[v_rel_more_eqns] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`comp_map:source_to_flat_environment`;
    `flat_environment_v_fupd (\env. CONS (n,w2) env) (env_v_local':(flat_v)flat_environment)`;
    `CONS n (MAP FST (flat_environment_v (env_v_local':(flat_v)flat_environment)))`;
    `t:mlstring list`; `ts:tra list`] THEN
  ASM_REWRITE_TAC[LENGTH; ADD1; flat_do_opapp_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH_MAP; env_all_rel_cases] THEN
  MAP_EVERY EXISTS_TAC
   [`nsBind n v2 (env_v_local:(modN,varN,v)namespace)`; `env0:(v)sem_env`;
    `CONS (n,w2) (flat_environment_v (env_v_local':(flat_v)flat_environment))`] THEN
  REWRITE_TAC[sem_env_component_equality; flat_environment_component_equality;
              sem_env_INFO.ri_accessors; sem_env_INFO.ri_accfupds; K_THM;
              flat_environment_INFO.ri_accessors; flat_environment_INFO.ri_accfupds;
              nsAppend_nsBind] THEN
  CONJ_TAC THENL
  [FIRST_ASSUM(X_CHOOSE_THEN `l:(varN#v)list` STRIP_ASSUME_TAC o MATCH_MP env_rel_dom) THEN
   EXISTS_TAC `CONS (n:varN,v2:v) l` THEN ASM_REWRITE_TAC[alist_to_ns_cons; MAP];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[set_of_list] THEN ONCE_REWRITE_TAC[SET_RULE `(x:varN) INSERT s = {x} UNION s`] THEN
   MATCH_MP_TAC global_env_inv_add_locals THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[v_rel_eqns; CONS_11; PAIR_EQ] THEN ASM_MESON_TAC[]]);;

let FLATP1AUX_MAP_Recclosure = prove
 (CASE_TERM `!(cl:(v)sem_env) fs (funs:(varN#varN#exp)list).
     MAP (\fne. match fne with (f,n,e) -> (f, Recclosure cl fs f)) funs =
     MAP (\(f,n,e). (f, Recclosure cl fs f)) funs`,
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CASE_REWRITE_TAC[]);;

let FLATP1AUX_MAP_flat_Recclosure = prove
 (CASE_TERM `!(cl:(flat_v)flat_environment) fs (funs:(varN#varN#flat_exp)list).
     MAP (\fne. match fne with (f,n,e) -> (f, flat_Recclosure cl fs f)) funs =
     MAP (\(fn,n,e). (fn, flat_Recclosure cl fs fn)) funs`,
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  CASE_REWRITE_TAC[]);;

let FLATP1AUX_MAP_FST_compile_funs = prove
 (`!t env funs. MAP FST (compile_funs t env funs) = MAP FST funs`,
  REWRITE_TAC[GSYM source_to_flatProof_fst_lem; GSYM compile_funs_dom]);;

let FLATP1AUX_MAP_FST_pair_lambda = prove
 (`!(g:A->C) (funs:(A#B#D)list). MAP FST (MAP (\(f,n,e). (f, g f)) funs) = MAP FST funs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  SPEC_TAC(`h:A#B#D`,`h:A#B#D`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST]);;

let FLATP1AUX_do_opapp_Rec_local = prove
 (`!genv comp_map env0 env_v_local env_v_local' funs n' t ts n'' e v2 w2.
     source_to_flatProof_env_rel genv env_v_local (flat_environment_v env_v_local') /\
     global_env_inv genv comp_map
       (set_of_list (MAP FST (flat_environment_v env_v_local'))) env0 /\
     LENGTH ts = LENGTH funs + LENGTH (flat_environment_v env_v_local') /\
     find_recfun n' funs = SOME (n'',e) /\ ALL_DISTINCT (MAP FST funs) /\
     source_to_flatProof_v_rel genv v2 w2
     ==> ?comp_map' env_i1 locals t1 ts'.
           env_all_rel genv comp_map'
             (sem_env_v_fupd
                (K (nsBind n'' v2
                      (build_rec_env funs
                         (sem_env_v_fupd (K (nsAppend env_v_local (sem_env_v env0))) env0)
                         (nsAppend env_v_local (sem_env_v env0)))))
                (sem_env_v_fupd (K (nsAppend env_v_local (sem_env_v env0))) env0))
             env_i1 locals /\
           LENGTH ts' = LENGTH locals /\
           flat_do_opapp
             [flat_Recclosure env_v_local'
                (compile_funs t
                   (source_to_flat_environment_v_fupd
                      (K (bind_locals ts (APPEND (MAP FST funs)
                                            (MAP FST (flat_environment_v env_v_local')))
                            (source_to_flat_environment_v comp_map))) comp_map)
                   funs) n'; w2] =
             SOME (env_i1, source_to_flat_compile_exp t1
                             (source_to_flat_environment_v_fupd
                                (K (bind_locals ts' locals
                                      (source_to_flat_environment_v comp_map'))) comp_map')
                             e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `L = APPEND (MAP FST (funs:(varN#varN#exp)list))
                    (MAP FST (flat_environment_v (env_v_local':(flat_v)flat_environment)))` THEN
  ABBREV_TAC `X = source_to_flat_environment_v_fupd
                    (K (bind_locals ts L (source_to_flat_environment_v comp_map))) comp_map` THEN
  MAP_EVERY EXISTS_TAC
   [`comp_map:source_to_flat_environment`;
    `flat_environment_v_fupd
       (K (CONS (n'',w2) (flat_build_rec_env (compile_funs t X funs) env_v_local'
                            (flat_environment_v env_v_local'))))
       (env_v_local':(flat_v)flat_environment)`;
    `CONS (n'':varN) L`; `CONS (n':varN) t`; `CONS backend_common_None ts`] THEN
  ASSUME_TAC(SPECL [`X:source_to_flat_environment`; `t:mlstring list`]
    (MATCH_MP find_recfun
      (ASSUME `find_recfun (n':varN) (funs:(varN#varN#exp)list) = SOME (n'':varN,e:exp)`))) THEN
  REPEAT CONJ_TAC THENL
  [REWRITE_TAC[env_all_rel_cases] THEN
   MAP_EVERY EXISTS_TAC
    [`nsBind n'' v2
        (nsAppend (alist_to_ns (MAP (\(f,n,e). (f, Recclosure
             (sem_env_v_fupd (K (nsAppend env_v_local (sem_env_v env0))) env0) funs f))
             (funs:(varN#varN#exp)list))) (env_v_local:(modN,varN,v)namespace))`;
     `env0:(v)sem_env`;
     `CONS (n'',w2) (flat_build_rec_env (compile_funs t X funs) env_v_local'
                       (flat_environment_v (env_v_local':(flat_v)flat_environment)))`] THEN
   REWRITE_TAC[sem_env_component_equality; flat_environment_component_equality;
               sem_env_INFO.ri_accessors; sem_env_INFO.ri_accfupds; K_THM;
               flat_environment_INFO.ri_accessors; flat_environment_INFO.ri_accfupds;
               build_rec_env_merge; FLATP1AUX_MAP_Recclosure; nsAppend_nsBind;
               nsAppend_assoc] THEN
   FIRST_ASSUM(X_CHOOSE_THEN `l0:(varN#v)list` STRIP_ASSUME_TAC o MATCH_MP env_rel_dom) THEN
   REPEAT CONJ_TAC THENL
   [EXISTS_TAC `CONS (n'':varN, v2:v)
                  (APPEND (MAP (\(f,n,e). (f, Recclosure
                     (sem_env_v_fupd (K (nsAppend env_v_local (sem_env_v env0))) env0) funs f))
                     (funs:(varN#varN#exp)list)) l0)` THEN
    ASM_REWRITE_TAC[alist_to_ns_cons; GSYM nsAppend_alist_to_ns; MAP; MAP_APPEND; CONS_11;
                    FLATP1AUX_MAP_FST_pair_lambda] THEN
    EXPAND_TAC "L" THEN REWRITE_TAC[];
    EXPAND_TAC "L" THEN REWRITE_TAC[set_of_list; SET_OF_LIST_APPEND] THEN
    ONCE_REWRITE_TAC[SET_RULE `(x:varN) INSERT (a UNION b) = (x INSERT a) UNION b`] THEN
    MATCH_MP_TAC global_env_inv_add_locals THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[v_rel_eqns; CONS_11; PAIR_EQ] THEN SIMP[] THEN
    REWRITE_TAC[flat_build_rec_env_merge; FLATP1AUX_MAP_flat_Recclosure] THEN
    REWRITE_TAC[env_rel_LIST_REL] THEN MATCH_MP_TAC LIST_REL_APPEND_suff THEN
    REWRITE_TAC[GSYM env_rel_LIST_REL] THEN CONJ_TAC THENL
    [EXPAND_TAC "X" THEN EXPAND_TAC "L" THEN
     MATCH_MP_TAC (REWRITE_RULE[FLATP1AUX_ITLIST_nsBind; GSYM bind_locals_def]
                     do_app_rec_help) THEN
     ASM_MESON_TAC[];
     ASM_MESON_TAC[]]];
   REWRITE_TAC[LENGTH; SUC_INJ] THEN EXPAND_TAC "L" THEN
   ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_MAP];
   REWRITE_TAC[flat_do_opapp_def] THEN CASE_REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[FLATP1AUX_MAP_FST_compile_funs] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[option_INJ; PAIR_EQ] THEN
   EXPAND_TAC "X" THEN
   REWRITE_TAC[source_to_flat_environment_INFO.ri_accfupds;
               source_to_flat_environment_INFO.ri_fupdfupds; K_o_THM; K_THM;
               FLATP1AUX_bind_locals_CONS]]);;

let FLATP1AUX_do_opapp_Rec_global = prove
 (`!genv comp_map env funs flat_env x y e' new_vars t1 t2 n'' e v2 w2.
     MAP FST new_vars = MAP FST (REVERSE funs) /\
     global_env_inv genv comp_map {} env /\
     flat_environment_v flat_env = [] /\
     find_recfun x funs = SOME (y, e') /\
     (!x. x IN set_of_list (MAP FST funs)
          ==> ?n y e tr1 t2' tr3.
                ALOOKUP new_vars x = SOME (Glob tr1 n) /\
                n < LENGTH (global_env_v genv) /\
                find_recfun x funs = SOME (y,e) /\
                EL n (global_env_v genv) =
                  SOME (flat_Closure flat_env y
                         (source_to_flat_compile_exp t2'
                            (source_to_flat_environment_v_fupd
                               (K (nsBindList (CONS (y, source_to_flat_Local tr3 y) new_vars)
                                     (source_to_flat_environment_v comp_map))) comp_map)
                            e))) /\
     find_recfun x funs = SOME (n'', e) /\
     source_to_flatProof_v_rel genv v2 w2
     ==> ?comp_map' env_i1 locals t1' ts'.
           env_all_rel genv comp_map'
             (sem_env_v_fupd (K (nsBind n'' v2 (build_rec_env funs env (sem_env_v env)))) env)
             env_i1 locals /\
           LENGTH ts' = LENGTH locals /\
           flat_do_opapp
             [flat_Closure flat_env y
                (source_to_flat_compile_exp t1
                   (source_to_flat_environment_v_fupd
                      (K (nsBindList (CONS (y, source_to_flat_Local t2 y) new_vars)
                            (source_to_flat_environment_v comp_map))) comp_map)
                   e'); w2] =
             SOME (env_i1, source_to_flat_compile_exp t1'
                             (source_to_flat_environment_v_fupd
                                (K (bind_locals ts' locals
                                      (source_to_flat_environment_v comp_map'))) comp_map')
                             e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n'':varN = y /\ e:exp = e'` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
  [UNDISCH_TAC `find_recfun (x:varN) (funs:(varN#varN#exp)list) = SOME (n'',e)` THEN
   ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN MESON_TAC[];
   ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`source_to_flat_environment_v_fupd
       (K (nsBindList new_vars (source_to_flat_environment_v comp_map))) comp_map`;
    `flat_environment_v_fupd (\env. CONS (y,w2) env) (flat_env:(flat_v)flat_environment)`;
    `[y:varN]`; `t1:mlstring list`; `[t2:tra]`] THEN
  REWRITE_TAC[LENGTH; flat_do_opapp_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_INJ; PAIR_EQ] THEN
  REWRITE_TAC[source_to_flat_environment_INFO.ri_accfupds;
              source_to_flat_environment_INFO.ri_fupdfupds; K_o_THM; K_THM;
              FLATP1AUX_bind_locals_CONS; FLATP1AUX_nsBindList_CONS] THEN
  REWRITE_TAC[bind_locals_def; MAP2; nsBindList_def; ITLIST] THEN
  REWRITE_TAC[GSYM nsBindList_def] THEN
  REWRITE_TAC[env_all_rel_cases] THEN
  MAP_EVERY EXISTS_TAC
   [`nsBind y v2 nsEmpty:(modN,varN,v)namespace`;
    `sem_env_v_fupd (K (build_rec_env funs env (sem_env_v env))) (env:(v)sem_env)`;
    `[(y:varN, w2:flat_v)]`] THEN
  REWRITE_TAC[sem_env_component_equality; flat_environment_component_equality;
              sem_env_INFO.ri_accessors; sem_env_INFO.ri_accfupds; K_THM;
              flat_environment_INFO.ri_accessors; flat_environment_INFO.ri_accfupds;
              nsAppend_nsBind; nsAppend_nsEmpty] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [EXISTS_TAC `[(y:varN, v2:v)]` THEN REWRITE_TAC[alist_to_ns_cons; alist_to_ns_nil; MAP];
   REWRITE_TAC[build_rec_env_merge; FLATP1AUX_MAP_Recclosure] THEN
   MATCH_MP_TAC global_env_inv_extend2 THEN
   EXISTS_TAC `nsEmpty:(modN,conN,num#stamp)namespace` THEN
   REPEAT CONJ_TAC THENL
   [REWRITE_TAC[nsDom_alist_to_ns; MAP_o] THEN
    ASM_REWRITE_TAC[FLATP1AUX_MAP_FST_pair_lambda; MAP_REVERSE] THEN
    REWRITE_TAC[GSYM MAP_REVERSE; GSYM MAP_o] THEN
    REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_MAP; MEM_REVERSE];
    REWRITE_TAC[set_of_list] THEN
    ONCE_REWRITE_TAC[SET_RULE `(x:varN) INSERT {} = {x} UNION {}`] THEN
    MATCH_MP_TAC global_env_inv_add_locals THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[v_rel_global_eqn; sem_env_INFO.ri_accessors; nsLookup_nsEmpty;
                option_DISTINCT; source_to_flat_environment_INFO.ri_accfupds; K_THM] THEN
    MAP_EVERY X_GEN_TAC [`xx:(modN,varN)id`; `vv:v`] THEN
    REWRITE_TAC[nsLookup_alist_to_ns_some] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP lookup_build_rec_env_lem) THEN
    SUBGOAL_THEN `(x':varN) IN set_of_list (MAP FST (funs:(varN#varN#exp)list))` MP_TAC THENL
    [REWRITE_TAC[IN_SET_OF_LIST] THEN
     ONCE_REWRITE_TAC[GSYM (ISPEC `\fn:varN. Recclosure env funs fn`
                                   FLATP1AUX_MAP_FST_pair_lambda)] THEN
     ASM_MESON_TAC[ALOOKUP_NONE; option_DISTINCT];
     ALL_TAC] THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th o
      check (fun th -> is_forall (concl th) && is_imp (snd (dest_forall (concl th)))))) THEN
    DISCH_THEN(X_CHOOSE_THEN `n0:num` (X_CHOOSE_THEN `y0:varN` (X_CHOOSE_THEN `e0:exp`
      (X_CHOOSE_THEN `tr1:tra` (X_CHOOSE_THEN `t20:mlstring list`
      (X_CHOOSE_THEN `tr3:tra` STRIP_ASSUME_TAC)))))) THEN
    MAP_EVERY EXISTS_TAC
     [`n0:num`;
      `flat_Closure flat_env y0
         (source_to_flat_compile_exp t20
            (source_to_flat_environment_v_fupd
               (K (nsBindList (CONS (y0, source_to_flat_Local tr3 y0) new_vars)
                     (source_to_flat_environment_v comp_map))) comp_map) e0)`;
      `tr1:tra`] THEN
    ASM_REWRITE_TAC[nsLookup_alist_to_ns_some; injectivity "id"; UNWIND_THM1] THEN
    FLATP1AUX_RULES_TAC source_to_flatProof_v_rel_rules THEN ASM_REWRITE_TAC[]];
   REWRITE_TAC[env_rel_one; CONS_11; PAIR_EQ] THEN ASM_MESON_TAC[]]);;

(* HOL4 line 1631 *)
let do_opapp = prove
 (`!genv vs vs_i1 env e.
     do_opapp vs = SOME (env, e) /\ ALL2 (source_to_flatProof_v_rel genv) vs vs_i1
     ==> ?comp_map env_i1 locals t1 ts.
           env_all_rel genv comp_map env env_i1 locals /\
           LENGTH ts = LENGTH locals /\
           flat_do_opapp vs_i1 =
             SOME (env_i1, source_to_flat_compile_exp t1
                             (source_to_flat_environment_v_fupd
                                (K (bind_locals ts locals
                                      (source_to_flat_environment_v comp_map))) comp_map)
                             e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[do_opapp_cases] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL; EVALAUX_MAP_FST3]) THEN
  SEVPAUX_STRIPS_TAC THEN RVEQ_TAC THENL
  [MATCH_MP_TAC FLATP1AUX_do_opapp_Closure THEN ASM_REWRITE_TAC[];
   FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[v_rel_more_eqns] o
     check (fun th -> let c = concl th in
       is_comb c && is_comb (rator c) &&
       (let h,args = strip_comb c in length args = 3 &&
        fst(dest_const h) = "source_to_flatProof_v_rel" &&
        (let h2,_ = strip_comb (el 1 args) in is_const h2 &&
                                             fst(dest_const h2) = "Recclosure")))) THEN
   RVEQ_TAC THEN
   REWRITE_TAC[sem_env_INFO.ri_accessors; sem_env_INFO.ri_accfupds; K_THM] THENL
   [MATCH_MP_TAC FLATP1AUX_do_opapp_Rec_local THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FLATP1AUX_do_opapp_Rec_global THEN ASM_MESON_TAC[]]]);;

(* HOL4 line 1751 (HOL4's pat_bindings take an accumulator; here both have   *)
(* one argument) *)
let pat_bindings_compile_pat = prove
 (`!comp_map (p:pat). flat_pat_bindings (compile_pat comp_map p) = pat_bindings p`,
  MATCH_MP_TAC compile_pat_ind THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[compile_pat_def; flat_pat_bindings_def; pat_bindings_def] THEN
  ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`ps:pat list`,`ps:pat list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; flat_pat_bindings_def; pat_bindings_def; MEM] THEN
  REPEAT STRIP_TAC THEN BINOP_TAC THEN ASM_MESON_TAC[]);;
let _ = cake_add_simps [pat_bindings_compile_pat];;

(* HOL4 line 1761 *)
let eta2 = prove
 (`!(f:A->B->C) x. (\y. f x y) = f x`,
  REWRITE_TAC[ETA_AX]);;

(* HOL4 line 1767 (flatSem's ctor_same_type, which the HOL4 script sees) *)
let ctor_same_type_refl = prove
 (`!x.
     flat_ctor_same_type (x:(A#B)option) x`,
  GEN_TAC THEN CASES_ON `x:(A#B)option` THEN REWRITE_TAC[FLATP1AUX_flat_ctor_same_type]);;

(* HOL4 line 1777 *)
let ctor_same_type_SND = prove
 (`!x y.
     flat_ctor_same_type (SOME (x:A#B)) (SOME (y:C#B)) = (SND x = SND y)`,
  REWRITE_TAC[FLATP1AUX_flat_ctor_same_type]);;

(* HOL4 line 1783 *)
let genv_c_ok_pmatch_stamps_ok = prove
 (`!genv s t comp_map_c nm flat_cn ty_gp src_stamp src_stamp' l flat_stamp' l'.
     source_to_flatProof_s_rel genv (s:(FFI)state) (t:(C,FFI)flat_state) /\
   nsLookup (comp_map_c:(modN,conN,ctor_id#type_group_id)namespace) nm =
     SOME (flat_cn, ty_gp) /\
   same_type src_stamp src_stamp' /\
   genv_c_ok (global_env_c genv) /\
   genv_c_tys_ok (global_env_c genv) (global_env_tys genv) /\
   FLOOKUP (global_env_c genv) ((flat_cn, OPTION_MAP FST ty_gp), l) = SOME src_stamp /\
   FLOOKUP (global_env_c genv) (flat_stamp', l') = SOME src_stamp' /\
   (!ty_id ctors. ty_gp = SOME (ty_id, ctors)
                  ==> FLOOKUP (global_env_tys genv) ty_id = SOME ctors)
   ==> pmatch_stamps_ok (SOME (flat_cn, ty_gp)) (SOME flat_stamp') l l'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[genv_c_ok_def; genv_c_tys_ok_def; FDOM_FLOOKUP] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[ctor_same_type_def; FLATP1AUX_flat_ctor_same_type]) THEN
  SUBGOAL_THEN `OPTION_MAP FST (ty_gp:type_group_id) = SND (flat_stamp':ctor_id#type_id)`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPECL [`(flat_cn:ctor_id, OPTION_MAP FST (ty_gp:type_group_id))`;
     `flat_stamp':ctor_id#type_id`; `l:num`; `l':num`; `src_stamp:stamp`;
     `src_stamp':stamp`] o check (fun th -> is_forall (concl th) &&
       length (fst (strip_forall (concl th))) = 6)) THEN
   ASM_REWRITE_TAC[SND];
   ALL_TAC] THEN
  MP_TAC(ISPEC `flat_stamp':ctor_id#type_id` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cn':ctor_id` (X_CHOOSE_THEN `tid:type_id` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SND]) THEN
  CASES_ON `ty_gp:type_group_id` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[OPTION_MAP_DEF; option_DISTINCT; option_INJ]) THEN
  RVEQ_TAC THEN REWRITE_TAC[pmatch_stamps_ok_cases; option_DISTINCT; option_INJ; PAIR_EQ;
                            distinctness "option"] THENL
  [MESON_TAC[];
   MP_TAC(ISPEC `a:num#(ctor_id#num)list` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `tyid:num` (X_CHOOSE_THEN `ctors:(ctor_id#num)list`
     SUBST_ALL_TAC)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[FST; PAIR_EQ]) THEN REWRITE_TAC[FST; PAIR_EQ] THEN
   SUBGOAL_THEN `FLOOKUP (global_env_tys genv) tyid = SOME (ctors:(ctor_id#num)list)`
     ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   FIRST_X_ASSUM(fun th8 -> if is_forall (concl th8) &&
                               length (fst (strip_forall (concl th8))) = 3 then
     MP_TAC (SPECL [`flat_cn:ctor_id`; `tyid:num`; `l:num`] th8) THEN
     MP_TAC (SPECL [`cn':ctor_id`; `tyid:num`; `l':num`] th8) else NO_TAC) THEN
   ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
   DISCH_THEN(X_CHOOSE_THEN `c1:(ctor_id#num)list` STRIP_ASSUME_TAC) THEN
   DISCH_THEN(X_CHOOSE_THEN `c2:(ctor_id#num)list` STRIP_ASSUME_TAC) THEN
   RVEQ_TAC THEN
   MAP_EVERY EXISTS_TAC [`tyid:num`; `tyid:num`; `flat_cn:ctor_id`; `c1:(ctor_id#num)list`;
                         `cn':ctor_id`] THEN
   ASM_REWRITE_TAC[]]);;

(* HOL4 line 1816 *)
let FST_PAIR_MAP_I = prove
 (`!f x.
     FST (((I:A->A) ## (f:B->C)) x) = FST x`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_MAP_THM; I_THM; FST]);;

(* HOL4 line 1822 *)
let genv_c_ok_same_type_FST_eq_imp_same_ctor = prove
 (`!genv_c cn1 l1 stamp1 cn2 l2 stamp2.
     genv_c_ok genv_c /\
   FLOOKUP genv_c (cn1, l1) = SOME stamp1 /\
   FLOOKUP genv_c (cn2, l2) = SOME stamp2 /\
   same_type stamp1 stamp2 /\ FST cn1 = FST cn2 /\ l1 = l2
   ==> same_ctor stamp1 stamp2`,
  REWRITE_TAC[FORALL_PAIR_THM; genv_c_ok_def; same_ctor_def; FST] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[ctor_same_type_def; FLATP1AUX_flat_ctor_same_type]) THEN
  RVEQ_TAC THEN
  SUBGOAL_THEN `p2:type_id = p2'` SUBST_ALL_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPECL [`p1':ctor_id`; `p2:type_id`; `p1':ctor_id`; `p2':type_id`;
     `l2:num`; `l2:num`; `stamp1:stamp`; `stamp2:stamp`] o check (fun th ->
       is_forall (concl th) && length (fst (strip_forall (concl th))) = 8)) THEN
   ASM_REWRITE_TAC[];
   ASM_MESON_TAC[option_INJ]]);;

let FLATP1AUX_s_rel_store_lookup = prove
 (`!genv st (s_i1:(C,FFI)flat_state) n.
     source_to_flatProof_s_rel genv st s_i1
     ==> (!sv. store_lookup n (state_refs st) = SOME sv
               ==> ?sv'. store_lookup (n + 1) (flat_state_refs s_i1) = SOME sv' /\
                         source_to_flatProof_sv_rel genv sv sv') /\
         (store_lookup n (state_refs st) = NONE
          ==> store_lookup (n + 1) (flat_state_refs s_i1) = NONE)`,
  REWRITE_TAC[source_to_flatProof_s_rel_cases; NOT_NULL_EQ] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_comb (lhs (concl th)) &&
                             is_const (rator (lhs (concl th))) &&
                             fst (dest_const (rator (lhs (concl th)))) = "flat_state_refs"
                          then SUBST_ALL_TAC th else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TL]) THEN
  ASM_MESON_TAC[FLATP1AUX_store_lookup_rel; FLATP1AUX_store_lookup_NONE]);;

let FLATP1AUX_pmatch = prove
 (`!genv comp_map2 shadowers senv comp_map.
     global_env_inv genv comp_map2 shadowers senv /\
     genv_c_ok (global_env_c genv) /\
     genv_c_tys_ok (global_env_c genv) (global_env_tys genv) /\
     source_to_flat_environment_c comp_map2 = source_to_flat_environment_c comp_map
     ==> (!cenv s p v env.
            cenv = sem_env_c senv
            ==> !env' env'' env_i1 (s_i1:(C,FFI)flat_state) v_i1 (st':(FFI)state).
                  source_to_flatProof_s_rel genv st' s_i1 /\
                  env = APPEND env' env'' /\
                  flat_state_globals s_i1 = global_env_v genv /\
                  s = state_refs st' /\
                  source_to_flatProof_v_rel genv v v_i1 /\
                  source_to_flatProof_env_rel genv (alist_to_ns env') env_i1
                  ==> source_to_flatProof_match_result_rel genv env''
                        (pmatch cenv s p v env)
                        (flat_pmatch s_i1 (compile_pat comp_map p) v_i1 env_i1)) /\
         (!cenv s ps vs env.
            cenv = sem_env_c senv
            ==> !env' env'' env_i1 (s_i1:(C,FFI)flat_state) vs_i1 (st':(FFI)state).
                  source_to_flatProof_s_rel genv st' s_i1 /\
                  env = APPEND env' env'' /\
                  flat_state_globals s_i1 = global_env_v genv /\
                  s = state_refs st' /\
                  ALL2 (source_to_flatProof_v_rel genv) vs vs_i1 /\
                  source_to_flatProof_env_rel genv (alist_to_ns env') env_i1
                  ==> source_to_flatProof_match_result_rel genv env''
                        (pmatch_list cenv s ps vs env)
                        (flat_pmatch_list s_i1 (MAP (compile_pat comp_map) ps) vs_i1 env_i1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC pmatch_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[pmatch_def; compile_pat_def; source_to_flatProof_match_result_rel_def] THEN
  FLATP1AUX_VREL_TAC [] THEN
  REWRITE_TAC[flat_pmatch_def; source_to_flatProof_match_result_rel_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THENL
  [(* Pany *)
   EXISTS_TAC `env':(varN#v)list` THEN ASM_REWRITE_TAC[];
   (* Pvar *)
   EXISTS_TAC `CONS (x:varN,v':v) env'` THEN
   ASM_REWRITE_TAC[APPEND; alist_to_ns_cons; v_rel_eqns; CONS_11; PAIR_EQ] THEN
   ASM_MESON_TAC[];
   (* Plit *)
   ASM_CASES_TAC `l:lit = l'` THEN ASM_REWRITE_TAC[source_to_flatProof_match_result_rel_def] THENL
   [EXISTS_TAC `env':(varN#v)list` THEN ASM_REWRITE_TAC[];
    COND_CASES_TAC THEN REWRITE_TAC[source_to_flatProof_match_result_rel_def]];
   (* Pcon SOME *)
   REWRITE_TAC[OPTION_MAP_DEF; OPTION_JOIN_DEF; LENGTH_MAP] THEN
   IMP_RES_TAC LIST_REL_LENGTH THEN
   CASES_ON `nsLookup (sem_env_c (senv:(v)sem_env)) n` THEN
   CASE_REWRITE_TAC[source_to_flatProof_match_result_rel_def] THEN
   MP_TAC(ISPEC `a:num#stamp` PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `stamp:stamp` SUBST_ALL_TAC)) THEN
   CASE_REWRITE_TAC[] THEN
   FIRST_ASSUM(MP_TAC o SPECL [`n:(modN,conN)id`; `l:num`; `stamp:stamp`] o CONJUNCT2 o
     REWRITE_RULE[v_rel_global_eqn] o
     check (fun th -> let h,_ = strip_comb (concl th) in is_const h &&
                      fst (dest_const h) = "global_env_inv")) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `cn:ctor_id` (X_CHOOSE_THEN `ty_gp:type_group_id`
     STRIP_ASSUME_TAC)) THEN
   SUBGOAL_THEN `nsLookup (source_to_flat_environment_c comp_map) n =
                 SOME (cn:ctor_id,ty_gp:type_group_id)` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_CASES_TAC `same_type stamp cn1 /\ LENGTH (ps:pat list) = l` THEN
   ASM_REWRITE_TAC[source_to_flatProof_match_result_rel_def] THEN
   FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
   SUBGOAL_THEN `pmatch_stamps_ok (SOME (cn:ctor_id,ty_gp:type_group_id))
                   (SOME (cn2:ctor_id#type_id)) l (LENGTH (vs:v list))`
     ASSUME_TAC THENL
   [MATCH_MP_TAC genv_c_ok_pmatch_stamps_ok THEN
    MAP_EVERY EXISTS_TAC [`genv:global_env`; `st':(FFI)state`; `s_i1:(C,FFI)flat_state`;
      `source_to_flat_environment_c comp_map2`; `n:(modN,conN)id`; `stamp:stamp`;
      `cn1:stamp`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   ASM_REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN
   ASM_CASES_TAC `same_ctor stamp cn1` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `(cn:ctor_id,OPTION_MAP FST (ty_gp:type_group_id)) = (cn2:ctor_id#type_id) /\
                  l = LENGTH (vs':flat_v list)`
      STRIP_ASSUME_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[same_ctor_def]) THEN RVEQ_TAC THEN
     FIRST_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
       REWRITE_RULE[genv_c_ok_def] o
       check (fun th -> concl th = `genv_c_ok (global_env_c genv)`)) THEN
     ASM_MESON_TAC[];
     ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
      is_var (rhs (concl th)) && fst (dest_var (rhs (concl th))) = "cn2")) THEN
    ASM_REWRITE_TAC[FST] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `stamp:stamp` o
      check (fun th -> is_forall (concl th) &&
                       type_of (fst (dest_forall (concl th))) = `:stamp`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`env':(varN#v)list`; `st':(FFI)state`] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~((cn:ctor_id) = FST (cn2:ctor_id#type_id) /\ l = LENGTH (vs':flat_v list))`
      (fun th -> REWRITE_TAC[th; source_to_flatProof_match_result_rel_def]) THEN
    STRIP_TAC THEN UNDISCH_TAC `~same_ctor stamp cn1` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC genv_c_ok_same_type_FST_eq_imp_same_ctor THEN
    MAP_EVERY EXISTS_TAC [`global_env_c genv`; `(cn:ctor_id, OPTION_MAP FST (ty_gp:type_group_id))`;
      `l:num`; `cn2:ctor_id#type_id`; `LENGTH (vs':flat_v list)`] THEN
    ASM_REWRITE_TAC[FST] THEN ASM_MESON_TAC[]];
   (* Pcon NONE *)
   REWRITE_TAC[OPTION_MAP_DEF; OPTION_JOIN_DEF; LENGTH_MAP; pmatch_stamps_ok_cases;
               distinctness "option"] THEN
   IMP_RES_TAC LIST_REL_LENGTH THEN ASM_REWRITE_TAC[] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[source_to_flatProof_match_result_rel_def] THEN
   FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   MAP_EVERY EXISTS_TAC [`env':(varN#v)list`; `st':(FFI)state`] THEN ASM_REWRITE_TAC[];
   (* Pref *)
   FIRST_ASSUM(MP_TAC o SPEC `lnum:num` o MATCH_MP FLATP1AUX_s_rel_store_lookup o
     check (fun th -> let h,_ = strip_comb (concl th) in is_const h &&
                      fst (dest_const h) = "source_to_flatProof_s_rel")) THEN
   CASES_ON `store_lookup lnum (state_refs (st':(FFI)state))` THEN
   REWRITE_TAC[option_DISTINCT; option_INJ] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[source_to_flatProof_match_result_rel_def] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `sv':flat_v store_v` STRIP_ASSUME_TAC o REWRITE_RULE[] o
     SPEC `a:v store_v` o
     check (fun th -> is_forall (concl th) &&
                      fst (dest_var (fst (dest_forall (concl th)))) = "sv")) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   CASES_ON `a:v store_v` THEN
   RULE_ASSUM_TAC(REWRITE_RULE[FLATP1AUX_sv_rel_eqns]) THEN SEVPAUX_STRIPS_TAC THEN
   RVEQ_TAC THEN CASE_REWRITE_TAC[source_to_flatProof_match_result_rel_def] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `a':v` o
     check (fun th -> is_forall (concl th) && is_imp (snd (dest_forall (concl th))))) THEN
   REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   MAP_EVERY EXISTS_TAC [`env':(varN#v)list`; `st':(FFI)state`] THEN ASM_REWRITE_TAC[];
   (* Pas *)
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MAP_EVERY EXISTS_TAC [`CONS (i:varN,v:v) env'`; `st':(FFI)state`] THEN
   ASM_REWRITE_TAC[APPEND; alist_to_ns_cons; v_rel_eqns; CONS_11; PAIR_EQ] THEN
   ASM_MESON_TAC[];
   (* Ptannot *)
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MAP_EVERY EXISTS_TAC [`env':(varN#v)list`; `st':(FFI)state`] THEN ASM_REWRITE_TAC[];
   (* list nil *)
   REWRITE_TAC[MAP; flat_pmatch_def; source_to_flatProof_match_result_rel_def] THEN
   EXISTS_TAC `env':(varN#v)list` THEN ASM_REWRITE_TAC[];
   (* list cons *)
   REWRITE_TAC[MAP; flat_pmatch_def] THEN
   SUBGOAL_THEN `source_to_flatProof_match_result_rel genv env''
       (pmatch (sem_env_c (senv:(v)sem_env)) (state_refs (st':(FFI)state)) p v (APPEND env' env''))
       (flat_pmatch (s_i1:(C,FFI)flat_state) (compile_pat comp_map p) h' env_i1)`
     ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`env':(varN#v)list`; `st':(FFI)state`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP match_result_rel_imp) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[source_to_flatProof_match_result_rel_def] THENL
   [SUBGOAL_THEN `source_to_flatProof_match_result_rel genv env''
       (pmatch_list (sem_env_c (senv:(v)sem_env)) (state_refs (st':(FFI)state)) ps vs
          (APPEND env' env''))
       (flat_pmatch_list (s_i1:(C,FFI)flat_state) (MAP (compile_pat comp_map) ps) t' env_i1)`
      ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) && is_eq (lhand (concl th)))) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
     MAP_EVERY EXISTS_TAC [`env':(varN#v)list`; `st':(FFI)state`] THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP match_result_rel_imp) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[source_to_flatProof_match_result_rel_def];
    FIRST_X_ASSUM(MP_TAC o SPEC `env1:(varN#v)list` o
      check (fun th -> is_forall (concl th) && is_imp (snd (dest_forall (concl th))) &&
                       is_eq (lhand (snd (dest_forall (concl th)))))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> let h,_ = strip_comb (concl th) in
      is_const h && fst (dest_const h) = "source_to_flatProof_match_result_rel")) THEN
    ASM_REWRITE_TAC[source_to_flatProof_match_result_rel_def] THEN
    DISCH_THEN(X_CHOOSE_THEN `env3:(varN#v)list` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`env3:(varN#v)list`; `st':(FFI)state`] THEN ASM_REWRITE_TAC[]]]);;

(* HOL4 line 1836 (HOL4's s_i1 has the type ('f_orac_st,'ffi) flatSem$state) *)
let source_to_flatProof_pmatch = prove
 (`!genv comp_map2 shadowers senv comp_map.
     (!cenv s p v env r env' env'' env_i1 (s_i1:(C,FFI)flat_state) v_i1
      (st':(FFI)state).
      pmatch cenv s p v env = r /\
      source_to_flatProof_s_rel genv st' s_i1 /\
      global_env_inv genv comp_map2 shadowers senv /\
      genv_c_ok (global_env_c genv) /\
      genv_c_tys_ok (global_env_c genv) (global_env_tys genv) /\
      cenv = sem_env_c senv /\
      source_to_flat_environment_c comp_map2 = source_to_flat_environment_c comp_map /\
      env = APPEND env' env'' /\
      flat_state_globals s_i1 = global_env_v genv /\
      s = state_refs st' /\
      source_to_flatProof_v_rel genv v v_i1 /\
      source_to_flatProof_env_rel genv (alist_to_ns env') env_i1
      ==> ?r_i1. flat_pmatch s_i1 (compile_pat comp_map p) v_i1 env_i1 = r_i1 /\
                 source_to_flatProof_match_result_rel genv env'' r r_i1) /\
   (!cenv s ps vs env r env' env'' env_i1 (s_i1:(C,FFI)flat_state) vs_i1
      (st':(FFI)state).
      pmatch_list cenv s ps vs env = r /\
      global_env_inv genv comp_map2 shadowers senv /\
      genv_c_ok (global_env_c genv) /\
      genv_c_tys_ok (global_env_c genv) (global_env_tys genv) /\
      cenv = sem_env_c senv /\
      source_to_flat_environment_c comp_map2 = source_to_flat_environment_c comp_map /\
      env = APPEND env' env'' /\
      flat_state_globals s_i1 = global_env_v genv /\
      source_to_flatProof_s_rel genv st' s_i1 /\
      s = state_refs st' /\
      ALL2 (source_to_flatProof_v_rel genv) vs vs_i1 /\
      source_to_flatProof_env_rel genv (alist_to_ns env') env_i1
      ==> ?r_i1. flat_pmatch_list s_i1 (MAP (compile_pat comp_map) ps) vs_i1 env_i1 = r_i1 /\
                 source_to_flatProof_match_result_rel genv env'' r r_i1)`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`genv:global_env`; `comp_map2:source_to_flat_environment`;
                `shadowers:varN->bool`; `senv:(v)sem_env`;
                `comp_map:source_to_flat_environment`] FLATP1AUX_pmatch) THEN
  ASM_REWRITE_TAC[] THENL
  [DISCH_THEN(MP_TAC o SPECL [`cenv:env_ctor`; `s:(v store_v)list`; `p:pat`; `v:v`;
                              `env:(varN#v)list`] o CONJUNCT1) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`env':(varN#v)list`; `env'':(varN#v)list`;
     `env_i1:(varN#flat_v)list`; `s_i1:(C,FFI)flat_state`; `v_i1:flat_v`; `st':(FFI)state`]);
   DISCH_THEN(MP_TAC o SPECL [`cenv:env_ctor`; `s:(v store_v)list`; `ps:pat list`;
                              `vs:v list`; `env:(varN#v)list`] o CONJUNCT2) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPECL [`env':(varN#v)list`; `env'':(varN#v)list`;
     `env_i1:(varN#flat_v)list`; `s_i1:(C,FFI)flat_state`; `vs_i1:flat_v list`;
     `st':(FFI)state`])] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* compiler correctness *)

(* HOL4 line 1940 *)
let opt_bind_lem = prove
 (`opt_bind (NONE:A option) = \(x:B) (y:(A#B)list). y`,
  REWRITE_TAC[FUN_EQ_THM; opt_bind_def] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 1946 *)
let env_updated_lem = prove
 (`!env.
     flat_environment_v_fupd (\y. y) env = (env:(A)flat_environment)`,
  REWRITE_TAC[flat_environment_component_equality; flat_environment_INFO.ri_accfupds]);;

let FLATP1AUX_flat_evaluate_Let = prove
 (CASE_TERM `!env (s:(C,FFI)flat_state) t n e1 e2.
     flat_evaluate env s [flat_Let t n e1 e2] =
     match flat_evaluate env s [e1] with
       (s',Rval vs) ->
         flat_evaluate (flat_environment_v_fupd (opt_bind n (HD vs)) env) s' [e2]
     | res -> res`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [flat_evaluate_def] THEN REFL_TAC);;

(* HOL4 line 1952 *)
let evaluate_foldr_let_err = prove
 (`!env (s:(C,FFI)flat_state) s' exps e x t.
     flat_evaluate env s exps = (s', Rerr x)
     ==> flat_evaluate env s [ITLIST (flat_Let t NONE) exps e] = (s', Rerr x)`,
  SUBGOAL_THEN `!exps env (s:(C,FFI)flat_state) s' e x t.
     flat_evaluate env s exps = (s', Rerr x)
     ==> flat_evaluate env s [ITLIST (flat_Let t NONE) exps e] = (s', Rerr x)`
    (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC[flat_evaluate_def; PAIR_EQ; distinctness "result"];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[flat_evaluate_cons]) THEN
  REWRITE_TAC[ITLIST; FLATP1AUX_flat_evaluate_Let] THEN
  MP_TAC(ISPEC `flat_evaluate env (s:(C,FFI)flat_state) [h]` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(C,FFI)flat_state`
    (X_CHOOSE_THEN `r1:(flat_v list,flat_v)result` SUBST1_TAC)) THEN
  CASE_REWRITE_TAC[] THEN CASES_ON `r1:(flat_v list,flat_v)result` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[opt_bind_lem; env_updated_lem] THEN
  MP_TAC(ISPEC `flat_evaluate env (s1:(C,FFI)flat_state) t` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:(C,FFI)flat_state`
    (X_CHOOSE_THEN `r2:(flat_v list,flat_v)result` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN CASES_ON `r2:(flat_v list,flat_v)result` THEN
  CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 1971 *)
let env_domain_eq_def = cake_def
  `env_domain_eq (var_map:source_to_flat_environment) (env:(A)sem_env) <=>
     nsDom (source_to_flat_environment_v var_map) = nsDom (sem_env_v env) /\
     nsDomMod (source_to_flat_environment_v var_map) = nsDomMod (sem_env_v env) /\
     nsDom (source_to_flat_environment_c var_map) = nsDom (sem_env_c env) /\
     nsDomMod (source_to_flat_environment_c var_map) = nsDomMod (sem_env_c env)`;;

(* HOL4 line 1979 *)
let env_domain_eq_append = prove
 (`!env1 env1' env2 env2'.
     env_domain_eq env1 (env1':(v)sem_env) /\ env_domain_eq env2 env2'
   ==> env_domain_eq (extend_env env1 env2) (extend_dec_env env1' env2')`,
  REWRITE_TAC[env_domain_eq_def; extend_env_def; extend_dec_env_def;
              source_to_flat_environment_INFO.ri_accessors; sem_env_INFO.ri_accessors] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`source_to_flat_environment_v env1`; `source_to_flat_environment_v env2`;
                 `sem_env_v (env1':(v)sem_env)`; `sem_env_v (env2':(v)sem_env)`]
                nsDom_nsAppend_equal) THEN
  MP_TAC(ISPECL [`source_to_flat_environment_c env1`; `source_to_flat_environment_c env2`;
                 `sem_env_c (env1':(v)sem_env)`; `sem_env_c (env2':(v)sem_env)`]
                nsDom_nsAppend_equal) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let FLATP1AUX_nsDom_eq_NONE = prove
 (`!(a:(M,N,V1)namespace) (b:(M,N,V2)namespace) x.
     nsDom a = nsDom b ==> (nsLookup a x = NONE <=> nsLookup b x = NONE)`,
  REWRITE_TAC[nsDom_def; EXTENSION; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:(M,N)id`) THEN
  MP_TAC(ISPEC `nsLookup (a:(M,N,V1)namespace) x` (cases "option")) THEN
  MP_TAC(ISPEC `nsLookup (b:(M,N,V2)namespace) x` (cases "option")) THEN
  STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN MESON_TAC[]);;

let FLATP1AUX_nsDomMod_eq_NONE = prove
 (`!(a:(M,N,V1)namespace) (b:(M,N,V2)namespace) p.
     nsDomMod a = nsDomMod b ==> (nsLookupMod a p = NONE <=> nsLookupMod b p = NONE)`,
  REWRITE_TAC[nsDomMod_def; EXTENSION; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:M list`) THEN
  MP_TAC(ISPEC `nsLookupMod (a:(M,N,V1)namespace) p` (cases "option")) THEN
  MP_TAC(ISPEC `nsLookupMod (b:(M,N,V2)namespace) p` (cases "option")) THEN
  STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN MESON_TAC[]);;

(* HOL4 line 1991 *)
let global_env_inv_append = prove
 (`!genv var_map1 var_map2 env1 env2.
     env_domain_eq var_map1 env1 /\
     global_env_inv genv var_map1 {} env1 /\
     global_env_inv genv var_map2 {} env2
     ==> global_env_inv genv (extend_env var_map1 var_map2) {}
           (extend_dec_env env1 env2)`,
  REWRITE_TAC[env_domain_eq_def; v_rel_global_eqn; extend_env_def; extend_dec_env_def;
              source_to_flat_environment_INFO.ri_accessors; sem_env_INFO.ri_accessors;
              IMAGE_CLAUSES; NOT_IN_EMPTY] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
  [MAP_EVERY X_GEN_TAC [`x:(modN,varN)id`; `v:v`] THEN
   REWRITE_TAC[nsLookup_nsAppend_some] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`x:(modN,varN)id`; `v:v`] o
      check (fun th -> is_forall (concl th) &&
                       free_in `sem_env_v (env1:(v)sem_env)` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:(modN,varN)id`; `v:v`] o
      check (fun th -> is_forall (concl th) &&
                       free_in `sem_env_v (env2:(v)sem_env)` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `v':flat_v`; `t:tra`] THEN ASM_REWRITE_TAC[] THEN
    DISJ2_TAC THEN
    ASSUM_LIST(fun thl -> REWRITE_TAC(mapfilter (MATCH_MP FLATP1AUX_nsDom_eq_NONE) thl @
                                      mapfilter (MATCH_MP FLATP1AUX_nsDomMod_eq_NONE) thl)) THEN
    ASM_REWRITE_TAC[]];
   MAP_EVERY X_GEN_TAC [`x:(modN,conN)id`; `arity:num`; `stamp:stamp`] THEN
   REWRITE_TAC[nsLookup_nsAppend_some] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`x:(modN,conN)id`; `arity:num`; `stamp:stamp`] o
      check (fun th -> is_forall (concl th) &&
                       free_in `sem_env_c (env1:(v)sem_env)` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:(modN,conN)id`; `arity:num`; `stamp:stamp`] o
      check (fun th -> is_forall (concl th) &&
                       free_in `sem_env_c (env2:(v)sem_env)` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`cn:ctor_id`; `ty_gp:type_group_id`] THEN ASM_REWRITE_TAC[] THEN
    DISJ2_TAC THEN
    ASSUM_LIST(fun thl -> REWRITE_TAC(mapfilter (MATCH_MP FLATP1AUX_nsDom_eq_NONE) thl @
                                      mapfilter (MATCH_MP FLATP1AUX_nsDomMod_eq_NONE) thl)) THEN
    ASM_REWRITE_TAC[]]]);;

(* HOL4 line 2022: result_rel_imp, the first implication of result_rel_cases *)
let result_rel_imp = prove
 (`!(f:global_env->A->B->bool) genv a0 a1.
     source_to_flatProof_result_rel f genv a0 a1
     ==> (?v v'. a0 = Rval v /\ a1 = Rval v' /\ f genv v v') \/
         (?v v'. a0 = Rerr (Rraise v) /\ a1 = Rerr (Rraise v') /\
                 source_to_flatProof_v_rel genv v v') \/
         (?a. a0 = Rerr (Rabort a) /\ a1 = Rerr (Rabort a))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[source_to_flatProof_result_rel_cases] THEN MESON_TAC[]);;

(* HOL4 line 2024 *)
let idx_prev_def = cake_def
  `idx_prev idx idx2 <=>
     next_indices_vidx idx <= next_indices_vidx idx2 /\
     next_indices_tidx idx <= next_indices_tidx idx2 /\
     next_indices_eidx idx <= next_indices_eidx idx2`;;

(* HOL4 line 2029 *)
let idx_prev_refl = prove
 (`!idx.
     idx_prev idx idx`,
  REWRITE_TAC[idx_prev_def; LE_REFL]);;

(* HOL4 line 2035 *)
let idx_prev_trans = prove
 (`!idx idx2 idx3.
     idx_prev idx idx2 /\ idx_prev idx2 idx3 ==> idx_prev idx idx3`,
  REWRITE_TAC[idx_prev_def] THEN ARITH_TAC);;

(* HOL4 line 2041 *)
let idx_types_INDUCT,idx_types_RECURSION = cake_type
  "idx_types = Idx_Var | Idx_Type | Idx_Exn";;

(* HOL4 line 2046 *)
let idx_types_FORALL = prove
 (`!P.
     (!x:idx_types. P x) = (P Idx_Var /\ P Idx_Type /\ P Idx_Exn)`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN STRIP_TAC THEN GEN_TAC THEN
  CASES_ON `x:idx_types` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 2053 *)
let ALL_DISJOINT_DEF = cake_def
  `ALL_DISJOINT (xs:(A->bool)list) <=>
     !i j. i < LENGTH xs /\ j < LENGTH xs /\ ~(i = j) ==> EL i xs INTER EL j xs = {}`;;

let FLATP1AUX_ALL_DISJOINT_CONS = prove
 (`!(x:A->bool) xs. ALL_DISJOINT (CONS x xs) <=>
                    ALL (\y. DISJOINT x y) xs /\ ALL_DISJOINT xs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL_DISJOINT_DEF; LENGTH; GSYM ALL_EL] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[LISTAUX_FORALL_LT_SUC; EL; HD; TL; NOT_SUC; GSYM NOT_SUC; SUC_INJ] THEN
  REWRITE_TAC[EVERY_EL; DISJOINT] THEN
  MESON_TAC[INTER_COMM]);;

let FLATP1AUX_ALL_DISJOINT_NIL = prove
 (`ALL_DISJOINT ([]:(A->bool)list)`,
  REWRITE_TAC[ALL_DISJOINT_DEF; LENGTH; CONJUNCT1 LT]);;

(* HOL4 line 2058 *)
let ALL_DISJOINT_CONS = prove
 (`!x y zs.
     (ALL_DISJOINT [x:A->bool] = T) /\
   (ALL_DISJOINT (CONS (x:A->bool) (CONS y zs)) =
      (DISJOINT x y /\ ALL_DISJOINT (CONS (x UNION y) zs)))`,
  REWRITE_TAC[FLATP1AUX_ALL_DISJOINT_CONS; FLATP1AUX_ALL_DISJOINT_NIL; ALL; DISJOINT_UNION;
              GSYM AND_ALL] THEN
  REPEAT GEN_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN MESON_TAC[]);;

(* HOL4 line 2070 *)
let idx_block_def = cake_def
  `idx_block start_idx end_idx =
     {(i, Idx_Var) | next_indices_vidx start_idx <= i /\ i < next_indices_vidx end_idx}
     UNION {(i, Idx_Type) | next_indices_tidx start_idx <= i /\
                            i < next_indices_tidx end_idx}
     UNION {(i, Idx_Exn) | next_indices_eidx start_idx <= i /\
                           i < next_indices_eidx end_idx}`;;

(* HOL4 line 2077 *)
let idx_final_block_def = cake_def
  `idx_final_block start_idx =
     {(i, Idx_Var) | next_indices_vidx start_idx <= i}
     UNION {(i, Idx_Type) | next_indices_tidx start_idx <= i}
     UNION {(i, Idx_Exn) | next_indices_eidx start_idx <= i}`;;

(* HOL4 line 2084 *)
let genv_allocated_idxs_def = cake_def
  `genv_allocated_idxs genv =
     {(i, Idx_Var) | i < LENGTH (global_env_v genv) /\ ~(EL i (global_env_v genv) = NONE)}
     UNION {(i, Idx_Type) | ?cn a. ((cn, SOME i), a) IN FDOM (global_env_c genv)}
     UNION {(i, Idx_Type) | i IN FDOM (global_env_tys genv)}
     UNION {(i, Idx_Exn) | ?a. ((i, NONE), a) IN FDOM (global_env_c genv)}`;;

(* simple invariants on env generations and stores: allocation from the     *)
(* next field will always be free                                           *)

(* HOL4 line 2094 *)
let env_gen_inv_def = cake_def
  `env_gen_inv (e:environment_generation_store) <=>
     domain (environment_generation_store_envs e) SUBSET
       pred_set_count (environment_generation_store_next e)`;;

(* HOL4 line 2099 *)
let env_store_inv_def = cake_def
  `env_store_inv (e:environment_store) <=>
     domain (environment_store_env_gens e) SUBSET pred_set_count (environment_store_next e)`;;

let FLATP1AUX_subspt_insert_fresh = prove
 (`!k (v:A) t. ~(k IN domain t) ==> subspt t (insert k v t)`,
  REWRITE_TAC[subspt_lookup; lookup_insert; domain_lookup] THEN MESON_TAC[]);;

(* HOL4 line 2104 *)
let inc_compile_prog_env_submap = prove
 (`!env_id c p c' p'.
     inc_compile_prog env_id c p = (c', p') /\
   env_store_inv (source_to_flat_config_envs c)
   ==> env_store_inv (source_to_flat_config_envs c') /\
       subspt (environment_store_env_gens (source_to_flat_config_envs c))
              (environment_store_env_gens (source_to_flat_config_envs c'))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[inc_compile_prog_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT PAIRARG_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[source_to_flat_config_INFO.ri_accfupds; K_THM;
              environment_store_INFO.ri_accessors] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[env_store_inv_def]) THEN
  REWRITE_TAC[env_store_inv_def; environment_store_INFO.ri_accessors; domain_insert] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[INSERT_SUBSET; pred_set_count_DEF; IN_ELIM_THM] THEN CONJ_TAC THENL
   [ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
      fst (dest_const (rator (rator (concl th)))) = "SUBSET")) THEN
    REWRITE_TAC[SUBSET; pred_set_count_DEF; IN_ELIM_THM] THEN MESON_TAC[ARITH_RULE `m < n ==> m < n + 1`]];
   MATCH_MP_TAC FLATP1AUX_subspt_insert_fresh THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
      fst (dest_const (rator (rator (concl th)))) = "SUBSET")) THEN
   REWRITE_TAC[SUBSET; pred_set_count_DEF; IN_ELIM_THM] THEN MESON_TAC[LT_REFL]]);;

(* HOL4 line 2130: the compiler state stored in the source oracle is the    *)
(* one from applying compile_prog                                            *)
let src_orac_step_invs_def = cake_def
  `src_orac_step_invs (ci:(v->(source_to_flat_config#C)option)option)
                      (g:dec list->dec list) (eval_state:(eval_state)option) <=>
     match (ci, eval_state) with
       (NONE, NONE) -> T
     | (SOME dec, SOME (EvalOracle s)) ->
         (!k env_id state_v decs.
            eval_oracle_state_oracle s k = (env_id, state_v, decs)
            ==> ?c x. dec state_v = SOME (c, x)) /\
         (let c_orac = FST o THE o dec o FST o SND o eval_oracle_state_oracle s in
          !k env_id state_v decs.
            eval_oracle_state_oracle s k = (env_id, state_v, decs)
            ==> c_orac (SUC k) = FST (inc_compile_prog env_id (c_orac k) (g decs)))
     | _ -> F`;;

(* HOL4 line 2146: the flatLang oracle is derived from the source oracle by *)
(* compile_prog, and the two compile oracles agree also                      *)
let orac_rel_inner_def = cake_def
  `orac_rel_inner (dec:v->(source_to_flat_config#C)option) s (s_compiler:compiler_fun)
                  (g:dec list->dec list) (c:(C)install_config) <=>
     !k env_id state_v decs.
       eval_oracle_state_oracle s k = (env_id, state_v, decs)
       ==> (let x = THE (dec state_v) in
            let f_decs = SND (inc_compile_prog env_id (FST x) (g decs)) in
            install_config_compile_oracle c k = (SND x, f_decs) /\
            (~(s_compiler (env_id, state_v, decs) = NONE)
             ==> ?bytes words f_st st_v2.
                   install_config_compile c (SND x) f_decs = SOME (bytes, words, f_st) /\
                   s_compiler (env_id, state_v, decs) = SOME (st_v2, bytes, words) /\
                   (!x2. dec st_v2 = SOME x2 ==> SND x2 = f_st)))`;;

(* HOL4 line 2160 *)
let orac_rel_def = cake_def
  `orac_rel (interp:(v->(source_to_flat_config#C)option)option) (g:dec list->dec list)
            (src_eval:(eval_state)option) (flat_eval:(C)install_config) <=>
     match (interp, src_eval) with
       (_, NONE) -> T
     | (SOME dec, SOME (EvalOracle s)) ->
         ?s_compiler. eval_oracle_state_custom_do_eval s = do_eval_oracle s_compiler g /\
                      orac_rel_inner dec s s_compiler g flat_eval
     | _ -> F`;;

(* HOL4 line 2171 *)
let orac_rel_SOME_eval = prove
 (`!interp g eval_state flat_eval.
     orac_rel interp g (SOME eval_state) (flat_eval:(C)install_config)
   ==> ?dec orac_st. interp = SOME dec /\ eval_state = EvalOracle orac_st`,
  REPEAT GEN_TAC THEN REWRITE_TAC[orac_rel_def] THEN
  CASES_ON `interp:(v->(source_to_flat_config#C)option)option` THEN
  CASES_ON `eval_state:eval_state` THEN CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4 line 2179 *)
let src_orac_next_cfg_inner_def = cake_def
  `src_orac_next_cfg_inner (interp:(v->(source_to_flat_config#C)option)option)
                           (orac_0:compiler_args) =
     match (interp, orac_0) with
       (SOME dec, (env_id, state_v, decs)) ->
         (match dec state_v with
            SOME (c, x) -> SOME c
          | _ -> NONE)
     | _ -> NONE`;;

(* HOL4 line 2189 *)
let src_orac_next_cfg_def = cake_def
  `src_orac_next_cfg (interp:(v->(source_to_flat_config#C)option)option)
                     (eval_state:(eval_state)option) =
     match eval_state with
       SOME (EvalOracle s) -> src_orac_next_cfg_inner interp (eval_oracle_state_oracle s 0)
     | _ -> NONE`;;

(* HOL4 line 2197: every env stored in the eval state is related to a      *)
(* concrete env representation in the next oracle state                      *)
let src_orac_env_invs_def = cake_def
  `src_orac_env_invs (interp:(v->(source_to_flat_config#C)option)option) genv
                     (eval_state:(eval_state)option) <=>
     match eval_state with
       NONE -> T
     | SOME (EvalOracle s) ->
         (?c. src_orac_next_cfg interp eval_state = SOME c /\
              env_store_inv (source_to_flat_config_envs c) /\
              environment_store_next (source_to_flat_config_envs c) =
                LENGTH (eval_oracle_state_envs s) /\
              (!g_id id. g_id < LENGTH (eval_oracle_state_envs s) /\
                         id < LENGTH (EL g_id (eval_oracle_state_envs s))
                         ==> ?comp_map_gen comp_map.
                               lookup g_id (environment_store_env_gens
                                              (source_to_flat_config_envs c)) =
                                 SOME comp_map_gen /\
                               lookup id comp_map_gen = SOME comp_map /\
                               global_env_inv genv comp_map {}
                                 (EL id (EL g_id (eval_oracle_state_envs s)))))
     | _ -> F`;;

(* HOL4 line 2214 (HOL4 leaves the EvalDecs case unspecified: ARB) *)
let src_orac_gen_inv_def = cake_def
  `src_orac_gen_inv (eval_state:(eval_state)option) <=>
     match eval_state with
       NONE -> T
     | SOME (EvalOracle s) ->
         eval_oracle_state_generation s < LENGTH (eval_oracle_state_envs s)
     | SOME (EvalDecs d) -> ARB`;;

(* HOL4 line 2222 *)
let src_orac_invs_def = cake_def
  `src_orac_invs (interp:(v->(source_to_flat_config#C)option)option) g genv
                 (eval_state:(eval_state)option) <=>
     src_orac_step_invs interp g eval_state /\
     src_orac_env_invs interp genv eval_state /\
     src_orac_gen_inv eval_state`;;

(* HOL4 line 2229 *)
let src_orac_invs_weak = prove
 (`!interp g genv src_eval genv'.
     src_orac_invs (interp:(v->(source_to_flat_config#C)option)option) g genv src_eval /\
   global_env_c genv SUBMAP global_env_c genv' /\
   global_env_tys genv SUBMAP global_env_tys genv' /\
   subglobals (global_env_v genv) (global_env_v genv')
   ==> src_orac_invs interp g genv' src_eval`,
  REWRITE_TAC[src_orac_invs_def; src_orac_env_invs_def] THEN REPEAT GEN_TAC THEN
  CASES_ON `src_eval:(eval_state)option` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a:eval_state` THEN CASE_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `c:source_to_flat_config` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`g_id:num`; `id:num`] o
    check (fun th -> is_forall (concl th) && length (fst (strip_forall (concl th))) = 2)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`comp_map_gen:source_to_flat_environment spt`;
                        `comp_map:source_to_flat_environment`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC global_env_inv_weak THEN
  EXISTS_TAC `genv:global_env` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 2247: the current generation of envs in the compiler state     *)
(* matches that generation in oracle state                                   *)
let env_gen_rel_def = cake_def
  `env_gen_rel (gen:environment_generation_store) (eval_state:(eval_state)option) <=>
     match eval_state with
       NONE -> T
     | SOME (EvalOracle s) ->
         environment_generation_store_generation gen = eval_oracle_state_generation s /\
         eval_oracle_state_generation s < LENGTH (eval_oracle_state_envs s) /\
         environment_generation_store_next gen =
           LENGTH (EL (eval_oracle_state_generation s) (eval_oracle_state_envs s))
     | _ -> F`;;

(* HOL4 line 2260: the oracle state is in the future, where this generation *)
(* has already been compiled and its environments saved                      *)
let env_gen_future_rel_def = cake_def
  `env_gen_future_rel (interp:(v->(source_to_flat_config#C)option)option)
                      (gen:environment_generation_store) (eval_state:(eval_state)option) <=>
     match src_orac_next_cfg interp eval_state with
       SOME c -> ?gen_final.
                   lookup (environment_generation_store_generation gen)
                     (environment_store_env_gens (source_to_flat_config_envs c)) =
                     SOME gen_final /\
                   subspt (environment_generation_store_envs gen) gen_final
     | NONE -> T`;;

(* HOL4 line 2282: indexes and ranges (see the HOL4 comment) *)
let idx_range_rel_def = cake_def
  `idx_range_rel (interp:(v->(source_to_flat_config#C)option)option) genv s_n_ts s_n_en
                 (s_eval:(eval_state)option) idxs <=>
     ?idx end_idx fin_idx other_blocks.
       idxs = (idx, end_idx, other_blocks) /\
       (match src_orac_next_cfg interp s_eval with
          NONE -> T
        | SOME c -> fin_idx = source_to_flat_config_next c) /\
       idx_prev end_idx fin_idx /\
       ALL_DISJOINT [idx_block idx end_idx; idx_final_block fin_idx; other_blocks;
                     genv_allocated_idxs genv] /\
       (!cn t. t >= s_n_ts ==> ~(TypeStamp cn t IN FRANGE (global_env_c genv))) /\
       (!cn. cn >= s_n_en ==> ~(ExnStamp cn IN FRANGE (global_env_c genv)))`;;

(* HOL4 line 2298 *)
let fin_idx_match_def = cake_def
  `fin_idx_match len end_idx (next_cfg:(source_to_flat_config)option) <=>
     match next_cfg with
       NONE -> next_indices_vidx end_idx <= len
     | SOME c -> next_indices_vidx (source_to_flat_config_next c) = len`;;

(* HOL4 line 2304 *)
let eval_ref_inv_def = cake_def
  `eval_ref_inv first_global (first_ref:(flat_v store_v)list) <=>
     first_global = [SOME (flat_Loc T 0)] /\ ?v. first_ref = [Refv v]`;;

(* HOL4 line 2310 *)
let source_to_flatProof_invariant_def = cake_def
  `source_to_flatProof_invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv idxs
             (s:(FFI)state) (s_i1:(C,FFI)flat_state) <=>
     genv_c_ok (global_env_c genv) /\
     genv_c_tys_ok (global_env_c genv) (global_env_tys genv) /\
     source_to_flatProof_s_rel genv s s_i1 /\
     idx_range_rel interp genv (state_next_type_stamp s) (state_next_exn_stamp s)
       (state_eval_state s) idxs /\
     src_orac_invs interp g genv (state_eval_state s) /\
     orac_rel interp g (state_eval_state s) (flat_state_eval_config s_i1) /\
     global_env_v genv = flat_state_globals s_i1 /\
     eval_ref_inv (TAKE 1 (flat_state_globals s_i1)) (TAKE 1 (flat_state_refs s_i1)) /\
     env_gen_inv gen /\
     fin_idx_match (LENGTH (flat_state_globals s_i1)) (FST (SND idxs))
       (src_orac_next_cfg interp (state_eval_state s))`;;

(* HOL4 line 2327: subsequent oracle config will still have the previous   *)
(* envs in store                                                             *)
let orac_config_envs_subspt_def = cake_def
  `orac_config_envs_subspt (interp:(v->(source_to_flat_config#C)option)option)
                           (es1:(eval_state)option) es2 <=>
     OPTREL (\c c'. subspt (environment_store_env_gens (source_to_flat_config_envs c))
                           (environment_store_env_gens (source_to_flat_config_envs c')))
       (src_orac_next_cfg interp es1) (src_orac_next_cfg interp es2)`;;

let FLATP1AUX_OPTREL_trans = prove
 (`!(R:A->A->bool) a b c.
     (!x y z. R x y /\ R y z ==> R x z) /\ OPTREL R a b /\ OPTREL R b c ==> OPTREL R a c`,
  REWRITE_TAC[OPTREL_DEF] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT; option_INJ]) THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN RVEQ_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 2334 *)
let orac_config_envs_subspt_trans = prove
 (`!interp es1 es2 es3.
     orac_config_envs_subspt (interp:(v->(source_to_flat_config#C)option)option) es1 es2 /\
   orac_config_envs_subspt interp es2 es3
   ==> orac_config_envs_subspt interp es1 es3`,
  REWRITE_TAC[orac_config_envs_subspt_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FLATP1AUX_OPTREL_trans THEN
  EXISTS_TAC `src_orac_next_cfg (interp:(v->(source_to_flat_config#C)option)option) es2` THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  MESON_TAC[subspt_trans]);;

(* HOL4 line 2344 *)
let orac_config_envs_subspt_refl = prove
 (`!interp es1.
     orac_config_envs_subspt (interp:(v->(source_to_flat_config#C)option)option) es1 es1`,
  REWRITE_TAC[orac_config_envs_subspt_def; OPTREL_DEF] THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `src_orac_next_cfg (interp:(v->(source_to_flat_config#C)option)option) es1`
    (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  MESON_TAC[subspt_refl]);;

(* HOL4 line 2353: this relation holds over any successful evaluate or     *)
(* evaluate_decs: the eval generation stack will be back to the same        *)
(* generation                                                                *)
let eval_state_call_rel_def = cake_def
  `eval_state_call_rel (es1:(eval_state)option) (es2:(eval_state)option) <=>
     match es1 with
       SOME (EvalOracle s1) ->
         ?s2. es2 = SOME (EvalOracle s2) /\
              eval_oracle_state_generation s2 = eval_oracle_state_generation s1 /\
              LENGTH (eval_oracle_state_envs s1) <= LENGTH (eval_oracle_state_envs s2) /\
              (!i. i < eval_oracle_state_generation s1
                   ==> EL i (eval_oracle_state_envs s2) = EL i (eval_oracle_state_envs s1))
     | _ -> T`;;

(* HOL4 line 2363 *)
let eval_state_call_rel_trans = prove
 (`!es1 es2 es3.
     eval_state_call_rel es1 es2 /\ eval_state_call_rel es2 es3
   ==> eval_state_call_rel es1 es3`,
  REWRITE_TAC[eval_state_call_rel_def] THEN REPEAT GEN_TAC THEN
  CASES_ON `es1:(eval_state)option` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a:eval_state` THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN SEVPAUX_STRIPS_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; injectivity "eval_state"]) THEN RVEQ_TAC THEN
  EXISTS_TAC `s2':eval_oracle_state` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[LE_TRANS]; ASM_MESON_TAC[]]);;

(* HOL4 line 2372 *)
let eval_state_call_rel_refl = prove
 (`!es1.
     eval_state_call_rel es1 es1`,
  REWRITE_TAC[eval_state_call_rel_def] THEN GEN_TAC THEN
  CASES_ON `es1:(eval_state)option` THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `a:eval_state` THEN CASE_REWRITE_TAC[] THEN
  EXISTS_TAC `a':eval_oracle_state` THEN REWRITE_TAC[LE_REFL]);;

(* HOL4 line 2379 *)
let orac_forward_rel_def = cake_def
  `orac_forward_rel (interp:(v->(source_to_flat_config#C)option)option)
                    (es1:(eval_state)option) es2 <=>
     orac_config_envs_subspt interp es1 es2 /\ eval_state_call_rel es1 es2`;;

(* HOL4 line 2385 *)
let orac_forward_rel_trans = prove
 (`!interp es1 es2 es3.
     orac_forward_rel (interp:(v->(source_to_flat_config#C)option)option) es1 es2 /\
   orac_forward_rel interp es2 es3
   ==> orac_forward_rel interp es1 es3`,
  REWRITE_TAC[orac_forward_rel_def] THEN
  MESON_TAC[orac_config_envs_subspt_trans; eval_state_call_rel_trans]);;

(* HOL4 line 2393 *)
let orac_forward_rel_refl = prove
 (`!interp es1.
     orac_forward_rel (interp:(v->(source_to_flat_config#C)option)option) es1 es1`,
  REWRITE_TAC[orac_forward_rel_def; orac_config_envs_subspt_refl; eval_state_call_rel_refl]);;
let _ = cake_add_simps [orac_forward_rel_refl];;

let FLATP1AUX_CONTRA_TAC : tactic =
  FIRST_ASSUM(fun th -> FIRST_ASSUM(fun th2 ->
    if concl th2 = mk_neg (concl th) then CONTR_TAC (MP (NOT_ELIM th2) th)
    else NO_TAC));;

let FLATP1AUX_pmatch_invariant = prove
 (`!interp v g gen genv idxs st st' comp_map2 env env' locals comp_map v' p.
     source_to_flatProof_invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv idxs
     (st:(FFI)state) (st':(C,FFI)flat_state) /\
   env_all_rel genv comp_map2 env env' locals /\
   source_to_flat_environment_c comp_map2 = source_to_flat_environment_c comp_map /\
   source_to_flatProof_v_rel genv v v'
   ==> source_to_flatProof_match_result_rel genv []
         (pmatch (sem_env_c env) (state_refs st) p v [])
         (flat_pmatch st' (compile_pat comp_map p) v' [])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[source_to_flatProof_invariant_def; env_all_rel_cases] THEN STRIP_TAC THEN
  RVEQ_TAC THEN REWRITE_TAC[sem_env_INFO.ri_accessors] THEN
  MP_TAC(SPECL [`genv:global_env`; `comp_map2:source_to_flat_environment`;
                `set_of_list (MAP FST (l:(varN#v)list))`; `env'':(v)sem_env`;
                `comp_map:source_to_flat_environment`] FLATP1AUX_pmatch) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`sem_env_c (env'':(v)sem_env)`; `state_refs (st:(FFI)state)`;
                             `p:pat`; `v:v`; `[]:(varN#v)list`] o CONJUNCT1) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`[]:(varN#v)list`; `[]:(varN#v)list`; `[]:(varN#flat_v)list`;
                             `st':(C,FFI)flat_state`; `v':flat_v`; `st:(FFI)state`]) THEN
  ASM_REWRITE_TAC[APPEND; alist_to_ns_nil; v_rel_eqns]);;

(* HOL4 line 2400 *)
let can_pmatch_all_IMP_pmatch_rows = prove
 (`!env st pes v interp g gen genv idxs s_i1 comp_map env_i1 locals v' t ts.
     can_pmatch_all (sem_env_c env) (state_refs st) (MAP FST pes) v /\
   source_to_flatProof_invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv idxs
     (st:(FFI)state) (s_i1:(C,FFI)flat_state) /\
   env_all_rel genv comp_map env env_i1 locals /\
   source_to_flatProof_v_rel genv v v'
   ==> ~(pmatch_rows
           (compile_pes t
              (source_to_flat_environment_v_fupd
                 (K (bind_locals ts locals (source_to_flat_environment_v comp_map)))
                 comp_map) pes)
           s_i1 v' = Match_type_error)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[source_to_flat_compile_exp_def; pmatch_rows_def;
              distinctness "match_result"] THEN
  SPEC_TAC(`h:pat#exp`,`h:pat#exp`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:pat`; `e:exp`] THEN
  REWRITE_TAC[MAP; can_pmatch_all_def; source_to_flat_compile_exp_def; LET_DEF;
              LET_END_DEF; pmatch_rows_def] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`interp:(v->(source_to_flat_config#C)option)option`; `v:v`;
                `g:dec list->dec list`; `gen:environment_generation_store`;
                `genv:global_env`; `idxs:next_indices#next_indices#(num#idx_types->bool)`;
                `st:(FFI)state`; `s_i1:(C,FFI)flat_state`;
                `comp_map:source_to_flat_environment`; `env:(v)sem_env`;
                `env_i1:(flat_v)flat_environment`; `locals:varN list`;
                `source_to_flat_environment_v_fupd
                   (K (bind_locals ts locals (source_to_flat_environment_v comp_map)))
                   comp_map`; `v':flat_v`; `p:pat`] FLATP1AUX_pmatch_invariant) THEN
  ASM_REWRITE_TAC[source_to_flat_environment_INFO.ri_accfupds] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP match_result_rel_imp th)) THEN
  TRY FLATP1AUX_CONTRA_TAC THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[distinctness "match_result"] THEN
  (SUBGOAL_THEN `~(pmatch_rows (compile_pes t' (source_to_flat_environment_v_fupd
                   (K (bind_locals ts locals (source_to_flat_environment_v comp_map)))
                   comp_map) t) (s_i1:(C,FFI)flat_state) v' = Match_type_error)`
    MP_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
  SPEC_TAC(`pmatch_rows (compile_pes t' (source_to_flat_environment_v_fupd
                   (K (bind_locals ts locals (source_to_flat_environment_v comp_map)))
                   comp_map) t) (s_i1:(C,FFI)flat_state) v'`,
           `m:((varN#flat_v)list#flat_pat#flat_exp)match_result`) THEN
  GEN_TAC THEN CASES_ON `m:((varN#flat_v)list#flat_pat#flat_exp)match_result` THEN
  CASE_REWRITE_TAC[distinctness "match_result"]);;

(* HOL4 line 2428 *)
let invariant_globals = prove
 (`!interp g gen genv idxs s s_i1.
     source_to_flatProof_invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv idxs
     (s:(FFI)state) (s_i1:(C,FFI)flat_state)
   ==> flat_state_globals s_i1 = global_env_v genv`,
  REWRITE_TAC[source_to_flatProof_invariant_def] THEN MESON_TAC[]);;

(* HOL4 line 2434 *)
let invariant_genv_c_ok = prove
 (`!interp g gen genv idxs s s_i1.
     source_to_flatProof_invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv idxs
     (s:(FFI)state) (s_i1:(C,FFI)flat_state)
   ==> genv_c_ok (global_env_c genv)`,
  SIMP_TAC[source_to_flatProof_invariant_def]);;

(* HOL4 line 2440 *)
let invariant_change_clock = prove
 (`!interp g gen genv env st1 st2 k.
     source_to_flatProof_invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv env
     (st1:(FFI)state) (st2:(C,FFI)flat_state)
   ==> source_to_flatProof_invariant interp g gen genv env (state_clock_fupd (K k) st1)
         (flat_state_clock_fupd (K k) st2)`,
  REWRITE_TAC[source_to_flatProof_invariant_def; source_to_flatProof_s_rel_cases; state_INFO.ri_accfupds;
              flat_state_INFO.ri_accfupds; K_THM] THEN MESON_TAC[]);;

(* HOL4 line 2447 *)
let invariant_dec_clock = prove
 (`!interp g gen genv env st1 st2.
     source_to_flatProof_invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv env
     (st1:(FFI)state) (st2:(C,FFI)flat_state)
   ==> state_clock st1 = flat_state_clock st2 /\
       source_to_flatProof_invariant interp g gen genv env (dec_clock st1) (flat_dec_clock st2)`,
  REWRITE_TAC[source_to_flatProof_invariant_def; source_to_flatProof_s_rel_cases; state_INFO.ri_accfupds;
              flat_state_INFO.ri_accfupds; K_THM; dec_clock_def; flat_dec_clock_def] THEN
  MESON_TAC[]);;

(* HOL4 line 2456 *)
let v_rel_Bool_eqn = prove
 (`!genv b v.
     genv_c_ok (global_env_c genv)
   ==> (source_to_flatProof_v_rel genv (Boolv b) v <=> v = flat_Boolv b)`,
  MESON_TAC[FLATP1AUX_v_rel_Boolv]);;

(* HOL4 line 2466 *)
let source_to_flatProof_evaluate_Bool = prove
 (`!genv s s' env t b.
     source_to_flatProof_s_rel genv (s:(FFI)state) (s':(C,FFI)flat_state) /\
   genv_c_ok (global_env_c genv)
   ==> flat_evaluate env s' [flat_Bool t b] = (s', Rval [flat_Boolv b])`,
  REWRITE_TAC[flat_Bool_def; flat_evaluate_def; REVERSE; flat_Boolv_def; bool_to_tag_def] THEN
  CASE_REWRITE_TAC[REVERSE]);;

(* HOL4 line 2477 (flatSem's Boolv) *)
let source_to_flatProof_Boolv_11 = prove
 (`!b b'.
     (flat_Boolv b = flat_Boolv b') = (b = b')`,
  REWRITE_TAC[FLATP1AUX_flat_Boolv_11]);;

(* HOL4 line 2483 *)
let opt_case_bool_eq = prove
 (`!opt nc scc.
     option_CASE (opt:A option) nc scc <=> (opt = NONE /\ nc) \/ (?x. opt = SOME x /\ scc x)`,
  GEN_TAC THEN CASES_ON `opt:A option` THEN CASE_REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;

(* HOL4 line 2489 *)
let bind_locals_fold_nsBind = prove
 (`!nm t ts locals v_map.
     nsBind nm (source_to_flat_Local t nm) (bind_locals ts locals v_map) =
   bind_locals (CONS t ts) (CONS nm locals) v_map`,
  REWRITE_TAC[FLATP1AUX_bind_locals_CONS]);;

(* HOL4 line 2496 *)
let compile_decs_idx_prev = prove
 (`!t n next env envs ds n' next' env' envs' ds_i1.
     source_to_flat_compile_decs t n next env envs ds = (n', next', env', envs', ds_i1)
     ==> idx_prev next next'`,
  MATCH_MP_TAC source_to_flat_compile_decs_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC[source_to_flat_compile_decs_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ; option_case_eq; pair_case_eq; case_eq "var_name"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  TRY(REWRITE_TAC[idx_prev_def; next_indices_INFO.ri_accfupds; K_THM; LE_REFL; LE_ADD] THEN
      NO_TAC) THEN
  ASM_MESON_TAC[idx_prev_trans]);;

(* HOL4 line 2509 *)
let inc_compile_prog_idx_prev = prove
 (`!env_id c0 decs c1 fdecs.
     inc_compile_prog env_id c0 decs = (c1, fdecs)
   ==> idx_prev (source_to_flat_config_next c0) (source_to_flat_config_next c1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[inc_compile_prog_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[source_to_flat_config_INFO.ri_accfupds; K_THM;
              source_to_flat_config_INFO.ri_accessors] THEN
  ASM_MESON_TAC[compile_decs_idx_prev]);;

(* HOL4 line 2520 *)
let compile_decs_generation = prove
 (`!t n next env envs ds n' next' env' envs' ds_i1.
     source_to_flat_compile_decs t n next env envs ds = (n', next', env', envs', ds_i1)
     ==> environment_generation_store_generation envs' =
         environment_generation_store_generation envs`,
  MATCH_MP_TAC source_to_flat_compile_decs_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC[source_to_flat_compile_decs_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ; option_case_eq; pair_case_eq; case_eq "var_name"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  TRY(REWRITE_TAC[environment_generation_store_INFO.ri_accfupds; K_THM] THEN NO_TAC) THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 2533 *)
let compile_decs_env_gen_inv = prove
 (`!t n next env envs ds n' next' env' envs' ds_i1.
     source_to_flat_compile_decs t n next env envs ds = (n', next', env', envs', ds_i1) /\
     env_gen_inv envs
     ==> env_gen_inv envs' /\
         subspt (environment_generation_store_envs envs)
                (environment_generation_store_envs envs')`,
  MATCH_MP_TAC source_to_flat_compile_decs_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC[source_to_flat_compile_decs_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ; option_case_eq; pair_case_eq; case_eq "var_name"] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[subspt_refl] THEN
  TRY(ASM_MESON_TAC[subspt_trans] THEN NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[env_gen_inv_def]) THEN
  REWRITE_TAC[env_gen_inv_def; environment_generation_store_INFO.ri_accfupds; K_THM;
              domain_insert] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[SUBSET; INSERT_SUBSET; pred_set_count_DEF; IN_ELIM_THM] THEN
  DISCH_TAC THEN
  TRY(MATCH_MP_TAC FLATP1AUX_subspt_insert_fresh THEN ASM_MESON_TAC[LT_REFL] THEN NO_TAC) THEN
  ASM_MESON_TAC[ARITH_RULE `x < n ==> x < n + 1`; ARITH_RULE `n < n + 1`]);;

(* HOL4 line 2556: the conjuncts of v_rel_eqns without global_env_inv: all  *)
(* of them *)
let v_rel_eqns_non_global = v_rel_eqns;;

(* HOL4 line 2561 *)
let ALL_DISJOINT_SUBSETS = prove
 (`!xs ys:(A->bool)list.
     ALL_DISJOINT xs /\ ALL2 (\x y. y SUBSET x) xs ys ==> ALL_DISJOINT ys`,
  REWRITE_TAC[ALL_DISJOINT_DEF; LIST_REL_EL_EQN] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(BETA_RULE) THEN
  SUBGOAL_THEN `EL i (ys:(A->bool)list) SUBSET EL i xs /\ EL j ys SUBSET EL j xs /\
                EL i xs INTER EL j xs = {}` MP_TAC THENL
  [ASM_MESON_TAC[]; SET_TAC[]]);;

(* HOL4 line 2570 *)
let ALL_DISJOINT_MOVE = prove
 (`!i j mv_set (xs:(A->bool)list) ys.
     ALL_DISJOINT xs /\
     ys = LUPDATE (EL i xs DIFF mv_set) i (LUPDATE (EL j xs UNION mv_set) j xs) /\
     mv_set SUBSET EL i xs /\ i < LENGTH xs /\ j < LENGTH xs
     ==> ALL_DISJOINT ys`,
  REWRITE_TAC[ALL_DISJOINT_DEF] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_LUPDATE]) THEN
  ASM_REWRITE_TAC[EL_LUPDATE; LENGTH_LUPDATE] THEN
  REPEAT COND_CASES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  SEVPAUX_STRIPS_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; EXTENSION; IN_INTER; NOT_IN_EMPTY]) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_DIFF; IN_UNION] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 2585 *)
let idx_range_shrink = prove
 (`!i genv nts nes eval_config l_idx r_idx etc l_idx'.
     idx_range_rel (i:(v->(source_to_flat_config#C)option)option) genv nts nes eval_config
     (l_idx, r_idx, etc) /\
   idx_prev l_idx l_idx' /\ idx_prev l_idx' r_idx
   ==> idx_range_rel i genv nts nes eval_config (l_idx', r_idx, etc)`,
  REWRITE_TAC[idx_range_rel_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`l_idx':next_indices`; `end_idx:next_indices`; `fin_idx:next_indices`;
                        `other_blocks:num#idx_types->bool`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `l_idx:next_indices = idx`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ALL_DISJOINT_SUBSETS THEN
  EXISTS_TAC `[idx_block idx end_idx; idx_final_block fin_idx; other_blocks;
               genv_allocated_idxs genv]` THEN
  ASM_REWRITE_TAC[ALL2; SUBSET_REFL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[idx_prev_def]) THEN
  REWRITE_TAC[idx_block_def; SUBSET; IN_UNION; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[LE_TRANS]);;

(* HOL4 line 2601 *)
let invariant_idx_range_shrink = prove
 (`!interp g gen genv l_idx r_idx etc st st' l_idx'.
     source_to_flatProof_invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv
     (l_idx, r_idx, etc) (st:(FFI)state) (st':(C,FFI)flat_state) /\
   idx_prev l_idx l_idx' /\ idx_prev l_idx' r_idx
   ==> source_to_flatProof_invariant interp g gen genv (l_idx', r_idx, etc) st st'`,
  REWRITE_TAC[source_to_flatProof_invariant_def; FST; SND] THEN MESON_TAC[idx_range_shrink]);;

(* HOL4 line 2611 *)
let invariant_idx_range_shrink_gen = prove
 (`!interp g gen genv l_idx r_idx etc st st' l_idx' gen'.
     source_to_flatProof_invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv
     (l_idx, r_idx, etc) (st:(FFI)state) (st':(C,FFI)flat_state) /\
   idx_prev l_idx l_idx' /\ idx_prev l_idx' r_idx /\
   (env_gen_inv gen ==> env_gen_inv gen')
   ==> source_to_flatProof_invariant interp g gen' genv (l_idx', r_idx, etc) st st'`,
  REWRITE_TAC[source_to_flatProof_invariant_def; FST; SND] THEN MESON_TAC[idx_range_shrink]);;

(* HOL4 line 2622 *)
let pmatch_invariant = prove
 (`!interp v g gen genv idxs st st' comp_map2 env env' locals comp_map v' p.
     source_to_flatProof_invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv idxs
     (st:(FFI)state) (st':(C,FFI)flat_state) /\
   env_all_rel genv comp_map2 env env' locals /\
   source_to_flat_environment_c comp_map2 = source_to_flat_environment_c comp_map /\
   source_to_flatProof_v_rel genv v v'
   ==> source_to_flatProof_match_result_rel genv []
         (pmatch (sem_env_c env) (state_refs st) p v [])
         (flat_pmatch st' (compile_pat comp_map p) v' [])`,
  MATCH_ACCEPT_TAC FLATP1AUX_pmatch_invariant);;

let FLATP1AUX_eval_GlobalVarInit = prove
 (`!env (s:(C,FFI)flat_state) t t' idx x v.
     ALOOKUP (flat_environment_v env) x = SOME v /\
     idx < LENGTH (flat_state_globals s) /\ EL idx (flat_state_globals s) = NONE
     ==> flat_evaluate env s [flat_App t (GlobalVarInit idx) [Var_local t' x]] =
         (flat_state_globals_fupd (K (LUPDATE (SOME v) idx (flat_state_globals s))) s,
          Rval [Unitv])`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[flat_evaluate_def; REVERSE; APPEND] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "flat_op"; REVERSE; APPEND] THEN
  REWRITE_TAC[flat_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[IS_NONE_DEF] THEN CASE_REWRITE_TAC[list_result_def]);;

let FLATP1AUX_flat_state_globals_K = prove
 (`!(s:(C,FFI)flat_state). flat_state_globals_fupd (K (flat_state_globals s)) s = s`,
  REWRITE_TAC[flat_state_component_equality; flat_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 line 2640 *)
let evaluate_make_varls = prove
 (`!n t idx vars g g' (s:(C,FFI)flat_state) env vals len.
     flat_state_globals s = APPEND g (APPEND (REPLICATE len NONE) g') /\
     LENGTH g = idx /\ LENGTH vals = LENGTH vars /\ len = LENGTH vars /\
     (!n. n < LENGTH vals
          ==> ALOOKUP (flat_environment_v env) (EL n vars) = SOME (EL n vals))
     ==> flat_evaluate env s [make_varls n t idx vars] =
         (flat_state_globals_fupd (K (APPEND g (APPEND (MAP SOME vals) g'))) s,
          Rval [flat_Conv NONE []])`,
  MATCH_MP_TAC make_varls_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
  [REWRITE_TAC[LENGTH; LENGTH_EQ_NIL] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REPLICATE; APPEND]) THEN
   REWRITE_TAC[make_varls_def; flat_evaluate_def; REVERSE] THEN CASE_REWRITE_TAC[REVERSE] THEN
   REWRITE_TAC[MAP; APPEND] THEN
   FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[FLATP1AUX_flat_state_globals_K];
   REWRITE_TAC[LENGTH; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   REWRITE_TAC[make_varls_def] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[EL; HD; LENGTH; LT_0] THEN DISCH_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REPLICATE; APPEND]) THEN
   W(fun (asl,w) -> MP_TAC(ISPECL [`env:(flat_v)flat_environment`; `s:(C,FFI)flat_state`;
       `backend_common_None`; `backend_common_None`; `LENGTH (g:(flat_v option)list)`;
       `x:varN`; `h:flat_v`] FLATP1AUX_eval_GlobalVarInit)) THEN
   ASM_REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD; LENGTH_APPEND; LENGTH;
                   ARITH_RULE `l < l + SUC n`] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[LUPDATE_LENGTH; MAP; APPEND; flat_Unitv_def];
   DISCH_TAC THEN REWRITE_TAC[LENGTH; LENGTH_EQ_CONS] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   REWRITE_TAC[make_varls_def; FLATP1AUX_flat_evaluate_Let] THEN
   FIRST_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[EL; HD; LENGTH; LT_0] THEN DISCH_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REPLICATE; APPEND]) THEN
   MP_TAC(ISPECL [`env:(flat_v)flat_environment`; `s:(C,FFI)flat_state`;
       `backend_common_None`; `backend_common_None`; `LENGTH (g:(flat_v option)list)`;
       `x:varN`; `h:flat_v`] FLATP1AUX_eval_GlobalVarInit) THEN
   ASM_REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD; LENGTH_APPEND; LENGTH;
                   ARITH_RULE `l < l + SUC n`] THEN
   DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[HD; opt_bind_lem; env_updated_lem; LUPDATE_LENGTH] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL
     [`APPEND g [SOME (h:flat_v)]`; `g':(flat_v option)list`;
      `flat_state_globals_fupd
         (K (APPEND g (CONS (SOME (h:flat_v))
              (CONS NONE (APPEND (REPLICATE (LENGTH (v7:varN list)) NONE) g')))))
         (s:(C,FFI)flat_state)`;
      `env:(flat_v)flat_environment`; `CONS (h':flat_v) t''`;
      `LENGTH (CONS (v6:varN) v7)`] o
     check (fun th -> is_forall (concl th) && length (fst (strip_forall (concl th))) = 6)) THEN
   ANTS_TAC THENL
   [REWRITE_TAC[flat_state_INFO.ri_accfupds; K_THM; LENGTH; REPLICATE; LENGTH_APPEND;
                GSYM APPEND_ASSOC; APPEND] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC m`) THEN ASM_REWRITE_TAC[EL; TL; LENGTH; LT_SUC];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[flat_state_INFO.ri_fupdfupds; K_o_THM; GSYM APPEND_ASSOC; APPEND; MAP]]]);;

(* HOL4 line 2711 *)
let EL_APPEND_IF = prove
 (`!i xs ys.
     EL i (APPEND (xs:A list) ys) =
   if i < LENGTH xs then EL i xs else EL (i - LENGTH xs) ys`,
  REWRITE_TAC[EL_APPEND]);;

(* HOL4 line 2717 *)
let ALL_DISJOINT_elem = prove
 (`!x i xs. ALL_DISJOINT (xs:(A->bool)list) /\ i < LENGTH xs /\ x IN EL i xs
         ==> ALL I (MAPi (\j y. j = i \/ ~(x IN y)) xs)`,
  REWRITE_TAC[ALL_DISJOINT_DEF; EVERY_EL; LENGTH_MAPi] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_MAPi; I_THM] THEN
  ASM_CASES_TAC `n:num = i` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `i:num`]) THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

(* HOL4 line 2727 *)
let subglobals_NONE = prove
 (`!n g.
     subglobals (REPLICATE n (NONE:A option)) g <=> n <= LENGTH g`,
  SIMP_TAC[subglobals_def; LENGTH_REPLICATE; IMP_CONJ; EL_REPLICATE; IS_SOME_DEF]);;

(* HOL4 line 2733 *)
let EL_add_SOME_SOME = prove
 (`!i pre xs post.
     ~(EL i (APPEND pre (APPEND (MAP SOME (xs:A list)) post)) = NONE) <=>
   ~(EL i (APPEND pre (APPEND (REPLICATE (LENGTH xs) NONE) post)) = NONE) \/
   (LENGTH pre <= i /\ i < LENGTH pre + LENGTH xs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EL_APPEND; LENGTH_MAP; LENGTH_REPLICATE] THEN
  ASM_CASES_TAC `i < LENGTH (pre:(A option)list)` THEN ASM_REWRITE_TAC[] THENL
  [ASM_SIMP_TAC[ARITH_RULE `i < l ==> ~(l <= i)`];
   ASM_SIMP_TAC[ARITH_RULE `~(i < l) ==> l <= i`] THEN
   ASM_CASES_TAC `i - LENGTH (pre:(A option)list) < LENGTH (xs:A list)` THEN
   ASM_SIMP_TAC[EL_MAP; EL_REPLICATE; option_DISTINCT] THENL
   [ASM_ARITH_TAC;
    SUBGOAL_THEN `~(i < LENGTH (pre:(A option)list) + LENGTH (xs:A list))`
      (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC]]);;

let FLATP1AUX_ALOOKUP_alloc_defs_EL = prove
 (`!(xs:A list) m l k. ALL_DISTINCT xs /\ k < LENGTH xs
     ==> ALOOKUP (alloc_defs m l xs) (EL k xs) = SOME (Glob om_tra (l + k))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[ALL_DISTINCT; EL; HD; TL; LT_SUC; ADD_CLAUSES; alloc_defs_def; ALOOKUP_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~((h:A) = EL k t)` (fun th -> REWRITE_TAC[th]) THENL
  [DISCH_TAC THEN UNDISCH_TAC `~MEM (h:A) t` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[ADD_AC; ADD1]);;

(* HOL4 line 2743 *)
let ALOOKUP_alloc_defs_EL = prove
 (`!(funs:(varN#varN#exp)list) l n m.
     ALL_DISTINCT (MAP (\(x,y,z). x) funs) /\ n < LENGTH funs
     ==> ?tt. ALOOKUP (alloc_defs m l (MAP FST (REVERSE funs))) (EL n (MAP FST funs)) =
              SOME (Glob tt (l + LENGTH funs - (n + 1)))`,
  REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[source_to_flatProof_fst_lem]) THEN
  EXISTS_TAC `om_tra` THEN
  SUBGOAL_THEN `EL n (MAP FST (funs:(varN#varN#exp)list)) =
                EL (LENGTH funs - (n + 1)) (MAP FST (REVERSE funs))` SUBST1_TAC THENL
  [REWRITE_TAC[GSYM MAP_REVERSE] THEN
   SIMP_TAC[EL_REVERSE; LENGTH_MAP; ASSUME `n < LENGTH (funs:(varN#varN#exp)list)`;
            ARITH_RULE `n < l ==> l - (n + 1) < l`] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `n < LENGTH (funs:(varN#varN#exp)list)` THEN
   ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `l + LENGTH (funs:(varN#varN#exp)list) - (n + 1) =
                l + (LENGTH funs - (n + 1))` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FLATP1AUX_ALOOKUP_alloc_defs_EL THEN
  ASM_REWRITE_TAC[GSYM MAP_REVERSE; ALL_DISTINCT_REVERSE; LENGTH_REVERSE; LENGTH_MAP] THEN
  ASM_ARITH_TAC);;

let FLATP1AUX_ALOOKUP_alloc_defs = prove
 (`!(ps:(A#B)list) m l x v.
     ALOOKUP ps x = SOME v
     ==> ?n. n < LENGTH ps /\ EL n ps = (x,v) /\
             ALOOKUP (alloc_defs m l (MAP FST ps)) x = SOME (Glob om_tra (l + n))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_THM; option_DISTINCT] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:A`; `w:B`; `m:num`; `l:num`; `x:A`; `v:B`] THEN
  REWRITE_TAC[ALOOKUP_THM; MAP; alloc_defs_def; LENGTH] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ] THENL
  [DISCH_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
   REWRITE_TAC[EL; HD; ADD_CLAUSES; LT_0; ALOOKUP_THM];
   DISCH_THEN(MP_TAC o SPECL [`m + 1`; `l + 1`] o MATCH_MP
     (REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM]
        (ASSUME `!m l x v. ALOOKUP (t:(A#B)list) x = SOME v
                 ==> ?n. n < LENGTH t /\ EL n t = (x,v) /\
                         ALOOKUP (alloc_defs m l (MAP FST t)) x =
                         SOME (Glob om_tra (l + n))`))) THEN
   STRIP_TAC THEN EXISTS_TAC `SUC n` THEN
   ASM_REWRITE_TAC[EL; TL; LT_SUC; ALOOKUP_THM] THEN
   REWRITE_TAC[ADD1; ADD_AC]]);;

(* HOL4 line 2787 *)
let ALOOKUP_alloc_defs = prove
 (`!(env:(varN#A)list) x v l tt.
     ALOOKUP (REVERSE env) x = SOME v
     ==> ?n t. ALOOKUP (alloc_defs tt l (MAP FST (REVERSE env))) x = SOME (Glob t (l + n)) /\
               n < LENGTH (MAP FST env) /\
               EL n (REVERSE (MAP SOME (MAP SND env))) = SOME v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`tt:num`; `l:num`] o MATCH_MP FLATP1AUX_ALOOKUP_alloc_defs) THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`n:num`; `om_tra`] THEN
  ASM_REWRITE_TAC[GSYM MAP_REVERSE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_REVERSE]) THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN REWRITE_TAC[MAP_REVERSE] THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_MAP; LENGTH_REVERSE; SND]);;

(* HOL4 line 2825 *)
let global_env_inv_extend = prove
 (`!pat_env genv pat_env' tt g1 g2.
     source_to_flatProof_env_rel genv (alist_to_ns pat_env) pat_env' /\
     global_env_v genv =
       APPEND g1 (APPEND (MAP SOME (REVERSE (MAP SND pat_env'))) g2) /\
     ALL_DISTINCT (MAP FST pat_env)
     ==> global_env_inv genv
           (source_to_flat_environment_REC nsEmpty
              (alist_to_ns (alloc_defs tt (LENGTH g1) (REVERSE (MAP FST pat_env')))))
           {}
           (sem_env_REC (alist_to_ns pat_env) nsEmpty)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `MAP FST (pat_env':(varN#flat_v)list) = MAP FST (pat_env:(varN#v)list)`
    ASSUME_TAC THENL
  [FIRST_ASSUM(X_CHOOSE_THEN `l0:(varN#v)list` STRIP_ASSUME_TAC o MATCH_MP env_rel_dom) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[alist_to_ns_11]) THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (pat_env':(varN#flat_v)list) = LENGTH (pat_env:(varN#v)list)`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[LENGTH_MAP]; ALL_TAC] THEN
  REWRITE_TAC[v_rel_global_eqn; sem_env_INFO.ri_accessors;
              source_to_flat_environment_INFO.ri_accessors; nsLookup_nsEmpty;
              option_DISTINCT; IMAGE_CLAUSES; NOT_IN_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`x:(modN,varN)id`; `v:v`] THEN
  REWRITE_TAC[nsLookup_alist_to_ns_some] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:varN` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`tt:num`; `LENGTH (g1:(flat_v option)list)`] o
    MATCH_MP FLATP1AUX_ALOOKUP_alloc_defs o
    ONCE_REWRITE_RULE[GSYM (MATCH_MP alookup_distinct_reverse
      (ASSUME `ALL_DISTINCT (MAP FST (pat_env:(varN#v)list))`))]) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_REVERSE]) THEN
  MAP_EVERY EXISTS_TAC [`LENGTH (g1:(flat_v option)list) + n`;
                        `EL n (REVERSE (MAP SND (pat_env':(varN#flat_v)list)))`;
                        `om_tra`] THEN
  ASM_REWRITE_TAC[injectivity "id"; UNWIND_THM1; MAP_REVERSE] THEN
  REWRITE_TAC[GSYM MAP_REVERSE] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_MAP; LENGTH_REVERSE; EL_APPEND] THEN
  REWRITE_TAC[ARITH_RULE `~(l + n < l:num)`; ADD_SUB2] THEN
  ASM_SIMP_TAC[LENGTH_MAP; LENGTH_REVERSE; EL_MAP; ARITH_RULE `n < m ==> l + n < l + m + k`] THEN
  REWRITE_TAC[MAP_REVERSE] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_REVERSE; LENGTH_MAP] THEN
  SUBGOAL_THEN `v = SND (EL n (REVERSE (pat_env:(varN#v)list)))` SUBST1_TAC THENL
  [ASM_REWRITE_TAC[SND]; ALL_TAC] THEN
  SUBGOAL_THEN `n < LENGTH (pat_env':(varN#flat_v)list)` ASSUME_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[EL_REVERSE; ASSUME `n < LENGTH (pat_env:(varN#v)list)`;
           ASSUME `n < LENGTH (pat_env':(varN#flat_v)list)`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[source_to_flatProof_env_rel_el] o
    check (fun th -> let h,_ = strip_comb (concl th) in is_const h &&
                     fst (dest_const h) = "source_to_flatProof_env_rel")) THEN
  DISCH_THEN(MP_TAC o SPEC `PRE (LENGTH (pat_env:(varN#v)list) - n)`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]);;

(* HOL4 line 2858 *)
let LIST_REL_sv_rel_weak = prove
 (`!genv vs vs' genv'.
     ALL2 (source_to_flatProof_sv_rel genv) vs vs' /\
   subglobals (global_env_v genv) (global_env_v genv') /\
   global_env_c genv SUBMAP global_env_c genv' /\
   global_env_tys genv SUBMAP global_env_tys genv'
   ==> ALL2 (source_to_flatProof_sv_rel genv') vs vs'`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `ALL2 (source_to_flatProof_sv_rel genv) vs vs'` THEN
  MATCH_MP_TAC MONO_ALL2 THEN ASM_MESON_TAC[sv_rel_weak]);;

let FLATP1AUX_split_NONE = prove
 (`!(V:(A option)list) k n.
     k + n <= LENGTH V /\ (!i. k <= i /\ i < k + n ==> EL i V = NONE)
     ==> V = APPEND (TAKE k V) (APPEND (REPLICATE n NONE) (DROP (k + n) V))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ_REWRITE] THEN
  SUBGOAL_THEN `k <= LENGTH (V:(A option)list)` ASSUME_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LENGTH_APPEND; LENGTH_TAKE; LENGTH_REPLICATE; LENGTH_DROP] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_APPEND; LENGTH_TAKE; LENGTH_REPLICATE] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[EL_TAKE] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[EL_REPLICATE] THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
   W(fun (asl,w) -> MP_TAC(ISPECL [`x - k - n:num`; `k + n:num`; `V:(A option)list`] EL_DROP)) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]);;

(* HOL4 line 2874 *)
let idx_range_rel_v_REPLICATE_NONE = prove
 (`!interp genv nts nes eval_state idx end_idx others n.
     idx_range_rel (interp:(v->(source_to_flat_config#C)option)option) genv nts nes
     eval_state (idx, end_idx, others) /\
   fin_idx_match (LENGTH (global_env_v genv)) end_idx
     (src_orac_next_cfg interp eval_state) /\
   n + next_indices_vidx idx <= next_indices_vidx end_idx
   ==> ?pre post. global_env_v genv = APPEND pre (APPEND (REPLICATE n NONE) post) /\
                  LENGTH pre = next_indices_vidx idx`,
  REPEAT GEN_TAC THEN REWRITE_TAC[idx_range_rel_def; PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    is_var (rhs (concl th)) && is_var (lhs (concl th))))) THEN
  SUBGOAL_THEN `next_indices_vidx idx + n <= LENGTH (global_env_v genv)` ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o check (fun th -> let h,_ = strip_comb (concl th) in
     is_const h && fst (dest_const h) = "fin_idx_match")) THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_case_app (concl th))) THEN
   CASES_ON `src_orac_next_cfg (interp:(v->(source_to_flat_config#C)option)option)
               eval_state` THEN
   CASE_REWRITE_TAC[fin_idx_match_def] THEN RULE_ASSUM_TAC(REWRITE_RULE[idx_prev_def]) THEN
   REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `!i. next_indices_vidx idx <= i /\ i < next_indices_vidx idx + n
                    ==> EL i (global_env_v genv) = NONE` ASSUME_TAC THENL
  [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> let h,_ = strip_comb (concl th) in
     is_const h && fst (dest_const h) = "ALL_DISJOINT")) THEN
   REWRITE_TAC[FLATP1AUX_ALL_DISJOINT_CONS; ALL] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
   DISCH_THEN(MP_TAC o SPEC `(i:num, Idx_Var)` o CONJUNCT2 o CONJUNCT2 o CONJUNCT1) THEN
   REWRITE_TAC[idx_block_def; genv_allocated_idxs_def; IN_UNION; IN_ELIM_THM; PAIR_EQ;
               distinctness "idx_types"] THEN
   REWRITE_TAC[UNWIND_THM1; UNWIND_THM2; RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM] THEN
   SIMP[] THEN ASM_CASES_TAC `EL i (global_env_v genv) = NONE` THEN ASM_REWRITE_TAC[] THEN
   ASM_ARITH_TAC;
   ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`TAKE (next_indices_vidx idx) (global_env_v genv)`;
                        `DROP (next_indices_vidx idx + n) (global_env_v genv)`] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC FLATP1AUX_split_NONE THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC LENGTH_TAKE THEN ASM_ARITH_TAC]);;

let FLATP1AUX_genv_allocated_idxs_v = prove
 (`!genv pre (xs:flat_v list) post.
     global_env_v genv = APPEND pre (APPEND (REPLICATE (LENGTH xs) NONE) post)
     ==> genv_allocated_idxs
           (global_env_v_fupd (K (APPEND pre (APPEND (MAP SOME xs) post))) genv) =
         genv_allocated_idxs genv UNION
         {(i, Idx_Var) | LENGTH pre <= i /\ i < LENGTH pre + LENGTH xs}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[genv_allocated_idxs_def; global_env_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[EL_add_SOME_SOME; LENGTH_APPEND; LENGTH_MAP; LENGTH_REPLICATE] THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; idx_types_FORALL; IN_UNION; IN_ELIM_THM;
              PAIR_EQ; distinctness "idx_types"] THEN
  REWRITE_TAC[UNWIND_THM1; UNWIND_THM2] THEN SIMP[] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let FLATP1AUX_idx_block_shift = prove
 (`!idx end_idx l.
     next_indices_vidx idx + l <= next_indices_vidx end_idx
     ==> idx_block (next_indices_vidx_fupd (K (next_indices_vidx idx + l)) idx) end_idx =
         idx_block idx end_idx DIFF
         {(i, Idx_Var) | next_indices_vidx idx <= i /\ i < next_indices_vidx idx + l}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[idx_block_def; next_indices_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; idx_types_FORALL; IN_UNION; IN_DIFF; IN_ELIM_THM;
              PAIR_EQ; distinctness "idx_types"] THEN
  REWRITE_TAC[UNWIND_THM1; UNWIND_THM2] THEN SIMP[] THEN
  REPEAT GEN_TAC THEN ASM_ARITH_TAC);;

let FLATP1AUX_LUPDATE4 = prove
 (`!(x0:A->bool) x1 x2 x3 m.
     LUPDATE (EL 0 [x0;x1;x2;x3] DIFF m) 0
       (LUPDATE (EL 3 [x0;x1;x2;x3] UNION m) 3 [x0;x1;x2;x3]) =
     [x0 DIFF m; x1; x2; x3 UNION m]`,
  REWRITE_TAC[ARITH_RULE `3 = SUC (SUC (SUC 0))`; LUPDATE_def; EL; HD; TL]);;

let FLATP1AUX_idx_range_rel_extend = prove
 (`!interp genv nts nes es idx end_idx others pre (xs:flat_v list) post l.
     idx_range_rel (interp:(v->(source_to_flat_config#C)option)option) genv nts nes es
       (idx, end_idx, others) /\
     global_env_v genv = APPEND pre (APPEND (REPLICATE l NONE) post) /\
     LENGTH xs = l /\
     LENGTH pre = next_indices_vidx idx /\
     next_indices_vidx idx + l <= next_indices_vidx end_idx
     ==> idx_range_rel interp
           (global_env_v_fupd (K (APPEND pre (APPEND (MAP SOME xs) post))) genv) nts nes es
           (next_indices_vidx_fupd (K (next_indices_vidx idx + l)) idx,
            end_idx, others)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[idx_range_rel_def; PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    is_var (rhs (concl th)) && is_var (lhs (concl th))))) THEN
  MAP_EVERY EXISTS_TAC
   [`next_indices_vidx_fupd (K (next_indices_vidx idx + LENGTH (xs:flat_v list))) idx`;
    `end_idx:next_indices`; `fin_idx:next_indices`; `others:num#idx_types->bool`] THEN
  ASM_REWRITE_TAC[global_env_INFO.ri_accfupds; K_THM] THEN
  ASM_SIMP_TAC[FLATP1AUX_idx_block_shift; FLATP1AUX_genv_allocated_idxs_v] THEN
  MATCH_MP_TAC (ISPECL [`0`; `3`] ALL_DISJOINT_MOVE) THEN
  EXISTS_TAC `{(i, Idx_Var) | next_indices_vidx idx <= i /\
                              i < next_indices_vidx idx + LENGTH (xs:flat_v list)}` THEN
  EXISTS_TAC `[idx_block idx end_idx; idx_final_block fin_idx; others;
               genv_allocated_idxs genv]` THEN
  ASM_REWRITE_TAC[FLATP1AUX_LUPDATE4; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EL; HD] THEN
  REWRITE_TAC[idx_block_def; SUBSET; IN_UNION; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
  EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* HOL4 line 2901 *)
let invariant_make_varls = prove
 (`!interp g gen genv idx end_idx others st st' vidx vars env n t.
     source_to_flatProof_invariant (interp:(v->(source_to_flat_config#C)option)option) g gen genv
     (idx, end_idx, others) (st:(FFI)state) (st':(C,FFI)flat_state) /\
   next_indices_vidx idx = vidx /\
   next_indices_vidx idx + LENGTH vars <= next_indices_vidx end_idx /\
   vars = REVERSE (MAP FST (flat_environment_v env)) /\
   ALL_DISTINCT (MAP FST (flat_environment_v env))
   ==> ?genv' st''.
         flat_evaluate env st' [make_varls n t vidx vars] = (st'', Rval [Unitv]) /\
         source_to_flatProof_invariant interp g gen genv'
           (next_indices_vidx_fupd (K (next_indices_vidx idx + LENGTH vars)) idx,
            end_idx, others) st st'' /\
         global_env_c genv' = global_env_c genv /\
         global_env_tys genv' = global_env_tys genv /\
         subglobals (global_env_v genv) (global_env_v genv') /\
         (!env1 tt.
            source_to_flatProof_env_rel genv' (alist_to_ns env1) (flat_environment_v env)
            ==> global_env_inv genv'
                  (source_to_flat_environment_REC nsEmpty
                     (alist_to_ns (alloc_defs tt vidx
                                     (REVERSE (MAP FST (flat_environment_v env))))))
                  {}
                  (sem_env_REC (alist_to_ns env1) nsEmpty))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `flat_environment_v (env:(flat_v)flat_environment) = []` THENL
  [FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THEN
   RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[MAP; REVERSE]) THEN
   MAP_EVERY EXISTS_TAC [`genv:global_env`; `st':(C,FFI)flat_state`] THEN
   REWRITE_TAC[MAP; REVERSE; LENGTH; ADD_CLAUSES; make_varls_def; flat_evaluate_def;
               subglobals_refl; alloc_defs_def; flat_Unitv_def] THEN
   CASE_REWRITE_TAC[REVERSE] THEN
   SUBGOAL_THEN `next_indices_vidx_fupd (K (next_indices_vidx idx)) idx = idx` SUBST1_TAC THENL
   [REWRITE_TAC[next_indices_INFO.ri_component_equality; next_indices_INFO.ri_accfupds;
                K_THM];
    ALL_TAC] THEN
   ASM_REWRITE_TAC[env_rel_LIST_REL; LIST_REL_NIL] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   REWRITE_TAC[v_rel_global_eqn; sem_env_INFO.ri_accessors;
               source_to_flat_environment_INFO.ri_accessors; alist_to_ns_nil;
               nsLookup_nsEmpty; option_DISTINCT];
   ALL_TAC] THEN
  RVEQ_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[source_to_flatProof_invariant_def; FST; SND] o
    check (fun th -> let h,_ = strip_comb (concl th) in is_const h &&
                     fst (dest_const h) = "source_to_flatProof_invariant")) THEN
  MP_TAC(ISPECL [`interp:(v->(source_to_flat_config#C)option)option`; `genv:global_env`;
                 `state_next_type_stamp (st:(FFI)state)`; `state_next_exn_stamp (st:(FFI)state)`;
                 `state_eval_state (st:(FFI)state)`; `idx:next_indices`;
                 `end_idx:next_indices`; `others:num#idx_types->bool`;
                 `LENGTH (flat_environment_v (env:(flat_v)flat_environment))`]
                idx_range_rel_v_REPLICATE_NONE) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_REVERSE; LENGTH_MAP]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `pre:(flat_v option)list`
    (X_CHOOSE_THEN `post:(flat_v option)list` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`n:num`; `t:tra`; `next_indices_vidx idx`;
                 `REVERSE (MAP FST (flat_environment_v (env:(flat_v)flat_environment)))`;
                 `pre:(flat_v option)list`; `post:(flat_v option)list`;
                 `st':(C,FFI)flat_state`; `env:(flat_v)flat_environment`;
                 `REVERSE (MAP SND (flat_environment_v (env:(flat_v)flat_environment)))`;
                 `LENGTH (flat_environment_v (env:(flat_v)flat_environment))`]
                evaluate_make_varls) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[LENGTH_REVERSE; LENGTH_MAP] THEN
   X_GEN_TAC `k:num` THEN DISCH_TAC THEN
   REWRITE_TAC[MAP_REVERSE] THEN
   SUBGOAL_THEN `k < LENGTH (REVERSE (flat_environment_v (env:(flat_v)flat_environment)))`
     ASSUME_TAC THENL [ASM_REWRITE_TAC[LENGTH_REVERSE]; ALL_TAC] THEN
   ASM_SIMP_TAC[EL_MAP] THEN
   ASM_SIMP_TAC[EL_REVERSE] THEN MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_EL THEN
   ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
   DISCH_TAC] THEN
  SUBGOAL_THEN `subglobals
     (APPEND pre (APPEND (REPLICATE (LENGTH (flat_environment_v
        (env:(flat_v)flat_environment))) NONE) post))
     (APPEND pre (APPEND (MAP SOME (REVERSE (MAP SND
        (flat_environment_v (env:(flat_v)flat_environment))))) post))` ASSUME_TAC THENL
  [REWRITE_TAC[subglobals_refl_append] THEN
   MP_TAC(CONJUNCT2 (ISPECL [`post:(flat_v option)list`;
      `REPLICATE (LENGTH (flat_environment_v (env:(flat_v)flat_environment))) (NONE:flat_v option)`;
      `MAP SOME (REVERSE (MAP SND (flat_environment_v (env:(flat_v)flat_environment))))`]
      subglobals_refl_append)) THEN
   REWRITE_TAC[LENGTH_REPLICATE; LENGTH_MAP; LENGTH_REVERSE] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[subglobals_NONE; LENGTH_MAP; LENGTH_REVERSE; LE_REFL];
   ALL_TAC] THEN
  EXISTS_TAC `global_env_v_fupd (K (APPEND pre (APPEND (MAP SOME (REVERSE (MAP SND
        (flat_environment_v (env:(flat_v)flat_environment))))) post))) genv` THEN
  EXISTS_TAC `flat_state_globals_fupd (K (APPEND pre (APPEND (MAP SOME (REVERSE (MAP SND
        (flat_environment_v (env:(flat_v)flat_environment))))) post))) (st':(C,FFI)flat_state)` THEN
  ASM_REWRITE_TAC[flat_Unitv_def; global_env_INFO.ri_accfupds; K_THM; LENGTH_REVERSE;
                  LENGTH_MAP] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[source_to_flatProof_invariant_def; FST; SND; global_env_INFO.ri_accfupds;
               flat_state_INFO.ri_accfupds; K_THM] THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* s_rel *)
    RULE_ASSUM_TAC(REWRITE_RULE[source_to_flatProof_s_rel_cases]) THEN
    REWRITE_TAC[source_to_flatProof_s_rel_cases; flat_state_INFO.ri_accfupds; K_THM] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LIST_REL_sv_rel_weak THEN
    EXISTS_TAC `genv:global_env` THEN
    ASM_REWRITE_TAC[global_env_INFO.ri_accfupds; K_THM; SUBMAP_REFL];
    (* idx_range_rel *)
    MATCH_MP_TAC FLATP1AUX_idx_range_rel_extend THEN
    ASM_REWRITE_TAC[LENGTH_REVERSE; LENGTH_MAP] THEN ASM_MESON_TAC[];
    (* src_orac_invs *)
    MATCH_MP_TAC src_orac_invs_weak THEN EXISTS_TAC `genv:global_env` THEN
    ASM_REWRITE_TAC[global_env_INFO.ri_accfupds; K_THM; SUBMAP_REFL];
    (* eval_ref_inv *)
    UNDISCH_TAC `eval_ref_inv (TAKE 1 (flat_state_globals (st':(C,FFI)flat_state)))
                   (TAKE 1 (flat_state_refs st'))` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `flat_environment_v (env:(flat_v)flat_environment)` list_CASES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `hh:varN#flat_v` (X_CHOOSE_THEN `tl:(varN#flat_v)list`
      SUBST1_TAC)) THEN
    CASES_ON `pre:(flat_v option)list` THEN
    REWRITE_TAC[APPEND; LENGTH; REPLICATE; TAKE_def; ARITH_RULE `~(1 = 0)`;
                ARITH_RULE `1 - 1 = 0`; TAKE_0; eval_ref_inv_def; CONS_11; option_DISTINCT];
    (* fin_idx_match *)
    UNDISCH_TAC `fin_idx_match (LENGTH (flat_state_globals (st':(C,FFI)flat_state))) end_idx
                   (src_orac_next_cfg (interp:(v->(source_to_flat_config#C)option)option)
                      (state_eval_state (st:(FFI)state)))` THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_MAP; LENGTH_REPLICATE; LENGTH_REVERSE]];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`env1:(varN#v)list`;
     `global_env_v_fupd (K (APPEND pre (APPEND (MAP SOME (REVERSE (MAP SND
        (flat_environment_v (env:(flat_v)flat_environment))))) post))) genv`;
     `flat_environment_v (env:(flat_v)flat_environment)`; `tt:num`;
     `pre:(flat_v option)list`; `post:(flat_v option)list`] global_env_inv_extend) THEN
  ASM_REWRITE_TAC[global_env_INFO.ri_accfupds; K_THM] THEN
  ANTS_TAC THENL
  [FIRST_ASSUM(X_CHOOSE_THEN `l0:(varN#v)list` STRIP_ASSUME_TAC o MATCH_MP env_rel_dom o
     check (fun th -> let h,_ = strip_comb (concl th) in is_const h &&
                      fst (dest_const h) = "source_to_flatProof_env_rel")) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[alist_to_ns_11]) THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;
