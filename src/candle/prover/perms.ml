(* ========================================================================= *)
(* perms: port of HOL4 candle/prover/permsScript.sml (CakeML v3479).         *)
(* Permissions for CakeML values.                                            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/evaluate.ml";;
needs "hol4/sptree.ml";;
needs "translator/ml_prog.ml";;
needs "candle/prover/ast_extras.ml";;

type_invention_error := true;;
(* HOL4: Type loc = :num *)
new_type_abbrev("perms_loc",`:num`);;

(* ------------------------------------------------------------------------- *)
(* We define a set of permissions for our value relation, which restricts   *)
(* what our code can do.                                                     *)
(* ------------------------------------------------------------------------- *)

(* FFIWrite: write to the FFI channel with that name; RefMention: mention   *)
(* the reference with that pointer; RefUpdate: write to references;        *)
(* RefAlloc: allocate new references; DoFFI: call the FFI; W8Alloc:         *)
(* allocate byte arrays                                                      *)

let permission_INDUCT,permission_RECURSION = cake_type
  "permission = FFIWrite string
              | RefMention perms_loc
              | RefUpdate
              | RefAlloc
              | DoFFI
              | W8Alloc";;

let perms_ok_exp_def = cake_def
  `perms_ok_exp (ps:permission->bool) =
     every_exp (\x. match x with
                      App op xs ->
                        ~(op = Eval) /\
                        (op = Opref ==> RefAlloc IN ps) /\
                        (op = Aalloc ==> RefAlloc IN ps) /\
                        (op = AallocEmpty ==> RefAlloc IN ps) /\
                        (op = AallocFixed ==> RefAlloc IN ps) /\
                        (op = Aw8alloc ==> W8Alloc IN ps) /\
                        (op = Opassign ==> RefUpdate IN ps) /\
                        (!chn. op = FFI chn ==>
                               FFIWrite (explode chn) IN ps /\ DoFFI IN ps) /\
                        (!m. op = ThunkOp (AllocThunk m) ==> RefAlloc IN ps) /\
                        (!m. op = ThunkOp (UpdateThunk m) ==> RefUpdate IN ps)
                    | _ -> T)`;;

(* HOL4: perms_ok_exp_thm (the clauses of perms_ok_exp; HOL4 derives them
   from perms_ok_exp_def by simplification) *)
let perms_ok_exp_thm = prove
 (`(!ps e. perms_ok_exp ps (Raise e) <=> perms_ok_exp ps e) /\
   (!ps e pes. perms_ok_exp ps (Handle e pes) <=>
      perms_ok_exp ps e /\ ALL (perms_ok_exp ps) (MAP SND pes)) /\
   (!ps lit. perms_ok_exp ps (Lit lit)) /\
   (!ps cn es. perms_ok_exp ps (Con cn es) <=> ALL (perms_ok_exp ps) es) /\
   (!ps n. perms_ok_exp ps (Var n)) /\
   (!ps n x. perms_ok_exp ps (Fun n x) <=> perms_ok_exp ps x) /\
   (!ps op xs. perms_ok_exp ps (App op xs) <=>
      (~(op = Eval) /\
       (op = Opref ==> RefAlloc IN ps) /\
       (op = Aalloc ==> RefAlloc IN ps) /\
       (op = AallocEmpty ==> RefAlloc IN ps) /\
       (op = AallocFixed ==> RefAlloc IN ps) /\
       (op = Aw8alloc ==> W8Alloc IN ps) /\
       (op = Opassign ==> RefUpdate IN ps) /\
       (!chn. op = FFI chn ==> FFIWrite (explode chn) IN ps /\ DoFFI IN ps) /\
       (!m. op = ThunkOp (AllocThunk m) ==> RefAlloc IN ps) /\
       (!m. op = ThunkOp (UpdateThunk m) ==> RefUpdate IN ps)) /\
      ALL (perms_ok_exp ps) xs) /\
   (!ps lop x y. perms_ok_exp ps (Log lop x y) <=>
      perms_ok_exp ps x /\ perms_ok_exp ps y) /\
   (!ps x y z. perms_ok_exp ps (If x y z) <=>
      perms_ok_exp ps x /\ perms_ok_exp ps y /\ perms_ok_exp ps z) /\
   (!ps e pes. perms_ok_exp ps (Mat e pes) <=>
      perms_ok_exp ps e /\ ALL (perms_ok_exp ps) (MAP SND pes)) /\
   (!ps opt x y. perms_ok_exp ps (Let opt x y) <=>
      perms_ok_exp ps x /\ perms_ok_exp ps y) /\
   (!ps f x. perms_ok_exp ps (Letrec f x) <=>
      perms_ok_exp ps x /\ ALL (perms_ok_exp ps) (MAP (SND o SND) f)) /\
   (!ps x t. perms_ok_exp ps (Tannot x t) <=> perms_ok_exp ps x) /\
   (!ps x l. perms_ok_exp ps (Lannot x l) <=> perms_ok_exp ps x)`,
  REWRITE_TAC[perms_ok_exp_def] THEN SIMP[ast_extras_every_exp_def]);;

let _ = cake_add_simps [perms_ok_exp_thm];;

let perms_ok_dec_def = cake_def
  `perms_ok_dec (ps:permission->bool) =
     every_dec (\d. match d with
                      Dlet locs pat e -> perms_ok_exp ps e
                    | Dletrec locs funs -> ALL (perms_ok_exp ps) (MAP (SND o SND) funs)
                    | _ -> T)`;;

let perms_ok_dec_thm = prove
 (`(!ps l p e. perms_ok_dec ps (Dlet l p e) <=> perms_ok_exp ps e) /\
   (!ps l f. perms_ok_dec ps (Dletrec l f) <=>
      ALL (perms_ok_exp ps) (MAP (SND o SND) f)) /\
   (!ps l tds. perms_ok_dec ps (Dtype l tds)) /\
   (!ps l ns n t. perms_ok_dec ps (Dtabbrev l ns n t)) /\
   (!ps l n ts. perms_ok_dec ps (Dexn l n ts)) /\
   (!ps n ds. perms_ok_dec ps (Dmod n ds) <=> ALL (perms_ok_dec ps) ds) /\
   (!ps ds1 ds2. perms_ok_dec ps (Dlocal ds1 ds2) <=>
      ALL (perms_ok_dec ps) ds1 /\ ALL (perms_ok_dec ps) ds2) /\
   (!ps n. perms_ok_dec ps (Denv n))`,
  REWRITE_TAC[perms_ok_dec_def] THEN SIMP[every_dec_def]);;
let _ = cake_add_simps [perms_ok_dec_thm];;

(* HOL4: Inductive perms_ok, with the rules perms_ok_Conv .. perms_ok_env *)
let perms_ok_rules,perms_ok_ind,perms_ok_cases,perms_ok_strongind = cake_inductive
  `(!ps opt vs.
      ALL (perms_ok ps) vs ==>
      perms_ok (ps:permission->bool) (Conv opt vs)) /\
   (!ps env n x.
      perms_ok_env ps (freevars x DIFF {Short n}) env /\
      perms_ok_exp ps x ==>
      perms_ok ps (Closure env n x)) /\
   (!ps env f n.
      perms_ok_env ps
        (UNIONS (set_of_list (MAP (\fvx. match fvx with
                                     (fn,vn,x) -> freevars x DIFF {Short fn, Short vn})
                                  f)))
        env /\
      ALL (perms_ok_exp ps) (MAP (SND o SND) f) ==>
      perms_ok ps (Recclosure env f n)) /\
   (!ps vs.
      ALL (perms_ok ps) vs ==>
      perms_ok ps (Vectorv vs)) /\
   (!ps lit.
      perms_ok ps (Litv lit)) /\
   (!ps b loc.
      RefMention loc IN ps ==>
      perms_ok ps (Loc b loc)) /\
   (!ps env ns.
      perms_ok_env ps (:(modN,varN)id) env ==>
      perms_ok ps (Env env ns)) /\
   (!ps fvs env.
      (!n v. n IN fvs /\ nsLookup (sem_env_v env) n = SOME v ==> perms_ok ps v) ==>
      perms_ok_env ps fvs env)`;;

let perms_ok_Conv = el 0 (CONJUNCTS perms_ok_rules);;
let perms_ok_Closure = el 1 (CONJUNCTS perms_ok_rules);;
let perms_ok_Recclosure = el 2 (CONJUNCTS perms_ok_rules);;
let perms_ok_Vectorv = el 3 (CONJUNCTS perms_ok_rules);;
let perms_ok_Litv = el 4 (CONJUNCTS perms_ok_rules);;
let perms_ok_Loc = el 5 (CONJUNCTS perms_ok_rules);;
let perms_ok_Env = el 6 (CONJUNCTS perms_ok_rules);;
let perms_ok_env = el 7 (CONJUNCTS perms_ok_rules);;

(* HOL4: perms_ok_def (the cases of perms_ok for each constructor) *)
let perms_ok_def = prove
 (CASE_TERM
   `(!ps lit. perms_ok ps (Litv lit)) /\
    (!ps opt vs. perms_ok ps (Conv opt vs) <=> ALL (perms_ok ps) vs) /\
    (!ps env n x. perms_ok ps (Closure env n x) <=>
       perms_ok_env ps (freevars x DIFF {Short n}) env /\ perms_ok_exp ps x) /\
    (!ps env f n. perms_ok ps (Recclosure env f n) <=>
       perms_ok_env ps
         (UNIONS (set_of_list (MAP (\fvx. match fvx with
                                      (fn,vn,x) -> freevars x DIFF {Short fn, Short vn})
                                   f)))
         env /\
       ALL (perms_ok_exp ps) (MAP (SND o SND) f)) /\
    (!ps b loc. perms_ok ps (Loc b loc) <=> RefMention loc IN ps) /\
    (!ps vs. perms_ok ps (Vectorv vs) <=> ALL (perms_ok ps) vs) /\
    (!ps env ns. perms_ok ps (Env env ns) <=> perms_ok_env ps (:(modN,varN)id) env)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[CONJUNCT1 perms_ok_cases] THEN
  SIMP[distinctness "v"; injectivity "v"]);;

let perms_ok_env_def = prove
 (`!ps fvs env. perms_ok_env ps fvs env <=>
     (!n v. n IN fvs /\ nsLookup (sem_env_v env) n = SOME v ==> perms_ok ps v)`,
  REWRITE_TAC[CONJUNCT2 perms_ok_cases]);;

let perms_ok_env_UNION = prove
 (`!ps x y env. perms_ok_env ps (x UNION y) env <=>
     perms_ok_env ps x env /\ perms_ok_env ps y env`,
  REWRITE_TAC[perms_ok_env_def; IN_UNION] THEN MESON_TAC[]);;

let perms_ok_env_BIGUNION = prove
 (`!ps xs env. perms_ok_env ps (UNIONS xs) env <=>
     !x. x IN xs ==> perms_ok_env ps x env`,
  REWRITE_TAC[perms_ok_env_def; IN_UNIONS] THEN MESON_TAC[]);;

let perms_ok_bind_exn_v = prove
 (`!ps. perms_ok ps bind_exn_v`,
  RW[perms_ok_def; bind_exn_v_def; ALL]);;
let _ = cake_add_simps [perms_ok_bind_exn_v];;

let perms_ok_div_exn_v = prove
 (`!ps. perms_ok ps div_exn_v`,
  RW[perms_ok_def; div_exn_v_def; ALL]);;
let _ = cake_add_simps [perms_ok_div_exn_v];;

let perms_ok_sub_exn_v = prove
 (`!ps. perms_ok ps sub_exn_v`,
  RW[perms_ok_def; sub_exn_v_def; ALL]);;
let _ = cake_add_simps [perms_ok_sub_exn_v];;

let perms_ok_chr_exn_v = prove
 (`!ps. perms_ok ps chr_exn_v`,
  RW[perms_ok_def; chr_exn_v_def; ALL]);;
let _ = cake_add_simps [perms_ok_chr_exn_v];;

let perms_ok_ref_def = cake_def
  `(perms_ok_ref ps (Refv v) <=> perms_ok ps v) /\
   (perms_ok_ref ps (Varray vs) <=> ALL (perms_ok ps) vs) /\
   (perms_ok_ref ps (W8array ws) <=> T) /\
   (perms_ok_ref ps (Thunk _ v) <=> perms_ok ps v)`;;

let perms_ok_state_def = cake_def
  `perms_ok_state ps (s:(FFI)state) <=>
     !n. n < LENGTH (state_refs s) /\ RefMention n IN ps ==>
         perms_ok_ref ps (EL n (state_refs s))`;;

let perms_ok_state_with_clock = prove
 (`!ps (s:(FFI)state) ck.
     perms_ok_state ps (state_clock_fupd (K ck) s) <=> perms_ok_state ps s`,
  RW[perms_ok_state_def]);;
let _ = cake_add_simps [perms_ok_state_with_clock];;

let pmatch_perms_ok = prove
 (`!perms.
   (!envC s p v ws env.
     pmatch envC s p v ws = Match env /\
     perms_ok perms v /\
     (RefAlloc IN perms ==> IMAGE RefMention (:num) SUBSET perms) /\
     (!n. n < LENGTH s /\ RefMention n IN perms ==> perms_ok_ref perms (EL n s)) /\
     ALL (perms_ok perms) (MAP SND ws) ==>
     ALL (perms_ok perms) (MAP SND env)) /\
   (!envC s ps vs ws env.
     pmatch_list envC s ps vs ws = Match env /\
     ALL (perms_ok perms) vs /\
     (RefAlloc IN perms ==> IMAGE RefMention (:num) SUBSET perms) /\
     (!n. n < LENGTH s /\ RefMention n IN perms ==> perms_ok_ref perms (EL n s)) /\
     ALL (perms_ok perms) (MAP SND ws) ==>
     ALL (perms_ok perms) (MAP SND env))`,
  GEN_TAC THEN MATCH_MP_TAC pmatch_ind THEN RW[] THEN GVS[pmatch_def] THEN
  GVS[COND_CASE_EQ; option_case_eq; pair_case_eq; case_eq "match_result";
      case_eq "store_v"; perms_ok_def; GSYM ALL_MEM; store_lookup_def; MAP] THEN
  (* Pref *)
  FIRST_X_ASSUM (QSPEC_THEN "lnum" MP_TAC) THEN ASM_REWRITE_TAC[perms_ok_ref_def] THEN
  ASM_MESON_TAC[]);;

let perms_ok_env_extend_dec_env = prove
 (`!ps fvs env1 env.
     perms_ok_env ps fvs env1 /\ perms_ok_env ps fvs env ==>
     perms_ok_env ps fvs (extend_dec_env env1 env)`,
  RW[perms_ok_env_def; extend_dec_env_def] THEN
  FS[nsLookup_nsAppend_some] THEN ASM_MESON_TAC[]);;

let EVERY_perms_ok_env_BIGUNION = prove
 (`!ps (P:A->(modN,varN)id->bool) env xs.
     ALL (\x. perms_ok_env ps (P x) env) xs <=>
     perms_ok_env ps (UNIONS (set_of_list (MAP P xs))) env`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL; MAP; set_of_list; UNIONS_0; UNIONS_INSERT; perms_ok_env_UNION] THEN
  REWRITE_TAC[perms_ok_env_def; NOT_IN_EMPTY]);;

let perms_ok_env_EMPTY = prove
 (`!ps env. perms_ok_env ps {} env`,
  RW[perms_ok_env_def; NOT_IN_EMPTY]);;

let dfreevars_def = sem1aux_def_wf `MEASURE dec_size` SEM1AUX_TC_TAC
  `(dfreevars (Dlet locs p x) =
      (freevars x DIFF set_of_list (MAP Short (pat_bindings p)))) /\
   (dfreevars (Dletrec locs f) =
      UNIONS (set_of_list (MAP (\fvx. match fvx with
                                  (fn,vn,x) -> freevars x DIFF {Short fn, Short vn})
                               f))) /\
   (dfreevars (Dmod mn ds) = UNIONS (set_of_list (MAP dfreevars ds))) /\
   (dfreevars (Dlocal ds1 ds2) =
      (UNIONS (set_of_list (MAP dfreevars ds1)) UNION
       UNIONS (set_of_list (MAP dfreevars ds2)))) /\
   (dfreevars _ = {})`;;

let dfreevars_ind = cake_ind "dfreevars";;

let perms_ok_v_to_list = prove
 (`!v vs ps. v_to_list v = SOME vs /\ perms_ok ps v ==> ALL (perms_ok ps) vs`,
  MATCH_MP_TAC v_to_list_ind THEN SIMP[perms_ok_def; v_to_list_def] THEN
  RW[] THEN GVS[option_case_eq; list_case_eq; ALL]);;

let PERMSAUX_perms_ok_list_to_v = prove
 (`!ps l. perms_ok ps (list_to_v l) <=> ALL (perms_ok ps) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_to_v_def; perms_ok_def; ALL]);;

(* ------------------------------------------------------------------------- *)
(* do_app_perms: the results of a primitive operation (other than function  *)
(* application and Eval) respect the permissions                            *)
(* ------------------------------------------------------------------------- *)

let PERMSAUX_do_arith = prove
 (`!a ty vs r ps.
     do_arith a ty vs = SOME r ==>
     (!e. r = INL e ==> perms_ok ps e) /\ (!v. r = INR v ==> perms_ok ps v)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `ty:prim_type` prim_type_cases) THEN
  REWRITE_TAC[do_arith_def] THEN
  REPEAT (FIRST [TOP_CASE_TAC; DISCH_TAC]) THEN
  GVS[perms_ok_def; semanticPrimitives_Boolv_def; div_exn_v_def; ALL] THEN
  RW[perms_ok_def; ALL]);;

let PERMSAUX_do_conversion = prove
 (`!v ty1 ty2 r ps.
     do_conversion v ty1 ty2 = SOME r ==>
     (!e. r = INL e ==> perms_ok ps e) /\ (!v. r = INR v ==> perms_ok ps v)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `ty1:prim_type` prim_type_cases) THEN
  STRUCT_CASES_TAC (SPEC `ty2:prim_type` prim_type_cases) THEN
  REWRITE_TAC[do_conversion_def; LET_DEF; LET_END_DEF] THEN
  RW[perms_ok_def; chr_exn_v_def; ALL] THEN GVS[perms_ok_def; ALL]);;

let PERMSAUX_store_lookup = prove
 (`!refs ps.
     (!n. n < LENGTH refs /\ RefMention n IN ps ==> perms_ok_ref ps (EL n refs)) ==>
     !n x. store_lookup n refs = SOME x /\ RefMention n IN ps ==> perms_ok_ref ps x`,
  REWRITE_TAC[store_lookup_def] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN ASM_MESON_TAC[]);;

let PERMSAUX_EL_SUB_SING = prove
 (`!n m (x:A). ~(n < m) /\ n < m + 1 ==> EL (n - m) [x] = x`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `n - m = 0` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[EL; HD]]);;

let PERMSAUX_ALL_EL = prove
 (`!(P:A->bool) l k. ALL P l /\ k < LENGTH l ==> P (EL k l)`,
  MESON_TAC[ALL_EL]);;

let PERMSAUX_ALL_LUPDATE = prove
 (`!(P:A->bool) x n l. P x /\ ALL P l ==> ALL P (LUPDATE x n l)`,
  MESON_TAC[IMP_EVERY_LUPDATE]);;

let PERMSAUX_SPLIT_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP PERMSAUX_store_lookup) THEN
  QPAT_X_ASSUM "do_app _ _ _ = _" (MP_TAC o REWRITE_RULE[do_app_cases]) THEN
  DISCH_THEN CAKE_STRIP_ASSUME_TAC;;
let PERMSAUX_FIN_TAC =
  RVEQ_TAC THEN
  GVS[PAIR_EQ; sum_case_eq; perms_ok_def; ALL; thunk_op_def; case_eq "thunk_op";
      list_case_eq; case_eq "v"; option_case_eq; pair_case_eq; COND_CASE_EQ;
      call_FFI_def; case_eq "ffi_result"; case_eq "oracle_result"] THEN
  IMP_RES_TAC PERMSAUX_do_arith THEN IMP_RES_TAC PERMSAUX_do_conversion THEN
  IMP_RES_TAC perms_ok_v_to_list THEN FULL_RES_TAC THEN
  GVS[perms_ok_ref_def; store_lookup_def; store_assign_def; store_alloc_def;
      COND_CASE_EQ; EL_LUPDATE; LENGTH_LUPDATE; EL_APPEND_EQN; LENGTH_APPEND;
      PERMSAUX_perms_ok_list_to_v; ALL_APPEND; ALL_MAP; o_DEF; perms_ok_def;
      semanticPrimitives_Boolv_def; nat_to_v_def; SUBSET; IN_IMAGE; IN_UNIV;
      PULL_EXISTS; PERMSAUX_EL_SUB_SING; PERMSAUX_ALL_EL; PERMSAUX_ALL_LUPDATE;
      GE; NOT_LE; MEM_APPEND; MEM] THEN
  RW[perms_ok_def; perms_ok_ref_def; ALL; PERMSAUX_ALL_LUPDATE];;

let do_app_perms = prove
 (CASE_TERM
  `!refs (ffi:(FFI)ffi_state) op vs refs1 ffi1 res ps.
     do_app (refs,ffi) op vs = SOME ((refs1,ffi1),res) /\
     ~(op = Opapp) /\ ~(op = Eval) /\
     ALL (perms_ok ps) vs /\
     (RefAlloc IN ps ==> IMAGE RefMention (:num) SUBSET ps) /\
     (W8Alloc IN ps ==> IMAGE RefMention (:num) SUBSET ps) /\
     (!n. n < LENGTH refs /\ RefMention n IN ps ==> perms_ok_ref ps (EL n refs)) /\
     (op = Opref ==> RefAlloc IN ps) /\
     (op = Aalloc ==> RefAlloc IN ps) /\
     (op = AallocEmpty ==> RefAlloc IN ps) /\
     (op = AallocFixed ==> RefAlloc IN ps) /\
     (op = Aw8alloc ==> W8Alloc IN ps) /\
     (op = Opassign ==> RefUpdate IN ps) /\
     (!chn. op = FFI chn ==> FFIWrite (explode chn) IN ps /\ DoFFI IN ps) /\
     (!m. op = ThunkOp (AllocThunk m) ==> RefAlloc IN ps) /\
     (!m. op = ThunkOp (UpdateThunk m) ==> RefUpdate IN ps) /\
     ~(op = Opapp) ==>
     (!n. n < LENGTH refs1 /\ RefMention n IN ps ==> perms_ok_ref ps (EL n refs1)) /\
     (~(RefAlloc IN ps) /\ ~(W8Alloc IN ps) ==> LENGTH refs1 = LENGTH refs) /\
     (~(DoFFI IN ps) ==> ffi1 = ffi) /\
     (!ch out y. MEM (IO_event (ExtCall ch) out y) (ffi_state_io_events ffi1) ==>
                 MEM (IO_event (ExtCall ch) out y) (ffi_state_io_events ffi) \/
                 FFIWrite (explode ch) IN ps) /\
     (match list_result res with
        Rval vs -> ALL (perms_ok ps) vs
      | Rerr (Rraise v) -> perms_ok ps v
      | Rerr (Rabort err) -> T)`,
  PERMSAUX_SPLIT_TAC THEN PERMSAUX_FIN_TAC);;

let PERMSAUX_ALOOKUP_rec = prove
 (CASE_TERM
   `!(funs:(A#B#C)list) (g:A->D) x.
      ALOOKUP (MAP (\fne. match fne with (f,n,e) -> (f,g f)) funs) x =
      if MEM x (MAP FST funs) then SOME (g x) else NONE`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM; ALOOKUP_THM] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`h:A#B#C`,`h:A#B#C`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; FST; ALOOKUP_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(p1:A) = x` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let PERMSAUX_nsLookupMod_alist_to_ns = prove
 (`!(l:(N#V)list) (p:M list). ~(p = []) ==> nsLookupMod (alist_to_ns l) p = NONE`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; nsLookupMod_alist_to_ns]);;

let PERMSAUX_nsLookup_nsAppend_alist = prove
 (`!(l:(N#V)list) (e:(M,N,V)namespace) x v.
     nsLookup (nsAppend (alist_to_ns l) e) x = SOME v <=>
     nsLookup (alist_to_ns l) x = SOME v \/
     (nsLookup (alist_to_ns l) x = NONE /\ nsLookup e x = SOME v)`,
  SIMP[nsLookup_nsAppend_some; PERMSAUX_nsLookupMod_alist_to_ns]);;

let PERMSAUX_nsLookup_build_rec_env = prove
 (`!(funs:(varN#varN#exp)list) cl env x v.
     nsLookup (build_rec_env funs cl env) x = SOME v <=>
     (?f. x = Short f /\ MEM f (MAP FST funs) /\ v = Recclosure cl funs f) \/
     ((!f. MEM f (MAP FST funs) ==> ~(x = Short f)) /\ nsLookup env x = SOME v)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[build_rec_env_merge; PERMSAUX_nsLookup_nsAppend_alist;
              nsLookup_alist_to_ns_some; nsLookup_alist_to_ns_none;
              PERMSAUX_ALOOKUP_rec] THEN
  CASES_ON `x:(modN,varN)id` THEN
  SIMP[injectivity "id"; distinctness "id"] THEN
  RW[] THEN MESON_TAC[]);;

let PERMSAUX_IN_UNIONS_rec = prove
 (CASE_TERM
   `!(funs:(varN#varN#exp)list) fn vn e x.
      MEM (fn,vn,e) funs /\ x IN freevars e /\ ~(x = Short fn) /\ ~(x = Short vn) ==>
      x IN UNIONS (set_of_list (MAP (\fvx. match fvx with
                                       (fn,vn,x) -> freevars x DIFF {Short fn, Short vn})
                                    funs))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_UNIONS; IN_SET_OF_LIST; MEM_MAP] THEN
  EXISTS_TAC `freevars e DIFF {Short fn, Short vn}` THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
  EXISTS_TAC `(fn:varN,vn:varN,e:exp)` THEN ASM_REWRITE_TAC[pair_CASE]);;

let perms_ok_do_opapp = prove
 (`!ps fv av env e.
     perms_ok ps fv /\ perms_ok ps av /\ do_opapp [fv; av] = SOME (env,e) ==>
     perms_ok_exp ps e /\ perms_ok_env ps (freevars e) env`,
  REPEAT GEN_TAC THEN REWRITE_TAC[do_opapp_cases] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC)) THEN
  FIRST_X_ASSUM CAKE_STRIP_ASSUME_TAC THENL
   [(* Closure *)
    GVS[CONS_11; perms_ok_def; perms_ok_env_def; PULL_EXISTS] THEN
    X_GEN_TAC `x:(modN,varN)id` THEN X_GEN_TAC `w:v` THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`x:(modN,varN)id`; `w:v`]) THEN
    CASES_ON `x:(modN,varN)id` THEN
    FS[nsLookup_nsBind_compute; injectivity "id"; distinctness "id"] THEN
    RW[] THEN FS[] THEN GVS[COND_CASE_EQ] THEN ASM_MESON_TAC[];
    (* Recclosure *)
    GVS[CONS_11; perms_ok_def; find_recfun_ALOOKUP] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP ALOOKUP_MEM) THEN CONJ_TAC THENL
     [FS[ALL_MAP; GSYM ALL_MEM; o_THM] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `(n':varN,n'':varN,e':exp)`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SIMP[perms_ok_env_def] THEN X_GEN_TAC `x:(modN,varN)id` THEN X_GEN_TAC `w:v` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~(x = Short n'') /\ ~(x = Short n') /\
                  nsLookup (sem_env_v env'') x = SOME w ==> perms_ok ps w`
      ASSUME_TAC THENL
     [STRIP_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE[perms_ok_env_def]) THEN
      EXISTS_TAC `x:(modN,varN)id` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PERMSAUX_IN_UNIONS_rec THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `MEM (n':varN) (MAP FST (funs:(varN#varN#exp)list))` ASSUME_TAC THENL
     [REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `(n':varN,n'':varN,e':exp)` THEN
      ASM_REWRITE_TAC[FST];
      ALL_TAC] THEN
    CASES_ON `x:(modN,varN)id` THEN
    GVS[nsLookup_nsBind_compute; COND_CASE_EQ; PERMSAUX_nsLookup_build_rec_env;
        injectivity "id"; distinctness "id"; perms_ok_def] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* evaluate_perms_ok: evaluation respects the permissions.  The HOL4 proof   *)
(* goes case by case with gvs and the induction hypotheses resolved by       *)
(* drule; here each case of full_evaluate_ind has its tactic (in the list    *)
(* below), built from the following helpers.                                 *)
(* ------------------------------------------------------------------------- *)

(* an assumption !ps. a ==> c (an induction hypothesis whose evaluation    *)
(* the simplifier has already matched) is specialised to the goal's ps;     *)
(* if tac proves a, c is stripped into the assumptions and the hypothesis   *)
(* removed; repeated while some hypothesis can be used                       *)
let PERMSAUX_IHS_TAC (tac:tactic) : tactic = fun (asl,w as gl) ->
  let pty = `:permission->bool` in
  let ps = try find (fun v -> type_of v = pty)
                    (frees w @ flat (map (frees o concl o snd) asl))
           with Failure _ -> failwith "PERMSAUX_IHS_TAC: no ps" in
  let ihs = filter (fun (_,th) -> let c = concl th in
                      is_forall c && type_of (fst (dest_forall c)) = pty &&
                      is_imp (snd (dest_forall c))) asl in
  let use (_,ih) =
    UNDISCH_THEN (concl ih) (fun th ->
      MP_TAC (SPEC ps th) THEN ANTS_TAC THENL [tac THEN NO_TAC; STRIP_TAC]) in
  FIRST (map use ihs) gl;;

let PERMSAUX_EV_FIN_TAC : tactic =
  REPEAT (PERMSAUX_IHS_TAC (ASM_REWRITE_TAC[])) THEN
  IMP_RES_TAC evaluate_sing THEN GVS[ALL] THEN
  REPEAT CONJ_TAC THEN ASM_MESON_TAC[];;

let PERMSAUX_EV_START_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN STRIP_ASSUME_TAC);;

let PERMSAUX_EV_STD_TAC : tactic =
  PERMSAUX_EV_START_TAC THEN
  GVS[evaluate_def; pair_case_eq; case_eq "result"; case_eq "error_result"; ALL] THEN
  PERMSAUX_EV_FIN_TAC;;

let PERMSAUX_ALL_pes = prove
 (CASE_TERM
   `!ps env (pes:(pat#exp)list).
      ALL (\pe. match pe with
                  (p,x) -> perms_ok_env ps (freevars x DIFF
                                            set_of_list (MAP Short (pat_bindings p))) env)
          pes <=>
      perms_ok_env ps
        (UNIONS (set_of_list (MAP (\pe. match pe with
                                     (p,e) -> freevars e DIFF
                                              set_of_list (MAP Short (pat_bindings p)))
                                  pes)))
        env`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL; MAP; set_of_list; UNIONS_0; UNIONS_INSERT; perms_ok_env_UNION;
                  perms_ok_env_EMPTY] THEN
  SPEC_TAC(`h:pat#exp`,`h:pat#exp`) THEN REWRITE_TAC[FORALL_PAIR_THM; pair_CASE]);;

let PERMSAUX_getOpClass = prove
 (`!op. (getOpClass op = FunApp <=> op = Opapp) /\
        (getOpClass op = EvalOp <=> op = Eval) /\
        (getOpClass op = Force <=> op = ThunkOp ForceThunk) /\
        (getOpClass op = Simple <=>
         ~(op = Opapp) /\ ~(op = Eval) /\ ~(op = ThunkOp ForceThunk))`,
  GEN_TAC THEN CASES_ON `op:op` THEN REWRITE_TAC[getOpClass_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[distinctness "op_class"; distinctness "op";
                                      injectivity "op"] THEN
  CASES_ON `a:thunk_op` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "op_class"; distinctness "thunk_op"]);;

let PERMSAUX_do_opapp_perms = prove
 (`!ps vs env e.
     ALL (perms_ok ps) vs /\ do_opapp vs = SOME (env,e) ==>
     perms_ok_exp ps e /\ perms_ok_env ps (freevars e) env`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?fv av. (vs:v list) = [fv; av]` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM (MP_TAC o REWRITE_RULE[do_opapp_cases]) THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC perms_ok_do_opapp THEN
  EXISTS_TAC `fv:v` THEN EXISTS_TAC `av:v` THEN FS[ALL]);;

let PERMSAUX_do_opapp_REV = prove
 (`!vs env e ps.
     do_opapp (REVERSE vs) = SOME (env,e) ==> ALL (perms_ok ps) vs ==>
     perms_ok_exp ps e /\ perms_ok_env ps (freevars e) env`,
  REPEAT STRIP_TAC THEN MP_TAC (SPECL [`ps:permission->bool`; `REVERSE vs:v list`;
                                       `env:v sem_env`; `e:exp`] PERMSAUX_do_opapp_perms) THEN
  ASM_REWRITE_TAC[EVERY_REVERSE] THEN SIMP_TAC[]);;

(* resolve a do_opapp assumption (with REVERSE) and an ALL perms_ok fact *)
let PERMSAUX_OPAPP_TAC : tactic = fun (asl,w as gl) ->
  let pty = `:permission->bool` in
  let ps = find (fun v -> type_of v = pty)
                (frees w @ flat (map (frees o concl o snd) asl)) in
  FIRST_ASSUM (fun th -> MP_TAC (SPEC ps (MATCH_MP PERMSAUX_do_opapp_REV th)) THEN
                         ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN NO_TAC; STRIP_TAC]) gl;;

let PERMSAUX_dest_thunk = prove
 (`!ps (s:(FFI)state) vs m v.
     perms_ok_state ps s /\ ALL (perms_ok ps) vs /\
     dest_thunk vs (state_refs s) = IsThunk m v ==>
     perms_ok ps v`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ONELINE dest_thunk_def] THEN
  STRIP_TAC THEN
  GVS[list_case_eq; case_eq "v"; option_case_eq; case_eq "store_v";
      case_eq "thunk_mode"; COND_CASE_EQ; perms_ok_def; ALL; store_lookup_def;
      perms_ok_state_def] THEN
  FIRST_X_ASSUM (QSPEC_THEN "a1" MP_TAC) THEN ASM_REWRITE_TAC[perms_ok_ref_def]);;

let PERMSAUX_update_thunk = prove
 (`!ps (s:(FFI)state) vs vs2 refs.
     perms_ok_state ps s /\ ALL (perms_ok ps) vs2 /\
     update_thunk vs (state_refs s) vs2 = SOME refs ==>
     LENGTH refs = LENGTH (state_refs s) /\
     perms_ok_state ps (state_refs_fupd (K refs) s)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ONELINE update_thunk_def] THEN STRIP_TAC THEN
  GVS[list_case_eq; case_eq "v"; COND_CASE_EQ; case_eq "dest_thunk_ret"; ALL;
      store_assign_def; option_case_eq; perms_ok_state_def; LENGTH_LUPDATE;
      EL_LUPDATE] THEN
  RW[perms_ok_ref_def] THEN ASM_SIMP_TAC[]);;

let PERMSAUX_MP_TAC (th:thm) : tactic = fun (asl,w as gl) ->
  let pty = `:permission->bool` in
  let ps = find (fun v -> type_of v = pty)
                (frees w @ flat (map (frees o concl o snd) asl)) in
  FIRST_ASSUM (fun a ->
    let th1 = MATCH_MP th a in
    let c1 = concl th1 in
    let th2 = if is_forall c1 && type_of (fst (dest_forall c1)) = pty
              then SPEC ps th1 else th1 in
    MP_TAC th2 THEN
    REPEAT (ANTS_TAC THENL
              [ASM_REWRITE_TAC[EVERY_REVERSE; ALL; MAP; perms_ok_def] THEN NO_TAC;
               ALL_TAC]) THEN
    DISCH_THEN STRIP_ASSUME_TAC) gl;;

let PERMSAUX_dest_thunk_MP = prove
 (`!vs (s:(FFI)state) m v. dest_thunk vs (state_refs s) = IsThunk m v ==>
     !ps. perms_ok_state ps s ==> ALL (perms_ok ps) vs ==> perms_ok ps v`,
  MESON_TAC[PERMSAUX_dest_thunk]);;

let PERMSAUX_update_thunk_MP = prove
 (`!vs (s:(FFI)state) vs2 refs. update_thunk vs (state_refs s) vs2 = SOME refs ==>
     !ps. perms_ok_state ps s ==> ALL (perms_ok ps) vs2 ==>
          LENGTH refs = LENGTH (state_refs s) /\
          perms_ok_state ps (state_refs_fupd (K refs) s)`,
  MESON_TAC[PERMSAUX_update_thunk]);;

let PERMSAUX_do_opapp_MP = prove
 (`!vs env e. do_opapp vs = SOME (env,e) ==>
     !ps. ALL (perms_ok ps) vs ==>
          perms_ok_exp ps e /\ perms_ok_env ps (freevars e) env`,
  MESON_TAC[PERMSAUX_do_opapp_perms]);;

let PERMSAUX_EV_APP_START_TAC =
  PERMSAUX_EV_START_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [PERMSAUX_getOpClass]) THEN
  RULE_ASSUM_TAC (REWRITE_RULE[ALL; perms_ok_exp_thm; freevars_def; GSYM CONJ_ASSOC;
                               GSYM EVERY_perms_ok_env_BIGUNION]) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;
let PERMSAUX_EV_FORCE_FIN_TAC =
  REPEAT (PERMSAUX_IHS_TAC (ASM_REWRITE_TAC[])) THEN
  TRY (PERMSAUX_MP_TAC PERMSAUX_dest_thunk_MP) THEN
  TRY (PERMSAUX_MP_TAC PERMSAUX_do_opapp_MP) THEN
  REPEAT (PERMSAUX_IHS_TAC (ASM_REWRITE_TAC[])) THEN
  TRY (PERMSAUX_MP_TAC PERMSAUX_update_thunk_MP) THEN
  PERMSAUX_EV_FIN_TAC;;
let PERMSAUX_do_app_MP = IMP_CURRY_RULE do_app_perms;;
let PERMSAUX_EV_APP_TAC =
  PERMSAUX_EV_APP_START_TAC THEN
  ASM_CASES_TAC `op = Opapp` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    QPAT_X_ASSUM "evaluate _ _ [App _ _] = _" (MP_TAC o ONCE_REWRITE_RULE[evaluate_def]) THEN
    REWRITE_TAC[getOpClass_def] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[distinctness "op"]) THEN
    GVS[pair_case_eq; case_eq "result"; case_eq "error_result";
        option_case_eq; COND_CASE_EQ; EVERY_REVERSE; dec_clock_def] THEN
    REPEAT (PERMSAUX_IHS_TAC (ASM_REWRITE_TAC[])) THEN TRY PERMSAUX_OPAPP_TAC THEN
    PERMSAUX_EV_FIN_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `op = ThunkOp ForceThunk` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    QPAT_X_ASSUM "evaluate _ _ [App _ _] = _" (MP_TAC o ONCE_REWRITE_RULE[evaluate_def]) THEN
    REWRITE_TAC[getOpClass_def] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[distinctness "op"; injectivity "op";
                                 distinctness "thunk_op"]) THEN
    GVS[pair_case_eq; case_eq "result"; case_eq "error_result";
        option_case_eq; COND_CASE_EQ; EVERY_REVERSE; dec_clock_def;
        case_eq "dest_thunk_ret"; case_eq "thunk_mode"] THEN
    PERMSAUX_EV_FORCE_FIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `getOpClass op = Simple` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PERMSAUX_getOpClass]; ALL_TAC] THEN
  QPAT_X_ASSUM "evaluate _ _ [App _ _] = _" (MP_TAC o ONCE_REWRITE_RULE[evaluate_def]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  QPAT_X_ASSUM "getOpClass op = Simple" (K ALL_TAC) THEN DISCH_TAC THEN
  GVS[pair_case_eq; case_eq "result"; option_case_eq; EVERY_REVERSE] THEN
  REPEAT (PERMSAUX_IHS_TAC (ASM_REWRITE_TAC[])) THEN
  RULE_ASSUM_TAC (REWRITE_RULE[perms_ok_state_def]) THEN
  SIMP[perms_ok_state_def] THEN
  TRY (PERMSAUX_MP_TAC PERMSAUX_do_app_MP) THEN
  PERMSAUX_EV_FIN_TAC;;

let PERMSAUX_perms_ok_env_nsBind = prove
 (`!ps fvs n v env.
     perms_ok ps v /\ perms_ok_env ps (fvs DIFF {Short n}) env ==>
     perms_ok_env ps fvs (sem_env_v_fupd (K (nsBind n v (sem_env_v env))) env)`,
  REPEAT GEN_TAC THEN SIMP[perms_ok_env_def; IN_DIFF; IN_SING] THEN
  STRIP_TAC THEN X_GEN_TAC `x:(modN,varN)id` THEN X_GEN_TAC `w:v` THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`x:(modN,varN)id`; `w:v`]) THEN
  CASES_ON `x:(modN,varN)id` THEN
  REWRITE_TAC[nsLookup_nsBind_compute; injectivity "id"; distinctness "id"] THEN
  RW[] THEN GVS[COND_CASE_EQ]);;

let PERMSAUX_perms_ok_env_nsOptBind = prove
 (CASE_TERM
   `!ps fvs xo v env.
      perms_ok ps v /\
      perms_ok_env ps (fvs DIFF (match xo with SOME n -> {Short n} | _ -> {})) env ==>
      perms_ok_env ps fvs (sem_env_v_fupd (K (nsOptBind xo v (sem_env_v env))) env)`,
  REPEAT GEN_TAC THEN CASES_ON `xo:mlstring option` THEN
  REWRITE_TAC[option_CASE; nsOptBind_def; DIFF_EMPTY; PERMSAUX_perms_ok_env_nsBind] THEN
  SIMP[RECORD_SELFID_ss]);;

let PERMSAUX_build_rec_env_lookup = prove
 (CASE_TERM
   `!ps (funs:(varN#varN#exp)list) cl e x w.
      perms_ok_env ps
        (UNIONS (set_of_list (MAP (\fvx. match fvx with
                                     (fn,vn,x) -> freevars x DIFF {Short fn, Short vn})
                                  funs)))
        cl /\
      ALL (perms_ok_exp ps) (MAP (SND o SND) funs) /\
      nsLookup (build_rec_env funs cl e) x = SOME w ==>
      perms_ok ps w \/
      ((!f. MEM f (MAP FST funs) ==> ~(x = Short f)) /\ nsLookup e x = SOME w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PERMSAUX_nsLookup_build_rec_env] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[perms_ok_def]);;

let PERMSAUX_perms_ok_env_build_rec_env = prove
 (CASE_TERM
   `!ps fvs (funs:(varN#varN#exp)list) env.
      perms_ok_env ps
        (UNIONS (set_of_list (MAP (\fvx. match fvx with
                                     (fn,vn,x) -> freevars x DIFF {Short fn, Short vn})
                                  funs)))
        env /\
      ALL (perms_ok_exp ps) (MAP (SND o SND) funs) /\
      perms_ok_env ps (fvs DIFF set_of_list (MAP (Short o FST) funs)) env ==>
      perms_ok_env ps fvs
        (sem_env_v_fupd (K (build_rec_env funs env (sem_env_v env))) env)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SIMP[perms_ok_env_def] THEN
  X_GEN_TAC `x:(modN,varN)id` THEN X_GEN_TAC `w:v` THEN STRIP_TAC THEN
  MP_TAC (SPECL [`ps:permission->bool`; `funs:(varN#varN#exp)list`; `env:v sem_env`;
                 `sem_env_v (env:v sem_env)`; `x:(modN,varN)id`; `w:v`]
                PERMSAUX_build_rec_env_lookup) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM (MP_TAC o REWRITE_RULE[perms_ok_env_def] o check (fun th ->
    let c = concl th in try fst (dest_const (fst (strip_comb c))) = "perms_ok_env" &&
                            is_comb (rand (rator c)) with _ -> false)) THEN
  DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `x:(modN,varN)id` THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_SET_OF_LIST; MEM_MAP; o_THM] THEN
  ASM_MESON_TAC[MEM_MAP]);;

let PERMSAUX_pmatch_MP = prove
 (`!envC (st:(FFI)state) p v ws env.
     pmatch envC (state_refs st) p v ws = Match env ==>
     !ps. perms_ok ps v ==>
          (RefAlloc IN ps ==> IMAGE RefMention (:num) SUBSET ps) ==>
          perms_ok_state ps st ==>
          ALL (perms_ok ps) (MAP SND ws) ==>
          ALL (perms_ok ps) (MAP SND env)`,
  REWRITE_TAC[perms_ok_state_def] THEN MESON_TAC[pmatch_perms_ok]);;

let PERMSAUX_pmatch_extend = prove
 (`!envC s p v env.
     pmatch envC s p v [] = Match env ==> MAP FST env = pat_bindings p`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP (CONJUNCT1 pmatch_extend)) THEN
  REWRITE_TAC[APPEND_NIL] THEN MESON_TAC[]);;

let PERMSAUX_perms_ok_env_alist = prove
 (`!ps fvs (l:(varN#v)list) env.
     ALL (perms_ok ps) (MAP SND l) /\
     perms_ok_env ps (fvs DIFF set_of_list (MAP Short (MAP FST l))) env ==>
     perms_ok_env ps fvs (sem_env_v_fupd (K (nsAppend (alist_to_ns l) (sem_env_v env))) env)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SIMP[perms_ok_env_def] THEN
  X_GEN_TAC `x:(modN,varN)id` THEN X_GEN_TAC `w:v` THEN
  REWRITE_TAC[PERMSAUX_nsLookup_nsAppend_alist; nsLookup_alist_to_ns_some;
              nsLookup_alist_to_ns_none] THEN
  STRIP_TAC THENL
   [IMP_RES_TAC ALOOKUP_MEM THEN
    UNDISCH_TAC `ALL (perms_ok ps) (MAP SND (l:(varN#v)list))` THEN
    REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `(x':varN,w:v)` THEN ASM_REWRITE_TAC[SND];
    FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE[perms_ok_env_def] o
      check (fun th -> is_comb (concl th) &&
                       (try fst (dest_const (fst (strip_comb (concl th)))) = "perms_ok_env"
                        with Failure _ -> false))) THEN
    EXISTS_TAC `x:(modN,varN)id` THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_SET_OF_LIST; MEM_MAP] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `y:varN` THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `y:varN`) THEN ASM_REWRITE_TAC[ALOOKUP_NONE; MEM_MAP] THEN
    ASM_MESON_TAC[]]);;

let PERMSAUX_perms_ok_env_REC = prove
 (`!ps fvs env1 env2 c.
     perms_ok_env ps fvs env1 /\ perms_ok_env ps fvs env2 ==>
     perms_ok_env ps fvs (sem_env_REC (nsAppend (sem_env_v env2) (sem_env_v env1)) c)`,
  SIMP[perms_ok_env_def; nsLookup_nsAppend_some] THEN MESON_TAC[]);;

let PERMSAUX_perms_ok_env_UNIV = prove
 (`!ps fvs env. perms_ok_env ps (:(modN,varN)id) env ==> perms_ok_env ps fvs env`,
  REWRITE_TAC[perms_ok_env_def; IN_UNIV] THEN MESON_TAC[]);;

let PERMSAUX_perms_ok_env_alist_REC = prove
 (`!ps fvs (l:(varN#v)list) c.
     ALL (perms_ok ps) (MAP SND l) ==> perms_ok_env ps fvs (sem_env_REC (alist_to_ns l) c)`,
  REPEAT GEN_TAC THEN SIMP[perms_ok_env_def; nsLookup_alist_to_ns_some] THEN
  REPEAT STRIP_TAC THEN IMP_RES_TAC ALOOKUP_MEM THEN
  UNDISCH_TAC `ALL (perms_ok ps) (MAP SND (l:(varN#v)list))` THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN DISCH_THEN MATCH_MP_TAC THEN
  EXISTS_TAC `(x':varN,v:v)` THEN ASM_REWRITE_TAC[SND]);;

let PERMSAUX_UNIV_ENV_TAC : tactic =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (MATCH_MP_TAC PERMSAUX_perms_ok_env_UNIV THEN FIRST_ASSUM ACCEPT_TAC));;

let PERMSAUX_perms_ok_env_rec_REC = prove
 (CASE_TERM
   `!ps fvs (funs:(varN#varN#exp)list) env c.
      perms_ok_env ps
        (UNIONS (set_of_list (MAP (\fvx. match fvx with
                                     (fn,vn,x) -> freevars x DIFF {Short fn, Short vn})
                                  funs)))
        env /\
      ALL (perms_ok_exp ps) (MAP (SND o SND) funs) ==>
      perms_ok_env ps fvs (sem_env_REC (build_rec_env funs env nsEmpty) c)`,
  REPEAT STRIP_TAC THEN SIMP[perms_ok_env_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`ps:permission->bool`; `funs:(varN#varN#exp)list`; `env:v sem_env`;
                 `nsEmpty:(modN,varN,v)namespace`; `n:(modN,varN)id`; `v:v`]
                PERMSAUX_build_rec_env_lookup) THEN
  ASM_REWRITE_TAC[nsLookup_nsEmpty; option_DISTINCT]);;

let PERMSAUX_perms_ok_env_nsLift = prove
 (`!ps fvs mn e c.
     perms_ok_env ps (:(modN,varN)id) e ==>
     perms_ok_env ps fvs (sem_env_REC (nsLift mn (sem_env_v e)) c)`,
  REPEAT GEN_TAC THEN SIMP[perms_ok_env_def; IN_UNIV] THEN DISCH_TAC THEN
  X_GEN_TAC `x:(modN,varN)id` THEN X_GEN_TAC `w:v` THEN
  CASES_ON `x:(modN,varN)id` THEN REWRITE_TAC[nsLookup_nsLift] THEN
  CASE_REWRITE_TAC[] THEN RW[option_DISTINCT] THEN ASM_MESON_TAC[]);;

let evaluate_perms_ok = prove
 (CASE_TERM
  `(!(s:(FFI)state) env xs s' res ps.
     ALL (perms_ok_exp ps) xs /\
     ALL (\x. perms_ok_env ps (freevars x) env) xs /\
     perms_ok_state ps s /\
     (RefAlloc IN ps ==> IMAGE RefMention (:num) SUBSET ps) /\
     (W8Alloc IN ps ==> IMAGE RefMention (:num) SUBSET ps) /\
     evaluate s env xs = (s',res) ==>
     (~(RefAlloc IN ps) /\ ~(W8Alloc IN ps) ==>
      LENGTH (state_refs s') = LENGTH (state_refs s)) /\
     state_next_type_stamp s' = state_next_type_stamp s /\
     state_eval_state s' = state_eval_state s /\
     (~(DoFFI IN ps) ==> state_ffi s' = state_ffi s) /\
     perms_ok_state ps s' /\
     (!ffi out y.
        MEM (IO_event (ExtCall ffi) out y) (ffi_state_io_events (state_ffi s')) ==>
        MEM (IO_event (ExtCall ffi) out y) (ffi_state_io_events (state_ffi s)) \/
        FFIWrite (explode ffi) IN ps) /\
     (match res with
        Rerr (Rraise v) -> perms_ok ps v
      | Rval vs -> ALL (perms_ok ps) vs
      | _ -> T)) /\
  (!(s:(FFI)state) env v pes errv s' res ps.
     ALL (perms_ok_exp ps) (MAP SND pes) /\
     ALL (\pe. match pe with
                 (p,x) -> perms_ok_env ps (freevars x DIFF
                                           set_of_list (MAP Short (pat_bindings p))) env)
         pes /\
     perms_ok_state ps s /\
     perms_ok ps v /\
     perms_ok ps errv /\
     (RefAlloc IN ps ==> IMAGE RefMention (:num) SUBSET ps) /\
     (W8Alloc IN ps ==> IMAGE RefMention (:num) SUBSET ps) /\
     evaluate_match s env v pes errv = (s',res) ==>
     (~(RefAlloc IN ps) /\ ~(W8Alloc IN ps) ==>
      LENGTH (state_refs s') = LENGTH (state_refs s)) /\
     state_next_type_stamp s' = state_next_type_stamp s /\
     state_eval_state s' = state_eval_state s /\
     (~(DoFFI IN ps) ==> state_ffi s' = state_ffi s) /\
     perms_ok_state ps s' /\
     (!ffi out y.
        MEM (IO_event (ExtCall ffi) out y) (ffi_state_io_events (state_ffi s')) ==>
        MEM (IO_event (ExtCall ffi) out y) (ffi_state_io_events (state_ffi s)) \/
        FFIWrite (explode ffi) IN ps) /\
     (match res with
        Rerr (Rraise v) -> perms_ok ps v
      | Rval vs -> ALL (perms_ok ps) vs
      | _ -> T)) /\
  (!(s:(FFI)state) env ds s' res ps.
     ALL (perms_ok_dec ps) ds /\
     perms_ok_state ps s /\
     perms_ok_env ps (:(modN,varN)id) env /\
     (RefAlloc IN ps ==> IMAGE RefMention (:num) SUBSET ps) /\
     (W8Alloc IN ps ==> IMAGE RefMention (:num) SUBSET ps) /\
     evaluate_decs s env ds = (s',res) ==>
     (~(RefAlloc IN ps) /\ ~(W8Alloc IN ps) ==>
      LENGTH (state_refs s') = LENGTH (state_refs s)) /\
     (~(DoFFI IN ps) ==> state_ffi s' = state_ffi s) /\
     perms_ok_state ps s' /\
     (!ffi out y.
        MEM (IO_event (ExtCall ffi) out y) (ffi_state_io_events (state_ffi s')) ==>
        MEM (IO_event (ExtCall ffi) out y) (ffi_state_io_events (state_ffi s)) \/
        FFIWrite (explode ffi) IN ps) /\
     (match res with
        Rerr (Rraise v) -> perms_ok ps v
      | Rval env1 -> perms_ok_env ps (:(modN,varN)id) env1
      | _ -> T))`,
  MATCH_MP_TAC full_evaluate_ind THEN REPEAT CONJ_TAC THENL
  [
   (* 1 [] *)
   PERMSAUX_EV_START_TAC THEN GVS[evaluate_def; ALL];
   (* 2 e1::e2::es *)
   PERMSAUX_EV_STD_TAC;
   (* 3 Lit *)
   PERMSAUX_EV_START_TAC THEN GVS[evaluate_def; perms_ok_def; ALL];
   (* 4 Raise *)
   PERMSAUX_EV_STD_TAC;
   (* 5 Handle *)
   PERMSAUX_EV_START_TAC THEN
   GVS[evaluate_def; pair_case_eq; case_eq "result"; case_eq "error_result";
   COND_CASE_EQ; ALL; perms_ok_env_UNION; GSYM PERMSAUX_ALL_pes] THEN
   PERMSAUX_EV_FIN_TAC;
   (* 6 Con *)
   PERMSAUX_EV_START_TAC THEN
   GVS[evaluate_def; pair_case_eq; case_eq "result"; case_eq "error_result";
   COND_CASE_EQ; option_case_eq; ALL; GSYM EVERY_perms_ok_env_BIGUNION;
   EVERY_REVERSE; build_conv_def; perms_ok_def] THEN
   PERMSAUX_EV_FIN_TAC;
   (* 7 Var *)
   PERMSAUX_EV_START_TAC THEN
   GVS[evaluate_def; option_case_eq; ALL; perms_ok_env_def; IN_SING] THEN
   ASM_MESON_TAC[];
   (* 8 Fun *)
   PERMSAUX_EV_START_TAC THEN GVS[evaluate_def; ALL; perms_ok_def];
   (* 9 App *)
   PERMSAUX_EV_APP_TAC;
   (* 10 Log *)
   PERMSAUX_EV_START_TAC THEN
   GVS[evaluate_def; pair_case_eq; case_eq "result"; case_eq "error_result"; ALL;
   perms_ok_env_UNION; do_log_def; option_case_eq; case_eq "exp_or_val";
   COND_CASE_EQ] THEN
   PERMSAUX_EV_FIN_TAC;
   (* 11 If *)
   PERMSAUX_EV_START_TAC THEN
   GVS[evaluate_def; pair_case_eq; case_eq "result"; case_eq "error_result"; ALL;
   perms_ok_env_UNION; do_if_def; option_case_eq; COND_CASE_EQ] THEN
   PERMSAUX_EV_FIN_TAC;
   (* 12 Mat *)
   PERMSAUX_EV_START_TAC THEN
   GVS[evaluate_def; pair_case_eq; case_eq "result"; case_eq "error_result";
   COND_CASE_EQ; ALL; perms_ok_env_UNION; GSYM PERMSAUX_ALL_pes] THEN
   REPEAT (PERMSAUX_IHS_TAC (ASM_REWRITE_TAC[])) THEN
   IMP_RES_TAC evaluate_sing THEN GVS[HD] THEN PERMSAUX_EV_FIN_TAC;
   (* 13 Let *)
   PERMSAUX_EV_START_TAC THEN
   GVS[evaluate_def; pair_case_eq; case_eq "result"; case_eq "error_result"; ALL;
   perms_ok_env_UNION] THEN
   REPEAT (PERMSAUX_IHS_TAC (ASM_REWRITE_TAC[])) THEN
   IMP_RES_TAC evaluate_sing THEN GVS[HD] THEN
   REPEAT (PERMSAUX_IHS_TAC (ASM_SIMP_TAC[PERMSAUX_perms_ok_env_nsOptBind])) THEN
   PERMSAUX_EV_FIN_TAC;
   (* 14 Letrec *)
   PERMSAUX_EV_START_TAC THEN
   GVS[evaluate_def; COND_CASE_EQ; ALL; perms_ok_env_UNION] THEN
   REPEAT (PERMSAUX_IHS_TAC (ASM_SIMP_TAC[PERMSAUX_perms_ok_env_build_rec_env])) THEN
   PERMSAUX_EV_FIN_TAC;
   (* 15 Tannot *)
   PERMSAUX_EV_STD_TAC;
   (* 16 Lannot *)
   PERMSAUX_EV_STD_TAC;
   (* 17 evaluate_match [] *)
   PERMSAUX_EV_START_TAC THEN GVS[evaluate_def];
   (* 18 evaluate_match (p,e)::pes *)
   PERMSAUX_EV_START_TAC THEN
   GVS[evaluate_def; COND_CASE_EQ; case_eq "match_result"; ALL; MAP] THEN
   TRY (PERMSAUX_MP_TAC PERMSAUX_pmatch_MP) THEN
   IMP_RES_TAC PERMSAUX_pmatch_extend THEN
   REPEAT (PERMSAUX_IHS_TAC (ASM_SIMP_TAC[PERMSAUX_perms_ok_env_alist])) THEN
   PERMSAUX_EV_FIN_TAC;
   (* 19 evaluate_decs [] *)
   PERMSAUX_EV_START_TAC THEN GVS[evaluate_decs_def; perms_ok_env_def];
   (* 20 evaluate_decs d1::d2::ds *)
   PERMSAUX_EV_START_TAC THEN
   GVS[evaluate_decs_def; pair_case_eq; case_eq "result"; case_eq "error_result";
   ALL; combine_dec_result_def] THEN
   REPEAT (PERMSAUX_IHS_TAC (ASM_SIMP_TAC[perms_ok_env_extend_dec_env])) THEN
   GVS[PERMSAUX_perms_ok_env_REC] THEN PERMSAUX_EV_FIN_TAC;
   (* 21 Dlet *)
   PERMSAUX_EV_START_TAC THEN
   GVS[evaluate_decs_def; pair_case_eq; case_eq "result"; case_eq "error_result";
   COND_CASE_EQ; ALL] THEN
   REPEAT (PERMSAUX_IHS_TAC PERMSAUX_UNIV_ENV_TAC) THEN
   IMP_RES_TAC evaluate_sing THEN GVS[HD] THEN
   REPEAT TOP_CASE_TAC THEN GVS[case_eq "result"; case_eq "match_result"] THEN
   TRY (PERMSAUX_MP_TAC PERMSAUX_pmatch_MP) THEN
   GVS[PERMSAUX_perms_ok_env_alist_REC] THEN PERMSAUX_EV_FIN_TAC;
   (* 22 Dletrec *)
   PERMSAUX_EV_START_TAC THEN GVS[evaluate_decs_def; COND_CASE_EQ; ALL] THEN
   MATCH_MP_TAC PERMSAUX_perms_ok_env_rec_REC THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC PERMSAUX_perms_ok_env_UNIV THEN ASM_REWRITE_TAC[];
   (* 23 Dtype *)
   PERMSAUX_EV_START_TAC THEN
   GVS[evaluate_decs_def; COND_CASE_EQ; ALL; perms_ok_state_def; perms_ok_env_def;
   nsLookup_nsEmpty];
   (* 24 Dtabbrev *)
   PERMSAUX_EV_START_TAC THEN
   GVS[evaluate_decs_def; COND_CASE_EQ; ALL; perms_ok_state_def; perms_ok_env_def;
   nsLookup_nsEmpty];
   (* 25 Denv *)
   PERMSAUX_EV_START_TAC THEN
   GVS[evaluate_decs_def; option_case_eq; pair_case_eq; ALL; declare_env_def;
   case_eq "eval_state"; perms_ok_state_def; perms_ok_env_def; nsLookup_nsSing;
   COND_CASE_EQ; perms_ok_def; nat_to_v_def] THEN
   ASM_MESON_TAC[];
   (* 26 Dexn *)
   PERMSAUX_EV_START_TAC THEN
   GVS[evaluate_decs_def; COND_CASE_EQ; ALL; perms_ok_state_def; perms_ok_env_def;
   nsLookup_nsEmpty];
   (* 27 Dmod *)
   PERMSAUX_EV_START_TAC THEN
   GVS[evaluate_decs_def; pair_case_eq; case_eq "result"; ALL] THEN
   REPEAT (PERMSAUX_IHS_TAC (ASM_REWRITE_TAC[])) THEN
   ASM_SIMP_TAC[PERMSAUX_perms_ok_env_nsLift] THEN PERMSAUX_EV_FIN_TAC;
   (* 28 Dlocal *)
   PERMSAUX_EV_START_TAC THEN
   GVS[evaluate_decs_def; pair_case_eq; case_eq "result"; case_eq "error_result";
   ALL] THEN
   REPEAT (PERMSAUX_IHS_TAC (ASM_SIMP_TAC[perms_ok_env_extend_dec_env])) THEN
   PERMSAUX_EV_FIN_TAC]);;

let evaluate_perms_ok_exp = prove
 (CASE_TERM
  `!(s:(FFI)state) env exp s' res ps.
     perms_ok_exp ps exp /\
     perms_ok_env ps (freevars exp) env /\
     perms_ok_state ps s /\
     (RefAlloc IN ps ==> IMAGE RefMention (:num) SUBSET ps) /\
     (W8Alloc IN ps ==> IMAGE RefMention (:num) SUBSET ps) /\
     evaluate s env [exp] = (s',res) ==>
     (~(RefAlloc IN ps) /\ ~(W8Alloc IN ps) ==>
      LENGTH (state_refs s') = LENGTH (state_refs s)) /\
     state_next_type_stamp s' = state_next_type_stamp s /\
     state_eval_state s' = state_eval_state s /\
     (~(DoFFI IN ps) ==> state_ffi s' = state_ffi s) /\
     perms_ok_state ps s' /\
     (!ffi out y.
        MEM (IO_event (ExtCall ffi) out y) (ffi_state_io_events (state_ffi s')) ==>
        MEM (IO_event (ExtCall ffi) out y) (ffi_state_io_events (state_ffi s)) \/
        FFIWrite (explode ffi) IN ps) /\
     (match res with
        Rerr (Rraise v) -> perms_ok ps v
      | Rval vs -> ALL (perms_ok ps) vs
      | _ -> T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (CONJUNCT1 evaluate_perms_ok) THEN EXISTS_TAC `env:v sem_env` THEN
  EXISTS_TAC `[exp:exp]` THEN ASM_REWRITE_TAC[ALL]);;

let evaluate_perms_ok_pat = prove
 (CASE_TERM
  `!(s:(FFI)state) env v p e errv s' res ps.
     perms_ok_exp ps e /\
     perms_ok_env ps (freevars e DIFF set_of_list (MAP Short (pat_bindings p))) env /\
     perms_ok_state ps s /\
     perms_ok ps v /\
     perms_ok ps errv /\
     (RefAlloc IN ps ==> IMAGE RefMention (:num) SUBSET ps) /\
     (W8Alloc IN ps ==> IMAGE RefMention (:num) SUBSET ps) /\
     evaluate_match s env v [(p,e)] errv = (s',res) ==>
     (~(RefAlloc IN ps) /\ ~(W8Alloc IN ps) ==>
      LENGTH (state_refs s') = LENGTH (state_refs s)) /\
     state_next_type_stamp s' = state_next_type_stamp s /\
     state_eval_state s' = state_eval_state s /\
     (~(DoFFI IN ps) ==> state_ffi s' = state_ffi s) /\
     perms_ok_state ps s' /\
     (!ffi out y.
        MEM (IO_event (ExtCall ffi) out y) (ffi_state_io_events (state_ffi s')) ==>
        MEM (IO_event (ExtCall ffi) out y) (ffi_state_io_events (state_ffi s)) \/
        FFIWrite (explode ffi) IN ps) /\
     (match res with
        Rerr (Rraise v) -> perms_ok ps v
      | Rval vs -> ALL (perms_ok ps) vs
      | _ -> T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 evaluate_perms_ok)) THEN
  MAP_EVERY EXISTS_TAC [`env:v sem_env`; `v:v`; `[(p:pat,e:exp)]`; `errv:v`] THEN
  ASM_REWRITE_TAC[ALL; MAP; SND; pair_CASE]);;

let evaluate_perms_ok_dec = prove
 (CASE_TERM
  `!(s:(FFI)state) env dec s' res ps.
     perms_ok_dec ps dec /\
     perms_ok_state ps s /\
     perms_ok_env ps (:(modN,varN)id) env /\
     (RefAlloc IN ps ==> IMAGE RefMention (:num) SUBSET ps) /\
     (W8Alloc IN ps ==> IMAGE RefMention (:num) SUBSET ps) /\
     evaluate_decs s env [dec] = (s',res) ==>
     (~(RefAlloc IN ps) /\ ~(W8Alloc IN ps) ==>
      LENGTH (state_refs s') = LENGTH (state_refs s)) /\
     (~(DoFFI IN ps) ==> state_ffi s' = state_ffi s) /\
     perms_ok_state ps s' /\
     (!ffi out y.
        MEM (IO_event (ExtCall ffi) out y) (ffi_state_io_events (state_ffi s')) ==>
        MEM (IO_event (ExtCall ffi) out y) (ffi_state_io_events (state_ffi s)) \/
        FFIWrite (explode ffi) IN ps) /\
     (match res with
        Rerr (Rraise v) -> perms_ok ps v
      | Rval env1 -> perms_ok_env ps (:(modN,varN)id) env1
      | _ -> T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (CONJUNCT2 (CONJUNCT2 evaluate_perms_ok)) THEN
  MAP_EVERY EXISTS_TAC [`env:v sem_env`; `[dec:dec]`] THEN
  ASM_REWRITE_TAC[ALL]);;
