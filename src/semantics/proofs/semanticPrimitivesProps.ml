(* ========================================================================= *)
(* semanticPrimitivesProps: port of HOL4                                     *)
(* semantics/proofs/semanticPrimitivesPropsScript.sml (CakeML v3479).        *)
(* Various basic properties of the semantic primitives.                     *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's relation composition R1 O R2 is written out as                   *)
(*   (\x z. ?y. R2 x y /\ R1 y z) (as LIST_REL_O in hol4/list.ml).           *)
(* - HOL4's word_lsl, word_lsr, word_asr, word_ror are word_shl, word_ushr,  *)
(*   word_ishr, word_ror (as in semanticPrimitives.ml).                      *)
(* - The local pair_case_eq of the script is the kit's pair_case_eq.         *)
(* - HOL4's Overload SFV (the set of x with Short x IN FV e) is an          *)
(*   abbreviation, not a definition.                                         *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/proofs/namespaceProps.ml";;

type_invention_error := true;;

let with_same_v = prove
 (`!env:V sem_env. sem_env_v_fupd (combin_K (sem_env_v env)) env = env`,
  REWRITE_TAC[sem_env_component_equality; sem_env_INFO.ri_accfupds; K_THM]);;
let _ = cake_add_simps [with_same_v];;

let unchanged_env = prove
 (`!env:A sem_env. sem_env_REC (sem_env_v env) (sem_env_c env) = env`,
  REWRITE_TAC[sem_env_component_equality; sem_env_INFO.ri_accessors]);;
let _ = cake_add_simps [unchanged_env];;

let with_same_clock = prove
 (`!st:(FFI)state. state_clock_fupd (combin_K (state_clock st)) st = st`,
  REWRITE_TAC[state_component_equality; state_INFO.ri_accfupds; K_THM]);;

(* HOL4: Boolv_11 *)
let semanticPrimitivesProps_Boolv_11 = prove
 (`!b1 b2. Boolv b1 = Boolv b2 <=> b1 = b2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[semanticPrimitives_Boolv_def] THEN
  MAP_EVERY BOOL_CASES_TAC [`b1:bool`; `b2:bool`] THEN SIMP[]);;
let _ = cake_add_simps [semanticPrimitivesProps_Boolv_11];;

let extend_dec_env_assoc = prove
 (`!env1 env2 env3.
     extend_dec_env env1 (extend_dec_env env2 env3) =
     extend_dec_env (extend_dec_env env1 env2) env3`,
  REWRITE_TAC[extend_dec_env_def; sem_env_INFO.ri_accessors; nsAppend_assoc]);;
let _ = cake_add_simps [extend_dec_env_assoc];;

let shift_lookup_def = cake_def
  `(shift_lookup Lsl = (word_shl:A word->num->A word)) /\
   (shift_lookup Lsr = (word_ushr:A word->num->A word)) /\
   (shift_lookup Asr = (word_ishr:A word->num->A word)) /\
   (shift_lookup Ror = (word_ror:A word->num->A word))`;;
let _ = cake_add_simps [shift_lookup_def];;

(* the clauses are parsed apart: w is a byte in one and an int64 in the     *)
(* other                                                                     *)
let do_shift_def = sem1aux_def (list_mk_conj
  [`do_shift sh n W8 (Word8 w) = SOME (Word8 (shift_lookup sh w n))`;
   `do_shift sh n W64 (Word64 w) = SOME (Word64 (shift_lookup sh w n))`;
   `do_shift (_:shift) (_:num) (_:word_size) (_:lit) = (NONE:lit option)`]);;
let _ = cake_add_simps [do_shift_def];;

(* HOL4's do_word_op_def, do_word_to_int_def and do_word_from_int_def are in *)
(* a comment of the script (not defined)                                     *)

let lit_same_type_refl = prove
 (`!l. lit_same_type l l`,
  GEN_TAC THEN CASES_ON `l:lit` THEN SIMP[lit_same_type_def]);;
let _ = cake_add_simps [lit_same_type_refl];;

let lit_same_type_sym = prove
 (`!l1 l2. lit_same_type l1 l2 ==> lit_same_type l2 l1`,
  REPEAT GEN_TAC THEN CASES_ON `l1:lit` THEN CASES_ON `l2:lit` THEN
  SIMP[lit_same_type_def]);;

let pmatch_append = prove
 (`(!(cenv:env_ctor) (st:(v store_v) list) p v env env' env''.
      pmatch cenv st p v env = Match env' ==>
      pmatch cenv st p v (APPEND env env'') = Match (APPEND env' env'')) /\
   (!(cenv:env_ctor) (st:(v store_v) list) ps v env env' env''.
      pmatch_list cenv st ps v env = Match env' ==>
      pmatch_list cenv st ps v (APPEND env env'') = Match (APPEND env' env''))`,
  MATCH_MP_TAC pmatch_ind THEN RW[pmatch_def] THEN EVERY_CASE_TAC THEN FS[] THEN
  ASM_METIS_TAC[]);;

let pmatch_extend = prove
 (`(!(cenv:env_ctor) (s:(v store_v) list) p v env env' (env'':(varN#v)list).
      pmatch cenv s p v env = Match env'
      ==> ?env''. env' = APPEND env'' env /\ MAP FST env'' = pat_bindings p) /\
   (!(cenv:env_ctor) (s:(v store_v) list) ps vs env env' (env'':(varN#v)list).
      pmatch_list cenv s ps vs env = Match env'
      ==> ?env''. env' = APPEND env'' env /\ MAP FST env'' = pats_bindings ps)`,
  MATCH_MP_TAC pmatch_ind THEN RW[pat_bindings_def; pmatch_def] THEN
  EVERY_CASE_TAC THEN FS[] THEN RW[] THEN RES_TAC THEN RVEQ_TAC THEN RW[] THEN
  FIRST
   [EXISTS_TAC `APPEND env'' [(i:varN,v:v)]` THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; MAP_APPEND; MAP] THEN NO_TAC;
    EXISTS_TAC `[(x:varN,v':v)]` THEN REWRITE_TAC[APPEND; CONS_11] THEN
    EXISTS_TAC `(x:varN,v':v)` THEN REWRITE_TAC[FST]]);;

let EVALAUX_nsLookup_nsAppend_SOME = prove
 (`!(e1:(M,N,V)namespace) id e2 v.
     nsLookup e1 id = SOME v ==> nsLookup (nsAppend e1 e2) id = SOME v`,
  SIMP[nsLookup_nsAppend_some]);;

let pmatch_nsAppend = prove
 (`(!(ns:env_ctor) (st:(v store_v) list) pat v env m ns'.
      (pmatch ns st pat v env = No_match
       ==> pmatch (nsAppend ns ns') st pat v env = No_match) /\
      (pmatch ns st pat v env = Match m
       ==> pmatch (nsAppend ns ns') st pat v env = Match m)) /\
   (!(ns:env_ctor) (st:(v store_v) list) pats vs env m ns'.
      (pmatch_list ns st pats vs env = No_match
       ==> pmatch_list (nsAppend ns ns') st pats vs env = No_match) /\
      (pmatch_list ns st pats vs env = Match m
       ==> pmatch_list (nsAppend ns ns') st pats vs env = Match m))`,
  MATCH_MP_TAC pmatch_ind THEN RW[pmatch_def] THEN
  EVERY_CASE_TAC THEN FS[] THEN IMP_RES_TAC EVALAUX_nsLookup_nsAppend_SOME THEN
  GVS[] THEN RES_TAC THEN GVS[]);;

(* HOL4: pmatch_nsAppend |> cj 1 |> cj 1 and pmatch_nsAppend |> cj 1 |> cj 2 *)
let pmatch_nsAppend_No_match =
  GEN_ALL (CONJUNCT1 (SPEC_ALL (CONJUNCT1 pmatch_nsAppend)));;

let pmatch_nsAppend_Match =
  GEN_ALL (CONJUNCT2 (SPEC_ALL (CONJUNCT1 pmatch_nsAppend)));;

let EVALAUX_CONS_APPEND_RCANCEL = prove
 (`!(a:A) l1 l2 l. CONS a (APPEND l1 l2) = APPEND l l2 <=> CONS a l1 = l`,
  REWRITE_TAC[GSYM(CONJUNCT2 APPEND); APPEND_RCANCEL]);;

let pmatch_acc = prove
 (`(!(envc:env_ctor) (store:(v store_v) list) p v env env' env2.
      (pmatch envc store p v env = Match env' <=>
       pmatch envc store p v (APPEND env env2) = Match (APPEND env' env2)) /\
      (pmatch envc store p v env = No_match <=>
       pmatch envc store p v (APPEND env env2) = No_match) /\
      (pmatch envc store p v env = Match_type_error <=>
       pmatch envc store p v (APPEND env env2) = Match_type_error)) /\
   (!(envc:env_ctor) (store:(v store_v) list) ps vs env env' env2.
      (pmatch_list envc store ps vs env = Match env' <=>
       pmatch_list envc store ps vs (APPEND env env2) = Match (APPEND env' env2)) /\
      (pmatch_list envc store ps vs env = No_match <=>
       pmatch_list envc store ps vs (APPEND env env2) = No_match) /\
      (pmatch_list envc store ps vs env = Match_type_error <=>
       pmatch_list envc store ps vs (APPEND env env2) = Match_type_error))`,
  MATCH_MP_TAC pmatch_ind THEN RW[pmatch_def; EVALAUX_CONS_APPEND_RCANCEL] THEN
  EVERY_CASE_TAC THEN RW[] THEN
  ASM_METIS_TAC[distinctness "match_result"; injectivity "match_result"]);;

(* HOL4: val eqs = LIST_CONJ (map TypeBase.case_eq_of [op, list, option, v,  *)
(* store_v, lit, eq_result, word_size]) (see do_app_cases below); the local *)
(* pair_case_eq is the kit's pair_case_eq                                    *)

(* HOL4 [local] *)
let pair_lam_lem = prove
 (CASE_TERM `!(f:A->B->C) v z. (let (x,y) = z in f x y) = v <=>
             ?x1 x2. z = (x1,x2) /\ f x1 x2 = v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pair_case_eq] THEN MESON_TAC[]);;

(* HOL4: do_app_cases is the result of simplifying do_app (s,t) op vs =     *)
(* SOME (st',v) with do_app_def, the case equations eqs, pair_case_eq,       *)
(* pair_lam_lem and PULL_EXISTS (srw_ss() ++ COND_elim_ss); here the same    *)
(* with the kit's simplifier: a disjunction over the operators (its form is  *)
(* that of our simplifier, not HOL4's; bound variables renamed apart)        *)

let EVALAUX_do_app_eqs =
  [pair_case_eq; option_case_eq; list_case_eq; COND_CASE_EQ] @
  map case_eq ["op"; "v"; "store_v"; "lit"; "eq_result"; "word_size"];;

(* bound variables renamed apart from every enclosing binder and free        *)
(* variable (also of other types), for readable statements                   *)
let EVALAUX_RENAME_APART_RULE th =
  let rec fresh n used = if mem n used then fresh (n^"'") used else n in
  let rec go used t = match t with
      Abs(v,b) -> let n,ty = dest_var v in
                  let n' = fresh n used in
                  let v' = mk_var(n',ty) in
                  let b' = if n' = n then b else vsubst [v',v] b in
                  mk_abs(v',go (n'::used) b')
    | Comb(a,b) -> mk_comb(go used a,go used b)
    | _ -> t in
  let c = concl th in
  let c' = go (map (fst o dest_var) (frees c)) c in
  EQ_MP (ALPHA c c') th;;

let do_app_cases =
  EVALAUX_RENAME_APART_RULE
   (CAKE_SIMP_CONV ([do_app_def; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM;
                     pair_lam_lem] @ EVALAUX_do_app_eqs)
      `do_app (s,t:(A)ffi_state) op vs = SOME (st',v)`);;

let do_opapp_cases = prove
 (CASE_TERM `!env' vs v.
    do_opapp vs = SOME (env',v) <=>
    (?v2 env'' n e.
       vs = [Closure env'' n e; v2] /\
       env' = sem_env_v_fupd (combin_K (nsBind n v2 (sem_env_v env''))) env'' /\ v = e) \/
    (?v2 env'' funs n' n'' e.
       vs = [Recclosure env'' funs n'; v2] /\
       find_recfun n' funs = SOME (n'',e) /\
       ALL_DISTINCT (MAP (\fxe. match fxe with (f,x,e) -> f) funs) /\
       env' = sem_env_v_fupd (combin_K (nsBind n'' v2 (build_rec_env funs env''
                                                  (sem_env_v env'')))) env'' /\
       v = e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[do_opapp_def] THEN
  CASES_ON `vs:v list` THEN SIMP[] THEN
  CASES_ON `t:v list` THEN SIMP[] THEN
  CASES_ON `h:v` THEN SIMP[] THEN
  CASES_ON `t':v list` THEN SIMP[] THEN
  RW[] THEN EVERY_CASE_TAC THEN GVS[] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The ffi state matters only to the FFI operator: for any other operator   *)
(*   do_app (s,t') op vs = OPTION_MAP (\((a,b),c). ((a,t'),c)) (do_app (s,t) op vs). *)
(* Proved by pushing OPTION_MAP through the case tree of do_app_def (each   *)
(* case constant, conditional and let commutes with a function applied to   *)
(* it) down to its leaves NONE and SOME ((a,t),c).                            *)
(* ------------------------------------------------------------------------- *)

let EVALAUX_case_rand_cache = ref ([]:(string*thm) list);;

(* the type variables of th renamed apart from those of any term it is      *)
(* specialised to                                                            *)
let EVALAUX_TVS_APART th =
  let tvs = type_vars_in_term (concl th) in
  INST_TYPE (map2 (fun tv i -> mk_vartype("EVALAUX_TV"^string_of_int i),tv)
                  tvs (1--length tvs)) th;;

(* !g x f1 .. fn. g (C x f1 .. fn) = C x (\ys. g (f1 ys)) .. (\ys. g (fn ys)) *)
let EVALAUX_case_rand (ci:case_info) =
  let cname = fst(dest_const ci.ci_case) in
  try assoc cname !EVALAUX_case_rand_cache with Failure _ ->
  let c = ci.ci_case in
  let cty = type_of c in
  let n = length ci.ci_pats in
  let rec split k ty acc =
    if k = 0 then rev acc,ty else
    let a,b = dest_fun_ty ty in split (k-1) b (a::acc) in
  let argtys,rty = split (n+1) cty [] in
  if not (is_vartype rty) then failwith "EVALAUX_case_rand: result type" else
  let xty = hd argtys and armtys = tl argtys in
  let used = map dest_vartype (tyvars cty) in
  let sty = mk_vartype (find (fun s -> not (mem s used)) ["S";"S1";"S2";"S3";"S4"]) in
  let g = mk_var("g",mk_fun_ty rty sty) and x = mk_var("x",xty) in
  let fs = map2 (fun ty i -> mk_var("f"^string_of_int i,ty)) armtys (1--n) in
  let arms = map2 (fun ((vs,_),f) i ->
      let k = length vs in
      let tys,_ = split k (type_of f) [] in
      let ys = map2 (fun ty j -> mk_var("y"^string_of_int i^"_"^string_of_int j,ty))
                    tys (1--k) in
      list_mk_abs(ys,mk_comb(g,list_mk_comb(f,ys)))) (zip ci.ci_pats fs) (1--n) in
  let c' = inst [sty,rty] c in
  let lhs_ = mk_comb(g,list_mk_comb(c,x::fs)) in
  let rhs_ = list_mk_comb(c',x::arms) in
  let tm = list_mk_forall(g::x::fs,mk_eq(lhs_,rhs_)) in
  let th = prove(tm,
    GEN_TAC THEN X_GEN_TAC x THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC(ISPEC x ci.ci_nchotomy) THEN REWRITE_TAC[ci.ci_def]) in
  let th = EVALAUX_TVS_APART th in
  EVALAUX_case_rand_cache := (cname,th) :: !EVALAUX_case_rand_cache;
  th;;

let EVALAUX_LET_RAND = prove
 (`!(g:B->C) (f:A->B) x. g (LET f x) = LET (\y. g (f y)) x`,
  REWRITE_TAC[LET_DEF]);;

let EVALAUX_LET_END_RAND = prove
 (`!(g:A->B) x. g (LET_END x) = LET_END (g x)`,
  REWRITE_TAC[LET_END_DEF]);;

(* push g0 (a function term) through the case constants, conditionals and   *)
(* lets of its argument, then apply the leaf rules                           *)
let EVALAUX_PUSH_CONV (g0:term) (leaves:thm list) : conv =
  let leaf_net =
    itlist (net_of_thm true) (itlist (mk_rewrites false) leaves []) empty_net in
  let cond_rule = ISPEC g0 (EVALAUX_TVS_APART bool_COND_RAND)
  and let_rule = ISPEC g0 (EVALAUX_TVS_APART EVALAUX_LET_RAND)
  and let_end_rule = ISPEC g0 (EVALAUX_TVS_APART EVALAUX_LET_END_RAND) in
  let step tm =
    if not (is_comb tm) || rator tm <> g0 then failwith "EVALAUX_PUSH_CONV" else
    let a = rand tm in
    if is_case_app a then
      let c,_,_ = dest_case_app a in
      REWR_CONV (ISPEC g0 (EVALAUX_case_rand (case_info_of_const c))) tm
    else if is_cond a then REWR_CONV cond_rule tm
    else if is_comb a && is_comb (rator a) && is_const (rator(rator a)) &&
            fst(dest_const(rator(rator a))) = "LET" then REWR_CONV let_rule tm
    else if is_comb a && is_const (rator a) &&
            fst(dest_const(rator a)) = "LET_END" then REWR_CONV let_end_rule tm
    else REWRITES_CONV leaf_net tm in
  TOP_DEPTH_CONV (step ORELSEC BETA_CONV);;

let EVALAUX_ffi_fix_tm =
  CASE_TERM `\p:((v store_v) list # (A)ffi_state) # (v,v)result.
               match p with ((a,b),c) -> ((a,t':(B)ffi_state),c)`;;
let EVALAUX_ffi_fix_map =
  mk_icomb(`OPTION_MAP:(X->Y)->X option->Y option`,EVALAUX_ffi_fix_tm);;

let EVALAUX_ffi_fix_leaves =
  [prove(mk_eq(mk_comb(EVALAUX_ffi_fix_map,
                 `NONE:(((v store_v) list # (A)ffi_state) # (v,v)result) option`),
               `NONE:(((v store_v) list # (B)ffi_state) # (v,v)result) option`),
         REWRITE_TAC[OPTION_MAP_DEF]);
   prove(list_mk_forall([`a:(v store_v) list`; `b:(A)ffi_state`; `c:(v,v)result`],
           mk_eq(mk_comb(EVALAUX_ffi_fix_map,
                   `SOME ((a:(v store_v) list,b:(A)ffi_state),c:(v,v)result)`),
                 `SOME ((a:(v store_v) list,t':(B)ffi_state),c:(v,v)result)`)),
         REWRITE_TAC[OPTION_MAP_DEF; pair_CASE])];;
let EVALAUX_do_app_ffi_indep = prove
 (list_mk_forall([`s:(v store_v) list`; `t:(A)ffi_state`; `t':(B)ffi_state`; `op:op`;
                  `vs:v list`],
   mk_imp(`!n. ~(op = FFI n)`,
     mk_eq(`do_app (s,t':(B)ffi_state) op vs`,
           mk_comb(EVALAUX_ffi_fix_map,`do_app (s,t:(A)ffi_state) op vs`)))),
  REPEAT GEN_TAC THEN CASES_ON `op:op` THEN
  REWRITE_TAC[distinctness "op"; injectivity "op"] THEN
  TRY(DISCH_THEN(fun th -> let x = lhs(dest_neg(snd(dest_forall(concl th)))) in
                           MP_TAC(SPEC x th) THEN REWRITE_TAC[] THEN NO_TAC)) THEN
  REWRITE_TAC[do_app_def; thunk_op_def] THEN CAKE_REWRITE_TAC[] THEN
  CONV_TAC(RAND_CONV (EVALAUX_PUSH_CONV EVALAUX_ffi_fix_map EVALAUX_ffi_fix_leaves)) THEN
  CONV_TAC(LAND_CONV (TOP_DEPTH_CONV BETA_CONV)) THEN REFL_TAC);;

let EVALAUX_store_assign_W8array = prove
 (`!lnum (s:(v store_v) list) ws ws'.
     store_lookup lnum s = SOME (W8array ws)
     ==> store_assign lnum (W8array ws') s = SOME (LUPDATE (W8array ws') lnum s)`,
  REWRITE_TAC[store_lookup_def; store_assign_def] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN SIMP[] THEN DISCH_TAC THEN SIMP[store_v_same_type_def]);;

let EVALAUX_call_FFI_same = prove
 (`!(t:(FFI)ffi_state) s conf bytes bytes'.
     call_FFI t s conf bytes = FFI_return t bytes'
     ==> s = ExtCall (implode "") /\ bytes' = bytes`,
  REPEAT GEN_TAC THEN REWRITE_TAC[call_FFI_def] THEN
  COND_CASES_TAC THEN SIMP[] THEN
  CASES_ON `ffi_state_oracle (t:(FFI)ffi_state) s (ffi_state_ffi_state t) conf bytes` THEN
  SIMP[] THEN COND_CASES_TAC THEN SIMP[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `ffi_state_io_events:(FFI)ffi_state->io_event list` o
             CONJUNCT1) THEN
  SIMP[] THEN DISCH_THEN(MP_TAC o AP_TERM `LENGTH:io_event list->num`) THEN
  SIMP[LENGTH_APPEND] THEN ARITH_TAC);;

let EVALAUX_do_app_FFI_NONE = prove
 (`!s (t:(A)ffi_state) n vs.
     do_app (s,t) (FFI n) vs = NONE <=>
     ~(?conf b lnum ws. vs = [Litv (StrLit conf); Loc b lnum] /\
                       store_lookup lnum s = SOME (W8array ws))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN IMP_RES_TAC EVALAUX_store_assign_W8array THEN GVS[]);;

let do_app_NONE_ffi = prove
 (`!refs (ffi:(A)ffi_state) op args (ffi':(B)ffi_state).
     do_app (refs,ffi) op args = NONE ==> do_app (refs,ffi') op args = NONE`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `?n. op = FFI n` THENL
   [FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC) THEN REWRITE_TAC[EVALAUX_do_app_FFI_NONE];
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN
    MP_TAC(SPECL [`refs:(v store_v)list`; `ffi:(A)ffi_state`; `ffi':(B)ffi_state`;
                  `op:op`; `args:v list`] EVALAUX_do_app_ffi_indep) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[OPTION_MAP_DEF]]);;

let EVALAUX_do_app_FFI_same = prove
 (`!s (t:(A)ffi_state) n vs s' r (t':(B)ffi_state).
     do_app (s,t) (FFI n) vs = SOME ((s',t),r) /\
     (!outcome. ~(r = Rerr (Rabort (Rffi_error outcome))))
     ==> do_app (s,t') (FFI n) vs = SOME ((s',t'),r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  STRIP_TAC THEN GVS(EVALAUX_do_app_eqs @ [case_eq "ffi_result"]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP EVALAUX_call_FFI_same) THEN
  GVS[call_FFI_def]);;

let do_app_SOME_ffi_same = prove
 (`!refs (ffi:(A)ffi_state) op args refs' r (ffi':(B)ffi_state).
     do_app (refs,ffi) op args = SOME ((refs',ffi),r) /\
     (!outcome. ~(r = Rerr (Rabort (Rffi_error outcome))))
     ==> do_app (refs,ffi') op args = SOME ((refs',ffi'),r)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `?n. op = FFI n` THENL
   [FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC[EVALAUX_do_app_FFI_same];
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN
    MP_TAC(SPECL [`refs:(v store_v)list`; `ffi:(A)ffi_state`; `ffi':(B)ffi_state`;
                  `op:op`; `args:v list`] EVALAUX_do_app_ffi_indep) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[OPTION_MAP_DEF; pair_CASE]]);;

let do_app_ffi_unchanged = prove
 (`!st (ffi:(A)ffi_state) op vs st' ffi' res.
     (!s. ~(op = FFI s)) /\ do_app (st,ffi) op vs = SOME ((st',ffi'),res)
     ==> ffi = ffi'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`st:(v store_v)list`; `ffi:(A)ffi_state`; `ffi:(A)ffi_state`;
                `op:op`; `vs:v list`]
           (INST_TYPE [`:A`,`:B`] EVALAUX_do_app_ffi_indep)) THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; pair_CASE; option_INJ; PAIR_EQ] THEN
  MESON_TAC[]);;

let do_app_ffi_changed = prove
 (`!st (ffi:(A)ffi_state) op vs st' ffi' res.
     do_app (st,ffi) op vs = SOME ((st',ffi'),res) /\ ~(ffi = ffi')
     ==> ?s conf lnum ws ffi_st ws' b.
           op = FFI s /\
           vs = [Litv (StrLit conf); Loc b lnum] /\
           store_lookup lnum st = SOME (W8array ws) /\
           ~(s = implode "") /\
           ffi_state_oracle ffi (ExtCall s) (ffi_state_ffi_state ffi)
             (MAP (\c. word (ORD c)) (explode conf)) ws = Oracle_return ffi_st ws' /\
           LENGTH ws = LENGTH ws' /\
           st' = LUPDATE (W8array ws') lnum st /\
           ffi_state_oracle ffi' = ffi_state_oracle ffi /\
           ffi_state_ffi_state ffi' = ffi_st /\
           ffi_state_io_events ffi' =
             APPEND (ffi_state_io_events ffi)
               [IO_event (ExtCall s) (MAP (\c. word (ORD c)) (explode conf))
                         (ZIP ws ws')]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `?s. op = FFI s` THENL
   [ALL_TAC; ASM_MESON_TAC[do_app_ffi_unchanged]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `s:mlstring` SUBST_ALL_TAC) THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN GVS(EVALAUX_do_app_eqs @ [case_eq "ffi_result"]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[call_FFI_def; o_DEF]) THEN
  IMP_RES_TAC EVALAUX_store_assign_W8array THEN
  GVS[COND_CASE_EQ; case_eq "oracle_result"; o_DEF]);;

(* HOL4: by do_app_cases, thunk_op_def, AllCaseEqs() and store_alloc_def *)
let EVALAUX_DO_APP_CASES_TAC =
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `s:(v store_v) list # (A)ffi_state` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:(v store_v) list`
               (X_CHOOSE_THEN `t0:(A)ffi_state` SUBST1_TAC)) THEN
  REWRITE_TAC[do_app_cases] THEN
  RW[] THEN GVS([thunk_op_def; store_alloc_def; sum_case_eq; case_eq "ffi_result";
                 case_eq "thunk_op"; case_eq "thunk_mode"] @ EVALAUX_do_app_eqs);;
let do_app_not_timeout = prove
 (`!(s:(v store_v) list # (A)ffi_state) op vs s' a.
     do_app s op vs = SOME (s',Rerr (Rabort a)) ==> ~(a = Rtimeout_error)`,
  EVALAUX_DO_APP_CASES_TAC);;
let do_app_type_error = prove
 (`!(s:(v store_v) list # (A)ffi_state) op es x a.
     do_app s op es = SOME (x,Rerr (Rabort a)) ==> x = s`,
  EVALAUX_DO_APP_CASES_TAC);;

(* HOL4 [local] *)
let build_rec_env_help_lem = prove
 (CASE_TERM
   `!(funs:(varN#varN#exp)list) env (funs':(varN#varN#exp)list)
     (env':(mlstring,mlstring,v)namespace).
      ITLIST (\fxe env'. match fxe with
                           (f,x,e) -> nsBind f (Recclosure env funs' f) env')
             funs env' =
      nsAppend (alist_to_ns (MAP (\fne. match fne with
                                          (f,n,e) -> (f,Recclosure env funs' f))
                                 funs)) env'`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ITLIST; MAP] THEN
  REWRITE_TAC[alist_to_ns_nil; nsAppend_nsEmpty] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `h:varN#varN#exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:varN` (X_CHOOSE_THEN `xe:varN#exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `xe:varN#exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:varN` (X_CHOOSE_THEN `e:exp` SUBST1_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE; alist_to_ns_cons; nsAppend_nsBind]);;

(* Alternate definition for build_rec_env *)
let build_rec_env_merge = prove
 (CASE_TERM
   `!funs (funs':(varN#varN#exp)list) env env'.
      build_rec_env funs env env' =
      nsAppend (alist_to_ns (MAP (\fne. match fne with
                                          (f,n,e) -> (f,Recclosure env funs f))
                                 funs)) env'`,
  REWRITE_TAC[build_rec_env_def; build_rec_env_help_lem]);;

let do_con_check_build_conv = prove
 (`!tenvC cn vs l. do_con_check tenvC cn l ==> ?v. build_conv tenvC cn vs = SOME v`,
  RW[do_con_check_def; build_conv_def] THEN EVERY_CASE_TAC THEN FS[]);;

let map_error_result_def = cake_def
  `(map_error_result (f:A->B) (Rraise e) = Rraise (f e)) /\
   (map_error_result f (Rabort a) = Rabort a)`;;
let _ = cake_add_simps [map_error_result_def];;

let map_error_result_Rtype_error = prove
 (`!(f:A->B) e a. map_error_result f e = Rabort a <=> e = Rabort a`,
  REPEAT GEN_TAC THEN CASES_ON `e:(A)error_result` THEN SIMP[]);;
let _ = cake_add_simps [map_error_result_Rtype_error];;

let map_error_result_I = prove
 (`!e:(A)error_result. map_error_result I e = e`,
  GEN_TAC THEN CASES_ON `e:(A)error_result` THEN SIMP[]);;
let _ = cake_add_simps [map_error_result_I];;

let map_result_def = cake_def
  `(map_result (f1:A->C) (f2:B->D) (Rval v) = Rval (f1 v)) /\
   (map_result f1 f2 (Rerr e) = Rerr (map_error_result f2 e))`;;
let _ = cake_add_simps [map_result_def];;

let map_result_Rval = prove
 (`!(f1:A->C) (f2:B->D) e x.
     map_result f1 f2 e = Rval x <=> ?y. e = Rval y /\ x = f1 y`,
  REPEAT GEN_TAC THEN CASES_ON `e:(A,B)result` THEN SIMP[] THEN MESON_TAC[]);;
let _ = cake_add_simps [map_result_Rval];;

let map_result_Rerr = prove
 (`!(f1:A->C) (f2:B->D) e e'.
     map_result f1 f2 e = Rerr e' <=> ?a. e = Rerr a /\ map_error_result f2 a = e'`,
  REPEAT GEN_TAC THEN CASES_ON `e:(A,B)result` THEN SIMP[]);;
let _ = cake_add_simps [map_result_Rerr];;

let exc_rel_def = cake_def
  `(exc_rel (R:A->B->bool) (Rraise v1) (Rraise v2) <=> R v1 v2) /\
   (exc_rel _ (Rabort a1) (Rabort a2) <=> a1 = a2) /\
   (exc_rel _ _ _ <=> F)`;;
let _ = cake_add_simps [exc_rel_def];;

let exc_rel_raise1 = prove
 (`!R (v:A) (e:(B)error_result). exc_rel R (Rraise v) e <=> ?v'. e = Rraise v' /\ R v v'`,
  REPEAT GEN_TAC THEN CASES_ON `e:(B)error_result` THEN SIMP[]);;
let _ = cake_add_simps [exc_rel_raise1];;

let exc_rel_raise2 = prove
 (`!R (e:(A)error_result) (v:B). exc_rel R e (Rraise v) <=> ?v'. e = Rraise v' /\ R v' v`,
  REPEAT GEN_TAC THEN CASES_ON `e:(A)error_result` THEN SIMP[]);;
let _ = cake_add_simps [exc_rel_raise2];;

let exc_rel_type_error1 = prove
 (`!(R:A->B->bool) a e. exc_rel R (Rabort a) e <=> e = Rabort a`,
  REPEAT GEN_TAC THEN CASES_ON `e:(B)error_result` THEN SIMP[] THEN METIS_TAC[]);;
let _ = cake_add_simps [exc_rel_type_error1];;

let exc_rel_type_error2 = prove
 (`!(R:A->B->bool) e a. exc_rel R e (Rabort a) <=> e = Rabort a`,
  REPEAT GEN_TAC THEN CASES_ON `e:(A)error_result` THEN SIMP[] THEN METIS_TAC[]);;
let _ = cake_add_simps [exc_rel_type_error2];;

let exc_rel_refl = prove
 (`!R:A->A->bool. (!x. R x x) ==> !x. exc_rel R x x`,
  GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN CASES_ON `x:(A)error_result` THEN
  SIMP[]);;
let _ = cake_add_simps [exc_rel_refl];;

let exc_rel_trans = prove
 (`!R:A->A->bool. (!x y z. R x y /\ R y z ==> R x z)
     ==> (!x y z. exc_rel R x y /\ exc_rel R y z ==> exc_rel R x z)`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  CASES_ON `x:(A)error_result` THEN FS[] THEN RW[] THEN FS[] THEN ASM_MESON_TAC[]);;

let result_rel_def = cake_def
  `(result_rel (R1:A->B->bool) (_:C->D->bool) (Rval v1) (Rval v2) <=> R1 v1 v2) /\
   (result_rel _ R2 (Rerr e1) (Rerr e2) <=> exc_rel R2 e1 e2) /\
   (result_rel _ _ _ _ <=> F)`;;
let _ = cake_add_simps [result_rel_def];;

let result_rel_Rval = prove
 (`!(R1:A->B->bool) (R2:C->D->bool) v r.
     result_rel R1 R2 (Rval v) r <=> ?v'. r = Rval v' /\ R1 v v'`,
  REPEAT GEN_TAC THEN CASES_ON `r:(B,D)result` THEN SIMP[]);;
let _ = cake_add_simps [result_rel_Rval];;

let result_rel_Rerr1 = prove
 (`!(R1:A->B->bool) (R2:C->D->bool) e r.
     result_rel R1 R2 (Rerr e) r <=> ?e'. r = Rerr e' /\ exc_rel R2 e e'`,
  REPEAT GEN_TAC THEN CASES_ON `r:(B,D)result` THEN SIMP[]);;
let _ = cake_add_simps [result_rel_Rerr1];;

let result_rel_Rerr2 = prove
 (`!(R1:A->B->bool) (R2:C->D->bool) r e.
     result_rel R1 R2 r (Rerr e) <=> ?e'. r = Rerr e' /\ exc_rel R2 e' e`,
  REPEAT GEN_TAC THEN CASES_ON `r:(A,C)result` THEN SIMP[]);;
let _ = cake_add_simps [result_rel_Rerr2];;

let result_rel_refl = prove
 (`!(R1:A->A->bool) (R2:B->B->bool).
     (!x. R1 x x) /\ (!x. R2 x x) ==> !x. result_rel R1 R2 x x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN CASES_ON `x:(A,B)result` THEN
  SIMP[] THEN MATCH_MP_TAC exc_rel_refl THEN ASM_REWRITE_TAC[]);;
let _ = cake_add_simps [result_rel_refl];;

let result_rel_trans = prove
 (`!(R1:A->A->bool) (R2:B->B->bool).
     (!x y z. R1 x y /\ R1 y z ==> R1 x z) /\ (!x y z. R2 x y /\ R2 y z ==> R2 x z)
     ==> (!x y z. result_rel R1 R2 x y /\ result_rel R1 R2 y z
                  ==> result_rel R1 R2 x z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  CASES_ON `x:(A,B)result` THEN FS[] THEN RW[] THEN FS[] THEN
  ASM_MESON_TAC[exc_rel_trans]);;

let every_error_result_def = cake_def
  `(every_error_result (P:A->bool) (Rraise e) <=> P e) /\
   (every_error_result P (Rabort a) <=> T)`;;
let _ = cake_add_simps [every_error_result_def];;

let every_result_def = cake_def
  `(every_result (P1:A->bool) (P2:B->bool) (Rval v) <=> P1 v) /\
   (every_result P1 P2 (Rerr e) <=> every_error_result P2 e)`;;
let _ = cake_add_simps [every_result_def];;

let map_sv_def = cake_def
  `(map_sv (f:A->B) (Refv v) = Refv (f v)) /\
   (map_sv _ (W8array w) = W8array w) /\
   (map_sv f (Varray vs) = Varray (MAP f vs)) /\
   (map_sv f (Thunk m v) = Thunk m (f v))`;;
let _ = cake_add_simps [map_sv_def];;

let dest_Refv_def = cake_def
  `dest_Refv (Refv (v:A)) = v`;;
let _ = cake_add_simps [dest_Refv_def];;

let is_Refv_def = cake_def
  `(is_Refv (Refv (_:A)) <=> T) /\
   (is_Refv _ <=> F)`;;
let _ = cake_add_simps [is_Refv_def];;

let sv_every_def = cake_def
  `(sv_every (P:A->bool) (Refv v) <=> P v) /\
   (sv_every P (Varray vs) <=> ALL P vs) /\
   (sv_every P (Thunk m v) <=> P v) /\
   (sv_every P _ <=> T)`;;
let _ = cake_add_simps [sv_every_def];;

(* sem1aux_def: the kit's cake_def needs more than ten minutes for the 16   *)
(* completed clauses                                                         *)
let sv_rel_def = sem1aux_def
  `(sv_rel (R:A->B->bool) (Refv v1) (Refv v2) <=> R v1 v2) /\
   (sv_rel R (W8array w1) (W8array w2) <=> w1 = w2) /\
   (sv_rel R (Varray vs1) (Varray vs2) <=> ALL2 R vs1 vs2) /\
   (sv_rel R (Thunk m1 v1) (Thunk m2 v2) <=> m1 = m2 /\ R v1 v2) /\
   (sv_rel R _ _ <=> F)`;;
let _ = cake_add_simps [sv_rel_def];;

let sv_rel_refl = prove
 (`!R (x:(A)store_v). (!x. R x x) ==> sv_rel R x x`,
  GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN CASES_ON `x:(A)store_v` THEN
  SIMP[sv_rel_def] THEN MATCH_MP_TAC EVERY2_refl THEN ASM_REWRITE_TAC[]);;
let _ = cake_add_simps [sv_rel_refl];;

let sv_rel_trans = prove
 (`!R:A->A->bool. (!x y z. R x y /\ R y z ==> R x z)
     ==> !x y z. sv_rel R x y /\ sv_rel R y z ==> sv_rel R x z`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  CASES_ON `x:(A)store_v` THEN CASES_ON `y:(A)store_v` THEN
  CASES_ON `z:(A)store_v` THEN SIMP[sv_rel_def] THEN
  ASM_METIS_TAC[LIST_REL_trans]);;

let sv_rel_cases = prove
 (`!x y. sv_rel (R:A->B->bool) x y <=>
     (?v1 v2. x = Refv v1 /\ y = Refv v2 /\ R v1 v2) \/
     (?w. x = W8array w /\ y = W8array w) \/
     (?m v1 v2. x = Thunk m v1 /\ y = Thunk m v2 /\ R v1 v2) \/
     (?vs1 vs2. x = Varray vs1 /\ y = Varray vs2 /\ ALL2 R vs1 vs2)`,
  REPEAT GEN_TAC THEN CASES_ON `x:(A)store_v` THEN CASES_ON `y:(B)store_v` THEN
  SIMP[sv_rel_def] THEN METIS_TAC[]);;

let EVALAUX_EXISTS_store_v = prove
 (`!P. (?y:(A)store_v. P y) <=>
       (?a. P (Refv a)) \/ (?w. P (W8array w)) \/ (?l. P (Varray l)) \/
       (?m a. P (Thunk m a))`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:(A)store_v` MP_TAC) THEN
    STRUCT_CASES_TAC(ISPEC `y:(A)store_v` (cases "store_v")) THEN MESON_TAC[];
    MESON_TAC[]]);;

(* HOL4: sv_rel (R1 O R2) = sv_rel R1 O sv_rel R2 *)
let sv_rel_O = prove
 (`!(R1:B->C->bool) (R2:A->B->bool).
     sv_rel (\x z. ?y. R2 x y /\ R1 y z) = (\x z. ?y. sv_rel R2 x y /\ sv_rel R1 y z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:(A)store_v`; `z:(C)store_v`] THEN
  REWRITE_TAC[EVALAUX_EXISTS_store_v] THEN
  CASES_ON `x:(A)store_v` THEN CASES_ON `z:(C)store_v` THEN
  REWRITE_TAC[sv_rel_def; LIST_REL_O] THEN MESON_TAC[]);;

let sv_rel_mono = prove
 (`!P Q x y. (!x y. P x y ==> Q x y)
             ==> sv_rel P x y ==> sv_rel Q (x:(A)store_v) (y:(B)store_v)`,
  REWRITE_TAC[sv_rel_cases] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[LIST_REL_mono]);;

let store_v_vs_def = cake_def
  `(store_v_vs (Refv (v:A)) = [v]) /\
   (store_v_vs (Varray vs) = vs) /\
   (store_v_vs (W8array _) = []) /\
   (store_v_vs (Thunk _ v) = [v])`;;
let _ = cake_add_simps [store_v_vs_def];;

let store_vs_def = cake_def
  `store_vs (s:(A store_v) list) = FLAT (MAP store_v_vs s)`;;

let EVERY_sv_every_MAP_map_sv = prove
 (`!P (f:A->B) ls. ALL P (MAP f (store_vs ls)) ==> ALL (sv_every P) (MAP (map_sv f) ls)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[store_vs_def; MAP; FLAT; ALL; MAP_APPEND; ALL_APPEND] THEN
  REPEAT STRIP_TAC THENL
   [CASES_ON `h:(A)store_v` THEN FS[];
    RULE_ASSUM_TAC(REWRITE_RULE[store_vs_def]) THEN ASM_MESON_TAC[]]);;

let LIST_REL_store_vs_intro = prove
 (`!P l1 l2. ALL2 (sv_rel (P:A->B->bool)) l1 l2 ==> ALL2 P (store_vs l1) (store_vs l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; store_vs_def; MAP; FLAT] THEN STRIP_TAC THEN
  MATCH_MP_TAC EVERY2_APPEND_suff THEN CONJ_TAC THENL
   [UNDISCH_TAC `sv_rel (P:A->B->bool) h h'` THEN
    REWRITE_TAC[sv_rel_cases] THEN STRIP_TAC THEN ASM_REWRITE_TAC[store_v_vs_def; ALL2];
    RULE_ASSUM_TAC(REWRITE_RULE[store_vs_def]) THEN ASM_MESON_TAC[]]);;

let EVERY_sv_every_EVERY_store_vs = prove
 (`!P ls. ALL (sv_every (P:A->bool)) ls <=> ALL P (store_vs ls)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[store_vs_def; MAP; FLAT; ALL; ALL_APPEND] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[store_vs_def]) THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `h:(A)store_v` THEN SIMP[]);;

let EVERY_store_vs_intro = prove
 (`!P ls. ALL (sv_every (P:A->bool)) ls ==> ALL P (store_vs ls)`,
  REWRITE_TAC[EVERY_sv_every_EVERY_store_vs]);;

let map_sv_compose = prove
 (`!(f:B->C) (g:A->B) x. map_sv f (map_sv g x) = map_sv (f o g) x`,
  REPEAT GEN_TAC THEN CASES_ON `x:(A)store_v` THEN SIMP[MAP_o; o_THM]);;

let map_match_def = cake_def
  `(map_match (f:A->A) (Match env) = Match (f env)) /\
   (map_match f x = x)`;;
let _ = cake_add_simps [map_match_def];;

let find_recfun_ALOOKUP = prove
 (`!funs (n:mlstring). find_recfun n funs = ALOOKUP funs n:(A#B)option`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[find_recfun_def] THEN
  REWRITE_TAC[ALOOKUP_THM; list_CASE] THEN GEN_TAC THEN
  MP_TAC(ISPEC `h:mlstring#A#B` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:mlstring` (X_CHOOSE_THEN `xe:A#B` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `xe:A#B` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` (X_CHOOSE_THEN `e:B` SUBST1_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE; ALOOKUP_THM] THEN MESON_TAC[]);;

let EVALAUX_MAP_FST3 = prove
 (CASE_TERM `!l:(A#B#C)list. MAP (\fxe. match fxe with (f,x,e) -> f) l = MAP FST l`,
  GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; pair_CASE; FST]);;

let find_recfun_el = prove
 (CASE_TERM `!f (funs:(mlstring#A#B)list) x e n.
    ALL_DISTINCT (MAP (\fxe. match fxe with (f,x,e) -> f) funs) /\
    n < LENGTH funs /\ EL n funs = (f,x,e)
    ==> find_recfun f funs = SOME (x,e)`,
  REWRITE_TAC[EVALAUX_MAP_FST3; find_recfun_ALOOKUP] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN ASM_MESON_TAC[MEM_EL]);;

let ctors_of_tdef_def = cake_def
  `ctors_of_tdef ((_:A),(_:B),(condefs:(C#D)list)) = MAP FST condefs`;;
let _ = cake_add_simps [ctors_of_tdef_def];;

let ctors_of_dec_def = sem1aux_def
  `(ctors_of_dec (Dtype locs tds) = FLAT (MAP ctors_of_tdef tds)) /\
   (ctors_of_dec (Dexn locs s _) = [s]) /\
   (ctors_of_dec _ = [])`;;
let _ = cake_add_simps [ctors_of_dec_def];;

(* free vars; HOL4's left associative UNION and DIFF are parenthesised      *)
let FV_def = sem1aux_def
  `(FV (Raise e) = FV e) /\
   (FV (Handle e pes) = FV e UNION FV_pes pes) /\
   (FV (Lit _) = {}) /\
   (FV (Con _ ls) = FV_list ls) /\
   (FV (Var id) = {id}) /\
   (FV (Fun x e) = FV e DIFF {Short x}) /\
   (FV (App _ es) = FV_list es) /\
   (FV (Log _ e1 e2) = FV e1 UNION FV e2) /\
   (FV (If e1 e2 e3) = (FV e1 UNION FV e2) UNION FV e3) /\
   (FV (Mat e pes) = FV e UNION FV_pes pes) /\
   (FV (Let xo e b) =
      FV e UNION (FV b DIFF (match xo with NONE -> {} | SOME x -> {Short x}))) /\
   (FV (Letrec defs b) =
      (FV_defs defs UNION FV b) DIFF set_of_list (MAP (Short o FST) defs)) /\
   (FV (Tannot e t) = FV e) /\
   (FV (Lannot e l) = FV e) /\
   (FV_list [] = {}) /\
   (FV_list (CONS e es) = FV e UNION FV_list es) /\
   (FV_pes [] = {}) /\
   (FV_pes (CONS (p,e) pes) =
      (FV e DIFF (IMAGE Short (set_of_list (pat_bindings p)))) UNION FV_pes pes) /\
   (FV_defs [] = {}) /\
   (FV_defs (CONS (_,x,e) defs) = (FV e DIFF {Short x}) UNION FV_defs defs)`;;
let _ = cake_add_simps [FV_def];;

(* HOL4: Overload SFV (an abbreviation, see the header)                     *)

let FV_pes_MAP = prove
 (CASE_TERM `!pes. FV_pes pes =
    UNIONS (IMAGE (\pe. match pe with
                          (p,e) -> FV e DIFF (IMAGE Short (set_of_list (pat_bindings p))))
                  (set_of_list pes))`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FV_def; set_of_list; IMAGE_CLAUSES; UNIONS_0;
                                       UNIONS_INSERT] THEN
  MP_TAC(ISPEC `h:pat#exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:pat` (X_CHOOSE_THEN `e:exp` SUBST1_TAC)) THEN
  ASM_REWRITE_TAC[FV_def; pair_CASE]);;

let FV_defs_MAP = prove
 (CASE_TERM `!ls. FV_defs ls =
    UNIONS (IMAGE (\fxe. match fxe with (f,x,e) -> FV e DIFF {Short x})
                  (set_of_list ls))`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FV_def; set_of_list; IMAGE_CLAUSES; UNIONS_0;
                                       UNIONS_INSERT] THEN
  MP_TAC(ISPEC `h:varN#varN#exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:varN` (X_CHOOSE_THEN `xe:varN#exp` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `xe:varN#exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:varN` (X_CHOOSE_THEN `e:exp` SUBST1_TAC)) THEN
  ASM_REWRITE_TAC[FV_def; pair_CASE]);;

let FV_dec_def = sem1aux_def
  `(FV_dec (Dlet locs p e) = FV (Mat e [(p,Lit ARB)])) /\
   (FV_dec (Dletrec locs defs) = FV (Letrec defs (Lit ARB))) /\
   (FV_dec (Dtype _ _) = {}) /\
   (FV_dec (Dtabbrev _ _ _ _) = {}) /\
   (FV_dec (Dexn _ _ _) = {})`;;
let _ = cake_add_simps [FV_dec_def];;

let nat_to_v_11 = prove
 (`!i j. nat_to_v i = nat_to_v j <=> i = j`,
  SIMP[nat_to_v_def; INT_OF_NUM_EQ]);;
let _ = cake_add_simps [nat_to_v_11];;

let concrete_v_list = prove
 (`!xs. concrete_v_list xs <=> ALL concrete_v xs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[concrete_v_def; ALL]);;
let _ = cake_add_simps [concrete_v_list];;

let concrete_v_simps = prove
 (`(!l. concrete_v (Litv l) <=> T) /\
   (!b n. concrete_v (Loc b n) <=> T) /\
   (!stmp xs. concrete_v (Conv stmp xs) <=> ALL concrete_v xs) /\
   (!xs. concrete_v (Vectorv xs) <=> ALL concrete_v xs) /\
   (!id e. concrete_v (Env id e) <=> F) /\
   (!e2 nm x. concrete_v (Closure e2 nm x) <=> F) /\
   (!e3 funs nm2. concrete_v (Recclosure e3 funs nm2) <=> F)`,
  REWRITE_TAC[concrete_v_list] THEN ONCE_REWRITE_TAC[concrete_v_def] THEN
  CAKE_REWRITE_TAC[concrete_v_list]);;
let _ = cake_add_simps [concrete_v_simps];;

let prim_type_cases = prove
 (`!ty. ty = BoolT \/ ty = IntT \/ ty = CharT \/ ty = StrT \/
        ty = WordT W8 \/ ty = WordT W64 \/ ty = Float64T`,
  GEN_TAC THEN CASES_ON `ty:prim_type` THEN SIMP[] THEN
  MESON_TAC[cases "word_size"]);;
let do_conversion_check_type = prove
 (`!v ty1 ty2 res. do_conversion v ty1 ty2 = SOME (INR res) ==> check_type ty2 res`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `ty2:prim_type` prim_type_cases) THEN
  STRUCT_CASES_TAC(SPEC `ty1:prim_type` prim_type_cases) THEN
  REWRITE_TAC[do_conversion_def] THEN GVS[COND_CASE_EQ] THEN
  RW[check_type_def]);;

let do_arith_check_type = prove
 (`!a ty vs res. do_arith a ty vs = SOME (INR res) ==> check_type ty res`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `ty:prim_type` prim_type_cases) THEN
  REWRITE_TAC[do_arith_def] THEN
  GVS([COND_CASE_EQ; pair_case_eq; option_case_eq; list_case_eq; sum_case_eq] @
      map case_eq ["arith"]) THEN
  RW[check_type_def] THEN MESON_TAC[]);;
