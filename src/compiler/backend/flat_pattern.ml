(* ========================================================================= *)
(* flat_pattern: port of HOL4 compiler/backend/flat_patternScript.sml        *)
(* (CakeML v3479).                                                           *)
(* Interface between flatLang and the pattern compiler:                      *)
(* - ensures every case match is on a variable                               *)
(* - sends case matches to the pattern compiler to get a decision tree       *)
(* - decodes the decision tree to an if-tree                                 *)
(* - encodes the variable bindings of each case as let-bindings              *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's flatLang$pat1_size (the size of a pattern list) is              *)
(*   list_size flat_pat_size; HOL4 FOLDR f e l is ITLIST f l e, EXISTS is   *)
(*   EX, () is one, #"." is CHR 46, the mlstring literal of decode_dtree is *)
(*   implode "impossible-case", and pattern_comp$comp is pattern_comp_comp. *)
(* - A clause variable whose name HOL4 uses with two types in one           *)
(*   definition gets a second name: the names of Fun and Letrec (fnm, lnm), *)
(*   the variable option of Let (vo), the variable of Pas in                *)
(*   naive_pattern_match (nm); the k bound inside the lambda of             *)
(*   compile_pat_bindings is kk; HOL4 wildcards in lambdas are named.       *)
(* - In the Letrec clause of compile_exp the MAP over the functions is      *)
(*   written \fn. match fn with (a,b,c) -> ..., so that the recursion gets  *)
(*   the context MEM fn fs (HOL4's MAP congruence rule).                    *)
(* - simp_guard_ind is HOL4's induction theorem (the structural one: the    *)
(*   recursive calls are in let-bound expressions), proved by dGuard        *)
(*   induction.                                                              *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/flatLang.ml";;
needs "hol4/sptree.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/pattern_matching/pattern_comp.ml";;
needs "semantics/sem1aux_tfl.ml";;
needs "compiler/backend/il1aux_mutual.ml";;

type_invention_error := true;;

let flat_pattern_config_INFO = cake_record "flat_pattern_config"
  ["pat_heuristic","num"];;

let flat_pattern_init_config_def = cake_def
  `flat_pattern_init_config ph = flat_pattern_config_REC ph`;;

let sum_string_ords_def = cake_def_wf
  `MEASURE (\p:num # mlstring. strlen (SND p) - FST p)`
  (REPEAT STRIP_TAC THEN REWRITE_TAC(WF_REL_THMS @ [FST; SND]) THEN
   ASM_ARITH_TAC)
  `sum_string_ords i str =
     if i < strlen str
     then (ORD (strsub str i) - 35) + sum_string_ords (i + 1) str
     else 0`;;

let sum_string_ords_ind = cake_ind "sum_string_ords";;

let dec_name_to_num_def = cake_def
  `dec_name_to_num name =
     if strlen name < 2 then 0
     else if strsub name 0 = CHR 46 /\ strsub name 1 = CHR 46
     then sum_string_ords 2 name else 0`;;

let enc_num_to_name_aux_def = cake_def_wf
  `MEASURE (FST:num # char list -> num)`
  (REWRITE_TAC(WF_REL_THMS @ [FST; SND]) THEN REPEAT STRIP_TAC THEN
   ASM_ARITH_TAC)
  `enc_num_to_name_aux i xs =
     if i < 90 then CONS (CHR 46) (CONS (CHR 46) (CONS (CHR (i + 35)) xs))
     else enc_num_to_name_aux (i - 90) (CONS (CHR 125) xs)`;;

let enc_num_to_name_def = cake_def
  `enc_num_to_name i = implode (enc_num_to_name_aux i [])`;;

(* HOL4 flatLang$pat1_size is list_size flat_pat_size *)

let pat1_size = prove
 (`!xs. list_size flat_pat_size xs = LENGTH xs + SUM (MAP flat_pat_size xs)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[list_size; LENGTH; MAP; SUM] THEN
  ARITH_TAC);;

let MAPi_eq_MAP = prove
 (`MAPi (\n x. (f:A->B) x) xs = MAP f xs`,
  REWRITE_TAC[MAPi_EQ_MAP]);;

(* the termination of compile_pat_bindings: the patterns of the arguments  *)
(* of a constructor pattern, numbered by enumerate, are the arguments       *)

let IL1AUX_MAP_ENUM_FST = prove
 (`!(f:num # flat_pat -> (num # mlstring) # flat_pat # num # flat_exp) ps n.
     (!j p. FST (SND (f (j,p))) = p) ==>
     MAP (flat_pat_size o FST) (MAP SND (MAP f (enumerate n ps))) =
     MAP flat_pat_size ps`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[enumerate_def; MAP; o_THM]);;

let IL1AUX_PATB_TC_TAC : tactic =
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN REWRITE_TAC(WF_REL_THMS @ [FST; SND]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[MAP_APPEND; SUM_APPEND; LENGTH_APPEND; LENGTH_MAP;
              LENGTH_enumerate; MAP; SUM; LENGTH; o_THM; FST; SND] THEN
  REPEAT (fun (asl,w as g) ->
     let is_enum_map t =
       try let h,args = strip_comb t in
           fst(dest_const h) = "MAP" && length args = 2 &&
           (let h2,_ = strip_comb (el 1 args) in fst(dest_const h2) = "enumerate")
       with Failure _ -> false in
     match (try Some(find_term is_enum_map w) with Failure _ -> None) with
       None -> failwith "IL1AUX_PATB_TC_TAC"
     | Some tm ->
         let f = rand(rator tm) in
         let _,eargs = strip_comb (rand tm) in
         let n = hd eargs and ps = el 1 eargs in
         (MP_TAC (ISPECL [f; ps; n] IL1AUX_MAP_ENUM_FST) THEN
          ANTS_TAC THENL
           [REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
            REWRITE_TAC[FST; SND; LET_DEF; LET_END_DEF];
            DISCH_THEN SUBST1_TAC]) g) THEN
  REWRITE_TAC[type_size_def "flat_pat"] THEN
  REWRITE_TAC(size_aux_eqs "flat_pat") THEN REWRITE_TAC[pat1_size] THEN
  ARITH_TAC;;

let compile_pat_bindings_def = cake_def_wf
  `MEASURE (\x:tra # num # (flat_pat # num # flat_exp) list # flat_exp.
              SUM (MAP (flat_pat_size o FST) (FST (SND (SND x)))) +
              LENGTH (FST (SND (SND x))))`
  IL1AUX_PATB_TC_TAC
  `(compile_pat_bindings _ _ [] exp = (LN:num_set, exp)) /\
   (compile_pat_bindings t i (CONS (flat_Pany, _, _) m) exp =
      compile_pat_bindings t i m exp) /\
   (compile_pat_bindings t i (CONS (flat_Pvar s, k, x) m) exp =
      let (spt, exp2) = compile_pat_bindings t i m exp in
      (insert k one spt, flat_Let t (SOME s) x exp2)) /\
   (compile_pat_bindings t i (CONS (flat_Plit _, _, _) m) exp =
      compile_pat_bindings t i m exp) /\
   (compile_pat_bindings t i (CONS (flat_Pcon _ ps, k, x) m) exp =
      let j_nms = MAP (\(j, p). let kk = i + 1 + j in
                                let nm = enc_num_to_name kk in
                                ((j, nm), (p, kk, Var_local t nm)))
                      (enumerate 0 ps) in
      let (spt, exp2) = compile_pat_bindings t (i + 2 + LENGTH ps)
                          (APPEND (MAP SND j_nms) m) exp in
      let j_nms_used = FILTER (\(jn, (q, kk, e)). IS_SOME (lookup kk spt)) j_nms in
      let exp3 = ITLIST (\((j, nm), r) exp.
                           flat_Let t (SOME nm) (flat_App t (flat_El j) [x]) exp)
                        j_nms_used exp2 in
      let spt2 = if NULL j_nms_used then spt else insert k one spt in
      (spt2, exp3)) /\
   (compile_pat_bindings t i (CONS (flat_Pas p v, k, x) m) exp =
      let nm = enc_num_to_name (i + 1) in
      let (spt, exp2) = compile_pat_bindings t (i + 2)
                          (CONS (p, i + 1, Var_local t nm) m) exp in
      (insert k one spt, flat_Let t (SOME v) x
                           (flat_Let t (SOME nm) (Var_local t v) exp2))) /\
   (compile_pat_bindings t i (CONS (flat_Pref p, k, x) m) exp =
      let nm = enc_num_to_name (i + 1) in
      let (spt, exp2) = compile_pat_bindings t (i + 2)
                          (CONS (p, i + 1, Var_local t nm) m) exp in
      (insert k one spt, flat_Let t (SOME nm) (flat_App t (flat_El 0) [x]) exp2))`;;

let compile_pat_bindings_ind = cake_ind "compile_pat_bindings";;

let compile_pat_rhs_def = cake_def
  `compile_pat_rhs t i v (p, exp) =
     SND (compile_pat_bindings t (i + 1) [(p, i, v)] exp)`;;

let decode_pos_def = cake_def
  `(decode_pos t v EmptyPos = v) /\
   (decode_pos t v (Pos i pos) = decode_pos t (flat_App t (flat_El i) [v]) pos)`;;

let flat_pattern_decode_test_def = cake_def
  `(flat_pattern_decode_test t (pattern_semantics_TagLenEq tag l) v =
      flat_App t (flat_TagLenEq tag l) [v]) /\
   (flat_pattern_decode_test t (LitEq lit) v =
      flat_App t (Src Equality) [v; flat_Lit t lit])`;;

let simp_guard_def = cake_def
  `(simp_guard (Conj x y) =
      let v = simp_guard x in
      let w = simp_guard y in
      if v = pattern_semantics_Not True \/ w = pattern_semantics_Not True then
        pattern_semantics_Not True
      else if v = True then w
      else if w = True then v
      else Conj v w) /\
   (simp_guard (Disj x y) =
      let v = simp_guard x in
      let w = simp_guard y in
      if v = True \/ w = True then True
      else if v = pattern_semantics_Not True then w
      else if w = pattern_semantics_Not True then v
      else Disj v w) /\
   (simp_guard (pattern_semantics_Not x) =
      let v = simp_guard x in
      match v with
        pattern_semantics_Not True -> True
      | pattern_semantics_Not w -> w
      | _ -> pattern_semantics_Not v) /\
   (simp_guard x = x)`;;

let simp_guard_ind = prove
 (`!P. (!x y. P x /\ P y ==> P (Conj x y)) /\
       (!x y. P x /\ P y ==> P (Disj x y)) /\
       (!x. P x ==> P (pattern_semantics_Not x)) /\
       (!v0 v1. P (PosTest v0 v1)) /\ P True
       ==> !v. P v`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC dGuard_INDUCT THEN
  ASM_SIMP_TAC[]);;

let decode_guard_def = cake_def
  `(decode_guard t v (pattern_semantics_Not gd) =
      flat_App t (Src Equality) [decode_guard t v gd; flat_Bool t F]) /\
   (decode_guard t v (Conj gd1 gd2) =
      SmartIf t (decode_guard t v gd1) (decode_guard t v gd2) (flat_Bool t F)) /\
   (decode_guard t v (Disj gd1 gd2) =
      SmartIf t (decode_guard t v gd1) (flat_Bool t T) (decode_guard t v gd2)) /\
   (decode_guard t v True = flat_Bool t T) /\
   (decode_guard t v (PosTest pos test) =
      flat_pattern_decode_test t test (decode_pos t v pos))`;;

let decode_dtree_def = cake_def
  `(decode_dtree t br_spt v df (pattern_semantics_Leaf n) =
      match lookup n br_spt with
        SOME br -> br
      | NONE -> df) /\
   (decode_dtree t br_spt v df pattern_semantics_Fail = df) /\
   (decode_dtree t br_spt v df TypeFail =
      Var_local t (implode "impossible-case")) /\
   (decode_dtree t br_spt v df (pattern_semantics_If guard dt1 dt2) =
      let guard = simp_guard guard in
      let dec1 = decode_dtree t br_spt v df dt1 in
      let dec2 = decode_dtree t br_spt v df dt2 in
      if guard = True then dec1
      else if guard = pattern_semantics_Not True then dec2
      else SmartIf t (decode_guard t v guard) dec1 dec2)`;;

let encode_pat_def = sem1aux_def_wf
  `MEASURE flat_pat_size`
  SEM1AUX_TC_TAC
  `(encode_pat flat_Pany = pattern_semantics_Any) /\
   (encode_pat (flat_Plit l) = pattern_semantics_Lit l) /\
   (encode_pat (flat_Pvar _) = pattern_semantics_Any) /\
   (encode_pat (flat_Pcon stmp ps) =
      pattern_semantics_Cons
        (match stmp with
           NONE -> NONE
         | SOME (i, NONE) -> SOME (i, NONE)
         | SOME (i, SOME (ty, ctors)) -> SOME (i, SOME ctors))
        (MAP encode_pat ps)) /\
   (encode_pat (flat_Pas p v) = encode_pat p) /\
   (encode_pat (flat_Pref p) = pattern_semantics_Ref (encode_pat p))`;;

let encode_pat_ind = cake_ind "encode_pat";;

(* the termination of naive_pattern_match: MAPi keeps the patterns *)

let IL1AUX_MAPi_FST = prove
 (`!(f:num->flat_pat->flat_pat # flat_exp) ps.
     (!i p. FST (f i p) = p) ==>
     MAP (flat_pat_size o FST) (MAPi f ps) = MAP flat_pat_size ps`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAPi_DEF; MAP; o_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[CONS_11] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[o_THM]);;

let IL1AUX_NAIVE_TC_TAC : tactic =
  REWRITE_TAC(WF_REL_THMS @ [FST; SND]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[MAP_APPEND; SUM_APPEND; LENGTH_APPEND; LENGTH_MAP; LENGTH_MAPi;
              MAP; SUM; LENGTH; o_THM; FST; SND] THEN
  REPEAT (fun (asl,w as g) ->
     let is_mapi_map t =
       try let h,args = strip_comb t in
           fst(dest_const h) = "MAP" && length args = 2 &&
           (let h2,_ = strip_comb (el 1 args) in fst(dest_const h2) = "MAPi")
       with Failure _ -> false in
     match (try Some(find_term is_mapi_map w) with Failure _ -> None) with
       None -> failwith "IL1AUX_NAIVE_TC_TAC"
     | Some tm ->
         let _,margs = strip_comb (rand tm) in
         let f = hd margs and ps = el 1 margs in
         (MP_TAC (ISPECL [f; ps] IL1AUX_MAPi_FST) THEN
          ANTS_TAC THENL
           [REPEAT GEN_TAC THEN REWRITE_TAC[FST]; DISCH_THEN SUBST1_TAC]) g) THEN
  REWRITE_TAC[type_size_def "flat_pat"] THEN
  REWRITE_TAC(size_aux_eqs "flat_pat") THEN REWRITE_TAC[pat1_size] THEN
  ARITH_TAC;;

let naive_pattern_match_def = cake_def_wf
  `MEASURE (\x:tra # (flat_pat # flat_exp) list.
              SUM (MAP (flat_pat_size o FST) (SND x)) + LENGTH (SND x))`
  IL1AUX_NAIVE_TC_TAC
  `(naive_pattern_match t [] = flat_Bool t T) /\
   (naive_pattern_match t (CONS (flat_Pany, _) mats) = naive_pattern_match t mats) /\
   (naive_pattern_match t (CONS (flat_Pvar _, _) mats) =
      naive_pattern_match t mats) /\
   (naive_pattern_match t (CONS (flat_Plit l, v) mats) =
      SmartIf t (flat_App t (Src Equality) [v; flat_Lit t l])
        (naive_pattern_match t mats) (flat_Bool t F)) /\
   (naive_pattern_match t (CONS (flat_Pcon NONE ps, v) mats) =
      naive_pattern_match t
        (APPEND (MAPi (\i p. (p, flat_App t (flat_El i) [v])) ps) mats)) /\
   (naive_pattern_match t (CONS (flat_Pas p nm, v) mats) =
      naive_pattern_match t (CONS (p, v) mats)) /\
   (naive_pattern_match t (CONS (flat_Pcon (SOME stmp) ps, v) mats) =
      SmartIf t (flat_App t (flat_TagLenEq (FST stmp) (LENGTH ps)) [v])
        (naive_pattern_match t
           (APPEND (MAPi (\i p. (p, flat_App t (flat_El i) [v])) ps) mats))
        (flat_Bool t F)) /\
   (naive_pattern_match t (CONS (flat_Pref p, v) mats) =
      naive_pattern_match t (CONS (p, flat_App t (flat_El 0) [v]) mats))`;;

let naive_pattern_match_ind = cake_ind "naive_pattern_match";;

let naive_pattern_matches_def = cake_def
  `(naive_pattern_matches t v [] dflt_x = dflt_x) /\
   (naive_pattern_matches t v (CONS (p, x) ps) dflt_x =
      SmartIf t (naive_pattern_match t [(p, v)]) x
        (naive_pattern_matches t v ps dflt_x))`;;

let naive_pattern_matches_ind = cake_ind "naive_pattern_matches";;

let compile_pats_def = cake_def
  `compile_pats (cfg:flat_pattern_config) naive t i v default_x ps =
     let branches = MAP (compile_pat_rhs t i v) ps in
     if naive then
       naive_pattern_matches t v (ZIP (MAP FST ps) branches) default_x
     else
       let pats = MAPi (\j (p, q). (encode_pat p, j)) ps in
       let dt = pattern_comp_comp pats in
       decode_dtree t (fromList branches) v default_x dt`;;

let max_dec_name_def = cake_def
  `(max_dec_name [] = 0) /\
   (max_dec_name (CONS nm nms) = MAX (dec_name_to_num nm) (max_dec_name nms))`;;

let op_sets_globals_def = cake_def
  `(op_sets_globals (GlobalVarInit n) <=> T) /\
   (op_sets_globals (_:flat_op) <=> F)`;;

let op_sets_globals_EX = prove
 (`op_sets_globals op <=> (?n. op = GlobalVarInit n)`,
  STRUCT_CASES_TAC (ISPEC `op:flat_op` (nchotomy_of_type `:flat_op`)) THEN
  REWRITE_TAC[op_sets_globals_def; distinctness "flat_op"; injectivity "flat_op"] THEN
  MESON_TAC[]);;

let IL1AUX_FPC_TC_TAC : tactic =
  SEM1AUX_TC_TAC ORELSE
  (REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
   RVEQ_TAC THEN
   REPEAT (FIRST_X_ASSUM (K ALL_TAC o check (fun th ->
     is_neg (concl th) && is_exists (dest_neg (concl th))))) THEN
   REWRITE_TAC(WF_REL_THMS @ [FST; SND; sum_CASE; exp6_size_REVERSE]) THEN
   TERM_TAC);;

let flat_pattern_compile_exp_def = sem1aux_def_wf
  `MEASURE (\x:(flat_pattern_config # flat_exp) +
               (flat_pattern_config # flat_exp list) +
               (flat_pattern_config # (flat_pat # flat_exp) list).
     sum_CASE x (\p. flat_exp_size (SND p))
       (\y. sum_CASE y (\p. list_size flat_exp_size (SND p))
              (\p. list_size (pair_size flat_pat_size flat_exp_size) (SND p))))`
  IL1AUX_FPC_TC_TAC
  `(flat_pattern_compile_exp cfg (Var_local t vid) =
      (dec_name_to_num vid, F, Var_local t vid)) /\
   (flat_pattern_compile_exp cfg (flat_Raise t x) =
      let (i, sg, y) = flat_pattern_compile_exp cfg x in
      (i, sg, flat_Raise t y)) /\
   (flat_pattern_compile_exp cfg (flat_Handle t x ps) =
      let (i, sgx, y) = flat_pattern_compile_exp cfg x in
      let (j, sgp, ps2) = compile_match cfg ps in
      let k = MAX i j + 2 in
      let nm = enc_num_to_name k in
      let v = Var_local t nm in
      let r = flat_Raise t v in
      let exp = compile_pats cfg sgp t k v r ps2 in
      (k, (sgx \/ sgp), flat_Handle t y [(flat_Pvar nm, exp)])) /\
   (flat_pattern_compile_exp cfg (flat_Con t ts xs) =
      let (i, sg, ys) = flat_pattern_compile_exps cfg (REVERSE xs) in
      (i, sg, flat_Con t ts (REVERSE ys))) /\
   (flat_pattern_compile_exp cfg (flat_Fun fnm vs x) =
      let (i, sg, y) = flat_pattern_compile_exp cfg x in
      (i, sg, flat_Fun fnm vs y)) /\
   (flat_pattern_compile_exp cfg (flat_App t op xs) =
      let (i, sg, ys) = flat_pattern_compile_exps cfg (REVERSE xs) in
      (i, (sg \/ op_sets_globals op), flat_App t op (REVERSE ys))) /\
   (flat_pattern_compile_exp cfg (flat_Mat t x ps) =
      let (i, sgx, y) = flat_pattern_compile_exp cfg x in
      let (j, sgp, ps2) = compile_match cfg ps in
      let k = MAX i j + 2 in
      let nm = enc_num_to_name k in
      let v = Var_local t nm in
      let r = flat_Raise t (flat_Con t (SOME (bind_tag, NONE)) []) in
      let exp = compile_pats cfg sgp t k v r ps2 in
      (k, (sgx \/ sgp), flat_Let t (SOME nm) y exp)) /\
   (flat_pattern_compile_exp cfg (flat_Let t vo x1 x2) =
      let (i, sg1, y1) = flat_pattern_compile_exp cfg x1 in
      let (j, sg2, y2) = flat_pattern_compile_exp cfg x2 in
      let k = (match vo with NONE -> 0 | SOME vid -> dec_name_to_num vid) in
      (MAX i (MAX j k), (sg1 \/ sg2), flat_Let t vo y1 y2)) /\
   (flat_pattern_compile_exp cfg (flat_Letrec lnm fs x) =
      let ys = MAP (\fn. match fn with
                           (a,b,c) -> (a, b, flat_pattern_compile_exp cfg c)) fs in
      let (i, sgx, y) = flat_pattern_compile_exp cfg x in
      let j = MAX_LIST (MAP (\(a,b,(j,sg,e)). j) ys) in
      let sgfs = EX (\(a,b,(j,sg,e)). sg) ys in
      let fs2 = MAP (\(a,b,(j,sg,e)). (a, b, e)) ys in
      (MAX i j, (sgfs \/ sgx), flat_Letrec lnm fs2 y)) /\
   (flat_pattern_compile_exp cfg (flat_If t x1 x2 x3) =
      let (i, sg1, y1) = flat_pattern_compile_exp cfg x1 in
      let (j, sg2, y2) = flat_pattern_compile_exp cfg x2 in
      let (k, sg3, y3) = flat_pattern_compile_exp cfg x3 in
      (MAX i (MAX j k), (sg1 \/ sg2 \/ sg3), SmartIf t y1 y2 y3)) /\
   (flat_pattern_compile_exp cfg exp = (0, F, exp)) /\
   (flat_pattern_compile_exps cfg [] = (0, F, [])) /\
   (flat_pattern_compile_exps cfg (CONS x xs) =
      let (i, sgx, y) = flat_pattern_compile_exp cfg x in
      let (j, sgy, ys) = flat_pattern_compile_exps cfg xs in
      (MAX i j, (sgx \/ sgy), CONS y ys)) /\
   (compile_match cfg [] = (0, F, [])) /\
   (compile_match cfg (CONS (p, x) ps) =
      let (i, sgx, y) = flat_pattern_compile_exp cfg x in
      let j = max_dec_name (flat_pat_bindings p) in
      let (k, sgp, ps2) = compile_match cfg ps in
      (MAX i (MAX j k), (sgx \/ sgp), CONS (p, y) ps2))`;;

let flat_pattern_compile_exp_ind = cake_ind "flat_pattern_compile_exp";;

let LENGTH_compile_exps_IMP = prove
 (`(!cfg x. let v = flat_pattern_compile_exp cfg x in T) /\
   (!cfg xs i sg ys. flat_pattern_compile_exps cfg xs = (i, sg, ys) ==>
                     LENGTH ys = LENGTH xs) /\
   (!cfg ps i sg ps2. compile_match cfg ps = (i, sg, ps2) ==>
                      LENGTH ps2 = LENGTH ps)`,
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONJ_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[flat_pattern_compile_exp_def; PAIR_EQ; LENGTH] THENL
   [MESON_TAC[LENGTH];
    REPEAT GEN_TAC THEN REPEAT IL1AUX_PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    MESON_TAC[LENGTH];
    SPEC_TAC(`h:flat_pat # flat_exp`,`h:flat_pat # flat_exp`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; flat_pattern_compile_exp_def] THEN
    REPEAT GEN_TAC THEN REPEAT IL1AUX_PAIRARG_TAC THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[LENGTH; SUC_INJ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let LENGTH_SND_compile_exps = prove
 (`LENGTH (SND (SND (flat_pattern_compile_exps cfg xs))) = LENGTH xs /\
   LENGTH (SND (SND (compile_match cfg ps))) = LENGTH ps`,
  CONJ_TAC THENL
   [MATCH_MP_TAC (CONJUNCT1 (CONJUNCT2 LENGTH_compile_exps_IMP)) THEN
    MAP_EVERY EXISTS_TAC
      [`cfg:flat_pattern_config`; `FST (flat_pattern_compile_exps cfg xs)`;
       `FST (SND (flat_pattern_compile_exps cfg xs))`];
    MATCH_MP_TAC (CONJUNCT2 (CONJUNCT2 LENGTH_compile_exps_IMP)) THEN
    MAP_EVERY EXISTS_TAC
      [`cfg:flat_pattern_config`; `FST (compile_match cfg ps)`;
       `FST (SND (compile_match cfg ps))`]] THEN
  REWRITE_TAC[PAIR]);;

let compile_dec_def = cake_def
  `compile_dec cfg exp = SND (SND (flat_pattern_compile_exp cfg exp))`;;
