(* ========================================================================= *)
(* clos_numberProof: port of HOL4 compiler/backend/proofs/                   *)
(* clos_numberProofScript.sml (CakeML v3479).                                *)
(* Correctness proof for clos_number.                                        *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_number.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/closProps.ml";;

type_invention_error := true;;

(* properties of renumber_code_locs *)

(* HOL4's tac (case-split the calls of renumber_code_locs on variables) is   *)
(* PAIRARG_TAC here                                                          *)

let renumber_code_locs_list_IMP_LENGTH = prove
 (`renumber_code_locs_list loc es = (l1,es2) ==> LENGTH es2 = LENGTH es`,
  MESON_TAC[SND; renumber_code_locs_length]);;

(* local tactics: the equations renumber_code_locs n e = (m,e') of the     *)
(* assumptions rewrite the others; contexts are unwound; arithmetic on the  *)
(* numeric assumptions only                                                 *)
let CLOSP1AUX_num_is_rcl_eq th =
  let c = concl th in
  is_eq c && (CLOSPROPSAUX_is_app "renumber_code_locs" (lhs c) ||
              CLOSPROPSAUX_is_app "renumber_code_locs_list" (lhs c)) &&
  is_pair (rhs c);;
(* rewrite the other assumptions with the equations renumber_code_locs n e = (m,e') *)
let CLOSP1AUX_NUM_EQS_TAC : tactic = fun (asl,w as gl) ->
  let eqs = filter CLOSP1AUX_num_is_rcl_eq (map snd asl) in
  (RULE_ASSUM_TAC(fun th -> if CLOSP1AUX_num_is_rcl_eq th then th
                            else REWRITE_RULE (eqs @ [FST; SND; PAIR_EQ]) th) THEN
   REWRITE_TAC (eqs @ [FST; SND; PAIR_EQ])) gl;;

(* unwind the equations c = x (x bound) in the antecedents of hypotheses *)
let CLOSP1AUX_NUM_UNWIND_TAC : tactic =
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV (CHANGED_CONV FORALL_UNWIND_CONV)));;

(* arithmetic with the numeric assumptions only *)
let CLOSP1AUX_NUM_ARITH_TAC : tactic = fun (asl,w as gl) ->
  let is_num_rel t =
    let t = if is_neg t then dest_neg t else t in
    (is_comb t && is_comb (rator t) &&
     (let h = rator (rator t) in
      is_const h && mem (fst (dest_const h)) ["<"; "<="; ">"; ">="] &&
      type_of (rand t) = `:num`)) ||
    (is_eq t && type_of (lhs t) = `:num`) in
  let ths = filter (fun th -> is_num_rel (concl th)) (map snd asl) in
  (MAP_EVERY MP_TAC ths THEN ARITH_TAC) gl;;

let CLOSP1AUX_NUM_NORM_TAC : tactic =
  CLOSP1AUX_NUM_UNWIND_TAC THEN CLOSP1AUX_NUM_EQS_TAC THEN
  CLOSP1AUX_NUM_UNWIND_TAC THEN CLOSP1AUX_NUM_EQS_TAC THEN
  CLOSP1AUX_NUM_UNWIND_TAC THEN CLOSP1AUX_NUM_EQS_TAC;;

let renumber_code_locs_inc = prove
 (`(!n es. n <= FST (renumber_code_locs_list n es)) /\
   (!n e. n <= FST (renumber_code_locs n e))`,
  MATCH_MP_TAC renumber_code_locs_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[renumber_code_locs_def] THEN REPEAT STRIP_TAC THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[FST; LE_REFL] THEN CLOSP1AUX_NUM_NORM_TAC THEN CLOSP1AUX_NUM_ARITH_TAC);;

let renumber_code_locs_imp_inc = prove
 (`(renumber_code_locs_list n es = (m,vs) ==> n <= m) /\
   (renumber_code_locs n e = (z,v) ==> n <= z)`,
  MESON_TAC[renumber_code_locs_inc; FST]);;

let renumber_code_locs_list_length = prove
 (`!ls n x y. renumber_code_locs_list n ls = (x,y) ==> LENGTH y = LENGTH ls`,
  MESON_TAC[renumber_code_locs_list_IMP_LENGTH]);;

let CLOSP1AUX_NUM_INC_TAC : tactic = fun (asl,w as gl) ->
  let inc th = try MATCH_MP (CONJUNCT1 renumber_code_locs_imp_inc) th
               with Failure _ -> MATCH_MP (CONJUNCT2 renumber_code_locs_imp_inc) th in
  MAP_EVERY ASSUME_TAC (mapfilter (fun (_,th) -> inc th) asl) gl;;
let CLOSP1AUX_NUM_LEN_TAC : tactic = fun (asl,w as gl) ->
  MAP_EVERY ASSUME_TAC
    (mapfilter (fun (_,th) -> SYM (REWRITE_RULE[LENGTH_MAP]
                  (MATCH_MP renumber_code_locs_list_length th))) asl) gl;;

(* local helpers: sorted lists of code locations within bounds *)
let CLOSP1AUX_num_SR_APPEND = prove
 (`!a b c l1 l2.
     (SORTED (<) l1 /\ ALL ((<=) a) l1 /\ ALL ((>) b) l1) /\
     (SORTED (<) l2 /\ ALL ((<=) b) l2 /\ ALL ((>) c) l2) /\ a <= b /\ b <= c ==>
     SORTED (<) (APPEND l1 l2) /\ ALL ((<=) a) (APPEND l1 l2) /\
     ALL ((>) c) (APPEND l1 l2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM; ALL_APPEND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `transitive ((<):num->num->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[transitive_DEF] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SORTED_APPEND] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GT]) THEN ASM_ARITH_TAC);;

let CLOSP1AUX_num_SR_NIL = prove
 (`!a b. SORTED (<) [] /\ ALL ((<=) a) [] /\ ALL ((>) b) []`,
  REWRITE_TAC[SORTED_DEF; ALL]);;

let CLOSP1AUX_num_SR_SING = prove
 (`!a b x. a <= x /\ x < b ==> SORTED (<) [x] /\ ALL ((<=) a) [x] /\ ALL ((>) b) [x]`,
  REWRITE_TAC[SORTED_DEF; ALL; GT]);;

let CLOSP1AUX_num_SR_GENLIST = prove
 (`!m k. SORTED (<) (list_of_seq (\i. m + 2 * i) k) /\
         ALL ((<=) m) (list_of_seq (\i. m + 2 * i) k) /\
         ALL ((>) (m + 2 * k)) (list_of_seq (\i. m + 2 * i) k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM; MEM_GENLIST] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SORTED_EL_SUC; LENGTH_LIST_OF_SEQ] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `SUC m < n ==> m < n`] THEN ARITH_TAC;
    REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[GT] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC]);;

(* prove SORTED (<) L /\ ALL ((<=) a) L /\ ALL ((>) c) L for L an APPEND of  *)
(* code_locs of renumbered parts, location lists and GENLISTs, by splitting  *)
(* the APPENDs at the upper bounds of the parts                             *)
let rec CLOSP1AUX_num_upper asms l =
  if CLOSPROPSAUX_is_app "APPEND" l then CLOSP1AUX_num_upper asms (rand l)
  else if CLOSPROPSAUX_is_app "list_of_seq" l then
    let f = lhand l and k = rand l in
    let m = lhand (body f) in
    mk_binop `(+):num->num->num` m (mk_binop `( * ):num->num->num` `2` k)
  else
    let pat t = is_comb t && is_comb (rator t) &&
                CLOSPROPSAUX_is_app "ALL" t && rand t = l &&
                CLOSPROPSAUX_is_app ">" (lhand t) in
    let cands = flat (map (fun th -> filter pat (conjuncts (concl th))) asms) in
    rand (lhand (hd cands));;

let rec CLOSP1AUX_NUM_SR_TAC : tactic = fun (asl,w as gl) ->
  let l = rand (rand (rand w)) in
  if CLOSPROPSAUX_is_app "APPEND" l then
    let a = rand (lhand (lhand (rand w))) and c = rand (lhand (rand (rand w))) in
    let l1 = lhand l and l2 = rand l in
    let b = CLOSP1AUX_num_upper (map snd asl) l1 in
    (MATCH_MP_TAC (SPECL [a; b; c; l1; l2] CLOSP1AUX_num_SR_APPEND) THEN
     CONJ_TAC THENL
      [CLOSP1AUX_NUM_SR_TAC;
       CONJ_TAC THENL [CLOSP1AUX_NUM_SR_TAC; CONJ_TAC THEN CLOSP1AUX_NUM_ARITH_TAC]]) gl
  else
    (ASM_REWRITE_TAC[CLOSP1AUX_num_SR_GENLIST] THEN
     TRY (MATCH_MP_TAC CLOSP1AUX_num_SR_SING THEN CLOSP1AUX_NUM_ARITH_TAC)) gl;;

let renumber_code_locs_distinct_lemma = prove
 (`(!n es. SORTED (<) (code_locs (SND (renumber_code_locs_list n es))) /\
           ALL ((<=) n) (code_locs (SND (renumber_code_locs_list n es))) /\
           ALL ((>) (FST (renumber_code_locs_list n es)))
               (code_locs (SND (renumber_code_locs_list n es)))) /\
   (!n e. SORTED (<) (code_locs [SND (renumber_code_locs n e)]) /\
          ALL ((<=) n) (code_locs [SND (renumber_code_locs n e)]) /\
          ALL ((>) (FST (renumber_code_locs n e))) (code_locs [SND (renumber_code_locs n e)]))`,
  MATCH_MP_TAC renumber_code_locs_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY(DISCH_THEN(STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[renumber_code_locs_def] THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[FST; SND] THEN CLOSP1AUX_NUM_NORM_TAC THEN CLOSP1AUX_NUM_INC_TAC THEN
  CLOSP1AUX_NUM_LEN_TAC THEN ONCE_REWRITE_TAC[code_locs_cons] THEN
  REWRITE_TAC[code_locs_def; LET_DEF; LET_END_DEF; APPEND_NIL; CLOSP1AUX_num_SR_NIL] THEN
  CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MAP_SND_ZIP; LENGTH_ZIP; LENGTH_MAP] THEN
  CLOSP1AUX_NUM_SR_TAC);;

let CLOSP1AUX_num_lt_order = prove
 (`irreflexive ((<):num->num->bool) /\ transitive ((<):num->num->bool)`,
  REWRITE_TAC[irreflexive_DEF; transitive_DEF] THEN ARITH_TAC);;

let renumber_code_locs_distinct = prove
 (`!n e. ALL_DISTINCT (code_locs [SND (renumber_code_locs n e)]) /\
         ALL ((<=) n) (code_locs [SND (renumber_code_locs n e)]) /\
         ALL ((>) (FST (renumber_code_locs n e))) (code_locs [SND (renumber_code_locs n e)])`,
  MESON_TAC[renumber_code_locs_distinct_lemma; SORTED_ALL_DISTINCT; CLOSP1AUX_num_lt_order]);;

let renumber_code_locs_list_distinct = prove
 (`!n es.
     ALL_DISTINCT (code_locs (SND (renumber_code_locs_list n es))) /\
     ALL ((<=) n) (code_locs (SND (renumber_code_locs_list n es))) /\
     ALL ((>) (FST (renumber_code_locs_list n es)))
         (code_locs (SND (renumber_code_locs_list n es)))`,
  MESON_TAC[renumber_code_locs_distinct_lemma; SORTED_ALL_DISTINCT; CLOSP1AUX_num_lt_order]);;
let renumber_code_locs_list_els = prove
 (`!ls ls' n n'. renumber_code_locs_list n ls = (n',ls') ==>
     !x. x < LENGTH ls ==> ?m. EL x ls' = SND (renumber_code_locs m (EL x ls))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[renumber_code_locs_def; LENGTH; CONJUNCT1 LT] THEN
  REPEAT GEN_TAC THEN REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; LT_SUC] THEN DISCH_TAC THENL
   [EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[SND];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall (concl th) &&
      length (fst (strip_forall (concl th))) = 3)) THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th o
      check (fun th' -> CLOSPROPSAUX_is_app "renumber_code_locs_list" (lhs (concl th'))))) THEN
    ASM_SIMP_TAC[]]);;

(* value relation *)

(* HOL4: v_rel (the free variables of the rules are bound; HOL4 ZIP (l1,l2) *)
(* is ZIP l1 l2, the lists have the same length)                            *)
let clos_numberProof_v_rel_rules,clos_numberProof_v_rel_ind,
    clos_numberProof_v_rel_cases,clos_numberProof_v_rel_strongind =
  cake_inductive
  `(!max_app j. clos_numberProof_v_rel max_app (clos_Number j) (clos_Number j)) /\
   (!max_app w. clos_numberProof_v_rel max_app (clos_Word64 w) (clos_Word64 w)) /\
   (!max_app t xs ys.
      ALL2 (clos_numberProof_v_rel max_app) xs ys ==>
      clos_numberProof_v_rel max_app (clos_Block t xs) (clos_Block t ys)) /\
   (!max_app ws. clos_numberProof_v_rel max_app (ByteVector ws) (ByteVector ws)) /\
   (!max_app b r1. clos_numberProof_v_rel max_app (clos_RefPtr b r1) (clos_RefPtr b r1)) /\
   (!max_app env env' argenv argenv' c c' n p p' num_args.
      ALL2 (clos_numberProof_v_rel max_app) env env' /\
      ALL2 (clos_numberProof_v_rel max_app) argenv argenv' /\
      ~contains_App_SOME max_app [c] /\
      c' = SND (renumber_code_locs n c) ==>
      clos_numberProof_v_rel max_app (clos_Closure p argenv env num_args c)
                                     (clos_Closure p' argenv' env' num_args c')) /\
   (!max_app env env' argenv argenv' es es' n p p' k.
      ALL2 (clos_numberProof_v_rel max_app) env env' /\
      ALL2 (clos_numberProof_v_rel max_app) argenv argenv' /\
      ~contains_App_SOME max_app (MAP SND es) /\
      es' = ZIP (MAP FST es) (SND (renumber_code_locs_list n (MAP SND es))) ==>
      clos_numberProof_v_rel max_app (clos_Recclosure p argenv env es k)
                                     (clos_Recclosure p' argenv' env' es' k))`;;

(* HOL4: state_rel *)
let clos_numberProof_state_rel_def = cake_def
  `clos_numberProof_state_rel (s:(num#C,FFI)clos_state) (t:(C,FFI)clos_state) <=>
     clos_state_clock s = clos_state_clock t /\ clos_state_ffi s = clos_state_ffi t /\
     clos_state_max_app t = clos_state_max_app s /\
     clos_state_compile s =
       state_cc (ignore_table clos_number_compile_inc) (clos_state_compile t) /\
     clos_state_compile_oracle t =
       state_co (ignore_table clos_number_compile_inc) (clos_state_compile_oracle s) /\
     fmap_rel (clos_ref_rel (clos_numberProof_v_rel (clos_state_max_app s)))
              (clos_state_refs s) (clos_state_refs t) /\
     ALL2 (OPTREL (clos_numberProof_v_rel (clos_state_max_app s)))
          (clos_state_globals s) (clos_state_globals t) /\
     (!n. SND (SND (clos_state_compile_oracle s n)) = [] /\
          ~contains_App_SOME (clos_state_max_app s)
             (FST (SND (clos_state_compile_oracle s n)))) /\
     clos_state_code s = FEMPTY /\ clos_state_code t = FEMPTY`;;

(* HOL4: state_rel_max_app [local] *)
let clos_numberProof_state_rel_max_app = prove
 (`!(s:(num#C,FFI)clos_state) t.
     clos_numberProof_state_rel s t ==> clos_state_max_app s = clos_state_max_app t`,
  SIMP_TAC[clos_numberProof_state_rel_def]);;

(* HOL4: state_rel_with_clock [local] *)
let clos_numberProof_state_rel_with_clock = prove
 (`!(s:(num#C,FFI)clos_state) t.
     clos_numberProof_state_rel s t ==>
     clos_numberProof_state_rel (clos_state_clock_fupd (K x) s)
                                (clos_state_clock_fupd (K x) t)`,
  REWRITE_TAC[clos_numberProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[]);;

(* HOL4: state_rel_clock [local] *)
let clos_numberProof_state_rel_clock = prove
 (`clos_numberProof_state_rel (s:(num#C,FFI)clos_state) t ==>
   clos_state_clock s = clos_state_clock t`,
  SIMP_TAC[clos_numberProof_state_rel_def]);;

(* HOL4: state_rel_globals [local] *)
let clos_numberProof_state_rel_globals = prove
 (`clos_numberProof_state_rel (s:(num#C,FFI)clos_state) t ==>
   ALL2 (OPTREL (clos_numberProof_v_rel (clos_state_max_app s)))
        (clos_state_globals s) (clos_state_globals t)`,
  SIMP_TAC[clos_numberProof_state_rel_def]);;

(* HOL4: state_rel_refs [local] *)
let state_rel_refs = prove
 (`clos_numberProof_state_rel (s:(num#C,FFI)clos_state) t ==>
   fmap_rel (clos_ref_rel (clos_numberProof_v_rel (clos_state_max_app t)))
            (clos_state_refs s) (clos_state_refs t)`,
  SIMP_TAC[clos_numberProof_state_rel_def]);;

(* HOL4: state_rel_code [local] *)
let state_rel_code = prove
 (`clos_numberProof_state_rel (s:(num#C,FFI)clos_state) t ==>
   clos_state_code s = FEMPTY /\ clos_state_code t = FEMPTY`,
  SIMP_TAC[clos_numberProof_state_rel_def]);;
(* HOL4: v_rel_simp (HOL4 computes it with SIMP_CONV from v_rel_cases) *)
let clos_numberProof_v_rel_simp = prove
 (`(!max_app x y. clos_numberProof_v_rel max_app (clos_Number x) y <=> y = clos_Number x) /\
   (!max_app n y. clos_numberProof_v_rel max_app (clos_Word64 n) y <=> y = clos_Word64 n) /\
   (!max_app n l y. clos_numberProof_v_rel max_app (clos_Block n l) y <=>
                    ?ys. y = clos_Block n ys /\ ALL2 (clos_numberProof_v_rel max_app) l ys) /\
   (!max_app ws y. clos_numberProof_v_rel max_app (ByteVector ws) y <=> y = ByteVector ws) /\
   (!max_app b x y. clos_numberProof_v_rel max_app (clos_RefPtr b x) y <=>
                    y = clos_RefPtr b x) /\
   (!max_app n a l narg x y.
      clos_numberProof_v_rel max_app (clos_Closure n a l narg x) y <=>
      ?env' argenv' n' p'.
        y = clos_Closure p' argenv' env' narg (SND (renumber_code_locs n' x)) /\
        ALL2 (clos_numberProof_v_rel max_app) l env' /\
        ALL2 (clos_numberProof_v_rel max_app) a argenv' /\
        ~contains_App_SOME max_app [x]) /\
   (!max_app x1 x2 x3 x4 x5 y.
      clos_numberProof_v_rel max_app (clos_Recclosure x1 x2 x3 x4 x5) y <=>
      ?env' argenv' n p'.
        y = clos_Recclosure p' argenv' env'
              (ZIP (MAP FST x4) (SND (renumber_code_locs_list n (MAP SND x4)))) x5 /\
        ALL2 (clos_numberProof_v_rel max_app) x3 env' /\
        ALL2 (clos_numberProof_v_rel max_app) x2 argenv' /\
        ~contains_App_SOME max_app (MAP SND x4)) /\
   (!max_app x y. clos_numberProof_v_rel max_app y (clos_Number x) <=> y = clos_Number x) /\
   (!max_app n y. clos_numberProof_v_rel max_app y (clos_Word64 n) <=> y = clos_Word64 n) /\
   (!max_app n l y. clos_numberProof_v_rel max_app y (clos_Block n l) <=>
                    ?xs. y = clos_Block n xs /\ ALL2 (clos_numberProof_v_rel max_app) xs l) /\
   (!max_app ws y. clos_numberProof_v_rel max_app y (ByteVector ws) <=> y = ByteVector ws) /\
   (!max_app b x y. clos_numberProof_v_rel max_app y (clos_RefPtr b x) <=>
                    y = clos_RefPtr b x) /\
   (!max_app n a l narg x y.
      clos_numberProof_v_rel max_app y (clos_Closure n a l narg x) <=>
      ?p argenv env c n'.
        y = clos_Closure p argenv env narg c /\
        ALL2 (clos_numberProof_v_rel max_app) env l /\
        ALL2 (clos_numberProof_v_rel max_app) argenv a /\
        ~contains_App_SOME max_app [c] /\ x = SND (renumber_code_locs n' c)) /\
   (!max_app x1 x2 x3 x4 x5 y.
      clos_numberProof_v_rel max_app y (clos_Recclosure x1 x2 x3 x4 x5) <=>
      ?p argenv env es n.
        y = clos_Recclosure p argenv env es x5 /\
        ALL2 (clos_numberProof_v_rel max_app) env x3 /\
        ALL2 (clos_numberProof_v_rel max_app) argenv x2 /\
        ~contains_App_SOME max_app (MAP SND es) /\
        x4 = ZIP (MAP FST es) (SND (renumber_code_locs_list n (MAP SND es))))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_numberProof_v_rel_cases] THEN
  REWRITE_TAC[distinctness "clos_v"; injectivity "clos_v"; GSYM CONJ_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
let clos_numberProof_v_rel_Boolv = prove
 (`(clos_numberProof_v_rel max_app x (clos_Boolv b) <=> x = clos_Boolv b) /\
   (clos_numberProof_v_rel max_app (clos_Boolv b) x <=> x = clos_Boolv b)`,
  REWRITE_TAC[clos_Boolv_def; clos_numberProof_v_rel_simp; LIST_REL_NIL] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [clos_numberProof_v_rel_Boolv];;

let clos_numberProof_v_rel_Unit = prove
 (`(clos_numberProof_v_rel max_app x clos_Unit <=> x = clos_Unit) /\
   (clos_numberProof_v_rel max_app clos_Unit x <=> x = clos_Unit)`,
  REWRITE_TAC[clos_Unit_def; clos_numberProof_v_rel_simp; LIST_REL_NIL] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [clos_numberProof_v_rel_Unit];;
(* semantic functions respect relation *)

(* local helpers: lengths of related lists; ALL2 goals on APPEND, REVERSE,  *)
(* TAKE, DROP and GENLIST of related lists; the witness of a renumbering    *)
let CLOSP1AUX_NUM_ALL2_LENGTH_TAC : tactic = fun (asl,w as gl) ->
  let ths = mapfilter (fun (_,th) -> MATCH_MP LIST_REL_LENGTH th) asl in
  let ths = filter (fun th -> not (exists (fun (_,a) -> concl a = concl th) asl)) ths in
  MAP_EVERY ASSUME_TAC ths gl;;

let CLOSP1AUX_NUM_LENGTHS_TAC : tactic =
  CLOSP1AUX_NUM_ALL2_LENGTH_TAC THEN
  (fun (asl,w as gl) ->
     let eqs = filter (fun th -> let c = concl th in
                        is_eq c && CLOSPROPSAUX_is_app "LENGTH" (lhs c) &&
                        CLOSPROPSAUX_is_app "LENGTH" (rhs c) && is_var (rand (rhs c)))
                      (map snd asl) in
     REWRITE_TAC (map SYM eqs) gl);;

let CLOSP1AUX_NUM_RENUM_WITNESS_TAC : tactic = fun (asl,w as gl) ->
  let fvs = frees w @ freesl (map (concl o snd) asl) in
  let t = find_term (fun t -> is_comb t && is_comb (rator t) &&
                              (CLOSPROPSAUX_is_app "renumber_code_locs" t ||
                               CLOSPROPSAUX_is_app "renumber_code_locs_list" t) &&
                              subset (frees t) fvs) (snd (strip_exists w)) in
  EXISTS_TAC (lhand t) gl;;

let CLOSP1AUX_NUM_ALL2_TAC : tactic =
  REPEAT((MATCH_MP_TAC EVERY2_APPEND_suff THEN CONJ_TAC) ORELSE
         MATCH_MP_TAC EVERY2_REVERSE ORELSE MATCH_MP_TAC EVERY2_TAKE ORELSE
         MATCH_MP_TAC EVERY2_DROP) THEN
  ASM_REWRITE_TAC[ALL2; LIST_REL_GENLIST] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[clos_numberProof_v_rel_simp; injectivity "clos_v"; GSYM CONJ_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  TRY CLOSP1AUX_NUM_RENUM_WITNESS_TAC THEN ASM_REWRITE_TAC[ALL2];;

(* local helpers: the functions of a renumbered Letrec *)
let CLOSP1AUX_num_LENGTH_ZIP_renum = prove
 (`!n (es:(num#clos_exp)list).
     LENGTH (ZIP (MAP FST es) (SND (renumber_code_locs_list n (MAP SND es)))) = LENGTH es`,
  SIMP_TAC[LENGTH_ZIP; renumber_code_locs_length; LENGTH_MAP]);;

let CLOSP1AUX_num_EL_ZIP_renum = prove
 (`!n (es:(num#clos_exp)list) k. k < LENGTH es ==>
     EL k (ZIP (MAP FST es) (SND (renumber_code_locs_list n (MAP SND es)))) =
     (FST (EL k es), EL k (SND (renumber_code_locs_list n (MAP SND es))))`,
  SIMP_TAC[EL_ZIP; renumber_code_locs_length; LENGTH_MAP; EL_MAP]);;
let CLOSP1AUX_num_els = prove
 (`!n ls x. x < LENGTH ls ==>
     ?m. EL x (SND (renumber_code_locs_list n ls)) = SND (renumber_code_locs m (EL x ls))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `renumber_code_locs_list n ls` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `ls1:clos_exp list` ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP renumber_code_locs_list_els) THEN
  ASM_REWRITE_TAC[SND] THEN MESON_TAC[]);;

let CLOSP1AUX_num_contains_EL = prove
 (`!ls k. ~contains_App_SOME max_app ls /\ k < LENGTH ls ==>
          ~contains_App_SOME max_app [EL k ls]`,
  ONCE_REWRITE_TAC[contains_App_SOME_EXISTS] THEN
  REWRITE_TAC[EX; GSYM EX_MEM] THEN MESON_TAC[MEM_EL]);;
(* a local helper: dest_closure with no location gives NONE or Partial_app *)
(* for related arguments in step                                          *)
let CLOSP1AUX_num_dest_closure_NONE_Partial = prove
 (`clos_numberProof_v_rel max_app f f' /\ ALL2 (clos_numberProof_v_rel max_app) args args' ==>
   (dest_closure max_app NONE f args = NONE ==>
    dest_closure max_app NONE f' args' = NONE) /\
   (!c. dest_closure max_app NONE f args = SOME (Partial_app c) ==>
        ?c'. dest_closure max_app NONE f' args' = SOME (Partial_app c') /\
             clos_numberProof_v_rel max_app c c')`,
  CASES_ON `f:clos_v` THEN REWRITE_TAC[clos_numberProof_v_rel_simp] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH o
              check (fun th -> CLOSPROPSAUX_is_app "ALL2" (concl th) &&
                               lhand (concl th) = `args:clos_v list`)) THEN
  REWRITE_TAC[dest_closure_def; check_loc_def] THEN CASE_REWRITE_TAC[check_loc_def] THENL
   [ALL_TAC;
    REWRITE_TAC[CLOSP1AUX_num_LENGTH_ZIP_renum] THEN
    ASM_CASES_TAC `LENGTH (a3:(num#clos_exp)list) <= a4` THENL
     [ASM_REWRITE_TAC[] THEN REPEAT PAIRARG_TAC THEN ASM_REWRITE_TAC[distinctness "option"];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP CLOSP1AUX_num_EL_ZIP_renum
      (REWRITE_RULE[NOT_LE] th)]) THEN
    REWRITE_TAC[pair_CASE] THEN REPEAT PAIRARG_TAC THEN ASM_REWRITE_TAC[FST] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF]] THEN
  CLOSP1AUX_NUM_LENGTHS_TAC THEN
  REPEAT(COND_CASES_TAC THEN
         REWRITE_TAC[distinctness "option"; injectivity "option";
                     distinctness "app_kind"; injectivity "app_kind"]) THEN
  REWRITE_TAC[MESON[] `!a:clos_v P. (!x. a = x ==> P x) <=> P a`;
              MESON[] `!a:clos_v P. (?x. a = x /\ P x) <=> P a`] THEN
  REWRITE_TAC[clos_numberProof_v_rel_simp; injectivity "clos_v"] THEN
  ASM_MESON_TAC[EVERY2_APPEND_suff]);;

(* HOL4: dest_closure_v_rel_none [local] *)
let dest_closure_v_rel_none = prove
 (`!f args f' args'.
     clos_numberProof_v_rel max_app f f' /\
     ALL2 (clos_numberProof_v_rel max_app) args args' /\
     dest_closure max_app NONE f args = NONE ==>
     dest_closure max_app NONE f' args' = NONE`,
  MESON_TAC[CLOSP1AUX_num_dest_closure_NONE_Partial]);;

(* HOL4: dest_closure_v_rel_partial [local] *)
let dest_closure_v_rel_partial = prove
 (`!c f args f' args'.
     clos_numberProof_v_rel max_app f f' /\
     ALL2 (clos_numberProof_v_rel max_app) args args' /\
     dest_closure max_app NONE f args = SOME (Partial_app c) ==>
     ?c'. dest_closure max_app NONE f' args' = SOME (Partial_app c') /\
          clos_numberProof_v_rel max_app c c'`,
  MESON_TAC[CLOSP1AUX_num_dest_closure_NONE_Partial]);;

(* HOL4: dest_closure_v_rel_full [local] (c is unused, as in HOL4) *)
let dest_closure_v_rel_full = prove
 (`!(c:A) f args f' args' args1 args2.
     clos_numberProof_v_rel max_app f f' /\
     ALL2 (clos_numberProof_v_rel max_app) args args' /\
     dest_closure max_app NONE f args = SOME (Full_app exp args1 args2) ==>
     ?args1' args2' n.
       dest_closure max_app NONE f' args' =
         SOME (Full_app (SND (renumber_code_locs n exp)) args1' args2') /\
       ALL2 (clos_numberProof_v_rel max_app) args1 args1' /\
       ALL2 (clos_numberProof_v_rel max_app) args2 args2' /\
       ~contains_App_SOME max_app [exp]`,
  REPEAT GEN_TAC THEN CASES_ON `f:clos_v` THEN REWRITE_TAC[clos_numberProof_v_rel_simp] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_var (lhs (concl th))
                          then SUBST_ALL_TAC th else NO_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> CLOSPROPSAUX_is_app "dest_closure"
                                            (lhs (concl th)))) THEN
  REWRITE_TAC[dest_closure_def; check_loc_def] THEN CASE_REWRITE_TAC[check_loc_def] THEN
  CLOSP1AUX_NUM_LENGTHS_TAC THENL
   [REPEAT(COND_CASES_TAC THEN
           REWRITE_TAC[distinctness "option"; injectivity "option";
                       distinctness "app_kind"; injectivity "app_kind"]) THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
    CLOSP1AUX_NUM_RENUM_WITNESS_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN CLOSP1AUX_NUM_ALL2_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[CLOSP1AUX_num_LENGTH_ZIP_renum] THEN
  ASM_CASES_TAC `LENGTH (a3:(num#clos_exp)list) <= a4` THENL
   [ASM_REWRITE_TAC[] THEN REPEAT PAIRARG_TAC THEN ASM_REWRITE_TAC[distinctness "option"];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP CLOSP1AUX_num_EL_ZIP_renum
    (REWRITE_RULE[NOT_LE] th)]) THEN
  REWRITE_TAC[pair_CASE] THEN REPEAT PAIRARG_TAC THEN ASM_REWRITE_TAC[FST] THEN
  CLOSP1AUX_NUM_LENGTHS_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT(COND_CASES_TAC THEN
         REWRITE_TAC[distinctness "option"; injectivity "option";
                     distinctness "app_kind"; injectivity "app_kind"]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `a4 < LENGTH (a3:(num#clos_exp)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `MAP SND (a3:(num#clos_exp)list)`; `a4:num`] CLOSP1AUX_num_els) THEN
  ASM_SIMP_TAC[LENGTH_MAP; EL_MAP] THEN ASM_REWRITE_TAC[SND] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  CLOSP1AUX_NUM_RENUM_WITNESS_TAC THEN REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [CLOSP1AUX_NUM_ALL2_TAC; CLOSP1AUX_NUM_ALL2_TAC;
    MP_TAC(SPECL [`MAP SND (a3:(num#clos_exp)list)`; `a4:num`] CLOSP1AUX_num_contains_EL) THEN
    ASM_SIMP_TAC[LENGTH_MAP; EL_MAP; SND]]);;

(* HOL4: helper [local] *)
let clos_numberProof_helper = prove
 (`SND ((\(n',x'). (n',[x'])) (x:A#B)) = [SND x]`,
  MP_TAC(ISPEC `x:A#B` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[SND]);;

(* HOL4: v_rel_Boolv_mono [local] *)
let v_rel_Boolv_mono = prove
 (`(x <=> y) ==> clos_numberProof_v_rel max_app (clos_Boolv x) (clos_Boolv y)`,
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[clos_numberProof_v_rel_Boolv]);;

(* HOL4: v_to_list [local] *)
let clos_numberProof_v_to_list = prove
 (`!x y. clos_numberProof_v_rel max_app x y ==>
         OPTREL (ALL2 (clos_numberProof_v_rel max_app)) (clos_v_to_list x) (clos_v_to_list y)`,
  MATCH_MP_TAC clos_v_to_list_ind THEN REPEAT CONJ_TAC THENL
   [ALL_TAC; REPEAT GEN_TAC THEN DISCH_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC;
    ALL_TAC; ALL_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_numberProof_v_rel_simp; LIST_REL_NIL; LIST_REL_CONS1] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[clos_v_to_list_def; OPTREL_THM] THEN
  COND_CASES_TAC THEN REWRITE_TAC[OPTREL_THM; ALL2] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h'':clos_v` o C MP (ASSUME `tag = cons_tag`)) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `clos_v_to_list bt` THEN CASES_ON `clos_v_to_list h''` THEN
  REWRITE_TAC[OPTREL_THM; case_def "option"; ALL2] THEN ASM_REWRITE_TAC[]);;

(* HOL4: simple_val_rel *)
let clos_numberProof_simple_val_rel = prove
 (`clos_simple_val_rel (clos_numberProof_v_rel max_app_n)`,
  REWRITE_TAC[clos_simple_val_rel_def; clos_numberProof_v_rel_simp; isClos_cases] THEN
  MESON_TAC[]);;

(* a local helper: clos_ref_rel with the right side known *)
let CLOSP1AUX_num_ref_rel_right = prove
 (`(!(R:A->B->bool) x vs. clos_ref_rel R x (clos_ValueArray vs) <=>
                          ?ws. x = clos_ValueArray ws /\ ALL2 R ws vs) /\
   (!(R:A->B->bool) x bs. clos_ref_rel R x (clos_ByteArray bs) <=> x = clos_ByteArray bs) /\
   (!(R:A->B->bool) x m v. clos_ref_rel R x (clos_Thunk m v) <=>
                           ?w. x = clos_Thunk m w /\ R w v)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN CASES_ON `x:(A)clos_ref` THEN
  REWRITE_TAC[clos_ref_rel_def; distinctness "clos_ref"; injectivity "clos_ref"] THEN
  MESON_TAC[]);;

(* HOL4: simple_state_rel *)
let clos_numberProof_simple_state_rel = prove
 (`clos_simple_state_rel (clos_numberProof_v_rel max_app_n)
     (\(s:(num#C,FFI)clos_state) (t:(C,FFI)clos_state).
        clos_state_max_app s = max_app_n /\ clos_numberProof_state_rel s t)`,
  REWRITE_TAC[clos_simple_state_rel_def; clos_numberProof_state_rel_def] THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM; fmap_rel_def; FLOOKUP_DEF;
              FDOM_FUPDATE; IN_INSERT; FAPPLY_FUPDATE_THM] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRY(FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
                                 CLOSPROPSAUX_is_app "clos_state_max_app" (lhs (concl th)) &&
                                 is_var (rhs (concl th))
                              then SUBST_ALL_TAC th THEN ASSUME_TAC th else NO_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_eq (concl th) && CLOSPROPSAUX_is_app "FDOM" (lhs (concl th))
                                 then SUBST_ALL_TAC th else NO_TAC)) THEN
  REWRITE_TAC[] THEN
  TRY(FIRST_X_ASSUM(MP_TAC o check (is_cond o lhs o concl)) THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[distinctness "option"; injectivity "option"] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `ptr:num` o
                    check (fun th -> can (find_term (fun t -> try fst(dest_const t) =
                             "clos_ref_rel" with Failure _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[CLOSP1AUX_num_ref_rel_right] THEN MESON_TAC[] THEN NO_TAC) THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[clos_ref_rel_def]);;

(* HOL4: do_app_lemma *)
let clos_numberProof_do_app_lemma = prove
 (CASE_TERM
  `clos_numberProof_state_rel (s:(num#C,FFI)clos_state) t /\
   ALL2 (clos_numberProof_v_rel (clos_state_max_app s)) xs ys ==>
   match clos_do_app opp xs s with
     Rval (x,s1) -> ?y t1. clos_numberProof_v_rel (clos_state_max_app s) x y /\
                           (clos_state_max_app s1 = clos_state_max_app s /\
                            clos_numberProof_state_rel s1 t1) /\
                           clos_do_app opp ys t = Rval (y,t1)
   | Rerr err1 -> ?err2. clos_do_app opp ys t = Rerr err2 /\
                         exc_rel (clos_numberProof_v_rel (clos_state_max_app s)) err1 err2`,
  MP_TAC(ISPECL [`clos_numberProof_v_rel (clos_state_max_app (s:(num#C,FFI)clos_state))`;
                 `\(r:(num#C,FFI)clos_state) (t:(C,FFI)clos_state).
                     clos_state_max_app r = clos_state_max_app (s:(num#C,FFI)clos_state) /\
                     clos_numberProof_state_rel r t`;
                 `s:(num#C,FFI)clos_state`; `t:(C,FFI)clos_state`; `xs:clos_v list`;
                 `ys:clos_v list`; `opp:clos_op`] simple_val_rel_do_app) THEN
  REWRITE_TAC[GEN_ALL clos_numberProof_simple_val_rel;
              GEN_ALL clos_numberProof_simple_state_rel] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[]);;

(* HOL4: list_to_v_v_rel *)
let clos_numberProof_list_to_v_v_rel = prove
 (`!xs ys. ALL2 (clos_numberProof_v_rel ap) xs ys ==>
           clos_numberProof_v_rel ap (clos_list_to_v xs) (clos_list_to_v ys)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1] THEN REPEAT STRIP_TAC THEN
  RVEQ_TAC THEN REWRITE_TAC[clos_list_to_v_def; clos_numberProof_v_rel_simp] THEN
  ASM_SIMP_TAC[ALL2; injectivity "clos_v"; UNWIND_THM1] THEN
  REWRITE_TAC[MESON[] `!a:clos_v list P. (?x. a = x /\ P x) <=> P a`;
              MESON[] `!a:clos_v list P. (?x. x = a /\ P x) <=> P a`] THEN
  ASM_SIMP_TAC[ALL2]);;

(* HOL4: do_app [local] *)
let clos_numberProof_do_app = prove
 (`clos_numberProof_state_rel (s1:(num#C,FFI)clos_state) s2 /\
   ALL2 (clos_numberProof_v_rel (clos_state_max_app s1)) x1 x2 ==>
   (!err. clos_do_app op x1 s1 = Rerr err ==> clos_do_app op x2 s2 = Rerr err) /\
   (!v1 w1. clos_do_app op x1 s1 = Rval (v1,w1) ==>
            ?v2 w2. clos_do_app op x2 s2 = Rval (v2,w2) /\
                    clos_numberProof_v_rel (clos_state_max_app s1) v1 v2 /\
                    clos_numberProof_state_rel w1 w2)`,
  STRIP_TAC THEN
  MP_TAC(INST [`s1:(num#C,FFI)clos_state`,`s:(num#C,FFI)clos_state`;
               `s2:(C,FFI)clos_state`,`t:(C,FFI)clos_state`;
               `x1:clos_v list`,`xs:clos_v list`; `x2:clos_v list`,`ys:clos_v list`;
               `op:clos_op`,`opp:clos_op`] clos_numberProof_do_app_lemma) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`op:clos_op`; `x1:clos_v list`; `s1:(num#C,FFI)clos_state`]
                CLOSPROPSAUX_do_app_not_Rraise) THEN
  CASES_ON `clos_do_app op x1 (s1:(num#C,FFI)clos_state)` THEN
  REWRITE_TAC[case_def "result"; distinctness "result"; injectivity "result"] THEN
  TRY(CASES_ON `a:clos_v#(num#C,FFI)clos_state` THEN REWRITE_TAC[case_def "prod"; PAIR_EQ] THEN
      MESON_TAC[]) THEN
  CASES_ON `a:(clos_v)error_result` THEN
  REWRITE_TAC[injectivity "error_result"; distinctness "error_result"] THEN
  REWRITE_TAC[exc_rel_type_error1] THEN MESON_TAC[]);;

(* HOL4: v_to_bytes [local] *)
let clos_numberProof_v_to_bytes = prove
 (`clos_numberProof_v_rel m v w ==> clos_v_to_bytes v = clos_v_to_bytes w`,
  MESON_TAC[clos_numberProof_simple_val_rel; clos_simple_val_rel_v_to_bytes]);;

(* HOL4: v_to_words [local] *)
let clos_numberProof_v_to_words = prove
 (`clos_numberProof_v_rel m v w ==> clos_v_to_words v = clos_v_to_words w`,
  MESON_TAC[clos_numberProof_simple_val_rel; clos_simple_val_rel_v_to_words]);;

(* HOL4: ignore_table_imp *)
let ignore_table_imp = prove
 (`ignore_table (f:A->B->C#D) st (p:B#E) = (st',p') ==> SND p' = SND p`,
  MP_TAC(ISPEC `p:B#E` PAIR_SURJECTIVE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ignore_table_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPEC `(f:A->B->C#D) st x` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[pair_CASE; PAIR_EQ] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[SND]);;


(* local helpers for do_install *)
(* a local helper: two related lists are both of length two or neither *)
let CLOSP1AUX_num_ALL2_two = prove
 (`!(R:A->B->bool) x1 x2.
     ALL2 R x1 x2 ==>
     (?v1 v2 w1 w2. x1 = [v1;v2] /\ x2 = [w1;w2] /\ R v1 w1 /\ R v2 w2) \/
     ((!v1 v2. ~(x1 = [v1;v2])) /\ (!w1 w2. ~(x2 = [w1;w2])))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `?v1 v2. x1 = [v1:A;v2]` THENL
   [DISJ1_TAC THEN FIRST_X_ASSUM(REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC o
                                 check (is_exists o concl)) THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[CONS_11; GSYM CONJ_ASSOC] THEN
    CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[LIST_REL_CONS2; LIST_REL_NIL] o
                  check (fun th -> is_comb (concl th) && not (is_neg (concl th)))) THEN
    STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[]]);;

(* a local helper: the states after an installation are related *)
let CLOSP1AUX_num_state_rel_install = prove
 (`!(s1:(num#C,FFI)clos_state) s2 k.
     clos_numberProof_state_rel s1 s2 ==>
     clos_numberProof_state_rel
       (clos_state_code_fupd (K (FEMPTY |++ []))
         (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle s1)))
           (clos_state_clock_fupd (K k) s1)))
       (clos_state_code_fupd (K (FEMPTY |++ []))
         (clos_state_compile_oracle_fupd (K (shift_seq 1 (clos_state_compile_oracle s2)))
           (clos_state_clock_fupd (K k) s2)))`,
  REWRITE_TAC[clos_numberProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM;
              FUPDATE_LIST_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[shift_seq_def] THEN
  REWRITE_TAC[FUN_EQ_THM; state_co_def]);;

(* a local helper: the oracles and compilers of related states *)
let CLOSP1AUX_num_oracle = prove
 (CASE_TERM `!(s1:(num#C,FFI)clos_state) s2 st c exps st' code'.
     clos_numberProof_state_rel s1 s2 /\
     clos_state_compile_oracle s1 0 = ((st,c),(exps,[])) /\
     clos_number_compile_inc st exps = (st',code') ==>
     clos_state_compile_oracle s2 0 = (c,(code',[])) /\
     FST (clos_state_compile_oracle s2 1) = SND (FST (clos_state_compile_oracle s1 1)) /\
     clos_state_compile s1 (st,c) (exps,[]) =
       (match clos_state_compile s2 c (code',[]) with
          NONE -> NONE
        | SOME (code,data,cfg1) -> SOME (code,data,st',cfg1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_numberProof_state_rel_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FST_state_co] THEN CONJ_TAC THENL
   [REWRITE_TAC[state_co_def] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC[pair_CASE; ignore_table_def; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[pair_CASE];
    REWRITE_TAC[state_cc_def] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC[pair_CASE; ignore_table_def; LET_DEF; LET_END_DEF] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[pair_CASE] THEN
    CASES_ON `clos_state_compile (s2:(C,FFI)clos_state) c (code',[])` THEN
    CASE_REWRITE_TAC[]]);;

let CLOSP1AUX_num_state_rel_oracle = prove
 (`!(s1:(num#C,FFI)clos_state) s2.
     clos_numberProof_state_rel s1 s2 ==>
     (!n. SND (SND (clos_state_compile_oracle s1 n)) = [] /\
          ~contains_App_SOME (clos_state_max_app s1)
             (FST (SND (clos_state_compile_oracle s1 n))))`,
  SIMP_TAC[clos_numberProof_state_rel_def]);;

let CLOSP1AUX_NUM_SPLIT_SOME_TAC : tactic = fun (asl,w as gl) ->
  let th = snd (find (fun (_,th) -> let c = concl th in
               is_eq c && CLOSPROPSAUX_is_app "SOME" (rhs c) && is_var (rand (rhs c)) &&
               (try fst (dest_type (type_of (rand (rhs c)))) = "prod" with Failure _ -> false))
             asl) in
  let p = rand (rhs (concl th)) in
  (UNDISCH_TAC (concl th) THEN SPEC_TAC(p,p) THEN
   REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC) gl;;

let CLOSP1AUX_num_shift_seq_app = prove
 (`!k (s:num->A) n. shift_seq k s n = s (n + k)`,
  REWRITE_TAC[shift_seq_def]);;

let CLOSP1AUX_num_compile_inc_nonnil = prove
 (`!n xs m ys. clos_number_compile_inc n xs = (m,ys) ==> ~(ys = [])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_number_compile_inc_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  MP_TAC(ISPEC `renumber_code_locs_list (make_even (n + MAX (LENGTH (xs:clos_exp list)) 1)) xs`
               PAIR_SURJECTIVE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE; PAIR_EQ] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[NOT_CONS_NIL]);;

(* HOL4: do_install [local] (err is unused, as in HOL4) *)
let do_install = prove
 (`clos_numberProof_state_rel (s1:(num#C,FFI)clos_state) s2 /\
   ALL2 (clos_numberProof_v_rel (clos_state_max_app s1)) x1 x2 ==>
   (!(err:A) t. clos_do_install x1 s1 = (Rerr (Rabort Rtimeout_error),t) ==>
          ?t'. clos_do_install x2 s2 = (Rerr (Rabort Rtimeout_error),t') /\
               clos_numberProof_state_rel t t') /\
   (!e1 t1. clos_do_install x1 s1 = (Rval e1,t1) ==>
     ?e2 t2. clos_do_install x2 s2 = (Rval e2,t2) /\
             ~contains_App_SOME (clos_state_max_app t1) e1 /\
             clos_state_max_app t1 = clos_state_max_app s1 /\
             e2 = SND (clos_number_compile_inc (FST (FST (clos_state_compile_oracle s1 0))) e1) /\
             clos_numberProof_state_rel t1 t2)`,
  STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP CLOSP1AUX_num_ALL2_two) THENL
   [ALL_TAC;
    ASM_SIMP_TAC[CLOSPROPSAUX_do_install_not2; PAIR_EQ; injectivity "result";
                 distinctness "result"; injectivity "error_result"; distinctness "abort"]] THEN
  FIRST_X_ASSUM(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN RVEQ_TAC THEN
  REWRITE_TAC[clos_do_install_def] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `clos_v_to_bytes w1 = clos_v_to_bytes v1 /\ clos_v_to_words w2 = clos_v_to_words v2`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[clos_numberProof_v_to_bytes; clos_numberProof_v_to_words]; ALL_TAC] THEN
  CASES_ON `clos_v_to_bytes v1` THEN CASES_ON `clos_v_to_words v2` THEN
  CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"; injectivity "result";
                   injectivity "error_result"; distinctness "abort"] THEN
  MP_TAC(ISPEC `clos_state_compile_oracle (s1:(num#C,FFI)clos_state) 0` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[EXISTS_PAIR_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `st:num` (X_CHOOSE_THEN `c:C` (X_CHOOSE_THEN `exps:clos_exp list`
    (X_CHOOSE_THEN `aux:(num#num#clos_exp)list` ASSUME_TAC)))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `0` o MATCH_MP CLOSP1AUX_num_state_rel_oracle) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPEC `clos_number_compile_inc st exps` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `st':num` (X_CHOOSE_THEN `code':clos_exp list` ASSUME_TAC)) THEN
  MP_TAC(SPECL [`s1:(num#C,FFI)clos_state`; `s2:(C,FFI)clos_state`; `st:num`; `c:C`;
                `exps:clos_exp list`; `st':num`; `code':clos_exp list`] CLOSP1AUX_num_oracle) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[pair_CASE; FST; SND] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP state_rel_code th]) THEN
  REWRITE_TAC[FDOM_FEMPTY; DISJOINT_EMPTY; MAP; ALL_DISTINCT; set_of_list; LET_DEF;
              LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CASES_ON `clos_state_compile (s2:(C,FFI)clos_state) c (code',[])` THEN
  CASE_REWRITE_TAC[PAIR_EQ; distinctness "result"; injectivity "result";
                   injectivity "error_result"; distinctness "abort"] THEN
  CLOSP1AUX_NUM_SPLIT_SOME_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[CLOSP1AUX_num_shift_seq_app; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP clos_numberProof_state_rel_clock th]) THEN
  SUBGOAL_THEN `~(code':clos_exp list = [])` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSP1AUX_num_compile_inc_nonnil]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ; distinctness "result"; injectivity "result";
              injectivity "error_result"; distinctness "abort"] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  ASM_REWRITE_TAC[SND] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[PAIR_EQ; distinctness "result"; injectivity "result";
              injectivity "error_result"; distinctness "abort"] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; SND] THEN
  TRY(MATCH_MP_TAC CLOSP1AUX_num_state_rel_install) THEN ASM_REWRITE_TAC[]);;

(* HOL4: lookup_vars_NONE_related_env *)
let lookup_vars_NONE_related_env = prove
 (`ALL2 (clos_numberProof_v_rel max_app) e1 e2 ==>
   (lookup_vars vs e1 = NONE <=> lookup_vars vs e2 = NONE)`,
  DISCH_THEN(ASSUME_TAC o MATCH_MP LIST_REL_LENGTH) THEN
  ASM_REWRITE_TAC[lookup_vars_NONE]);;

(* HOL4: lookup_vars_SOME_related_env *)
let lookup_vars_SOME_related_env = prove
 (`ALL2 (clos_numberProof_v_rel max_app) e1 e2 /\ lookup_vars vs e1 = SOME e1' /\
   lookup_vars vs e2 = SOME e2' ==> ALL2 (clos_numberProof_v_rel max_app) e1' e2'`,
  MAP_EVERY (fun t -> SPEC_TAC(t,t))
    [`e2':clos_v list`; `e1':clos_v list`; `e2:clos_v list`; `e1:clos_v list`;
     `vs:num list`] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[lookup_vars_def; injectivity "option"] THENL
   [MESON_TAC[ALL2]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  CASES_ON `lookup_vars (t:num list) (e1:clos_v list)` THEN
  CASES_ON `lookup_vars (t:num list) (e2:clos_v list)` THEN
  REWRITE_TAC[case_def "option"; distinctness "option"; injectivity "option"] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl) o
    check (fun th -> is_var (rhs (concl th))))) THEN
  REWRITE_TAC[ALL2] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[LIST_REL_EL_EQN]; ASM_MESON_TAC[]]);;

(* local helpers for rel_update_thunk: the references of related states, *)
(* an update of related references                                       *)
let CLOSP1AUX_num_flookup_rel = prove
 (`!(s1:(num#C,FFI)clos_state) s2 n.
     clos_numberProof_state_rel s1 s2 ==>
     OPTREL (clos_ref_rel (clos_numberProof_v_rel (clos_state_max_app s1)))
            (FLOOKUP (clos_state_refs s1) n) (FLOOKUP (clos_state_refs s2) n)`,
  REWRITE_TAC[clos_numberProof_state_rel_def; fmap_rel_def; FLOOKUP_DEF] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[OPTREL_THM]);;

let CLOSP1AUX_num_state_rel_refs_upd = prove
 (`!(s1:(num#C,FFI)clos_state) s2 p a b.
     clos_numberProof_state_rel s1 s2 /\
     clos_ref_rel (clos_numberProof_v_rel (clos_state_max_app s1)) a b ==>
     clos_numberProof_state_rel
       (clos_state_refs_fupd (K (clos_state_refs s1 |+ (p,a))) s1)
       (clos_state_refs_fupd (K (clos_state_refs s2 |+ (p,b))) s2)`,
  REWRITE_TAC[clos_numberProof_state_rel_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  SIMP_TAC[fmap_rel_FUPDATE_same]);;

(* HOL4: rel_update_thunk [local] *)
let clos_numberProof_rel_update_thunk = prove
 (`clos_numberProof_state_rel (s1:(num#C,FFI)clos_state) s2 /\
   ALL2 (clos_numberProof_v_rel (clos_state_max_app s1)) vs ys /\
   clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s1) vs = SOME refs1 ==>
   ?refs2. clos_update_thunk [clos_RefPtr v ptr] (clos_state_refs s2) ys = SOME refs2 /\
           clos_numberProof_state_rel (clos_state_refs_fupd (K refs1) s1)
                                      (clos_state_refs_fupd (K refs2) s2)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `(vs = [] /\ ys = []) \/
                (?x y. vs = [x] /\ ys = [y] /\
                       clos_numberProof_v_rel
                         (clos_state_max_app (s1:(num#C,FFI)clos_state)) x y) \/
                (?x1 x2 r1 y1 y2 r2. vs = CONS x1 (CONS x2 r1) /\
                                     ys = CONS y1 (CONS y2 r2))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ALL2 (clos_numberProof_v_rel (clos_state_max_app (s1:(num#C,FFI)clos_state)))
                      vs ys` THEN
    STRUCT_CASES_TAC(ISPEC `vs:clos_v list` list_CASES) THEN
    REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1] THENL [MESON_TAC[]; ALL_TAC] THEN
    STRUCT_CASES_TAC(ISPEC `t:clos_v list` list_CASES) THEN
    REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[CONS_11; NOT_CONS_NIL; UNWIND_THM1] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `clos_update_thunk [clos_RefPtr v ptr]
                   (clos_state_refs (s1:(num#C,FFI)clos_state)) vs = SOME refs1` THEN
    ASM_REWRITE_TAC[clos_update_thunk_def; distinctness "option"];
    ALL_TAC;
    UNDISCH_TAC `clos_update_thunk [clos_RefPtr v ptr]
                   (clos_state_refs (s1:(num#C,FFI)clos_state)) vs = SOME refs1` THEN
    ASM_REWRITE_TAC[clos_update_thunk_def; distinctness "option"]] THEN
  UNDISCH_TAC `clos_update_thunk [clos_RefPtr v ptr]
                 (clos_state_refs (s1:(num#C,FFI)clos_state)) vs = SOME refs1` THEN
  ASM_REWRITE_TAC[clos_update_thunk_def] THEN
  SUBGOAL_THEN `(clos_dest_thunk [x] (clos_state_refs (s1:(num#C,FFI)clos_state)) =
                 clos_NotThunk) <=>
                (clos_dest_thunk [y] (clos_state_refs (s2:(C,FFI)clos_state)) =
                 clos_NotThunk)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`clos_numberProof_v_rel (clos_state_max_app (s1:(num#C,FFI)clos_state))`;
                   `\(r:(num#C,FFI)clos_state) (t:(C,FFI)clos_state).
                      clos_state_max_app r = clos_state_max_app (s1:(num#C,FFI)clos_state) /\
                      clos_numberProof_state_rel r t`;
                   `s1:(num#C,FFI)clos_state`; `s2:(C,FFI)clos_state`;
                   `x:clos_v`; `y:clos_v`; `Evaluated`] CLOSPROPSAUX_bad_thunk_rel) THEN
    ASM_REWRITE_TAC[GEN_ALL clos_numberProof_simple_val_rel;
                    GEN_ALL clos_numberProof_simple_state_rel; clos_bad_thunk_update_def] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
  ASM_CASES_TAC `clos_dest_thunk [x] (clos_state_refs (s1:(num#C,FFI)clos_state)) =
                 clos_NotThunk` THENL
   [SUBGOAL_THEN `clos_dest_thunk [y] (clos_state_refs (s2:(C,FFI)clos_state)) =
                  clos_NotThunk`
      ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP CLOSSEMAUX_dest_thunk_NONE th]) THEN
    REWRITE_TAC[distinctness "option"]] THEN
  REWRITE_TAC[store_thunk_def] THEN
  MP_TAC(ISPECL [`s1:(num#C,FFI)clos_state`; `s2:(C,FFI)clos_state`; `ptr:num`]
                CLOSP1AUX_num_flookup_rel) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `FLOOKUP (clos_state_refs (s1:(num#C,FFI)clos_state)) ptr` THEN
  CASES_ON `FLOOKUP (clos_state_refs (s2:(C,FFI)clos_state)) ptr` THEN
  REWRITE_TAC[OPTREL_THM; case_def "option"; distinctness "option"] THEN
  CASES_ON `a':(clos_v)clos_ref` THEN REWRITE_TAC[CLOSP1AUX_num_ref_rel_right] THEN
  STRIP_TAC THEN RVEQ_TAC THEN CASE_REWRITE_TAC[distinctness "option"] THEN
  TRY(CASES_ON `a0:thunk_mode` THEN CASE_REWRITE_TAC[]) THEN
  REWRITE_TAC[injectivity "option"; distinctness "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[UNWIND_THM1] THEN
  MATCH_MP_TAC CLOSP1AUX_num_state_rel_refs_upd THEN
  ASM_REWRITE_TAC[clos_ref_rel_def]);;

(* ------------------------------------------------------------------------- *)
(* The correctness of renumber_code_locs (HOL4: renumber_code_locs_correct), *)
(* proved by the induction of closProps (CLOSPROPSAUX_evaluate_ind) with one *)
(* lemma per case and local tactics: an induction hypothesis is applied to   *)
(* a named sub-evaluation of the source (a type error there is a type error  *)
(* of the whole), with the index of the renumbering of the sub-expression,  *)
(* which gives the target sub-evaluation; max_app of later states is that  *)
(* of the first one (evaluate_const)                                        *)
(* ------------------------------------------------------------------------- *)

(* close a goal with the assumption F *)
let CLOSP1AUX_NUM_FALSE_TAC : tactic =
  FIRST_ASSUM(fun th -> if concl th = `F` then CONTR_TAC th else NO_TAC);;

let CLOSP1AUX_num_ind =
  let p = `\xs env (s1:(num#C,FFI)clos_state).
     !n res s2 env' t1.
       clos_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) /\
       ~contains_App_SOME (clos_state_max_app s1) xs /\
       ALL2 (clos_numberProof_v_rel (clos_state_max_app s1)) env env' /\
       clos_numberProof_state_rel s1 t1 ==>
       ?res' t2.
         clos_evaluate (SND (renumber_code_locs_list n xs),env',t1) = (res',t2) /\
         result_rel (ALL2 (clos_numberProof_v_rel (clos_state_max_app s1)))
                    (clos_numberProof_v_rel (clos_state_max_app s1)) res res' /\
         clos_numberProof_state_rel s2 t2`
  and q = `\loc f args (s:(num#C,FFI)clos_state).
     !res s2 f' args' t1.
       evaluate_app loc f args s = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) /\
       clos_numberProof_v_rel (clos_state_max_app s) f f' /\ loc = NONE /\
       ALL2 (clos_numberProof_v_rel (clos_state_max_app s)) args args' /\
       clos_numberProof_state_rel s t1 ==>
       ?res' t2.
         evaluate_app loc f' args' t1 = (res',t2) /\
         result_rel (ALL2 (clos_numberProof_v_rel (clos_state_max_app s)))
                    (clos_numberProof_v_rel (clos_state_max_app s)) res res' /\
         clos_numberProof_state_rel s2 t2` in
  CONV_RULE (DEPTH_CONV BETA_CONV) (ISPECL [p;q] CLOSPROPSAUX_evaluate_ind);;

let CLOSP1AUX_num_cases = conjuncts (lhand (concl CLOSP1AUX_num_ind));;

(* a local helper: the renumbering of a singleton *)
let CLOSP1AUX_num_SND_sing = prove
 (`!n e. SND (renumber_code_locs_list n [e]) = [SND (renumber_code_locs n e)]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[renumber_code_locs_def] THEN REPEAT PAIRARG_TAC THEN
  ASM_REWRITE_TAC[SND]);;

(* a local helper: the renumbering of the application of a thunk *)
let CLOSP1AUX_num_renum_AppUnit = prove
 (`!n. SND (renumber_code_locs_list n [clos_AppUnit (clos_Var backend_common_None 0)]) =
       [clos_AppUnit (clos_Var backend_common_None 0)]`,
  GEN_TAC THEN REWRITE_TAC[clos_AppUnit_def] THEN
  REPEAT(CHANGED_TAC(REWRITE_TAC[renumber_code_locs_def] THEN CASE_REWRITE_TAC[])) THEN
  REWRITE_TAC[SND]);;

(* the P- and Q-shaped facts: an evaluation of the source with a variable  *)
(* result implies a related evaluation of the target                       *)
let CLOSP1AUX_num_is_PQ name th =
  let c = snd(strip_forall(concl th)) in
  is_imp c && is_conj (lhand c) &&
  (let a = lhand (lhand c) in
   is_eq a && CLOSPROPSAUX_is_app name (lhs a) && is_pair (rhs a) &&
   is_var (lhand (rhs a)));;

let CLOSP1AUX_num_is_P = CLOSP1AUX_num_is_PQ "clos_evaluate";;

let CLOSP1AUX_num_is_Q = CLOSP1AUX_num_is_PQ "evaluate_app";;

(* resolve the conditional induction hypotheses (whose conclusion is P- or  *)
(* Q-shaped) with the assumptions                                           *)
let CLOSP1AUX_NUM_COND_IH_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let mentions_eval t =
    can (find_term (fun t -> try let n = fst(dest_const t) in
                                 n = "clos_evaluate" || n = "evaluate_app"
                             with Failure _ -> false)) t in
  let is_cond_ih th =
    not (CLOSP1AUX_num_is_P th) && not (CLOSP1AUX_num_is_Q th) &&
    (let c = snd(strip_forall(concl th)) in
     is_imp c && mentions_eval (rand c) && is_forall (rand c)) in
  let cihs = filter is_cond_ih asms in
  let rec resolve depth th =
    if CLOSP1AUX_num_is_P th || CLOSP1AUX_num_is_Q th then [th]
    else if depth = 0 then [] else
    let rs = mapfilter (fun a -> MATCH_MP th a) asms in
    flat (map (resolve (depth-1)) rs) in
  let res = flat (map (fun th -> resolve 4 (CLOSPROPSAUX_curry_top th)) cihs) in
  let res = filter (fun th -> not (exists (fun a -> aconv (concl a) (concl th)) asms)) res in
  MAP_EVERY ASSUME_TAC res gl;;

(* name the first clos_evaluate of the antecedent of the goal that is not   *)
(* yet the left side of an assumption; the result variable is remembered   *)
let CLOSP1AUX_num_counter = ref 0;;

let CLOSP1AUX_num_last = ref `T`;;

let CLOSP1AUX_NUM_NAME_EVAL_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w in
  let fvs = frees w @ freesl (map (concl o snd) asl) in
  let named = mapfilter (fun (_,th) -> lhs (concl th)) asl in
  let evs = find_terms (fun t -> is_comb t && CLOSPROPSAUX_is_app "clos_evaluate" t &&
                                 not (mem t named) && subset (frees t) fvs) ant in
  let tm = hd evs in
  let rty,sty = (match dest_type (type_of tm) with (_,[a;b]) -> a,b | _ -> failwith "NAME") in
  incr CLOSP1AUX_num_counter;
  let k = string_of_int (!CLOSP1AUX_num_counter) in
  let r = mk_var("rr" ^ k, rty) and s = mk_var("ss" ^ k, sty) in
  CLOSP1AUX_num_last := r;
  (MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN r (X_CHOOSE_THEN s ASSUME_TAC)) THEN
   POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th)) gl;;

(* a type error of the named sub-evaluation is a type error of the whole *)
let CLOSP1AUX_NUM_TE_TAC : tactic = fun (asl,w as gl) ->
  let r = !CLOSP1AUX_num_last in
  let te = mk_eq(r, `Rerr (Rabort Rtype_error):(clos_v list,clos_v)result`) in
  (ASM_CASES_TAC te THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN CLOSP1AUX_NUM_FALSE_TAC;
    ALL_TAC]) gl;;

(* max_app of all states is that of the first source state *)
let CLOSP1AUX_num_maxapp_rws =
  GEN_ALL (CONJUNCT1 (SPEC_ALL CLOSPROPSAUX_max_app_dec_clock)) ::
  filter (fun th -> CLOSPROPSAUX_is_app "clos_state_max_app" (lhs (concl (SPEC_ALL th))))
         (CONJUNCTS clos_state_INFO.ri_accfupds);;

let CLOSP1AUX_num_maxapp_eqs (asl:(string*thm) list) : thm list =
  let fs = [MATCH_MP evaluate_const; MATCH_MP evaluate_app_const;
            (fun th -> CONJUNCT1 (MATCH_MP do_install_const th));
            (fun th -> CONJUNCT1 (CONJUNCT2 (MATCH_MP clos_do_app_const th)));
            (fun th -> SYM (MATCH_MP clos_numberProof_state_rel_max_app th))] in
  let eqs = flat (map (fun (_,th) -> mapfilter (fun f -> f th) fs) asl) in
  let eqs = filter (fun th -> let c = concl th in is_eq c && not (lhs c = rhs c)) eqs in
  eqs @ CLOSP1AUX_num_maxapp_rws;;

let CLOSP1AUX_NUM_MAXAPP_TAC : tactic = fun (asl,w as gl) ->
  let rws = CLOSP1AUX_num_maxapp_eqs asl in
  (RULE_ASSUM_TAC(REWRITE_RULE rws) THEN REWRITE_TAC rws) gl;;

(* the index of a renumbered expression, from an equation of the assumptions *)
let CLOSP1AUX_NUM_RCL_WITNESS_TAC : tactic = fun (asl,w as gl) ->
  let v,bod = dest_exists w in
  let t = find_term (fun t -> (CLOSPROPSAUX_is_app "renumber_code_locs" t ||
                                CLOSPROPSAUX_is_app "renumber_code_locs_list" t) &&
                               length (snd (strip_comb t)) = 2 && lhand t = v) bod in
  let x = rand t in
  let eq = find (fun th -> CLOSP1AUX_num_is_rcl_eq th && rand (lhs (concl th)) = x)
                (map snd asl) in
  EXISTS_TAC (lhand (lhs (concl eq))) gl;;

(* related environments of the evaluation of a body *)
let CLOSP1AUX_NUM_ENV_ALL2_TAC : tactic =
  REPEAT((MATCH_MP_TAC EVERY2_APPEND_suff THEN CONJ_TAC) ORELSE
         MATCH_MP_TAC EVERY2_REVERSE ORELSE MATCH_MP_TAC EVERY2_TAKE ORELSE
         MATCH_MP_TAC EVERY2_DROP) THEN
  ASM_REWRITE_TAC[ALL2; LIST_REL_GENLIST] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[clos_numberProof_v_rel_simp; injectivity "clos_v"; GSYM CONJ_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  TRY CLOSP1AUX_NUM_RCL_WITNESS_TAC THEN ASM_REWRITE_TAC[ALL2; SND];;

(* the index n of the renumbering of the source expressions x: from the    *)
(* equations renumber_code_locs n e = (m,e') or from the goal              *)
let CLOSP1AUX_num_index (asms:term list) (w:term) (x:term) : term =
  let rcl name arg =
    tryfind (fun c -> if is_eq c && CLOSPROPSAUX_is_app name (lhs c) && rand (lhs c) = arg
                      then lhand (lhs c) else failwith "rcl") asms in
  let ingoal name arg =
    lhand (find_term (fun t -> CLOSPROPSAUX_is_app name t &&
                               length (snd (strip_comb t)) = 2 && rand t = arg) w) in
  try (match dest_list x with
         [e] -> (try rcl "renumber_code_locs" e with Failure _ -> ingoal "renumber_code_locs" e)
       | _ -> failwith "list")
  with Failure _ ->
    (try rcl "renumber_code_locs_list" x with Failure _ ->
     try ingoal "renumber_code_locs_list" x with Failure _ -> `0`);;

(* the target expressions of the source expressions x *)
let CLOSP1AUX_num_target (asl:thm list) (n:term) (x:term) : term =
  let rcls = filter CLOSP1AUX_num_is_rcl_eq asl in
  let t = mk_comb(`SND:num#clos_exp list->clos_exp list`,
                  list_mk_comb(`renumber_code_locs_list`, [n; x])) in
  rhs (concl (REWRITE_CONV (CLOSP1AUX_num_renum_AppUnit :: CLOSP1AUX_num_SND_sing :: SND ::
                            rcls) t));;

(* apply an induction hypothesis of P shape with index n to an evaluation  *)
let CLOSP1AUX_num_spec_index (n:term) (ih:thm) : thm =
  let vs,bod = strip_forall (concl ih) in
  let isn v = type_of v = `:num` &&
              can (find_term (fun t -> is_comb t &&
                                       rator t = mk_comb(`renumber_code_locs_list`, v))) bod in
  let rec go th vs =
    match vs with
      [] -> failwith "CLOSP1AUX_num_spec_index"
    | v::rest -> if isn v then SPEC n th else GEN v (go (SPEC v th) rest) in
  go ih vs;;

let CLOSP1AUX_num_apply (asms:thm list) (ih:thm) (ev:thm) (n:term) : thm =
  let th1 = MATCH_MP (REWRITE_RULE[IMP_CONJ] (CLOSP1AUX_num_spec_index n ih)) ev in
  let rec go th =
    if is_imp (snd (strip_forall (concl th)))
    then go (tryfind (fun a -> MATCH_MP th a) asms) else th in
  go th1;;

(* the named evaluation *)
let CLOSP1AUX_num_named (asms:thm list) : thm =
  let r = !CLOSP1AUX_num_last in
  find (fun th -> let c = concl th in is_eq c &&
          CLOSPROPSAUX_is_app "clos_evaluate" (lhs c) &&
          is_pair (rhs c) && fst (dest_pair (rhs c)) = r) asms;;

(* relate the environments of the named evaluation and of its target *)
let CLOSP1AUX_NUM_ENV_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let ev = CLOSP1AUX_num_named asms in
  let x,es = dest_pair (rand (lhs (concl ev))) in
  let e = fst (dest_pair es) in
  let n = CLOSP1AUX_num_index (map concl asms) w x in
  let tg = CLOSP1AUX_num_target asms n x in
  let con = rand w in
  let tev = find_term (fun t -> is_comb t && CLOSPROPSAUX_is_app "clos_evaluate" t &&
                                fst (dest_pair (rand t)) = tg) con in
  let e2 = fst (dest_pair (snd (dest_pair (rand tev)))) in
  let m = rand (find_term (fun t -> is_comb t && rator t = `clos_numberProof_v_rel`) con) in
  let all2 = list_mk_comb(`ALL2:(clos_v->clos_v->bool)->clos_v list->clos_v list->bool`,
                          [mk_comb(`clos_numberProof_v_rel`, m); e; e2]) in
  (if exists (fun th -> concl th = all2) asms then ALL_TAC
   else SUBGOAL_THEN all2 ASSUME_TAC THENL [CLOSP1AUX_NUM_ENV_ALL2_TAC; ALL_TAC]) gl;;

(* apply the induction hypotheses to the named evaluation *)
let CLOSP1AUX_NUM_IH_ON_NEW_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let ev = CLOSP1AUX_num_named asms in
  let x = fst (dest_pair (rand (lhs (concl ev)))) in
  let n = CLOSP1AUX_num_index (map concl asms) w x in
  let ihs = filter CLOSP1AUX_num_is_P asms in
  let rcls = filter CLOSP1AUX_num_is_rcl_eq asms in
  let res = mapfilter (fun ih -> CLOSP1AUX_num_apply asms ih ev n) ihs in
  (if res = [] then NO_TAC
   else STRIP_ASSUME_TAC (REWRITE_RULE (CLOSP1AUX_num_renum_AppUnit :: CLOSP1AUX_num_SND_sing ::
                                        SND :: rcls) (hd res))) gl;;

(* after an induction hypothesis gave evaluate (target) = (res2,t2) and     *)
(* result_rel R1 R2 r res2: rewrite the target with it and split r         *)
let CLOSP1AUX_NUM_SPLIT_RES_TAC : tactic = fun (asl,w as gl) ->
  let rr = find (fun (_,th) -> CLOSPROPSAUX_is_app "result_rel" (concl th) &&
                               is_var (rand (rator (concl th)))) asl in
  let r = rand (rator (concl (snd rr))) in
  let r2 = rand (concl (snd rr)) in
  let tgt = find (fun (_,th) -> is_eq (concl th) && is_pair (rhs (concl th)) &&
                                fst (dest_pair (rhs (concl th))) = r2) asl in
  (REWRITE_TAC[snd tgt] THEN
   CASES_ON r THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> CLOSPROPSAUX_is_app "result_rel" (concl th) &&
                                           rand (concl th) = r2)) THEN
   REWRITE_TAC[result_rel_Rval; result_rel_Rerr1] THEN
   DISCH_THEN(STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
   CASE_REWRITE_TAC[]) gl;;

(* singleton results: clos_evaluate ([e],env,s) = (Rval a,s') gives a = [r] *)
let CLOSP1AUX_NUM_SING_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && CLOSPROPSAUX_is_app "clos_evaluate" (lhs c) &&
       (let r = fst(dest_pair(rhs c)) in
        CLOSPROPSAUX_is_app "Rval" r && is_var (rand r))
    then (STRIP_ASSUME_TAC(MATCH_MP clos_evaluate_SING th) THEN ASSUME_TAC th)
    else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_var (lhs (concl th)) &&
                              is_cons (rhs (concl th)) then SUBST_ALL_TAC th else NO_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if CLOSPROPSAUX_is_app "ALL2" c && is_cons (lhand c) &&
       (is_var (rand c) || is_cons (rand c))
    then MP_TAC th THEN REWRITE_TAC[LIST_REL_CONS1; LIST_REL_NIL; ALL2] THEN STRIP_TAC THEN
         RVEQ_TAC
    else NO_TAC));;

(* the end of a case: the results are equal or related *)
let CLOSP1AUX_NUM_FIN_TAC : tactic =
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  (fun (asl,w as gl) ->
     let isne c = is_neg c && is_eq (dest_neg c) && lhs (dest_neg c) = rhs (dest_neg c) in
     if exists (fun (_,th) -> isne (concl th)) asl
     then FIRST_ASSUM(fun th -> if isne (concl th)
                                then CONTR_TAC (MP (NOT_ELIM th) (REFL (lhs (dest_neg (concl th)))))
                                else NO_TAC) gl
     else ALL_TAC gl) THEN
  REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC] THEN CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  CLOSP1AUX_NUM_SING_TAC THEN
  ASM_REWRITE_TAC[result_rel_def; exc_rel_def; injectivity "result"; distinctness "result";
                  HD; ALL2];;

(* split a related pair of errors exc_rel R a e' (a a variable) *)
let CLOSP1AUX_NUM_SPLIT_EXC_TAC : tactic = fun (asl,w as gl) ->
  let er = find (fun (_,th) -> CLOSPROPSAUX_is_app "exc_rel" (concl th) &&
                               is_var (rand (rator (concl th)))) asl in
  let a = rand (rator (concl (snd er))) and e2 = rand (concl (snd er)) in
  (CASES_ON a THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> CLOSPROPSAUX_is_app "exc_rel" (concl th) &&
                                           rand (concl th) = e2)) THEN
   REWRITE_TAC[exc_rel_raise1; exc_rel_type_error1] THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN CASE_REWRITE_TAC[]) gl;;

(* related states with decreased clocks *)
let CLOSP1AUX_num_state_rel_dec_clock = prove
 (`!(s:(num#C,FFI)clos_state) t k.
     clos_numberProof_state_rel s t ==>
     clos_numberProof_state_rel (clos_dec_clock k s) (clos_dec_clock k t)`,
  REWRITE_TAC[clos_numberProof_state_rel_def; clos_dec_clock_def;
              clos_state_INFO.ri_accfupds; K_THM] THEN SIMP_TAC[]);;

let CLOSP1AUX_NUM_DEC_CLOCK_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w in
  let dcs = find_terms (fun t -> is_comb t && CLOSPROPSAUX_is_app "clos_dec_clock" t &&
                                 length (snd (strip_comb t)) = 2) ant in
  let srs = filter (fun th -> CLOSPROPSAUX_is_app "clos_numberProof_state_rel" (concl th))
                   (map snd asl) in
  let ths = flat (map (fun dc ->
     let [k;x] = snd (strip_comb dc) in
     mapfilter (fun sr -> if lhand (concl sr) = x
                          then SPEC k (MATCH_MP CLOSP1AUX_num_state_rel_dec_clock sr)
                          else failwith "DEC") srs) dcs) in
  let ths = filter (fun th -> not (exists (fun (_,a) -> concl a = concl th) asl)) ths in
  MAP_EVERY ASSUME_TAC ths gl;;

let CLOSP1AUX_NUM_STEP_TAC : tactic =
  CLOSP1AUX_NUM_COND_IH_TAC THEN CLOSP1AUX_NUM_DEC_CLOCK_TAC THEN
  CLOSP1AUX_NUM_NAME_EVAL_TAC THEN CLOSP1AUX_NUM_TE_TAC THEN CLOSP1AUX_NUM_MAXAPP_TAC THEN
  CLOSP1AUX_NUM_ENV_TAC THEN CLOSP1AUX_NUM_IH_ON_NEW_TAC THEN CLOSP1AUX_NUM_SPLIT_RES_TAC;;

(* split the hypothesis ~contains_App_SOME m [e] *)
let CLOSP1AUX_NUM_CAS_TAC : tactic =
  FIRST_X_ASSUM(fun th -> if is_neg (concl th) &&
                             CLOSPROPSAUX_is_app "contains_App_SOME" (dest_neg (concl th))
                          then MP_TAC th else NO_TAC) THEN
  REWRITE_TAC[contains_App_SOME_def; DE_MORGAN_THM] THEN STRIP_TAC;;

(* unfold the renumbering of the target and the evaluation of both sides *)
let CLOSP1AUX_NUM_UNFOLD_TAC : tactic =
  REWRITE_TAC[CLOSP1AUX_num_SND_sing; renumber_code_locs_def] THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[SND] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
                                CLOSPROPSAUX_is_app "clos_evaluate" (lhs (concl th)))) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def];;

let CLOSP1AUX_num_nil = prove
 (el 0 CLOSP1AUX_num_cases,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_evaluate_def; renumber_code_locs_def; PAIR_EQ; SND] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`Rval []:(clos_v list,clos_v)result`; `t1:(C,FFI)clos_state`] THEN
  ASM_REWRITE_TAC[clos_evaluate_def; result_rel_def; ALL2]);;

let CLOSP1AUX_num_cons = prove
 (el 1 CLOSP1AUX_num_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_NUM_CAS_TAC THEN
  ONCE_REWRITE_TAC[renumber_code_locs_def] THEN REPEAT PAIRARG_TAC THEN REWRITE_TAC[SND] THEN
  ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
                                CLOSPROPSAUX_is_app "clos_evaluate" (lhs (concl th)))) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN
  REPEAT CLOSP1AUX_NUM_STEP_TAC THEN CLOSP1AUX_NUM_FIN_TAC);;

let CLOSP1AUX_num_var = prove
 (el 2 CLOSP1AUX_num_cases,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_NUM_UNFOLD_TAC THEN
  CLOSP1AUX_NUM_LENGTHS_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CLOSP1AUX_NUM_FIN_TAC THEN ASM_MESON_TAC[LIST_REL_EL_EQN]);;

(* local helpers: related singleton results agree on being a boolean *)
let CLOSP1AUX_num_Boolv_HD = prove
 (`!m a v' b. ALL2 (clos_numberProof_v_rel m) a v' /\ ~(a = []) ==>
              (clos_Boolv b = HD v' <=> clos_Boolv b = HD a)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; LIST_REL_CONS1] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[HD] THEN
  EQ_TAC THEN DISCH_THEN(ASSUME_TAC o SYM) THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_numberProof_v_rel_Boolv]) THEN ASM_REWRITE_TAC[]);;

(* rewrite the boolean tests on the head of a target result to the source *)
let CLOSP1AUX_NUM_BOOLV_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let nes = mapfilter (MATCH_MP CLOSPROPSAUX_eval_SING_NIL) asms in
  let ths = flat (map (fun ne -> mapfilter (fun a ->
               MATCH_MP CLOSP1AUX_num_Boolv_HD (CONJ a ne)) asms) nes) in
  REWRITE_TAC ths gl;;

let CLOSP1AUX_num_if = prove
 (el 3 CLOSP1AUX_num_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_NUM_CAS_TAC THEN CLOSP1AUX_NUM_UNFOLD_TAC THEN
  CLOSP1AUX_NUM_STEP_TAC THENL [ALL_TAC; CLOSP1AUX_NUM_FIN_TAC] THEN
  CLOSP1AUX_NUM_BOOLV_TAC THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[]) THEN
  REPEAT CLOSP1AUX_NUM_STEP_TAC THEN CLOSP1AUX_NUM_FIN_TAC);;

let CLOSP1AUX_num_let = prove
 (el 4 CLOSP1AUX_num_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_NUM_CAS_TAC THEN CLOSP1AUX_NUM_UNFOLD_TAC THEN
  CLOSP1AUX_NUM_STEP_TAC THENL [ALL_TAC; CLOSP1AUX_NUM_FIN_TAC] THEN
  REPEAT CLOSP1AUX_NUM_STEP_TAC THEN CLOSP1AUX_NUM_FIN_TAC);;

let CLOSP1AUX_num_raise = prove
 (el 5 CLOSP1AUX_num_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_NUM_CAS_TAC THEN CLOSP1AUX_NUM_UNFOLD_TAC THEN
  REPEAT CLOSP1AUX_NUM_STEP_TAC THEN CLOSP1AUX_NUM_FIN_TAC);;

let CLOSP1AUX_num_handle = prove
 (el 6 CLOSP1AUX_num_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_NUM_CAS_TAC THEN CLOSP1AUX_NUM_UNFOLD_TAC THEN
  CLOSP1AUX_NUM_STEP_TAC THENL [CLOSP1AUX_NUM_FIN_TAC; ALL_TAC] THEN
  CLOSP1AUX_NUM_SPLIT_EXC_TAC THENL [ALL_TAC; CLOSP1AUX_NUM_FIN_TAC] THEN
  REPEAT CLOSP1AUX_NUM_STEP_TAC THEN CLOSP1AUX_NUM_FIN_TAC);;

(* local helpers for the Op case: contains_App_SOME of an operation; the    *)
(* programs installed are not empty                                         *)
let CLOSP1AUX_num_cas_Op = prove
 (`!m t op xs. contains_App_SOME m [clos_Op t op xs] <=>
               contains_App_SOME m xs \/ (op = clos_ThunkOp ForceThunk /\ m < 1)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC clos_op_INDUCT THEN
  REWRITE_TAC[contains_App_SOME_def; distinctness "clos_op"; injectivity "clos_op"] THEN
  GEN_TAC THEN CASES_ON `a:thunk_op` THEN
  REWRITE_TAC[contains_App_SOME_def; distinctness "thunk_op"] THEN MESON_TAC[]);;

let CLOSP1AUX_num_do_install_nonnil = prove
 (`!vs (s:(C,FFI)clos_state) es t. clos_do_install vs s = (Rval es,t) ==> ~(es = [])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_install_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[]);;

(* local helpers for the Install case: the constant installed first; the  *)
(* last value of related lists                                             *)
let CLOSP1AUX_num_eval_const = prove
 (`!t i env (s:(C,FFI)clos_state).
     clos_evaluate ([clos_Op t (IntOp (clos_Const i)) []],env,s) = (Rval [clos_Number i],s)`,
  REWRITE_TAC[clos_evaluate_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; clos_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_do_int_app_def] THEN CASE_REWRITE_TAC[]);;

let CLOSP1AUX_num_LAST_CONS = prove
 (`!(R:clos_v->clos_v->bool) l1 l2 x.
     ALL2 R l1 l2 /\ ~(l1 = []) ==> R (LAST l1) (LAST (CONS x l2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(l2:clos_v list = [])` ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_REL_LENGTH; LENGTH_EQ_NIL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LAST] THEN MATCH_MP_TAC LIST_REL_LAST THEN ASM_REWRITE_TAC[]);;

(* the do_app of the antecedent and the consequent, related by do_app_lemma *)
(* split the pair p of an assumption tm = Rval p *)
let CLOSP1AUX_NUM_SPLIT_PAIR_TAC (tm:term) : tactic = fun (asl,w as gl) ->
  let th = snd (find (fun (_,th) -> is_eq (concl th) && lhs (concl th) = tm) asl) in
  let r = rhs (concl th) in
  if CLOSPROPSAUX_is_app "Rval" r && is_var (rand r) && is_type (type_of (rand r)) &&
     fst (dest_type (type_of (rand r))) = "prod"
  then (CASES_ON (rand r) THEN CASE_REWRITE_TAC[]) gl
  else ALL_TAC gl;;

let CLOSP1AUX_NUM_DO_APP_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w and con = rand w in
  let is_da t = is_comb t && CLOSPROPSAUX_is_app "clos_do_app" t &&
                length (snd (strip_comb t)) = 3 in
  let da = find_term is_da ant in
  let [op; xs; s] = snd (strip_comb da) in
  let db = find_term (fun t -> is_da t && hd (snd (strip_comb t)) = op) con in
  let [_; ys; t] = snd (strip_comb db) in
  let th = REWRITE_RULE (CLOSP1AUX_num_maxapp_eqs asl)
             (INST [s,`s:(num#C,FFI)clos_state`; t,`t:(C,FFI)clos_state`;
                    xs,`xs:clos_v list`; ys,`ys:clos_v list`; op,`opp:clos_op`]
                   clos_numberProof_do_app_lemma) in
  (MP_TAC th THEN ANTS_TAC THENL [ASM_SIMP_TAC[EVERY2_REVERSE]; ALL_TAC] THEN
   CASES_ON da THEN CASE_REWRITE_TAC[] THEN
   CLOSP1AUX_NUM_SPLIT_PAIR_TAC da THEN
   DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) gl;;

(* the dest_thunk of the antecedent and the consequent                      *)
let CLOSP1AUX_NUM_DEST_THUNK_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w and con = rand w in
  let is_dt t = is_comb t && CLOSPROPSAUX_is_app "clos_dest_thunk" t &&
                length (snd (strip_comb t)) = 2 in
  let da = find_term is_dt ant in
  let [xs; rs] = snd (strip_comb da) in
  let db = find_term is_dt con in
  let [ys; rt] = snd (strip_comb db) in
  let s = rand rs and t = rand rt in
  let m = rand (find_term (fun t -> is_comb t && rator t = `clos_numberProof_v_rel`) con) in
  let sr = vsubst [m,`M:num`]
    `\(r:(num#C,FFI)clos_state) (t:(C,FFI)clos_state).
        clos_state_max_app r = M /\ clos_numberProof_state_rel r t` in
  let th = ISPECL [mk_comb(`clos_numberProof_v_rel`, m); sr; s; t; xs; ys]
                  CLOSPROPSAUX_dest_thunk_rel in
  (MP_TAC th THEN
   ANTS_TAC THENL
    [REWRITE_TAC[GEN_ALL clos_numberProof_simple_val_rel;
                 GEN_ALL clos_numberProof_simple_state_rel] THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC(CLOSP1AUX_num_maxapp_eqs asl) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   CASES_ON db THEN CASE_REWRITE_TAC[] THEN
   DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) gl;;

(* the arguments of a forced thunk are a single reference *)
let CLOSP1AUX_NUM_THUNK_ARGS_TAC : tactic = fun (asl,w as gl) ->
  let dt = snd (find (fun (_,th) -> is_eq (concl th) &&
                       CLOSPROPSAUX_is_app "clos_dest_thunk" (lhs (concl th)) &&
                       CLOSPROPSAUX_is_app "clos_IsThunk" (rhs (concl th)) &&
                       is_var (lhand (lhs (concl th)))) asl) in
  let xs = lhand (lhs (concl dt)) in
  let all2 = snd (find (fun (_,th) -> CLOSPROPSAUX_is_app "ALL2" (concl th) &&
                         lhand (concl th) = xs) asl) in
  let ys = rand (concl all2) in
  let vr = rand (rator (rator (concl all2))) in
  (MP_TAC(ISPECL [vr; xs; ys] CLOSPROPSAUX_vr_RefPtr_shape) THEN
   ASM_REWRITE_TAC[GEN_ALL clos_numberProof_simple_val_rel] THEN STRIP_TAC THENL
   [REPEAT(FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_var (lhs (concl th)) &&
             (lhs (concl th) = xs || lhs (concl th) = ys) then SUBST_ALL_TAC th else NO_TAC));
    MP_TAC(SPECL [xs; rand (lhs (concl dt))] CLOSSEMAUX_dest_thunk_NotThunk) THEN
    ASM_REWRITE_TAC[distinctness "clos_dest_thunk_ret"]]) gl;;

(* the update_thunk of the antecedent and the consequent                    *)
let CLOSP1AUX_NUM_UPDATE_THUNK_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w and con = rand w in
  let is_ut t = is_comb t && CLOSPROPSAUX_is_app "clos_update_thunk" t &&
                length (snd (strip_comb t)) = 3 in
  let ua = find_term is_ut ant in
  let [xs; rs; vs] = snd (strip_comb ua) in
  let ub = find_term is_ut con in
  let [_; rt; ws] = snd (strip_comb ub) in
  let s1 = rand rs and s2 = rand rt in
  let [rp] = dest_list xs in
  let [b; ptr] = snd (strip_comb rp) in
  let th0 = REWRITE_RULE (CLOSP1AUX_num_maxapp_eqs asl)
     (INST [s1,`s1:(num#C,FFI)clos_state`; s2,`s2:(C,FFI)clos_state`; vs,`vs:clos_v list`;
            ws,`ys:clos_v list`; b,`v:bool`; ptr,`ptr:num`]
           clos_numberProof_rel_update_thunk) in
  (CASES_ON ua THEN CASE_REWRITE_TAC[] THENL
   [CLOSP1AUX_NUM_FIN_TAC;
    (fun (asl,w as gl) ->
       let eq = snd (find (fun (_,th) -> is_eq (concl th) && lhs (concl th) = ua) asl) in
       let th1 = INST [rand (rhs (concl eq)), `refs1:(num,(clos_v)clos_ref)fmap`] th0 in
       (MP_TAC th1 THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) gl)]) gl;;

(* a local helper: the code installed by clos_number_compile_inc *)
let CLOSP1AUX_num_SND_compile_inc = prove
 (`!n xs. SND (clos_number_compile_inc n xs) =
          CONS (clos_Op backend_common_None (IntOp (clos_Const (&n))) [])
               (SND (renumber_code_locs_list (make_even (n + MAX (LENGTH xs) 1)) xs))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_number_compile_inc_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  MP_TAC(ISPEC `renumber_code_locs_list (make_even (n + MAX (LENGTH (xs:clos_exp list)) 1)) xs`
               PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[SND]);;

(* the source equation clos_do_install xs s = (r,s') named by DO_INSTALL *)
let CLOSP1AUX_num_di_eq (asl:(string*thm) list) : thm =
  snd (find (fun (_,th) -> let c = concl th in
               is_eq c && CLOSPROPSAUX_is_app "clos_do_install" (lhs c) &&
               type_of (rand (lhs c)) = `:(num#C,FFI)clos_state` &&
               is_pair (rhs c) && is_var (snd (dest_pair (rhs c)))) asl);;

(* the do_install of the antecedent and the consequent, related by          *)
(* do_install; the source result is named and split                         *)
let CLOSP1AUX_NUM_DO_INSTALL_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w and con = rand w in
  let is_di t = is_comb t && CLOSPROPSAUX_is_app "clos_do_install" t &&
                length (snd (strip_comb t)) = 2 in
  let da = find_term is_di ant in
  let [xs; s] = snd (strip_comb da) in
  let db = find_term is_di con in
  let [ys; t] = snd (strip_comb db) in
  let th = REWRITE_RULE (FORALL_SIMP :: CLOSP1AUX_num_maxapp_eqs asl)
     (INST [s,`s1:(num#C,FFI)clos_state`; t,`s2:(C,FFI)clos_state`; xs,`x1:clos_v list`;
            ys,`x2:clos_v list`] do_install) in
  let rty,sty = (match dest_type (type_of da) with (_,[a;b]) -> a,b | _ -> failwith "DI") in
  incr CLOSP1AUX_num_counter;
  let k = string_of_int (!CLOSP1AUX_num_counter) in
  let r = mk_var("rr" ^ k, rty) and s' = mk_var("ss" ^ k, sty) in
  (MP_TAC th THEN ANTS_TAC THENL [ASM_SIMP_TAC[EVERY2_REVERSE]; ALL_TAC] THEN
   DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
   MP_TAC(ISPEC da PAIR_SURJECTIVE) THEN
   DISCH_THEN(X_CHOOSE_THEN r (X_CHOOSE_THEN s' ASSUME_TAC)) THEN
   POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
   CASES_ON r THEN CASE_REWRITE_TAC[]) gl;;

(* resolve the do_install facts with the named equation; rewrite the target *)
let CLOSP1AUX_NUM_DI_RES_TAC : tactic =
  (fun (asl,w as gl) ->
     let eq = CLOSP1AUX_num_di_eq asl in
     FIRST_X_ASSUM(fun th -> STRIP_ASSUME_TAC (MATCH_MP th eq)) gl) THEN
  (fun (asl,w as gl) ->
     let teq = snd (find (fun (_,th) -> let c = concl th in
                 is_eq c && CLOSPROPSAUX_is_app "clos_do_install" (lhs c) &&
                 type_of (rand (lhs c)) = `:(C,FFI)clos_state`) asl) in
     REWRITE_TAC[teq] gl) THEN
  CASE_REWRITE_TAC[];;

(* the last value of the evaluation of installed code *)
let CLOSP1AUX_NUM_LAST_TAC : tactic =
  MATCH_MP_TAC CLOSP1AUX_num_LAST_CONS THEN ASM_REWRITE_TAC[] THEN
  (fun (asl,w as gl) ->
     let asms = map snd asl in
     let lens = mapfilter (MATCH_MP clos_evaluate_IMP_LENGTH) asms in
     let nes = mapfilter (MATCH_MP CLOSP1AUX_num_do_install_nonnil) asms in
     (MAP_EVERY MP_TAC (lens @ nes) THEN ASM_MESON_TAC[LENGTH_EQ_NIL]) gl);;

(* an installation: its programs are evaluated *)
let CLOSP1AUX_NUM_INSTALL_VAL_TAC : tactic =
  CLOSP1AUX_NUM_DI_RES_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_var (lhs (concl th)) &&
                             CLOSPROPSAUX_is_app "SND" (rhs (concl th))
                          then SUBST_ALL_TAC th else NO_TAC) THEN
  REWRITE_TAC[CLOSP1AUX_num_SND_compile_inc] THEN
  ONCE_REWRITE_TAC[clos_evaluate_CONS] THEN REWRITE_TAC[CLOSP1AUX_num_eval_const] THEN
  CASE_REWRITE_TAC[] THEN CLOSP1AUX_NUM_MAXAPP_TAC THEN
  CLOSP1AUX_NUM_STEP_TAC THENL
   [CLOSP1AUX_NUM_FIN_TAC THEN CLOSP1AUX_NUM_LAST_TAC; CLOSP1AUX_NUM_FIN_TAC];;

(* an installation error: a timeout (do_install raises no exception and no *)
(* FFI error; a type error contradicts the hypothesis)                     *)
let CLOSP1AUX_NUM_INSTALL_ERR_TAC : tactic = fun (asl,w as gl) ->
  let e = rand (fst (dest_pair (rhs (concl (CLOSP1AUX_num_di_eq asl))))) in
  (CASES_ON e THENL
   [(fun (asl,w as gl) ->
       let eq = CLOSP1AUX_num_di_eq asl in
       let v = rand (rand (fst (dest_pair (rhs (concl eq))))) in
       (MP_TAC (SPEC v (MATCH_MP do_install_not_Rraise eq)) THEN REWRITE_TAC[]) gl);
    (fun (asl,w as gl) ->
       let eq = CLOSP1AUX_num_di_eq asl in
       let ab = rand (rand (fst (dest_pair (rhs (concl eq))))) in
       (CASES_ON ab THENL
        [CLOSP1AUX_NUM_FIN_TAC;
         CLOSP1AUX_NUM_DI_RES_TAC THEN CLOSP1AUX_NUM_FIN_TAC;
         (fun (asl,w as gl) ->
            let eq = CLOSP1AUX_num_di_eq asl in
            let f = rand (rand (rand (fst (dest_pair (rhs (concl eq)))))) in
            (MP_TAC (SPEC f (MATCH_MP do_install_not_Rffi_error eq)) THEN REWRITE_TAC[]) gl)])
       gl)]) gl;;

(* a local helper: contains_App_SOME of an operation, negated *)
let CLOSP1AUX_num_not_cas_Op = prove
 (`!m t op xs. ~contains_App_SOME m [clos_Op t op xs] <=>
               ~contains_App_SOME m xs /\ (op = clos_ThunkOp ForceThunk ==> ~(m < 1))`,
  REWRITE_TAC[CLOSP1AUX_num_cas_Op] THEN MESON_TAC[]);;

(* the forced thunk: the hypothesis on its application *)
let CLOSP1AUX_NUM_APPUNIT_CAS_TAC : tactic = fun (asl,w as gl) ->
  let m = rand (find_term (fun t -> is_comb t && rator t = `clos_numberProof_v_rel`) (rand w)) in
  let g = mk_neg (list_mk_comb(`contains_App_SOME`,
                   [m; `[clos_AppUnit (clos_Var backend_common_None 0)]`])) in
  (SUBGOAL_THEN g ASSUME_TAC THENL
   [REWRITE_TAC[clos_AppUnit_def; contains_App_SOME_def; IS_SOME_DEF; LENGTH] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[];
    ALL_TAC]) gl;;

let CLOSP1AUX_NUM_MODE_CASES_TAC : tactic = fun (asl,w as gl) ->
  let v = find_term (fun t -> is_var t && type_of t = `:thunk_mode`) w in
  (CASES_ON v THEN CASE_REWRITE_TAC[]) gl;;

let CLOSP1AUX_num_op = prove
 (el 7 CLOSP1AUX_num_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
                  CLOSPROPSAUX_is_app "contains_App_SOME" (dest_neg (concl th)))) THEN
  REWRITE_TAC[CLOSP1AUX_num_not_cas_Op] THEN STRIP_TAC THEN
  CLOSP1AUX_NUM_UNFOLD_TAC THEN
  CLOSP1AUX_NUM_STEP_TAC THENL [ALL_TAC; CLOSP1AUX_NUM_FIN_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [CLOSP1AUX_NUM_DO_INSTALL_TAC THENL
     [CLOSP1AUX_NUM_INSTALL_VAL_TAC; CLOSP1AUX_NUM_INSTALL_ERR_TAC];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [CLOSP1AUX_NUM_DEST_THUNK_TAC THEN TRY(CLOSP1AUX_NUM_FIN_TAC THEN NO_TAC) THEN
    CLOSP1AUX_NUM_MODE_CASES_TAC THENL [CLOSP1AUX_NUM_FIN_TAC; ALL_TAC] THEN
    CLOSP1AUX_NUM_THUNK_ARGS_TAC THEN CLOSP1AUX_NUM_APPUNIT_CAS_TAC THEN
    CLOSP1AUX_NUM_STEP_TAC THENL
     [CLOSP1AUX_NUM_UPDATE_THUNK_TAC THEN CLOSP1AUX_NUM_FIN_TAC; CLOSP1AUX_NUM_FIN_TAC];
    CLOSP1AUX_NUM_DO_APP_TAC THEN CLOSP1AUX_NUM_FIN_TAC]);;

(* local helpers for the Fn and Letrec cases: lookup_vars of related       *)
(* environments; a condition on the arities of renumbered functions        *)
let CLOSP1AUX_num_lookup_vars_rel = prove
 (CASE_TERM `!m (vs:num list) (env1:clos_v list) (env2:clos_v list).
     ALL2 (clos_numberProof_v_rel m) env1 env2 ==>
     match lookup_vars vs env1 with
       NONE -> lookup_vars vs env2 = NONE
     | SOME l1 -> ?l2. ALL2 (clos_numberProof_v_rel m) l1 l2 /\ lookup_vars vs env2 = SOME l2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `vs:num list` o MATCH_MP (GEN_ALL lookup_vars_NONE_related_env)) THEN
  CASES_ON `lookup_vars (vs:num list) (env1:clos_v list)` THEN
  CASES_ON `lookup_vars (vs:num list) (env2:clos_v list)` THEN
  CASE_REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  ASM_MESON_TAC[GEN_ALL lookup_vars_SOME_related_env]);;

let CLOSP1AUX_num_ALL_ZIP_FST = prove
 (`!(f:num#clos_exp->bool) (fns:(num#clos_exp)list) fns'.
     LENGTH fns = LENGTH fns' /\ (!a e1 e2. f (a,e1) <=> f (a,e2)) ==>
     (ALL f (ZIP (MAP FST fns) fns') <=> ALL f fns)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; MAP; ZIP; ALL] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(f:num#clos_exp->bool) (FST h,h') <=> f h` SUBST1_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM PAIR] THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

(* the lookup_vars of the antecedent and the consequent *)
let CLOSP1AUX_NUM_LOOKUP_VARS_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w and con = rand w in
  let is_lv t = is_comb t && CLOSPROPSAUX_is_app "lookup_vars" t &&
                length (snd (strip_comb t)) = 2 in
  let la = find_term is_lv ant in
  let [vs; e1] = snd (strip_comb la) in
  let lb = find_term (fun t -> is_lv t && lhand t = vs) con in
  let e2 = rand lb in
  let m = rand (find_term (fun t -> is_comb t && rator t = `clos_numberProof_v_rel`) con) in
  (MP_TAC(ISPECL [m; vs; e1; e2] CLOSP1AUX_num_lookup_vars_rel) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   CASES_ON la THEN CASE_REWRITE_TAC[] THEN
   DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) gl;;

(* a related closure value *)
let CLOSP1AUX_NUM_CLOSURE_TAC : tactic =
  REWRITE_TAC[clos_numberProof_v_rel_simp; injectivity "clos_v"; GSYM CONJ_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV UNWIND_CONV) THEN
  CLOSP1AUX_NUM_RCL_WITNESS_TAC THEN ASM_REWRITE_TAC[SND; ALL2];;

(* the condition on the arities of the renumbered functions of a Letrec *)
let CLOSP1AUX_NUM_ALL_ZIP_TAC : tactic = fun (asl,w as gl) ->
  let t = find_term (fun t -> CLOSPROPSAUX_is_app "ALL" t && is_comb t &&
                              CLOSPROPSAUX_is_app "ZIP" (rand t)) w in
  let f = lhand t and z = rand t in
  let fns = rand (lhand z) and fns' = rand z in
  (MP_TAC(ISPECL [f; fns; fns'] CLOSP1AUX_num_ALL_ZIP_FST) THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
     REPEAT GEN_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN CASE_REWRITE_TAC[];
     DISCH_THEN SUBST1_TAC]) gl;;

let CLOSP1AUX_num_fn = prove
 (el 8 CLOSP1AUX_num_cases,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_NUM_CAS_TAC THEN CLOSP1AUX_NUM_UNFOLD_TAC THEN
  CLOSP1AUX_NUM_MAXAPP_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL [ALL_TAC; CLOSP1AUX_NUM_FIN_TAC] THEN
  CASES_ON `vsopt:(num list)option` THEN CASE_REWRITE_TAC[] THEN
  TRY CLOSP1AUX_NUM_LOOKUP_VARS_TAC THEN CLOSP1AUX_NUM_FIN_TAC THEN CLOSP1AUX_NUM_CLOSURE_TAC);;

let CLOSP1AUX_num_letrec = prove
 (el 9 CLOSP1AUX_num_cases,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CLOSP1AUX_NUM_CAS_TAC THEN CLOSP1AUX_NUM_UNFOLD_TAC THEN CLOSP1AUX_NUM_MAXAPP_TAC THEN
  CLOSP1AUX_NUM_LEN_TAC THEN CLOSP1AUX_NUM_ALL_ZIP_TAC THEN
  FIRST_ASSUM(fun th -> if is_eq (concl th) && CLOSPROPSAUX_is_app "LENGTH" (lhs (concl th))
                        then SIMP_TAC[LENGTH_ZIP; LENGTH_MAP; th] THEN REWRITE_TAC[SYM th]
                        else NO_TAC) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL [ALL_TAC; CLOSP1AUX_NUM_FIN_TAC] THEN
  CASES_ON `namesopt:(num list)option` THEN CASE_REWRITE_TAC[] THENL
   [REPEAT CLOSP1AUX_NUM_STEP_TAC THEN CLOSP1AUX_NUM_FIN_TAC;
    CLOSP1AUX_NUM_LOOKUP_VARS_TAC THEN REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN
    TRY(CLOSP1AUX_NUM_FIN_TAC THEN NO_TAC) THEN
    REPEAT CLOSP1AUX_NUM_STEP_TAC THEN CLOSP1AUX_NUM_FIN_TAC]);;

(* the evaluate_app of the antecedent, by the Q-shaped hypothesis *)
let CLOSP1AUX_NUM_APP_Q_TAC : tactic =
  CLOSP1AUX_NUM_SING_TAC THEN REWRITE_TAC[HD] THEN CASE_REWRITE_TAC[] THEN
  CLOSP1AUX_NUM_COND_IH_TAC THEN CLOSP1AUX_NUM_MAXAPP_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> if CLOSP1AUX_num_is_Q th then MATCH_MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[HD];;

let CLOSP1AUX_num_app = prove
 (el 10 CLOSP1AUX_num_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_NUM_CAS_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o REWRITE_RULE[NOT_IS_SOME_EQ_NONE] o
                check (fun th -> is_neg (concl th) &&
                                 CLOSPROPSAUX_is_app "IS_SOME" (dest_neg (concl th)))) THEN
  CLOSP1AUX_NUM_UNFOLD_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP renumber_code_locs_list_length th]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL [ALL_TAC; CLOSP1AUX_NUM_FIN_TAC] THEN
  REPEAT CLOSP1AUX_NUM_STEP_TAC THEN TRY(CLOSP1AUX_NUM_FIN_TAC THEN NO_TAC) THEN
  CLOSP1AUX_NUM_APP_Q_TAC);;

let CLOSP1AUX_num_tick = prove
 (el 11 CLOSP1AUX_num_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_NUM_CAS_TAC THEN CLOSP1AUX_NUM_UNFOLD_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM (MATCH_MP clos_numberProof_state_rel_clock th)]) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL [CLOSP1AUX_NUM_FIN_TAC; ALL_TAC] THEN
  REPEAT CLOSP1AUX_NUM_STEP_TAC THEN CLOSP1AUX_NUM_FIN_TAC);;

let CLOSP1AUX_num_call = prove
 (el 12 CLOSP1AUX_num_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CLOSP1AUX_NUM_CAS_TAC THEN CLOSP1AUX_NUM_UNFOLD_TAC THEN
  CLOSP1AUX_NUM_STEP_TAC THENL [ALL_TAC; CLOSP1AUX_NUM_FIN_TAC] THEN
  (fun (asl,w as gl) ->
     REWRITE_TAC (mapfilter (fun (_,th) -> CONJUNCT1 (MATCH_MP state_rel_code th)) asl) gl) THEN
  REWRITE_TAC[clos_find_code_def; FLOOKUP_EMPTY] THEN CASE_REWRITE_TAC[] THEN
  CLOSP1AUX_NUM_FIN_TAC);;

let CLOSP1AUX_num_app_nil = prove
 (el 13 CLOSP1AUX_num_cases,
  REPEAT GEN_TAC THEN REWRITE_TAC[evaluate_app_NIL; LIST_REL_NIL; PAIR_EQ] THEN STRIP_TAC THEN
  RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`Rval [f']:(clos_v list,clos_v)result`; `t1:(C,FFI)clos_state`] THEN
  ASM_REWRITE_TAC[evaluate_app_NIL; result_rel_def; ALL2]);;

(* local helpers for the application of closures: clock updates of related *)
(* states; the dest_closure of the antecedent and the consequent           *)
let CLOSP1AUX_num_state_rel_clock_upd = prove
 (`!(s:(num#C,FFI)clos_state) t n.
     clos_numberProof_state_rel s t ==>
     clos_numberProof_state_rel (clos_state_clock_fupd (K n) s) (clos_state_clock_fupd (K n) t) /\
     clos_numberProof_state_rel (clos_dec_clock n s) (clos_dec_clock n t)`,
  SIMP_TAC[clos_numberProof_state_rel_with_clock; CLOSP1AUX_num_state_rel_dec_clock]);;

let CLOSP1AUX_NUM_STATE_CLOCK_TAC : tactic =
  FIRST_ASSUM(fun th -> if CLOSPROPSAUX_is_app "clos_numberProof_state_rel" (concl th)
                        then MP_TAC (GEN `n:num` (MATCH_MP CLOSP1AUX_num_state_rel_clock_upd th))
                        else NO_TAC) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC;;

let CLOSP1AUX_NUM_DEST_CLOSURE_TAC : tactic = fun (asl,w as gl) ->
  let ant = lhand w and con = rand w in
  let is_dc t = is_comb t && CLOSPROPSAUX_is_app "dest_closure" t &&
                length (snd (strip_comb t)) = 4 in
  let da = find_term is_dc ant and db = find_term is_dc con in
  let [m; _; f1; a1] = snd (strip_comb da) and [_; _; f2; a2] = snd (strip_comb db) in
  let th = INST [m,`max_app:num`; f1,`f:clos_v`; f2,`f':clos_v`; a1,`args:clos_v list`;
                 a2,`args':clos_v list`] CLOSP1AUX_num_dest_closure_NONE_Partial in
  (MP_TAC th THEN ANTS_TAC THENL [ASM_REWRITE_TAC[ALL2]; ALL_TAC] THEN
   CASES_ON da THEN CASE_REWRITE_TAC[] THENL
   [DISCH_TAC THEN CLOSP1AUX_NUM_FIN_TAC; ALL_TAC]) gl;;

(* the Full_app case: the target closure by dest_closure_v_rel_full *)
let CLOSP1AUX_NUM_FULL_APP_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let dc = find (fun th -> let c = concl th in is_eq c &&
                   CLOSPROPSAUX_is_app "dest_closure" (lhs c) &&
                   CLOSPROPSAUX_is_app "SOME" (rhs c) &&
                   CLOSPROPSAUX_is_app "Full_app" (rand (rhs c))) asms in
  let [m; _; f1; a1] = snd (strip_comb (lhs (concl dc))) in
  let vr = find (fun th -> let c = concl th in
                   CLOSPROPSAUX_is_app "clos_numberProof_v_rel" c && lhand c = f1) asms in
  let a2 = find (fun th -> let c = concl th in
                   CLOSPROPSAUX_is_app "ALL2" c && lhand c = a1) asms in
  let th = MATCH_MP (REWRITE_RULE[FORALL_SIMP] dest_closure_v_rel_full) (CONJ vr (CONJ a2 dc)) in
  STRIP_ASSUME_TAC th gl;;

let CLOSP1AUX_NUM_KIND_CASES_TAC : tactic = fun (asl,w as gl) ->
  let v = find_term (fun t -> is_var t && type_of t = `:app_kind`) w in
  (CASES_ON v THEN CASE_REWRITE_TAC[]) gl;;

let CLOSP1AUX_num_app_cons = prove
 (el 14 CLOSP1AUX_num_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) && rhs (concl th) = `NONE:num option`
                          then SUBST_ALL_TAC th else NO_TAC) THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> CLOSPROPSAUX_is_app "ALL2" (concl th) &&
                                        is_cons (lhand (concl th)))) THEN
  REWRITE_TAC[LIST_REL_CONS1] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
                                CLOSPROPSAUX_is_app "evaluate_app" (lhs (concl th)))) THEN
  ONCE_REWRITE_TAC[clos_evaluate_def] THEN CLOSP1AUX_NUM_MAXAPP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM (MATCH_MP clos_numberProof_state_rel_clock th)]) THEN
  REWRITE_TAC[LENGTH] THEN RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
  CLOSP1AUX_NUM_LENGTHS_TAC THEN CLOSP1AUX_NUM_STATE_CLOCK_TAC THEN
  CLOSP1AUX_NUM_DEST_CLOSURE_TAC THEN CLOSP1AUX_NUM_KIND_CASES_TAC THENL
   [REWRITE_TAC[MESON[] `!a:clos_v P. (!x. a = x ==> P x) <=> P a`] THEN
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN CLOSP1AUX_NUM_FIN_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[injectivity "option"; injectivity "app_kind"]) THEN
    CLOSP1AUX_NUM_UNWIND_TAC THEN
    CLOSP1AUX_NUM_FULL_APP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    CLOSP1AUX_NUM_LENGTHS_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THENL
     [CLOSP1AUX_NUM_FIN_TAC; ALL_TAC] THEN
    CLOSP1AUX_NUM_STEP_TAC THENL [CLOSP1AUX_NUM_APP_Q_TAC; CLOSP1AUX_NUM_FIN_TAC]]);;

(* HOL4: renumber_code_locs_correct *)
let renumber_code_locs_correct = prove
 (`(!tmp xs env (s1:(num#C,FFI)clos_state) env' t1 res s2 n.
      tmp = (xs,env,s1) /\
      clos_evaluate (xs,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
      ~contains_App_SOME (clos_state_max_app s1) xs /\
      ALL2 (clos_numberProof_v_rel (clos_state_max_app s1)) env env' /\
      clos_numberProof_state_rel s1 t1 ==>
      ?res' t2.
        clos_evaluate (SND (renumber_code_locs_list n xs),env',t1) = (res',t2) /\
        result_rel (ALL2 (clos_numberProof_v_rel (clos_state_max_app s1)))
                   (clos_numberProof_v_rel (clos_state_max_app s1)) res res' /\
        clos_numberProof_state_rel s2 t2) /\
   (!loc f args (s:(num#C,FFI)clos_state) res s2 f' args' t1.
      evaluate_app loc f args s = (res,s2) /\ ~(res = Rerr (Rabort Rtype_error)) ==>
      clos_numberProof_v_rel (clos_state_max_app s) f f' /\
      loc = NONE /\
      ALL2 (clos_numberProof_v_rel (clos_state_max_app s)) args args' /\
      clos_numberProof_state_rel s t1 ==>
      ?res' t2.
        evaluate_app loc f' args' t1 = (res',t2) /\
        result_rel (ALL2 (clos_numberProof_v_rel (clos_state_max_app s)))
                   (clos_numberProof_v_rel (clos_state_max_app s)) res res' /\
        clos_numberProof_state_rel s2 t2)`,
  MP_TAC(MATCH_MP CLOSP1AUX_num_ind (end_itlist CONJ
    [CLOSP1AUX_num_nil; CLOSP1AUX_num_cons; CLOSP1AUX_num_var; CLOSP1AUX_num_if;
     CLOSP1AUX_num_let; CLOSP1AUX_num_raise; CLOSP1AUX_num_handle; CLOSP1AUX_num_op;
     CLOSP1AUX_num_fn; CLOSP1AUX_num_letrec; CLOSP1AUX_num_app; CLOSP1AUX_num_tick;
     CLOSP1AUX_num_call; CLOSP1AUX_num_app_nil; CLOSP1AUX_num_app_cons])) THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL
      [`xs:clos_exp list`; `env:clos_v list`; `s1:(num#C,FFI)clos_state`; `n:num`;
       `res:(clos_v list,clos_v)result`; `s2:(num#C,FFI)clos_state`; `env':clos_v list`;
       `t1:(C,FFI)clos_state`] o check CLOSP1AUX_num_is_P);
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`loc:num option`; `f:clos_v`; `args:clos_v list`; `s:(num#C,FFI)clos_state`;
       `res:(clos_v list,clos_v)result`; `s2:(num#C,FFI)clos_state`; `f':clos_v`;
       `args':clos_v list`; `t1:(C,FFI)clos_state`] o check CLOSP1AUX_num_is_Q)] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* syntactic properties of renumber_code_locs                                *)
(* ------------------------------------------------------------------------- *)

(* the induction of renumber_code_locs, the calls named, the contexts unwound *)
let CLOSP1AUX_NUM_IND_TAC : tactic =
  MATCH_MP_TAC renumber_code_locs_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY(DISCH_THEN(STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[renumber_code_locs_def] THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[FST; SND] THEN CLOSP1AUX_NUM_NORM_TAC THEN CLOSP1AUX_NUM_LEN_TAC;;

(* HOL4: renumber_code_locs_every_Fn_SOME *)
let renumber_code_locs_every_Fn_SOME = prove
 (`(!n es. every_Fn_SOME (SND (renumber_code_locs_list n es))) /\
   (!n e. every_Fn_SOME [SND (renumber_code_locs n e)])`,
  CLOSP1AUX_NUM_IND_TAC THEN
  REWRITE_TAC[every_Fn_SOME_def; IS_SOME_DEF] THEN
  ONCE_REWRITE_TAC[CLOSPROPSAUX_every_Fn_SOME_cons] THEN
  ASM_REWRITE_TAC[every_Fn_SOME_def] THEN ASM_SIMP_TAC[MAP_SND_ZIP; LENGTH_MAP]);;

(* HOL4: renumber_code_locs_every_Fn_vs_NONE *)
let renumber_code_locs_every_Fn_vs_NONE = prove
 (`(!n es. every_Fn_vs_NONE (SND (renumber_code_locs_list n es)) <=> every_Fn_vs_NONE es) /\
   (!n e. every_Fn_vs_NONE [SND (renumber_code_locs n e)] <=> every_Fn_vs_NONE [e])`,
  CLOSP1AUX_NUM_IND_TAC THEN
  REWRITE_TAC[every_Fn_vs_NONE_def] THEN
  ONCE_REWRITE_TAC[CLOSPROPSAUX_every_Fn_vs_NONE_cons] THEN
  ASM_REWRITE_TAC[every_Fn_vs_NONE_def] THEN ASM_SIMP_TAC[MAP_SND_ZIP; LENGTH_MAP]);;

(* three bounded rounds of resolution, the conjunctions split *)
let CLOSP1AUX_NUM_RES3_TAC : tactic =
  let split = REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                             else NO_TAC)) in
  CLOSPROPSAUX_RES_TAC THEN split THEN CLOSPROPSAUX_RES_TAC THEN split THEN
  CLOSPROPSAUX_RES_TAC THEN split;;

(* HOL4: renumber_code_locs_EVEN *)
let renumber_code_locs_EVEN = prove
 (`(!n es. EVEN n ==> EVEN (FST (renumber_code_locs_list n es)) /\
                      ALL EVEN (code_locs (SND (renumber_code_locs_list n es)))) /\
   (!n e. EVEN n ==> EVEN (FST (renumber_code_locs n e)) /\
                     ALL EVEN (code_locs [SND (renumber_code_locs n e)]))`,
  CLOSP1AUX_NUM_IND_TAC THEN TRY DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EVEN_ADD; EVEN_MULT; ARITH]) THEN
  CLOSP1AUX_NUM_RES3_TAC THEN
  ONCE_REWRITE_TAC[code_locs_cons] THEN
  REWRITE_TAC[code_locs_def; LET_DEF; LET_END_DEF; APPEND_NIL; ALL; ALL_APPEND] THEN
  CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[MAP_SND_ZIP; LENGTH_ZIP; LENGTH_MAP] THEN
  ASM_REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH] THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_GENLIST] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH]);;

(* the induction of renumber_code_locs for statements about a call          *)
(* renumber_code_locs n e = (m,e'): the call is unfolded and its parts named *)
let CLOSP1AUX_NUM_IND2_TAC : tactic =
  MATCH_MP_TAC renumber_code_locs_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  (fun (asl,w as gl) ->
     let ant = lhand w in
     if is_forall ant || (is_conj ant && exists is_forall (conjuncts ant))
     then (DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT GEN_TAC) gl else ALL_TAC gl) THEN
  REWRITE_TAC[renumber_code_locs_def] THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  CLOSP1AUX_NUM_NORM_TAC THEN CLOSP1AUX_NUM_LEN_TAC THEN CLOSP1AUX_NUM_RES3_TAC;;

(* HOL4: renumber_code_locs_elist_globals *)
let renumber_code_locs_elist_globals = prove
 (`(!loc es n es'.
      renumber_code_locs_list loc es = (n,es') ==>
      clos_elist_globals es' = clos_elist_globals es) /\
   (!loc e n e'.
      renumber_code_locs loc e = (n,e') ==>
      clos_set_globals e' = clos_set_globals e)`,
  CLOSP1AUX_NUM_IND2_TAC THEN
  ASM_SIMP_TAC[clos_set_globals_def; clos_op_gbag_def; BAG_UNION_EMPTY; MAP_SND_ZIP;
               LENGTH_MAP]);;

(* the same, the hypotheses rewritten with thl first *)
let CLOSP1AUX_NUM_IND3_TAC (thl:thm list) : tactic =
  MATCH_MP_TAC renumber_code_locs_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  (fun (asl,w as gl) ->
     let ant = lhand w in
     if is_forall ant || (is_conj ant && exists is_forall (conjuncts ant))
     then (DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT GEN_TAC) gl else ALL_TAC gl) THEN
  REWRITE_TAC[renumber_code_locs_def] THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE thl) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  CLOSP1AUX_NUM_NORM_TAC THEN CLOSP1AUX_NUM_LEN_TAC THEN CLOSP1AUX_NUM_RES3_TAC;;

(* HOL4: renumber_code_locs_esgc_free *)
let renumber_code_locs_esgc_free = prove
 (`(!loc es n es'.
      renumber_code_locs_list loc es = (n,es') /\ ALL clos_esgc_free es ==>
      ALL clos_esgc_free es') /\
   (!loc e n e'.
      renumber_code_locs loc e = (n,e') /\ clos_esgc_free e ==> clos_esgc_free e')`,
  CLOSP1AUX_NUM_IND3_TAC[clos_esgc_free_def; ALL] THEN
  ASM_REWRITE_TAC[clos_esgc_free_def; ALL] THEN
  ASM_SIMP_TAC[MAP_SND_ZIP; LENGTH_MAP] THEN
  ASM_MESON_TAC[renumber_code_locs_elist_globals]);;

(* HOL4: renumber_code_locs_obeys_max_app *)
let renumber_code_locs_obeys_max_app = prove
 (`(!loc es n es'.
      renumber_code_locs_list loc es = (n,es') /\ ALL (obeys_max_app m) es ==>
      ALL (obeys_max_app m) es') /\
   (!loc e n e'.
      renumber_code_locs loc e = (n,e') /\ obeys_max_app m e ==> obeys_max_app m e')`,
  CLOSP1AUX_NUM_IND3_TAC[obeys_max_app_def; ALL] THEN
  ASM_REWRITE_TAC[obeys_max_app_def; ALL] THEN
  ASM_SIMP_TAC[MAP_SND_ZIP; LENGTH_MAP] THEN CLOSP1AUX_NUM_ARITH_TAC);;

(* HOL4: renumber_code_locs_no_Labels *)
let renumber_code_locs_no_Labels = prove
 (`(!loc es n es'.
      renumber_code_locs_list loc es = (n,es') /\ ALL no_Labels es ==>
      ALL no_Labels es') /\
   (!loc e n e'.
      renumber_code_locs loc e = (n,e') /\ no_Labels e ==> no_Labels e')`,
  CLOSP1AUX_NUM_IND3_TAC[no_Labels_def; ALL] THEN
  ASM_REWRITE_TAC[no_Labels_def; ALL; distinctness "clos_op"] THEN
  ASM_SIMP_TAC[MAP_SND_ZIP; LENGTH_MAP]);;

(* HOL4: renumber_code_locs_imp_EVEN *)
let renumber_code_locs_imp_EVEN = prove
 (`(!n es n' es'. renumber_code_locs_list n es = (n',es') /\ EVEN n ==> EVEN n') /\
   (!n e n' e'. renumber_code_locs n e = (n',e') /\ EVEN n ==> EVEN n')`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(SPECL [`n:num`; `es:clos_exp list`] (CONJUNCT1 renumber_code_locs_EVEN));
    MP_TAC(SPECL [`n:num`; `e:clos_exp`] (CONJUNCT2 renumber_code_locs_EVEN))] THEN
  ASM_REWRITE_TAC[FST] THEN SIMP_TAC[]);;

(* local helpers for renumber_code_locs_get_code_labels: sets of even numbers *)
let CLOSP1AUX_num_all_empty = prove
 (`!(g:A->num->bool) l.
     ALL ((=) {}) (MAP g l) <=> UNIONS (set_of_list (MAP g l)) = {}`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; ALL; set_of_list; UNIONS_0; UNIONS_INSERT; EMPTY_UNION] THEN
  MESON_TAC[]);;

let CLOSP1AUX_num_evens_eq = prove
 (`!n m. EVEN n ==> {n + 2 * k | k | n + 2 * k < m} = {x | EVEN x /\ n <= x /\ x < m}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:num` THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH] THEN ASM_ARITH_TAC;
    STRIP_TAC THEN
    SUBGOAL_THEN `EVEN (x - n)` MP_TAC THENL
     [ASM_REWRITE_TAC[EVEN_SUB]; REWRITE_TAC[EVEN_EXISTS]] THEN
    DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN EXISTS_TAC `k:num` THEN ASM_ARITH_TAC]);;

let CLOSP1AUX_num_evens_image = prove
 (`!m l. EVEN m ==>
         IMAGE (\k. m + 2 * k) (pred_set_count l) = {x | EVEN x /\ m <= x /\ x < m + 2 * l}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_COUNT; IN_ELIM_THM] THEN
  X_GEN_TAC `x:num` THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH] THEN ASM_ARITH_TAC;
    STRIP_TAC THEN
    SUBGOAL_THEN `EVEN (x - m)` MP_TAC THENL
     [ASM_REWRITE_TAC[EVEN_SUB]; REWRITE_TAC[EVEN_EXISTS]] THEN
    DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN EXISTS_TAC `k:num` THEN ASM_ARITH_TAC]);;

let CLOSP1AUX_num_evens_insert = prove
 (`!n m. EVEN m /\ n <= m ==>
         {m} UNION {x | EVEN x /\ n <= x /\ x < m} = {x | EVEN x /\ n <= x /\ x < m + 2}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_UNION; IN_SING; IN_ELIM_THM] THEN
  X_GEN_TAC `x:num` THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    STRIP_TAC THEN ASM_CASES_TAC `x < m:num` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(x = m + 1)` MP_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `EVEN x` THEN ASM_REWRITE_TAC[EVEN_ADD; ARITH];
      ASM_ARITH_TAC]]);;

(* for each equation renumber_code_locs(_list) a b = (c,d): EVEN a ==> EVEN c *)
let CLOSP1AUX_NUM_EVEN_TAC : tactic = fun (asl,w as gl) ->
  let imps = CONJUNCTS (REWRITE_RULE[IMP_CONJ] renumber_code_locs_imp_EVEN) in
  let ev th = REWRITE_RULE[EVEN_ADD; EVEN_MULT; ARITH] (tryfind (fun i -> MATCH_MP i th) imps) in
  MAP_EVERY ASSUME_TAC (mapfilter (fun (_,th) -> ev th) asl) gl;;

(* a local helper: the code labels of a renumbered expression are the even  *)
(* numbers from the first index below the second                           *)
let CLOSP1AUX_num_gcl = prove
 (`(!n es n' es'.
      renumber_code_locs_list n es = (n',es') /\
      ALL ((=) {}) (MAP clos_get_code_labels es) /\ EVEN n ==>
      UNIONS (set_of_list (MAP clos_get_code_labels es')) =
      {x | EVEN x /\ n <= x /\ x < n'}) /\
   (!n e n' e'.
      renumber_code_locs n e = (n',e') /\ clos_get_code_labels e = {} /\ EVEN n ==>
      clos_get_code_labels e' = {x | EVEN x /\ n <= x /\ x < n'})`,
  MATCH_MP_TAC renumber_code_locs_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  (fun (asl,w as gl) ->
     let ant = lhand w in
     if is_forall ant || (is_conj ant && exists is_forall (conjuncts ant))
     then (DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT GEN_TAC) gl else ALL_TAC gl) THEN
  REWRITE_TAC[renumber_code_locs_def] THEN REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  CLOSP1AUX_NUM_NORM_TAC THEN CLOSP1AUX_NUM_LEN_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CLOSP1AUX_num_all_empty; MAP; set_of_list; UNIONS_0;
                              UNIONS_INSERT; clos_get_code_labels_def; MAP_MAP_o;
                              EMPTY_UNION; NOT_INSERT_EMPTY; EVEN_ADD; EVEN_MULT; ARITH]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th
                                 else NO_TAC)) THEN
  TRY CLOSP1AUX_NUM_FALSE_TAC THEN
  CLOSP1AUX_NUM_EVEN_TAC THEN CLOSP1AUX_NUM_INC_TAC THEN CLOSP1AUX_NUM_RES3_TAC THEN
  REWRITE_TAC[clos_get_code_labels_def; MAP; set_of_list; UNIONS_0; UNIONS_INSERT;
              UNION_EMPTY; assign_get_code_label_def] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[MAP_o] THEN ASM_SIMP_TAC[MAP_SND_ZIP; LENGTH_ZIP; LENGTH_MAP] THEN
  ASM_REWRITE_TAC[UNION_EMPTY] THEN
  ASM_SIMP_TAC[CLOSP1AUX_num_evens_insert; CLOSP1AUX_num_evens_image] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; NOT_IN_EMPTY] THEN X_GEN_TAC `x:num` THEN
  ASM_CASES_TAC `EVEN x` THEN ASM_REWRITE_TAC[] THEN CLOSP1AUX_NUM_ARITH_TAC);;

(* HOL4: renumber_code_locs_get_code_labels *)
let renumber_code_locs_get_code_labels = prove
 (`(!n es n' es'.
      renumber_code_locs_list n es = (n',es') /\
      ALL ((=) {}) (MAP clos_get_code_labels es) /\ EVEN n ==>
      UNIONS (set_of_list (MAP clos_get_code_labels es')) =
      {n + 2 * k | k | n + 2 * k < n'}) /\
   (!n e n' e'.
      renumber_code_locs n e = (n',e') /\ clos_get_code_labels e = {} /\ EVEN n ==>
      clos_get_code_labels e' = {n + 2 * k | k | n + 2 * k < n'})`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CLOSP1AUX_num_evens_eq] THEN
  ASM_MESON_TAC[CLOSP1AUX_num_gcl]);;

(* HOL4: renumber_code_locs_any_dests (HOL4 any_dests is app_call_dests NONE) *)
let renumber_code_locs_any_dests = prove
 (`(!k xs n ys.
      renumber_code_locs_list k xs = (n,ys) ==> app_call_dests NONE ys = {}) /\
   (!k x n y.
      renumber_code_locs k x = (n,y) ==> app_call_dests NONE [y] = {})`,
  CLOSP1AUX_NUM_IND2_TAC THEN
  TRY(ONCE_REWRITE_TAC[any_dest_cons]) THEN
  ASM_SIMP_TAC[app_call_dests_def; LET_DEF; LET_END_DEF; MAP_SND_ZIP; LENGTH_MAP;
               UNION_EMPTY; distinctness "option"] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[UNION_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* preservation of observable semantics                                     *)
(* ------------------------------------------------------------------------- *)

(* HOL4: semantics_number *)
let semantics_number = prove
 (`~(clos_semantics (ffi:(FFI)ffi_state) max_app FEMPTY (co:num->(num#C)#clos_prog)
       (state_cc (ignore_table clos_number_compile_inc)
                 (cc:C->clos_prog->(byte list#int64 list#C)option)) xs = Fail) ==>
   ~contains_App_SOME max_app xs /\
   (!n. SND (SND (co n)) = [] /\ ~contains_App_SOME max_app (FST (SND (co n)))) ==>
   clos_semantics ffi max_app FEMPTY (state_co (ignore_table clos_number_compile_inc) co) cc
     (SND (renumber_code_locs_list n xs)) =
   clos_semantics ffi max_app FEMPTY co (state_cc (ignore_table clos_number_compile_inc) cc) xs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ffi:(FFI)ffi_state`; `max_app:num`; `FEMPTY:(num,num#clos_exp)fmap`;
                 `co:num->(num#C)#clos_prog`;
                 `(state_cc (ignore_table clos_number_compile_inc)
                     (cc:C->clos_prog->(byte list#int64 list#C)option)):
                    (num#C)->clos_prog->(byte list#int64 list#(num#C))option`;
                 `xs:clos_exp list`; `FEMPTY:(num,num#clos_exp)fmap`;
                 `(state_co (ignore_table clos_number_compile_inc)
                     (co:num->(num#C)#clos_prog)):num->C#clos_prog`;
                 `cc:C->clos_prog->(byte list#int64 list#C)option`;
                 `SND (renumber_code_locs_list n xs)`;
                 `\(c1:(num,num#clos_exp)fmap) (o1:num->(num#C)#clos_prog)
                   (k1:(num#C)->clos_prog->(byte list#int64 list#(num#C))option)
                   (e1:clos_exp list) (c2:(num,num#clos_exp)fmap) (o2:num->C#clos_prog)
                   (k2:C->clos_prog->(byte list#int64 list#C)option) (e2:clos_exp list). T`]
                clos_IMP_semantics_eq) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[clos_eval_sim_def] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES] THEN
  MP_TAC(SPECL [`xs:clos_exp list,[]:clos_v list,
                 clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY
                   (co:num->(num#C)#clos_prog)
                   (state_cc (ignore_table clos_number_compile_inc)
                      (cc:C->clos_prog->(byte list#int64 list#C)option)) k`;
                `xs:clos_exp list`; `[]:clos_v list`;
                `clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY
                   (co:num->(num#C)#clos_prog)
                   (state_cc (ignore_table clos_number_compile_inc)
                      (cc:C->clos_prog->(byte list#int64 list#C)option)) k`;
                `[]:clos_v list`;
                `clos_initial_state (ffi:(FFI)ffi_state) max_app FEMPTY
                   (state_co (ignore_table clos_number_compile_inc)
                      (co:num->(num#C)#clos_prog))
                   (cc:C->clos_prog->(byte list#int64 list#C)option) k`;
                `res1:(clos_v list,clos_v)result`; `s2:(num#C,FFI)clos_state`; `n:num`]
               (CONJUNCT1 renumber_code_locs_correct)) THEN
  ASM_REWRITE_TAC[ALL2] THEN ANTS_TAC THENL
   [REWRITE_TAC[clos_numberProof_state_rel_def; clos_initial_state_def;
                clos_state_INFO.ri_accessors; ALL2; fmap_rel_FEMPTY] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`res':(clos_v list,clos_v)result`; `t2:(C,FFI)clos_state`] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[clos_numberProof_state_rel_def] o
    check (CLOSPROPSAUX_is_app "clos_numberProof_state_rel" o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (CLOSPROPSAUX_is_app "result_rel" o concl)) THEN
  CASES_ON `res1:(clos_v list,clos_v)result` THEN CASES_ON `res':(clos_v list,clos_v)result` THEN
  REWRITE_TAC[result_rel_def] THEN
  TRY(CASES_ON `a:(clos_v)error_result` THEN CASES_ON `a':(clos_v)error_result`) THEN
  REWRITE_TAC[exc_rel_def]);;
