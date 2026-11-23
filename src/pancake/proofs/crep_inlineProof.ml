(* ========================================================================= *)
(* crep_inlineProof: port of HOL4 pancake/proofs/crep_inlineProofScript.sml  *)
(* (CakeML v3479).  Correctness proof for the function inlining pass.        *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Statements as in HOL4, except: MEM_MAP2_IMP and                         *)
(*   exps_of_nested_seq_assign get a length hypothesis (HOL Light's MAP2     *)
(*   does not truncate); HOL4's variables val and TC are value and tcp;      *)
(*   the expression variable of exps_of_inst_inline is x (HOL4: e, as the    *)
(*   function name of the induction); some types are more general (the FFI  *)
(*   types of the two states of locals_rel, code_inl_rel, locals_ext_rel).   *)
(* - inline_prog_correct comes after the helpers of its Call case (HOL4:     *)
(*   suspend and Resume); evaluate_call_same_result_state is proved from it  *)
(*   with the empty inline map, state_rel_imp_semantics_local from          *)
(*   PCINLAUX_SEM_EQ (the runs of the two states agree for every clock).     *)
(* - Local helpers: PCINLAUX_ (and PCINLAUX_C_ for HOL4 lines 663-697 and    *)
(*   1442-2299).                                                             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "pancake/crepLang.ml";;
needs "pancake/semantics/crepSem.ml";;
needs "pancake/semantics/crepProps.ml";;
needs "pancake/crep_inline.ml";;
needs "pancake/semantics/pan_commonProps.ml";;
needs "pancake/pan_common.ml";;

prioritize_num();;
type_invention_error := true;;
cake_distinct_names ();;

let crep_inlineProof_state_rel_def = cake_def
  `crep_inlineProof_state_rel (s:(A,FFI)crep_state) (t:(A,FFI)crep_state) <=>
     crep_state_globals s = crep_state_globals t /\
     crep_state_code s = crep_state_code t /\
     crep_state_memory s = crep_state_memory t /\
     crep_state_memaddrs s = crep_state_memaddrs t /\
     crep_state_sh_memaddrs s = crep_state_sh_memaddrs t /\
     crep_state_clock s = crep_state_clock t /\
     crep_state_be s = crep_state_be t /\
     crep_state_ffi s = crep_state_ffi t /\
     crep_state_base_addr s = crep_state_base_addr t /\
     crep_state_top_addr s = crep_state_top_addr t`;;

let crep_inlineProof_locals_rel_def = cake_def
  `crep_inlineProof_locals_rel (s:(A,B)crep_state) (t:(A,C)crep_state) <=>
     crep_state_locals s SUBMAP crep_state_locals t`;;

let locals_strong_rel_def = cake_def
  `locals_strong_rel (s:(A,B)crep_state) (t:(A,C)crep_state) <=>
     crep_state_locals s = crep_state_locals t`;;

let OPT_MMAP_SOME_ALL = prove
 (`!(f:A->B option) l.
     (?x. OPT_MMAP f l = SOME x) <=> (!x. MEM x l ==> ?y. f x = SOME y)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN SIMP[OPT_MMAP_def; MEM] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN GVS[] THEN ASM_MESON_TAC[]);;

let OPT_MMAP_ALL_EQ = prove
 (`!(f:A->B option) g l.
     (!x. MEM x l ==> f x = g x) ==> OPT_MMAP f l = OPT_MMAP g l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN SIMP[OPT_MMAP_def; MEM] THEN
  ASM_MESON_TAC[]);;

let SUBMAP_IMP_FUPDATE_SUBMAP = prove
 (`!(f:(A,B)fmap) g x y. f SUBMAP g ==> f |+ (x,y) SUBMAP g |+ (x,y)`,
  REWRITE_TAC[SUBMAP_FLOOKUP_EQN; FLOOKUP_UPDATE] THEN MESON_TAC[]);;

let SUBMAP_IMP_DOMSUB_SUBMAP = prove
 (`!(f:(A,B)fmap) g x. f SUBMAP g ==> f \\ x SUBMAP g \\ x`,
  REWRITE_TAC[SUBMAP_FLOOKUP_EQN; DOMSUB_FLOOKUP_THM] THEN MESON_TAC[]);;

let SUBMAP_IMP_DOMSUB_FUPDATE = prove
 (`!(f:(A,B)fmap) g x y. f SUBMAP g ==> f \\ x SUBMAP g |+ (x,y)`,
  REWRITE_TAC[SUBMAP_FLOOKUP_EQN; DOMSUB_FLOOKUP_THM; FLOOKUP_UPDATE] THEN
  MESON_TAC[option_DISTINCT]);;

let SUBMAP_IMP_FUPDATE_LIST_SUBMAP = prove
 (`!x (y:B list) (f:(A,B)fmap) g.
     f SUBMAP g /\ LENGTH x = LENGTH y ==> f |++ ZIP x y SUBMAP g |++ ZIP x y`,
  LIST_INDUCT_TAC THEN FS[FUPDATE_LIST_THM; ZIP_def] THEN
  REPEAT STRIP_TAC THEN CASES_ON `y:B list` THEN FS[FUPDATE_LIST_THM; ZIP_def] THEN
  LAST_X_ASSUM IRULE THEN FS[SUBMAP_IMP_FUPDATE_SUBMAP]);;

let res_var_submap_res_var = prove
 (`!(f:(A,B)fmap) g x y.
     f SUBMAP g ==> crep_res_var f (x,y) SUBMAP crep_res_var g (x,y)`,
  REPEAT STRIP_TAC THEN CASES_ON `y:B option` THEN
  ASM_SIMP_TAC[crep_res_var_def; SUBMAP_IMP_DOMSUB_SUBMAP; SUBMAP_IMP_FUPDATE_SUBMAP]);;

let locals_ext_rel_def = cake_def
  `locals_ext_rel (a:(A1,B1)crep_state) (b:(A2,B2)crep_state)
                  (a':(A,C1)crep_state) (b':(A,C2)crep_state) <=>
     FDIFF (crep_state_locals a') (FDOM (crep_state_locals a)) =
     FDIFF (crep_state_locals b') (FDOM (crep_state_locals b))`;;

let locals_rel_dec_clock = prove
 (`!(s:(A,FFI)crep_state) t.
     crep_inlineProof_locals_rel s t /\ crep_inlineProof_state_rel s t
     ==> crep_inlineProof_locals_rel (crep_dec_clock s) (crep_dec_clock t) /\
         crep_inlineProof_state_rel (crep_dec_clock s) (crep_dec_clock t)`,
  GVS[crep_dec_clock_def; crep_inlineProof_locals_rel_def;
      crep_inlineProof_state_rel_def]);;

let opt_mmap_some_then_subset_fdom = prove
 (`!vs (fm:(A,B)fmap) vals.
     OPT_MMAP (FLOOKUP fm) vs = SOME vals ==> set_of_list vs SUBSET FDOM fm`,
  LIST_INDUCT_TAC THEN RW[flookup_thm; OPT_MMAP_def; set_of_list] THEN
  GVS[OPT_MMAP_def; flookup_thm; INSERT_SUBSET] THEN ASM_MESON_TAC[]);;

(* the Op cases of the eval lemmas below: OPT_MMAP f l = SOME x carries    *)
(* over to g when g agrees with f on the defined values                    *)

let PCINLAUX_OPT_MMAP_SOME_IMP = prove
 (`!(f:A->B option) g l x.
     OPT_MMAP f l = SOME x /\ (!y v. MEM y l /\ f y = SOME v ==> g y = SOME v)
     ==> OPT_MMAP g l = SOME x`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN SIMP[OPT_MMAP_def; MEM] THEN
  REPEAT STRIP_TAC THEN GVS[OPT_MMAP_def] THEN ASM_MESON_TAC[]);;

let eval_original_extend_locals = prove
 (`!(s:(A,FFI)crep_state) e wl l.
     crep_eval s e = SOME wl /\ crep_state_locals s SUBMAP l
     ==> crep_eval (crep_state_locals_fupd (K l) s) e = SOME wl`,
  REC_IND_TAC crep_eval_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN QPAT_X_ASSUM "crep_eval _ _ = SOME _" MP_TAC THEN
  ONCE_REWRITE_TAC[crep_eval_def] THEN DISCH_TAC THEN
  GVS(crep_mem_load_def :: SUBMAP_FLOOKUP_EQN :: all_case_eqs()) THEN
  RES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_EXISTS_TAC THEN MATCH_MP_TAC PCINLAUX_OPT_MMAP_SOME_IMP THEN
  ASM_EXISTS_TAC THEN ASM_MESON_TAC[]);;

let eval_original_extend_locals_rel = prove
 (`!(s:(A,FFI)crep_state) e wl t.
     crep_eval s e = SOME wl
     ==> crep_inlineProof_locals_rel s t /\ crep_inlineProof_state_rel s t
         ==> crep_eval t e = SOME wl`,
  SIMP[crep_inlineProof_locals_rel_def; crep_inlineProof_state_rel_def] THEN
  REPEAT STRIP_TAC THEN
  DRULE eval_original_extend_locals THEN
  DISCH_THEN(QSPEC_THEN "crep_state_locals t" ASSUME_TAC) THEN GVS[] THEN
  SUBGOAL_THEN `crep_state_locals_fupd (K (crep_state_locals t)) s =
                (t:(A,FFI)crep_state)` (fun th -> ASM_MESON_TAC[th]) THEN
  FS[crep_state_component_equality]);;

let eval_state_locals_rel = prove
 (`!(s:(A,FFI)crep_state) e wl t.
     crep_eval s e = SOME wl /\ crep_inlineProof_state_rel s t /\
     crep_inlineProof_locals_rel s t
     ==> crep_eval t e = SOME wl`,
  MESON_TAC[eval_original_extend_locals_rel]);;

let eval_optmmap_state_locals_rel = prove
 (`!(s:(A,FFI)crep_state) es ws t.
     OPT_MMAP (crep_eval s) es = SOME ws /\ crep_inlineProof_state_rel s t /\
     crep_inlineProof_locals_rel s t
     ==> OPT_MMAP (crep_eval t) es = SOME ws`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PCINLAUX_OPT_MMAP_SOME_IMP THEN
  ASM_EXISTS_TAC THEN ASM_MESON_TAC[eval_state_locals_rel]);;

(* HOL4's  >~ [evaluate (C _, _)] >- tac  after an induction on            *)
(* crep_evaluate: PCINLAUX_PROG_CASES [("crep_C",tac); ...] dflt applies to *)
(* each goal the tactic of the constructor of the program it evaluates      *)
(* (the head of the first crep_evaluate (C .., s) in the goal, C a          *)
(* constructor), else dflt                                                  *)

let PCINLAUX_PROG_CASES (cases:(string*tactic) list) (dflt:tactic) : tactic =
  fun (asl,w as g) ->
    let is_ev t =
      is_comb t &&
      (try fst(dest_const(rator t)) = "crep_evaluate" with Failure _ -> false) &&
      (try is_constructor_app(fst(dest_pair(rand t))) with Failure _ -> false) in
    let name =
      try let t = find_term is_ev w in
          fst(dest_const(fst(strip_comb(fst(dest_pair(rand t))))))
      with Failure _ -> "" in
    (try assoc name cases with Failure _ -> dflt) g;;

let PCINLAUX_FDOM_GEN : tactic =
  REPEAT STRIP_TAC THEN QPAT_X_ASSUM "crep_evaluate _ = _" MP_TAC THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN DISCH_TAC THEN
  GVS([crep_set_globals_def; crep_empty_locals_def; crep_dec_clock_def] @ all_case_eqs());;
let PCINLAUX_FDOM_TAC : tactic =
  PCINLAUX_PROG_CASES
   ["crep_Dec",
    (PCINLAUX_FDOM_GEN THEN QCASES_ON "FLOOKUP (crep_state_locals s) v" THEN
     GVS[crep_res_var_def; flookup_thm; FDOM_DOMSUB; FDOM_FUPDATE] THEN TRY(ASM SET_TAC[]));
    "crep_Primitive",
    (PCINLAUX_FDOM_GEN THEN FS[FDOM_FUPDATE_LIST; MAP_ZIP; GSYM SUBSET_UNION_ABSORPTION] THEN
     FS[SUBSET; IN_SET_OF_LIST; GSYM ALL_MEM; IS_SOME_EXISTS; flookup_thm] THEN
     REWRITE_TAC[EXTENSION; IN_UNION; IN_SET_OF_LIST] THEN ASM_MESON_TAC[]);
    "crep_Assign", (PCINLAUX_FDOM_GEN THEN GVS[FDOM_FUPDATE; flookup_thm] THEN TRY(ASM SET_TAC[]));
    "crep_ShMem",
    (PCINLAUX_FDOM_GEN THEN
     QPAT_X_ASSUM "crep_sh_mem_op _ _ _ _ = _" MP_TAC THEN QCASES_ON "op" THEN
     SIMP[crep_sh_mem_op_def; crep_sh_mem_load_def; crep_sh_mem_store_def; is_load_def] THEN
     RW[] THEN
     GVS(crep_set_var_def :: crep_empty_locals_def :: FDOM_FUPDATE :: flookup_thm ::
         all_case_eqs()) THEN ASM_SIMP_TAC[SET_RULE `(x:num) IN s ==> s = x INSERT s`]);
    "crep_Call",
    (PCINLAUX_FDOM_GEN THEN IMP_RES_TAC opt_mmap_some_then_subset_fdom THEN
     ASM_SIMP_TAC[FDOM_FUPDATE_LIST; MAP_ZIP; SET_RULE `(t:num->bool) SUBSET s ==> s = s UNION t`])]
   PCINLAUX_FDOM_GEN;;

let evaluate_locals_same_fdom = prove
 (CASE_TERM
  `!p (s:(A,FFI)crep_state) r s'.
     crep_evaluate (p,s) = (r,s') /\
     (match r with
        NONE -> T
      | SOME (crepSem_Continue n) -> T
      | SOME (crepSem_Break n) -> T
      | _ -> F) = T
     ==> FDOM (crep_state_locals s) = FDOM (crep_state_locals s')`,
  REC_IND_TAC crep_evaluate_ind THEN REPEAT CONJ_TAC THEN PCINLAUX_FDOM_TAC);;

let evaluate_locals_same_fdom' = prove
 (`!p (s:(A,FFI)crep_state) r s'.
     crep_evaluate (p,s) = (r,s') /\
     (r = NONE \/ (?n. r = SOME (crepSem_Break n)) \/
      (?n. r = SOME (crepSem_Continue n)))
     ==> FDOM (crep_state_locals s) = FDOM (crep_state_locals s')`,
  REPEAT STRIP_TAC THEN DRULE evaluate_locals_same_fdom THEN FS[]);;

(* ------------------------------------------------------------------------- *)
(* evaluate_state_locals_rel_strong: a run from a state with more locals.    *)
(* Proved by induction as PCINLAUX_evaluate_state_locals_rel_strong (the    *)
(* antecedents curried); the case tactics are local (PCINLAUX_SLS_...).      *)
(* ------------------------------------------------------------------------- *)

(* the facts about s's locals carry over to a t with more locals *)

let PCINLAUX_SUBMAP_OPT_MMAP_FLOOKUP = prove
 (`!(f:(A,B)fmap) g vs ws.
     f SUBMAP g /\ OPT_MMAP (FLOOKUP f) vs = SOME ws
     ==> OPT_MMAP (FLOOKUP g) vs = SOME ws`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PCINLAUX_OPT_MMAP_SOME_IMP THEN
  ASM_EXISTS_TAC THEN ASM_MESON_TAC[FLOOKUP_SUBMAP]);;

let PCINLAUX_SUBMAP_ALL_IS_SOME = prove
 (`!(f:(A,B)fmap) g l.
     f SUBMAP g /\ ALL (\v. IS_SOME (FLOOKUP f v)) l
     ==> ALL (\v. IS_SOME (FLOOKUP g v)) l`,
  REWRITE_TAC[GSYM ALL_MEM; IS_SOME_EXISTS] THEN MESON_TAC[FLOOKUP_SUBMAP]);;

(* updates of variables of s keep the locals outside s *)

let PCINLAUX_FDIFF_FUPDATE_IN = prove
 (`!(f:(K,V)fmap) k v s. k IN s ==> FDIFF (f |+ (k,v)) s = FDIFF f s`,
  SIMP_TAC[FDIFF_FUPDATE]);;

let PCINLAUX_FDIFF_FUPDATE_LIST_ZIP = prove
 (`!(f:(K,V)fmap) xs ys s.
     LENGTH xs = LENGTH ys /\ set_of_list xs SUBSET s
     ==> FDIFF (f |++ ZIP xs ys) s = FDIFF f s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FDIFF] THEN
  X_GEN_TAC `k:K` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC flookup_fupdate_zip_not_mem THEN
  ASM_MESON_TAC[SUBSET; IN_SET_OF_LIST]);;

(* crep_sh_mem_op in a related state with more locals *)

let PCINLAUX_sh_mem_op_rel = prove
 (`!op v (a:A word) (s:(A,FFI)crep_state) t (r:((B)crep_result)option) s'.
     crep_sh_mem_op op v a s = (r,s') /\ ~(r = SOME crep_Error) /\
     crep_inlineProof_state_rel s t /\
     crep_state_locals s SUBMAP crep_state_locals t /\ v IN FDOM (crep_state_locals s)
     ==> ?t'. crep_sh_mem_op op v a t = (r,t') /\ crep_inlineProof_state_rel s' t' /\
              (r = NONE /\ crep_state_locals s' SUBMAP crep_state_locals t' /\
               FDIFF (crep_state_locals t) (FDOM (crep_state_locals s)) =
               FDIFF (crep_state_locals t') (FDOM (crep_state_locals s')) \/
               ?e. r = SOME (crep_FinalFFI e))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[crep_inlineProof_state_rel_def] THEN STRIP_TAC THEN
  QPAT_X_ASSUM "crep_sh_mem_op _ _ _ _ = _" MP_TAC THEN QCASES_ON "op" THEN
  ASM_REWRITE_TAC[crep_sh_mem_op_def; crep_sh_mem_load_def; crep_sh_mem_store_def] THEN
  DISCH_TAC THEN GVS_ASM(crep_set_var_def :: crep_empty_locals_def :: all_case_eqs()) THEN
  IMP_RES_TAC FLOOKUP_SUBMAP THEN ASM_REWRITE_TAC[] THEN
  SIMP[crep_set_var_def; crep_empty_locals_def; FDOM_FUPDATE] THEN
  ASM_SIMP_TAC[SUBMAP_IMP_FUPDATE_SUBMAP] THEN
  ASM_SIMP_TAC[SET_RULE `(x:num) IN s ==> x INSERT s = s`] THEN
  ASM_SIMP_TAC[PCINLAUX_FDIFF_FUPDATE_IN]);;

(* restoring a shadowed variable keeps the locals related *)

let PCINLAUX_res_var_SUBMAP = prove
 (`!(f:(K,V)fmap) g h k v.
     f SUBMAP g /\ h SUBMAP k
     ==> crep_res_var f (v,FLOOKUP h v) SUBMAP crep_res_var g (v,FLOOKUP k v)`,
  REPEAT STRIP_TAC THEN QCASES_ON "FLOOKUP h v" THENL
   [QCASES_ON "FLOOKUP k v" THEN
    ASM_SIMP_TAC[crep_res_var_def; SUBMAP_IMP_DOMSUB_SUBMAP; SUBMAP_IMP_DOMSUB_FUPDATE];
    IMP_RES_TAC FLOOKUP_SUBMAP THEN
    ASM_SIMP_TAC[crep_res_var_def; SUBMAP_IMP_FUPDATE_SUBMAP]]);;

(* the recurring result case of the simulation theorems is monotone in the *)
(* property of the normal results                                           *)

let PCINLAUX_RES_CASE_MONO = prove
 (CASE_TERM `!(r:((A)crep_result)option) P Q.
     (match r with
        NONE -> P
      | SOME (crepSem_Break n) -> P
      | SOME (crepSem_Continue n) -> P
      | SOME crep_Error -> F
      | _ -> T) /\
     ((r = NONE \/ (?n. r = SOME (crepSem_Break n)) \/ (?n. r = SOME (crepSem_Continue n)))
      ==> P ==> Q)
     ==> (match r with
            NONE -> Q
          | SOME (crepSem_Break n) -> Q
          | SOME (crepSem_Continue n) -> Q
          | SOME crep_Error -> F
          | _ -> T)`,
  GEN_TAC THEN QCASES_ON "r" THEN SIMP[] THEN QCASES_ON "a" THEN SIMP[] THEN
  MESON_TAC[]);;

(* restoring a shadowed variable: the domain and the locals outside it *)

let PCINLAUX_FDOM_res_var = prove
 (`!(st:(K,V)fmap) (s:(K,V)fmap) v.
     FDOM st = v INSERT FDOM s ==> FDOM (crep_res_var st (v,FLOOKUP s v)) = FDOM s`,
  REPEAT STRIP_TAC THEN QCASES_ON "FLOOKUP s v" THEN
  ASM_REWRITE_TAC[crep_res_var_def; FDOM_DOMSUB; FDOM_FUPDATE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[flookup_thm]) THEN ASM SET_TAC[]);;

let PCINLAUX_res_var_FDIFF = prove
 (`!(t:(K,V)fmap) t1 s v.
     FDIFF t (v INSERT s) = FDIFF t1 (v INSERT s)
     ==> FDIFF t s = FDIFF (crep_res_var t1 (v,FLOOKUP t v)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FDIFF; IN_INSERT] THEN
  DISCH_TAC THEN X_GEN_TAC `k:K` THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  QCASES_ON "FLOOKUP t v" THEN
  ASM_REWRITE_TAC[crep_res_var_def; FLOOKUP_UPDATE; DOMSUB_FLOOKUP_THM] THEN
  ASM_CASES_TAC `k:K = v` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:K`) THEN ASM_REWRITE_TAC[]);;

let PCINLAUX_SLS_GEN : tactic =
  REPEAT STRIP_TAC THEN QPAT_X_ASSUM "crep_evaluate _ = _" MP_TAC THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN DISCH_TAC THEN
  GVS([crep_set_globals_def; crep_empty_locals_def; crep_dec_clock_def] @ all_case_eqs()) THEN
  IMP_RES_TAC eval_state_locals_rel THEN IMP_RES_TAC eval_optmmap_state_locals_rel THEN
  RULE_ASSUM_TAC(REWRITE_RULE[crep_inlineProof_state_rel_def;
                              crep_inlineProof_locals_rel_def]) THEN
  IMP_RES_TAC FLOOKUP_SUBMAP THEN IMP_RES_TAC PCINLAUX_SUBMAP_OPT_MMAP_FLOOKUP THEN
  IMP_RES_TAC PCINLAUX_SUBMAP_ALL_IS_SOME THEN FS[] THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  SIMP[PAIR_EQ; crep_set_globals_def; crep_empty_locals_def; crep_dec_clock_def;
       crep_inlineProof_state_rel_def; crep_inlineProof_locals_rel_def; locals_ext_rel_def;
       SUBMAP_IMP_FUPDATE_SUBMAP; SUBMAP_IMP_FUPDATE_LIST_SUBMAP];;

let PCINLAUX_SLS_ASSIGN_TAC : tactic =
  PCINLAUX_SLS_GEN THEN FS[flookup_thm] THEN
  ASM_SIMP_TAC[SET_RULE `(x:num) IN s ==> x INSERT s = s`; PCINLAUX_FDIFF_FUPDATE_IN];;

let PCINLAUX_SLS_PRIM_TAC : tactic =
  PCINLAUX_SLS_GEN THEN
  SUBGOAL_THEN `set_of_list lhss SUBSET FDOM (crep_state_locals (s:(A,FFI)crep_state))`
    ASSUME_TAC THENL
   [FS[SUBSET; IN_SET_OF_LIST; GSYM ALL_MEM; IS_SOME_EXISTS; flookup_thm] THEN
    ASM_MESON_TAC[];
    ASM_SIMP_TAC[FDOM_FUPDATE_LIST; MAP_ZIP; PCINLAUX_FDIFF_FUPDATE_LIST_ZIP;
                 SET_RULE `(t:num->bool) SUBSET s ==> s UNION t = s`]];;

let PCINLAUX_SLS_SHMEM_TAC : tactic =
  PCINLAUX_SLS_GEN THEN
  (DRULE PCINLAUX_sh_mem_op_rel THEN DISCH_THEN(QSPEC_THEN "t" MP_TAC) THEN
   ASM_REWRITE_TAC[crep_inlineProof_state_rel_def] THEN
   ANTS_TAC THENL [ASM_MESON_TAC[flookup_thm]; ALL_TAC] THEN STRIP_TAC THEN
   ASM_EXISTS_TAC THEN GVS[locals_ext_rel_def]);;

let PCINLAUX_SLS_DEC_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  QCASES_ON "crep_eval s e" THEN SIMP[] THEN
  RENAME1 "crep_eval s e = SOME value" THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `value:(A)word_lab`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  SUBGOAL_THEN `?res st. crep_evaluate (prog,crep_state_locals_fupd
                   (K (crep_state_locals s |+ (v,value))) (s:(A,FFI)crep_state)) = (res,st)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC eval_state_locals_rel THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`res:((A)crep_result)option`; `st:(A,FFI)crep_state`;
     `crep_state_locals_fupd (K (crep_state_locals t |+ (v,value))) (t:(A,FFI)crep_state)`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FS[crep_inlineProof_locals_rel_def; crep_inlineProof_state_rel_def;
       SUBMAP_IMP_FUPDATE_SUBMAP];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
  QPAT_X_ASSUM "_ = s'" (SUBST_ALL_TAC o SYM) THEN CONJ_TAC THENL
   [FS[crep_inlineProof_state_rel_def]; ALL_TAC] THEN
  MATCH_MP_TAC PCINLAUX_RES_CASE_MONO THEN ASM_EXISTS_TAC THEN
  REWRITE_TAC[crep_inlineProof_locals_rel_def; locals_ext_rel_def] THEN
  DISCH_TAC THEN STRIP_TAC THEN SIMP[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PCINLAUX_res_var_SUBMAP THEN FS[crep_inlineProof_locals_rel_def]; ALL_TAC] THEN
  SUBGOAL_THEN `FDOM (crep_state_locals (st:(A,FFI)crep_state)) =
                v INSERT FDOM (crep_state_locals (s:(A,FFI)crep_state))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`prog:(A)crep_prog`;
                   `crep_state_locals_fupd (K (crep_state_locals s |+ (v,value)))
                      (s:(A,FFI)crep_state)`;
                   `r:((A)crep_result)option`; `st:(A,FFI)crep_state`]
                  evaluate_locals_same_fdom') THEN
    ASM_REWRITE_TAC[] THEN SIMP[FDOM_FUPDATE] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PCINLAUX_FDOM_res_var] THEN MATCH_MP_TAC PCINLAUX_res_var_FDIFF THEN
  QPAT_X_ASSUM "FDIFF _ _ = FDIFF _ _" MP_TAC THEN
  SIMP[FDOM_FUPDATE; FDIFF_FUPDATE; IN_INSERT];;

let PCINLAUX_SLS_SEQ_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?res1 s1. crep_evaluate (c1,s:(A,FFI)crep_state) = (res1,s1)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`res1:((A)crep_result)option`;
                                     `s1:(A,FFI)crep_state`; `t:(A,FFI)crep_state`]) THEN
  REMOVE_THEN "ih2" (MP_TAC o SPEC `s1:(A,FFI)crep_state`) THEN
  ASM_CASES_TAC `res1:((A)crep_result)option = NONE` THEN RFS[] THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(QSPEC_THEN "t'" MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN SIMP[] THEN MATCH_MP_TAC PCINLAUX_RES_CASE_MONO THEN ASM_EXISTS_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[locals_ext_rel_def]) THEN REWRITE_TAC[locals_ext_rel_def] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    GVS[]];;

let PCINLAUX_SLS_IF_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN REPEAT DISCH_TAC THEN
  GVS_ASM(all_case_eqs()) THEN
  IMP_RES_TAC eval_state_locals_rel THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(QSPEC_THEN "t" MP_TAC) THEN ASM_REWRITE_TAC[] THEN SIMP[];;

let PCINLAUX_SLS_WHILE_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `crep_state_clock (t:(A,FFI)crep_state) = crep_state_clock (s:(A,FFI)crep_state)`
    ASSUME_TAC THENL [ASM_MESON_TAC[crep_inlineProof_state_rel_def]; ALL_TAC] THEN
  QCASES_ON "crep_eval s e" THEN FS[] THEN
  IMP_RES_TAC eval_state_locals_rel THEN ASM_REWRITE_TAC[] THEN
  QCASES_ON "a" THEN FS[] THEN
  ASM_CASES_TAC `a' = word 0:A word` THENL [GVS[locals_ext_rel_def] THEN NO_TAC; ALL_TAC] THEN
  RFS[] THEN
  ASM_CASES_TAC `crep_state_clock (s:(A,FFI)crep_state) = 0` THENL
   [GVS[] THEN FS[crep_inlineProof_state_rel_def; crep_empty_locals_def] THEN NO_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?res1 s1. crep_evaluate (c,crep_dec_clock s) = (res1,s1:(A,FFI)crep_state)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  RFS[] THEN
  SUBGOAL_THEN `~(res1 = SOME (crep_Error:(A)crep_result))` ASSUME_TAC THENL
   [DISCH_TAC THEN GVS[] THEN NO_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(QSPEC_THEN "crep_dec_clock t" MP_TAC) THEN
  ASM_SIMP_TAC[locals_rel_dec_clock] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN GVS[locals_ext_rel_def; crep_dec_clock_def];;

let PCINLAUX_SLS_CALL_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `crep_state_clock (t:(A,FFI)crep_state) = crep_state_clock (s:(A,FFI)crep_state) /\
                crep_state_code t = crep_state_code s`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[crep_inlineProof_state_rel_def]; ALL_TAC] THEN
  QCASES_ON "OPT_MMAP (crep_eval s) argexps" THEN FS[] THEN
  IMP_RES_TAC eval_optmmap_state_locals_rel THEN ASM_REWRITE_TAC[] THEN
  QCASES_ON "crep_lookup_code (crep_state_code s) fname a (LENGTH a)" THEN FS[] THEN
  NAMED_CASES_ON "a'" ["prog newlocals"] THEN RFS[] THEN
  COND_CASES_TAC THEN RFS[] THEN
  COND_CASES_TAC THEN RFS[] THENL
   [GVS[] THEN FS[crep_inlineProof_state_rel_def; crep_empty_locals_def] THEN NO_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?res st. crep_evaluate (prog,crep_state_locals_fupd (K newlocals)
                   (crep_dec_clock s)) = (res,st:(A,FFI)crep_state)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN RFS[] THEN
  SUBGOAL_THEN `~(res = SOME (crep_Error:(A)crep_result))` ASSUME_TAC THENL
   [DISCH_TAC THEN GVS[] THEN NO_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(QSPEC_THEN "crep_state_locals_fupd (K newlocals) (crep_dec_clock t)" MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FS[crep_inlineProof_locals_rel_def; crep_inlineProof_state_rel_def; crep_dec_clock_def;
       SUBMAP_REFL];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN GVS[] THEN
  TRY(FS[crep_inlineProof_state_rel_def; crep_empty_locals_def] THEN NO_TAC) THEN
  TRY(FIRST_X_ASSUM(QSPEC_THEN "crep_state_locals_fupd (K (crep_state_locals t)) t'" MP_TAC) THEN
      FS[crep_inlineProof_locals_rel_def; crep_inlineProof_state_rel_def; locals_ext_rel_def] THEN
      STRIP_TAC THEN ASM_EXISTS_TAC THEN FS[] THEN NO_TAC) THEN
  TRY(IMP_RES_TAC opt_mmap_some_then_subset_fdom THEN
      FS[crep_inlineProof_locals_rel_def; crep_inlineProof_state_rel_def; locals_ext_rel_def;
         SUBMAP_IMP_FUPDATE_LIST_SUBMAP; FDOM_FUPDATE_LIST; MAP_ZIP] THEN
      ASM_SIMP_TAC[SET_RULE `(t:num->bool) SUBSET s ==> s UNION t = s`;
                   PCINLAUX_FDIFF_FUPDATE_LIST_ZIP] THEN NO_TAC) THEN
  TRY(FS[crep_inlineProof_locals_rel_def] THEN IMP_RES_TAC PCINLAUX_SUBMAP_OPT_MMAP_FLOOKUP THEN
      FS[] THEN NO_TAC) THEN
  ALL_TAC;;

let PCINLAUX_evaluate_state_locals_rel_strong = prove
 (CASE_TERM `!p (s:(A,FFI)crep_state) r s' t.
     crep_evaluate (p,s) = (r,s')
     ==> ~(r = SOME crep_Error)
     ==> crep_inlineProof_locals_rel s t /\ crep_inlineProof_state_rel s t
     ==> ?t'. crep_evaluate (p,t) = (r,t') /\ crep_inlineProof_state_rel s' t' /\
              (match r with
                 NONE -> crep_inlineProof_locals_rel s' t' /\ locals_ext_rel s s' t t'
               | SOME (crepSem_Break n) ->
                   crep_inlineProof_locals_rel s' t' /\ locals_ext_rel s s' t t'
               | SOME (crepSem_Continue n) ->
                   crep_inlineProof_locals_rel s' t' /\ locals_ext_rel s s' t t'
               | SOME crep_Error -> F
               | _ -> T)`,
  REC_IND_TAC crep_evaluate_ind THEN REPEAT CONJ_TAC THEN
  PCINLAUX_PROG_CASES
   ["crep_Assign",PCINLAUX_SLS_ASSIGN_TAC;
    "crep_Primitive",PCINLAUX_SLS_PRIM_TAC;
    "crep_ShMem",PCINLAUX_SLS_SHMEM_TAC;
    "crep_Dec",PCINLAUX_SLS_DEC_TAC;
    "crep_Seq",PCINLAUX_SLS_SEQ_TAC;
    "crep_If",PCINLAUX_SLS_IF_TAC;
    "crep_While",PCINLAUX_SLS_WHILE_TAC;
    "crep_Call",PCINLAUX_SLS_CALL_TAC] PCINLAUX_SLS_GEN);;

let evaluate_state_locals_rel_strong = prove
 (CASE_TERM `!p (s:(A,FFI)crep_state) r s' t.
     crep_evaluate (p,s) = (r,s') /\ ~(r = SOME crep_Error) /\
     crep_inlineProof_locals_rel s t /\ crep_inlineProof_state_rel s t
     ==> ?t'. crep_evaluate (p,t) = (r,t') /\ crep_inlineProof_state_rel s' t' /\
              (match r with
                 NONE -> crep_inlineProof_locals_rel s' t' /\ locals_ext_rel s s' t t'
               | SOME (crepSem_Break n) ->
                   crep_inlineProof_locals_rel s' t' /\ locals_ext_rel s s' t t'
               | SOME (crepSem_Continue n) ->
                   crep_inlineProof_locals_rel s' t' /\ locals_ext_rel s s' t t'
               | SOME crep_Error -> F
               | _ -> T)`,
  MATCH_ACCEPT_TAC(REWRITE_RULE[IMP_IMP; GSYM CONJ_ASSOC]
                     PCINLAUX_evaluate_state_locals_rel_strong));;

let opt_mmap_flookup_some_then_same_fdom = prove
 (`!vs (fm:(K,V)fmap) vals (upd_vals:V list).
     OPT_MMAP (FLOOKUP fm) vs = SOME vals /\ LENGTH vs = LENGTH upd_vals
     ==> FDOM (fm |++ ZIP vs upd_vals) = FDOM fm`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC opt_mmap_some_then_subset_fdom THEN
  ASM_SIMP_TAC[FDOM_FUPDATE_LIST; MAP_ZIP] THEN ASM SET_TAC[]);;

let evaluate_state_locals_rel = prove
 (CASE_TERM `!p (s:(A,FFI)crep_state) r s' t.
     crep_evaluate (p,s) = (r,s')
     ==> ~(r = SOME crep_Error)
     ==> crep_inlineProof_locals_rel s t /\ crep_inlineProof_state_rel s t
     ==> ?t'. crep_evaluate (p,t) = (r,t') /\ crep_inlineProof_state_rel s' t' /\
              (match r with
                 NONE -> crep_inlineProof_locals_rel s' t'
               | SOME (crepSem_Break n) -> crep_inlineProof_locals_rel s' t'
               | SOME (crepSem_Continue n) -> crep_inlineProof_locals_rel s' t'
               | SOME crep_Error -> F
               | _ -> T)`,
  REPEAT STRIP_TAC THEN DRULE PCINLAUX_evaluate_state_locals_rel_strong THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(QSPEC_THEN "t" MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_EXISTS_TAC THEN MATCH_MP_TAC PCINLAUX_RES_CASE_MONO THEN
  ASM_EXISTS_TAC THEN SIMP[]);;

(* HOL4's variable val (a word value) is value here: val is a constant     *)

let single_dec_evaluate = prove
 (`!p (s:(A,FFI)crep_state) r s' v e value.
     crep_eval s e = SOME value /\
     crep_evaluate (p,crep_state_locals_fupd (K (crep_state_locals s |+ (v,value))) s) =
     (r,s') /\
     ~(r = SOME crep_Error)
     ==> ?t'. crep_evaluate (crep_Dec v e p,s) = (r,t') /\
              crep_inlineProof_state_rel s' t'`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN SIMP[crep_inlineProof_state_rel_def]);;

let nested_decs_evaluate = prove
 (`!vs es p (s:(A,FFI)crep_state) r s' vals.
     OPT_MMAP (crep_eval s) es = SOME vals /\
     LENGTH vs = LENGTH es /\
     ALL_DISTINCT vs /\
     (!v. MEM v vs ==> !e. MEM e es ==> ~MEM v (var_cexp e)) /\
     crep_evaluate (p,crep_state_locals_fupd (K (crep_state_locals s |++ ZIP vs vals)) s) =
     (r,s') /\
     ~(r = SOME crep_Error)
     ==> ?t'. crep_evaluate (nested_decs vs es p,s) = (r,t') /\
              crep_inlineProof_state_rel s' t'`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN CASES_ON `es:((A)crep_exp)list` THEN
  SIMP[nested_decs_def; LENGTH; NOT_SUC; OPT_MMAP_def; ZIP_def; FUPDATE_LIST_THM] THENL
   [SIMP[RECORD_SELFID_ss] THEN REPEAT STRIP_TAC THEN SIMP[crep_inlineProof_state_rel_def];
    ALL_TAC] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `OPT_MMAP (crep_eval (crep_state_locals_fupd (K (crep_state_locals s |+ (h,x)))
                  (s:(A,FFI)crep_state))) a1 = SOME (x':((A)word_lab)list)` ASSUME_TAC THENL
   [QPAT_X_ASSUM "OPT_MMAP (crep_eval s) a1 = _" (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC OPT_MMAP_ALL_EQ THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC update_locals_not_vars_eval_eq' THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a1:((A)crep_exp)list`; `p:(A)crep_prog`;
     `crep_state_locals_fupd (K (crep_state_locals s |+ (h,x))) (s:(A,FFI)crep_state)`;
     `r:((A)crep_result)option`; `s':(A,FFI)crep_state`; `x':((A)word_lab)list`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FS[ZIP_def; FUPDATE_LIST_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`nested_decs t a1 p:(A)crep_prog`; `s:(A,FFI)crep_state`;
                 `r:((A)crep_result)option`; `t':(A,FFI)crep_state`; `h:num`;
                 `a0:(A)crep_exp`; `x:(A)word_lab`] single_dec_evaluate) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_EXISTS_TAC THEN
  FS[crep_inlineProof_state_rel_def]);;

let genlist_less_than = prove
 (`!n a v. MEM v (list_of_seq (\x. (a:num) + SUC x) n) ==> a < v`,
  REWRITE_TAC[MEM_GENLIST] THEN ARITH_TAC);;

let genlist_not_in = prove
 (`!n a v. v <= a ==> ~MEM v (list_of_seq (\x. (a:num) + SUC x) n)`,
  MESON_TAC[genlist_less_than; NOT_LT]);;

let genlist_all_distinct = prove
 (`!n a. ALL_DISTINCT (list_of_seq (\x. a + SUC x) n)`,
  REWRITE_TAC[ALL_DISTINCT_GENLIST] THEN ARITH_TAC);;

(* HOL4 proves this with crepProps' eval_upd_clock_eq; here directly: eval  *)
(* does not read the clock                                                  *)

let eval_dec_clock_eq = prove
 (`!(s:(A,FFI)crep_state) e. crep_eval (crep_dec_clock s) e = crep_eval s e`,
  REC_IND_TAC crep_eval_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[crep_eval_def] THEN
  TRY(SUBGOAL_THEN `OPT_MMAP (crep_eval (crep_dec_clock (s:(A,FFI)crep_state))) es =
                    OPT_MMAP (crep_eval s) (es:((A)crep_exp)list)` SUBST1_TAC THENL
      [MATCH_MP_TAC OPT_MMAP_ALL_EQ THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
  ASM_SIMP_TAC[crep_mem_load_def; crep_dec_clock_def] THEN SIMP[]);;

let opt_mmap_eval_dec_clock_eq = prove
 (`!(s:(A,FFI)crep_state) es.
     OPT_MMAP (crep_eval (crep_dec_clock s)) es = OPT_MMAP (crep_eval s) es`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC OPT_MMAP_CONG THEN SIMP[eval_dec_clock_eq]);;


(* ------------------------------------------------------------------------- *)
(* HOL4 lines 663-697 (after opt_mmap_eval_dec_clock_eq in HOL4's order).    *)
(* not_has_return_not_evaluate_return' is proved first, by induction, and    *)
(* not_has_return_not_evaluate_return from it (HOL4: the other way round).   *)
(* ------------------------------------------------------------------------- *)

let PCINLAUX_C_NHR_GEN : tactic =
  REPEAT STRIP_TAC THEN
  QPAT_X_ASSUM "crep_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
  DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[has_return_def]) THEN
  GVS([crep_empty_locals_def] @ all_case_eqs()) THEN
  TRY(QPAT_X_ASSUM "crep_sh_mem_op _ _ _ _ = _" MP_TAC THEN QCASES_ON "op" THEN
      SIMP[crep_sh_mem_op_def; crep_sh_mem_load_def; crep_sh_mem_store_def] THEN
      RW[] THEN GVS(all_case_eqs()) THEN NO_TAC) THEN
  TRY(FIRST_X_ASSUM(MP_TAC o SPEC `retv:((A)word_lab)list`) THEN REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC);;

let not_has_return_not_evaluate_return' = prove
 (`!p (s:(A,FFI)crep_state) r s' retv.
     ~has_return p /\ crep_evaluate (p,s) = (r,s')
     ==> ~(r = SOME (crepSem_Return retv))`,
  REC_IND_TAC crep_evaluate_ind THEN REPEAT CONJ_TAC THEN PCINLAUX_C_NHR_GEN);;

let not_has_return_not_evaluate_return = prove
 (CASE_TERM `!p (s:(A,FFI)crep_state).
     ~has_return p
     ==> ?r s'. crep_evaluate (p,s) = (r,s') /\
                (match r with SOME (crepSem_Return retv) -> F | _ -> T)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `crep_evaluate (p:(A)crep_prog,s:(A,FFI)crep_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)crep_result)option`
               (X_CHOOSE_TAC `s':(A,FFI)crep_state`)) THEN
  ASM_EXISTS_TAC THEN
  DRULE_AT (Pos last) not_has_return_not_evaluate_return' THEN ASM_REWRITE_TAC[] THEN
  QCASES_ON "r" THEN SIMP[] THEN QCASES_ON "a" THEN SIMP[] THEN MESON_TAC[]);;

let res_var_commutes_strong = prove
 (`crep_res_var (crep_res_var (lc:(K,V)fmap) (h,FLOOKUP lc' h)) (n,FLOOKUP lc' n) =
   crep_res_var (crep_res_var lc (n,FLOOKUP lc' n)) (h,FLOOKUP lc' h)`,
  ASM_CASES_TAC `n:K = h` THENL [ASM_REWRITE_TAC[]; ASM_MESON_TAC[res_var_commutes]]);;

let res_var_foldl_commutes_strong = prove
 (`!h vs (lc1:(K,V)fmap) lc2.
     crep_res_var (FOLDL crep_res_var lc1 (ZIP vs (MAP (FLOOKUP lc2) vs))) (h,FLOOKUP lc2 h) =
     FOLDL crep_res_var (crep_res_var lc1 (h,FLOOKUP lc2 h)) (ZIP vs (MAP (FLOOKUP lc2) vs))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ZIP_def; FOLDL] THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [res_var_commutes_strong] THEN REFL_TAC);;

let evaluate_nested_decs_locals_nested_res_var = prove
 (`!p (s:(A,FFI)crep_state) r s' vs es vals.
     OPT_MMAP (crep_eval s) es = SOME vals /\
     LENGTH vs = LENGTH es /\
     ALL_DISTINCT vs /\
     (!v. MEM v vs ==> !e. MEM e es ==> ~MEM v (var_cexp e)) /\
     crep_evaluate (p,crep_state_locals_fupd (K (crep_state_locals s |++ ZIP vs vals)) s) =
     (r,s')
     ==> ?t'. crep_evaluate (nested_decs vs es p,s) = (r,t') /\
              crep_inlineProof_state_rel s' t' /\
              crep_state_locals t' =
              FOLDL crep_res_var (crep_state_locals s') (ZIP vs (MAP (FLOOKUP (crep_state_locals s)) vs))`,
  QINDUCT_ON "vs" THENL
   [REPEAT GEN_TAC THEN CASES_ON `es:((A)crep_exp)list` THEN
    SIMP[nested_decs_def; LENGTH; NOT_SUC; OPT_MMAP_def; ZIP_def; FUPDATE_LIST_THM; MAP;
         FOLDL; RECORD_SELFID_ss] THEN
    REPEAT STRIP_TAC THEN SIMP[crep_inlineProof_state_rel_def];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN CASES_ON `es:((A)crep_exp)list` THEN
  SIMP[nested_decs_def; LENGTH; NOT_SUC; OPT_MMAP_def; ZIP_def; FUPDATE_LIST_THM; MAP; FOLDL] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `OPT_MMAP (crep_eval (crep_state_locals_fupd (K (crep_state_locals s |+ (a0,x)))
                  (s:(A,FFI)crep_state))) a1' = SOME (x':((A)word_lab)list)` ASSUME_TAC THENL
   [QPAT_X_ASSUM "OPT_MMAP (crep_eval s) a1' = _" (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC OPT_MMAP_ALL_EQ THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC update_locals_not_vars_eval_eq' THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:(A)crep_prog`;
     `crep_state_locals_fupd (K (crep_state_locals s |+ (a0,x))) (s:(A,FFI)crep_state)`;
     `r:((A)crep_result)option`; `s':(A,FFI)crep_state`;
     `a1':((A)crep_exp)list`; `x':((A)word_lab)list`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FS[ZIP_def; FUPDATE_LIST_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
  CONJ_TAC THENL [FS[crep_inlineProof_state_rel_def]; ALL_TAC] THEN
  SUBGOAL_THEN `MAP (FLOOKUP (crep_state_locals (s:(A,FFI)crep_state) |+ (a0,x))) a1 =
                MAP (FLOOKUP (crep_state_locals s)) a1` SUBST1_TAC THENL
   [MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; FLOOKUP_UPDATE] THEN
    X_GEN_TAC `y:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[res_var_foldl_commutes_strong]);;

let evaluate_nested_decs_locals_nested_res_var_drule = prove
 (`!p (s:(A,FFI)crep_state) r s' vs es vals r1 t'.
     OPT_MMAP (crep_eval s) es = SOME vals /\
     LENGTH vs = LENGTH es /\
     ALL_DISTINCT vs /\
     (!v. MEM v vs ==> !e. MEM e es ==> ~MEM v (var_cexp e)) /\
     crep_evaluate (p,crep_state_locals_fupd (K (crep_state_locals s |++ ZIP vs vals)) s) =
     (r,s') /\
     crep_evaluate (nested_decs vs es p,s) = (r1,t')
     ==> r1 = r /\ crep_inlineProof_state_rel s' t' /\
         crep_state_locals t' =
         FOLDL crep_res_var (crep_state_locals s')
           (ZIP vs (MAP (FLOOKUP (crep_state_locals s)) vs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:(A)crep_prog`; `s:(A,FFI)crep_state`; `r:((A)crep_result)option`;
                `s':(A,FFI)crep_state`; `vs:num list`; `es:((A)crep_exp)list`;
                `vals:((A)word_lab)list`] evaluate_nested_decs_locals_nested_res_var) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN GVS[]);;

let not_some_is_none = prove
 (`!(a:A option). (!v. ~(a = SOME v)) <=> a = NONE`,
  GEN_TAC THEN QCASES_ON "a" THEN SIMP[] THEN MESON_TAC[]);;

let fdom_eq_flookup_thm = prove
 (`!(f1:(K,V)fmap) (f2:(K,V)fmap).
     FDOM f1 = FDOM f2 <=>
     (!x. (?v. FLOOKUP f1 x = SOME v) ==> (?v. FLOOKUP f2 x = SOME v)) /\
     (!x. FLOOKUP f1 x = NONE ==> FLOOKUP f2 x = NONE)`,
  REWRITE_TAC[EXTENSION; flookup_thm] THEN MESON_TAC[]);;

let flookup_res_var_is_mem_zip_eq = prove
 (`!xs x (lc1:(K,V)fmap) lc2.
     MEM x xs
     ==> FLOOKUP (FOLDL crep_res_var lc1 (ZIP xs (MAP (FLOOKUP lc2) xs))) x =
         FLOOKUP lc2 x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; MAP; ZIP_def; FOLDL] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM res_var_foldl_commutes_strong] THENL
   [ASM_REWRITE_TAC[flookup_res_var_thm];
    ASM_CASES_TAC `x:K = h` THEN ASM_SIMP_TAC[flookup_res_var_thm]]);;

let SUBMAP_DIFF_LIST = prove
 (`!(l:(K,V)fmap) vs vals.
     LENGTH vs = LENGTH vals /\ ALL_DISTINCT vs /\ (!v. MEM v vs ==> ~(v IN FDOM l))
     ==> l SUBMAP l |++ ZIP vs vals`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBMAP_FLOOKUP_EQN] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~MEM (x:K) vs` ASSUME_TAC THENL
   [ASM_MESON_TAC[flookup_thm]; ASM_SIMP_TAC[flookup_fupdate_zip_not_mem]]);;

(* the variables of a returning call include its return variables *)

let PCINLAUX_NOT_MEM_VAR_CTYP = prove
 (CASE_TERM `!(x:num) rts (y:(A word # (A)crep_prog)option).
     ~MEM x (match y with NONE -> rts | SOME (w,hdl) -> APPEND rts (var_prog hdl))
     ==> ~MEM x rts`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP[MEM_APPEND] THEN MESON_TAC[]);;

let PCINLAUX_NVP_GEN : tactic =
  REPEAT STRIP_TAC THEN QPAT_X_ASSUM "crep_evaluate _ = _" MP_TAC THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN DISCH_TAC THEN
  GVS([NOT_ss; crep_set_globals_def; crep_empty_locals_def; crep_dec_clock_def; var_prog_def;
       FLOOKUP_UPDATE] @ all_case_eqs());;

let PCINLAUX_NVP_TAC : tactic =
  PCINLAUX_PROG_CASES
   ["crep_Dec",
    (PCINLAUX_NVP_GEN THEN REWRITE_TAC[flookup_res_var_thm] THEN ASM_SIMP_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
     ASM_SIMP_TAC[FLOOKUP_UPDATE]);
    "crep_Primitive",
    (PCINLAUX_NVP_GEN THEN MATCH_MP_TAC flookup_fupdate_zip_not_mem THEN ASM_REWRITE_TAC[]);
    "crep_ShMem",
    (PCINLAUX_NVP_GEN THEN
     QPAT_X_ASSUM "crep_sh_mem_op _ _ _ _ = _" MP_TAC THEN QCASES_ON "op" THEN
     SIMP[crep_sh_mem_op_def; crep_sh_mem_load_def; crep_sh_mem_store_def; is_load_def] THEN
     RW[] THEN GVS(crep_set_var_def :: crep_empty_locals_def :: FLOOKUP_UPDATE ::
                   all_case_eqs()));
    "crep_Call",
    (PCINLAUX_NVP_GEN THEN TRY(MATCH_MP_TAC flookup_fupdate_zip_not_mem THEN
     ASM_REWRITE_TAC[] THEN IMP_RES_TAC PCINLAUX_NOT_MEM_VAR_CTYP THEN ASM_REWRITE_TAC[] THEN
     NO_TAC))]
   (PCINLAUX_NVP_GEN THEN TRY(ASM_MESON_TAC[]));;

let not_var_prog_flookup_eqn = prove
 (CASE_TERM `!p (s:(A,FFI)crep_state) r s' x.
     crep_evaluate (p,s) = (r,s') /\
     ~MEM x (var_prog p) /\
     (match r with
        NONE -> T
      | SOME (crepSem_Break n) -> T
      | SOME (crepSem_Continue n) -> T
      | _ -> F) = T
     ==> FLOOKUP (crep_state_locals s') x = FLOOKUP (crep_state_locals s) x`,
  REC_IND_TAC crep_evaluate_ind THEN REPEAT CONJ_TAC THEN PCINLAUX_NVP_TAC THEN
  TRY(FS[NOT_ss] THEN ASM_MESON_TAC[]));;

(* the property of a normal result, from the recurring result case *)

let PCINLAUX_RES_CASE_NORMAL = prove
 (CASE_TERM `!(r:((A)crep_result)option) P.
     (match r with
        NONE -> P
      | SOME (crepSem_Break n) -> P
      | SOME (crepSem_Continue n) -> P
      | SOME crep_Error -> F
      | _ -> T) /\
     (r = NONE \/ (?n. r = SOME (crepSem_Break n)) \/ (?n. r = SOME (crepSem_Continue n)))
     ==> P`,
  REPEAT GEN_TAC THEN QCASES_ON "r" THEN SIMP[] THEN QCASES_ON "a" THEN SIMP[]);;

let nested_decs_evaluate_sublocals_strong = prove
 (CASE_TERM `!vs es p (s:(A,FFI)crep_state) r s' vals t.
     OPT_MMAP (crep_eval s) es = SOME vals /\
     LENGTH vs = LENGTH es /\
     ALL_DISTINCT vs /\
     (!v. MEM v vs ==> !e. MEM e es ==> ~MEM v (var_cexp e)) /\
     (!v. MEM v vs ==> ~(v IN FDOM t)) /\
     crep_evaluate (p,crep_state_locals_fupd (K (t |++ ZIP vs vals)) s) = (r,s') /\
     t SUBMAP crep_state_locals s /\
     (match r with
        NONE -> T
      | SOME (crepSem_Break n) -> T
      | SOME (crepSem_Continue n) -> T
      | _ -> F) = T
     ==> ?t'. crep_evaluate (nested_decs vs es p,s) = (r,t') /\
              crep_inlineProof_state_rel s' t' /\
              FDIFF (crep_state_locals s) (FDOM t) SUBMAP crep_state_locals t'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(r:((A)crep_result)option) = NONE \/ (?n. r = SOME (crepSem_Break n)) \/
                (?n. r = SOME (crepSem_Continue n))` ASSUME_TAC THENL
   [QPAT_X_ASSUM "_ <=> T" MP_TAC THEN QCASES_ON "r" THEN SIMP[] THEN QCASES_ON "a" THEN
    SIMP[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (vals:((A)word_lab)list) = LENGTH (vs:num list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[opt_mmap_length_eq]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:(A)crep_prog`; `crep_state_locals_fupd (K (t |++ ZIP vs vals)) (s:(A,FFI)crep_state)`;
                 `r:((A)crep_result)option`; `s':(A,FFI)crep_state`;
                 `crep_state_locals_fupd (K (crep_state_locals s |++ ZIP vs vals)) (s:(A,FFI)crep_state)`]
                evaluate_state_locals_rel_strong) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN FS[] THEN NO_TAC; ALL_TAC] THEN
    SIMP[crep_inlineProof_locals_rel_def; crep_inlineProof_state_rel_def] THEN
    MATCH_MP_TAC SUBMAP_IMP_FUPDATE_LIST_SUBMAP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  RENAME1 "crep_evaluate (p,crep_state_locals_fupd (K (crep_state_locals s |++ ZIP vs vals)) s) = (r,t2)" THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PCINLAUX_RES_CASE_NORMAL o
    (fun th -> CONJ th (ASSUME `(r:((A)crep_result)option) = NONE \/ (?n. r = SOME (crepSem_Break n)) \/ (?n. r = SOME (crepSem_Continue n))`))) THEN
  REWRITE_TAC[crep_inlineProof_locals_rel_def; locals_ext_rel_def] THEN SIMP[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`p:(A)crep_prog`; `s:(A,FFI)crep_state`; `r:((A)crep_result)option`;
                 `t2:(A,FFI)crep_state`; `vs:num list`; `es:((A)crep_exp)list`;
                 `vals:((A)word_lab)list`] evaluate_nested_decs_locals_nested_res_var) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_EXISTS_TAC THEN
  CONJ_TAC THENL [FS[crep_inlineProof_state_rel_def]; ALL_TAC] THEN
  SUBGOAL_THEN `FDOM (crep_state_locals (s':(A,FFI)crep_state)) =
                FDOM (t |++ ZIP vs (vals:((A)word_lab)list))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:(A)crep_prog`;
                   `crep_state_locals_fupd (K (t |++ ZIP vs vals)) (s:(A,FFI)crep_state)`;
                   `r:((A)crep_result)option`; `s':(A,FFI)crep_state`]
                  evaluate_locals_same_fdom') THEN
    ASM_REWRITE_TAC[] THEN SIMP[] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBMAP_FLOOKUP_EQN; FLOOKUP_FDIFF] THEN
  X_GEN_TAC `k:num` THEN X_GEN_TAC `y:(A)word_lab` THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `MEM (k:num) vs` THENL
   [ASM_SIMP_TAC[flookup_res_var_is_mem_zip_eq]; ALL_TAC] THEN
  ASM_SIMP_TAC[flookup_res_var_distinct_zip_eq; LENGTH_MAP] THEN
  QPAT_X_ASSUM "FDIFF _ _ = FDIFF _ _"
    (MP_TAC o AP_TERM `\f. FLOOKUP (f:(num,(A)word_lab)fmap) k`) THEN
  ASM_REWRITE_TAC[FLOOKUP_FDIFF; FDOM_FUPDATE_LIST; IN_UNION; IN_SET_OF_LIST] THEN
  ASM_SIMP_TAC[MAP_ZIP; flookup_fupdate_zip_not_mem]);;

let general_simulate_arg_load_correct = prove
 (`!(s:(A,FFI)crep_state) es (vals:((A)word_lab)list) vs t p r s' tmp_vars.
     OPT_MMAP (crep_eval s) es = SOME vals /\
     LENGTH vs = LENGTH vals /\
     ALL_DISTINCT vs /\
     t SUBMAP crep_state_locals s /\
     crep_evaluate (p,crep_state_locals_fupd (K (t |++ ZIP vs vals)) s) = (r,s') /\
     (!v. MEM v vs \/ MEM v tmp_vars ==> ~(v IN FDOM t)) /\
     ~(r = SOME crep_Error) /\
     ALL_DISTINCT tmp_vars /\ LENGTH tmp_vars = LENGTH vs /\
     (!x. MEM x tmp_vars ==> ~MEM x vs) /\
     (!x. MEM x tmp_vars ==> ~MEM x (FLAT (MAP var_cexp es)))
     ==> ?t'. crep_evaluate (nested_decs tmp_vars es
                               (nested_decs vs (MAP crep_Var tmp_vars) p),s) = (r,t') /\
              crep_inlineProof_state_rel s' t'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (es:((A)crep_exp)list) = LENGTH (vals:((A)word_lab)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[opt_mmap_length_eq]; ALL_TAC] THEN
  (* run 1: more locals, the temporaries *)
  MP_TAC(ISPECL [`p:(A)crep_prog`; `crep_state_locals_fupd (K (t |++ ZIP vs vals)) (s:(A,FFI)crep_state)`;
                 `r:((A)crep_result)option`; `s':(A,FFI)crep_state`;
                 `crep_state_locals_fupd (K ((t |++ ZIP tmp_vars vals) |++ ZIP vs vals)) (s:(A,FFI)crep_state)`]
                evaluate_state_locals_rel) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [SIMP[crep_inlineProof_locals_rel_def; crep_inlineProof_state_rel_def] THEN
    MATCH_MP_TAC SUBMAP_IMP_FUPDATE_LIST_SUBMAP THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBMAP_DIFF_LIST THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,FFI)crep_state` STRIP_ASSUME_TAC) THEN
  (* run 2: all of s's locals *)
  MP_TAC(ISPECL [`p:(A)crep_prog`;
                 `crep_state_locals_fupd (K ((t |++ ZIP tmp_vars vals) |++ ZIP vs vals)) (s:(A,FFI)crep_state)`;
                 `r:((A)crep_result)option`; `t1:(A,FFI)crep_state`;
                 `crep_state_locals_fupd (K ((crep_state_locals s |++ ZIP tmp_vars vals) |++ ZIP vs vals))
                    (s:(A,FFI)crep_state)`]
                evaluate_state_locals_rel) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [SIMP[crep_inlineProof_locals_rel_def; crep_inlineProof_state_rel_def] THEN
    REPEAT(MATCH_MP_TAC SUBMAP_IMP_FUPDATE_LIST_SUBMAP THEN ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:(A,FFI)crep_state` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`vs:num list`; `MAP crep_Var tmp_vars:((A)crep_exp)list`; `p:(A)crep_prog`;
                 `crep_state_locals_fupd (K (crep_state_locals s |++ ZIP tmp_vars vals))
                    (s:(A,FFI)crep_state)`;
                 `r:((A)crep_result)option`; `t2:(A,FFI)crep_state`; `vals:((A)word_lab)list`]
                nested_decs_evaluate) THEN
  ANTS_TAC THENL
   [SIMP[LENGTH_MAP; GSYM lookup_locals_eq_map_vars] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[opt_mmap_some_eq_zip_flookup] THEN
    REWRITE_TAC[MEM_MAP] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    FS[var_cexp_def; MEM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(A,FFI)crep_state` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tmp_vars:num list`; `es:((A)crep_exp)list`;
                 `nested_decs vs (MAP crep_Var tmp_vars) p:(A)crep_prog`;
                 `s:(A,FFI)crep_state`; `r:((A)crep_result)option`; `t3:(A,FFI)crep_state`;
                 `vals:((A)word_lab)list`] nested_decs_evaluate) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FS[MEM_FLAT; MEM_MAP] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_EXISTS_TAC THEN FS[crep_inlineProof_state_rel_def]);;

let general_simulate_arg_load_preserve_locals = prove
 (CASE_TERM `!(s:(A,FFI)crep_state) es (vals:((A)word_lab)list) vs t p r s' tmp_vars.
     OPT_MMAP (crep_eval s) es = SOME vals /\
     LENGTH vs = LENGTH vals /\
     ALL_DISTINCT vs /\
     t SUBMAP crep_state_locals s /\
     crep_evaluate (p,crep_state_locals_fupd (K (t |++ ZIP vs vals)) s) = (r,s') /\
     (!v. MEM v vs \/ MEM v tmp_vars ==> ~(v IN FDOM t)) /\
     (match r with
        NONE -> T
      | SOME (crepSem_Break n) -> T
      | SOME (crepSem_Continue n) -> T
      | _ -> F) = T /\
     ALL_DISTINCT tmp_vars /\ LENGTH tmp_vars = LENGTH vs /\
     (!x. MEM x tmp_vars ==> ~MEM x vs) /\
     (!x. MEM x tmp_vars ==> ~MEM x (FLAT (MAP var_cexp es)))
     ==> ?t'. crep_evaluate (nested_decs tmp_vars es
                               (nested_decs vs (MAP crep_Var tmp_vars) p),s) = (r,t') /\
              crep_inlineProof_state_rel s' t' /\
              FOLDL crep_res_var (crep_state_locals s')
                (ZIP vs (MAP (FLOOKUP (crep_state_locals s)) vs)) SUBMAP
              crep_state_locals t'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(r:((A)crep_result)option) = NONE \/ (?n. r = SOME (crepSem_Break n)) \/
                (?n. r = SOME (crepSem_Continue n))` ASSUME_TAC THENL
   [QPAT_X_ASSUM "_ <=> T" MP_TAC THEN QCASES_ON "r" THEN SIMP[] THEN QCASES_ON "a" THEN
    SIMP[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(r = SOME (crep_Error:(A)crep_result))` ASSUME_TAC THENL
   [ASM_MESON_TAC[option_INJ; option_DISTINCT; distinctness "crep_result"]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (es:((A)crep_exp)list) = LENGTH (vals:((A)word_lab)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[opt_mmap_length_eq]; ALL_TAC] THEN
  (* run 1: the temporaries added to the locals *)
  MP_TAC(ISPECL [`p:(A)crep_prog`; `crep_state_locals_fupd (K (t |++ ZIP vs vals)) (s:(A,FFI)crep_state)`;
                 `r:((A)crep_result)option`; `s':(A,FFI)crep_state`;
                 `crep_state_locals_fupd (K ((t |++ ZIP tmp_vars vals) |++ ZIP vs vals)) (s:(A,FFI)crep_state)`]
                evaluate_state_locals_rel) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [SIMP[crep_inlineProof_locals_rel_def; crep_inlineProof_state_rel_def] THEN
    MATCH_MP_TAC SUBMAP_IMP_FUPDATE_LIST_SUBMAP THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBMAP_DIFF_LIST THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,FFI)crep_state` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `crep_state_locals (s':(A,FFI)crep_state) SUBMAP crep_state_locals (t1:(A,FFI)crep_state)`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`r:((A)crep_result)option`;
                   `crep_inlineProof_locals_rel (s':(A,FFI)crep_state) (t1:(A,FFI)crep_state)`]
                  PCINLAUX_RES_CASE_NORMAL) THEN
    ASM_REWRITE_TAC[crep_inlineProof_locals_rel_def];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:(A)crep_prog`;
                 `crep_state_locals_fupd (K (t |++ ZIP tmp_vars vals)) (s:(A,FFI)crep_state)`;
                 `r:((A)crep_result)option`; `t1:(A,FFI)crep_state`; `vs:num list`;
                 `MAP crep_Var tmp_vars:((A)crep_exp)list`; `vals:((A)word_lab)list`]
                evaluate_nested_decs_locals_nested_res_var) THEN
  ANTS_TAC THENL
   [SIMP[LENGTH_MAP; GSYM lookup_locals_eq_map_vars] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[opt_mmap_some_eq_zip_flookup] THEN
    REWRITE_TAC[MEM_MAP] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    FS[var_cexp_def; MEM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tA:(A,FFI)crep_state` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`nested_decs vs (MAP crep_Var tmp_vars) p:(A)crep_prog`;
                 `crep_state_locals_fupd (K (t |++ ZIP tmp_vars vals)) (s:(A,FFI)crep_state)`;
                 `r:((A)crep_result)option`; `tA:(A,FFI)crep_state`;
                 `crep_state_locals_fupd (K (crep_state_locals s |++ ZIP tmp_vars vals))
                    (s:(A,FFI)crep_state)`]
                evaluate_state_locals_rel_strong) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SIMP[crep_inlineProof_locals_rel_def; crep_inlineProof_state_rel_def] THEN
    MATCH_MP_TAC SUBMAP_IMP_FUPDATE_LIST_SUBMAP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tB:(A,FFI)crep_state` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PCINLAUX_RES_CASE_NORMAL o
    (fun th -> CONJ th (ASSUME `(r:((A)crep_result)option) = NONE \/
       (?n. r = SOME (crepSem_Break n)) \/ (?n. r = SOME (crepSem_Continue n))`))) THEN
  REWRITE_TAC[crep_inlineProof_locals_rel_def; locals_ext_rel_def] THEN SIMP[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`nested_decs vs (MAP crep_Var tmp_vars) p:(A)crep_prog`;
                 `s:(A,FFI)crep_state`; `r:((A)crep_result)option`; `tB:(A,FFI)crep_state`;
                 `tmp_vars:num list`; `es:((A)crep_exp)list`; `vals:((A)word_lab)list`]
                evaluate_nested_decs_locals_nested_res_var) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FS[MEM_FLAT; MEM_MAP] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tC:(A,FFI)crep_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `tC:(A,FFI)crep_state` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [FS[crep_inlineProof_state_rel_def]; ALL_TAC] THEN
  SUBGOAL_THEN `FDOM (crep_state_locals (s':(A,FFI)crep_state)) =
                FDOM (t |++ ZIP vs (vals:((A)word_lab)list))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:(A)crep_prog`;
                   `crep_state_locals_fupd (K (t |++ ZIP vs vals)) (s:(A,FFI)crep_state)`;
                   `r:((A)crep_result)option`; `s':(A,FFI)crep_state`]
                  evaluate_locals_same_fdom') THEN
    ASM_REWRITE_TAC[] THEN SIMP[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FDOM (crep_state_locals (tA:(A,FFI)crep_state)) =
                FDOM (t |++ ZIP tmp_vars (vals:((A)word_lab)list))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`nested_decs vs (MAP crep_Var tmp_vars) p:(A)crep_prog`;
                   `crep_state_locals_fupd (K (t |++ ZIP tmp_vars vals)) (s:(A,FFI)crep_state)`;
                   `r:((A)crep_result)option`; `tA:(A,FFI)crep_state`]
                  evaluate_locals_same_fdom') THEN
    ASM_REWRITE_TAC[] THEN SIMP[] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBMAP_FLOOKUP_EQN] THEN X_GEN_TAC `k:num` THEN X_GEN_TAC `y:(A)word_lab` THEN
  ASM_CASES_TAC `MEM (k:num) tmp_vars` THENL
   [SUBGOAL_THEN `~MEM (k:num) vs` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[flookup_res_var_is_mem_zip_eq; flookup_res_var_distinct_zip_eq; LENGTH_MAP] THEN
    QPAT_ASSUM "!v. MEM v vs \/ MEM v tmp_vars ==> _" (MP_TAC o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `FLOOKUP (crep_state_locals (s':(A,FFI)crep_state)) k = NONE` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[flookup_thm; FDOM_FUPDATE_LIST; IN_UNION; IN_SET_OF_LIST] THEN
      ASM_SIMP_TAC[MAP_ZIP];
      ASM_REWRITE_TAC[option_DISTINCT] THEN RFS[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[flookup_res_var_distinct_zip_eq; LENGTH_MAP] THEN
  ASM_CASES_TAC `MEM (k:num) vs` THENL
   [ASM_SIMP_TAC[flookup_res_var_is_mem_zip_eq] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((k:num) IN FDOM (t:(num,(A)word_lab)fmap))` ASSUME_TAC THENL
     [QPAT_ASSUM "!v. MEM v vs \/ MEM v tmp_vars ==> _" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    QPAT_X_ASSUM "FDIFF _ _ = FDIFF _ _"
      (MP_TAC o AP_TERM `\f. FLOOKUP (f:(num,(A)word_lab)fmap) k`) THEN
    QPAT_X_ASSUM "crep_state_locals tA = _" (fun th -> ASM_REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[FLOOKUP_FDIFF; FDOM_FUPDATE_LIST; IN_UNION; IN_SET_OF_LIST] THEN
    ASM_SIMP_TAC[MAP_ZIP; flookup_fupdate_zip_not_mem] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[flookup_res_var_distinct_zip_eq; LENGTH_MAP] THEN DISCH_TAC THEN
  SUBGOAL_THEN `FLOOKUP (crep_state_locals (t1:(A,FFI)crep_state)) k = SOME (y:(A)word_lab)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC FLOOKUP_SUBMAP THEN EXISTS_TAC `crep_state_locals (s':(A,FFI)crep_state)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC FLOOKUP_SUBMAP THEN
  EXISTS_TAC `FOLDL crep_res_var (crep_state_locals (t1:(A,FFI)crep_state))
                (ZIP vs (MAP (FLOOKUP (t |++ ZIP tmp_vars (vals:((A)word_lab)list))) vs))` THEN
  ASM_SIMP_TAC[flookup_res_var_distinct_zip_eq; LENGTH_MAP]);;

let general_simulate_arg_load_strong = prove
 (CASE_TERM `!(s:(A,FFI)crep_state) es (vals:((A)word_lab)list) vs t p r s' tmp_vars.
     OPT_MMAP (crep_eval s) es = SOME vals /\
     LENGTH vs = LENGTH vals /\
     ALL_DISTINCT vs /\
     t SUBMAP crep_state_locals s /\
     crep_evaluate (p,crep_state_locals_fupd (K (t |++ ZIP vs vals)) s) = (r,s') /\
     (!v. MEM v vs \/ MEM v tmp_vars ==> ~(v IN FDOM t)) /\
     (match r with
        NONE -> T
      | SOME (crepSem_Break n) -> T
      | SOME (crepSem_Continue n) -> T
      | _ -> F) = T /\
     ALL_DISTINCT tmp_vars /\ LENGTH tmp_vars = LENGTH vs /\
     (!x. MEM x tmp_vars ==> ~MEM x vs) /\
     (!x. MEM x tmp_vars ==> ~MEM x (FLAT (MAP var_cexp es)))
     ==> ?t'. crep_evaluate (nested_decs tmp_vars es
                               (nested_decs vs (MAP crep_Var tmp_vars) p),s) = (r,t') /\
              crep_inlineProof_state_rel s' t' /\
              FDIFF (crep_state_locals s) (FDOM t) SUBMAP crep_state_locals t'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (es:((A)crep_exp)list) = LENGTH (vals:((A)word_lab)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[opt_mmap_length_eq]; ALL_TAC] THEN
  SUBGOAL_THEN `(!v. MEM v vs ==> ~(v IN FDOM (t:(num,(A)word_lab)fmap))) /\
                (!v. MEM v tmp_vars ==> ~(v IN FDOM t))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`vs:num list`; `MAP crep_Var tmp_vars:((A)crep_exp)list`; `p:(A)crep_prog`;
                 `crep_state_locals_fupd (K (t |++ ZIP tmp_vars vals)) (s:(A,FFI)crep_state)`;
                 `r:((A)crep_result)option`; `s':(A,FFI)crep_state`; `vals:((A)word_lab)list`;
                 `t:(num,(A)word_lab)fmap`] nested_decs_evaluate_sublocals_strong) THEN
  ANTS_TAC THENL
   [SIMP[LENGTH_MAP; GSYM lookup_locals_eq_map_vars] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[opt_mmap_some_eq_zip_flookup] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MEM_MAP] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
      FS[var_cexp_def; MEM] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC SUBMAP_DIFF_LIST THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tA:(A,FFI)crep_state` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tmp_vars:num list`; `es:((A)crep_exp)list`;
                 `nested_decs vs (MAP crep_Var tmp_vars) p:(A)crep_prog`;
                 `s:(A,FFI)crep_state`; `r:((A)crep_result)option`; `tA:(A,FFI)crep_state`;
                 `vals:((A)word_lab)list`; `t:(num,(A)word_lab)fmap`]
                nested_decs_evaluate_sublocals_strong) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FS[MEM_FLAT; MEM_MAP] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_EXISTS_TAC THEN FS[crep_inlineProof_state_rel_def]);;

let general_simulate_arg_load_strong_1 = prove
 (CASE_TERM `!(s:(A,FFI)crep_state) es (vals:((A)word_lab)list) vs t p r s' tmp_vars.
     OPT_MMAP (crep_eval s) es = SOME vals /\
     LENGTH vs = LENGTH vals /\
     ALL_DISTINCT vs /\
     t SUBMAP crep_state_locals s /\
     crep_evaluate (p,crep_state_locals_fupd (K (t |++ ZIP vs vals)) s) = (r,s') /\
     (!v. MEM v vs \/ MEM v tmp_vars ==> ~(v IN FDOM t)) /\
     (match r with
        NONE -> T
      | SOME (crepSem_Break n) -> T
      | SOME (crepSem_Continue n) -> T
      | _ -> F) = T /\
     ALL_DISTINCT tmp_vars /\ LENGTH tmp_vars = LENGTH vs /\
     (!x. MEM x tmp_vars ==> ~MEM x vs) /\
     (!x. MEM x tmp_vars ==> ~MEM x (FLAT (MAP var_cexp es)))
     ==> ?t'. crep_evaluate (nested_decs tmp_vars es
                               (nested_decs vs (MAP crep_Var tmp_vars) p),s) = (r,t') /\
              crep_inlineProof_state_rel s' t' /\
              FDIFF (crep_state_locals s) (FDOM t) SUBMAP crep_state_locals t' /\
              FOLDL crep_res_var (crep_state_locals s')
                (ZIP vs (MAP (FLOOKUP (crep_state_locals s)) vs)) SUBMAP
              crep_state_locals t'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL general_simulate_arg_load_preserve_locals) THEN
  MP_TAC(SPEC_ALL general_simulate_arg_load_strong) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN GVS[] THEN ASM_EXISTS_TAC THEN ASM_REWRITE_TAC[]);;

let general_simulate_arg_load_strong_all = prove
 (CASE_TERM `!(s:(A,FFI)crep_state) es (vals:((A)word_lab)list) vs t p r s' tmp_vars.
     OPT_MMAP (crep_eval s) es = SOME vals /\
     LENGTH vs = LENGTH vals /\
     ALL_DISTINCT vs /\
     t SUBMAP crep_state_locals s /\
     crep_evaluate (p,crep_state_locals_fupd (K (t |++ ZIP vs vals)) s) = (r,s') /\
     (!v. MEM v vs \/ MEM v tmp_vars ==> ~(v IN FDOM t)) /\
     ~(r = SOME crep_Error) /\
     ALL_DISTINCT tmp_vars /\ LENGTH tmp_vars = LENGTH vs /\
     (!x. MEM x tmp_vars ==> ~MEM x vs) /\
     (!x. MEM x tmp_vars ==> ~MEM x (FLAT (MAP var_cexp es)))
     ==> ?t'. crep_evaluate (nested_decs tmp_vars es
                               (nested_decs vs (MAP crep_Var tmp_vars) p),s) = (r,t') /\
              crep_inlineProof_state_rel s' t' /\
              (match r with
                 NONE ->
                   FDIFF (crep_state_locals s) (FDOM t) SUBMAP crep_state_locals t' /\
                   FOLDL crep_res_var (crep_state_locals s')
                     (ZIP vs (MAP (FLOOKUP (crep_state_locals s)) vs)) SUBMAP
                   crep_state_locals t'
               | SOME (crepSem_Break n) ->
                   FDIFF (crep_state_locals s) (FDOM t) SUBMAP crep_state_locals t' /\
                   FOLDL crep_res_var (crep_state_locals s')
                     (ZIP vs (MAP (FLOOKUP (crep_state_locals s)) vs)) SUBMAP
                   crep_state_locals t'
               | SOME (crepSem_Continue n) ->
                   FDIFF (crep_state_locals s) (FDOM t) SUBMAP crep_state_locals t' /\
                   FOLDL crep_res_var (crep_state_locals s')
                     (ZIP vs (MAP (FLOOKUP (crep_state_locals s)) vs)) SUBMAP
                   crep_state_locals t'
               | SOME crep_Error -> F
               | _ -> T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL general_simulate_arg_load_correct) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,FFI)crep_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t1:(A,FFI)crep_state` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC_ALL general_simulate_arg_load_strong_1) THEN ASM_REWRITE_TAC[] THEN
  QCASES_ON "r" THEN SIMP[] THEN TRY(QCASES_ON "a" THEN SIMP[]) THEN
  RFS[] THEN STRIP_TAC THEN GVS[]);;

let general_simulate_arg_load_strong_all_drule = prove
 (CASE_TERM `!(s:(A,FFI)crep_state) es (vals:((A)word_lab)list) vs t p r s' tmp_vars r1 t'.
     OPT_MMAP (crep_eval s) es = SOME vals /\
     LENGTH vs = LENGTH vals /\
     ALL_DISTINCT vs /\
     t SUBMAP crep_state_locals s /\
     crep_evaluate (p,crep_state_locals_fupd (K (t |++ ZIP vs vals)) s) = (r,s') /\
     (!v. MEM v vs \/ MEM v tmp_vars ==> ~(v IN FDOM t)) /\
     ~(r = SOME crep_Error) /\
     ALL_DISTINCT tmp_vars /\ LENGTH tmp_vars = LENGTH vs /\
     (!x. MEM x tmp_vars ==> ~MEM x vs) /\
     (!x. MEM x tmp_vars ==> ~MEM x (FLAT (MAP var_cexp es))) /\
     crep_evaluate (nested_decs tmp_vars es (nested_decs vs (MAP crep_Var tmp_vars) p),s) =
     (r1,t')
     ==> r1 = r /\
         crep_inlineProof_state_rel s' t' /\
         (match r with
            NONE ->
              FDIFF (crep_state_locals s) (FDOM t) SUBMAP crep_state_locals t' /\
              FOLDL crep_res_var (crep_state_locals s')
                (ZIP vs (MAP (FLOOKUP (crep_state_locals s)) vs)) SUBMAP
              crep_state_locals t'
          | SOME (crepSem_Break n) ->
              FDIFF (crep_state_locals s) (FDOM t) SUBMAP crep_state_locals t' /\
              FOLDL crep_res_var (crep_state_locals s')
                (ZIP vs (MAP (FLOOKUP (crep_state_locals s)) vs)) SUBMAP
              crep_state_locals t'
          | SOME (crepSem_Continue n) ->
              FDIFF (crep_state_locals s) (FDOM t) SUBMAP crep_state_locals t' /\
              FOLDL crep_res_var (crep_state_locals s')
                (ZIP vs (MAP (FLOOKUP (crep_state_locals s)) vs)) SUBMAP
              crep_state_locals t'
          | SOME crep_Error -> F
          | _ -> T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL general_simulate_arg_load_strong_all) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN GVS[]);;

let arg_load_correct = prove
 (CASE_TERM `!(s:(A,FFI)crep_state) es (vals:((A)word_lab)list) vs t p r s' tmp_vars.
     OPT_MMAP (crep_eval s) es = SOME vals /\
     LENGTH vs = LENGTH vals /\
     ALL_DISTINCT vs /\
     t SUBMAP crep_state_locals s /\
     crep_evaluate (p,crep_state_locals_fupd (K (t |++ ZIP vs vals)) s) = (r,s') /\
     (!v. MEM v vs \/ MEM v tmp_vars ==> ~(v IN FDOM t)) /\
     ~(r = SOME crep_Error) /\
     ALL_DISTINCT tmp_vars /\ LENGTH tmp_vars = LENGTH vs /\
     (!x. MEM x tmp_vars ==> ~MEM x vs) /\
     (!x. MEM x tmp_vars ==> ~MEM x (FLAT (MAP var_cexp es)))
     ==> ?t'. crep_evaluate (arg_load tmp_vars es vs p,s) = (r,t') /\
              crep_inlineProof_state_rel s' t' /\
              (match r with
                 NONE ->
                   FDIFF (crep_state_locals s) (FDOM t) SUBMAP crep_state_locals t' /\
                   FOLDL crep_res_var (crep_state_locals s')
                     (ZIP vs (MAP (FLOOKUP (crep_state_locals s)) vs)) SUBMAP
                   crep_state_locals t'
               | SOME (crepSem_Break n) ->
                   FDIFF (crep_state_locals s) (FDOM t) SUBMAP crep_state_locals t' /\
                   FOLDL crep_res_var (crep_state_locals s')
                     (ZIP vs (MAP (FLOOKUP (crep_state_locals s)) vs)) SUBMAP
                   crep_state_locals t'
               | SOME (crepSem_Continue n) ->
                   FDIFF (crep_state_locals s) (FDOM t) SUBMAP crep_state_locals t' /\
                   FOLDL crep_res_var (crep_state_locals s')
                     (ZIP vs (MAP (FLOOKUP (crep_state_locals s)) vs)) SUBMAP
                   crep_state_locals t'
               | SOME crep_Error -> F
               | _ -> T)`,
  REWRITE_TAC[arg_load_def; general_simulate_arg_load_strong_all]);;

let arg_load_stronger = prove
 (CASE_TERM `!(s:(A,FFI)crep_state) es (vals:((A)word_lab)list) vs t p r s' tmp_vars.
     OPT_MMAP (crep_eval s) es = SOME vals /\
     LENGTH vs = LENGTH vals /\
     ALL_DISTINCT vs /\
     t SUBMAP crep_state_locals s /\
     crep_evaluate (p,crep_state_locals_fupd (K (t |++ ZIP vs vals)) s) = (r,s') /\
     (!v. MEM v vs \/ MEM v tmp_vars ==> ~(v IN FDOM t)) /\
     ~(r = SOME crep_Error) /\
     ALL_DISTINCT tmp_vars /\ LENGTH tmp_vars = LENGTH vs /\
     (!x. MEM x tmp_vars ==> ~MEM x vs) /\
     (!x. MEM x tmp_vars ==> ~MEM x (FLAT (MAP var_cexp es)))
     ==> ?t'. crep_evaluate (arg_load tmp_vars es vs p,s) = (r,t') /\
              crep_inlineProof_state_rel s' t' /\
              (match r with
                 NONE ->
                   FDIFF (crep_state_locals s) (FDOM t) =
                   FDIFF (crep_state_locals t') (FDOM t) /\
                   FOLDL crep_res_var (crep_state_locals s')
                     (ZIP vs (MAP (FLOOKUP (crep_state_locals s)) vs)) SUBMAP
                   crep_state_locals t'
               | SOME (crepSem_Break n) ->
                   FDIFF (crep_state_locals s) (FDOM t) =
                   FDIFF (crep_state_locals t') (FDOM t) /\
                   FOLDL crep_res_var (crep_state_locals s')
                     (ZIP vs (MAP (FLOOKUP (crep_state_locals s)) vs)) SUBMAP
                   crep_state_locals t'
               | SOME (crepSem_Continue n) ->
                   FDIFF (crep_state_locals s) (FDOM t) =
                   FDIFF (crep_state_locals t') (FDOM t) /\
                   FOLDL crep_res_var (crep_state_locals s')
                     (ZIP vs (MAP (FLOOKUP (crep_state_locals s)) vs)) SUBMAP
                   crep_state_locals t'
               | SOME crep_Error -> F
               | _ -> T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL arg_load_correct) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,FFI)crep_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t1:(A,FFI)crep_state` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PCINLAUX_RES_CASE_MONO THEN ASM_EXISTS_TAC THEN
  DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FDOM (crep_state_locals (s:(A,FFI)crep_state)) =
                FDOM (crep_state_locals (t1:(A,FFI)crep_state))` ASSUME_TAC THENL
   [MATCH_MP_TAC evaluate_locals_same_fdom' THEN
    EXISTS_TAC `arg_load tmp_vars es vs p:(A)crep_prog` THEN
    EXISTS_TAC `r:((A)crep_result)option` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_FDIFF] THEN X_GEN_TAC `k:num` THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  QCASES_ON "FLOOKUP (crep_state_locals s) k" THENL
   [ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[flookup_thm] THEN
    QPAT_X_ASSUM "FDOM _ = FDOM _" (SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[GSYM flookup_thm];
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o REWRITE_RULE[SUBMAP_FLOOKUP_EQN; FLOOKUP_FDIFF] o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "SUBMAP" &&
                           can (find_term ((=) `FDOM (t:(num,(A)word_lab)fmap)`)) (concl th)
                       with Failure _ -> false)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Code relation and evaluation with inlined code (HOL4 lines 1442-1560).   *)
(* ------------------------------------------------------------------------- *)

let state_rel_code_def = cake_def
  `state_rel_code (s:(A,FFI)crep_state) (t:(A,FFI)crep_state) <=>
     crep_state_globals s = crep_state_globals t /\
     crep_state_memory s = crep_state_memory t /\
     crep_state_memaddrs s = crep_state_memaddrs t /\
     crep_state_sh_memaddrs s = crep_state_sh_memaddrs t /\
     crep_state_clock s = crep_state_clock t /\
     crep_state_be s = crep_state_be t /\
     crep_state_ffi s = crep_state_ffi t /\
     crep_state_base_addr s = crep_state_base_addr t /\
     crep_state_top_addr s = crep_state_top_addr t`;;

let fdom_subset_flookup_thm = prove
 (`!(f:(K,V)fmap) (g:(K,W)fmap).
     FDOM f SUBSET FDOM g <=>
     (!x p. FLOOKUP f x = SOME p ==> ?q. FLOOKUP g x = SOME q)`,
  REWRITE_TAC[SUBSET; flookup_thm] THEN MESON_TAC[]);;

(* HOL4's variable val (a word_lab value) is value here *)

let eval_state_locals_same_code_fdom_same = prove
 (`!(s:(A,FFI)crep_state) e value s1.
     crep_eval s e = SOME value /\ state_rel_code s s1 /\ locals_strong_rel s s1 /\
     FDOM (crep_state_code s) SUBSET FDOM (crep_state_code s1)
     ==> crep_eval s1 e = SOME value`,
  REC_IND_TAC crep_eval_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN QPAT_X_ASSUM "crep_eval _ _ = SOME _" MP_TAC THEN
  ONCE_REWRITE_TAC[crep_eval_def] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[state_rel_code_def; locals_strong_rel_def]) THEN
  GVS(crep_mem_load_def :: all_case_eqs()) THEN
  RES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_EXISTS_TAC THEN MATCH_MP_TAC PCINLAUX_OPT_MMAP_SOME_IMP THEN
  ASM_EXISTS_TAC THEN ASM_MESON_TAC[]);;

let code_inl_rel_def = cake_def
  `code_inl_rel (inl_fs:(mlstring,num list # (A)crep_prog)fmap) (s:(A,B)crep_state)
                (t:(A,C)crep_state) <=>
     !fname args prog.
       FLOOKUP (crep_state_code s) fname = SOME (args,prog)
       ==> ?inl_bag. inl_bag SUBMAP inl_fs /\
                     FLOOKUP (crep_state_code t) fname =
                     SOME (args,inline_prog inl_bag prog)`;;

let eval_code_inl = prove
 (`!(s:(A,FFI)crep_state) e value s1 (inl_fs:(mlstring,num list # (A)crep_prog)fmap).
     crep_eval s e = SOME value /\ state_rel_code s s1 /\ locals_strong_rel s s1 /\
     code_inl_rel inl_fs s s1
     ==> crep_eval s1 e = SOME value`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC eval_state_locals_same_code_fdom_same THEN
  EXISTS_TAC `s:(A,FFI)crep_state` THEN ASM_REWRITE_TAC[fdom_subset_flookup_thm] THEN
  REPEAT GEN_TAC THEN QCASES_ON "p" THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[code_inl_rel_def]) THEN RES_TAC THEN ASM_MESON_TAC[]);;

let opt_mmap_eval_code_inl = prove
 (`!(s:(A,FFI)crep_state) es vals s1 (inl_fs:(mlstring,num list # (A)crep_prog)fmap).
     OPT_MMAP (crep_eval s) es = SOME vals /\ state_rel_code s s1 /\
     locals_strong_rel s s1 /\ code_inl_rel inl_fs s s1
     ==> OPT_MMAP (crep_eval s1) es = SOME vals`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PCINLAUX_OPT_MMAP_SOME_IMP THEN
  ASM_EXISTS_TAC THEN ASM_MESON_TAC[eval_code_inl]);;

(* HOL4 proves this by induction; in HOL Light every pair is a pair *)

let evaluate_is_total = prove
 (`!p (s:(A,FFI)crep_state). ?r s'. crep_evaluate (p,s) = (r,s')`,
  MESON_TAC[PAIR_SURJECTIVE]);;

let MORE_THEN_NOT_MAX_LIST = prove
 (`!l x. MAX_LIST l < x ==> ~MEM x l`,
  MESON_TAC[MAX_LIST_PROPERTY; NOT_LE]);;

(* ------------------------------------------------------------------------- *)
(* Elimination of unreachable code (HOL4 lines 1569-1800).                  *)
(* ------------------------------------------------------------------------- *)

let PCINLAUX_C_UE_GEN : tactic =
  REPEAT STRIP_TAC THEN
  QPAT_X_ASSUM "crep_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
  QPAT_X_ASSUM "unreach_elim _ = _" (MP_TAC o ONCE_REWRITE_RULE[unreach_elim_def]) THEN
  REPEAT DISCH_TAC THEN GVS([crep_empty_locals_def] @ all_case_eqs()) THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
      MESON_TAC[] THEN NO_TAC) THEN
  ASM_MESON_TAC[cases "option"];;

let unreach_elim_not_none_evaluate = prove
 (`!p (s:(A,FFI)crep_state) r s' p1 e.
     unreach_elim p = (p1,SOME e) /\ crep_evaluate (p,s) = (r,s') ==> ?e. r = SOME e`,
  REC_IND_TAC crep_evaluate_ind THEN REPEAT CONJ_TAC THEN PCINLAUX_C_UE_GEN);;

(* a program with an early exit never finishes normally *)

let PCINLAUX_C_UE_NOT_NONE = prove
 (`!p (s:(A,FFI)crep_state) r s' p1 x.
     unreach_elim p = (p1,x) /\ ~(x = NONE) /\ crep_evaluate (p,s) = (r,s')
     ==> ~(r = NONE)`,
  REPEAT GEN_TAC THEN QCASES_ON "x" THEN REWRITE_TAC[] THEN
  MESON_TAC[unreach_elim_not_none_evaluate; option_DISTINCT]);;

let PCINLAUX_C_UEC_GEN : tactic =
  REPEAT STRIP_TAC THEN
  QPAT_X_ASSUM "crep_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
  QPAT_X_ASSUM "unreach_elim _ = _" (MP_TAC o ONCE_REWRITE_RULE[unreach_elim_def]) THEN
  REPEAT DISCH_TAC THEN GVS([crep_empty_locals_def] @ all_case_eqs()) THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  SIMP[crep_empty_locals_def] THEN
  TRY(IMP_RES_TAC PCINLAUX_C_UE_NOT_NONE THEN FS[] THEN NO_TAC) THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[unreach_elim_def] THEN
      TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN MESON_TAC[] THEN NO_TAC);;

let unreach_elim_correct = prove
 (`!p (s:(A,FFI)crep_state) r s' p1 s1.
     crep_evaluate (p,s) = (r,s') /\ ~(r = SOME crep_Error) /\ unreach_elim p = (p1,s1)
     ==> crep_evaluate (p1,s) = (r,s')`,
  REC_IND_TAC crep_evaluate_ind THEN REPEAT CONJ_TAC THEN PCINLAUX_C_UEC_GEN);;

let unreach_elim_converge = prove
 (`!(p:(A)crep_prog) q r. unreach_elim p = (q,r) ==> unreach_elim q = (q,r)`,
  REC_IND_TAC unreach_elim_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[unreach_elim_def] THEN SIMP[] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RW[] THEN
  ONCE_REWRITE_TAC[unreach_elim_def] THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
  GVS(unreach_elim_def :: all_case_eqs()));;

let unreach_elim_fix_point = prove
 (`!(q:(A)crep_prog) r. (?p. unreach_elim p = (q,r)) <=> unreach_elim q = (q,r)`,
  MESON_TAC[unreach_elim_converge]);;

let unreach_elim_nested_decs = prove
 (`!vs es (p:(A)crep_prog) r.
     LENGTH vs = LENGTH es /\ unreach_elim p = (p,r)
     ==> unreach_elim (nested_decs vs es p) = (nested_decs vs es p,r)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  SIMP[nested_decs_def; LENGTH; NOT_SUC; SUC_INJ] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[unreach_elim_def] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t':((A)crep_exp)list`; `p:(A)crep_prog`;
                                `r:(early_exit)option`]) THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

let unreach_elim_arg_load = prove
 (`!(p:(A)crep_prog) tmp_vars args args_vname r.
     LENGTH tmp_vars = LENGTH args /\ LENGTH args = LENGTH args_vname /\
     unreach_elim p = (p,r)
     ==> unreach_elim (arg_load tmp_vars args args_vname p) =
         (arg_load tmp_vars args args_vname p,r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[arg_load_def] THEN
  REPEAT(MATCH_MP_TAC unreach_elim_nested_decs THEN ASM_REWRITE_TAC[LENGTH_MAP]));;

let unreach_elim_arg_load_perm = prove
 (`!(p:(A)crep_prog) tmp_vars args args_vname r.
     LENGTH tmp_vars = LENGTH args_vname /\ LENGTH args = LENGTH args_vname /\
     unreach_elim p = (p,r)
     ==> unreach_elim (arg_load tmp_vars args args_vname p) =
         (arg_load tmp_vars args args_vname p,r)`,
  MESON_TAC[unreach_elim_arg_load]);;

let unreach_elim_prog_size = prove
 (`!(p:(A)crep_prog) q r f.
     unreach_elim p = (q,r) ==> crep_prog_size f q <= crep_prog_size f p`,
  REC_IND_TAC unreach_elim_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[unreach_elim_def] THEN SIMP[] THEN
  REPEAT(PAIRARG_TAC THEN FS[]) THEN RW[] THEN
  GVS(unreach_elim_def :: type_size_def "crep_prog" :: size_aux_eqs "crep_prog" @
      all_case_eqs()) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `f:A->num`)) THEN
  SIMP[pair_size_THM] THEN ARITH_TAC);;

(* the constructor under the first fname (C ..) of the goal selects the case *)
(* tactic (for inductions on the program by unreach_elim_ind, has_return_ind)*)

let PCINLAUX_C_CASES_BY (fname:string) (cases:(string*tactic) list) (dflt:tactic) : tactic =
  fun (asl,w as g) ->
    let is_app t =
      is_comb t &&
      (try fst(dest_const(rator t)) = fname with Failure _ -> false) &&
      (try is_constructor_app(rand t) with Failure _ -> false) in
    let name =
      try fst(dest_const(fst(strip_comb(rand(find_term is_app w)))))
      with Failure _ -> "" in
    (try assoc name cases with Failure _ -> dflt) g;;

let not_has_return_imp_not_branch_ret = prove
 (`!p:(A)crep_prog. ~has_return p ==> not_branch_ret p`,
  REC_IND_TAC has_return_ind THEN REPEAT CONJ_TAC THEN
  RW[has_return_def; not_branch_ret_def; DE_MORGAN_THM] THEN EVERY_CASE_TAC THEN
  GVS[] THEN ASM_MESON_TAC[]);;

let PCINLAUX_C_UE_PAIR (t:term) : tactic =
  MP_TAC(ISPEC t PAIR_SURJECTIVE) THEN STRIP_TAC THEN ASM_REWRITE_TAC[];;

let not_has_return_imp_unreach_elim = prove
 (`!(p:(A)crep_prog) r.
     ~has_return p /\ unreach_elim p = (p,r) ==> ~(r = SOME crep_inline_Ret)`,
  REC_IND_TAC has_return_ind THEN REPEAT CONJ_TAC THEN
  PCINLAUX_C_CASES_BY "unreach_elim"
   ["crep_Dec",
    (REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
     ONCE_REWRITE_TAC[unreach_elim_def; has_return_def] THEN
     PCINLAUX_C_UE_PAIR `unreach_elim (p:(A)crep_prog)` THEN SIMP[] THEN
     ASM_MESON_TAC[]);
    "crep_While",
    (REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
     ONCE_REWRITE_TAC[unreach_elim_def; has_return_def] THEN
     PCINLAUX_C_UE_PAIR `unreach_elim (p:(A)crep_prog)` THEN SIMP[] THEN
     DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2 o CONJUNCT2) THEN SIMP[]);
    "crep_Seq",
    (REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
     ONCE_REWRITE_TAC[unreach_elim_def; has_return_def] THEN
     PCINLAUX_C_UE_PAIR `unreach_elim (p1:(A)crep_prog)` THEN
     PCINLAUX_C_UE_PAIR `unreach_elim (p2:(A)crep_prog)` THEN SIMP[] THEN
     COND_CASES_TAC THEN SIMP[] THEN STRIP_TAC THENL
      [IMP_RES_TAC unreach_elim_prog_size THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `\x:A. 0`) THEN
       FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_var(rand(concl th)))) THEN
       SIMP[type_size_def "crep_prog"] THEN ARITH_TAC;
       ASM_MESON_TAC[]]);
    "crep_If",
    (REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
     ONCE_REWRITE_TAC[unreach_elim_def; has_return_def] THEN
     PCINLAUX_C_UE_PAIR `unreach_elim (p1:(A)crep_prog)` THEN
     PCINLAUX_C_UE_PAIR `unreach_elim (p2:(A)crep_prog)` THEN SIMP[LET_DEF; LET_END_DEF] THEN
     REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
     FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
     REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o rand o concl))) THEN
     SUBGOAL_THEN `~(y = SOME crep_inline_Ret) /\ ~(y' = SOME crep_inline_Ret)`
       MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
     QCASES_ON "y" THEN QCASES_ON "y'" THEN SIMP[] THEN
     TRY(QCASES_ON "a") THEN TRY(QCASES_ON "a'") THEN SIMP[]);
    "crep_Call",
    (REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
     ONCE_REWRITE_TAC[unreach_elim_def; has_return_def] THEN
     QCASES_ON "ctyp" THEN SIMP[] THEN EVERY_CASE_TAC THEN GVS[] THEN
     REPEAT STRIP_TAC THEN GVS[])]
    (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[unreach_elim_def; has_return_def] THEN SIMP[] THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[]));;

(* a program without unreachable code whose returns are not in branches has *)
(* no return statement at all                                                *)

let PCINLAUX_C_UE_NBR_NHR = prove
 (`!p:(A)crep_prog.
     unreach_elim p = (p,NONE) /\ not_branch_ret p ==> ~has_return p`,
  REC_IND_TAC has_return_ind THEN REPEAT CONJ_TAC THEN
  PCINLAUX_C_CASES_BY "unreach_elim"
   ["crep_Dec",
    (REPEAT GEN_TAC THEN DISCH_TAC THEN
     ONCE_REWRITE_TAC[unreach_elim_def; has_return_def; not_branch_ret_def] THEN
     PCINLAUX_C_UE_PAIR `unreach_elim (p:(A)crep_prog)` THEN SIMP[] THEN
     ASM_MESON_TAC[]);
    "crep_Seq",
    (REPEAT GEN_TAC THEN DISCH_TAC THEN
     ONCE_REWRITE_TAC[unreach_elim_def; has_return_def; not_branch_ret_def] THEN
     PCINLAUX_C_UE_PAIR `unreach_elim (p1:(A)crep_prog)` THEN
     PCINLAUX_C_UE_PAIR `unreach_elim (p2:(A)crep_prog)` THEN SIMP[] THEN
     COND_CASES_TAC THEN SIMP[] THEN REWRITE_TAC[DE_MORGAN_THM] THEN
     STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o rand o concl))) THEN
     ASM_MESON_TAC[]);
    "crep_If",
    (REPEAT GEN_TAC THEN DISCH_TAC THEN
     ONCE_REWRITE_TAC[has_return_def; not_branch_ret_def] THEN SIMP[]);
    "crep_While",
    (REPEAT GEN_TAC THEN DISCH_TAC THEN
     ONCE_REWRITE_TAC[has_return_def; not_branch_ret_def] THEN SIMP[]);
    "crep_Call",
    (REPEAT GEN_TAC THEN DISCH_TAC THEN
     ONCE_REWRITE_TAC[unreach_elim_def; has_return_def; not_branch_ret_def] THEN
     QCASES_ON "ctyp" THEN SIMP[] THEN EVERY_CASE_TAC THEN GVS[])]
   (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[unreach_elim_def; has_return_def; not_branch_ret_def] THEN SIMP[]));;

let not_branch_ret_evaluate_return_unreach_elim = prove
 (`!p (s:(A,FFI)crep_state) r s'.
     unreach_elim p = (p,NONE) /\ not_branch_ret p /\ crep_evaluate (p,s) = (r,s')
     ==> !rv. ~(r = SOME (crepSem_Return rv))`,
  MESON_TAC[not_has_return_not_evaluate_return'; PCINLAUX_C_UE_NBR_NHR]);;

(* ------------------------------------------------------------------------- *)
(* Lookups of variables and assignment sequences (HOL4 lines 1802-1891).    *)
(* ------------------------------------------------------------------------- *)

let opt_mmap_some_imp_fupdate_exist_some = prove
 (`!vs (fm:(K,V)fmap) vals nv.
     OPT_MMAP (FLOOKUP fm) vs = SOME vals
     ==> ?z. OPT_MMAP (FLOOKUP (fm |+ nv)) vs = SOME z`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?vals'. OPT_MMAP (FLOOKUP (fm:(K,V)fmap)) vs = SOME vals'` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  QCASES_ON "nv" THEN REWRITE_TAC[OPT_MMAP_SOME_ALL; FLOOKUP_UPDATE] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [MESON_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let opt_mmap_some_imp_fupdate_list_exist_some = prove
 (`!xs (ys:V list) vs (fm:(K,V)fmap) vals.
     OPT_MMAP (FLOOKUP fm) vs = SOME vals /\ LENGTH xs = LENGTH ys
     ==> ?z. OPT_MMAP (FLOOKUP (fm |++ ZIP xs ys)) vs = SOME z`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN QCASES_ON "ys" THEN
  SIMP[LENGTH; NOT_SUC; SUC_INJ; ZIP_def; FUPDATE_LIST_THM] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[opt_mmap_some_imp_fupdate_exist_some]);;

let opt_mmap_flookup_not_mem_domsub = prove
 (`!vs (fm:(K,V)fmap) vals x.
     OPT_MMAP (FLOOKUP fm) vs = SOME vals /\ ~MEM x vs
     ==> OPT_MMAP (FLOOKUP (fm \\ x)) vs = SOME vals`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PCINLAUX_OPT_MMAP_SOME_IMP THEN ASM_EXISTS_TAC THEN
  REWRITE_TAC[DOMSUB_FLOOKUP_THM] THEN ASM_MESON_TAC[]);;

let fdoms_eq_opt_mmap_flookup_some = prove
 (`!vs (fm:(K,V)fmap) (fm':(K,W)fmap) vals.
     FDOM fm = FDOM fm' /\ OPT_MMAP (FLOOKUP fm) vs = SOME vals
     ==> ?z. OPT_MMAP (FLOOKUP fm') vs = SOME z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?vals'. OPT_MMAP (FLOOKUP (fm:(K,V)fmap)) vs = SOME vals'` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[OPT_MMAP_SOME_ALL; flookup_thm] THEN ASM_MESON_TAC[]);;

let opt_mmap_update_locals_not_vars_eval_eq = prove
 (`!es n vs w (s:(A,FFI)crep_state).
     ~MEM n (FLAT (MAP var_cexp es)) /\ OPT_MMAP (crep_eval s) es = SOME vs
     ==> OPT_MMAP (crep_eval (crep_state_locals_fupd (K (crep_state_locals s |+ (n,w))) s))
           es = SOME vs`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PCINLAUX_OPT_MMAP_SOME_IMP THEN ASM_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC crep_update_locals_not_vars_eval_eq THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MEM_FLAT; MEM_MAP]) THEN ASM_MESON_TAC[]);;

(* MAP2 is HOL Light's here; the hypotheses give LENGTH ns = LENGTH es       *)

let evaluate_nested_seq_assign = prove
 (`!ns (s:(A,FFI)crep_state) es ws vals.
     OPT_MMAP (crep_eval s) es = SOME ws /\
     (!x. MEM x ns ==> ~MEM x (FLAT (MAP var_cexp es))) /\
     OPT_MMAP (FLOOKUP (crep_state_locals s)) ns = SOME vals /\
     LENGTH ns = LENGTH ws /\ ALL_DISTINCT ns
     ==> ?s'. crep_evaluate (crep_nested_seq (MAP2 crep_Assign ns es),s) = (NONE,s') /\
              crep_inlineProof_state_rel s s' /\
              (!x. ~MEM x ns ==> FLOOKUP (crep_state_locals s') x =
                                 FLOOKUP (crep_state_locals s) x) /\
              OPT_MMAP (FLOOKUP (crep_state_locals s')) ns = SOME ws`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN QCASES_ON "es" THEN
  SIMP[MAP2; MAP2_DEF; crep_nested_seq_def; OPT_MMAP_def; LENGTH; MEM; ALL_DISTINCT] THEN
  REPEAT STRIP_TAC THEN GVS[] THENL
   [SIMP[crep_evaluate_def; crep_inlineProof_state_rel_def]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`crep_state_locals_fupd (K (crep_state_locals s |+ (h,x))) (s:(A,FFI)crep_state)`;
    `a1:((A)crep_exp)list`; `x':((A)word_lab)list`; `x''':((A)word_lab)list`]) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC opt_mmap_update_locals_not_vars_eval_eq THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      SIMP[] THEN MATCH_MP_TAC opt_mmap_flookup_update THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_EXISTS_TAC THEN FS[crep_inlineProof_state_rel_def] THEN
  SIMP[FLOOKUP_UPDATE; DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FLOOKUP_UPDATE] THEN ASM_MESON_TAC[]);;

let evaluate_nested_seq_assign_drule = prove
 (`!ns (s:(A,FFI)crep_state) es ws vals r s'.
     OPT_MMAP (crep_eval s) es = SOME ws /\
     (!x. MEM x ns ==> ~MEM x (FLAT (MAP var_cexp es))) /\
     OPT_MMAP (FLOOKUP (crep_state_locals s)) ns = SOME vals /\
     LENGTH ns = LENGTH ws /\ ALL_DISTINCT ns /\
     crep_evaluate (crep_nested_seq (MAP2 crep_Assign ns es),s) = (r,s')
     ==> r = NONE /\ crep_inlineProof_state_rel s s' /\
         (!x. ~MEM x ns ==> FLOOKUP (crep_state_locals s') x =
                            FLOOKUP (crep_state_locals s) x) /\
         OPT_MMAP (FLOOKUP (crep_state_locals s')) ns = SOME ws`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ns:num list`; `s:(A,FFI)crep_state`; `es:((A)crep_exp)list`;
                `ws:((A)word_lab)list`; `vals:((A)word_lab)list`]
               evaluate_nested_seq_assign) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN GVS[]);;

(* ------------------------------------------------------------------------- *)
(* transform_eoc_correct (HOL4 lines 1893-2040).  The case tactics are local *)
(* (PCINLAUX_C_TE_...); unreach_elim p = (p,res) rules out code after an   *)
(* early exit, not_branch_ret p returns inside loops and conditionals.      *)
(* ------------------------------------------------------------------------- *)
(* the cases where transform_eoc is the identity: no return is possible *)

let PCINLAUX_C_TE_ID_TAC : tactic =
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!retvs. ~(r = SOME (crepSem_Return retvs:(A)crep_result))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC not_has_return_not_evaluate_return' THEN
    ASM_EXISTS_TAC THEN ASM_REWRITE_TAC[has_return_def]; ALL_TAC] THEN
  REWRITE_TAC[transform_eoc_def] THEN ASM_EXISTS_TAC THEN
  REWRITE_TAC[crep_inlineProof_state_rel_def; locals_strong_rel_def] THEN
  QCASES_ON "r" THEN SIMP[] THEN QCASES_ON "a" THEN FS[] THEN ASM_MESON_TAC[];;

let PCINLAUX_C_TE_RET_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  QPAT_X_ASSUM "crep_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
  DISCH_TAC THEN GVS_ASM(crep_empty_locals_def :: all_case_eqs()) THEN
  IMP_RES_TAC opt_mmap_length_eq THEN REWRITE_TAC[transform_eoc_def] THEN
  SUBGOAL_THEN `TAKE (LENGTH (es:((A)crep_exp)list)) (rts:num list) = rts` SUBST1_TAC THENL
   [ASM_MESON_TAC[TAKE_LENGTH_ID]; ALL_TAC] THEN
  MP_TAC(SPECL [`rts:num list`; `s:(A,FFI)crep_state`; `es:((A)crep_exp)list`;
                `a:((A)word_lab)list`; `z:((A)word_lab)list`] evaluate_nested_seq_assign) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN FS[var_prog_def]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_EXISTS_TAC THEN SIMP[] THEN FS[crep_inlineProof_state_rel_def];;

let PCINLAUX_C_TE_DEC_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[not_branch_ret_def; var_prog_def; transform_eoc_def; MEM_APPEND; MEM;
              DE_MORGAN_THM] THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  QCASES_ON "crep_eval s e" THEN SIMP[] THENL [REPEAT STRIP_TAC THEN GVS[]; ALL_TAC] THEN
  RENAME1 "crep_eval s e = SOME value" THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `value:(A)word_lab`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  SUBGOAL_THEN `?res' st. crep_evaluate (prog,crep_state_locals_fupd
                   (K (crep_state_locals s |+ (v,value))) (s:(A,FFI)crep_state)) = (res',st)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  ONCE_REWRITE_TAC[unreach_elim_def] THEN
  PCINLAUX_C_UE_PAIR `unreach_elim (prog:(A)crep_prog)` THEN SIMP[] THEN
  REPEAT STRIP_TAC THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`res':((A)crep_result)option`; `st:(A,FFI)crep_state`;
                                    `res:(early_exit)option`; `rts:num list`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[];
      SIMP[] THEN MATCH_MP_TAC opt_mmap_some_imp_fupdate_exist_some THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
  QPAT_X_ASSUM "_ = s'" (SUBST_ALL_TAC o SYM) THEN
  CONJ_TAC THENL [FS[crep_inlineProof_state_rel_def]; ALL_TAC] THEN
  QCASES_ON "r" THEN FS[locals_strong_rel_def] THEN
  TRY(TOP_CASE_TAC THEN FS[locals_strong_rel_def]) THEN
  SUBGOAL_THEN `~MEM (v:num) rts` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  QCASES_ON "FLOOKUP (crep_state_locals s) v" THEN SIMP[crep_res_var_def] THENL
   [MATCH_MP_TAC opt_mmap_flookup_not_mem_domsub; MATCH_MP_TAC opt_mmap_flookup_update] THEN
  ASM_REWRITE_TAC[];;

let PCINLAUX_C_TE_SEQ_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[not_branch_ret_def; var_prog_def; transform_eoc_def; MEM_APPEND;
              DE_MORGAN_THM] THEN
  ONCE_REWRITE_TAC[unreach_elim_def] THEN
  PCINLAUX_C_UE_PAIR `unreach_elim (c1:(A)crep_prog)` THEN
  PCINLAUX_C_UE_PAIR `unreach_elim (c2:(A)crep_prog)` THEN SIMP[] THEN
  COND_CASES_TAC THEN SIMP[] THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`c1:(A)crep_prog`; `x:(A)crep_prog`; `y:(early_exit)option`; `\x:A. 0`]
                  unreach_elim_prog_size) THEN
    ASM_REWRITE_TAC[type_size_def "crep_prog"] THEN ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o rand o concl))) THEN
  SUBGOAL_THEN `?res1 s1. crep_evaluate (c1,s:(A,FFI)crep_state) = (res1,s1)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  QPAT_X_ASSUM "crep_evaluate (crep_Seq _ _,_) = _"
    (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  ASM_CASES_TAC `res1:((A)crep_result)option = NONE` THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THENL
   [(* the first part finishes normally *)
    QPAT_X_ASSUM "y = NONE" SUBST_ALL_TAC THEN
  QPAT_X_ASSUM "res1 = NONE" SUBST_ALL_TAC THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`NONE:((A)crep_result)option`; `s1:(A,FFI)crep_state`;
                                     `NONE:(early_exit)option`; `rts:num list`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMP[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SIMP[locals_strong_rel_def] THEN STRIP_TAC THEN
    SUBGOAL_THEN `s1' = (s1:(A,FFI)crep_state)` SUBST_ALL_TAC THENL
   [FS[crep_state_component_equality; crep_inlineProof_state_rel_def]; ALL_TAC] THEN
  REMOVE_THEN "ih2" (MP_TAC o SPEC `s1:(A,FFI)crep_state`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`r:((A)crep_result)option`; `s':(A,FFI)crep_state`;
                             `res:(early_exit)option`; `rts:num list`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(ISPECL [`rts:num list`; `crep_state_locals (s:(A,FFI)crep_state)`;
                         `crep_state_locals (s1:(A,FFI)crep_state)`; `z:((A)word_lab)list`]
                        fdoms_eq_opt_mmap_flookup_some) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC evaluate_locals_same_fdom' THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
  ASM_REWRITE_TAC[] THEN
    FS[locals_strong_rel_def];
    (* it exits early *)
    RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  QPAT_X_ASSUM "y = NONE" SUBST_ALL_TAC THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`r:((A)crep_result)option`; `s':(A,FFI)crep_state`;
                                     `NONE:(early_exit)option`; `rts:num list`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!retvs. ~(r = SOME (crepSem_Return retvs:(A)crep_result))` ASSUME_TAC THENL
   [MATCH_MP_TAC not_branch_ret_evaluate_return_unreach_elim THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `r1 = (r:((A)crep_result)option)` SUBST_ALL_TAC THENL
   [QCASES_ON "r" THEN FS[] THEN EVERY_CASE_TAC THEN FS[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
  ASM_REWRITE_TAC[]];;

let PCINLAUX_C_TE_IF_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[not_branch_ret_def; var_prog_def; transform_eoc_def; MEM_APPEND;
              DE_MORGAN_THM] THEN
  ONCE_REWRITE_TAC[unreach_elim_def] THEN
  PCINLAUX_C_UE_PAIR `unreach_elim (c1:(A)crep_prog)` THEN
  PCINLAUX_C_UE_PAIR `unreach_elim (c2:(A)crep_prog)` THEN SIMP[LET_DEF; LET_END_DEF] THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  QCASES_ON "crep_eval s e" THEN SIMP[] THENL [REPEAT STRIP_TAC THEN GVS[]; ALL_TAC] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o rand o concl))) THEN
  QCASES_ON "a" THEN FS[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`r:((A)crep_result)option`; `s':(A,FFI)crep_state`;
                             `if ~(a' = word 0:A word) then y else y':(early_exit)option`;
                             `rts:num list`]) THEN
  ASM_CASES_TAC `a' = word 0:A word` THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[not_has_return_imp_not_branch_ret];
    SIMP[];
    ASM_MESON_TAC[not_has_return_imp_not_branch_ret];
    SIMP[]];;

(* the first assumption that contains tm *)
let PCINLAUX_C_ASSUM_WITH (tm:term) (ttac:thm_tactic) : tactic =
  FIRST_X_ASSUM (fun th ->
    if can (find_term (aconv tm)) (concl th) then ttac th else failwith "ASSUM_WITH");;

let PCINLAUX_C_TE_WHILE_AGAIN (res1:term) : tactic =
  SUBGOAL_THEN `s1' = (s1:(A,FFI)crep_state)` SUBST_ALL_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[crep_inlineProof_state_rel_def; locals_strong_rel_def]) THEN
    ASM_REWRITE_TAC[crep_state_component_equality];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) &&
       can (find_term (aconv `transform_eoc rts (crep_While e (c:(A)crep_prog))`))
           (concl th)
    then (let n = length(fst(strip_forall(concl th))) in
          let args = if n = 2 then [`NONE:(early_exit)option`; `rts:num list`]
                     else [`r:((A)crep_result)option`; `s':(A,FFI)crep_state`;
                           `NONE:(early_exit)option`; `rts:num list`] in
          MP_TAC(SPECL args th))
    else failwith "WHILE_AGAIN") THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[not_branch_ret_def; var_prog_def; MEM_APPEND; DE_MORGAN_THM] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[unreach_elim_def] THEN ASM_REWRITE_TAC[] THEN SIMP[];
      MATCH_MP_TAC(ISPECL [`rts:num list`; `crep_state_locals (s:(A,FFI)crep_state)`;
                           `crep_state_locals (s1:(A,FFI)crep_state)`; `z:((A)word_lab)list`]
                          fdoms_eq_opt_mmap_flookup_some) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(A)crep_prog`; `crep_dec_clock (s:(A,FFI)crep_state)`;
                     res1; `s1:(A,FFI)crep_state`]
                    evaluate_locals_same_fdom') THEN
      ASM_REWRITE_TAC[dec_clock_simp] THEN SIMP[]];
    ALL_TAC] THEN
  REWRITE_TAC[transform_eoc_def] THEN STRIP_TAC THEN ASM_EXISTS_TAC THEN ASM_REWRITE_TAC[];;

let PCINLAUX_C_TE_WHILE_TAC : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihc") (CONJUNCTS_THEN2 (LABEL_TAC "ihn")
                                                               (LABEL_TAC "ihb"))) THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[not_branch_ret_def; var_prog_def; transform_eoc_def; MEM_APPEND;
              DE_MORGAN_THM] THEN
  ONCE_REWRITE_TAC[unreach_elim_def] THEN
  PCINLAUX_C_UE_PAIR `unreach_elim (c:(A)crep_prog)` THEN SIMP[] THEN
  STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o rand o concl))) THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  QPAT_X_ASSUM "crep_evaluate (crep_While _ _,_) = _"
    (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
  QCASES_ON "crep_eval s e" THEN SIMP[] THEN QCASES_ON "a" THEN SIMP[] THEN
  ASM_CASES_TAC `a' = word 0:A word` THEN ASM_REWRITE_TAC[] THEN SIMP[PAIR_EQ] THENL
   [DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    SIMP[crep_inlineProof_state_rel_def; locals_strong_rel_def];
    ALL_TAC] THEN
  ASM_CASES_TAC `crep_state_clock (s:(A,FFI)crep_state) = 0` THEN ASM_REWRITE_TAC[] THEN
  SIMP[PAIR_EQ] THENL
   [DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    SIMP[crep_inlineProof_state_rel_def; crep_empty_locals_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `?res1 s1. crep_evaluate (c,crep_dec_clock s) = (res1,s1:(A,FFI)crep_state)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(res1 = SOME (crep_Error:(A)crep_result))` ASSUME_TAC THENL
   [DISCH_TAC THEN GVS[]; ALL_TAC] THEN
  SUBGOAL_THEN `!retvs. ~(res1 = SOME (crepSem_Return retvs:(A)crep_result))` ASSUME_TAC THENL
   [ASM_MESON_TAC[not_has_return_not_evaluate_return']; ALL_TAC] THEN
  REMOVE_THEN "ihb" (MP_TAC o SPEC `a':A word`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res1:((A)crep_result)option`; `s1:(A,FFI)crep_state`;
                             `y:(early_exit)option`; `rts:num list`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[dec_clock_simp] THEN
    ASM_MESON_TAC[not_has_return_imp_not_branch_ret];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
  NAMED_CASES_ON "res1" ["";"rr"] THEN RFS[] THENL
   [PCINLAUX_C_TE_WHILE_AGAIN `NONE:((A)crep_result)option`;
    NAMED_CASES_ON "rr" ["";"";"nn";"nn";"vs";"eid";"fe"] THEN RFS[] THEN
    TRY(FIRST_ASSUM(MP_TAC o SPEC `vs:((A)word_lab)list`) THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(ASM_CASES_TAC `nn = 0` THEN RFS[]) THEN
    TRY(PCINLAUX_C_TE_WHILE_AGAIN `SOME (crepSem_Continue 0):((A)crep_result)option` THEN
        NO_TAC) THEN
    GVS[locals_strong_rel_def; crep_inlineProof_state_rel_def]];;

let PCINLAUX_C_TE_CALL_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihc") (LABEL_TAC "ihh")) THEN
  REPEAT GEN_TAC THEN
  NAMED_CASES_ON "caltyp" ["";"ct"] THENL
   [ALL_TAC; NAMED_CASES_ON "ct" ["rs hd"] THEN NAMED_CASES_ON "hd" ["";"wh"] THENL
     [ALL_TAC; NAMED_CASES_ON "wh" ["w hdl"]]] THEN
  REWRITE_TAC[not_branch_ret_def; var_prog_def; transform_eoc_def] THEN SIMP[] THENL
   [(* tail call: becomes a call that assigns the results *)
    STRIP_TAC THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  QPAT_X_ASSUM "crep_evaluate (crep_Call _ _ _,_) = _"
    (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
  DISCH_TAC THEN GVS_ASM(crep_empty_locals_def :: all_case_eqs()) THEN
  ASM_REWRITE_TAC[] THEN SIMP[crep_empty_locals_def; crep_inlineProof_state_rel_def] THEN
  ASM_SIMP_TAC[opt_mmap_some_eq_zip_flookup];
    (* no handler: transform_eoc is the identity *)
    STRIP_TAC THEN
  SUBGOAL_THEN `!retvs. ~(r = SOME (crepSem_Return retvs:(A)crep_result))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC not_has_return_not_evaluate_return' THEN ASM_EXISTS_TAC THEN
    ASM_REWRITE_TAC[has_return_def] THEN SIMP[];
    ALL_TAC] THEN
  TRY ASM_EXISTS_TAC THEN REWRITE_TAC[crep_inlineProof_state_rel_def; locals_strong_rel_def] THEN
  QCASES_ON "r" THEN SIMP[] THEN QCASES_ON "a" THEN FS[] THEN ASM_MESON_TAC[];
    (* a handler: transformed in the same way *)
    STRIP_TAC THEN
  SUBGOAL_THEN `!retvs. ~(r = SOME (crepSem_Return retvs:(A)crep_result))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC not_has_return_not_evaluate_return' THEN
    MAP_EVERY EXISTS_TAC [`crep_Call (SOME (rs,SOME (w,hdl))) fname argexps:(A)crep_prog`;
                          `s:(A,FFI)crep_state`; `s':(A,FFI)crep_state`] THEN
    ASM_REWRITE_TAC[has_return_def] THEN SIMP[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  QPAT_X_ASSUM "crep_evaluate (crep_Call _ _ _,_) = _"
    (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
  DISCH_TAC THEN GVS_ASM(crep_empty_locals_def :: all_case_eqs()) THEN
  ASM_REWRITE_TAC[] THEN SIMP[crep_empty_locals_def; crep_inlineProof_state_rel_def;
                             locals_strong_rel_def] THEN
    SUBGOAL_THEN `?rh. unreach_elim (hdl:(A)crep_prog) = (hdl,rh)` STRIP_ASSUME_TAC THENL
   [QPAT_X_ASSUM "unreach_elim (crep_Call _ _ _) = _"
      (MP_TAC o ONCE_REWRITE_RULE[unreach_elim_def]) THEN
    PCINLAUX_C_UE_PAIR `unreach_elim (hdl:(A)crep_prog)` THEN SIMP[] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`rh:(early_exit)option`; `rts:num list`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[not_has_return_imp_not_branch_ret];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_EXISTS_TAC THEN
  FS[crep_inlineProof_state_rel_def; locals_strong_rel_def]];;

let transform_eoc_correct = prove
 (CASE_TERM `!p (s:(A,FFI)crep_state) r s' res rts.
     crep_evaluate (p,s) = (r,s') /\
     unreach_elim p = (p,res) /\
     not_branch_ret p /\
     (!retvs. r = SOME (crepSem_Return retvs) ==> LENGTH rts = LENGTH retvs) /\
     (!x. MEM x rts ==> ~MEM x (var_prog p)) /\
     (?z. OPT_MMAP (FLOOKUP (crep_state_locals s)) rts = SOME z) /\
     ALL_DISTINCT rts /\
     ~(r = SOME crep_Error)
     ==> ?r1 s1'. crep_evaluate (transform_eoc rts p,s) = (r1,s1') /\
                  crep_inlineProof_state_rel s' s1' /\
                  (match r with
                     NONE -> r1 = NONE /\ locals_strong_rel s' s1'
                   | SOME (crepSem_Break n) ->
                       r1 = SOME (crepSem_Break n) /\ locals_strong_rel s' s1'
                   | SOME (crepSem_Continue n) ->
                       r1 = SOME (crepSem_Continue n) /\ locals_strong_rel s' s1'
                   | SOME (crepSem_Return retvs) ->
                       r1 = NONE /\
                       OPT_MMAP (FLOOKUP (crep_state_locals s1')) rts = SOME retvs
                   | SOME crep_Error -> F
                   | x -> r1 = x)`,
  REC_IND_TAC crep_evaluate_ind THEN REPEAT CONJ_TAC THEN
  PCINLAUX_PROG_CASES
   ["crep_While",PCINLAUX_C_TE_WHILE_TAC; "crep_Call",PCINLAUX_C_TE_CALL_TAC;
    "crep_Dec",PCINLAUX_C_TE_DEC_TAC; "crep_If",PCINLAUX_C_TE_IF_TAC;
    "crep_Seq",PCINLAUX_C_TE_SEQ_TAC; "crep_Return",PCINLAUX_C_TE_RET_TAC]
   PCINLAUX_C_TE_ID_TAC);;

(* ------------------------------------------------------------------------- *)
(* transform_branch_correct (HOL4 lines 2042-2186).  HOL4 quantifies an      *)
(* unused variable res (a type variable there): res:B here.  Case tactics   *)
(* PCINLAUX_C_TB_...                                                         *)
(* ------------------------------------------------------------------------- *)

(* specialise the leading quantifiers of th by name (others stay as they are) *)

let PCINLAUX_C_SPEC_NAMED (insts:(string*term) list) (th:thm) : thm =
  let rec go th =
    if is_forall(concl th) then
      let v = fst(dest_forall(concl th)) in
      let t = try assoc (fst(dest_var v)) insts with Failure _ -> v in
      go (SPEC t th)
    else th in
  go th;;

(* specialise the first quantifiers of th with tms, the others by themselves *)

let PCINLAUX_C_SPEC_FIRST (tms:term list) (th:thm) : thm =
  PCINLAUX_C_SPEC_NAMED [] (SPECL tms th);;

(* specialise each leading quantifier of th with the first term of tms of   *)
(* its type (the others by themselves)                                       *)

let PCINLAUX_C_SPEC_TYPED (tms:term list) (th:thm) : thm =
  let rec go th =
    if is_forall(concl th) then
      let v = fst(dest_forall(concl th)) in
      let t = try find (fun t -> type_of t = type_of v) tms with Failure _ -> v in
      go (SPEC t th)
    else th in
  go th;;

let PCINLAUX_C_TB_ID_TAC : tactic =
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!retvs. ~(r = SOME (crepSem_Return retvs:(A)crep_result))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC not_has_return_not_evaluate_return' THEN
    ASM_EXISTS_TAC THEN ASM_REWRITE_TAC[has_return_def]; ALL_TAC] THEN
  REWRITE_TAC[transform_branch_def] THEN ASM_EXISTS_TAC THEN
  REWRITE_TAC[crep_inlineProof_state_rel_def; locals_strong_rel_def] THEN
  QCASES_ON "r" THEN SIMP[] THEN QCASES_ON "a" THEN FS[] THEN ASM_MESON_TAC[];;

let PCINLAUX_C_TB_RET_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  QPAT_X_ASSUM "crep_evaluate _ = _" (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
  DISCH_TAC THEN GVS_ASM(crep_empty_locals_def :: all_case_eqs()) THEN
  IMP_RES_TAC opt_mmap_length_eq THEN REWRITE_TAC[transform_branch_def] THEN
  SUBGOAL_THEN `TAKE (LENGTH (es:((A)crep_exp)list)) (rts:num list) = rts` SUBST1_TAC THENL
   [ASM_MESON_TAC[TAKE_LENGTH_ID]; ALL_TAC] THEN
  MP_TAC(SPECL [`rts:num list`; `s:(A,FFI)crep_state`; `es:((A)crep_exp)list`;
                `a:((A)word_lab)list`; `z:((A)word_lab)list`] evaluate_nested_seq_assign) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN FS[var_prog_def]; ALL_TAC] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  SIMP[] THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN SIMP[] THEN
  FS[crep_inlineProof_state_rel_def];;

let PCINLAUX_C_TB_DEC_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[var_prog_def; transform_branch_def; MEM_APPEND; MEM; DE_MORGAN_THM] THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  QCASES_ON "crep_eval s e" THEN SIMP[] THENL [REPEAT STRIP_TAC THEN GVS[]; ALL_TAC] THEN
  RENAME1 "crep_eval s e = SOME value" THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `value:(A)word_lab`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  SUBGOAL_THEN `?res' st. crep_evaluate (prog,crep_state_locals_fupd
                   (K (crep_state_locals s |+ (v,value))) (s:(A,FFI)crep_state)) = (res',st)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  REPEAT STRIP_TAC THEN
  REMOVE_THEN "ih" (MP_TAC o PCINLAUX_C_SPEC_FIRST
    [`res':((A)crep_result)option`; `st:(A,FFI)crep_state`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[];
      SIMP[] THEN MATCH_MP_TAC opt_mmap_some_imp_fupdate_exist_some THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
  QPAT_X_ASSUM "_ = s'" (SUBST_ALL_TAC o SYM) THEN
  CONJ_TAC THENL [FS[crep_inlineProof_state_rel_def]; ALL_TAC] THEN
  QCASES_ON "r" THEN FS[locals_strong_rel_def] THEN
  TRY(TOP_CASE_TAC THEN FS[locals_strong_rel_def]) THEN
  SUBGOAL_THEN `~MEM (v:num) rts` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  QCASES_ON "FLOOKUP (crep_state_locals s) v" THEN SIMP[crep_res_var_def] THENL
   [MATCH_MP_TAC opt_mmap_flookup_not_mem_domsub; MATCH_MP_TAC opt_mmap_flookup_update] THEN
  ASM_REWRITE_TAC[];;

let PCINLAUX_C_TB_SEQ_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[var_prog_def; transform_branch_def; MEM_APPEND; DE_MORGAN_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?res1 s1. crep_evaluate (c1,s:(A,FFI)crep_state) = (res1,s1)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  QPAT_X_ASSUM "crep_evaluate (crep_Seq _ _,_) = _"
    (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  ASM_CASES_TAC `res1:((A)crep_result)option = NONE` THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THENL
   [(* the first part finishes normally *)
    QPAT_X_ASSUM "res1 = NONE" SUBST_ALL_TAC THEN
    REMOVE_THEN "ih1" (MP_TAC o PCINLAUX_C_SPEC_FIRST
      [`NONE:((A)crep_result)option`; `s1:(A,FFI)crep_state`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMP[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SIMP[locals_strong_rel_def] THEN STRIP_TAC THEN
    SUBGOAL_THEN `s1' = (s1:(A,FFI)crep_state)` SUBST_ALL_TAC THENL
     [FS[crep_state_component_equality; crep_inlineProof_state_rel_def]; ALL_TAC] THEN
    REMOVE_THEN "ih2" (MP_TAC o SPEC `s1:(A,FFI)crep_state`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o PCINLAUX_C_SPEC_FIRST
      [`r:((A)crep_result)option`; `s':(A,FFI)crep_state`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(ISPECL [`rts:num list`; `crep_state_locals (s:(A,FFI)crep_state)`;
                           `crep_state_locals (s1:(A,FFI)crep_state)`; `z:((A)word_lab)list`]
                          fdoms_eq_opt_mmap_flookup_some) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC evaluate_locals_same_fdom' THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
    ASM_REWRITE_TAC[] THEN FS[locals_strong_rel_def];
    (* it exits early *)
    RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    REMOVE_THEN "ih1" (MP_TAC o PCINLAUX_C_SPEC_FIRST
      [`r:((A)crep_result)option`; `s':(A,FFI)crep_state`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(r1 = NONE:((A)crep_result)option)` ASSUME_TAC THENL
     [QCASES_ON "r" THEN FS[] THEN EVERY_CASE_TAC THEN FS[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[crep_evaluate_def] THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
    ASM_REWRITE_TAC[]];;

let PCINLAUX_C_TB_IF_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[var_prog_def; transform_branch_def; MEM_APPEND; DE_MORGAN_THM] THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  QCASES_ON "crep_eval s e" THEN SIMP[] THENL [REPEAT STRIP_TAC THEN GVS[]; ALL_TAC] THEN
  STRIP_TAC THEN QCASES_ON "a" THEN FS[] THEN
  FIRST_X_ASSUM(MP_TAC o PCINLAUX_C_SPEC_FIRST
    [`r:((A)crep_result)option`; `s':(A,FFI)crep_state`]) THEN
  ASM_CASES_TAC `a' = word 0:A word` THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP[]; ASM_MESON_TAC[]; SIMP[]];;

(* the first assumption that contains tm *)

let PCINLAUX_C_TB_WHILE_AGAIN (res1:term) : tactic =
  SUBGOAL_THEN `s1' = (s1:(A,FFI)crep_state)` SUBST_ALL_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[crep_inlineProof_state_rel_def; locals_strong_rel_def]) THEN
    ASM_REWRITE_TAC[crep_state_component_equality];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) &&
       can (find_term (aconv `transform_branch ld rts (crep_While e (c:(A)crep_prog))`))
           (concl th)
    then MP_TAC(PCINLAUX_C_SPEC_TYPED [`r:((A)crep_result)option`; `s':(A,FFI)crep_state`;
                                       `ld:num`] th)
    else failwith "WHILE_AGAIN") THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[var_prog_def; MEM_APPEND; DE_MORGAN_THM] THEN
    MATCH_MP_TAC(ISPECL [`rts:num list`; `crep_state_locals (s:(A,FFI)crep_state)`;
                         `crep_state_locals (s1:(A,FFI)crep_state)`; `z:((A)word_lab)list`]
                        fdoms_eq_opt_mmap_flookup_some) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(A)crep_prog`; `crep_dec_clock (s:(A,FFI)crep_state)`;
                   res1; `s1:(A,FFI)crep_state`]
                  evaluate_locals_same_fdom') THEN
    ASM_REWRITE_TAC[dec_clock_simp] THEN SIMP[];
    ALL_TAC] THEN
  REWRITE_TAC[transform_branch_def] THEN STRIP_TAC THEN ASM_EXISTS_TAC THEN ASM_REWRITE_TAC[];;

let PCINLAUX_C_TB_WHILE_TAC : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihc") (CONJUNCTS_THEN2 (LABEL_TAC "ihn")
                                                               (LABEL_TAC "ihb"))) THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[var_prog_def; transform_branch_def; MEM_APPEND; DE_MORGAN_THM] THEN
  STRIP_TAC THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  QPAT_X_ASSUM "crep_evaluate (crep_While _ _,_) = _"
    (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
  QCASES_ON "crep_eval s e" THEN SIMP[] THEN QCASES_ON "a" THEN SIMP[] THEN
  ASM_CASES_TAC `a' = word 0:A word` THEN ASM_REWRITE_TAC[] THEN SIMP[PAIR_EQ] THENL
   [DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    SIMP[crep_inlineProof_state_rel_def; locals_strong_rel_def];
    ALL_TAC] THEN
  ASM_CASES_TAC `crep_state_clock (s:(A,FFI)crep_state) = 0` THEN ASM_REWRITE_TAC[] THEN
  SIMP[PAIR_EQ] THENL
   [DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    SIMP[crep_inlineProof_state_rel_def; crep_empty_locals_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `?res1 s1. crep_evaluate (c,crep_dec_clock s) = (res1,s1:(A,FFI)crep_state)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(res1 = SOME (crep_Error:(A)crep_result))` ASSUME_TAC THENL
   [DISCH_TAC THEN GVS[]; ALL_TAC] THEN
  REMOVE_THEN "ihb" (MP_TAC o SPEC `a':A word`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o PCINLAUX_C_SPEC_TYPED [`res1:((A)crep_result)option`;
                                              `s1:(A,FFI)crep_state`; `ld + 1`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[dec_clock_simp] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN GVS[];
      CONJ_TAC THENL [ASM_MESON_TAC[]; MESON_TAC[]]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
  NAMED_CASES_ON "res1" ["";"rr"] THEN RFS[] THENL
   [PCINLAUX_C_TB_WHILE_AGAIN `NONE:((A)crep_result)option`;
    NAMED_CASES_ON "rr" ["";"";"nn";"nn";"vs";"eid";"fe"] THEN RFS[] THEN
    TRY(ASM_CASES_TAC `nn = 0` THEN RFS[]) THEN
    TRY(PCINLAUX_C_TB_WHILE_AGAIN `SOME (crepSem_Continue 0):((A)crep_result)option` THEN
        NO_TAC) THEN
    GVS[ARITH_ss; locals_strong_rel_def; crep_inlineProof_state_rel_def]];;

let PCINLAUX_C_TB_CALL_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihc") (LABEL_TAC "ihh")) THEN
  REPEAT GEN_TAC THEN
  NAMED_CASES_ON "caltyp" ["";"ct"] THENL
   [ALL_TAC; NAMED_CASES_ON "ct" ["rs hd"] THEN NAMED_CASES_ON "hd" ["";"wh"] THENL
     [ALL_TAC; NAMED_CASES_ON "wh" ["w hdl"]]] THEN
  REWRITE_TAC[var_prog_def; transform_branch_def] THEN SIMP[] THENL
   [(* tail call: assign the results, then leave the loop *)
    STRIP_TAC THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  QPAT_X_ASSUM "crep_evaluate (crep_Call _ _ _,_) = _"
    (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
  DISCH_TAC THEN GVS_ASM(crep_empty_locals_def :: all_case_eqs()) THEN
  ASM_REWRITE_TAC[] THEN SIMP[crep_empty_locals_def; crep_inlineProof_state_rel_def] THEN
  ASM_SIMP_TAC[opt_mmap_some_eq_zip_flookup];
    (* no handler: transform_branch is the identity *)
    STRIP_TAC THEN
  SUBGOAL_THEN `!retvs. ~(r = SOME (crepSem_Return retvs:(A)crep_result))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC not_has_return_not_evaluate_return' THEN ASM_EXISTS_TAC THEN
    ASM_REWRITE_TAC[has_return_def] THEN SIMP[];
    ALL_TAC] THEN
  TRY ASM_EXISTS_TAC THEN REWRITE_TAC[crep_inlineProof_state_rel_def; locals_strong_rel_def] THEN
  QCASES_ON "r" THEN SIMP[] THEN QCASES_ON "a" THEN FS[] THEN ASM_MESON_TAC[];
    (* a handler: transformed in the same way *)
    STRIP_TAC THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  QPAT_X_ASSUM "crep_evaluate (crep_Call _ _ _,_) = _"
    (MP_TAC o ONCE_REWRITE_RULE[crep_evaluate_def]) THEN
  DISCH_TAC THEN GVS_ASM(crep_empty_locals_def :: all_case_eqs()) THEN
  ASM_REWRITE_TAC[] THEN SIMP[crep_empty_locals_def; crep_inlineProof_state_rel_def;
                             locals_strong_rel_def] THEN
    PCINLAUX_C_ASSUM_WITH `transform_branch ld rts (hdl:(A)crep_prog)`
    (MP_TAC o SPECL [`ld:num`; `rts:num list`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_EXISTS_TAC THEN
  FS[crep_inlineProof_state_rel_def; locals_strong_rel_def]];;

let transform_branch_correct = prove
 (CASE_TERM `!p (s:(A,FFI)crep_state) r s' (res:B) ld rts.
     crep_evaluate (p,s) = (r,s') /\
     (!retvs. r = SOME (crepSem_Return retvs) ==> LENGTH rts = LENGTH retvs) /\
     (!x. MEM x rts ==> ~MEM x (var_prog p)) /\
     (?z. OPT_MMAP (FLOOKUP (crep_state_locals s)) rts = SOME z) /\
     ALL_DISTINCT rts /\
     ~(r = SOME crep_Error)
     ==> ?r1 s1'. crep_evaluate (transform_branch ld rts p,s) = (r1,s1') /\
                  crep_inlineProof_state_rel s' s1' /\
                  (match r with
                     NONE -> r1 = NONE /\ locals_strong_rel s' s1'
                   | SOME (crepSem_Break n) ->
                       r1 = SOME (crepSem_Break n) /\ locals_strong_rel s' s1'
                   | SOME (crepSem_Continue n) ->
                       r1 = SOME (crepSem_Continue n) /\ locals_strong_rel s' s1'
                   | SOME (crepSem_Return retvs) ->
                       r1 = SOME (crepSem_Break ld) /\
                       OPT_MMAP (FLOOKUP (crep_state_locals s1')) rts = SOME retvs
                   | SOME crep_Error -> F
                   | x -> r1 = x)`,
  REC_IND_TAC crep_evaluate_ind THEN REPEAT CONJ_TAC THEN
  PCINLAUX_PROG_CASES
   ["crep_While",PCINLAUX_C_TB_WHILE_TAC; "crep_Call",PCINLAUX_C_TB_CALL_TAC;
    "crep_Dec",PCINLAUX_C_TB_DEC_TAC; "crep_If",PCINLAUX_C_TB_IF_TAC;
    "crep_Seq",PCINLAUX_C_TB_SEQ_TAC; "crep_Return",PCINLAUX_C_TB_RET_TAC]
   PCINLAUX_C_TB_ID_TAC);;

(* ------------------------------------------------------------------------- *)
(* The wrapped transformation and the variables of the transformed code     *)
(* (HOL4 lines 2168-2299).                                                   *)
(* ------------------------------------------------------------------------- *)

let cont_res_def = cake_def
  `(cont_res (NONE:((A)crep_result)option) <=> T) /\
   (cont_res (SOME (crepSem_Break n)) <=> T) /\
   (cont_res (SOME (crepSem_Continue n)) <=> T) /\
   (cont_res (SOME crep_Error) <=> T) /\
   (cont_res _ <=> F)`;;

let wrapped_transform_if = prove
 (CASE_TERM `!p (s:(A,FFI)crep_state) r s' res rts loc.
     crep_evaluate (p,crep_state_locals_fupd (K loc) (crep_dec_clock s)) = (r,s') /\
     unreach_elim p = (p,res) /\
     (!retvs. r = SOME (crepSem_Return retvs) ==> LENGTH rts = LENGTH retvs) /\
     (!x. MEM x rts ==> ~MEM x (var_prog p)) /\
     (?z. OPT_MMAP (FLOOKUP loc) rts = SOME z) /\
     ALL_DISTINCT rts /\
     ~cont_res r /\
     ~(crep_state_clock s = 0) /\
     ~(r = SOME crep_Error)
     ==> ?r1 s1'.
           crep_evaluate
             ((if not_branch_ret p then crep_Seq crep_Tick (transform_eoc rts p)
               else crep_While (crep_Const (word 1)) (transform_branch 0 rts p)),
              crep_state_locals_fupd (K loc) s) = (r1,s1') /\
           crep_inlineProof_state_rel s' s1' /\
           (match r with
              SOME (crepSem_Return retvs) ->
                r1 = NONE /\ OPT_MMAP (FLOOKUP (crep_state_locals s1')) rts = SOME retvs
            | SOME (crep_Exception eid) -> r1 = SOME (crep_Exception eid)
            | SOME crep_TimeOut -> r1 = SOME crep_TimeOut
            | SOME (crep_FinalFFI ffi) -> r1 = SOME (crep_FinalFFI ffi)
            | _ -> F)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `not_branch_ret (p:(A)crep_prog)` THEN
  ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`p:(A)crep_prog`;
                   `crep_state_locals_fupd (K loc) (crep_dec_clock (s:(A,FFI)crep_state))`;
                   `r:((A)crep_result)option`; `s':(A,FFI)crep_state`;
                   `res:(early_exit)option`; `rts:num list`] transform_eoc_correct) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SIMP[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
    ONCE_REWRITE_TAC[crep_evaluate_def] THEN
    SUBGOAL_THEN `crep_dec_clock (crep_state_locals_fupd (K loc) (s:(A,FFI)crep_state)) =
                  crep_state_locals_fupd (K loc) (crep_dec_clock s)` SUBST1_TAC THENL
     [SIMP[crep_dec_clock_def; crep_state_component_equality]; ALL_TAC] THEN
    SIMP[] THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
    QCASES_ON "r" THEN FS[cont_res_def] THEN TOP_CASE_TAC THEN FS[cont_res_def];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:(A)crep_prog`;
                 `crep_state_locals_fupd (K loc) (crep_dec_clock (s:(A,FFI)crep_state))`;
                 `r:((A)crep_result)option`; `s':(A,FFI)crep_state`;
                 `res:(early_exit)option`; `0`; `rts:num list`] transform_branch_correct) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SIMP[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  REWRITE_TAC[crep_eval_def] THEN SIMP[WORD_NE_10] THEN
  SUBGOAL_THEN `crep_dec_clock (crep_state_locals_fupd (K loc) (s:(A,FFI)crep_state)) =
                crep_state_locals_fupd (K loc) (crep_dec_clock s)` SUBST1_TAC THENL
   [SIMP[crep_dec_clock_def; crep_state_component_equality]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  QCASES_ON "r" THEN FS[cont_res_def] THEN QCASES_ON "a" THEN FS[cont_res_def]);;

let mem_var_prog_nested_seq = prove
 (`!ps (x:num).
     MEM x (var_prog (crep_nested_seq ps:(A)crep_prog)) <=> MEM x (FLAT (MAP var_prog ps))`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[crep_nested_seq_def; var_prog_def; MAP; FLAT; MEM;
                                       MEM_APPEND]);;

(* HOL4's MAP2 truncates the longer list; with HOL Light's MAP2 (HD/TL of    *)
(* the second list) the statement holds when the first list is not longer:  *)
(* the hypothesis LENGTH l1 <= LENGTH l2 is added.                           *)

let MEM_MAP2_IMP = prove
 (`!(f:A->B->C) l1 l2 x.
     LENGTH l1 <= LENGTH l2 /\ MEM x (MAP2 f l1 l2)
     ==> ?y1 y2. x = f y1 y2 /\ MEM y1 l1 /\ MEM y2 l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN QCASES_ON "l2" THEN
  SIMP[MAP2; MAP2_DEF; MEM; LENGTH; LE_SUC] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* the variables of the assignments that replace a Return *)

let PCINLAUX_C_MEM_VAR_PROG_ASSIGNS = prove
 (`!(es:((A)crep_exp)list) rets x.
     MEM x (var_prog (crep_nested_seq (MAP2 crep_Assign (TAKE (LENGTH es) rets) es)))
     ==> MEM x (FLAT (MAP var_cexp es)) \/ MEM x rets`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN QCASES_ON "rets" THEN
  REWRITE_TAC[LENGTH; TAKE_DEF; MAP2; MAP2_DEF; crep_nested_seq_def; var_prog_def; MEM;
              NOT_SUC; SUC_SUB1; MAP; FLAT; MEM_APPEND] THEN
  ASM_MESON_TAC[]);;

(* the same for a function whose last argument is the program *)

let PCINLAUX_C_CASES_BY_LAST (fname:string) (cases:(string*tactic) list) (dflt:tactic)
    : tactic =
  fun (asl,w as g) ->
    let is_app t =
      let h,args = strip_comb t in
      (try fst(dest_const h) = fname with Failure _ -> false) && args <> [] &&
      (try is_constructor_app(last args) with Failure _ -> false) in
    let name =
      try fst(dest_const(fst(strip_comb(last(snd(strip_comb(find_term is_app w)))))))
      with Failure _ -> "" in
    (try assoc name cases with Failure _ -> dflt) g;;

let PCINLAUX_C_MVP_DFLT : tactic =
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[transform_eoc_def; transform_branch_def; var_prog_def;
                              MEM_APPEND]) THEN
  REWRITE_TAC[var_prog_def; MEM_APPEND] THEN ASM_MESON_TAC[];;

let PCINLAUX_C_MVP_CALL : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  NAMED_CASES_ON "ctyp" ["";"ct"] THENL
   [ALL_TAC; NAMED_CASES_ON "ct" ["rs hd"] THEN NAMED_CASES_ON "hd" ["";"wh"] THENL
     [ALL_TAC; NAMED_CASES_ON "wh" ["w hdl"]]] THEN
  FS[transform_eoc_def; transform_branch_def; var_prog_def; MEM_APPEND] THEN
  ASM_MESON_TAC[];;

let PCINLAUX_C_MVP_RET : tactic =
  REPEAT STRIP_TAC THEN REWRITE_TAC[var_prog_def] THEN
  MATCH_MP_TAC PCINLAUX_C_MEM_VAR_PROG_ASSIGNS THEN
  RULE_ASSUM_TAC(REWRITE_RULE[transform_eoc_def; transform_branch_def; var_prog_def;
                              MEM_APPEND; MEM]) THEN
  ASM_REWRITE_TAC[];;

let mem_var_prog_transform_eoc = prove
 (`!rts (p:(A)crep_prog) x.
     MEM x (var_prog (transform_eoc rts p)) ==> MEM x (var_prog p) \/ MEM x rts`,
  REC_IND_TAC transform_eoc_ind THEN REPEAT CONJ_TAC THEN
  PCINLAUX_C_CASES_BY_LAST "transform_eoc"
   ["crep_Return",PCINLAUX_C_MVP_RET; "crep_Call",PCINLAUX_C_MVP_CALL]
   PCINLAUX_C_MVP_DFLT);;

let mem_var_prog_transform_branch = prove
 (`!ld rts (p:(A)crep_prog) x.
     MEM x (var_prog (transform_branch ld rts p)) ==> MEM x (var_prog p) \/ MEM x rts`,
  REC_IND_TAC transform_branch_ind THEN REPEAT CONJ_TAC THEN
  PCINLAUX_C_CASES_BY_LAST "transform_branch"
   ["crep_Return",PCINLAUX_C_MVP_RET; "crep_Call",PCINLAUX_C_MVP_CALL]
   PCINLAUX_C_MVP_DFLT);;

let PCINLAUX_C_UEP_GEN : tactic =
  REPEAT GEN_TAC THEN TRY DISCH_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[unreach_elim_def] THEN
  REWRITE_TAC[has_return_def; not_branch_ret_def] THEN
  REPEAT(PAIRARG_TAC THEN ASM_REWRITE_TAC[]) THEN
  RW[] THEN GVS(unreach_elim_def :: has_return_def :: not_branch_ret_def :: all_case_eqs());;

let unreach_elim_preserve_has_return = prove
 (`!(p:(A)crep_prog) q r.
     ~has_return p /\ unreach_elim p = (q,r) ==> ~has_return q`,
  REC_IND_TAC has_return_ind THEN REPEAT CONJ_TAC THEN PCINLAUX_C_UEP_GEN);;

let unreach_elim_preserve_not_branch_ret = prove
 (`!(p:(A)crep_prog) q r.
     not_branch_ret p /\ unreach_elim p = (q,r) ==> not_branch_ret q`,
  REC_IND_TAC not_branch_ret_ind THEN REPEAT CONJ_TAC THEN PCINLAUX_C_UEP_GEN THEN
  IMP_RES_TAC unreach_elim_preserve_has_return THEN GVS[]);;

(* ------------------------------------------------------------------------- *)
(* Helpers of the Nontail case of inline_prog_correct (HOL4 lines 2573-2717) *)
(* ------------------------------------------------------------------------- *)

let crep_inlineProof_evaluate_replicate_const = prove
 (`!n (s:(A,FFI)crep_state).
     OPT_MMAP (crep_eval s) (REPLICATE n (crep_Const (word 0))) =
     SOME (REPLICATE n (Word (word 0)))`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE; OPT_MMAP_def; crep_eval_def] THEN SIMP[]);;

let max_list_genlist_add_suc_val = prove
 (`~(n = 0) ==> MAX_LIST (list_of_seq (\x. SUC x + k) n) = n + k`,
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN REWRITE_TAC[NOT_SUC] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_SIMP_TAC[GENLIST; SNOC; MAX_LIST; MAX] THEN
  SIMP[MAX_LIST_SNOC] THEN ARITH_TAC);;

let update_list_locals_not_vars_eval_eq = prove
 (`!vs (s:(A,FFI)crep_state) res e vals.
     (!x. MEM x vs ==> ~MEM x (var_cexp e)) /\ crep_eval s e = res /\ LENGTH vs = LENGTH vals
     ==> crep_eval (crep_state_locals_fupd (K (crep_state_locals s |++ ZIP vs vals)) s) e = res`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN CASES_ON `vals:((A)word_lab)list` THEN
  SIMP[LENGTH; NOT_SUC; ZIP_def; FUPDATE_LIST_THM; RECORD_SELFID_ss; MEM] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`crep_state_locals_fupd (K (crep_state_locals s |+ (h,a0))) (s:(A,FFI)crep_state)`;
     `res:((A)word_lab)option`; `e:(A)crep_exp`; `a1:((A)word_lab)list`]) THEN
  SIMP[] THEN DISCH_THEN MATCH_MP_TAC THEN
  QPAT_X_ASSUM "crep_eval s e = res" (SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC update_locals_not_vars_eval_eq' THEN ASM_MESON_TAC[]);;

let opt_mmap_update_list_locals_not_vars_eval_eq = prove
 (`!es vs vals (s:(A,FFI)crep_state) res.
     (!x. MEM x vs ==> ~MEM x (FLAT (MAP var_cexp es))) /\ OPT_MMAP (crep_eval s) es = res /\
     LENGTH vs = LENGTH vals
     ==> OPT_MMAP (crep_eval (crep_state_locals_fupd (K (crep_state_locals s |++ ZIP vs vals)) s))
           es = res`,
  REPEAT STRIP_TAC THEN QPAT_X_ASSUM "OPT_MMAP (crep_eval s) es = res" (SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC OPT_MMAP_ALL_EQ THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC update_list_locals_not_vars_eval_eq THEN ASM_REWRITE_TAC[] THEN
  FS[MEM_FLAT; MEM_MAP] THEN ASM_MESON_TAC[]);;

let opt_mmap_update_list_locals_not_vars_eval_eq' = prove
 (`!es vs (ws:B list) vals (s:(A,FFI)crep_state) locs.
     (!x. MEM x vs ==> ~MEM x (FLAT (MAP var_cexp es))) /\ LENGTH vs = LENGTH vals
     ==> OPT_MMAP (crep_eval (crep_state_locals_fupd (K (locs |++ ZIP vs vals)) s)) es =
         OPT_MMAP (crep_eval (crep_state_locals_fupd (K locs) s)) es`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`es:((A)crep_exp)list`; `vs:num list`; `vals:((A)word_lab)list`;
                 `crep_state_locals_fupd (K locs) (s:(A,FFI)crep_state)`;
                 `OPT_MMAP (crep_eval (crep_state_locals_fupd (K locs) (s:(A,FFI)crep_state))) es`]
                opt_mmap_update_list_locals_not_vars_eval_eq) THEN
  ASM_REWRITE_TAC[] THEN SIMP[]);;

(* HOL4 [local]; HOL4's variables val and val2 are value and value2 here *)

let FDIFF_fupdate_list_empty_flookup_var = prove
 (`!(fm:(K,V)fmap) zs value (value2:W) fm' x v.
     FDIFF (fm |++ ZIP zs (REPLICATE (LENGTH zs) value))
       (FDOM (FEMPTY |++ ZIP zs (REPLICATE (LENGTH zs) value2))) SUBMAP fm' /\
     FLOOKUP fm x = SOME v /\ ~MEM x zs
     ==> FLOOKUP fm' x = SOME v`,
  REPEAT STRIP_TAC THEN QPAT_X_ASSUM "_ SUBMAP _" (MP_TAC o REWRITE_RULE[SUBMAP_FLOOKUP_EQN]) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[FLOOKUP_FDIFF; FDOM_FUPDATE_LIST; MAP_ZIP; LENGTH_REPLICATE; FDOM_FEMPTY;
               UNION_EMPTY; IN_SET_OF_LIST; flookup_fupdate_zip_not_mem]);;

let FDIFF_fupdate_list_empty_flookup = prove
 (`!xs (fm:(K,V)fmap) zs value (value2:W) fm' vs.
     FDIFF (fm |++ ZIP zs (REPLICATE (LENGTH zs) value))
       (FDOM (FEMPTY |++ ZIP zs (REPLICATE (LENGTH zs) value2))) SUBMAP fm' /\
     OPT_MMAP (FLOOKUP fm) xs = SOME vs /\ (!x. MEM x xs ==> ~MEM x zs)
     ==> OPT_MMAP (FLOOKUP fm') xs = SOME vs`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PCINLAUX_OPT_MMAP_SOME_IMP THEN
  EXISTS_TAC `FLOOKUP (fm:(K,V)fmap)` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FDIFF_fupdate_list_empty_flookup_var THEN
  MAP_EVERY EXISTS_TAC [`fm:(K,V)fmap`; `zs:K list`; `value:V`; `value2:W`] THEN
  ASM_MESON_TAC[]);;

let FOLDL_res_var_ZIP_lookup_var = prove
 (`!(l:(K,V)fmap) ns l' l1 x v.
     FOLDL crep_res_var l (ZIP ns (MAP (FLOOKUP l') ns)) SUBMAP l1 /\
     FLOOKUP l x = SOME v /\ ~MEM x ns
     ==> FLOOKUP l1 x = SOME v`,
  REPEAT STRIP_TAC THEN QPAT_X_ASSUM "_ SUBMAP _" (MP_TAC o REWRITE_RULE[SUBMAP_FLOOKUP_EQN]) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[flookup_res_var_distinct_zip_eq; LENGTH_MAP]);;

let FOLDL_res_var_ZIP_lookup = prove
 (`!(l:(K,V)fmap) ns l' l1 xs vs.
     FOLDL crep_res_var l (ZIP ns (MAP (FLOOKUP l') ns)) SUBMAP l1 /\
     OPT_MMAP (FLOOKUP l) xs = SOME vs /\ (!x. MEM x xs ==> ~MEM x ns)
     ==> OPT_MMAP (FLOOKUP l1) xs = SOME vs`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PCINLAUX_OPT_MMAP_SOME_IMP THEN
  EXISTS_TAC `FLOOKUP (l:(K,V)fmap)` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FOLDL_res_var_ZIP_lookup_var THEN
  MAP_EVERY EXISTS_TAC [`l:(K,V)fmap`; `ns:K list`; `l':(K,V)fmap`] THEN
  ASM_MESON_TAC[]);;

let submap_finish_flookup = prove
 (`!(fm:(K,V)fmap) q l fm' ns.
     (!x y. ~MEM x q /\ ~MEM x ns /\ FLOOKUP fm x = SOME y ==> FLOOKUP fm' x = SOME y) /\
     (!x. MEM x q ==> ~MEM x ns) /\
     ALL_DISTINCT q /\
     OPT_MMAP (FLOOKUP fm') q = SOME l
     ==> fm |++ ZIP q l SUBMAP FOLDL crep_res_var fm' (ZIP ns (MAP (FLOOKUP fm) ns))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBMAP_FLOOKUP_EQN] THEN
  X_GEN_TAC `x:K` THEN X_GEN_TAC `y:V` THEN
  SUBGOAL_THEN `LENGTH (q:K list) = LENGTH (l:V list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[opt_mmap_length_eq]; ALL_TAC] THEN
  ASM_CASES_TAC `MEM (x:K) q` THENL
   [SUBGOAL_THEN `~MEM (x:K) ns` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?n. n < LENGTH (q:K list) /\ x = EL n q` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM list_MEM_EL] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  QPAT_X_ASSUM "x = EL n q" SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[update_eq_zip_flookup; flookup_res_var_distinct_zip_eq; LENGTH_MAP] THEN
  MP_TAC(ISPECL [`q:K list`; `FLOOKUP (fm':(K,V)fmap)`; `l:V list`; `n:num`] opt_mmap_el) THEN
  ASM_REWRITE_TAC[] THEN SIMP[option_INJ];
    ASM_SIMP_TAC[flookup_fupdate_zip_not_mem] THEN DISCH_TAC THEN
  ASM_CASES_TAC `MEM (x:K) ns` THENL
   [ASM_SIMP_TAC[flookup_res_var_is_mem_zip_eq];
    ASM_SIMP_TAC[flookup_res_var_distinct_zip_eq; LENGTH_MAP] THEN
    QPAT_X_ASSUM "!x y. _" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* inline_prog_correct (HOL4 lines 2301-2571 and 2719-3037; the Call case   *)
(* last, as in HOL4's suspend/Resume).                                       *)
(* ------------------------------------------------------------------------- *)

(* crep_sh_mem_op in a state with the same locals and another code *)

let PCINLAUX_sh_mem_op_code = prove
 (`!op v (a:A word) (s:(A,FFI)crep_state) s1 (r:((B)crep_result)option) s'.
     crep_sh_mem_op op v a s = (r,s') /\ state_rel_code s s1 /\
     crep_state_locals s = crep_state_locals s1
     ==> ?s1'. crep_sh_mem_op op v a s1 = (r,s1') /\ state_rel_code s' s1' /\
               crep_state_locals s' = crep_state_locals s1' /\
               crep_state_code s' = crep_state_code s /\
               crep_state_code s1' = crep_state_code s1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[state_rel_code_def] THEN STRIP_TAC THEN
  QPAT_X_ASSUM "crep_sh_mem_op _ _ _ _ = _" MP_TAC THEN QCASES_ON "op" THEN
  ASM_REWRITE_TAC[crep_sh_mem_op_def; crep_sh_mem_load_def; crep_sh_mem_store_def] THEN
  DISCH_TAC THEN GVS_ASM(crep_set_var_def :: crep_empty_locals_def :: all_case_eqs()) THEN
  ASM_REWRITE_TAC[] THEN SIMP[crep_set_var_def; crep_empty_locals_def]);;


(* introducing the recurring result case: only the normal results need P *)

let PCINLAUX_RES_CASE_INTRO = prove
 (CASE_TERM `!(r:((A)crep_result)option) P.
     ~(r = SOME crep_Error) /\
     ((r = NONE \/ (?n. r = SOME (crepSem_Break n)) \/ (?n. r = SOME (crepSem_Continue n)))
      ==> P)
     ==> (match r with
            NONE -> P
          | SOME (crepSem_Break n) -> P
          | SOME (crepSem_Continue n) -> P
          | SOME crep_Error -> F
          | _ -> T)`,
  GEN_TAC THEN QCASES_ON "r" THEN SIMP[] THEN QCASES_ON "a" THEN SIMP[] THEN
  MESON_TAC[]);;


let PCINLAUX_IPC_STMT = CASE_TERM
 `!p (s:(A,FFI)crep_state) r s' inl_fs s1 inl_bag.
    crep_evaluate (p,s) = (r,s') /\
    ~(r = SOME crep_Error) /\
    inl_fs SUBMAP crep_state_code s /\
    inl_bag SUBMAP inl_fs /\
    state_rel_code s s1 /\
    locals_strong_rel s s1 /\
    code_inl_rel inl_fs s s1
    ==> ?s1'. crep_evaluate (inline_prog inl_bag p,s1) = (r,s1') /\
              state_rel_code s' s1' /\
              code_inl_rel inl_fs s' s1' /\
              (match r with
                 NONE -> locals_strong_rel s' s1'
               | SOME (crepSem_Break n) -> locals_strong_rel s' s1'
               | SOME (crepSem_Continue n) -> locals_strong_rel s' s1'
               | SOME crep_Error -> F
               | _ -> T)`;;
let PCINLAUX_IPC_GEN : tactic =
  REPEAT STRIP_TAC THEN QPAT_X_ASSUM "crep_evaluate _ = _" MP_TAC THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN DISCH_TAC THEN
  GVS([crep_set_globals_def; crep_empty_locals_def; crep_dec_clock_def] @ all_case_eqs()) THEN
  IMP_RES_TAC eval_code_inl THEN IMP_RES_TAC opt_mmap_eval_code_inl THEN
  RULE_ASSUM_TAC(REWRITE_RULE[state_rel_code_def; locals_strong_rel_def]) THEN FS[] THEN
  REWRITE_TAC[inline_prog_def] THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  SIMP[PAIR_EQ; crep_set_globals_def; crep_empty_locals_def; crep_dec_clock_def;
       state_rel_code_def; locals_strong_rel_def] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[code_inl_rel_def]) THEN ASM_SIMP_TAC[code_inl_rel_def] THEN SIMP[];;

let PCINLAUX_IPC_SHMEM_TAC : tactic =
  PCINLAUX_IPC_GEN THEN
  (DRULE PCINLAUX_sh_mem_op_code THEN DISCH_THEN(QSPEC_THEN "s1" MP_TAC) THEN
   ASM_REWRITE_TAC[state_rel_code_def] THEN STRIP_TAC THEN ASM_EXISTS_TAC THEN
   FS[state_rel_code_def] THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC PCINLAUX_RES_CASE_INTRO THEN ASM_REWRITE_TAC[locals_strong_rel_def]);;

let PCINLAUX_IPC_DEC_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  QPAT_X_ASSUM "crep_evaluate _ = _" MP_TAC THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  QCASES_ON "crep_eval s e" THEN SIMP[] THEN
  RENAME1 "crep_eval s e = SOME value" THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `value:(A)word_lab`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  SUBGOAL_THEN `?res st. crep_evaluate (prog,crep_state_locals_fupd
                   (K (crep_state_locals s |+ (v,value))) (s:(A,FFI)crep_state)) = (res,st)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC eval_code_inl THEN
  REWRITE_TAC[inline_prog_def] THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`res:((A)crep_result)option`; `st:(A,FFI)crep_state`;
     `inl_fs:(mlstring,num list # (A)crep_prog)fmap`;
     `crep_state_locals_fupd (K (crep_state_locals s1 |+ (v,value))) (s1:(A,FFI)crep_state)`;
     `inl_bag:(mlstring,num list # (A)crep_prog)fmap`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FS[state_rel_code_def; locals_strong_rel_def; code_inl_rel_def]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
  QPAT_X_ASSUM "_ = s'" (SUBST_ALL_TAC o SYM) THEN
  REPEAT CONJ_TAC THENL
   [FS[state_rel_code_def];
    FS[code_inl_rel_def];
    MATCH_MP_TAC PCINLAUX_RES_CASE_MONO THEN ASM_EXISTS_TAC THEN
    REWRITE_TAC[locals_strong_rel_def] THEN REPEAT STRIP_TAC THEN SIMP[] THEN
    FS[locals_strong_rel_def]];;

let PCINLAUX_IPC_SEQ_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?res1 s2. crep_evaluate (c1,s:(A,FFI)crep_state) = (res1,s2)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  QPAT_X_ASSUM "crep_evaluate (crep_Seq _ _,_) = _" MP_TAC THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN DISCH_TAC THEN
  REWRITE_TAC[inline_prog_def] THEN SIMP[] THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  SUBGOAL_THEN `~(res1 = SOME (crep_Error:(A)crep_result))` ASSUME_TAC THENL
   [DISCH_TAC THEN RFS[] THEN NO_TAC; ALL_TAC] THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`res1:((A)crep_result)option`; `s2:(A,FFI)crep_state`;
     `inl_fs:(mlstring,num list # (A)crep_prog)fmap`; `s1:(A,FFI)crep_state`;
     `inl_bag:(mlstring,num list # (A)crep_prog)fmap`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t1:(A,FFI)crep_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  ASM_CASES_TAC `res1:((A)crep_result)option = NONE` THENL
   [ALL_TAC; GVS[] THEN NO_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  REMOVE_THEN "ih2" (MP_TAC o SPEC `s2:(A,FFI)crep_state`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`r:((A)crep_result)option`; `s':(A,FFI)crep_state`;
     `inl_fs:(mlstring,num list # (A)crep_prog)fmap`; `t1:(A,FFI)crep_state`;
     `inl_bag:(mlstring,num list # (A)crep_prog)fmap`]) THEN
  IMP_RES_TAC evaluate_code_invariant THEN
  ASM_REWRITE_TAC[] THEN RFS[locals_strong_rel_def];;

let PCINLAUX_IPC_IF_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  QPAT_X_ASSUM "crep_evaluate _ = _" MP_TAC THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  DISCH_TAC THEN GVS_ASM(all_case_eqs()) THEN
  IMP_RES_TAC eval_code_inl THEN
  REWRITE_TAC[inline_prog_def] THEN SIMP[] THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  FIRST_X_ASSUM(QSPECL_THEN ["inl_fs"; "s1"; "inl_bag"] MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];;

let PCINLAUX_IPC_IH_AT_TARGET : tactic = fun (asl,w as g) ->
  let is_ev t = is_comb t &&
    (try fst(dest_const(rator t)) = "crep_evaluate" with Failure _ -> false) in
  let ev = find_term is_ev w in
  let tgt = snd(dest_pair(rand ev)) in
  (FIRST_X_ASSUM(fun ih -> MP_TAC(ISPECL
     [`inl_fs:(mlstring,num list # (A)crep_prog)fmap`; tgt;
      `inl_bag:(mlstring,num list # (A)crep_prog)fmap`] ih)) THEN
   ASM_REWRITE_TAC[inline_prog_def]) g;;

let PCINLAUX_IPC_WHILE_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  QPAT_X_ASSUM "crep_evaluate _ = _" MP_TAC THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  DISCH_TAC THEN REWRITE_TAC[inline_prog_def] THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  SUBGOAL_THEN `crep_state_clock (s1:(A,FFI)crep_state) = crep_state_clock (s:(A,FFI)crep_state)`
    ASSUME_TAC THENL [ASM_MESON_TAC[state_rel_code_def]; ALL_TAC] THEN
  QCASES_ON "crep_eval s e" THEN FS[] THEN
  IMP_RES_TAC eval_code_inl THEN ASM_REWRITE_TAC[] THEN
  QCASES_ON "a" THEN FS[] THEN
  ASM_CASES_TAC `a' = word 0:A word` THENL [GVS[] THEN NO_TAC; ALL_TAC] THEN
  RFS[] THEN
  ASM_CASES_TAC `crep_state_clock (s:(A,FFI)crep_state) = 0` THENL
   [GVS[] THEN FS[state_rel_code_def; code_inl_rel_def; crep_empty_locals_def] THEN NO_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?res1 s2. crep_evaluate (c,crep_dec_clock s) = (res1,s2:(A,FFI)crep_state)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  RFS[] THEN
  SUBGOAL_THEN `~(res1 = SOME (crep_Error:(A)crep_result))` ASSUME_TAC THENL
   [DISCH_TAC THEN GVS[] THEN NO_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(QSPECL_THEN ["inl_fs"; "crep_dec_clock s1"; "inl_bag"] MP_TAC) THEN
  FS[crep_dec_clock_def; state_rel_code_def; locals_strong_rel_def; code_inl_rel_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  QPAT_ASSUM "crep_evaluate (c,_) = _" (ASSUME_TAC o MATCH_MP evaluate_code_invariant) THEN
  RULE_ASSUM_TAC(SIMP_RULE[crep_dec_clock_def]) THEN
  EVERY_CASE_TAC THEN GVS[] THEN TRY PCINLAUX_IPC_IH_AT_TARGET;;

(* the temporaries of inline_prog are distinct and above the maxima *)

let PCINLAUX_GENLIST_SUC_FRESH = prove
 (`!k n. ALL_DISTINCT (list_of_seq (\x. SUC x + k) n) /\
         LENGTH (list_of_seq (\x. SUC x + k) n) = n /\
         (!x. MEM x (list_of_seq (\x. SUC x + k) n) ==> k < x)`,
  REWRITE_TAC[ALL_DISTINCT_GENLIST; LENGTH_GENLIST] THEN
  MESON_TAC[mem_genlist_add_suc_val; SUC_INJ; EQ_ADD_RCANCEL]);;

let PCINLAUX_TMP_VARS_FRESH = prove
 (`!(l1:num list) l2 n.
     ALL_DISTINCT (list_of_seq (\x. SUC x + MAX (MAX_LIST l1) (MAX_LIST l2)) n) /\
     LENGTH (list_of_seq (\x. SUC x + MAX (MAX_LIST l1) (MAX_LIST l2)) n) = n /\
     (!x. MEM x (list_of_seq (\x. SUC x + MAX (MAX_LIST l1) (MAX_LIST l2)) n)
          ==> ~MEM x l1 /\ ~MEM x l2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PCINLAUX_GENLIST_SUC_FRESH] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`MAX (MAX_LIST (l1:num list)) (MAX_LIST l2)`; `n:num`] PCINLAUX_GENLIST_SUC_FRESH) THEN
  DISCH_THEN(MP_TAC o SPEC `x:num` o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  IMP_RES_TAC MAX_LIST_PROPERTY THEN ASM_ARITH_TAC);;

let PCINLAUX_IPC_CALL_PRE : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihc") (LABEL_TAC "ihh")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  QPAT_X_ASSUM "crep_evaluate _ = _" MP_TAC THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  QCASES_ON "OPT_MMAP (crep_eval s) argexps" THEN SIMP[] THEN
  RENAME1 "OPT_MMAP (crep_eval s) argexps = SOME args" THEN
  QCASES_ON "crep_lookup_code (crep_state_code s) fname args (LENGTH args)" THEN SIMP[] THEN
  RENAME1 "crep_lookup_code (crep_state_code s) fname args (LENGTH args) = SOME pn" THEN
  NAMED_CASES_ON "pn" ["prog newlocals"] THEN SIMP[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `crep_state_clock (s1:(A,FFI)crep_state) = crep_state_clock (s:(A,FFI)crep_state) /\
                crep_state_locals s1 = crep_state_locals s`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[state_rel_code_def; locals_strong_rel_def]; ALL_TAC] THEN
  IMP_RES_TAC opt_mmap_eval_code_inl THEN
  QPAT_X_ASSUM "crep_lookup_code _ _ _ _ = _" (fun th ->
    ASSUME_TAC th THEN MP_TAC(REWRITE_RULE[crep_lookup_code_def] th)) THEN
  QCASES_ON "FLOOKUP (crep_state_code s) fname" THEN SIMP[] THEN
  RENAME1 "FLOOKUP (crep_state_code s) fname = SOME nsp" THEN
  NAMED_CASES_ON "nsp" ["ns body"] THEN SIMP[] THEN STRIP_TAC THEN
  QPAT_X_ASSUM "body = prog" SUBST_ALL_TAC THEN
  QPAT_X_ASSUM "FEMPTY |++ ZIP ns args = newlocals" (SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[inline_prog_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV);;

let PCINLAUX_IPC_TAIL_NOINL_TAC : tactic =
  QPAT_ASSUM "code_inl_rel inl_fs s s1" (MP_TAC o SPECL [`fname:mlstring`; `ns:num list`; `prog:(A)crep_prog`] o REWRITE_RULE[code_inl_rel_def]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `bag:(mlstring,num list # (A)crep_prog)fmap` STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN ASM_REWRITE_TAC[crep_lookup_code_def] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  QPAT_X_ASSUM "(if _ then _ else _) = _" MP_TAC THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `crep_state_clock (s:(A,FFI)crep_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN SIMP[] THEN
  FS[state_rel_code_def; code_inl_rel_def; crep_empty_locals_def];
    SUBGOAL_THEN `?res st. crep_evaluate (prog,crep_state_locals_fupd (K (FEMPTY |++ ZIP ns args))
                   (crep_dec_clock (s:(A,FFI)crep_state))) = (res,st)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(res = SOME (crep_Error:(A)crep_result))` ASSUME_TAC THENL
   [DISCH_TAC THEN RFS[] THEN NO_TAC; ALL_TAC] THEN
  REMOVE_THEN "ihc" (MP_TAC o SPECL [`args:((A)word_lab)list`; `prog:(A)crep_prog`;
                                     `FEMPTY |++ ZIP (ns:num list) (args:((A)word_lab)list)`]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((A)crep_result)option`; `st:(A,FFI)crep_state`;
     `inl_fs:(mlstring,num list # (A)crep_prog)fmap`;
     `crep_state_locals_fupd (K (FEMPTY |++ ZIP (ns:num list) args)) (crep_dec_clock (s1:(A,FFI)crep_state))`;
     `bag:(mlstring,num list # (A)crep_prog)fmap`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FS[state_rel_code_def; locals_strong_rel_def; code_inl_rel_def; crep_dec_clock_def];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `st1:(A,FFI)crep_state` STRIP_ASSUME_TAC) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
    EVERY_CASE_TAC THEN GVS[] THEN
    FS[state_rel_code_def; code_inl_rel_def; crep_empty_locals_def; locals_strong_rel_def]];;
let PCINLAUX_IPC_TAIL_INL_TAC : tactic =
  RENAME1 "FLOOKUP inl_bag fname = SOME ap" THEN NAMED_CASES_ON "ap" ["args_vname cb"] THEN
  CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FLOOKUP (crep_state_code (s:(A,FFI)crep_state)) fname = SOME (args_vname,cb)`
    MP_TAC THENL
   [MATCH_MP_TAC FLOOKUP_SUBMAP THEN EXISTS_TAC `inl_fs:(mlstring,num list # (A)crep_prog)fmap` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FLOOKUP_SUBMAP THEN
    EXISTS_TAC `inl_bag:(mlstring,num list # (A)crep_prog)fmap` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `ns:num list = args_vname` || concl th = `prog:(A)crep_prog = cb`))) THEN
  SUBGOAL_THEN `?ic et. unreach_elim (inline_prog ((inl_bag:(mlstring,num list # (A)crep_prog)fmap) \\ fname) prog) = (ic,et:(early_exit)option)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[inline_tail_def] THEN ONCE_REWRITE_TAC[crep_evaluate_def] THEN
  GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [crep_evaluate_def] THEN
  QPAT_X_ASSUM "(if _ then _ else _) = _" MP_TAC THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `crep_state_clock (s:(A,FFI)crep_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN SIMP[] THEN
    FS[state_rel_code_def; code_inl_rel_def; crep_empty_locals_def] THEN NO_TAC;
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `?res st. crep_evaluate (prog,crep_state_locals_fupd
                   (K (FEMPTY |++ ZIP (ns:num list) args)) (crep_dec_clock (s:(A,FFI)crep_state))) =
                   (res,st)` STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(res = SOME (crep_Error:(A)crep_result))` ASSUME_TAC THENL
   [DISCH_TAC THEN RFS[] THEN NO_TAC; ALL_TAC] THEN
  REMOVE_THEN "ihc" (MP_TAC o SPECL [`args:((A)word_lab)list`; `prog:(A)crep_prog`;
                                     `FEMPTY |++ ZIP (ns:num list) (args:((A)word_lab)list)`]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((A)crep_result)option`; `st:(A,FFI)crep_state`;
     `inl_fs:(mlstring,num list # (A)crep_prog)fmap`;
     `crep_state_locals_fupd (K (FEMPTY |++ ZIP (ns:num list) args))
        (crep_dec_clock (s1:(A,FFI)crep_state))`;
     `(inl_bag:(mlstring,num list # (A)crep_prog)fmap) \\ fname`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FS[state_rel_code_def; locals_strong_rel_def; code_inl_rel_def; crep_dec_clock_def] THEN
    ASM_MESON_TAC[SUBMAP_DOMSUB; SUBMAP_TRANS];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `st1:(A,FFI)crep_state` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`inline_prog ((inl_bag:(mlstring,num list # (A)crep_prog)fmap) \\ fname) prog`;
                 `crep_state_locals_fupd (K (FEMPTY |++ ZIP (ns:num list) args))
                    (crep_dec_clock (s1:(A,FFI)crep_state))`;
                 `res:((A)crep_result)option`; `st1:(A,FFI)crep_state`;
                 `ic:(A)crep_prog`; `et:(early_exit)option`] unreach_elim_correct) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_GOALSUB_ABBREV_TAC "arg_load tmp _ _ _" THEN
  SUBGOAL_THEN `?r1 t'. crep_evaluate (arg_load tmp argexps ns ic,crep_dec_clock s1) =
                        (r1,t':(A,FFI)crep_state)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`crep_dec_clock (s1:(A,FFI)crep_state)`; `argexps:((A)crep_exp)list`;
                 `args:((A)word_lab)list`; `ns:num list`; `FEMPTY:(num,(A)word_lab)fmap`;
                 `ic:(A)crep_prog`; `res:((A)crep_result)option`; `st1:(A,FFI)crep_state`;
                 `tmp:num list`; `r1:((A)crep_result)option`; `t':(A,FFI)crep_state`]
                general_simulate_arg_load_strong_all_drule) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM arg_load_def] THEN
    ASM_REWRITE_TAC[opt_mmap_eval_dec_clock_eq; SUBMAP_FEMPTY; FDOM_FEMPTY; NOT_IN_EMPTY] THEN
    QPAT_X_ASSUM "list_of_seq _ _ = tmp" (SUBST_ALL_TAC o SYM) THEN
    MP_TAC(ISPECL [`FLAT (MAP var_cexp (argexps:((A)crep_exp)list))`; `ns:num list`;
                   `LENGTH (args:((A)word_lab)list)`] PCINLAUX_TMP_VARS_FRESH) THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  QPAT_ASSUM "crep_evaluate (prog,_) = _" (ASSUME_TAC o MATCH_MP evaluate_code_invariant) THEN
  QPAT_ASSUM "crep_evaluate (inline_prog _ _,_) = _"
    (ASSUME_TAC o MATCH_MP evaluate_code_invariant) THEN
  RULE_ASSUM_TAC(SIMP_RULE[crep_dec_clock_def]) THEN
  QPAT_X_ASSUM "r1 = res" SUBST_ALL_TAC THEN
  EVERY_CASE_TAC THEN GVS[] THEN
  FS[state_rel_code_def; code_inl_rel_def; crep_empty_locals_def; crep_inlineProof_state_rel_def];;



(* a pair case whose arms do not use the components *)

let PCINLAUX_IPC_HDL_FINISH : tactic =
  TRY(QPAT_ASSUM "crep_evaluate (prog,_) = _" (ASSUME_TAC o MATCH_MP evaluate_code_invariant)) THEN
  RULE_ASSUM_TAC(SIMP_RULE[crep_dec_clock_def]) THEN
  PCINLAUX_IPC_IH_AT_TARGET THEN FS[];;

let PCINLAUX_IPC_HDL_TAC : tactic =
  NAMED_CASES_ON "wh" ["w hdl"] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  QCASES_ON "FLOOKUP inl_bag fname" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[BASICAUX_pair_CASE_K] THEN PCINLAUX_IPC_TAIL_NOINL_TAC THEN
  TRY PCINLAUX_IPC_HDL_FINISH;;

(* the target of a non-tail inlined call: the transformed callee tcp runs in s1 with the
   temporaries tr and the arguments declared; an exceptional result is the result of the
   whole program *)

let PCINLAUX_NONTAIL_EXC = prove
 (`!(s1:(A,FFI)crep_state) argexps args ns tv tr (rts:num list) tcp rc sc.
     OPT_MMAP (crep_eval s1) argexps = SOME args /\ LENGTH ns = LENGTH args /\
     ALL_DISTINCT ns /\ ALL_DISTINCT tv /\ LENGTH tv = LENGTH ns /\
     (!x. MEM x tv ==> ~MEM x ns) /\ (!x. MEM x tv ==> ~MEM x (FLAT (MAP var_cexp argexps))) /\
     ALL_DISTINCT tr /\
     (!x. MEM x tr ==> ~MEM x ns) /\ (!x. MEM x tr ==> ~MEM x tv) /\
     (!x. MEM x tr ==> ~MEM x (FLAT (MAP var_cexp argexps))) /\
     crep_evaluate (tcp,crep_state_locals_fupd
        (K ((FEMPTY |++ ZIP tr (REPLICATE (LENGTH tr) (Word (word 0)))) |++ ZIP ns args)) s1) =
     (rc,sc) /\
     ~(rc = NONE) /\ ~(rc = SOME crep_Error)
     ==> ?tT. crep_evaluate (inline_nontail tcp rts tr tv argexps ns,s1) = (rc,tT) /\
              crep_inlineProof_state_rel sc tT`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inline_nontail_def] THEN
  ABBREV_TAC `zs = REPLICATE (LENGTH (tr:num list)) (Word (word 0):(A)word_lab)` THEN
  ABBREV_TAC `WB = crep_Seq (arg_load tv argexps ns tcp)
                     (crep_nested_seq (MAP2 crep_Assign rts (MAP crep_Var tr))):(A)crep_prog` THEN
  SUBGOAL_THEN `?rW sW. crep_evaluate (WB,crep_state_locals_fupd
                   (K (crep_state_locals s1 |++ ZIP tr zs)) (s1:(A,FFI)crep_state)) = (rW,sW)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `?r1 t1. crep_evaluate (nested_decs tr (REPLICATE (LENGTH tr) (crep_Const (word 0)))
                   WB,s1) = (r1,t1:(A,FFI)crep_state)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`WB:(A)crep_prog`; `s1:(A,FFI)crep_state`; `rW:((A)crep_result)option`;
                 `sW:(A,FFI)crep_state`; `tr:num list`;
                 `REPLICATE (LENGTH (tr:num list)) (crep_Const (word 0):(A)crep_exp)`;
                 `zs:((A)word_lab)list`; `r1:((A)crep_result)option`; `t1:(A,FFI)crep_state`]
                evaluate_nested_decs_locals_nested_res_var_drule) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "zs" THEN
    ASM_REWRITE_TAC[crep_inlineProof_evaluate_replicate_const; LENGTH_REPLICATE] THEN
    REWRITE_TAC[MEM_REPLICATE] THEN REPEAT STRIP_TAC THEN GVS[var_cexp_def];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?rA sA. crep_evaluate (arg_load tv argexps ns tcp,crep_state_locals_fupd
                   (K (crep_state_locals s1 |++ ZIP tr zs)) (s1:(A,FFI)crep_state)) = (rA,sA)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`crep_state_locals_fupd (K (crep_state_locals s1 |++ ZIP tr zs))
                    (s1:(A,FFI)crep_state)`;
                 `argexps:((A)crep_exp)list`; `args:((A)word_lab)list`; `ns:num list`;
                 `FEMPTY |++ ZIP (tr:num list) (zs:((A)word_lab)list)`; `tcp:(A)crep_prog`;
                 `rc:((A)crep_result)option`; `sc:(A,FFI)crep_state`; `tv:num list`;
                 `rA:((A)crep_result)option`; `sA:(A,FFI)crep_state`]
                general_simulate_arg_load_strong_all_drule) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM arg_load_def] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `LENGTH (tr:num list) = LENGTH (zs:((A)word_lab)list)` ASSUME_TAC THENL
     [EXPAND_TAC "zs" THEN REWRITE_TAC[LENGTH_REPLICATE]; ALL_TAC] THEN
    ASM_SIMP_TAC[opt_mmap_update_list_locals_not_vars_eval_eq'] THEN
    SIMP[RECORD_SELFID_ss] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SUBMAP_IMP_FUPDATE_LIST_SUBMAP; SUBMAP_FEMPTY] THEN
    ASM_REWRITE_TAC[FDOM_FUPDATE_LIST; FDOM_FEMPTY; UNION_EMPTY; IN_SET_OF_LIST] THEN
    ASM_SIMP_TAC[MAP_ZIP] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  QPAT_X_ASSUM "crep_evaluate (WB,_) = _" MP_TAC THEN EXPAND_TAC "WB" THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  EXISTS_TAC `t1:(A,FFI)crep_state` THEN GVS[] THEN FS[crep_inlineProof_state_rel_def]);;

(* the same program when the transformed callee returns normally with the return
   values in the temporaries tr: the values end up in rts *)

let PCINLAUX_NONTAIL_RET = prove
 (`!(s1:(A,FFI)crep_state) argexps args ns tv tr (rts:num list) tcp sc retvs z.
     OPT_MMAP (crep_eval s1) argexps = SOME args /\ LENGTH ns = LENGTH args /\
     ALL_DISTINCT ns /\ ALL_DISTINCT tv /\ LENGTH tv = LENGTH ns /\
     (!x. MEM x tv ==> ~MEM x ns) /\ (!x. MEM x tv ==> ~MEM x (FLAT (MAP var_cexp argexps))) /\
     ALL_DISTINCT tr /\
     (!x. MEM x tr ==> ~MEM x ns) /\ (!x. MEM x tr ==> ~MEM x tv) /\
     (!x. MEM x tr ==> ~MEM x (FLAT (MAP var_cexp argexps))) /\
     crep_evaluate (tcp,crep_state_locals_fupd
        (K ((FEMPTY |++ ZIP tr (REPLICATE (LENGTH tr) (Word (word 0)))) |++ ZIP ns args)) s1) =
     (NONE,sc) /\
     (!x. MEM x tr ==> ~MEM x rts) /\ ALL_DISTINCT rts /\
     OPT_MMAP (FLOOKUP (crep_state_locals s1)) rts = SOME z /\ LENGTH retvs = LENGTH rts /\
     OPT_MMAP (FLOOKUP (crep_state_locals sc)) tr = SOME retvs
     ==> ?tT. crep_evaluate (inline_nontail tcp rts tr tv argexps ns,s1) = (NONE,tT) /\
              crep_inlineProof_state_rel sc tT /\
              crep_state_locals tT = crep_state_locals s1 |++ ZIP rts retvs`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inline_nontail_def] THEN
  ABBREV_TAC `zs = REPLICATE (LENGTH (tr:num list)) (Word (word 0):(A)word_lab)` THEN
  ABBREV_TAC `WB = crep_Seq (arg_load tv argexps ns tcp)
                     (crep_nested_seq (MAP2 crep_Assign rts (MAP crep_Var tr))):(A)crep_prog` THEN
  SUBGOAL_THEN `?rW sW. crep_evaluate (WB,crep_state_locals_fupd
                   (K (crep_state_locals s1 |++ ZIP tr zs)) (s1:(A,FFI)crep_state)) = (rW,sW)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `?r1 t1. crep_evaluate (nested_decs tr (REPLICATE (LENGTH tr) (crep_Const (word 0)))
                   WB,s1) = (r1,t1:(A,FFI)crep_state)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`WB:(A)crep_prog`; `s1:(A,FFI)crep_state`; `rW:((A)crep_result)option`;
                 `sW:(A,FFI)crep_state`; `tr:num list`;
                 `REPLICATE (LENGTH (tr:num list)) (crep_Const (word 0):(A)crep_exp)`;
                 `zs:((A)word_lab)list`; `r1:((A)crep_result)option`; `t1:(A,FFI)crep_state`]
                evaluate_nested_decs_locals_nested_res_var_drule) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "zs" THEN
    ASM_REWRITE_TAC[crep_inlineProof_evaluate_replicate_const; LENGTH_REPLICATE] THEN
    REWRITE_TAC[MEM_REPLICATE] THEN REPEAT STRIP_TAC THEN GVS[var_cexp_def];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?rA sA. crep_evaluate (arg_load tv argexps ns tcp,crep_state_locals_fupd
                   (K (crep_state_locals s1 |++ ZIP tr zs)) (s1:(A,FFI)crep_state)) = (rA,sA)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`crep_state_locals_fupd (K (crep_state_locals s1 |++ ZIP tr zs))
                    (s1:(A,FFI)crep_state)`;
                 `argexps:((A)crep_exp)list`; `args:((A)word_lab)list`; `ns:num list`;
                 `FEMPTY |++ ZIP (tr:num list) (zs:((A)word_lab)list)`; `tcp:(A)crep_prog`;
                 `NONE:((A)crep_result)option`; `sc:(A,FFI)crep_state`; `tv:num list`;
                 `rA:((A)crep_result)option`; `sA:(A,FFI)crep_state`]
                general_simulate_arg_load_strong_all_drule) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM arg_load_def] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `LENGTH (tr:num list) = LENGTH (zs:((A)word_lab)list)` ASSUME_TAC THENL
     [EXPAND_TAC "zs" THEN REWRITE_TAC[LENGTH_REPLICATE]; ALL_TAC] THEN
    ASM_SIMP_TAC[opt_mmap_update_list_locals_not_vars_eval_eq'] THEN
    SIMP[RECORD_SELFID_ss] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SUBMAP_IMP_FUPDATE_LIST_SUBMAP; SUBMAP_FEMPTY] THEN
    ASM_REWRITE_TAC[FDOM_FUPDATE_LIST; FDOM_FEMPTY; UNION_EMPTY; IN_SET_OF_LIST] THEN
    ASM_SIMP_TAC[MAP_ZIP] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN
  QPAT_ASSUM "REPLICATE _ _ = zs" (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[SYM th])) THEN
  SUBGOAL_THEN `OPT_MMAP (FLOOKUP (crep_state_locals (sA:(A,FFI)crep_state))) tr =
                SOME (retvs:((A)word_lab)list)` ASSUME_TAC THENL
   [MATCH_MP_TAC FOLDL_res_var_ZIP_lookup THEN
    MAP_EVERY EXISTS_TAC [`crep_state_locals (sc:(A,FFI)crep_state)`; `ns:num list`;
       `crep_state_locals (s1:(A,FFI)crep_state) |++
        ZIP tr (REPLICATE (LENGTH (tr:num list)) (Word (word 0):(A)word_lab))`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `OPT_MMAP (FLOOKUP (crep_state_locals (sA:(A,FFI)crep_state))) rts =
                SOME (z:((A)word_lab)list)` ASSUME_TAC THENL
   [MATCH_MP_TAC (INST_TYPE [`:(A)word_lab`,`:W`] FDIFF_fupdate_list_empty_flookup) THEN
    MAP_EVERY EXISTS_TAC [`crep_state_locals (s1:(A,FFI)crep_state)`; `tr:num list`;
       `Word (word 0):(A)word_lab`; `Word (word 0):(A)word_lab`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  QPAT_ASSUM "!x. MEM x tr ==> ~MEM x rts"
    (fun th -> ASSUME_TAC (MESON[th] `!x:num. MEM x rts ==> ~MEM x tr`)) THEN
  SUBGOAL_THEN `?rB sB. crep_evaluate (crep_nested_seq (MAP2 crep_Assign rts (MAP crep_Var tr)),
                   sA:(A,FFI)crep_state) = (rB,sB)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`rts:num list`; `sA:(A,FFI)crep_state`; `MAP crep_Var tr:((A)crep_exp)list`;
                 `retvs:((A)word_lab)list`; `z:((A)word_lab)list`; `rB:((A)crep_result)option`;
                 `sB:(A,FFI)crep_state`] evaluate_nested_seq_assign_drule) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM lookup_locals_eq_map_vars; map_var_cexp_eq_var] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  QPAT_X_ASSUM "crep_evaluate (WB,_) = _" MP_TAC THEN EXPAND_TAC "WB" THEN
  ONCE_REWRITE_TAC[crep_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(rW:((A)crep_result)option) = rB /\ (sW:(A,FFI)crep_state) = sB`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [QPAT_X_ASSUM "crep_evaluate (crep_nested_seq _,sA) = rW,sW" MP_TAC THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FS[crep_inlineProof_state_rel_def]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[EQ_FDOM_SUBMAP] THEN CONJ_TAC THENL
   [MATCH_MP_TAC submap_finish_flookup THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    QPAT_ASSUM "!x. ~MEM x rts ==> _" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~MEM (x:num) rts`)]) THEN
    MATCH_MP_TAC (INST_TYPE [`:(A)word_lab`,`:W`] FDIFF_fupdate_list_empty_flookup_var) THEN
    MAP_EVERY EXISTS_TAC [`crep_state_locals (s1:(A,FFI)crep_state)`; `tr:num list`;
       `Word (word 0):(A)word_lab`; `Word (word 0):(A)word_lab`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  QPAT_X_ASSUM "crep_state_locals t1 = _" (SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`rts:num list`; `crep_state_locals (s1:(A,FFI)crep_state)`; `z:((A)word_lab)list`;
                 `retvs:((A)word_lab)list`] opt_mmap_flookup_some_then_same_fdom) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC evaluate_locals_same_fdom' THEN
  MAP_EVERY EXISTS_TAC [`nested_decs tr (REPLICATE (LENGTH tr) (crep_Const (word 0))) WB:(A)crep_prog`;
                        `NONE:((A)crep_result)option`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* the return temporaries of inline_prog lie above the return variables, the variables of
   the callee and the argument temporaries (and, with arguments, above their sources) *)

let PCINLAUX_TEMP_RETS_FRESH = prove
 (`!(rts:num list) (ic:(A)crep_prog) l1 l2 n x.
     MEM x (list_of_seq (\x. SUC x + MAX_LIST [MAX_LIST rts; vmax_prog ic;
              MAX_LIST (list_of_seq (\x. SUC x + MAX (MAX_LIST l1) (MAX_LIST l2)) n)])
            (LENGTH rts))
     ==> ~MEM x rts /\ ~MEM x (var_prog ic) /\
         ~MEM x (list_of_seq (\x. SUC x + MAX (MAX_LIST l1) (MAX_LIST l2)) n) /\
         (~(n = 0) ==> ~MEM x l1 /\ ~MEM x l2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `MAX_LIST [MAX_LIST rts; vmax_prog (ic:(A)crep_prog);
                  MAX_LIST (list_of_seq (\x. SUC x + MAX (MAX_LIST l1) (MAX_LIST l2)) n)] < x`
    MP_TAC THENL
   [MP_TAC(SPECL [`MAX_LIST [MAX_LIST rts; vmax_prog (ic:(A)crep_prog);
                    MAX_LIST (list_of_seq (\x. SUC x + MAX (MAX_LIST l1) (MAX_LIST l2)) n)]`;
                  `LENGTH (rts:num list)`] PCINLAUX_GENLIST_SUC_FRESH) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MAX_LIST; vmax_prog_def] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN IMP_RES_TAC MAX_LIST_PROPERTY THEN ASM_ARITH_TAC;
    DISCH_TAC THEN IMP_RES_TAC MAX_LIST_PROPERTY THEN ASM_ARITH_TAC;
    DISCH_TAC THEN IMP_RES_TAC MAX_LIST_PROPERTY THEN ASM_ARITH_TAC;
    DISCH_TAC THEN
    MP_TAC(INST [`MAX (MAX_LIST (l1:num list)) (MAX_LIST l2)`,`k:num`]
                max_list_genlist_add_suc_val) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THEN DISCH_TAC THEN
    IMP_RES_TAC MAX_LIST_PROPERTY THEN ASM_ARITH_TAC]);;

(* the temporaries of an inlined non-tail call: argument copies tv and return copies tr *)

let PCINLAUX_NONTAIL_FRESH = prove
 (`!(s1:(A,FFI)crep_state) argexps args (ns:num list) (rts:num list) (ic:(A)crep_prog) tv tr.
     OPT_MMAP (crep_eval s1) argexps = SOME args /\ LENGTH ns = LENGTH args /\
     tv = list_of_seq (\x. SUC x + MAX (MAX_LIST (FLAT (MAP var_cexp argexps))) (MAX_LIST ns))
            (LENGTH args) /\
     tr = list_of_seq (\x. SUC x + MAX_LIST [MAX_LIST rts; vmax_prog ic; MAX_LIST tv])
            (LENGTH rts)
     ==> ALL_DISTINCT tv /\ LENGTH tv = LENGTH ns /\
         (!x. MEM x tv ==> ~MEM x ns) /\
         (!x. MEM x tv ==> ~MEM x (FLAT (MAP var_cexp argexps))) /\
         ALL_DISTINCT tr /\ LENGTH tr = LENGTH rts /\
         (!x. MEM x tr ==> ~MEM x ns) /\ (!x. MEM x tr ==> ~MEM x tv) /\
         (!x. MEM x tr ==> ~MEM x (FLAT (MAP var_cexp argexps))) /\
         (!x. MEM x tr ==> ~MEM x rts) /\ (!x. MEM x tr ==> ~MEM x (var_prog ic))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`FLAT (MAP var_cexp (argexps:((A)crep_exp)list))`; `ns:num list`;
                 `LENGTH (args:((A)word_lab)list)`] PCINLAUX_TMP_VARS_FRESH) THEN
  MP_TAC(ISPECL [`MAX_LIST [MAX_LIST (rts:num list); vmax_prog (ic:(A)crep_prog);
                            MAX_LIST (tv:num list)]`;
                 `LENGTH (rts:num list)`] PCINLAUX_GENLIST_SUC_FRESH) THEN
  MP_TAC(ISPECL [`rts:num list`; `ic:(A)crep_prog`;
                 `FLAT (MAP var_cexp (argexps:((A)crep_exp)list))`; `ns:num list`;
                 `LENGTH (args:((A)word_lab)list)`] PCINLAUX_TEMP_RETS_FRESH) THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    let l = lhs(concl th) in l = `tr:num list` || l = `tv:num list`))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `LENGTH (args:((A)word_lab)list) = 0` THENL
   [SUBGOAL_THEN `ns:num list = [] /\ argexps:((A)crep_exp)list = []` STRIP_ASSUME_TAC THENL
     [IMP_RES_TAC opt_mmap_length_eq THEN ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[MEM; MAP; FLAT] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* the locals of the inlined callee: the arguments over the zeroed return copies *)

let PCINLAUX_NONTAIL_LOC = prove
 (`!(tr:num list) (ns:num list) (args:((A)word_lab)list).
     LENGTH ns = LENGTH args /\ ALL_DISTINCT tr /\ (!x. MEM x tr ==> ~MEM x ns)
     ==> (FEMPTY |++ ZIP ns args) SUBMAP
         ((FEMPTY |++ ZIP tr (REPLICATE (LENGTH tr) (Word (word 0)))) |++ ZIP ns args) /\
         OPT_MMAP (FLOOKUP ((FEMPTY |++ ZIP tr (REPLICATE (LENGTH tr) (Word (word 0)))) |++
                            ZIP ns args)) tr =
         SOME (REPLICATE (LENGTH tr) (Word (word 0)))`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SUBMAP_IMP_FUPDATE_LIST_SUBMAP THEN ASM_REWRITE_TAC[SUBMAP_FEMPTY];
    ALL_TAC] THEN
  W(fun (_,w) -> MP_TAC(PART_MATCH (lhs o rand) opt_mmap_disj_zip_flookup (lhs w))) THEN
  ASM_REWRITE_TAC[distinct_lists_def; GSYM ALL_MEM] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC opt_mmap_some_eq_zip_flookup THEN ASM_REWRITE_TAC[LENGTH_REPLICATE]);;

let PCINLAUX_STATE_REL_TRANS = prove
 (`!(a:(A,FFI)crep_state) b c.
     crep_inlineProof_state_rel a b /\ crep_inlineProof_state_rel b c
     ==> crep_inlineProof_state_rel a c`,
  REWRITE_TAC[crep_inlineProof_state_rel_def] THEN MESON_TAC[]);;

(* the two kinds of exit of the inlined callee in PCINLAUX_NONTAIL_SIM *)

let PCINLAUX_NT_EXC_FIN : tactic =
  DISCH_THEN SUBST_ALL_TAC THEN REMOVE_THEN "exc" MP_TAC THEN SIMP[] THEN MESON_TAC[];;

let PCINLAUX_NT_RET_FIN : tactic =
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `retvs:((A)word_lab)list` o check (fun th ->
    is_forall(concl th) &&
    can (find_term ((=) `crepSem_Return:((A)word_lab)list->(A)crep_result`)) (concl th))) THEN
  REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `z:((A)word_lab)list` ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s1:(A,FFI)crep_state`; `argexps:((A)crep_exp)list`; `args:((A)word_lab)list`;
                 `ns:num list`; `tv:num list`; `tr:num list`; `rts:num list`; `tcp:(A)crep_prog`;
                 `s2:(A,FFI)crep_state`; `retvs:((A)word_lab)list`; `z:((A)word_lab)list`]
                PCINLAUX_NONTAIL_RET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tT:(A,FFI)crep_state` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`NONE:((A)crep_result)option`; `tT:(A,FFI)crep_state`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PCINLAUX_STATE_REL_TRANS];;

(* the inlined non-tail call when the inlined callee ic runs to an exit *)

let PCINLAUX_NONTAIL_SIM = prove
 (CASE_TERM `!(s1:(A,FFI)crep_state) argexps args ns (rts:num list) (ic:(A)crep_prog) et res st1
      tv tr tcp.
     OPT_MMAP (crep_eval s1) argexps = SOME args /\ LENGTH ns = LENGTH args /\ ALL_DISTINCT ns /\
     ALL_DISTINCT rts /\ ~(crep_state_clock s1 = 0) /\
     unreach_elim ic = (ic,et) /\
     crep_evaluate (ic,crep_state_locals_fupd (K (FEMPTY |++ ZIP ns args)) (crep_dec_clock s1)) =
       (res,st1) /\
     ~cont_res res /\
     (!retvs. res = SOME (crepSem_Return retvs)
              ==> LENGTH retvs = LENGTH rts /\
                  (?z. OPT_MMAP (FLOOKUP (crep_state_locals s1)) rts = SOME z)) /\
     tv = list_of_seq (\x. SUC x + MAX (MAX_LIST (FLAT (MAP var_cexp argexps))) (MAX_LIST ns))
            (LENGTH args) /\
     tr = list_of_seq (\x. SUC x + MAX_LIST [MAX_LIST rts; vmax_prog ic; MAX_LIST tv])
            (LENGTH rts) /\
     tcp = (if not_branch_ret ic then crep_Seq crep_Tick (transform_eoc tr ic)
            else crep_While (crep_Const (word 1)) (transform_branch 0 tr ic))
     ==> ?r1 tT. crep_evaluate (inline_nontail tcp rts tr tv argexps ns,s1) = (r1,tT) /\
                 crep_inlineProof_state_rel st1 tT /\
                 (match res with
                    SOME (crepSem_Return retvs) ->
                      r1 = NONE /\
                      crep_state_locals tT = crep_state_locals s1 |++ ZIP rts retvs
                  | _ -> r1 = res)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(fun th -> let c = concl th in
    if is_eq c && is_var(lhs c) && mem (fst(dest_var(lhs c))) ["tv";"tr";"tcp"]
    then SYM th else th) THEN
  MP_TAC(ISPECL [`s1:(A,FFI)crep_state`; `argexps:((A)crep_exp)list`; `args:((A)word_lab)list`;
                 `ns:num list`; `rts:num list`; `ic:(A)crep_prog`; `tv:num list`; `tr:num list`]
                PCINLAUX_NONTAIL_FRESH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  QPAT_X_ASSUM "LENGTH tr = LENGTH rts" (ASSUME_TAC o SYM) THEN
  MP_TAC(ISPECL [`tr:num list`; `ns:num list`; `args:((A)word_lab)list`] PCINLAUX_NONTAIL_LOC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `~(res = SOME (crep_Error:(A)crep_result))` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~cont_res (res:((A)crep_result)option)` THEN
    ASM_REWRITE_TAC[cont_res_def]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ic:(A)crep_prog`;
     `crep_state_locals_fupd (K (FEMPTY |++ ZIP (ns:num list) (args:((A)word_lab)list)))
        (crep_dec_clock (s1:(A,FFI)crep_state))`;
     `res:((A)crep_result)option`; `st1:(A,FFI)crep_state`;
     `crep_state_locals_fupd
        (K ((FEMPTY |++ ZIP (tr:num list) (REPLICATE (LENGTH tr) (Word (word 0):(A)word_lab))) |++
            ZIP (ns:num list) (args:((A)word_lab)list)))
        (crep_dec_clock (s1:(A,FFI)crep_state))`] evaluate_state_locals_rel_strong) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[crep_inlineProof_locals_rel_def; crep_inlineProof_state_rel_def] THEN
    SIMP[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(A,FFI)crep_state` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`ic:(A)crep_prog`; `s1:(A,FFI)crep_state`; `res:((A)crep_result)option`;
                 `t1:(A,FFI)crep_state`; `et:(early_exit)option`; `tr:num list`;
                 `(FEMPTY |++ ZIP (tr:num list) (REPLICATE (LENGTH tr) (Word (word 0):(A)word_lab))) |++
                  ZIP (ns:num list) (args:((A)word_lab)list)`] wrapped_transform_if) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:((A)crep_result)option` (X_CHOOSE_THEN `s2:(A,FFI)crep_state`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  QPAT_X_ASSUM "_ = tcp" (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `~(r1 = NONE) /\ ~(r1 = SOME (crep_Error:(A)crep_result))
                ==> ?tT. crep_evaluate (inline_nontail tcp rts tr tv argexps ns,s1) = (r1,tT) /\
                         crep_inlineProof_state_rel st1 (tT:(A,FFI)crep_state)` (LABEL_TAC "exc") THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`s1:(A,FFI)crep_state`; `argexps:((A)crep_exp)list`; `args:((A)word_lab)list`;
                   `ns:num list`; `tv:num list`; `tr:num list`; `rts:num list`; `tcp:(A)crep_prog`;
                   `r1:((A)crep_result)option`; `s2:(A,FFI)crep_state`] PCINLAUX_NONTAIL_EXC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `tT:(A,FFI)crep_state` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `tT:(A,FFI)crep_state` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[PCINLAUX_STATE_REL_TRANS];
    ALL_TAC] THEN
  NAMED_CASES_ON "res" ["";"a"] THEN TRY(FS[cont_res_def] THEN NO_TAC) THEN
  NAMED_CASES_ON "a" ["";"";"n";"n";"retvs";"eid";"f"] THEN TRY(FS[cont_res_def] THEN NO_TAC) THEN
  CASE_REWRITE_TAC[] THENL
   [PCINLAUX_NT_EXC_FIN; PCINLAUX_NT_RET_FIN; PCINLAUX_NT_EXC_FIN; PCINLAUX_NT_EXC_FIN]);;

(* the inlined non-tail call when the clock is out: the transformed callee times out *)

let PCINLAUX_NONTAIL_CLK0 = prove
 (`!(s1:(A,FFI)crep_state) argexps args ns (rts:num list) (ic:(A)crep_prog) tv tr tcp.
     OPT_MMAP (crep_eval s1) argexps = SOME args /\ LENGTH ns = LENGTH args /\ ALL_DISTINCT ns /\
     crep_state_clock s1 = 0 /\
     tv = list_of_seq (\x. SUC x + MAX (MAX_LIST (FLAT (MAP var_cexp argexps))) (MAX_LIST ns))
            (LENGTH args) /\
     tr = list_of_seq (\x. SUC x + MAX_LIST [MAX_LIST rts; vmax_prog ic; MAX_LIST tv])
            (LENGTH rts) /\
     tcp = (if not_branch_ret ic then crep_Seq crep_Tick (transform_eoc tr ic)
            else crep_While (crep_Const (word 1)) (transform_branch 0 tr ic))
     ==> ?tT. crep_evaluate (inline_nontail tcp rts tr tv argexps ns,s1) =
              (SOME crep_TimeOut,tT) /\
              crep_inlineProof_state_rel s1 tT`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(fun th -> let c = concl th in
    if is_eq c && is_var(lhs c) && mem (fst(dest_var(lhs c))) ["tv";"tr";"tcp"]
    then SYM th else th) THEN
  MP_TAC(ISPECL [`s1:(A,FFI)crep_state`; `argexps:((A)crep_exp)list`; `args:((A)word_lab)list`;
                 `ns:num list`; `rts:num list`; `ic:(A)crep_prog`; `tv:num list`; `tr:num list`]
                PCINLAUX_NONTAIL_FRESH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `?sc. crep_evaluate (tcp:(A)crep_prog,crep_state_locals_fupd
           (K ((FEMPTY |++ ZIP (tr:num list) (REPLICATE (LENGTH tr) (Word (word 0):(A)word_lab))) |++
               ZIP (ns:num list) (args:((A)word_lab)list))) (s1:(A,FFI)crep_state)) =
           (SOME crep_TimeOut,sc) /\
         crep_inlineProof_state_rel s1 (sc:(A,FFI)crep_state)`
   STRIP_ASSUME_TAC THENL
   [QPAT_X_ASSUM "_ = tcp" (SUBST1_TAC o SYM) THEN COND_CASES_TAC THEN
    ONCE_REWRITE_TAC[crep_evaluate_def] THENL
     [ONCE_REWRITE_TAC[crep_evaluate_def] THEN SIMP[crep_fix_clock_def] THEN
      ASM_REWRITE_TAC[] THEN SIMP[crep_inlineProof_state_rel_def; crep_empty_locals_def];
      REWRITE_TAC[crep_eval_def] THEN CASE_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[WORD_NE_10] THEN
      SIMP[crep_inlineProof_state_rel_def; crep_empty_locals_def]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s1:(A,FFI)crep_state`; `argexps:((A)crep_exp)list`; `args:((A)word_lab)list`;
                 `ns:num list`; `tv:num list`; `tr:num list`; `rts:num list`; `tcp:(A)crep_prog`;
                 `SOME (crep_TimeOut:(A)crep_result)`; `sc:(A,FFI)crep_state`] PCINLAUX_NONTAIL_EXC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMP[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tT:(A,FFI)crep_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `tT:(A,FFI)crep_state` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PCINLAUX_STATE_REL_TRANS]);;

(* the Nontail case of inline_prog_correct (an inlined call with return variables and no
   handler), after PCINLAUX_IPC_CALL_PRE and the case splits of the Call case *)

let PCINLAUX_NONTAIL_SIM' = prove
 (CASE_TERM `!(s1:(A,FFI)crep_state) ns args (ic:(A)crep_prog) res st1 argexps (rts:num list) et
      tv tr tcp.
     crep_evaluate (ic,crep_state_locals_fupd (K (FEMPTY |++ ZIP ns args)) (crep_dec_clock s1)) =
       (res,st1)
     ==> OPT_MMAP (crep_eval s1) argexps = SOME args /\ LENGTH ns = LENGTH args /\
         ALL_DISTINCT ns /\ ALL_DISTINCT rts /\ ~(crep_state_clock s1 = 0) /\
         unreach_elim ic = (ic,et) /\ ~cont_res res /\
         (!retvs. res = SOME (crepSem_Return retvs)
                  ==> LENGTH retvs = LENGTH rts /\
                      (?z. OPT_MMAP (FLOOKUP (crep_state_locals s1)) rts = SOME z)) /\
         tv = list_of_seq (\x. SUC x + MAX (MAX_LIST (FLAT (MAP var_cexp argexps))) (MAX_LIST ns))
                (LENGTH args) /\
         tr = list_of_seq (\x. SUC x + MAX_LIST [MAX_LIST rts; vmax_prog ic; MAX_LIST tv])
                (LENGTH rts) /\
         tcp = (if not_branch_ret ic then crep_Seq crep_Tick (transform_eoc tr ic)
                else crep_While (crep_Const (word 1)) (transform_branch 0 tr ic))
         ==> ?r1 tT. crep_evaluate (inline_nontail tcp rts tr tv argexps ns,s1) = (r1,tT) /\
                     crep_inlineProof_state_rel st1 tT /\
                     (match res with
                        SOME (crepSem_Return retvs) ->
                          r1 = NONE /\
                          crep_state_locals tT = crep_state_locals s1 |++ ZIP rts retvs
                      | _ -> r1 = res)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PCINLAUX_NONTAIL_SIM THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let PCINLAUX_CODE_INL_REL_TRANS = prove
 (`!inl_fs (s:(A,B)crep_state) (t:(A,C)crep_state) (t':(A,C)crep_state).
     code_inl_rel inl_fs s t /\ crep_state_code t = crep_state_code t'
     ==> code_inl_rel inl_fs s t'`,
  REWRITE_TAC[code_inl_rel_def] THEN REPEAT STRIP_TAC THEN
  QPAT_X_ASSUM "crep_state_code t = _" (fun th -> REWRITE_TAC[GSYM th]) THEN
  ASM_MESON_TAC[]);;

let PCINLAUX_IPC_NT_FIN : tactic =
  CASE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:((A)crep_result)option` (X_CHOOSE_THEN `tT:(A,FFI)crep_state`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `code_inl_rel inl_fs (st:(A,FFI)crep_state) (tT:(A,FFI)crep_state)` ASSUME_TAC THENL
   [MATCH_MP_TAC PCINLAUX_CODE_INL_REL_TRANS THEN EXISTS_TAC `st1:(A,FFI)crep_state` THEN
    ASM_REWRITE_TAC[] THEN FS[crep_inlineProof_state_rel_def];
    ALL_TAC] THEN
  EXISTS_TAC `tT:(A,FFI)crep_state` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FS[state_rel_code_def; code_inl_rel_def; crep_inlineProof_state_rel_def; crep_empty_locals_def;
     locals_strong_rel_def];;

let PCINLAUX_IPC_NT_APPLY : tactic =
  QPAT_ASSUM "crep_evaluate (ic,_) = _" (fun th ->
    MP_TAC(SPECL [`argexps:((A)crep_exp)list`; `rts:num list`; `et:(early_exit)option`;
                  `tv:num list`; `tr:num list`; `tcp:(A)crep_prog`]
           (MATCH_MP PCINLAUX_NONTAIL_SIM' th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[cont_res_def] THEN SIMP[]; PCINLAUX_IPC_NT_FIN];;

let PCINLAUX_IPC_NONTAIL_TAC : tactic =
  QPAT_X_ASSUM "(if _ then _ else _) = _" MP_TAC THEN
  ABBREV_TAC `tv = list_of_seq (\x. SUC x + MAX (MAX_LIST (FLAT (MAP var_cexp
                 (argexps:((A)crep_exp)list)))) (MAX_LIST (ns:num list)))
                 (LENGTH (args:((A)word_lab)list))` THEN
  ABBREV_TAC `tr = list_of_seq (\x. SUC x + MAX_LIST [MAX_LIST (rts:num list);
                 vmax_prog (ic:(A)crep_prog); MAX_LIST (tv:num list)]) (LENGTH rts)` THEN
  ABBREV_TAC `tcp = (if not_branch_ret (ic:(A)crep_prog)
                     then crep_Seq crep_Tick (transform_eoc (tr:num list) ic)
                     else crep_While (crep_Const (word 1)) (transform_branch 0 tr ic))` THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `crep_state_clock (s:(A,FFI)crep_state) = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    MP_TAC(ISPECL [`s1:(A,FFI)crep_state`; `argexps:((A)crep_exp)list`; `args:((A)word_lab)list`;
                   `ns:num list`; `rts:num list`; `ic:(A)crep_prog`; `tv:num list`; `tr:num list`;
                   `tcp:(A)crep_prog`] PCINLAUX_NONTAIL_CLK0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `tT:(A,FFI)crep_state` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `code_inl_rel inl_fs (s:(A,FFI)crep_state) (tT:(A,FFI)crep_state)` ASSUME_TAC THENL
     [MATCH_MP_TAC PCINLAUX_CODE_INL_REL_TRANS THEN EXISTS_TAC `s1:(A,FFI)crep_state` THEN
      ASM_REWRITE_TAC[] THEN FS[crep_inlineProof_state_rel_def];
      ALL_TAC] THEN
    EXISTS_TAC `tT:(A,FFI)crep_state` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    FS[state_rel_code_def; code_inl_rel_def; crep_inlineProof_state_rel_def;
       crep_empty_locals_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `?res st. crep_evaluate (prog,crep_state_locals_fupd
                   (K (FEMPTY |++ ZIP (ns:num list) args)) (crep_dec_clock (s:(A,FFI)crep_state))) =
                   (res,st)` STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(res = SOME (crep_Error:(A)crep_result))` ASSUME_TAC THENL
   [DISCH_TAC THEN RFS[] THEN NO_TAC; ALL_TAC] THEN
  REMOVE_THEN "ihc" (MP_TAC o SPECL [`args:((A)word_lab)list`; `prog:(A)crep_prog`;
                                     `FEMPTY |++ ZIP (ns:num list) (args:((A)word_lab)list)`]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`res:((A)crep_result)option`; `st:(A,FFI)crep_state`;
     `inl_fs:(mlstring,num list # (A)crep_prog)fmap`;
     `crep_state_locals_fupd (K (FEMPTY |++ ZIP (ns:num list) args))
        (crep_dec_clock (s1:(A,FFI)crep_state))`;
     `(inl_bag:(mlstring,num list # (A)crep_prog)fmap) \\ fname`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FS[state_rel_code_def; locals_strong_rel_def; code_inl_rel_def; crep_dec_clock_def] THEN
    ASM_MESON_TAC[SUBMAP_DOMSUB; SUBMAP_TRANS];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `st1:(A,FFI)crep_state` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`inline_prog ((inl_bag:(mlstring,num list # (A)crep_prog)fmap) \\ fname) prog`;
                 `crep_state_locals_fupd (K (FEMPTY |++ ZIP (ns:num list) args))
                    (crep_dec_clock (s1:(A,FFI)crep_state))`;
                 `res:((A)crep_result)option`; `st1:(A,FFI)crep_state`;
                 `ic:(A)crep_prog`; `et:(early_exit)option`] unreach_elim_correct) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP unreach_elim_converge o check (fun th ->
    can (term_match [] `unreach_elim (inline_prog b p) = (q:(A)crep_prog,e:(early_exit)option)`)
        (concl th))) THEN
  QPAT_X_ASSUM "_ = (r,s')" MP_TAC THEN
  NAMED_CASES_ON "res" ["";"ra"] THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN FS[] THEN NO_TAC; ALL_TAC] THEN
  NAMED_CASES_ON "ra" ["";"";"n";"n";"retvs";"eid";"f"] THEN CASE_REWRITE_TAC[] THEN
  TRY(REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN FS[] THEN NO_TAC) THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    PCINLAUX_IPC_NT_APPLY;
    ASM_CASES_TAC `LENGTH (retvs:((A)word_lab)list) = LENGTH (rts:num list)` THEN
    ASM_REWRITE_TAC[] THENL [ALL_TAC; REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN FS[] THEN NO_TAC] THEN
    QCASES_ON "OPT_MMAP (FLOOKUP (crep_state_locals s)) rts" THEN CASE_REWRITE_TAC[] THENL
     [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN FS[] THEN NO_TAC; ALL_TAC] THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    PCINLAUX_IPC_NT_APPLY;
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    PCINLAUX_IPC_NT_APPLY;
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    PCINLAUX_IPC_NT_APPLY];;

(* the inlined Nontail call: name the callee and its unreach_elim'd inlined body *)

let PCINLAUX_IPC_NT_PRE : tactic =
  RENAME1 "FLOOKUP inl_bag fname = SOME ap" THEN NAMED_CASES_ON "ap" ["args_vname cb"] THEN
  CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FLOOKUP (crep_state_code (s:(A,FFI)crep_state)) fname = SOME (args_vname,cb)`
    MP_TAC THENL
   [MATCH_MP_TAC FLOOKUP_SUBMAP THEN EXISTS_TAC `inl_fs:(mlstring,num list # (A)crep_prog)fmap` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FLOOKUP_SUBMAP THEN
    EXISTS_TAC `inl_bag:(mlstring,num list # (A)crep_prog)fmap` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `ns:num list = args_vname` || concl th = `prog:(A)crep_prog = cb`))) THEN
  SUBGOAL_THEN `?ic et. unreach_elim (inline_prog ((inl_bag:(mlstring,num list # (A)crep_prog)fmap)
                  \\ fname) prog) = (ic,et:(early_exit)option)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];;

let PCINLAUX_IPC_CALL_TAC : tactic =
  PCINLAUX_IPC_CALL_PRE THEN NAMED_CASES_ON "caltyp" ["";"ctx"] THEN CASE_REWRITE_TAC[] THENL
   [QCASES_ON "FLOOKUP inl_bag fname" THEN CASE_REWRITE_TAC[] THENL
     [PCINLAUX_IPC_TAIL_NOINL_TAC; PCINLAUX_IPC_TAIL_INL_TAC];
    ALL_TAC] THEN
  NAMED_CASES_ON "ctx" ["rts hdlo"] THEN CASE_REWRITE_TAC[] THEN
  ASM_CASES_TAC `ALL_DISTINCT (rts:num list)` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; RFS[] THEN NO_TAC] THEN
  NAMED_CASES_ON "hdlo" ["";"wh"] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THENL
   [QCASES_ON "FLOOKUP inl_bag fname" THEN CASE_REWRITE_TAC[] THENL
     [PCINLAUX_IPC_TAIL_NOINL_TAC; PCINLAUX_IPC_NT_PRE THEN PCINLAUX_IPC_NONTAIL_TAC];
    PCINLAUX_IPC_HDL_TAC];;

let inline_prog_correct = prove
 (PCINLAUX_IPC_STMT,
  REC_IND_TAC crep_evaluate_ind THEN REPEAT CONJ_TAC THEN
  PCINLAUX_PROG_CASES
   ["crep_ShMem",PCINLAUX_IPC_SHMEM_TAC; "crep_Dec",PCINLAUX_IPC_DEC_TAC;
    "crep_Seq",PCINLAUX_IPC_SEQ_TAC; "crep_If",PCINLAUX_IPC_IF_TAC;
    "crep_While",PCINLAUX_IPC_WHILE_TAC; "crep_Call",PCINLAUX_IPC_CALL_TAC]
   PCINLAUX_IPC_GEN);;

(* ------------------------------------------------------------------------- *)
(* Expressions of the inlined code and semantics preservation (HOL4 lines   *)
(* 3042-3460)                                                               *)
(* ------------------------------------------------------------------------- *)

(* HOL4's MAP2 truncates the longer list; with HOL Light's MAP2 (HD/TL of the  *)
(* second list) the hypothesis LENGTH ns <= LENGTH es is added; every use      *)
(* has it                                                                    *)

let exps_of_nested_seq_assign = prove
 (`!ns es (e:(A)crep_exp).
     LENGTH ns <= LENGTH es /\
     MEM e (crep_exps_of (crep_nested_seq (MAP2 crep_Assign ns es)))
     ==> MEM e es`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAP2_DEF; crep_nested_seq_def; crep_exps_of_def; MEM]; ALL_TAC] THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC n <= 0)`; MAP2_DEF; HD; TL; LE_SUC] THEN
  REWRITE_TAC[crep_nested_seq_def; crep_exps_of_def; APPEND; MEM] THEN ASM_MESON_TAC[]);;

let exps_of_nested_decs = prove
 (`!(e:(A)crep_exp) vs es p.
     MEM e (crep_exps_of (nested_decs vs es p)) ==> MEM e es \/ MEM e (crep_exps_of p)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `vs:num list` list_CASES) THEN
  REWRITE_TAC[nested_decs_def; crep_exps_of_def; MEM; APPEND] THEN ASM_MESON_TAC[]);;

let exps_of_arg_load = prove
 (`!(e:(A)crep_exp) tmp_vars args args_vname p.
     MEM e (crep_exps_of (arg_load tmp_vars args args_vname p))
     ==> MEM e args \/ (?c. MEM c tmp_vars /\ e = crep_Var c) \/ MEM e (crep_exps_of p)`,
  REWRITE_TAC[arg_load_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP exps_of_nested_decs) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP exps_of_nested_decs) THEN ASM_REWRITE_TAC[] THEN
  FS[MEM_MAP] THEN ASM_MESON_TAC[]);;

let submap_flookup_alist_to_fmap = prove
 (`!(s:(K,V)fmap) t x v.
     s SUBMAP alist_to_fmap t /\ FLOOKUP s x = SOME v ==> MEM (x,v) t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ALOOKUP_MEM THEN
  REWRITE_TAC[GSYM(CONJUNCT1 ALOOKUP_EQ_FLOOKUP)] THEN ASM_MESON_TAC[FLOOKUP_SUBMAP]);;

let exps_of_unreach_elim = prove
 (`!(p:(A)crep_prog) q r e (rt:B).
     unreach_elim p = (q,r) /\ MEM e (crep_exps_of q) ==> MEM e (crep_exps_of p)`,
  REC_IND_TAC unreach_elim_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN TRY DISCH_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[unreach_elim_def] THEN
  REPEAT(PAIRARG_TAC THEN ASM_REWRITE_TAC[]) THEN
  RW[] THEN GVS(unreach_elim_def :: crep_exps_of_def :: MEM_APPEND :: all_case_eqs()) THEN
  ASM_MESON_TAC[]);;

(* the assignments that replace a Return use its expressions *)

let PCINLAUX_EXPS_OF_ASSIGNS = prove
 (`!(es:((A)crep_exp)list) rets e.
     MEM e (crep_exps_of (crep_nested_seq (MAP2 crep_Assign (TAKE (LENGTH es) rets) es)))
     ==> MEM e es`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC exps_of_nested_seq_assign THEN
  EXISTS_TAC `TAKE (LENGTH (es:((A)crep_exp)list)) (rets:num list)` THEN
  ASM_REWRITE_TAC[LENGTH_TAKE_EQ] THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let PCINLAUX_EXT_DFLT : tactic =
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[transform_eoc_def; transform_branch_def; crep_exps_of_def;
                              MEM_APPEND; MEM]) THEN
  REWRITE_TAC[crep_exps_of_def; MEM_APPEND; MEM] THEN ASM_MESON_TAC[];;

let PCINLAUX_EXT_CALL : tactic =
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  NAMED_CASES_ON "ctyp" ["";"ct"] THENL
   [ALL_TAC; NAMED_CASES_ON "ct" ["rs hd"] THEN NAMED_CASES_ON "hd" ["";"wh"] THENL
     [ALL_TAC; NAMED_CASES_ON "wh" ["w hdl"]]] THEN
  FS[transform_eoc_def; transform_branch_def; crep_exps_of_def; MEM_APPEND] THEN
  ASM_MESON_TAC[];;

let PCINLAUX_EXT_RET : tactic =
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[transform_eoc_def; transform_branch_def; crep_exps_of_def;
                              MEM_APPEND; MEM]) THEN
  REWRITE_TAC[crep_exps_of_def] THEN ASM_MESON_TAC[PCINLAUX_EXPS_OF_ASSIGNS];;

let exps_of_transform_eoc = prove
 (`!rts (p:(A)crep_prog) e.
     MEM e (crep_exps_of (transform_eoc rts p)) ==> MEM e (crep_exps_of p)`,
  REC_IND_TAC transform_eoc_ind THEN REPEAT CONJ_TAC THEN
  PCINLAUX_C_CASES_BY_LAST "transform_eoc"
   ["crep_Return",PCINLAUX_EXT_RET; "crep_Call",PCINLAUX_EXT_CALL]
   PCINLAUX_EXT_DFLT);;

let exps_of_transform_branch = prove
 (`!ld rts (p:(A)crep_prog) e.
     MEM e (crep_exps_of (transform_branch ld rts p)) ==> MEM e (crep_exps_of p)`,
  REC_IND_TAC transform_branch_ind THEN REPEAT CONJ_TAC THEN
  PCINLAUX_C_CASES_BY_LAST "transform_branch"
   ["crep_Return",PCINLAUX_EXT_RET; "crep_Call",PCINLAUX_EXT_CALL]
   PCINLAUX_EXT_DFLT);;

(* the expressions of an inlined callee come from the code *)

let PCINLAUX_EII_CALLEE = prove
 (`!(inl:(mlstring,num list # (A)crep_prog)fmap) fname args_vname p ic et crep_code x.
     inl SUBMAP alist_to_fmap crep_code /\ FLOOKUP inl fname = SOME (args_vname,p) /\
     unreach_elim (inline_prog (inl \\ fname) p) = (ic,et:(early_exit)option) /\
     (!crep_code x.
        inl \\ fname SUBMAP alist_to_fmap crep_code /\
        MEM x (crep_exps_of (inline_prog (inl \\ fname) p))
        ==> MEM x (crep_exps_of p) \/ (?c. x = crep_Const c) \/ (?v. x = crep_Var v) \/
            (?name params body. MEM (name,params,body) crep_code /\
                                MEM x (crep_exps_of body))) /\
     MEM x (crep_exps_of ic)
     ==> (?c. x = crep_Const c) \/ (?v. x = crep_Var v) \/
         (?name params body. MEM (name,params,body) crep_code /\ MEM x (crep_exps_of body))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MEM (x:(A)crep_exp) (crep_exps_of (inline_prog (inl \\ fname) p))` ASSUME_TAC
  THENL [ASM_MESON_TAC[exps_of_unreach_elim]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`crep_code:(mlstring # num list # (A)crep_prog)list`;
                                `x:(A)crep_exp`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBMAP_DOMSUB; SUBMAP_TRANS]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISJ2_TAC THEN DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`fname:mlstring`; `args_vname:num list`; `p:(A)crep_prog`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC submap_flookup_alist_to_fmap THEN
    EXISTS_TAC `inl:(mlstring,num list # (A)crep_prog)fmap` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]]);;

(* the assignments back from the return temporaries use variables only *)

let PCINLAUX_EXPS_OF_ASSIGN_VARS = prove
 (`!(rs:num list) tr (x:(A)crep_exp).
     MEM x (crep_exps_of (crep_nested_seq (MAP2 crep_Assign rs (MAP crep_Var tr))))
     ==> LENGTH tr = LENGTH rs ==> ?v. x = crep_Var v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`rs:num list`; `MAP crep_Var (tr:num list):((A)crep_exp)list`; `x:(A)crep_exp`]
                exps_of_nested_seq_assign) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; LE_REFL; MEM_MAP] THEN MESON_TAC[]);;

(* the Call case of exps_of_inst_inline: the callee found and its body named *)

let PCINLAUX_EII_FOUND : tactic =
  RENAME1 "FLOOKUP inlineable_fs e = SOME ap" THEN NAMED_CASES_ON "ap" ["args_vname p"] THEN
  SUBGOAL_THEN `?ic et. unreach_elim (inline_prog ((inlineable_fs:(mlstring,num list # (A)crep_prog)
                  fmap) \\ e) p) = (ic,et:(early_exit)option)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[pair_CASE] THEN CASE_REWRITE_TAC[] THEN
  REMOVE_THEN "ihc" (MP_TAC o SPECL [`args_vname:num list`; `p:(A)crep_prog`]) THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let PCINLAUX_EII_FROM_IC : tactic =
  DISJ2_TAC THEN MATCH_MP_TAC PCINLAUX_EII_CALLEE THEN
  MAP_EVERY EXISTS_TAC [`inlineable_fs:(mlstring,num list # (A)crep_prog)fmap`; `e:mlstring`;
                        `args_vname:num list`; `p:(A)crep_prog`; `ic:(A)crep_prog`;
                        `et:(early_exit)option`] THEN
  ASM_REWRITE_TAC[];;

let PCINLAUX_EII_TAIL : tactic =
  PCINLAUX_EII_FOUND THEN REWRITE_TAC[inline_tail_def; crep_exps_of_def; APPEND] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o MATCH_MP exps_of_arg_load) THENL
   [ASM_REWRITE_TAC[crep_exps_of_def]; ASM_MESON_TAC[]; PCINLAUX_EII_FROM_IC];;

let PCINLAUX_EII_NONTAIL : tactic =
  PCINLAUX_EII_FOUND THEN REWRITE_TAC[inline_nontail_def] THEN
  DISCH_THEN(DISJ_CASES_TAC o MATCH_MP exps_of_nested_decs) THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[MEM_REPLICATE]) THEN MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[crep_exps_of_def; MEM_APPEND]) THENL
   [FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o MATCH_MP exps_of_arg_load) THENL
     [ASM_REWRITE_TAC[crep_exps_of_def]; ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "not_branch_ret" with Failure _ -> false))
          (concl th))) THEN
    COND_CASES_TAC THEN REWRITE_TAC[crep_exps_of_def; APPEND; MEM] THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP exps_of_transform_eoc) THEN PCINLAUX_EII_FROM_IC;
      ASM_MESON_TAC[];
      FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP exps_of_transform_branch) THEN PCINLAUX_EII_FROM_IC];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP PCINLAUX_EXPS_OF_ASSIGN_VARS) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN MESON_TAC[]];;

let PCINLAUX_EII_DFLT : tactic =
  REPEAT GEN_TAC THEN TRY(DISCH_THEN(fun th -> REPEAT GEN_TAC THEN MP_TAC th)) THEN
  REWRITE_TAC[inline_prog_def; LET_DEF; LET_END_DEF; crep_exps_of_def; MEM; MEM_APPEND] THEN
  MESON_TAC[];;

let PCINLAUX_EII_CALL : tactic =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> LABEL_TAC "ihc" (CONJUNCT1 th) THEN LABEL_TAC "ihh" (last (CONJUNCTS th))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  QPAT_X_ASSUM "MEM x _" (MP_TAC o ONCE_REWRITE_RULE[inline_prog_def]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  NAMED_CASES_ON "ctyp" ["";"ct"] THENL
   [ALL_TAC; NAMED_CASES_ON "ct" ["rs hd"] THEN NAMED_CASES_ON "hd" ["";"wh"] THENL
     [ALL_TAC; NAMED_CASES_ON "wh" ["w hdl"]]] THEN
  CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[] THEN QCASES_ON "FLOOKUP inlineable_fs e" THEN CASE_REWRITE_TAC[] THENL
     [DISCH_TAC THEN ASM_REWRITE_TAC[]; PCINLAUX_EII_TAIL];
    COND_CASES_TAC THENL [REWRITE_TAC[crep_exps_of_def] THEN MESON_TAC[]; ALL_TAC] THEN
    QCASES_ON "FLOOKUP inlineable_fs e" THEN CASE_REWRITE_TAC[] THENL
     [REWRITE_TAC[crep_exps_of_def] THEN MESON_TAC[]; PCINLAUX_EII_NONTAIL];
    COND_CASES_TAC THEN TRY(QCASES_ON "FLOOKUP inlineable_fs e") THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[BASICAUX_pair_CASE_K; crep_exps_of_def; MEM_APPEND] THEN
    REMOVE_THEN "ihh" (MP_TAC o SPECL [`rs:num list`; `w:A word`; `hdl:(A)crep_prog`]) THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`crep_code:(mlstring # num list # (A)crep_prog)list`;
                               `x:(A)crep_exp`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]];;

(* HOL4's statement names the expression e, as the function name of the induction; *)
(* here it is x                                                                     *)

let exps_of_inst_inline = prove
 (`!(inl_fs:(mlstring,num list # (A)crep_prog)fmap) prog crep_code x.
     inl_fs SUBMAP alist_to_fmap crep_code /\ MEM x (crep_exps_of (inline_prog inl_fs prog))
     ==> MEM x (crep_exps_of prog) \/ (?c. x = crep_Const c) \/ (?v. x = crep_Var v) \/
         (?name params body. MEM (name,params,body) crep_code /\ MEM x (crep_exps_of body))`,
  REC_IND_TAC inline_prog_ind THEN REPEAT CONJ_TAC THEN
  PCINLAUX_C_CASES_BY_LAST "inline_prog" ["crep_Call",PCINLAUX_EII_CALL] PCINLAUX_EII_DFLT);;

let every_inst_crep_inline = prove
 (`!(crep_code:(mlstring # num list # (A)crep_prog)list) inl_fs.
     (!e. MEM e crep_code
          ==> (\(name,params,body).
                 !e. MEM e (crep_exps_of body)
                     ==> crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2) e) e) /\
     inl_fs SUBMAP alist_to_fmap crep_code
     ==> (!e. MEM e (compile_inl_prog inl_fs crep_code)
              ==> (\(name,params,body).
                     !e. MEM e (crep_exps_of body)
                         ==> crep_every_exp (\x. !op es. x = Crepop op es ==> LENGTH es = 2)
                               e) e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[compile_inl_prog_def; MEM_MAP] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RENAME1 "MEM y crep_code" THEN NAMED_CASES_ON "y" ["n ps b"] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(inl_fs:(mlstring,num list # (A)crep_prog)fmap) \\ n`; `b:(A)crep_prog`;
                 `crep_code:(mlstring # num list # (A)crep_prog)list`; `e:(A)crep_exp`]
                exps_of_inst_inline) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBMAP_DOMSUB; SUBMAP_TRANS]; ALL_TAC] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(n:mlstring,ps:num list,b:(A)crep_prog)`) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[crep_every_exp_def] THEN SIMP[];
    ASM_REWRITE_TAC[crep_every_exp_def] THEN SIMP[];
    FIRST_X_ASSUM(MP_TAC o SPEC `(name:mlstring,params:num list,body:(A)crep_prog)`) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN ASM_MESON_TAC[]]);;

let fst_map_3_f = prove
 (`!(inl_fs:(mlstring,num list # (A)crep_prog)fmap) (x:mlstring # B # (A)crep_prog).
     FST x =
     (FST o (\(name,params,body). name,params,inline_prog (inl_fs \\ name) body)) x`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN SIMP[]);;

let compile_inline_distinct = prove
 (`!(crep_code:(mlstring # B # (A)crep_prog)list) inl_fs.
     ALL_DISTINCT (MAP FST crep_code)
     ==> ALL_DISTINCT (MAP FST (compile_inl_prog inl_fs crep_code))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_inl_prog_def; MAP_MAP_o] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN REWRITE_TAC[GSYM fst_map_3_f]);;

(* HOL4 proves this by unfolding the Call; here it is inline_prog_correct with the   *)
(* empty inline map (inline_prog FEMPTY leaves the call as it is)                    *)

let evaluate_call_same_result_state = prove
 (`!e args (s:(A,FFI)crep_state) r s' t inl_fs.
     crep_evaluate (crep_Call NONE e args,s) = (r,s') /\ state_rel_code s t /\
     inl_fs SUBMAP crep_state_code s /\ locals_strong_rel s t /\ code_inl_rel inl_fs s t /\
     ~(r = SOME crep_Error)
     ==> FST (crep_evaluate (crep_Call NONE e args,t)) =
         FST (crep_evaluate (crep_Call NONE e args,s)) /\
         state_rel_code (SND (crep_evaluate (crep_Call NONE e args,s)))
                        (SND (crep_evaluate (crep_Call NONE e args,t)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`crep_Call NONE e args:(A)crep_prog`; `s:(A,FFI)crep_state`;
                 `r:((A)crep_result)option`; `s':(A,FFI)crep_state`;
                 `inl_fs:(mlstring,num list # (A)crep_prog)fmap`; `t:(A,FFI)crep_state`;
                 `FEMPTY:(mlstring,num list # (A)crep_prog)fmap`] inline_prog_correct) THEN
  ASM_REWRITE_TAC[SUBMAP_FEMPTY] THEN
  SUBGOAL_THEN `inline_prog (FEMPTY:(mlstring,num list # (A)crep_prog)fmap)
                  (crep_Call NONE e args) = crep_Call NONE e args` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[inline_prog_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF; FLOOKUP_EMPTY] THEN
    CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* the semantics depends on the runs only through their results and ffi states *)

let PCINLAUX_SEM_EQ = prove
 (`!(s:(A,FFI)crep_state) (t:(A,FFI)crep_state) start.
     (!k. FST (crep_evaluate (crep_Call NONE start [],crep_state_clock_fupd (K k) t)) =
          FST (crep_evaluate (crep_Call NONE start [],crep_state_clock_fupd (K k) s)) /\
          crep_state_ffi (SND (crep_evaluate (crep_Call NONE start [],
                                              crep_state_clock_fupd (K k) t))) =
          crep_state_ffi (SND (crep_evaluate (crep_Call NONE start [],
                                              crep_state_clock_fupd (K k) s))))
     ==> crep_semantics t start = crep_semantics s start`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[crep_semantics_def; LET_DEF; LET_END_DEF] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (CASE_TERM
   `!res:behaviour.
      (?k t' (r:((A)crep_result)option) outcome.
         crep_evaluate (crep_Call NONE start [],crep_state_clock_fupd (K k) (t:(A,FFI)crep_state)) =
           (r,t') /\
         (match r with
            SOME (crep_FinalFFI e) -> outcome = FFI_outcome e
          | SOME (crepSem_Return _) -> outcome = Success
          | _ -> F) /\
         res = Terminate outcome (ffi_state_io_events (crep_state_ffi t'))) <=>
      (?k t' (r:((A)crep_result)option) outcome.
         crep_evaluate (crep_Call NONE start [],crep_state_clock_fupd (K k) (s:(A,FFI)crep_state)) =
           (r,t') /\
         (match r with
            SOME (crep_FinalFFI e) -> outcome = FFI_outcome e
          | SOME (crepSem_Return _) -> outcome = Success
          | _ -> F) /\
         res = Terminate outcome (ffi_state_io_events (crep_state_ffi t')))`)
   (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `t1:(A,FFI)crep_state`
    (X_CHOOSE_THEN `r1:((A)crep_result)option` (X_CHOOSE_THEN `oc:outcome`
      STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC
     [`k:num`; `SND (crep_evaluate (crep_Call NONE start [],
                                    crep_state_clock_fupd (K k) (s:(A,FFI)crep_state)))`;
      `r1:((A)crep_result)option`; `oc:outcome`];
    MAP_EVERY EXISTS_TAC
     [`k:num`; `SND (crep_evaluate (crep_Call NONE start [],
                                    crep_state_clock_fupd (K k) (t:(A,FFI)crep_state)))`;
      `r1:((A)crep_result)option`; `oc:outcome`]] THEN
  ASM_REWRITE_TAC[BASICAUX_PAIR_SND]);;

(* the code of compile_inl_prog *)

let PCINLAUX_ALOOKUP_COMPILE = prove
 (`!(inl_fs:(mlstring,num list # (A)crep_prog)fmap) (l:(mlstring # B # (A)crep_prog)list) x.
     ALOOKUP (compile_inl_prog inl_fs l) x =
     OPTION_MAP (\(params,body). params,inline_prog (inl_fs \\ x) body) (ALOOKUP l x)`,
  GEN_TAC THEN REWRITE_TAC[compile_inl_prog_def] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ALOOKUP_THM; OPTION_MAP_DEF] THEN
  SPEC_TAC(`h:mlstring # B # (A)crep_prog`,`h:mlstring # B # (A)crep_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[ALOOKUP_THM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[]);;

let state_rel_imp_semantics_local = prove
 (`!(s:(A,FFI)crep_state) t crep_code start inl_fs ns prog.
     state_rel_code s t /\ locals_strong_rel s t /\ ALL_DISTINCT (MAP FST crep_code) /\
     crep_state_code s = alist_to_fmap crep_code /\ inl_fs SUBMAP crep_state_code s /\
     crep_state_code t = alist_to_fmap (compile_inl_prog inl_fs crep_code) /\
     FLOOKUP (crep_state_code s) start = SOME (ns,prog) /\
     ~(crep_semantics s start = Fail)
     ==> crep_semantics t start = crep_semantics s start`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `code_inl_rel inl_fs (s:(A,FFI)crep_state) (t:(A,FFI)crep_state)` ASSUME_TAC THENL
   [REWRITE_TAC[code_inl_rel_def] THEN
    ASM_REWRITE_TAC[CONJUNCT1 ALOOKUP_EQ_FLOOKUP; PCINLAUX_ALOOKUP_COMPILE] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `(inl_fs:(mlstring,num list # (A)crep_prog)fmap) \\ fname` THEN
    ASM_REWRITE_TAC[SUBMAP_DOMSUB; OPTION_MAP_DEF] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. ~(FST (crep_evaluate (crep_Call NONE start [],
                       crep_state_clock_fupd (K k) (s:(A,FFI)crep_state))) = SOME crep_Error)`
    ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~(crep_semantics (s:(A,FFI)crep_state) start = Fail)` THEN
    REWRITE_TAC[crep_semantics_def; LET_DEF; LET_END_DEF] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC PCINLAUX_SEM_EQ THEN GEN_TAC THEN
  MP_TAC(ISPECL [`start:mlstring`; `[]:((A)crep_exp)list`;
                 `crep_state_clock_fupd (K k) (s:(A,FFI)crep_state)`;
                 `FST (crep_evaluate (crep_Call NONE start [],
                         crep_state_clock_fupd (K k) (s:(A,FFI)crep_state)))`;
                 `SND (crep_evaluate (crep_Call NONE start [],
                         crep_state_clock_fupd (K k) (s:(A,FFI)crep_state)))`;
                 `crep_state_clock_fupd (K k) (t:(A,FFI)crep_state)`;
                 `inl_fs:(mlstring,num list # (A)crep_prog)fmap`]
                evaluate_call_same_result_state) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[PAIR] THEN ASM_REWRITE_TAC[] THEN
    FS[state_rel_code_def; locals_strong_rel_def; code_inl_rel_def];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FS[state_rel_code_def]);;

let crep_inlineProof_state_rel_imp_semantics = prove
 (`!(s:(A,FFI)crep_state) t crep_code start inl_fname ns prog.
     state_rel_code s t /\ locals_strong_rel s t /\ ALL_DISTINCT (MAP FST crep_code) /\
     crep_state_code s = alist_to_fmap crep_code /\
     crep_state_code t = alist_to_fmap (compile_inl_top inl_fname crep_code) /\
     FLOOKUP (crep_state_code s) start = SOME (ns,prog) /\
     ~(crep_semantics s start = Fail)
     ==> crep_semantics t start = crep_semantics s start`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_inl_top_def; LET_DEF; LET_END_DEF] THEN STRIP_TAC THEN
  MATCH_MP_TAC state_rel_imp_semantics_local THEN
  MAP_EVERY EXISTS_TAC
   [`crep_code:(mlstring # num list # (A)crep_prog)list`;
    `alist_to_fmap (FILTER (\(x,y). MEM x inl_fname) (crep_code:(mlstring # num list # (A)crep_prog)list))`;
    `ns:num list`; `prog:(A)crep_prog`] THEN
  ASM_REWRITE_TAC[SUBMAP_FLOOKUP_EQN; CONJUNCT1 ALOOKUP_EQ_FLOOKUP; ALOOKUP_FILTER] THEN
  MESON_TAC[option_DISTINCT]);;
