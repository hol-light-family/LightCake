(* ========================================================================= *)
(* typeSysProps: port of HOL4 semantics/proofs/typeSysPropsScript.sml        *)
(* (CakeML v3479).  Theorems about the type system.                          *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/typeSystem.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Notes on the rendering:                                                   *)
(* - Record fields: tenv.v is type_env_v tenv (typeSystem); tenv with v :=   *)
(*   x is type_env_v_fupd (K x) tenv; EVERY is ALL, LIST_REL is ALL2, set   *)
(*   is set_of_list, ZIP (l1,l2) is ZIP l1 l2 (every ZIP of this file comes  *)
(*   with a LENGTH hypothesis, so HOL4's truncation never matters).         *)
(* - HOL4's paired lambdas (\(a,b). t) are (\p. match p with (a,b) -> t);    *)
(*   the restricted quantifier of type_pes_def is !p e. MEM (p,e) pes ==>.   *)
(* - Variables that a HOL4 statement quantifies without using them (their   *)
(*   HOL4 type is a type variable) get the type their name suggests;         *)
(*   variables that a HOL4 statement leaves free stay free.                 *)
(* - HOL4 rebinds tveLookup_freevars with a [local] theorem of another       *)
(*   statement: that one is TPROPSAUX_tveLookup_freevars here.              *)
(* - type_op_cases is computed as in HOL4 (case theorems, DNF, PULL_EXISTS). *)
(* - TPROPSAUX_ names are local helpers (lemmas and tactics).               *)
(* ------------------------------------------------------------------------- *)

(* HOL4 export_rewrites of the type abbreviations of typeSystem *)
let _ = cake_add_simps [typeSystem_Tarray_def; typeSystem_Tbool_def;
  typeSystem_Tchar_def; typeSystem_Texn_def; typeSystem_Tfn_def;
  typeSystem_Tint_def; typeSystem_Tlist_def; typeSystem_Tref_def;
  typeSystem_Tstring_def; typeSystem_Ttup_def; typeSystem_Tvector_def;
  typeSystem_Tword64_def; typeSystem_Tword8_def; typeSystem_Tword8array_def;
  typeSystem_Tdouble_def];;

(* ----------- Basic stuff ----------- *)

let unchanged_tenv = prove
 (`!tenv:type_env.
     type_env_REC (type_env_v tenv) (type_env_c tenv) (type_env_t tenv) = tenv`,
  REWRITE_TAC[type_env_component_equality; type_env_INFO.ri_accessors]);;
let _ = cake_add_simps [unchanged_tenv];;

let extend_dec_tenv_assoc = prove
 (`!tenv1 tenv2 tenv3:type_env.
     extend_dec_tenv tenv1 (extend_dec_tenv tenv2 tenv3) =
     extend_dec_tenv (extend_dec_tenv tenv1 tenv2) tenv3`,
  RW[extend_dec_tenv_def]);;
let _ = cake_add_simps [extend_dec_tenv_assoc];;

let tenv_val_ok_nsEmpty = prove
 (`tenv_val_ok nsEmpty`,
  RW[tenv_val_ok_def]);;
let _ = cake_add_simps [tenv_val_ok_nsEmpty];;

let tenv_ctor_ok_nsEmpty = prove
 (`tenv_ctor_ok nsEmpty`,
  RW[tenv_ctor_ok_def]);;
let _ = cake_add_simps [tenv_ctor_ok_nsEmpty];;

let tenv_abbrev_ok_nsEmpty = prove
 (`tenv_abbrev_ok nsEmpty`,
  RW[tenv_abbrev_ok_def]);;
let _ = cake_add_simps [tenv_abbrev_ok_nsEmpty];;

let tenv_ok_empty = prove
 (`tenv_ok (type_env_REC nsEmpty nsEmpty nsEmpty)`,
  RW[tenv_ok_def; tenv_val_ok_def; tenv_ctor_ok_def; tenv_abbrev_ok_def]);;
let _ = cake_add_simps [tenv_ok_empty];;

(* HOL4's restricted quantifier !(p,e)::set pes. P is written           *)
(* !p e. MEM (p,e) pes ==> P (as for the Handle and Mat rules of type_e) *)

let type_pes_def = cake_def
  `type_pes (tvs:num) (tvs':num) (tenv:type_env) (tenvE:tenv_val_exp)
            (pes:(pat#exp)list) (t1:t) (t2:t) <=>
     (!p e. MEM (p,e) pes
            ==> ?bindings.
                  ALL_DISTINCT (pat_bindings p) /\
                  type_p tvs tenv p t1 bindings /\
                  type_e tenv (bind_var_list tvs' bindings tenvE) e t2)`;;

let type_pes_cons = prove
 (`!tvs tvs' tenv tenvE p e pes t1 t2.
     type_pes tvs tvs' tenv tenvE (CONS (p,e) pes) t1 t2 <=>
     (ALL_DISTINCT (pat_bindings p) /\
      (?bindings.
         type_p tvs tenv p t1 bindings /\
         type_e tenv (bind_var_list tvs' bindings tenvE) e t2) /\
      type_pes tvs tvs' tenv tenvE pes t1 t2)`,
  REWRITE_TAC[type_pes_def; MEM; PAIR_EQ] THEN MESON_TAC[]);;

(* ---------- check_freevars ---------- *)

let check_freevars_add = prove
 (`!tvs tvs' t. check_freevars tvs tvs' t
     ==> !tvs''. tvs'' >= tvs ==> check_freevars tvs'' tvs' t`,
  MATCH_MP_TAC check_freevars_ind THEN RW[check_freevars_def] THENL
   [ASM_MESON_TAC[EVERY_MEM]; ASM_ARITH_TAC]);;

(* ---------- type_subst ---------- *)

let check_freevars_subst_single = prove
 (`!dbmax tvs t tvs' ts.
     LENGTH tvs = LENGTH ts /\
     check_freevars dbmax tvs t /\
     ALL (check_freevars dbmax tvs') ts
     ==> check_freevars dbmax tvs' (type_subst (alist_to_fmap (ZIP tvs ts)) t)`,
  MATCH_MP_TAC check_freevars_ind THEN
  RW[check_freevars_def; type_subst_def; EVERY_MAP; ALOOKUP_EQ_FLOOKUP] THENL
   [CASE_TAC THEN FS[check_freevars_def; ALOOKUP_NONE] THENL
     [ASM_MESON_TAC[MAP_FST_ZIP];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN ASM_SIMP_TAC[MEM_ZIP] THEN
      FS[EVERY_MEM] THEN ASM_MESON_TAC[MEM_EL]];
    FS[EVERY_MEM] THEN ASM_MESON_TAC[]]);;

let check_freevars_subst_list = prove
 (`!dbmax tvs tvs' ts ts'.
     LENGTH tvs = LENGTH ts /\
     ALL (check_freevars dbmax tvs) ts' /\
     ALL (check_freevars dbmax tvs') ts
     ==> ALL (check_freevars dbmax tvs')
             (MAP (type_subst (alist_to_fmap (ZIP tvs ts))) ts')`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  RW[] THEN ASM_MESON_TAC[check_freevars_subst_single]);;

(* ---------- deBruijn_inc ---------- *)

let deBruijn_inc0 = prove
 (`(!t sk. deBruijn_inc sk 0 t = t) /\
   (!ts sk. MAP (deBruijn_inc sk 0) ts = ts)`,
  MATCH_MP_TAC t_INDUCT THEN RW[deBruijn_inc_def] THEN ASM_MESON_TAC[]);;

(* MAP f (MAP g l) = MAP h l from the hypothesis !y. MEM y l ==> ...    *)
let TPROPSAUX_MAP_EQ_TAC =
  REWRITE_TAC[GSYM MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; o_THM] THEN ASM_MESON_TAC[];;

let deBruijn_inc_deBruijn_inc = prove
 (`!sk i2 t i1.
     deBruijn_inc sk i1 (deBruijn_inc sk i2 t) = deBruijn_inc sk (i1 + i2) t`,
  MATCH_MP_TAC deBruijn_inc_ind THEN RW[deBruijn_inc_def] THENL
   [FS[];
    COND_CASES_TAC THEN REWRITE_TAC[injectivity "t"] THEN ASM_ARITH_TAC;
    TPROPSAUX_MAP_EQ_TAC]);;

let deBuijn_inc_lem1 = prove
 (`!sk i2 t i1.
     deBruijn_inc sk i1 (deBruijn_inc 0 (sk + i2) t) =
     deBruijn_inc 0 (i1 + (sk + i2)) t`,
  MATCH_MP_TAC deBruijn_inc_ind THEN RW[deBruijn_inc_def] THEN
  RW[injectivity "t"] THEN TRY ASM_ARITH_TAC THEN
  SIMP[MAP_MAP_o; MAP_EQ_f; o_THM] THEN ASM_MESON_TAC[]);;
let type_subst_deBruijn_inc_single = prove
 (`!s t ts tvs inc sk.
     LENGTH tvs = LENGTH ts /\
     s = alist_to_fmap (ZIP tvs ts) /\
     check_freevars 0 tvs t
     ==> deBruijn_inc sk inc (type_subst s t) =
         type_subst (alist_to_fmap (ZIP tvs (MAP (\t. deBruijn_inc sk inc t) ts))) t`,
  MATCH_MP_TAC type_subst_ind THEN
  RW[deBruijn_inc_def; type_subst_def; check_freevars_def; ALOOKUP_EQ_FLOOKUP] THENL
   [ASM_SIMP_TAC[ALOOKUP_ZIP_MAP_SND; o_THM] THEN CASE_TAC THEN
    SIMP[OPTION_MAP_DEF; deBruijn_inc_def] THEN
    FS[ALOOKUP_NONE] THEN ASM_MESON_TAC[MAP_FST_ZIP];
    SIMP[MAP_MAP_o; MAP_EQ_f; o_THM] THEN FS[EVERY_MEM] THEN ASM_MESON_TAC[];
    ASM_ARITH_TAC]);;

let type_subst_deBruijn_inc_list = prove
 (`!ts' ts tvs inc sk.
     LENGTH tvs = LENGTH ts /\
     ALL (check_freevars 0 tvs) ts'
     ==> MAP (deBruijn_inc sk inc) (MAP (type_subst (alist_to_fmap (ZIP tvs ts))) ts') =
         MAP (type_subst (alist_to_fmap (ZIP tvs (MAP (\t. deBruijn_inc sk inc t) ts)))) ts'`,
  LIST_INDUCT_TAC THEN RW[] THEN ASM_MESON_TAC[type_subst_deBruijn_inc_single]);;

let check_freevars_deBruijn_inc = prove
 (`!tvs tvs' t. check_freevars tvs tvs' t
     ==> !n n'. check_freevars (n + tvs) tvs' (deBruijn_inc n' n t)`,
  MATCH_MP_TAC check_freevars_ind THEN
  RW[check_freevars_def; deBruijn_inc_def] THEN
  FS[EVERY_MAP; EVERY_MEM] THEN RW[check_freevars_def] THEN ASM_ARITH_TAC);;

let nil_deBruijn_inc = prove
 (`!skip tvs t.
     (check_freevars skip [] t \/ check_freevars skip [] (deBruijn_inc skip tvs t))
     ==> deBruijn_inc skip tvs t = t`,
  MATCH_MP_TAC deBruijn_inc_ind THEN
  RW[deBruijn_inc_def; check_freevars_def] THEN TRY ASM_ARITH_TAC THEN
  MATCH_MP_TAC MAP_EQ_DEGEN THEN FS[EVERY_MEM; EVERY_MAP] THEN ASM_MESON_TAC[]);;


(* ---------- deBruijn_subst ---------- *)

(* HOL4 quantifies some variables that the statement does not use (n,   *)
(* tvs'' and others below); their HOL4 type is a type variable, here    *)
(* the type that the name suggests                                      *)

let deBruijn_subst_check_freevars = prove
 (`!tvs tvs' t ts (n:num).
     check_freevars tvs tvs' t /\
     ALL (check_freevars tvs tvs') ts
     ==> check_freevars tvs tvs' (deBruijn_subst 0 ts t)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC check_freevars_ind THEN
  RW[check_freevars_def; deBruijn_subst_def; EVERY_MAP] THEN
  FS[EVERY_MEM] THEN FS[MEM_EL] THEN TRY (ASM_MESON_TAC[]) THEN ASM_ARITH_TAC);;
let deBruijn_subst_check_freevars2 = prove
 (`!tvs tvs' t ts (n:num) (tvs'':num).
     check_freevars (LENGTH ts) tvs' t /\
     ALL (check_freevars tvs tvs') ts
     ==> check_freevars tvs tvs' (deBruijn_subst 0 ts t)`,
  MATCH_MP_TAC check_freevars_ind THEN
  RW[check_freevars_def; deBruijn_subst_def; EVERY_MAP] THEN
  FS[EVERY_MEM] THEN FS[MEM_EL] THEN TRY (ASM_MESON_TAC[]) THEN ASM_ARITH_TAC);;

let check_freevars_subst_inc = prove
 (`!tvs tvs2 t.
     check_freevars tvs tvs2 t
     ==> !tvs' targs tvs1.
           tvs = LENGTH targs + tvs' /\
           ALL (check_freevars (tvs1 + tvs') tvs2) targs
           ==> check_freevars (tvs1 + tvs') tvs2
                 (deBruijn_subst 0 targs (deBruijn_inc (LENGTH targs) tvs1 t))`,
  MATCH_MP_TAC check_freevars_ind THEN
  RW[check_freevars_def; deBruijn_inc_def; deBruijn_subst_def; EVERY_MAP] THEN
  FS[EVERY_MEM] THEN
  ASM_CASES_TAC `n < LENGTH (targs:t list)` THEN
  RW[deBruijn_subst_def; check_freevars_def] THEN
  FS[MEM_EL] THEN TRY (ASM_MESON_TAC[]) THEN ASM_ARITH_TAC);;

let check_freevars_subst = prove
 (`!tvs tvs2 t.
     check_freevars tvs tvs2 t
     ==> !tvs' targs tvs1.
           tvs = LENGTH targs + tvs' /\
           ALL (check_freevars (tvs1 + tvs') tvs2) targs
           ==> check_freevars (tvs1 + tvs') tvs2 (deBruijn_subst 0 targs t)`,
  MATCH_MP_TAC check_freevars_ind THEN
  RW[check_freevars_def; deBruijn_inc_def; deBruijn_subst_def; EVERY_MAP] THEN
  FS[EVERY_MEM] THEN
  ASM_CASES_TAC `n < LENGTH (targs:t list)` THEN
  RW[deBruijn_subst_def; check_freevars_def] THEN
  FS[MEM_EL] THEN TRY (ASM_MESON_TAC[]) THEN ASM_ARITH_TAC);;


let type_subst_deBruijn_subst_single = prove
 (`!s t tvs (tvs':num) ts ts' inc.
     LENGTH tvs = LENGTH ts /\
     check_freevars 0 tvs t /\
     s = alist_to_fmap (ZIP tvs ts)
     ==> deBruijn_subst inc ts' (type_subst (alist_to_fmap (ZIP tvs ts)) t) =
         type_subst (alist_to_fmap (ZIP tvs (MAP (\t. deBruijn_subst inc ts' t) ts))) t`,
  MATCH_MP_TAC type_subst_ind THEN
  RW[deBruijn_subst_def; deBruijn_inc_def; type_subst_def; check_freevars_def;
     ALOOKUP_EQ_FLOOKUP] THENL
   [ASM_SIMP_TAC[ALOOKUP_ZIP_MAP_SND; o_THM] THEN CASE_TAC THEN
    SIMP[OPTION_MAP_DEF] THEN FS[ALOOKUP_NONE] THEN ASM_MESON_TAC[MAP_FST_ZIP];
    SIMP[MAP_MAP_o; MAP_EQ_f; o_THM] THEN FS[EVERY_MEM] THEN ASM_MESON_TAC[];
    ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let type_subst_deBruijn_subst_list = prove
 (`!(t:t) tvs (tvs':num) ts ts' ts'' inc.
     LENGTH tvs = LENGTH ts /\
     ALL (check_freevars 0 tvs) ts''
     ==> MAP (deBruijn_subst inc ts') (MAP (type_subst (alist_to_fmap (ZIP tvs ts))) ts'') =
         MAP (type_subst (alist_to_fmap (ZIP tvs (MAP (\t. deBruijn_subst inc ts' t) ts)))) ts''`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN
  RW[] THEN ASM_MESON_TAC[type_subst_deBruijn_subst_single]);;

let check_freevars_lem = prove
 (`!l tvs' t.
     check_freevars l tvs' t
     ==> !targs n1 tvs.
           l = n1 + LENGTH targs /\
           ALL (check_freevars tvs tvs') targs
           ==> check_freevars (n1 + tvs) tvs'
                 (deBruijn_subst n1 (MAP (deBruijn_inc 0 n1) targs) t)`,
  MATCH_MP_TAC check_freevars_ind THEN
  RW[deBruijn_inc_def; deBruijn_subst_def; check_freevars_def] THENL
   [FS[EVERY_MAP; EVERY_MEM] THEN ASM_MESON_TAC[];
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `n - n1 < LENGTH (targs:t list)` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[EL_MAP] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM ALL_MEM]) THEN
      DISCH_THEN(MP_TAC o SPEC `EL (n - n1) (targs:t list)`) THEN
      ASM_SIMP_TAC[MEM_EL] THEN
      DISCH_THEN(ACCEPT_TAC o SPECL [`n1:num`; `0`] o
                 MATCH_MP check_freevars_deBruijn_inc);
      COND_CASES_TAC THEN REWRITE_TAC[check_freevars_def] THEN ASM_ARITH_TAC]]);;

let nil_deBruijn_subst = prove
 (`!skip tvs t. check_freevars skip [] t ==> deBruijn_subst skip tvs t = t`,
  MATCH_MP_TAC deBruijn_subst_ind THEN
  RW[deBruijn_subst_def; check_freevars_def] THEN
  MATCH_MP_TAC MAP_EQ_DEGEN THEN FS[EVERY_MEM] THEN ASM_MESON_TAC[]);;
let deBruijn_subst2 = prove
 (`(!t sk targs targs' (tvs':num).
      check_freevars (LENGTH targs) [] t
      ==> deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs') (deBruijn_subst 0 targs t) =
          deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs) t) /\
   (!ts sk targs targs' (tvs':num).
      ALL (check_freevars (LENGTH targs) []) ts
      ==> MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) (MAP (deBruijn_subst 0 targs) ts) =
          MAP (deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs)) ts)`,
  MATCH_MP_TAC t_INDUCT THEN
  RW[deBruijn_subst_def; deBruijn_inc_def] THEN
  FS[EL_MAP; MAP_MAP_o; o_DEF; check_freevars_def] THEN
  TRY ASM_ARITH_TAC THEN ASM_MESON_TAC[]);;

let type_e_subst_lem3 = prove
 (`!tvs tvs2 t.
     check_freevars tvs tvs2 t
     ==> !tvs' targs n.
           tvs = n + LENGTH targs /\
           ALL (check_freevars tvs' tvs2) targs
           ==> check_freevars (n + tvs') tvs2
                 (deBruijn_subst n (MAP (deBruijn_inc 0 n) targs) t)`,
  MATCH_MP_TAC check_freevars_ind THEN
  RW[check_freevars_def; deBruijn_inc_def; deBruijn_subst_def; EVERY_MAP] THEN
  FS[EVERY_MEM] THEN RW[] THEN
  FS[check_freevars_def; EL_MAP; MEM_EL] THENL
   [SUBGOAL_THEN `n - n' < LENGTH (targs:t list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_MAP] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `EL (n - n') (targs:t list)`) THEN
    ASM_SIMP_TAC[MEM_EL] THEN
    DISCH_THEN(ACCEPT_TAC o SPECL [`n':num`; `0`] o
               MATCH_MP check_freevars_deBruijn_inc);
    ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let type_e_subst_lem5 = prove
 (`(!t n inc n' targs.
      deBruijn_inc n inc
        (deBruijn_subst (n + n') (MAP (deBruijn_inc 0 (n + n')) targs) t) =
      deBruijn_subst (n + inc + n') (MAP (deBruijn_inc 0 (n + inc + n')) targs)
        (deBruijn_inc n inc t)) /\
   (!ts n inc n' targs.
      MAP (deBruijn_inc n inc)
        (MAP (deBruijn_subst (n + n') (MAP (deBruijn_inc 0 (n + n')) targs)) ts) =
      MAP (deBruijn_subst (n + inc + n') (MAP (deBruijn_inc 0 (n + inc + n')) targs))
        (MAP (deBruijn_inc n inc) ts))`,
  MATCH_MP_TAC t_INDUCT THEN
  RW[deBruijn_subst_def; deBruijn_inc_def] THEN RW[] THEN
  FS[EL_MAP] THEN TRY ASM_ARITH_TAC THEN
  SUBGOAL_THEN `(a + inc) - (n + inc + n') = a - (n + n') /\
                a - (n + n') < LENGTH (targs:t list)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MAP; deBuijn_inc_lem1] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* split the conditionals of a goal about deBruijn indices, then arithmetic *)
let TPROPSAUX_COND_ARITH_TAC =
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[injectivity "t"] THEN ASM_ARITH_TAC;;

let subst_inc_cancel = prove
 (`(!t ts inc.
      deBruijn_subst 0 ts (deBruijn_inc 0 (inc + LENGTH ts) t) =
      deBruijn_inc 0 inc t) /\
   (!ts' ts inc.
      MAP (deBruijn_subst 0 ts) (MAP (deBruijn_inc 0 (inc + LENGTH ts)) ts') =
      MAP (deBruijn_inc 0 inc) ts')`,
  MATCH_MP_TAC t_INDUCT THEN
  RW[deBruijn_subst_def; deBruijn_inc_def] THEN FS[] THEN
  TPROPSAUX_COND_ARITH_TAC);;

let type_e_subst_lem7 = prove
 (`(!t sk targs targs' (tvs':num) (tvs'':num).
      deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs') (deBruijn_subst 0 targs t) =
      deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs)
        (deBruijn_subst (LENGTH targs + sk)
           (MAP (deBruijn_inc 0 (LENGTH targs + sk)) targs') t)) /\
   (!ts sk targs targs' (tvs':num) (tvs'':num).
      MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) (MAP (deBruijn_subst 0 targs) ts) =
      MAP (deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs))
        (MAP (deBruijn_subst (LENGTH targs + sk)
               (MAP (deBruijn_inc 0 (LENGTH targs + sk)) targs')) ts))`,
  MATCH_MP_TAC t_INDUCT THEN
  RW[deBruijn_subst_def; deBruijn_inc_def] THEN
  FS[EL_MAP; MAP_MAP_o; o_DEF] THEN RW[] THEN
  FS[EL_MAP; deBruijn_subst_def; check_freevars_def] THEN
  RW[] THEN FS[] THEN TRY ASM_ARITH_TAC THEN
  SUBGOAL_THEN `a - LENGTH (targs:t list) - sk = a - (LENGTH targs + sk) /\
                a - (LENGTH targs + sk) < LENGTH (targs':t list)`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MAP] THEN
  SUBGOAL_THEN `LENGTH (targs:t list) + sk =
                sk + LENGTH (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs'))
                                 targs)` SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH_MAP] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[CONJUNCT1 subst_inc_cancel]);;

let deBruijn_subst_id = prove
 (`(!t n. check_freevars n [] t
          ==> deBruijn_subst 0 (MAP Tvar_db (COUNT_LIST n)) t = t) /\
   (!ts n. ALL (check_freevars n []) ts
           ==> MAP (deBruijn_subst 0 (MAP Tvar_db (COUNT_LIST n))) ts = ts)`,
  MATCH_MP_TAC t_INDUCT THEN
  RW[deBruijn_subst_def; LENGTH_COUNT_LIST; EL_MAP; EL_COUNT_LIST;
     check_freevars_def; LENGTH_MAP] THEN
  ASM_MESON_TAC[]);;

let deBruijn_subst_freevars = prove
 (`!skip targs t tvs.
     skip = 0 /\
     ALL (check_freevars tvs []) targs /\
     check_freevars (LENGTH targs) [] t
     ==> check_freevars tvs [] (deBruijn_subst skip targs t)`,
  MATCH_MP_TAC deBruijn_subst_ind THEN
  RW[check_freevars_def; deBruijn_subst_def; EVERY_MAP] THEN
  FS[EVERY_MEM; MEM_EL] THEN TRY ASM_ARITH_TAC THEN ASM_MESON_TAC[]);;

(* ---------- tenv_abbrev_ok, tenv_ctor_ok ---------- *)

let tenv_abbrev_ok_lookup = prove
 (`!tenvT tn tvs t.
     tenv_abbrev_ok tenvT /\ nsLookup tenvT tn = SOME (tvs,t)
     ==> check_freevars 0 tvs t`,
  RW[tenv_abbrev_ok_def] THEN DRULE nsLookup_nsAll THEN
  DISCH_THEN DRULE THEN SIMP[]);;

let check_freevars_type_name_subst = prove
 (`!tvs t dbmax tenvT.
     tenv_abbrev_ok tenvT /\
     check_type_names tenvT t /\
     check_freevars_ast tvs t
     ==> check_freevars dbmax tvs (type_name_subst tenvT t)`,
  MATCH_MP_TAC check_freevars_ast_ind THEN
  RW[type_name_subst_def; LET_DEF; LET_END_DEF] THEN EVERY_CASE_TAC THEN
  GVS[check_type_names_def; check_freevars_def; check_freevars_ast_def;
      EVERY_MAP] THEN
  FS[EVERY_MEM] THEN
  MATCH_MP_TAC check_freevars_subst_single THEN
  ASM_REWRITE_TAC[LENGTH_MAP; EVERY_MAP; EVERY_MEM] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP tenv_abbrev_ok_lookup o
    CONJ (ASSUME `tenv_abbrev_ok (tenvT:tenv_abbrev)`)) THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP check_freevars_add) THEN ARITH_TAC);;

let tenv_abbrev_ok_merge = prove
 (`!tenvT1 tenvT2.
     tenv_abbrev_ok tenvT1 /\ tenv_abbrev_ok tenvT2
     ==> tenv_abbrev_ok (nsAppend tenvT1 tenvT2)`,
  RW[tenv_abbrev_ok_def] THEN IRULE nsAll_nsAppend THEN RW[]);;

let type_ctor_long = prove
 (`!ctMap (mn:M) (id:(M,N)id). type_ctor ctMap (Long mn id) = type_ctor ctMap id`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; type_ctor_def]);;

let tenv_ctor_ok_merge = prove
 (`!tenvC1 tenvC2.
     tenv_ctor_ok tenvC1 /\ tenv_ctor_ok tenvC2
     ==> tenv_ctor_ok (nsAppend tenvC1 tenvC2)`,
  RW[tenv_ctor_ok_def] THEN IRULE nsAll_nsAppend THEN RW[]);;
let _ = cake_add_simps [tenv_ctor_ok_merge];;

let tenv_ctor_ok_lookup = prove
 (`!tenvC cn tvs ts tn.
     tenv_ctor_ok tenvC /\ nsLookup tenvC cn = SOME (tvs,ts,tn)
     ==> ALL (check_freevars 0 tvs) ts`,
  RW[tenv_ctor_ok_def] THEN DRULE nsLookup_nsAll THEN
  DISCH_THEN DRULE THEN SIMP[]);;

(* ---------- tenv_val_exp: deBruijn_subst_tenvE, db_merge ---------- *)

let deBruijn_subst_tenvE_def = cake_def
  `(deBruijn_subst_tenvE (targs:t list) Empty = Empty) /\
   (deBruijn_subst_tenvE targs (Bind_tvar tvs env) =
      Bind_tvar tvs (deBruijn_subst_tenvE targs env)) /\
   (deBruijn_subst_tenvE targs (Bind_name x tvs t env) =
      Bind_name x tvs
        (deBruijn_subst (tvs + num_tvs env)
                        (MAP (deBruijn_inc 0 (tvs + num_tvs env)) targs) t)
        (deBruijn_subst_tenvE targs env))`;;

let db_merge_def = cake_def
  `(db_merge Empty (e:tenv_val_exp) = e) /\
   (db_merge (Bind_tvar tvs e1) e2 = Bind_tvar tvs (db_merge e1 e2)) /\
   (db_merge (Bind_name x tvs t e1) e2 = Bind_name x tvs t (db_merge e1 e2))`;;


let bind_tvar_rewrites = prove
 (`(!tvs e1 e2. db_merge (bind_tvar tvs e1) e2 = bind_tvar tvs (db_merge e1 e2)) /\
   (!tvs e. num_tvs (bind_tvar tvs e) = tvs + num_tvs e) /\
   (!tvs e. num_tvs (Bind_tvar tvs e) = tvs + num_tvs e) /\
   (!tvs n t e. num_tvs (Bind_name n tvs t e) = num_tvs e) /\
   (!(tvs:num) (e:tenv_val_exp). num_tvs Empty = 0) /\
   (!n inc tvs e. tveLookup n inc (bind_tvar tvs e) = tveLookup n (inc + tvs) e) /\
   (!tvs e. tenv_val_exp_ok (bind_tvar tvs e) <=> tenv_val_exp_ok e) /\
   (!targs tvs e.
      deBruijn_subst_tenvE targs (bind_tvar tvs e) =
      bind_tvar tvs (deBruijn_subst_tenvE targs e))`,
  RW[bind_tvar_def; deBruijn_subst_tenvE_def; db_merge_def; num_tvs_def;
     tveLookup_def; tenv_val_exp_ok_def] THEN FS[]);;
let _ = cake_add_simps [bind_tvar_rewrites];;

let bind_tvar0 = prove
 (`!x. bind_tvar 0 x = x`,
  RW[bind_tvar_def]);;
let _ = cake_add_simps [bind_tvar0];;

(* HOL4's Induct_on on a universally quantified variable x of the goal:   *)
(* induction on x with the other quantified variables kept universal in   *)
(* the induction hypothesis (the kit's INDUCT_ON takes a free variable)  *)
let TPROPSAUX_INDUCT_ON (x:term) : tactic =
  fun (asl,w as gl) ->
    let vs,_ = strip_forall w in
    if mem x vs then
      (MAP_EVERY X_GEN_TAC vs THEN
       MAP_EVERY (fun v -> SPEC_TAC(v,v)) (rev (filter (fun v -> v <> x) vs)) THEN
       INDUCT_ON x) gl
    else INDUCT_ON x gl;;

let tveLookup_subst_none = prove
 (`!n inc e.
     tveLookup n inc (deBruijn_subst_tenvE targs e) = NONE <=>
     tveLookup n inc e = NONE`,
  TPROPSAUX_INDUCT_ON `e:tenv_val_exp` THEN
  RW[deBruijn_subst_tenvE_def; tveLookup_def]);;

let tveLookup_db_merge_none = prove
 (`!n inc e1 e2.
     tveLookup n inc (db_merge e1 e2) = NONE <=>
     tveLookup n inc e1 = NONE /\ tveLookup n (num_tvs e1 + inc) e2 = NONE`,
  TPROPSAUX_INDUCT_ON `e1:tenv_val_exp` THEN
  RW[tveLookup_def; db_merge_def; num_tvs_def] THEN
  REWRITE_TAC[ADD_AC; CONJ_ACI]);;
let tveLookup_inc_none = prove
 (`!n inc e. tveLookup n inc e = NONE <=> tveLookup n 0 e = NONE`,
  TPROPSAUX_INDUCT_ON `e:tenv_val_exp` THEN REWRITE_TAC[tveLookup_def] THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[]);;

let tveLookup_freevars = prove
 (`!n tvs tenvE tvs' t.
     tenv_val_exp_ok tenvE /\ num_tvs tenvE = 0 /\
     tveLookup n tvs tenvE = SOME (tvs',t)
     ==> check_freevars tvs' [] t`,
  TPROPSAUX_INDUCT_ON `tenvE:tenv_val_exp` THEN
  RW[tveLookup_def; tenv_val_exp_ok_def] THEN FS[] THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN RW[] THENL
     [GVS[] THEN ASM_SIMP_TAC[nil_deBruijn_inc];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]]);;

(* the kit's RW can leave a goal whose assumptions contain ~T (a split     *)
(* conditional whose guard became T): close such goals as HOL4's rw does  *)
let TPROPSAUX_RW thl =
  RW thl THEN
  TRY (FIRST_ASSUM (fun th ->
    if concl th = `~T` then
      (fun (_,w as g) -> ACCEPT_TAC (CONTR w (MP (NOT_ELIM th) TRUTH)) g)
    else NO_TAC));;

let tveLookup_bvl = prove
 (CASE_TERM `!x tvs tvs' bindings tenvE.
    tveLookup x tvs (bind_var_list tvs' bindings tenvE) =
    match ALOOKUP bindings x with
      SOME t -> SOME (tvs',deBruijn_inc tvs' tvs t)
    | NONE -> tveLookup x tvs tenvE`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  RW[bind_var_list_def] THEN
  SPEC_TAC(`h:mlstring#t`,`h:mlstring#t`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  TPROPSAUX_RW[bind_var_list_def; tveLookup_def]);;

let bind_var_list_append = prove
 (`!n te1 te2 te3.
     bind_var_list n (APPEND te1 te2) te3 =
     bind_var_list n te1 (bind_var_list n te2 te3)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN RW[bind_var_list_def] THEN
  SPEC_TAC(`h:mlstring#t`,`h:mlstring#t`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  RW[bind_var_list_def]);;

let num_tvs_bind_var_list = prove
 (`!tvs env tenvE. num_tvs (bind_var_list tvs env tenvE) = num_tvs tenvE`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN RW[num_tvs_def; bind_var_list_def] THEN
  SPEC_TAC(`h:mlstring#t`,`h:mlstring#t`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  RW[bind_var_list_def; num_tvs_def]);;
let _ = cake_add_simps [num_tvs_bind_var_list];;

let tenv_val_exp_ok_bvl = prove
 (`!tenvE env.
     tenv_val_exp_ok tenvE /\ ALL (check_freevars (num_tvs tenvE) []) (MAP SND env)
     ==> tenv_val_exp_ok (bind_var_list 0 env tenvE)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN RW[tenv_val_exp_ok_def; bind_var_list_def] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`h:mlstring#t`,`h:mlstring#t`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  RW[tenv_val_exp_ok_def; bind_var_list_def] THEN FS[]);;

let tveLookup_subst_some = prove
 (`!n e targs tvs t inc.
     tveLookup n inc e = SOME (tvs,t)
     ==> tveLookup n inc (deBruijn_subst_tenvE targs e) =
         SOME (tvs, deBruijn_subst (tvs + inc + num_tvs e)
                      (MAP (deBruijn_inc 0 (tvs + inc + num_tvs e)) targs) t)`,
  TPROPSAUX_INDUCT_ON `e:tenv_val_exp` THEN
  TPROPSAUX_RW[tveLookup_def; deBruijn_subst_tenvE_def; deBruijn_inc_def;
               num_tvs_def; type_e_subst_lem5] THENL
   [REWRITE_TAC[ADD_AC];
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN TPROPSAUX_RW[] THEN
    ASM_MESON_TAC[]]);;

let num_tvs_db_merge = prove
 (`!e1 e2. num_tvs (db_merge e1 e2) = num_tvs e1 + num_tvs e2`,
  TPROPSAUX_INDUCT_ON `e1:tenv_val_exp` THEN
  RW[num_tvs_def; db_merge_def] THEN ARITH_TAC);;
let _ = cake_add_simps [num_tvs_db_merge];;

let num_tvs_deBruijn_subst_tenvE = prove
 (`!targs tenvE. num_tvs (deBruijn_subst_tenvE targs tenvE) = num_tvs tenvE`,
  TPROPSAUX_INDUCT_ON `tenvE:tenv_val_exp` THEN
  RW[deBruijn_subst_tenvE_def; num_tvs_def]);;
let _ = cake_add_simps [num_tvs_deBruijn_subst_tenvE];;

let tveLookup_inc_some = prove
 (`!n inc e tvs t inc2.
     tveLookup n inc e = SOME (tvs,t)
     ==> ?t'. t = deBruijn_inc tvs inc t' /\
              tveLookup n inc2 e = SOME (tvs, deBruijn_inc tvs inc2 t')`,
  TPROPSAUX_INDUCT_ON `e:tenv_val_exp` THEN
  TPROPSAUX_RW[deBruijn_inc_def; tveLookup_def] THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`n:mlstring`; `inc + a0:num`; `tvs:num`; `t:t`;
                                  `inc2 + a0:num`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `deBruijn_inc tvs a0 t'` THEN
    ASM_REWRITE_TAC[deBruijn_inc_deBruijn_inc];
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN TPROPSAUX_RW[] THEN
    EXISTS_TAC `a2:t` THEN REWRITE_TAC[]]);;

let tveLookup_add_inc = prove
 (`!x inc tenv tvs t inc2.
     tveLookup x inc tenv = SOME (tvs,t)
     ==> tveLookup x (inc2 + inc) tenv = SOME (tvs, deBruijn_inc tvs inc2 t)`,
  TPROPSAUX_INDUCT_ON `tenv:tenv_val_exp` THEN
  TPROPSAUX_RW[tveLookup_def] THENL
   [REWRITE_TAC[GSYM ADD_ASSOC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
    TPROPSAUX_RW[deBruijn_inc_deBruijn_inc]]);;

(* case split on an assumption (if b then x else y) = z *)
let TPROPSAUX_ASM_COND_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_eq (concl th) && is_cond (lhs (concl th)) then MP_TAC th
    else NO_TAC) THEN
  COND_CASES_TAC;;

let tveLookup_freevars_subst = prove
 (`!tenvE targs n t inc.
     ALL (check_freevars (inc + num_tvs tenvE) []) targs /\
     tveLookup n inc tenvE = SOME (LENGTH targs,t) /\
     tenv_val_exp_ok tenvE
     ==> check_freevars (inc + num_tvs tenvE) [] (deBruijn_subst 0 targs t)`,
  TPROPSAUX_INDUCT_ON `tenvE:tenv_val_exp` THEN
  TPROPSAUX_RW[check_freevars_def; num_tvs_def; tveLookup_def;
               tenv_val_exp_ok_def] THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`targs:t list`; `n:mlstring`; `t:t`;
                                  `inc + a0:num`]) THEN
    ASM_REWRITE_TAC[GSYM ADD_ASSOC];
    TPROPSAUX_ASM_COND_TAC THEN TPROPSAUX_RW[] THENL
     [MP_TAC(MATCH_MP check_freevars_subst_inc (ASSUME
        `check_freevars (LENGTH (targs:t list) + num_tvs a3) [] a2`)) THEN
      DISCH_THEN(MP_TAC o SPECL [`num_tvs a3`; `targs:t list`; `inc:num`]) THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]]]);;

let tenv_val_exp_ok_db_merge = prove
 (`!e1 e2. tenv_val_exp_ok (db_merge e1 e2) ==> tenv_val_exp_ok e2`,
  TPROPSAUX_INDUCT_ON `e1:tenv_val_exp` THEN
  TPROPSAUX_RW[tenv_val_exp_ok_def; db_merge_def]);;

(* HOL4 rebinds tveLookup_freevars with this [local] theorem; the exported *)
(* theorem of that name is the one above                                   *)
let TPROPSAUX_tveLookup_freevars = prove
 (`!e n inc t tvs.
     tenv_val_exp_ok e /\ tveLookup n inc e = SOME (tvs,t)
     ==> check_freevars (tvs + inc + num_tvs e) [] t`,
  TPROPSAUX_INDUCT_ON `e:tenv_val_exp` THEN
  TPROPSAUX_RW[tveLookup_def; num_tvs_def; tenv_val_exp_ok_def] THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`n:mlstring`; `inc + a0:num`; `t:t`; `tvs:num`]) THEN
    ASM_REWRITE_TAC[GSYM ADD_ASSOC];
    TPROPSAUX_ASM_COND_TAC THEN TPROPSAUX_RW[] THENL
     [FIRST_ASSUM(MP_TAC o SPECL [`inc:num`; `tvs:num`] o
                  MATCH_MP check_freevars_deBruijn_inc) THEN
      REWRITE_TAC[ADD_AC];
      ASM_MESON_TAC[]]]);;

let tveLookup_no_tvs = prove
 (`!tvs l tenv n t.
     tenv_val_exp_ok tenv /\ num_tvs tenv = 0
     ==> (tveLookup n tvs tenv = SOME (l,t) <=> tveLookup n 0 tenv = SOME (l,t))`,
  TPROPSAUX_INDUCT_ON `tenv:tenv_val_exp` THEN
  REWRITE_TAC[tveLookup_def; num_tvs_def; tenv_val_exp_ok_def; ADD_EQ_0] THEN
  REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[ADD_CLAUSES] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `check_freevars a1 [] a2` ASSUME_TAC THENL
     [ASM_MESON_TAC[ADD_CLAUSES]; ALL_TAC] THEN
    MP_TAC(SPECL [`a1:num`; `tvs:num`; `a2:t`] nil_deBruijn_inc) THEN
    ASM_REWRITE_TAC[CONJUNCT1 deBruijn_inc0] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let deBruijn_subst_E_bvl = prove
 (CASE_TERM `!tenv1 tenv2 tvs.
     deBruijn_subst_tenvE targs (bind_var_list tvs tenv1 tenv2) =
     bind_var_list tvs
       (MAP (\p. match p with
                   (x,t) -> (x, deBruijn_subst (tvs + num_tvs tenv2)
                                  (MAP (deBruijn_inc 0 (tvs + num_tvs tenv2)) targs) t))
            tenv1)
       (deBruijn_subst_tenvE targs tenv2)`,
  LIST_INDUCT_TAC THEN RW[bind_var_list_def] THEN
  SPEC_TAC(`h:mlstring#t`,`h:mlstring#t`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  RW[bind_var_list_def; deBruijn_subst_tenvE_def]);;

let db_merge_bvl = prove
 (`!tenv1 tenv2 tenv3 tvs.
     db_merge (bind_var_list tvs tenv1 tenv2) tenv3 =
     bind_var_list tvs tenv1 (db_merge tenv2 tenv3)`,
  LIST_INDUCT_TAC THEN RW[bind_var_list_def] THEN
  SPEC_TAC(`h:mlstring#t`,`h:mlstring#t`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  RW[bind_var_list_def; db_merge_def]);;

let tveLookup_db_merge_some = prove
 (`!n inc tenvE1 tenvE2 tvs t.
     tveLookup n inc (db_merge tenvE1 tenvE2) = SOME (tvs,t) <=>
     tveLookup n inc tenvE1 = SOME (tvs,t) \/
     (tveLookup n inc tenvE1 = NONE /\
      tveLookup n (num_tvs tenvE1 + inc) tenvE2 = SOME (tvs,t))`,
  TPROPSAUX_INDUCT_ON `tenvE1:tenv_val_exp` THEN
  TPROPSAUX_RW[db_merge_def; tveLookup_def; num_tvs_def] THENL
   [REWRITE_TAC[ADD_AC];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 computes type_op_cases: SIMP_CONV with type_op_def and the case   *)
(* theorems of op, list, t, word_size and id, then DNF_ss and PULL_EXISTS. *)
(* The same computation: the case constants of type_op_def are eliminated *)
(* with their case_eq theorems, then simplified, distributed into a        *)
(* disjunctive normal form, existentials pulled out, simplified again.     *)
let type_op_cases =
  let eqT = prove(`!t. t <=> (t <=> T)`, REWRITE_TAC[]) in
  let eqs = [case_eq "op"; list_case_eq; case_eq "t"; case_eq "word_size";
             pair_case_eq] in
  let th1 = REWRITE_CONV[type_op_def] `type_op op ts t3` in
  let th2 = CONV_RULE (RAND_CONV (REWR_CONV eqT)) th1 in
  let th3 = CONV_RULE (RAND_CONV (REPEATC (CHANGED_CONV
              (GEN_REWRITE_CONV TOP_DEPTH_CONV eqs THENC
               DEPTH_CONV BETA_CONV)))) th2 in
  let th4 = CONV_RULE (RAND_CONV (REWRITE_CONV[])) th3 in
  let th5 = CONV_RULE (RAND_CONV (CAKE_SIMP_CONV [])) th4 in
  let th6 = CONV_RULE (RAND_CONV (REWRITE_CONV
              [LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM; EXISTS_OR_THM;
               LEFT_OR_DISTRIB; RIGHT_OR_DISTRIB; GSYM DISJ_ASSOC;
               GSYM CONJ_ASSOC])) th5 in
  CONV_RULE (RAND_CONV (CAKE_SIMP_CONV [])) th6;;

let type_ps_length = prove
 (`!tvs tenvC ps ts tenv.
     type_ps tvs tenvC ps ts tenv ==> LENGTH ps = LENGTH ts`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ONCE_REWRITE_TAC[type_p_cases] THEN RW[] THEN RW[LENGTH] THEN
  ASM_MESON_TAC[]);;

let type_p_freevars = prove
 (`(!tvs tenvC p t env'.
      type_p tvs tenvC p t env'
      ==> check_freevars tvs [] t /\ ALL (check_freevars tvs []) (MAP SND env')) /\
   (!tvs tenvC ps ts env'.
      type_ps tvs tenvC ps ts env'
      ==> ALL (check_freevars tvs []) ts /\
          ALL (check_freevars tvs []) (MAP SND env'))`,
  MATCH_MP_TAC type_p_ind THEN
  RW[check_freevars_def; bind_tvar_def; bind_var_list_def; ALL_APPEND] THEN
  ASM_MESON_TAC[]);;

let TPROPSAUX_check_freevars_lem = prove
 (`!inc targs tvs tvs' t.
     check_freevars (inc + LENGTH targs) tvs' t /\ ALL (check_freevars tvs tvs') targs
     ==> check_freevars (inc + tvs) tvs'
           (deBruijn_subst inc (MAP (deBruijn_inc 0 inc) targs) t)`,
  MESON_TAC[check_freevars_lem]);;

(* type_subst_deBruijn_subst_list with its lambda eta-reduced *)
let TPROPSAUX_type_subst_deBruijn_subst_list =
  REWRITE_RULE[ETA_AX] type_subst_deBruijn_subst_list;;


let type_p_subst = prove
 (CASE_TERM `(!n tenv p t new_bindings. type_p n tenv p t new_bindings
      ==> !targs' inc tvs targs.
            tenv_abbrev_ok (type_env_t tenv) /\
            tenv_ctor_ok (type_env_c tenv) /\
            n = inc + LENGTH targs /\
            ALL (check_freevars tvs []) targs /\
            targs' = MAP (deBruijn_inc 0 inc) targs
            ==> type_p (inc + tvs) tenv p (deBruijn_subst inc targs' t)
                  (MAP (\xt. match xt with (x,t) -> (x, deBruijn_subst inc targs' t))
                       new_bindings)) /\
   (!n tenv ps ts new_bindings. type_ps n tenv ps ts new_bindings
      ==> !targs' inc targs tvs.
            tenv_abbrev_ok (type_env_t tenv) /\
            tenv_ctor_ok (type_env_c tenv) /\
            n = inc + LENGTH targs /\
            ALL (check_freevars tvs []) targs /\
            targs' = MAP (deBruijn_inc 0 inc) targs
            ==> type_ps (inc + tvs) tenv ps (MAP (deBruijn_subst inc targs') ts)
                  (MAP (\xt. match xt with (x,t) -> (x, deBruijn_subst inc targs' t))
                       new_bindings))`,
  MATCH_MP_TAC type_p_strongind THEN RW[] THEN ONCE_REWRITE_TAC[type_p_cases] THEN
  SIMP[deBruijn_subst_def; OPTION_MAP_DEF] THENL
   [MATCH_MP_TAC TPROPSAUX_check_freevars_lem THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC TPROPSAUX_check_freevars_lem THEN ASM_REWRITE_TAC[];
    CONJ_TAC THENL
     [REWRITE_TAC[EVERY_MAP] THEN
      UNDISCH_TAC `ALL (check_freevars (inc + LENGTH (targs:t list)) []) (ts':t list)` THEN
      MATCH_MP_TAC MONO_ALL THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC TPROPSAUX_check_freevars_lem THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN
       `MAP (type_subst (alist_to_fmap (ZIP tvs'
              (MAP (deBruijn_subst inc (MAP (deBruijn_inc 0 inc) targs)) ts')))) ts =
        MAP (deBruijn_subst inc (MAP (deBruijn_inc 0 inc) targs))
            (MAP (type_subst (alist_to_fmap (ZIP (tvs':mlstring list) ts')))
                 (ts:t list))`
       SUBST1_TAC THENL
       [MATCH_MP_TAC EQ_SYM THEN
        MATCH_MP_TAC TPROPSAUX_type_subst_deBruijn_subst_list THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[tenv_ctor_ok_lookup]];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    SUBGOAL_THEN
     `deBruijn_subst inc (MAP (deBruijn_inc 0 inc) targs)
        (type_name_subst (type_env_t tenv) (t:ast_t)) =
      type_name_subst (type_env_t tenv) t` ASSUME_TAC THENL
     [MATCH_MP_TAC nil_deBruijn_subst THEN
      MATCH_MP_TAC check_freevars_type_name_subst THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`inc:num`; `tvs':num`; `targs:t list`]) THEN
      ASM_REWRITE_TAC[]];
    ASM_MESON_TAC[]]);;

let type_p_bvl = prove
 (`(!tvs tenvC p t bindings. type_p tvs tenvC p t bindings
      ==> !tenv'. tenv_val_exp_ok tenv'
                  ==> tenv_val_exp_ok (bind_var_list tvs bindings tenv')) /\
   (!tvs tenvC ps ts bindings. type_ps tvs tenvC ps ts bindings
      ==> !tenv'. tenv_val_exp_ok tenv'
                  ==> tenv_val_exp_ok (bind_var_list tvs bindings tenv'))`,
  MATCH_MP_TAC type_p_strongind THEN
  RW[bind_var_list_def; tenv_val_exp_ok_def; num_tvs_def; bind_var_list_append] THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP check_freevars_add) THEN ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[tenv_val_exp_ok_def] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP (CONJUNCT1 type_p_freevars)) THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP check_freevars_add) THEN ARITH_TAC]);;

let type_p_tenvV_indep = prove
 (`(!p tvs tenv t bindings tenvV.
      type_p tvs tenv p t bindings =
      type_p tvs (type_env_v_fupd (K tenvV) tenv) p t bindings) /\
   (!ps tvs tenv t bindings tenvV.
      type_ps tvs tenv ps t bindings =
      type_ps tvs (type_env_v_fupd (K tenvV) tenv) ps t bindings)`,
  MATCH_MP_TAC pat_INDUCT THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[type_p_cases] THEN SIMP_NOASM[] THEN
  ASM_MESON_TAC[]);;

let type_es_list_rel = prove
 (`!es ts tenv tenvE. type_es tenv tenvE es ts = ALL2 (type_e tenv tenvE) es ts`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ts:t list` list_CASES) THEN
  ONCE_REWRITE_TAC[type_e_cases] THEN RW[ALL2] THEN ASM_MESON_TAC[]);;


let type_es_length = prove
 (`!tenv tenvE es ts. type_es tenv tenvE es ts ==> LENGTH es = LENGTH ts`,
  REWRITE_TAC[type_es_list_rel] THEN MESON_TAC[LIST_REL_LENGTH]);;

let type_funs_MAP_FST = prove
 (`!funs tenv tenvE env.
     type_funs tenv tenvE funs env ==> MAP FST funs = MAP FST env`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[type_e_cases] THEN RW[] THEN
  RW[MAP] THEN ASM_MESON_TAC[]);;

let tenv_val_exp_ok_bvl_tvs = prove
 (`!funs tenv env tvs bindings tenvE.
     type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs env /\
     tenv_val_exp_ok tenvE
     ==> tenv_val_exp_ok (bind_var_list tvs env tenvE)`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[type_e_cases] THEN
  RW[check_freevars_def] THEN
  RW[check_freevars_def; bind_var_list_def; tenv_val_exp_ok_def] THEN
  ASM_MESON_TAC[]);;

let tenv_val_exp_ok_bvl_funs = prove
 (`!funs env tenv bindings (tenv_val:tenv_val) tenvE.
     type_funs tenv (bind_var_list 0 bindings tenvE) funs env /\
     tenv_val_exp_ok tenvE
     ==> tenv_val_exp_ok (bind_var_list 0 env tenvE)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[type_e_cases] THEN
  RW[check_freevars_def] THEN
  RW[check_freevars_def; bind_var_list_def; tenv_val_exp_ok_def] THEN
  ASM_MESON_TAC[]);;

let TPROPSAUX_tveLookup_freevars_subst0 = prove
 (`!tenvE targs n t.
     tveLookup n 0 tenvE = SOME (LENGTH targs,t)
     ==> ALL (check_freevars (num_tvs tenvE) []) targs /\ tenv_val_exp_ok tenvE
     ==> check_freevars (num_tvs tenvE) [] (deBruijn_subst 0 targs t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tenvE:tenv_val_exp`; `targs:t list`; `n:mlstring`; `t:t`; `0`]
    tveLookup_freevars_subst) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES]);;


let type_e_freevars = prove
 (`(!tenv tenvE e t.
      type_e tenv tenvE e t
      ==> tenv_val_exp_ok tenvE /\ tenv_val_ok (type_env_v tenv)
      ==> check_freevars (num_tvs tenvE) [] t) /\
   (!tenv tenvE es ts.
      type_es tenv tenvE es ts
      ==> tenv_val_exp_ok tenvE /\ tenv_val_ok (type_env_v tenv)
      ==> ALL (check_freevars (num_tvs tenvE) []) ts) /\
   (!tenv tenvE funs env.
      type_funs tenv tenvE funs env
      ==> tenv_val_exp_ok tenvE /\ tenv_val_ok (type_env_v tenv)
      ==> ALL (check_freevars (num_tvs tenvE) []) (MAP SND env))`,
  MATCH_MP_TAC type_e_strongind THEN
  RW[check_freevars_def; num_tvs_def; tenv_val_ok_def; bind_tvar_def;
     bind_var_list_def; opt_bind_name_def] THEN
  FS[check_freevars_def] THENL
   [(* Var *)
    FS[lookup_var_def; lookup_varE_def] THEN EVERY_CASE_TAC THEN FS[] THEN RW[] THEN
    FIRST
     [DRULE nsLookup_nsAll THEN DISCH_THEN DRULE THEN SIMP[] THEN DISCH_TAC THEN
      MATCH_MP_TAC deBruijn_subst_check_freevars2 THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP TPROPSAUX_tveLookup_freevars_subst0) THEN
      ASM_REWRITE_TAC[]];
    (* Fun *)
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[tenv_val_exp_ok_def; ADD_CLAUSES];
    (* Mat *)
    SUBGOAL_THEN `?p0 e0. MEM ((p0:pat),(e0:exp)) pes` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(pes:(pat#exp)list = [])` THEN
      SPEC_TAC(`pes:(pat#exp)list`,`l:(pat#exp)list`) THEN LIST_INDUCT_TAC THEN
      REWRITE_TAC[MEM; NOT_CONS_NIL] THEN MESON_TAC[PAIR];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`p0:pat`; `e0:exp`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC tenv_val_exp_ok_bvl THEN ASM_MESON_TAC[type_p_freevars];
    (* Let *)
    CASES_ON `n:mlstring option` THEN FS[num_tvs_def; tenv_val_exp_ok_def] THEN
    ASM_MESON_TAC[];
    (* Letrec *)
    ASM_MESON_TAC[tenv_val_exp_ok_bvl_funs]]);;

let TPROPSAUX_tveLookup_merge_none = prove
 (`!x tenvE1 tenvE2 targs' a b.
     tveLookup x 0 (db_merge tenvE1 (bind_tvar a tenvE2)) = NONE <=>
     tveLookup x 0 (db_merge (deBruijn_subst_tenvE targs' tenvE1) (bind_tvar b tenvE2)) =
     NONE`,
  REWRITE_TAC[tveLookup_db_merge_none; tveLookup_subst_none; bind_tvar_rewrites;
              num_tvs_deBruijn_subst_tenvE] THEN
  MESON_TAC[tveLookup_inc_none]);;

let TPROPSAUX_type_e_subst_var_local = prove
 (`!x tenvE1 tenvE2 targs t targs' tvs'.
     num_tvs tenvE2 = 0 /\
     tenv_val_exp_ok (db_merge tenvE1 (bind_tvar (LENGTH targs') tenvE2)) /\
     tveLookup x 0 (db_merge tenvE1 (bind_tvar (LENGTH targs') tenvE2)) =
       SOME (LENGTH targs,t)
     ==> ?t''. deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs')
                 (deBruijn_subst 0 targs t) =
               deBruijn_subst 0
                 (MAP (deBruijn_subst (num_tvs tenvE1)
                        (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs')) targs) t'' /\
               tveLookup x 0 (db_merge (deBruijn_subst_tenvE targs' tenvE1)
                                       (bind_tvar tvs' tenvE2)) =
                 SOME (LENGTH targs,t'')`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [tveLookup_db_merge_some]) THEN
  STRIP_TAC THENL
   [EXISTS_TAC `deBruijn_subst (LENGTH (targs:t list) + num_tvs tenvE1)
                  (MAP (deBruijn_inc 0 (LENGTH targs + num_tvs tenvE1)) targs') t` THEN
    REWRITE_TAC[CONJUNCT1 type_e_subst_lem7; tveLookup_db_merge_some] THEN
    DISJ1_TAC THEN
    MP_TAC(SPECL [`x:mlstring`; `tenvE1:tenv_val_exp`; `targs':t list`;
                  `LENGTH (targs:t list)`; `t:t`; `0`] tveLookup_subst_some) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES];
    SUBGOAL_THEN `tenv_val_exp_ok tenvE2` ASSUME_TAC THENL
     [ASM_MESON_TAC[tenv_val_exp_ok_db_merge; bind_tvar_rewrites]; ALL_TAC] THEN
    SUBGOAL_THEN `!inc. tveLookup x inc tenvE2 = SOME (LENGTH (targs:t list),t)`
      ASSUME_TAC THENL
     [UNDISCH_TAC `tveLookup x (num_tvs tenvE1 + 0)
                      (bind_tvar (LENGTH (targs':t list)) tenvE2) =
                    SOME (LENGTH (targs:t list),t)` THEN
      REWRITE_TAC[bind_tvar_rewrites; ADD_CLAUSES] THEN
      ASM_MESON_TAC[tveLookup_no_tvs];
      ALL_TAC] THEN
    SUBGOAL_THEN `check_freevars (LENGTH (targs:t list)) [] t` ASSUME_TAC THENL
     [ASM_MESON_TAC[tveLookup_freevars]; ALL_TAC] THEN
    EXISTS_TAC `t:t` THEN CONJ_TAC THENL
     [MATCH_MP_TAC (CONJUNCT1 deBruijn_subst2) THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[tveLookup_db_merge_some; tveLookup_subst_none;
                      bind_tvar_rewrites]]]);;

let TPROPSAUX_type_e_subst_var = prove
 (`!tenv tenvE1 tenvE2 n targs t targs' tvs'.
     num_tvs tenvE2 = 0 /\
     tenv_val_ok (type_env_v tenv) /\
     tenv_val_exp_ok (db_merge tenvE1 (bind_tvar (LENGTH targs') tenvE2)) /\
     ALL (check_freevars tvs' []) targs' /\
     ALL (check_freevars (num_tvs tenvE1 + LENGTH targs') []) targs /\
     lookup_var n (db_merge tenvE1 (bind_tvar (LENGTH targs') tenvE2)) tenv =
       SOME (LENGTH targs,t)
     ==> ?t'' targs''.
           deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs')
             (deBruijn_subst 0 targs t) = deBruijn_subst 0 targs'' t'' /\
           ALL (check_freevars (num_tvs tenvE1 + tvs') []) targs'' /\
           lookup_var n
             (db_merge (deBruijn_subst_tenvE targs' tenvE1) (bind_tvar tvs' tenvE2))
             tenv = SOME (LENGTH targs'',t'')`,
  let GLOBAL_TAC =
    DISCH_TAC THEN EXISTS_TAC `t:t` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC (CONJUNCT1 deBruijn_subst2) THEN
    DRULE nsLookup_nsAll THEN DISCH_THEN DRULE THEN SIMP[] in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ALL (check_freevars (num_tvs tenvE1 + tvs') [])
     (MAP (deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs'))
          (targs:t list))` ASSUME_TAC THENL
   [REWRITE_TAC[EVERY_MAP] THEN
    UNDISCH_TAC `ALL (check_freevars (num_tvs tenvE1 + LENGTH (targs':t list)) [])
                     (targs:t list)` THEN
    MATCH_MP_TAC MONO_ALL THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC TPROPSAUX_check_freevars_lem THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  EXISTS_TAC `MAP (deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs'))
                  (targs:t list)` THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN
  UNDISCH_TAC `lookup_var n (db_merge tenvE1 (bind_tvar (LENGTH (targs':t list)) tenvE2)) tenv =
               SOME (LENGTH (targs:t list),t)` THEN
  REWRITE_TAC[lookup_var_def; lookup_varE_def] THEN
  CASES_ON `n:(mlstring,mlstring)id` THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[tenv_val_ok_def]) THENL
   [ASM_CASES_TAC `tveLookup a 0 (db_merge tenvE1 (bind_tvar (LENGTH (targs':t list)) tenvE2)) =
                   NONE` THENL
     [SUBGOAL_THEN `tveLookup a 0 (db_merge (deBruijn_subst_tenvE targs' tenvE1)
                                            (bind_tvar tvs' tenvE2)) = NONE`
        ASSUME_TAC THENL [ASM_MESON_TAC[TPROPSAUX_tveLookup_merge_none]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN GLOBAL_TAC;
      FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[cases "option"]
        `~(x:(num#t)option = NONE) ==> ?y. x = SOME y`)) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[option_INJ] THEN DISCH_THEN SUBST_ALL_TAC THEN
      MP_TAC(SPECL [`a:mlstring`; `tenvE1:tenv_val_exp`; `tenvE2:tenv_val_exp`;
                    `targs:t list`; `t:t`; `targs':t list`; `tvs':num`]
        TPROPSAUX_type_e_subst_var_local) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `t'':t` THEN
      ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]];
    GLOBAL_TAC]);;

let TPROPSAUX_deBruijn_subst_t_of = prove
 (`!sk targs ty. deBruijn_subst sk targs (t_of ty) = t_of ty`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC prim_type_INDUCT THEN REPEAT CONJ_TAC THEN
  TRY (MATCH_MP_TAC word_size_INDUCT) THEN
  REWRITE_TAC[t_of_def; typeSystem_Tbool_def; typeSystem_Tint_def; typeSystem_Tchar_def;
              typeSystem_Tstring_def; typeSystem_Tword8_def; typeSystem_Tword64_def;
              typeSystem_Tdouble_def; deBruijn_subst_def; MAP]);;

let TPROPSAUX_type_op_subst = prove
 (`!op ts t sk targs.
     type_op op ts t
     ==> type_op op (MAP (deBruijn_subst sk targs) ts) (deBruijn_subst sk targs t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[type_op_cases] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN SIMP[MAP; deBruijn_subst_def; TPROPSAUX_deBruijn_subst_t_of] THEN
  SUBGOAL_THEN `MAP (deBruijn_subst sk targs) ts = ts`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC MAP_EQ_DEGEN THEN
  UNDISCH_TAC `ALL (\arg. arg = t_of a1) (ts:t list)` THEN
  MATCH_MP_TAC MONO_ALL THEN SIMP[TPROPSAUX_deBruijn_subst_t_of]);;


(* MP_TAC the instance at tms of the assumption !x1 .. xn. A ==> c ...    *)
(* whose conclusion has the head constant c (an induction hypothesis)    *)
let TPROPSAUX_IH_TAC (c:term) (tms:term list) : tactic =
  FIRST_X_ASSUM(fun th ->
    let _,b = strip_forall (concl th) in
    if is_imp b && fst(strip_comb(rand b)) = c then MP_TAC(SPECL tms th)
    else NO_TAC);;

(* rewrite the assumptions with num_tvs tenvE2 = 0 (type_e_subst) *)
let TPROPSAUX_NTVS0_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `num_tvs tenvE2 = 0` then
      RULE_ASSUM_TAC(fun th' -> if concl th' = concl th then th'
                                else REWRITE_RULE[th; ADD_CLAUSES] th')
    else NO_TAC);;

(* HOL4's statement has tenvE2 free (not quantified) *)
let type_e_subst = prove
 (CASE_TERM
 `(!tenv tenvE e t. type_e tenv tenvE e t
     ==> !tenvE1 targs tvs targs'.
           num_tvs tenvE2 = 0 /\
           tenv_abbrev_ok (type_env_t tenv) /\
           tenv_ctor_ok (type_env_c tenv) /\
           tenv_val_ok (type_env_v tenv) /\
           tenv_val_exp_ok tenvE /\
           ALL (check_freevars tvs []) targs /\
           tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2) /\
           targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs
           ==> type_e tenv
                 (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
                 e (deBruijn_subst (num_tvs tenvE1) targs' t)) /\
  (!tenv tenvE es ts. type_es tenv tenvE es ts
     ==> !tenvE1 targs tvs targs'.
           num_tvs tenvE2 = 0 /\
           tenv_abbrev_ok (type_env_t tenv) /\
           tenv_ctor_ok (type_env_c tenv) /\
           tenv_val_ok (type_env_v tenv) /\
           tenv_val_exp_ok tenvE /\
           ALL (check_freevars tvs []) targs /\
           tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2) /\
           targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs
           ==> type_es tenv
                 (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
                 es (MAP (deBruijn_subst (num_tvs tenvE1) targs') ts)) /\
  (!tenv tenvE funs env. type_funs tenv tenvE funs env
     ==> !tenvE1 targs tvs targs'.
           num_tvs tenvE2 = 0 /\
           tenv_abbrev_ok (type_env_t tenv) /\
           tenv_ctor_ok (type_env_c tenv) /\
           tenv_val_ok (type_env_v tenv) /\
           tenv_val_exp_ok tenvE /\
           ALL (check_freevars tvs []) targs /\
           tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2) /\
           targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs
           ==> type_funs tenv
                 (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
                 funs
                 (MAP (\xt. match xt with
                              (x,t) -> (x, deBruijn_subst (num_tvs tenvE1) targs' t))
                      env))`,
  let PES_TAC p e =
    FIRST_X_ASSUM(MP_TAC o SPECL [p; e]) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC (CASE_TERM `MAP (\xt. match xt with (x,t) -> (x, deBruijn_subst (num_tvs tenvE1)
        (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs) t)) (bindings:(mlstring#t)list)`) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPECL [`MAP (deBruijn_inc 0 (num_tvs tenvE1)) (targs:t list)`;
         `num_tvs tenvE1`; `tvs:num`; `targs:t list`] o MATCH_MP (CONJUNCT1 type_p_subst)) THEN
      ASM_REWRITE_TAC[deBruijn_subst_def; MAP];
      FIRST_X_ASSUM(MP_TAC o SPECL [`bind_var_list 0 bindings tenvE1`; `targs:t list`;
                                    `tvs:num`]) THEN
      REWRITE_TAC[num_tvs_bind_var_list; deBruijn_subst_E_bvl; db_merge_bvl; ADD_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC tenv_val_exp_ok_bvl THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP (CONJUNCT1 type_p_freevars)) THEN
      ASM_SIMP_TAC[num_tvs_db_merge; bind_tvar_rewrites; ADD_CLAUSES]] in
  let BIND_NAME_TAC n t1 =
    TPROPSAUX_IH_TAC `type_e` [mk_comb(mk_comb(mk_comb(mk_comb(`Bind_name`,n),`0`),t1),
                                       `tenvE1:tenv_val_exp`);
                               `targs:t list`; `tvs:num`] THEN
    REWRITE_TAC[num_tvs_def; deBruijn_subst_tenvE_def; db_merge_def; ADD_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[tenv_val_exp_ok_def; num_tvs_db_merge; bind_tvar_rewrites;
                    ADD_CLAUSES] in
  MATCH_MP_TAC type_e_strongind THEN RW[] THEN ONCE_REWRITE_TAC[type_e_cases] THEN
  RW[deBruijn_subst_def; deBruijn_subst_tenvE_def; opt_bind_name_def; num_tvs_def;
     OPTION_MAP_DEF; num_tvs_db_merge; num_tvs_deBruijn_subst_tenvE] THEN
  FS[deBruijn_subst_def; deBruijn_subst_tenvE_def; opt_bind_name_def; num_tvs_def;
     OPTION_MAP_DEF; num_tvs_db_merge; num_tvs_deBruijn_subst_tenvE; tenv_val_ok_def] THEN
  TPROPSAUX_NTVS0_TAC THENL
   [(* Raise *)
    MATCH_MP_TAC TPROPSAUX_check_freevars_lem THEN ASM_REWRITE_TAC[];
    (* Handle *)
    PES_TAC `p:pat` `e':exp`;
    (* Con (SOME cn): the type arguments *)
    REWRITE_TAC[EVERY_MAP] THEN
    UNDISCH_TAC `ALL (check_freevars (num_tvs tenvE1 + LENGTH (targs:t list)) [])
                     (ts':t list)` THEN
    MATCH_MP_TAC MONO_ALL THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC TPROPSAUX_check_freevars_lem THEN ASM_REWRITE_TAC[];
    (* Con (SOME cn): the arguments *)
    SUBGOAL_THEN `MAP (type_subst (alist_to_fmap (ZIP tvs (MAP (deBruijn_subst (num_tvs tenvE1)
                     (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs)) ts')))) ts =
                  MAP (deBruijn_subst (num_tvs (tenvE1:tenv_val_exp))
                     (MAP (deBruijn_inc 0 (num_tvs tenvE1)) (targs:t list)))
                    (MAP (type_subst (alist_to_fmap (ZIP (tvs:mlstring list) (ts':t list))))
                         (ts:t list))`
      SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_SYM THEN MATCH_MP_TAC TPROPSAUX_type_subst_deBruijn_subst_list THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_MESON_TAC[tenv_ctor_ok_lookup]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* Var *)
    MATCH_MP_TAC TPROPSAUX_type_e_subst_var THEN ASM_REWRITE_TAC[tenv_val_ok_def];
    (* Fun: the argument type *)
    MATCH_MP_TAC TPROPSAUX_check_freevars_lem THEN ASM_REWRITE_TAC[];
    (* Fun: the body *)
    BIND_NAME_TAC `n:mlstring` `t1:t`;
    (* App *)
    EXISTS_TAC `MAP (deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs))
                    (ts:t list)` THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC TPROPSAUX_type_op_subst THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC TPROPSAUX_check_freevars_lem THEN ASM_REWRITE_TAC[]];
    (* Mat *)
    EXISTS_TAC `deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs)
                  (t1:t)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`p0:pat`; `e0:exp`] THEN DISCH_TAC THEN
      PES_TAC `p0:pat` `e0:exp`];
    (* Let *)
    EXISTS_TAC `deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs)
                  (t1:t)` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `check_freevars (num_tvs tenvE1 + LENGTH (targs:t list)) [] t1`
      ASSUME_TAC THENL
     [MP_TAC(SPECL [`tenv:type_env`;
                    `db_merge tenvE1 (bind_tvar (LENGTH (targs:t list)) tenvE2)`;
                    `e1:exp`; `t1:t`] (CONJUNCT1 type_e_freevars)) THEN
      ASM_REWRITE_TAC[tenv_val_ok_def; num_tvs_db_merge; bind_tvar_rewrites; ADD_CLAUSES];
      ALL_TAC] THEN
    CASES_ON `n:mlstring option` THEN CASE_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      BIND_NAME_TAC `a:mlstring` `t1:t`];
    (* Letrec *)
    EXISTS_TAC (CASE_TERM `MAP (\xt. match xt with (x,t) -> (x, deBruijn_subst (num_tvs tenvE1)
        (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs) t)) (bindings:(mlstring#t)list)`) THEN
    SUBGOAL_THEN `tenv_val_exp_ok (bind_var_list 0 bindings
                    (db_merge tenvE1 (bind_tvar (LENGTH (targs:t list)) tenvE2)))`
      ASSUME_TAC THENL
     [ASM_MESON_TAC[tenv_val_exp_ok_bvl_funs]; ALL_TAC] THEN
    REPEAT (FIRST_X_ASSUM(MP_TAC o SPECL [`bind_var_list 0 bindings tenvE1`; `targs:t list`;
                                          `tvs:num`])) THEN
    REWRITE_TAC[num_tvs_bind_var_list; deBruijn_subst_E_bvl; db_merge_bvl; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[];
    (* Tannot: the type *)
    MATCH_MP_TAC nil_deBruijn_subst THEN MATCH_MP_TAC check_freevars_type_name_subst THEN
    ASM_REWRITE_TAC[];
    (* Tannot: the expression *)
    FIRST_X_ASSUM(MP_TAC o SPECL [`tenvE1:tenv_val_exp`; `targs:t list`; `tvs:num`]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `deBruijn_subst (num_tvs tenvE1) (MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs)
                    (type_name_subst (type_env_t tenv) (t:ast_t)) =
                  type_name_subst (type_env_t tenv) t` SUBST1_TAC THENL
     [MATCH_MP_TAC nil_deBruijn_subst THEN MATCH_MP_TAC check_freevars_type_name_subst THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[]];
    (* type_funs: the function type *)
    MP_TAC(SPECL [`num_tvs (tenvE1:tenv_val_exp)`; `targs:t list`; `tvs:num`;
                  `[]:mlstring list`; `Tapp [t1; t2] Tfn_num`]
      TPROPSAUX_check_freevars_lem) THEN
    ASM_REWRITE_TAC[deBruijn_subst_def; MAP];
    (* type_funs: the body *)
    RULE_ASSUM_TAC(REWRITE_RULE[check_freevars_def; ALL]) THEN
    BIND_NAME_TAC `n:mlstring` `t1:t`;
    (* type_funs: the name is new *)
    UNDISCH_TAC `ALOOKUP (bindings:(mlstring#t)list) fn = NONE` THEN
    REWRITE_TAC[ALOOKUP_FAILS; MEM_MAP; EXISTS_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]]);;

let type_funs_Tfn = prove
 (`!tenv tenvE funs bindings (tvs:num) t n.
     type_funs tenv tenvE funs bindings /\ ALOOKUP bindings n = SOME t
     ==> ?t1 t2. t = Tfn t1 t2 /\ check_freevars (num_tvs tenvE) [] (Tfn t1 t2)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[type_e_cases] THEN RW[] THEN FS[] THEN
  TPROPSAUX_ASM_COND_TAC THEN TPROPSAUX_RW[] THEN ASM_MESON_TAC[]);;

let type_funs_lookup = prove
 (`!fn tenvE funs bindings n e tenv.
     MEM (fn,n,e) funs /\ type_funs tenv tenvE funs bindings
     ==> ?t. ALOOKUP bindings fn = SOME t`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[type_e_cases] THEN RW[MEM] THEN FS[] THEN
  TRY COND_CASES_TAC THEN ASM_MESON_TAC[option_DISTINCT]);;

let type_funs_find_recfun = prove
 (`!fn (env:A) funs bindings (e:exp) tenv tenvE t.
     ALOOKUP bindings fn = SOME t /\ type_funs tenv tenvE funs bindings
     ==> ?n e. find_recfun fn funs = SOME (n,e)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[type_e_cases] THEN RW[] THEN FS[] THEN
  ONCE_REWRITE_TAC[find_recfun_def] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ; PAIR_EQ] THEN
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* the rules of type_funs as equations (HOL4 uses simp [Once type_e_cases]) *)
let TPROPSAUX_type_funs_cases = prove
 (`(!tenv tenvE bindings. type_funs tenv tenvE [] bindings <=> bindings = []) /\
   (!tenv tenvE fn n e funs bindings.
      type_funs tenv tenvE (CONS (fn,n,e) funs) bindings <=>
      ?t1 t2 bindings'.
        bindings = CONS (fn,Tfn t1 t2) bindings' /\
        check_freevars (num_tvs tenvE) [] (Tfn t1 t2) /\
        type_e tenv (Bind_name n 0 t1 tenvE) e t2 /\
        type_funs tenv tenvE funs bindings' /\
        ALOOKUP bindings' fn = NONE)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [type_e_cases] THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11; PAIR_EQ] THEN MESON_TAC[]);;

let type_recfun_lookup = prove
 (`!fn funs n e tenv tenvE bindings (tvs:num) t1 t2.
     find_recfun fn funs = SOME (n,e) /\
     type_funs tenv tenvE funs bindings /\
     ALOOKUP bindings fn = SOME (Tfn t1 t2)
     ==> type_e tenv (Bind_name n 0 t1 tenvE) e t2 /\
         check_freevars (num_tvs tenvE) [] (Tfn t1 t2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[find_recfun_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  SPEC_TAC(`h:mlstring#mlstring#exp`,`h:mlstring#mlstring#exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[TPROPSAUX_type_funs_cases] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
  GVS[ALOOKUP_THM] THEN ASM_MESON_TAC[]);;

let type_funs_distinct = prove
 (CASE_TERM `!tenv tenvE funs bindings.
     type_funs tenv tenvE funs bindings
     ==> ALL_DISTINCT (MAP (\p. match p with (x,y,z) -> x) funs)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ALL_DISTINCT] THEN
  SPEC_TAC(`h:mlstring#mlstring#exp`,`h:mlstring#mlstring#exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[TPROPSAUX_type_funs_cases] THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MEM_MAP]) THEN
    REWRITE_TAC[EXISTS_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p1:mlstring`; `tenvE:tenv_val_exp`; `t:(mlstring#mlstring#exp)list`;
                  `bindings':(mlstring#t)list`] type_funs_lookup) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[option_DISTINCT];
    ASM_MESON_TAC[]]);;

let type_funs_tenv_exp_ok = prove
 (`!funs env tenv tenvE tvs bindings.
     num_tvs tenvE = 0 /\
     type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs env
     ==> tenv_val_exp_ok (bind_var_list tvs env Empty)`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  TRY (SPEC_TAC(`h:mlstring#mlstring#exp`,`h:mlstring#mlstring#exp`) THEN
       REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC) THEN
  REWRITE_TAC[TPROPSAUX_type_funs_cases] THEN
  RW[bind_var_list_def; tenv_val_exp_ok_def] THEN
  FS[ADD_CLAUSES] THEN ASM_MESON_TAC[]);;

(* HOL4 has x and t1 free; targs' is not used *)
let type_e_subst_lem = prove
 (`!tenv tenvE e t targs tvs (targs':t list).
     type_e tenv (Bind_name x 0 t1 (bind_tvar (LENGTH targs) tenvE)) e t /\
     num_tvs tenvE = 0 /\
     tenv_abbrev_ok (type_env_t tenv) /\
     tenv_ctor_ok (type_env_c tenv) /\
     tenv_val_ok (type_env_v tenv) /\
     tenv_val_exp_ok (bind_tvar (LENGTH targs) tenvE) /\
     ALL (check_freevars tvs []) targs /\
     check_freevars (LENGTH targs) [] t1
     ==> type_e tenv (Bind_name x 0 (deBruijn_subst 0 targs t1) (bind_tvar tvs tenvE)) e
                 (deBruijn_subst 0 targs t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`tenv:type_env`;
                `Bind_name x 0 t1 (bind_tvar (LENGTH (targs:t list)) tenvE)`;
                `e:exp`; `t:t`] (CONJUNCT1 (INST [`tenvE:tenv_val_exp`,`tenvE2:tenv_val_exp`]
                                            type_e_subst))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`Bind_name x 0 t1 Empty`; `targs:t list`; `tvs:num`;
                             `MAP (deBruijn_inc 0 0) (targs:t list)`]) THEN
  ASM_REWRITE_TAC[db_merge_def; deBruijn_subst_tenvE_def; num_tvs_def; ADD_CLAUSES;
                  deBruijn_inc0; tenv_val_exp_ok_def] THEN
  ASM_SIMP_TAC[bind_tvar_rewrites; ADD_CLAUSES]);;

let type_def_to_ctMap_def = cake_def
  `(type_def_to_ctMap (tenvT:tenv_abbrev) (next_stamp:num)
      ([]:(tvarN list # typeN # (conN # ast_t list) list) list) ([]:num list) =
      []:(stamp # (tvarN list # t list # num)) list) /\
   (type_def_to_ctMap tenvT next_stamp (CONS (tvs,tn,ctors) tds) (CONS id ids) =
      APPEND (type_def_to_ctMap tenvT (next_stamp + 1) tds ids)
        (REVERSE
          (MAP (\p. match p with
                      (cn,ts) -> (TypeStamp cn next_stamp,
                                  (tvs, MAP (type_name_subst tenvT) ts, id)))
               ctors)))`;;

let type_def_to_ctMap_ind = cake_ind "type_def_to_ctMap";;

let mem_type_def_to_ctMap = prove
 (`!tenvT next tds ids stamp x.
     MEM (stamp,x) (type_def_to_ctMap tenvT next tds ids) /\ LENGTH tds = LENGTH ids
     ==> ?cn i. stamp = TypeStamp cn i /\ next <= i /\ i < next + LENGTH tds`,
  MATCH_MP_TAC type_def_to_ctMap_ind THEN
  RW[type_def_to_ctMap_def; MEM_APPEND; MEM_REVERSE] THEN FS[] THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`stamp:stamp`; `x:mlstring list#t list#num`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`cn:mlstring`; `i:num`] THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MEM_MAP]) THEN
    REWRITE_TAC[EXISTS_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`p1:mlstring`; `next_stamp:num`] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let o_f_FRANGE2 = prove
 (`(?x:B. (y:C) = f x /\ x IN FRANGE (g:(A,B)fmap)) ==> y IN FRANGE (f o_f g)`,
  REWRITE_TAC[IN_FRANGE_FLOOKUP; FLOOKUP_o_f] THEN STRIP_TAC THEN
  EXISTS_TAC `k:A` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let TPROPSAUX_ti_IN_FRANGE = prove
 (`!(m:ctMap) k tvs ts ti.
     FLOOKUP m k = SOME (tvs,ts,ti) ==> ti IN FRANGE ((SND o SND) o_f m)`,
  REWRITE_TAC[IN_FRANGE_FLOOKUP; FLOOKUP_o_f] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `k:stamp` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[o_THM]);;

let ctMap_ok_merge_imp = prove
 (`!ctMap1 ctMap2:ctMap.
     DISJOINT (FRANGE ((SND o SND) o_f ctMap1)) (FRANGE ((SND o SND) o_f ctMap2)) /\
     ctMap_ok ctMap1 /\ ctMap_ok ctMap2
     ==> ctMap_ok (FUNION ctMap1 ctMap2)`,
  REWRITE_TAC[ctMap_ok_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC fevery_funion THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FLOOKUP_FUNION] THEN REPEAT GEN_TAC THEN
    CASES_ON `FLOOKUP (ctMap1:ctMap) (ExnStamp ex)` THEN CASE_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[FLOOKUP_FUNION] THEN REPEAT GEN_TAC THEN
    CASES_ON `FLOOKUP (ctMap1:ctMap) (TypeStamp cn x)` THEN CASE_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[FLOOKUP_FUNION] THEN REPEAT GEN_TAC THEN
    CASES_ON `FLOOKUP (ctMap1:ctMap) stamp1` THEN
    CASES_ON `FLOOKUP (ctMap1:ctMap) stamp2` THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_INJ] THEN STRIP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC; ALL_TAC; ASM_MESON_TAC[]] THEN
    (* the mixed cases: ti is in the range of both maps *)
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_DISJOINT]) THEN
    ASM_MESON_TAC[TPROPSAUX_ti_IN_FRANGE]]);;

let ctMap_ok_lookup = prove
 (`!ctMap (cn:mlstring) tvs ts ti tn.
     ctMap_ok ctMap /\ FLOOKUP ctMap tn = SOME (tvs,ts,ti)
     ==> ALL (check_freevars 0 tvs) ts`,
  RW[ctMap_ok_def; FEVERY_ALL_FLOOKUP] THEN RES_TAC THEN FS[]);;

(* case split on an assumption (case x of ...) = v, by cases on x *)
let TPROPSAUX_ASM_CASE_TAC : tactic =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_case_app (lhs c) then
      let _,x,_ = dest_case_app (lhs c) in MP_TAC th THEN CASES_ON x
    else NO_TAC) THEN
  CASE_REWRITE_TAC[];;

let type_def_to_ctMap_mem = prove
 (`!tenvT next tds tids.
     ALOOKUP (type_def_to_ctMap tenvT next tds tids) k = SOME x /\
     LENGTH tds = LENGTH tids
     ==> MEM (SND (SND x)) tids`,
  MATCH_MP_TAC type_def_to_ctMap_ind THEN
  RW[type_def_to_ctMap_def; ALOOKUP_APPEND] THEN FS[] THEN
  TPROPSAUX_ASM_CASE_TAC THEN RW[] THEN FS[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
  REWRITE_TAC[MEM_REVERSE; MEM_MAP; EXISTS_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let fupdate2_union = prove
 (`!(m:(A,B)fmap) a1 a2. m |++ a1 |++ a2 = FUNION (FEMPTY |++ a2) (m |++ a1)`,
  REWRITE_TAC[FLOOKUP_EXT; FUN_EQ_THM; FLOOKUP_FUNION; flookup_fupdate_list;
              FLOOKUP_EMPTY] THEN
  REPEAT GEN_TAC THEN CASES_ON `ALOOKUP (REVERSE (a2:(A#B)list)) x` THEN
  CASE_REWRITE_TAC[]);;

(* the constructor map of one type definition *)
let TPROPSAUX_ctMap_ok_ctors = prove
 (CASE_TERM `!(tenvT:tenv_abbrev) next tvs ctors (id:num).
     (!cn ts. MEM (cn,ts) ctors
              ==> ALL (check_freevars_ast tvs) ts /\ ALL (check_type_names tenvT) ts) /\
     tenv_abbrev_ok tenvT /\ ~MEM id prim_type_nums
     ==> ctMap_ok (FEMPTY |++
           MAP (\p. match p with
                      (cn,ts) -> (TypeStamp cn next,
                                  (tvs, MAP (type_name_subst tenvT) ts, id))) ctors)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ctMap_ok_def; FEVERY_ALL_FLOOKUP; flookup_fupdate_list; FLOOKUP_EMPTY;
              SPTAUX_optcase_lemma] THEN
  SUBGOAL_THEN (CASE_TERM
   `!k v. ALOOKUP (REVERSE (MAP (\p. match p with
                      (cn,ts) -> (TypeStamp cn next,
                                  (tvs, MAP (type_name_subst tenvT) ts, (id:num))))
                      (ctors:(mlstring#ast_t list)list))) k =
          SOME v
          ==> ?cn ts. MEM (cn,ts) ctors /\ k = TypeStamp cn next /\
                      v = (tvs:mlstring list, MAP (type_name_subst (tenvT:tenv_abbrev)) ts, id)`)
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
    REWRITE_TAC[MEM_REVERSE; MEM_MAP; EXISTS_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [DISCH_THEN(fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[EVERY_MAP] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`cn:mlstring`; `ts:ast_t list`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC check_freevars_type_name_subst THEN ASM_REWRITE_TAC[] THEN
    FS[EVERY_MEM] THEN ASM_MESON_TAC[];
    DISCH_THEN(fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
    FS[distinctness "stamp"];
    DISCH_THEN(fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THEN
    FS[PAIR_EQ];
    STRIP_TAC THEN
    REPEAT (FIRST_X_ASSUM(fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th))) THEN
    ASM_REWRITE_TAC[same_type_def]]);;

let TPROPSAUX_FRANGE_fupdate_list = prove
 (`!(l:(stamp#(mlstring list#t list#num))list) ti.
     ti IN FRANGE ((SND o SND) o_f (FEMPTY |++ l))
     ==> ?k v. ALOOKUP (REVERSE l) k = SOME v /\ ti = SND (SND v)`,
  REWRITE_TAC[IN_FRANGE_FLOOKUP; FLOOKUP_o_f; flookup_fupdate_list; FLOOKUP_EMPTY;
              SPTAUX_optcase_lemma] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `k:stamp` MP_TAC) THEN
  CASES_ON `ALOOKUP (REVERSE (l:(stamp#(mlstring list#t list#num))list)) k` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_INJ; o_THM] THEN ASM_MESON_TAC[]);;

let TPROPSAUX_FRANGE_ctors = prove
 (CASE_TERM `!next (tvs:mlstring list) (ctors:(mlstring#ast_t list)list) (id:num)
       (tenvT:tenv_abbrev) ti.
     ti IN FRANGE ((SND o SND) o_f
       (FEMPTY |++ MAP (\p. match p with
                              (cn,ts) -> (TypeStamp cn next,
                                          (tvs, MAP (type_name_subst tenvT) ts, id))) ctors))
     ==> ti = id`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP TPROPSAUX_FRANGE_fupdate_list) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
  ASM_REWRITE_TAC[MEM_REVERSE; MEM_MAP; EXISTS_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let TPROPSAUX_FRANGE_type_def_to_ctMap = prove
 (`!tenvT next tds tids ti.
     LENGTH tds = LENGTH tids /\
     ti IN FRANGE ((SND o SND) o_f
                   (FEMPTY |++ REVERSE (type_def_to_ctMap tenvT next tds tids)))
     ==> MEM ti tids`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP TPROPSAUX_FRANGE_fupdate_list) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REVERSE_REVERSE]) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`tenvT:tenv_abbrev`; `next:num`;
                 `tds:(mlstring list#mlstring#(mlstring#ast_t list)list)list`;
                 `tids:num list`]
    (INST [`k:stamp`,`k:stamp`; `v:mlstring list#t list#num`,`x:mlstring list#t list#num`]
       type_def_to_ctMap_mem)) THEN
  ASM_REWRITE_TAC[]);;

let ctMap_ok_type_defs = prove
 (`!tenvT next tds tids.
     ALL_DISTINCT tids /\
     DISJOINT (set_of_list tids) (set_of_list prim_type_nums) /\
     LENGTH tds = LENGTH tids /\
     check_ctor_tenv tenvT tds /\
     tenv_abbrev_ok tenvT
     ==> ctMap_ok (FEMPTY |++ REVERSE (type_def_to_ctMap tenvT next tds tids))`,
  MATCH_MP_TAC type_def_to_ctMap_ind THEN
  RW[type_def_to_ctMap_def; check_ctor_tenv_def] THENL
   [REWRITE_TAC[REVERSE; FUPDATE_LIST_THM] THEN
    REWRITE_TAC[ctMap_ok_def; FLOOKUP_EMPTY; FEVERY_FEMPTY; option_DISTINCT];
    ALL_TAC] THEN
  REWRITE_TAC[REVERSE_APPEND; REVERSE_REVERSE; FUPDATE_LIST_APPEND; fupdate2_union] THEN
  MATCH_MP_TAC ctMap_ok_merge_imp THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_DISJOINT; NOT_EXISTS_THM] THEN X_GEN_TAC `ti:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`tenvT:tenv_abbrev`; `next_stamp + 1`;
                  `tds:(mlstring list#mlstring#(mlstring#ast_t list)list)list`;
                  `ids:num list`; `ti:num`] TPROPSAUX_FRANGE_type_def_to_ctMap) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP TPROPSAUX_FRANGE_ctors) THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC TPROPSAUX_ctMap_ok_ctors THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM ALL_MEM]) THEN
      DISCH_THEN(MP_TAC o SPEC `(cn,ts):mlstring#ast_t list`) THEN ASM_REWRITE_TAC[] THEN
      CASE_REWRITE_TAC[] THEN SIMP_TAC[];
      ASM_MESON_TAC[IN_DISJOINT; IN_INSERT; IN_SET_OF_LIST]]]);;

let all_distinct_map_fst_lemma = prove
 (CASE_TERM `!l (v:C).
     ALL_DISTINCT (MAP (\p. match p with (x,y) -> x) (l:(A#B)list))
     ==> ALL_DISTINCT (MAP (\p. match p with (x,y) -> (x,v)) l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL_DISTINCT] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[]);;

let check_ctor_tenv_change_tenvT = prove
 (CASE_TERM `!tenvT1 env tenvT2.
     ALL (\p. match p with
                (cn,ts) -> ALL (check_type_names tenvT1) ts
                           ==> ALL (check_type_names tenvT2) ts)
         (FLAT (MAP (SND o SND) env)) /\
     check_ctor_tenv tenvT1 env
     ==> check_ctor_tenv tenvT2 env`,
  MATCH_MP_TAC check_ctor_tenv_ind THEN
  RW[check_ctor_tenv_def] THEN FS[EVERY_MEM; MEM_FLAT; MEM_MAP; o_THM] THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[] o REWRITE_RULE[FORALL_PAIR_THM]) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let check_ctor_tenv_EVERY = prove
 (CASE_TERM `!tenvT tds.
     check_ctor_tenv tenvT tds <=>
     ALL check_dup_ctors tds /\
     ALL (ALL_DISTINCT o FST) tds /\
     ALL (\p. match p with
                (tvs,tn,ctors) ->
                  ALL (\q. match q with
                             (cn,ts) -> ALL (check_freevars_ast tvs) ts /\
                                        ALL (check_type_names tenvT) ts) ctors) tds /\
     ALL_DISTINCT (MAP (FST o SND) tds)`,
  MATCH_MP_TAC check_ctor_tenv_ind THEN
  REWRITE_TAC[check_ctor_tenv_def; ALL; MAP; ALL_DISTINCT; o_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN (CASE_TERM `MAP (\p. match p with (x,tn,y) -> tn)
                   (tds:(mlstring list#mlstring#(mlstring#ast_t list)list)list) =
                 MAP (FST o SND) tds`) SUBST1_TAC THENL
   [MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; o_THM] THEN
    CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONJ_ACI]);;

let nsLookup_add_tenvE1 = prove
 (`!tenvE tenvV n tvs t tvs2.
     check_freevars tvs2 [] t /\ tveLookup n tvs tenvE = SOME (tvs2,t)
     ==> nsLookup (add_tenvE tenvE tenvV) (Short n) = SOME (tvs2,t)`,
  TPROPSAUX_INDUCT_ON `tenvE:tenv_val_exp` THEN
  TPROPSAUX_RW[tveLookup_def; add_tenvE_def] THEN FS[] THENL
   [ASM_MESON_TAC[];
    TPROPSAUX_ASM_COND_TAC THEN TPROPSAUX_RW[] THENL
     [ASM_MESON_TAC[nil_deBruijn_inc]; ASM_MESON_TAC[]]]);;

let nsLookup_add_tenvE2 = prove
 (`!tenvE tenvV n tvs t tvs2.
     tveLookup n tvs tenvE = NONE /\ nsLookup tenvV (Short n) = SOME (tvs2,t)
     ==> nsLookup (add_tenvE tenvE tenvV) (Short n) = SOME (tvs2,t)`,
  TPROPSAUX_INDUCT_ON `tenvE:tenv_val_exp` THEN
  TPROPSAUX_RW[tveLookup_def; add_tenvE_def] THEN FS[] THEN
  TRY (TPROPSAUX_ASM_COND_TAC THEN TPROPSAUX_RW[]) THEN ASM_MESON_TAC[]);;

let nsLookup_add_tenvE3 = prove
 (`!tenvE tenvV n t tvs2 mn.
     nsLookup tenvV (Long mn n) = SOME (tvs2,t)
     ==> nsLookup (add_tenvE tenvE tenvV) (Long mn n) = SOME (tvs2,t)`,
  TPROPSAUX_INDUCT_ON `tenvE:tenv_val_exp` THEN
  TPROPSAUX_RW[tveLookup_def; add_tenvE_def] THEN FS[] THEN ASM_MESON_TAC[]);;

let tenv_val_ok_add_tenvE = prove
 (`!tenvE tenvV.
     num_tvs tenvE = 0 /\ tenv_val_exp_ok tenvE /\ tenv_val_ok tenvV
     ==> tenv_val_ok (add_tenvE tenvE tenvV)`,
  TPROPSAUX_INDUCT_ON `tenvE:tenv_val_exp` THEN
  TPROPSAUX_RW[add_tenvE_def; tenv_val_exp_ok_def; num_tvs_def] THEN
  FS[tenv_val_ok_def] THEN MATCH_MP_TAC nsAll_nsBind THEN
  FS[ADD_CLAUSES] THEN ASM_MESON_TAC[]);;

let add_tenvE_nsAppend = prove
 (`!tenvE tenvV. nsAppend (add_tenvE tenvE nsEmpty) tenvV = add_tenvE tenvE tenvV`,
  TPROPSAUX_INDUCT_ON `tenvE:tenv_val_exp` THEN RW[add_tenvE_def]);;

let add_tenvE_bvl = prove
 (CASE_TERM `!n bindings tenvE tenvV.
     add_tenvE (bind_var_list n bindings tenvE) tenvV =
     nsBindList (MAP (\p. match p with (x,t) -> (x,(n,t))) bindings)
                (add_tenvE tenvE tenvV)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN RW[bind_var_list_def; nsBindList_def; ITLIST] THEN
  SPEC_TAC(`h:mlstring#t`,`h:mlstring#t`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  RW[bind_var_list_def; add_tenvE_def; nsBindList_def; ITLIST] THEN
  FS[nsBindList_def]);;

let TPROPSAUX_ALL2_ALL_SND = prove
 (`!(R:A->B->bool) Q l1 l2. ALL2 (\a b. R a b /\ Q b) l1 l2 ==> ALL Q l2`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES) THEN
  REWRITE_TAC[ALL2; ALL] THEN ASM_MESON_TAC[]);;

let type_v_freevars = prove
 (`!tvs tenvC tenvS v t. type_v tvs tenvC tenvS v t ==> check_freevars tvs [] t`,
  MATCH_MP_TAC type_v_strongind THEN
  RW[check_freevars_def; tenv_val_ok_def; num_tvs_def] THENL
   [MATCH_MP_TAC(ISPECL [`type_v tvs ctMap tenvS`; `check_freevars tvs []`; `vs:v list`]
                    TPROPSAUX_ALL2_ALL_SND) THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`tenv:type_env`; `Bind_name n 0 t1 (bind_tvar tvs tenvE)`; `e:exp`; `t2:t`]
      (CONJUNCT1 type_e_freevars)) THEN
    FS[tenv_ok_def] THEN
    ASM_REWRITE_TAC[tenv_val_exp_ok_def; num_tvs_def; bind_tvar_rewrites; ADD_CLAUSES];
    MP_TAC(SPECL [`tenv:type_env`; `bind_var_list 0 bindings (bind_tvar tvs tenvE)`;
                  `funs:(mlstring#mlstring#exp)list`; `bindings:(mlstring#t)list`;
                  `0`; `t:t`; `n:mlstring`] type_funs_Tfn) THEN
    ASM_REWRITE_TAC[num_tvs_bind_var_list; bind_tvar_rewrites; ADD_CLAUSES] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP check_freevars_add) THEN ARITH_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP check_freevars_add) THEN ARITH_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP check_freevars_add) THEN ARITH_TAC]);;

let remove_lambda_prod = prove
 (CASE_TERM `(\p. match p with (x,y) -> (P:A->B->C) x y) = (\xy. P (FST xy) (SND xy))`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[]);;

let TPROPSAUX_FEMPTY_FUPDATE_LIST_REVERSE = prove
 (`!l:(A#B)list. FEMPTY |++ REVERSE l = alist_to_fmap l`,
  REWRITE_TAC[GSYM FUNION_alist_to_fmap; FUNION_FEMPTY_2]);;

let TPROPSAUX_ALL2_MAP = prove
 (`!(R1:A->B->bool) (R2:A->C->bool) (Q:B->bool) (f:B->C) l1 l2.
     ALL2 (\a b. R1 a b /\ (Q b ==> R2 a (f b))) l1 l2 /\ ALL Q l2
     ==> ALL2 R2 l1 (MAP f l2)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l2:B list` list_CASES) THEN
  REWRITE_TAC[ALL2; ALL; MAP] THEN ASM_MESON_TAC[]);;

let TPROPSAUX_ALOOKUP_MAP_SND = prove
 (CASE_TERM `!(f:B->C) (l:(A#B)list) k v.
     ALOOKUP l k = SOME v
     ==> ALOOKUP (MAP (\p. match p with (x,y) -> (x, f y)) l) k = SOME (f v)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_THM; MAP; option_DISTINCT] THEN
  SPEC_TAC(`h:A#B`,`h:A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ALOOKUP_THM] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[option_INJ]);;

(* nsAll2 R2 e1 e2 from an assumption nsAll2 R1 e1 e2, with the pointwise *)
(* implication left as the goal                                           *)
let TPROPSAUX_NSALL2_MONO_TAC : tactic =
  fun (asl,w as gl) ->
    let _,args = strip_comb w in
    let es = tl args in
    (FIRST_ASSUM(fun th ->
       let h,args' = strip_comb (concl th) in
       if is_const h && fst(dest_const h) = "nsAll2" && tl args' = es
       then MP_TAC th else NO_TAC) THEN
     MATCH_MP_TAC nsAll2_mono) gl;;

(* HOL4's statement has targs and tvs' free *)
let type_subst = prove
 (`!tvs ctMap tenvS v t.
     type_v tvs ctMap tenvS v t
     ==> tvs = LENGTH targs /\ ctMap_ok ctMap /\ ALL (check_freevars tvs' []) targs /\
         check_freevars (LENGTH targs) [] t
     ==> type_v tvs' ctMap tenvS v (deBruijn_subst 0 targs t)`,
  let ALL2_TAC l =
    MP_TAC(ISPECL [`type_v (LENGTH (targs:t list)) ctMap tenvS`; `type_v tvs' ctMap tenvS`;
                   `\y. ctMap_ok ctMap /\ ALL (check_freevars tvs' []) (targs:t list) /\
                        check_freevars (LENGTH targs) [] y`;
                   `deBruijn_subst 0 targs`; `vs:v list`; l] TPROPSAUX_ALL2_MAP) THEN
    BETA_TAC in
  MATCH_MP_TAC type_v_strongind THEN RW[] THEN ONCE_REWRITE_TAC[type_v_cases] THEN
  SIMP[deBruijn_inc_def; deBruijn_subst_def] THEN FS[check_freevars_def] THENL
   [(* Conv (SOME stamp) *)
    CONJ_TAC THENL
     [REWRITE_TAC[EVERY_MAP] THEN
      UNDISCH_TAC `ALL (check_freevars (LENGTH (targs:t list)) []) (ts':t list)` THEN
      MATCH_MP_TAC MONO_ALL THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC deBruijn_subst_check_freevars2 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TPROPSAUX_FEMPTY_FUPDATE_LIST_REVERSE]) THEN
    REWRITE_TAC[TPROPSAUX_FEMPTY_FUPDATE_LIST_REVERSE] THEN
    SUBGOAL_THEN `ALL (check_freevars 0 tvs'') (ts:t list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[ctMap_ok_lookup]; ALL_TAC] THEN
    SUBGOAL_THEN
     `MAP (type_subst (alist_to_fmap (ZIP tvs'' (MAP (deBruijn_subst 0 targs) ts')))) ts =
      MAP (deBruijn_subst 0 targs)
        (MAP (type_subst (alist_to_fmap (ZIP (tvs'':mlstring list) (ts':t list))))
             (ts:t list))`
      SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_SYM THEN MATCH_MP_TAC TPROPSAUX_type_subst_deBruijn_subst_list THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ALL2_TAC `MAP (type_subst (alist_to_fmap (ZIP (tvs'':mlstring list) (ts':t list))))
                  (ts:t list)` THEN
    ANTS_TAC THENL [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]; REWRITE_TAC[]] THEN
    ASM_REWRITE_TAC[EVERY_MAP] THEN
    UNDISCH_TAC `ALL (check_freevars 0 tvs'') (ts:t list)` THEN MATCH_MP_TAC MONO_ALL THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC check_freevars_subst_single THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP check_freevars_add) THEN ARITH_TAC;
    (* Conv NONE *)
    ALL2_TAC `ts:t list` THEN ASM_REWRITE_TAC[ETA_AX];
    (* Closure *)
    MAP_EVERY EXISTS_TAC [`tenv:type_env`; `tenvE:tenv_val_exp`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [TPROPSAUX_NSALL2_MONO_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
      MESON_TAC[];
      MATCH_MP_TAC deBruijn_subst_check_freevars2 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC type_e_subst_lem THEN FS[tenv_ok_def; bind_tvar_rewrites]];
    (* Recclosure *)
    MAP_EVERY EXISTS_TAC [`tenv:type_env`; `tenvE:tenv_val_exp`] THEN
    EXISTS_TAC (CASE_TERM `MAP (\p. match p with (x,t) -> (x, deBruijn_subst 0 targs t))
                               (bindings:(mlstring#t)list)`) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [TPROPSAUX_NSALL2_MONO_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
      MESON_TAC[];
      MP_TAC(SPECL [`tenv:type_env`;
                    `bind_var_list 0 bindings (bind_tvar (LENGTH (targs:t list)) tenvE)`;
                    `funs:(mlstring#mlstring#exp)list`; `bindings:(mlstring#t)list`]
        (CONJUNCT2 (CONJUNCT2 (INST [`tenvE:tenv_val_exp`,`tenvE2:tenv_val_exp`]
                                      type_e_subst)))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`bind_var_list 0 bindings Empty`; `targs:t list`; `tvs':num`;
                                 `MAP (deBruijn_inc 0 0) (targs:t list)`]) THEN
      REWRITE_TAC[num_tvs_bind_var_list; num_tvs_def; deBruijn_subst_E_bvl; db_merge_bvl;
                  db_merge_def; deBruijn_subst_tenvE_def; ADD_CLAUSES; deBruijn_inc0] THEN
      DISCH_THEN MATCH_MP_TAC THEN FS[tenv_ok_def] THEN
      MATCH_MP_TAC tenv_val_exp_ok_bvl_funs THEN
      ASM_REWRITE_TAC[bind_tvar_rewrites] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC TPROPSAUX_ALOOKUP_MAP_SND THEN ASM_REWRITE_TAC[]];
    (* Loc: Ref_t *)
    ASM_SIMP_TAC[nil_deBruijn_subst];
    (* Loc: Varray_t *)
    ASM_SIMP_TAC[nil_deBruijn_subst];
    (* Vectorv *)
    ASM_SIMP_TAC[nil_deBruijn_subst] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
       fst(strip_comb(concl th)) = `ALL:(v->bool)->v list->bool`)) THEN
    MATCH_MP_TAC MONO_ALL THEN BETA_TAC THEN ASM_SIMP_TAC[nil_deBruijn_subst]]);;

let check_ctor_tenv_ok = prove
 (`!tenvT tds tis.
     LENGTH tds = LENGTH tis /\ check_ctor_tenv tenvT tds /\ tenv_abbrev_ok tenvT
     ==> tenv_ctor_ok (build_ctor_tenv tenvT tds tis)`,
  MATCH_MP_TAC build_ctor_tenv_ind THEN
  RW[build_ctor_tenv_def; tenv_ctor_ok_def; check_ctor_tenv_def] THEN
  MATCH_MP_TAC nsAll_nsAppend THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC nsAll_alist_to_ns THEN
  REWRITE_TAC[EVERY_REVERSE; EVERY_MAP] THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[] o REWRITE_RULE[GSYM ALL_MEM; FORALL_PAIR_THM]) THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p1:mlstring`; `p2:ast_t list`]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MEM_MAP]) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC check_freevars_type_name_subst THEN
  ASM_SIMP_TAC[]);;

let nsMap_build_ctor_tenv = prove
 (CASE_TERM `!(ga:ast_t list->ast_t list) (g:t list->t list) (h:E->F) tenvT
              (tds:(C#D#(B#ast_t list)list)list) (ids:E list).
     LENGTH tds = LENGTH ids /\
     (!x. MEM x (MAP SND (FLAT (MAP (SND o SND) tds)))
          ==> MAP (type_name_subst tenvT) (ga x) = g (MAP (type_name_subst tenvT) x))
     ==> nsMap (\p. match p with (tvs,ts,tid) -> (tvs, g ts, h tid))
               (build_ctor_tenv tenvT tds ids:(A,B,C#t list#E)namespace) =
         build_ctor_tenv tenvT (MAP (I ## I ## MAP (I ## ga)) tds) (MAP h ids)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC build_ctor_tenv_ind THEN
  RW[build_ctor_tenv_def; MAP; PAIR_MAP_THM; I_THM] THEN
  RW[nsMap_nsAppend; nsMap_alist_to_ns; MAP_REVERSE; MAP_MAP_o; o_DEF] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; MEM_REVERSE] THEN BETA_TAC THEN
  REWRITE_TAC[PAIR_MAP_THM; I_THM] THEN CASE_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN DISJ1_TAC THEN
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM] THEN ASM_MESON_TAC[]);;

let type_d_check_uniq = prove
 (`(!check tenv d tdecs new_tenv.
      type_d check tenv d tdecs new_tenv ==> type_d F tenv d tdecs new_tenv) /\
   (!check tenv d tdecs new_tenv.
      type_ds check tenv d tdecs new_tenv ==> type_ds F tenv d tdecs new_tenv)`,
  MATCH_MP_TAC type_d_ind THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[type_d_cases] THEN REWRITE_TAC[distinctness "dec"; injectivity "dec"] THEN
  ASM_MESON_TAC[]);;

let extend_dec_tenv_ok = prove
 (`!tenv tenv'. tenv_ok tenv /\ tenv_ok tenv' ==> tenv_ok (extend_dec_tenv tenv tenv')`,
  RW[extend_dec_tenv_def; tenv_ok_def] THEN
  FS[tenv_val_ok_def; tenv_abbrev_ok_def] THEN
  MATCH_MP_TAC nsAll_nsAppend THEN ASM_REWRITE_TAC[]);;

let TPROPSAUX_tenv_ok_tenv_add_tvs = prove
 (`!tvs bindings.
     ALL (check_freevars tvs []) (MAP SND bindings)
     ==> tenv_ok (type_env_REC (alist_to_ns (tenv_add_tvs tvs bindings)) nsEmpty nsEmpty)`,
  REPEAT STRIP_TAC THEN RW[tenv_ok_def; tenv_val_ok_def] THEN
  MATCH_MP_TAC nsAll_alist_to_ns THEN
  REWRITE_TAC[tenv_add_tvs_def; EVERY_MAP] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[EVERY_MAP] THEN MATCH_MP_TAC MONO_ALL THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[]);;

let TPROPSAUX_tenv_abbrev_ok_tdefs = prove
 (CASE_TERM `!tdefs (ids:num list).
     tenv_abbrev_ok
       (alist_to_ns
          (MAP2 (\tdef i. match tdef with (tvs,tn,ctors) -> (tn,(tvs,Tapp (MAP Tvar tvs) i)))
                (tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list) ids))`,
  REWRITE_TAC[tenv_abbrev_ok_def] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC nsAll_alist_to_ns THEN BETA_TAC THEN
  SPEC_TAC(`ids:num list`,`ids:num list`) THEN
  SPEC_TAC(`tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list`,
           `tdefs:(mlstring list#mlstring#(mlstring#ast_t list)list)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP2_DEF; ALL] THEN GEN_TAC THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  SPEC_TAC(`h:mlstring list#mlstring#(mlstring#ast_t list)list`,
           `h:mlstring list#mlstring#(mlstring#ast_t list)list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[check_freevars_def; EVERY_MAP; GSYM ALL_MEM]);;

let type_d_tenv_ok_helper = prove
 (`(!check tenv d tdecs tenv'.
      type_d check tenv d tdecs tenv' ==> tenv_ok tenv ==> tenv_ok tenv') /\
   (!check tenv d tdecs tenv'.
      type_ds check tenv d tdecs tenv' ==> tenv_ok tenv ==> tenv_ok tenv')`,
  MATCH_MP_TAC type_d_ind THEN RW[tenv_ctor_ok_def; tenvLift_def] THENL
   [(* Dlet (value) *)
    MATCH_MP_TAC TPROPSAUX_tenv_ok_tenv_add_tvs THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 type_p_freevars) o
      check (fun th -> can (term_match [] `type_p a b c d e`) (concl th))) THEN SIMP_TAC[];
    (* Dlet *)
    MATCH_MP_TAC TPROPSAUX_tenv_ok_tenv_add_tvs THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (CONJUNCT1 type_p_freevars) o
      check (fun th -> can (term_match [] `type_p a b c d e`) (concl th))) THEN SIMP_TAC[];
    (* Dletrec *)
    MATCH_MP_TAC TPROPSAUX_tenv_ok_tenv_add_tvs THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (CONJUNCT2 (CONJUNCT2 type_e_freevars)) o
      check (fun th -> can (term_match [] `type_funs a b c d`) (concl th))) THEN
    REWRITE_TAC[num_tvs_bind_var_list; bind_tvar_rewrites; num_tvs_def; ADD_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN FS[tenv_ok_def] THEN
    MATCH_MP_TAC tenv_val_exp_ok_bvl_funs THEN
    REWRITE_TAC[bind_tvar_rewrites; tenv_val_exp_ok_def] THEN ASM_MESON_TAC[];
    (* Dtype *)
    REWRITE_TAC[tenv_ok_def; type_env_INFO.ri_accessors; tenv_val_ok_nsEmpty;
                TPROPSAUX_tenv_abbrev_ok_tdefs] THEN
    MATCH_MP_TAC check_ctor_tenv_ok THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC tenv_abbrev_ok_merge THEN REWRITE_TAC[TPROPSAUX_tenv_abbrev_ok_tdefs] THEN
    FS[tenv_ok_def];
    (* Dtabbrev *)
    FS[tenv_ok_def; tenv_abbrev_ok_def; nsAll_nsSing] THEN CASE_REWRITE_TAC[] THEN
    MATCH_MP_TAC check_freevars_type_name_subst THEN ASM_REWRITE_TAC[tenv_abbrev_ok_def];
    (* Dexn *)
    FS[tenv_ok_def; tenv_ctor_ok_def; nsAll_nsSing] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[EVERY_MAP] THEN FS[EVERY_MEM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC check_freevars_type_name_subst THEN ASM_SIMP_TAC[tenv_abbrev_ok_def];
    (* Dmod *)
    FS[tenv_ok_def; tenv_val_ok_def; tenv_ctor_ok_def; tenv_abbrev_ok_def; nsAll_nsLift] THEN
    ASM_REWRITE_TAC[ETA_AX];
    (* Dlocal *)
    ASM_MESON_TAC[extend_dec_tenv_ok];
    (* type_ds *)
    ASM_MESON_TAC[extend_dec_tenv_ok]]);;

let type_d_tenv_ok = prove
 (`!check tenv d tdecs tenv'.
     type_d check tenv d tdecs tenv' /\ tenv_ok tenv
     ==> tenv_ok (extend_dec_tenv tenv' tenv)`,
  MESON_TAC[extend_dec_tenv_ok; type_d_tenv_ok_helper]);;

(* ---------- type_ds ---------- *)

let type_ds_empty = prove
 (`!check tenv decls r.
     type_ds check tenv [] decls r <=>
     decls = {} /\ r = type_env_REC nsEmpty nsEmpty nsEmpty`,
  ONCE_REWRITE_TAC[type_d_cases] THEN REWRITE_TAC[NOT_CONS_NIL] THEN MESON_TAC[]);;
let _ = cake_add_simps [type_ds_empty];;

let type_ds_sing = prove
 (`!check tenv d decls r.
     type_ds check tenv [d] decls r <=> type_d check tenv d decls r`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [type_d_cases] THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN
  SIMP_NOASM[type_ds_empty; extend_dec_tenv_def; UNION_EMPTY; DISJOINT_EMPTY]);;
let _ = cake_add_simps [type_ds_sing];;
