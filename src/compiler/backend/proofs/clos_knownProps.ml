(* ========================================================================= *)
(* clos_knownProps: port of HOL4 compiler/backend/proofs/                    *)
(* clos_knownPropsScript.sml (CakeML v3479).                                 *)
(* Lemmas used in proof of clos_known                                        *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/clos_known.ml";;

type_invention_error := true;;

(* HOL4: merge_Other [simp] *)
let merge_Other = prove
 (`!a. merge clos_known_Other a = clos_known_Other /\
       merge a clos_known_Other = clos_known_Other`,
  GEN_TAC THEN CASES_ON `a:val_approx` THEN REWRITE_TAC[merge_def]);;
let _ = cake_add_simps [merge_Other];;

(* HOL4: merge_Impossible [simp] *)
let merge_Impossible = prove
 (`!a. merge a Impossible = a`,
  GEN_TAC THEN CASES_ON `a:val_approx` THEN REWRITE_TAC[merge_def]);;
let _ = cake_add_simps [merge_Impossible];;

(* local helpers: MAP2 (HOL Light's MAP2 takes HD and TL of the second list) *)
let CLOSPROPSAUX_MAP2_comm = prove
 (`!(f:A->A->A) xs ys.
     LENGTH xs = LENGTH ys /\ (!x y. MEM x xs ==> f x y = f y x) ==>
     MAP2 f xs ys = MAP2 f ys xs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ys:A list` list_CASES) THEN
  REWRITE_TAC[MAP2_DEF; LENGTH; NOT_SUC; HD; TL; SUC_INJ; MEM; CONS_11] THEN
  ASM_MESON_TAC[]);;

let CLOSPROPSAUX_MAP2_assoc = prove
 (`!(f:A->A->A) xs ys zs.
     LENGTH xs = LENGTH ys /\ LENGTH ys = LENGTH zs /\
     (!x y z. MEM x xs ==> f x (f y z) = f (f x y) z) ==>
     MAP2 f xs (MAP2 f ys zs) = MAP2 f (MAP2 f xs ys) zs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ys:A list` list_CASES) THEN
  STRUCT_CASES_TAC(ISPEC `zs:A list` list_CASES) THEN
  REWRITE_TAC[MAP2_DEF; LENGTH; NOT_SUC; HD; TL; SUC_INJ; MEM; CONS_11] THEN
  ASM_MESON_TAC[]);;

let CLOSPROPSAUX_MAP2_idem = prove
 (`!(f:A->A->A) xs. (!x. MEM x xs ==> f x x = x) ==> MAP2 f xs xs = xs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP2_DEF; MEM; HD; TL; CONS_11] THEN
  ASM_MESON_TAC[]);;

let CLOSPROPSAUX_LENGTH_MAP2 = prove
 (`!(f:A->B->C) xs ys. LENGTH (MAP2 f xs ys) = LENGTH xs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP2_DEF; LENGTH]);;

(* HOL4: merge_comm *)
let merge_comm = prove
 (`!a1 a2. merge a1 a2 = merge a2 a1`,
  MATCH_MP_TAC merge_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[merge_def; merge_Impossible] THEN
  TRY(DISCH_TAC THEN
      ASM_CASES_TAC `LENGTH (xs:val_approx list) = LENGTH (ys:val_approx list)` THEN
      ASM_CASES_TAC `tg1:num = tg2` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[injectivity "val_approx"] THEN
      MATCH_MP_TAC CLOSPROPSAUX_MAP2_comm THEN ASM_MESON_TAC[] THEN NO_TAC) THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[injectivity "val_approx"] THEN
  ASM_MESON_TAC[]);;

(* HOL4: merge_assoc *)
let merge_assoc = prove
 (`!a1 a2 a3. merge a1 (merge a2 a3) = merge (merge a1 a2) a3`,
  MATCH_MP_TAC merge_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY DISCH_TAC THEN REPEAT GEN_TAC THEN CASES_ON `a3:val_approx` THEN
  REWRITE_TAC[merge_def; merge_Other; merge_Impossible] THEN
  REPEAT(COND_CASES_TAC THEN
         REWRITE_TAC[merge_def; merge_Other; merge_Impossible; CLOSPROPSAUX_LENGTH_MAP2;
                     injectivity "val_approx"; distinctness "val_approx"]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; CLOSPROPSAUX_LENGTH_MAP2]) THEN
  TRY(MATCH_MP_TAC CLOSPROPSAUX_MAP2_assoc THEN ASM_MESON_TAC[] THEN NO_TAC) THEN
  ASM_MESON_TAC[]);;

(* a local helper: merge a a = a, with the list form for the induction *)
let CLOSPROPSAUX_merge_idem = prove
 (`(!a. merge a a = a) /\ (!l. MAP2 merge l l = l)`,
  MATCH_MP_TAC val_approx_INDUCT THEN
  REWRITE_TAC[merge_def; MAP2_DEF; HD; TL] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* HOL4: merge_idem [simp] *)
let merge_idem = prove
 (`!a. merge a a = a`,
  REWRITE_TAC[CLOSPROPSAUX_merge_idem]);;
let _ = cake_add_simps [merge_idem];;

(* See merge as a join operation on a semi-lattice: it's a join because it's *)
(* a little akin to a union: as merge is used, more and more values might    *)
(* inhabit the approximation, with Other at the top corresponding to         *)
(* anything at all. HOL4 writes subapprox as the infix overload a1 <| a2.    *)

let subapprox_def = cake_def
  `subapprox a1 a2 <=> merge a1 a2 = a2`;;

let subapprox_refl = prove
 (`!a. subapprox a a`,
  REWRITE_TAC[subapprox_def; merge_idem]);;
let _ = cake_add_simps [subapprox_refl];;

let subapprox_trans = prove
 (`!a1 a2 a3. subapprox a1 a2 /\ subapprox a2 a3 ==> subapprox a1 a3`,
  REWRITE_TAC[subapprox_def] THEN MESON_TAC[merge_assoc]);;

let subapprox_antisym = prove
 (`!a1 a2. subapprox a1 a2 /\ subapprox a2 a1 ==> a1 = a2`,
  REWRITE_TAC[subapprox_def] THEN MESON_TAC[merge_comm]);;

let subapprox_merge = prove
 (`!a b. subapprox a (merge a b) /\ subapprox a (merge b a)`,
  REWRITE_TAC[subapprox_def] THEN MESON_TAC[merge_assoc; merge_comm; merge_idem]);;
let _ = cake_add_simps [subapprox_merge];;

let subapprox_Other = prove
 (`!a. (subapprox clos_known_Other a <=> a = clos_known_Other) /\
       subapprox a clos_known_Other`,
  REWRITE_TAC[subapprox_def; merge_Other] THEN MESON_TAC[]);;
let _ = cake_add_simps [subapprox_Other];;

let CLOSPROPSAUX_SUBAPPROX_TAC : tactic =
  REPEAT GEN_TAC THEN REWRITE_TAC[subapprox_def] THEN CASES_ON `a:val_approx` THEN
  REWRITE_TAC[merge_def; injectivity "val_approx"; distinctness "val_approx"] THEN
  REPEAT(COND_CASES_TAC THEN
         ASM_REWRITE_TAC[injectivity "val_approx"; distinctness "val_approx"]) THEN
  ASM_MESON_TAC[];;

let subapprox_Int = prove
 (`!a i. (subapprox a (clos_known_Int i) <=> a = clos_known_Int i \/ a = Impossible) /\
         (subapprox (clos_known_Int i) a <=> a = clos_known_Int i \/ a = clos_known_Other)`,
  CLOSPROPSAUX_SUBAPPROX_TAC);;
let _ = cake_add_simps [subapprox_Int];;

let subapprox_ClosNoInline = prove
 (`!a m n.
     (subapprox a (ClosNoInline m n) <=> a = ClosNoInline m n \/ a = Impossible) /\
     (subapprox (ClosNoInline m n) a <=> a = ClosNoInline m n \/ a = clos_known_Other)`,
  CLOSPROPSAUX_SUBAPPROX_TAC);;
let _ = cake_add_simps [subapprox_ClosNoInline];;

let subapprox_Clos = prove
 (`!a m n e s.
     (subapprox a (clos_known_Clos m n e s) <=> a = clos_known_Clos m n e s \/ a = Impossible) /\
     (subapprox (clos_known_Clos m n e s) a <=>
      a = clos_known_Clos m n e s \/ a = clos_known_Other)`,
  CLOSPROPSAUX_SUBAPPROX_TAC);;
let _ = cake_add_simps [subapprox_Clos];;

let subapprox_Impossible = prove
 (`!a. (subapprox a Impossible <=> a = Impossible) /\ subapprox Impossible a`,
  REWRITE_TAC[subapprox_def; merge_def; merge_Impossible] THEN MESON_TAC[]);;
let _ = cake_add_simps [subapprox_Impossible];;

(* a local helper: MAP2 f xs ys = ys elementwise *)
let CLOSPROPSAUX_MAP2_eq_snd = prove
 (`!(f:A->B->B) xs ys.
     LENGTH xs = LENGTH ys ==> (MAP2 f xs ys = ys <=> ALL2 (\x y. f x y = y) xs ys)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `ys:B list` list_CASES) THEN
  REWRITE_TAC[MAP2_DEF; LENGTH; NOT_SUC; HD; TL; SUC_INJ; ALL2; CONS_11] THEN
  ASM_MESON_TAC[]);;

let subapprox_Tuple = prove
 (`!tg1 as1 tg2 as2.
     subapprox (clos_known_Tuple tg1 as1) (clos_known_Tuple tg2 as2) <=>
     tg1 = tg2 /\ ALL2 subapprox as1 as2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[subapprox_def; merge_def] THEN
  ASM_CASES_TAC `LENGTH (as1:val_approx list) = LENGTH (as2:val_approx list)` THEN
  ASM_CASES_TAC `tg1:num = tg2` THEN
  ASM_REWRITE_TAC[injectivity "val_approx"; distinctness "val_approx"] THENL
   [ASM_SIMP_TAC[CLOSPROPSAUX_MAP2_eq_snd] THEN AP_THM_TAC THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; subapprox_def];
    ASM_MESON_TAC[LIST_REL_LENGTH]]);;
let _ = cake_add_simps [subapprox_Tuple];;

let better_definedg_def = cake_def
  `better_definedg (g1:val_approx spt) g2 <=>
     !k. k IN domain g1 ==>
         k IN domain g2 /\ subapprox (THE (lookup k g1)) (THE (lookup k g2))`;;

let better_definedg_refl = prove
 (`!g. better_definedg g g`,
  REWRITE_TAC[better_definedg_def; subapprox_refl]);;
let _ = cake_add_simps [better_definedg_refl];;

let better_definedg_trans = prove
 (`!g1 g2 g3. better_definedg g1 g2 /\ better_definedg g2 g3 ==> better_definedg g1 g3`,
  REWRITE_TAC[better_definedg_def] THEN MESON_TAC[subapprox_trans]);;

(* HOL4: known_op_better_definedg *)
let known_op_better_definedg = prove
 (`!opn apxs (g0:val_approx spt) a g. known_op opn apxs g0 = (a,g) ==> better_definedg g0 g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[known_op_pmatch] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[better_definedg_refl] THEN
  REWRITE_TAC[better_definedg_def; domain_insert; IN_INSERT; lookup_insert] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[subapprox_refl] THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[domain_lookup]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_exists o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[distinctness "option"; injectivity "option"]) THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[THE_DEF; subapprox_merge] THEN
  ASM_MESON_TAC[distinctness "option"; injectivity "option"]);;

(* a local tactic for known_better_definedg: unfold known once, split the   *)
(* pairs and cases, resolve the induction hypotheses, chain the relations   *)
let CLOSPROPSAUX_KNOWN_BDG_TAC : tactic =
  REPEAT GEN_TAC THEN
  TRY(DISCH_THEN(fun th -> if is_eq (concl th) then MP_TAC th else STRIP_ASSUME_TAC th)) THEN
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[known_def] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT PAIRARG_TAC THEN REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REPEAT PAIRARG_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  CLOSPROPSAUX_RES_TAC THEN CLOSPROPSAUX_RES_TAC THEN CLOSPROPSAUX_RES_TAC THEN
  IMP_RES_TAC known_op_better_definedg THEN
  ASM_MESON_TAC[better_definedg_trans; better_definedg_refl];;
(* HOL4: known_better_definedg *)
let known_better_definedg = prove
 (`!c es apxs (g0:val_approx spt) alist g.
     known c es apxs g0 = (alist,g) ==> better_definedg g0 g`,
  MATCH_MP_TAC known_ind THEN REPEAT CONJ_TAC THEN CLOSPROPSAUX_KNOWN_BDG_TAC);;

(* HOL4: mk_Ticks_alt (HOL4 mk_Ticks is clos_known_mk_Ticks; the trace     *)
(* t extended with tc is mk_cons t tc)                                      *)
let mk_Ticks_alt = prove
 (`(!t tc e. clos_known_mk_Ticks t tc 0 e = e) /\
   (!t tc n e. clos_known_mk_Ticks t tc (SUC n) e =
               clos_known_mk_Ticks t (tc + 1) n (clos_Tick (mk_cons t tc) e))`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_known_mk_Ticks_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1]);;
