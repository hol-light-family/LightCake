(* ========================================================================= *)
(* basic: port of the HOL4 basic library theories used by the CakeML        *)
(* closure (CakeML v3479): combin, bool, marker, one, sum, option, pair,     *)
(* num, prim_rec, arithmetic, While, relation, basicSize and the pred_set    *)
(* extras that HOL Light's sets.ml lacks (HOL4 src/bool, src/combin,       *)
(* src/marker, src/coretypes, src/num/theories, src/relation, src/pred_set). *)
(* The constants shared with the other units are in vocab.ml; HOL4 names     *)
(* already bound in HOL Light with another statement get a theory prefix     *)
(* (arithmetic_, pred_set_, pair_, relation_, bool_, marker_).               *)
(* HOL4 count_def is pred_set_count_def (HOL4 count is pred_set_count, a     *)
(* short common word).                                                       *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* combin (HOL4 src/combin/combinScript.sml).  HOL4 C is vocab.ml's flip,     *)
(* HOL4 UPDATE is vocab.ml's =+, K is the kit's (K_DEF, K_THM).              *)
(* ------------------------------------------------------------------------- *)

let C_DEF = prove
 (`flip = \(f:A->B->C) x y. f y x`,
  REWRITE_TAC[FUN_EQ_THM; flip_DEF]);;

let C_THM = prove
 (`!(f:A->B->C) x y. flip f x y = f y x`,
  REWRITE_TAC[flip_DEF]);;

let C_ABS_L = prove
 (`flip (\x:A. (f:A->B->C) x) (y:B) = (\x. f x y)`,
  REWRITE_TAC[FUN_EQ_THM; flip_DEF]);;

let o_ABS_L = prove
 (`(\x:A. (f:A->C) x) o (g:B->A) = (\x. f (g x))`,
  REWRITE_TAC[FUN_EQ_THM; o_THM]);;

let o_ABS_R = prove
 (`(f:B->C) o (\x:A. (g:A->B) x) = (\x. f (g x))`,
  REWRITE_TAC[FUN_EQ_THM; o_THM]);;

let o_ASSOC' = prove
 (`!(f:C->D) (g:B->C) (h:A->B). (f o g) o h = f o (g o h)`,
  REWRITE_TAC[o_ASSOC]);;

let I_o_ID = I_O_ID;;

let UPDATE_def = UPDATE_DEF;;

let UPDATE_APPLY = prove
 (`(!(a:A) (x:B) f. (a =+ x) f a = x) /\
   (!(a:A) b (x:B) f. ~(a = b) ==> ((a =+ x) f b = f b))`,
  REWRITE_TAC[APPLY_UPDATE_THM] THEN MESON_TAC[]);;

let UPDATE_APPLY1 = CONJUNCT1 UPDATE_APPLY;;

let UPDATE_COMMUTES = prove
 (`!(f:A->B) a b c d. ~(a = b) ==>
     ((a =+ c) ((b =+ d) f) = (b =+ d) ((a =+ c) f))`,
  REWRITE_TAC[FUN_EQ_THM; APPLY_UPDATE_THM] THEN MESON_TAC[]);;

let UPDATE_EQ = prove
 (`!(f:A->B) a b c. (a =+ c) ((a =+ b) f) = (a =+ c) f`,
  REWRITE_TAC[FUN_EQ_THM; APPLY_UPDATE_THM] THEN MESON_TAC[]);;

let UPDATE_APPLY_ID = prove
 (`!(f:A->B) a b. (f a = b) <=> ((a =+ b) f = f)`,
  REWRITE_TAC[FUN_EQ_THM; APPLY_UPDATE_THM] THEN MESON_TAC[]);;

let UPDATE_APPLY_ID_RWT = prove
 (`(!(f:A->B) a b. ((a =+ b) f = f) <=> (f a = b)) /\
   (!(f:A->B) a b. (f = (a =+ b) f) <=> (f a = b))`,
  REWRITE_TAC[FUN_EQ_THM; APPLY_UPDATE_THM] THEN MESON_TAC[]);;

let APPLY_UPDATE_ID = prove
 (`!(f:A->B) a. (a =+ f a) f = f`,
  REWRITE_TAC[FUN_EQ_THM; APPLY_UPDATE_THM] THEN MESON_TAC[]);;

let FAIL_DEF = new_definition
  `FAIL = \(x:A) (y:B). x`;;

let LEFT_ID_DEF = new_definition
  `LEFT_ID (f:A->B->B) e <=> (!x. f e x = x)`;;
(* ------------------------------------------------------------------------- *)
(* bool (HOL4 src/bool/boolScript.sml).  Most of it is HOL Light's core      *)
(* under the same names (FUN_EQ_THM, CONJ_ASSOC, SKOLEM_THM, COND_RAND, ...). *)
(* PULL_EXISTS and PULL_FORALL are single conjunctive theorems, as in HOL4:   *)
(* any theorem list (REWRITE_TAC, SIMP, FS, GVS) splits them.                *)
(* ------------------------------------------------------------------------- *)

let PULL_EXISTS = prove
 (`!(P:A->bool) Q.
     (((?x. P x) ==> Q) <=> (!x. P x ==> Q)) /\
     ((?x. P x) /\ Q <=> (?x. P x /\ Q)) /\
     (Q /\ (?x. P x) <=> (?x. Q /\ P x))`,
  MESON_TAC[]);;

let PULL_FORALL = prove
 (`!(P:A->bool) Q.
     ((Q ==> (!x. P x)) <=> (!x. Q ==> P x)) /\
     ((!x. P x) /\ Q <=> (!x. P x /\ Q)) /\
     (Q /\ (!x. P x) <=> (!x. Q /\ P x))`,
  MESON_TAC[]);;

let LET_THM = LET_DEF;;

(* HOL4 LET_DEF is the lambda form; HOL Light's LET_DEF is pointwise *)

let bool_LET_DEF = prove
 (`LET = \(f:A->B) x. f x`,
  REWRITE_TAC[FUN_EQ_THM; LET_DEF]);;

let AND_IMP_INTRO = prove
 (`!t1 t2 t3. t1 ==> t2 ==> t3 <=> t1 /\ t2 ==> t3`,
  REWRITE_TAC[IMP_IMP]);;

let bool_case_eq = prove
 (`((if x then t1 else t2) = (v:A)) <=>
   ((x <=> T) /\ t1 = v) \/ ((x <=> F) /\ t2 = v)`,
  BOOL_CASES_TAC `x:bool` THEN REWRITE_TAC[]);;

let CONJ_COMM = CONJ_SYM;;

let DISJ_COMM = DISJ_SYM;;

let ETA_THM = ETA_AX;;

let FORALL_BOOL = FORALL_BOOL_THM;;

let LEFT_AND_OVER_OR = LEFT_OR_DISTRIB;;

let EQ_IMP_THM = prove
 (`!t1 t2. (t1 <=> t2) <=> (t1 ==> t2) /\ (t2 ==> t1)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `t1:bool` THEN
  BOOL_CASES_TAC `t2:bool` THEN REWRITE_TAC[]);;

let IN_DEF = prove
 (`(IN) = \(x:A) f. f x`,
  REWRITE_TAC[FUN_EQ_THM; IN]);;

let DISJ_IMP_THM = prove
 (`!P Q R. (P \/ Q ==> R) <=> (P ==> R) /\ (Q ==> R)`,
  MESON_TAC[]);;

let IMP_CONJ_THM = prove
 (`!P Q R. P ==> Q /\ R <=> (P ==> Q) /\ (P ==> R)`,
  MESON_TAC[]);;

let IMP_DISJ_THM = prove
 (`!A B. A ==> B <=> ~A \/ B`,
  MESON_TAC[]);;

let COND_EXPAND_IMP = prove
 (`!b t1 t2. (if b then t1 else t2) <=> (b ==> t1) /\ (~b ==> t2)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;

let DISJ_EQ_IMP = prove
 (`!A B. A \/ B <=> ~A ==> B`,
  MESON_TAC[]);;

let OR_INTRO_THM1 = prove
 (`!t1 t2. t1 ==> t1 \/ t2`,
  MESON_TAC[]);;

let OR_INTRO_THM2 = prove
 (`!t1 t2. t2 ==> t1 \/ t2`,
  MESON_TAC[]);;

let FALSITY = prove
 (`!t. F ==> t`,
  REWRITE_TAC[]);;

let IMP_F = prove
 (`!t. (t ==> F) ==> ~t`,
  REWRITE_TAC[]);;

let COND_CONG = prove
 (`!P Q (x:A) x' y y'.
     (P = Q) /\ (Q ==> (x = x')) /\ (~Q ==> (y = y'))
     ==> ((if P then x else y) = (if Q then x' else y'))`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `Q:bool` THEN SIMP_TAC[]);;

let bool_case_CONG = COND_CONG;;

(* HOL4 COND_RAND quantifies f first; HOL Light's COND_RAND quantifies b
   first (same as a rewrite) *)

let bool_COND_RAND = prove
 (`!(f:A->B) b x y. f (if b then x else y) = if b then f x else f y`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let RES_FORALL_DEF = new_definition
  `RES_FORALL = \(p:A->bool) m. !x. x IN p ==> m x`;;

let RES_FORALL_THM = prove
 (`!(P:A->bool) f. RES_FORALL P f <=> !x. x IN P ==> f x`,
  REWRITE_TAC[RES_FORALL_DEF]);;
(* ------------------------------------------------------------------------- *)
(* marker (HOL4 src/marker/markerScript.sml): only Abbrev; Case, lab and     *)
(* NoAsms are tactic markers.  OCaml cannot bind Abbrev_def (jrh lexer).    *)
(* ------------------------------------------------------------------------- *)

let marker_Abbrev_def = new_definition
  `Abbrev (x:bool) <=> x`;;

(* ------------------------------------------------------------------------- *)
(* one and sum (HOL4 src/coretypes).  HOL4 one is HOL Light's 1, with the    *)
(* same theorem one; HOL4 OUTL and OUTR are HOL Light's (ISL, ISR unused).   *)
(* ------------------------------------------------------------------------- *)

let INL_11 = prove
 (`((INL (x:A)):A+B = INL y) <=> (x = y)`,
  REWRITE_TAC[injectivity "sum"]);;

let INR_11 = prove
 (`((INR (x:B)):A+B = INR y) <=> (x = y)`,
  REWRITE_TAC[injectivity "sum"]);;

let INR_INL_11 = prove
 (`(!(x:A) y. ((INL x):A+B = INL y) <=> (x = y)) /\
   (!(x:B) y. ((INR x):A+B = INR y) <=> (x = y))`,
  REWRITE_TAC[injectivity "sum"]);;

let sum_distinct = prove
 (`!(x:A) (y:B). ~(INL x = INR y)`,
  REWRITE_TAC[distinctness "sum"]);;

let sum_distinct1 = prove
 (`!(x:A) (y:B). ~(INR y = INL x)`,
  REWRITE_TAC[distinctness "sum"]);;

let FORALL_SUM = prove
 (`(!s:A+B. P s) <=> (!x. P (INL x)) /\ (!y. P (INR y))`,
  EQ_TAC THENL [SIMP_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC sum_INDUCT THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* num and prim_rec (HOL4 src/num/theories).  HOL4 measure and WF_measure   *)
(* are HOL Light's MEASURE and WF_MEASURE (wf.ml).                           *)
(* ------------------------------------------------------------------------- *)

let INV_SUC = prove
 (`!m n. (SUC m = SUC n) ==> (m = n)`,
  REWRITE_TAC[SUC_INJ]);;

let LESS_REFL = LT_REFL;;

let LESS_NOT_EQ = LT_IMP_NE;;

let LESS_SUC = prove
 (`!m n. (m < n) ==> (m < SUC n)`,
  ARITH_TAC);;

let LESS_LEMMA1 = prove
 (`!m n. (m < SUC n) ==> (m = n) \/ (m < n)`,
  ARITH_TAC);;

let LESS_THM = prove
 (`!m n. m < SUC n <=> (m = n) \/ (m < n)`,
  ARITH_TAC);;

let PRE_DEF = prove
 (`PRE m = (if (m = 0) then 0 else @n. m = SUC n)`,
  STRUCT_CASES_TAC (SPEC `m:num` num_CASES) THEN
  REWRITE_TAC[PRE; NOT_SUC; SUC_INJ] THEN MESON_TAC[]);;

let measure_thm = measure_THM;;

(* basicSize: pair_size is the kit's (pair_size, pair_size_THM) *)

let pair_size_def = pair_size_THM;;
(* ------------------------------------------------------------------------- *)
(* option (HOL4 src/coretypes/optionScript.sml).  The constants are in       *)
(* vocab.ml (THE_DEF, IS_SOME_DEF, IS_NONE_DEF, OPTION_MAP_DEF, ...), the    *)
(* case constant option_CASE and option_case_eq in the kit.  HOL4 () is one. *)
(* ------------------------------------------------------------------------- *)

let SOME_11 = option_INJ;;

let NOT_SOME_NONE = option_DISTINCT;;

let NOT_NONE_SOME = prove
 (`!x:A. ~(NONE = SOME x)`,
  REWRITE_TAC[option_DISTINCT]);;

let option_nchotomy = prove
 (`!opt:A option. (opt = NONE) \/ ?x. opt = SOME x`,
  MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;

let option_CASES = prove
 (`!opt:A option. (?x. opt = SOME x) \/ (opt = NONE)`,
  MESON_TAC[option_nchotomy]);;

let FORALL_OPTION = FORALL_OPTION_THM;;

let EXISTS_OPTION = prove
 (`(?opt:A option. P opt) <=> P NONE \/ ?x. P (SOME x)`,
  MESON_TAC[option_nchotomy]);;

let OPTREL_def = OPTREL_DEF;;

let some_def = some_DEF;;

let OPTION_BIND_def = OPTION_BIND_DEF;;

let OPTION_CHOICE_def = OPTION_CHOICE_DEF;;

let OPTION_GUARD_def = prove
 (`(OPTION_GUARD T = SOME one) /\ (OPTION_GUARD F = NONE)`,
  REWRITE_TAC[OPTION_GUARD_DEF]);;

let OPTION_GUARD_COND = OPTION_GUARD_DEF;;

let IS_SOME_EXISTS = prove
 (`!opt:A option. IS_SOME opt <=> ?x. opt = SOME x`,
  MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[IS_SOME_DEF; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let IS_SOME_EQ_NOT_NONE = prove
 (`!x:A option. IS_SOME x <=> ~(x = NONE)`,
  MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[IS_SOME_DEF; option_DISTINCT]);;

let IS_NONE_EQ_NONE = prove
 (`!x:A option. IS_NONE x <=> (x = NONE)`,
  MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[IS_NONE_DEF; option_DISTINCT]);;

let NOT_IS_SOME_EQ_NONE = prove
 (`!x:A option. ~(IS_SOME x) <=> (x = NONE)`,
  MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[IS_SOME_DEF; option_DISTINCT]);;

let option_case_ID = prove
 (`!x:A option. option_CASE x NONE SOME = x`,
  MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[option_CASE]);;

let option_case_SOME_ID = prove
 (`!x:A option. (option_CASE x x SOME = x)`,
  MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[option_CASE]);;

let option_CLAUSES = prove
 (`(!x y:A. (SOME x = SOME y) <=> (x = y)) /\
   (!x:A. THE (SOME x) = x) /\
   (!x:A. ~(NONE = SOME x)) /\
   (!x:A. ~(SOME x = NONE)) /\
   (!x:A. IS_SOME (SOME x) <=> T) /\
   (IS_SOME (NONE:A option) <=> F) /\
   (!x:A option. IS_NONE x <=> (x = NONE)) /\
   (!x:A option. ~(IS_SOME x) <=> (x = NONE)) /\
   (!x:A option. IS_SOME x ==> (SOME (THE x) = x)) /\
   (!x:A option. option_CASE x NONE SOME = x) /\
   (!x:A option. option_CASE x x SOME = x) /\
   (!x:A option e (f:A->B). IS_NONE x ==> (option_CASE x e f = e)) /\
   (!x:A option e (f:A->B). IS_SOME x ==> (option_CASE x e f = f (THE x))) /\
   (!x:A option e. IS_SOME x ==> (option_CASE x e SOME = x)) /\
   (!(v:B) (f:A->B). option_CASE NONE v f = v) /\
   (!(v:B) (f:A->B) x. option_CASE (SOME x) v f = f x) /\
   (!(f:A->B) x. OPTION_MAP f (SOME x) = SOME (f x)) /\
   (!(f:A->B). OPTION_MAP f NONE = NONE) /\
   (OPTION_JOIN (NONE:(A option) option) = NONE) /\
   (!x:A option. OPTION_JOIN (SOME x) = x)`,
  REWRITE_TAC[option_INJ; option_DISTINCT; THE_DEF; IS_SOME_DEF; IS_NONE_DEF;
              option_CASE; OPTION_MAP_DEF; OPTION_JOIN_DEF] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; THE_DEF; IS_SOME_DEF; IS_NONE_DEF;
              option_CASE]);;

let option_case_compute = prove
 (`option_CASE (x:A option) (e:B) f = if IS_SOME x then f (THE x) else e`,
  STRUCT_CASES_TAC (ISPEC `x:A option` option_nchotomy) THEN
  REWRITE_TAC[option_CASE; IS_SOME_DEF; THE_DEF]);;

let option_case_cong = prove
 (`!M M' (v:B) v' (f:A->B) f'.
     (M = M') /\ ((M' = NONE) ==> (v = v')) /\
     (!x. (M' = SOME x) ==> (f x = f' x))
     ==> (option_CASE M v f = option_CASE M' v' f')`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `M':A option` option_nchotomy) THEN
  SIMP_TAC[option_CASE; option_DISTINCT; option_INJ]);;

let OPTION_MAP_EQ_SOME = prove
 (`!(f:A->B) (x:A option) y. (OPTION_MAP f x = SOME y) <=> ?z. (x = SOME z) /\ (y = f z)`,
  GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let OPTION_MAP_EQ_NONE = prove
 (`!(f:A->B) x. (OPTION_MAP f x = NONE) <=> (x = NONE)`,
  GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT]);;

let OPTION_MAP_EQ_NONE_both_ways = prove
 (`((OPTION_MAP (f:A->B) x = NONE) <=> (x = NONE)) /\
   ((NONE = OPTION_MAP f x) <=> (x = NONE))`,
  MESON_TAC[OPTION_MAP_EQ_NONE]);;

let OPTION_MAP_id = prove
 (`(OPTION_MAP I (x:A option) = x) /\ (OPTION_MAP (\x. x) x = x)`,
  STRUCT_CASES_TAC (ISPEC `x:A option` option_nchotomy) THEN
  REWRITE_TAC[OPTION_MAP_DEF; I_THM]);;

let OPTION_MAP_COMPOSE = prove
 (`OPTION_MAP (f:B->C) (OPTION_MAP (g:A->B) (x:A option)) = OPTION_MAP (f o g) x`,
  STRUCT_CASES_TAC (ISPEC `x:A option` option_nchotomy) THEN
  REWRITE_TAC[OPTION_MAP_DEF; o_THM]);;

let OPTION_MAP_CASE = prove
 (`OPTION_MAP (f:A->B) (x:A option) = option_CASE x NONE (SOME o f)`,
  STRUCT_CASES_TAC (ISPEC `x:A option` option_nchotomy) THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_CASE; o_THM]);;

let OPTION_MAP_CONG = prove
 (`!opt1 opt2 (f1:A->B) f2.
     (opt1 = opt2) /\ (!x. (opt2 = SOME x) ==> (f1 x = f2 x))
     ==> (OPTION_MAP f1 opt1 = OPTION_MAP f2 opt2)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `opt2:A option` option_nchotomy) THEN
  SIMP_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ]);;

let IS_SOME_MAP = prove
 (`IS_SOME (OPTION_MAP (f:A->B) x) = IS_SOME (x:A option)`,
  STRUCT_CASES_TAC (ISPEC `x:A option` option_nchotomy) THEN
  REWRITE_TAC[OPTION_MAP_DEF; IS_SOME_DEF]);;

let OPTION_JOIN_EQ_SOME = prove
 (`!(x:(A option) option) y. (OPTION_JOIN x = SOME y) <=> (x = SOME (SOME y))`,
  MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[OPTION_JOIN_DEF; option_DISTINCT; option_INJ]);;

let OPTION_MAP2_THM = prove
 (`(OPTION_MAP2 (f:A->B->C) (SOME x) (SOME y) = SOME (f x y)) /\
   (OPTION_MAP2 f (SOME x) NONE = NONE) /\
   (OPTION_MAP2 f NONE (SOME y) = NONE) /\
   (OPTION_MAP2 f NONE NONE = NONE)`,
  REWRITE_TAC[OPTION_MAP2_DEF; IS_SOME_DEF; THE_DEF]);;

let OPTION_MAP2_NONE = prove
 (`(OPTION_MAP2 (f:A->B->C) (o1:A option) (o2:B option) = NONE) <=>
   (o1 = NONE) \/ (o2 = NONE)`,
  STRUCT_CASES_TAC (ISPEC `o1:A option` option_nchotomy) THEN
  STRUCT_CASES_TAC (ISPEC `o2:B option` option_nchotomy) THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_DISTINCT]);;

let OPTION_MAP2_SOME = prove
 (`(OPTION_MAP2 (f:A->B->C) (o1:A option) (o2:B option) = SOME v) <=>
   (?x1 x2. (o1 = SOME x1) /\ (o2 = SOME x2) /\ (v = f x1 x2))`,
  STRUCT_CASES_TAC (ISPEC `o1:A option` option_nchotomy) THEN
  STRUCT_CASES_TAC (ISPEC `o2:B option` option_nchotomy) THEN
  REWRITE_TAC[OPTION_MAP2_THM; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let OPTION_MAP2_cong = prove
 (`!x1 x2 y1 y2 (f1:A->B->C) f2.
     (x1 = x2) /\ (y1 = y2) /\
     (!x y. (x2 = SOME x) /\ (y2 = SOME y) ==> (f1 x y = f2 x y))
     ==> (OPTION_MAP2 f1 x1 y1 = OPTION_MAP2 f2 x2 y2)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `x2:A option` option_nchotomy) THEN
  STRUCT_CASES_TAC (ISPEC `y2:B option` option_nchotomy) THEN
  SIMP_TAC[OPTION_MAP2_THM; option_DISTINCT; option_INJ]);;

let OPTION_BIND_SOME = prove
 (`!opt:A option. OPTION_BIND opt SOME = opt`,
  MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[OPTION_BIND_DEF]);;

let OPTION_BIND_EQUALS_OPTION = prove
 (`((OPTION_BIND (p:A option) (f:A->B option) = NONE) <=>
      (p = NONE) \/ ?x. (p = SOME x) /\ (f x = NONE)) /\
   ((OPTION_BIND p f = SOME y) <=> ?x. (p = SOME x) /\ (f x = SOME y))`,
  STRUCT_CASES_TAC (ISPEC `p:A option` option_nchotomy) THEN
  REWRITE_TAC[OPTION_BIND_DEF; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let OPTION_BIND_cong = prove
 (`!o1 o2 (f1:A->B option) f2.
     (o1 = o2) /\ (!x. (o2 = SOME x) ==> (f1 x = f2 x))
     ==> (OPTION_BIND o1 f1 = OPTION_BIND o2 f2)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `o2:A option` option_nchotomy) THEN
  SIMP_TAC[OPTION_BIND_DEF; option_DISTINCT; option_INJ]);;

let IS_SOME_BIND = prove
 (`IS_SOME (OPTION_BIND (x:A option) (g:A->B option)) ==> IS_SOME x`,
  STRUCT_CASES_TAC (ISPEC `x:A option` option_nchotomy) THEN
  REWRITE_TAC[OPTION_BIND_DEF; IS_SOME_DEF]);;

let OPTION_IGNORE_BIND_thm = prove
 (`(OPTION_IGNORE_BIND (NONE:A option) (m:B option) = NONE) /\
   (OPTION_IGNORE_BIND (SOME (v:A)) (m:B option) = m)`,
  REWRITE_TAC[OPTION_IGNORE_BIND_DEF; OPTION_BIND_DEF]);;

let OPTION_IGNORE_BIND_EQUALS_OPTION = prove
 (`((OPTION_IGNORE_BIND (m1:A option) (m2:B option) = NONE) <=>
      (m1 = NONE) \/ (m2 = NONE)) /\
   ((OPTION_IGNORE_BIND m1 m2 = SOME y) <=> ?x. (m1 = SOME x) /\ (m2 = SOME y))`,
  STRUCT_CASES_TAC (ISPEC `m1:A option` option_nchotomy) THEN
  REWRITE_TAC[OPTION_IGNORE_BIND_thm; option_DISTINCT; option_INJ] THEN
  MESON_TAC[]);;

let OPTION_GUARD_EQ_THM = prove
 (`((OPTION_GUARD b = SOME one) <=> b) /\ ((OPTION_GUARD b = NONE) <=> ~b)`,
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[OPTION_GUARD_def; option_DISTINCT]);;

let OPTION_CHOICE_EQ_NONE = prove
 (`(OPTION_CHOICE (m1:A option) m2 = NONE) <=> (m1 = NONE) /\ (m2 = NONE)`,
  STRUCT_CASES_TAC (ISPEC `m1:A option` option_nchotomy) THEN
  REWRITE_TAC[OPTION_CHOICE_DEF; option_DISTINCT]);;

let OPTION_CHOICE_NONE = prove
 (`OPTION_CHOICE (m1:A option) NONE = m1`,
  STRUCT_CASES_TAC (ISPEC `m1:A option` option_nchotomy) THEN
  REWRITE_TAC[OPTION_CHOICE_DEF]);;

let IF_EQUALS_OPTION = prove
 (`(((if P then SOME (x:A) else NONE) = NONE) <=> ~P) /\
   (((if P then NONE else SOME (x:A)) = NONE) <=> P) /\
   (((if P then SOME x else NONE) = SOME y) <=> P /\ (x = y)) /\
   (((if P then NONE else SOME x) = SOME y) <=> ~P /\ (x = y))`,
  BOOL_CASES_TAC `P:bool` THEN REWRITE_TAC[option_DISTINCT; option_INJ]);;

let if_option_eq = prove
 (`(((if P then X else SOME (x:A)) = NONE) <=> P /\ (X = NONE)) /\
   (((if P then SOME x else X) = NONE) <=> ~P /\ (X = NONE)) /\
   (((if P then X else NONE) = SOME x) <=> P /\ (X = SOME x)) /\
   (((if P then NONE else X) = SOME x) <=> ~P /\ (X = SOME x))`,
  BOOL_CASES_TAC `P:bool` THEN REWRITE_TAC[option_DISTINCT; option_INJ]);;

let OPTREL_THM = prove
 (`(OPTREL (R:A->B->bool) (SOME x) NONE <=> F) /\
   (OPTREL R NONE (SOME y) <=> F) /\
   (OPTREL R NONE NONE <=> T) /\
   (OPTREL R (SOME x) (SOME y) <=> R x y)`,
  REWRITE_TAC[OPTREL_DEF; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let OPTREL_SOME = prove
 (`(!(R:A->B->bool) x y. OPTREL R (SOME x) y <=> ?z. (y = SOME z) /\ R x z) /\
   (!(R:A->B->bool) x y. OPTREL R x (SOME y) <=> ?z. (x = SOME z) /\ R z y)`,
  REWRITE_TAC[OPTREL_DEF; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let OPTREL_NONE = prove
 (`(OPTREL (R:A->B->bool) NONE y <=> (y = NONE)) /\
   (OPTREL R x NONE <=> (x = NONE))`,
  REWRITE_TAC[OPTREL_DEF; option_DISTINCT] THEN MESON_TAC[]);;

let OPTREL_MONO = prove
 (`(!(x:A) (y:B). P x y ==> Q x y) ==> (OPTREL P x y ==> OPTREL Q x y)`,
  REWRITE_TAC[OPTREL_DEF] THEN MESON_TAC[]);;

let OPTREL_eq = prove
 (`OPTREL (=) = ((=):A option->A option->bool)`,
  REWRITE_TAC[FUN_EQ_THM] THEN
  MATCH_MP_TAC option_INDUCT THEN CONJ_TAC THENL [ALL_TAC; GEN_TAC] THEN
  MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[OPTREL_THM; option_DISTINCT; option_INJ]);;

let OPTREL_refl = prove
 (`(!x:A. R x x) ==> !x. OPTREL R x x`,
  DISCH_TAC THEN MATCH_MP_TAC option_INDUCT THEN ASM_REWRITE_TAC[OPTREL_THM]);;

let OPTION_ALL_def = new_recursive_definition option_RECURSION
  `(OPTION_ALL (P:A->bool) NONE <=> T) /\ (OPTION_ALL P (SOME x) <=> P x)`;;

let OPTION_ALL_MONO = prove
 (`(!x:A. P x ==> P' x) ==> OPTION_ALL P opt ==> OPTION_ALL P' opt`,
  STRUCT_CASES_TAC (ISPEC `opt:A option` option_nchotomy) THEN
  REWRITE_TAC[OPTION_ALL_def] THEN MESON_TAC[]);;

let some_intro = prove
 (`(!x:A. P x ==> Q (SOME x)) /\ ((!x. ~P x) ==> Q NONE) ==> Q ((some) P)`,
  REWRITE_TAC[some_DEF] THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let some_elim = prove
 (`Q ((some) (P:A->bool)) ==> (?x. P x /\ Q (SOME x)) \/ ((!x. ~P x) /\ Q NONE)`,
  REWRITE_TAC[some_DEF] THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let some_F = prove
 (`(some x:A. F) = NONE`,
  REWRITE_TAC[some_DEF]);;

let some_EQ = prove
 (`((some x:A. x = y) = SOME y) /\ ((some x:A. y = x) = SOME y)`,
  REWRITE_TAC[some_DEF] THEN MESON_TAC[]);;

let BASICAUX_option3_cases = prove
 (`!(o1:(A#B#C)option). o1 = NONE \/ ?x y z. o1 = SOME (x,y,z)`,
  MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  GEN_TAC THEN MAP_EVERY EXISTS_TAC [`FST (a:A#B#C)`; `FST (SND (a:A#B#C))`;
    `SND (SND (a:A#B#C))`] THEN REWRITE_TAC[PAIR]);;

let BASICAUX_option_CASE_cong = prove
 (`!(a:B option) b (n1:C) n2 f.
     a = b /\ (b = NONE ==> n1 = n2) ==> option_CASE a n1 f = option_CASE b n2 f`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `b:B option` (cases "option")) THEN
  REWRITE_TAC[option_CASE; option_DISTINCT] THEN MESON_TAC[option_CASE]);;

let BASICAUX_some_SOME = prove
 (`!P (a:A). (some) P = SOME a ==> P a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[some_DEF] THEN COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC[]);;

let BASICAUX_some_NONE = prove
 (`!P:A->bool. (some) P = NONE <=> !x. ~P x`,
  GEN_TAC THEN REWRITE_TAC[some_DEF] THEN COND_CASES_TAC THEN
  ASM_MESON_TAC[option_DISTINCT]);;
(* ------------------------------------------------------------------------- *)
(* pair (HOL4 src/coretypes/pairScript.sml).  HOL Light's pair.ml has FST,   *)
(* SND, PAIR, PAIR_EQ, CURRY_DEF, UNCURRY_DEF; HOL4 ## is vocab.ml's ##,      *)
(* LEX and its LEX_DEF (FST/SND form) are the kit's; paired lambdas are      *)
(* HOL Light's (GABS, not UNCURRY).                                          *)
(* ------------------------------------------------------------------------- *)

let FORALL_PROD = FORALL_PAIR_THM;;

let EXISTS_PROD = EXISTS_PAIR_THM;;

let LAMBDA_PROD = LAMBDA_PAIR_THM;;

let pair_CASES = PAIR_SURJECTIVE;;

let BASICAUX_TUPLE3 = prove
 (`!p:A#B#C. ?a b c. p = (a,b,c)`,
  MESON_TAC[PAIR_SURJECTIVE]);;

let BASICAUX_TUPLE4 = prove
 (`!p:A#B#C#D. ?a b c d. p = (a,b,c,d)`,
  MESON_TAC[PAIR_SURJECTIVE]);;

let BASICAUX_TUPLE5 = prove
 (`!p:A#B#C#D#E. ?a b c d e. p = (a,b,c,d,e)`,
  MESON_TAC[PAIR_SURJECTIVE]);;

let ABS_PAIR_THM = PAIR_SURJECTIVE;;

let LEX_DEF_THM = LEX_THM;;

(* HOL4 WF_LEX; HOL Light's WF_LEX writes the order inline *)

let pair_WF_LEX = WF_LEX_HOL4;;

(* HOL4 LEX_DEF, with HOL Light paired lambdas (the kit's LEX_DEF uses FST
   and SND) *)

let pair_LEX_DEF = prove
 (`(R1:A->A->bool) LEX (R2:B->B->bool) =
   \(s,t) (u,v). R1 s u \/ (s = u) /\ R2 t v`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; LEX_THM]);;

let UNCURRY = prove
 (`UNCURRY (f:A->B->C) (v:A#B) = f (FST v) (SND v)`,
  STRUCT_CASES_TAC (ISPEC `v:A#B` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[UNCURRY_DEF; FST; SND]);;

let UNCURRY_VAR = UNCURRY;;

let ELIM_UNCURRY = prove
 (`!f:A->B->C. UNCURRY f = \x. f (FST x) (SND x)`,
  REWRITE_TAC[FUN_EQ_THM; UNCURRY]);;

let UNCURRY_EQ = prove
 (`(UNCURRY (f:A->B->C) x = y) <=> ?a b. (x = (a,b)) /\ (f a b = y)`,
  STRUCT_CASES_TAC (ISPEC `x:A#B` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[UNCURRY_DEF; PAIR_EQ] THEN MESON_TAC[]);;

let UNCURRY_CONST = prove
 (`UNCURRY (\x1 x2. (y:C)) (x:A#B) = y`,
  REWRITE_TAC[UNCURRY]);;

let CURRY_UNCURRY_THM = prove
 (`!f:A->B->C. CURRY (UNCURRY f) = f`,
  REWRITE_TAC[FUN_EQ_THM; CURRY_DEF; UNCURRY_DEF]);;

let UNCURRY_CURRY_THM = prove
 (`!f:A#B->C. UNCURRY (CURRY f) = f`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; CURRY_DEF; UNCURRY_DEF]);;

let PAIR_FST_SND_EQ = prove
 (`!(p:A#B) q. (p = q) <=> (FST p = FST q) /\ (SND p = SND q)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; FST; SND]);;

let FST_EQ_EQUIV = prove
 (`(FST p = (x:A)) <=> ?y:B. p = (x,y)`,
  STRUCT_CASES_TAC (ISPEC `p:A#B` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[FST; PAIR_EQ] THEN MESON_TAC[]);;

let SND_EQ_EQUIV = prove
 (`(SND p = (y:B)) <=> ?x:A. p = (x,y)`,
  STRUCT_CASES_TAC (ISPEC `p:A#B` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[SND; PAIR_EQ] THEN MESON_TAC[]);;

let PAIR_MAP = prove
 (`((f:A->C) ## (g:B->D)) p = (f (FST p), g (SND p))`,
  REWRITE_TAC[PAIR_MAP_DEF]);;

let FST_PAIR_MAP = prove
 (`!p (f:A->C) (g:B->D). FST ((f ## g) p) = f (FST p)`,
  REWRITE_TAC[PAIR_MAP_DEF; FST]);;

let SND_PAIR_MAP = prove
 (`!p (f:A->C) (g:B->D). SND ((f ## g) p) = g (SND p)`,
  REWRITE_TAC[PAIR_MAP_DEF; SND]);;

let pair_map_eq = prove
 (`(((f:A->C) ## (g:B->D)) p = (w,v)) <=>
   (?x y. (p = (x,y)) /\ (w = f x) /\ (v = g y))`,
  STRUCT_CASES_TAC (ISPEC `p:A#B` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[PAIR_MAP_THM; PAIR_EQ] THEN MESON_TAC[]);;

let PAIR_MAP_I = prove
 (`((I:A->A) ## (I:B->B)) = I`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; PAIR_MAP_THM; I_THM]);;

let o_UNCURRY_R = prove
 (`(f:C->D) o UNCURRY (g:A->B->C) = UNCURRY ((o) f o g)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; UNCURRY_DEF; o_THM]);;

let C_UNCURRY_L = prove
 (`flip (UNCURRY (f:A->B->C->D)) x = UNCURRY (flip (flip o f) x)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; UNCURRY_DEF; o_THM; flip_DEF]);;

(* HOL4 FORALL_UNCURRY; HOL Light's FORALL_UNCURRY is another theorem *)

let pair_FORALL_UNCURRY = prove
 (`(!) (UNCURRY (f:A->B->bool)) = (!) ((!) o f)`,
  CONV_TAC (BINOP_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX)))) THEN
  REWRITE_TAC[FORALL_PAIR_THM; UNCURRY_DEF; o_THM] THEN
  REWRITE_TAC[ETA_AX]);;

let pair_CASE_def = prove
 (`pair_CASE (p:A#B) (f:A->B->C) = f (FST p) (SND p)`,
  STRUCT_CASES_TAC (ISPEC `p:A#B` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[pair_CASE; FST; SND]);;

let pair_CASE_UNCURRY = prove
 (`(pair_CASE:A#B->(A->B->C)->C) = flip UNCURRY`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; pair_CASE; flip_DEF; UNCURRY_DEF]);;

let UNCURRY_pair_CASE = prove
 (`(UNCURRY:(A->B->C)->A#B->C) = flip pair_CASE`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; pair_CASE; flip_DEF; UNCURRY_DEF]);;

(* RPROD, written ### as in HOL4 *)

let RPROD_DEF = new_definition
  `RPROD (R1:A->B->bool) (R2:C->D->bool) = \(s,t) (u,v). R1 s u /\ R2 t v`;;

parse_as_infix("###",(20,"right"));;
override_interface("###",`RPROD:(A->B->bool)->(C->D->bool)->A#C->B#D->bool`);;

let PAIR_REL = RPROD_DEF;;

let PAIR_REL_THM = prove
 (`((R1:A->B->bool) ### (R2:C->D->bool)) (a,b) (c,d) <=> R1 a c /\ R2 b d`,
  REWRITE_TAC[RPROD_DEF] THEN CONV_TAC (DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[]);;

let PAIR_REL_EQ = prove
 (`(((=):A->A->bool) ### ((=):B->B->bool)) = (=)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; PAIR_REL_THM; PAIR_EQ]);;

let transitive_LEX = prove
 (`transitive (R1:A->A->bool) /\ transitive (R2:B->B->bool)
   ==> transitive (R1 LEX R2)`,
  REWRITE_TAC[transitive_DEF; FORALL_PAIR_THM; LEX_THM] THEN MESON_TAC[]);;

let reflexive_LEX = prove
 (`reflexive ((R1:A->A->bool) LEX (R2:B->B->bool)) <=>
   reflexive R1 \/ reflexive R2`,
  REWRITE_TAC[reflexive_DEF; FORALL_PAIR_THM; LEX_THM] THEN MESON_TAC[]);;

let symmetric_LEX = prove
 (`symmetric (R1:A->A->bool) /\ symmetric (R2:B->B->bool)
   ==> symmetric (R1 LEX R2)`,
  REWRITE_TAC[symmetric_DEF; FORALL_PAIR_THM; LEX_THM] THEN MESON_TAC[]);;

let total_LEX = prove
 (`total (R1:A->A->bool) /\ total (R2:B->B->bool) ==> total (R1 LEX R2)`,
  REWRITE_TAC[total_DEF; FORALL_PAIR_THM; LEX_THM] THEN MESON_TAC[]);;
(* ------------------------------------------------------------------------- *)
(* arithmetic (HOL4 src/num/theories/arithmeticScript.sml).  HOL4 FUNPOW f n *)
(* x is HOL Light's ITER n f x (Library/iter.ml).  HOL4 names that HOL Light *)
(* uses for other statements get the prefix arithmetic_.                     *)
(* ------------------------------------------------------------------------- *)

let NOT_LESS = NOT_LT;;
let ADD_COMM = ADD_SYM;;
let MULT_COMM = MULT_SYM;;
let LESS_EQ_EXISTS = LE_EXISTS;;
let LESS_EQ_TRANS = LE_TRANS;;
let LESS_LESS_EQ_TRANS = LTE_TRANS;;
let EVEN_MOD2 = EVEN_MOD;;
let LESS_EQ_LESS_TRANS = LET_TRANS;;
let LESS_TRANS = LT_TRANS;;
let LESS_EQ_CASES = LE_CASES;;
let LESS_OR_EQ = LE_LT;;
let NOT_LESS_EQUAL = NOT_LE;;
let LESS_DIV_EQ_ZERO = DIV_LT;;
let LESS_IMP_LESS_OR_EQ = LT_IMP_LE;;
let ZERO_LESS_EQ = LE_0;;
let LESS_EQ_REFL = LE_REFL;;
let ZERO_LESS_MULT = LT_MULT;;
let LESS_EQ_ADD = LE_ADD;;
let LESS_EQ_ANTISYM = LTE_ANTISYM;;
let LESS_EQ_LESS_EQ_MONO = LE_ADD2;;
let binary_induct = BINARY_INDUCT;;
let ZERO_EXP = EXP_ZERO;;
let DIV2_def = DIV2_DEF;;

(* HOL4 LEFT_ADD_DISTRIB, LEFT_SUB_DISTRIB and EXP_ADD quantify their
   variables in another order than HOL Light's theorems of these names
   (identical as rewrites; these copies are for SPECL) *)

let arithmetic_LEFT_ADD_DISTRIB = prove
 (`!m n p. p * (m + n) = (p * m) + (p * n)`,
  REWRITE_TAC[LEFT_ADD_DISTRIB]);;

let arithmetic_LEFT_SUB_DISTRIB = prove
 (`!m n p. p * (m - n) = (p * m) - (p * n)`,
  REWRITE_TAC[LEFT_SUB_DISTRIB]);;

let arithmetic_EXP_ADD = prove
 (`!p q n. n EXP (p + q) = (n EXP p) * (n EXP q)`,
  REWRITE_TAC[EXP_ADD]);;

let MAX_DEF = prove
 (`MAX m n = if m < n then n else m`,
  REWRITE_TAC[MAX] THEN ARITH_TAC);;

let MIN_DEF = prove
 (`MIN m n = if m < n then m else n`,
  REWRITE_TAC[MIN] THEN ARITH_TAC);;

let GREATER_EQ = prove
 (`!n m. n >= m <=> m <= n`,
  REWRITE_TAC[GE]);;

let GREATER_DEF = prove
 (`!m n. m > n <=> n < m`,
  REWRITE_TAC[GT]);;

let ODD_EVEN = prove
 (`!n. ODD n <=> ~(EVEN n)`,
  REWRITE_TAC[NOT_EVEN]);;

let EVEN_ODD = prove
 (`!n. EVEN n <=> ~ODD n`,
  REWRITE_TAC[NOT_ODD]);;

let NOT_ZERO_LT_ZERO = prove
 (`!n. ~(n = 0) <=> 0 < n`,
  ARITH_TAC);;

let NOT_ZERO = NOT_ZERO_LT_ZERO;;

let LESS_EQ = prove
 (`!m n. (m < n) <=> (SUC m <= n)`,
  ARITH_TAC);;

let LESS_OR = prove
 (`!m n. m < n ==> SUC m <= n`,
  ARITH_TAC);;

let PRE_SUB1 = prove
 (`!m. PRE m = m - 1`,
  ARITH_TAC);;

let SUC_ONE_ADD = prove
 (`!n. SUC n = 1 + n`,
  ARITH_TAC);;

let SUC_ADD_SYM = prove
 (`!m n. SUC (m + n) = (SUC n) + m`,
  ARITH_TAC);;

let SUC_NOT = prove
 (`!n. ~(0 = SUC n)`,
  ARITH_TAC);;

(* HOL4 ADD_SUC; HOL Light's ADD_SUC is the other orientation *)

let arithmetic_ADD_SUC = prove
 (`!m n. SUC (m + n) = (m + SUC n)`,
  ARITH_TAC);;

let NOT_GREATER = prove
 (`!m n. ~(m > n) <=> (m <= n)`,
  ARITH_TAC);;

let NOT_GREATER_EQ = prove
 (`!m n. ~(m >= n) <=> SUC m <= n`,
  ARITH_TAC);;

let SUB_PLUS = prove
 (`!a b c. a - (b + c) = (a - b) - c`,
  ARITH_TAC);;

let SUB_LEFT_ADD = prove
 (`!m n p. m + (n - p) = (if (n <= p) then m else (m + n) - p)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let SUB_LEFT_SUB = prove
 (`!m n p. m - (n - p) = (if (n <= p) then m else (m + p) - n)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let SUB_RIGHT_ADD = prove
 (`!m n p. (m - n) + p = (if (m <= n) then p else (m + p) - n)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let SUB_RIGHT_EQ = prove
 (`!m n p. (m - n = p) <=> (m = n + p) \/ (m <= n /\ p <= 0)`,
  ARITH_TAC);;

let SUB_RIGHT_SUB = prove
 (`!m n p. (m - n) - p = m - (n + p)`,
  ARITH_TAC);;

let SUB_LEFT_LESS = prove
 (`!m n p. (m < (n - p)) <=> ((m + p) < n)`,
  ARITH_TAC);;

let SUB_LEFT_LESS_EQ = prove
 (`!m n p. m <= (n - p) <=> m + p <= n \/ m <= 0`,
  ARITH_TAC);;

let SUB_SUB = prove
 (`!b c. (c <= b) ==> !a. ((a - (b - c)) = ((a + c) - b))`,
  ARITH_TAC);;

let LESS_EQ_ADD_SUB = prove
 (`!c b. (c <= b) ==> !a. (((a + b) - c) = (a + (b - c)))`,
  ARITH_TAC);;

let SUB_CANCEL = prove
 (`!p n m. ((n <= p) /\ (m <= p)) ==> (((p - n) = (p - m)) <=> (n = m))`,
  ARITH_TAC);;

let SUB_LESS = prove
 (`!m n. 0 < n /\ n <= m ==> m - n < m`,
  ARITH_TAC);;

let LESS_SUB_ADD_LESS = prove
 (`!n m i. (i < (n - m)) ==> ((i + m) < n)`,
  ARITH_TAC);;

let LESS_NOT_SUC = prove
 (`!m n. (m < n) /\ ~(n = SUC m) ==> SUC m < n`,
  ARITH_TAC);;

let LESS_SUC_EQ_COR = prove
 (`!m n. ((m < n) /\ (~(SUC m = n))) ==> (SUC m < n)`,
  ARITH_TAC);;

let LESS_CASES_IMP = prove
 (`!m n. ~(m < n) /\ ~(m = n) ==> (n < m)`,
  ARITH_TAC);;

let LESS_LESS_CASES = prove
 (`!m n. (m = n) \/ (m < n) \/ (n < m)`,
  ARITH_TAC);;

let LE_LT1 = prove
 (`!x y. x <= y <=> x < y + 1`,
  ARITH_TAC);;

let ZERO_LESS_ADD = prove
 (`!m n. 0 < m + n <=> 0 < m \/ 0 < n`,
  ARITH_TAC);;

let LESS_EQUAL_ANTISYM = prove
 (`!n m. n <= m /\ m <= n ==> (n = m)`,
  ARITH_TAC);;

let LESS_MONO_ADD = prove
 (`!m n p. (m < n) ==> (m + p) < (n + p)`,
  ARITH_TAC);;

let LESS_MONO_MULT = prove
 (`!m n p. (m <= n) ==> ((m * p) <= (n * p))`,
  SIMP_TAC[LE_MULT_RCANCEL]);;

let LESS_MONO_MULT2 = prove
 (`!m n i j. m <= i /\ n <= j ==> m * n <= i * j`,
  REWRITE_TAC[LE_MULT2]);;

let LESS_MULT2 = prove
 (`!m n. 0 < m /\ 0 < n ==> 0 < (m * n)`,
  SIMP_TAC[LT_MULT]);;

let LESS_EQ_ADD_EXISTS = prove
 (`!m n. n <= m ==> ?p. p + n = m`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `m - n:num` THEN ASM_ARITH_TAC);;

let LESS_ADD = prove
 (`!m n. n < m ==> ?p. p + n = m`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `m - n:num` THEN ASM_ARITH_TAC);;

let LESS_EQUAL_ADD = prove
 (`!m n. m <= n ==> ?p. n = m + p`,
  MESON_TAC[LE_EXISTS]);;

let LESS_ADD_1 = prove
 (`!m n. (n < m) ==> ?p. m = n + (p + 1)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `m - n - 1` THEN ASM_ARITH_TAC);;

let EXISTS_NUM = prove
 (`!P. (?n. P n) <=> P 0 \/ (?m. P (SUC m))`,
  MESON_TAC[num_CASES]);;

let FORALL_NUM = prove
 (`!P. (!n. P n) <=> P 0 /\ !n. P (SUC n)`,
  MESON_TAC[num_CASES]);;

let MAX_COMM = prove
 (`!m n. MAX m n = MAX n m`,
  ARITH_TAC);;

let MIN_COMM = prove
 (`!m n. MIN m n = MIN n m`,
  ARITH_TAC);;

let MAX_ASSOC = prove
 (`!m n p. MAX m (MAX n p) = MAX (MAX m n) p`,
  ARITH_TAC);;

let MAX_CASES = prove
 (`!m n. (MAX n m = n) \/ (MAX n m = m)`,
  ARITH_TAC);;

let MAX_EQ_0 = prove
 (`(MAX m n = 0) <=> (m = 0) /\ (n = 0)`,
  ARITH_TAC);;

let MIN_EQ_0 = prove
 (`(MIN m n = 0) <=> (m = 0) \/ (n = 0)`,
  ARITH_TAC);;

let LT1_EQ0 = prove
 (`x < 1 <=> (x = 0)`,
  ARITH_TAC);;

let NOT_LT_ZERO_EQ_ZERO = prove
 (`!n. ~(0 < n) <=> (n = 0)`,
  ARITH_TAC);;

let SUC_SUB = prove
 (`!a. SUC a - a = 1`,
  ARITH_TAC);;

let MULT_RIGHT_1 = prove
 (`!m. m * 1 = m`,
  REWRITE_TAC[MULT_CLAUSES]);;

(* HOL4 LT_SUC; HOL Light's LT_SUC is SUC m < SUC n <=> m < n *)

let arithmetic_LT_SUC = prove
 (`n < SUC m <=> (n = 0) \/ ?n0. (n = SUC n0) /\ n0 < m`,
  STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[NOT_SUC; SUC_INJ; LT_SUC; LT_0] THEN MESON_TAC[]);;

let arithmetic_LT_MULT_LCANCEL = prove
 (`!m n p. m * n < m * p <=> 0 < m /\ n < p`,
  REWRITE_TAC[LT_MULT_LCANCEL] THEN ARITH_TAC);;

let arithmetic_LT_MULT_RCANCEL = prove
 (`!m n p. m * n < p * n <=> 0 < n /\ m < p`,
  REWRITE_TAC[LT_MULT_RCANCEL] THEN ARITH_TAC);;

let arithmetic_LE_MULT_RCANCEL = prove
 (`!m n p. m * n <= p * n <=> (n = 0) \/ m <= p`,
  REWRITE_TAC[LE_MULT_RCANCEL] THEN ARITH_TAC);;

let arithmetic_EQ_MULT_RCANCEL = prove
 (`!m n p. (n * m = p * m) <=> (m = 0) \/ (n = p)`,
  REWRITE_TAC[EQ_MULT_RCANCEL] THEN ARITH_TAC);;

let MULT_EQ_ID = prove
 (`!m n. ((m * n = n) <=> (m = 1) \/ (n = 0)) /\
         ((n * m = n) <=> (m = 1) \/ (n = 0))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`m:num`; `1`; `n:num`] EQ_MULT_RCANCEL) THEN
  MP_TAC (SPECL [`n:num`; `m:num`; `1`] EQ_MULT_LCANCEL) THEN
  REWRITE_TAC[MULT_CLAUSES] THEN MESON_TAC[]);;

(* exponentiation *)

let arithmetic_EXP_EQ_0 = prove
 (`!n m. (n EXP m = 0) <=> (n = 0) /\ (0 < m)`,
  REWRITE_TAC[EXP_EQ_0] THEN ARITH_TAC);;

let arithmetic_EXP_1 = prove
 (`!n. (1 EXP n = 1) /\ (n EXP 1 = n)`,
  REWRITE_TAC[EXP_ONE; EXP_1]);;

let ZERO_LT_EXP = prove
 (`0 < x EXP y <=> 0 < x \/ (y = 0)`,
  REWRITE_TAC[EXP_LT_0] THEN ARITH_TAC);;

let ONE_LE_EXP = prove
 (`1 <= x EXP y <=> 0 < x \/ (y = 0)`,
  REWRITE_TAC[ARITH_RULE `1 <= a <=> 0 < a`; ZERO_LT_EXP]);;

let ONE_LT_EXP = prove
 (`!x y. 1 < x EXP y <=> 1 < x /\ 0 < y`,
  REPEAT GEN_TAC THEN MP_TAC (SPECL [`x:num`; `0`; `y:num`] LT_EXP) THEN
  REWRITE_TAC[EXP] THEN ARITH_TAC);;

let TWO_LE_EXP = prove
 (`!x y. 2 <= x EXP y <=> 1 < x /\ 0 < y`,
  REWRITE_TAC[ARITH_RULE `2 <= a <=> 1 < a`; ONE_LT_EXP]);;

let EXP_BASE_LE_IFF = prove
 (`b EXP m <= b EXP n <=>
   (b = 0) /\ (n = 0) \/ (b = 0) /\ 0 < m \/ (b = 1) \/ 1 < b /\ m <= n`,
  REWRITE_TAC[LE_EXP] THEN ASM_CASES_TAC `b = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let EXP_BASE_LEQ_MONO_IMP = prove
 (`!n m b. 0 < b /\ m <= n ==> b EXP m <= b EXP n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LE_EXP] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

let EXP_BASE_LT_MONO = prove
 (`!b. 1 < b ==> !n m. b EXP m < b EXP n <=> m < n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LT_EXP] THEN ASM_ARITH_TAC);;

let X_LT_EXP_X = prove
 (`1 < b ==> x < b EXP x`,
  DISCH_TAC THEN MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP x` THEN
  REWRITE_TAC[LT_POW2_REFL] THEN MATCH_MP_TAC EXP_MONO_LE_IMP THEN
  ASM_ARITH_TAC);;

let X_LT_EXP_X_IFF = prove
 (`x < b EXP x <=> 1 < b \/ (x = 0)`,
  EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `b = 0 \/ b = 1 \/ 1 < b` STRIP_ASSUME_TAC THENL
     [ARITH_TAC;
      UNDISCH_TAC `x < b EXP x` THEN ASM_REWRITE_TAC[EXP_ZERO] THEN
      COND_CASES_TAC THEN ASM_ARITH_TAC;
      UNDISCH_TAC `x < b EXP x` THEN ASM_REWRITE_TAC[EXP_ONE] THEN ARITH_TAC;
      ASM_REWRITE_TAC[]];
    STRIP_TAC THEN ASM_SIMP_TAC[X_LT_EXP_X] THEN REWRITE_TAC[EXP] THEN
    ARITH_TAC]);;

(* DIV and MOD: HOL4 states them with 0 < n, HOL Light with ~(n = 0) or
   none *)

let arithmetic_DIVISION = prove
 (`!n. 0 < n ==> !k. (k = k DIV n * n + k MOD n) /\ k MOD n < n`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN MATCH_MP_TAC DIVISION THEN
  ASM_ARITH_TAC);;

let DA = prove
 (`!k n. 0 < n ==> ?r q. (k = (q * n) + r) /\ r < n`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `k MOD n` THEN EXISTS_TAC `k DIV n` THEN
  MATCH_MP_TAC DIVISION THEN ASM_ARITH_TAC);;

let arithmetic_MULT_DIV = prove
 (`!n q. 0 < n ==> ((q * n) DIV n = q)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
  ASM_REWRITE_TAC[ADD_CLAUSES]);;

let MULT_TO_DIV = prove
 (`!m n. 0 < n ==> ((n * m) DIV n = m)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_MULT THEN ASM_ARITH_TAC);;

let arithmetic_DIV_MULT = prove
 (`!n r. r < n ==> !q. (q * n + r) DIV n = q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `r:num` THEN
  ASM_REWRITE_TAC[]);;

let arithmetic_MOD_MULT = prove
 (`!n r. r < n ==> !q. (q * n + r) MOD n = r`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q:num` THEN
  ASM_REWRITE_TAC[]);;

let arithmetic_MOD_EQ_0 = prove
 (`!n. 0 < n ==> !k. ((k * n) MOD n) = 0`,
  REWRITE_TAC[MOD_EQ_0] THEN MESON_TAC[]);;

let MOD_TIMES = prove
 (`!n q r. ((q * n) + r) MOD n = r MOD n`,
  REWRITE_TAC[MOD_MULT_ADD]);;

let MOD_PLUS = prove
 (`!n j k. ((j MOD n) + (k MOD n)) MOD n = (j + k) MOD n`,
  REWRITE_TAC[MOD_ADD_MOD]);;

let MOD_TIMES2 = prove
 (`!n j k. ((j MOD n) * (k MOD n)) MOD n = (j * k) MOD n`,
  REWRITE_TAC[MOD_MULT_MOD2]);;

let LESS_MOD = prove
 (`!n k. k < n ==> (k MOD n = k)`,
  SIMP_TAC[MOD_LT]);;

let MOD_LESS = prove
 (`!m n. 0 < n ==> m MOD n < n`,
  REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC);;

let MOD_LESS_EQ = prove
 (`0 < y ==> x MOD y <= x`,
  REWRITE_TAC[MOD_LE]);;

let DIV_LESS_EQ = prove
 (`!n. 0 < n ==> !k. (k DIV n) <= k`,
  REWRITE_TAC[DIV_LE]);;

let DIV_LE_MONOTONE = prove
 (`!n x y. 0 < n /\ x <= y ==> x DIV n <= y DIV n`,
  SIMP_TAC[DIV_MONO]);;

let ZERO_DIV = prove
 (`!n. 0 < n ==> (0 DIV n = 0)`,
  REWRITE_TAC[DIV_0]);;

let ZERO_MOD = prove
 (`!n. 0 < n ==> (0 MOD n = 0)`,
  REWRITE_TAC[MOD_0]);;

let MOD_ID = MOD_REFL;;

let DIV_ID = prove
 (`!n. 0 < n ==> (n DIV n = 1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_REFL THEN ASM_ARITH_TAC);;

(* HOL4 DIV_0 and MOD_0 (both [simp]) have two conjuncts *)

let arithmetic_DIV_0 = prove
 (`(k DIV 0 = 0) /\ (0 DIV n = 0)`,
  REWRITE_TAC[DIV_ZERO; DIV_0]);;

let arithmetic_MOD_0 = prove
 (`(k MOD 0 = k) /\ (0 MOD n = 0)`,
  REWRITE_TAC[MOD_ZERO; MOD_0]);;

let X_MOD_Y_EQ_X = prove
 (`!x y. 0 < y ==> ((x MOD y = x) <=> x < y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOD_EQ_SELF] THEN ASM_ARITH_TAC);;

let MOD_EQ_0_DIVISOR = prove
 (`0 < n ==> ((k MOD n = 0) <=> (?d. k = d * n))`,
  REWRITE_TAC[MOD_EQ_0]);;

let arithmetic_MOD_MULT_MOD = prove
 (`!m n. 0 < n /\ 0 < m ==> !x. ((x MOD (n * m)) MOD n = x MOD n)`,
  REWRITE_TAC[MOD_MOD]);;

let MOD_COMMON_FACTOR = prove
 (`!n p q. 0 < n /\ 0 < q ==> (n * (p MOD q) = (n * p) MOD (n * q))`,
  REWRITE_TAC[MOD_MULT2]);;

let DIV_MOD_MOD_DIV = prove
 (`!m n k. 0 < n /\ 0 < k ==> ((m DIV n) MOD k = (m MOD (n * k)) DIV n)`,
  REWRITE_TAC[DIV_MOD]);;

let DIV_DIV_DIV_MULT = prove
 (`!m n. 0 < m /\ 0 < n ==> !x. ((x DIV m) DIV n = x DIV (m * n))`,
  REWRITE_TAC[DIV_DIV]);;

let ADD_DIV_ADD_DIV = prove
 (`!n. 0 < n ==> !x r. ((x * n) + r) DIV n = x + (r DIV n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC (CONJUNCT1 DIV_MULT_ADD) THEN
  ASM_ARITH_TAC);;

let ADD_DIV_RWT = prove
 (`!n. 0 < n ==> !m p. (m MOD n = 0) \/ (p MOD n = 0) ==>
                       ((m + p) DIV n = m DIV n + p DIV n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_ADD THEN
  ASM_REWRITE_TAC[DIVIDES_MOD]);;

let ADD_MODULUS = prove
 (`(!n x. (x + n) MOD n = x MOD n) /\ (!n x. (n + x) MOD n = x MOD n)`,
  MP_TAC (SPEC `1` (CONJUNCT1 MOD_MULT_ADD)) THEN
  REWRITE_TAC[MULT_CLAUSES] THEN MESON_TAC[ADD_SYM]);;

let SUB_MOD = prove
 (`!m n. 0 < n /\ n <= m ==> ((m - n) MOD n = m MOD n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `m MOD n = (1 * n + (m - n)) MOD n` SUBST1_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[MOD_MULT_ADD]]);;

let MOD_TIMES_SUB = prove
 (`!n q r. 0 < n /\ 0 < q /\ r <= n ==> ((q * n - r) MOD n = (n - r) MOD n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n <= q * n` ASSUME_TAC THENL
   [MATCH_MP_TAC (ARITH_RULE `1 * n <= q * n ==> n <= q * n`) THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `q * n - r = (q - 1) * n + (n - r)` SUBST1_TAC THENL
   [REWRITE_TAC[RIGHT_SUB_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC;
    REWRITE_TAC[MOD_MULT_ADD]]);;

let ADD_MOD = prove
 (`!n a b p. 0 < n ==> (((a + p) MOD n = (b + p) MOD n) <=> (a MOD n = b MOD n))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CONG] THEN NUMBER_TAC);;

let MOD_LIFT_PLUS_IFF = prove
 (`0 < n ==> (((x + k) MOD n = x MOD n + k) <=> (k < n - x MOD n))`,
  DISCH_TAC THEN
  SUBGOAL_THEN `(x + k) MOD n = (x MOD n + k) MOD n` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN REWRITE_TAC[MOD_MOD_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[MOD_EQ_SELF] THEN
  MP_TAC (SPECL [`x:num`; `n:num`] MOD_LT_EQ) THEN ASM_ARITH_TAC);;

let DIV_LT_X = prove
 (`!x y z. 0 < z ==> (y DIV z < x <=> y < x * z)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `0 < z ==> ~(z = 0)`] THEN
  REWRITE_TAC[MULT_SYM]);;

let X_LT_DIV = prove
 (`!x y z. 0 < z ==> (x < y DIV z <=> (x + 1) * z <= y)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LDIV_LT_EQ; ARITH_RULE `0 < z ==> ~(z = 0)`] THEN
  REWRITE_TAC[MULT_SYM]);;

let X_LE_DIV = prove
 (`!x y z. 0 < z ==> (x <= y DIV z <=> x * z <= y)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `0 < z ==> ~(z = 0)`] THEN
  REWRITE_TAC[MULT_SYM]);;

let DIV_LE_X = prove
 (`!x y z. 0 < z ==> (y DIV z <= x <=> y < (x + 1) * z)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LE_LDIV_EQ; ARITH_RULE `0 < z ==> ~(z = 0)`] THEN
  REWRITE_TAC[MULT_SYM]);;

let DIV_EQ_X = prove
 (`!x y z. 0 < z ==> ((y DIV z = x) <=> x * z <= y /\ y < SUC x * z)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `(a = x) <=> x <= a /\ a < x + 1`] THEN
  ASM_SIMP_TAC[X_LE_DIV; DIV_LT_X] THEN REWRITE_TAC[ADD1]);;

let arithmetic_DIV_EQ_0 = prove
 (`1 < b ==> ((n DIV b = 0) <=> (n < b))`,
  DISCH_TAC THEN MATCH_MP_TAC DIV_EQ_0 THEN ASM_ARITH_TAC);;

let DIV_LESS = prove
 (`!n d. 0 < n /\ 1 < d ==> n DIV d < n`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `1 < d ==> ~(d = 0)`] THEN
  MATCH_MP_TAC (ARITH_RULE `1 * n < d * n ==> n < d * n`) THEN
  REWRITE_TAC[LT_MULT_RCANCEL] THEN ASM_ARITH_TAC);;

let DIV_SUB = prove
 (`0 < n /\ n * q <= m ==> ((m - n * q) DIV n = m DIV n - q)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `m DIV n = (q * n + (m - n * q)) DIV n` SUBST1_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] (ASSUME `n * q <= m`)] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  ARITH_TAC);;

let EXP_SUB = prove
 (`!p q n. 0 < n /\ q <= p ==> (n EXP (p - q) = n EXP p DIV n EXP q)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIV_EXP; ARITH_RULE `0 < n ==> ~(n = 0)`]);;

let DIV2_DOUBLE = prove
 (`!n. DIV2 (2 * n) = n`,
  REWRITE_TAC[DIV2_DEF] THEN GEN_TAC THEN MATCH_MP_TAC DIV_MULT THEN
  ARITH_TAC);;

(* EVEN and ODD *)

let arithmetic_EVEN_SUB = prove
 (`!m n. m <= n ==> (EVEN (n - m) <=> (EVEN n <=> EVEN m))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EVEN_SUB] THEN
  ASM_CASES_TAC `n:num = m` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(n <= m)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

let EVEN_ODD_EXISTS = prove
 (`!n. (EVEN n ==> ?m. n = 2 * m) /\ (ODD n ==> ?m. n = SUC (2 * m))`,
  REWRITE_TAC[EVEN_EXISTS; ODD_EXISTS]);;

(* FUNPOW = ITER *)

let FUNPOW = prove
 (`(ITER 0 f (x:A) = x) /\ (ITER (SUC n) f x = ITER n f (f x))`,
  REWRITE_TAC[ITER_ALT]);;

let FUNPOW_0 = prove
 (`ITER 0 f (x:A) = x`,
  REWRITE_TAC[ITER]);;

let FUNPOW_1 = prove
 (`ITER 1 f (x:A) = f x`,
  REWRITE_TAC[ITER_1]);;

let FUNPOW_SUC = prove
 (`!f n (x:A). ITER (SUC n) f x = f (ITER n f x)`,
  REWRITE_TAC[ITER]);;

let FUNPOW_ADD = prove
 (`!m n. ITER (m + n) f (x:A) = ITER m f (ITER n f x)`,
  REWRITE_TAC[ITER_ADD]);;

(* NRC = HOL Light's RELPOW (Library/rstc.ml) *)

let NRC_0 = CONJUNCT1 NRC;;

let NRC_1 = prove
 (`NRC (R:A->A->bool) 1 x y <=> R x y`,
  REWRITE_TAC[num_CONV `1`; NRC] THEN MESON_TAC[]);;

let BASICAUX_NRC_RELPOW = prove
 (`!n (R:A->A->bool) x y. NRC R n x y <=> RELPOW n R x y`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[NRC; RELPOW_R]);;

let RTC_eq_NRC = prove
 (`!(R:A->A->bool) x y. RTC R x y <=> ?n. NRC R n x y`,
  REWRITE_TAC[BASICAUX_NRC_RELPOW; RTC_RELPOW]);;

let RTC_NRC = prove
 (`!x y. RTC (R:A->A->bool) x y ==> ?n. NRC R n x y`,
  MESON_TAC[RTC_eq_NRC]);;

let transitive_LESS = prove
 (`transitive ((<):num->num->bool)`,
  REWRITE_TAC[transitive_DEF] THEN ARITH_TAC);;

let transitive_LE = prove
 (`transitive ((<=):num->num->bool)`,
  REWRITE_TAC[transitive_DEF] THEN ARITH_TAC);;

let BASICAUX_num_of_int_lt = prove
 (`!i n. &0 <= i /\ i < &n ==> num_of_int i < n`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_LT; INT_OF_NUM_OF_INT]);;

let BASICAUX_EX_ADD = prove
 (`!P k. (?y. P (k + y)) ==> (?x:num. P x)`,
  MESON_TAC[]);;
(* ------------------------------------------------------------------------- *)
(* While (HOL4 src/num/theories/WhileScript.sml).  HOL4 LEAST is HOL Light's *)
(* minimal ($LEAST P = (minimal) P); OWHILE, WHILE, OLEAST are vocab.ml's.   *)
(* ------------------------------------------------------------------------- *)

let LEAST_EXISTS = MINIMAL;;

let LEAST_INTRO = prove
 (`!P x. P x ==> P ((minimal) P)`,
  MESON_TAC[MINIMAL]);;

let LEAST_EXISTS_IMP = prove
 (`!p. (?n. p n) ==> (p ((minimal) p) /\ !n. n < (minimal) p ==> ~p n)`,
  REWRITE_TAC[MINIMAL]);;

let LEAST_ELIM = prove
 (`!Q P. (?n. P n) /\ (!n. (!m. m < n ==> ~P m) /\ P n ==> Q n)
         ==> Q ((minimal) P)`,
  MESON_TAC[MINIMAL]);;

let FULL_LEAST_INTRO = prove
 (`!x. P x ==> P ((minimal) P) /\ (minimal) P <= x`,
  MESON_TAC[MINIMAL; MINIMAL_UBOUND]);;

let LESS_LEAST = prove
 (`!P m. m < (minimal) P ==> ~P m`,
  MESON_TAC[MINIMAL]);;

let OLEAST_def = OLEAST_DEF;;

let OLEAST_INTRO = prove
 (`((!n. ~P n) ==> Q NONE) /\
   (!n. P n /\ (!m. m < n ==> ~P m) ==> Q (SOME n))
   ==> Q ((OLEAST) P)`,
  REWRITE_TAC[OLEAST_DEF] THEN STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [MINIMAL]) THEN
    REWRITE_TAC[ETA_AX];
    ASM_MESON_TAC[]]);;

let BASICAUX_MINIMAL_ETA = prove
 (`!P. (minimal n. P n) = (minimal) P`,
  REWRITE_TAC[ETA_AX]);;

let OLEAST_EQ_SOME = prove
 (`((OLEAST) P = SOME n) <=> P n /\ !m. m < n ==> ~P m`,
  REWRITE_TAC[OLEAST_DEF; BASICAUX_MINIMAL_ETA] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THENL
   [EQ_TAC THENL
     [DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_MESON_TAC[MINIMAL];
      MESON_TAC[MINIMAL_UNIQUE]];
    ASM_MESON_TAC[]]);;

let OLEAST_EQ_NONE = prove
 (`((OLEAST) P = NONE) <=> !n. ~P n`,
  REWRITE_TAC[OLEAST_DEF] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[]);;

let OLEAST_EQNS = prove
 (`((OLEAST n. n = x) = SOME x) /\
   ((OLEAST n. x = n) = SOME x) /\
   ((OLEAST n. F) = NONE) /\
   ((OLEAST n. T) = SOME 0)`,
  REWRITE_TAC[OLEAST_EQ_SOME; OLEAST_EQ_NONE] THEN
  MESON_TAC[LT_REFL; ARITH_RULE `~(m < 0)`]);;

(* the recursion equation of vocab.ml's WHILE (HOL4 WHILE) and OWHILE *)

let BASICAUX_WHILE_ITER = prove
 (`!(P:A->bool) g x. P x ==>
     ((?n. ~P (ITER n g x)) <=> (?n. ~P (ITER n g (g x)))) /\
     ((?n. ~P (ITER n g x))
      ==> ITER (minimal n. ~P (ITER n g x)) g x =
          ITER (minimal n. ~P (ITER n g (g x))) g (g x))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(?n. ~(P:A->bool) (ITER n g x)) <=> (?n. ~P (ITER n g (g x)))`
  ASSUME_TAC THENL
   [EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
      STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
      ASM_REWRITE_TAC[ITER_ALT] THEN MESON_TAC[];
      DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN EXISTS_TAC `SUC m` THEN
      ASM_REWRITE_TAC[ITER_ALT]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(minimal n. ~(P:A->bool) (ITER n g x)) =
                SUC (minimal n. ~P (ITER n g (g x)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MINIMAL_UNIQUE THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MINIMAL]) THEN
    REWRITE_TAC[ITER_ALT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:num` THEN STRUCT_CASES_TAC (SPEC `j:num` num_CASES) THEN
    ASM_REWRITE_TAC[ITER_ALT; LT_SUC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[ITER_ALT]]);;

let BASICAUX_WHILE_STOP = prove
 (`!(P:A->bool) g x. ~P x ==>
     (?n. ~P (ITER n g x)) /\ (minimal n. ~P (ITER n g x)) = 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ITER];
    MATCH_MP_TAC MINIMAL_UNIQUE THEN ASM_REWRITE_TAC[ITER; LT]]);;

let WHILE = prove
 (`!(P:A->bool) g x. WHILE P g x = if P x then WHILE P g (g x) else x`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [MP_TAC (UNDISCH (SPECL [`P:A->bool`; `g:A->A`; `x:A`] BASICAUX_WHILE_ITER)) THEN
    REWRITE_TAC[WHILE_DEF] THEN
    ASM_CASES_TAC `?n. ~(P:A->bool) (ITER n g x)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    MP_TAC (UNDISCH (SPECL [`P:A->bool`; `g:A->A`; `x:A`] BASICAUX_WHILE_STOP)) THEN
    REWRITE_TAC[WHILE_DEF] THEN DISCH_THEN(fun th -> REWRITE_TAC[th; ITER])]);;

let OWHILE_THM = prove
 (`OWHILE (G:A->bool) f s = if G s then OWHILE G f (f s) else SOME s`,
  COND_CASES_TAC THENL
   [MP_TAC (UNDISCH (SPECL [`G:A->bool`; `f:A->A`; `s:A`] BASICAUX_WHILE_ITER)) THEN
    REWRITE_TAC[OWHILE_DEF] THEN
    ASM_CASES_TAC `?n. ~(G:A->bool) (ITER n f s)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    MP_TAC (UNDISCH (SPECL [`G:A->bool`; `f:A->A`; `s:A`] BASICAUX_WHILE_STOP)) THEN
    REWRITE_TAC[OWHILE_DEF] THEN DISCH_THEN(fun th -> REWRITE_TAC[th; ITER])]);;

(* TAILREC (a new_specification, as in HOL4) and TAILCALL *)

let BASICAUX_SELECT_EQ = prove
 (`!a:A. (@x. a = x) = a`,
  GEN_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN MESON_TAC[]);;

let BASICAUX_WHILE_SUM = prove
 (`!(f:A->A+B) y.
     WHILE (\s. ?a. f s = INL a) (\s. @a. f s = INL a) y =
     sum_CASE (f y) (\a. WHILE (\s. ?a. f s = INL a) (\s. @a. f s = INL a) a)
                    (\b. y)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [WHILE] THEN
  REWRITE_TAC[] THEN
  STRUCT_CASES_TAC (ISPEC `(f:A->A+B) y` (cases "sum")) THEN
  REWRITE_TAC[sum_CASE; injectivity "sum"; distinctness "sum";
              BASICAUX_SELECT_EQ; MESON[] `!a:A. ?x. a = x`]);;

let TAILREC = new_specification ["TAILREC"]
 (prove
   (`?tailrec. !(f:A->A+B) x.
       tailrec f x = sum_CASE (f x) (\z. tailrec f z) (\y. y)`,
    EXISTS_TAC
     `\(f:A->A+B) x.
        sum_CASE (f (WHILE (\s. ?a. f s = INL a) (\s. @a. f s = INL a) x))
                 (\a. @y:B. T) (\y. y)` THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [BASICAUX_WHILE_SUM] THEN
    MP_TAC (ISPEC `(f:A->A+B) x` (cases "sum")) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[sum_CASE]));;

let TAILCALL_def = new_definition
  `TAILCALL (f:A->A+B) (k:A->B) x = sum_CASE (f x) (\cv. k cv) (\tv. tv)`;;

let TAILREC_TAILCALL = prove
 (`TAILREC (f:A->A+B) x = TAILCALL f (TAILREC f) x`,
  GEN_REWRITE_TAC LAND_CONV [TAILREC] THEN REWRITE_TAC[TAILCALL_def]);;
(* ------------------------------------------------------------------------- *)
(* relation (HOL4 src/relation/relationScript.sml).  RTC, TC, RC are         *)
(* Library/rstc.ml's, WF is HOL Light's; transitive, reflexive, ... and      *)
(* RSUBSET (prefix here, infix in HOL4) are vocab.ml's, inv_image the kit's. *)
(* ------------------------------------------------------------------------- *)

let transitive_def = transitive_DEF;;
let reflexive_def = reflexive_DEF;;
let irreflexive_def = irreflexive_DEF;;
let symmetric_def = symmetric_DEF;;
let antisymmetric_def = antisymmetric_DEF;;
let total_def = total_DEF;;
let trichotomous = trichotomous_DEF;;
let RSUBSET = RSUBSET_DEF;;
let inv_image_def = inv_image;;
let WF_DEF = WF;;

let RTC_CASES1 = RTC_CASES_R;;
let TC_SUBSET = TC_INC;;
let RTC_SINGLE = RTC_INC;;
let RTC_SUBSET = RTC_INC;;
let TC_LEFT1_I = TC_TRANS_R;;
let TC_RIGHT1_I = TC_TRANS_L;;
let TC_RTC = RTC_INC_TC;;
let WF_TC_EQN = WF_TC;;

(* HOL4 RTC_INDUCT and RTC_RULES (RTC_rules); HOL Light's RTC_INDUCT and
   RTC_RULES have the three clauses inc/refl/trans *)

let relation_RTC_INDUCT = RTC_INDUCT_R;;

let relation_RTC_RULES = prove
 (`!R. (!x:A. RTC R x x) /\ (!x y z. R x y /\ RTC R y z ==> RTC R x z)`,
  REWRITE_TAC[RTC_REFL] THEN MESON_TAC[RTC_TRANS_R]);;

let inv_image_thm = inv_image_THM;;

let RTC_CASES_RTC_TWICE = prove
 (`!R (x:A) y. RTC R x y <=> ?u. RTC R x u /\ RTC R u y`,
  MESON_TAC[RTC_REFL; RTC_TRANS]);;

let RTC_TRANSITIVE = prove
 (`!R:A->A->bool. transitive (RTC R)`,
  REWRITE_TAC[transitive_DEF] THEN MESON_TAC[RTC_TRANS]);;

let transitive_RTC = RTC_TRANSITIVE;;

let TC_TRANSITIVE = prove
 (`!R:A->A->bool. transitive (TC R)`,
  REWRITE_TAC[transitive_DEF] THEN MESON_TAC[TC_TRANS]);;

let RTC_REFLEXIVE = prove
 (`!R:A->A->bool. reflexive (RTC R)`,
  REWRITE_TAC[reflexive_DEF; RTC_REFL]);;

let RC_DEF = prove
 (`RC (R:A->A->bool) x y <=> (x = y) \/ R x y`,
  REWRITE_TAC[RC_EXPLICIT] THEN MESON_TAC[]);;

let TC_RC_EQNS = prove
 (`!R:A->A->bool. (RC (TC R) = RTC R) /\ (TC (RC R) = RTC R)`,
  REWRITE_TAC[RTC; TC_RC]);;

let RTC_lifts_invariants = prove
 (`(!x y. P x /\ (R:A->A->bool) x y ==> P y) ==>
   !x y. P x /\ RTC R x y ==> P y`,
  DISCH_TAC THEN
  SUBGOAL_THEN `!x y. RTC (R:A->A->bool) x y ==> P x ==> P y`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC RTC_INDUCT_R THEN ASM_MESON_TAC[]);;

let RTC_lifts_equalities = prove
 (`(!x y. (R:A->A->bool) x y ==> ((f:A->B) x = f y)) ==>
   !x y. RTC R x y ==> (f x = f y)`,
  DISCH_TAC THEN MATCH_MP_TAC RTC_INDUCT_R THEN ASM_MESON_TAC[]);;

let TC_STRONG_INDUCT_LEFT1 = prove
 (`!(R:A->A->bool) P.
     (!x y. R x y ==> P x y) /\
     (!x y z. R x y /\ P y z /\ TC R y z ==> P x z)
     ==> (!u v. TC R u v ==> P u v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!u v. TC (R:A->A->bool) u v ==> P u v /\ TC R u v`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC TC_INDUCT_R THEN ASM_MESON_TAC[TC_INC; TC_TRANS_R]);;

let TC_STRONG_INDUCT_RIGHT1 = prove
 (`!(R:A->A->bool) P.
     (!x y. R x y ==> P x y) /\
     (!x y z. P x y /\ TC R x y /\ R y z ==> P x z)
     ==> (!u v. TC R u v ==> P u v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!u v. TC (R:A->A->bool) u v ==> P u v /\ TC R u v`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC TC_INDUCT_L THEN ASM_MESON_TAC[TC_INC; TC_TRANS_L]);;

let WF_INDUCTION_THM = prove
 (`!(R:A->A->bool). WF R ==> !P. (!x. (!y. R y x ==> P y) ==> P x) ==> !x. P x`,
  REWRITE_TAC[WF_IND]);;

let transitive_inv_image = prove
 (`!(R:B->B->bool) (f:A->B). transitive R ==> transitive (inv_image R f)`,
  REWRITE_TAC[transitive_DEF; inv_image_THM] THEN MESON_TAC[]);;

let reflexive_inv_image = prove
 (`!(R:B->B->bool) (f:A->B). reflexive R ==> reflexive (inv_image R f)`,
  REWRITE_TAC[reflexive_DEF; inv_image_THM] THEN MESON_TAC[]);;

let symmetric_inv_image = prove
 (`!(R:B->B->bool) (f:A->B). symmetric R ==> symmetric (inv_image R f)`,
  REWRITE_TAC[symmetric_DEF; inv_image_THM] THEN MESON_TAC[]);;

let total_inv_image = prove
 (`!(R:B->B->bool) (f:A->B). total R ==> total (inv_image R f)`,
  REWRITE_TAC[total_DEF; inv_image_THM] THEN MESON_TAC[]);;

(* StrongOrder, StrongLinearOrder, RINTER (infix, as in HOL4) *)

let StrongOrder = new_definition
  `StrongOrder (Z:A->A->bool) <=> irreflexive Z /\ transitive Z`;;

let StrongLinearOrder = new_definition
  `StrongLinearOrder (R:A->A->bool) <=> StrongOrder R /\ trichotomous R`;;

parse_as_infix("RINTER",(20,"left"));;

let RINTER = new_definition
  `((R1:A->B->bool) RINTER R2) x y <=> R1 x y /\ R2 x y`;;

(* WFP, the well-founded part of a relation *)

let WFP_DEF = new_definition
  `WFP (R:A->A->bool) a <=> !P. (!x. (!y. R y x ==> P y) ==> P x) ==> P a`;;

let WFP_RULES = prove
 (`!(R:A->A->bool) x. (!y. R y x ==> WFP R y) ==> WFP R x`,
  REWRITE_TAC[WFP_DEF] THEN MESON_TAC[]);;

let WFP_INDUCT = prove
 (`!(R:A->A->bool) P. (!x. (!y. R y x ==> P y) ==> P x) ==> !x. WFP R x ==> P x`,
  REWRITE_TAC[WFP_DEF] THEN MESON_TAC[]);;

let WFP_STRONG_INDUCT = prove
 (`!(R:A->A->bool).
     (!x. WFP R x /\ (!y. R y x ==> P y) ==> P x) ==> !x. WFP R x ==> P x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x. WFP (R:A->A->bool) x ==> WFP R x /\ P x`
    (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC WFP_INDUCT THEN ASM_MESON_TAC[WFP_RULES]);;

let WFP_CASES = prove
 (`!(R:A->A->bool) x. WFP R x <=> !y. R y x ==> WFP R y`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[WFP_RULES]] THEN
  SPEC_TAC(`x:A`,`x:A`) THEN MATCH_MP_TAC WFP_INDUCT THEN
  MESON_TAC[WFP_RULES]);;

let WF_EQ_WFP = prove
 (`!R:A->A->bool. WF R <=> !x. WFP R x`,
  GEN_TAC THEN REWRITE_TAC[WF_IND] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `WFP (R:A->A->bool)`) THEN MESON_TAC[WFP_RULES];
    DISCH_TAC THEN X_GEN_TAC `P:A->bool` THEN DISCH_TAC THEN
    X_GEN_TAC `x:A` THEN
    MP_TAC (SPECL [`R:A->A->bool`; `P:A->bool`] WFP_INDUCT) THEN
    ASM_MESON_TAC[]]);;
(* While: TAILREC_GUARD_ELIMINATION (needs WFP of relation) *)

let TAILREC_GUARD_ELIMINATION = prove
 (`(!x y. P x /\ ((c:A->A+B) x = INL y) ==> P y) /\
   (!x. P x ==>
        ?R. WFP R x /\ !y z. P y /\ RTC R y x /\ (c y = INL z) ==> R z y) /\
   (!x. P x ==> ((f:A->B) x = TAILCALL c f x))
   ==> (!x. P x ==> (f x = TAILREC c x))`,
  STRIP_TAC THEN X_GEN_TAC `x0:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `x0:A` th) THEN ANTS_TAC THENL
    [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `R:A->A->bool` STRIP_ASSUME_TAC) THEN
    ASSUME_TAC th) THEN
  SUBGOAL_THEN
   `!x. WFP (R:A->A->bool) x ==>
        (!y z. P y /\ RTC R y x /\ ((c:A->A+B) y = INL z) ==> R z y) ==>
        P x ==> ((f:A->B) x = TAILREC c x)`
   (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC WFP_STRONG_INDUCT THEN X_GEN_TAC `x:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "IH")) THEN
  DISCH_THEN(LABEL_TAC "D") THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:A->B) x = TAILCALL c f x` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [TAILREC] THEN REWRITE_TAC[TAILCALL_def] THEN
  MP_TAC (ISPEC `(c:A->A+B) x` (cases "sum")) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[sum_CASE] THEN
  REMOVE_THEN "IH" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
  SUBGOAL_THEN `(R:A->A->bool) a x` ASSUME_TAC THENL
   [USE_THEN "D" MATCH_MP_TAC THEN ASM_REWRITE_TAC[RTC_REFL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "D" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RTC_TRANS; RTC_INC];
    ASM_MESON_TAC[]]);;
(* ------------------------------------------------------------------------- *)
(* pred_set (HOL4 src/pred_set/src/pred_setScript.sml): the extras HOL       *)
(* Light's sets.ml lacks.  count, COMPL, PREIMAGE, MAX_SET, SUM_SET are      *)
(* vocab.ml's; BIGUNION is UNIONS; HOL4 PERMUTES (an overload) is            *)
(* BIJ f s s.  HOL4 names that sets.ml uses for other statements get the     *)
(* prefix pred_set_.                                                          *)
(* ------------------------------------------------------------------------- *)

let SUBSET_DEF = SUBSET;;
let BIJ_DEF = BIJ;;
let SURJ_DEF = SURJ;;
let DISJOINT_DEF = DISJOINT;;
let IMAGE_COMPOSE = IMAGE_o;;
let EMPTY_DEF = EMPTY;;
let INTER_DEF = INTER;;
let UNION_DEF = UNION;;
let DIFF_DEF = DIFF;;
let SPECIFICATION = IN;;
let BIGUNION = UNIONS;;
let PSUBSET_DEF = PSUBSET;;
let INFINITE_NUM_UNIV = num_INFINITE;;
let DIFF_SUBSET = SUBSET_DIFF;;
let pred_set_count_def = pred_set_count_DEF;;

(* HOL4 GSPECIFICATION is about HOL4's GSPEC (f:'b -> 'a # bool); HOL Light
   encodes set comprehensions with GSPEC and SETSPEC, whose membership rule
   is IN_ELIM_THM *)

let GSPECIFICATION = IN_ELIM_THM;;

let INJ_DEF = prove
 (`INJ (f:A->B) s t <=>
   (!x. x IN s ==> (f x) IN t) /\
   (!x y. (x IN s /\ y IN s) ==> (f x = f y) ==> (x = y))`,
  REWRITE_TAC[INJ] THEN MESON_TAC[]);;

let DELETE_DEF = prove
 (`(s:A->bool) DELETE x = s DIFF {x}`,
  SET_TAC[]);;

let IMAGE_DEF = prove
 (`IMAGE (f:A->B) s = {f x | x IN s}`,
  REWRITE_TAC[SIMPLE_IMAGE]);;

(* HOL4 INSERT_DEF; HOL Light's INSERT_DEF is the lambda form *)

let pred_set_INSERT_DEF = prove
 (`(x:A) INSERT s = {y | (y = x) \/ y IN s}`,
  SET_TAC[]);;

let SET_EQ_SUBSET = prove
 (`!(s:A->bool) t. (s = t) <=> s SUBSET t /\ t SUBSET s`,
  REWRITE_TAC[SUBSET_ANTISYM_EQ]);;

let SUBSET_THM = prove
 (`!(P:A->bool) Q. P SUBSET Q ==> (!x. x IN P ==> x IN Q)`,
  REWRITE_TAC[SUBSET]);;

(* HOL4 UNION_ASSOC; HOL Light's UNION_ASSOC is the other orientation *)

let pred_set_UNION_ASSOC = prove
 (`!(s:A->bool) t u. s UNION (t UNION u) = (s UNION t) UNION u`,
  REWRITE_TAC[UNION_ASSOC]);;

(* HOL4 SUBSET_DIFF; HOL Light's SUBSET_DIFF is HOL4 DIFF_SUBSET *)

let pred_set_SUBSET_DIFF = prove
 (`!(s1:A->bool) s2 s3. (s1 SUBSET (s2 DIFF s3)) <=> s1 SUBSET s2 /\ DISJOINT s1 s3`,
  SET_TAC[]);;

let DISJOINT_ALT = prove
 (`!(s:A->bool) t. DISJOINT s t <=> !x. x IN s ==> ~(x IN t)`,
  SET_TAC[]);;

let INSERT_SING_UNION = prove
 (`!s. !x:A. x INSERT s = {x} UNION s`,
  SET_TAC[]);;

let SUBSET_DISJOINT = prove
 (`!(s:A->bool) t u v. DISJOINT s t /\ u SUBSET s /\ v SUBSET t ==> DISJOINT u v`,
  SET_TAC[]);;

let DIFF_UNION = prove
 (`!(x:A->bool) y z. x DIFF (y UNION z) = x DIFF y DIFF z`,
  SET_TAC[]);;

let SUBSET_OF_INSERT = prove
 (`!(x:A) s. s SUBSET (x INSERT s)`,
  SET_TAC[]);;

let DISJOINT_SUBSET = prove
 (`!(s:A->bool) t u. DISJOINT s t /\ u SUBSET t ==> DISJOINT s u`,
  SET_TAC[]);;

let SUBSET_INSERT_RIGHT = prove
 (`!(e:A) s1 s2. s1 SUBSET s2 ==> s1 SUBSET (e INSERT s2)`,
  SET_TAC[]);;

let INTER_UNION = prove
 (`(((A:B->bool) UNION B) INTER A = A) /\ ((B UNION A) INTER A = A) /\
   (A INTER (A UNION B) = A) /\ (A INTER (B UNION A) = A)`,
  SET_TAC[]);;

let ABSORPTION_RWT = prove
 (`!(x:A) s. x IN s ==> (x INSERT s = s)`,
  SET_TAC[]);;

let DIFF_SAME_UNION = prove
 (`!(x:A->bool) y. ((x UNION y) DIFF x = y DIFF x) /\ ((x UNION y) DIFF y = x DIFF y)`,
  SET_TAC[]);;

let DISJOINT_DIFF = prove
 (`!(s:A->bool) t. DISJOINT t (s DIFF t) /\ DISJOINT (s DIFF t) t`,
  SET_TAC[]);;

let DISJOINT_UNION' = prove
 (`!(s:A->bool) t u. DISJOINT u (s UNION t) <=> DISJOINT u s /\ DISJOINT u t`,
  SET_TAC[]);;

let DELETE_NON_ELEMENT_RWT = prove
 (`!(s:A->bool) x. ~(x IN s) ==> (s DELETE x = s)`,
  SET_TAC[]);;

let SUBSET_INTER2 = prove
 (`!(s:A->bool) t. s SUBSET t ==> (t INTER s = s)`,
  SET_TAC[]);;

let IMAGE_SUBSET_gen = prove
 (`!(f:A->B) s u t. s SUBSET u /\ (IMAGE f u SUBSET t) ==> IMAGE f s SUBSET t`,
  SET_TAC[]);;

let IMAGE_INSERT = prove
 (`!(f:A->B) x s. IMAGE f (x INSERT s) = f x INSERT (IMAGE f s)`,
  REWRITE_TAC[IMAGE_CLAUSES]);;

let IMAGE_IMAGE = prove
 (`!(f:B->C) (g:A->B) s. IMAGE f (IMAGE g s) = IMAGE (f o g) s`,
  REWRITE_TAC[IMAGE_o]);;

let IMAGE_CONG = prove
 (`!(f:A->B) s f' s'. (s = s') /\ (!x. x IN s' ==> (f x = f' x))
                      ==> (IMAGE f s = IMAGE f' s')`,
  SIMP_TAC[] THEN SET_TAC[]);;

let IMAGE_FINITE = prove
 (`!s. FINITE s ==> !f:A->B. FINITE (IMAGE f s)`,
  SIMP_TAC[FINITE_IMAGE]);;

let IN_BIGUNION = prove
 (`!(x:A) sos. x IN UNIONS sos <=> ?s. x IN s /\ s IN sos`,
  REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[]);;

let SUBSET_FINITE = prove
 (`!s:A->bool. FINITE s ==> (!t. t SUBSET s ==> FINITE t)`,
  MESON_TAC[FINITE_SUBSET]);;

let SUBSET_FINITE_I = prove
 (`!(s:A->bool) t. FINITE s /\ t SUBSET s ==> FINITE t`,
  MESON_TAC[FINITE_SUBSET]);;

let IN_INFINITE_NOT_FINITE = prove
 (`!s t. INFINITE s /\ FINITE t ==> ?x:A. x IN s /\ ~(x IN t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `INFINITE ((s:A->bool) DIFF t)` MP_TAC THENL
   [ASM_SIMP_TAC[INFINITE_DIFF_FINITE]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INFINITE_NONEMPTY) THEN SET_TAC[]);;

(* HOL4 FINITE_INDUCT, CARD_SUBSET, CARD_PSUBSET, CARD_UNION; HOL Light's
   theorems of these names have other forms *)

let pred_set_FINITE_INDUCT = prove
 (`!P. P {} /\ (!s. FINITE s /\ P s ==> (!e. ~(e IN s) ==> P (e INSERT s)))
       ==> !s:A->bool. FINITE s ==> P s`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_MESON_TAC[]);;

let pred_set_CARD_SUBSET = prove
 (`!s:A->bool. FINITE s ==> !t. t SUBSET s ==> CARD t <= CARD s`,
  MESON_TAC[CARD_SUBSET]);;

let pred_set_CARD_PSUBSET = prove
 (`!s:A->bool. FINITE s ==> !t. t PSUBSET s ==> CARD t < CARD s`,
  MESON_TAC[CARD_PSUBSET]);;

let pred_set_CARD_UNION = prove
 (`!s:A->bool. FINITE s ==> !t. FINITE t ==>
     (CARD (s UNION t) + CARD (s INTER t) = CARD s + CARD t)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CARD_UNION_GEN] THEN
  MATCH_MP_TAC(ARITH_RULE `c <= a + b ==> (a + b) - c + c = a + b`) THEN
  MATCH_MP_TAC(ARITH_RULE `c <= a ==> c <= a + b`) THEN
  MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[INTER_SUBSET]);;

let CARD_DEF = prove
 (`(CARD (EMPTY:A->bool) = 0) /\
   (!s. FINITE s ==>
        !x:A. CARD (x INSERT s) = (if x IN s then CARD s else SUC (CARD s)))`,
  SIMP_TAC[CARD_CLAUSES]);;

let CARD_INSERT = CONJUNCT2 CARD_DEF;;

let SUBSET_EQ_CARD = prove
 (`!s:A->bool. FINITE s ==>
     !t. FINITE t /\ (CARD s = CARD t) /\ s SUBSET t ==> (s = t)`,
  MESON_TAC[CARD_SUBSET_EQ]);;

(* count *)

let IN_COUNT = prove
 (`!m n. m IN pred_set_count n <=> m < n`,
  REWRITE_TAC[pred_set_count_DEF; IN_ELIM_THM]);;

let COUNT_ZERO = prove
 (`pred_set_count 0 = {}`,
  REWRITE_TAC[EXTENSION; IN_COUNT; NOT_IN_EMPTY] THEN ARITH_TAC);;

let COUNT_SUC = prove
 (`!n. pred_set_count (SUC n) = n INSERT pred_set_count n`,
  REWRITE_TAC[EXTENSION; IN_COUNT; IN_INSERT] THEN ARITH_TAC);;

let count_add1 = prove
 (`!n. pred_set_count (n + 1) = n INSERT pred_set_count n`,
  REWRITE_TAC[EXTENSION; IN_COUNT; IN_INSERT] THEN ARITH_TAC);;

let FINITE_COUNT = prove
 (`!n. FINITE (pred_set_count n)`,
  REWRITE_TAC[pred_set_count_DEF; FINITE_NUMSEG_LT]);;

let CARD_COUNT = prove
 (`!n. CARD (pred_set_count n) = n`,
  REWRITE_TAC[pred_set_count_DEF; CARD_NUMSEG_LT]);;

let COUNT_MONO = prove
 (`!m n. m <= n ==> (pred_set_count m) SUBSET (pred_set_count n)`,
  REWRITE_TAC[SUBSET; IN_COUNT] THEN ARITH_TAC);;

let count_add = prove
 (`!n m. pred_set_count (n + m) = pred_set_count n UNION IMAGE ((+) n) (pred_set_count m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_UNION; IN_IMAGE; IN_COUNT] THEN
  X_GEN_TAC `x:num` THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_CASES_TAC `x < n` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `x - n:num` THEN ASM_ARITH_TAC;
    STRIP_TAC THEN ASM_ARITH_TAC]);;

(* COMPL and PREIMAGE *)

let IN_COMPL = prove
 (`!(x:A) s. x IN COMPL s <=> ~(x IN s)`,
  REWRITE_TAC[COMPL_DEF; IN_DIFF; IN_UNIV]);;

let COMPL_INTER = prove
 (`((x:A->bool) INTER COMPL x = {}) /\ (COMPL x INTER x = {})`,
  REWRITE_TAC[EXTENSION; IN_INTER; IN_COMPL; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let IN_PREIMAGE = prove
 (`!(f:A->B) s x. x IN PREIMAGE f s <=> f x IN s`,
  REWRITE_TAC[PREIMAGE_DEF; IN_ELIM_THM]);;

(* MAX_SET and SUM_SET *)

let X_LE_MAX_SET = prove
 (`!s. FINITE s ==> !x. x IN s ==> x <= MAX_SET s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MAX_SET_DEF] THEN
  COND_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?m. m IN s /\ !n:num. n IN s ==> n <= m` MP_TAC THENL
   [MP_TAC (SPEC `\x:num. x IN s` num_MAX) THEN REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[num_FINITE]];
    DISCH_THEN(MP_TAC o SELECT_RULE) THEN ASM_MESON_TAC[]]);;

let in_max_set = X_LE_MAX_SET;;

(* HOL4 SUM_SET_DEF; vocab.ml's SUM_SET_DEF is the nsum form *)

let pred_set_SUM_SET_DEF = prove
 (`SUM_SET = SUM_IMAGE I`,
  REWRITE_TAC[FUN_EQ_THM; SUM_SET_DEF; SUM_IMAGE_DEF; I_DEF]);;

let SUM_SET_IN_LE = prove
 (`!x s. FINITE s /\ x IN s ==> x <= SUM_SET s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUM_SET_DEF] THEN
  MP_TAC (ISPECL [`\x:num. x`; `s:num->bool`; `x:num`] NSUM_DELETE) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let SUM_SET_count = prove
 (`SUM_SET (pred_set_count n) = (n * (n - 1)) DIV 2`,
  SUBGOAL_THEN `!n. nsum {m | m < n} (\x. x) * 2 = n * (n - 1)` ASSUME_TAC THENL
   [INDUCT_TAC THEN
    REWRITE_TAC[NUMSEG_CLAUSES_LT; NSUM_CLAUSES; MULT_CLAUSES] THEN
    SIMP_TAC[NSUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
    POP_ASSUM MP_TAC THEN
    STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
    REWRITE_TAC[SUC_SUB1; SUB_0; MULT_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_SET_DEF; pred_set_count_DEF] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN ARITH_TAC);;
(* INJ, SURJ, BIJ; LINV_OPT and LINV as in HOL4 (LINV_LO) *)

let INJ_IFF = prove
 (`INJ (f:A->B) s t <=>
   (!x. x IN s ==> f x IN t) /\
   (!x y. x IN s /\ y IN s ==> ((f x = f y) <=> (x = y)))`,
  REWRITE_TAC[INJ] THEN MESON_TAC[]);;

let INJ_SUBSET = prove
 (`!(f:A->B) s t s0 t0. INJ f s t /\ s0 SUBSET s /\ t SUBSET t0 ==> INJ f s0 t0`,
  REWRITE_TAC[INJ; SUBSET] THEN MESON_TAC[]);;

let INJ_INSERT = prove
 (`!(f:A->B) x s t. INJ f (x INSERT s) t <=>
     INJ f s t /\ (f x) IN t /\ (!y. y IN s /\ (f x = f y) ==> (x = y))`,
  REWRITE_TAC[INJ; IN_INSERT] THEN MESON_TAC[]);;

let INJ_EXTEND = prove
 (`!(b:A->B) s t x y. INJ b s t /\ ~(x IN s) /\ ~(y IN t)
     ==> INJ ((x =+ y) b) (x INSERT s) (y INSERT t)`,
  REWRITE_TAC[INJ; IN_INSERT; APPLY_UPDATE_THM] THEN MESON_TAC[]);;

let INJ_COMPOSE = prove
 (`!(f:A->B) (g:B->C) s t u. INJ f s t /\ INJ g t u ==> INJ (g o f) s u`,
  REWRITE_TAC[INJ; o_THM] THEN MESON_TAC[]);;

let INJ_IMAGE = prove
 (`!(f:A->B) s t. INJ f s t ==> INJ f s (IMAGE f s)`,
  REWRITE_TAC[INJ; IN_IMAGE] THEN MESON_TAC[]);;

let INJ_CARD = prove
 (`!(f:A->B) s t. INJ f s t /\ FINITE t ==> CARD s <= CARD t`,
  REWRITE_TAC[INJ] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (s:A->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `s = {x:A | x IN s /\ (f:A->B) x IN t}` SUBST1_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC FINITE_IMAGE_INJ_GENERAL THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(IMAGE (f:A->B) s)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_MESON_TAC[];
    MATCH_MP_TAC CARD_SUBSET THEN ASM SET_TAC[]]);;

let PHP = prove
 (`!(f:A->B) s t. FINITE t /\ CARD t < CARD s ==> ~INJ f s t`,
  MESON_TAC[INJ_CARD; NOT_LT]);;

let IMAGE_SURJ = prove
 (`!(f:A->B) s t. SURJ f s t <=> (IMAGE f s = t)`,
  REWRITE_TAC[SURJ] THEN SET_TAC[]);;

let BIJ_IMP_11 = prove
 (`BIJ (f:A->B) UNIV UNIV ==> !x y. (f x = f y) <=> (x = y)`,
  REWRITE_TAC[BIJ; INJ; IN_UNIV] THEN MESON_TAC[]);;

let BIJ_INSERT = prove
 (`!(f:A->B) e s t. BIJ f (e INSERT s) t <=>
     ~(e IN s) /\ f e IN t /\ BIJ f s (t DELETE f e) \/ e IN s /\ BIJ f s t`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(e:A) IN s` THENL
   [ASM_SIMP_TAC[SET_RULE `(e:A) IN s ==> e INSERT s = s`]; ALL_TAC] THEN
  ASM_REWRITE_TAC[BIJ; INJ; SURJ; IN_INSERT; IN_DELETE] THEN ASM_MESON_TAC[]);;

let BIJ_support = prove
 (`!(f:A->A) s' s. BIJ f s' s' /\ s' SUBSET s /\ (!x. ~(x IN s') ==> (f x = x))
     ==> BIJ f s s`,
  REWRITE_TAC[BIJ; INJ; SURJ; SUBSET] THEN REPEAT STRIP_TAC THENL
   [ASM_CASES_TAC `(x:A) IN s'` THEN ASM_MESON_TAC[];
    ASM_CASES_TAC `(x:A) IN s'` THEN ASM_CASES_TAC `(y:A) IN s'` THEN
    ASM_MESON_TAC[];
    ASM_CASES_TAC `(x:A) IN s'` THEN ASM_MESON_TAC[];
    ASM_CASES_TAC `(x:A) IN s'` THEN ASM_MESON_TAC[]]);;

let FINITE_SURJ_BIJ = prove
 (`FINITE (s:A->bool) /\ SURJ (f:A->B) s t /\ (CARD t = CARD s) ==> BIJ f s t`,
  REWRITE_TAC[BIJ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `SURJ (f:A->B) s t` THEN REWRITE_TAC[SURJ; INJ] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE (t:B->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `t = IMAGE (f:A->B) s` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[FINITE_IMAGE]];
    ALL_TAC] THEN
  MP_TAC (ISPECL [`s:A->bool`; `t:B->bool`; `f:A->B`]
                 SURJECTIVE_IFF_INJECTIVE_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ASM_MESON_TAC[]]);;

let LINV_OPT_def = new_definition
  `LINV_OPT (f:A->B) s y =
     if y IN IMAGE f s then SOME (@x. x IN s /\ (f x = y)) else NONE`;;

let LINV_LO = new_definition
  `LINV (f:A->B) s y = THE (LINV_OPT f s y)`;;

let INJ_LINV_OPT = prove
 (`INJ (f:A->B) s t ==> !x:A. !y:B.
     (LINV_OPT f s y = SOME x) <=> (y = f x) /\ x IN s /\ y IN t`,
  REWRITE_TAC[INJ; LINV_OPT_def; IN_IMAGE] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(@x:A. x IN s /\ (f:A->B) x = y) = x0` SUBST1_TAC THENL
     [MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[]; ASM_MESON_TAC[]];
    ASM_MESON_TAC[]]);;

let LINV_DEF = prove
 (`!(f:A->B) s t. INJ f s t ==> (!x. x IN s ==> (LINV f s (f x) = x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LINV_LO] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:A`; `(f:A->B) x`] o MATCH_MP INJ_LINV_OPT) THEN
  SUBGOAL_THEN `(f:A->B) x IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[INJ]; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[THE_DEF]);;

let BIJ_LINV_INV = prove
 (`!(f:A->B) s t. BIJ f s t ==> !x. x IN t ==> (f (LINV f s x) = x)`,
  REWRITE_TAC[BIJ; SURJ] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?y:A. y IN s /\ (f:A->B) y = x` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  AP_TERM_TAC THEN ASM_MESON_TAC[LINV_DEF]);;

let BIJ_LINV_BIJ = prove
 (`!(f:A->B) s t. BIJ f s t ==> BIJ (LINV f s) t s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BIJ_LINV_INV) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BIJ]) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> ASSUME_TAC(MATCH_MP LINV_DEF th) THEN MP_TAC th) MP_TAC) THEN
  REWRITE_TAC[INJ; SURJ] THEN STRIP_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[BIJ; INJ; SURJ] THEN ASM_MESON_TAC[]);;

let BIJ_IFF_INV = prove
 (`!(f:A->B) s t. BIJ f s t <=>
     (!x. x IN s ==> f x IN t) /\
     ?g. (!x. x IN t ==> g x IN s) /\ (!x. x IN s ==> (g (f x) = x)) /\
         (!x. x IN t ==> (f (g x) = x))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[BIJ; INJ]; ALL_TAC] THEN
    EXISTS_TAC `LINV (f:A->B) s` THEN
    FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP BIJ_LINV_BIJ th) THEN
                          ASSUME_TAC(MATCH_MP BIJ_LINV_INV th)) THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[BIJ; INJ];
      ASM_MESON_TAC[BIJ; LINV_DEF];
      FIRST_ASSUM ACCEPT_TAC];
    REWRITE_TAC[BIJ; INJ; SURJ] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The HOL4 [simp] / export_rewrites theorems of these theories that make   *)
(* good rewrite rules (HOL4's srw_ss, COMBIN_ss), for SIMP / FS / GVS / RW.  *)
(* ------------------------------------------------------------------------- *)

let _ = cake_add_simps
 [(* combin *)
  C_THM; UPDATE_EQ; UPDATE_APPLY1; UPDATE_APPLY_ID_RWT; I_o_ID; o_ASSOC';
  (* sum *)
  INR_INL_11; sum_distinct; sum_distinct1;
  (* option *)
  THE_DEF; IS_SOME_DEF; IS_NONE_DEF; OPTION_MAP_DEF; OPTION_BIND_DEF;
  OPTION_JOIN_DEF; OPTION_CHOICE_DEF; OPTION_APPLY_DEF; OPTION_GUARD_def;
  OPTION_ALL_def; IS_NONE_EQ_NONE; NOT_IS_SOME_EQ_NONE; option_case_ID;
  option_case_SOME_ID; IF_EQUALS_OPTION; if_option_eq; OPTION_MAP_EQ_SOME;
  OPTION_MAP_EQ_NONE_both_ways; OPTION_MAP_id; OPTION_MAP2_THM;
  OPTION_MAP2_NONE; OPTION_MAP2_SOME; OPTION_BIND_EQUALS_OPTION;
  OPTION_IGNORE_BIND_thm; OPTION_IGNORE_BIND_EQUALS_OPTION;
  OPTION_GUARD_EQ_THM; OPTION_CHOICE_NONE; OPTREL_THM; OPTREL_NONE;
  OPTREL_eq; OPTREL_refl; some_EQ; some_F;
  (* pair *)
  UNCURRY_DEF; CURRY_DEF; PAIR_MAP_THM; FST_PAIR_MAP; SND_PAIR_MAP;
  pair_map_eq; PAIR_MAP_I; PAIR_REL_THM; PAIR_REL_EQ; UNCURRY_CONST;
  CURRY_UNCURRY_THM; UNCURRY_CURRY_THM; transitive_LEX; reflexive_LEX;
  symmetric_LEX; total_LEX;
  (* prim_rec and arithmetic *)
  WF_MEASURE; measure_thm; EQ_MULT_LCANCEL; arithmetic_EQ_MULT_RCANCEL;
  arithmetic_EXP_1; EXP_EQ_1; arithmetic_EXP_EQ_0; LT1_EQ0; MAX_EQ_0;
  MIN_EQ_0; arithmetic_DIV_0; arithmetic_MOD_0; MOD_ID; DIV_ID;
  NOT_LT_ZERO_EQ_ZERO; SUC_SUB; ZERO_LT_EXP; ONE_LE_EXP; ONE_LT_EXP;
  TWO_LE_EXP; ZERO_LESS_MULT; MULT_EQ_ID; DIV2_DOUBLE; transitive_LESS;
  transitive_LE; FUNPOW_0; FUNPOW_1; NRC_0; NRC_1;
  (* While *)
  OLEAST_EQNS; OLEAST_EQ_NONE;
  (* relation *)
  RTC_REFL; RTC_SINGLE; RTC_TRANSITIVE; TC_TRANSITIVE; RTC_REFLEXIVE;
  inv_image_thm; transitive_inv_image; reflexive_inv_image;
  symmetric_inv_image; total_inv_image;
  (* pred_set (HOL Light's sets.ml theorems that are [simp] in HOL4) *)
  IN_INSERT; IN_UNION; IN_INTER; IN_DIFF; IN_DELETE; IN_UNIV; NOT_IN_EMPTY;
  IN_SING; IN_IMAGE; IN_UNIONS; IN_ELIM_THM; IN_COUNT; IN_PREIMAGE; IN_COMPL;
  SUBSET_REFL; EMPTY_SUBSET; SUBSET_EMPTY; UNIV_SUBSET; SUBSET_UNIV;
  INSERT_SUBSET; UNION_SUBSET; SUBSET_INTER; SUBSET_UNION; INTER_SUBSET;
  DELETE_SUBSET; DIFF_SUBSET; UNION_EMPTY; INTER_EMPTY; UNION_IDEMPOT;
  INTER_IDEMPOT; UNION_UNIV; INTER_UNIV; DIFF_EMPTY; EMPTY_DIFF;
  DIFF_EQ_EMPTY; EMPTY_DELETE; EMPTY_UNION; NOT_INSERT_EMPTY;
  NOT_EMPTY_INSERT; INSERT_INSERT; DISJOINT_EMPTY; PSUBSET_IRREFL;
  FINITE_EMPTY; FINITE_INSERT; FINITE_SING; FINITE_UNION; FINITE_DELETE;
  FINITE_COUNT; IMAGE_CLAUSES; IMAGE_UNION; IMAGE_EQ_EMPTY; IMAGE_ID; IMAGE_I;
  CARD_CLAUSES; CARD_EQ_0; CARD_COUNT; COUNT_ZERO; COMPL_INTER;
  INFINITE_NUM_UNIV];;

(* ------------------------------------------------------------------------- *)
(* Lemmas used by several later files.                                       *)
(* ------------------------------------------------------------------------- *)

let BASICAUX_some_unique = prove
 (`!P (a:A). P a /\ (!x. P x ==> x = a) ==> (some) P = SOME a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[some_def] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[option_INJ] THEN ASM_MESON_TAC[]);;

let BASICAUX_PAIR_SND = prove
 (`!(p:A#B) x. p = (x,SND p) <=> FST p = x`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; FST; SND]);;

let BASICAUX_pair_CASE_K = prove
 (`!(p:A#B) (x:C). pair_CASE p (\a b. x) = x`,
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE]);;
