(* ========================================================================= *)
(* clos_to_bvlProof_p1: part 1 of 3 (HOL4 lines 1-3432) of the port of      *)
(* HOL4 compiler/backend/proofs/clos_to_bvlProofScript.sml (CakeML v3479).   *)
(* Correctness proof for clos_to_bvl.                                        *)
(* The parts _p1 ... _p3 are loaded one after the other (each needs the     *)
(* previous one).                                                            *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Records: s.f (closSem state) is clos_state_f s, t.f (bvlSem state) is   *)
(*   bvl_state_f t, c.f (clos_to_bvl config) is clos_to_bvl_config_f c;      *)
(*   r with f := v is RECTYPE_f_fupd (K v) r, r with f updated_by g is       *)
(*   RECTYPE_f_fupd g r; t with <| f1 := v1; f2 := v2 |> is                  *)
(*   RECTYPE_f1_fupd (K v1) (RECTYPE_f2_fupd (K v2) t).                      *)
(* - Constants of two theories with one HOL4 name: closSem's evaluate,       *)
(*   semantics, find_code, initial_state, do_eq, v_to_list, dest_thunk, ...  *)
(*   are clos_ ones, bvlSem's bvl_ ones (decided by the types and by the     *)
(*   HOL4 Overloads at the top of the script: evaluate is bvlSem's where     *)
(*   both type-check); clos_to_bvl$compile_inc is clos_to_bvl_compile_inc'   *)
(*   (clos_to_bvl_compile_inc is the backend's); get_code_labels of closLang *)
(*   programs is clos_get_code_labels, of bvl programs bvl_get_code_labels;  *)
(*   HOL4 compile (clos_mti, clos_call, clos_known, clos_annotate) is        *)
(*   clos_mti_compile, clos_call_compile, clos_known_compile,                 *)
(*   clos_annotate_compile; fvs_inc is (clos_fvs_compile_inc:clos_prog->     *)
(*   clos_prog), the compile_inc of clos_fvs, clos_ticks, clos_letop and     *)
(*   clos_mti being polymorphic.                                            *)
(* - HOL4 Types: closSem state (C,FFI)clos_state, bvlSem state                *)
(*   (C,FFI)bvl_state; clos_co 'b is num->B#clos_prog, clos_cc 'b is          *)
(*   B->clos_prog->(byte list#int64 list#B)option; num_set is num_set.        *)
(* - HOL4 f1 SUBMAP f2 is SUBMAP (infix); FDIFF is FDIFF; BIGUNION is        *)
(*   UNIONS; set is set_of_list; GENLIST is list_of_seq; EVERY is ALL,       *)
(*   LIST_REL is ALL2; ++ is APPEND (left-associative in HOL4); $+ n is      *)
(*   (+) n; $< is (<); bag <= is SUB_BAG, (+) of bags BAG_UNION; FOLDR f e l *)
(*   is ITLIST f l e; HOL4 Abbrev (y = P) is y = P; HOL4 case is match       *)
(*   (statements with match or paired let use CASE_TERM).                    *)
(* - HOL4's paired lambdas (\(loc,args,_) exp. ...) are written as in        *)
(*   clos_to_bvl_compile_prog_def: (\p exp. match p with (loc,args,_) -> ..).*)
(* - Free variables of HOL4 statements are universally quantified, after    *)
(*   HOL4's explicit binders; unused bound variables are left out (comment). *)
(* - HOL4 theorems derived by rules (Theorem X = ..., val X = ... |> RULE)  *)
(*   are stated with their resulting statement; vals that are lists of      *)
(*   theorems (..._intros) or ML functions are comments.                     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ffi/ffi.ml";;
needs "hol4/lprefix_lub.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/proofs/clos_knownProps.ml";;
needs "compiler/backend/proofs/bvl_jumpProof.ml";;
needs "compiler/backend/proofs/clos_constantProof.ml";;
needs "compiler/backend/proofs/clos_mtiProof.ml";;
needs "compiler/backend/proofs/clos_numberProof.ml";;
needs "compiler/backend/proofs/clos_callProof.ml";;
needs "compiler/backend/proofs/clos_fvsProof.ml";;
needs "compiler/backend/proofs/clos_knownProof.ml";;
needs "compiler/backend/proofs/clos_annotateProof.ml";;

prioritize_num();;
type_invention_error := true;;

(* C2BP1AUX_ names are local helpers. *)
(* ===== PART 1: HOL4 lines 1-3432 ===== *)

(* HOL4 lines 16-24: temp_delsimps, diminish_srw_ss, set_trace and          *)
(* temp_bring_to_front_overload (evaluate is bvlSem's, num_stubs and        *)
(* compile_exps clos_to_bvl's): parser and simpset settings.                *)

(* HOL4 line 28: val EVERY2_GENLIST = LIST_REL_GENLIST |> EQ_IMP_RULE |>    *)
(* snd |> Q.GEN l (a derived theorem)                                        *)
let clos_to_bvlProof_EVERY2_GENLIST = prove
 (`!(l:A list) (R:A->B->bool) f.
     (!i. i < LENGTH l ==> R (EL i l) (f i)) ==> ALL2 R l (list_of_seq f (LENGTH l))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(l:A list) = list_of_seq (\i. EL i l) (LENGTH l)` SUBST1_TAC THENL
   [REWRITE_TAC[LIST_EQ] THEN SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ];
    REWRITE_TAC[LENGTH_LIST_OF_SEQ; LIST_REL_GENLIST] THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ]]);;

(* HOL4 line 30 *)
let EVERY_ZIP_GENLIST = prove
 (`!(xs:A list) (P:A#B->bool) f.
     (!i. i < LENGTH xs ==> P (EL i xs,f i))
     ==> ALL P (ZIP xs (list_of_seq f (LENGTH xs)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM ALL_EL] THEN
  SIMP_TAC[LENGTH_ZIP; LENGTH_LIST_OF_SEQ; EL_ZIP; EL_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[]);;

(* HOL4 line 45 *)
let IS_SUBLIST_MEM = prove
 (`!(ls:A list) ls' x. MEM x ls /\ IS_SUBLIST ls' ls ==> MEM x ls'`,
  REWRITE_TAC[IS_SUBLIST_DEF] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[MEM_APPEND]);;

(* HOL4 line 54 (HOL4's variables A B C are a b c here) *)
let IS_SUBLIST_APPEND1 = prove
 (`!(a:A list) b c. IS_SUBLIST a c ==> IS_SUBLIST (APPEND a b) c`,
  REWRITE_TAC[IS_SUBLIST_DEF] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN MESON_TAC[]);;

(* HOL4 line 64 (HOL4's variables A B C are a b c here) *)
let IS_SUBLIST_APPEND2 = prove
 (`!(a:A list) b c. IS_SUBLIST b c ==> IS_SUBLIST (APPEND a b) c`,
  REWRITE_TAC[IS_SUBLIST_DEF] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[APPEND_ASSOC] THEN MESON_TAC[]);;

(* HOL4 line 72 *)
let IS_SUBLIST_REFL = prove
 (`!(ls:A list). IS_SUBLIST ls ls`,
  REWRITE_TAC[IS_SUBLIST_DEF] THEN MESON_TAC[APPEND; APPEND_NIL]);;

(* HOL4 line 79 *)
let map2_snoc = prove
 (`!(l1:A list) (l2:B list) (f:A->B->C) x y.
     LENGTH l1 = LENGTH l2
     ==> MAP2 f (SNOC x l1) (SNOC y l2) = APPEND (MAP2 f l1 l2) [f x y]`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; SNOC; MAP2; APPEND] THEN
  ASM_SIMP_TAC[]);;

(* HOL4 line 92 *)
let el_map2 = prove
 (`!x (f:A->B->C) l1 l2.
     LENGTH l1 = LENGTH l2 /\ x < LENGTH l1 ==> EL x (MAP2 f l1 l2) = f (EL x l1) (EL x l2)`,
  INDUCT_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; MAP2; EL; HD; TL; LT; LT_SUC] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 106 *)
let length_take2 = prove
 (`!x (l:A list). ~(x <= LENGTH l) ==> LENGTH (TAKE x l) = LENGTH l`,
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC TAKE_LENGTH_TOO_LONG THEN
  ASM_ARITH_TAC);;

(* HOL4 line 117 *)
let el_take_append = prove
 (`!n (l:A list) x l2. n <= LENGTH l ==> EL n (APPEND (APPEND (TAKE n l) [x]) l2) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EL_APPEND_EQN; LENGTH_APPEND; LENGTH] THEN
  ASM_SIMP_TAC[LENGTH_TAKE; LT_REFL; SUB_REFL; EL; HD; ARITH_RULE `n < n + SUC 0`]);;

(* HOL4 line 126 *)
let el_append2 = prove
 (`!(l:A list) x. EL (LENGTH l) (APPEND l [x]) = x`,
  REWRITE_TAC[EL_APPEND_EQN; LT_REFL; SUB_REFL; EL; HD]);;

(* HOL4 line 132 *)
let el_append2_lemma = prove
 (`!n (args:A list) x. n + 1 = LENGTH args ==> EL (SUC n) (APPEND args [x]) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EL_APPEND_EQN] THEN
  ASM_SIMP_TAC[ARITH_RULE `n + 1 = l ==> ~(SUC n < l) /\ SUC n - l = 0`; EL; HD]);;

(* HOL4 line 142 *)
let hd_append = prove
 (`!(l1:A list) l2. 0 < LENGTH l1 ==> HD (APPEND l1 l2) = HD l1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; LT_REFL; APPEND; HD]);;

(* HOL4 line 148 *)
let tl_append = prove
 (`!(l1:A list) l2. 0 < LENGTH l1 ==> TL (APPEND l1 l2) = APPEND (TL l1) l2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; LT_REFL; APPEND; TL]);;

(* HOL4 line 154 *)
let twod_table_lemma = prove
 (`!x y z (f:num->num->A).
     z <= y
     ==> list_of_seq (\t. f ((t + x * y) DIV y) ((t + x * y) MOD y)) z =
         list_of_seq (\t. f x t) z`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[list_of_seq] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `z <= y /\ z < y` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `(z + x * y) DIV y = x /\ (z + x * y) MOD y = z`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC DIVMOD_UNIQ THEN ASM_ARITH_TAC);;

(* HOL4 line 169 *)
let twod_table = prove
 (`!(f:num->num->A) x y.
     0 < y
     ==> FLAT (list_of_seq (\m. list_of_seq (\n. f m n) y) x) =
         list_of_seq (\n. f (n DIV y) (n MOD y)) (x * y)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[list_of_seq; MULT_CLAUSES; FLAT] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FLAT_APPEND; FLAT; APPEND_NIL] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `x * y + y = y + x * y`] THEN
  REWRITE_TAC[GENLIST_APPEND] THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC twod_table_lemma THEN REWRITE_TAC[LE_REFL]);;

(* HOL4 line 181 *)
let less_rectangle = prove
 (`!(x:num) y m n. m < x /\ n < y ==> x * n + m < x * y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x * SUC n <= x * y` MP_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
    REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC]);;

(* HOL4 line 191 *)
let less_rectangle2 = prove
 (`!(x:num) y m n. m < x /\ n < y ==> m + n * x < x * y`,
  MESON_TAC[less_rectangle; ADD_SYM; MULT_SYM]);;

(* HOL4 line 197: val ARITH_TAC = intLib.ARITH_TAC (a tactic) *)

(* HOL4 line 199 (HOL4 multiplication binds tighter than DIV) *)
let sum_genlist_triangle_help = prove
 (`!x. SUM (list_of_seq (\y. y) (x + 1)) = (x * (x + 1)) DIV 2`,
  SUBGOAL_THEN `!x. 2 * SUM (list_of_seq (\y. y) (x + 1)) = x * (x + 1)`
    (fun th -> REWRITE_TAC[GSYM th] THEN SIMP_TAC[DIV_MULT; ARITH_EQ]) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; ONE; list_of_seq; APPEND; SUM; MULT_CLAUSES];
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC[ADD_CLAUSES; list_of_seq; SUM_APPEND; SUM] THEN
    ARITH_TAC]);;

(* HOL4 line 208 *)
let sum_genlist_triangle = prove
 (`!x. SUM (list_of_seq (\y. y) x) = (x * (x - 1)) DIV 2`,
  GEN_TAC THEN ASM_CASES_TAC `x = 0` THENL
   [ASM_REWRITE_TAC[list_of_seq; SUM; MULT_CLAUSES; DIV_0; ARITH_EQ];
    MP_TAC (SPEC `x - 1` sum_genlist_triangle_help) THEN
    ASM_SIMP_TAC[SUB_ADD; ARITH_RULE `~(x = 0) ==> 1 <= x`] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MULT_SYM]]);;

(* HOL4 line 217 *)
let triangle_table_size = prove
 (`!max (f:num->num->A).
     LENGTH (FLAT (list_of_seq (\x. list_of_seq (\y. f x y) x) max)) =
     (max * (max - 1)) DIV 2`,
  REWRITE_TAC[LENGTH_FLAT; MAP_GENLIST; o_DEF; LENGTH_LIST_OF_SEQ] THEN
  REWRITE_TAC[sum_genlist_triangle]);;

let C2BP1AUX_SUM_GENLIST_SUC = prove
 (`!n. SUM (list_of_seq (\y. y) (SUC n)) = SUM (list_of_seq (\y. y) n) + n`,
  REWRITE_TAC[list_of_seq; SUM_APPEND; SUM; ADD_CLAUSES]);;

let C2BP1AUX_SUM_GENLIST_MONO = prove
 (`!m n. m <= n ==> SUM (list_of_seq (\y. y) m) <= SUM (list_of_seq (\y. y) n)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[GENLIST_APPEND; SUM_APPEND; LE_ADD]);;

(* HOL4 line 224 *)
let tri_lemma = prove
 (`!tot max_app.
     tot < max_app
     ==> tot + (tot * (tot - 1)) DIV 2 < max_app + ((max_app - 1) * (max_app - 2)) DIV 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `max_app - 2 = (max_app - 1) - 1` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM sum_genlist_triangle] THEN
  MP_TAC (SPECL [`tot:num`; `max_app - 1`] C2BP1AUX_SUM_GENLIST_MONO) THEN
  ASM_ARITH_TAC);;

(* HOL4 line 243 *)
let triangle_div_lemma = prove
 (`!max_app n tot.
     tot < max_app /\ n < tot ==> n + (tot * (tot - 1)) DIV 2 < (max_app * (max_app - 1)) DIV 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM sum_genlist_triangle] THEN
  MP_TAC (SPECL [`SUC tot`; `max_app:num`] C2BP1AUX_SUM_GENLIST_MONO) THEN
  REWRITE_TAC[C2BP1AUX_SUM_GENLIST_SUC] THEN ASM_ARITH_TAC);;

(* HOL4 line 267 (HOL4's binder g is unused, left out) *)
let triangle_el = prove
 (`!n tot max_app (stuff:A list) f.
     n < tot /\ tot < max_app
     ==> EL (n + (tot * (tot - 1)) DIV 2)
           (APPEND (FLAT (list_of_seq (\tot. list_of_seq (\prev. f tot prev) tot) max_app))
              stuff) =
         f tot n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LT] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[list_of_seq; FLAT_APPEND; FLAT; APPEND_NIL; GSYM APPEND_ASSOC] THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[EL_APPEND_EQN; triangle_table_size] THEN
    REWRITE_TAC[ARITH_RULE `~(n + m < m:num) /\ (n + m) - m = n`] THEN
    ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 291 (HOL4's binder g is unused, left out) *)
let triangle_el_no_suff = prove
 (`!n tot max_app (f:num->num->A).
     n < tot /\ tot < max_app
     ==> EL (n + (tot * (tot - 1)) DIV 2)
           (FLAT (list_of_seq (\tot. list_of_seq (\prev. f tot prev) tot) max_app)) =
         f tot n`,
  MESON_TAC[triangle_el; APPEND_NIL]);;

(* HOL4 line 307 *)
let if_expand = prove
 (`!(w:A) x y z. (if x then y else z) = w <=> x /\ y = w \/ ~x /\ z = w`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 313 *)
let take_drop_lemma = prove
 (`!rem_args (arg_list:A list) stuff.
     LENGTH arg_list > rem_args
     ==> TAKE (rem_args + 1)
           (DROP (LENGTH arg_list - (rem_args + 1)) (APPEND arg_list stuff)) =
         DROP (LENGTH arg_list - (rem_args + 1)) arg_list`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[DROP_APPEND1; ARITH_RULE `l - k <= l:num`] THEN
  SUBGOAL_THEN `rem_args + 1 = LENGTH (DROP (LENGTH (arg_list:A list) - (rem_args + 1)) arg_list)`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THENL
   [REWRITE_TAC[LENGTH_DROP] THEN ASM_ARITH_TAC;
    REWRITE_TAC[TAKE_LENGTH_APPEND]]);;

(* HOL4 line 324 *)
let ETA2_THM = prove
 (`!(f:A->B->C->D->E->G) a b c. (\x y. f a b c x y) = f a b c`,
  REWRITE_TAC[ETA_AX]);;

(* HOL4 line 330 *)
let p_genlist = prove
 (`!k (exps_ps:((num#A)#num)list) n' e p loc max_app.
     EL k exps_ps = ((n',e),p) /\
     MAP SND exps_ps =
       list_of_seq (\n. loc + num_stubs max_app + 2 * n) (LENGTH exps_ps) /\
     k < LENGTH exps_ps
     ==> p = EL k (list_of_seq (\n. loc + num_stubs max_app + 2 * n) (LENGTH exps_ps))`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[EL_MAP]);;

(* HOL4 line 342 *)
let list_CASE_same = prove
 (`!(ls:A list) (P:A list->B).
     list_CASE ls (P []) (\x y. P (CONS x y)) = P ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[list_CASE]);;

let C2BP1AUX_do_app_ElemAt = prove
 (`!n tag xs (s:(C,FFI)bvl_state).
     bvl_do_app (BlockOp (ElemAt n)) [bvl_Block tag xs] s =
     if n < LENGTH xs then Rval (EL n xs,s) else Rerr (Rabort Rtype_error)`,
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[]);;

let C2BP1AUX_do_app_IntOp = prove
 (CASE_TERM `!op vs (s:(C,FFI)bvl_state).
     bvl_do_app (IntOp op) vs s =
     match bvl_do_int_app op vs with
       SOME res -> Rval (res,s)
     | NONE -> Rerr (Rabort Rtype_error)`,
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 352 (HOL4 mk_elem_at b i is bvl_Op (BlockOp (ElemAt i)) [b]) *)
let evaluate_genlist_prev_args = prove
 (`!prev_args z x tag arg_list (st:(C,FFI)bvl_state).
     bvl_evaluate
       (REVERSE (list_of_seq (\prev_arg. bvl_Op (BlockOp (ElemAt (prev_arg + LENGTH z)))
                                           [bvl_Var (LENGTH x)]) (LENGTH prev_args)),
        APPEND x (CONS (bvl_Block tag (APPEND z prev_args)) arg_list),
        st) =
     (Rval (REVERSE prev_args),st)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; list_of_seq; REVERSE; bvl_evaluate_def]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LENGTH; GENLIST_CONS; REVERSE; bvl_evaluate_APPEND] THEN
  SUBGOAL_THEN
   `(\prev_arg. bvl_Op (BlockOp (ElemAt (prev_arg + LENGTH (z:bvl_v list))))
                  [bvl_Var (LENGTH (x:bvl_v list))]) o SUC =
    (\prev_arg. bvl_Op (BlockOp (ElemAt (prev_arg + LENGTH (APPEND z [h:bvl_v]))))
                  [bvl_Var (LENGTH x)])` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LENGTH_APPEND; LENGTH; ADD_CLAUSES]; ALL_TAC] THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`APPEND z [h:bvl_v]`; `x:bvl_v list`; `tag:num`;
                                 `arg_list:bvl_v list`; `st:(C,FFI)bvl_state`]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN DISCH_THEN SUBST1_TAC THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvl_evaluate_def; LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `a < SUC (a + b)`] THEN
  SIMP_TAC[EL_LENGTH_APPEND; NULL; HD] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[REVERSE; APPEND; C2BP1AUX_do_app_ElemAt] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES; ARITH_RULE `a < SUC (a + b)`] THEN
  SIMP_TAC[EL_LENGTH_APPEND; NULL; HD] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 376 *)
let evaluate_genlist_prev_args1_simpl = prove
 (`!prev_args x y tag p n cl a (st:(C,FFI)bvl_state).
     bvl_evaluate
       (REVERSE (list_of_seq (\prev_arg. bvl_Op (BlockOp (ElemAt (prev_arg + 3))) [bvl_Var 3])
                  (LENGTH prev_args)),
        [x; y; a; bvl_Block tag (CONS p (CONS n (CONS cl prev_args)))],
        st) =
     (Rval (REVERSE prev_args),st)`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`prev_args:bvl_v list`; `[p;n;cl]:bvl_v list`; `[x;y;a]:bvl_v list`;
                 `tag:num`; `[]:bvl_v list`; `st:(C,FFI)bvl_state`]
          evaluate_genlist_prev_args) THEN
  REWRITE_TAC[LENGTH; APPEND; ARITH]);;

(* HOL4 line 390 *)
let evaluate_genlist_prev_args_no_rev = prove
 (`!prev_args z x tag arg_list (st:(C,FFI)bvl_state).
     bvl_evaluate
       (list_of_seq (\prev_arg. bvl_Op (BlockOp (ElemAt (prev_arg + LENGTH z)))
                                  [bvl_Var (LENGTH x)]) (LENGTH prev_args),
        APPEND x (CONS (bvl_Block tag (APPEND z prev_args)) arg_list),
        st) =
     (Rval prev_args,st)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; list_of_seq; bvl_evaluate_def]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LENGTH; GENLIST_CONS] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN
  SUBGOAL_THEN
   `(\prev_arg. bvl_Op (BlockOp (ElemAt (prev_arg + LENGTH (z:bvl_v list))))
                  [bvl_Var (LENGTH (x:bvl_v list))]) o SUC =
    (\prev_arg. bvl_Op (BlockOp (ElemAt (prev_arg + LENGTH (APPEND z [h:bvl_v]))))
                  [bvl_Var (LENGTH x)])` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LENGTH_APPEND; LENGTH; ADD_CLAUSES]; ALL_TAC] THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`APPEND z [h:bvl_v]`; `x:bvl_v list`; `tag:num`;
                                 `arg_list:bvl_v list`; `st:(C,FFI)bvl_state`]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN DISCH_TAC THEN
  REWRITE_TAC[bvl_evaluate_def; LENGTH_APPEND; LENGTH; ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `a < SUC (a + b)`] THEN
  SIMP_TAC[EL_LENGTH_APPEND; NULL; HD] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[REVERSE; APPEND; C2BP1AUX_do_app_ElemAt] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; ADD_CLAUSES; ARITH_RULE `a < SUC (a + b)`] THEN
  SIMP_TAC[EL_LENGTH_APPEND; NULL; HD] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[HD]);;

(* HOL4 line 414 *)
let evaluate_genlist_prev_args1_no_rev = prove
 (`!prev_args x tag p n cl args (st:(C,FFI)bvl_state).
     bvl_evaluate
       (list_of_seq (\prev_arg. bvl_Op (BlockOp (ElemAt (prev_arg + 3)))
                                  [bvl_Var (LENGTH args + 1)]) (LENGTH prev_args),
        CONS x (APPEND args [bvl_Block tag (CONS p (CONS n (CONS cl prev_args)))]),
        st) =
     (Rval prev_args,st)`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`prev_args:bvl_v list`; `[p;n;cl]:bvl_v list`; `CONS x args:bvl_v list`;
                 `tag:num`; `[]:bvl_v list`; `st:(C,FFI)bvl_state`]
          evaluate_genlist_prev_args_no_rev) THEN
  REWRITE_TAC[LENGTH; APPEND; ADD1] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

(* HOL4 line 427 *)
let evaluate_partial_app_fn_location_code = prove
 (`!max_app n total_args (st:(C,FFI)bvl_state) args tag ptr x fvs.
     partial_app_fn_location max_app total_args n IN domain (bvl_state_code st) /\
     n < total_args /\ total_args < max_app
     ==> bvl_evaluate
           ([partial_app_fn_location_code max_app
               (bvl_Op (BlockOp (ElemAt 1)) [bvl_Var (LENGTH args + 1)])
               (bvl_Op (IntOp (clos_Const (&n))) [])],
            CONS x (APPEND args
                      [bvl_Block tag (CONS ptr (CONS (bvl_Number (&total_args)) fvs))]),
            st) =
         (Rval [bvl_Number (&((total_args * (total_args - 1)) DIV 2 + n))],st)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[partial_app_fn_location_code_def; mk_const_def] THEN
  SUBGOAL_THEN `EL (LENGTH args + 1) (CONS (x:bvl_v) (APPEND args
                  [bvl_Block tag (CONS ptr (CONS (bvl_Number (&total_args)) fvs))])) =
                bvl_Block tag (CONS ptr (CONS (bvl_Number (&total_args)) fvs))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM ADD1; EL; TL] THEN SIMP_TAC[EL_LENGTH_APPEND; NULL; HD]; ALL_TAC] THEN
  SUBGOAL_THEN `int_div ((&total_args - &1) * &total_args) (&2) + &n =
                &((total_args * (total_args - 1)) DIV 2 + n)` ASSUME_TAC THENL
   [SUBGOAL_THEN `1 <= total_args` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_MUL; INT_DIV; ARITH_EQ; INT_OF_NUM_ADD] THEN
    REWRITE_TAC[MULT_SYM];
    ALL_TAC] THEN
  SIMP[bvl_evaluate_def; C2BP1AUX_do_app_ElemAt; C2BP1AUX_do_app_IntOp; bvl_do_int_app_def;
       LENGTH; LENGTH_APPEND; REVERSE; APPEND; HD; ARITH_RULE `1 <= SUC n`;
       INT_OF_NUM_EQ; ARITH_EQ]);;

(* HOL4 line 446 *)
let global_table_def = cake_def
  `global_table max_app =
     bvl_Block tuple_tag
       (FLAT (list_of_seq (\tot. list_of_seq
          (\prev. bvl_CodePtr (partial_app_fn_location max_app tot prev)) tot) max_app))`;;

(* ------------------------------------------------------------------------- *)
(* A symbolic evaluator for bvl_evaluate (HOL4 evaluates the generated code  *)
(* with simp[evaluate_def, do_app_def], whose congruences never expand the  *)
(* dead branch of a decided conditional; HOL Light's simplifier does).  One  *)
(* clause of bvl_evaluate_def (or of a given lemma, whose hypotheses are     *)
(* proved by the side prover) is unfolded at a time, and the cases and       *)
(* conditionals of the result are reduced as soon as their scrutinee is a    *)
(* constructor or their guard is decided (call by value).  The side prover   *)
(* is the simplifier with the facts, the given rewrites and a decision step  *)
(* for comparisons of numbers (ARITH_RULE from the arithmetic facts).        *)
(* ------------------------------------------------------------------------- *)

let C2BP1AUX_is_arith_fact tm =
  let tm = if is_neg tm then dest_neg tm else tm in
  (try let op,args = strip_comb tm in
       length args = 2 &&
       is_const op && mem (fst(dest_const op)) ["<"; "<="; ">"; ">="; "="] &&
       type_of (hd args) = `:num`
   with _ -> false);;

let C2BP1AUX_ARITH_DEC_CONV facts tm =
  let prove_it t =
    if facts = [] then ARITH_RULE t else
    MP (ARITH_RULE (mk_imp(list_mk_conj (map concl facts), t)))
       (end_itlist CONJ facts) in
  try EQT_INTRO (prove_it tm) with Failure _ ->
  try EQF_INTRO (prove_it (mk_neg tm)) with Failure _ ->
  failwith "C2BP1AUX_ARITH_DEC_CONV";;

(* ASM_ARITH_TAC with the arithmetic assumptions only (int facts stop it) *)
let C2BP1AUX_ARITH_TAC : tactic = fun (asl,w as g) ->
  let facts = filter (fun th -> C2BP1AUX_is_arith_fact (concl th)) (map snd asl) in
  (MAP_EVERY MP_TAC facts THEN ARITH_TAC) g;;

let C2BP1AUX_arith_ss facts =
  let afacts = filter (fun th -> C2BP1AUX_is_arith_fact (concl th)) facts in
  let dec = C2BP1AUX_ARITH_DEC_CONV afacts in
  itlist (fun pat ss -> ss_of_conv pat dec ss)
         [`m < n:num`; `m <= n:num`; `m = n:num`] (cake_active_ss());;

(* HOL4 simp with ARITH_ss *)
let C2BP1AUX_ESIMP thl : tactic = fun (asl,w as g) ->
  let ss = C2BP1AUX_arith_ss (map snd asl) in
  ASM (fun l -> CONV_TAC (SIMPLIFY_CONV ss l)) thl g;;

let C2BP1AUX_is_eval tm =
  try fst(dest_const(fst(strip_comb tm))) = "bvl_evaluate" with Failure _ -> false;;

let C2BP1AUX_eval_trace = ref false;;

(* abbreviations unfolded in the expressions before evaluation *)
let C2BP1AUX_eval_unfolds = ref [mk_const_def; mk_el_def; mk_label_def;
                                 partial_app_fn_location_code_def];;

let C2BP1AUX_EVAL_CONV (facts:thm list) (lemmas:thm list) : conv =
  let ss = C2BP1AUX_arith_ss facts in
  let lemmas' = map (fun th -> REWRITE_RULE[IMP_IMP] (SPEC_ALL th)) lemmas in
  let unfold = GEN_REWRITE_CONV I [bvl_evaluate_def; bvl_evaluate_APPEND] in
  let evfacts = filter (fun th -> let c = concl th in
                                  is_eq c && C2BP1AUX_is_eval (lhs c)) facts in
  let eqfacts = filter (fun th -> let c = snd(strip_forall(concl th)) in
                                  is_eq c && not (is_var (lhs c))) facts in
  let es_norm = RAND_CONV (REWRITE_CONV (REVERSE :: APPEND :: !C2BP1AUX_eval_unfolds) THENC
                           TOP_DEPTH_CONV BETA_CONV THENC REWRITE_CONV eqfacts) in
  let case_step = GENERAL_REWRITE_CONV false I (!cake_case_net) [] THENC
                  TOP_DEPTH_CONV BETA_CONV in
  let rec side tm =
    (TRY_CONV (ONCE_DEPTH_CONV (fun t -> if C2BP1AUX_is_eval t then eval t
                                         else failwith "")) THENC
     SIMPLIFY_CONV ss (facts @ lemmas)) tm
  and norm tm = try side tm with Failure _ -> REFL tm
  and try_lemma tm =
    tryfind (fun th ->
        if is_imp (concl th) then
          let ith = IMP_REWR_CONV th tm in
          let ant = lhand(concl ith) in
          (* variables of the hypotheses that the match leaves open are found *)
          (* by evaluating the hypotheses bvl_evaluate (...) = pattern        *)
          let fvs = subtract (frees ant) (union (frees tm) (freesl (map concl facts))) in
          let ith =
            if fvs = [] then ith else
            itlist (fun c ith ->
                let ant = lhand(concl ith) in
                let c = find (fun c' -> is_eq c' && C2BP1AUX_is_eval (lhs c') &&
                                        intersect (frees (rhs c')) fvs <> [] &&
                                        aconv (lhs c') (lhs c)) (conjuncts ant) in
                let eth = eval (lhs c) in
                let pat = rhs c in
                let inst = term_match (subtract (frees pat) fvs) pat (rand(concl eth)) in
                INSTANTIATE inst ith)
              (filter (fun c -> is_eq c && C2BP1AUX_is_eval (lhs c) &&
                                intersect (frees (rhs c)) fvs <> []) (conjuncts ant)) ith in
          let ant = lhand(concl ith) in
          let ath = EQT_ELIM (side ant) in
          MP ith ath
        else REWR_CONV th tm) (evfacts @ lemmas')
  and reduce tm =
    if C2BP1AUX_is_eval tm then eval tm
    else if is_case_app tm then
      let c,x,fs = dest_case_app tm in
      let n = length fs in
      let th1 = funpow n RATOR_CONV (RAND_CONV reduce) tm in
      let tm1 = rand(concl th1) in
      let _,x1,_ = dest_case_app tm1 in
      match (try Some (case_step tm1) with Failure _ -> None) with
        Some th2 -> TRANS th1 (TRANS th2 (reduce (rand(concl th2))))
      | None ->
         if is_cond x1 then
           let v = genvar (type_of x1) in
           let f = mk_abs(v,list_mk_comb(c,v::fs)) in
           let b,(y1,y2) = dest_cond x1 in
           let th2 = ISPECL [b; f; y1; y2] COND_RAND in
           let th2 = CONV_RULE (LAND_CONV BETA_CONV THENC
                                RAND_CONV (RAND_CONV BETA_CONV THENC
                                           RATOR_CONV(RAND_CONV BETA_CONV))) th2 in
           TRANS th1 (TRANS th2 (reduce (rand(concl th2))))
         else th1
    else if is_cond tm then
      let th1 = RATOR_CONV(RATOR_CONV(RAND_CONV norm)) tm in
      let tm1 = rand(concl th1) in
      let b,(x,y) = dest_cond tm1 in
      if b = `T` then
        let th2 = CONJUNCT1 (ISPECL [x; y] COND_CLAUSES) in
        TRANS th1 (TRANS th2 (reduce x))
      else if b = `F` then
        let th2 = CONJUNCT2 (ISPECL [x; y] COND_CLAUSES) in
        TRANS th1 (TRANS th2 (reduce y))
      else TRANS th1 ((RAND_CONV reduce THENC RATOR_CONV(RAND_CONV reduce)) tm1)
    else norm tm
  and eval tm =
    let th0 = es_norm tm in
    let tm0 = rand(concl th0) in
    match (try Some (try_lemma tm0) with Failure _ -> None) with
      Some th1 -> TRANS th0 (TRANS th1 (reduce (rand(concl th1))))
    | None ->
    match (try Some (unfold tm0) with Failure _ -> None) with
      Some th1 -> TRANS th0 (TRANS th1 (reduce (rand(concl th1))))
    | None ->
      (if !C2BP1AUX_eval_trace then
         (Format.print_string "C2BP1AUX_EVAL stuck at ";
          print_term tm0; Format.print_newline()) else ());
      th0 in
  fun tm -> if C2BP1AUX_is_eval tm then eval tm else failwith "C2BP1AUX_EVAL_CONV";;

let C2BP1AUX_EVAL_TAC lemmas : tactic = fun (asl,w as g) ->
  CONV_TAC (ONCE_DEPTH_CONV (C2BP1AUX_EVAL_CONV (map snd asl) lemmas)) g;;

let C2BP1AUX_EVAL_LHS_TAC lemmas : tactic = fun (asl,w as g) ->
  CONV_TAC (LAND_CONV (C2BP1AUX_EVAL_CONV (map snd asl) lemmas)) g;;

let C2BP1AUX_do_app_TagEq = prove
 (`!n tag xs (s:(C,FFI)bvl_state).
     bvl_do_app (BlockOp (TagEq n)) [bvl_Block tag xs] s = Rval (bvl_Boolv (tag = n),s)`,
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[]);;

let C2BP1AUX_do_app_LengthBlock = prove
 (`!tag xs (s:(C,FFI)bvl_state).
     bvl_do_app (BlockOp LengthBlock) [bvl_Block tag xs] s =
     Rval (bvl_Number (&(LENGTH xs)),s)`,
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[]);;

let C2BP1AUX_do_app_Label = prove
 (`!n (s:(C,FFI)bvl_state).
     bvl_do_app (clos_Label n) [] s =
     if n IN domain (bvl_state_code s) then Rval (bvl_CodePtr n,s)
     else Rerr (Rabort Rtype_error)`,
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[]);;

let C2BP1AUX_do_app_El = prove
 (`!tag xs i (s:(C,FFI)bvl_state).
     bvl_do_app (MemOp clos_El) [bvl_Block tag xs; bvl_Number i] s =
     if &0 <= i /\ num_of_int i < LENGTH xs then Rval (EL (num_of_int i) xs,s)
     else Rerr (Rabort Rtype_error)`,
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[]);;

let C2BP1AUX_do_app_Global = prove
 (CASE_TERM `!n (s:(C,FFI)bvl_state).
     bvl_do_app (GlobOp (clos_Global n)) [] s =
     match get_global n (bvl_state_globals s) with
       SOME (SOME v) -> Rval (v,s)
     | _ -> Rerr (Rabort Rtype_error)`,
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[]);;

let C2BP1AUX_do_app_ConsExtend = prove
 (`!tag tag' xs' lower len tot xs (s:(C,FFI)bvl_state).
     bvl_do_app (BlockOp (ConsExtend tag))
       (CONS (bvl_Block tag' xs') (CONS (bvl_Number lower) (CONS (bvl_Number len)
          (CONS (bvl_Number tot) xs)))) s =
     if lower < &0 \/ len < &0 \/ lower + len > &(LENGTH xs') \/
        tot = &0 \/ ~(tot = &(LENGTH xs) + len) then
       Rerr (Rabort Rtype_error)
     else
       Rval (bvl_Block tag (APPEND xs (TAKE (num_of_int len)
                                         (DROP (num_of_int lower) xs'))), s)`,
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[]);;

let C2BP1AUX_do_app_EqualConst_Int = prove
 (`!i j (s:(C,FFI)bvl_state).
     bvl_do_app (BlockOp (EqualConst (clos_Int i))) [bvl_Number j] s =
     Rval (bvl_Boolv (i = j),s)`,
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[]);;

let C2BP1AUX_tri_int = prove
 (`!tot n. int_div ((&tot - &1) * &tot) (&2) + &n = &(n + (tot * (tot - 1)) DIV 2)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `tot = 0` THENL
   [ASM_REWRITE_TAC[INT_MUL_RZERO; MULT_CLAUSES; DIV_0] THEN
    SIMP_TAC[INT_DIV; ARITH_EQ; DIV_0; INT_ADD_LID; ADD_CLAUSES];
    SUBGOAL_THEN `1 <= tot` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_MUL; INT_DIV; ARITH_EQ; INT_OF_NUM_ADD] THEN
    REWRITE_TAC[MULT_SYM; ADD_SYM]]);;

(* HOL4 line 453 *)
let evaluate_generic_app1 = prove
 (`!n args (st:(C,FFI)bvl_state) total_args l fvs cl max_app.
     partial_app_fn_location max_app total_args n IN domain (bvl_state_code st) /\
     n < total_args /\
     total_args < max_app /\
     n + 1 = LENGTH args /\
     get_global 0 (bvl_state_globals st) = SOME (SOME (global_table max_app)) /\
     cl = bvl_Block closure_tag
            (CONS (bvl_CodePtr l) (CONS (bvl_Number (&total_args)) fvs))
     ==> bvl_evaluate ([generate_generic_app max_app n],APPEND args [cl],st) =
         if bvl_state_clock st < n then
           (Rerr (Rabort Rtimeout_error),bvl_state_clock_fupd (K 0) st)
         else
           (Rval [bvl_Block partial_app_tag
                    (CONS (bvl_CodePtr (partial_app_fn_location max_app total_args n))
                       (CONS (bvl_Number (&(total_args - (n + 1))))
                          (CONS cl args)))],
            bvl_dec_clock n st)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x:bvl_v. EL (n + 1) (APPEND args [cl:bvl_v]) = cl /\
                EL (n + 2) (CONS x (APPEND args [cl:bvl_v])) = cl /\
                TAKE (n + 1) (APPEND args [cl:bvl_v]) = args` ASSUME_TAC THENL
   [UNDISCH_THEN `n + 1 = LENGTH (args:bvl_v list)` (fun th -> ASSUME_TAC th THEN
      REWRITE_TAC[ARITH_RULE `n + 2 = SUC (n + 1)`; EL; TL] THEN
      REWRITE_TAC[th; el_append2; TAKE_LENGTH_APPEND]); ALL_TAC] THEN
  SUBGOAL_THEN `&total_args - &(n + 1) = &(total_args - (n + 1)):int` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_OF_NUM_SUB THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `n + (total_args * (total_args - 1)) DIV 2 < (max_app * (max_app - 1)) DIV 2 /\
                EL (n + (total_args * (total_args - 1)) DIV 2)
                  (FLAT (list_of_seq (\tot. list_of_seq
                    (\prev. bvl_CodePtr (partial_app_fn_location max_app tot prev)) tot)
                    max_app)) =
                bvl_CodePtr (partial_app_fn_location max_app total_args n)`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[triangle_div_lemma; triangle_el_no_suff]; ALL_TAC] THEN
  FIRST_X_ASSUM (ASSUME_TAC o SYM o check (fun th -> rhs(concl th) = `LENGTH (args:bvl_v list)`)) THEN
  FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `cl:bvl_v`)) THEN
  REWRITE_TAC[generate_generic_app_def] THEN
  C2BP1AUX_EVAL_TAC[C2BP1AUX_do_app_IntOp; bvl_do_int_app_def; C2BP1AUX_do_app_ElemAt;
                    C2BP1AUX_do_app_TagEq; C2BP1AUX_do_app_El; C2BP1AUX_do_app_Global;
                    bvl_do_app_Cons; evaluate_mk_tick; evaluate_genlist_vars_rev;
                    INT_OF_NUM_LT; INT_OF_NUM_EQ; LENGTH; LENGTH_APPEND; HD; REVERSE; APPEND;
                    C2BP1AUX_tri_int; triangle_table_size; global_table_def;
                    NUM_OF_INT_OF_NUM; INT_POS; bvl_dec_clock_def] THEN
  REWRITE_TAC[REVERSE_APPEND; REVERSE_REVERSE; REVERSE; APPEND; bvl_dec_clock_def]);;

let C2BP1AUX_eval_lemmas =
  [C2BP1AUX_do_app_IntOp; bvl_do_int_app_def; C2BP1AUX_do_app_ElemAt;
   C2BP1AUX_do_app_TagEq; C2BP1AUX_do_app_El; C2BP1AUX_do_app_Global;
   C2BP1AUX_do_app_LengthBlock; C2BP1AUX_do_app_ConsExtend; C2BP1AUX_do_app_Label;
   C2BP1AUX_do_app_EqualConst_Int;
   bvl_do_app_Cons; evaluate_mk_tick; evaluate_genlist_vars_rev; bvl_evaluate_genlist_vars;
   INT_OF_NUM_LT; INT_OF_NUM_LE; INT_OF_NUM_EQ; INT_OF_NUM_ADD; INT_OF_NUM_MUL;
   INT_OF_NUM_SUB; INT_DIV; NUM_OF_INT_OF_NUM; INT_POS; INT_GT; INT_GE; GT; GE;
   LENGTH; LENGTH_APPEND; HD; REVERSE; APPEND; bvl_dec_clock_def; global_table_def;
   triangle_table_size; REVERSE_APPEND; REVERSE_REVERSE; DROP_def; TAKE_LENGTH_ID];;

(* HOL4 line 493 *)
let evaluate_generic_app2 = prove
 (`!n args (st:(C,FFI)bvl_state) rem_args prev_args l clo cl max_app.
     partial_app_fn_location max_app (rem_args + LENGTH prev_args) (n + LENGTH prev_args) IN
       domain (bvl_state_code st) /\
     n < rem_args /\
     n + 1 = LENGTH args /\
     LENGTH prev_args > 0 /\
     rem_args + LENGTH prev_args < max_app /\
     get_global 0 (bvl_state_globals st) = SOME (SOME (global_table max_app)) /\
     cl = bvl_Block partial_app_tag
            (CONS (bvl_CodePtr l) (CONS (bvl_Number (&rem_args)) (CONS clo prev_args)))
     ==> bvl_evaluate ([generate_generic_app max_app n],APPEND args [cl],st) =
         if bvl_state_clock st < n then
           (Rerr (Rabort Rtimeout_error),bvl_state_clock_fupd (K 0) st)
         else
           (Rval [bvl_Block partial_app_tag
                    (CONS (bvl_CodePtr (partial_app_fn_location max_app
                                          (rem_args + LENGTH prev_args)
                                          (n + LENGTH prev_args)))
                       (CONS (bvl_Number (&rem_args - &(n + 1)))
                          (CONS clo (APPEND args prev_args))))],
            bvl_dec_clock n st)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x y:bvl_v. EL (n + 1) (APPEND args [cl:bvl_v]) = cl /\
                EL (n + 2) (CONS x (APPEND args [cl:bvl_v])) = cl /\
                EL (n + 3) (CONS y (CONS x (APPEND args [cl:bvl_v]))) = cl /\
                TAKE (n + 1) (APPEND args [cl:bvl_v]) = args` ASSUME_TAC THENL
   [UNDISCH_THEN `n + 1 = LENGTH (args:bvl_v list)` (fun th -> ASSUME_TAC th THEN
      REWRITE_TAC[ARITH_RULE `n + 2 = SUC (n + 1) /\ n + 3 = SUC (SUC (n + 1))`; EL; TL] THEN
      REWRITE_TAC[th; el_append2; TAKE_LENGTH_APPEND]); ALL_TAC] THEN
  FIRST_X_ASSUM (ASSUME_TAC o SYM o check (fun th -> rhs(concl th) = `LENGTH (args:bvl_v list)`)) THEN
  FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `cl:bvl_v`)) THEN
  SUBGOAL_THEN `SUC (SUC (SUC (LENGTH (prev_args:bvl_v list)))) - 3 = LENGTH prev_args /\
                rem_args - (n + 1) + n + 1 = rem_args`
    (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(((rem_args + LENGTH (prev_args:bvl_v list)) - 1) *
                 (rem_args + LENGTH prev_args)) DIV 2 + n + LENGTH prev_args <
                (max_app * (max_app - 1)) DIV 2 /\
                EL ((((rem_args + LENGTH prev_args) - 1) * (rem_args + LENGTH prev_args)) DIV 2 +
                    n + LENGTH prev_args)
                  (FLAT (list_of_seq (\tot. list_of_seq
                    (\prev. bvl_CodePtr (partial_app_fn_location max_app tot prev)) tot)
                    max_app)) =
                bvl_CodePtr (partial_app_fn_location max_app (rem_args + LENGTH prev_args)
                               (n + LENGTH prev_args))`
    STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(((rem_args + LENGTH (prev_args:bvl_v list)) - 1) *
                   (rem_args + LENGTH prev_args)) DIV 2 + n + LENGTH prev_args =
                  (n + LENGTH prev_args) +
                  ((rem_args + LENGTH prev_args) * ((rem_args + LENGTH prev_args) - 1)) DIV 2`
      SUBST1_TAC THENL [REWRITE_TAC[MULT_SYM] THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `n + LENGTH (prev_args:bvl_v list) < rem_args + LENGTH prev_args`
      ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC triangle_div_lemma THEN ASM_REWRITE_TAC[];
      MP_TAC (ISPECL [`n + LENGTH (prev_args:bvl_v list)`; `rem_args + LENGTH (prev_args:bvl_v list)`;
                      `max_app:num`;
                      `\tot prev. bvl_CodePtr (partial_app_fn_location max_app tot prev)`]
              triangle_el_no_suff) THEN
      ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  REWRITE_TAC[generate_generic_app_def] THEN
  C2BP1AUX_EVAL_TAC C2BP1AUX_eval_lemmas THEN
  SUBGOAL_THEN `n + 1 <= rem_args` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[bvl_dec_clock_def; INT_OF_NUM_SUB]);;

(* HOL4 line 560 (HOL4 Num is num_of_int; total_args >= 0 is the int        *)
(* comparison)                                                                *)
let unpack_closure_rules,unpack_closure_ind,unpack_closure_cases,unpack_closure_strongind =
  cake_inductive
  `(!total_args l fvs.
      total_args >= &0
      ==> unpack_closure
            (bvl_Block closure_tag (CONS (bvl_CodePtr l) (CONS (bvl_Number total_args) fvs)))
            ([],num_of_int total_args,
             bvl_Block closure_tag (CONS (bvl_CodePtr l) (CONS (bvl_Number total_args) fvs)))) /\
   (!prev_args rem_args l clo.
      ~(prev_args = []) /\ rem_args >= &0
      ==> unpack_closure
            (bvl_Block partial_app_tag
               (CONS (bvl_CodePtr l) (CONS (bvl_Number rem_args) (CONS clo prev_args))))
            (prev_args,num_of_int rem_args + LENGTH prev_args,clo))`;;

(* HOL4 line 572 *)
let evaluate_generic_app_partial = prove
 (`!total_args prev_args (st:(C,FFI)bvl_state) args cl sub_cl max_app.
     partial_app_fn_location max_app total_args (LENGTH prev_args + (LENGTH args - 1)) IN
       domain (bvl_state_code st) /\
     total_args < max_app /\
     LENGTH args < (total_args + 1) - LENGTH prev_args /\
     ~(LENGTH args = 0) /\
     get_global 0 (bvl_state_globals st) = SOME (SOME (global_table max_app)) /\
     unpack_closure cl (prev_args,total_args,sub_cl)
     ==> bvl_evaluate ([generate_generic_app max_app (LENGTH args - 1)],APPEND args [cl],st) =
         if bvl_state_clock st < LENGTH args - 1 then
           (Rerr (Rabort Rtimeout_error),bvl_state_clock_fupd (K 0) st)
         else
           (Rval [bvl_Block partial_app_tag
                    (CONS (bvl_CodePtr (partial_app_fn_location max_app total_args
                                          (LENGTH prev_args + (LENGTH args - 1))))
                       (CONS (bvl_Number (&(total_args - (LENGTH prev_args + LENGTH args))))
                          (CONS sub_cl (APPEND args prev_args))))],
            bvl_dec_clock (LENGTH args - 1) st)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[unpack_closure_cases; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THENL
   [MP_TAC (ISPECL [`LENGTH (args:bvl_v list) - 1`; `args:bvl_v list`; `st:(C,FFI)bvl_state`;
                    `num_of_int total_args'`; `l:num`; `fvs:bvl_v list`;
                    `bvl_Block closure_tag (CONS (bvl_CodePtr l)
                       (CONS (bvl_Number total_args') fvs))`; `max_app:num`]
            evaluate_generic_app1) THEN
    SUBGOAL_THEN `&(num_of_int total_args') = total_args'` ASSUME_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_REWRITE_TAC[GSYM INT_GE]; ALL_TAC] THEN
    RULE_ASSUM_TAC (REWRITE_RULE[LENGTH; ADD_CLAUSES; SUB_0]) THEN
    ASM_REWRITE_TAC[LENGTH; ADD_CLAUSES; APPEND_NIL] THEN
    ANTS_TAC THENL [C2BP1AUX_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `LENGTH (args:bvl_v list) - 1 + 1 = LENGTH args` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[]];
    MP_TAC (ISPECL [`LENGTH (args:bvl_v list) - 1`; `args:bvl_v list`; `st:(C,FFI)bvl_state`;
                    `num_of_int rem_args`; `prev_args':bvl_v list`; `l:num`; `clo:bvl_v`;
                    `bvl_Block partial_app_tag (CONS (bvl_CodePtr l)
                       (CONS (bvl_Number rem_args) (CONS clo prev_args')))`; `max_app:num`]
            evaluate_generic_app2) THEN
    SUBGOAL_THEN `&(num_of_int rem_args) = rem_args` ASSUME_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_REWRITE_TAC[GSYM INT_GE]; ALL_TAC] THEN
    SUBGOAL_THEN `0 < LENGTH (prev_args':bvl_v list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[LENGTH_EQ_NIL; ARITH_RULE `0 < n <=> ~(n = 0)`]; ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (args:bvl_v list) - 1 + LENGTH (prev_args':bvl_v list) =
                  LENGTH prev_args' + (LENGTH args - 1)` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[GT] THEN
    ANTS_TAC THENL [C2BP1AUX_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `rem_args - &(LENGTH (args:bvl_v list) - 1 + 1) =
                  &((num_of_int rem_args + LENGTH (prev_args':bvl_v list)) -
                    (LENGTH prev_args' + LENGTH args)):int` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_THEN `&(num_of_int rem_args) = rem_args`
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
    SUBGOAL_THEN `LENGTH (args:bvl_v list) - 1 + 1 = LENGTH args /\
                  (num_of_int rem_args + LENGTH (prev_args':bvl_v list)) -
                  (LENGTH prev_args' + LENGTH args) = num_of_int rem_args - LENGTH args /\
                  LENGTH args <= num_of_int rem_args` STRIP_ASSUME_TAC THENL
     [C2BP1AUX_ARITH_TAC; ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[INT_OF_NUM_SUB]]]);;

let C2BP1AUX_evaluate_Jump_GENLIST = prove
 (`!x (f:num->bvl_exp) k env (s:(C,FFI)bvl_state) i t.
     bvl_evaluate ([x],env,s) = (Rval [bvl_Number (&i)],t) /\ i < k
     ==> bvl_evaluate ([bvl_jump_Jump x (list_of_seq f k)],env,s) =
         bvl_evaluate ([f i],CONS (bvl_Number (&i)) env,t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`x:bvl_exp`; `env:bvl_v list`; `s:(C,FFI)bvl_state`; `i:num`;
                  `t:(C,FFI)bvl_state`; `list_of_seq (f:num->bvl_exp) k`] evaluate_Jump) THEN
  ASM_SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

(* HOL4 line 621 (HOL4's unused binder clo is left out) *)
let evaluate_generic_app_full = prove
 (CASE_TERM `!n args (st:(C,FFI)bvl_state) rem_args vs l tag exp max_app.
     lookup l (bvl_state_code st) = SOME (rem_args + 2,exp) /\
     n + 1 = LENGTH args /\
     n > rem_args /\
     rem_args < max_app
     ==> bvl_evaluate
           ([generate_generic_app max_app n],
            APPEND args
              [bvl_Block tag (CONS (bvl_CodePtr l) (CONS (bvl_Number (&rem_args)) vs))],
            st) =
         if bvl_state_clock st < rem_args + 1
         then (Rerr (Rabort Rtimeout_error),bvl_state_clock_fupd (K 0) st)
         else
           match bvl_evaluate
                   ([exp],
                    APPEND (DROP (LENGTH args - (rem_args + 1)) args)
                      [bvl_Block tag (CONS (bvl_CodePtr l) (CONS (bvl_Number (&rem_args)) vs))],
                    bvl_dec_clock (rem_args + 1) st) with
             (Rval [v],st') ->
               (match bvl_evaluate
                        ([mk_cl_call (bvl_Var 0)
                            (list_of_seq (\n. bvl_Var (n + 3)) (n - rem_args))],
                         CONS v (CONS (bvl_Number (&rem_args))
                           (CONS (bvl_Number (&rem_args - &(LENGTH args)))
                              (APPEND args
                                 [bvl_Block tag (CONS (bvl_CodePtr l)
                                                  (CONS (bvl_Number (&rem_args)) vs))]))),
                         st') with
                  (Rval v,s2) -> (Rval [HD v],s2)
                | x -> x)
           | x -> x`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `cl = bvl_Block tag (CONS (bvl_CodePtr l) (CONS (bvl_Number (&rem_args)) vs))` THEN
  SUBGOAL_THEN `!x y:bvl_v.
                TAKE (rem_args + 1) (DROP ((n + 2) - rem_args) (CONS y (CONS x (APPEND args [cl])))) =
                DROP (LENGTH args - (rem_args + 1)) args` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN `(n + 2) - rem_args = SUC (SUC (LENGTH (args:bvl_v list) - (rem_args + 1)))`
      SUBST1_TAC THENL [C2BP1AUX_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[DROP] THEN MATCH_MP_TAC take_drop_lemma THEN C2BP1AUX_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:bvl_v. EL (n + 1) (APPEND args [cl:bvl_v]) = cl /\
                EL (n + 2) (CONS x (APPEND args [cl:bvl_v])) = cl /\
                EL (n + 3) (CONS y (CONS x (APPEND args [cl:bvl_v]))) = cl` ASSUME_TAC THENL
   [UNDISCH_THEN `n + 1 = LENGTH (args:bvl_v list)` (fun th -> ASSUME_TAC th THEN
      REWRITE_TAC[ARITH_RULE `n + 2 = SUC (n + 1) /\ n + 3 = SUC (SUC (n + 1))`; EL; TL] THEN
      REWRITE_TAC[th; el_append2]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(&rem_args - &(n + 1):int) < &0 /\
                (!arg. ((arg + 2) + n) - rem_args = arg + ((n + 2) - rem_args))`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INT_ARITH `a - b < &0 <=> a < b:int`; INT_OF_NUM_LT] THEN
    UNDISCH_TAC `n > rem_args` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM (ASSUME_TAC o SYM o check (fun th -> rhs(concl th) = `LENGTH (args:bvl_v list)`)) THEN
  FIRST_X_ASSUM (SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `cl:bvl_v`)) THEN
  REWRITE_TAC[generate_generic_app_def] THEN
  C2BP1AUX_EVAL_LHS_TAC (C2BP1AUX_evaluate_Jump_GENLIST :: C2BP1AUX_eval_lemmas @
                         [bvl_find_code_def; LAST_APPEND; LAST; BUTLAST_APPEND; BUTLAST;
                          NOT_CONS_NIL]) THEN
  ASM_REWRITE_TAC[APPEND] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  EVERY_CASE_TAC THEN GVS[] THEN IMP_RES_TAC bvl_evaluate_SING THEN GVS[]);;

(* HOL4 line 701 *)
let mk_cl_lem = prove
 (`!l env a b c (st:(C,FFI)bvl_state).
     l < LENGTH env
     ==> bvl_evaluate (list_of_seq (\n. bvl_Var (n + 3)) l,CONS a (CONS b (CONS c env)),st) =
         bvl_evaluate (list_of_seq (\n. bvl_Var (n + 1)) l,CONS a env,st)`,
  REPEAT STRIP_TAC THEN
  W(fun (asl,w) -> MP_TAC (ISPECL [`3`; `CONS a (CONS b (CONS c env)):bvl_v list`; `l:num`;
                                   `st:(C,FFI)bvl_state`] bvl_evaluate_genlist_vars) THEN
                   MP_TAC (ISPECL [`1`; `CONS a env:bvl_v list`; `l:num`;
                                   `st:(C,FFI)bvl_state`] bvl_evaluate_genlist_vars)) THEN
  REWRITE_TAC[LENGTH] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SIMP[DROP_def]);;

(* HOL4 line 714 *)
let evaluate_mk_cl_simpl = prove
 (`!args' n v a b tag p xs (st':(C,FFI)bvl_state).
     bvl_evaluate
       ([mk_cl_call (bvl_Var 0) (list_of_seq (\n. bvl_Var (n + 3)) (LENGTH args' - (n + 1)))],
        CONS v (CONS a (CONS b
          (APPEND args'
             [bvl_Block tag (CONS (bvl_CodePtr p) (CONS (bvl_Number (&n)) xs))]))),
        st') =
     bvl_evaluate
       ([mk_cl_call (bvl_Var 0) (list_of_seq (\n. bvl_Var (n + 1)) (LENGTH args' - (n + 1)))],
        CONS v (APPEND args'
                  [bvl_Block tag (CONS (bvl_CodePtr p) (CONS (bvl_Number (&n)) xs))]),
        st')`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `LENGTH (args':bvl_v list) - (n + 1) <
                LENGTH (APPEND args' [bvl_Block tag (CONS (bvl_CodePtr p)
                                       (CONS (bvl_Number (&n)) xs))])` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[mk_cl_call_def; bvl_evaluate_def; bvl_evaluate_APPEND] THEN
  ASM_SIMP_TAC[mk_cl_lem; LENGTH_LIST_OF_SEQ; EL; HD; LENGTH; LT_0]);;

(* HOL4 line 737 (HOL4's binder exp2 is unused, left out) *)
let evaluate_mk_cl_call = prove
 (CASE_TERM `!cl env (s:(C,FFI)bvl_state) tag p n args args' exp xs max_app.
     bvl_evaluate ([cl],env,s) =
       (Rval [bvl_Block tag (CONS (bvl_CodePtr p) (CONS (bvl_Number (&n)) xs))],s) /\
     bvl_evaluate (args,env,s) = (Rval args',s) /\
     lookup p (bvl_state_code s) = SOME (n + 2,exp) /\
     lookup (generic_app_fn_location (LENGTH args' - 1)) (bvl_state_code s) =
       SOME (LENGTH args' + 1,generate_generic_app max_app (LENGTH args' - 1)) /\
     LENGTH args' - 1 >= n /\
     n < max_app /\
     ~(LENGTH args = 0)
     ==> bvl_evaluate ([mk_cl_call cl args],env,s) =
         if n = LENGTH args - 1 then
           if bvl_state_clock s < LENGTH args
           then (Rerr (Rabort Rtimeout_error),bvl_state_clock_fupd (K 0) s)
           else bvl_evaluate
                  ([exp],
                   APPEND args'
                     [bvl_Block tag (CONS (bvl_CodePtr p)
                                       (CONS (bvl_Number (&(LENGTH args - 1))) xs))],
                   bvl_dec_clock (LENGTH args) s)
         else
           if bvl_state_clock s < n + 2
           then (Rerr (Rabort Rtimeout_error),bvl_state_clock_fupd (K 0) s)
           else
             match bvl_evaluate
                     ([exp],
                      APPEND (DROP (LENGTH args' - (n + 1)) args')
                        [bvl_Block tag (CONS (bvl_CodePtr p) (CONS (bvl_Number (&n)) xs))],
                      bvl_dec_clock (n + 2) s) with
               (Rval [v],st') ->
                 (match bvl_evaluate
                          ([mk_cl_call (bvl_Var 0)
                              (list_of_seq (\n. bvl_Var (n + 1)) (LENGTH args' - (n + 1)))],
                           CONS v (APPEND args'
                                     [bvl_Block tag (CONS (bvl_CodePtr p)
                                                       (CONS (bvl_Number (&n)) xs))]),
                           st') with
                    (Rval v,s2) -> (Rval [HD v],s2)
                  | x -> x)
             | x -> x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (args':bvl_v list) = LENGTH (args:bvl_exp list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[bvl_evaluate_IMP_LENGTH]; ALL_TAC] THEN
  UNDISCH_THEN `LENGTH (args':bvl_v list) = LENGTH (args:bvl_exp list)`
    (fun th -> RULE_ASSUM_TAC (REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
  ASM_CASES_TAC `n = LENGTH (args:bvl_exp list) - 1` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC (LAND_CONV (REWRITE_CONV[mk_cl_call_def])) THEN
  C2BP1AUX_EVAL_LHS_TAC (C2BP1AUX_eval_lemmas @
                         [bvl_find_code_def; LAST_APPEND; LAST; BUTLAST_APPEND; BUTLAST;
                          NOT_CONS_NIL; bvl_Boolv_11; evaluate_generic_app_full;
                          generic_app_fn_location_def]) THENL
   [SUBGOAL_THEN `LENGTH (args:bvl_exp list) - 1 + 1 = LENGTH args` SUBST1_TAC THENL
     [C2BP1AUX_ARITH_TAC; REWRITE_TAC[]];
    SUBGOAL_THEN `LENGTH (args:bvl_exp list) - 1 - n = LENGTH (args':bvl_v list) - (n + 1)`
      SUBST1_TAC THENL [C2BP1AUX_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[evaluate_mk_cl_simpl] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!c. c - 1 - (n + 1) = c - (n + 2)` ASSUME_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    SIMP[bvl_dec_clock_def] THEN
    ASM_CASES_TAC `bvl_state_clock (s:(C,FFI)bvl_state) < n + 2` THEN ASM_REWRITE_TAC[] THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      C2BP1AUX_ARITH_TAC;
      SUBGOAL_THEN `~(bvl_state_clock (s:(C,FFI)bvl_state) = 0) /\
                    ~(bvl_state_clock s - 1 < n + 1)` (fun th -> REWRITE_TAC[th]) THEN
      C2BP1AUX_ARITH_TAC]]);;

(* HOL4 line 788 *)
let evaluate_partial_app_fn = prove
 (`!num_args args' num_args' prev_args tag num tag' l l' fvs exp code.
     lookup l code = SOME (LENGTH args' + LENGTH prev_args + 1,exp) /\
     ~(LENGTH prev_args = 0) /\
     LENGTH prev_args < num_args /\
     num_args = LENGTH prev_args + LENGTH args'
     ==> !(st:(C,FFI)bvl_state).
           bvl_evaluate
             ([generate_partial_app_closure_fn (num_args - 1) (LENGTH prev_args - 1)],
              APPEND (DROP ((LENGTH args' + LENGTH prev_args) - num_args) args')
                [bvl_Block tag
                   (CONS l' (CONS num
                      (CONS (bvl_Block tag' (CONS (bvl_CodePtr l) (CONS num_args' fvs)))
                         prev_args)))],
              bvl_state_code_fupd (K code) st) =
           if bvl_state_clock st = 0 then
             (Rerr (Rabort Rtimeout_error),bvl_state_code_fupd (K code) st)
           else
             bvl_evaluate
               ([exp],
                APPEND (APPEND (DROP ((LENGTH args' + LENGTH prev_args) - num_args) args')
                          prev_args)
                  [bvl_Block tag' (CONS (bvl_CodePtr l) (CONS num_args' fvs))],
                bvl_dec_clock 1 (bvl_state_code_fupd (K code) st))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[ARITH_RULE `(a + l) - (l + a) = 0`; DROP_0] THEN
  ABBREV_TAC `inner = bvl_Block tag' (CONS (bvl_CodePtr l) (CONS num_args' fvs))` THEN
  ABBREV_TAC `cl = bvl_Block tag (CONS l' (CONS num (CONS inner prev_args)))` THEN
  REWRITE_TAC[generate_partial_app_closure_fn_def] THEN
  SUBGOAL_THEN `((LENGTH prev_args + LENGTH args') - 1) - (LENGTH prev_args - 1) = LENGTH (args':bvl_v list) /\
                (LENGTH (prev_args:bvl_v list) - 1) + 1 = LENGTH prev_args`
    (fun th -> REWRITE_TAC[th]) THENL [C2BP1AUX_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x:bvl_v. EL (LENGTH args') (APPEND args' [cl:bvl_v]) = cl /\
                EL (LENGTH args' + 1) (CONS x (APPEND args' [cl:bvl_v])) = cl /\
                TAKE (LENGTH args') (APPEND args' [cl:bvl_v]) = args'` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM ADD1; EL; TL; el_append2; TAKE_LENGTH_APPEND]; ALL_TAC] THEN
  FIRST_X_ASSUM (SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `cl:bvl_v`)) THEN
  FIRST_X_ASSUM (SUBST_ALL_TAC o SYM o check (fun th -> rhs(concl th) = `inner:bvl_v`)) THEN
  C2BP1AUX_EVAL_LHS_TAC (C2BP1AUX_eval_lemmas @
                         [bvl_find_code_def; LAST_APPEND; LAST; BUTLAST_APPEND; BUTLAST;
                          NOT_CONS_NIL; evaluate_genlist_prev_args1_no_rev]) THEN
  COND_CASES_TAC THEN SIMP[bvl_state_component_equality; ARITH]);;

(* HOL4 line 828 *)
let clos_to_bvlProof_code_installed_def = cake_def
  `clos_to_bvlProof_code_installed (aux:(num#num#bvl_exp)list) code <=>
     ALL (\(n,num_args,exp). lookup n code = SOME (num_args,exp)) aux`;;

(* HOL4 line 833 *)
let closure_code_installed_def = cake_def
  `closure_code_installed max_app code (exps_ps:((num#clos_exp)#num)list)
     (env:clos_v list) <=>
     ALL (\((n,exp),p).
            n <= max_app /\
            ~(n = 0) /\
            ?aux c aux1.
              clos_to_bvl_compile_exps max_app [exp] aux = ([c],aux1) /\
              lookup p code =
                SOME (n + 1,SND (code_for_recc_case (LENGTH env + LENGTH exps_ps) n c)) /\
              clos_to_bvlProof_code_installed aux1 code) exps_ps`;;

(* HOL4 line 844 (HOL4 Let is bvl's) *)
let cl_rel_rules,cl_rel_ind,cl_rel_cases,cl_rel_strongind = cake_inductive
  `(!max_app fs refs code env ys p num_args x aux c aux1.
      num_args <= max_app /\
      ~(num_args = 0) /\
      every_Fn_SOME [x] /\
      every_Fn_vs_SOME [x] /\
      clos_to_bvl_compile_exps max_app [x] aux = ([c],aux1) /\
      clos_to_bvlProof_code_installed aux1 code /\
      lookup (p + num_stubs max_app) code =
        SOME (num_args + 1:num,
              bvl_Let (APPEND (list_of_seq bvl_Var num_args)
                         (free_let (bvl_Var num_args) (LENGTH env))) c)
      ==> cl_rel max_app (fs:num->bool) (refs:(num,(bvl_v)bvl_ref)fmap) code (env,ys)
            (clos_Closure (SOME p) [] env num_args x)
            (bvl_Block closure_tag
               (CONS (bvl_CodePtr (p + num_stubs max_app))
                  (CONS (bvl_Number (&(num_args - 1))) ys)))) /\
   (!max_app fs refs code env ys p num_args x aux c aux1.
      num_args <= max_app /\
      ~(num_args = 0) /\
      every_Fn_SOME [x] /\
      every_Fn_vs_SOME [x] /\
      clos_to_bvl_compile_exps max_app [x] aux = ([c],aux1) /\
      clos_to_bvlProof_code_installed aux1 code /\
      lookup (p + num_stubs max_app) code =
        SOME (num_args + 1:num,
              bvl_Let (APPEND (list_of_seq bvl_Var (num_args + 1))
                         (free_let (bvl_Var num_args) (LENGTH env))) c)
      ==> cl_rel max_app fs refs code (env,ys)
            (clos_Recclosure (SOME p) [] env [(num_args,x)] 0)
            (bvl_Block closure_tag
               (CONS (bvl_CodePtr (p + num_stubs max_app))
                  (CONS (bvl_Number (&(num_args - 1))) ys)))) /\
   (!max_app fs refs code env ys exps exps_ps ps loc rs r k.
      exps = MAP FST exps_ps /\
      ps = MAP SND exps_ps /\
      ps = list_of_seq (\n. loc + num_stubs max_app + 2 * n) (LENGTH exps_ps) /\
      rs = MAP (\((n,e),p). bvl_Block closure_tag
                              [bvl_CodePtr p; bvl_Number (&(n - 1)); bvl_RefPtr T r])
             exps_ps /\
      ~(r IN fs) /\
      FLOOKUP refs r = SOME (bvl_ValueArray (APPEND rs ys)) /\
      1 < LENGTH exps /\ k < LENGTH exps /\
      every_Fn_SOME (MAP SND exps) /\
      every_Fn_vs_SOME (MAP SND exps) /\
      closure_code_installed max_app code exps_ps env
      ==> cl_rel max_app fs refs code (env,ys)
            (clos_Recclosure (SOME loc) [] env exps k) (EL k rs))`;;

(* HOL4 line 883 *)
let add_args_def = cake_def
  `(add_args (clos_Closure loc_opt args env num_args exp) args' =
      SOME (clos_Closure loc_opt (APPEND args' args) env num_args exp)) /\
   (add_args (clos_Recclosure loc_opt args env funs i) args' =
      SOME (clos_Recclosure loc_opt (APPEND args' args) env funs i)) /\
   (add_args (_:clos_v) (_:clos_v list) = NONE)`;;

(* HOL4 line 891 *)
let add_args_append = prove
 (`!cl arg_env func args.
     add_args cl arg_env = SOME func
     ==> add_args cl (APPEND args arg_env) = add_args func args`,
  GEN_TAC THEN CASES_ON `cl:clos_v` THEN
  REWRITE_TAC[add_args_def; option_DISTINCT; option_INJ] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[add_args_def; APPEND_ASSOC]);;

(* HOL4 line 901 *)
let get_num_args_def = cake_def
  `(get_num_args (clos_Closure loc_opt args env num_args exp) = SOME num_args) /\
   (get_num_args (clos_Recclosure loc_opt args env funs i) = SOME (FST (EL i funs))) /\
   (get_num_args (_:clos_v) = NONE)`;;

(* HOL4 line 909 *)
let clos_to_bvlProof_v_rel_rules,clos_to_bvlProof_v_rel_ind,clos_to_bvlProof_v_rel_cases,
    clos_to_bvlProof_v_rel_strongind = cake_inductive
  `(!max_app f refs code n.
      clos_to_bvlProof_v_rel max_app f refs code (clos_Number n) (bvl_Number n)) /\
   (!max_app f refs code w.
      clos_to_bvlProof_v_rel max_app f refs code (clos_Word64 w) (bvl_Word64 w)) /\
   (!max_app f refs code xs ys t.
      ALL2 (clos_to_bvlProof_v_rel max_app f refs code) xs (ys:bvl_v list)
      ==> clos_to_bvlProof_v_rel max_app f refs code (clos_Block t xs)
            (bvl_Block (clos_tag_shift t) ys)) /\
   (!max_app f refs code p bs.
      FLOOKUP refs p = SOME (bvl_ByteArray T bs) /\ ~(p IN FRANGE f)
      ==> clos_to_bvlProof_v_rel max_app f refs code (ByteVector bs) (bvl_RefPtr T p)) /\
   (!max_app f refs code r1 r2 b.
      FLOOKUP f r1 = SOME r2
      ==> clos_to_bvlProof_v_rel max_app f refs code (clos_RefPtr b r1) (bvl_RefPtr b r2)) /\
   (!max_app f refs code env fvs cl p n ys.
      ALL2 (clos_to_bvlProof_v_rel max_app f refs code) env fvs /\
      cl_rel max_app (FRANGE f) refs code (env,fvs) cl
        (bvl_Block closure_tag (CONS (bvl_CodePtr p) (CONS (bvl_Number n) ys)))
      ==> clos_to_bvlProof_v_rel max_app f refs code cl
            (bvl_Block closure_tag (CONS (bvl_CodePtr p) (CONS (bvl_Number n) ys)))) /\
   (!max_app f refs code env fvs arg_env ys num_args cl cl_app cl'.
      ALL2 (clos_to_bvlProof_v_rel max_app f refs code) env fvs /\
      ALL2 (clos_to_bvlProof_v_rel max_app f refs code) arg_env ys /\
      ~(arg_env = []) /\
      LENGTH arg_env < num_args /\
      lookup (partial_app_fn_location max_app (num_args - 1) (LENGTH ys - 1)) code =
        SOME ((num_args - LENGTH arg_env) + 1,
              generate_partial_app_closure_fn (num_args - 1) (LENGTH ys - 1)) /\
      add_args cl arg_env = SOME cl_app /\
      get_num_args cl = SOME num_args /\
      cl_rel max_app (FRANGE f) refs code (env,fvs) cl cl'
      ==> clos_to_bvlProof_v_rel max_app f refs code cl_app
            (bvl_Block partial_app_tag
               (CONS (bvl_CodePtr (partial_app_fn_location max_app (num_args - 1)
                                     (LENGTH ys - 1)))
                  (CONS (bvl_Number (&((num_args - 1) - LENGTH arg_env)))
                     (CONS cl' ys)))))`;;
(* HOL4 line 944 *)
let cl_rel_F = prove
 (`!max_app f refs code env ys i cl w b p tag xs bs.
     ~cl_rel max_app f refs code (env,ys) (clos_Number i) cl /\
     ~cl_rel max_app f refs code (env,ys) (clos_Word64 w) cl /\
     ~cl_rel max_app f refs code (env,ys) (clos_RefPtr b p) cl /\
     ~cl_rel max_app f refs code (env,ys) (clos_Block tag xs) cl /\
     ~cl_rel max_app f refs code (env,ys) (ByteVector bs) cl`,
  REWRITE_TAC[cl_rel_cases] THEN SIMP[]);;

(* HOL4 line 954 *)
let add_args_F = prove
 (`!cl args p i tag xs b w bs.
     ~(add_args cl args = SOME (clos_RefPtr b p)) /\
     ~(add_args cl args = SOME (clos_Number i)) /\
     ~(add_args cl args = SOME (clos_Word64 w)) /\
     ~(add_args cl args = SOME (clos_Block tag xs)) /\
     ~(add_args cl args = SOME (ByteVector bs))`,
  GEN_TAC THEN CASES_ON `cl:clos_v` THEN SIMP[add_args_def]);;

(* HOL4 line 966 *)
let clos_to_bvlProof_v_rel_Unit = prove
 (`!max_app f refs code y x.
     (clos_to_bvlProof_v_rel max_app f refs code clos_Unit y <=> y = bvl_Unit) /\
     (clos_to_bvlProof_v_rel max_app f refs code x bvl_Unit <=> x = clos_Unit)`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_to_bvlProof_v_rel_cases] THEN
  REWRITE_TAC[clos_Unit_def; bvl_Unit_def] THEN
  SIMP[cl_rel_F; add_args_F; ALL2; clos_tag_shift_def; tuple_tag_def; closure_tag_def;
       partial_app_tag_def] THEN
  REWRITE_TAC[ARITH_RULE `0 = (if t < 30 then t else t + 2) <=> t = 0`] THEN
  MESON_TAC[]);;

let _ = cake_add_simps [clos_to_bvlProof_v_rel_Unit];;

(* HOL4 line 975 *)
let clos_to_bvlProof_v_rel_Boolv = prove
 (`!max_app f refs code b y x.
     (clos_to_bvlProof_v_rel max_app f refs code (clos_Boolv b) y <=> y = bvl_Boolv b) /\
     (clos_to_bvlProof_v_rel max_app f refs code x (bvl_Boolv b) <=> x = clos_Boolv b)`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_to_bvlProof_v_rel_cases] THEN
  REWRITE_TAC[clos_Boolv_def; bvl_Boolv_def; bool_to_tag_def] THEN
  SIMP[cl_rel_F; add_args_F; ALL2; clos_tag_shift_def; true_tag_def; false_tag_def;
       closure_tag_def; partial_app_tag_def] THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `1 = (if t < 30 then t else t + 2) <=> t = 1`;
              ARITH_RULE `0 = (if t < 30 then t else t + 2) <=> t = 0`] THEN
  MESON_TAC[]);;

let _ = cake_add_simps [clos_to_bvlProof_v_rel_Boolv];;

(* HOL4 line 984: Theorem v_rel_SIMP = map (SIMP_CONV (srw_ss()) [v_rel_cases, *)
(* cl_rel_F, add_args_F]) [the nine terms below] |> LIST_CONJ (a derived     *)
(* theorem): the cases of v_rel for these shapes with the impossible         *)
(* disjuncts removed, in the order of v_rel_cases (HOL4's simplifier may     *)
(* name the bound variables differently).                                    *)
let v_rel_SIMP = prove
 (`!max_app f refs code b p y x0 tag xs bs i w loc args env num_args exp fns k.
     (clos_to_bvlProof_v_rel max_app f refs code (clos_RefPtr b p) y <=>
      ?r2. y = bvl_RefPtr b r2 /\ FLOOKUP f p = SOME r2) /\
     (clos_to_bvlProof_v_rel max_app f refs code (clos_Block tag xs) y <=>
      ?ys. y = bvl_Block (clos_tag_shift tag) ys /\
           ALL2 (clos_to_bvlProof_v_rel max_app f refs code) xs ys) /\
     (clos_to_bvlProof_v_rel max_app f refs code (ByteVector bs) y <=>
      ?p. y = bvl_RefPtr T p /\ FLOOKUP refs p = SOME (bvl_ByteArray T bs) /\
          ~(p IN FRANGE f)) /\
     (clos_to_bvlProof_v_rel max_app f refs code (clos_Number i) y <=> y = bvl_Number i) /\
     (clos_to_bvlProof_v_rel max_app f refs code x0 (bvl_Number i) <=> x0 = clos_Number i) /\
     (clos_to_bvlProof_v_rel max_app f refs code (clos_Word64 w) y <=> y = bvl_Word64 w) /\
     (clos_to_bvlProof_v_rel max_app f refs code x0 (bvl_Word64 w) <=> x0 = clos_Word64 w) /\
     (clos_to_bvlProof_v_rel max_app f refs code (clos_Closure loc args env num_args exp) y <=>
      (?env' fvs p n ys.
         y = bvl_Block closure_tag (CONS (bvl_CodePtr p) (CONS (bvl_Number n) ys)) /\
         ALL2 (clos_to_bvlProof_v_rel max_app f refs code) env' fvs /\
         cl_rel max_app (FRANGE f) refs code (env',fvs)
           (clos_Closure loc args env num_args exp)
           (bvl_Block closure_tag (CONS (bvl_CodePtr p) (CONS (bvl_Number n) ys)))) \/
      (?env' fvs arg_env ys num_args' cl cl'.
         y = bvl_Block partial_app_tag
               (CONS (bvl_CodePtr (partial_app_fn_location max_app (num_args' - 1)
                                     (LENGTH ys - 1)))
                  (CONS (bvl_Number (&((num_args' - 1) - LENGTH arg_env))) (CONS cl' ys))) /\
         ALL2 (clos_to_bvlProof_v_rel max_app f refs code) env' fvs /\
         ALL2 (clos_to_bvlProof_v_rel max_app f refs code) arg_env ys /\
         ~(arg_env = []) /\
         LENGTH arg_env < num_args' /\
         lookup (partial_app_fn_location max_app (num_args' - 1) (LENGTH ys - 1)) code =
           SOME ((num_args' - LENGTH arg_env) + 1,
                 generate_partial_app_closure_fn (num_args' - 1) (LENGTH ys - 1)) /\
         add_args cl arg_env = SOME (clos_Closure loc args env num_args exp) /\
         get_num_args cl = SOME num_args' /\
         cl_rel max_app (FRANGE f) refs code (env',fvs) cl cl')) /\
     (clos_to_bvlProof_v_rel max_app f refs code (clos_Recclosure loc args env fns k) y <=>
      (?env' fvs p n ys.
         y = bvl_Block closure_tag (CONS (bvl_CodePtr p) (CONS (bvl_Number n) ys)) /\
         ALL2 (clos_to_bvlProof_v_rel max_app f refs code) env' fvs /\
         cl_rel max_app (FRANGE f) refs code (env',fvs)
           (clos_Recclosure loc args env fns k)
           (bvl_Block closure_tag (CONS (bvl_CodePtr p) (CONS (bvl_Number n) ys)))) \/
      (?env' fvs arg_env ys num_args' cl cl'.
         y = bvl_Block partial_app_tag
               (CONS (bvl_CodePtr (partial_app_fn_location max_app (num_args' - 1)
                                     (LENGTH ys - 1)))
                  (CONS (bvl_Number (&((num_args' - 1) - LENGTH arg_env))) (CONS cl' ys))) /\
         ALL2 (clos_to_bvlProof_v_rel max_app f refs code) env' fvs /\
         ALL2 (clos_to_bvlProof_v_rel max_app f refs code) arg_env ys /\
         ~(arg_env = []) /\
         LENGTH arg_env < num_args' /\
         lookup (partial_app_fn_location max_app (num_args' - 1) (LENGTH ys - 1)) code =
           SOME ((num_args' - LENGTH arg_env) + 1,
                 generate_partial_app_closure_fn (num_args' - 1) (LENGTH ys - 1)) /\
         add_args cl arg_env = SOME (clos_Recclosure loc args env fns k) /\
         get_num_args cl = SOME num_args' /\
         cl_rel max_app (FRANGE f) refs code (env',fvs) cl cl'))`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_to_bvlProof_v_rel_cases] THEN
  SIMP[cl_rel_F; add_args_F]);;

(* HOL4 line 997 *)
let clos_to_bvlProof_env_rel_def = cake_def
  `(clos_to_bvlProof_env_rel max_app f refs code ([]:clos_v list) ([]:bvl_v list) <=> T) /\
   (clos_to_bvlProof_env_rel max_app f refs code [] ys <=> T) /\
   (clos_to_bvlProof_env_rel max_app f refs code (CONS x xs) [] <=> F) /\
   (clos_to_bvlProof_env_rel max_app f refs code (CONS x xs) (CONS y ys) <=>
      clos_to_bvlProof_v_rel max_app f refs code x y /\
      clos_to_bvlProof_env_rel max_app f refs code xs ys)`;;

(* HOL4 line 2834: val env_rel_ind = theorem "env_rel_ind" (made here) *)
let clos_to_bvlProof_env_rel_ind = cake_ind "clos_to_bvlProof_env_rel";;

let C2BP1AUX_env_rel_NIL = prove
 (`!max_app f refs code ys. clos_to_bvlProof_env_rel max_app f refs code [] ys`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `ys:bvl_v list` list_CASES) THEN
  REWRITE_TAC[clos_to_bvlProof_env_rel_def]);;

(* HOL4 line 1005 *)
let clos_to_bvlProof_env_rel_APPEND = prove
 (`!xs1 xs2 max_app f1 refs code ys1 ys2.
     ALL2 (clos_to_bvlProof_v_rel max_app f1 refs code) xs1 xs2 /\
     clos_to_bvlProof_env_rel max_app f1 refs code ys1 ys2
     ==> clos_to_bvlProof_env_rel max_app f1 refs code (APPEND xs1 ys1) (APPEND xs2 ys2)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[ALL2; APPEND; clos_to_bvlProof_env_rel_def]);;

(* HOL4 line 1014 *)
let list_rel_IMP_env_rel = prove
 (`!xs ys max_app f refs code ts.
     ALL2 (clos_to_bvlProof_v_rel max_app f refs code) xs ys
     ==> clos_to_bvlProof_env_rel max_app f refs code xs (APPEND ys ts)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[ALL2; APPEND; clos_to_bvlProof_env_rel_def; C2BP1AUX_env_rel_NIL]);;

(* HOL4 line 1023 *)
let env_rel_IMP_LENGTH = prove
 (`!env1 env2 max_app f refs code.
     clos_to_bvlProof_env_rel max_app f refs code env1 env2 ==> LENGTH env1 <= LENGTH env2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; clos_to_bvlProof_env_rel_def; LE_0; LE_SUC] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 1031 *)
let LESS_LENGTH_env_rel_IMP = prove
 (`!env env2 n max_app f refs code.
     n < LENGTH env /\ clos_to_bvlProof_env_rel max_app f refs code env env2
     ==> n < LENGTH env2 /\
         clos_to_bvlProof_v_rel max_app f refs code (EL n env) (EL n env2)`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH; LT]; ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[clos_to_bvlProof_env_rel_def] THEN
  INDUCT_TAC THEN REWRITE_TAC[LENGTH; EL; HD; TL; LT_0; LT_SUC] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`t':bvl_v list`; `n:num`; `max_app:num`;
                                 `f:(num,num)fmap`; `refs:(num,(bvl_v)bvl_ref)fmap`;
                                 `code:(num#bvl_exp)spt`]) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4 line 1041: val env_rel_IMP_EL = LESS_LENGTH_env_rel_IMP |> SPEC_ALL |> *)
(* UNDISCH |> CONJUNCT2 |> DISCH_ALL |> GEN_ALL (a derived theorem)          *)
let env_rel_IMP_EL = prove
 (`!env env2 n max_app f refs code.
     n < LENGTH env /\ clos_to_bvlProof_env_rel max_app f refs code env env2
     ==> clos_to_bvlProof_v_rel max_app f refs code (EL n env) (EL n env2)`,
  MESON_TAC[LESS_LENGTH_env_rel_IMP]);;

(* HOL4 line 1063 *)
let clos_to_bvlProof_nth_code_def = cake_def
  `(clos_to_bvlProof_nth_code (t_co:num->C#(num#num#bvl_exp)list) 0 = LN) /\
   (clos_to_bvlProof_nth_code t_co (SUC n) =
      sptree_union (fromAList (SND (t_co 0))) (clos_to_bvlProof_nth_code (shift_seq 1 t_co) n))`;;

let clos_to_bvlProof_nth_code_ind = cake_ind "clos_to_bvlProof_nth_code";;

(* HOL4 line 1069 *)
let compile_oracle_inv_def = cake_def
  `compile_oracle_inv max_app (s_code:(num,num#clos_exp)fmap)
     (s_cc:C->clos_prog->(byte list#int64 list#C)option) (s_co:num->C#clos_prog)
     (t_code:(num#bvl_exp)spt)
     (t_cc:C->(num#num#bvl_exp)list->(byte list#int64 list#C)option)
     (t_co:num->C#(num#num#bvl_exp)list) <=>
     s_cc = pure_cc (clos_to_bvl_compile_inc' max_app) t_cc /\
     t_co = pure_co (clos_to_bvl_compile_inc' max_app) o s_co /\
     (!n cfg ps. t_co n = (cfg,ps) ==> ALL_DISTINCT (MAP FST ps)) /\
     (!n. DISJOINT (domain (sptree_union t_code (clos_to_bvlProof_nth_code t_co n)))
            (set_of_list (MAP FST (SND (t_co n))))) /\
     !n cfg e ps.
       s_co n = (cfg,e,ps)
       ==> every_Fn_SOME e /\ every_Fn_vs_SOME e /\
           ALL (\p. every_Fn_SOME [SND (SND p)]) ps /\
           ALL (\p. every_Fn_vs_SOME [SND (SND p)]) ps`;;

(* HOL4 line 1091 [simp] (made with sem1aux_def: the kit's completion of   *)
(* the catch-all over two arguments did not finish in 10 min) *)
let clos_to_bvlProof_ref_rel_def = sem1aux_def
  `(clos_to_bvlProof_ref_rel (R:A->B->bool) (clos_ValueArray vs) (bvl_ValueArray ws) <=>
      ALL2 R vs ws) /\
   (clos_to_bvlProof_ref_rel R (clos_Thunk m1 v) (bvl_Thunk m2 w) <=> m1 = m2 /\ R v w) /\
   (clos_to_bvlProof_ref_rel R (clos_ByteArray as) (bvl_ByteArray g bs) <=>
      ~g /\ as = bs) /\
   (clos_to_bvlProof_ref_rel R _ _ <=> F)`;;

let _ = cake_add_simps [clos_to_bvlProof_ref_rel_def];;

(* HOL4 line 1098 [simp] *)
let clos_to_bvlProof_ref_rel_simp = prove
 (`!(R:A->B->bool) vs y m v bs.
     (clos_to_bvlProof_ref_rel R (clos_ValueArray vs) y <=>
      ?ws. y = bvl_ValueArray ws /\ ALL2 R vs ws) /\
     (clos_to_bvlProof_ref_rel R (clos_Thunk m v) y <=> ?w. y = bvl_Thunk m w /\ R v w) /\
     (clos_to_bvlProof_ref_rel R (clos_ByteArray bs) y <=> y = bvl_ByteArray F bs)`,
  REPEAT GEN_TAC THEN CASES_ON `y:(B)bvl_ref` THEN
  REWRITE_TAC[clos_to_bvlProof_ref_rel_def] THEN SIMP[] THEN MESON_TAC[]);;

let _ = cake_add_simps [clos_to_bvlProof_ref_rel_simp];;

(* HOL4 line 1106 (HOL4 $' f is FAPPLY f) *)
let clos_to_bvlProof_state_rel_def = cake_def
  `clos_to_bvlProof_state_rel (f:(num,num)fmap) (s:(C,FFI)clos_state)
     (t:(C,FFI)bvl_state) <=>
     clos_state_ffi s = bvl_state_ffi t /\
     ALL2 (OPTREL (clos_to_bvlProof_v_rel (clos_state_max_app s) f (bvl_state_refs t)
                     (bvl_state_code t)))
       (clos_state_globals s) (DROP num_added_globals (bvl_state_globals t)) /\
     get_global 0 (bvl_state_globals t) = SOME (SOME (global_table (clos_state_max_app s))) /\
     INJ (FAPPLY f) (FDOM f) (FRANGE f) /\
     (!x y bs. FLOOKUP f x = SOME y ==> ~(FLOOKUP (bvl_state_refs t) y = SOME (bvl_ByteArray T bs))) /\
     FDOM f = FDOM (clos_state_refs s) /\
     FRANGE f SUBSET FDOM (bvl_state_refs t) /\
     (!n x. FLOOKUP (clos_state_refs s) n = SOME x
            ==> ?y m. FLOOKUP f n = SOME m /\
                      FLOOKUP (bvl_state_refs t) m = SOME y /\
                      clos_to_bvlProof_ref_rel
                        (clos_to_bvlProof_v_rel (clos_state_max_app s) f (bvl_state_refs t)
                           (bvl_state_code t)) x y) /\
     (!n. n < clos_state_max_app s
          ==> lookup (generic_app_fn_location n) (bvl_state_code t) =
              SOME (n + 2,generate_generic_app (clos_state_max_app s) n)) /\
     (!tot n. tot < clos_state_max_app s /\ n < tot
              ==> lookup (partial_app_fn_location (clos_state_max_app s) tot n)
                    (bvl_state_code t) =
                  SOME ((tot - n) + 1,generate_partial_app_closure_fn tot n)) /\
     lookup (num_stubs (clos_state_max_app s) - 2) (bvl_state_code t) =
       SOME (2,force_thunk_code) /\
     compile_oracle_inv (clos_state_max_app s) (clos_state_code s) (clos_state_compile s)
       (clos_state_compile_oracle s) (bvl_state_code t) (bvl_state_compile t)
       (bvl_state_compile_oracle t) /\
     (!name arity c.
        FLOOKUP (clos_state_code s) name = SOME (arity,c)
        ==> ?aux1 c2 aux2.
              clos_to_bvl_compile_exps (clos_state_max_app s) [c] aux1 = ([c2],aux2) /\
              lookup (name + num_stubs (clos_state_max_app s)) (bvl_state_code t) =
                SOME (arity,c2) /\
              clos_to_bvlProof_code_installed aux2 (bvl_state_code t))`;;

(* HOL4 line 1134 *)
let clos_to_bvlProof_state_rel_globals = prove
 (`!f (s:(C,FFI)clos_state) (t:(C,FFI)bvl_state).
     clos_to_bvlProof_state_rel f s t
     ==> get_global 0 (bvl_state_globals t) =
           SOME (SOME (global_table (clos_state_max_app s))) /\
         ALL2 (OPTREL (clos_to_bvlProof_v_rel (clos_state_max_app s) f (bvl_state_refs t)
                         (bvl_state_code t)))
           (clos_state_globals s) (DROP num_added_globals (bvl_state_globals t))`,
  SIMP_TAC[clos_to_bvlProof_state_rel_def]);;

(* HOL4 line 1142 *)
let clos_to_bvlProof_state_rel_clock = prove
 (`!x. (!f (s:(C,FFI)clos_state) (t:(C,FFI)bvl_state).
          clos_to_bvlProof_state_rel f s (bvl_state_clock_fupd (K x) t) <=>
          clos_to_bvlProof_state_rel f s t) /\
       (!f (s:(C,FFI)clos_state) (t:(C,FFI)bvl_state).
          clos_to_bvlProof_state_rel f (clos_state_clock_fupd (K x) s) t <=>
          clos_to_bvlProof_state_rel f s t)`,
  SIMP[clos_to_bvlProof_state_rel_def]);;

let _ = cake_add_simps [clos_to_bvlProof_state_rel_clock];;

(* HOL4 line 1149 *)
let state_rel_refs_lookup = prove
 (`!f (s1:(C,FFI)clos_state) (s2:(C,FFI)bvl_state) p x p'.
     clos_to_bvlProof_state_rel f s1 s2 /\
     FLOOKUP (clos_state_refs s1) p = SOME x /\
     FLOOKUP f p = SOME p'
     ==> ?x'. FLOOKUP (bvl_state_refs s2) p' = SOME x' /\
              clos_to_bvlProof_ref_rel
                (clos_to_bvlProof_v_rel (clos_state_max_app s1) f (bvl_state_refs s2)
                   (bvl_state_code s2)) x x'`,
  REWRITE_TAC[clos_to_bvlProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`p:num`; `x:(clos_v)clos_ref`]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[option_INJ]);;

let C2BP1AUX_FDIFF_SUBMAP_LOOKUP = prove
 (`!(r1:(A,B)fmap) r2 f1 f2 k v.
     FDIFF r1 f1 SUBMAP FDIFF r2 f2 /\ ~(k IN f1) /\ FLOOKUP r1 k = SOME v
     ==> ~(k IN f2) /\ FLOOKUP r2 k = SOME v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FLOOKUP (FDIFF (r2:(A,B)fmap) f2) k = SOME v` MP_TAC THENL
   [MATCH_MP_TAC FLOOKUP_SUBMAP THEN EXISTS_TAC `FDIFF (r1:(A,B)fmap) f1` THEN
    ASM_REWRITE_TAC[FLOOKUP_FDIFF];
    REWRITE_TAC[FLOOKUP_FDIFF] THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT]]);;

(* HOL4 line 1160 *)
let cl_rel_SUBMAP = prove
 (`!max_app f1 refs1 code env ys x y f2 refs2.
     cl_rel max_app f1 refs1 code (env,ys) x y /\
     f1 SUBSET f2 /\ FDIFF refs1 f1 SUBMAP FDIFF refs2 f2
     ==> cl_rel max_app f2 refs2 code (env,ys) x y`,
  SUBGOAL_THEN
   `!max_app f1 refs1 code e x y.
      cl_rel max_app f1 refs1 code e x y
      ==> !f2 refs2. f1 SUBSET f2 /\ FDIFF refs1 f1 SUBMAP FDIFF refs2 f2
                     ==> cl_rel max_app f2 refs2 code e x y`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC cl_rel_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC (el 0 (CONJUNCTS cl_rel_rules)) THEN ASM_MESON_TAC[];
    MATCH_MP_TAC (el 1 (CONJUNCTS cl_rel_rules)) THEN ASM_MESON_TAC[];
    MATCH_MP_TAC (el 2 (CONJUNCTS cl_rel_rules)) THEN
    MP_TAC (ISPECL [`refs:(num,(bvl_v)bvl_ref)fmap`; `refs2:(num,(bvl_v)bvl_ref)fmap`;
                    `fs:num->bool`; `f2:num->bool`; `r:num`;
                    `bvl_ValueArray (APPEND (rs:bvl_v list) ys)`]
            C2BP1AUX_FDIFF_SUBMAP_LOOKUP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[]]);;

(* the induction hypothesis of a v_rel rule induction for a list argument:  *)
(* ALL2 (\x y. !... ==> v_rel ... x y) xs ys gives the ALL2 of the goal     *)
let C2BP1AUX_ALL2_IH_TAC : tactic = fun (asl,w as g) ->
  let lists t = let _,args = strip_comb t in tl args in
  let ok th =
    let c = concl th in
    let h,args = strip_comb c in
    is_const h && fst(dest_const h) = "ALL2" && length args = 3 &&
    lists c = lists w in
  let th = find ok (map snd asl) in
  (MP_TAC (BETA_RULE th) THEN MATCH_MP_TAC MONO_ALL2 THEN BETA_TAC THEN
   REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]) g;;

(* HOL4 line 1175: val v_rel_SUBMAP = Q.prove(...) |> SPEC_ALL |> MP_CANON *)
(* (theory prefix added: clos_callProof binds v_rel_SUBMAP) *)
let clos_to_bvlProof_v_rel_SUBMAP = prove
 (`!max_app f1 refs1 code x y f2 refs2.
     clos_to_bvlProof_v_rel max_app f1 refs1 code x y /\
     f1 SUBMAP f2 /\ FDIFF refs1 (FRANGE f1) SUBMAP FDIFF refs2 (FRANGE f2)
     ==> clos_to_bvlProof_v_rel max_app f2 refs2 code x y`,
  SUBGOAL_THEN
   `!max_app f1 refs1 code x y.
      clos_to_bvlProof_v_rel max_app f1 refs1 code x y
      ==> !f2 refs2. f1 SUBMAP f2 /\ FDIFF refs1 (FRANGE f1) SUBMAP FDIFF refs2 (FRANGE f2)
                     ==> clos_to_bvlProof_v_rel max_app f2 refs2 code x y`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC clos_to_bvlProof_v_rel_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MESON_TAC[clos_to_bvlProof_v_rel_rules];
    MESON_TAC[clos_to_bvlProof_v_rel_rules];
    MATCH_MP_TAC (el 2 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN C2BP1AUX_ALL2_IH_TAC;
    MATCH_MP_TAC (el 3 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    ASM_MESON_TAC[C2BP1AUX_FDIFF_SUBMAP_LOOKUP];
    MATCH_MP_TAC (el 4 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    ASM_MESON_TAC[FLOOKUP_SUBMAP];
    MATCH_MP_TAC (el 5 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    MAP_EVERY EXISTS_TAC [`env:clos_v list`; `fvs:bvl_v list`] THEN CONJ_TAC THENL
     [C2BP1AUX_ALL2_IH_TAC;
      MATCH_MP_TAC cl_rel_SUBMAP THEN
      MAP_EVERY EXISTS_TAC [`FRANGE (f:(num,num)fmap)`; `refs:(num,(bvl_v)bvl_ref)fmap`] THEN
      ASM_SIMP_TAC[SUBMAP_FRANGE]];
    MATCH_MP_TAC (el 6 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    MAP_EVERY EXISTS_TAC [`env:clos_v list`; `fvs:bvl_v list`; `cl:clos_v`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [C2BP1AUX_ALL2_IH_TAC; C2BP1AUX_ALL2_IH_TAC;
      MATCH_MP_TAC cl_rel_SUBMAP THEN
      MAP_EVERY EXISTS_TAC [`FRANGE (f:(num,num)fmap)`; `refs:(num,(bvl_v)bvl_ref)fmap`] THEN
      ASM_SIMP_TAC[SUBMAP_FRANGE]]]);;

(* HOL4 line 1195: val env_rel_SUBMAP = Q.prove(...) |> GEN_ALL *)
(* (theory prefix added: clos_callProof binds env_rel_SUBMAP) *)
let clos_to_bvlProof_env_rel_SUBMAP = prove
 (`!env1 env2 max_app f1 refs1 code f2 refs2.
     clos_to_bvlProof_env_rel max_app f1 refs1 code env1 env2 /\
     f1 SUBMAP f2 /\ FDIFF refs1 (FRANGE f1) SUBMAP FDIFF refs2 (FRANGE f2)
     ==> clos_to_bvlProof_env_rel max_app f2 refs2 code env1 env2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[clos_to_bvlProof_env_rel_def] THEN ASM_MESON_TAC[clos_to_bvlProof_v_rel_SUBMAP]);;

let C2BP1AUX_FLOOKUP_NEQ = prove
 (`!(fm:(A,B)fmap) k1 k2 v. FLOOKUP fm k1 = SOME v /\ ~(k2 IN FDOM fm) ==> ~(k1 = k2)`,
  REWRITE_TAC[FLOOKUP_DEF] THEN MESON_TAC[option_DISTINCT]);;

let C2BP1AUX_FRANGE_FUPDATE_NOTIN = prove
 (`!(f:(A,B)fmap) pp qq. ~(pp IN FDOM f) ==> FRANGE (f |+ (pp,qq)) = qq INSERT FRANGE f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_INSERT; IN_FRANGE_FLOOKUP; FLOOKUP_UPDATE] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[option_INJ];
    ASM_MESON_TAC[];
    EXISTS_TAC `k:A` THEN ASM_MESON_TAC[C2BP1AUX_FLOOKUP_NEQ]]);;

(* HOL4 line 1203 *)
let cl_rel_NEW_REF = prove
 (`!x y max_app f1 refs1 code env ys r t.
     cl_rel max_app f1 refs1 code (env,ys) x y
     ==> ~(r IN FDOM refs1)
     ==> cl_rel max_app f1 (refs1 |+ (r,t)) code (env,ys) x y`,
  SUBGOAL_THEN
   `!max_app f1 refs1 code e x y.
      cl_rel max_app f1 refs1 code e x y
      ==> !r t. ~(r IN FDOM refs1) ==> cl_rel max_app f1 (refs1 |+ (r,t)) code e x y`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC cl_rel_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC (el 0 (CONJUNCTS cl_rel_rules)) THEN ASM_MESON_TAC[];
    MATCH_MP_TAC (el 1 (CONJUNCTS cl_rel_rules)) THEN ASM_MESON_TAC[];
    MATCH_MP_TAC (el 2 (CONJUNCTS cl_rel_rules)) THEN
    MAP_EVERY EXISTS_TAC [`exps_ps:((num#clos_exp)#num)list`; `ps:num list`; `r:num`] THEN
    ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN COND_CASES_TAC THENL
     [ASM_MESON_TAC[C2BP1AUX_FLOOKUP_NEQ]; ASM_MESON_TAC[]]]);;

(* HOL4 line 1217: val v_rel_NEW_REF = Q.prove(...) |> SPEC_ALL |> MP_CANON *)
let v_rel_NEW_REF = prove
 (`!max_app f1 refs1 code x y r t.
     clos_to_bvlProof_v_rel max_app f1 refs1 code x y /\ ~(r IN FDOM refs1)
     ==> clos_to_bvlProof_v_rel max_app f1 (refs1 |+ (r,t)) code x y`,
  SUBGOAL_THEN
   `!max_app f1 refs1 code x y.
      clos_to_bvlProof_v_rel max_app f1 refs1 code x y
      ==> !r t. ~(r IN FDOM refs1)
                ==> clos_to_bvlProof_v_rel max_app f1 (refs1 |+ (r,t)) code x y`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC clos_to_bvlProof_v_rel_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MESON_TAC[clos_to_bvlProof_v_rel_rules];
    MESON_TAC[clos_to_bvlProof_v_rel_rules];
    MATCH_MP_TAC (el 2 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN C2BP1AUX_ALL2_IH_TAC;
    MATCH_MP_TAC (el 3 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[C2BP1AUX_FLOOKUP_NEQ];
    MATCH_MP_TAC (el 4 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (el 5 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    MAP_EVERY EXISTS_TAC [`env:clos_v list`; `fvs:bvl_v list`] THEN CONJ_TAC THENL
     [C2BP1AUX_ALL2_IH_TAC; ASM_MESON_TAC[cl_rel_NEW_REF]];
    MATCH_MP_TAC (el 6 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    MAP_EVERY EXISTS_TAC [`env:clos_v list`; `fvs:bvl_v list`; `cl:clos_v`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [C2BP1AUX_ALL2_IH_TAC; C2BP1AUX_ALL2_IH_TAC; ASM_MESON_TAC[cl_rel_NEW_REF]]]);;

(* HOL4 line 1234 *)
let cl_rel_UPDATE_REF = prove
 (`!x y max_app f1 refs1 code env ys r t.
     cl_rel max_app f1 refs1 code (env,ys) x y
     ==> r IN f1
     ==> cl_rel max_app f1 (refs1 |+ (r,t)) code (env,ys) x y`,
  SUBGOAL_THEN
   `!max_app f1 refs1 code e x y.
      cl_rel max_app f1 refs1 code e x y
      ==> !r t. r IN f1 ==> cl_rel max_app f1 (refs1 |+ (r,t)) code e x y`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC cl_rel_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC (el 0 (CONJUNCTS cl_rel_rules)) THEN ASM_MESON_TAC[];
    MATCH_MP_TAC (el 1 (CONJUNCTS cl_rel_rules)) THEN ASM_MESON_TAC[];
    MATCH_MP_TAC (el 2 (CONJUNCTS cl_rel_rules)) THEN
    MAP_EVERY EXISTS_TAC [`exps_ps:((num#clos_exp)#num)list`; `ps:num list`; `r:num`] THEN
    ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN COND_CASES_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]]]);;

(* HOL4 line 1250: val v_rel_UPDATE_REF = Q.prove(...) |> SPEC_ALL |>        *)
(* MP_CANON                                                                   *)
let v_rel_UPDATE_REF = prove
 (`!max_app f1 refs1 code x y r t.
     clos_to_bvlProof_v_rel max_app f1 refs1 code x y /\ r IN FRANGE f1
     ==> clos_to_bvlProof_v_rel max_app f1 (refs1 |+ (r,t)) code x y`,
  SUBGOAL_THEN
   `!max_app f1 refs1 code x y.
      clos_to_bvlProof_v_rel max_app f1 refs1 code x y
      ==> !r t. r IN FRANGE f1
                ==> clos_to_bvlProof_v_rel max_app f1 (refs1 |+ (r,t)) code x y`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC clos_to_bvlProof_v_rel_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MESON_TAC[clos_to_bvlProof_v_rel_rules];
    MESON_TAC[clos_to_bvlProof_v_rel_rules];
    MATCH_MP_TAC (el 2 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN C2BP1AUX_ALL2_IH_TAC;
    MATCH_MP_TAC (el 3 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN COND_CASES_TAC THEN ASM_MESON_TAC[];
    MATCH_MP_TAC (el 4 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (el 5 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    MAP_EVERY EXISTS_TAC [`env:clos_v list`; `fvs:bvl_v list`] THEN CONJ_TAC THENL
     [C2BP1AUX_ALL2_IH_TAC; ASM_MESON_TAC[cl_rel_UPDATE_REF]];
    MATCH_MP_TAC (el 6 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    MAP_EVERY EXISTS_TAC [`env:clos_v list`; `fvs:bvl_v list`; `cl:clos_v`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [C2BP1AUX_ALL2_IH_TAC; C2BP1AUX_ALL2_IH_TAC; ASM_MESON_TAC[cl_rel_UPDATE_REF]]]);;

(* HOL4 line 1268 *)
let OPTREL_v_rel_NEW_REF = prove
 (`!max_app f1 refs1 code x y r t.
     OPTREL (clos_to_bvlProof_v_rel max_app f1 refs1 code) x y /\ ~(r IN FDOM refs1)
     ==> OPTREL (clos_to_bvlProof_v_rel max_app f1 (refs1 |+ (r,t)) code) x y`,
  REPEAT GEN_TAC THEN CASES_ON `x:clos_v option` THEN CASES_ON `y:bvl_v option` THEN
  REWRITE_TAC[OPTREL_def] THEN MESON_TAC[v_rel_NEW_REF]);;

(* HOL4 line 1275 *)
let OPTREL_v_rel_UPDATE_REF = prove
 (`!max_app f1 refs1 code x y r t.
     OPTREL (clos_to_bvlProof_v_rel max_app f1 refs1 code) x y /\ r IN FRANGE f1
     ==> OPTREL (clos_to_bvlProof_v_rel max_app f1 (refs1 |+ (r,t)) code) x y`,
  REPEAT GEN_TAC THEN CASES_ON `x:clos_v option` THEN CASES_ON `y:bvl_v option` THEN
  REWRITE_TAC[OPTREL_def] THEN MESON_TAC[v_rel_UPDATE_REF]);;

(* HOL4 line 1282 *)
let env_rel_NEW_REF = prove
 (`!x y max_app f1 refs1 code r t.
     clos_to_bvlProof_env_rel max_app f1 refs1 code x y /\ ~(r IN FDOM refs1)
     ==> clos_to_bvlProof_env_rel max_app f1 (refs1 |+ (r,t)) code x y`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[clos_to_bvlProof_env_rel_def] THEN ASM_MESON_TAC[v_rel_NEW_REF]);;

let C2BP1AUX_cl_rel_NEW_F_gen = prove
 (`!max_app f2 refs code e x y.
      cl_rel max_app f2 refs code e x y
      ==> !qq. ~(qq IN FDOM refs) ==> cl_rel max_app (qq INSERT f2) refs code e x y`,
  MATCH_MP_TAC cl_rel_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC (el 0 (CONJUNCTS cl_rel_rules)) THEN ASM_MESON_TAC[];
    MATCH_MP_TAC (el 1 (CONJUNCTS cl_rel_rules)) THEN ASM_MESON_TAC[];
    MATCH_MP_TAC (el 2 (CONJUNCTS cl_rel_rules)) THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[C2BP1AUX_FLOOKUP_NEQ]]);;

(* HOL4 line 1291 *)
let cl_rel_NEW_F = prove
 (`!x y max_app f2 (t2:(C,FFI)bvl_state) env ys qq.
     cl_rel max_app f2 (bvl_state_refs t2) (bvl_state_code t2) (env,ys) x y
     ==> ~(qq IN FDOM (bvl_state_refs t2))
     ==> cl_rel max_app (qq INSERT f2) (bvl_state_refs t2) (bvl_state_code t2) (env,ys) x y`,
  MESON_TAC[C2BP1AUX_cl_rel_NEW_F_gen]);;

(* HOL4 line 1304: val v_rel_NEW_F = Q.prove(...) |> SPEC_ALL |> MP_CANON *)
let v_rel_NEW_F = prove
 (`!max_app f2 (t2:(C,FFI)bvl_state) x y pp qq.
     clos_to_bvlProof_v_rel max_app f2 (bvl_state_refs t2) (bvl_state_code t2) x y /\
     ~(pp IN FDOM f2) /\ ~(qq IN FDOM (bvl_state_refs t2))
     ==> clos_to_bvlProof_v_rel max_app (f2 |+ (pp,qq)) (bvl_state_refs t2)
           (bvl_state_code t2) x y`,
  SUBGOAL_THEN
   `!max_app f2 refs code x y.
      clos_to_bvlProof_v_rel max_app f2 refs code x y
      ==> !pp qq. ~(pp IN FDOM f2) /\ ~(qq IN FDOM refs)
                  ==> clos_to_bvlProof_v_rel max_app (f2 |+ (pp,qq)) refs code x y`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC clos_to_bvlProof_v_rel_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MESON_TAC[clos_to_bvlProof_v_rel_rules];
    MESON_TAC[clos_to_bvlProof_v_rel_rules];
    MATCH_MP_TAC (el 2 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN C2BP1AUX_ALL2_IH_TAC;
    MATCH_MP_TAC (el 3 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    ASM_SIMP_TAC[C2BP1AUX_FRANGE_FUPDATE_NOTIN; IN_INSERT] THEN
    ASM_MESON_TAC[C2BP1AUX_FLOOKUP_NEQ];
    MATCH_MP_TAC (el 4 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[C2BP1AUX_FLOOKUP_NEQ];
    MATCH_MP_TAC (el 5 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    MAP_EVERY EXISTS_TAC [`env:clos_v list`; `fvs:bvl_v list`] THEN CONJ_TAC THENL
     [C2BP1AUX_ALL2_IH_TAC;
      ASM_SIMP_TAC[C2BP1AUX_FRANGE_FUPDATE_NOTIN; C2BP1AUX_cl_rel_NEW_F_gen]];
    MATCH_MP_TAC (el 6 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    MAP_EVERY EXISTS_TAC [`env:clos_v list`; `fvs:bvl_v list`; `cl:clos_v`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [C2BP1AUX_ALL2_IH_TAC; C2BP1AUX_ALL2_IH_TAC;
      ASM_SIMP_TAC[C2BP1AUX_FRANGE_FUPDATE_NOTIN; C2BP1AUX_cl_rel_NEW_F_gen]]]);;

(* HOL4 line 1325: val OPTREL_v_rel_NEW_F = Q.prove(...) |> MP_CANON *)
let OPTREL_v_rel_NEW_F = prove
 (`!max_app f2 (t2:(C,FFI)bvl_state) x y pp qq.
     OPTREL (clos_to_bvlProof_v_rel max_app f2 (bvl_state_refs t2) (bvl_state_code t2)) x y /\
     ~(pp IN FDOM f2) /\ ~(qq IN FDOM (bvl_state_refs t2))
     ==> OPTREL (clos_to_bvlProof_v_rel max_app (f2 |+ (pp,qq)) (bvl_state_refs t2)
                   (bvl_state_code t2)) x y`,
  REPEAT GEN_TAC THEN CASES_ON `x:clos_v option` THEN CASES_ON `y:bvl_v option` THEN
  REWRITE_TAC[OPTREL_def] THEN MESON_TAC[v_rel_NEW_F]);;

let C2BP1AUX_INJ_FLOOKUP = prove
 (`!(f:(A,B)fmap) x y v.
     INJ (FAPPLY f) (FDOM f) (FRANGE f) /\ FLOOKUP f x = SOME v /\ FLOOKUP f y = SOME v
     ==> x = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INJ; FLOOKUP_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let C2BP1AUX_ref_rel_MONO = prove
 (`!(R:A->B->bool) R' x y.
     clos_to_bvlProof_ref_rel R x y /\ (!a b. R a b ==> R' a b)
     ==> clos_to_bvlProof_ref_rel R' x y`,
  REPEAT GEN_TAC THEN CASES_ON `x:(A)clos_ref` THEN CASES_ON `y:(B)bvl_ref` THEN
  REWRITE_TAC[clos_to_bvlProof_ref_rel_def] THEN
  DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM (fun th -> MATCH_MP_TAC (MATCH_MP MONO_ALL2 th)) THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 1333 *)
let state_rel_UPDATE_REF = prove
 (`!f2 (p1:(C,FFI)clos_state) (t2:(C,FFI)bvl_state) dst r2 v0 v v'.
     clos_to_bvlProof_state_rel f2 p1 t2 /\
     FLOOKUP f2 dst = SOME r2 /\
     FLOOKUP (clos_state_refs p1) dst = SOME v0 /\
     clos_to_bvlProof_ref_rel
       (clos_to_bvlProof_v_rel (clos_state_max_app p1) f2 (bvl_state_refs t2)
          (bvl_state_code t2)) v v' /\
     (!bs. ~(v' = bvl_ByteArray T bs))
     ==> clos_to_bvlProof_state_rel f2
           (clos_state_refs_fupd (K (clos_state_refs p1 |+ (dst,v))) p1)
           (bvl_state_refs_fupd (K (bvl_state_refs t2 |+ (r2,v'))) t2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_to_bvlProof_state_rel_def] THEN
  SIMP[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `r2 IN FRANGE (f2:(num,num)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_FRANGE_FLOOKUP]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b. clos_to_bvlProof_v_rel (clos_state_max_app (p1:(C,FFI)clos_state)) f2
                        (bvl_state_refs (t2:(C,FFI)bvl_state)) (bvl_state_code t2) a b
                      ==> clos_to_bvlProof_v_rel (clos_state_max_app p1) f2
                            (bvl_state_refs t2 |+ (r2,v')) (bvl_state_code t2) a b`
    ASSUME_TAC THENL [ASM_MESON_TAC[v_rel_UPDATE_REF]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM (MP_TAC o check (fun th -> can (find_term ((=) `clos_state_globals (p1:(C,FFI)clos_state)`)) (concl th))) THEN
    MATCH_MP_TAC MONO_ALL2 THEN ASM_MESON_TAC[OPTREL_v_rel_UPDATE_REF];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[FLOOKUP_UPDATE] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[option_INJ]; ASM_MESON_TAC[]];
    SUBGOAL_THEN `dst IN FDOM (clos_state_refs (p1:(C,FFI)clos_state))` MP_TAC THENL
     [ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT]; ASM SET_TAC[]];
    ASM SET_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[FLOOKUP_UPDATE] THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[option_INJ] THEN DISCH_THEN SUBST_ALL_TAC THEN
      MAP_EVERY EXISTS_TAC [`v':(bvl_v)bvl_ref`; `r2:num`] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC C2BP1AUX_ref_rel_MONO THEN
      EXISTS_TAC `clos_to_bvlProof_v_rel (clos_state_max_app (p1:(C,FFI)clos_state)) f2
                    (bvl_state_refs (t2:(C,FFI)bvl_state)) (bvl_state_code t2)` THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [`n:num`; `x:(clos_v)clos_ref`] o
        check (fun th -> can (find_term ((=) `clos_to_bvlProof_ref_rel:(clos_v->bvl_v->bool)->(clos_v)clos_ref->(bvl_v)bvl_ref->bool`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`y:(bvl_v)bvl_ref`; `m:num`] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(r2:num = m)` (fun th -> REWRITE_TAC[th]) THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `~(dst:num = n)` THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC (ISPEC `f2:(num,num)fmap` C2BP1AUX_INJ_FLOOKUP) THEN
        EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C2BP1AUX_ref_rel_MONO THEN
      EXISTS_TAC `clos_to_bvlProof_v_rel (clos_state_max_app (p1:(C,FFI)clos_state)) f2
                    (bvl_state_refs (t2:(C,FFI)bvl_state)) (bvl_state_code t2)` THEN
      ASM_REWRITE_TAC[]]]);;

(* HOL4 line 1396 *)
let state_rel_NEW_REF = prove
 (`!f2 (p1:(C,FFI)clos_state) (t2:(C,FFI)bvl_state) p v.
     clos_to_bvlProof_state_rel f2 p1 t2 /\ ~(p IN FDOM (bvl_state_refs t2))
     ==> clos_to_bvlProof_state_rel f2 p1
           (bvl_state_refs_fupd (K (bvl_state_refs t2 |+ (p,v))) t2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_to_bvlProof_state_rel_def] THEN
  SIMP[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!m. m IN FRANGE (f2:(num,num)fmap) ==> ~(m = p)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM (MP_TAC o check (fun th -> can (find_term ((=) `clos_state_globals (p1:(C,FFI)clos_state)`)) (concl th))) THEN
    MATCH_MP_TAC MONO_ALL2 THEN ASM_MESON_TAC[OPTREL_v_rel_NEW_REF];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[FLOOKUP_UPDATE] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[IN_FRANGE_FLOOKUP]; ASM_MESON_TAC[]];
    ASM SET_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`n:num`; `x:(clos_v)clos_ref`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`y:(bvl_v)bvl_ref`; `m:num`] THEN
    ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN
    SUBGOAL_THEN `~(p:num = m)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[IN_FRANGE_FLOOKUP]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C2BP1AUX_ref_rel_MONO THEN
    EXISTS_TAC `clos_to_bvlProof_v_rel (clos_state_max_app (p1:(C,FFI)clos_state)) f2
                  (bvl_state_refs (t2:(C,FFI)bvl_state)) (bvl_state_code t2)` THEN
    ASM_MESON_TAC[v_rel_NEW_REF]]);;

(* HOL4 line 1431 *)
let clos_to_bvlProof_v_to_list = prove
 (`!v l v' max_app f r c.
     clos_v_to_list v = SOME l /\ clos_to_bvlProof_v_rel max_app f r c v v'
     ==> ?l'. bvl_v_to_list v' = SOME l' /\
              ALL2 (clos_to_bvlProof_v_rel max_app f r c) l l'`,
  MATCH_MP_TAC clos_v_to_list_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_v_to_list_def; option_DISTINCT] THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    REWRITE_TAC[v_rel_SIMP; LIST_REL_NIL] THEN STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[bvl_v_to_list_def; clos_tag_shift_nil_tag; ALL2] THEN
    MESON_TAC[ALL2];
    DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT] THEN
    CASES_ON `clos_v_to_list bt` THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[option_DISTINCT; option_INJ; v_rel_SIMP; LIST_REL_CONS1; LIST_REL_NIL] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`a:clos_v list`; `h'':bvl_v`; `max_app:num`;
                                   `f:(num,num)fmap`; `r:(num,(bvl_v)bvl_ref)fmap`;
                                   `c:(num#bvl_exp)spt`] o
                   REWRITE_RULE[ASSUME `tag = cons_tag`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[bvl_v_to_list_def; clos_tag_shift_cons_tag] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[option_INJ; ALL2] THEN ASM_MESON_TAC[ALL2]]);;

(* HOL4 line 1445 (HOL4 ^(closure_tag_def |> concl |> rand) is the value of *)
(* closure_tag, 30)                                                           *)
let not_isClos = prove
 (`!n (ys:A list). ~bvl_isClos (if n < 30 then n else n + 2) ys`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_isClos_def; closure_tag_def; partial_app_tag_def; DE_MORGAN_THM] THEN
  DISJ1_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let _ = cake_add_simps [not_isClos];;

let C2BP1AUX_do_eq_RefPtr = prove
 (`!(r:(num,(bvl_v)bvl_ref)fmap) b1 p1 b2 p2.
     (!bs. ~(FLOOKUP r p1 = SOME (bvl_ByteArray T bs))) /\
     (!bs. ~(FLOOKUP r p2 = SOME (bvl_ByteArray T bs)))
     ==> bvl_do_eq r (bvl_RefPtr b1 p1) (bvl_RefPtr b2 p2) =
         if b1 /\ b2 then Eq_val (p1 = p2) else Eq_type_error`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_eq_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  CASES_ON `FLOOKUP (r:(num,(bvl_v)bvl_ref)fmap) p1` THEN
  CASES_ON `FLOOKUP (r:(num,(bvl_v)bvl_ref)fmap) p2` THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN CASE_REWRITE_TAC[] THEN
  TRY (CASES_ON `a:(bvl_v)bvl_ref`) THEN TRY (CASES_ON `a':(bvl_v)bvl_ref`) THEN
  CASE_REWRITE_TAC[] THEN SIMP[] THEN MESON_TAC[]);;


let C2BP1AUX_do_eq_BV_BV = prove
 (`!(r:(num,(bvl_v)bvl_ref)fmap) p1 p2 bs1 bs2.
     FLOOKUP r p1 = SOME (bvl_ByteArray T bs1) /\ FLOOKUP r p2 = SOME (bvl_ByteArray T bs2)
     ==> bvl_do_eq r (bvl_RefPtr T p1) (bvl_RefPtr T p2) = Eq_val (bs1 = bs2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[bvl_do_eq_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[]);;

let C2BP1AUX_do_eq_BV_ref = prove
 (`!(r:(num,(bvl_v)bvl_ref)fmap) p1 p2 bs1 b2.
     FLOOKUP r p1 = SOME (bvl_ByteArray T bs1) /\
     (!bs. ~(FLOOKUP r p2 = SOME (bvl_ByteArray T bs)))
     ==> bvl_do_eq r (bvl_RefPtr T p1) (bvl_RefPtr b2 p2) = Eq_type_error /\
         bvl_do_eq r (bvl_RefPtr b2 p2) (bvl_RefPtr T p1) = Eq_type_error`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[bvl_do_eq_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN BOOL_CASES_TAC `b2:bool` THEN REWRITE_TAC[] THEN
  CASES_ON `FLOOKUP (r:(num,(bvl_v)bvl_ref)fmap) p2` THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN CASE_REWRITE_TAC[] THEN
  TRY (CASES_ON `a:(bvl_v)bvl_ref`) THEN CASE_REWRITE_TAC[] THEN SIMP[] THEN
  ASM_MESON_TAC[]);;

let C2BP1AUX_do_eq_RefPtr_v = prove
 (`!f r max_app c b1 i y x1 y1.
     INJ (FAPPLY f) (FDOM f) (FRANGE f) /\
     (!x y bs. FLOOKUP f x = SOME y ==> ~(FLOOKUP r y = SOME (bvl_ByteArray T bs))) /\
     clos_to_bvlProof_v_rel max_app f r c (clos_RefPtr b1 i) x1 /\
     clos_to_bvlProof_v_rel max_app f r c y y1
     ==> clos_do_eq (clos_RefPtr b1 i) y = bvl_do_eq r x1 y1`,
  REPEAT GEN_TAC THEN CASES_ON `y:clos_v` THEN REWRITE_TAC[v_rel_SIMP] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[clos_do_eq_def] THEN CASE_REWRITE_TAC[] THEN
  TRY (REWRITE_TAC[bvl_do_eq_def] THEN NO_TAC) THENL
   [MP_TAC (ISPECL [`r:(num,(bvl_v)bvl_ref)fmap`; `p:num`; `r2:num`; `a:byte list`;
                    `b1:bool`] C2BP1AUX_do_eq_BV_ref) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN GEN_TAC THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o check (is_forall o concl)) THEN
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    MP_TAC (ISPECL [`r:(num,(bvl_v)bvl_ref)fmap`; `b1:bool`; `r2:num`; `a0:bool`; `r2':num`]
            C2BP1AUX_do_eq_RefPtr) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN GEN_TAC THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o check (is_forall o concl)) THENL
       [EXISTS_TAC `i:num`; EXISTS_TAC `a1:num`] THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    EQ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `FLOOKUP (f:(num,num)fmap) a1 = SOME r2'` THEN
      ASM_REWRITE_TAC[option_INJ];
      DISCH_THEN SUBST_ALL_TAC THEN
      MATCH_MP_TAC (ISPEC `f:(num,num)fmap` C2BP1AUX_INJ_FLOOKUP) THEN
      EXISTS_TAC `r2':num` THEN ASM_REWRITE_TAC[]]]);;

let C2BP1AUX_do_eq_ByteVector_v = prove
 (`!f r max_app c bs y x1 y1.
     INJ (FAPPLY f) (FDOM f) (FRANGE f) /\
     (!x y bs. FLOOKUP f x = SOME y ==> ~(FLOOKUP r y = SOME (bvl_ByteArray T bs))) /\
     clos_to_bvlProof_v_rel max_app f r c (ByteVector bs) x1 /\
     clos_to_bvlProof_v_rel max_app f r c y y1
     ==> clos_do_eq (ByteVector bs) y = bvl_do_eq r x1 y1`,
  REPEAT GEN_TAC THEN CASES_ON `y:clos_v` THEN REWRITE_TAC[v_rel_SIMP] THEN
  STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[clos_do_eq_def] THEN CASE_REWRITE_TAC[] THEN
  TRY (REWRITE_TAC[bvl_do_eq_def] THEN NO_TAC) THENL
   [MP_TAC (ISPECL [`r:(num,(bvl_v)bvl_ref)fmap`; `p:num`; `p':num`; `bs:byte list`;
                    `a:byte list`] C2BP1AUX_do_eq_BV_BV) THEN ASM_SIMP_TAC[];
    MP_TAC (ISPECL [`r:(num,(bvl_v)bvl_ref)fmap`; `p:num`; `r2:num`; `bs:byte list`;
                    `a0:bool`] C2BP1AUX_do_eq_BV_ref) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN GEN_TAC THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o check (is_forall o concl)) THEN
      EXISTS_TAC `a1:num` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]]]);;

(* HOL4 line 1451 (HOL4 $' f is FAPPLY f) *)
let clos_to_bvlProof_do_eq = prove
 (`!f r max_app c.
     INJ (FAPPLY f) (FDOM f) (FRANGE f) /\
     (!x y bs. FLOOKUP f x = SOME y ==> ~(FLOOKUP r y = SOME (bvl_ByteArray T bs)))
     ==> (!x y x1 y1.
            clos_to_bvlProof_v_rel max_app f r c x x1 /\
            clos_to_bvlProof_v_rel max_app f r c y y1
            ==> clos_do_eq x y = bvl_do_eq r x1 y1) /\
         (!x y x1 y1.
            ALL2 (clos_to_bvlProof_v_rel max_app f r c) x x1 /\
            ALL2 (clos_to_bvlProof_v_rel max_app f r c) y y1
            ==> clos_do_eq_list x y = bvl_do_eq_list r x1 y1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC clos_do_eq_ind THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    CASES_ON `x:clos_v` THEN
    TRY (DISCH_TAC THEN MATCH_MP_TAC C2BP1AUX_do_eq_RefPtr_v THEN ASM_MESON_TAC[] THEN NO_TAC) THEN
    TRY (DISCH_TAC THEN MATCH_MP_TAC C2BP1AUX_do_eq_ByteVector_v THEN ASM_MESON_TAC[] THEN NO_TAC) THEN
    CASES_ON `y:clos_v` THEN REWRITE_TAC[v_rel_SIMP] THEN
    STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[clos_do_eq_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[bvl_do_eq_def; clos_tag_shift_def; not_isClos] THEN
    REWRITE_TAC[bvl_isClos_def; closure_tag_def; partial_app_tag_def; NOT_CONS_NIL] THEN
    REWRITE_TAC[ARITH_RULE `~((if t < 30 then t else t + 2) = 30) /\
                            ~((if t < 30 then t else t + 2) = 31)`] THEN
    SUBGOAL_THEN `LENGTH (a1:clos_v list) = LENGTH (ys:bvl_v list) /\
                  LENGTH (a1':clos_v list) = LENGTH (ys':bvl_v list)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[LIST_REL_LENGTH]; ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE `(if a < 30 then a else a + 2) = (if b < 30 then b else b + 2)
                                <=> a = b`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`a0:num`; `a1:clos_v list`; `a1':clos_v list`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LIST_REL_NIL] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[CONJ (end_itlist CONJ (tl (CONJUNCTS clos_do_eq_def))) bvl_do_eq_def];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[LIST_REL_CONS1] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[CONJ (end_itlist CONJ (tl (CONJUNCTS clos_do_eq_def))) bvl_do_eq_def] THEN
    SUBGOAL_THEN `clos_do_eq x y = bvl_do_eq (r:(num,(bvl_v)bvl_ref)fmap) h' h''` (fun th -> REWRITE_TAC[GSYM th]) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CASES_ON `clos_do_eq x y` THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `a:bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[CONJ (end_itlist CONJ (tl (CONJUNCTS clos_do_eq_def))) bvl_do_eq_def];
    REWRITE_TAC[LIST_REL_NIL; LIST_REL_CONS1] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[CONJ (end_itlist CONJ (tl (CONJUNCTS clos_do_eq_def))) bvl_do_eq_def]]);;

(* HOL4 line 1490: val r = mk_var (r, num |-> 'a ref) (the variable r      *)
(* of do_eq_sym: (num,(A)bvl_ref)fmap)                                     *)

(* HOL4 line 1492 *)
let clos_to_bvlProof_do_eq_sym = prove
 (`(!(r:(num,(bvl_v)bvl_ref)fmap) x y. bvl_do_eq r x y = bvl_do_eq r y x) /\
   (!(r:(num,(bvl_v)bvl_ref)fmap) x y. bvl_do_eq_list r x y = bvl_do_eq_list r y x)`,
  MATCH_MP_TAC bvl_do_eq_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_do_eq_def] THENL
   [CASES_ON `x'':bvl_v` THEN REWRITE_TAC[bvl_do_eq_def];
    REWRITE_TAC[EQ_SYM_EQ];
    REWRITE_TAC[EQ_SYM_EQ];
    GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) [CONJ_SYM] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    CASES_ON `FLOOKUP (refs:(num,(bvl_v)bvl_ref)fmap) n1` THEN
    CASES_ON `FLOOKUP (refs:(num,(bvl_v)bvl_ref)fmap) n2` THEN CASE_REWRITE_TAC[] THEN
    TRY (CASES_ON `a:(bvl_v)bvl_ref`) THEN TRY (CASES_ON `a':(bvl_v)bvl_ref`) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[EQ_SYM_EQ] THEN
    TRY (BOOL_CASES_TAC `a0:bool` THEN REWRITE_TAC[EQ_SYM_EQ]) THEN
    TRY (BOOL_CASES_TAC `a0':bool` THEN REWRITE_TAC[EQ_SYM_EQ]);
    DISCH_TAC THEN ASM_CASES_TAC `bvl_isClos t1 (l1:bvl_v list)` THEN
    ASM_CASES_TAC `bvl_isClos t2 (l2:bvl_v list)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `t1:num = t2 /\ LENGTH (l1:bvl_v list) = LENGTH (l2:bvl_v list)` THENL
     [FIRST_ASSUM (STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `~(t2:num = t1 /\ LENGTH (l2:bvl_v list) = LENGTH (l1:bvl_v list))`
        (fun th -> ASM_REWRITE_TAC[th]) THEN ASM_MESON_TAC[]];
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    CASES_ON `bvl_do_eq (refs:(num,(bvl_v)bvl_ref)fmap) v1 v2` THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `T` THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 1508 *)
let do_eq_list_T_every = prove
 (`!vs1 vs2 (r:(num,(bvl_v)bvl_ref)fmap).
     bvl_do_eq_list r vs1 vs2 = Eq_val T <=>
     ALL2 (\v1 v2. bvl_do_eq r v1 v2 = Eq_val T) vs1 vs2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  SIMP[bvl_do_eq_def; ALL2] THEN
  GEN_TAC THEN CASES_ON `bvl_do_eq (r:(num,(bvl_v)bvl_ref)fmap) h h'` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[] THEN BOOL_CASES_TAC `a:bool` THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

(* HOL4 line 1517 *)
let clos_to_bvlProof_list_to_v_v_rel = prove
 (`!xs ys app f refs code.
     ALL2 (clos_to_bvlProof_v_rel app f refs code) xs ys
     ==> clos_to_bvlProof_v_rel app f refs code (clos_list_to_v xs) (bvl_list_to_v ys)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2] THEN
  REWRITE_TAC[clos_list_to_v_def; bvl_list_to_v_def] THEN REPEAT STRIP_TAC THENL
   [MP_TAC (ISPECL [`app:num`; `f:(num,num)fmap`; `refs:(num,(bvl_v)bvl_ref)fmap`;
                    `code:(num#bvl_exp)spt`; `[]:clos_v list`; `[]:bvl_v list`; `nil_tag`]
            (el 2 (CONJUNCTS clos_to_bvlProof_v_rel_rules))) THEN
    REWRITE_TAC[ALL2; clos_tag_shift_nil_tag];
    MP_TAC (ISPECL [`app:num`; `f:(num,num)fmap`; `refs:(num,(bvl_v)bvl_ref)fmap`;
                    `code:(num#bvl_exp)spt`; `[h; clos_list_to_v t]`;
                    `[h'; bvl_list_to_v t']`; `cons_tag`]
            (el 2 (CONJUNCTS clos_to_bvlProof_v_rel_rules))) THEN
    REWRITE_TAC[ALL2; clos_tag_shift_cons_tag] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[]]);;

(* HOL4 line 1527: fun cases_on_op (a tactic) *)

let C2BP1AUX_clos_do_word_app_ind = CLOSSEMAUX_cases_ind clos_do_word_app_def;;

let C2BP1AUX_clos_do_int_app_ind = CLOSSEMAUX_cases_ind clos_do_int_app_def;;

let C2BP1AUX_do_int_app = prove
 (`!iop xs r ys max_app f refs code.
     ALL2 (clos_to_bvlProof_v_rel max_app f refs code) xs ys /\
     clos_do_int_app iop xs = SOME r
     ==> ?r'. bvl_do_int_app iop ys = SOME r' /\
              clos_to_bvlProof_v_rel max_app f refs code r r'`,
  MATCH_MP_TAC C2BP1AUX_clos_do_int_app_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_do_int_app_def; option_DISTINCT] THEN
  REWRITE_TAC[LIST_REL_CONS1; LIST_REL_NIL; v_rel_SIMP] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REPEAT (POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[bvl_do_int_app_def] THEN
  TRY COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[option_INJ; UNWIND_THM1; clos_to_bvlProof_v_rel_rules;
                  clos_to_bvlProof_v_rel_Boolv]);;

let C2BP1AUX_do_word_app = prove
 (`!wop xs r ys max_app f refs code.
     ALL2 (clos_to_bvlProof_v_rel max_app f refs code) xs ys /\
     clos_do_word_app wop xs = SOME r
     ==> ?r'. bvl_do_word_app wop ys = SOME r' /\
              clos_to_bvlProof_v_rel max_app f refs code r r'`,
  MATCH_MP_TAC C2BP1AUX_clos_do_word_app_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_do_word_app_def; option_DISTINCT] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
  POP_ASSUM_LIST (MAP_EVERY (STRIP_ASSUME_TAC o
                             REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL; v_rel_SIMP; option_INJ])) THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[bvl_do_word_app_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[option_INJ; UNWIND_THM1; clos_to_bvlProof_v_rel_rules;
                  clos_to_bvlProof_v_rel_Boolv]);;

(* FULL_CASE_TAC of the kit splits a boolean variable scrutinee with       *)
(* BOOL_CASES_TAC, which rewrites only the goal: with the conditional in an  *)
(* assumption EVERY_CASE_TAC then loops; this variant substitutes it         *)
let C2BP1AUX_FULL_CASE_TAC : tactic =
  fun (asl,w as gl) ->
    let whole = list_mk_conj(w :: map (concl o snd) asl) in
    let x = inner_case_scrutinee whole whole in
    ((if type_of x = bool_ty && is_var x then
        DISJ_CASES_THEN SUBST_ALL_TAC (SPEC x BOOL_CASES_AX)
      else CASES_ON x) THEN CASE_ASM_TIDY_TAC THEN CASE_TIDY_TAC) gl;;

let C2BP1AUX_EVERY_CASE_TAC : tactic = REPEAT C2BP1AUX_FULL_CASE_TAC;;

let C2BP1AUX_tag_shift_11 = prove
 (`!a b. clos_tag_shift a = clos_tag_shift b <=> a = b`,
  MESON_TAC[clos_tag_shift_inj]);;

let C2BP1AUX_DOAPP_FIN_LIST =
  [PAIR_EQ; UNWIND_THM1; GSYM CONJ_ASSOC; clos_to_bvlProof_v_rel_rules;
   clos_to_bvlProof_v_rel_Boolv; clos_to_bvlProof_v_rel_Unit;
   RIGHT_EXISTS_AND_THM; EXISTS_REFL; C2BP1AUX_tag_shift_11; bvl_Boolv_11; clos_Boolv_11;
   INT_GT];;

let C2BP1AUX_DOAPP_TAC : tactic =
  REWRITE_TAC[clos_do_app_def; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  C2BP1AUX_EVERY_CASE_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  POP_ASSUM_LIST (MAP_EVERY (STRIP_ASSUME_TAC o
     REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL; v_rel_SIMP; clos_to_bvlProof_v_rel_Boolv;
                  clos_to_bvlProof_v_rel_Unit; PAIR_EQ])) THEN
  RVEQ_TAC THEN
  ASSUM_LIST (MAP_EVERY (fun th -> try ASSUME_TAC (SYM (MATCH_MP EVERY2_LENGTH th))
                                   with Failure _ -> ALL_TAC)) THEN
  REWRITE_TAC[bvl_do_app_def; clos_to_bvl_compile_op_def; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC C2BP1AUX_DOAPP_FIN_LIST THEN
  TRY (CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC C2BP1AUX_DOAPP_FIN_LIST);;

let C2BP1AUX_BOOL_SPLIT_TAC : tactic =
  RULE_ASSUM_TAC (REWRITE_RULE[DE_MORGAN_THM]) THEN
  REPEAT (FIRST_X_ASSUM (DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th ->
    is_disj (concl th) && is_eq (lhand (concl th)) && is_var (lhs (lhand (concl th)))))) THEN
  RULE_ASSUM_TAC (REWRITE_RULE[clos_to_bvlProof_v_rel_Boolv]) THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC C2BP1AUX_DOAPP_FIN_LIST THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC C2BP1AUX_DOAPP_FIN_LIST THEN
  TRY (RULE_ASSUM_TAC (REWRITE_RULE[clos_Boolv_11; bvl_Boolv_11]) THEN ASM_REWRITE_TAC[]);;

let C2BP1AUX_do_eq_rel = prove
 (`!f (s:(C,FFI)clos_state) (t:(C,FFI)bvl_state) x x1 y y1.
     clos_to_bvlProof_state_rel f s t /\
     clos_to_bvlProof_v_rel (clos_state_max_app s) f (bvl_state_refs t) (bvl_state_code t)
       x x1 /\
     clos_to_bvlProof_v_rel (clos_state_max_app s) f (bvl_state_refs t) (bvl_state_code t)
       y y1
     ==> bvl_do_eq (bvl_state_refs t) x1 y1 = clos_do_eq x y`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MP_TAC (SPECL [`f:(num,num)fmap`; `bvl_state_refs (t:(C,FFI)bvl_state)`;
                 `clos_state_max_app (s:(C,FFI)clos_state)`;
                 `bvl_state_code (t:(C,FFI)bvl_state)`] clos_to_bvlProof_do_eq) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `clos_to_bvlProof_state_rel f (s:(C,FFI)clos_state) (t:(C,FFI)bvl_state)` THEN
    REWRITE_TAC[clos_to_bvlProof_state_rel_def] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN (MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]);;

let C2BP1AUX_V2L_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (fun th ->
    if can (term_match [] `clos_v_to_list x = SOME l`) (concl th) then
      FIRST_ASSUM (fun vr -> STRIP_ASSUME_TAC (MATCH_MP clos_to_bvlProof_v_to_list (CONJ th vr)))
    else NO_TAC));;

let C2BP1AUX_ALL2_MAP_MAP2 = prove
 (`!(R:A->B->bool) (m1:C->A) m2 l.
     (!k. R (m1 k) (m2 k)) ==> ALL2 R (MAP m1 l) (MAP m2 l)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_SIMP_TAC[MAP; ALL2]);;

let C2BP1AUX_REFS_TAC : tactic =
  IMP_RES_TAC state_rel_refs_lookup THEN
  RULE_ASSUM_TAC (REWRITE_RULE[clos_to_bvlProof_ref_rel_simp]) THEN
  REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
  RVEQ_TAC THEN
  ASSUM_LIST (MAP_EVERY (fun th -> try ASSUME_TAC (SYM (MATCH_MP EVERY2_LENGTH th))
                                   with Failure _ -> ALL_TAC)) THEN
  ASM_REWRITE_TAC C2BP1AUX_DOAPP_FIN_LIST THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC C2BP1AUX_DOAPP_FIN_LIST THEN
  TRY (CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC C2BP1AUX_DOAPP_FIN_LIST);;

let C2BP1AUX_doapp_rel_IntOp = prove
 (`!iop xs (s1:(C,FFI)clos_state) v s2 f (t1:(C,FFI)bvl_state) ys.
     clos_do_app (IntOp iop) xs s1 = Rval (v,s2) /\
     clos_to_bvlProof_state_rel f s1 t1 /\
     ALL2 (clos_to_bvlProof_v_rel (clos_state_max_app s1) f (bvl_state_refs t1)
             (bvl_state_code t1)) xs ys
     ==> ?w t2.
           bvl_do_app (clos_to_bvl_compile_op (IntOp iop)) ys t1 = Rval (w,t2) /\
           clos_to_bvlProof_v_rel (clos_state_max_app s1) f (bvl_state_refs t1)
             (bvl_state_code t1) v w /\
           clos_to_bvlProof_state_rel f s2 t2 /\
           bvl_state_refs t1 = bvl_state_refs t2 /\ bvl_state_code t1 = bvl_state_code t2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def; clos_to_bvl_compile_op_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `clos_do_int_app iop xs` THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM (fun a -> FIRST_ASSUM (fun b ->
    STRIP_ASSUME_TAC (MATCH_MP C2BP1AUX_do_int_app (CONJ a b)))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC C2BP1AUX_DOAPP_FIN_LIST THEN ASM_REWRITE_TAC[]);;

let C2BP1AUX_doapp_rel_WordOp = prove
 (`!wop xs (s1:(C,FFI)clos_state) v s2 f (t1:(C,FFI)bvl_state) ys.
     clos_do_app (WordOp wop) xs s1 = Rval (v,s2) /\
     clos_to_bvlProof_state_rel f s1 t1 /\
     ALL2 (clos_to_bvlProof_v_rel (clos_state_max_app s1) f (bvl_state_refs t1)
             (bvl_state_code t1)) xs ys
     ==> ?w t2.
           bvl_do_app (clos_to_bvl_compile_op (WordOp wop)) ys t1 = Rval (w,t2) /\
           clos_to_bvlProof_v_rel (clos_state_max_app s1) f (bvl_state_refs t1)
             (bvl_state_code t1) v w /\
           clos_to_bvlProof_state_rel f s2 t2 /\
           bvl_state_refs t1 = bvl_state_refs t2 /\ bvl_state_code t1 = bvl_state_code t2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def; clos_to_bvl_compile_op_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[] THEN
  CASES_ON `clos_do_word_app wop xs` THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM (fun a -> FIRST_ASSUM (fun b ->
    STRIP_ASSUME_TAC (MATCH_MP C2BP1AUX_do_word_app (CONJ a b)))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC C2BP1AUX_DOAPP_FIN_LIST THEN ASM_REWRITE_TAC[]);;

let C2BP1AUX_doapp_rel_BlockOp = prove
 (`!bop xs (s1:(C,FFI)clos_state) v s2 f (t1:(C,FFI)bvl_state) ys.
     clos_do_app (BlockOp bop) xs s1 = Rval (v,s2) /\
     clos_to_bvlProof_state_rel f s1 t1 /\
     ALL2 (clos_to_bvlProof_v_rel (clos_state_max_app s1) f (bvl_state_refs t1)
             (bvl_state_code t1)) xs ys /\
     (!c. ~(bop = Constant c))
     ==> ?w t2.
           bvl_do_app (clos_to_bvl_compile_op (BlockOp bop)) ys t1 = Rval (w,t2) /\
           clos_to_bvlProof_v_rel (clos_state_max_app s1) f (bvl_state_refs t1)
             (bvl_state_code t1) v w /\
           clos_to_bvlProof_state_rel f s2 t2 /\
           bvl_state_refs t1 = bvl_state_refs t2 /\ bvl_state_code t1 = bvl_state_code t2`,
  GEN_TAC THEN CASES_ON `bop:block_op` THEN REPEAT GEN_TAC THENL
   [(* Cons *)
    C2BP1AUX_DOAPP_TAC THEN MATCH_MP_TAC (el 2 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    ASM_REWRITE_TAC[];
    (* ElemAt *)
    C2BP1AUX_DOAPP_TAC THEN CASE_REWRITE_TAC C2BP1AUX_DOAPP_FIN_LIST THEN
    ASM_MESON_TAC[LIST_REL_EL_EQN];
    (* TagLenEq *) C2BP1AUX_DOAPP_TAC;
    (* LenEq *) C2BP1AUX_DOAPP_TAC;
    (* TagEq *) C2BP1AUX_DOAPP_TAC;
    (* LengthBlock *) C2BP1AUX_DOAPP_TAC;
    (* BoolTest *) C2BP1AUX_DOAPP_TAC THEN C2BP1AUX_BOOL_SPLIT_TAC;
    (* BoolNot *) C2BP1AUX_DOAPP_TAC THEN C2BP1AUX_BOOL_SPLIT_TAC;
    (* BoundsCheckBlock *) C2BP1AUX_DOAPP_TAC;
    (* ConsExtend *)
    C2BP1AUX_DOAPP_TAC THEN
    MATCH_MP_TAC (el 2 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    MATCH_MP_TAC EVERY2_APPEND_suff THEN ASM_SIMP_TAC[EVERY2_TAKE; EVERY2_DROP];
    (* FromList *)
    C2BP1AUX_DOAPP_TAC THEN C2BP1AUX_V2L_TAC THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC C2BP1AUX_DOAPP_FIN_LIST THEN
    ASM_SIMP_TAC[clos_to_bvlProof_v_rel_rules];
    (* ListAppend *)
    C2BP1AUX_DOAPP_TAC THEN C2BP1AUX_V2L_TAC THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC C2BP1AUX_DOAPP_FIN_LIST THEN
    ASM_SIMP_TAC[clos_to_bvlProof_list_to_v_v_rel; EVERY2_APPEND_suff];
    (* Constant *)
    REWRITE_TAC[injectivity "block_op"] THEN MESON_TAC[];
    (* Equal *)
    C2BP1AUX_DOAPP_TAC THEN IMP_RES_TAC C2BP1AUX_do_eq_rel THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC C2BP1AUX_DOAPP_FIN_LIST THEN ASM_REWRITE_TAC[];
    (* EqualConst *) C2BP1AUX_DOAPP_TAC;
    (* Build *) C2BP1AUX_DOAPP_TAC]);;

let C2BP1AUX_get_global_rel = prove
 (`!f (s:(C,FFI)clos_state) (t:(C,FFI)bvl_state) n x.
     clos_to_bvlProof_state_rel f s t /\ get_global n (clos_state_globals s) = SOME x
     ==> ?y. get_global (n + num_added_globals) (bvl_state_globals t) = SOME y /\
             OPTREL (clos_to_bvlProof_v_rel (clos_state_max_app s) f (bvl_state_refs t)
                       (bvl_state_code t)) x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_to_bvlProof_state_rel_def; get_global_def] THEN
  STRIP_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM (MP_TAC o check (fun th ->
    can (term_match [] `ALL2 (R:clos_v option->bvl_v option->bool) (a:(clos_v option)list) b`) (concl th))) THEN
  REWRITE_TAC[LIST_REL_EL_EQN; LENGTH_DROP] THEN STRIP_TAC THEN
  SUBGOAL_THEN `n + num_added_globals < LENGTH (bvl_state_globals (t:(C,FFI)bvl_state))`
    ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[option_INJ; UNWIND_THM1] THEN
  ASM_MESON_TAC[EL_DROP]);;

let C2BP1AUX_state_rel_SetGlobal = prove
 (`!f (s:(C,FFI)clos_state) (t:(C,FFI)bvl_state) n v w.
     clos_to_bvlProof_state_rel f s t /\
     clos_to_bvlProof_v_rel (clos_state_max_app s) f (bvl_state_refs t) (bvl_state_code t) v w
     ==> clos_to_bvlProof_state_rel f
           (clos_state_globals_fupd (K (LUPDATE (SOME v) n (clos_state_globals s))) s)
           (bvl_state_globals_fupd
              (K (LUPDATE (SOME w) (n + num_added_globals) (bvl_state_globals t))) t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_to_bvlProof_state_rel_def; clos_state_INFO.ri_accfupds;
              bvl_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[misc_DROP_LUPDATE; ARITH_RULE `a <= n + a:num`; ADD_SUB] THEN
    MATCH_MP_TAC EVERY2_LUPDATE_same THEN ASM_REWRITE_TAC[OPTREL_THM];
    UNDISCH_TAC `get_global 0 (bvl_state_globals (t:(C,FFI)bvl_state)) =
                 SOME (SOME (global_table (clos_state_max_app (s:(C,FFI)clos_state))))` THEN
    REWRITE_TAC[get_global_def; LENGTH_LUPDATE; num_added_globals_def] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[EL_LUPDATE; ARITH_RULE `~(0 = n + 1)`]]);;

let C2BP1AUX_state_rel_AllocGlobal = prove
 (`!f (s:(C,FFI)clos_state) (t:(C,FFI)bvl_state) k.
     clos_to_bvlProof_state_rel f s t
     ==> clos_to_bvlProof_state_rel f
           (clos_state_globals_fupd
              (K (APPEND (clos_state_globals s) (REPLICATE k NONE))) s)
           (bvl_state_globals_fupd
              (K (APPEND (bvl_state_globals t) (REPLICATE k NONE))) t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_to_bvlProof_state_rel_def; clos_state_INFO.ri_accfupds;
              bvl_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `0 < LENGTH (bvl_state_globals (t:(C,FFI)bvl_state))` ASSUME_TAC THENL
   [UNDISCH_TAC `get_global 0 (bvl_state_globals (t:(C,FFI)bvl_state)) =
                 SOME (SOME (global_table (clos_state_max_app (s:(C,FFI)clos_state))))` THEN
    REWRITE_TAC[get_global_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[DROP_APPEND1; num_added_globals_def; ARITH_RULE `0 < n ==> 1 <= n`] THEN
    MATCH_MP_TAC EVERY2_APPEND_suff THEN
    ASM_REWRITE_TAC[GSYM num_added_globals_def; LIST_REL_REPLICATE_same; OPTREL_THM];
    UNDISCH_TAC `get_global 0 (bvl_state_globals (t:(C,FFI)bvl_state)) =
                 SOME (SOME (global_table (clos_state_max_app (s:(C,FFI)clos_state))))` THEN
    ASM_SIMP_TAC[get_global_def; LENGTH_APPEND; EL_APPEND1;
                 ARITH_RULE `0 < a ==> 0 < a + b`]]);;

let C2BP1AUX_doapp_rel_GlobOp = prove
 (`!gop xs (s1:(C,FFI)clos_state) v s2 f (t1:(C,FFI)bvl_state) ys.
     clos_do_app (GlobOp gop) xs s1 = Rval (v,s2) /\
     clos_to_bvlProof_state_rel f s1 t1 /\
     ALL2 (clos_to_bvlProof_v_rel (clos_state_max_app s1) f (bvl_state_refs t1)
             (bvl_state_code t1)) xs ys
     ==> ?w t2.
           bvl_do_app (clos_to_bvl_compile_op (GlobOp gop)) ys t1 = Rval (w,t2) /\
           clos_to_bvlProof_v_rel (clos_state_max_app s1) f (bvl_state_refs t1)
             (bvl_state_code t1) v w /\
           clos_to_bvlProof_state_rel f s2 t2 /\
           bvl_state_refs t1 = bvl_state_refs t2 /\ bvl_state_code t1 = bvl_state_code t2`,
  GEN_TAC THEN CASES_ON `gop:glob_op` THEN REPEAT GEN_TAC THENL
   [(* Global *)
    C2BP1AUX_DOAPP_TAC THEN IMP_RES_TAC C2BP1AUX_get_global_rel THEN
    RULE_ASSUM_TAC (REWRITE_RULE[OPTREL_SOME]) THEN
    REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC C2BP1AUX_DOAPP_FIN_LIST THEN
    ASM_REWRITE_TAC[];
    (* SetGlobal *)
    C2BP1AUX_DOAPP_TAC THEN IMP_RES_TAC C2BP1AUX_get_global_rel THEN
    REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o check (is_exists o concl))) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC C2BP1AUX_DOAPP_FIN_LIST THEN
    ASM_SIMP_TAC[C2BP1AUX_state_rel_SetGlobal; bvl_state_INFO.ri_accfupds];
    (* AllocGlobal *)
    C2BP1AUX_DOAPP_TAC THEN
    ASM_SIMP_TAC[C2BP1AUX_state_rel_AllocGlobal; bvl_state_INFO.ri_accfupds];
    (* GlobalsPtr *) C2BP1AUX_DOAPP_TAC;
    (* SetGlobalsPtr *) C2BP1AUX_DOAPP_TAC]);;

let C2BP1AUX_doapp_rel_MemOp = prove
 (`!mop xs (s1:(C,FFI)clos_state) v s2 f (t1:(C,FFI)bvl_state) ys.
     clos_do_app (MemOp mop) xs s1 = Rval (v,s2) /\
     clos_to_bvlProof_state_rel f s1 t1 /\
     ALL2 (clos_to_bvlProof_v_rel (clos_state_max_app s1) f (bvl_state_refs t1)
             (bvl_state_code t1)) xs ys /\
     ~(mop = clos_Ref) /\ ~(mop = Update) /\ ~(mop = XorByte) /\
     ~(mop = RefArray) /\ (!f. ~(mop = RefByte f)) /\ ~(mop = UpdateByte) /\
     ~(mop = FromListByte) /\ ~(mop = ConcatByteVec) /\ (!b. ~(mop = CopyByte b))
     ==> ?w t2.
           bvl_do_app (clos_to_bvl_compile_op (MemOp mop)) ys t1 = Rval (w,t2) /\
           clos_to_bvlProof_v_rel (clos_state_max_app s1) f (bvl_state_refs t1)
             (bvl_state_code t1) v w /\
           clos_to_bvlProof_state_rel f s2 t2 /\
           bvl_state_refs t1 = bvl_state_refs t2 /\ bvl_state_code t1 = bvl_state_code t2`,
  GEN_TAC THEN CASES_ON `mop:mem_op` THEN REPEAT GEN_TAC THENL
   [
    (* Ref *)
    REWRITE_TAC[injectivity "mem_op"; distinctness "mem_op"] THEN MESON_TAC[];
    (* Update *)
    REWRITE_TAC[injectivity "mem_op"; distinctness "mem_op"] THEN MESON_TAC[];
    (* El *)
    REWRITE_TAC[distinctness "mem_op"] THEN C2BP1AUX_DOAPP_TAC THEN TRY C2BP1AUX_REFS_TAC THEN
    ASM_MESON_TAC[LIST_REL_EL_EQN; BASICAUX_num_of_int_lt];
    (* Length *)
    REWRITE_TAC[distinctness "mem_op"] THEN C2BP1AUX_DOAPP_TAC THEN C2BP1AUX_REFS_TAC;
    (* LengthByte *)
    REWRITE_TAC[distinctness "mem_op"] THEN C2BP1AUX_DOAPP_TAC THEN C2BP1AUX_REFS_TAC;
    (* RefByte *)
    REWRITE_TAC[injectivity "mem_op"; distinctness "mem_op"] THEN MESON_TAC[];
    (* RefArray *)
    REWRITE_TAC[injectivity "mem_op"; distinctness "mem_op"] THEN MESON_TAC[];
    (* DerefByte *)
    REWRITE_TAC[distinctness "mem_op"] THEN C2BP1AUX_DOAPP_TAC THEN C2BP1AUX_REFS_TAC;
    (* UpdateByte *)
    REWRITE_TAC[injectivity "mem_op"; distinctness "mem_op"] THEN MESON_TAC[];
    (* ConcatByteVec *)
    REWRITE_TAC[injectivity "mem_op"; distinctness "mem_op"] THEN MESON_TAC[];
    (* CopyByte *)
    REWRITE_TAC[injectivity "mem_op"; distinctness "mem_op"] THEN MESON_TAC[];
    (* FromListByte *)
    REWRITE_TAC[injectivity "mem_op"; distinctness "mem_op"] THEN MESON_TAC[];
    (* ToListByte *)
    REWRITE_TAC[distinctness "mem_op"] THEN C2BP1AUX_DOAPP_TAC THEN MATCH_MP_TAC clos_to_bvlProof_list_to_v_v_rel THEN
    MATCH_MP_TAC C2BP1AUX_ALL2_MAP_MAP2 THEN REWRITE_TAC[clos_to_bvlProof_v_rel_rules];
    (* LengthByteVec *)
    REWRITE_TAC[distinctness "mem_op"] THEN C2BP1AUX_DOAPP_TAC;
    (* DerefByteVec *)
    REWRITE_TAC[distinctness "mem_op"] THEN C2BP1AUX_DOAPP_TAC THEN CASE_REWRITE_TAC C2BP1AUX_DOAPP_FIN_LIST THEN
    ASM_REWRITE_TAC C2BP1AUX_DOAPP_FIN_LIST;
    (* StringCmp *)
    REWRITE_TAC[distinctness "mem_op"] THEN C2BP1AUX_DOAPP_TAC;
    (* XorByte *)
    REWRITE_TAC[injectivity "mem_op"; distinctness "mem_op"] THEN MESON_TAC[];
    (* BoundsCheckArray *)
    REWRITE_TAC[distinctness "mem_op"] THEN C2BP1AUX_DOAPP_TAC THEN C2BP1AUX_REFS_TAC;
    (* BoundsCheckByte *)
    REWRITE_TAC[distinctness "mem_op"] THEN C2BP1AUX_DOAPP_TAC THEN C2BP1AUX_REFS_TAC;
    (* MutCons *)
    REWRITE_TAC[distinctness "mem_op"] THEN C2BP1AUX_DOAPP_TAC;
    (* UpdateCons *)
    REWRITE_TAC[distinctness "mem_op"] THEN C2BP1AUX_DOAPP_TAC;
    (* FinaliseCons *)
    REWRITE_TAC[distinctness "mem_op"] THEN C2BP1AUX_DOAPP_TAC;
    (* ConfigGC *)
    REWRITE_TAC[distinctness "mem_op"] THEN C2BP1AUX_DOAPP_TAC]);;

(* HOL4 line 1530 (closSem's do_app on the left, bvlSem's on the right; HOL4 *)
(* MemOp Ref etc. are closLang's op constructors)                            *)
let clos_to_bvlProof_do_app = prove
 (`!op xs (s1:(C,FFI)clos_state) v s2 f (t1:(C,FFI)bvl_state) ys.
     clos_do_app op xs s1 = Rval (v,s2) /\
     clos_to_bvlProof_state_rel f s1 t1 /\
     ALL2 (clos_to_bvlProof_v_rel (clos_state_max_app s1) f (bvl_state_refs t1)
             (bvl_state_code t1)) xs ys /\
     ~(op = MemOp clos_Ref) /\ ~(op = MemOp Update) /\ ~(op = MemOp XorByte) /\
     ~(op = MemOp RefArray) /\ (!f. ~(op = MemOp (RefByte f))) /\ ~(op = MemOp UpdateByte) /\
     ~(op = MemOp FromListByte) /\ ~(op = MemOp ConcatByteVec) /\
     (!b. ~(op = MemOp (CopyByte b))) /\ (!c. ~(op = BlockOp (Constant c))) /\
     (!n. ~(op = clos_FFI n)) /\
     (!t. ~(op = clos_ThunkOp t))
     ==> ?w t2.
           bvl_do_app (clos_to_bvl_compile_op op) ys t1 = Rval (w,t2) /\
           clos_to_bvlProof_v_rel (clos_state_max_app s1) f (bvl_state_refs t1)
             (bvl_state_code t1) v w /\
           clos_to_bvlProof_state_rel f s2 t2 /\
           bvl_state_refs t1 = bvl_state_refs t2 /\ bvl_state_code t1 = bvl_state_code t2`,
  GEN_TAC THEN CASES_ON `op:clos_op` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[injectivity "clos_op"; distinctness "clos_op"] THENL
   [(* Label *) C2BP1AUX_DOAPP_TAC;
    (* FFI *) MESON_TAC[];
    (* IntOp *)
    STRIP_TAC THEN MATCH_MP_TAC C2BP1AUX_doapp_rel_IntOp THEN
    EXISTS_TAC `xs:clos_v list` THEN ASM_REWRITE_TAC[];
    (* WordOp *)
    STRIP_TAC THEN MATCH_MP_TAC C2BP1AUX_doapp_rel_WordOp THEN
    EXISTS_TAC `xs:clos_v list` THEN ASM_REWRITE_TAC[];
    (* BlockOp *)
    STRIP_TAC THEN MATCH_MP_TAC C2BP1AUX_doapp_rel_BlockOp THEN
    EXISTS_TAC `xs:clos_v list` THEN ASM_REWRITE_TAC[];
    (* GlobOp *)
    STRIP_TAC THEN MATCH_MP_TAC C2BP1AUX_doapp_rel_GlobOp THEN
    EXISTS_TAC `xs:clos_v list` THEN ASM_REWRITE_TAC[];
    (* MemOp *)
    STRIP_TAC THEN MATCH_MP_TAC C2BP1AUX_doapp_rel_MemOp THEN
    EXISTS_TAC `xs:clos_v list` THEN ASM_REWRITE_TAC[];
    (* Install *) C2BP1AUX_DOAPP_TAC;
    (* ThunkOp *) MESON_TAC[]]);;

(* HOL4 line 1801: val v_case_eq_thms (case theorems for the proofs) *)

let C2BP1AUX_ERR_PRE_TAC : tactic =
  REWRITE_TAC[clos_do_app_def; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  C2BP1AUX_EVERY_CASE_TAC THEN CASE_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE[]) THEN
  TRY (FIRST_ASSUM (CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  ASM_REWRITE_TAC[];;

(* the case equations turn the hypothesis into a formula whose leaves are   *)
(* the results of closSem do_app: Rval (false) or Rerr (Rabort Rtype_error), *)
(* false by the hypothesis on the error                                     *)
let C2BP1AUX_ERR_FAST_TAC : tactic =
  REWRITE_TAC[clos_do_app_def; LET_DEF; LET_END_DEF] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC (all_case_eqs()) THEN
  DISCH_THEN (fun th ->
    let a = CONJUNCT1 th and b = CONJUNCT1 (CONJUNCT2 th) in
    MP_TAC (CASE_REWRITE_RULE[b] a)) THEN REWRITE_TAC[];;

let C2BP1AUX_FFI_ERR_TAC : tactic =
  POP_ASSUM_LIST (MAP_EVERY (STRIP_ASSUME_TAC o
     REWRITE_RULE[LIST_REL_CONS1; LIST_REL_NIL; v_rel_SIMP; PAIR_EQ])) THEN RVEQ_TAC THEN
  IMP_RES_TAC state_rel_refs_lookup THEN
  RULE_ASSUM_TAC (REWRITE_RULE[clos_to_bvlProof_ref_rel_simp]) THEN
  REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o check (is_exists o concl))) THEN RVEQ_TAC THEN
  SUBGOAL_THEN `bvl_state_ffi (t1:(C,FFI)bvl_state) = clos_state_ffi (s1:(C,FFI)clos_state)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `clos_to_bvlProof_state_rel f (s1:(C,FFI)clos_state) (t1:(C,FFI)bvl_state)` THEN
    SIMP_TAC[clos_to_bvlProof_state_rel_def];
    ALL_TAC] THEN
  REWRITE_TAC[bvl_do_app_def; clos_to_bvl_compile_op_def] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[exc_rel_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[exc_rel_def] THEN REWRITE_TAC[UNWIND_THM1] THEN
  CASE_REWRITE_TAC[exc_rel_def];;

(* HOL4 line 1806 *)
let clos_to_bvlProof_do_app_err = prove
 (`!op xs (s1:(C,FFI)clos_state) err f (t1:(C,FFI)bvl_state) ys.
     clos_do_app op xs s1 = Rerr err /\
     ~(err = Rabort Rtype_error) /\
     clos_to_bvlProof_state_rel f s1 t1 /\
     ALL2 (clos_to_bvlProof_v_rel (clos_state_max_app s1) f (bvl_state_refs t1)
             (bvl_state_code t1)) xs ys
     ==> ?e. bvl_do_app (clos_to_bvl_compile_op op) ys t1 = Rerr e /\
             exc_rel (clos_to_bvlProof_v_rel (clos_state_max_app s1) f (bvl_state_refs t1)
                        (bvl_state_code t1)) err e`,
  GEN_TAC THEN CASES_ON `op:clos_op` THEN REPEAT GEN_TAC THENL
   [(* Label *) C2BP1AUX_ERR_FAST_TAC;
    (* FFI *) C2BP1AUX_ERR_PRE_TAC THEN C2BP1AUX_FFI_ERR_TAC;
    (* IntOp *) C2BP1AUX_ERR_FAST_TAC;
    (* WordOp *) C2BP1AUX_ERR_FAST_TAC;
    (* BlockOp *) C2BP1AUX_ERR_FAST_TAC;
    (* GlobOp *) C2BP1AUX_ERR_FAST_TAC;
    (* MemOp *) C2BP1AUX_ERR_FAST_TAC;
    (* Install *) C2BP1AUX_ERR_FAST_TAC;
    (* ThunkOp *) C2BP1AUX_ERR_FAST_TAC]);;

(* HOL4 line 1839 *)
let eq_res_def = cake_def
  `(eq_res (Eq_val b) = Rval [bvl_Boolv b]) /\
   (eq_res _ = (Rerr (Rabort Rtype_error):(bvl_v list,bvl_v)result))`;;

let _ = cake_add_simps [eq_res_def];;

(* HOL4 line 1844 *)
let eq_res_not_timeout = prove
 (`!x. ~(eq_res x = Rerr (Rabort Rtimeout_error))`,
  GEN_TAC THEN CASES_ON `x:eq_result` THEN SIMP[eq_res_def]);;

(* HOL4 line 1850 *)
let evaluate_check_closure = prove
 (`!n env t vs e (s:(C,FFI)bvl_state).
     n < LENGTH env /\ EL n env = bvl_Block t vs
     ==> bvl_evaluate ([check_closure n e],env,s) =
         if t = closure_tag \/ t = partial_app_tag then (eq_res (Eq_val T),s)
         else bvl_evaluate ([e],env,s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[check_closure_def] THEN
  ASM_REWRITE_TAC[bvl_evaluate_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; APPEND; C2BP1AUX_do_app_TagEq] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[HD; bvl_Boolv_11] THEN
  REWRITE_TAC[bvl_Bool_def; bvl_evaluate_def; eq_res_def; REVERSE; bvl_do_app_Cons] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[bvl_Boolv_def; eq_res_def] THEN
  ASM_CASES_TAC `t = closure_tag` THEN ASM_REWRITE_TAC[REVERSE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 1864: val s = s:('c,'ffi) bvlSem$state (an annotation) *)

(* HOL4 line 1868 *)
let EXISTS_NOT_IN_refs = prove
 (`!(t1:(C,FFI)bvl_state). ?x. ~(x IN FDOM (bvl_state_refs t1))`,
  GEN_TAC THEN MP_TAC (ISPEC `bvl_state_refs (t1:(C,FFI)bvl_state)` FDOM_FINITE) THEN
  REWRITE_TAC[num_FINITE] THEN STRIP_TAC THEN EXISTS_TAC `a + 1` THEN
  ASM_MESON_TAC[ARITH_RULE `~(a + 1 <= a)`]);;

(* HOL4 line 1874: val lookup_vars_IMP2 = Q.prove(...) |> INST_TYPE        *)
(* [alpha |-> 'c, beta |-> 'ffi]                                             *)
let lookup_vars_IMP2 = prove
 (`!vs env xs env2 max_app f refs code.
     lookup_vars vs env = SOME xs /\
     clos_to_bvlProof_env_rel max_app f refs code env env2
     ==> ?ys. (!(t1:(C,FFI)bvl_state). bvl_evaluate (MAP bvl_Var vs,env2,t1) = (Rval ys,t1)) /\
              ALL2 (clos_to_bvlProof_v_rel max_app f refs code) xs ys /\
              LENGTH vs = LENGTH xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[lookup_vars_def; option_INJ; MAP] THENL
   [REPEAT STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `[]:bvl_v list` THEN
    REWRITE_TAC[bvl_evaluate_def; ALL2; LENGTH];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  CASES_ON `lookup_vars t (env:clos_v list)` THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`env:clos_v list`; `a:clos_v list`; `env2:bvl_v list`;
                                 `max_app:num`; `f:(num,num)fmap`;
                                 `refs:(num,(bvl_v)bvl_ref)fmap`; `code:(num#bvl_exp)spt`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`env:clos_v list`; `env2:bvl_v list`; `h:num`; `max_app:num`;
                  `f:(num,num)fmap`; `refs:(num,(bvl_v)bvl_ref)fmap`; `code:(num#bvl_exp)spt`]
          LESS_LENGTH_env_rel_IMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `CONS (EL h env2) (ys:bvl_v list)` THEN
  ASM_REWRITE_TAC[ALL2; LENGTH] THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN ASM_REWRITE_TAC[bvl_evaluate_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD]);;

(* HOL4 line 1889 *)
let lookup_vars_IMP = prove
 (`!vs env xs env2 max_app f refs code (t1:(C,FFI)bvl_state).
     lookup_vars vs env = SOME xs /\
     clos_to_bvlProof_env_rel max_app f refs code env env2
     ==> ?ys. bvl_evaluate (MAP bvl_Var vs,env2,t1) = (Rval ys,t1) /\
              ALL2 (clos_to_bvlProof_v_rel max_app f refs code) xs ys /\
              LENGTH vs = LENGTH xs`,
  MESON_TAC[lookup_vars_IMP2]);;

(* HOL4 line 1901 *)
let compile_exps_IMP_code_installed = prove
 (`!max_app xs aux c aux1 code.
     clos_to_bvl_compile_exps max_app xs aux = (c,aux1) /\
     clos_to_bvlProof_code_installed aux1 code
     ==> clos_to_bvlProof_code_installed aux code`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`max_app:num`; `xs:clos_exp list`; `aux:(num#num#bvl_exp)list`]
          compile_exps_acc) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[clos_to_bvlProof_code_installed_def]) THEN
  REWRITE_TAC[clos_to_bvlProof_code_installed_def] THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[ALL_APPEND]) THEN ASM_REWRITE_TAC[]);;

let C2BP1AUX_build_aux_MEM_EL = prove
 (`!l n (aux:(num#num#bvl_exp)list) n1 aux1 k.
     build_aux n l aux = (n1,aux1) /\ k < LENGTH l ==> MEM (n + 2 * k,EL k l) aux1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; LT; build_aux_def] THEN
  REWRITE_TAC[GSYM LT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CASES_ON `k:num` THENL
   [REWRITE_TAC[EL; HD; MULT_CLAUSES; ADD_CLAUSES] THEN
    MP_TAC (ISPECL [`t:(num#bvl_exp)list`; `n + 2`; `CONS (n:num,h:num#bvl_exp) aux`]
            build_aux_acc) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[MEM_APPEND; MEM];
    REWRITE_TAC[EL; TL] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`n + 2`; `CONS (n:num,h:num#bvl_exp) aux`; `n1:num`;
                                   `aux1:(num#num#bvl_exp)list`; `n':num`]) THEN
    RULE_ASSUM_TAC (REWRITE_RULE[LT_SUC]) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `(n + 2) + 2 * k = n + 2 * SUC k`]]);;

let C2BP1AUX_code_installed_MEM = prove
 (`!aux code. clos_to_bvlProof_code_installed aux code <=>
              !n a e. MEM (n,a,e) aux ==> lookup n code = SOME (a,e)`,
  REWRITE_TAC[clos_to_bvlProof_code_installed_def; GSYM ALL_MEM; FORALL_PAIR_THM] THEN
  CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

(* compile_exps_EL (HOL4 line 1975), used here before its place *)
let C2BP1AUX_compile_exps_EL = prove
 (`!ls aux l2 aux2 n ma.
     clos_to_bvl_compile_exps ma ls aux = (l2,aux2) /\ n < LENGTH ls
     ==> ?auxn aux2n.
           clos_to_bvl_compile_exps ma [EL n ls] auxn = ([EL n l2],aux2n) /\
           IS_SUBLIST aux2 aux2n`,
  MATCH_MP_TAC SNOC_INDUCT THEN REWRITE_TAC[LENGTH; LT] THEN
  X_GEN_TAC `ls:clos_exp list` THEN DISCH_TAC THEN X_GEN_TAC `x:clos_exp` THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_exps_SNOC; LENGTH_SNOC] THEN
  PAIRARG_TAC THEN PAIRARG_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `LENGTH (c1:bvl_exp list) = LENGTH (ls:clos_exp list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[clos_to_bvl_compile_exps_LENGTH]; ALL_TAC] THEN
  FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP clos_to_bvl_compile_exps_SING o
    check (fun th -> can (find_term ((=) `[x:clos_exp]`)) (concl th))) THEN
  RVEQ_TAC THEN
  ASM_CASES_TAC `n = LENGTH (ls:clos_exp list)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MAP_EVERY EXISTS_TAC [`aux1:(num#num#bvl_exp)list`; `aux2:(num#num#bvl_exp)list`] THEN
    REWRITE_TAC[EL_LENGTH_SNOC; IS_SUBLIST_REFL] THEN
    UNDISCH_TAC `LENGTH (c1:bvl_exp list) = LENGTH (ls:clos_exp list)` THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[el_append2];
    SUBGOAL_THEN `n < LENGTH (ls:clos_exp list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_SNOC; EL_APPEND1] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`aux:(num#num#bvl_exp)list`; `c1:bvl_exp list`;
                                   `aux1:(num#num#bvl_exp)list`; `n:num`; `ma:num`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`auxn:(num#num#bvl_exp)list`; `aux2n:(num#num#bvl_exp)list`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC (SPECL [`ma:num`; `[x:clos_exp]`; `aux1:(num#num#bvl_exp)list`] compile_exps_acc) THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[IS_SUBLIST_APPEND2]]);;

(* HOL4 line 1911 *)
let compile_exps_LIST_IMP_compile_exps_EL = prove
 (`!exps aux1 c7 aux7 i n8 n4 aux5 num_args e max_app k (t1:(C,FFI)bvl_state).
     EL i exps = (num_args,e) /\
     clos_to_bvl_compile_exps max_app (MAP SND exps) aux1 = (c7,aux7) /\ i < LENGTH exps /\
     build_aux n8 (MAP2 (code_for_recc_case k) (MAP FST exps) c7) aux7 = (n4,aux5) /\
     clos_to_bvlProof_code_installed aux5 (bvl_state_code t1)
     ==> ?aux c aux1'.
           clos_to_bvl_compile_exps max_app [e] aux = ([c],aux1') /\
           lookup (n8 + 2 * i) (bvl_state_code t1) =
             SOME (num_args + 1,SND (code_for_recc_case k num_args c)) /\
           clos_to_bvlProof_code_installed aux1' (bvl_state_code t1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`MAP SND (exps:(num#clos_exp)list)`; `aux1:(num#num#bvl_exp)list`;
                  `c7:bvl_exp list`; `aux7:(num#num#bvl_exp)list`; `i:num`; `max_app:num`]
          C2BP1AUX_compile_exps_EL) THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (c7:bvl_exp list) = LENGTH (exps:(num#clos_exp)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[clos_to_bvl_compile_exps_LENGTH; LENGTH_MAP]; ALL_TAC] THEN
  SUBGOAL_THEN `EL i (MAP SND (exps:(num#clos_exp)list)) = e /\
                EL i (MAP FST (exps:(num#clos_exp)list)) = num_args` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[EL_MAP]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`auxn:(num#num#bvl_exp)list`; `EL i (c7:bvl_exp list)`;
                        `aux2n:(num#num#bvl_exp)list`] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[ASSUME `EL i (MAP SND (exps:(num#clos_exp)list)) = e`]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC (ISPECL [`MAP2 (code_for_recc_case k) (MAP FST (exps:(num#clos_exp)list)) c7`;
                  `n8:num`; `aux7:(num#num#bvl_exp)list`]
          build_aux_acc) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o REWRITE_RULE[C2BP1AUX_code_installed_MEM] o
    check (fun th -> can (find_term ((=) `aux5:(num#num#bvl_exp)list`)) (concl th) &&
                     can (find_term ((=) `clos_to_bvlProof_code_installed`)) (concl th))) THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [MP_TAC (ISPECL [`MAP2 (code_for_recc_case k) (MAP FST (exps:(num#clos_exp)list)) c7`;
                    `n8:num`; `aux7:(num#num#bvl_exp)list`; `n4:num`;
                    `aux5:(num#num#bvl_exp)list`; `i:num`] C2BP1AUX_build_aux_MEM_EL) THEN
    ASM_SIMP_TAC[LENGTH_MAP2; LENGTH_MAP; el_map2] THEN
    REWRITE_TAC[code_for_recc_case_def] THEN ASM_MESON_TAC[];
    REWRITE_TAC[C2BP1AUX_code_installed_MEM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM_APPEND] THEN DISJ2_TAC THEN
    MATCH_MP_TAC IS_SUBLIST_MEM THEN EXISTS_TAC `aux2n:(num#num#bvl_exp)list` THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 1975 *)
let compile_exps_EL = prove
 (`!ls aux l2 aux2 n ma.
     clos_to_bvl_compile_exps ma ls aux = (l2,aux2) /\ n < LENGTH ls
     ==> ?auxn aux2n.
           clos_to_bvl_compile_exps ma [EL n ls] auxn = ([EL n l2],aux2n) /\
           IS_SUBLIST aux2 aux2n`,
  MATCH_ACCEPT_TAC C2BP1AUX_compile_exps_EL);;

let C2BP1AUX_do_app_Update = prove
 (CASE_TERM `!b ptr i v (s:(C,FFI)bvl_state).
     bvl_do_app (MemOp Update) [bvl_RefPtr b ptr; bvl_Number i; v] s =
     match FLOOKUP (bvl_state_refs s) ptr with
       SOME (bvl_ValueArray xs) ->
         (if &0 <= i /\ i < &(LENGTH xs)
          then Rval (bvl_Unit,
                     bvl_state_refs_fupd
                       (K (bvl_state_refs s |+
                           (ptr,bvl_ValueArray (LUPDATE v (num_of_int i) xs)))) s)
          else Rerr (Rabort Rtype_error))
     | _ -> Rerr (Rabort Rtype_error)`,
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[]);;

let C2BP1AUX_eval_recc_Let = prove
 (`!n num_args i rest env (s:(C,FFI)bvl_state) rr p a refsl.
     n IN domain (bvl_state_code s) /\
     FLOOKUP (bvl_state_refs s) rr = SOME (bvl_ValueArray refsl) /\ i < LENGTH refsl
     ==> bvl_evaluate ([bvl_Let [recc_Let n num_args i] rest],
                       CONS (bvl_Block closure_tag [bvl_CodePtr p; bvl_Number a; bvl_RefPtr T rr])
                         env, s) =
         bvl_evaluate ([rest],
                       CONS (bvl_Block closure_tag [bvl_CodePtr n; bvl_Number (&(num_args - 1));
                                                    bvl_RefPtr T rr])
                         (CONS (bvl_Block closure_tag [bvl_CodePtr p; bvl_Number a;
                                                       bvl_RefPtr T rr]) env),
                       bvl_state_refs_fupd
                         (K (bvl_state_refs s |+
                             (rr,bvl_ValueArray
                                   (LUPDATE (bvl_Block closure_tag
                                               [bvl_CodePtr n; bvl_Number (&(num_args - 1));
                                                bvl_RefPtr T rr]) i refsl)))) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[recc_Let_def] THEN
  C2BP1AUX_EVAL_LHS_TAC (C2BP1AUX_eval_lemmas @ [C2BP1AUX_do_app_Update; LENGTH; EL; HD; TL]) THEN
  REWRITE_TAC[]);;

let C2BP1AUX_eval_recc_Let2 = prove
 (`!n num_args i rest env (s:(C,FFI)bvl_state) r rr p a refsl.
     n IN domain (bvl_state_code s) /\ i < LENGTH refsl
     ==> bvl_evaluate ([bvl_Let [recc_Let n num_args i] rest],
                       CONS (bvl_Block closure_tag [bvl_CodePtr p; bvl_Number a; bvl_RefPtr T rr])
                         env,
                       bvl_state_refs_fupd (K (r |+ (rr,bvl_ValueArray refsl))) s) =
         bvl_evaluate ([rest],
                       CONS (bvl_Block closure_tag [bvl_CodePtr n; bvl_Number (&(num_args - 1));
                                                    bvl_RefPtr T rr])
                         (CONS (bvl_Block closure_tag [bvl_CodePtr p; bvl_Number a;
                                                       bvl_RefPtr T rr]) env),
                       bvl_state_refs_fupd
                         (K (r |+
                             (rr,bvl_ValueArray
                                   (LUPDATE (bvl_Block closure_tag
                                               [bvl_CodePtr n; bvl_Number (&(num_args - 1));
                                                bvl_RefPtr T rr]) i refsl)))) s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`n:num`; `num_args:num`; `i:num`; `rest:bvl_exp`; `env:bvl_v list`;
                  `bvl_state_refs_fupd (K (r |+ (rr,bvl_ValueArray refsl))) (s:(C,FFI)bvl_state)`;
                  `rr:num`; `p:num`; `a:int`; `refsl:bvl_v list`] C2BP1AUX_eval_recc_Let) THEN
  SIMP[FLOOKUP_UPDATE; FUPDATE_EQ]);;

let C2BP1AUX_recc_MAP2_SNOC = prove
 (`!(f:num->num->bvl_v) (l:(num#A)list) (y0:num#A) a.
     MAP2 f (list_of_seq I (SUC (LENGTH l) + 1)) (APPEND (SNOC (FST y0) (MAP FST l)) [a]) =
     APPEND (MAP2 f (list_of_seq I (LENGTH l + 1)) (APPEND (MAP FST l) [FST y0]))
       [f (SUC (LENGTH l)) a]`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `list_of_seq I (SUC (LENGTH (l:(num#A)list)) + 1) =
                SNOC (SUC (LENGTH l)) (list_of_seq I (LENGTH l + 1))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM ADD1] THEN REWRITE_TAC[CONJUNCT2 GENLIST; I_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `APPEND (SNOC (FST (y0:num#A)) (MAP FST (l:(num#A)list))) [a:num] =
                SNOC a (APPEND (MAP FST l) [FST y0])` SUBST1_TAC THENL
   [REWRITE_TAC[SNOC_APPEND]; ALL_TAC] THEN
  MATCH_MP_TAC map2_snoc THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; LENGTH_APPEND; LENGTH_MAP; LENGTH] THEN ARITH_TAC);;

let C2BP1AUX_recc_LUPDATE = prove
 (`!(l:(num#A)list) (y0:num#A) nb b ys.
     LUPDATE nb (LENGTH l)
       (APPEND (APPEND (SNOC (K (bvl_Number (&0)) (FST y0)) (MAP (K (bvl_Number (&0))) (MAP FST l)))
                 [b]) ys) =
     APPEND (APPEND (MAP (K (bvl_Number (&0))) (MAP FST l)) [nb]) (CONS b ys)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `LENGTH (l:(num#A)list) = LENGTH (MAP (K (bvl_Number (&0))) (MAP FST l))`
    SUBST1_TAC THENL [REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  REWRITE_TAC[SNOC_APPEND; GSYM APPEND_ASSOC; APPEND; LUPDATE_LENGTH]);;

(* HOL4 line 2003 (ns is free in HOL4) *)
let evaluate_recc_Lets = prove
 (`!(ll:(num#A)list) n7 rr env' (t1:(C,FFI)bvl_state) ys c8 (x:num#A) (x':num#A) ck ns.
     ALL (\n. n7 + ns + 2 * n IN domain (bvl_state_code t1)) (list_of_seq I (LENGTH ll))
     ==> bvl_evaluate
           ([recc_Lets (n7 + ns) (REVERSE (MAP FST ll)) (LENGTH ll) (HD c8)],
            CONS (bvl_Block closure_tag
                    [bvl_CodePtr (n7 + (ns + 2 * LENGTH ll)); bvl_Number (&(FST x - 1));
                     bvl_RefPtr T rr]) env',
            bvl_state_refs_fupd
              (K (bvl_state_refs t1 |+
                  (rr,bvl_ValueArray
                        (APPEND (APPEND (MAP (K (bvl_Number (&0))) (MAP FST ll))
                           [bvl_Block closure_tag
                              [bvl_CodePtr (n7 + (ns + 2 * LENGTH ll));
                               bvl_Number (&(FST x' - 1)); bvl_RefPtr T rr]]) ys))))
              (bvl_state_clock_fupd (K ck) t1)) =
         bvl_evaluate
           ([HD c8],
            APPEND (MAP2 (\n args. bvl_Block closure_tag
                                     [bvl_CodePtr (n7 + ns + 2 * n); bvl_Number (&(args - 1));
                                      bvl_RefPtr T rr])
                      (list_of_seq I (LENGTH ll + 1)) (APPEND (MAP FST ll) [FST x])) env',
            bvl_state_refs_fupd
              (K (bvl_state_refs t1 |+
                  (rr,bvl_ValueArray
                        (APPEND (MAP2 (\n args. bvl_Block closure_tag
                                                  [bvl_CodePtr (n7 + ns + 2 * n);
                                                   bvl_Number (&(args - 1)); bvl_RefPtr T rr])
                                   (list_of_seq I (LENGTH ll + 1))
                                   (APPEND (MAP FST ll) [FST x'])) ys))))
              (bvl_state_clock_fupd (K ck) t1))`,
  MATCH_MP_TAC SNOC_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[recc_Lets_def] THEN
    REWRITE_TAC[LENGTH; MAP; REVERSE; APPEND; ADD_CLAUSES; MULT_CLAUSES] THEN
    REWRITE_TAC[ONE; list_of_seq; APPEND; MAP2; I_THM] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES];
    ALL_TAC] THEN
  X_GEN_TAC `l:(num#A)list` THEN DISCH_TAC THEN X_GEN_TAC `y0:num#A` THEN
  MAP_EVERY X_GEN_TAC [`n7:num`; `rr:num`; `env':bvl_v list`; `t1:(C,FFI)bvl_state`;
                       `ys:bvl_v list`; `c8:bvl_exp list`; `x:num#A`; `x':num#A`; `ck:num`;
                       `ns:num`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE[LENGTH_SNOC; CONJUNCT2 GENLIST; EVERY_SNOC;
                                                 I_THM]) THEN
  REWRITE_TAC[LENGTH_SNOC; MAP_SNOC; REVERSE_SNOC] THEN
  ONCE_REWRITE_TAC[recc_Lets_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; LET_DEF; LET_END_DEF; HD; TL] THEN
  W(fun (asl,w) -> MP_TAC (PART_MATCH (lhand o rand) C2BP1AUX_eval_recc_Let2 (lhand w))) THEN
  ANTS_TAC THENL
   [SIMP[GSYM ADD_ASSOC; LENGTH_APPEND; LENGTH_SNOC; LENGTH_MAP; LENGTH] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[C2BP1AUX_recc_LUPDATE; C2BP1AUX_recc_MAP2_SNOC; GSYM APPEND_ASSOC; APPEND;
              GSYM ADD_ASSOC] THEN
  FIRST_X_ASSUM (MP_TAC o SPECL
    [`n7:num`; `rr:num`;
     `CONS (bvl_Block closure_tag [bvl_CodePtr (n7 + ns + 2 * SUC (LENGTH (l:(num#A)list)));
                                   bvl_Number (&(FST (x:num#A) - 1)); bvl_RefPtr T rr]) env'`;
     `t1:(C,FFI)bvl_state`;
     `CONS (bvl_Block closure_tag [bvl_CodePtr (n7 + ns + 2 * SUC (LENGTH (l:(num#A)list)));
                                   bvl_Number (&(FST (x':num#A) - 1)); bvl_RefPtr T rr]) ys`;
     `c8:bvl_exp list`; `y0:num#A`; `y0:num#A`; `ck:num`; `ns:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN (fun th -> REWRITE_TAC[REWRITE_RULE[GSYM APPEND_ASSOC; APPEND] th]));;

(* HOL4 line 2055 *)
let evaluate_app_helper = prove
 (CASE_TERM `!r c8 env (s:(C,FFI)bvl_state) s' loc c7 max_app.
     (!x. ~(r = Rval x)) /\ bvl_evaluate (c8,env,s) = (r,s')
     ==> bvl_evaluate
           ([match loc with
               NONE -> bvl_Let (APPEND c8 [c7])
                         (mk_cl_call (bvl_Var (LENGTH c8)) (list_of_seq bvl_Var (LENGTH c8)))
             | SOME loc -> bvl_Call (LENGTH c8 - 1) (SOME (loc + num_stubs max_app))
                             (APPEND c8 [c7])],env,s) = (r,s')`,
  REPEAT GEN_TAC THEN CASES_ON `r:(bvl_v list,bvl_v)result` THENL
   [MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  CASES_ON `loc:num option` THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[bvl_evaluate_def; bvl_evaluate_APPEND] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 2070 *)
let evaluate_app_helper2 = prove
 (CASE_TERM `!r c8 env (s:(C,FFI)bvl_state) x s' c7 s'' loc max_app.
     (!x. ~(r = Rval x)) /\ bvl_evaluate (c8,env,s) = (Rval x,s') /\
     bvl_evaluate ([c7],env,s') = (r,s'')
     ==> bvl_evaluate
           ([match loc with
               NONE -> bvl_Let (APPEND c8 [c7])
                         (mk_cl_call (bvl_Var (LENGTH c8)) (list_of_seq bvl_Var (LENGTH c8)))
             | SOME loc -> bvl_Call (LENGTH c8 - 1) (SOME (loc + num_stubs max_app))
                             (APPEND c8 [c7])],env,s) = (r,s'')`,
  REPEAT GEN_TAC THEN CASES_ON `r:(bvl_v list,bvl_v)result` THENL
   [MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  CASES_ON `loc:num option` THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[bvl_evaluate_def; bvl_evaluate_APPEND] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 2084 *)
let evaluate_simple_genlist_vars = prove
 (`!env1 env2 (s:(C,FFI)bvl_state).
     0 < LENGTH env1
     ==> bvl_evaluate (list_of_seq bvl_Var (LENGTH env1),APPEND env1 env2,s) = (Rval env1,s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`0`; `APPEND env1 env2:bvl_v list`; `LENGTH (env1:bvl_v list)`;
                  `s:(C,FFI)bvl_state`] bvl_evaluate_genlist_vars) THEN
  REWRITE_TAC[ADD_CLAUSES; LENGTH_APPEND; LE_ADD; DROP_0; TAKE_LENGTH_APPEND; ETA_AX]);;

(* HOL4 line 2098 *)
let num_remaining_args_def = cake_def
  `(num_remaining_args (clos_Closure loc_opt args env num_args exp) =
      SOME (num_args - LENGTH args)) /\
   (num_remaining_args (clos_Recclosure loc_opt args env funs i) =
      SOME (FST (EL i funs) - LENGTH args)) /\
   (num_remaining_args (_:clos_v) = NONE)`;;

(* HOL4 line 2106 (HOL4's binders f1 and t1 are unused, left out) *)
let dest_closure_part_app = prove
 (`!loc_opt func args c max_app.
     ~(LENGTH args = 0) /\
     dest_closure max_app loc_opt func args = SOME (Partial_app c)
     ==> loc_opt = NONE /\
         SOME c = add_args func args /\
         ?n. num_remaining_args func = SOME n /\ LENGTH args < n /\ LENGTH args <= max_app`,
  REPEAT GEN_TAC THEN CASES_ON `func:clos_v` THEN
  REWRITE_TAC[dest_closure_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  TRY (PAIRARG_TAC) THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT COND_CASES_TAC THEN
  SIMP[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  CASES_ON `loc_opt:num option` THEN
  RULE_ASSUM_TAC (REWRITE_RULE[check_loc_def; DE_MORGAN_THM]) THEN
  ASM_REWRITE_TAC[add_args_def; num_remaining_args_def; option_INJ; option_DISTINCT] THEN
  TRY (FIRST_X_ASSUM (STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  ASM_REWRITE_TAC[UNWIND_THM1] THEN C2BP1AUX_ARITH_TAC);;

(* HOL4 line 2127 (made with sem1aux_def: cake_def takes 270 s) *)
let get_loc_def = sem1aux_def
  `(get_loc (clos_Closure (SOME loc) args env num_args exp) = SOME loc) /\
   (get_loc (clos_Recclosure (SOME loc) args env fns i) = SOME (loc + 2 * i)) /\
   (get_loc (_:clos_v) = NONE)`;;

(* HOL4 line 2133 *)
let get_old_args_def = cake_def
  `(get_old_args (clos_Closure loc args env num_args exp) = SOME args) /\
   (get_old_args (clos_Recclosure loc args env fns i) = SOME args) /\
   (get_old_args (_:clos_v) = NONE)`;;

(* HOL4 line 2139 *)
let get_cl_env_def = cake_def
  `(get_cl_env (clos_Closure loc args env num_args exp) = SOME env) /\
   (get_cl_env (clos_Recclosure loc args env fns i) = SOME env) /\
   (get_cl_env (_:clos_v) = NONE)`;;

(* HOL4 line 2145 (HOL4's binders c, f1 and t1 are unused, left out) *)
let dest_closure_full_app = prove
 (`!loc_opt func args exp args1 args2 max_app.
     dest_closure max_app loc_opt func args = SOME (Full_app exp args1 args2)
     ==> ?rem_args loc num_args old_args cl_env.
           get_loc func = loc /\
           num_remaining_args func = SOME rem_args /\
           get_num_args func = SOME num_args /\
           get_old_args func = SOME old_args /\
           get_cl_env func = SOME cl_env /\
           rem_args <= LENGTH args /\
           rem_args <= num_args /\
           num_args <= LENGTH old_args + LENGTH args /\
           LENGTH args2 = LENGTH args - rem_args /\
           check_loc max_app loc_opt loc num_args (LENGTH args) (num_args - rem_args)`,
  REPEAT GEN_TAC THEN CASES_ON `func:clos_v` THEN
  REWRITE_TAC[dest_closure_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  TRY (PAIRARG_TAC) THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT COND_CASES_TAC THEN SIMP[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[get_loc_def; num_remaining_args_def; get_num_args_def; get_old_args_def;
                  get_cl_env_def; option_INJ; UNWIND_THM1; LENGTH_REVERSE; LENGTH_DROP] THEN
  SIMP[] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[DE_MORGAN_THM; NOT_LE]) THEN
  REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  ASM_SIMP_TAC[ARITH_RULE `!a b. b < a ==> a - (a - b) = b`] THEN
  CASES_ON `a0:num option` THEN
  RULE_ASSUM_TAC (REWRITE_RULE[OPTION_MAP_DEF]) THEN
  ASM_REWRITE_TAC[get_loc_def] THEN
  TRY (ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[]) THEN
  C2BP1AUX_ARITH_TAC);;

let C2BP1AUX_closure_code_installed_EL = prove
 (`!max_app code exps_ps env k n e p.
     closure_code_installed max_app code exps_ps env /\ k < LENGTH exps_ps /\
     EL k exps_ps = ((n,e),p)
     ==> n <= max_app /\ ~(n = 0) /\
         ?aux c aux1.
           clos_to_bvl_compile_exps max_app [e] aux = ([c],aux1) /\
           lookup p code =
             SOME (n + 1,SND (code_for_recc_case (LENGTH env + LENGTH exps_ps) n c)) /\
           clos_to_bvlProof_code_installed aux1 code`,
  REWRITE_TAC[closure_code_installed_def; GSYM ALL_EL] THEN REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 (MP_TAC o SPEC `k:num`) STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let C2BP1AUX_cl_rel_IMP = prove
 (`!max_app fs refs code e x y.
     cl_rel max_app fs refs code e x y
     ==> ?n ptr rest exp.
           get_num_args x = SOME n /\ num_remaining_args x = SOME n /\
           get_old_args x = SOME [] /\ ~(n = 0) /\ n <= max_app /\
           y = bvl_Block closure_tag (CONS (bvl_CodePtr ptr) (CONS (bvl_Number (&(n - 1))) rest)) /\
           lookup ptr code = SOME (n + 1,exp)`,
  MATCH_MP_TAC cl_rel_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[get_num_args_def; num_remaining_args_def; get_old_args_def; LENGTH; SUB_0;
                  EL; HD] THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?n0 e0 p0. EL k (exps_ps:((num#clos_exp)#num)list) = ((n0,e0),p0)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `k < LENGTH (exps_ps:((num#clos_exp)#num)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_MAP]; ALL_TAC] THEN
  MP_TAC (ISPECL [`max_app:num`; `code:(num#bvl_exp)spt`; `exps_ps:((num#clos_exp)#num)list`;
                  `env:clos_v list`; `k:num`; `n0:num`; `e0:clos_exp`; `p0:num`]
          C2BP1AUX_closure_code_installed_EL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`n0:num`; `p0:num`; `[bvl_RefPtr T r]`;
                        `SND (code_for_recc_case (LENGTH (env:clos_v list) +
                                LENGTH (exps_ps:((num#clos_exp)#num)list)) n0 c)`] THEN
  ASM_SIMP_TAC[EL_MAP] THEN CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let C2BP1AUX_INT_SUB1 = prove
 (`!a b. ~(b = 0) ==> (&a - &1 = &(b - 1):int <=> a = b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&(b - 1):int = &b - &1` SUBST1_TAC THENL
   [MATCH_MP_TAC (GSYM INT_OF_NUM_SUB) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INT_ARITH `a - &1 = b - &1 <=> a = b:int`; INT_OF_NUM_EQ]);;

let C2BP1AUX_add_args_IMP = prove
 (`!cl args cl'.
     add_args cl args = SOME cl' /\ get_old_args cl = SOME []
     ==> num_remaining_args cl' = OPTION_MAP (\m. m - LENGTH args) (num_remaining_args cl) /\
         get_num_args cl' = get_num_args cl /\ get_old_args cl' = SOME args`,
  GEN_TAC THEN CASES_ON `cl:clos_v` THEN
  REWRITE_TAC[add_args_def; get_old_args_def; option_DISTINCT; option_INJ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[num_remaining_args_def; get_num_args_def; get_old_args_def; OPTION_MAP_DEF;
              APPEND_NIL; LENGTH; SUB_0]);;

(* HOL4 line 2176 *)
let v_rel_num_rem_args = prove
 (`!f refs code v1 v2 n max_app.
     clos_to_bvlProof_v_rel max_app f refs code v1 v2 /\
     num_remaining_args v1 = SOME n
     ==> ?tag ptr rest exp.
           v2 = bvl_Block tag (CONS (bvl_CodePtr ptr) (CONS (bvl_Number (&n - &1)) rest)) /\
           ~(n = 0) /\
           lookup ptr code = SOME (n + 1,exp)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [clos_to_bvlProof_v_rel_cases] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[num_remaining_args_def; option_DISTINCT]) THEN
  TRY (FIRST_X_ASSUM CONTR_TAC) THENL
   [FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP C2BP1AUX_cl_rel_IMP) THEN
    SUBGOAL_THEN `n'' = n:num` SUBST_ALL_TAC THENL [ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
    RULE_ASSUM_TAC (CAKE_SIMP_RULE[]) THEN
    REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o check (is_conj o concl))) THEN RVEQ_TAC THEN
    SUBGOAL_THEN `&(n - 1):int = &n - &1` SUBST1_TAC THENL
     [MATCH_MP_TAC (GSYM INT_OF_NUM_SUB) THEN C2BP1AUX_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP C2BP1AUX_cl_rel_IMP) THEN
    MP_TAC (ISPECL [`cl:clos_v`; `arg_env:clos_v list`; `v1:clos_v`] C2BP1AUX_add_args_IMP) THEN
    ASM_REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN STRIP_TAC THEN
    SUBGOAL_THEN `n' = num_args:num /\ n = num_args - LENGTH (arg_env:clos_v list)`
      (CONJUNCTS_THEN SUBST_ALL_TAC) THENL [ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`partial_app_tag`;
                          `partial_app_fn_location max_app (num_args - 1) (LENGTH (ys:bvl_v list) - 1)`;
                          `CONS (cl':bvl_v) ys`;
                          `generate_partial_app_closure_fn (num_args - 1) (LENGTH (ys:bvl_v list) - 1)`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&((num_args - 1) - LENGTH (arg_env:clos_v list)):int = &(num_args - LENGTH arg_env) - &1`
      SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `(a - 1) - b = (a - b) - 1`] THEN
      MATCH_MP_TAC (GSYM INT_OF_NUM_SUB) THEN C2BP1AUX_ARITH_TAC;
      C2BP1AUX_ARITH_TAC]]);;

(* HOL4 line 2209: val unpack_closure_thm = Q.prove(...) |> INST_TYPE       *)
(* [alpha |-> 'ffi]                                                           *)
let unpack_closure_thm = prove
 (`!max_app f1 (t1:(C,FFI)bvl_state) func tag ptr n rest.
     clos_to_bvlProof_v_rel max_app f1 (bvl_state_refs t1) (bvl_state_code t1) func
       (bvl_Block tag (CONS ptr (CONS (bvl_Number (&n - &1)) rest))) /\
     num_remaining_args func = SOME n
     ==> ?prev_args total_args clo.
           unpack_closure (bvl_Block tag (CONS ptr (CONS (bvl_Number (&n - &1)) rest)))
             (prev_args,total_args,clo) /\
           total_args < max_app /\
           n = (total_args - LENGTH prev_args) + 1 /\
           (tag = closure_tag
            ==> prev_args = [] /\
                clo = bvl_Block tag (CONS ptr (CONS (bvl_Number (&n - &1)) rest)))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [clos_to_bvlProof_v_rel_cases] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC (CAKE_SIMP_RULE[num_remaining_args_def]) THEN
  REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE[num_remaining_args_def; option_DISTINCT]) THEN
  TRY (FIRST_X_ASSUM CONTR_TAC) THEN
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP C2BP1AUX_cl_rel_IMP) THENL
   [SUBGOAL_THEN `n'' = n:num` SUBST_ALL_TAC THENL [ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
    SUBGOAL_THEN `&n - &1:int = &(n - 1)` SUBST1_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_SUB THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`[]:bvl_v list`; `n - 1`] THEN
    EXISTS_TAC `bvl_Block closure_tag (CONS (bvl_CodePtr p) (CONS (bvl_Number (&(n - 1))) ys))` THEN
    REWRITE_TAC[LENGTH; SUB_0] THEN CONJ_TAC THENL
     [MP_TAC (ISPECL [`&(n - 1):int`; `p:num`; `ys:bvl_v list`]
              (CONJUNCT1 unpack_closure_rules)) THEN
      REWRITE_TAC[NUM_OF_INT_OF_NUM; INT_GE; INT_POS];
      C2BP1AUX_ARITH_TAC];
    MP_TAC (ISPECL [`cl:clos_v`; `arg_env:clos_v list`; `func:clos_v`] C2BP1AUX_add_args_IMP) THEN
    ASM_REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN STRIP_TAC THEN
    SUBGOAL_THEN `n' = num_args:num` SUBST_ALL_TAC THENL [ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (ys:bvl_v list) = LENGTH (arg_env:clos_v list)` ASSUME_TAC THENL
     [ASM_MESON_TAC[LIST_REL_LENGTH]; ALL_TAC] THEN
    SUBGOAL_THEN `~(ys:bvl_v list = [])` ASSUME_TAC THENL
     [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`ys:bvl_v list`;
                          `num_args - 1 - LENGTH (arg_env:clos_v list) + LENGTH (ys:bvl_v list)`] THEN
    REWRITE_TAC[closure_tag_def; partial_app_tag_def; ARITH_EQ; RIGHT_EXISTS_AND_THM] THEN
    EXISTS_TAC `bvl_Block 30 (CONS (bvl_CodePtr ptr) (CONS (bvl_Number (&(num_args - 1))) rest))` THEN
    CONJ_TAC THENL
     [MP_TAC (ISPECL [`ys:bvl_v list`; `&(num_args - 1 - LENGTH (arg_env:clos_v list)):int`;
                      `partial_app_fn_location max_app (num_args - 1) (LENGTH (ys:bvl_v list) - 1)`;
                      `bvl_Block 30 (CONS (bvl_CodePtr ptr) (CONS (bvl_Number (&(num_args - 1))) rest))`]
                     (CONJUNCT2 unpack_closure_rules)) THEN
      ASM_REWRITE_TAC[NUM_OF_INT_OF_NUM; INT_GE; INT_POS; partial_app_tag_def];
      C2BP1AUX_ARITH_TAC]]);;

(* HOL4 line 2242 (HOL4 &(total_args) - 1 is the int &total_args - &1) *)
let cl_rel_get_num_args = prove
 (`!max_app f1 refs code env ys func tag p total_args fvs.
     cl_rel max_app f1 refs code (env,ys) func
       (bvl_Block tag (CONS p (CONS (bvl_Number (&total_args - &1)) fvs)))
     ==> get_num_args func = SOME total_args`,
  REPEAT GEN_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o MATCH_MP C2BP1AUX_cl_rel_IMP) THEN
  RULE_ASSUM_TAC (CAKE_SIMP_RULE[]) THEN
  ASM_REWRITE_TAC[option_INJ] THEN ASM_MESON_TAC[C2BP1AUX_INT_SUB1]);;

(* HOL4 line 2259 (HOL4 x - 1 - (LENGTH args' - 1) is                       *)
(* (x - 1) - (LENGTH args' - 1))                                              *)
let arith_helper_lem = prove
 (`!(args':A list) x.
     ~(LENGTH args' = 0) ==> (x - 1) - (LENGTH args' - 1) = x - LENGTH args'`,
  REPEAT GEN_TAC THEN ARITH_TAC);;

(* HOL4 line 2265 *)
let arith_helper_lem3 = prove
 (`!(args':A list) (prev_args:B list) total_args num_args.
     LENGTH args' < (total_args + 1) - LENGTH prev_args /\
     ~(LENGTH args' = 0) /\
     (total_args - LENGTH prev_args) + 1 = num_args - LENGTH prev_args
     ==> total_args - ((LENGTH args' + LENGTH prev_args) - 1) =
           (total_args + 1) - (LENGTH args' + LENGTH prev_args) /\
         LENGTH args' + LENGTH prev_args < total_args + 1 /\
         num_args = total_args + 1`,
  REPEAT GEN_TAC THEN ARITH_TAC);;

(* HOL4 lines 2277-2285: val closure_tag_neq_1 (EVAL), cEval_def, cEval_SING, *)
(* bEval_def, bEval_CONS, bEval_SING, bEval_APPEND, bEvalOp_def (aliases of *)
(* closSem/closProps/bvlSem/bvlProps theorems)                               *)

(* HOL4 line 2287 *)
let evaluate_mk_cl_call_spec = prove
 (CASE_TERM `!(s:(C,FFI)bvl_state) env tag p n args exp xs max_app.
     lookup p (bvl_state_code s) = SOME (n + 2,exp) /\
     lookup (generic_app_fn_location (LENGTH args - 1)) (bvl_state_code s) =
       SOME (LENGTH args + 1,generate_generic_app max_app (LENGTH args - 1)) /\
     LENGTH args - 1 >= n /\
     n < max_app /\
     ~(LENGTH args = 0)
     ==> bvl_evaluate
           ([mk_cl_call (bvl_Var (LENGTH args)) (list_of_seq bvl_Var (LENGTH args))],
            APPEND (APPEND args
                      [bvl_Block tag (CONS (bvl_CodePtr p) (CONS (bvl_Number (&n)) xs))]) env,
            s) =
         if n = LENGTH args - 1 then
           if bvl_state_clock s < LENGTH args
           then (Rerr (Rabort Rtimeout_error),bvl_state_clock_fupd (K 0) s)
           else bvl_evaluate
                  ([exp],
                   APPEND args
                     [bvl_Block tag (CONS (bvl_CodePtr p)
                                       (CONS (bvl_Number (&(LENGTH args - 1))) xs))],
                   bvl_dec_clock (LENGTH args) s)
         else
           if bvl_state_clock s < n + 2
           then (Rerr (Rabort Rtimeout_error),bvl_state_clock_fupd (K 0) s)
           else
             match bvl_evaluate
                     ([exp],
                      APPEND (DROP (LENGTH args - (n + 1)) args)
                        [bvl_Block tag (CONS (bvl_CodePtr p) (CONS (bvl_Number (&n)) xs))],
                      bvl_dec_clock (n + 2) s) with
               (Rval [v],st') ->
                 (match bvl_evaluate
                          ([mk_cl_call (bvl_Var 0)
                              (list_of_seq (\n. bvl_Var (n + 1)) (LENGTH args - (n + 1)))],
                           CONS v (APPEND args
                                     [bvl_Block tag (CONS (bvl_CodePtr p)
                                                       (CONS (bvl_Number (&n)) xs))]),
                           st') with
                    (Rval v,s2) -> (Rval [HD v],s2)
                  | x -> x)
             | x -> x`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `cl = bvl_Block tag (CONS (bvl_CodePtr p) (CONS (bvl_Number (&n)) xs))` THEN
  MP_TAC (ISPECL [`bvl_Var (LENGTH (args:bvl_v list))`;
                  `APPEND (APPEND args [cl:bvl_v]) env`; `s:(C,FFI)bvl_state`; `tag:num`;
                  `p:num`; `n:num`; `list_of_seq bvl_Var (LENGTH (args:bvl_v list))`;
                  `args:bvl_v list`; `exp:bvl_exp`; `xs:bvl_v list`; `max_app:num`]
          evaluate_mk_cl_call) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[bvl_evaluate_def; LENGTH_APPEND; LENGTH] THEN
      REWRITE_TAC[ARITH_RULE `a < (a + SUC 0) + b`; GSYM APPEND_ASSOC; APPEND] THEN
      SIMP_TAC[EL_LENGTH_APPEND; NULL; HD];
      MP_TAC (ISPECL [`0`; `APPEND (APPEND args [cl:bvl_v]) env`; `LENGTH (args:bvl_v list)`;
                      `s:(C,FFI)bvl_state`] bvl_evaluate_genlist_vars) THEN
      REWRITE_TAC[ADD_CLAUSES; LENGTH_APPEND; DROP_0; ETA_AX; LENGTH] THEN
      REWRITE_TAC[GSYM APPEND_ASSOC; TAKE_LENGTH_APPEND] THEN
      DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;
(* HOL4 line 2335 [local] *)
let cl_rel_get_loc = prove
 (`!max_app f1 refs code env fvs func tag p n ys.
     cl_rel max_app f1 refs code (env,fvs) func
       (bvl_Block tag (CONS (bvl_CodePtr p) (CONS n ys)))
     ==> num_stubs max_app <= p /\ get_loc func = SOME (p - num_stubs max_app)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cl_rel_cases; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC (CAKE_SIMP_RULE[]) THEN
  REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o check (is_conj o concl))) THEN RVEQ_TAC THEN
  REWRITE_TAC[get_loc_def; option_INJ; MULT_CLAUSES; ADD_CLAUSES] THEN
  TRY (CONJ_TAC THEN ARITH_TAC) THEN
  SUBGOAL_THEN `?n0 e0 p0. EL k (exps_ps:((num#clos_exp)#num)list) = ((n0,e0),p0)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  UNDISCH_TAC `bvl_Block tag (CONS (bvl_CodePtr p) (CONS n ys)) =
      EL k (MAP (\((n,e),p). bvl_Block closure_tag
            [bvl_CodePtr p; bvl_Number (&(n - 1)); bvl_RefPtr T r])
      (exps_ps:((num#clos_exp)#num)list))` THEN
  ASM_SIMP_TAC[EL_MAP] THEN CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[injectivity "bvl_v"; CONS_11] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC (ISPECL [`k:num`; `exps_ps:((num#clos_exp)#num)list`; `n0:num`; `e0:clos_exp`;
                  `p0:num`; `loc:num`; `max_app:num`] p_genlist) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN DISCH_THEN SUBST1_TAC THEN ARITH_TAC]);;

(* HOL4 line 2357 (HOL4 types num_params and num_args by a type variable; *)
(* they are num here, as in closSem's check_loc) *)
let check_loc'_def = cake_def
  `(check_loc' (NONE:A option) (loc:A option) (num_params:num) (num_args:num) (so_far:num) <=>
      T) /\
   (check_loc' (SOME p) loc num_params num_args so_far <=>
      num_params = num_args /\ so_far = 0 /\ SOME p = loc)`;;

(* HOL4 line 2363 (HOL4 a ++ b ++ c is left-associative) *)
let dest_closure'_def = cake_def
  `dest_closure' loc_opt f (args:clos_v list) =
     match f with
       clos_Closure loc arg_env clo_env num_args exp ->
         if check_loc' loc_opt loc num_args (LENGTH args) (LENGTH arg_env) /\
            LENGTH arg_env < num_args then
           if ~(LENGTH args + LENGTH arg_env < num_args) then
             SOME (Full_app exp
                     (APPEND (APPEND (REVERSE (TAKE (num_args - LENGTH arg_env)
                                                    (REVERSE args)))
                                     arg_env) clo_env)
                     (REVERSE (DROP (num_args - LENGTH arg_env) (REVERSE args))))
           else
             SOME (Partial_app (clos_Closure loc (APPEND args arg_env) clo_env
                                             num_args exp))
         else
           NONE
     | clos_Recclosure loc arg_env clo_env fns i ->
         let (num_args,exp) = EL i fns in
           if LENGTH fns <= i \/
              ~check_loc' loc_opt (OPTION_MAP ((+) (2 * i)) loc) num_args
                          (LENGTH args) (LENGTH arg_env) \/
              ~(LENGTH arg_env < num_args)
           then NONE
           else
             let rs = list_of_seq (clos_Recclosure loc [] clo_env fns) (LENGTH fns) in
               if ~(LENGTH args + LENGTH arg_env < num_args) then
                 SOME (Full_app exp
                         (APPEND (APPEND (APPEND (REVERSE (TAKE (num_args - LENGTH arg_env)
                                                                (REVERSE args)))
                                                 arg_env) rs) clo_env)
                         (REVERSE (DROP (num_args - LENGTH arg_env) (REVERSE args))))
               else
                 SOME (Partial_app (clos_Recclosure loc (APPEND args arg_env) clo_env
                                                    fns i))
     | _ -> NONE`;;

let C2BP1AUX_check_loc_IMP = prove
 (`!max_app (l:num option) loc np na sf.
     check_loc max_app l loc np na sf ==> check_loc' l loc np na sf`,
  REPEAT GEN_TAC THEN CASES_ON `l:num option` THEN REWRITE_TAC[check_loc_def; check_loc'_def] THEN
  MESON_TAC[]);;

(* HOL4 line 2393 [local] *)
let dest_cl_imp_dest_cl' = prove
 (`!max_app l f a x. dest_closure max_app l f a = SOME x ==> dest_closure' l f a = SOME x`,
  REPEAT GEN_TAC THEN CASES_ON `f:clos_v` THEN
  REWRITE_TAC[dest_closure_def; dest_closure'_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT] THEN TRY PAIRARG_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  ASM_MESON_TAC[C2BP1AUX_check_loc_IMP]);;

let C2BP1AUX_TAKE_APPEND_LENGTH = prove
 (`!n (l1:A list) l2. LENGTH l1 = n ==> TAKE n (APPEND l1 l2) = l1`,
  MESON_TAC[TAKE_LENGTH_APPEND]);;

(* HOL4 line 2405 [local] *)
let cl_rel_run_lemma1 = prove
 (`!num_args args' stuff (t1:(C,FFI)bvl_state).
     num_args <= LENGTH args'
     ==> bvl_evaluate (list_of_seq bvl_Var num_args,
                       APPEND (DROP (LENGTH args' - num_args) args') stuff,t1) =
         (Rval (DROP (LENGTH args' - num_args) args'),t1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (DROP (LENGTH (args':bvl_v list) - num_args) args') = num_args`
    ASSUME_TAC THENL [REWRITE_TAC[LENGTH_DROP] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC (ISPECL [`0`; `APPEND (DROP (LENGTH (args':bvl_v list) - num_args) args') stuff`;
                  `num_args:num`; `t1:(C,FFI)bvl_state`] bvl_evaluate_genlist_vars) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; LENGTH_APPEND; LE_ADD; DROP_0; ETA_AX] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[C2BP1AUX_TAKE_APPEND_LENGTH]);;

(* HOL4 line 2420: val cl_rel_run_lemma2 = Q.prove (...) |> Q.INST         *)
(* [stuff |-> []] |> SIMP_RULE (srw_ss()) [] (its resulting statement)       *)
let cl_rel_run_lemma2 = prove
 (`!num_args args' f (t1:(C,FFI)bvl_state).
     num_args <= LENGTH args'
     ==> bvl_evaluate (list_of_seq bvl_Var (num_args + 1),
                       APPEND (DROP (LENGTH args' - num_args) args') [f],t1) =
         (Rval (APPEND (DROP (LENGTH args' - num_args) args') [f]),t1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (APPEND (DROP (LENGTH (args':bvl_v list) - num_args) args') [f]) =
                num_args + 1` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_DROP; LENGTH_APPEND; LENGTH] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC (ISPECL [`0`; `APPEND (DROP (LENGTH (args':bvl_v list) - num_args) args') [f]`;
                  `num_args + 1`; `t1:(C,FFI)bvl_state`] bvl_evaluate_genlist_vars) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; LE_REFL; DROP_0; ETA_AX] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC[TAKE_LENGTH_ID]);;

(* HOL4 line 2433 [local] *)
let cl_rel_run_lemma3 = prove
 (`!(R:A->B->bool) args args' n.
     ALL2 R args args'
     ==> ALL2 R (DROP (LENGTH args' - n) args) (DROP (LENGTH args' - n) args')`,
  REWRITE_TAC[LIST_REL_EL_EQN] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_DROP] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n' + (LENGTH (args':B list) - n) < LENGTH (args:A list) /\
                n' + (LENGTH (args':B list) - n) < LENGTH (args':B list)` STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC (REWRITE_RULE[LENGTH_DROP]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_DROP]);;

let C2BP1AUX_free_let_Block = prove
 (`!ys zs x env (s:(C,FFI)bvl_state) n y z.
     bvl_evaluate ([x],env,s) = (Rval [bvl_Block n (CONS y (CONS z (APPEND ys zs)))],s)
     ==> bvl_evaluate (free_let x (LENGTH ys),env,s) = (Rval ys,s)`,
  MATCH_MP_TAC SNOC_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[free_let_def; LENGTH; list_of_seq; bvl_evaluate_def]; ALL_TAC] THEN
  X_GEN_TAC `ys:bvl_v list` THEN DISCH_TAC THEN X_GEN_TAC `h:bvl_v` THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[free_let_def; LENGTH_SNOC; GENLIST; bvl_evaluate_SNOC] THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`CONS (h:bvl_v) zs`; `x:bvl_exp`; `env:bvl_v list`;
                                 `s:(C,FFI)bvl_state`; `n:num`; `y:bvl_v`; `z:bvl_v`]) THEN
  RULE_ASSUM_TAC (REWRITE_RULE[SNOC_APPEND; GSYM APPEND_ASSOC; APPEND]) THEN
  ASM_REWRITE_TAC[free_let_def] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[bvl_evaluate_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[REVERSE; APPEND; C2BP1AUX_do_app_ElemAt; LENGTH; LENGTH_APPEND] THEN
  REWRITE_TAC[ARITH_RULE `a + 2 < SUC (SUC (a + SUC b))`] THEN
  REWRITE_TAC[ARITH_RULE `a + 2 = SUC (SUC a)`; EL; TL] THEN
  SIMP_TAC[EL_LENGTH_APPEND; NULL; HD] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[SNOC_APPEND]);;

(* HOL4 line 2444: val bEval_free_let_Block = Q.prove (...) |> Q.SPECL     *)
(* [ys, []] |> SIMP_RULE std_ss [APPEND_NIL] (its resulting statement)       *)
let bEval_free_let_Block = prove
 (`!x env (s:(C,FFI)bvl_state) n y z ys.
     bvl_evaluate ([x],env,s) = (Rval [bvl_Block n (CONS y (CONS z ys))],s)
     ==> bvl_evaluate (free_let x (LENGTH ys),env,s) = (Rval ys,s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C2BP1AUX_free_let_Block THEN
  MAP_EVERY EXISTS_TAC [`[]:bvl_v list`; `n:num`; `y:bvl_v`; `z:bvl_v`] THEN
  ASM_REWRITE_TAC[APPEND_NIL]);;

(* HOL4 line 2458: val cl_rel_run_tac (an ML tactic) *)

let C2BP1AUX_do_app_ElemAt_Ref = prove
 (CASE_TERM `!n b ptr (s:(C,FFI)bvl_state).
     bvl_do_app (BlockOp (ElemAt n)) [bvl_RefPtr b ptr] s =
     match FLOOKUP (bvl_state_refs s) ptr with
       SOME (bvl_ValueArray xs) ->
         (if n < LENGTH xs then Rval (EL n xs,s) else Rerr (Rabort Rtype_error))
     | _ -> Rerr (Rabort Rtype_error)`,
  REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 2482 [local] (HOL4 mk_elem_at (Var 0) j is                    *)
(* bvl_Op (BlockOp (ElemAt j)) [bvl_Var 0]) *)
let genlist_el = prove
 (`!skip (st:(C,FFI)bvl_state) r xs args p n env ys.
     FLOOKUP (bvl_state_refs st) r = SOME (bvl_ValueArray (APPEND ys xs)) /\
     skip = LENGTH ys
     ==> bvl_evaluate
           (list_of_seq (\i. bvl_Op (BlockOp (ElemAt (i + skip))) [bvl_Var 0]) (LENGTH xs),
            CONS (bvl_RefPtr T r)
              (APPEND args
                 (CONS (bvl_Block closure_tag [bvl_CodePtr p; bvl_Number (&n); bvl_RefPtr T r])
                    env)),
            st) =
         (Rval xs,st)`,
  SUBGOAL_THEN
   `!xs skip (st:(C,FFI)bvl_state) r args p n env ys.
     FLOOKUP (bvl_state_refs st) r = SOME (bvl_ValueArray (APPEND ys xs)) /\
     skip = LENGTH ys
     ==> bvl_evaluate
           (list_of_seq (\i. bvl_Op (BlockOp (ElemAt (i + skip))) [bvl_Var 0]) (LENGTH xs),
            CONS (bvl_RefPtr T r)
              (APPEND args
                 (CONS (bvl_Block closure_tag [bvl_CodePtr p; bvl_Number (&n); bvl_RefPtr T r])
                    env)),
            st) =
         (Rval xs,st)` (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; list_of_seq; bvl_evaluate_def]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[LENGTH; GENLIST_CONS] THEN ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN
  SUBGOAL_THEN
   `(\i. bvl_Op (BlockOp (ElemAt (i + LENGTH (ys:bvl_v list)))) [bvl_Var 0]) o SUC =
    (\i. bvl_Op (BlockOp (ElemAt (i + LENGTH (APPEND ys [h:bvl_v])))) [bvl_Var 0])`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LENGTH_APPEND; LENGTH; ADD_CLAUSES]; ALL_TAC] THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`LENGTH (APPEND ys [h:bvl_v])`; `st:(C,FFI)bvl_state`; `r:num`;
                                 `args:bvl_v list`; `p:num`; `n:num`; `env:bvl_v list`;
                                 `APPEND ys [h:bvl_v]`]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `EL (LENGTH ys) (APPEND ys (CONS (h:bvl_v) t)) = h` ASSUME_TAC THENL
   [SIMP_TAC[EL_LENGTH_APPEND; NULL; HD]; ALL_TAC] THEN
  C2BP1AUX_EVAL_TAC (C2BP1AUX_do_app_ElemAt_Ref :: C2BP1AUX_eval_lemmas) THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[HD]);;

(* HOL4 line 2504 [local] (HOL4 a ++ b ++ c ++ d ++ e :: env is             *)
(* left-associative, :: binding tighter) *)
let evaluate_code_for_recc_case = prove
 (`!(st:(C,FFI)bvl_state) r xs args c p n env.
     FLOOKUP (bvl_state_refs st) r = SOME (bvl_ValueArray xs)
     ==> bvl_evaluate
           ([SND (code_for_recc_case (LENGTH xs) (LENGTH args) c)],
            APPEND args
              (CONS (bvl_Block closure_tag [bvl_CodePtr p; bvl_Number (&n); bvl_RefPtr T r]) env),
            st) =
         bvl_evaluate
           ([c],
            APPEND (APPEND (APPEND (APPEND args xs) [bvl_RefPtr T r]) args)
              (CONS (bvl_Block closure_tag [bvl_CodePtr p; bvl_Number (&n); bvl_RefPtr T r]) env),
            st)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`0`; `st:(C,FFI)bvl_state`; `r:num`; `xs:bvl_v list`; `args:bvl_v list`;
                  `p:num`; `n:num`; `env:bvl_v list`; `[]:bvl_v list`] genlist_el) THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; ADD_CLAUSES; ETA_AX] THEN DISCH_TAC THEN
  SUBGOAL_THEN `EL (LENGTH args) (APPEND args (CONS (bvl_Block closure_tag
                  [bvl_CodePtr p; bvl_Number (&n); bvl_RefPtr T r]) env)) =
                bvl_Block closure_tag [bvl_CodePtr p; bvl_Number (&n); bvl_RefPtr T r]`
    ASSUME_TAC THENL [SIMP_TAC[EL_LENGTH_APPEND; NULL; HD]; ALL_TAC] THEN
  REWRITE_TAC[code_for_recc_case_def] THEN
  C2BP1AUX_EVAL_LHS_TAC (TAKE_LENGTH_APPEND :: C2BP1AUX_eval_lemmas) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

let C2BP1AUX_cl_rel_run_env = prove
 (`!max_app f1 refs code args args' env fvs stuff k.
     ALL2 (clos_to_bvlProof_v_rel max_app f1 refs code) env fvs /\
     ALL2 (clos_to_bvlProof_v_rel max_app f1 refs code) args args' /\ k <= LENGTH args
     ==> clos_to_bvlProof_env_rel max_app f1 refs code
           (APPEND (REVERSE (TAKE k (REVERSE args))) env)
           (APPEND (DROP (LENGTH args' - k) args') (APPEND fvs stuff))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (args:clos_v list) = LENGTH (args':bvl_v list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_REL_LENGTH]; ALL_TAC] THEN
  ASM_SIMP_TAC[revtakerev] THEN
  MATCH_MP_TAC clos_to_bvlProof_env_rel_APPEND THEN CONJ_TAC THENL
   [UNDISCH_TAC `LENGTH (args:clos_v list) = LENGTH (args':bvl_v list)` THEN
    DISCH_THEN (SUBST1_TAC) THEN MATCH_MP_TAC cl_rel_run_lemma3 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC list_rel_IMP_env_rel THEN ASM_REWRITE_TAC[]]);;

let C2BP1AUX_eval_closure_code = prove
 (`!(D:bvl_v list) tag y z fvs c k (t:(C,FFI)bvl_state).
     LENGTH D = k
     ==> bvl_evaluate ([bvl_Let (APPEND (list_of_seq bvl_Var k)
                                   (free_let (bvl_Var k) (LENGTH fvs))) c],
                       APPEND D [bvl_Block tag (CONS y (CONS z fvs))],t) =
         bvl_evaluate ([c],APPEND (APPEND D fvs) (APPEND D [bvl_Block tag (CONS y (CONS z fvs))]),t)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `f = bvl_Block tag (CONS y (CONS z fvs))` THEN
  SUBGOAL_THEN `bvl_evaluate (list_of_seq bvl_Var k,APPEND D [f:bvl_v],t:(C,FFI)bvl_state) =
                (Rval D,t)` ASSUME_TAC THENL
   [MP_TAC (ISPECL [`0`; `APPEND D [f:bvl_v]`; `k:num`; `t:(C,FFI)bvl_state`]
            bvl_evaluate_genlist_vars) THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `k:num`)) THEN
    REWRITE_TAC[ADD_CLAUSES; LENGTH_APPEND; LE_ADD; DROP_0; ETA_AX; TAKE_LENGTH_APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN `bvl_evaluate (free_let (bvl_Var k) (LENGTH (fvs:bvl_v list)),APPEND D [f:bvl_v],
                              t:(C,FFI)bvl_state) = (Rval fvs,t)` ASSUME_TAC THENL
   [MATCH_MP_TAC bEval_free_let_Block THEN
    MAP_EVERY EXISTS_TAC [`tag:num`; `y:bvl_v`; `z:bvl_v`] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `f:bvl_v`)) THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `k:num`)) THEN
    REWRITE_TAC[bvl_evaluate_def; LENGTH_APPEND; LENGTH] THEN
    REWRITE_TAC[ARITH_RULE `a < a + SUC 0`; el_append2];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[bvl_evaluate_def; bvl_evaluate_APPEND] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND_ASSOC]);;

let C2BP1AUX_eval_rec_closure_code = prove
 (`!(D:bvl_v list) tag y z fvs c k (t:(C,FFI)bvl_state).
     LENGTH D = k
     ==> bvl_evaluate ([bvl_Let (APPEND (list_of_seq bvl_Var (k + 1))
                                   (free_let (bvl_Var k) (LENGTH fvs))) c],
                       APPEND D [bvl_Block tag (CONS y (CONS z fvs))],t) =
         bvl_evaluate ([c],APPEND (APPEND (APPEND D [bvl_Block tag (CONS y (CONS z fvs))]) fvs)
                             (APPEND D [bvl_Block tag (CONS y (CONS z fvs))]),t)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `f = bvl_Block tag (CONS y (CONS z fvs))` THEN
  SUBGOAL_THEN `bvl_evaluate (list_of_seq bvl_Var (k + 1),APPEND D [f:bvl_v],t:(C,FFI)bvl_state) =
                (Rval (APPEND D [f]),t)` ASSUME_TAC THENL
   [MP_TAC (ISPECL [`0`; `APPEND D [f:bvl_v]`; `k + 1`; `t:(C,FFI)bvl_state`]
            bvl_evaluate_genlist_vars) THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `k:num`)) THEN
    REWRITE_TAC[ADD_CLAUSES; LENGTH_APPEND; LENGTH; LE_REFL; DROP_0; ETA_AX] THEN
    REWRITE_TAC[ARITH_RULE `a + 1 <= SUC a`] THEN
    SUBGOAL_THEN `LENGTH (D:bvl_v list) + 1 = LENGTH (APPEND D [f:bvl_v])`
      (fun th -> REWRITE_TAC[th; TAKE_LENGTH_ID]) THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `bvl_evaluate (free_let (bvl_Var k) (LENGTH (fvs:bvl_v list)),APPEND D [f:bvl_v],
                              t:(C,FFI)bvl_state) = (Rval fvs,t)` ASSUME_TAC THENL
   [MATCH_MP_TAC bEval_free_let_Block THEN
    MAP_EVERY EXISTS_TAC [`tag:num`; `y:bvl_v`; `z:bvl_v`] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `f:bvl_v`)) THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `k:num`)) THEN
    REWRITE_TAC[bvl_evaluate_def; LENGTH_APPEND; LENGTH] THEN
    REWRITE_TAC[ARITH_RULE `a < a + SUC 0`; el_append2];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[bvl_evaluate_def; bvl_evaluate_APPEND] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[APPEND_ASSOC]);;

let C2BP1AUX_cl_rel_run_env_gen = prove
 (`!max_app f1 refs code args args' env1 env2 k.
     clos_to_bvlProof_env_rel max_app f1 refs code env1 env2 /\
     ALL2 (clos_to_bvlProof_v_rel max_app f1 refs code) args args' /\ k <= LENGTH args
     ==> clos_to_bvlProof_env_rel max_app f1 refs code
           (APPEND (REVERSE (TAKE k (REVERSE args))) env1)
           (APPEND (DROP (LENGTH args' - k) args') env2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (args:clos_v list) = LENGTH (args':bvl_v list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_REL_LENGTH]; ALL_TAC] THEN
  ASM_SIMP_TAC[revtakerev] THEN
  MATCH_MP_TAC clos_to_bvlProof_env_rel_APPEND THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `LENGTH (args:clos_v list) = LENGTH (args':bvl_v list)` THEN
  DISCH_THEN (SUBST1_TAC) THEN MATCH_MP_TAC cl_rel_run_lemma3 THEN ASM_REWRITE_TAC[]);;

let C2BP1AUX_rec_closures_v_rel = prove
 (`!max_app f1 refs code env ys exps_ps loc r j.
     ALL2 (clos_to_bvlProof_v_rel max_app f1 refs code) env ys /\
     list_of_seq (\n. loc + num_stubs max_app + 2 * n) (LENGTH exps_ps) = MAP SND exps_ps /\
     ~(r IN FRANGE f1) /\
     FLOOKUP refs r =
       SOME (bvl_ValueArray
               (APPEND (MAP (\((n,e),p). bvl_Block closure_tag
                               [bvl_CodePtr p; bvl_Number (&(n - 1)); bvl_RefPtr T r])
                            exps_ps) ys)) /\
     1 < LENGTH exps_ps /\
     every_Fn_SOME (MAP SND (MAP FST exps_ps)) /\
     every_Fn_vs_SOME (MAP SND (MAP FST exps_ps)) /\
     closure_code_installed max_app code exps_ps env /\
     j < LENGTH exps_ps
     ==> clos_to_bvlProof_v_rel max_app f1 refs code
           (clos_Recclosure (SOME loc) [] env (MAP FST exps_ps) j)
           (EL j (MAP (\((n,e),p). bvl_Block closure_tag
                         [bvl_CodePtr p; bvl_Number (&(n - 1)); bvl_RefPtr T r]) exps_ps))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?nj ej pj. EL j (exps_ps:((num#clos_exp)#num)list) = ((nj,ej),pj)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MAP] THEN CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  MATCH_MP_TAC (el 5 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
  MAP_EVERY EXISTS_TAC [`env:clos_v list`; `ys:bvl_v list`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `bvl_Block closure_tag [bvl_CodePtr pj; bvl_Number (&(nj - 1)); bvl_RefPtr T r] =
    EL j (MAP (\((n,e),p). bvl_Block closure_tag
                [bvl_CodePtr p; bvl_Number (&(n - 1)); bvl_RefPtr T r])
              (exps_ps:((num#clos_exp)#num)list))` SUBST1_TAC THENL
   [ASM_SIMP_TAC[EL_MAP] THEN CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC (el 2 (CONJUNCTS cl_rel_rules)) THEN
  MAP_EVERY EXISTS_TAC [`exps_ps:((num#clos_exp)#num)list`; `MAP SND (exps_ps:((num#clos_exp)#num)list)`] THEN
  ASM_REWRITE_TAC[LENGTH_MAP] THEN ASM_MESON_TAC[]);;

(* HOL4 line 2527 [local] (HOL4 t1 with <| refs := refs; code := code |>   *)
(* is bvl_state_refs_fupd (K refs) (bvl_state_code_fupd (K code) t1)) *)
let cl_rel_run = prove
 (`!loc f1 refs code args args' env env' ptr body new_env func func' rest n fvs max_app.
     func' = bvl_Block closure_tag (CONS (bvl_CodePtr ptr) (CONS (bvl_Number (&n)) env')) /\
     dest_closure' loc func args = SOME (Full_app body new_env rest) /\
     clos_to_bvlProof_v_rel max_app f1 refs code func func' /\
     cl_rel max_app (FRANGE f1) refs code (env,fvs) func func' /\
     ALL2 (clos_to_bvlProof_v_rel max_app f1 refs code) env fvs /\
     ALL2 (clos_to_bvlProof_v_rel max_app f1 refs code) args args'
     ==> ?body' aux1 aux2 new_env' exp'.
           lookup ptr code = SOME (n + 2,exp') /\
           clos_to_bvl_compile_exps max_app [body] aux1 = ([body'],aux2) /\
           clos_to_bvlProof_code_installed aux2 code /\
           clos_to_bvlProof_env_rel max_app f1 refs code new_env new_env' /\
           !(t1:(C,FFI)bvl_state).
             bvl_evaluate ([exp'],APPEND (DROP (LENGTH args' - (n + 1)) args') [func'],
                           bvl_state_refs_fupd (K refs) (bvl_state_code_fupd (K code) t1)) =
             bvl_evaluate ([body'],new_env',
                           bvl_state_refs_fupd (K refs) (bvl_state_code_fupd (K code) t1))`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (args:clos_v list) = LENGTH (args':bvl_v list) /\
                LENGTH (env:clos_v list) = LENGTH (fvs:bvl_v list)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_REL_LENGTH]; ALL_TAC] THEN
  FIRST_X_ASSUM (MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "cl_rel" with _ -> false)) THEN
  REWRITE_TAC[cl_rel_cases; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC) THENL
   [(RULE_ASSUM_TAC (CAKE_SIMP_RULE[INT_OF_NUM_EQ]) THEN
    REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o check (is_conj o concl))) THEN RVEQ_TAC) THEN
    (FIRST_X_ASSUM (MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "dest_closure'" with _ -> false)) THEN
    REWRITE_TAC[dest_closure'_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[LENGTH; ADD_CLAUSES; SUB_0; APPEND_NIL] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    COND_CASES_TAC THEN SIMP[] THEN STRIP_TAC THEN RVEQ_TAC) THEN
    (SUBGOAL_THEN `num_args - 1 + 1 = num_args /\
                  LENGTH (DROP (LENGTH (args':bvl_v list) - num_args) args') = num_args /\
                  num_args <= LENGTH (args:clos_v list)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_DROP] THEN C2BP1AUX_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`c:bvl_exp`; `aux:(num#num#bvl_exp)list`; `aux1:(num#num#bvl_exp)list`;
      `APPEND (APPEND (DROP (LENGTH (args':bvl_v list) - num_args) args') env')
         (APPEND (DROP (LENGTH args' - num_args) args')
            [bvl_Block closure_tag (CONS (bvl_CodePtr (p + num_stubs max_app))
               (CONS (bvl_Number (&(num_args - 1))) env'))])`] THEN
    CONJ_TAC THENL [C2BP1AUX_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM APPEND_ASSOC] THEN MATCH_MP_TAC C2BP1AUX_cl_rel_run_env THEN
      ASM_REWRITE_TAC[];
      GEN_TAC THEN MATCH_MP_TAC C2BP1AUX_eval_closure_code THEN ASM_REWRITE_TAC[]]);
    (RULE_ASSUM_TAC (CAKE_SIMP_RULE[INT_OF_NUM_EQ]) THEN
    REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o check (is_conj o concl))) THEN RVEQ_TAC) THEN
    (FIRST_X_ASSUM (MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "dest_closure'" with _ -> false)) THEN
    REWRITE_TAC[dest_closure'_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[EL; HD; LENGTH; ADD_CLAUSES; SUB_0; APPEND_NIL; LET_DEF; LET_END_DEF] THEN
    CASE_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    COND_CASES_TAC THEN SIMP[] THEN STRIP_TAC THEN RVEQ_TAC) THEN
    (REWRITE_TAC[LISTAUX_list_of_seq_1; GSYM APPEND_ASSOC; APPEND] THEN
    SUBGOAL_THEN `num_args - 1 + 1 = num_args /\
                  LENGTH (DROP (LENGTH (args':bvl_v list) - num_args) args') = num_args /\
                  num_args <= LENGTH (args:clos_v list)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_DROP] THEN C2BP1AUX_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`c:bvl_exp`; `aux:(num#num#bvl_exp)list`; `aux1:(num#num#bvl_exp)list`;
      `APPEND (APPEND (APPEND (DROP (LENGTH (args':bvl_v list) - num_args) args')
           [bvl_Block closure_tag (CONS (bvl_CodePtr (p + num_stubs max_app))
               (CONS (bvl_Number (&(num_args - 1))) env'))]) env')
         (APPEND (DROP (LENGTH args' - num_args) args')
            [bvl_Block closure_tag (CONS (bvl_CodePtr (p + num_stubs max_app))
               (CONS (bvl_Number (&(num_args - 1))) env'))])`] THEN
    CONJ_TAC THENL [C2BP1AUX_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN MATCH_MP_TAC C2BP1AUX_cl_rel_run_env_gen THEN
      ASM_REWRITE_TAC[clos_to_bvlProof_env_rel_def] THEN
      MATCH_MP_TAC list_rel_IMP_env_rel THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN MATCH_MP_TAC C2BP1AUX_eval_rec_closure_code THEN ASM_REWRITE_TAC[]]);
    ((SUBGOAL_THEN `?nk ek pk. EL k (exps_ps:((num#clos_exp)#num)list) = ((nk,ek),pk)`
      STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
    RULE_ASSUM_TAC (REWRITE_RULE[LENGTH_MAP]) THEN
    MP_TAC (ISPECL [`max_app:num`; `code:(num#bvl_exp)spt`; `exps_ps:((num#clos_exp)#num)list`;
                    `env'':clos_v list`; `k:num`; `nk:num`; `ek:clos_exp`; `pk:num`]
            C2BP1AUX_closure_code_installed_EL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o check (fun th -> try (fst(dest_const(fst(strip_comb(lhs(concl th))))) = "EL" &&
                                                  is_comb (rhs(concl th)) &&
                                                  fst(dest_const(fst(strip_comb(rhs(concl th))))) = "bvl_Block")
                                             with _ -> false)) THEN
    ASM_SIMP_TAC[EL_MAP] THEN CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[injectivity "bvl_v"; CONS_11; INT_OF_NUM_EQ] THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM o check (fun th -> not (is_eq (concl th) && lhs(concl th) = rhs(concl th)))))) THEN
    (FIRST_X_ASSUM (MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "dest_closure'" with _ -> false)) THEN
    REWRITE_TAC[dest_closure'_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[EL_MAP; LENGTH_MAP] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[LENGTH; ADD_CLAUSES; SUB_0; APPEND_NIL; LET_DEF; LET_END_DEF; NOT_LE] THEN
    ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    COND_CASES_TAC THEN SIMP[] THEN STRIP_TAC THEN
    REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
        (rhs(concl th) = `body:clos_exp` || rhs(concl th) = `new_env:clos_v list` ||
         rhs(concl th) = `rest:clos_v list`))))) THEN
    (SUBGOAL_THEN `nk - 1 + 1 = nk /\
                  LENGTH (DROP (LENGTH (args':bvl_v list) - nk) args') = nk /\
                  nk <= LENGTH (args:clos_v list)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_DROP] THEN C2BP1AUX_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`c:bvl_exp`; `aux:(num#num#bvl_exp)list`; `aux1:(num#num#bvl_exp)list`;
      `APPEND (APPEND (APPEND (APPEND (DROP (LENGTH (args':bvl_v list) - nk) args')
           (APPEND (MAP (\((n,e),p). bvl_Block closure_tag
                   [bvl_CodePtr p; bvl_Number (&(n - 1)); bvl_RefPtr T r])
                   (exps_ps:((num#clos_exp)#num)list)) ys)) [bvl_RefPtr T r])
             (DROP (LENGTH args' - nk) args'))
         [bvl_Block closure_tag [bvl_CodePtr pk; bvl_Number (&(nk - 1)); bvl_RefPtr T r]]`] THEN
    CONJ_TAC THENL [C2BP1AUX_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC)) THENL
    [(REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN MATCH_MP_TAC C2BP1AUX_cl_rel_run_env_gen THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC clos_to_bvlProof_env_rel_APPEND THEN CONJ_TAC THENL
     [REWRITE_TAC[LIST_REL_EL_EQN; LENGTH_LIST_OF_SEQ; LENGTH_MAP] THEN
      SIMP_TAC[EL_LIST_OF_SEQ] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC C2BP1AUX_rec_closures_v_rel THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC list_rel_IMP_env_rel THEN ASM_REWRITE_TAC[]]);
     (GEN_TAC THEN
    MP_TAC (ISPECL [`bvl_state_refs_fupd (K refs) (bvl_state_code_fupd (K code) (t1:(C,FFI)bvl_state))`;
                    `r:num`;
                    `APPEND (MAP (\((n,e),p). bvl_Block closure_tag
                       [bvl_CodePtr p; bvl_Number (&(n - 1)); bvl_RefPtr T r])
                       (exps_ps:((num#clos_exp)#num)list)) ys`;
                    `DROP (LENGTH (args':bvl_v list) - nk) args'`; `c:bvl_exp`; `pk:num`; `nk - 1`;
                    `[]:bvl_v list`] evaluate_code_for_recc_case) THEN
    SIMP[LENGTH_APPEND; LENGTH_MAP] THEN REWRITE_TAC[ADD_SYM] THEN
    DISCH_THEN ACCEPT_TAC)]]);;

(* HOL4 line 2618 [local] (the inner bound fvs, a bvl value list, is fvs1) *)
let cl_rel_dest = prove
 (`!f refs code cl cl' fvs fvs' max_app.
     cl_rel max_app f refs code (fvs,fvs') cl cl'
     ==> get_old_args cl = SOME [] /\
         ?l num_args fvs1.
           cl' = bvl_Block closure_tag
                   (CONS (bvl_CodePtr l) (CONS (bvl_Number (&num_args)) fvs1))`,
  REPEAT GEN_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o MATCH_MP C2BP1AUX_cl_rel_IMP) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let C2BP1AUX_TAKE_DROP_REV = prove
 (`!(args:A list) arg_env (a1:A list) num_args.
     LENGTH arg_env + LENGTH a1 <= num_args
     ==> REVERSE (TAKE (num_args - LENGTH a1) (REVERSE (APPEND args arg_env))) =
         APPEND (REVERSE (TAKE (num_args - (LENGTH arg_env + LENGTH a1)) (REVERSE args)))
                arg_env /\
         REVERSE (DROP (num_args - LENGTH a1) (REVERSE (APPEND args arg_env))) =
         REVERSE (DROP (num_args - (LENGTH arg_env + LENGTH a1)) (REVERSE args))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REVERSE_APPEND] THEN
  SUBGOAL_THEN `LENGTH (REVERSE (arg_env:A list)) <= num_args - LENGTH (a1:A list)`
    ASSUME_TAC THENL [REWRITE_TAC[LENGTH_REVERSE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[TAKE_APPEND2; DROP_APPEND2; REVERSE_APPEND; REVERSE_REVERSE; LENGTH_REVERSE] THEN
  REWRITE_TAC[ARITH_RULE `(n - a) - b = n - (b + a)`]);;

(* HOL4 line 2632 [local] *)
let dest_closure_full_of_part = prove
 (`!max_app loc func args body newenv rest arg_env cl num_args.
     dest_closure max_app loc func args = SOME (Full_app body newenv rest) /\
     ~(LENGTH arg_env = 0) /\
     add_args cl arg_env = SOME func /\
     get_num_args cl = SOME num_args /\
     LENGTH arg_env < num_args
     ==> dest_closure' loc cl (APPEND args arg_env) = SOME (Full_app body newenv rest)`,
  REPEAT GEN_TAC THEN CASES_ON `cl:clos_v` THEN
  REWRITE_TAC[add_args_def; get_num_args_def; option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[dest_closure_def]) THEN
  RULE_ASSUM_TAC (CASE_REWRITE_RULE[]) THEN
  REWRITE_TAC[dest_closure'_def] THEN CASE_REWRITE_TAC[] THENL
   [RULE_ASSUM_TAC (REWRITE_RULE[LENGTH_EQ_NIL]) THEN
    CASES_ON `loc:num option` THEN
    RULE_ASSUM_TAC (REWRITE_RULE[check_loc_def; LENGTH_APPEND; ADD_EQ_0; LENGTH_EQ_NIL; APPEND_EQ_NIL]) THEN
    REWRITE_TAC[check_loc'_def; LENGTH_APPEND] THEN
    FIRST_X_ASSUM (MP_TAC o check (is_eq o concl)) THEN
    ASM_REWRITE_TAC[option_DISTINCT] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    COND_CASES_TAC THEN SIMP[] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
    SUBGOAL_THEN `LENGTH (a1:clos_v list) < num_args /\
                  ~((LENGTH (args:clos_v list) + LENGTH (arg_env:clos_v list)) + LENGTH a1 <
                    num_args) /\
                  LENGTH arg_env + LENGTH a1 <= num_args` STRIP_ASSUME_TAC THENL
     [C2BP1AUX_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[C2BP1AUX_TAKE_DROP_REV; APPEND_ASSOC];
    MP_TAC (ISPEC `EL a4 (a3:(num#clos_exp)list)` PAIR_SURJECTIVE) THEN
    DISCH_THEN (X_CHOOSE_THEN `na:num` (X_CHOOSE_THEN `ex:clos_exp`
      (fun th -> RULE_ASSUM_TAC (REWRITE_RULE[th]) THEN REWRITE_TAC[th]))) THEN
    RULE_ASSUM_TAC (CASE_REWRITE_RULE[]) THEN CASE_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC (REWRITE_RULE[LET_DEF; LET_END_DEF; LENGTH_EQ_NIL]) THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    CASES_ON `loc:num option` THEN
    RULE_ASSUM_TAC (REWRITE_RULE[check_loc_def; LENGTH_APPEND; ADD_EQ_0; LENGTH_EQ_NIL;
                                 APPEND_EQ_NIL]) THEN
    REWRITE_TAC[check_loc'_def; LENGTH_APPEND] THEN
    FIRST_X_ASSUM (MP_TAC o check (is_eq o concl)) THEN
    ASM_REWRITE_TAC[option_DISTINCT] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    COND_CASES_TAC THEN SIMP[] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[DE_MORGAN_THM; NOT_LE]) THEN
    REPEAT (FIRST_X_ASSUM (STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
    SUBGOAL_THEN `LENGTH (a1:clos_v list) < na /\
                  ~((LENGTH (args:clos_v list) + LENGTH (arg_env:clos_v list)) + LENGTH a1 < na) /\
                  LENGTH arg_env + LENGTH a1 <= na` STRIP_ASSUME_TAC THENL
     [C2BP1AUX_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[C2BP1AUX_TAKE_DROP_REV; APPEND_ASSOC; NOT_LE]]);;

let C2BP1AUX_v_rel_closure_cases = prove
 (`!max_app f refs code func y loc args body newenv rest.
     dest_closure max_app loc func args = SOME (Full_app body newenv rest) /\
     clos_to_bvlProof_v_rel max_app f refs code func y
     ==> (?env fvs p n ys.
            y = bvl_Block closure_tag (CONS (bvl_CodePtr p) (CONS (bvl_Number n) ys)) /\
            ALL2 (clos_to_bvlProof_v_rel max_app f refs code) env fvs /\
            cl_rel max_app (FRANGE f) refs code (env,fvs) func y) \/
         (?env fvs arg_env ys num_args cl cl'.
            y = bvl_Block partial_app_tag
                  (CONS (bvl_CodePtr (partial_app_fn_location max_app (num_args - 1)
                                        (LENGTH ys - 1)))
                     (CONS (bvl_Number (&((num_args - 1) - LENGTH arg_env))) (CONS cl' ys))) /\
            ALL2 (clos_to_bvlProof_v_rel max_app f refs code) env fvs /\
            ALL2 (clos_to_bvlProof_v_rel max_app f refs code) arg_env ys /\
            ~(arg_env = []) /\
            LENGTH arg_env < num_args /\
            lookup (partial_app_fn_location max_app (num_args - 1) (LENGTH ys - 1)) code =
              SOME ((num_args - LENGTH arg_env) + 1,
                    generate_partial_app_closure_fn (num_args - 1) (LENGTH ys - 1)) /\
            add_args cl arg_env = SOME func /\
            get_num_args cl = SOME num_args /\
            cl_rel max_app (FRANGE f) refs code (env,fvs) cl cl')`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [clos_to_bvlProof_v_rel_cases] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  TRY (FIRST_X_ASSUM (MP_TAC o check (fun th ->
         try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "dest_closure"
         with _ -> false)) THEN
       REWRITE_TAC[dest_closure_def] THEN CASE_REWRITE_TAC[] THEN
       REWRITE_TAC[option_DISTINCT] THEN NO_TAC) THEN
  ASM_MESON_TAC[]);;

let C2BP1AUX_SUBST_VAR s =
  FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th -> let c = concl th in
    is_eq c && is_var (lhs c) && fst(dest_var(lhs c)) = s));;

(* HOL4 line 2668: val v_rel_run = Q.prove (...) (max_app is free in HOL4) *)
let v_rel_run = prove
 (`!f1 refs code args args' env' ptr body newenv func func' rest tag n loc max_app.
     ~(LENGTH args = 0) /\
     func' = bvl_Block tag (CONS (bvl_CodePtr ptr) (CONS (bvl_Number (&n)) env')) /\
     dest_closure max_app loc func args = SOME (Full_app body newenv rest) /\
     clos_to_bvlProof_v_rel max_app f1 refs code func func' /\
     ALL2 (clos_to_bvlProof_v_rel max_app f1 refs code) args args'
     ==> ?ck' body' aux1 aux2 newenv' exp'.
           lookup ptr code = SOME (n + 2,exp') /\
           clos_to_bvl_compile_exps max_app [body] aux1 = ([body'],aux2) /\
           clos_to_bvlProof_code_installed aux2 code /\
           clos_to_bvlProof_env_rel max_app f1 refs code newenv newenv' /\
           !(t1:(C,FFI)bvl_state).
             bvl_evaluate ([exp'],APPEND (DROP (LENGTH args' - (n + 1)) args') [func'],
                           bvl_inc_clock ck'
                             (bvl_state_refs_fupd (K refs) (bvl_state_code_fupd (K code) t1))) =
             bvl_evaluate ([body'],newenv',
                           bvl_state_refs_fupd (K refs) (bvl_state_code_fupd (K code) t1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`max_app:num`; `f1:(num,num)fmap`; `refs:(num,(bvl_v)bvl_ref)fmap`;
                  `code:(num#bvl_exp)spt`; `func:clos_v`; `func':bvl_v`; `loc:num option`;
                  `args:clos_v list`; `body:clos_exp`; `newenv:clos_v list`;
                  `rest:clos_v list`] C2BP1AUX_v_rel_closure_cases) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th -> is_var (lhs (concl th)))) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o check (fun th -> can (term_match [] `bvl_Block a b = bvl_Block c d`) (concl th))) THEN
  CASE_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THENL
  [
  EXISTS_TAC `0` THEN REWRITE_TAC[inc_clock0] THEN MATCH_MP_TAC cl_rel_run THEN
  ASM_MESON_TAC[dest_cl_imp_dest_cl'];
  RULE_ASSUM_TAC (REWRITE_RULE[INT_OF_NUM_EQ]) THEN C2BP1AUX_SUBST_VAR "n" THEN
  FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP C2BP1AUX_cl_rel_IMP o
               check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "cl_rel" with _ -> false)) THEN
  C2BP1AUX_SUBST_VAR "cl'" THEN
  SUBGOAL_THEN `n':num = num_args` SUBST_ALL_TAC THENL [ASM_MESON_TAC[option_INJ]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (args:clos_v list) = LENGTH (args':bvl_v list) /\
                LENGTH (arg_env:clos_v list) = LENGTH (ys:bvl_v list)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[EVERY2_LENGTH]; ALL_TAC] THEN
  SUBGOAL_THEN `num_remaining_args (func:clos_v) = SOME (num_args - LENGTH (arg_env:clos_v list))`
    ASSUME_TAC THENL
   [MP_TAC (ISPECL [`cl:clos_v`; `arg_env:clos_v list`; `func:clos_v`] C2BP1AUX_add_args_IMP) THEN
    ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `num_args - LENGTH (arg_env:clos_v list) <= LENGTH (args:clos_v list)`
    ASSUME_TAC THENL
   [FIRST_ASSUM (MP_TAC o MATCH_MP dest_closure_full_app) THEN
    ASM_REWRITE_TAC[option_INJ] THEN STRIP_TAC THEN C2BP1AUX_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `dest_closure' (loc:num option) (cl:clos_v) (APPEND args arg_env) = SOME (Full_app body newenv rest)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC dest_closure_full_of_part THEN
    MAP_EVERY EXISTS_TAC [`max_app:num`; `func:clos_v`; `num_args:num`] THEN
    ASM_REWRITE_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
  SUBGOAL_THEN `clos_to_bvlProof_v_rel max_app f1 refs code cl
                  (bvl_Block closure_tag (CONS (bvl_CodePtr ptr')
                     (CONS (bvl_Number (&(num_args - 1))) rest')))` ASSUME_TAC THENL
   [MATCH_MP_TAC (el 5 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    MAP_EVERY EXISTS_TAC [`env:clos_v list`; `fvs:bvl_v list`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC (ISPECL [`loc:num option`; `f1:(num,num)fmap`; `refs:(num,(bvl_v)bvl_ref)fmap`;
                  `code:(num#bvl_exp)spt`; `APPEND args arg_env:clos_v list`;
                  `APPEND args' ys:bvl_v list`; `env:clos_v list`; `rest':bvl_v list`;
                  `ptr':num`; `body:clos_exp`; `newenv:clos_v list`; `cl:clos_v`;
                  `bvl_Block closure_tag (CONS (bvl_CodePtr ptr')
                     (CONS (bvl_Number (&(num_args - 1))) rest'))`;
                  `rest:clos_v list`; `num_args - 1`; `fvs:bvl_v list`; `max_app:num`]
            cl_rel_run) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[EVERY2_APPEND_suff]; STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC [`1`; `body':bvl_exp`; `aux1:(num#num#bvl_exp)list`;
                        `aux2:(num#num#bvl_exp)list`; `new_env':bvl_v list`;
                        `generate_partial_app_closure_fn (num_args - 1)
                           (LENGTH (ys:bvl_v list) - 1)`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[option_INJ; PAIR_EQ] THEN C2BP1AUX_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t1:(C,FFI)bvl_state` THEN
  ABBREV_TAC `args'' = DROP (LENGTH args' - (num_args - 1 - LENGTH (ys:bvl_v list) + 1))
                         (args':bvl_v list)` THEN
  SUBGOAL_THEN `LENGTH (args'':bvl_v list) = num_args - LENGTH (ys:bvl_v list)`
    ASSUME_TAC THENL
   [EXPAND_TAC "args''" THEN REWRITE_TAC[LENGTH_DROP] THEN C2BP1AUX_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `DROP (LENGTH (APPEND args' ys) - (num_args - 1 + 1)) (APPEND args' ys) =
                APPEND (args'':bvl_v list) ys` ASSUME_TAC THENL
   [EXPAND_TAC "args''" THEN REWRITE_TAC[LENGTH_APPEND] THEN
    SUBGOAL_THEN `(LENGTH (args':bvl_v list) + LENGTH (ys:bvl_v list)) - (num_args - 1 + 1) =
                  LENGTH args' - (num_args - 1 - LENGTH ys + 1)`
      SUBST1_TAC THENL [C2BP1AUX_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DROP_APPEND1; ARITH_RULE `a - b <= a:num`]; ALL_TAC] THEN
  MP_TAC (ISPECL [`num_args:num`; `args'':bvl_v list`; `bvl_Number (&(num_args - 1))`;
                  `ys:bvl_v list`; `partial_app_tag`;
                  `bvl_Number (&(num_args - 1 - LENGTH (ys:bvl_v list)))`;
                  `closure_tag`; `ptr':num`;
                  `bvl_CodePtr (partial_app_fn_location max_app (num_args - 1)
                                  (LENGTH (ys:bvl_v list) - 1))`;
                  `rest':bvl_v list`; `exp':bvl_exp`; `code:(num#bvl_exp)spt`]
            evaluate_partial_app_fn) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `LENGTH (args'':bvl_v list) + LENGTH (ys:bvl_v list) + 1 = num_args - 1 + 2`
        SUBST1_TAC THENL [C2BP1AUX_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
      UNDISCH_TAC `~(arg_env:clos_v list = [])` THEN REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
      ASM_REWRITE_TAC[];
      C2BP1AUX_ARITH_TAC;
      C2BP1AUX_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(LENGTH (args'':bvl_v list) + LENGTH (ys:bvl_v list)) - num_args = 0`
    SUBST1_TAC THENL [C2BP1AUX_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DROP_0] THEN
  DISCH_THEN (MP_TAC o SPEC `bvl_inc_clock 1 (bvl_state_refs_fupd (K refs)
                                                 (t1:(C,FFI)bvl_state))`) THEN
  SUBGOAL_THEN `bvl_state_code_fupd (K code)
                  (bvl_inc_clock 1 (bvl_state_refs_fupd (K refs) (t1:(C,FFI)bvl_state))) =
                bvl_inc_clock 1 (bvl_state_refs_fupd (K refs) (bvl_state_code_fupd (K code) t1))`
    SUBST1_TAC THENL
   [REWRITE_TAC[bvl_state_component_equality] THEN SIMP[bvl_inc_clock_def]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[bvl_inc_clock_clock; ADD_EQ_0; ARITH_EQ] THEN
  SUBGOAL_THEN `bvl_dec_clock 1 (bvl_inc_clock 1 (bvl_state_refs_fupd (K refs)
                  (bvl_state_code_fupd (K code) (t1:(C,FFI)bvl_state)))) =
                bvl_state_refs_fupd (K refs) (bvl_state_code_fupd (K code) t1)`
    SUBST1_TAC THENL
   [REWRITE_TAC[bvl_state_component_equality] THEN
    SIMP[bvl_inc_clock_def; bvl_dec_clock_def] THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `t1:(C,FFI)bvl_state` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[]]);;

let C2BP1AUX_ALL2_REV_DROP_REV = prove
 (`!(R:A->B->bool) args args' k.
     k <= LENGTH args /\ ALL2 R args args'
     ==> ALL2 R (REVERSE (DROP k (REVERSE args))) (TAKE (LENGTH args' - k) args')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k <= LENGTH (args':B list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[EVERY2_LENGTH]; ALL_TAC] THEN
  SUBGOAL_THEN `TAKE (LENGTH args' - k) (args':B list) = REVERSE (DROP k (REVERSE args'))`
    SUBST1_TAC THENL
   [ASM_SIMP_TAC[DROP_REVERSE; REVERSE_REVERSE; BUTLASTN_TAKE]; ALL_TAC] THEN
  REWRITE_TAC[LIST_REL_REVERSE_EQ] THEN MATCH_MP_TAC EVERY2_DROP THEN
  ASM_REWRITE_TAC[LIST_REL_REVERSE_EQ]);;

(* HOL4 line 2767 [local] *)
let list_rel_app = prove
 (`!(R:clos_v->B->bool) args args' l0 c l func rem_args max_app.
     dest_closure max_app NONE func args = SOME (Full_app c l l0) /\
     num_remaining_args func = SOME rem_args /\
     ALL2 R args args'
     ==> ALL2 R l0 (TAKE (LENGTH args' - rem_args) args')`,
  REPEAT GEN_TAC THEN CASES_ON `func:clos_v` THEN
  REWRITE_TAC[dest_closure_def; num_remaining_args_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT] THEN
  TRY (PAIRARG_TAC) THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT COND_CASES_TAC THEN SIMP[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  MATCH_MP_TAC C2BP1AUX_ALL2_REV_DROP_REV THEN ASM_REWRITE_TAC[] THEN
  C2BP1AUX_ARITH_TAC);;

let C2BP1AUX_mk_cl_call_cong = prove
 (`!cl args env cl' args' env' v vs.
     (!(s:(C,FFI)bvl_state). bvl_evaluate ([cl],env,s) = (Rval [v],s)) /\
     (!(s:(C,FFI)bvl_state). bvl_evaluate ([cl'],env',s) = (Rval [v],s)) /\
     (!(s:(C,FFI)bvl_state). bvl_evaluate (args,env,s) = (Rval vs,s)) /\
     (!(s:(C,FFI)bvl_state). bvl_evaluate (args',env',s) = (Rval vs,s)) /\
     LENGTH args = LENGTH args'
     ==> !(s:(C,FFI)bvl_state).
           bvl_evaluate ([mk_cl_call cl args],env,s) =
           bvl_evaluate ([mk_cl_call cl' args'],env',s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  ASM_REWRITE_TAC[mk_cl_call_def; bvl_evaluate_def; bvl_evaluate_APPEND]);;

(* HOL4 line 2788: val mk_call_simp2 = Q.prove (...) |> INST_TYPE          *)
(* [alpha |-> 'c, beta |-> 'ffi] (its resulting statement) *)
let mk_call_simp2 = prove
 (`!n args stuff stuff' v (t:(C,FFI)bvl_state).
     n <= LENGTH args /\ ~(LENGTH stuff' = 0)
     ==> bvl_evaluate ([mk_cl_call (bvl_Var n) (list_of_seq bvl_Var n)],
                       APPEND (APPEND (TAKE n args) [v]) stuff,t) =
         bvl_evaluate ([mk_cl_call (bvl_Var 0) (list_of_seq (\n. bvl_Var (n + 1)) n)],
                       CONS v (APPEND args stuff'),t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (TAKE n (args:bvl_v list)) = n` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LENGTH_TAKE]; ALL_TAC] THEN
  MP_TAC (ISPECL [`bvl_Var n`; `list_of_seq bvl_Var n`;
                  `APPEND (APPEND (TAKE n args) [v]) stuff:bvl_v list`;
                  `bvl_Var 0`; `list_of_seq (\n. bvl_Var (n + 1)) n`;
                  `CONS v (APPEND args stuff'):bvl_v list`; `v:bvl_v`;
                  `TAKE n (args:bvl_v list)`] C2BP1AUX_mk_cl_call_cong) THEN
  ANTS_TAC THENL
   [ALL_TAC; DISCH_THEN (fun th -> REWRITE_TAC[th])] THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN REPEAT CONJ_TAC THEN GEN_TAC THENL
   [ASM_REWRITE_TAC[bvl_evaluate_def; LENGTH_APPEND; LENGTH] THEN
    COND_CASES_TAC THENL [ASM_SIMP_TAC[el_take_append]; ASM_ARITH_TAC];
    REWRITE_TAC[bvl_evaluate_def; LENGTH; LT_0; EL; HD];
    MP_TAC (ISPECL [`0`; `APPEND (APPEND (TAKE n args) [v]) stuff:bvl_v list`; `n:num`;
                    `s:(C,FFI)bvl_state`] bvl_evaluate_genlist_vars) THEN
    REWRITE_TAC[ADD_CLAUSES; ETA_AX; DROP_0] THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    MP_TAC (ISPECL [`TAKE n (args:bvl_v list)`; `APPEND [v:bvl_v] stuff`]
              TAKE_LENGTH_APPEND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN (fun th -> REWRITE_TAC[th]);
    MP_TAC (ISPECL [`1`; `CONS v (APPEND args stuff'):bvl_v list`; `n:num`;
                    `s:(C,FFI)bvl_state`] bvl_evaluate_genlist_vars) THEN
    REWRITE_TAC[LENGTH; LENGTH_APPEND] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[DROP_DEF; ARITH_EQ; ARITH_RULE `1 - 1 = 0`; DROP_0] THEN
    ASM_SIMP_TAC[TAKE_APPEND1]]);;

(* HOL4 line 2814 [local] *)
let no_partial_args = prove
 (`!func x cl arg_env.
     num_remaining_args func = SOME x /\
     get_num_args func = SOME x /\
     ~(x = 0) /\
     add_args cl arg_env = SOME func
     ==> arg_env = []`,
  REPEAT GEN_TAC THEN CASES_ON `cl:clos_v` THEN
  REWRITE_TAC[add_args_def; option_DISTINCT; option_INJ] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC (REWRITE_RULE[num_remaining_args_def; get_num_args_def; option_INJ;
                               LENGTH_APPEND]) THEN
  REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC);;

(* HOL4 line 2831: val s1 = s1:('c,'ffi) closSem$state (written out where *)
(* used) *)

(* HOL4 line 2834: val env_rel_ind = theorem "env_rel_ind" (made with      *)
(* clos_to_bvlProof_env_rel_def, part 1) *)

(* HOL4 line 2836 *)
let code_installed_subspt = prove
 (`!aux code1 code2.
     clos_to_bvlProof_code_installed aux code1 /\ subspt code1 code2
     ==> clos_to_bvlProof_code_installed aux code2`,
  REWRITE_TAC[C2BP1AUX_code_installed_MEM; subspt_lookup] THEN MESON_TAC[]);;

(* HOL4 line 2844 *)
let closure_code_installed_subspt = prove
 (`!a code1 b c code2.
     closure_code_installed a code1 b c /\ subspt code1 code2
     ==> closure_code_installed a code2 b c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[closure_code_installed_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "ALL" with _ -> false)) THEN
  MATCH_MP_TAC MONO_ALL THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[];
    MAP_EVERY EXISTS_TAC [`aux:(num#num#bvl_exp)list`; `c':bvl_exp`;
                          `aux1:(num#num#bvl_exp)list`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[subspt_lookup]; ASM_MESON_TAC[code_installed_subspt]]]);;

(* HOL4 line 2852 *)
let cl_rel_subspt = prove
 (`!a b c x y z code1 code2.
     cl_rel x y z code1 a b c ==> subspt code1 code2 ==> cl_rel x y z code2 a b c`,
  SUBGOAL_THEN
   `!x y z code1 a b c. cl_rel x y z code1 a b c
      ==> !code2. subspt code1 code2 ==> cl_rel x y z code2 a b c`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC cl_rel_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC (el 0 (CONJUNCTS cl_rel_rules)) THEN
    ASM_MESON_TAC[subspt_lookup; code_installed_subspt];
    MATCH_MP_TAC (el 1 (CONJUNCTS cl_rel_rules)) THEN
    ASM_MESON_TAC[subspt_lookup; code_installed_subspt];
    MATCH_MP_TAC (el 2 (CONJUNCTS cl_rel_rules)) THEN
    MAP_EVERY EXISTS_TAC [`exps_ps:((num#clos_exp)#num)list`; `ps:num list`; `r:num`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[closure_code_installed_subspt]]);;

(* HOL4 line 2866: Theorem v_rel_subspt = Q.prove (...) |> SPEC_ALL |>     *)
(* MP_CANON (its resulting statement: the antecedents conjoined) *)
let clos_to_bvlProof_v_rel_subspt = prove
 (`!max_app f refs code1 x y code2.
     clos_to_bvlProof_v_rel max_app f refs code1 x y /\ subspt code1 code2
     ==> clos_to_bvlProof_v_rel max_app f refs code2 x y`,
  SUBGOAL_THEN
   `!max_app f refs code1 x y.
      clos_to_bvlProof_v_rel max_app f refs code1 x y
      ==> !code2. subspt code1 code2 ==> clos_to_bvlProof_v_rel max_app f refs code2 x y`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC clos_to_bvlProof_v_rel_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MESON_TAC[clos_to_bvlProof_v_rel_rules];
    MESON_TAC[clos_to_bvlProof_v_rel_rules];
    MATCH_MP_TAC (el 2 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN C2BP1AUX_ALL2_IH_TAC;
    MATCH_MP_TAC (el 3 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (el 4 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (el 5 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    MAP_EVERY EXISTS_TAC [`env:clos_v list`; `fvs:bvl_v list`] THEN CONJ_TAC THENL
     [C2BP1AUX_ALL2_IH_TAC; ASM_MESON_TAC[cl_rel_subspt]];
    MATCH_MP_TAC (el 6 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    MAP_EVERY EXISTS_TAC [`env:clos_v list`; `fvs:bvl_v list`; `cl:clos_v`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [C2BP1AUX_ALL2_IH_TAC; C2BP1AUX_ALL2_IH_TAC; ASM_MESON_TAC[subspt_lookup];
      ASM_MESON_TAC[cl_rel_subspt]]]);;

(* HOL4 line 2882 *)
let env_rel_subspt = prove
 (`!x y z code e1 e2.
     clos_to_bvlProof_env_rel x y z code e1 e2
     ==> !code'. subspt code code' ==> clos_to_bvlProof_env_rel x y z code' e1 e2`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[clos_to_bvlProof_env_rel_def] THEN
  ASM_MESON_TAC[clos_to_bvlProof_v_rel_subspt]);;

(* HOL4 line 2892 [simp] *)
let clos_tag_shift_eq_nil_tag = prove
 (`!tag. (clos_tag_shift tag = nil_tag <=> tag = nil_tag) /\
         (clos_tag_shift tag = cons_tag <=> tag = cons_tag)`,
  GEN_TAC THEN REWRITE_TAC[clos_tag_shift_def; nil_tag_def; cons_tag_def] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

let _ = cake_add_simps [clos_tag_shift_eq_nil_tag];;

let C2BP1AUX_bvl_v_to_list_closure_tag = prove
 (`!a b ys. bvl_v_to_list (bvl_Block closure_tag (CONS a (CONS b ys))) = NONE`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `ys:bvl_v list` list_CASES) THEN
  REWRITE_TAC[bvl_v_to_list_def; closure_tag_def; cons_tag_def; ARITH_EQ]);;

let C2BP1AUX_v_to_list_CONS_IFF = prove
 (CASE_TERM
  `!(g1:A->B) (g2:A->C) o1 o2 h h' ns.
     (!ns. o1 = SOME (MAP g1 ns) <=> o2 = SOME (MAP g2 ns)) /\
     (!n. h = g1 n <=> h' = g2 n)
     ==> ((match o1 with NONE -> NONE | SOME t -> SOME (CONS h t)) = SOME (MAP g1 ns) <=>
          (match o2 with NONE -> NONE | SOME t -> SOME (CONS h' t)) = SOME (MAP g2 ns))`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `ns:A list` list_CASES) THEN
  STRUCT_CASES_TAC (ISPEC `o1:(B list)option` option_CASES) THEN
  STRUCT_CASES_TAC (ISPEC `o2:(C list)option` option_CASES) THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; CONS_11; NOT_CONS_NIL; MAP] THEN
  MESON_TAC[]);;

let C2BP1AUX_v_rel_Word64_IFF = prove
 (`!max_app f refs code h h' n.
     clos_to_bvlProof_v_rel max_app f refs code h h'
     ==> (h = clos_Word64 n <=> h' = bvl_Word64 n)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[v_rel_SIMP]) THEN ASM_REWRITE_TAC[]);;

let C2BP1AUX_v_rel_Number_IFF = prove
 (`!max_app f refs code h h' n.
     clos_to_bvlProof_v_rel max_app f refs code h h'
     ==> (h = clos_Number n <=> h' = bvl_Number n)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[v_rel_SIMP]) THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 2900 [local] (closSem's v_to_list on the left, bvlSem's on the *)
(* right) *)
let clos_to_bvlProof_v_rel_IMP_v_to_words_lemma = prove
 (`!x y max_app f refs code.
     clos_to_bvlProof_v_rel max_app f refs code x y
     ==> !ns. clos_v_to_list x = SOME (MAP clos_Word64 ns) <=>
              bvl_v_to_list y = SOME (MAP bvl_Word64 ns)`,
  MATCH_MP_TAC clos_v_to_list_ind THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[v_rel_SIMP; LIST_REL_NIL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[clos_v_to_list_def; bvl_v_to_list_def; clos_tag_shift_eq_nil_tag] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    MESON_TAC[MAP_EQ_NIL];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[v_rel_SIMP; LIST_REL_CONS1; LIST_REL_NIL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[clos_v_to_list_def; bvl_v_to_list_def; clos_tag_shift_eq_nil_tag] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN GEN_TAC THEN
    MATCH_MP_TAC C2BP1AUX_v_to_list_CONS_IFF THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[C2BP1AUX_v_rel_Word64_IFF]];
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[v_rel_SIMP; LIST_REL_CONS1; LIST_REL_NIL] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[clos_v_to_list_def; bvl_v_to_list_def; option_DISTINCT;
                  C2BP1AUX_bvl_v_to_list_closure_tag]);;

(* HOL4 line 2916 [local] *)
let clos_to_bvlProof_v_rel_IMP_v_to_words = prove
 (`!max_app f refs code x y.
     clos_to_bvlProof_v_rel max_app f refs code x y ==> bvl_v_to_words y = clos_v_to_words x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvl_v_to_words_def; clos_v_to_words_def] THEN
  FIRST_ASSUM (fun th -> REWRITE_TAC[MATCH_MP clos_to_bvlProof_v_rel_IMP_v_to_words_lemma th]));;

(* HOL4 line 2923 [local] (HOL4 Number o $& o w2n is                        *)
(* clos_Number o int_of_num o val, and bvl_Number o ... for bvl) *)
let clos_to_bvlProof_v_rel_IMP_v_to_bytes_lemma = prove
 (`!x y max_app f refs code.
     clos_to_bvlProof_v_rel max_app f refs code x y
     ==> !ns. clos_v_to_list x = SOME (MAP (clos_Number o int_of_num o (val:byte->num)) ns) <=>
              bvl_v_to_list y = SOME (MAP (bvl_Number o int_of_num o (val:byte->num)) ns)`,
  MATCH_MP_TAC clos_v_to_list_ind THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[v_rel_SIMP; LIST_REL_NIL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[clos_v_to_list_def; bvl_v_to_list_def; clos_tag_shift_eq_nil_tag] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    MESON_TAC[MAP_EQ_NIL];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[v_rel_SIMP; LIST_REL_CONS1; LIST_REL_NIL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[clos_v_to_list_def; bvl_v_to_list_def; clos_tag_shift_eq_nil_tag] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN GEN_TAC THEN
    MATCH_MP_TAC C2BP1AUX_v_to_list_CONS_IFF THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[];
      REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[C2BP1AUX_v_rel_Number_IFF]];
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[v_rel_SIMP; LIST_REL_CONS1; LIST_REL_NIL] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[clos_v_to_list_def; bvl_v_to_list_def; option_DISTINCT;
                  C2BP1AUX_bvl_v_to_list_closure_tag]);;

(* HOL4 line 2939 [local] *)
let clos_to_bvlProof_v_rel_IMP_v_to_bytes = prove
 (`!max_app f refs code x y.
     clos_to_bvlProof_v_rel max_app f refs code x y ==> bvl_v_to_bytes y = clos_v_to_bytes x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bvl_v_to_bytes_def; clos_v_to_bytes_def] THEN
  FIRST_ASSUM (fun th -> REWRITE_TAC[MATCH_MP clos_to_bvlProof_v_rel_IMP_v_to_bytes_lemma th]));;

(* HOL4 line 2946 *)
let not_domain_lookup = prove
 (`!n (x:A spt). ~(n IN domain x) <=> lookup n x = NONE`,
  REWRITE_TAC[lookup_NONE_domain]);;

(* HOL4 line 2952 [local] *)
let cl_rel_union = prove
 (`!a x y max_app f2 refs code c2.
     cl_rel max_app f2 refs code a x y ==> cl_rel max_app f2 refs (sptree_union code c2) a x y`,
  MESON_TAC[cl_rel_subspt; subspt_union]);;

(* HOL4 line 2986 [local] *)
let v_rel_union = prove
 (`!c2 x y max_app f2 refs code.
     clos_to_bvlProof_v_rel max_app f2 refs code x y
     ==> clos_to_bvlProof_v_rel max_app f2 refs (sptree_union code c2) x y`,
  MESON_TAC[clos_to_bvlProof_v_rel_subspt; subspt_union]);;

(* HOL4 line 3021 *)
let FEVERY_FUPDATE_LIST_SUFF = prove
 (`!progs (x:(A,B)fmap) p. FEVERY p x /\ ALL p progs ==> FEVERY p (x |++ progs)`,
  SUBGOAL_THEN `!(x:(A,B)fmap) (h:A#B) p. FEVERY p x /\ p h ==> FEVERY p (x |+ h)`
    ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; FEVERY_ALL_FLOOKUP; FLOOKUP_UPDATE] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[option_INJ];
    LIST_INDUCT_TAC THEN REWRITE_TAC[FUPDATE_LIST_THM; ALL] THEN ASM_MESON_TAC[]]);;

(* HOL4 line 3030 *)
let code_installed_union = prove
 (`!aux y x.
     clos_to_bvlProof_code_installed aux y /\ DISJOINT (set_of_list (MAP FST aux)) (domain x)
     ==> clos_to_bvlProof_code_installed aux (sptree_union x y)`,
  REWRITE_TAC[C2BP1AUX_code_installed_MEM; lookup_union] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lookup n (x:(num#bvl_exp)spt) = NONE` SUBST1_TAC THENL
   [REWRITE_TAC[lookup_NONE_domain] THEN
    UNDISCH_TAC `DISJOINT (set_of_list (MAP FST (aux:(num#num#bvl_exp)list)))
                   (domain (x:(num#bvl_exp)spt))` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_SET_OF_LIST] THEN
    DISCH_THEN (MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; FST] THEN ASM_MESON_TAC[];
    REWRITE_TAC[option_CASE] THEN ASM_MESON_TAC[]]);;

(* HOL4 line 3045 *)
let code_installed_union1 = prove
 (`!aux t1 t2.
     clos_to_bvlProof_code_installed aux t1
     ==> clos_to_bvlProof_code_installed aux (sptree_union t1 t2)`,
  MESON_TAC[code_installed_subspt; subspt_union]);;

(* HOL4 line 3053 *)
let code_installed_insert = prove
 (`!aux t x y.
     clos_to_bvlProof_code_installed aux t /\ ~MEM x (MAP FST aux)
     ==> clos_to_bvlProof_code_installed aux (insert x y t)`,
  REWRITE_TAC[C2BP1AUX_code_installed_MEM; lookup_insert; MEM_MAP; EXISTS_PAIR_THM; FST] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 3066 *)
let code_installed_fromAList = prove
 (`!ls aux.
     ALL_DISTINCT (MAP FST ls) /\ IS_SUBLIST ls aux
     ==> clos_to_bvlProof_code_installed aux (fromAList ls)`,
  REWRITE_TAC[C2BP1AUX_code_installed_MEM; lookup_fromAList] THEN
  MESON_TAC[IS_SUBLIST_MEM; ALOOKUP_ALL_DISTINCT_MEM]);;

(* HOL4 line 3078 *)
let chain_exps_cons = prove
 (`!n real_es. ?k1 k2 other. chain_exps n real_es = CONS (k1,0,k2) other`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[chain_exps_def] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  STRUCT_CASES_TAC (ISPEC `t:clos_exp list` list_CASES) THEN
  REWRITE_TAC[chain_exps_def; CONS_11; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 line 3085 *)
let compile_exps_APPEND = prove
 (CASE_TERM
  `!max_app xs ys aux.
     clos_to_bvl_compile_exps max_app (APPEND xs ys) aux =
     (let (c1,aux1) = clos_to_bvl_compile_exps max_app xs aux in
      let (c2,aux2) = clos_to_bvl_compile_exps max_app ys aux1 in
        (APPEND c1 c2,aux2))`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; clos_to_bvl_compile_exps_def; pair_CASE] THEN
    REPEAT GEN_TAC THEN CLOS2AUX_SPLIT_PAIR_TAC THEN REWRITE_TAC[pair_CASE; APPEND];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[APPEND] THEN
  GEN_REWRITE_TAC LAND_CONV [compile_exps_CONS] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [compile_exps_CONS] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT (CLOS2AUX_SPLIT_PAIR_TAC THEN ASM_REWRITE_TAC[pair_CASE]) THEN
  REWRITE_TAC[APPEND_ASSOC]);;

let C2BP1AUX_compile_exps_CONS_SND = prove
 (`!max_app x xs aux.
     SND (clos_to_bvl_compile_exps max_app (CONS x xs) aux) =
     SND (clos_to_bvl_compile_exps max_app xs
            (SND (clos_to_bvl_compile_exps max_app [x] aux)))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [compile_exps_CONS] THEN
  CLOS2AUX_SPLIT_PAIR_TAC THEN REWRITE_TAC[SND] THEN
  CLOS2AUX_SPLIT_PAIR_TAC THEN REWRITE_TAC[SND]);;

let C2BP1AUX_compile_exps_APPEND_SND = prove
 (`!max_app xs ys aux.
     SND (clos_to_bvl_compile_exps max_app (APPEND xs ys) aux) =
     SND (clos_to_bvl_compile_exps max_app ys
            (SND (clos_to_bvl_compile_exps max_app xs aux)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_exps_APPEND] THEN
  CLOS2AUX_SPLIT_PAIR_TAC THEN REWRITE_TAC[SND] THEN
  CLOS2AUX_SPLIT_PAIR_TAC THEN REWRITE_TAC[SND]);;

let C2BP1AUX_compile_exps_acc_SND = prove
 (`!max_app xs aux. ?ys. SND (clos_to_bvl_compile_exps max_app xs aux) = APPEND ys aux`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`max_app:num`; `xs:clos_exp list`; `aux:(num#num#bvl_exp)list`]
            compile_exps_acc) THEN
  SPEC_TAC (`clos_to_bvl_compile_exps max_app xs aux`,
            `p:bvl_exp list#(num#num#bvl_exp)list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pair_CASE; SND] THEN MESON_TAC[]);;

let C2BP1AUX_compile_Op_nil_SND = prove
 (`!max_app t op aux.
     SND (clos_to_bvl_compile_exps max_app [clos_Op t op []] aux) = aux`,
  REWRITE_TAC[clos_to_bvl_compile_exps_def; pair_CASE; SND]);;

let C2BP1AUX_compile_Let_Call_SND = prove
 (`!max_app h a n.
     SND (clos_to_bvl_compile_exps max_app
            [clos_Let backend_common_None [h] (clos_Call backend_common_None 0 n [])] a) =
     SND (clos_to_bvl_compile_exps max_app [h] a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_to_bvl_compile_exps_def; pair_CASE] THEN
  CLOS2AUX_SPLIT_PAIR_TAC THEN REWRITE_TAC[SND]);;

let C2BP1AUX_chain_exps_SND = prove
 (`!t n h a max_app.
     SND (clos_to_bvl_compile_exps max_app (MAP (SND o SND) (chain_exps n (CONS h t))) a) =
     SND (clos_to_bvl_compile_exps max_app (CONS h t) a)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[chain_exps_def; MAP; o_THM; SND] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[C2BP1AUX_compile_exps_CONS_SND] THEN
  ASM_REWRITE_TAC[C2BP1AUX_compile_Let_Call_SND]);;

(* HOL4 line 3099 [local] *)
let compile_exps_chain_exps_cons = prove
 (`!n h t a new_exps aux x6 x7 max_app.
     clos_to_bvl_compile_exps max_app (MAP (SND o SND) (chain_exps n (CONS h t))) a =
       (new_exps,aux) /\
     clos_to_bvl_compile_exps max_app (CONS h t) a = (x6,x7)
     ==> x7 = aux`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`t:clos_exp list`; `n:num`; `h:clos_exp`; `a:(num#num#bvl_exp)list`;
                 `max_app:num`] C2BP1AUX_chain_exps_SND) THEN
  ASM_REWRITE_TAC[SND] THEN MESON_TAC[]);;

let C2BP1AUX_same_aux_SND = prove
 (`!max_app n real_es progs0.
     extract_name progs0 = (n,real_es)
     ==> SND (clos_to_bvl_compile_exps max_app (MAP (SND o SND) (chain_exps n real_es)) []) =
         SND (clos_to_bvl_compile_exps max_app progs0 [])`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `progs0:clos_exp list` list_CASES) THENL
   [REWRITE_TAC[extract_name_def; PAIR_EQ] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[chain_exps_def; MAP; o_THM; SND] THEN
    REWRITE_TAC[C2BP1AUX_compile_Op_nil_SND] THEN
    REWRITE_TAC[clos_to_bvl_compile_exps_def; SND];
    ALL_TAC] THEN
  REWRITE_TAC[extract_name_def] THEN
  CASES_ON `some n. ?t. h = clos_Op t (IntOp (clos_Const (&n))) []` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THENL
   [STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC[C2BP1AUX_chain_exps_SND];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP BASICAUX_some_SOME) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
  STRUCT_CASES_TAC (ISPEC `t:clos_exp list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL] THEN
  REWRITE_TAC[chain_exps_def; MAP; o_THM; SND; C2BP1AUX_chain_exps_SND] THEN
  GEN_REWRITE_TAC RAND_CONV [C2BP1AUX_compile_exps_CONS_SND] THEN
  REWRITE_TAC[C2BP1AUX_compile_Op_nil_SND]);;

(* HOL4 line 3113 *)
let compile_exps_same_aux = prove
 (`!max_app n real_es new_exps aux progs0 x6 x7.
     clos_to_bvl_compile_exps max_app (MAP (SND o SND) (chain_exps n real_es)) [] =
       (new_exps,aux) /\
     extract_name progs0 = (n,real_es) /\
     clos_to_bvl_compile_exps max_app progs0 [] = (x6,x7)
     ==> x7 = aux`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM (MP_TAC o SPEC `max_app:num` o MATCH_MP C2BP1AUX_same_aux_SND) THEN
  ASM_REWRITE_TAC[SND] THEN MESON_TAC[]);;

(* HOL4 line 3136 *)
let compile_exps_twice_IS_SUBLIST = prove
 (`!progs0 n real_es max_app progs1 new_exps aux x6 x7.
     extract_name progs0 = (n,real_es) /\
     clos_to_bvl_compile_exps max_app
       (APPEND (MAP (SND o SND) (chain_exps n real_es)) progs1) [] = (new_exps,aux) /\
     clos_to_bvl_compile_exps max_app progs0 [] = (x6,x7)
     ==> IS_SUBLIST aux x7`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `aux = SND (clos_to_bvl_compile_exps max_app progs1 x7)` SUBST1_TAC THENL
   [FIRST_ASSUM (MP_TAC o SPEC `max_app:num` o MATCH_MP C2BP1AUX_same_aux_SND) THEN
    MP_TAC (SPECL [`max_app:num`; `MAP (SND o SND) (chain_exps n real_es)`;
                   `progs1:clos_exp list`; `[]:(num#num#bvl_exp)list`]
              C2BP1AUX_compile_exps_APPEND_SND) THEN
    ASM_REWRITE_TAC[SND] THEN MESON_TAC[];
    MP_TAC (SPECL [`max_app:num`; `progs1:clos_exp list`; `x7:(num#num#bvl_exp)list`]
              C2BP1AUX_compile_exps_acc_SND) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IS_SUBLIST_DEF] THEN MESON_TAC[APPEND_NIL; APPEND]]);;

(* HOL4 line 3153 *)
let clos_to_bvlProof_code_installed_cons = prove
 (`!x xs c.
     clos_to_bvlProof_code_installed (CONS x xs) c ==> clos_to_bvlProof_code_installed xs c`,
  SIMP_TAC[clos_to_bvlProof_code_installed_def; ALL]);;

let C2BP1AUX_chain_exps_HD = prove
 (`!n (l:clos_exp list). ?e other. chain_exps n l = CONS (n,0,e) other`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[chain_exps_def] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  STRUCT_CASES_TAC (ISPEC `t:clos_exp list` list_CASES) THEN
  REWRITE_TAC[chain_exps_def; CONS_11; PAIR_EQ] THEN MESON_TAC[]);;

let C2BP1AUX_chain_compile_CONS2 = prove
 (`!max_app index h h' tl acc x6 x7 new_exps aux.
     clos_to_bvl_compile_exps max_app (CONS h (CONS h' tl)) acc = (x6,x7) /\
     clos_to_bvl_compile_exps max_app
       (MAP (SND o SND) (chain_exps index (CONS h (CONS h' tl)))) acc = (new_exps,aux)
     ==> ?ch a_h x6' new_exps'.
           clos_to_bvl_compile_exps max_app [h] acc = ([ch],a_h) /\
           x6 = CONS ch x6' /\
           clos_to_bvl_compile_exps max_app (CONS h' tl) a_h = (x6',x7) /\
           new_exps = CONS (bvl_Let [ch] (bvl_Call 0 (SOME ((index + 1) + num_stubs max_app)) []))
                        new_exps' /\
           clos_to_bvl_compile_exps max_app
             (MAP (SND o SND) (chain_exps (index + 1) (CONS h' tl))) a_h = (new_exps',aux)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (MP_TAC o ONCE_REWRITE_RULE[compile_exps_CONS] o
              REWRITE_RULE[chain_exps_def; MAP; o_THM; SND]) THEN
  REWRITE_TAC[clos_to_bvl_compile_exps_def; pair_CASE] THEN
  REPEAT (CLOS2AUX_SPLIT_PAIR_TAC THEN REWRITE_TAC[pair_CASE]) THEN
  FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP clos_to_bvl_compile_exps_SING) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  MAP_EVERY EXISTS_TAC [`d:bvl_exp`; `aux1:(num#num#bvl_exp)list`; `c2:bvl_exp list`;
                        `c2':bvl_exp list`] THEN
  ASM_REWRITE_TAC[APPEND; HD]);;

let C2BP1AUX_eval_Let_Call0 = prove
 (`!ch w (s2:(C,FFI)bvl_state) loc1 d1' ck (t:(C,FFI)bvl_state).
     bvl_evaluate ([ch],[],t) = (Rval [w],s2) /\
     lookup loc1 (bvl_state_code s2) = SOME (0,d1')
     ==> bvl_evaluate ([bvl_Let [ch] (bvl_Call 0 (SOME loc1) [])],[],
                       bvl_state_clock_fupd (K (ck + 1 + bvl_state_clock t)) t) =
         bvl_evaluate ([d1'],[],bvl_state_clock_fupd (K (ck + bvl_state_clock s2)) s2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM (MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] bvl_evaluate_add_clock)) THEN
  CASE_REWRITE_TAC[] THEN DISCH_THEN (MP_TAC o SPEC `ck + 1`) THEN
  SUBGOAL_THEN `bvl_inc_clock (ck + 1) t = bvl_state_clock_fupd (K (ck + 1 + bvl_state_clock t)) (t:(C,FFI)bvl_state)` SUBST1_TAC THENL
   [REWRITE_TAC[bvl_inc_clock_def] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  C2BP1AUX_EVAL_LHS_TAC (C2BP1AUX_eval_lemmas @ [bvl_find_code_def]) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[bvl_state_component_equality] THEN
  SIMP[bvl_dec_clock_def; bvl_inc_clock_def] THEN ARITH_TAC);;

let C2BP1AUX_chained_gen = prove
 (CASE_TERM `!all index x6 (t:(C,FFI)bvl_state) res t1 k1 d1 new_exps rest acc x7 max_app aux.
     bvl_evaluate (x6,[],t) = (res,t1) /\
     HD (APPEND (MAP2 (\p (exp:bvl_exp). match p with
                         (loc,args,_) -> (loc + num_stubs max_app,args,exp))
                   (chain_exps index all) new_exps) rest) = (k1,0,d1) /\
     clos_to_bvl_compile_exps max_app all acc = (x6,x7) /\
     clos_to_bvl_compile_exps max_app (MAP (SND o SND) (chain_exps index all)) acc =
       (new_exps,aux) /\
     clos_to_bvlProof_code_installed
       (APPEND (MAP2 (\p (exp:bvl_exp). match p with
                        (loc,args,_) -> (loc + num_stubs max_app,args,exp))
                  (chain_exps index all) new_exps) rest) (bvl_state_code t) /\
     ~(x6 = [])
     ==> ?ck8 res8.
           bvl_evaluate ([d1],[],bvl_state_clock_fupd (K (ck8 + bvl_state_clock t)) t) =
             (res8,t1) /\
           (match res with
              Rval vs -> res8 = Rval [LAST vs]
            | Rerr v3 -> res8 = Rerr v3)`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[clos_to_bvl_compile_exps_def; PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `h:clos_exp` THEN X_GEN_TAC `tl:clos_exp list` THEN DISCH_TAC THEN
  CASES_ON `tl:clos_exp list` THENL
   [(* single *)
    REPEAT GEN_TAC THEN REWRITE_TAC[chain_exps_def; MAP; o_THM; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `new_exps:bvl_exp list = x6 /\ aux:(num#num#bvl_exp)list = x7`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL [ASM_MESON_TAC[PAIR_EQ]; ALL_TAC] THEN
  FIRST_ASSUM (X_CHOOSE_THEN `d:bvl_exp` SUBST_ALL_TAC o
               MATCH_MP clos_to_bvl_compile_exps_SING) THEN
  RULE_ASSUM_TAC (CASE_REWRITE_RULE[MAP2; APPEND; HD; PAIR_EQ]) THEN
    REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; bvl_with_same_clock] THEN
  EXISTS_TAC `res:((bvl_v)list,bvl_v)result` THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `res:((bvl_v)list,bvl_v)result` THEN CASE_REWRITE_TAC[] THEN
  FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP bvl_evaluate_SING) THEN ASM_REWRITE_TAC[LAST];
    (* double *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL [`max_app:num`; `index:num`; `h:clos_exp`; `a0:clos_exp`; `a1:clos_exp list`;
                 `acc:(num#num#bvl_exp)list`; `x6:bvl_exp list`; `x7:(num#num#bvl_exp)list`;
                 `new_exps:bvl_exp list`; `aux:(num#num#bvl_exp)list`]
           C2BP1AUX_chain_compile_CONS2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC (CASE_REWRITE_RULE[chain_exps_def; MAP2; APPEND; HD; PAIR_EQ]) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP clos_to_bvlProof_code_installed_cons o
               check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                    "clos_to_bvlProof_code_installed" with _ -> false)) THEN
  MP_TAC (SPECL [`index + 1`; `CONS (a0:clos_exp) a1`] C2BP1AUX_chain_exps_HD) THEN
  DISCH_THEN (X_CHOOSE_THEN `e0:clos_exp` (X_CHOOSE_THEN `other:(num#num#clos_exp)list`
                ASSUME_TAC)) THEN
  SUBGOAL_THEN `?d' rest'. new_exps' = CONS (d':bvl_exp) rest'` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM (MP_TAC o MATCH_MP clos_to_bvl_compile_exps_LENGTH o
                 check (fun th -> try fst(dest_pair(rhs(concl th))) = `new_exps':bvl_exp list`
                                  with _ -> false)) THEN
    ASM_REWRITE_TAC[LENGTH_MAP; LENGTH] THEN
    STRUCT_CASES_TAC (ISPEC `new_exps':bvl_exp list` list_CASES) THEN
    REWRITE_TAC[LENGTH; CONS_11] THEN MESON_TAC[NOT_SUC];
    ALL_TAC] THEN
  C2BP1AUX_SUBST_VAR "new_exps'" THEN
  SUBGOAL_THEN `lookup ((index + 1) + num_stubs max_app) (bvl_state_code (t:(C,FFI)bvl_state)) =
                SOME (0,d')` ASSUME_TAC THENL
   [FIRST_ASSUM (fun ceq ->
      if can (term_match [] `chain_exps n l = CONS (a:num#num#clos_exp) b`) (concl ceq) then
        FIRST_ASSUM (MP_TAC o CASE_REWRITE_RULE[ceq; MAP2; APPEND] o
                     check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                          "clos_to_bvlProof_code_installed" &&
                                          not (can (term_match [] `CONS (a:num#num#bvl_exp) b`)
                                                 (rand(rator(concl th))))
                                      with _ -> false))
      else NO_TAC) THEN
    REWRITE_TAC[C2BP1AUX_code_installed_MEM; MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o ONCE_REWRITE_RULE[bvl_evaluate_CONS] o
                 check (fun th -> can (term_match [] `bvl_evaluate (CONS (a:bvl_exp) b,c,d:(C,FFI)bvl_state) = e`)
                                    (concl th))) THEN
    MP_TAC (ISPEC `bvl_evaluate ([ch],[],t:(C,FFI)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN (X_CHOOSE_THEN `r1:((bvl_v)list,bvl_v)result`
               (X_CHOOSE_THEN `s1:(C,FFI)bvl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `r1:((bvl_v)list,bvl_v)result` THEN CASE_REWRITE_TAC[] THENL
     [(* Rval *)
      FIRST_ASSUM (X_CHOOSE_THEN `w:bvl_v` SUBST_ALL_TAC o MATCH_MP bvl_evaluate_SING o
               check (fun th -> can (term_match [] `bvl_evaluate ([ch:bvl_exp],[]:bvl_v list,t:(C,FFI)bvl_state) = (Rval a,s1)`) (concl th))) THEN
  SUBGOAL_THEN `~(x6':bvl_exp list = [])` ASSUME_TAC THENL
   [FIRST_ASSUM (MP_TAC o MATCH_MP clos_to_bvl_compile_exps_LENGTH o
                 check (fun th -> try fst(dest_pair(rhs(concl th))) = `x6':bvl_exp list`
                                  with _ -> false)) THEN
    REWRITE_TAC[LENGTH] THEN MESON_TAC[LENGTH; NOT_SUC];
    ALL_TAC] THEN
  SUBGOAL_THEN `subspt (bvl_state_code (t:(C,FFI)bvl_state)) (bvl_state_code (s1:(C,FFI)bvl_state))`
    ASSUME_TAC THENL [ASM_MESON_TAC[bvl_evaluate_mono]; ALL_TAC] THEN
  MP_TAC (ISPEC `bvl_evaluate (x6',[],s1:(C,FFI)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN (X_CHOOSE_THEN `r2:((bvl_v)list,bvl_v)result`
               (X_CHOOSE_THEN `s2:(C,FFI)bvl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`index + 1`; `x6':bvl_exp list`; `s1:(C,FFI)bvl_state`;
                                 `r2:((bvl_v)list,bvl_v)result`; `s2:(C,FFI)bvl_state`;
                                 `(index + 1) + num_stubs max_app`; `d':bvl_exp`;
                                 `CONS (d':bvl_exp) rest'`; `rest:(num#num#bvl_exp)list`;
                                 `a_h:(num#num#bvl_exp)list`; `x7:(num#num#bvl_exp)list`;
                                 `max_app:num`; `aux:(num#num#bvl_exp)list`] o
                 check (is_forall o concl)) THEN
      ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM (fun ceq ->
        if can (term_match [] `chain_exps n l = CONS (a:num#num#clos_exp) b`) (concl ceq)
        then REWRITE_TAC[ceq] else NO_TAC) THEN
      CASE_REWRITE_TAC[MAP2; APPEND; HD];
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC code_installed_subspt THEN
      EXISTS_TAC `bvl_state_code (t:(C,FFI)bvl_state)` THEN CONJ_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `ck8:num` (X_CHOOSE_THEN `res8:((bvl_v)list,bvl_v)result`
                STRIP_ASSUME_TAC)) THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`ck8 + 1`; `res8:((bvl_v)list,bvl_v)result`] THEN
  (SUBGOAL_THEN `(ck8 + 1) + bvl_state_clock (t:(C,FFI)bvl_state) =
                 ck8 + 1 + bvl_state_clock t` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
  MP_TAC (SPECL [`ch:bvl_exp`; `w:bvl_v`; `s1:(C,FFI)bvl_state`;
                 `(index + 1) + num_stubs max_app`; `d':bvl_exp`; `ck8:num`;
                 `t:(C,FFI)bvl_state`] C2BP1AUX_eval_Let_Call0) THEN
  (ANTS_TAC THENL [ASM_MESON_TAC[subspt_lookup]; DISCH_THEN SUBST1_TAC]) THEN
  CASES_ON `r2:((bvl_v)list,bvl_v)result` THEN
  RULE_ASSUM_TAC (CASE_REWRITE_RULE[PAIR_EQ; HD]) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[LAST] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      ASM_MESON_TAC[bvl_evaluate_IMP_LENGTH; LENGTH; LENGTH_EQ_NIL];
      (* Rerr *)
      STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
      REWRITE_TAC[ADD_CLAUSES; bvl_with_same_clock] THEN
      ONCE_REWRITE_TAC[bvl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
      MESON_TAC[]]]);;

(* HOL4 line 3159 (HOL4 Abbrev (progs = ...) is progs = ...; the paired     *)
(* lambda of MAP2 is written as in clos_to_bvl_compile_prog_def) *)
let chained_lemma = prove
 (CASE_TERM
  `!index all x6 (t:(C,FFI)bvl_state) res t1 progs k1 d1 new_exps rest acc x7 max_app aux.
     bvl_evaluate (x6,[],t) = (res,t1) /\ HD progs = (k1,0,d1) /\
     progs =
       APPEND (MAP2 (\p (exp:bvl_exp). match p with
                       (loc,args,_) -> (loc + num_stubs max_app,args,exp))
                 (chain_exps index all) new_exps) rest /\
     clos_to_bvl_compile_exps max_app all acc = (x6,x7) /\
     clos_to_bvl_compile_exps max_app (MAP (SND o SND) (chain_exps index all)) acc =
       (new_exps,aux) /\
     clos_to_bvlProof_code_installed progs (bvl_state_code t) /\ ~(x6 = [])
     ==> ?ck8 res8.
           bvl_evaluate ([d1],[],bvl_state_clock_fupd (K (ck8 + bvl_state_clock t)) t) =
             (res8,t1) /\
           (match res with
              Rval vs -> res8 = Rval [LAST vs]
            | Rerr v3 -> res8 = Rerr v3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  MP_TAC (SPECL [`all:clos_exp list`; `index:num`; `x6:bvl_exp list`; `t:(C,FFI)bvl_state`;
                 `res:((bvl_v)list,bvl_v)result`; `t1:(C,FFI)bvl_state`; `k1:num`; `d1:bvl_exp`;
                 `new_exps:bvl_exp list`; `rest:(num#num#bvl_exp)list`;
                 `acc:(num#num#bvl_exp)list`; `x7:(num#num#bvl_exp)list`; `max_app:num`;
                 `aux:(num#num#bvl_exp)list`] C2BP1AUX_chained_gen) THEN
  ASM_REWRITE_TAC[]);;

let C2BP1AUX_HD_APPEND_MAP2 = prove
 (`!(f:A->B->C) l1 l2 m rest x r.
     ~(l1 = []) ==> LENGTH l1 = LENGTH l2 ==>
     APPEND (APPEND (MAP2 f l1 l2) m) rest = CONS x r ==> HD (APPEND (MAP2 f l1 l2) m) = x`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[NOT_CONS_NIL; LENGTH; NOT_SUC; MAP2; APPEND; HD; CONS_11] THEN MESON_TAC[]);;

let C2BP1AUX_chained_APPEND = prove
 (CASE_TERM `!all n progs1 x6 (t:(C,FFI)bvl_state) res t1 k1 d1 new_exps aux rest max_app acc x7
      progs.
     bvl_evaluate (x6,[],t) = (res,t1) /\
     APPEND progs aux = CONS (k1,0,d1) rest /\
     progs =
       MAP2 (\p (exp:bvl_exp). match p with
               (loc,args,_) -> (loc + num_stubs max_app,args,exp))
         (APPEND (chain_exps n all) progs1) new_exps /\
     clos_to_bvl_compile_exps max_app all acc = (x6,x7) /\
     clos_to_bvl_compile_exps max_app
       (APPEND (MAP (SND o SND) (chain_exps n all)) (MAP (SND o SND) progs1)) acc =
       (new_exps,aux) /\
     clos_to_bvlProof_code_installed progs (bvl_state_code t) /\ ~(x6 = [])
     ==> ?ck8 res8.
           bvl_evaluate ([d1],[],bvl_state_clock_fupd (K (bvl_state_clock t + ck8)) t) =
             (res8,t1) /\
           (match res with
              Rval vs -> res8 = Rval [LAST vs]
            | Rerr v3 -> res8 = Rerr v3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o REWRITE_RULE[compile_exps_APPEND] o
                 check (fun th -> try fst(dest_pair(rhs(concl th))) = `new_exps:bvl_exp list`
                                  with _ -> false)) THEN
  CLOS2AUX_SPLIT_PAIR_TAC THEN REWRITE_TAC[pair_CASE] THEN
  CLOS2AUX_SPLIT_PAIR_TAC THEN REWRITE_TAC[pair_CASE; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  SUBGOAL_THEN `LENGTH (c1:bvl_exp list) = LENGTH (chain_exps n (all:clos_exp list))`
    ASSUME_TAC THENL
   [FIRST_ASSUM (MP_TAC o MATCH_MP clos_to_bvl_compile_exps_LENGTH o
                 check (fun th -> try fst(dest_pair(rhs(concl th))) = `c1:bvl_exp list`
                                  with _ -> false)) THEN
    REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  SUBGOAL_THEN `~(chain_exps n (all:clos_exp list) = [])` ASSUME_TAC THENL
   [MESON_TAC[C2BP1AUX_chain_exps_HD; NOT_CONS_NIL]; ALL_TAC] THEN
  FIRST_ASSUM ((fun lth -> RULE_ASSUM_TAC (fun th -> if concl th = concl lth then th
                                                     else SIMP_RULE[MAP2_APPEND; lth] th)) o
               check (fun th -> can (term_match [] `LENGTH (c1:bvl_exp list) = x`) (concl th))) THEN
  FIRST_ASSUM (fun nth ->
    if can (term_match [] `~(chain_exps n l = [])`) (concl nth) then
      FIRST_ASSUM (fun lth ->
        if can (term_match [] `LENGTH (c1:bvl_exp list) = x`) (concl lth) then
          FIRST_ASSUM (fun ath ->
            if can (term_match [] `APPEND (APPEND (a:(num#num#bvl_exp)list) b) c = CONS d e`)
                   (concl ath)
            then ASSUME_TAC (MATCH_MP (MATCH_MP (MATCH_MP C2BP1AUX_HD_APPEND_MAP2 nth)
                                                (SYM lth)) ath)
            else NO_TAC)
        else NO_TAC)
    else NO_TAC) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC C2BP1AUX_chained_gen THEN
  ASM_MESON_TAC[]);;

let C2BP1AUX_compile_Op_Const = prove
 (`!max_app t' a aux.
     clos_to_bvl_compile_exps max_app [clos_Op t' (IntOp (clos_Const a)) []] aux =
     ([bvl_Op (IntOp (clos_Const a)) []],aux)`,
  REWRITE_TAC[clos_to_bvl_compile_exps_def; pair_CASE] THEN
  CASE_REWRITE_TAC[clos_to_bvl_compile_op_def]);;

let C2BP1AUX_eval_Op_Const = prove
 (`!a env (s:(C,FFI)bvl_state).
     bvl_evaluate ([bvl_Op (IntOp (clos_Const a)) []],env,s) = (Rval [bvl_Number a],s)`,
  REPEAT GEN_TAC THEN C2BP1AUX_EVAL_LHS_TAC C2BP1AUX_eval_lemmas THEN REWRITE_TAC[]);;

(* HOL4 line 3232 (HOL4 Abbrev (...) is the equation itself) *)
let evaluate_IMP_evaluate_chained = prove
 (CASE_TERM
  `!x6 (t:(C,FFI)bvl_state) res t1 progs aux k1 d1 rest max_app n real_es progs1 new_exps
     progs0 x7.
     bvl_evaluate (x6,[],t) = (res,t1) /\
     APPEND progs aux = CONS (k1,0,d1) rest /\
     progs =
       MAP2 (\p (exp:bvl_exp). match p with
               (loc,args,_) -> (loc + num_stubs max_app,args,exp))
         (APPEND (chain_exps n real_es) progs1) new_exps /\
     clos_to_bvl_compile_exps max_app progs0 [] = (x6,x7) /\
     clos_to_bvl_compile_exps max_app
       (APPEND (MAP (SND o SND) (chain_exps n real_es)) (MAP (SND o SND) progs1)) [] =
       (new_exps,aux) /\
     extract_name progs0 = (n,real_es) /\
     clos_to_bvlProof_code_installed progs (bvl_state_code t) /\ ~(x6 = [])
     ==> ?ck8 res8.
           bvl_evaluate ([d1],[],bvl_state_clock_fupd (K (bvl_state_clock t + ck8)) t) =
             (res8,t1) /\
           (match res with
              Rval vs -> res8 = Rval [LAST vs]
            | err -> res8 = err)`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `h:clos_exp` (X_CHOOSE_THEN `tl:clos_exp list`
    SUBST1_TAC)) (ISPEC `progs0:clos_exp list` list_CASES) THENL
   [REWRITE_TAC[extract_name_def; clos_to_bvl_compile_exps_def; PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[extract_name_def] THEN
  CASES_ON `some n. ?t. h = clos_Op t (IntOp (clos_Const (&n))) []` THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THENL
   [(* NONE *)
    STRIP_TAC THEN RVEQ_TAC THEN MATCH_MP_TAC C2BP1AUX_chained_APPEND THEN ASM_MESON_TAC[];
    (* SOME *)
    STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o MATCH_MP BASICAUX_some_SOME o
                 check (fun th -> can (term_match [] `(some) (P:num->bool) = SOME m`) (concl th))) THEN
  REWRITE_TAC[] THEN DISCH_THEN (CHOOSE_THEN SUBST_ALL_TAC) THEN
  RVEQ_TAC THEN ASM_CASES_TAC `tl:clos_exp list = []` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE[]) THEN RVEQ_TAC THEN
    MATCH_MP_TAC C2BP1AUX_chained_APPEND THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM ((fun th -> RULE_ASSUM_TAC (fun a -> if concl a = concl th then a
                                                  else REWRITE_RULE[th] a)) o
               check (fun th -> concl th = `~(tl:clos_exp list = [])`)) THEN
  RVEQ_TAC THEN
  FIRST_X_ASSUM (MP_TAC o REWRITE_RULE[C2BP1AUX_compile_Op_Const; pair_CASE] o
                 ONCE_REWRITE_RULE[compile_exps_CONS] o
                 check (fun th -> try fst(dest_pair(rhs(concl th))) = `x6:bvl_exp list`
                                  with _ -> false)) THEN
  CLOS2AUX_SPLIT_PAIR_TAC THEN REWRITE_TAC[pair_CASE; PAIR_EQ; APPEND] THEN STRIP_TAC THEN
  RVEQ_TAC THEN
    SUBGOAL_THEN `~(c2:bvl_exp list = [])` ASSUME_TAC THENL
   [FIRST_ASSUM (MP_TAC o MATCH_MP clos_to_bvl_compile_exps_LENGTH o
                 check (fun th -> try fst(dest_pair(rhs(concl th))) = `c2:bvl_exp list`
                                  with _ -> false)) THEN
    ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
  FIRST_X_ASSUM (MP_TAC o REWRITE_RULE[C2BP1AUX_eval_Op_Const] o
                 ONCE_REWRITE_RULE[bvl_evaluate_CONS] o
                 check (fun th -> can (term_match []
                          `bvl_evaluate (CONS (a:bvl_exp) b,c,d:(C,FFI)bvl_state) = e`)
                          (concl th))) THEN
  CASE_REWRITE_TAC[HD] THEN
  MP_TAC (ISPEC `bvl_evaluate (c2,[],t:(C,FFI)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN (X_CHOOSE_THEN `r2:((bvl_v)list,bvl_v)result`
               (X_CHOOSE_THEN `s2:(C,FFI)bvl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN (CASE_TERM
    `?ck8 res8.
       bvl_evaluate ([d1],[],bvl_state_clock_fupd (K (bvl_state_clock t + ck8))
                                (t:(C,FFI)bvl_state)) = (res8,s2) /\
       (match r2 with Rval vs -> res8 = Rval [LAST vs] | Rerr v3 -> res8 = Rerr v3)`)
    MP_TAC THENL
   [MATCH_MP_TAC C2BP1AUX_chained_APPEND THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `ck8:num` (X_CHOOSE_THEN `res8:((bvl_v)list,bvl_v)result`
                STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`ck8:num`; `res8:((bvl_v)list,bvl_v)result`] THEN
  CASES_ON `r2:((bvl_v)list,bvl_v)result` THEN
  RULE_ASSUM_TAC (CASE_REWRITE_RULE[PAIR_EQ]) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[LAST] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[bvl_evaluate_IMP_LENGTH; LENGTH; LENGTH_EQ_NIL]]);;

(* HOL4 line 3307 [local] *)
let refs_lemma = prove
 (`!(t2:(A,B)bvl_state). bvl_state_refs_fupd (K (bvl_state_refs t2)) t2 = t2`,
  REWRITE_TAC[bvl_state_component_equality] THEN SIMP[]);;

let C2BP1AUX_FDIFF_SUBMAP_FUPDATE = prove
 (`!(a:(num,B)fmap) b s s' p w.
     FDIFF a s SUBMAP FDIFF b s' /\ ~(p IN FDOM b)
     ==> FDIFF a s SUBMAP FDIFF (b |+ (p,w)) s'`,
  REWRITE_TAC[SUBMAP_FLOOKUP_EQN; FLOOKUP_FDIFF; FLOOKUP_UPDATE] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPECL [`x:num`; `y:B`]) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[flookup_thm; option_DISTINCT]);;

let C2BP1AUX_ALL2_MAP_MAP = prove
 (`!(R:A->B->bool) (m1:num->A) m2 ns.
     (!k. R (m1 k) (m2 k)) ==> ALL2 R (MAP m1 ns) (MAP m2 ns)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_SIMP_TAC[MAP; ALL2]);;

let C2BP1AUX_do_part_step = prove
 (`!h (m1:num->clos_v) (m2:num->bvl_v) (t2:(C,FFI)bvl_state) x refs1 f2 p1 (f1:(num,num)fmap)
    (t1:(A,B)bvl_state).
     (!k. clos_to_bvlProof_v_rel (clos_state_max_app p1) f2 (bvl_state_refs t2)
            (bvl_state_code t2) (m1 k) (m2 k)) /\
     bvl_do_part m2 (update_tag h) (bvl_state_refs t2) = (x,refs1) /\
     clos_to_bvlProof_state_rel f2 p1 t2 /\
     FDIFF (bvl_state_refs t1) (FRANGE f1) SUBMAP FDIFF (bvl_state_refs t2) (FRANGE f2)
     ==> clos_to_bvlProof_v_rel (clos_state_max_app p1) f2 refs1 (bvl_state_code t2)
           (build_part' m1 h) x /\
         (!k. clos_to_bvlProof_v_rel (clos_state_max_app p1) f2 refs1 (bvl_state_code t2)
                (m1 k) (m2 k)) /\
         clos_to_bvlProof_state_rel f2 p1 (bvl_state_refs_fupd (K refs1) t2) /\
         FDIFF (bvl_state_refs t1) (FRANGE f1) SUBMAP FDIFF refs1 (FRANGE f2)`,
  GEN_TAC THEN CASES_ON `h:const_part` THEN
  REWRITE_TAC[update_tag_def; bvl_do_part_def; build_part'_def; PAIR_EQ; LET_DEF;
              LET_END_DEF] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[refs_lemma] THENL
   [MATCH_MP_TAC (el 2 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    MATCH_MP_TAC C2BP1AUX_ALL2_MAP_MAP THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[clos_to_bvlProof_v_rel_rules];
    ALL_TAC;
    REWRITE_TAC[clos_to_bvlProof_v_rel_rules]] THEN
  MP_TAC (ISPEC `bvl_state_refs (t2:(C,FFI)bvl_state)` LEAST_NOTIN_FDOM) THEN
  ABBREV_TAC `ptr = minimal ptr. ~(ptr IN FDOM (bvl_state_refs (t2:(C,FFI)bvl_state)))` THEN
  DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC (el 3 (CONJUNCTS clos_to_bvlProof_v_rel_rules)) THEN
    REWRITE_TAC[FLOOKUP_UPDATE] THEN
    UNDISCH_TAC `clos_to_bvlProof_state_rel f2 p1 (t2:(C,FFI)bvl_state)` THEN
    REWRITE_TAC[clos_to_bvlProof_state_rel_def; SUBSET] THEN ASM_MESON_TAC[];
    GEN_TAC THEN MATCH_MP_TAC v_rel_NEW_REF THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC state_rel_NEW_REF THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC C2BP1AUX_FDIFF_SUBMAP_FUPDATE THEN ASM_REWRITE_TAC[]]);;

let C2BP1AUX_do_build_gen = prove
 (`!parts (m1:num->clos_v) (m2:num->bvl_v) n (t2:(C,FFI)bvl_state) v rs f2 p1
    (f1:(num,num)fmap) (t1:(A,B)bvl_state).
     (!k. clos_to_bvlProof_v_rel (clos_state_max_app p1) f2 (bvl_state_refs t2)
            (bvl_state_code t2) (m1 k) (m2 k)) /\
     bvl_do_build m2 n (MAP update_tag parts) (bvl_state_refs t2) = (v,rs) /\
     clos_to_bvlProof_state_rel f2 p1 t2 /\
     FDIFF (bvl_state_refs t1) (FRANGE f1) SUBMAP FDIFF (bvl_state_refs t2) (FRANGE f2)
     ==> clos_to_bvlProof_v_rel (clos_state_max_app p1) f2 rs (bvl_state_code t2)
           (build' m1 n parts) v /\
         clos_to_bvlProof_state_rel f2 p1 (bvl_state_refs_fupd (K rs) t2) /\
         FDIFF (bvl_state_refs t1) (FRANGE f1) SUBMAP FDIFF rs (FRANGE f2)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAP; bvl_do_build_def; build'_def; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[refs_lemma];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[MAP; bvl_do_build_def; build'_def] THEN
  MP_TAC (ISPEC `bvl_do_part m2 (update_tag h) (bvl_state_refs (t2:(C,FFI)bvl_state))`
            PAIR_SURJECTIVE) THEN
  DISCH_THEN (X_CHOOSE_THEN `x:bvl_v` (X_CHOOSE_THEN `refs1:(num,(bvl_v)bvl_ref)fmap`
                ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  MP_TAC (SPECL [`h:const_part`; `m1:num->clos_v`; `m2:num->bvl_v`; `t2:(C,FFI)bvl_state`;
                 `x:bvl_v`; `refs1:(num,(bvl_v)bvl_ref)fmap`; `f2:(num,num)fmap`;
                 `p1:(C,FFI)clos_state`; `f1:(num,num)fmap`; `t1:(A,B)bvl_state`]
           C2BP1AUX_do_part_step) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`(n =+ build_part' m1 h) (m1:num->clos_v)`;
                                 `(n =+ x) (m2:num->bvl_v)`; `n + 1`;
                                 `bvl_state_refs_fupd (K refs1) (t2:(C,FFI)bvl_state)`;
                                 `v:bvl_v`; `rs:(num,(bvl_v)bvl_ref)fmap`; `f2:(num,num)fmap`;
                                 `p1:(C,FFI)clos_state`; `f1:(num,num)fmap`;
                                 `t1:(A,B)bvl_state`]) THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; bvl_state_INFO.ri_fupdfupds; K_THM; K_o_THM] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN REWRITE_TAC[APPLY_UPDATE_THM] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    SIMP_TAC[]]);;

(* HOL4 line 3313 (HOL4 f1 SUBMAP f2 is the finite map order; t1 is of     *)
(* any state type, as in HOL4) *)
let do_build_const_thm = prove
 (`!parts (t2:(C,FFI)bvl_state) v rs f2 p1 f1 (t1:(A,B)bvl_state).
     bvl_do_build_const (MAP update_tag parts) (bvl_state_refs t2) = (v,rs) /\
     clos_to_bvlProof_state_rel f2 p1 t2 /\ f1 SUBMAP f2 /\
     FDIFF (bvl_state_refs t1) (FRANGE f1) SUBMAP FDIFF (bvl_state_refs t2) (FRANGE f2)
     ==> ?f2'.
           clos_to_bvlProof_v_rel (clos_state_max_app p1) f2' rs (bvl_state_code t2)
             (build_const' parts) v /\
           clos_to_bvlProof_state_rel f2' p1 (bvl_state_refs_fupd (K rs) t2) /\
           f1 SUBMAP f2' /\
           FDIFF (bvl_state_refs t1) (FRANGE f1) SUBMAP FDIFF rs (FRANGE f2')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_build_const_def; build_const'_def] THEN STRIP_TAC THEN
  EXISTS_TAC `f2:(num,num)fmap` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C2BP1AUX_do_build_gen THEN
  EXISTS_TAC `\x:num. bvl_Number (&0)` THEN
  ASM_REWRITE_TAC[clos_to_bvlProof_v_rel_rules]);;

(* HOL4 line 3401 (closSem's dest_thunk on the left, bvlSem's on the right) *)
let rel_dest_thunk = prove
 (`!f (s:(C,FFI)clos_state) t h y m r1.
     clos_to_bvlProof_state_rel f s t /\
     clos_to_bvlProof_v_rel (clos_state_max_app s) f (bvl_state_refs t) (bvl_state_code t) h y /\
     clos_dest_thunk [h] (clos_state_refs s) = clos_IsThunk m r1
     ==> ?r2. bvl_dest_thunk y (bvl_state_refs t) = bvl_IsThunk m r2 /\
              clos_to_bvlProof_v_rel (clos_state_max_app s) f (bvl_state_refs t)
                (bvl_state_code t) r1 r2`,
  REPEAT GEN_TAC THEN CASES_ON `h:clos_v` THEN
  REWRITE_TAC[clos_dest_thunk_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[v_rel_SIMP] THEN
  EVERY_CASE_TAC THEN CASE_REWRITE_TAC[] THEN
  STRIP_TAC THEN RVEQ_TAC THEN IMP_RES_TAC state_rel_refs_lookup THEN
  GVS[bvl_dest_thunk_def]);;

(* HOL4 line 3419 *)
let rel_dest_thunk_NotThunk = prove
 (`!f (s:(C,FFI)clos_state) t h y.
     clos_to_bvlProof_state_rel f s t /\
     clos_to_bvlProof_v_rel (clos_state_max_app s) f (bvl_state_refs t) (bvl_state_code t) h y /\
     clos_dest_thunk [h] (clos_state_refs s) = clos_NotThunk
     ==> bvl_dest_thunk y (bvl_state_refs t) = bvl_NotThunk`,
  REPEAT GEN_TAC THEN CASES_ON `h:clos_v` THEN
  REWRITE_TAC[clos_dest_thunk_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[v_rel_SIMP] THEN
  TRY (EVERY_CASE_TAC THEN CASE_REWRITE_TAC[]) THEN
  STRIP_TAC THEN RVEQ_TAC THEN TRY (IMP_RES_TAC state_rel_refs_lookup) THEN
  GVS[bvl_dest_thunk_def]);;
