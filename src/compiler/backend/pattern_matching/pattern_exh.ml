(* ========================================================================= *)
(* pattern_exh: port of HOL4 compiler/backend/pattern_matching/              *)
(* pattern_exhScript.sml (CakeML v3479).                                     *)
(* An exhaustiveness checker for pattern-match rows, in the style of        *)
(* Maranget's usefulness algorithm, but using sibling annotations instead   *)
(* of a typing environment.                                                  *)
(*                                                                           *)
(* The entry point is exh_rows.  It first removes all Or-patterns by         *)
(* expanding each row into its Or-free variants, then decides whether the   *)
(* resulting one-column pattern matrix covers every value.                  *)
(*                                                                           *)
(* The matrix algorithm (exh_matrix) works on a matrix of pattern vectors.  *)
(* Looking at the first column it computes, from the sibling information in *)
(* the patterns, an over-approximation col_ctors of the set of constructors *)
(* a well-typed value can have there.                                       *)
(* - If that set is unknown (NONE) the matrix is exhaustive when the        *)
(*   default matrix is: only rows starting with a wildcard can match a      *)
(*   value whose constructor is not mentioned.                              *)
(* - If the set is known, the matrix is exhaustive when every specialised   *)
(*   matrix is: each constructor of the set is considered in turn, and its  *)
(*   arguments are pushed onto the front of the vector.                     *)
(* Only well-typed values matter, i.e. values for which no row of the       *)
(* original match yields PTypeFailure.  Since match walks every row and     *)
(* fails with NONE as soon as one row type-fails, all rows constrain the    *)
(* value simultaneously.  Hence the constructor set of a column is the      *)
(* intersection over the rows of the constructors each head pattern allows, *)
(* which is what col_ctors computes.                                         *)
(*                                                                           *)
(* Notes on the rendering: the pattern_semantics names carry their prefix   *)
(* (pattern_semantics_Any, pattern_semantics_pmatch, ...); EVERY is ALL and *)
(* EXISTS is EX; definitions with catch-all clauses or mutual recursion are *)
(* made with sem1aux_def(_wf) (semantics/sem1aux_tfl.ml).                    *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/pattern_matching/pattern_common.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "semantics/ast.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* Constructors of values.  A well-typed value at a given position is a     *)
(* tagged term (TagC: tag and arity of a Term (SOME tag)), an untagged term, *)
(* i.e. a tuple (TupC: arity of a Term NONE), or a reference (RefC: a       *)
(* RefPtr).  Literals are deliberately not constructors here: their type is *)
(* (for all practical purposes) infinite, so a column of literals is never a *)
(* complete signature.                                                       *)

let ctor_INDUCT,ctor_RECURSION = cake_type
  "ctor = TagC num num | TupC num | RefC";;

let ctor_arity_def = cake_def
  `(ctor_arity (TagC t a) = a) /\
   (ctor_arity (TupC a) = a) /\
   (ctor_arity RefC = 1)`;;

let anys_def = cake_def
  `(anys 0 = []) /\
   (anys (SUC n) = CONS pattern_semantics_Any (anys n))`;;

(* Removing Or-patterns.  expand p is the list of Or-free patterns p can be *)
(* split into.  Given that pmatch does not type-fail, p matches a value     *)
(* exactly when one of the patterns in expand p does.                        *)

let add_head_def = cake_def
  `(add_head (x:A) [] = []) /\
   (add_head x (CONS ys yss) = CONS (CONS x ys) (add_head x yss))`;;

let mk_prods_def = cake_def
  `(mk_prods [] (ys:(A list) list) = []) /\
   (mk_prods (CONS x xs) ys = APPEND (add_head x ys) (mk_prods xs ys))`;;

let mk_refs_def = cake_def
  `(mk_refs [] = []) /\
   (mk_refs (CONS p ps) = CONS (pattern_semantics_Ref p) (mk_refs ps))`;;

let mk_conses_def = cake_def
  `(mk_conses t [] = []) /\
   (mk_conses t (CONS ps pss) = CONS (pattern_semantics_Cons t ps) (mk_conses t pss))`;;

let expand_def = sem1aux_def_wf
  `measure (\x:pattern_semantics_pat + pattern_semantics_pat list.
              sum_CASE x pattern_semantics_pat_size
                         (list_size pattern_semantics_pat_size))`
  SEM1AUX_TC_TAC
  `(expand pattern_semantics_Any = [pattern_semantics_Any]) /\
   (expand (pattern_semantics_Lit l) = [pattern_semantics_Lit l]) /\
   (expand (pattern_semantics_Or p q) = APPEND (expand p) (expand q)) /\
   (expand (pattern_semantics_Ref p) = mk_refs (expand p)) /\
   (expand (pattern_semantics_Cons t ps) = mk_conses t (expand_list ps)) /\
   (expand_list [] = [[]]) /\
   (expand_list (CONS p ps) = mk_prods (expand p) (expand_list ps))`;;

let expand_ind = cake_ind "expand";;

let mk_rows_def = cake_def
  `(mk_rows [] = []) /\
   (mk_rows (CONS (p:pattern_semantics_pat) ps) = CONS [p] (mk_rows ps))`;;

let or_rows_def = cake_def
  `(or_rows [] = []) /\
   (or_rows (CONS (p,e:A) rows) = APPEND (mk_rows (expand p)) (or_rows rows))`;;

(* The constructors a head pattern allows a well-typed value to have.  NONE *)
(* means no information, i.e. every constructor is allowed.  Note that a     *)
(* missing sibling list (Cons (SOME (t,NONE)) _), which is how exceptions   *)
(* are encoded, gives no information, and neither does a literal pattern.   *)

let tag_ctors_def = cake_def
  `(tag_ctors [] = []) /\
   (tag_ctors (CONS (t,a) sibs) = CONS (TagC t a) (tag_ctors sibs))`;;

let ctor_nub_def = cake_def
  `(ctor_nub [] = []:A list) /\
   (ctor_nub (CONS x xs) = if MEM x xs then ctor_nub xs else CONS x (ctor_nub xs))`;;

let ctors_of_def = sem1aux_def
  `(ctors_of pattern_semantics_Any = NONE) /\
   (ctors_of (pattern_semantics_Lit _) = NONE) /\
   (ctors_of (pattern_semantics_Or _ _) = NONE) /\
   (ctors_of (pattern_semantics_Ref _) = SOME [RefC]) /\
   (ctors_of (pattern_semantics_Cons NONE qs) = SOME [TupC (LENGTH qs)]) /\
   (ctors_of (pattern_semantics_Cons (SOME (t,NONE)) qs) = NONE) /\
   (ctors_of (pattern_semantics_Cons (SOME (t,SOME sibs)) qs) =
      SOME (ctor_nub (CONS (TagC t (LENGTH qs)) (tag_ctors sibs))))`;;

let ctor_keep_def = cake_def
  `(ctor_keep [] (ys:A list) = []) /\
   (ctor_keep (CONS x xs) ys =
      if MEM x ys then CONS x (ctor_keep xs ys) else ctor_keep xs ys)`;;

let ctor_inter_def = cake_def_clauses
  [`ctor_inter (NONE:(A list) option) (ys:(A list) option) = ys`;
   `ctor_inter (xs:(A list) option) (NONE:(A list) option) = xs`;
   `ctor_inter (SOME (xs:A list)) (SOME ys) = SOME (ctor_keep xs ys)`];;

let col_ctors_def = cake_def
  `(col_ctors [] = NONE) /\
   (col_ctors (CONS [] rows) = col_ctors rows) /\
   (col_ctors (CONS (CONS p _) rows) = ctor_inter (ctors_of p) (col_ctors rows))`;;

let col_ctors_ind = cake_ind "col_ctors";;

(* a case split on a free variable of option or pair type of the goal *)
(* (HOL4: Cases_on o, PairCases_on ts, ...)                          *)

let IL1AUX_SPLIT_TAC : tactic = fun (asl,w as g) ->
  let vs = filter (fun v -> match dest_type(type_of v) with
                              ("option",_) | ("prod",_) -> true | _ -> false
                            | exception Failure _ -> false) (frees w) in
  if vs = [] then failwith "IL1AUX_SPLIT_TAC" else CASES_ON (hd vs) g;;

(* Specialised and default matrices.  spec_row c takes the rows that can    *)
(* match a value whose head constructor is c, and replaces the head pattern *)
(* by the patterns for the arguments of c.  default_row keeps only the rows *)
(* that start with a wildcard, dropping the head pattern.                    *)

let spec_row_def = sem1aux_def
  `(spec_row c [] = []) /\
   (spec_row c (CONS pattern_semantics_Any rest) =
      [APPEND (anys (ctor_arity c)) rest]) /\
   (spec_row c (CONS (pattern_semantics_Cons NONE qs) rest) =
      if c = TupC (LENGTH qs) then [APPEND qs rest] else []) /\
   (spec_row c (CONS (pattern_semantics_Cons (SOME ts) qs) rest) =
      if c = TagC (FST ts) (LENGTH qs) then [APPEND qs rest] else []) /\
   (spec_row c (CONS (pattern_semantics_Ref q) rest) =
      if c = RefC then [CONS q rest] else []) /\
   (spec_row c (CONS (pattern_semantics_Lit l) rest) = []) /\
   (spec_row c (CONS (pattern_semantics_Or p q) rest) = [])`;;

(* HOL4's spec_row_ind (the induction theorem of the completed clauses, a    *)
(* case split)                                                                *)

let spec_row_ind = prove
 (`!P:ctor->(pattern_semantics_pat)list->bool.
       (!c. P c []) /\
       (!c rest. P c (CONS pattern_semantics_Any rest)) /\
       (!c qs rest. P c (CONS (pattern_semantics_Cons NONE qs) rest)) /\
       (!c ts qs rest. P c (CONS (pattern_semantics_Cons (SOME ts) qs) rest)) /\
       (!c q rest. P c (CONS (pattern_semantics_Ref q) rest)) /\
       (!c l rest. P c (CONS (pattern_semantics_Lit l) rest)) /\
       (!c p q rest. P c (CONS (pattern_semantics_Or p q) rest))
       ==> !c r. P c r`,
  REPEAT STRIP_TAC THEN QCASES_ON "r" THEN ASM_REWRITE_TAC[] THEN
  QCASES_ON "a0" THEN REPEAT IL1AUX_SPLIT_TAC THEN ASM_REWRITE_TAC[]);;

let spec_mat_def = cake_def
  `(spec_mat c [] = []) /\
   (spec_mat c (CONS r rows) = APPEND (spec_row c r) (spec_mat c rows))`;;

let spec_mats_def = cake_def
  `(spec_mats [] rows = []) /\
   (spec_mats (CONS c cs) rows = CONS (spec_mat c rows) (spec_mats cs rows))`;;

let default_row_def = sem1aux_def
  `(default_row (CONS pattern_semantics_Any rest) = [rest]) /\
   (default_row _ = [])`;;

(* HOL4's default_row_ind (a case split) *)

let default_row_ind = prove
 (`!P:(pattern_semantics_pat)list->bool.
       (!rest. P (CONS pattern_semantics_Any rest)) /\ P [] /\
       (!a0 a1 rest. P (CONS (pattern_semantics_Cons a0 a1) rest)) /\
       (!p q rest. P (CONS (pattern_semantics_Or p q) rest)) /\
       (!l rest. P (CONS (pattern_semantics_Lit l) rest)) /\
       (!q rest. P (CONS (pattern_semantics_Ref q) rest))
       ==> !r. P r`,
  REPEAT STRIP_TAC THEN QCASES_ON "r" THEN ASM_REWRITE_TAC[] THEN
  QCASES_ON "a0" THEN ASM_REWRITE_TAC[]);;

let default_mat_def = cake_def
  `(default_mat [] = []) /\
   (default_mat (CONS r rows) = APPEND (default_row r) (default_mat rows))`;;

(* Measures used for the termination of exh_matrix.  Specialising strictly  *)
(* decreases the number of constructor nodes in the matrix, provided some   *)
(* head pattern is a constructor pattern, which is exactly what col_ctors   *)
(* returning SOME guarantees.  Taking the default matrix does not increase  *)
(* that count, and strictly decreases the total number of columns.          *)

let pat_weight_def = sem1aux_def_wf
  `measure (\x:pattern_semantics_pat + pattern_semantics_pat list.
              sum_CASE x pattern_semantics_pat_size
                         (list_size pattern_semantics_pat_size))`
  SEM1AUX_TC_TAC
  `(pat_weight pattern_semantics_Any = (0:num)) /\
   (pat_weight (pattern_semantics_Lit l) = 0) /\
   (pat_weight (pattern_semantics_Or p q) = 1 + pat_weight p + pat_weight q) /\
   (pat_weight (pattern_semantics_Ref p) = 1 + pat_weight p) /\
   (pat_weight (pattern_semantics_Cons t ps) = 1 + pats_weight ps) /\
   (pats_weight [] = 0) /\
   (pats_weight (CONS p ps) = pat_weight p + pats_weight ps)`;;

let pat_weight_ind = cake_ind "pat_weight";;

let mat_weight_def = cake_def
  `(mat_weight [] = 0) /\
   (mat_weight (CONS r rows) = pats_weight r + mat_weight rows)`;;

let mat_len_def = cake_def
  `(mat_len [] = 0) /\
   (mat_len (CONS (r:pattern_semantics_pat list) rows) = LENGTH r + mat_len rows)`;;

let mats_weight_def = cake_def
  `(mats_weight [] = 0) /\
   (mats_weight (CONS m ms) = MAX (mat_weight m) (mats_weight ms))`;;

let mats_len_def = cake_def
  `(mats_len [] = 0) /\
   (mats_len (CONS m ms) = MAX (mat_len m) (mats_len ms))`;;

let pats_weight_append = prove
 (`!xs ys. pats_weight (APPEND xs ys) = pats_weight xs + pats_weight ys`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; pat_weight_def] THEN ARITH_TAC);;

let pats_weight_anys = prove
 (`!n. pats_weight (anys n) = 0`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[anys_def; pat_weight_def; ADD_CLAUSES]);;

let mat_weight_append = prove
 (`!xs ys. mat_weight (APPEND xs ys) = mat_weight xs + mat_weight ys`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; mat_weight_def] THEN ARITH_TAC);;

let mat_len_append = prove
 (`!xs ys. mat_len (APPEND xs ys) = mat_len xs + mat_len ys`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; mat_len_def] THEN ARITH_TAC);;

let mat_weight_spec_row = prove
 (`!c r. mat_weight (spec_row c r) <= pats_weight r`,
  MATCH_MP_TAC spec_row_ind THEN
  RW[spec_row_def; mat_weight_def; pat_weight_def; pats_weight_append;
     pats_weight_anys] THEN ARITH_TAC);;

let mat_weight_spec_mat = prove
 (`!c rows. mat_weight (spec_mat c rows) <= mat_weight rows`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN FS[spec_mat_def; mat_weight_def; mat_weight_append] THEN
  MATCH_MP_TAC LE_ADD2 THEN FS[mat_weight_spec_row]);;

let mat_weight_spec_row_less = prove
 (`!c p r. ~(ctors_of p = NONE) ==>
           mat_weight (spec_row c (CONS p r)) < pats_weight (CONS p r)`,
  GEN_TAC THEN GEN_TAC THEN QCASES_ON "p" THEN REPEAT IL1AUX_SPLIT_TAC THEN
  RW[ctors_of_def; spec_row_def; mat_weight_def; pat_weight_def; pats_weight_append] THEN
  DECIDE_TAC);;

let mat_weight_spec_mat_less = prove
 (`!c rows cs. col_ctors rows = SOME cs ==>
               mat_weight (spec_mat c rows) < mat_weight rows`,
  GEN_TAC THEN MATCH_MP_TAC col_ctors_ind THEN
  RW[col_ctors_def; spec_mat_def; mat_weight_def; mat_weight_append] THENL
   [FS[spec_row_def; mat_weight_def; pat_weight_def] THEN RES_TAC;
    QSPECL_THEN ["c"; "rows"] MP_TAC mat_weight_spec_mat THEN
    QSPECL_THEN ["c"; "CONS p x"] MP_TAC mat_weight_spec_row THEN
    QSPECL_THEN ["c"; "p"; "x"] MP_TAC mat_weight_spec_row_less THEN
    QCASES_ON "ctors_of p" THEN FS[ctor_inter_def] THEN RES_TAC THEN DECIDE_TAC]);;

let mat_weight_default_mat = prove
 (`!rows. mat_weight (default_mat rows) <= mat_weight rows`,
  LIST_INDUCT_TAC THEN FS[default_mat_def; mat_weight_def; mat_weight_append] THEN
  QCASES_ON "h" THEN FS[default_row_def; mat_weight_def; pat_weight_def] THEN
  QCASES_ON "a0" THEN FS[default_row_def; mat_weight_def; pat_weight_def] THEN DECIDE_TAC);;

let mat_len_default_mat = prove
 (`!rows. mat_len (default_mat rows) <= mat_len rows`,
  LIST_INDUCT_TAC THEN FS[default_mat_def; mat_len_def; mat_len_append] THEN
  QCASES_ON "h" THEN FS[default_row_def; mat_len_def] THEN
  QCASES_ON "a0" THEN FS[default_row_def; mat_len_def] THEN DECIDE_TAC);;

let mats_weight_spec_mats = prove
 (`!cs rows ds.
     col_ctors rows = SOME ds ==>
     mats_weight (spec_mats cs rows) < mat_weight rows`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[spec_mats_def; mats_weight_def] THEN
  ASM_MESON_TAC[mat_weight_spec_mat_less; ARITH_RULE `a < c ==> 0 < c`;
                ARITH_RULE `a < c /\ b < c ==> MAX a b < c`]);;

let mat_len_default_mat_less = prove
 (`!r rows. ~(r = []) ==>
            mat_len (default_mat (CONS r rows)) < mat_len (CONS r rows)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN QSPEC_THEN "rows" MP_TAC mat_len_default_mat THEN
  QCASES_ON "r" THEN FS[default_mat_def; mat_len_def; mat_len_append] THEN
  QCASES_ON "a0" THEN FS[default_row_def; mat_len_def] THEN DECIDE_TAC);;

(* the termination conditions of exh_matrix and exh_steps (HOL4's proof):  *)
(* the lemmas about the weights of the default and specialised matrices at  *)
(* the matrices of the condition                                            *)

let IL1AUX_EXH_TC_TAC : tactic =
  RW(NULL_EQ :: WF_REL_THMS @ [mats_weight_def; mats_len_def; LENGTH; MAX]) THEN
  IMP_RES_TAC mats_weight_spec_mats THEN IMP_RES_TAC mat_len_default_mat_less THEN
  MP_TAC (ISPEC `CONS (r:pattern_semantics_pat list) rows` mat_weight_default_mat) THEN
  FS[] THEN DECIDE_TAC;;

let exh_matrix_def = sem1aux_def_wf
  `inv_image ((<) LEX (<) LEX (<))
     (\x:((pattern_semantics_pat)list)list +
         (((pattern_semantics_pat)list)list)list.
        sum_CASE x (\rows. (mat_weight rows, mat_len rows, 0))
                   (\ms. (mats_weight ms, mats_len ms, LENGTH ms + 1)))`
  IL1AUX_EXH_TC_TAC
  `(exh_matrix [] <=> F) /\
   (exh_matrix (CONS r rows) <=>
      if NULL r then T else
      match col_ctors (CONS r rows) with
        NONE -> exh_matrix (default_mat (CONS r rows))
      | SOME cs -> exh_mats (spec_mats cs (CONS r rows))) /\
   (exh_mats [] <=> T) /\
   (exh_mats (CONS m ms) <=> exh_matrix m /\ exh_mats ms)`;;

let exh_matrix_ind = cake_ind "exh_matrix";;

let exh_rows_def = cake_def
  `exh_rows (rows:(pattern_semantics_pat # A) list) <=>
     exh_matrix (or_rows rows)`;;

(* A tail-recursive version, for execution.  exh_matrix is a mutual        *)
(* recursion justified by a non-structural measure, which cv_translation    *)
(* cannot take.  exh_all is a single tail recursion that keeps the matrices *)
(* still to be checked in a worklist.  It computes exactly the same answer  *)
(* (exh_rows_eq below), so it is the equation the compiler is run through.  *)
(* Its termination is justified by counting the steps the original          *)
(* recursion takes: exh_steps has exactly the recursion structure of        *)
(* exh_matrix, hence exactly the same termination argument, and every step  *)
(* exh_all makes consumes one of those steps.                               *)

let exh_steps_def = sem1aux_def_wf
  `inv_image ((<) LEX (<) LEX (<))
     (\x:((pattern_semantics_pat)list)list +
         (((pattern_semantics_pat)list)list)list.
        sum_CASE x (\rows. (mat_weight rows, mat_len rows, 0))
                   (\ms. (mats_weight ms, mats_len ms, LENGTH ms + 1)))`
  IL1AUX_EXH_TC_TAC
  `(exh_steps [] = (1:num)) /\
   (exh_steps (CONS r rows) =
      if NULL r then 1 else
      match col_ctors (CONS r rows) with
        NONE -> 1 + exh_steps (default_mat (CONS r rows))
      | SOME cs -> 1 + exh_steps_list (spec_mats cs (CONS r rows))) /\
   (exh_steps_list [] = 0) /\
   (exh_steps_list (CONS m ms) = exh_steps m + exh_steps_list ms)`;;

let exh_steps_ind = cake_ind "exh_steps";;

let exh_steps_list_append = prove
 (`!xs ys. exh_steps_list (APPEND xs ys) = exh_steps_list xs + exh_steps_list ys`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; exh_steps_def] THEN ARITH_TAC);;

let exh_all_def = sem1aux_def_wf
  `measure exh_steps_list`
  (RW(WF_REL_THMS @ [exh_steps_def; exh_steps_list_append]))
  `(exh_all [] <=> T) /\
   (exh_all (CONS [] ms) <=> F) /\
   (exh_all (CONS (CONS r rows) ms) <=>
      if NULL r then exh_all ms else
      match col_ctors (CONS r rows) with
        NONE -> exh_all (CONS (default_mat (CONS r rows)) ms)
      | SOME cs -> exh_all (APPEND (spec_mats cs (CONS r rows)) ms))`;;

let exh_all_ind = cake_ind "exh_all";;

let exh_mats_append = prove
 (`!xs ys. exh_mats (APPEND xs ys) <=> exh_mats xs /\ exh_mats ys`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; exh_matrix_def; CONJ_ASSOC]);;

let exh_all_thm = prove
 (`!ms. exh_all ms <=> exh_mats ms`,
  MATCH_MP_TAC exh_all_ind THEN
  REWRITE_TAC[exh_all_def; exh_matrix_def] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  CASES_ON `col_ctors (CONS (r:(pattern_semantics_pat)list) rows)` THEN
  CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[exh_mats_append]);;

let exh_rows_eq = prove
 (`!rows:(pattern_semantics_pat # A) list.
     exh_rows rows <=> exh_all [or_rows rows]`,
  REWRITE_TAC[exh_rows_def; exh_all_thm; exh_matrix_def]);;

(* Soundness.  The theorem to prove is the one that justifies replacing the *)
(* last row by a wildcard:                                                   *)
(*   match refs rows v <> NONE /\ exh_rows rows ==>                          *)
(*   match refs rows v <> SOME MatchFailure                                  *)
(* Read through match_def that says: if no row type-fails on v, then some   *)
(* row succeeds on v.  Everything below is phrased in those terms, at the   *)
(* level of matrices: ok means no row type-fails, hit means some row        *)
(* succeeds.                                                                 *)

(* pand combines the results of two matches performed one after the other. *)
(* It is exactly how pmatch_list glues a row together, and it makes the     *)
(* case analysis below disappear into two rewrite rules.                    *)

let pand_def = cake_def
  `(pand PMatchSuccess y = y) /\
   (pand PMatchFailure y = if y = PTypeFailure then PTypeFailure else PMatchFailure) /\
   (pand PTypeFailure y = PTypeFailure)`;;

(* HOL4 [local,simp]: pand_simps, pand_eq_PTypeFailure,                    *)
(* pand_eq_PMatchSuccess, pmatch_Any, pmatch_list_nil, pmatch_list_cons,    *)
(* LENGTH_anys, pmatch_list_anys and the MEM_ lemmas are passed explicitly  *)
(* (IL1AUX_PE_SIMPS below)                                                   *)

let pand_simps = prove
 (`(!y. pand PMatchSuccess y = y) /\ (!x. pand x PMatchSuccess = x) /\
   (!y. pand PTypeFailure y = PTypeFailure) /\
   (!x. pand x PTypeFailure = PTypeFailure)`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN TRY (CASES_ON `x:pmatchResult`) THEN
  REWRITE_TAC[pand_def; distinctness "pmatchResult"]);;

let pand_eq_PTypeFailure = prove
 (`!x y. pand x y = PTypeFailure <=> x = PTypeFailure \/ y = PTypeFailure`,
  REPEAT GEN_TAC THEN CASES_ON `x:pmatchResult` THEN CASES_ON `y:pmatchResult` THEN
  REWRITE_TAC[pand_def; distinctness "pmatchResult"]);;

let pand_eq_PMatchSuccess = prove
 (`!x y. pand x y = PMatchSuccess <=> x = PMatchSuccess /\ y = PMatchSuccess`,
  REPEAT GEN_TAC THEN CASES_ON `x:pmatchResult` THEN CASES_ON `y:pmatchResult` THEN
  REWRITE_TAC[pand_def; distinctness "pmatchResult"]);;

let pand_assoc = prove
 (`!x y z. pand (pand x y) z = pand x (pand y z)`,
  REPEAT GEN_TAC THEN CASES_ON `x:pmatchResult` THEN CASES_ON `y:pmatchResult` THEN
  CASES_ON `z:pmatchResult` THEN REWRITE_TAC[pand_def; distinctness "pmatchResult"]);;

(* From here on pmatch_list is only ever unfolded through these four        *)
(* rewrites, never through pmatch_def: the raw clauses of pmatch_def would  *)
(* compete with pmatch_list_cons and leave case expressions behind.          *)

let pmatch_Any = prove
 (`!refs v. pattern_semantics_pmatch refs pattern_semantics_Any v = PMatchSuccess`,
  REWRITE_TAC[pattern_semantics_pmatch_def]);;

let pmatch_list_nil = prove
 (`(!refs. pattern_semantics_pmatch_list refs [] [] = PMatchSuccess) /\
   (!refs v vs. pattern_semantics_pmatch_list refs [] (CONS v vs) = PTypeFailure) /\
   (!refs p ps. pattern_semantics_pmatch_list refs (CONS p ps) [] = PTypeFailure)`,
  REWRITE_TAC[pattern_semantics_pmatch_def]);;

let pmatch_list_cons = prove
 (`!refs p ps v vs.
     pattern_semantics_pmatch_list refs (CONS p ps) (CONS v vs) =
     pand (pattern_semantics_pmatch refs p v)
          (pattern_semantics_pmatch_list refs ps vs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pattern_semantics_pmatch_def] THEN
  CASES_ON `pattern_semantics_pmatch refs p v` THEN
  CASE_REWRITE_TAC[pand_def] THEN
  CASES_ON `pattern_semantics_pmatch_list refs ps vs` THEN
  CASE_REWRITE_TAC[distinctness "pmatchResult"]);;

let IL1AUX_PE_SIMPS = [pand_simps; pand_eq_PTypeFailure; pand_eq_PMatchSuccess;
                       pmatch_Any; pmatch_list_nil; pmatch_list_cons];;

(* HOL4: pmatch_list_LENGTH *)

let pattern_exh_pmatch_list_LENGTH = prove
 (`!refs ps vs. ~(pattern_semantics_pmatch_list refs ps vs = PTypeFailure) ==>
                LENGTH ps = LENGTH vs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC(LENGTH :: SUC_INJ :: IL1AUX_PE_SIMPS) THEN
  ASM_MESON_TAC[]);;

(* HOL4: pmatch_list_append *)

let pattern_exh_pmatch_list_append = prove
 (`!ps us qs ws refs.
     LENGTH ps = LENGTH us ==>
     pattern_semantics_pmatch_list refs (APPEND ps qs) (APPEND us ws) =
     pand (pattern_semantics_pmatch_list refs ps us)
          (pattern_semantics_pmatch_list refs qs ws)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC([LENGTH; NOT_SUC; SUC_INJ; APPEND; pand_assoc] @ IL1AUX_PE_SIMPS) THEN
  ASM_SIMP_TAC[pand_assoc]);;

let LENGTH_anys = prove
 (`!n. LENGTH (anys n) = n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[anys_def; LENGTH]);;

(* Stated with the width as an argument rather than as LENGTH as, so that  *)
(* it also rewrites the anys (ctor_arity c) that spec_row produces.         *)

let pmatch_list_anys = prove
 (`!n as refs.
     pattern_semantics_pmatch_list refs (anys n) as =
     (if LENGTH as = n then PMatchSuccess else PTypeFailure)`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC([anys_def; LENGTH; NOT_SUC; SUC_INJ; GSYM NOT_SUC] @ IL1AUX_PE_SIMPS) THEN
  COND_CASES_TAC THEN REWRITE_TAC IL1AUX_PE_SIMPS);;

(* What the first-order list-building helpers put into their results. *)

let MEM_ctor_nub = prove
 (`!l (x:A). MEM x (ctor_nub l) <=> MEM x l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ctor_nub_def; MEM] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MEM] THEN ASM_MESON_TAC[]);;

let MEM_ctor_keep = prove
 (`!xs (ys:A list) x. MEM x (ctor_keep xs ys) <=> MEM x xs /\ MEM x ys`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ctor_keep_def; MEM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MEM] THEN
  ASM_MESON_TAC[]);;

let MEM_tag_ctors = prove
 (`!sibs t a. MEM (TagC t a) (tag_ctors sibs) <=> MEM (t,a) sibs`,
  MATCH_MP_TAC list_INDUCT THEN FS[tag_ctors_def; FORALL_PAIR_THM] THEN MESON_TAC[]);;

let MEM_spec_mats = prove
 (`!cs c rows. MEM c cs ==> MEM (spec_mat c rows) (spec_mats cs rows)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[spec_mats_def; MEM] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

let MEM_add_head = prove
 (`!yss (x:A) ys. MEM ys (add_head x yss) <=> ?zs. MEM zs yss /\ ys = CONS x zs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[add_head_def; MEM] THEN MESON_TAC[]);;

let MEM_mk_prods = prove
 (`!xs (yss:(A list) list) zs.
     MEM zs (mk_prods xs yss) <=> ?x ys. MEM x xs /\ MEM ys yss /\ zs = CONS x ys`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[mk_prods_def; MEM; MEM_APPEND; MEM_add_head] THEN
  MESON_TAC[]);;

let MEM_mk_refs = prove
 (`!ps q. MEM q (mk_refs ps) <=> ?p. MEM p ps /\ q = pattern_semantics_Ref p`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[mk_refs_def; MEM] THEN MESON_TAC[]);;

let MEM_mk_conses = prove
 (`!pss t q. MEM q (mk_conses t pss) <=> ?ps. MEM ps pss /\ q = pattern_semantics_Cons t ps`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[mk_conses_def; MEM] THEN MESON_TAC[]);;

let MEM_mk_rows = prove
 (`!ps r. MEM r (mk_rows ps) <=> ?p. MEM p ps /\ r = [p]`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[mk_rows_def; MEM] THEN MESON_TAC[]);;

(* Expanding Or-patterns.  An expanded pattern never type-fails where the  *)
(* original does not, and if an expanded pattern matches then so does the   *)
(* original.  (The converse also holds, but soundness does not need it.)    *)

let LENGTH_expand_list = prove
 (`!ps qs. MEM qs (expand_list ps) ==> LENGTH qs = LENGTH ps`,
  LIST_INDUCT_TAC THEN FS[expand_def; MEM_mk_prods] THEN RW[] THEN RES_TAC THEN FS[]);;

let expand_thm = prove
 (`(!p q refs v.
      MEM q (expand p) /\ ~(pattern_semantics_pmatch refs p v = PTypeFailure) ==>
      ~(pattern_semantics_pmatch refs q v = PTypeFailure) /\
      (pattern_semantics_pmatch refs q v = PMatchSuccess ==>
       pattern_semantics_pmatch refs p v = PMatchSuccess)) /\
   (!ps qs refs vs.
      MEM qs (expand_list ps) /\
      ~(pattern_semantics_pmatch_list refs ps vs = PTypeFailure) ==>
      ~(pattern_semantics_pmatch_list refs qs vs = PTypeFailure) /\
      (pattern_semantics_pmatch_list refs qs vs = PMatchSuccess ==>
       pattern_semantics_pmatch_list refs ps vs = PMatchSuccess))`,
  MATCH_MP_TAC pattern_semantics_pat_INDUCT THEN REPEAT CONJ_TAC THENL
   [(* Any *)
    FS[expand_def];
    (* Cons *)
    GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN QCASES_ON "v" THEN
    REPEAT IL1AUX_SPLIT_TAC THEN RW[expand_def; MEM_mk_conses] THEN
    IMP_RES_TAC LENGTH_expand_list THEN
    GVS[pattern_semantics_pmatch_def; COND_CASE_EQ] THEN RES_TAC THEN FS[];
    (* Or: both branches must be free of type failures, and once that is *)
    (* known the induction hypotheses apply directly                       *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(pattern_semantics_pmatch refs a0 v = PTypeFailure) /\
                  ~(pattern_semantics_pmatch refs a1 v = PTypeFailure)`
      STRIP_ASSUME_TAC THENL
     [QPAT_X_ASSUM "~(pattern_semantics_pmatch refs (pattern_semantics_Or _ _) _ = _)"
        MP_TAC THEN
      FS[pattern_semantics_pmatch_def] THEN EVERY_CASE_TAC THEN FS[];
      ALL_TAC] THEN
    FS[expand_def; MEM_APPEND] THEN RES_TAC THEN FS[pattern_semantics_pmatch_def] THEN
    (* the induction hypotheses are used: without them FS is much cheaper *)
    REPEAT (FIRST_X_ASSUM (K ALL_TAC o check (is_forall o concl))) THEN
    CASES_ON `pattern_semantics_pmatch refs a0 v` THEN
    CASES_ON `pattern_semantics_pmatch refs a1 v` THEN FS[];
    (* Lit *)
    FS[expand_def];
    (* Ref *)
    FS[expand_def; MEM_mk_refs] THEN RW[] THEN QCASES_ON "v" THEN
    FS[pattern_semantics_pmatch_def] THEN EVERY_CASE_TAC THEN FS[] THEN RES_TAC THEN FS[];
    (* [] *)
    FS[expand_def];
    (* p::ps *)
    FS[expand_def; MEM_mk_prods] THEN RW[] THEN QCASES_ON "vs" THEN
    FS(DE_MORGAN_THM :: IL1AUX_PE_SIMPS) THEN RES_TAC THEN FS[]]);;

(* The constructor of a value, and its arguments.  dest_val is only defined *)
(* for the values that a constructor pattern can possibly match; literals   *)
(* and Other have no constructor.  Note that a reference has a constructor  *)
(* only when the pointer is in the heap, which is exactly when Ref does not *)
(* type-fail.                                                                *)

let dest_val_def = cake_def
  `(dest_val (refs:(num,term)fmap) (Term (SOME t) vs) =
      SOME (TagC t (LENGTH vs), vs)) /\
   (dest_val refs (Term NONE vs) = SOME (TupC (LENGTH vs), vs)) /\
   (dest_val refs (pattern_semantics_RefPtr r) =
      match FLOOKUP refs r with
        NONE -> NONE
      | SOME w -> SOME (RefC,[w])) /\
   (dest_val refs (pattern_semantics_Litv l) = NONE) /\
   (dest_val refs pattern_semantics_Other = NONE)`;;

let dest_val_eq_SOME = prove
 (`!refs v c as.
     dest_val refs v = SOME (c,as) <=>
     (?t. v = Term (SOME t) as /\ c = TagC t (LENGTH as)) \/
     (v = Term NONE as /\ c = TupC (LENGTH as)) \/
     (?r w. v = pattern_semantics_RefPtr r /\ FLOOKUP refs r = SOME w /\
            as = [w] /\ c = RefC)`,
  REPEAT GEN_TAC THEN QCASES_ON "v" THEN FS[dest_val_def] THEN REPEAT IL1AUX_SPLIT_TAC THEN
  FS[dest_val_def] THEN TRY CASE_TAC THEN FS[] THEN MESON_TAC[]);;

let LENGTH_dest_val = prove
 (`!refs v c as. dest_val refs v = SOME (c,as) ==> LENGTH as = ctor_arity c`,
  RW[dest_val_eq_SOME] THEN RW[ctor_arity_def]);;

(* A head pattern that reports a constructor set really does confine a      *)
(* value that it does not type-fail on to that set.                          *)

let ctors_of_thm = prove
 (`!p xs refs v.
     ctors_of p = SOME xs /\ ~(pattern_semantics_pmatch refs p v = PTypeFailure) ==>
     ?c as. dest_val refs v = SOME (c,as) /\ MEM c xs`,
  REPEAT GEN_TAC THEN QCASES_ON "p" THEN QCASES_ON "v" THEN REPEAT IL1AUX_SPLIT_TAC THEN
  FS[ctors_of_def] THEN RW[] THEN FS[pattern_semantics_pmatch_def; dest_val_def] THEN
  EVERY_CASE_TAC THEN FS[MEM_ctor_nub; MEM_tag_ctors; is_sibling_def] THEN
  IMP_RES_TAC pattern_exh_pmatch_list_LENGTH THEN FS[]);;

(* ... and therefore so does the intersection over a whole column. *)

let col_ctors_thm = prove
 (`!M cs refs v vs.
     col_ctors M = SOME cs /\
     ALL (\r. ~(pattern_semantics_pmatch_list refs r (CONS v vs) = PTypeFailure)) M ==>
     ?c as. dest_val refs v = SOME (c,as) /\ MEM c cs`,
  MATCH_MP_TAC col_ctors_ind THEN RW(col_ctors_def :: DE_MORGAN_THM :: IL1AUX_PE_SIMPS) THEN
  QCASES_ON "ctors_of p" THEN FS[ctor_inter_def] THENL
   [RES_TAC THEN FS[];
    DRULE_ALL ctors_of_thm THEN STRIP_TAC THEN
    QCASES_ON "col_ctors rows" THEN FS[ctor_inter_def] THEN RES_TAC THEN GVS[MEM_ctor_keep]]);;

(* Specialising and defaulting preserve match results: every row of a       *)
(* transformed matrix gives the same three-valued match result, against the *)
(* transformed value vector, as the row it came from does against the       *)
(* original one.                                                              *)

(* the clauses of pattern_semantics_pmatch (without those of                  *)
(* pattern_semantics_pmatch_list, which are used as pmatch_list_cons)          *)

let IL1AUX_PMATCH_CLAUSES =
  filter (fun th -> fst(dest_const(fst(strip_comb(lhs(snd(strip_forall(concl th)))))))
                    = "pattern_semantics_pmatch")
         (CONJUNCTS pattern_semantics_pmatch_def);;

let spec_row_thm = prove
 (`!c r row refs v vs as.
     dest_val refs v = SOME (c,as) /\ MEM row (spec_row c r) ==>
     pattern_semantics_pmatch_list refs row (APPEND as vs) =
     pattern_semantics_pmatch_list refs r (CONS v vs)`,
  MATCH_MP_TAC spec_row_ind THEN RW[spec_row_def] THEN
  TRY (PAIR_CASES_ON `ts:num # ((num # num) list) option`) THEN
  IMP_RES_TAC LENGTH_dest_val THEN
  GVS([dest_val_eq_SOME; pattern_exh_pmatch_list_append; ctor_arity_def; LENGTH_anys;
       pmatch_list_anys] @ IL1AUX_PMATCH_CLAUSES @ IL1AUX_PE_SIMPS) THEN
  EVERY_CASE_TAC THEN FS[pand_def]);;

let spec_mat_MEM = prove
 (`!M c as refs v vs row.
     dest_val refs v = SOME (c,as) /\ MEM row (spec_mat c M) ==>
     ?r. MEM r M /\
         pattern_semantics_pmatch_list refs row (APPEND as vs) =
         pattern_semantics_pmatch_list refs r (CONS v vs)`,
  LIST_INDUCT_TAC THEN FS[spec_mat_def; MEM_APPEND] THEN RW[] THENL
   [DRULE_ALL spec_row_thm THEN MESON_TAC[MEM];
    RES_TAC THEN ASM_MESON_TAC[MEM]]);;

let default_row_thm = prove
 (`!r row refs v vs.
     MEM row (default_row r) ==>
     pattern_semantics_pmatch_list refs row vs =
     pattern_semantics_pmatch_list refs r (CONS v vs)`,
  MATCH_MP_TAC default_row_ind THEN RW(default_row_def :: IL1AUX_PE_SIMPS));;

let default_mat_MEM = prove
 (`!M refs v vs row.
     MEM row (default_mat M) ==>
     ?r. MEM r M /\
         pattern_semantics_pmatch_list refs row vs =
         pattern_semantics_pmatch_list refs r (CONS v vs)`,
  LIST_INDUCT_TAC THEN FS[default_mat_def; MEM_APPEND] THEN RW[] THENL
   [DRULE default_row_thm THEN MESON_TAC[MEM];
    RES_TAC THEN ASM_MESON_TAC[MEM]]);;

(* Soundness of the matrix algorithm: "ok" (no row type-fails) is          *)
(* inherited by the sub-matrices, and "hit" (some row succeeds) is          *)
(* reflected back out of them.                                               *)

let exh_matrix_thm = prove
 (`(!M refs vs.
      exh_matrix M /\
      ALL (\r. ~(pattern_semantics_pmatch_list refs r vs = PTypeFailure)) M ==>
      EX (\r. pattern_semantics_pmatch_list refs r vs = PMatchSuccess) M) /\
   (!ms m refs vs.
      exh_mats ms /\ MEM m ms /\
      ALL (\r. ~(pattern_semantics_pmatch_list refs r vs = PTypeFailure)) m ==>
      EX (\r. pattern_semantics_pmatch_list refs r vs = PMatchSuccess) m)`,
  MATCH_MP_TAC exh_matrix_ind THEN REPEAT CONJ_TAC THENL
   [(* the empty matrix is never accepted *)
    FS[exh_matrix_def];
    ALL_TAC;
    FS[];
    FS[exh_matrix_def] THEN RW[] THEN FS[] THEN RES_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  QPAT_X_ASSUM "exh_matrix _" MP_TAC THEN SIMP[ONCE exh_matrix_def] THEN
  ASM_CASES_TAC `NULL (r:(pattern_semantics_pat)list)` THEN FS[] THENL
   [(* a row of width zero: the value vector must be empty too, and then  *)
    (* that row matches                                                     *)
    QCASES_ON "r" THEN FS[] THEN QCASES_ON "vs" THEN FS IL1AUX_PE_SIMPS;
    ALL_TAC] THEN
  SUBGOAL_THEN `?v vs'. vs = CONS (v:term) vs'` STRIP_ASSUME_TAC THENL
   [QCASES_ON "vs" THEN FS[] THEN QCASES_ON "r" THEN FS IL1AUX_PE_SIMPS; ALL_TAC] THEN
  GVS[] THEN QCASES_ON "col_ctors (CONS r rows)" THEN FS[] THEN STRIP_TAC THENL
   [(* nothing is known about the column, so only the wildcard rows can be *)
    (* relied on: work in the default matrix                                *)
    FIRST_X_ASSUM (QSPECL_THEN ["refs"; "vs'"] MP_TAC) THEN ANTS_TAC THENL
     [FS[GSYM ALL_MEM] THEN RW[] THEN DRULE default_mat_MEM THEN
      DISCH_THEN (QSPECL_THEN ["refs"; "v"; "vs'"] STRIP_ASSUME_TAC) THEN GVS[] THEN
      RES_TAC THEN FS[];
      FS[GSYM EX_MEM] THEN RW[] THEN DRULE default_mat_MEM THEN
      DISCH_THEN (QSPECL_THEN ["refs"; "v"; "vs'"] STRIP_ASSUME_TAC) THEN GVS[] THEN
      ASM_MESON_TAC[]];
    (* the column's constructors are known, so the value has one of them:  *)
    (* work in the matrix specialised for it                                *)
    SUBGOAL_THEN `ALL (\r. ~(pattern_semantics_pmatch_list refs r (CONS v vs') =
                             PTypeFailure)) (CONS r rows)` ASSUME_TAC THENL
     [FS[]; ALL_TAC] THEN
    DRULE_ALL col_ctors_thm THEN STRIP_TAC THEN
    FIRST_X_ASSUM (QSPECL_THEN ["spec_mat c (CONS r rows)"; "refs"; "APPEND as vs'"] MP_TAC) THEN
    ANTS_TAC THENL
     [FS[MEM_spec_mats; GSYM ALL_MEM] THEN RW[] THEN DRULE_ALL spec_mat_MEM THEN
      DISCH_THEN (QSPEC_THEN "vs'" STRIP_ASSUME_TAC) THEN GVS[] THEN RES_TAC THEN FS[];
      FS[GSYM EX_MEM] THEN RW[] THEN DRULE_ALL spec_mat_MEM THEN
      DISCH_THEN (QSPEC_THEN "vs'" STRIP_ASSUME_TAC) THEN GVS[] THEN ASM_MESON_TAC[]]]);;

(* From the matrix back to match. *)

let match_no_PTypeFailure = prove
 (`!rows:(pattern_semantics_pat # num) list.
     ~(pattern_semantics_match refs rows v = NONE) ==>
     ALL (\(p,e). ~(pattern_semantics_pmatch refs p v = PTypeFailure)) rows`,
  MATCH_MP_TAC list_INDUCT THEN FS[pattern_semantics_match_def; FORALL_PAIR_THM] THEN RW[] THEN
  CASES_ON `pattern_semantics_pmatch refs p1 v` THEN FS[] THEN EVERY_CASE_TAC THEN FS[]);;

let match_EXISTS = prove
 (`!rows:(pattern_semantics_pat # num) list.
     ~(pattern_semantics_match refs rows v = NONE) /\
     EX (\(p,e). pattern_semantics_pmatch refs p v = PMatchSuccess) rows ==>
     ~(pattern_semantics_match refs rows v = SOME MatchFailure)`,
  MATCH_MP_TAC list_INDUCT THEN FS[pattern_semantics_match_def; FORALL_PAIR_THM] THEN RW[] THEN
  CASES_ON `pattern_semantics_pmatch refs p1 v` THEN FS[] THEN EVERY_CASE_TAC THEN FS[]);;

let or_rows_ok = prove
 (`!rows:(pattern_semantics_pat # A) list.
     ALL (\(p,e). ~(pattern_semantics_pmatch refs p v = PTypeFailure)) rows ==>
     ALL (\r. ~(pattern_semantics_pmatch_list refs r [v] = PTypeFailure))
         (or_rows rows)`,
  MATCH_MP_TAC list_INDUCT THEN FS[or_rows_def; FORALL_PAIR_THM; ALL_APPEND] THEN RW[] THEN
  FS[GSYM ALL_MEM; MEM_mk_rows] THEN RW[] THEN FS IL1AUX_PE_SIMPS THEN
  DRULE_ALL (CONJUNCT1 expand_thm) THEN FS[]);;

let or_rows_hit = prove
 (`!rows:(pattern_semantics_pat # A) list.
     ALL (\(p,e). ~(pattern_semantics_pmatch refs p v = PTypeFailure)) rows /\
     EX (\r. pattern_semantics_pmatch_list refs r [v] = PMatchSuccess)
        (or_rows rows) ==>
     EX (\(p,e). pattern_semantics_pmatch refs p v = PMatchSuccess) rows`,
  MATCH_MP_TAC list_INDUCT THEN FS[or_rows_def; FORALL_PAIR_THM; EXISTS_APPEND] THEN RW[] THEN
  FS[GSYM EX_MEM; MEM_mk_rows] THEN RW[] THEN FS IL1AUX_PE_SIMPS THEN
  DRULE_ALL (CONJUNCT1 expand_thm) THEN FS[]);;

(* Soundness of exh_rows: the theorem the pattern compiler needs. *)

let exh_rows_thm = prove
 (`~(pattern_semantics_match refs rows v = NONE) /\ exh_rows rows ==>
   ~(pattern_semantics_match refs rows v = SOME MatchFailure)`,
  STRIP_TAC THEN IRULE match_EXISTS THEN FS[] THEN DRULE match_no_PTypeFailure THEN
  STRIP_TAC THEN IRULE or_rows_hit THEN FS[] THEN IRULE (CONJUNCT1 exh_matrix_thm) THEN
  FS[or_rows_ok] THEN FS[exh_rows_def]);;
