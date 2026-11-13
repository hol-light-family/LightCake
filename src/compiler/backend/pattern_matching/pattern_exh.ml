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
  GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC (ISPEC `h:pattern_semantics_pat`
                      (nchotomy_of_type `:pattern_semantics_pat`)) THEN
  ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC (ISPEC `a0:((num # ((num # num) list) option) option)`
                      (nchotomy_of_type `:(num # ((num # num) list) option) option`)) THEN
  ASM_REWRITE_TAC[]);;

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
  GEN_TAC THEN STRIP_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC (ISPEC `h:pattern_semantics_pat`
                      (nchotomy_of_type `:pattern_semantics_pat`)) THEN
  ASM_REWRITE_TAC[]);;

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
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[spec_mat_def; mat_weight_def; mat_weight_append; LE_REFL] THEN
  MP_TAC (SPECL [`c:ctor`; `h:(pattern_semantics_pat)list`] mat_weight_spec_row) THEN
  ASM_ARITH_TAC);;

(* a case split on a free variable of option or pair type of the goal *)
(* (HOL4: Cases_on o, PairCases_on ts, ...)                          *)

let IL1AUX_SPLIT_TAC : tactic = fun (asl,w as g) ->
  let vs = filter (fun v -> match dest_type(type_of v) with
                              ("option",_) | ("prod",_) -> true | _ -> false
                            | exception Failure _ -> false) (frees w) in
  if vs = [] then failwith "IL1AUX_SPLIT_TAC" else CASES_ON (hd vs) g;;

let mat_weight_spec_row_less = prove
 (`!c p r. ~(ctors_of p = NONE) ==>
           mat_weight (spec_row c (CONS p r)) < pats_weight (CONS p r)`,
  GEN_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `p:pattern_semantics_pat`
                      (nchotomy_of_type `:pattern_semantics_pat`)) THEN
  REPEAT IL1AUX_SPLIT_TAC THEN
  RW[ctors_of_def; spec_row_def; mat_weight_def; pat_weight_def;
     pats_weight_append] THEN ARITH_TAC);;
let mat_weight_spec_mat_less = prove
 (`!c rows cs. col_ctors rows = SOME cs ==>
               mat_weight (spec_mat c rows) < mat_weight rows`,
  GEN_TAC THEN MATCH_MP_TAC col_ctors_ind THEN
  REWRITE_TAC[col_ctors_def; spec_mat_def; mat_weight_def; mat_weight_append;
              distinctness "option"] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[spec_row_def; mat_weight_def; pat_weight_def; ADD_CLAUSES] THEN
    RES_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`p:pattern_semantics_pat`;
                         `qs:(pattern_semantics_pat)list`;
                         `rows:((pattern_semantics_pat)list)list`] THEN
    DISCH_TAC THEN GEN_TAC THEN
    MP_TAC (SPECL [`c:ctor`; `p:pattern_semantics_pat`;
                   `qs:(pattern_semantics_pat)list`] mat_weight_spec_row_less) THEN
    MP_TAC (SPECL [`c:ctor`; `CONS (p:pattern_semantics_pat) qs`]
                  mat_weight_spec_row) THEN
    MP_TAC (SPECL [`c:ctor`; `rows:((pattern_semantics_pat)list)list`]
                  mat_weight_spec_mat) THEN
    CASES_ON `ctors_of p` THEN
    CASES_ON `col_ctors rows` THEN
    REWRITE_TAC[ctor_inter_def; distinctness "option"] THEN
    REPEAT DISCH_TAC THEN RES_TAC THEN ASM_ARITH_TAC]);;
let mat_weight_default_mat = prove
 (`!rows. mat_weight (default_mat rows) <= mat_weight rows`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[default_mat_def; mat_weight_def; mat_weight_append; LE_REFL] THEN
  MATCH_MP_TAC (ARITH_RULE `a <= b /\ c <= d ==> a + c <= b + d:num`) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`h:(pattern_semantics_pat)list`,`r:(pattern_semantics_pat)list`) THEN
  MATCH_MP_TAC default_row_ind THEN
  REWRITE_TAC[default_row_def; mat_weight_def; pat_weight_def] THEN ARITH_TAC);;

let mat_len_default_mat = prove
 (`!rows. mat_len (default_mat rows) <= mat_len rows`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[default_mat_def; mat_len_def; mat_len_append; LE_REFL] THEN
  MATCH_MP_TAC (ARITH_RULE `a <= b /\ c <= d ==> a + c <= b + d:num`) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`h:(pattern_semantics_pat)list`,`r:(pattern_semantics_pat)list`) THEN
  MATCH_MP_TAC default_row_ind THEN
  REWRITE_TAC[default_row_def; mat_len_def; LENGTH] THEN ARITH_TAC);;

let mats_weight_spec_mats = prove
 (`!cs rows ds.
     col_ctors rows = SOME ds ==>
     mats_weight (spec_mats cs rows) < mat_weight rows`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[spec_mats_def; mats_weight_def] THEN
  REPEAT STRIP_TAC THENL
   [MP_TAC (SPECL [`RefC`; `rows:((pattern_semantics_pat)list)list`;
                   `ds:ctor list`] mat_weight_spec_mat_less) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    MP_TAC (SPECL [`h:ctor`; `rows:((pattern_semantics_pat)list)list`;
                   `ds:ctor list`] mat_weight_spec_mat_less) THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`rows:((pattern_semantics_pat)list)list`;
                                   `ds:ctor list`]) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[MAX] THEN ARITH_TAC]);;

let mat_len_default_mat_less = prove
 (`!r rows. ~(r = []) ==>
            mat_len (default_mat (CONS r rows)) < mat_len (CONS r rows)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (SPEC `rows:((pattern_semantics_pat)list)list` mat_len_default_mat) THEN
  REWRITE_TAC[default_mat_def; mat_len_def; mat_len_append] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`r:(pattern_semantics_pat)list`,`r:(pattern_semantics_pat)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  STRUCT_CASES_TAC (ISPEC `h:pattern_semantics_pat`
                      (nchotomy_of_type `:pattern_semantics_pat`)) THEN
  REWRITE_TAC[default_row_def; mat_len_def; LENGTH] THEN ARITH_TAC);;

(* the termination conditions of exh_matrix and exh_steps (HOL4's proof):  *)
(* the lemmas about the weights of the default and specialised matrices at  *)
(* the matrices of the condition                                            *)

let IL1AUX_EXH_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  REPEAT (FIRST_X_ASSUM (K ALL_TAC o check (fun th ->
    is_neg (concl th) && is_exists (dest_neg (concl th))))) THEN
  REWRITE_TAC(WF_REL_THMS @ [sum_CASE; FST; SND]) THEN
  (fun (asl,w as g) ->
     let find_app c n =
       find_term (fun t -> try let h,args = strip_comb t in
                               fst(dest_const h) = c && length args = n
                           with Failure _ -> false) w in
     let tac1 = try let rr = rand (find_app "default_mat" 1) in
                    let r,rows = dest_cons rr in
                    MP_TAC (ISPEC rr mat_weight_default_mat) THEN
                    MP_TAC (ISPECL [r; rows] mat_len_default_mat_less)
                with Failure _ -> ALL_TAC in
     let tac2 = try let _,args = strip_comb (find_app "spec_mats" 2) in
                    let cs = hd args and rows = hd (tl args) in
                    MP_TAC (ISPECL [cs; rows; cs] mats_weight_spec_mats)
                with Failure _ -> ALL_TAC in
     (tac1 THEN tac2) g) THEN
  REWRITE_TAC[GSYM NULL_EQ] THEN
  ASM_REWRITE_TAC[mats_weight_def; mats_len_def; LENGTH; MAX] THEN
  REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC;;

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
  (REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
   RVEQ_TAC THEN
   REPEAT (FIRST_X_ASSUM (K ALL_TAC o check (fun th ->
     is_neg (concl th) && is_exists (dest_neg (concl th))))) THEN
   REWRITE_TAC(WF_REL_THMS @ [exh_steps_def; exh_steps_list_append]) THEN
   ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_ARITH_TAC)
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
  LIST_INDUCT_TAC THEN REWRITE_TAC[tag_ctors_def; MEM] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  SUBGOAL_THEN `?p q. h = (p:num,q:num)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[tag_ctors_def; MEM; injectivity "ctor"; PAIR_EQ]);;

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
  LIST_INDUCT_TAC THEN REWRITE_TAC[expand_def; MEM; MEM_mk_prods] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN RES_TAC THEN
  ASM_REWRITE_TAC[]);;

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
  let easy_tac =
    REPEAT GEN_TAC THEN REWRITE_TAC[expand_def; MEM] THEN REPEAT STRIP_TAC THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]
  and cons_tac =
    (* the tagged and the tuple patterns: the expanded arguments have the  *)
    (* same length, so the same branch of pmatch is taken                  *)
    MAP_EVERY X_GEN_TAC [`t:((num # ((num # num) list) option) option)`;
                         `ps:(pattern_semantics_pat)list`] THEN
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`q:pattern_semantics_pat`; `refs:(num,term)fmap`;
                         `v:term`] THEN
    REWRITE_TAC[expand_def; MEM_mk_conses] THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `qs:(pattern_semantics_pat)list` STRIP_ASSUME_TAC) MP_TAC) THEN
    RVEQ_TAC THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP LENGTH_expand_list) THEN
    STRUCT_CASES_TAC (ISPEC `v:term` (nchotomy_of_type `:term`)) THEN
    REPEAT IL1AUX_SPLIT_TAC THEN
    REWRITE_TAC[pattern_semantics_pmatch_def; distinctness "pmatchResult"] THEN
    ASM_REWRITE_TAC[] THEN
    TRY (COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "pmatchResult"]) THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]
  and or_tac =
    (* both branches must be free of type failures, and once that is known *)
    (* the induction hypotheses apply directly                              *)
    MAP_EVERY X_GEN_TAC [`p1:pattern_semantics_pat`; `p2:pattern_semantics_pat`] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
    MAP_EVERY X_GEN_TAC [`q:pattern_semantics_pat`; `refs:(num,term)fmap`;
                         `v:term`] THEN
    REWRITE_TAC[expand_def; MEM_APPEND] THEN
    REMOVE_THEN "IH1" (MP_TAC o SPECL [`q:pattern_semantics_pat`;
                                       `refs:(num,term)fmap`; `v:term`]) THEN
    REMOVE_THEN "IH2" (MP_TAC o SPECL [`q:pattern_semantics_pat`;
                                       `refs:(num,term)fmap`; `v:term`]) THEN
    REWRITE_TAC[pattern_semantics_pmatch_def] THEN
    CASES_ON `pattern_semantics_pmatch refs p1 v` THEN
    CASES_ON `pattern_semantics_pmatch refs p2 v` THEN
    CASES_ON `pattern_semantics_pmatch refs q v` THEN
    CASE_REWRITE_TAC[distinctness "pmatchResult"] THEN MESON_TAC[]
  and ref_tac =
    X_GEN_TAC `p:pattern_semantics_pat` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`q:pattern_semantics_pat`; `refs:(num,term)fmap`;
                         `v:term`] THEN
    REWRITE_TAC[expand_def; MEM_mk_refs] THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `q':pattern_semantics_pat` STRIP_ASSUME_TAC) MP_TAC) THEN
    RVEQ_TAC THEN
    STRUCT_CASES_TAC (ISPEC `v:term` (nchotomy_of_type `:term`)) THEN
    REWRITE_TAC[pattern_semantics_pmatch_def] THEN
    CASES_ON `FLOOKUP (refs:(num,term)fmap) (a:num)` THEN
    CASE_REWRITE_TAC[distinctness "pmatchResult"] THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]
  and cons_list_tac =
    MAP_EVERY X_GEN_TAC [`p:pattern_semantics_pat`;
                         `ps:(pattern_semantics_pat)list`] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IH1") (LABEL_TAC "IH2")) THEN
    MAP_EVERY X_GEN_TAC [`qs:(pattern_semantics_pat)list`; `refs:(num,term)fmap`;
                         `vs:term list`] THEN
    REWRITE_TAC[expand_def; MEM_mk_prods] THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `x:pattern_semantics_pat`
         (X_CHOOSE_THEN `ys:(pattern_semantics_pat)list` STRIP_ASSUME_TAC))
      MP_TAC) THEN
    RVEQ_TAC THEN
    STRUCT_CASES_TAC (ISPEC `vs:term list` list_CASES) THEN
    REWRITE_TAC(IL1AUX_PE_SIMPS @ [distinctness "pmatchResult"]) THEN
    STRIP_TAC THEN
    REMOVE_THEN "IH1" (MP_TAC o SPECL [`x:pattern_semantics_pat`;
                                       `refs:(num,term)fmap`; `h:term`]) THEN
    REMOVE_THEN "IH2" (MP_TAC o SPECL [`ys:(pattern_semantics_pat)list`;
                                       `refs:(num,term)fmap`; `t:term list`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[] in
  MATCH_MP_TAC pattern_semantics_pat_INDUCT THEN REPEAT CONJ_TAC THENL
   [easy_tac; cons_tac; or_tac; easy_tac; ref_tac; easy_tac; cons_list_tac]);;

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
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `v:term` (nchotomy_of_type `:term`)) THEN
  REPEAT IL1AUX_SPLIT_TAC THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[dest_val_def; injectivity "term"; distinctness "term";
              injectivity "option"; distinctness "option"; PAIR_EQ;
              GSYM CONJ_ASSOC; UNWIND_THM1] THEN
  W (fun (_,w) ->
       if can (find_term (fun t -> is_const t && fst(dest_const t) = "FLOOKUP")) w
       then CASES_ON `FLOOKUP (refs:(num,term)fmap) a` else ALL_TAC) THEN
  CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[injectivity "option"; distinctness "option"; PAIR_EQ;
                  UNWIND_THM1] THEN
  EQ_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]);;

let LENGTH_dest_val = prove
 (`!refs v c as. dest_val refs v = SOME (c,as) ==> LENGTH as = ctor_arity c`,
  REWRITE_TAC[dest_val_eq_SOME] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[ctor_arity_def; LENGTH; ONE]);;

(* A head pattern that reports a constructor set really does confine a      *)
(* value that it does not type-fail on to that set.                          *)

let ctors_of_thm = prove
 (`!p xs refs v.
     ctors_of p = SOME xs /\ ~(pattern_semantics_pmatch refs p v = PTypeFailure) ==>
     ?c as. dest_val refs v = SOME (c,as) /\ MEM c xs`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `p:pattern_semantics_pat`
                      (nchotomy_of_type `:pattern_semantics_pat`)) THEN
  REPEAT IL1AUX_SPLIT_TAC THEN
  REWRITE_TAC[ctors_of_def; distinctness "option"; injectivity "option"] THEN
  DISCH_THEN (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) MP_TAC) THEN
  STRUCT_CASES_TAC (ISPEC `v:term` (nchotomy_of_type `:term`)) THEN
  REPEAT IL1AUX_SPLIT_TAC THEN
  REWRITE_TAC[pattern_semantics_pmatch_def; dest_val_def;
              distinctness "pmatchResult"] THEN
  W (fun (_,w) ->
       if can (find_term (fun t -> is_const t && fst(dest_const t) = "FLOOKUP")) w
       then CASES_ON `FLOOKUP (refs:(num,term)fmap) a'` else ALL_TAC) THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "option"; distinctness "option";
              distinctness "pmatchResult"; PAIR_EQ] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM1; MEM; MEM_ctor_nub; MEM_tag_ctors;
              injectivity "ctor"; is_sibling_def] THEN
  TRY (DISCH_THEN (MP_TAC o MATCH_MP pattern_exh_pmatch_list_LENGTH) THEN
       SIMP_TAC[] THEN NO_TAC) THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "pmatchResult"] THEN
  MESON_TAC[]);;

(* ... and therefore so does the intersection over a whole column. *)

let col_ctors_thm = prove
 (`!M cs refs v vs.
     col_ctors M = SOME cs /\
     ALL (\r. ~(pattern_semantics_pmatch_list refs r (CONS v vs) = PTypeFailure)) M ==>
     ?c as. dest_val refs v = SOME (c,as) /\ MEM c cs`,
  MATCH_MP_TAC col_ctors_ind THEN
  REWRITE_TAC[col_ctors_def; ALL; distinctness "option"; pmatch_list_nil;
              pmatch_list_cons; pand_eq_PTypeFailure; DE_MORGAN_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CASES_ON `ctors_of p` THEN
  FIRST_X_ASSUM (MP_TAC o check (is_eq o concl) o
                 check (can (find_term (fun t -> is_const t &&
                                fst(dest_const t) = "ctor_inter")) o concl)) THEN
  ASM_REWRITE_TAC[ctor_inter_def] THENL
   [DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC (SPECL [`p:pattern_semantics_pat`; `a:ctor list`;
                 `refs:(num,term)fmap`; `v:term`] ctors_of_thm) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `c:ctor` (X_CHOOSE_THEN `as:term list`
                STRIP_ASSUME_TAC)) THEN
  CASES_ON `col_ctors rows` THEN
  ASM_REWRITE_TAC[ctor_inter_def; injectivity "option"] THENL
   [DISCH_THEN (SUBST_ALL_TAC o SYM) THEN ASM_MESON_TAC[];
    DISCH_THEN (SUBST_ALL_TAC o SYM)] THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`a':ctor list`; `refs:(num,term)fmap`;
                                 `v:term`; `vs:term list`]) THEN
  ASM_REWRITE_TAC[injectivity "option"; PAIR_EQ] THEN
  DISCH_THEN (X_CHOOSE_THEN `c':ctor` (X_CHOOSE_THEN `as':term list`
                STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`c:ctor`; `as:term list`] THEN
  ASM_REWRITE_TAC[MEM_ctor_keep] THEN ASM_MESON_TAC[]);;

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
  MATCH_MP_TAC spec_row_ind THEN
  REWRITE_TAC[spec_row_def; MEM] THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN REPEAT GEN_TAC THEN
  TRY COND_CASES_TAC THEN REWRITE_TAC[MEM] THEN STRIP_TAC THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP LENGTH_dest_val) THEN
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [dest_val_eq_SOME]) THEN
  RVEQ_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[injectivity "ctor"; distinctness "ctor";
                               ctor_arity_def]) THEN
  TRY (FIRST_ASSUM CONTR_TAC) THEN
  RULE_ASSUM_TAC (REWRITE_RULE[GSYM CONJ_ASSOC]) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN
  REWRITE_TAC[ctor_arity_def; ONE; anys_def; APPEND; pmatch_list_cons] THEN
  ASM_SIMP_TAC[pattern_exh_pmatch_list_append; LENGTH_anys;
               pmatch_list_anys; pand_simps; pmatch_Any] THEN
  REWRITE_TAC IL1AUX_PMATCH_CLAUSES THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let spec_mat_MEM = prove
 (`!M c as refs v vs row.
     dest_val refs v = SOME (c,as) /\ MEM row (spec_mat c M) ==>
     ?r. MEM r M /\
         pattern_semantics_pmatch_list refs row (APPEND as vs) =
         pattern_semantics_pmatch_list refs r (CONS v vs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[spec_mat_def; MEM; MEM_APPEND] THEN
  REPEAT STRIP_TAC THENL
   [EXISTS_TAC `h:(pattern_semantics_pat)list` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC spec_row_thm THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM (MP_TAC o SPECL [`c:ctor`; `as:term list`;
                                   `refs:(num,term)fmap`; `v:term`;
                                   `vs:term list`;
                                   `row:(pattern_semantics_pat)list`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

let default_row_thm = prove
 (`!r row refs v vs.
     MEM row (default_row r) ==>
     pattern_semantics_pmatch_list refs row vs =
     pattern_semantics_pmatch_list refs r (CONS v vs)`,
  MATCH_MP_TAC default_row_ind THEN
  REWRITE_TAC[default_row_def; MEM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[pmatch_list_cons; pmatch_Any; pand_simps]);;

let default_mat_MEM = prove
 (`!M refs v vs row.
     MEM row (default_mat M) ==>
     ?r. MEM r M /\
         pattern_semantics_pmatch_list refs row vs =
         pattern_semantics_pmatch_list refs r (CONS v vs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[default_mat_def; MEM; MEM_APPEND] THEN
  REPEAT STRIP_TAC THENL
   [EXISTS_TAC `h:(pattern_semantics_pat)list` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC default_row_thm THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM (MP_TAC o SPECL [`refs:(num,term)fmap`; `v:term`;
                                   `vs:term list`;
                                   `row:(pattern_semantics_pat)list`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* Soundness of the matrix algorithm: "ok" (no row type-fails) is          *)
(* inherited by the sub-matrices, and "hit" (some row succeeds) is          *)
(* reflected back out of them.                                               *)

(* the "ok" and "hit" properties of the default and specialised matrices *)

let IL1AUX_DEFAULT_OK = prove
 (`!M refs v vs.
     ALL (\r. ~(pattern_semantics_pmatch_list refs r (CONS v vs) = PTypeFailure)) M
     ==> ALL (\r. ~(pattern_semantics_pmatch_list refs r vs = PTypeFailure))
             (default_mat M)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  DISCH_TAC THEN X_GEN_TAC `row:(pattern_semantics_pat)list` THEN DISCH_TAC THEN
  MP_TAC (SPECL [`M:((pattern_semantics_pat)list)list`; `refs:(num,term)fmap`;
                 `v:term`; `vs:term list`; `row:(pattern_semantics_pat)list`]
                default_mat_MEM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let IL1AUX_DEFAULT_HIT = prove
 (`!M refs v vs.
     EX (\r. pattern_semantics_pmatch_list refs r vs = PMatchSuccess)
        (default_mat M)
     ==> EX (\r. pattern_semantics_pmatch_list refs r (CONS v vs) = PMatchSuccess) M`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM EX_MEM] THEN
  DISCH_THEN (X_CHOOSE_THEN `row:(pattern_semantics_pat)list` STRIP_ASSUME_TAC) THEN
  MP_TAC (SPECL [`M:((pattern_semantics_pat)list)list`; `refs:(num,term)fmap`;
                 `v:term`; `vs:term list`; `row:(pattern_semantics_pat)list`]
                default_mat_MEM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `r:(pattern_semantics_pat)list` THEN ASM_MESON_TAC[]);;

let IL1AUX_SPEC_OK = prove
 (`!M c as refs v vs.
     dest_val refs v = SOME (c,as) /\
     ALL (\r. ~(pattern_semantics_pmatch_list refs r (CONS v vs) = PTypeFailure)) M
     ==> ALL (\r. ~(pattern_semantics_pmatch_list refs r (APPEND as vs) =
                    PTypeFailure))
             (spec_mat c M)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  STRIP_TAC THEN X_GEN_TAC `row:(pattern_semantics_pat)list` THEN DISCH_TAC THEN
  MP_TAC (SPECL [`M:((pattern_semantics_pat)list)list`; `c:ctor`; `as:term list`;
                 `refs:(num,term)fmap`; `v:term`; `vs:term list`;
                 `row:(pattern_semantics_pat)list`] spec_mat_MEM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let IL1AUX_SPEC_HIT = prove
 (`!M c as refs v vs.
     dest_val refs v = SOME (c,as) /\
     EX (\r. pattern_semantics_pmatch_list refs r (APPEND as vs) = PMatchSuccess)
        (spec_mat c M)
     ==> EX (\r. pattern_semantics_pmatch_list refs r (CONS v vs) = PMatchSuccess) M`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM EX_MEM] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `row:(pattern_semantics_pat)list` STRIP_ASSUME_TAC)) THEN
  MP_TAC (SPECL [`M:((pattern_semantics_pat)list)list`; `c:ctor`; `as:term list`;
                 `refs:(num,term)fmap`; `v:term`; `vs:term list`;
                 `row:(pattern_semantics_pat)list`] spec_mat_MEM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `r:(pattern_semantics_pat)list` THEN ASM_MESON_TAC[]);;

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
    REWRITE_TAC[exh_matrix_def];
    ALL_TAC;
    REWRITE_TAC[MEM];
    REWRITE_TAC[exh_matrix_def; MEM] THEN MESON_TAC[]] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "IHs") (LABEL_TAC "IHd")) THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[exh_matrix_def] THEN
  ASM_CASES_TAC `NULL (r:(pattern_semantics_pat)list)` THEN ASM_REWRITE_TAC[] THENL
   [(* a row of width zero: the value vector must be empty too, and then  *)
    (* that row matches                                                     *)
    UNDISCH_TAC `NULL (r:(pattern_semantics_pat)list)` THEN
    REWRITE_TAC[NULL_EQ] THEN DISCH_THEN SUBST_ALL_TAC THEN
    STRUCT_CASES_TAC (ISPEC `vs:term list` list_CASES) THEN
    REWRITE_TAC[ALL; EX; pmatch_list_nil];
    ALL_TAC] THEN
  SUBGOAL_THEN `?p ps. r = CONS (p:pattern_semantics_pat) ps` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[NULL_EQ; list_CASES]; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[NULL]) THEN REWRITE_TAC[NULL] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?v vs'. vs = CONS (v:term) vs'` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\r. ~(pattern_semantics_pmatch_list refs r vs = PTypeFailure))
                     (CONS (CONS p ps) rows)` THEN
    STRUCT_CASES_TAC (ISPEC `vs:term list` list_CASES) THEN
    REWRITE_TAC[ALL; pmatch_list_nil] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CASES_ON `col_ctors (CONS (CONS (p:pattern_semantics_pat) ps) rows)` THEN
  FIRST_X_ASSUM (MP_TAC o check (fun th -> is_case_app (concl th))) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THENL
   [(* nothing is known about the column, so only the wildcard rows can be *)
    (* relied on: work in the default matrix                                *)
    REMOVE_THEN "IHd" (MP_TAC o SPECL [`refs:(num,term)fmap`; `vs':term list`] o
                       REWRITE_RULE[]) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC IL1AUX_DEFAULT_OK THEN EXISTS_TAC `v:term` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC IL1AUX_DEFAULT_HIT THEN ASM_REWRITE_TAC[];
    (* the column's constructors are known, so the value has one of them:  *)
    (* work in the matrix specialised for it                                *)
    REMOVE_THEN "IHs" (MP_TAC o SPEC `a:ctor list`) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC (SPECL [`CONS (CONS (p:pattern_semantics_pat) ps) rows`; `a:ctor list`;
                   `refs:(num,term)fmap`; `v:term`; `vs':term list`]
                  col_ctors_thm) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN (X_CHOOSE_THEN `c:ctor` (X_CHOOSE_THEN `as:term list`
                  STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
      [`spec_mat c (CONS (CONS (p:pattern_semantics_pat) ps) rows)`;
       `refs:(num,term)fmap`; `APPEND (as:term list) vs'`]) THEN
    ASM_SIMP_TAC[MEM_spec_mats] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC IL1AUX_SPEC_OK THEN EXISTS_TAC `v:term` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC IL1AUX_SPEC_HIT THEN
    MAP_EVERY EXISTS_TAC [`c:ctor`; `as:term list`] THEN ASM_REWRITE_TAC[]]);;

(* From the matrix back to match. *)

let match_no_PTypeFailure = prove
 (`!rows:(pattern_semantics_pat # num) list.
     ~(pattern_semantics_match refs rows v = NONE) ==>
     ALL (\(p,e). ~(pattern_semantics_pmatch refs p v = PTypeFailure)) rows`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`h:pattern_semantics_pat # num`,`h:pattern_semantics_pat # num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:pattern_semantics_pat`; `e:num`] THEN
  REWRITE_TAC[pattern_semantics_match_def] THEN
  CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT DISCH_TAC THEN
  CASES_ON `pattern_semantics_pmatch refs p v` THEN
  RULE_ASSUM_TAC (CASE_REWRITE_RULE[]) THEN
  ASM_REWRITE_TAC[distinctness "pmatchResult"] THEN
  TRY (CASES_ON `pattern_semantics_match refs (t:(pattern_semantics_pat # num) list) v`) THEN
  RULE_ASSUM_TAC (CASE_REWRITE_RULE[]) THEN
  ASM_MESON_TAC[distinctness "option"]);;

let match_EXISTS = prove
 (`!rows:(pattern_semantics_pat # num) list.
     ~(pattern_semantics_match refs rows v = NONE) /\
     EX (\(p,e). pattern_semantics_pmatch refs p v = PMatchSuccess) rows ==>
     ~(pattern_semantics_match refs rows v = SOME MatchFailure)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[EX] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`h:pattern_semantics_pat # num`,`h:pattern_semantics_pat # num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:pattern_semantics_pat`; `e:num`] THEN
  REWRITE_TAC[pattern_semantics_match_def] THEN
  CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THEN
  CASES_ON `pattern_semantics_pmatch refs p v` THEN
  RULE_ASSUM_TAC (CASE_REWRITE_RULE[]) THEN
  RULE_ASSUM_TAC (REWRITE_RULE[distinctness "pmatchResult"]) THEN
  TRY (CASES_ON `pattern_semantics_match refs (t:(pattern_semantics_pat # num) list) v` THEN
       RULE_ASSUM_TAC (CASE_REWRITE_RULE[])) THEN
  ASM_MESON_TAC[distinctness "option"; injectivity "option";
                distinctness "matchResult"]);;

let or_rows_ok = prove
 (`!rows:(pattern_semantics_pat # A) list.
     ALL (\(p,e). ~(pattern_semantics_pmatch refs p v = PTypeFailure)) rows ==>
     ALL (\r. ~(pattern_semantics_pmatch_list refs r [v] = PTypeFailure))
         (or_rows rows)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; or_rows_def] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`h:pattern_semantics_pat # A`,`h:pattern_semantics_pat # A`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:pattern_semantics_pat`; `e:A`] THEN
  REWRITE_TAC[or_rows_def; ALL_APPEND] THEN
  CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM; MEM_mk_rows; LEFT_IMP_EXISTS_THM] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    REWRITE_TAC[pmatch_list_cons; pmatch_list_nil; pand_simps] THEN
    MP_TAC (SPECL [`p:pattern_semantics_pat`; `p':pattern_semantics_pat`;
                   `refs:(num,term)fmap`; `v:term`] (CONJUNCT1 expand_thm)) THEN
    ASM_SIMP_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let or_rows_hit = prove
 (`!rows:(pattern_semantics_pat # A) list.
     ALL (\(p,e). ~(pattern_semantics_pmatch refs p v = PTypeFailure)) rows /\
     EX (\r. pattern_semantics_pmatch_list refs r [v] = PMatchSuccess)
        (or_rows rows) ==>
     EX (\(p,e). pattern_semantics_pmatch refs p v = PMatchSuccess) rows`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; EX; or_rows_def] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`h:pattern_semantics_pat # A`,`h:pattern_semantics_pat # A`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:pattern_semantics_pat`; `e:A`] THEN
  REWRITE_TAC[or_rows_def; EXISTS_APPEND] THEN
  CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THENL
   [DISJ1_TAC THEN
    UNDISCH_TAC `EX (\r. pattern_semantics_pmatch_list refs r [v] = PMatchSuccess)
                    (mk_rows (expand p))` THEN
    REWRITE_TAC[GSYM EX_MEM; MEM_mk_rows] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[pmatch_list_cons; pmatch_list_nil; pand_simps]) THEN
    MP_TAC (SPECL [`p:pattern_semantics_pat`; `p':pattern_semantics_pat`;
                   `refs:(num,term)fmap`; `v:term`] (CONJUNCT1 expand_thm)) THEN
    ASM_SIMP_TAC[];
    DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Soundness of exh_rows: the theorem the pattern compiler needs. *)

let exh_rows_thm = prove
 (`~(pattern_semantics_match refs rows v = NONE) /\ exh_rows rows ==>
   ~(pattern_semantics_match refs rows v = SOME MatchFailure)`,
  STRIP_TAC THEN MATCH_MP_TAC match_EXISTS THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM (ASSUME_TAC o MATCH_MP match_no_PTypeFailure) THEN
  MATCH_MP_TAC or_rows_hit THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (CONJUNCT1 exh_matrix_thm) THEN
  ASM_SIMP_TAC[or_rows_ok] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[exh_rows_def]) THEN ASM_REWRITE_TAC[]);;
