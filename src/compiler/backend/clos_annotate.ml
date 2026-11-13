(* ========================================================================= *)
(* clos_annotate: port of HOL4 compiler/backend/clos_annotateScript.sml      *)
(* (CakeML v3479).                                                           *)
(* A compiler phase that annotates code that creates closures with          *)
(* (minimal) live variable annotations. Such live variable annotations are  *)
(* required for closure conversion, which is implemented in the clos_to_bvl *)
(* phase of the compiler.                                                    *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The constructors of db_var_set are db_vars_Empty, db_vars_Var,          *)
(*   db_vars_Shift, db_vars_Union; EVERY is ALL; HOL4 num_map is num spt.    *)
(* - The clauses of a HOL Light definition share their variables, so a name *)
(*   used with two types gets a second name: the names of Fn and clos_Letrec *)
(*   (HOL4 t) are nm and nms.                                                *)
(* - HOL4's paired lambdas (\(n,x). t) are written                           *)
(*   (\p. match p with (n,x) -> t).                                          *)
(* - The definitions are made with sem1aux_def_wf (semantics/sem1aux_tfl.ml) *)
(*   and, for the three mutually recursive functions, il1aux_def_wf          *)
(*   (compiler/backend/il1aux_mutual.ml); where HOL4's termination is        *)
(*   automatic, the relation is its size measure.                            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/db_vars.ml";;
needs "semantics/sem1aux_tfl.ml";;
needs "compiler/backend/il1aux_mutual.ml";;

type_invention_error := true;;

(* alt_free calculates free variable annotations, and replaces unused lets *)
(* with dummies                                                             *)

let const_0_def = cake_def
  `const_0 t = clos_Op t (IntOp (clos_Const (&0))) []`;;

let no_overlap_def = cake_def
  `(no_overlap 0 l <=> T) /\
   (no_overlap (SUC n) l <=> if has_var n l then F else no_overlap n l)`;;

let alt_free_def = sem1aux_def_wf
  `measure (\es:clos_exp list. list_size clos_exp_size es)`
  SEM1AUX_TC_TAC
  `(alt_free [] = ([],db_vars_Empty)) /\
   (alt_free (CONS (x:clos_exp) (CONS y xs)) =
      let (c1,l1) = alt_free [x] in
      let (c2,l2) = alt_free (CONS y xs) in
        (APPEND c1 c2, mk_Union l1 l2)) /\
   (alt_free [clos_Var t v] = ([clos_Var t v], db_vars_Var v)) /\
   (alt_free [clos_If t x1 x2 x3] =
      let (c1,l1) = alt_free [x1] in
      let (c2,l2) = alt_free [x2] in
      let (c3,l3) = alt_free [x3] in
        ([clos_If t (HD c1) (HD c2) (HD c3)], mk_Union l1 (mk_Union l2 l3))) /\
   (alt_free [clos_Let t xs x2] =
      let m = LENGTH xs in
      let (c2,l2) = alt_free [x2] in
        if no_overlap m l2 /\ ALL pure xs then
          ([clos_Let t (REPLICATE m (const_0 t)) (HD c2)], db_vars_Shift m l2)
        else
          let (c1,l1) = alt_free xs in
            ([clos_Let t c1 (HD c2)],
             mk_Union l1 (db_vars_Shift (LENGTH xs) l2))) /\
   (alt_free [clos_Raise t x1] =
      let (c1,l1) = alt_free [x1] in
        ([clos_Raise t (HD c1)], l1)) /\
   (alt_free [clos_Tick t x1] =
      let (c1,l1) = alt_free [x1] in
        ([clos_Tick t (HD c1)], l1)) /\
   (alt_free [clos_Op t op xs] =
      let (c1,l1) = alt_free xs in
        ([clos_Op t op c1], l1)) /\
   (alt_free [clos_App t loc_opt x1 xs2] =
      let (c1,l1) = alt_free [x1] in
      let (c2,l2) = alt_free xs2 in
        ([clos_App t loc_opt (HD c1) c2], mk_Union l1 l2)) /\
   (alt_free [Fn nm loc _ num_args x1] =
      let (c1,l1) = alt_free [x1] in
      let l2 = db_vars_Shift num_args l1 in
        ([Fn nm loc (SOME (vars_to_list l2)) num_args (HD c1)], l2)) /\
   (alt_free [clos_Letrec nms loc _ fns x1] =
      let m = LENGTH fns in
      let (c2,l2) = alt_free [x1] in
      let res = MAP (\p. match p with
                           (n,x) ->
                             let (c,l) = alt_free [x] in
                               ((n, HD c), db_vars_Shift (n + m) l)) fns in
      let c1 = MAP FST res in
      let l1 = list_mk_Union (MAP SND res) in
        ([clos_Letrec nms loc (SOME (vars_to_list l1)) c1 (HD c2)],
         mk_Union l1 (db_vars_Shift (LENGTH fns) l2))) /\
   (alt_free [clos_Handle t x1 x2] =
      let (c1,l1) = alt_free [x1] in
      let (c2,l2) = alt_free [x2] in
        ([clos_Handle t (HD c1) (HD c2)], mk_Union l1 (db_vars_Shift 1 l2))) /\
   (alt_free [clos_Call t ticks dest xs] =
      let (c1,l1) = alt_free xs in
        ([clos_Call t ticks dest c1], l1))`;;

let alt_free_ind = cake_ind "alt_free";;

let alt_free_sing_def = il1aux_def_wf
  `measure
     (\x:clos_exp + clos_exp list + (num # (num # clos_exp) list).
        sum_CASE x clos_exp_size
          (\y. sum_CASE y (list_size clos_exp_size)
                 (\p. list_size (pair_size (\x. x) clos_exp_size) (SND p))))`
  SEM1AUX_TC_TAC
  `(alt_free_sing (clos_Var t v) = (clos_Var t v, db_vars_Var v)) /\
   (alt_free_sing (clos_If t x1 x2 x3) =
      let (c1,l1) = alt_free_sing x1 in
      let (c2,l2) = alt_free_sing x2 in
      let (c3,l3) = alt_free_sing x3 in
        (clos_If t c1 c2 c3, mk_Union l1 (mk_Union l2 l3))) /\
   (alt_free_sing (clos_Let t xs x2) =
      let m = LENGTH xs in
      let (c2,l2) = alt_free_sing x2 in
        if no_overlap m l2 /\ ALL pure xs then
          (clos_Let t (REPLICATE m (const_0 t)) c2, db_vars_Shift m l2)
        else
          let (c1,l1) = alt_free_list xs in
            (clos_Let t c1 c2, mk_Union l1 (db_vars_Shift (LENGTH xs) l2))) /\
   (alt_free_sing (clos_Raise t x1) =
      let (c1,l1) = alt_free_sing x1 in (clos_Raise t c1, l1)) /\
   (alt_free_sing (clos_Tick t x1) =
      let (c1,l1) = alt_free_sing x1 in (clos_Tick t c1, l1)) /\
   (alt_free_sing (clos_Op t op xs) =
      let (c1,l1) = alt_free_list xs in (clos_Op t op c1, l1)) /\
   (alt_free_sing (clos_App t loc_opt x1 xs2) =
      let (c1,l1) = alt_free_sing x1 in
      let (c2,l2) = alt_free_list xs2 in
        (clos_App t loc_opt c1 c2, mk_Union l1 l2)) /\
   (alt_free_sing (Fn nm loc _ num_args x1) =
      let (c1,l1) = alt_free_sing x1 in
      let l2 = db_vars_Shift num_args l1 in
        (Fn nm loc (SOME (vars_to_list l2)) num_args c1, l2)) /\
   (alt_free_sing (clos_Letrec nms loc _ fns x1) =
      let m = LENGTH fns in
      let (c2,l2) = alt_free_sing x1 in
      let res = alt_free_letrec m fns in
      let c1 = MAP FST res in
      let l1 = list_mk_Union (MAP SND res) in
        (clos_Letrec nms loc (SOME (vars_to_list l1)) c1 c2,
         mk_Union l1 (db_vars_Shift (LENGTH fns) l2))) /\
   (alt_free_sing (clos_Handle t x1 x2) =
      let (c1,l1) = alt_free_sing x1 in
      let (c2,l2) = alt_free_sing x2 in
        (clos_Handle t c1 c2, mk_Union l1 (db_vars_Shift 1 l2))) /\
   (alt_free_sing (clos_Call t ticks dest xs) =
      let (c1,l1) = alt_free_list xs in (clos_Call t ticks dest c1, l1)) /\
   (alt_free_list [] = ([],db_vars_Empty)) /\
   (alt_free_list (CONS (x:clos_exp) xs) =
      let (c1,l1) = alt_free_sing x in
      let (c2,l2) = alt_free_list xs in
        (CONS c1 c2, mk_Union l1 l2)) /\
   (alt_free_letrec m [] = []) /\
   (alt_free_letrec m (CONS (n,x) rest) =
      let (c,l) = alt_free_sing x in
        CONS ((n,c), db_vars_Shift (n + m) l) (alt_free_letrec m rest))`;;

let alt_free_sing_ind = cake_ind "alt_free_sing";;

(* the functions of clos_Letrec in alt_free_sing_eq: HOL4's MAP_EQ_f step *)

let IL1AUX_ALT_FREE_MAP = prove
 (CASE_TERM
  `!fns. ALL (\p. match p with
                    (n,e) -> alt_free [e] =
                             (match alt_free_sing e with (e,dbs) -> ([e],dbs)))
             fns ==>
         !m. MAP (\p. match p with
                        (n,x) -> (let (c,l) = alt_free [x] in
                                    ((n, HD c), db_vars_Shift (n + m) l))) fns =
             MAP (\p. match p with
                        (n,x) -> (let (c,l) = alt_free_sing x in
                                    ((n,c), db_vars_Shift (n + m) l))) fns`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL; CONS_11] THEN
  SUBGOAL_THEN `?a b. h = (a:num,b:clos_exp)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `?c d. alt_free_sing b = (c,d)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[HD]);;

let alt_free_sing_eq = prove
 (CASE_TERM
  `(!e. alt_free [e] = (\p. match p with (e,dbs) -> ([e],dbs)) (alt_free_sing e)) /\
   (!es. alt_free es = alt_free_list es) /\
   (!m fns.
      ALL (\p. match p with
                 (n,e) -> alt_free [e] =
                          (\p. match p with (e,dbs) -> ([e],dbs)) (alt_free_sing e))
          fns /\
      alt_free_letrec m fns =
      MAP (\p. match p with
                 (n,x) -> (let (c,l) = alt_free_sing x in
                             ((n,c), db_vars_Shift (n + m) l))) fns)`,
  let letrec_tac =
    MAP_EVERY X_GEN_TAC [`nms:mlstring list`; `loc:num option`;
                         `vs:(num list)option`; `fns:(num#clos_exp)list`;
                         `x1:clos_exp`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH2") (LABEL_TAC "IH0")) THEN
    SUBGOAL_THEN `?c2 l2. alt_free_sing x1 = (c2,l2)` STRIP_ASSUME_TAC THENL
     [MESON_TAC[PAIR]; ALL_TAC] THEN
    REMOVE_THEN "IH2" (MP_TAC o SPECL [`c2:clos_exp`; `l2:db_var_set`;
                                       `LENGTH (fns:(num#clos_exp)list)`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (ASSUME_TAC o MATCH_MP IL1AUX_ALT_FREE_MAP o BETA_RULE) ASSUME_TAC) THEN
    REMOVE_THEN "IH0" MP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    REWRITE_TAC[alt_free_def; alt_free_sing_def; LET_DEF; LET_END_DEF] THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[HD]
  and base_tac =
    REPEAT GEN_TAC THEN RW[alt_free_def; alt_free_sing_def] THEN
    REPEAT (IL1AUX_PAIRARG_TAC THEN GVS[])
  and case_tac =
    TRY (TOP_CASE_TAC THEN GVS[] THEN
         TRY (TOP_CASE_TAC THEN GVS[] THEN TRY (TOP_CASE_TAC THEN GVS[]))) in
  MATCH_MP_TAC alt_free_sing_ind THEN REPEAT CONJ_TAC THEN
  FIRST
   [(* clos_Letrec, by IL1AUX_ALT_FREE_MAP (rewriting with the clauses and *)
    (* the induction hypotheses does not terminate on this case)           *)
    letrec_tac THEN NO_TAC;
    base_tac THEN case_tac THEN TRY (RES_TAC THEN ASM_REWRITE_TAC[]) THEN NO_TAC;
    (* the list of expressions: HOL4's Cases_on es *)
    base_tac THEN CASES_ON `xs:clos_exp list` THEN
    GVS[alt_free_def; alt_free_sing_def; mk_Union_Empty; APPEND]]);;

let alt_free_LENGTH_LEMMA = prove
 (CASE_TERM `!xs. match alt_free xs with (ys,s1) -> LENGTH xs = LENGTH ys`,
  REWRITE_TAC[alt_free_sing_eq] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[alt_free_sing_def] THEN CASE_REWRITE_TAC[LENGTH] THEN
  REPEAT (IL1AUX_PAIRARG_TAC THEN GVS[LENGTH]) THEN GVS[LENGTH]);;

let alt_free_LENGTH = prove
 (`!xs ys l. alt_free xs = (ys,l) ==> LENGTH ys = LENGTH xs`,
  REPEAT STRIP_TAC THEN MP_TAC (SPEC `xs:clos_exp list` alt_free_LENGTH_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

let alt_free_SING = prove
 (`!x ys l. alt_free [x] = (ys,l) ==> ?y. ys = [y]`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC alt_free_LENGTH THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`ys:clos_exp list`,`ys:clos_exp list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

let LENGTH_FST_alt_free = prove
 (`!fns. LENGTH (FST (alt_free fns)) = LENGTH fns`,
  GEN_TAC THEN MP_TAC (ISPEC `alt_free fns` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FST] THEN IMP_RES_TAC alt_free_LENGTH THEN
  ASM_REWRITE_TAC[]);;

let HD_FST_alt_free = prove
 (`!x1. [HD (FST (alt_free [x1]))] = FST (alt_free [x1])`,
  GEN_TAC THEN MP_TAC (ISPEC `alt_free [x1]` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FST] THEN IMP_RES_TAC alt_free_SING THEN
  ASM_REWRITE_TAC[HD]);;

let alt_free_CONS = prove
 (`!x xs. FST (alt_free (CONS x xs)) =
          CONS (HD (FST (alt_free [x]))) (FST (alt_free xs))`,
  REWRITE_TAC[alt_free_sing_eq] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[alt_free_sing_def] THEN REPEAT IL1AUX_PAIRARG_TAC THEN SIMP[HD]);;

(* shift renames variables to use only those in the annotations *)

(* HOL4: get_var *)

let clos_annotate_get_var_def = cake_def
  `clos_annotate_get_var (m:A) l i v =
     if v < l then v else l + zlookup i (v - l)`;;

let shifted_env_def = cake_def
  `(shifted_env n [] = LN:num spt) /\
   (shifted_env n (CONS x xs) = insert x (n:num) (shifted_env (n + 1) xs))`;;

let clos_annotate_shift_def = sem1aux_def_wf
  `measure (\p:clos_exp list # num # num # num spt.
              list_size clos_exp_size (FST p))`
  SEM1AUX_TC_TAC
  `(clos_annotate_shift [] (m:num) (l:num) (i:num spt) = []) /\
   (clos_annotate_shift (CONS (x:clos_exp) (CONS y xs)) m l i =
      let c1 = clos_annotate_shift [x] m l i in
      let c2 = clos_annotate_shift (CONS y xs) m l i in
        (APPEND c1 c2:clos_exp list)) /\
   (clos_annotate_shift [clos_Var t v] m l i = [clos_Var t (clos_annotate_get_var m l i v)]) /\
   (clos_annotate_shift [clos_If t x1 x2 x3] m l i =
      let c1 = clos_annotate_shift [x1] m l i in
      let c2 = clos_annotate_shift [x2] m l i in
      let c3 = clos_annotate_shift [x3] m l i in
        [clos_If t (HD c1) (HD c2) (HD c3)]) /\
   (clos_annotate_shift [clos_Let t xs x2] m l i =
      let c1 = clos_annotate_shift xs m l i in
      let c2 = clos_annotate_shift [x2] m (l + LENGTH xs) i in
        [clos_Let t c1 (HD c2)]) /\
   (clos_annotate_shift [clos_Raise t x1] m l i =
      let c1 = clos_annotate_shift [x1] m l i in
        [clos_Raise t (HD c1)]) /\
   (clos_annotate_shift [clos_Tick t x1] m l i =
      let c1 = clos_annotate_shift [x1] m l i in
        [clos_Tick t (HD c1)]) /\
   (clos_annotate_shift [clos_Op t op xs] m l i =
      let c1 = clos_annotate_shift xs m l i in
        [clos_Op t op c1]) /\
   (clos_annotate_shift [clos_App t loc_opt x1 xs2] m l i =
      let c1 = clos_annotate_shift [x1] m l i in
      let c2 = clos_annotate_shift xs2 m l i in
        [clos_App t loc_opt (HD c1) c2]) /\
   (clos_annotate_shift [Fn nm loc vs_opt num_args x1] m l i =
      let k = m + l in
      let vs = (match vs_opt with NONE -> [] | SOME vs -> vs) in
      let live = FILTER (\n. n < k) vs in
      let vars = MAP (clos_annotate_get_var m l i) live in
      let c1 = clos_annotate_shift [x1] k num_args (shifted_env 0 live) in
        [Fn nm loc (SOME vars) num_args (HD c1)]) /\
   (clos_annotate_shift [clos_Letrec nms loc vsopt fns x1] m l i =
      let vs = (match vsopt with NONE -> [] | SOME x -> x) in
      let k = m + l in
      let live = FILTER (\n. n < k) vs in
      let vars = MAP (clos_annotate_get_var m l i) live in
      let new_i = shifted_env 0 live in
      let fns_len = LENGTH fns in
      let cs = MAP (\p. match p with
                          (n,x) ->
                            let c = clos_annotate_shift [x] k (n + fns_len) new_i in
                              (n,HD c)) fns in
      let c1 = clos_annotate_shift [x1] m (l + LENGTH fns) i in
        [clos_Letrec nms loc (SOME vars) cs (HD c1)]) /\
   (clos_annotate_shift [clos_Handle t x1 x2] m l i =
      let c1 = clos_annotate_shift [x1] m l i in
      let c2 = clos_annotate_shift [x2] m (l + 1) i in
        [clos_Handle t (HD c1) (HD c2)]) /\
   (clos_annotate_shift [clos_Call t ticks dest xs] m l i =
      let c1 = clos_annotate_shift xs m l i in
        [clos_Call t ticks dest c1])`;;

let clos_annotate_shift_ind = cake_ind "clos_annotate_shift";;

let shift_sing_def = il1aux_def_wf
  `measure
     (\x:(clos_exp # num # num # num spt) + (clos_exp list # num # num # num spt) +
         (num # num # num spt # (num # clos_exp) list).
        sum_CASE x (\p. clos_exp_size (FST p))
          (\y. sum_CASE y (\p. list_size clos_exp_size (FST p))
                 (\p. list_size (pair_size (\x. x) clos_exp_size)
                        (SND (SND (SND p))))))`
  SEM1AUX_TC_TAC
  `(shift_sing (clos_Var t v) m l i = clos_Var t (clos_annotate_get_var m l i v)) /\
   (shift_sing (clos_If t x1 x2 x3) m l i =
      let c1 = shift_sing x1 m l i in
      let c2 = shift_sing x2 m l i in
      let c3 = shift_sing x3 m l i in
        clos_If t c1 c2 c3) /\
   (shift_sing (clos_Let t xs x2) m l i =
      let c1 = shift_list xs m l i in
      let c2 = shift_sing x2 m (l + LENGTH xs) i in
        clos_Let t c1 c2) /\
   (shift_sing (clos_Raise t x1) m l i =
      let c1 = shift_sing x1 m l i in
        clos_Raise t c1) /\
   (shift_sing (clos_Tick t x1) m l i =
      let c1 = shift_sing x1 m l i in
        clos_Tick t c1) /\
   (shift_sing (clos_Op t op xs) m l i =
      let c1 = shift_list xs m l i in
        clos_Op t op c1) /\
   (shift_sing (clos_App t loc_opt x1 xs2) m l i =
      let c1 = shift_sing x1 m l i in
      let c2 = shift_list xs2 m l i in
        clos_App t loc_opt c1 c2) /\
   (shift_sing (Fn nm loc vs_opt num_args x1) m l i =
      let k = m + l in
      let vs = (match vs_opt with NONE -> [] | SOME vs -> vs) in
      let live = FILTER (\n. n < k) vs in
      let vars = MAP (clos_annotate_get_var m l i) live in
      let c1 = shift_sing x1 k num_args (shifted_env 0 live) in
        Fn nm loc (SOME vars) num_args c1) /\
   (shift_sing (clos_Letrec nms loc vsopt fns x1) m l i =
      let vs = (match vsopt with NONE -> [] | SOME x -> x) in
      let k = m + l in
      let live = FILTER (\n. n < k) vs in
      let vars = MAP (clos_annotate_get_var m l i) live in
      let new_i = shifted_env 0 live in
      let fns_len = LENGTH fns in
      let cs = shift_letrec fns_len k new_i fns in
      let c1 = shift_sing x1 m (l + LENGTH fns) i in
        clos_Letrec nms loc (SOME vars) cs c1) /\
   (shift_sing (clos_Handle t x1 x2) m l i =
      let c1 = shift_sing x1 m l i in
      let c2 = shift_sing x2 m (l + 1) i in
        clos_Handle t c1 c2) /\
   (shift_sing (clos_Call t ticks dest xs) m l i =
      let c1 = shift_list xs m l i in
        clos_Call t ticks dest c1) /\
   (shift_list [] (m:num) (l:num) (i:num spt) = []) /\
   (shift_list (CONS (x:clos_exp) xs) m l i =
      let c1 = shift_sing x m l i in
      let c2 = shift_list xs m l i in
        CONS c1 c2) /\
   (shift_letrec fns_len k new_i [] = []) /\
   (shift_letrec fns_len k new_i (CONS (n,x) rest) =
      let c = shift_sing x k (n + fns_len) new_i in
        CONS (n,c) (shift_letrec fns_len k new_i rest))`;;

let shift_sing_ind = cake_ind "shift_sing";;

(* the functions of clos_Letrec in shift_sing_eq: HOL4's MAP_EQ_f step *)

let IL1AUX_SHIFT_MAP = prove
 (CASE_TERM
  `!fns fns_len k new_i.
     ALL (\p. match p with
                (n,e) -> clos_annotate_shift [e] k (n + fns_len) new_i =
                         [shift_sing e k (n + fns_len) new_i]) fns ==>
     MAP (\p. match p with
                (n,x) -> (n, HD (clos_annotate_shift [x] k (n + fns_len) new_i))) fns =
     MAP (\p. match p with
                (n,x) -> (n, shift_sing x k (n + fns_len) new_i)) fns`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ALL; CONS_11] THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?a b. h = (a:num,b:clos_exp)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[HD] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let shift_sing_eq = prove
 (CASE_TERM
  `(!e m l i. clos_annotate_shift [e] m l i = [shift_sing e m l i]) /\
   (!es m l i. clos_annotate_shift es m l i = shift_list es m l i) /\
   (!fns_len k new_i fns.
      ALL (\p. match p with
                 (n,e) -> clos_annotate_shift [e] k (n + fns_len) new_i =
                          [shift_sing e k (n + fns_len) new_i]) fns /\
      shift_letrec fns_len k new_i fns =
      MAP (\p. match p with
                 (n,x) -> (let c = shift_sing x k (n + fns_len) new_i in (n,c)))
          fns)`,
  let letrec_tac =
    MAP_EVERY X_GEN_TAC [`nms:mlstring list`; `loc:num option`;
                         `vsopt:(num list)option`; `fns:(num#clos_exp)list`;
                         `e:clos_exp`; `m:num`; `l:num`; `i:num spt`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "IH2")) THEN
    REMOVE_THEN "IH2" (fun th ->
      let th' = CONV_RULE (TOP_DEPTH_CONV let_CONV) th in
      ASSUME_TAC (GEN_ALL (CONJUNCT2 (SPEC_ALL th'))) THEN
      ASSUME_TAC (GEN_ALL (MATCH_MP IL1AUX_SHIFT_MAP
                                    (CONJUNCT1 (SPEC_ALL th'))))) THEN
    REWRITE_TAC[clos_annotate_shift_def; shift_sing_def] THEN
    CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[HD]
  and base_tac = REPEAT GEN_TAC THEN RW[clos_annotate_shift_def; shift_sing_def] in
  MATCH_MP_TAC shift_sing_ind THEN REPEAT CONJ_TAC THEN
  FIRST
   [(* clos_Letrec, by IL1AUX_SHIFT_MAP *)
    letrec_tac THEN NO_TAC;
    base_tac THEN NO_TAC;
    (* the list of expressions: HOL4's Cases_on es *)
    base_tac THEN CASES_ON `xs:clos_exp list` THEN
    GVS[clos_annotate_shift_def; shift_sing_def; APPEND]]);;

let shift_LENGTH_LEMMA = prove
 (`!xs m l i. LENGTH (clos_annotate_shift xs m l i) = LENGTH xs`,
  REWRITE_TAC[shift_sing_eq] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[shift_sing_def] THEN CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[LENGTH]);;

(* HOL4 states shift_SING as !ys. shift [x] m l i = ys ==> ?y. ys = [y]    *)
(* simplified to the form below                                              *)

let shift_SING = prove
 (`!x m l i. ?y. clos_annotate_shift [x] m l i = [y]`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`[x:clos_exp]`; `m:num`; `l:num`; `i:num spt`]
                shift_LENGTH_LEMMA) THEN
  SPEC_TAC (`clos_annotate_shift [x] m l i`,`ys:clos_exp list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

let shift_CONS = prove
 (`!x xs m l i.
     clos_annotate_shift (CONS (x:clos_exp) xs) m l i =
     let c1 = clos_annotate_shift [x] m l i in
     let c2 = clos_annotate_shift xs m l i in
       (CONS (HD c1) c2:clos_exp list)`,
  REPEAT GEN_TAC THEN CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
  X_CHOOSE_THEN `y:clos_exp` ASSUME_TAC
    (SPECL [`x:clos_exp`; `m:num`; `l:num`; `i:num spt`] shift_SING) THEN
  CASES_ON `xs:clos_exp list` THEN
  ASM_REWRITE_TAC[clos_annotate_shift_def; HD; APPEND] THEN
  CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[HD; APPEND]);;

let HD_shift = prove
 (`!x m l i. LENGTH (clos_annotate_shift [x] m l i) = 1 /\
             [HD (clos_annotate_shift [x] m l i)] = clos_annotate_shift [x] m l i`,
  REPEAT GEN_TAC THEN
  X_CHOOSE_THEN `y:clos_exp` SUBST1_TAC
    (SPECL [`x:clos_exp`; `m:num`; `l:num`; `i:num spt`] shift_SING) THEN
  REWRITE_TAC[LENGTH; HD; ONE]);;
let _ = cake_add_simps [HD_shift];;

(* main functions *)

(* HOL4: annotate *)

let clos_annotate_annotate_def = cake_def
  `clos_annotate_annotate arity xs = clos_annotate_shift (FST (alt_free xs)) 0 arity LN`;;

(* HOL4: compile *)

let clos_annotate_compile_def = cake_def
  `clos_annotate_compile (prog:(num # num # clos_exp) list) =
     MAP (\p. match p with
                (n,args,exp) -> (n,args,HD (clos_annotate_annotate args [exp])))
         prog`;;

(* HOL4: compile_inc *)

let clos_annotate_compile_inc_def = cake_def
  `clos_annotate_compile_inc (e,aux) =
     (clos_annotate_annotate 0 e,clos_annotate_compile aux)`;;

(* cv versions *)

let annotate_sing_def = cake_def
  `annotate_sing arity x = shift_sing (FST (alt_free_sing x)) 0 arity LN`;;

let annotate_list_def = cake_def
  `annotate_list arity xs = shift_list (FST (alt_free_list xs)) 0 arity LN`;;

let annotate_sing_eq = prove
 (`(!arity e. clos_annotate_annotate arity [e] = [annotate_sing arity e]) /\
   (!arity es. clos_annotate_annotate arity es = annotate_list arity es)`,
  REWRITE_TAC[clos_annotate_annotate_def; annotate_sing_def; annotate_list_def] THEN
  REWRITE_TAC[alt_free_sing_eq; shift_sing_eq] THEN REPEAT GEN_TAC THEN
  IL1AUX_PAIRARG_TAC THEN CASE_REWRITE_TAC[FST] THEN
  REWRITE_TAC[shift_sing_def] THEN CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[]);;

(* HOL4: compile_eq *)

let clos_annotate_compile_eq = prove
 (CASE_TERM
  `!prog:(num # num # clos_exp) list.
     clos_annotate_compile prog =
     MAP (\p. match p with (n,args,exp) -> (n,args,annotate_sing args exp)) prog`,
  REWRITE_TAC[clos_annotate_compile_def; annotate_sing_eq; HD]);;

(* HOL4: compile_inc_eq *)

let clos_annotate_compile_inc_eq = prove
 (`!e aux. clos_annotate_compile_inc (e,aux) =
           (annotate_list 0 e,clos_annotate_compile aux)`,
  REWRITE_TAC[clos_annotate_compile_inc_def; annotate_sing_eq]);;
