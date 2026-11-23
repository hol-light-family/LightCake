(* ========================================================================= *)
(* bvi_let: port of HOL4 compiler/backend/bvi_letScript.sml (CakeML v3479).  *)
(* This is a BVI transformation that propagates variable lookups that are    *)
(* immediately assigned to a new variable in Let bindings. This              *)
(* optimisation is to run immediately when entering BVI.                     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/bvi.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - HOL4 LLOOKUP env v is oEL v env; HOL4 exp2_size is                      *)
(*   list_size bvi_exp_size.                                                 *)
(* - The clauses of a HOL Light definition share their variables, so the     *)
(*   target of LetCall (HOL4 dest, also the name of the num option of        *)
(*   bvi_Call) is dest'.                                                     *)
(* - compile and compile_sing are made with sem1aux_def_wf (HOL4's TFL       *)
(*   completion of the overlapping clauses); HOL4's termination relations.   *)
(*   The recursion package gives a recursive call under let l = e no         *)
(*   context l = e, so the two definitions are first made with the lets      *)
(*   l = LENGTH xs and k = l - 1 of the Let clause written out (which gives  *)
(*   the induction theorems), and the clauses as HOL4 writes them are then   *)
(*   proved from them.                                                       *)
(* - HOL4 delete_var_ind (a case analysis) is made by BVIPAUX_LET_case_ind. *)

let bvi_let_extract_def = sem1aux_def
  `(bvi_let_extract (bvi_Var n) (ys:A list) = n + LENGTH ys + 1) /\
   (bvi_let_extract _ _ = 0)`;;

let bvi_let_extract_list_def = cake_def
  `(bvi_let_extract_list [] = []) /\
   (bvi_let_extract_list (CONS x xs) =
      CONS (bvi_let_extract x xs) (bvi_let_extract_list xs))`;;

let bvi_let_delete_var_def = sem1aux_def
  `(bvi_let_delete_var (bvi_Var n) = bvi_Op (IntOp (clos_Const (&0))) []) /\
   (bvi_let_delete_var x = x)`;;

(* the induction theorem (a case analysis) that HOL4 makes for a            *)
(* non-recursive definition by patterns: one case per clause of the         *)
(* definition theorem def (the completed clauses)                          *)

let BVIPAUX_LET_case_ind (def:thm) : thm =
  let cls = map (fun cl -> let vs,eq = strip_forall cl in
                           let c,args = strip_comb(lhs eq) in vs,c,args)
                (conjuncts(concl def)) in
  let _,c,args0 = hd cls in
  let tty = mk_tuple_ty (map type_of args0) in
  let wfth = ISPEC (mk_abs(mk_var("x",tty),`0`)) WF_MEASURE in
  derive_induction c (map (fun (vs,_,args) -> vs,args) cls) [] wfth;;

let bvi_let_delete_var_ind = BVIPAUX_LET_case_ind bvi_let_delete_var_def;;

let exp2_size_APPEND = prove
 (`!xs ys. list_size bvi_exp_size (APPEND xs ys) =
           list_size bvi_exp_size xs + list_size bvi_exp_size ys`,
  REWRITE_TAC[list_size_append]);;

(* the size facts of HOL4's termination proofs (by SNOC_CASES there) *)

let BVIPAUX_LET_list_size_BUTLAST = prove
 (`!f (l:A list). list_size f (BUTLAST l) <= list_size f l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[BUTLAST; list_size; LE_REFL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[list_size] THEN ASM_ARITH_TAC);;

let BVIPAUX_LET_list_size_LAST = prove
 (`!f (l:A list). ~(l = []) ==> f (LAST l) < list_size f l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LAST; list_size; NOT_CONS_NIL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[list_size] THENL
   [ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC]);;

(* the termination tactic: the kit's TERM_TAC with the two facts above for  *)
(* the BUTLAST and LAST terms of the goal                                   *)

let BVIPAUX_LET_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  (fun (asl,w as g) ->
     let has c t = is_comb t && is_const(rator t) &&
                   fst(dest_const(rator t)) = c in
     let bls = find_terms (has "BUTLAST") w
     and ls = find_terms (has "LAST") w in
     (MAP_EVERY (fun t -> ASSUME_TAC
         (ISPECL [`bvi_exp_size`; rand t] BVIPAUX_LET_list_size_BUTLAST)) bls THEN
      MAP_EVERY (fun t -> ASSUME_TAC
         (REWRITE_RULE[GSYM LENGTH_EQ_NIL]
            (ISPECL [`bvi_exp_size`; rand t] BVIPAUX_LET_list_size_LAST))) ls) g) THEN
  TERM_TAC;;

(* the definition with the lets l and k written out *)

let BVIPAUX_LET_compile_def0 = sem1aux_def_wf
  `MEASURE (\p:num list # num # bvi_exp list. list_size bvi_exp_size (SND (SND p)))`
  BVIPAUX_LET_TC_TAC
  `(bvi_let_compile env d [] = []) /\
   (bvi_let_compile env d (CONS x (CONS y xs)) =
      APPEND (bvi_let_compile env d [x]) (bvi_let_compile env d (CONS y xs))) /\
   (bvi_let_compile env d [bvi_Var v] =
      match oEL v env with
        SOME n -> [bvi_Var (v + n)]
      | _ -> [bvi_Var (v + d)]) /\
   (bvi_let_compile env d [bvi_If x1 x2 x3] =
      [bvi_If (HD (bvi_let_compile env d [x1]))
              (HD (bvi_let_compile env d [x2]))
              (HD (bvi_let_compile env d [x3]))]) /\
   (bvi_let_compile env d [bvi_Let xs x2] =
      if LENGTH xs = 0 then bvi_let_compile env d [x2] else
        if x2 = bvi_Var (LENGTH xs - 1) then
          let ys = bvi_let_compile env d (BUTLAST xs) in
            [bvi_Let ys (HD (bvi_let_compile (MAP ((+) (LENGTH xs - 1)) env)
                               (d + (LENGTH xs - 1)) [LAST xs]))]
        else
          let ys = bvi_let_compile env d xs in
            [bvi_Let (MAP bvi_let_delete_var ys)
               (HD (bvi_let_compile (APPEND (bvi_let_extract_list ys) env)
                      d [x2]))]) /\
   (bvi_let_compile env d [bvi_Raise x1] =
      [bvi_Raise (HD (bvi_let_compile env d [x1]))]) /\
   (bvi_let_compile env d [bvi_Op op xs] = [bvi_Op op (bvi_let_compile env d xs)]) /\
   (bvi_let_compile env d [bvi_Tick x] = [bvi_Tick (HD (bvi_let_compile env d [x]))]) /\
   (bvi_let_compile env d [bvi_Force loc v] =
      match oEL v env with
        SOME n -> [bvi_Force loc (v + n)]
      | _ -> [bvi_Force loc (v + d)]) /\
   (bvi_let_compile env d [bvi_Call t dest xs h] =
      [bvi_Call t dest (bvi_let_compile env d xs)
         (match h with
            NONE -> NONE
          | SOME e -> SOME (HD (bvi_let_compile (CONS 0 env) d [e])))]) /\
   (bvi_let_compile env d [bvi_Return xs] =
      [bvi_Return (bvi_let_compile env d xs)]) /\
   (bvi_let_compile env d [LetCall rets t dest' xs y] =
      [LetCall rets t dest' (bvi_let_compile env d xs)
         (HD (bvi_let_compile (APPEND (REPLICATE rets 0) env) d [y]))])`;;

let bvi_let_compile_ind = cake_ind "bvi_let_compile";;

(* HOL4: compile_def (the clauses as HOL4 writes them) *)

let bvi_let_compile_def =
  let cs = CONJUNCTS BVIPAUX_LET_compile_def0 in
  let let_cl = prove
   (`!env d xs x2.
       bvi_let_compile env d [bvi_Let xs x2] =
       let l = LENGTH xs in
         if l = 0 then bvi_let_compile env d [x2] else
           let k = l - 1 in
             if x2 = bvi_Var k then
               let ys = bvi_let_compile env d (BUTLAST xs) in
                 [bvi_Let ys (HD (bvi_let_compile (MAP ((+) k) env) (d + k)
                                    [LAST xs]))]
             else
               let ys = bvi_let_compile env d xs in
                 [bvi_Let (MAP bvi_let_delete_var ys)
                    (HD (bvi_let_compile (APPEND (bvi_let_extract_list ys) env)
                           d [x2]))]`,
    REWRITE_TAC[el 4 cs; LET_DEF; LET_END_DEF]) in
  end_itlist CONJ (map (fun (i,c) -> if i = 4 then let_cl else c)
                       (zip (0--(length cs - 1)) cs));;

(* the mutual definition with the lets l and k written out *)

let BVIPAUX_LET_compile_sing_def0 = sem1aux_def_wf
  `MEASURE (\x:(num list # num # bvi_exp) + (num list # num # bvi_exp list).
              sum_CASE x (\p. bvi_exp_size (SND (SND p)))
                         (\p. list_size bvi_exp_size (SND (SND p))))`
  BVIPAUX_LET_TC_TAC
  `(bvi_let_compile_sing env d (bvi_Var v) =
      match oEL v env with
        SOME n -> bvi_Var (v + n)
      | _ -> bvi_Var (v + d)) /\
   (bvi_let_compile_sing env d (bvi_If x1 x2 x3) =
      bvi_If (bvi_let_compile_sing env d x1)
             (bvi_let_compile_sing env d x2)
             (bvi_let_compile_sing env d x3)) /\
   (bvi_let_compile_sing env d (bvi_Let xs x2) =
      if LENGTH xs = 0 then bvi_let_compile_sing env d x2 else
        if x2 = bvi_Var (LENGTH xs - 1) then
          let ys = bvi_let_compile_list env d (BUTLAST xs) in
            bvi_Let ys (bvi_let_compile_sing (MAP ((+) (LENGTH xs - 1)) env)
                          (d + (LENGTH xs - 1)) (LAST xs))
        else
          let ys = bvi_let_compile_list env d xs in
            bvi_Let (MAP bvi_let_delete_var ys)
              (bvi_let_compile_sing (APPEND (bvi_let_extract_list ys) env) d x2)) /\
   (bvi_let_compile_sing env d (bvi_Raise x1) =
      bvi_Raise (bvi_let_compile_sing env d x1)) /\
   (bvi_let_compile_sing env d (bvi_Op op xs) =
      bvi_Op op (bvi_let_compile_list env d xs)) /\
   (bvi_let_compile_sing env d (bvi_Tick x) =
      bvi_Tick (bvi_let_compile_sing env d x)) /\
   (bvi_let_compile_sing env d (bvi_Force loc v) =
      match oEL v env with
        SOME n -> bvi_Force loc (v + n)
      | _ -> bvi_Force loc (v + d)) /\
   (bvi_let_compile_sing env d (bvi_Call t dest xs h) =
      bvi_Call t dest (bvi_let_compile_list env d xs)
        (match h with
           NONE -> NONE
         | SOME e -> SOME (bvi_let_compile_sing (CONS 0 env) d e))) /\
   (bvi_let_compile_sing env d (bvi_Return xs) =
      bvi_Return (bvi_let_compile_list env d xs)) /\
   (bvi_let_compile_sing env d (LetCall rets t dest' xs y) =
      LetCall rets t dest' (bvi_let_compile_list env d xs)
        (bvi_let_compile_sing (APPEND (REPLICATE rets 0) env) d y)) /\
   (bvi_let_compile_list env d [] = []) /\
   (bvi_let_compile_list env d (CONS x xs) =
      CONS (bvi_let_compile_sing env d x) (bvi_let_compile_list env d xs))`;;

let bvi_let_compile_sing_ind = cake_ind "bvi_let_compile_sing";;

(* HOL4: compile_sing_def (the clauses as HOL4 writes them) *)

let bvi_let_compile_sing_def =
  let cs = CONJUNCTS BVIPAUX_LET_compile_sing_def0 in
  let let_cl = prove
   (`!env d xs x2.
       bvi_let_compile_sing env d (bvi_Let xs x2) =
       let l = LENGTH xs in
         if l = 0 then bvi_let_compile_sing env d x2 else
           let k = l - 1 in
             if x2 = bvi_Var k then
               let ys = bvi_let_compile_list env d (BUTLAST xs) in
                 bvi_Let ys (bvi_let_compile_sing (MAP ((+) k) env) (d + k)
                               (LAST xs))
             else
               let ys = bvi_let_compile_list env d xs in
                 bvi_Let (MAP bvi_let_delete_var ys)
                   (bvi_let_compile_sing (APPEND (bvi_let_extract_list ys) env)
                      d x2)`,
    REWRITE_TAC[el 2 cs; LET_DEF; LET_END_DEF]) in
  end_itlist CONJ (map (fun (i,c) -> if i = 2 then let_cl else c)
                       (zip (0--(length cs - 1)) cs));;

let bvi_let_compile_sing = prove
 (`(!n d e. bvi_let_compile n d [e] = [bvi_let_compile_sing n d e]) /\
   (!n d e. bvi_let_compile_list n d e = bvi_let_compile n d e)`,
  MATCH_MP_TAC bvi_let_compile_sing_ind THEN REPEAT STRIP_TAC THEN
  GVS[bvi_let_compile_sing_def; bvi_let_compile_def] THEN
  EVERY_CASE_TAC THEN GVS[] THEN
  CASES_ON `xs:bvi_exp list` THEN GVS[] THEN
  GVS[bvi_let_compile_sing_def; bvi_let_compile_def]);;

let bvi_let_compile_length = prove
 (`!n d xs. LENGTH (bvi_let_compile n d xs) = LENGTH xs`,
  MATCH_MP_TAC bvi_let_compile_ind THEN REPEAT STRIP_TAC THEN
  FS[bvi_let_compile_def; LENGTH_APPEND] THEN
  EVERY_CASE_TAC THEN RW[] THEN ASM_ARITH_TAC);;
let _ = cake_add_simps [bvi_let_compile_length];;

let bvi_let_compile_HD_SING = prove
 (`!n d x. [HD (bvi_let_compile n d [x])] = bvi_let_compile n d [x]`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`n:num list`; `d:num`; `[x:bvi_exp]`] bvi_let_compile_length) THEN
  CASES_ON `bvi_let_compile n d [x]` THEN FS[LENGTH_EQ_NIL]);;

let bvi_let_compile_exp_def = cake_def
  `bvi_let_compile_exp x =
     match bvi_let_compile [] 0 [x] with
       CONS y _ -> y
     | _ -> bvi_Var 0`;;

let bvi_let_compile_exp_eq = prove
 (`!x. bvi_let_compile_exp x = bvi_let_compile_sing [] 0 x`,
  SIMP[bvi_let_compile_exp_def; bvi_let_compile_sing]);;
