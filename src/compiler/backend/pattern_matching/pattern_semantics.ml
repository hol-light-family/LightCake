(* ========================================================================= *)
(* pattern_semantics: port of HOL4 compiler/backend/pattern_matching/       *)
(* pattern_semanticsScript.sml (CakeML v3479).                               *)
(* The syntax and semantics of the input and output to the pattern-match    *)
(* compiler.                                                                 *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's local type abbreviations kind = num, tag = num and siblings =    *)
(*   ((num # num) list) option are written out.                              *)
(* - HOL4 match is pattern_semantics_match (match is a HOL Light keyword).   *)
(* - The clauses of a HOL Light definition share their variables, so a name *)
(*   used with two types gets a second name (pmatch: the tag t of a Term is  *)
(*   tg).                                                                    *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/pattern_matching/pattern_common.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/ast.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* input syntax *)

let pattern_semantics_pat_INDUCT,pattern_semantics_pat_RECURSION = cake_type
  "pattern_semantics_pat =
     pattern_semantics_Any
   | pattern_semantics_Cons ((num # ((num # num) list) option) option)
                            (pattern_semantics_pat list)
   | pattern_semantics_Or pattern_semantics_pat pattern_semantics_pat
   | pattern_semantics_Lit lit
   | pattern_semantics_Ref pattern_semantics_pat";;

(* output syntax *)

let dTest_INDUCT,dTest_RECURSION = cake_type
  "dTest = pattern_semantics_TagLenEq num num | LitEq lit";;

let dGuard_INDUCT,dGuard_RECURSION = cake_type
  "dGuard = PosTest position dTest
          | pattern_semantics_Not dGuard
          | Conj dGuard dGuard
          | Disj dGuard dGuard
          | True";;

let dTree_INDUCT,dTree_RECURSION = cake_type
  "dTree = pattern_semantics_Leaf num
         | pattern_semantics_Fail
         | TypeFail
         | pattern_semantics_If dGuard dTree dTree";;

(* semantic values *)

let term_INDUCT,term_RECURSION = cake_type
  "term = Term (num option) (term list)
        | pattern_semantics_Litv lit
        | pattern_semantics_RefPtr num
        | pattern_semantics_Other";;

(* semantics of input *)

let is_sibling_def = cake_def
  `(is_sibling (x:A) NONE <=> T) /\
   (is_sibling x (SOME l) <=> MEM x l)`;;

(* HOL4: pmatch, pmatch_list *)

let pattern_semantics_pmatch_def = sem1aux_def_wf
  `measure
     (\x:((num,term)fmap # pattern_semantics_pat # term) +
         ((num,term)fmap # pattern_semantics_pat list # term list).
        sum_CASE x (\t. pattern_semantics_pat_size (FST (SND t)))
                   (\t. list_size pattern_semantics_pat_size (FST (SND t))))`
  SEM1AUX_TC_TAC
  `(pattern_semantics_pmatch refs pattern_semantics_Any t = PMatchSuccess) /\
   (pattern_semantics_pmatch refs (pattern_semantics_Lit l)
                             (pattern_semantics_Litv l') =
      if ~lit_same_type l l' then PTypeFailure else
      if l = l' then PMatchSuccess else PMatchFailure) /\
   (pattern_semantics_pmatch refs
      (pattern_semantics_Cons (SOME (tag,siblings)) pargs)
      (Term (SOME tg) targs) =
      if tag = tg /\ LENGTH pargs = LENGTH targs
      then pattern_semantics_pmatch_list refs pargs targs else
      if is_sibling (tg,LENGTH targs) siblings
      then PMatchFailure else PTypeFailure) /\
   (pattern_semantics_pmatch refs (pattern_semantics_Cons NONE pargs)
                             (Term NONE targs) =
      pattern_semantics_pmatch_list refs pargs targs) /\
   (pattern_semantics_pmatch refs (pattern_semantics_Ref p)
                             (pattern_semantics_RefPtr r) =
      match FLOOKUP refs r with
        NONE -> PTypeFailure
      | SOME v -> pattern_semantics_pmatch refs p v) /\
   (pattern_semantics_pmatch refs (pattern_semantics_Or p1 p2) t =
      match pattern_semantics_pmatch refs p1 t with
        PMatchSuccess -> (match pattern_semantics_pmatch refs p2 t with
                            PTypeFailure -> PTypeFailure
                          | _ -> PMatchSuccess)
      | PMatchFailure -> pattern_semantics_pmatch refs p2 t
      | PTypeFailure -> PTypeFailure) /\
   (pattern_semantics_pmatch refs _ _ = PTypeFailure) /\
   (pattern_semantics_pmatch_list refs [] [] = PMatchSuccess) /\
   (pattern_semantics_pmatch_list refs [] ts = PTypeFailure) /\
   (pattern_semantics_pmatch_list refs ps [] = PTypeFailure) /\
   (pattern_semantics_pmatch_list refs (CONS p ps) (CONS t ts) =
      match pattern_semantics_pmatch refs p t with
        PMatchSuccess -> pattern_semantics_pmatch_list refs ps ts
      | PMatchFailure -> (match pattern_semantics_pmatch_list refs ps ts with
                            PTypeFailure -> PTypeFailure
                          | _ -> PMatchFailure)
      | PTypeFailure -> PTypeFailure)`;;

let pattern_semantics_pmatch_ind = cake_ind "pattern_semantics_pmatch";;

(* HOL4: match *)

let pattern_semantics_match_def = cake_def
  `(pattern_semantics_match refs [] v = SOME MatchFailure) /\
   (pattern_semantics_match refs (CONS (p,e) rows) v =
      match pattern_semantics_pmatch refs p v with
        PMatchSuccess ->
          (match pattern_semantics_match refs rows v with
             NONE -> NONE
           | SOME _ -> SOME (MatchSuccess e))
      | PMatchFailure -> pattern_semantics_match refs rows v
      | PTypeFailure -> NONE)`;;

let pattern_semantics_match_ind = cake_ind "pattern_semantics_match";;

(* semantics of output *)

let dt_test_def = cake_def
  `(dt_test (pattern_semantics_TagLenEq t l) (Term (SOME c) args) =
      SOME (t = c /\ l = LENGTH args)) /\
   (dt_test (LitEq l1) (pattern_semantics_Litv l2) =
      if lit_same_type l1 l2 then SOME (l1 = l2) else NONE) /\
   (dt_test _ _ = NONE)`;;

let app_pos_def = sem1aux_def
  `(app_pos refs EmptyPos v = SOME v) /\
   (app_pos refs (Pos 0 pos) (pattern_semantics_RefPtr r) =
      match FLOOKUP refs r with
        NONE -> NONE
      | SOME v -> app_pos refs pos v) /\
   (app_pos refs (Pos 0 pos) (Term c (CONS x xs)) = app_pos refs pos x) /\
   (app_pos refs (Pos (SUC n) pos) (Term c (CONS x xs)) =
      app_pos refs (Pos n pos) (Term c xs)) /\
   (app_pos refs (Pos _ _) _ = NONE)`;;

let app_pos_ind = cake_ind "app_pos";;

(* HOL4's arms SOME T => e1 | SOME F => e2 are written as the one arm       *)
(* SOME b -> if b then e1 else e2 that HOL4 compiles them to (the kit reads *)
(* T and F as literal tests, which would leave an unreachable ARB branch)   *)

let dt_eval_guard_def = cake_def
  `(dt_eval_guard refs v True = SOME T) /\
   (dt_eval_guard refs v (PosTest pos test) =
      match app_pos refs pos v with
        NONE -> NONE
      | SOME x -> dt_test test x) /\
   (dt_eval_guard refs v (pattern_semantics_Not g) =
      match dt_eval_guard refs v g with
        NONE -> NONE
      | SOME b -> SOME (~b)) /\
   (dt_eval_guard refs v (Conj g1 g2) =
      match dt_eval_guard refs v g1 with
        NONE -> NONE
      | SOME b -> if b then dt_eval_guard refs v g2 else SOME F) /\
   (dt_eval_guard refs v (Disj g1 g2) =
      match dt_eval_guard refs v g1 with
        NONE -> NONE
      | SOME b -> if b then SOME T else dt_eval_guard refs v g2)`;;

let dt_eval_guard_ind = cake_ind "dt_eval_guard";;

(* termination as HOL4's automatic proof: the size of the decision tree *)

let dt_eval_def = cake_def_wf
  `measure (\x:(num,term)fmap # term # dTree. dTree_size (SND (SND x)))`
  (TERM_TAC ORELSE (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN TERM_TAC))
  `(dt_eval refs _ (pattern_semantics_Leaf k) = SOME (MatchSuccess k)) /\
   (dt_eval refs _ pattern_semantics_Fail = SOME MatchFailure) /\
   (dt_eval refs _ TypeFail = NONE) /\
   (dt_eval refs v (pattern_semantics_If guard dt1 dt2) =
      match dt_eval_guard refs v guard with
        NONE -> NONE
      | SOME b -> dt_eval refs v (if b then dt1 else dt2))`;;

let dt_eval_ind = cake_ind "dt_eval";;
