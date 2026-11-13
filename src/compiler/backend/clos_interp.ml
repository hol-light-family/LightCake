(* ========================================================================= *)
(* clos_interp: port of HOL4 compiler/backend/clos_interpScript.sml (CakeML  *)
(* v3479).                                                                   *)
(* Implementation of interpreter for closLang expressions written in        *)
(* closLang.                                                                 *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's local overloads V, IsCase, GetEl, CallInterp and CallInterpList  *)
(*   are expanded: the quotations of clos_interp_el, clos_interp_rev and     *)
(*   clos_interpreter_body are built by the OCaml functions il1aux_v ...     *)
(*   below, so the definitions are HOL4's expanded terms.                    *)
(* - HOL4's pmatch case expressions are written with match like all others, *)
(*   so the NAME_pmatch theorems restate the definitions in match form.      *)
(* - HOL4 None (the trace) is backend_common_None; IS_NONE and the mlstring  *)
(*   literals implode "...".                                                 *)
(* - The definitions with catch-all clauses or two mutually recursive        *)
(*   functions are made with sem1aux_def(_wf) (semantics/sem1aux_tfl.ml);    *)
(*   where HOL4's termination is automatic, the relation is its size measure.*)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/backend_common.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* fits in subset *)

let can_interpret_op_def = sem1aux_def
  `(can_interpret_op (BlockOp (clos_Cons tag)) l <=> l = 0 \/ tag < 3) /\
   (can_interpret_op (IntOp (clos_Const i)) l <=> l = 0) /\
   (can_interpret_op (GlobOp (clos_Global n)) l <=> l = 0) /\
   (can_interpret_op (BlockOp (Constant c)) l <=> l = 0) /\
   (can_interpret_op _ l <=> F)`;;

let can_interpret_def = sem1aux_def_wf
  `measure (\x:clos_exp + clos_exp list.
              sum_CASE x clos_exp_size (list_size clos_exp_size))`
  SEM1AUX_TC_TAC
  `(can_interpret (clos_Var t n) <=> T) /\
   (can_interpret (clos_If t e1 e2 e3) <=>
      can_interpret e1 /\ can_interpret e2 /\ can_interpret e3) /\
   (can_interpret (clos_Let t es e) <=> can_interpret e /\ can_interpret_list es) /\
   (can_interpret (clos_Op t p es) <=>
      can_interpret_op p (LENGTH es) /\ can_interpret_list es) /\
   (can_interpret (clos_Raise t e) <=> can_interpret e) /\
   (can_interpret (clos_Tick t e) <=> can_interpret e) /\
   (can_interpret (Fn _ _ _ _ e) <=> F) /\
   (can_interpret (clos_Handle t e1 e2) <=> can_interpret e1 /\ can_interpret e2) /\
   (can_interpret (clos_Call _ _ _ es) <=> F) /\
   (can_interpret (clos_App _ opt e es) <=>
      IS_NONE opt /\ can_interpret e /\ can_interpret_list es /\ LENGTH es = 1) /\
   (can_interpret (clos_Letrec _ _ _ fns e) <=> F) /\
   (can_interpret_list [] <=> T) /\
   (can_interpret_list (CONS x xs) <=> can_interpret x /\ can_interpret_list xs)`;;

let can_interpret_ind = cake_ind "can_interpret";;

(* check size *)

let check_size_op_def = sem1aux_def
  `(check_size_op k (BlockOp (clos_Cons tag)) l =
      if l = 0:num then k else k - 1:num) /\
   (check_size_op k (IntOp (clos_Const i)) l = (k:num)) /\
   (check_size_op k (GlobOp (clos_Global n)) l = k) /\
   (check_size_op k _ l = k - 1)`;;

let check_size_def = sem1aux_def_wf
  `measure (\x:(num # clos_exp) + (num # clos_exp list).
              sum_CASE x (\p. clos_exp_size (SND p))
                         (\p. list_size clos_exp_size (SND p)))`
  SEM1AUX_TC_TAC
  `(check_size k (clos_Var t n) = (k:num)) /\
   (check_size k (clos_If t e1 e2 e3) =
      let k = check_size k e1 in if k = 0 then 0 else
      let k = check_size k e2 in if k = 0 then 0 else
        check_size k e3) /\
   (check_size k (clos_Let t es e) =
      let k = check_size_list k es in if k = 0 then 0 else
        check_size k e) /\
   (check_size k (clos_Op t p es) =
      let k = check_size_op k p (LENGTH es) in if k = 0 then 0 else
        check_size_list k es) /\
   (check_size k (clos_Raise t e) = check_size k e) /\
   (check_size k (clos_Tick t e) = check_size k e) /\
   (check_size k (Fn _ _ _ _ e) = k) /\
   (check_size k (clos_Handle t e1 e2) =
      let k = check_size k e1 in if k = 0 then 0 else
        check_size k e2) /\
   (check_size k (clos_Call _ _ _ es) = k) /\
   (check_size k (clos_App _ _ e es) =
      let k = check_size (k - 1) e in if k = 0 then 0 else
        check_size_list k es) /\
   (check_size k (clos_Letrec _ _ _ fns e) = k) /\
   (check_size_list k [] = k) /\
   (check_size_list k (CONS x xs) =
      let k = check_size k x in if k = 0 then 0 else
        check_size_list k xs)`;;

let check_size_ind = cake_ind "check_size";;

let nontrivial_size_def = cake_def
  `nontrivial_size e <=> check_size 8 e = 0`;;

(* convert to const *)

let to_constant_op_def = sem1aux_def
  `(to_constant_op (IntOp (clos_Const i)) (l:num) (cs:const) =
      ConstCons 1 [ConstInt i]) /\
   (to_constant_op (BlockOp (Constant c)) l cs = ConstCons 1 [c]) /\
   (to_constant_op (GlobOp (clos_Global n)) l cs =
      ConstCons 2 [ConstInt (&n)]) /\
   (to_constant_op (BlockOp (clos_Cons tag)) l cs =
      if l = 0 then ConstCons 1 [ConstCons tag []]
      else ConstCons (tag + 5) [cs]) /\
   (to_constant_op _ l cs = ConstInt (&0))`;;

let to_constant_def = sem1aux_def_wf
  `measure (\x:clos_exp + clos_exp list.
              sum_CASE x clos_exp_size (list_size clos_exp_size))`
  SEM1AUX_TC_TAC
  `(to_constant (clos_Var t n) = ConstCons 0 [ConstInt (&n)]) /\
   (to_constant (clos_App _ _ e es) =
      ConstCons 0 [to_constant e;
                   match es with [] -> ConstInt (&0) | CONS e1 _ -> to_constant e1]) /\
   (to_constant (clos_If t e1 e2 e3) =
      ConstCons 0 [to_constant e1; to_constant e2; to_constant e3]) /\
   (to_constant (clos_Let t es e) =
      ConstCons 1 [to_constant_list es; to_constant e]) /\
   (to_constant (clos_Op t p es) =
      to_constant_op p (LENGTH es) (to_constant_list es)) /\
   (to_constant (clos_Raise t e) = ConstCons 3 [to_constant e]) /\
   (to_constant (clos_Tick t e) = ConstCons 4 [to_constant e]) /\
   (to_constant (clos_Handle t e1 e2) =
      ConstCons 2 [to_constant e1; to_constant e2]) /\
   (to_constant (Fn _ _ _ _ e) = ConstInt (&0)) /\
   (to_constant (clos_Call _ _ _ es) = ConstInt (&0)) /\
   (to_constant (clos_Letrec _ _ _ fns e) = ConstInt (&0)) /\
   (to_constant_list [] = ConstCons 0 []) /\
   (to_constant_list (CONS x xs) =
      ConstCons 0 [to_constant x; to_constant_list xs])`;;

let to_constant_ind = cake_ind "to_constant";;

(* interpreter as closLang program *)

(* HOL4's local overloads: V n = Var None n; IsCase tag len = If None (Op   *)
(* None (BlockOp (TagLenEq tag len)) [V 0]); GetEl n x = Op None (BlockOp  *)
(* (ElemAt n)) [x]; CallInterp env x and CallInterpList env x apply the     *)
(* interpreter in global 0 to env, to Op None (BlockOp (Cons k)) [] (k = 0  *)
(* and 1) and to x.  As OCaml functions building quotation text:           *)

let il1aux_v n = "(clos_Var backend_common_None " ^ n ^ ")";;

let il1aux_getel n x =
  "(clos_Op backend_common_None (BlockOp (ElemAt " ^ n ^ ")) [" ^ x ^ "])";;

let il1aux_iscase tag len a b =
  "(clos_If backend_common_None (clos_Op backend_common_None " ^
  "(BlockOp (clos_TagLenEq " ^ tag ^ " " ^ len ^ ")) [" ^ il1aux_v "0" ^ "]) " ^
  a ^ " " ^ b ^ ")";;

let il1aux_call k env x =
  "(clos_App backend_common_None NONE (clos_App backend_common_None NONE " ^
  "(clos_App backend_common_None NONE (clos_Op backend_common_None " ^
  "(GlobOp (clos_Global 0)) []) [" ^ env ^ "]) " ^
  "[clos_Op backend_common_None (BlockOp (clos_Cons " ^ k ^ ")) []]) [" ^ x ^ "])";;

let il1aux_call_interp = il1aux_call "0";;
let il1aux_call_interp_list = il1aux_call "1";;

let clos_interp_el_def = cake_def (parse_term (
  "clos_interp_el = " ^
  "clos_If backend_common_None " ^
  "(clos_Op backend_common_None (BlockOp (EqualConst (clos_Int (&0)))) [" ^
  il1aux_v "1" ^ "]) " ^
  il1aux_getel "0" (il1aux_v "0") ^ " " ^
  "(clos_App backend_common_None NONE (clos_App backend_common_None NONE " ^
  il1aux_v "2" ^
  " [clos_Op backend_common_None (IntOp clos_Sub) " ^
  "[clos_Op backend_common_None (IntOp (clos_Const (&1))) []; " ^ il1aux_v "1" ^
  "]]) [" ^ il1aux_getel "1" (il1aux_v "0") ^ "])"));;

let clos_interp_rev_def = cake_def (parse_term (
  "clos_interp_rev = " ^
  "clos_If backend_common_None " ^
  "(clos_Op backend_common_None (BlockOp (clos_LenEq 0)) [" ^ il1aux_v "1" ^ "]) " ^
  il1aux_v "0" ^ " " ^
  "(clos_App backend_common_None NONE (clos_App backend_common_None NONE " ^
  il1aux_v "2" ^ " [" ^ il1aux_getel "1" (il1aux_v "1") ^ "]) " ^
  "[clos_Op backend_common_None (BlockOp (clos_Cons 0)) [" ^ il1aux_v "0" ^ "; " ^
  il1aux_getel "0" (il1aux_v "1") ^ "]])"));;

(* the cases of clos_interpreter_body: the _list version; App; Constant;   *)
(* Global; Var; Let; Handle; If; Raise; Tick; Cons for non-empty payload   *)
(* (Cons 0, Cons 1, Cons 2)                                                 *)

let clos_interpreter_body_def =
  let v = il1aux_v and getel = il1aux_getel and iscase = il1aux_iscase
  and ci = il1aux_call_interp and cil = il1aux_call_interp_list in
  let op opn args = "(clos_Op backend_common_None " ^ opn ^ " [" ^ args ^ "])" in
  let app f args = "(clos_App backend_common_None NONE " ^ f ^ " [" ^ args ^ "])" in
  let let_ args body = "(clos_Let backend_common_None [" ^ args ^ "] " ^ body ^ ")" in
  let letrec fn body =
    "(clos_Letrec [] NONE NONE [(1,Fn (implode \"\") NONE NONE 1 " ^ fn ^ ")] " ^
    body ^ ")" in
  let if_ a b c = "(clos_If backend_common_None " ^ a ^ " " ^ b ^ " " ^ c ^ ")" in
  let body =
    if_ (v "1")
      (if_ (op "(BlockOp (clos_LenEq 0))" (v "0")) (v "0")
         (let_ (ci (v "2") (getel "0" (v "0")) ^ "; " ^
                cil (v "2") (getel "1" (v "0")))
               (op "(BlockOp (clos_Cons 0))" (v "1" ^ "; " ^ v "0"))))
      (iscase "0" "2"
         (app (ci (v "2") (getel "0" (v "0"))) (ci (v "2") (getel "1" (v "0"))))
      (iscase "1" "1" (getel "0" (v "0"))
      (iscase "2" "1" (op "(GlobOp (clos_Global 0))" (getel "0" (v "0")))
      (iscase "0" "1"
         (letrec "clos_interp_el"
            (app (app (v "0") (getel "0" (v "1"))) (v "3")))
      (iscase "1" "2"
         (let_ (cil (v "2") (getel "0" (v "0")))
               (ci (op "(BlockOp clos_ListAppend)" (v "3" ^ "; " ^ v "0"))
                   (getel "1" (v "1"))))
      (iscase "2" "2"
         ("(clos_Handle backend_common_None " ^ ci (v "2") (getel "0" (v "0")) ^ " " ^
          ci (op "(BlockOp (clos_Cons 0))" (v "3" ^ "; " ^ v "0"))
             (getel "1" (v "1")) ^ ")")
      (iscase "0" "3"
         (if_ (ci (v "2") (getel "0" (v "0")))
              (ci (v "2") (getel "1" (v "0")))
              (ci (v "2") (getel "2" (v "0"))))
      (iscase "3" "1"
         ("(clos_Raise backend_common_None " ^ ci (v "2") (getel "0" (v "0")) ^ ")")
      (iscase "4" "1" (ci (v "2") (getel "0" (v "0")))
      (let_ (cil (v "2") (getel "0" (v "0")))
      (letrec "clos_interp_rev"
      (let_ (app (app (v "0") (v "1")) (op "(BlockOp (clos_Cons 0))" ""))
      (let_ (v "3")
      (iscase "5" "1" (op "(BlockOp (FromList 0))" (v "1"))
      (iscase "6" "1" (op "(BlockOp (FromList 1))" (v "1"))
      (iscase "7" "1" (op "(BlockOp (FromList 2))" (v "1"))
      (op "(BlockOp (clos_Cons 0))" ""))))))))))))))))) in
  cake_def (parse_term ("clos_interpreter_body = " ^ body));;

let clos_interpreter_def = cake_def
  `clos_interpreter =
     Fn (implode "env") NONE NONE 1
       (Fn (implode "exp") NONE NONE 1 clos_interpreter_body)`;;

(* functions that insert calls to interpreter *)

let opt_interp_def = cake_def (parse_term (
  "opt_interp e = " ^
  "if can_interpret e /\\ nontrivial_size e then SOME " ^
  il1aux_call_interp "(clos_Op backend_common_None (BlockOp (clos_Cons 0)) [])"
    "(clos_Op backend_common_None (BlockOp (Constant (to_constant e))) [])" ^
  " else NONE"));;

let opt_interp1_def = cake_def
  `opt_interp1 e = match opt_interp e with SOME x -> x | NONE -> e`;;

let insert_interp1_def = cake_def
  `insert_interp1 e =
     match opt_interp e with
       SOME x -> x
     | NONE ->
         (match e with
            clos_Let t ys y -> clos_Let backend_common_None (MAP opt_interp1 ys) y
          | _ -> e)`;;

let compile_init_def = cake_def
  `compile_init b =
     clos_Let backend_common_None
       [clos_Op backend_common_None (GlobOp AllocGlobal)
          [clos_Op backend_common_None (IntOp (clos_Const (&1))) []];
        if b then Fn (implode "clos_interpreter") NONE NONE 1 clos_interpreter
        else clos_Op backend_common_None (BlockOp (clos_Cons 0)) []]
       (clos_Op backend_common_None (GlobOp (SetGlobal 0))
          [clos_Var backend_common_None 1])`;;

let attach_interpreter_def = cake_def
  `attach_interpreter xs = CONS (compile_init (has_install_list xs)) xs`;;

let insert_interp_def = cake_def
  `insert_interp xs = MAP insert_interp1 xs`;;

(* pmatch versions of the op-functions *)

let IL1AUX_INTERP_PMATCH_TAC (defs:thm list) : tactic =
  REPEAT GEN_TAC THEN REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC defs) THEN
  FS defs;;

let can_interpret_op_pmatch = prove
 (CASE_TERM
  `!p l. can_interpret_op p l <=>
         match p with
           BlockOp (clos_Cons tag) -> (l = 0 \/ tag < 3)
         | IntOp (clos_Const i) -> (l = 0)
         | GlobOp (clos_Global n) -> (l = 0)
         | BlockOp (Constant c) -> (l = 0)
         | _ -> F`,
  IL1AUX_INTERP_PMATCH_TAC[can_interpret_op_def]);;

let check_size_op_pmatch = prove
 (CASE_TERM
  `!k p l. check_size_op k p l =
           match p with
             BlockOp (clos_Cons tag) -> (if l = 0:num then k else k - 1:num)
           | IntOp (clos_Const i) -> k
           | GlobOp (clos_Global n) -> k
           | _ -> k - 1`,
  IL1AUX_INTERP_PMATCH_TAC[check_size_op_def]);;

let to_constant_op_pmatch = prove
 (CASE_TERM
  `!p l cs. to_constant_op p l cs =
            match p with
              IntOp (clos_Const i) -> ConstCons 1 [ConstInt i]
            | BlockOp (Constant c) -> ConstCons 1 [c]
            | GlobOp (clos_Global n) -> ConstCons 2 [ConstInt (&n)]
            | BlockOp (clos_Cons tag) ->
                (if l = 0 then ConstCons 1 [ConstCons tag []]
                 else ConstCons (tag + 5) [cs])
            | _ -> ConstInt (&0)`,
  IL1AUX_INTERP_PMATCH_TAC[to_constant_op_def]);;
