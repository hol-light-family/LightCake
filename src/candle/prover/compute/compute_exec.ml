(* ========================================================================= *)
(* compute_exec: port of HOL4 candle/prover/compute/compute_execScript.sml   *)
(* (CakeML v3479).  Fast interpreter function for the Candle compute         *)
(* primitive.                                                                *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The overloads of compute_syntax (_CEXP_NUM, ...) are read by its parser *)
(*   extension (see the header of compute_syntax.ml).                        *)
(* - Names as doc/names.tsv says: the constructors of cv and ce are *)
(*   compute_exec_Num, compute_exec_Pair, compute_exec_Const, ...,           *)
(*   compute_exec_Let; monop, binop and their families take the prefix       *)
(*   compute_ (compute_monop_fst, compute_binop_add, ...).  HOL4's mlvector  *)
(*   length and sub are regexp_compiler_length and regexp_compiler_sub (see  *)
(*   the header of basis/pure/mlvector.ml).                                  *)
(* - The do-notation is written with the constants of ml_monadBase.ml, as in *)
(*   compute_eval.ml; timeout is holKernel_raise_Failure (implode "timeout").*)
(* - HOL4's monop_def has the clause monop IsPair = monop_ispair, IsPair a   *)
(*   variable (the constructor is Ispair), which TFL completes to            *)
(*   monop Ispair = monop_ispair: that is the clause written here.           *)
(* ========================================================================= *)

needs "candle/standard/monadic/holKernel.ml";;
needs "candle/prover/compute/compute_eval.ml";;
needs "basis/pure/mlvector.ml";;

prioritize_num();;
type_invention_error := true;;

compute_overloads_on ();;

(* ------------------------------------------------------------------------- *)
(* execute engine                                                            *)
(* ------------------------------------------------------------------------- *)

let cv_INDUCT,cv_RECURSION =
  cake_type "cv = compute_exec_Num num | compute_exec_Pair cv cv";;

let ce_INDUCT,ce_RECURSION =
  cake_type "ce = compute_exec_Const num
                | compute_exec_Var num
                | compute_exec_Monop (cv->cv) ce
                | compute_exec_Binop (cv->cv->cv) ce ce
                | compute_exec_App num (ce list)
                | compute_exec_If ce ce ce
                | compute_exec_Let ce ce";;

let env_lookup_def = cake_def
  `(env_lookup n [] = compute_exec_Num 0) /\
   (env_lookup n (CONS x xs) = if n = 0 then x else env_lookup (n - 1) xs)`;;

let get_code_def = cake_def
  `get_code f (funs:ce vector) =
     if f < regexp_compiler_length funs then
       st_ex_return (regexp_compiler_sub funs f)
     else
       holKernel_raise_Failure (implode "timeout")`;;

(* HOL4: Termination WF_REL_TAC inv_image ($< LEX $<) (the clock, then the *)
(* size of the expression or list) \ rw [] \ fs [] \ rpt (TOP_CASE_TAC   *)
(* \ fs [])                                                                *)
let exec_def = cake_def_wf
  `inv_image ((<) LEX (<))
     (\x. match x with
            INL ((funs:ce vector),(env:cv list),ck,cv) -> (ck,ce_size cv)
          | INR ((funs:ce vector),(env:cv list),ck,cvs,(acc:cv list)) ->
              (ck,list_size ce_size cvs))`
  (TERM_TAC ORELSE
   (REPEAT STRIP_TAC THEN TOP_CASE_TAC THEN REPEAT COND_CASES_TAC THEN TERM_TAC))
  `(exec (funs:ce vector) env ck (compute_exec_Const n) =
      st_ex_return (compute_exec_Num n)) /\
   (exec funs env ck (compute_exec_Var n) =
      st_ex_return (env_lookup n env)) /\
   (exec funs env ck (compute_exec_Monop m x) =
      st_ex_bind (exec funs env ck x) (\v.
      st_ex_return (m v))) /\
   (exec funs env ck (compute_exec_Binop b x y) =
      st_ex_bind (exec funs env ck x) (\v.
      st_ex_bind (exec funs env ck y) (\w.
      st_ex_return (b v w)))) /\
   (exec funs env ck (compute_exec_App f xs) =
      if ck = 0 then holKernel_raise_Failure (implode "timeout") else
      st_ex_bind (exec_list funs env ck xs []) (\vs.
      st_ex_bind (get_code f funs) (\c.
      exec funs vs (ck - 1) c))) /\
   (exec funs env ck (compute_exec_Let x y) =
      if ck = 0 then holKernel_raise_Failure (implode "timeout") else
      st_ex_bind (exec funs env ck x) (\v.
      exec funs (CONS v env) (ck - 1) y)) /\
   (exec funs env ck (compute_exec_If x y z) =
      st_ex_bind (exec funs env ck x) (\v.
      exec funs env ck (match v with
                          compute_exec_Num n -> if n = 0 then z else y
                        | compute_exec_Pair _ _ -> z))) /\
   (exec_list funs env ck [] acc = st_ex_return acc) /\
   (exec_list funs env ck (CONS x xs) acc =
      st_ex_bind (exec funs env ck x) (\v.
      exec_list funs env ck xs (CONS v acc)))`;;

let exec_ind = cake_ind "exec";;

let compute_monop_fst_def = cake_def
  `compute_monop_fst =
     \x. match x with compute_exec_Pair y z -> y | _ -> compute_exec_Num 0`;;

let compute_monop_snd_def = cake_def
  `compute_monop_snd =
     \x. match x with compute_exec_Pair y z -> z | _ -> compute_exec_Num 0`;;

let compute_monop_ispair_def = cake_def
  `compute_monop_ispair =
     \x. match x with compute_exec_Pair y z -> compute_exec_Num 1
                    | _ -> compute_exec_Num 0`;;

let compute_monop_def = cake_def
  `(compute_monop compute_Fst = compute_monop_fst) /\
   (compute_monop compute_Snd = compute_monop_snd) /\
   (compute_monop compute_Ispair = compute_monop_ispair)`;;

let to_num_def = cake_def
  `(to_num (compute_exec_Pair _ _) = 0) /\
   (to_num (compute_exec_Num n) = n)`;;
let _ = cake_add_simps [to_num_def];;

let cv_T_def = cake_def
  `cv_T = compute_exec_Num 1`;;

let cv_F_def = cake_def
  `cv_F = compute_exec_Num 0`;;

let compute_binop_add_def = cake_def
  `compute_binop_add = \x y. compute_exec_Num (to_num x + to_num y)`;;

let compute_binop_sub_def = cake_def
  `compute_binop_sub = \x y. compute_exec_Num (to_num x - to_num y)`;;

let compute_binop_mul_def = cake_def
  `compute_binop_mul = \x y. compute_exec_Num (to_num x * to_num y)`;;

let compute_binop_div_def = cake_def
  `compute_binop_div =
     \x y. compute_exec_Num
             (let k = to_num y in if k = 0 then 0 else to_num x DIV k)`;;

let compute_binop_mod_def = cake_def
  `compute_binop_mod =
     \x y. compute_exec_Num
             (let k = to_num y in if k = 0 then to_num x else to_num x MOD k)`;;

let compute_binop_eq_def = cake_def
  `compute_binop_eq = \x (y:cv). if x = y then cv_T else cv_F`;;

let compute_binop_less_def = cake_def
  `compute_binop_less =
     \x y. match x with
             compute_exec_Pair _ _ -> cv_F
           | compute_exec_Num n ->
               (match y with
                  compute_exec_Pair _ _ -> cv_F
                | compute_exec_Num m -> if n < m then cv_T else cv_F)`;;

let compute_binop_def = cake_def
  `compute_binop op =
     match op with
       compute_Add -> compute_binop_add
     | compute_Sub -> compute_binop_sub
     | compute_Mul -> compute_binop_mul
     | compute_Div -> compute_binop_div
     | compute_Mod -> compute_binop_mod
     | compute_Eq -> compute_binop_eq
     | compute_Less -> compute_binop_less`;;

(* HOL4: Termination WF_REL_TAC measure (compute_exp_size of the expression) *)
let to_ce_def = cake_def
  `(to_ce (eqs:(mlstring#mlstring list#compute_exp)list) args (compute_Var v) =
      compute_exec_Var (findi v args)) /\
   (to_ce eqs args (compute_Num n) = compute_exec_Const n) /\
   (to_ce eqs args (compute_Pair x y) =
      compute_exec_Binop compute_exec_Pair (to_ce eqs args x) (to_ce eqs args y)) /\
   (to_ce eqs args (compute_If x y z) =
      compute_exec_If (to_ce eqs args x) (to_ce eqs args y) (to_ce eqs args z)) /\
   (to_ce eqs args (compute_Let s x y) =
      compute_exec_Let (to_ce eqs args x) (to_ce eqs (CONS s args) y)) /\
   (to_ce eqs args (compute_Uop m x) =
      compute_exec_Monop (compute_monop m) (to_ce eqs args x)) /\
   (to_ce eqs args (compute_Binop b x y) =
      compute_exec_Binop (compute_binop b) (to_ce eqs args x) (to_ce eqs args y)) /\
   (to_ce eqs args (compute_App f xs) =
      compute_exec_App (findi f (MAP FST eqs)) (MAP (to_ce eqs args) xs))`;;

let to_ce_ind = cake_ind "to_ce";;

let compile_to_ce_def = cake_def
  `compile_to_ce (eqs:(mlstring#mlstring list#compute_exp)list) (n:mlstring,args,body) =
     to_ce eqs (REVERSE args) body`;;

let build_funs_def = cake_def
  `build_funs (eqs:(mlstring#mlstring list#compute_exp)list) =
     Vector (MAP (compile_to_ce eqs) eqs:ce list)`;;

let cv2term_def = cake_def
  `(cv2term (compute_exec_Num n) = _CEXP_NUM (_NUMERAL (num2bit n))) /\
   (cv2term (compute_exec_Pair p q) = _CEXP_PAIR (cv2term p) (cv2term q))`;;

compute_overloads_off ();;
