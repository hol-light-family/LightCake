(* ========================================================================= *)
(* source_let: port of HOL4 compiler/backend/source_letScript.sml (CakeML    *)
(* v3479).                                                                   *)
(* This is a source-to-source transformation that lifts Let/Letrec          *)
(* expressions that sit at the top of Dlet:s into their own                 *)
(* Dlet/Dletrec:s.                                                           *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's Overload string_size = list_size char_size is not used here.    *)
(* - The variables of the inner patterns of lift_let and compile_decs that  *)
(*   shadow a clause variable in HOL4 get new names (x1, x2, d').           *)
(* - dest_Let, dest_Letrec and lift_let (catch-all clauses over exp and     *)
(*   dec) are made with sem1aux_def (one case tree per function): the       *)
(*   kit's clause completion takes minutes for them.                        *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

let dest_Let_def = sem1aux_def
  `(dest_Let (Let opt x y) = SOME (opt,x,y)) /\
   (dest_Let (_:exp) = NONE)`;;

let _ = cake_add_simps [dest_Let_def];;

let dest_Let_SOME = prove
 (`dest_Let z = SOME (opt,x,y) <=> z = Let opt x y`,
  STRUCT_CASES_TAC (ISPEC `z:exp` (nchotomy_of_type `:exp`)) THEN
  REWRITE_TAC[dest_Let_def; injectivity "option"; distinctness "option";
              injectivity "exp"; distinctness "exp"; PAIR_EQ]);;

let dest_Let_NONE = prove
 (`dest_Let z = NONE <=> !opt x y. ~(z = Let opt x y)`,
  STRUCT_CASES_TAC (ISPEC `z:exp` (nchotomy_of_type `:exp`)) THEN
  REWRITE_TAC[dest_Let_def; injectivity "option"; distinctness "option";
              injectivity "exp"; distinctness "exp"; PAIR_EQ] THEN
  MESON_TAC[]);;

let dest_Letrec_def = sem1aux_def
  `(dest_Letrec (Letrec funs x) = SOME (funs, x)) /\
   (dest_Letrec (_:exp) = NONE)`;;

let _ = cake_add_simps [dest_Letrec_def];;

let dest_Letrec_SOME = prove
 (`dest_Letrec z = SOME (funs,x) <=> z = Letrec funs x`,
  STRUCT_CASES_TAC (ISPEC `z:exp` (nchotomy_of_type `:exp`)) THEN
  REWRITE_TAC[dest_Letrec_def; injectivity "option"; distinctness "option";
              injectivity "exp"; distinctness "exp"; PAIR_EQ]);;

let dest_Letrec_NONE = prove
 (`dest_Letrec z = NONE <=> !funs x. ~(z = Letrec funs x)`,
  STRUCT_CASES_TAC (ISPEC `z:exp` (nchotomy_of_type `:exp`)) THEN
  REWRITE_TAC[dest_Letrec_def; injectivity "option"; distinctness "option";
              injectivity "exp"; distinctness "exp"; PAIR_EQ] THEN
  MESON_TAC[]);;

let lift_let_def = sem1aux_def
  `(lift_let (Dlet l p x) =
      match dest_Let x with
        SOME (NONE,x1,y) -> SOME (Dlet l Pany x1, Dlet l p y)
      | SOME (SOME m,x1,y) -> SOME (Dlet l (Pvar m) x1, Dlet l p y)
      | NONE ->
          (match dest_Letrec x with
             SOME (funs,x2) -> SOME (Dletrec l funs, Dlet l p x2)
           | NONE -> NONE)) /\
   (lift_let (_:dec) = NONE)`;;

(* the termination of lift_lets: lifting a let makes the declaration smaller *)

let IL1AUX_LIFT_LET_SIZE = prove
 (`!d d1 d2. lift_let d = SOME (d1,d2) ==> dec_size d2 < dec_size d`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `d:dec` (nchotomy_of_type `:dec`)) THEN
  REWRITE_TAC[lift_let_def; distinctness "option"] THEN
  W (fun (_,w) ->
       let v = find_term (fun t -> is_var t && type_of t = `:exp`) w in
       STRUCT_CASES_TAC (ISPEC v (nchotomy_of_type `:exp`))) THEN
  REWRITE_TAC[dest_Let_def; dest_Letrec_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "option"] THEN
  W (fun (_,w) ->
       match filter (fun t -> is_var t &&
                        (try fst(dest_type(type_of t)) = "option" with Failure _ -> false))
                    (frees w) with
         v::_ -> CASES_ON v
       | [] -> ALL_TAC) THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "option"; PAIR_EQ; distinctness "option"] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[type_size_def "dec"; type_size_def "exp"] THEN ARITH_TAC);;

let lift_lets_def = cake_def_wf
  `MEASURE ((dec_size o SND):dec list # dec -> num)`
  (REWRITE_TAC(WF_REL_THMS @ [o_THM; SND]) THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   FIRST_ASSUM (ASSUME_TAC o MATCH_MP IL1AUX_LIFT_LET_SIZE) THEN ASM_ARITH_TAC)
  `lift_lets sofar d =
     match lift_let d with
       NONE -> (match sofar with [] -> NONE | _ -> SOME (REVERSE sofar, d))
     | SOME (d1, d2) -> lift_lets (CONS d1 sofar) d2`;;

let lift_lets_ind = cake_ind "lift_lets";;

let source_let_compile_decs_def = sem1aux_def_wf
  `MEASURE (list_size dec_size)`
  SEM1AUX_TC_TAC
  `(source_let_compile_decs [] = []) /\
   (source_let_compile_decs (CONS d ds) =
      match lift_lets [] d with
        SOME (pre, d') -> CONS (Dlocal pre [d']) (source_let_compile_decs ds)
      | NONE ->
          (match d with
             Dmod mn ds1 ->
               CONS (Dmod mn (source_let_compile_decs ds1)) (source_let_compile_decs ds)
           | Dlocal ds1 ds2 ->
               CONS (Dlocal (source_let_compile_decs ds1) (source_let_compile_decs ds2))
                    (source_let_compile_decs ds)
           | _ -> CONS d (source_let_compile_decs ds)))`;;

let source_let_compile_decs_ind = cake_ind "source_let_compile_decs";;
