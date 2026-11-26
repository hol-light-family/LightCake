(* ========================================================================= *)
(* ast_extras: port of HOL4 candle/prover/ast_extrasScript.sml (CakeML      *)
(* v3479).  Useful predicates on the CakeML ast.                             *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's ast_extras defines a second every_exp beside ast's; the two are *)
(*   extensionally equal, and here ast's constant is used (NAMING.md 11.1):  *)
(*   ast_extras_every_exp_def and ast_extras_every_exp_ind state HOL4's      *)
(*   clauses and induction theorem of it.  ast's own clauses (simp rules of *)
(*   semantics/ast.ml) have ALL over a pair_CASE lambda where HOL4's have    *)
(*   ALL over MAP SND (MAP (SND o SND) for Letrec); the two rewrites         *)
(*   ASTEXAUX_ALL_every_exp_SND and ASTEXAUX_ALL_every_exp_SND_SND join the  *)
(*   simpset, so that simplification gives HOL4's forms whichever clause     *)
(*   fires.                                                                  *)
(* - HOL4's paired lambdas are written with match (pair_CASE), as in ast.ml; *)
(*   clause variables of two types get second names (freevars: Var v,       *)
(*   Fun n e, Lannot x lc).                                                  *)
(* - every_pat, every_dec and freevars are defined with sem1aux_def (TFL     *)
(*   completion of the catch-all clauses, as HOL4 does).                     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* every_exp                                                                 *)
(* ------------------------------------------------------------------------- *)

let ASTEXAUX_ALL_every_exp_SND = prove
 (CASE_TERM
   `!p (pes:(pat#exp)list).
      ALL (\pe. match pe with (pat,e) -> every_exp p e) pes <=>
      ALL (every_exp p) (MAP SND pes)`,
  REWRITE_TAC[ALL_MAP; o_DEF] THEN REPEAT GEN_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; pair_CASE]);;

let ASTEXAUX_ALL_every_exp_SND_SND = prove
 (CASE_TERM
   `!p (funs:(varN#varN#exp)list).
      ALL (\nve. match nve with (n,v,e) -> every_exp p e) funs <=>
      ALL (every_exp p) (MAP (SND o SND) funs)`,
  REWRITE_TAC[ALL_MAP; o_DEF] THEN REPEAT GEN_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; pair_CASE]);;

(* HOL4: every_exp_def *)
let ast_extras_every_exp_def = prove
 (`(!f e. every_exp f (Raise e) <=> f (Raise e) /\ every_exp f e) /\
   (!f e pes. every_exp f (Handle e pes) <=>
      f (Handle e pes) /\ every_exp f e /\ ALL (every_exp f) (MAP SND pes)) /\
   (!f ts es. every_exp f (Con ts es) <=>
      f (Con ts es) /\ ALL (every_exp f) es) /\
   (!f n e. every_exp f (Fun n e) <=> f (Fun n e) /\ every_exp f e) /\
   (!f op es. every_exp f (App op es) <=>
      f (App op es) /\ ALL (every_exp f) es) /\
   (!f lop e1 e2. every_exp f (Log lop e1 e2) <=>
      f (Log lop e1 e2) /\ every_exp f e1 /\ every_exp f e2) /\
   (!f e1 e2 e3. every_exp f (If e1 e2 e3) <=>
      f (If e1 e2 e3) /\ every_exp f e1 /\ every_exp f e2 /\ every_exp f e3) /\
   (!f e pes. every_exp f (Mat e pes) <=>
      f (Mat e pes) /\ every_exp f e /\ ALL (every_exp f) (MAP SND pes)) /\
   (!f n x e. every_exp f (Let n x e) <=>
      f (Let n x e) /\ every_exp f x /\ every_exp f e) /\
   (!f funs e. every_exp f (Letrec funs e) <=>
      f (Letrec funs e) /\ every_exp f e /\
      ALL (every_exp f) (MAP (SND o SND) funs)) /\
   (!f e t. every_exp f (Tannot e t) <=> f (Tannot e t) /\ every_exp f e) /\
   (!f e l. every_exp f (Lannot e l) <=> f (Lannot e l) /\ every_exp f e) /\
   (!f l. every_exp f (Lit l) <=> f (Lit l)) /\
   (!f v. every_exp f (Var v) <=> f (Var v))`,
  REWRITE_TAC[every_exp_def; ASTEXAUX_ALL_every_exp_SND;
              ASTEXAUX_ALL_every_exp_SND_SND]);;
let _ = cake_add_simps [ast_extras_every_exp_def; ASTEXAUX_ALL_every_exp_SND;
                        ASTEXAUX_ALL_every_exp_SND_SND];;

(* the induction hypotheses of HOL4's every_exp_ind as those of ast's *)
let ASTEXAUX_MEM_MAP_SND = prove
 (`!(P:B->bool) (l:(A#B)list).
     (!a. MEM a (MAP SND l) ==> P a) <=> (!x y. MEM (x,y) l ==> P y)`,
  REWRITE_TAC[MEM_MAP; LEFT_IMP_EXISTS_THM; FORALL_PAIR_THM] THEN
  MESON_TAC[SND]);;

let ASTEXAUX_MEM_MAP_SND_SND = prove
 (`!(P:C->bool) (l:(A#B#C)list).
     (!a. MEM a (MAP (SND o SND) l) ==> P a) <=>
     (!x y z. MEM (x,y,z) l ==> P z)`,
  REWRITE_TAC[MEM_MAP; LEFT_IMP_EXISTS_THM; FORALL_PAIR_THM; o_THM] THEN
  MESON_TAC[SND]);;

(* HOL4: every_exp_ind *)
let ast_extras_every_exp_ind = prove
 (`!P:(exp->bool)->exp->bool.
       (!f e. P f e ==> P f (Raise e)) /\
       (!f e pes. P f e /\ (!a. MEM a (MAP SND pes) ==> P f a)
                  ==> P f (Handle e pes)) /\
       (!f ts es. (!a. MEM a es ==> P f a) ==> P f (Con ts es)) /\
       (!f n e. P f e ==> P f (Fun n e)) /\
       (!f op es. (!a. MEM a es ==> P f a) ==> P f (App op es)) /\
       (!f lop e1 e2. P f e1 /\ P f e2 ==> P f (Log lop e1 e2)) /\
       (!f e1 e2 e3. P f e1 /\ P f e2 /\ P f e3 ==> P f (If e1 e2 e3)) /\
       (!f e pes. P f e /\ (!a. MEM a (MAP SND pes) ==> P f a)
                  ==> P f (Mat e pes)) /\
       (!f n x e. P f x /\ P f e ==> P f (Let n x e)) /\
       (!f funs e. P f e /\ (!a. MEM a (MAP (SND o SND) funs) ==> P f a)
                   ==> P f (Letrec funs e)) /\
       (!f e t. P f e ==> P f (Tannot e t)) /\
       (!f e l. P f e ==> P f (Lannot e l)) /\
       (!f l. P f (Lit l)) /\
       (!f v. P f (Var v))
       ==> !v v1. P v v1`,
  REWRITE_TAC[ASTEXAUX_MEM_MAP_SND; ASTEXAUX_MEM_MAP_SND_SND] THEN
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC every_exp_ind THEN
  ASM_REWRITE_TAC[]);;

let every_exp_the = prove
 (`!P e. every_exp P e ==> P e`,
  REPEAT GEN_TAC THEN CASES_ON `e:exp` THEN
  REWRITE_TAC[ast_extras_every_exp_def] THEN MESON_TAC[]);;
let _ = cake_add_simps [every_exp_the];;

let every_exp_mono = prove
 (`!P e P'. (!e. P e ==> P' e) ==> every_exp P e ==> every_exp P' e`,
  MATCH_MP_TAC ast_extras_every_exp_ind THEN
  REWRITE_TAC[ast_extras_every_exp_def; GSYM ALL_MEM] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* every_pat                                                                 *)
(* ------------------------------------------------------------------------- *)

let every_pat_def = sem1aux_def
  `(every_pat f (Pcon opt ps) <=> f (Pcon opt ps) /\ ALL (every_pat f) ps) /\
   (every_pat f (Pref p) <=> f (Pref p) /\ every_pat f p) /\
   (every_pat f (Pas p s) <=> f (Pas p s) /\ every_pat f p) /\
   (every_pat f (Ptannot p t) <=> f (Ptannot p t) /\ every_pat f p) /\
   (every_pat f p <=> f p)`;;
let _ = cake_add_simps [every_pat_def];;

let every_pat_ind = cake_ind "every_pat";;

let every_pat_the = prove
 (`!P p. every_pat P p ==> P p`,
  REPEAT GEN_TAC THEN CASES_ON `p:pat` THEN
  REWRITE_TAC[every_pat_def] THEN MESON_TAC[]);;
let _ = cake_add_simps [every_pat_the];;

let every_pat_mono = prove
 (`!P p P'. (!p. P p ==> P' p) ==> every_pat P p ==> every_pat P' p`,
  MATCH_MP_TAC every_pat_ind THEN
  REWRITE_TAC[every_pat_def; GSYM ALL_MEM] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* every_dec                                                                 *)
(* ------------------------------------------------------------------------- *)

let every_dec_def = sem1aux_def
  `(every_dec f (Dmod n ds) <=> f (Dmod n ds) /\ ALL (every_dec f) ds) /\
   (every_dec f (Dlocal ds1 ds2) <=>
      f (Dlocal ds1 ds2) /\ ALL (every_dec f) ds1 /\ ALL (every_dec f) ds2) /\
   (every_dec f d <=> f d)`;;
let _ = cake_add_simps [every_dec_def];;

(* ------------------------------------------------------------------------- *)
(* freevars                                                                  *)
(* ------------------------------------------------------------------------- *)

let freevars_def = sem1aux_def
  `(freevars (Lit l) = {}) /\
   (freevars (Raise e) = freevars e) /\
   (freevars (Handle e pes) =
      (freevars e UNION
       UNIONS (set_of_list (MAP (\pe. match pe with
                                   (p,e) -> freevars e DIFF
                                            set_of_list (MAP Short (pat_bindings p)))
                                pes)))) /\
   (freevars (Con cn es) = UNIONS (set_of_list (MAP freevars es))) /\
   (freevars (Var v) = {v}) /\
   (freevars (Fun n e) = freevars e DIFF {Short n}) /\
   (freevars (App op xs) = UNIONS (set_of_list (MAP freevars xs))) /\
   (freevars (Log lop x y) = (freevars x UNION freevars y)) /\
   (freevars (If x y z) = (freevars x UNION freevars y UNION freevars z)) /\
   (freevars (Mat e pes) =
      (freevars e UNION
       UNIONS (set_of_list (MAP (\pe. match pe with
                                   (p,e) -> freevars e DIFF
                                            set_of_list (MAP Short (pat_bindings p)))
                                pes)))) /\
   (freevars (Let opt x y) =
      (freevars x UNION
       (freevars y DIFF (match opt with SOME n -> {Short n} | _ -> {})))) /\
   (freevars (Letrec f x) =
      (UNIONS (set_of_list (MAP (\fvx. match fvx with
                                   (fn,vn,x) -> freevars x DIFF {Short fn, Short vn})
                                f)) UNION
       (freevars x DIFF set_of_list (MAP (Short o FST) f)))) /\
   (freevars (Tannot x t) = freevars x) /\
   (freevars (Lannot x lc) = freevars x)`;;
let _ = cake_add_simps [freevars_def];;

(* ------------------------------------------------------------------------- *)
(* Partial applications of closures.                                         *)
(* ------------------------------------------------------------------------- *)

let do_partial_app_def = cake_def
  `do_partial_app f (v:v) =
     match f with
       Closure env n (Fun n' e) ->
         SOME (Closure (sem_env_v_fupd (combin_K (nsBind n v (sem_env_v env))) env) n' e)
     | _ -> NONE`;;
