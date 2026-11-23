(* ========================================================================= *)
(* ml_monadBase: port of HOL4 translator/monadic/monad_base/                 *)
(* ml_monadBaseScript.sml (CakeML v3479).  Definitions for the state-and-   *)
(* exception monad that is supported by the proof-producing monadic         *)
(* translator.                                                               *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's Type M = :'a -> ('b, 'c) exc # 'a (an abbreviation with type     *)
(*   variables, impossible in HOL Light) is written out where used.          *)
(* - HOL4's do-notation for the monad st_ex is written with its constants:   *)
(*   do x <- m; r od is st_ex_bind m (\x. r), do m; r od is                  *)
(*   st_ex_ignore_bind m r, return x is st_ex_return x, ++ is otherwise.    *)
(* - otherwise is an infix (HOL4: 400 RIGHT, the level of /\; here 8 right, *)
(*   the level of /\).  HOL4 () is one.                                      *)
(* - HOL4 run is ml_monadBase_run (a common word, see doc/CONVENTIONS.md).   *)
(* - HOL4 defines Mdref_aux and Mref_assign_aux as e n = \s. ..., with the   *)
(*   recursive call applied to the lambda's variable; the kit's recursion   *)
(*   package does not handle that shape, so both constants are defined with  *)
(*   the state as a further argument (MONADAUX_..._curried) and HOL4's       *)
(*   equations (..._def) are derived from those.                             *)
(* - The [local] theorems of the script are kept (OCaml bindings); free     *)
(*   variables of HOL4 statements are universally quantified.  HOL4         *)
(*   LIST_CONJ is end_itlist CONJ.                                           *)
(* - The congruence theorems st_ex_bind_CONG and st_ex_ignore_bind_CONG are *)
(*   proved.  In place of HOL4's export_cong, MONADAUX_ADMISSIBLE_st_ex_bind *)
(*   is registered with the kit (cake_register_admissible): recursive calls  *)
(*   in the continuation of st_ex_bind (a lambda, which the kit's recursion  *)
(*   package cannot otherwise analyse) are then admissible, with the         *)
(*   lambda's variable in their context, as with HOL4's TFL.                 *)
(* - MONADAUX_ names are local helpers (not HOL4 names).                     *)
(* - HOL4 can is ml_monadBase_can (a short or common word), and can_def is   *)
(*   ml_monadBase_can_def.                                                   *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/semanticPrimitives.ml";;

type_invention_error := true;;

(* 'a is the type of the state, 'b is the type of successful computations, *)
(* and 'c is the type of exceptions                                          *)

let exc_INDUCT,exc_RECURSION = cake_type "exc = M_success A | M_failure B";;

(* HOL4's ('a,'b,'c) M is written A->(B,C)exc#A *)

let liftM_def = cake_def
  `liftM (read:D->A) (write:(A->A)->D->D) (op:A->(B,C)exc#A) =
     (\state:D. let (ret,new) = op (read state) in (ret,write (K new) state))`;;

(* Definitions using monadic syntax *)

let st_ex_bind_def = cake_def
  `st_ex_bind (x:A->(B,C)exc#A) (f:B->A->(D,C)exc#A) =
     \s. match x s with
           (M_success y,s) -> f y s
         | (M_failure x,s) -> (M_failure x,s)`;;

let st_ex_ignore_bind_def = cake_def
  `st_ex_ignore_bind (x:A->(B,C)exc#A) (f:A->(D,C)exc#A) =
     \s. match x s with
           (M_success y,s) -> f s
         | (M_failure x,s) -> (M_failure x,s)`;;

(* Congruence theorems for st_ex_bind / st_ex_ignore_bind.  HOL4's TFL uses *)
(* them (DefnBase.export_cong) when deriving termination conditions, so that *)
(* the intermediate values of the monad bind (y, s'') are captured.          *)

let st_ex_ignore_bind_CONG = prove
 (`!(x:A->(B,C)exc#A) s x' s' (f:A->(D,C)exc#A) f'.
     x = x' /\ s = s' /\
     (!y s''. x' s' = (M_success y,s'') ==> f s'' = f' s'')
     ==> st_ex_ignore_bind x f s = st_ex_ignore_bind x' f' s'`,
  RW[st_ex_ignore_bind_def] THEN EVERY_CASE_TAC THEN FS[]);;

let st_ex_bind_CONG = prove
 (`!(x:A->(B,C)exc#A) s x' s' (f:B->A->(D,C)exc#A) f'.
     x = x' /\ s = s' /\
     (!y s''. x' s' = (M_success y,s'') ==> f y s'' = f' y s'')
     ==> st_ex_bind x f s = st_ex_bind x' f' s'`,
  RW[st_ex_bind_def] THEN EVERY_CASE_TAC THEN FS[]);;

(* The kit's analogue of DefnBase.export_cong "st_ex_bind_CONG": an           *)
(* admissibility rule (kit/recursion.ml) for recursive calls in the          *)
(* continuation of st_ex_bind, which is a lambda; the definitions of the     *)
(* closure use st_ex_bind without the state argument, where HOL4's TFL       *)
(* gives such a call no further context than the lambda's variable.          *)

let MONADAUX_ADMISSIBLE_st_ex_bind = prove
 (`!(<<) (p:(A->B)->P->bool) (s:P->A) (h:(A->B)->P->C->S->(D,E)exc#S) o1.
        admissible(<<) p s o1 /\
        admissible (<<) (\f (y,x). p f x) (\(y,x). s x) (\f (y,x). h f x y)
        ==> admissible (<<) p s (\f x. st_ex_bind (o1 f x) (h f x))`,
  REWRITE_TAC[admissible; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  BINOP_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]]);;

let () = cake_register_admissible "st_ex_bind" MONADAUX_ADMISSIBLE_st_ex_bind;;

let st_ex_return_def = cake_def
  `st_ex_return (x:B) = \s:A. (M_success x:(B,C)exc,s)`;;

(* HOL4: add_infix ("otherwise", 400, HOLgrammars.RIGHT), the level of /\ *)
parse_as_infix("otherwise",(8,"right"));;

let otherwise_def = cake_def
  `((x:A->(B,C)exc#A) otherwise (y:A->(B,C)exc#A)) =
     \s. match x s with
           (M_success y,s) -> (M_success y,s)
         | (M_failure e,s) -> y s`;;

(* HOL4 declares the monad st_ex for its do-notation (monadsyntax):          *)
(*   do x <- m; rest od  is  st_ex_bind m (\x. rest),                        *)
(*   do m; rest od       is  st_ex_ignore_bind m rest,                       *)
(*   return x            is  st_ex_return x,                                 *)
(*   m ++ m'             is  m otherwise m'.                                 *)
(* The port writes these constants.                                          *)

let ml_monadBase_can_def = cake_def
  `ml_monadBase_can (f:X->A->(B,C)exc#A) (x:X) =
     (st_ex_ignore_bind (f x) (st_ex_return T) otherwise st_ex_return F)`;;

(* Dynamic allocation of references *)

let store_ref_INDUCT,store_ref_RECURSION = cake_type "store_ref = StoreRef num";;

(* Arrays *)

(* Msub *)
let ml_monadBase_Msub_def = cake_def
  `Msub (e:E) (n:num) (l:A list) =
     match l with
       [] -> M_failure e
     | CONS x l' -> if n = 0 then M_success x else Msub e (n - 1) l'`;;

let ml_monadBase_Msub_ind = cake_ind "Msub";;

let ml_monadBase_Msub_eq = prove
 (`!(l:A list) n (e:E). n < LENGTH l ==> Msub e n l = M_success (EL n l)`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[ml_monadBase_Msub_def] THEN
  RW[LENGTH; LT] THEN CASES_ON `n:num` THEN FS[EL; HD; TL; SUC_SUB1]);;

let ml_monadBase_Msub_exn_eq = prove
 (`!(l:A list) n (e:E). n >= LENGTH l ==> Msub e n l = M_failure e`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[ml_monadBase_Msub_def] THEN
  RW[LENGTH; GE; LT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* Mupdate *)
let ml_monadBase_Mupdate_def = cake_def
  `Mupdate (e:E) (x:A) (n:num) (l:A list) =
     match l with
       [] -> M_failure e
     | CONS x' l' ->
         if n = 0 then M_success (CONS x l')
         else (match Mupdate e x (n - 1) l' with
                 M_success l'' -> M_success (CONS x' l'')
               | other -> other)`;;

let ml_monadBase_Mupdate_ind = cake_ind "Mupdate";;

let ml_monadBase_Mupdate_eq = prove
 (`!(l:A list) n x (e:E).
     n < LENGTH l ==> Mupdate e x n l = M_success (LUPDATE x n l)`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[ml_monadBase_Mupdate_def] THEN
  RW[LENGTH; LT; LUPDATE_def] THEN CASES_ON `n:num` THEN
  FS[LUPDATE_def; SUC_SUB1; LE_SUC_LT]);;

let ml_monadBase_Mupdate_exn_eq = prove
 (`!(l:A list) n x (e:E). n >= LENGTH l ==> Mupdate e x n l = M_failure e`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[ml_monadBase_Mupdate_def] THEN
  RW[LENGTH; GE; LT] THEN CASES_ON `n:num` THEN FS[SUC_SUB1; LT_SUC; GE]);;

(* Array resize *)
let array_resize_def = cake_def
  `array_resize (n:num) (x:A) (a:A list) =
     if n = 0 then []
     else match a with
            [] -> CONS x (array_resize (n - 1) x a)
          | CONS x' a' -> CONS x' (array_resize (n - 1) x a')`;;

let array_resize_ind = cake_ind "array_resize";;

let array_resize_eq = prove
 (`!(a:A list) n x. array_resize n x a = APPEND (TAKE n a) (REPLICATE (n - LENGTH a) x)`,
  LIST_INDUCT_TAC THEN INDUCT_TAC THEN ONCE_REWRITE_TAC[array_resize_def] THEN
  SIMP[TAKE_def; REPLICATE; LENGTH; SUC_SUB1; ARITH_RULE `SUC n - SUC m = n - m`]);;

(* User functions *)
let ml_monadBase_Marray_length_def = cake_def
  `Marray_length (get_arr:S->A list) =
     \s. (M_success (LENGTH (get_arr s)):(num,E)exc,s)`;;

let ml_monadBase_Marray_sub_def = cake_def
  `Marray_sub (get_arr:S->A list) (e:E) n =
     \s. (Msub e n (get_arr s),s)`;;

let ml_monadBase_Marray_update_def = cake_def
  `Marray_update (get_arr:S->A list) (set_arr:A list->S->S) (e:E) n x =
     \s. match Mupdate e x n (get_arr s) with
           M_success a -> (M_success one,set_arr a s)
         | M_failure e -> (M_failure e,s)`;;

let ml_monadBase_Marray_alloc_def = cake_def
  `Marray_alloc (set_arr:A list->S->S) n (x:A) =
     \s. (M_success one:(1,E)exc,set_arr (REPLICATE n x) s)`;;

let ml_monadBase_Marray_resize_def = cake_def
  `Marray_resize (get_arr:S->A list) (set_arr:A list->S->S) n (x:A) =
     \s. (M_success one:(1,E)exc,set_arr (array_resize n x (get_arr s)) s)`;;

(* Dynamic allocated references *)
let ml_monadBase_Mref_def = cake_def
  `Mref (cons:A->B) (x:A) =
     \s. (M_success (StoreRef (LENGTH s)):(store_ref,E)exc,CONS (cons x) s)`;;

let dref_def = cake_def
  `dref n = \s:A list. EL (LENGTH s - n - 1) s`;;

(* HOL4 defines Mdref_aux e n = \s. ... (and Mref_assign_aux below the same *)
(* way).  The kit's recursion package does not handle a recursive call      *)
(* applied to an argument bound by the lambda of the right-hand side, so    *)
(* the constant is defined with the state as an argument                    *)
(* (MONADAUX_Mdref_aux_curried) and HOL4's equation is derived from that.   *)
let MONADAUX_Mdref_aux_curried = cake_def
  `Mdref_aux (e:E) (n:num) (s:A list) =
     match s with
       [] -> M_failure e
     | CONS x s' -> if n = 0 then M_success x else Mdref_aux e (n - 1) s'`;;

let ml_monadBase_Mdref_aux_def = prove
 (CASE_TERM `!(e:E) (n:num). Mdref_aux e n =
     \s:A list. match s with
                  [] -> M_failure e
                | CONS x s -> if n = 0 then M_success x else Mdref_aux e (n - 1) s`,
  REWRITE_TAC[FUN_EQ_THM] THEN MATCH_ACCEPT_TAC MONADAUX_Mdref_aux_curried);;

let ml_monadBase_Mdref_def = cake_def
  `Mdref (e:E) (StoreRef n) =
     \s:A list. (Mdref_aux e (LENGTH s - n - 1) s,s)`;;

let ml_monadBase_Mpop_ref_def = cake_def
  `Mpop_ref (e:E) =
     \rs. match rs with
            (r,s) -> (match s with
                        CONS (x:A) s -> (r,s)
                      | [] -> (M_failure e:(B,E)exc,s))`;;

let MONADAUX_Mref_assign_aux_curried = cake_def
  `Mref_assign_aux (e:E) (n:num) (x:A) (s:A list) =
     match s with
       CONS x' s' ->
         if n = 0 then M_success (CONS x s')
         else (match Mref_assign_aux e (n - 1) x s' with
                 M_success s'' -> M_success (CONS x' s'')
               | other -> other)
     | [] -> M_failure e`;;

let ml_monadBase_Mref_assign_aux_def = prove
 (CASE_TERM `!(e:E) (n:num) (x:A). Mref_assign_aux e n x =
     \s. match s with
           CONS x' s ->
             if n = 0 then M_success (CONS x s)
             else (match Mref_assign_aux e (n - 1) x s with
                     M_success s -> M_success (CONS x' s)
                   | other -> other)
         | [] -> M_failure e`,
  REWRITE_TAC[FUN_EQ_THM] THEN MATCH_ACCEPT_TAC MONADAUX_Mref_assign_aux_curried);;

let ml_monadBase_Mref_assign_def = cake_def
  `Mref_assign (e:E) (StoreRef n) (x:A) =
     \s. match Mref_assign_aux e (LENGTH s - n - 1) x s with
           M_success s -> (M_success one,s)
         | M_failure e -> (M_failure e,s)`;;

let ref_assign_def = cake_def
  `ref_assign n (x:A) = \s. LUPDATE x (LENGTH s - n - 1) s`;;

let dref_cons_state = prove
 (`!n (state:A list) x. n < LENGTH state ==> dref n (CONS x state) = dref n state`,
  REWRITE_TAC[dref_def; LENGTH] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `SUC (LENGTH (state:A list)) - n - 1 = SUC (LENGTH state - n - 1)`
    SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[EL; TL]]);;

let dref_first = prove
 (`!(r:A) s. dref (LENGTH s) (CONS r s) = r`,
  REWRITE_TAC[dref_def; LENGTH; ARITH_RULE `SUC n - n - 1 = 0`; EL; HD]);;

(* MONADAUX_Mdref_aux_eq: Mdref_aux reads the element at its index *)
let MONADAUX_Mdref_aux_eq = prove
 (`!(s:A list) k (e:E). k < LENGTH s ==> Mdref_aux e k s = M_success (EL k s)`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[MONADAUX_Mdref_aux_curried] THEN
  RW[LENGTH; LT] THEN CASES_ON `k:num` THEN FS[EL; HD; TL; SUC_SUB1]);;

let ml_monadBase_Mdref_eq = prove
 (`!(e:E) (state:A list) n.
     n < LENGTH state
     ==> Mdref e (StoreRef n) state = (M_success (dref n state),state)`,
  RW[ml_monadBase_Mdref_def; dref_def] THEN
  MATCH_MP_TAC MONADAUX_Mdref_aux_eq THEN ASM_ARITH_TAC);;

(* MONADAUX_Mref_assign_aux_eq: Mref_assign_aux updates at its index *)
let MONADAUX_Mref_assign_aux_eq = prove
 (`!(s:A list) k x (e:E).
     k < LENGTH s ==> Mref_assign_aux e k x s = M_success (LUPDATE x k s)`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[MONADAUX_Mref_assign_aux_curried] THEN
  RW[LENGTH; LT] THEN CASES_ON `k:num` THEN FS[LUPDATE_def; SUC_SUB1]);;

let ml_monadBase_Mref_assign_aux_eq = prove
 (`!(state:A list) (e:E) n x.
     n < LENGTH state
     ==> Mref_assign_aux e (LENGTH state - n - 1) x state =
         M_success (ref_assign n x state)`,
  RW[ref_assign_def] THEN MATCH_MP_TAC MONADAUX_Mref_assign_aux_eq THEN
  ASM_ARITH_TAC);;

let ml_monadBase_Mref_assign_eq = prove
 (`!(state:A list) (e:E) n x.
     n < LENGTH state
     ==> Mref_assign e (StoreRef n) x state = (M_success one,ref_assign n x state)`,
  RW[ml_monadBase_Mref_assign_def] THEN
  IMP_RES_TAC ml_monadBase_Mref_assign_aux_eq THEN FS[]);;

let ref_bind_def = cake_def
  `ref_bind (create:S->(A,E)exc#S) (f:A->S->R) (pop:R->(B,E)exc#S) =
     \s. match create s with
           (M_success x,s) -> pop (f x s)
         | (M_failure x,s) -> (M_failure x,s)`;;

(* TODO: use that *)
let ml_monadBase_Mget_ref_def = cake_def
  `Mget_ref (get_var:S->A) = \s. (M_success (get_var s):(A,E)exc,s)`;;

let ml_monadBase_Mset_ref_def = cake_def
  `Mset_ref (set_var:A->S->S) x = \s. (M_success one:(1,E)exc,set_var x s)`;;

(* Rules to deal with the monads (HOL4: [local] theorems, collected in      *)
(* monad_eqs below; the free variables of the HOL4 statements are           *)
(* quantified here)                                                          *)

let ml_monadBase_st_ex_return_success = prove
 (`!(v:B) (st:A) (r:(B,C)exc) st'.
     st_ex_return v st = (r,st') <=> r = M_success v /\ st' = st`,
  RW[st_ex_return_def] THEN METIS_TAC[]);;

let ml_monadBase_st_ex_bind_success = prove
 (`!(f:A->(B,C)exc#A) (g:B->A->(D,C)exc#A) st st' v.
     st_ex_bind f g st = (M_success v,st') <=>
     ?v' st''. f st = (M_success v',st'') /\ g v' st'' = (M_success v,st')`,
  RW[st_ex_bind_def] THEN EVERY_CASE_TAC THEN RW[]);;

let otherwise_success = prove
 (`!(x:A->(B,C)exc#A) y s v s'.
     (x otherwise y) s = (M_success v,s') <=>
     x s = (M_success v,s') \/
     ?e s''. x s = (M_failure e,s'') /\ y s'' = (M_success v,s')`,
  RW[otherwise_def] THEN EVERY_CASE_TAC THEN RW[]);;

let otherwise_failure = prove
 (`!(x:A->(B,C)exc#A) y s e s'.
     (x otherwise y) s = (M_failure e,s') <=>
     ?e' s''. x s = (M_failure e',s'') /\ y s'' = (M_failure e,s')`,
  RW[otherwise_def] THEN EVERY_CASE_TAC THEN RW[]);;

let otherwise_eq = prove
 (`!(x:A->(B,C)exc#A) y s r s'.
     (x otherwise y) s = (r,s') <=>
     (?v. (x s = (M_success v,s') /\ r = M_success v) \/
          (?e s''. x s = (M_failure e,s'') /\
                   y s'' = (M_success v,s') /\
                   r = M_success v)) \/
     (?e e' s''. x s = (M_failure e',s'') /\
                 y s'' = (M_failure e,s') /\
                 r = M_failure e)`,
  REPEAT GEN_TAC THEN CASES_ON `r:(B,C)exc` THEN
  RW[otherwise_success; otherwise_failure] THEN METIS_TAC[]);;

let can_success = prove
 (`!(f:X->A->(B,C)exc#A) x s e s'. ml_monadBase_can f x s = (M_failure e,s') <=> F`,
  RW[ml_monadBase_can_def; otherwise_def; st_ex_ignore_bind_def; st_ex_return_def] THEN
  EVERY_CASE_TAC THEN RW[]);;

let ml_monadBase_Marray_length_success = prove
 (`!(get_arr:S->A list) s (r:(num,E)exc) s'.
     Marray_length get_arr s = (r,s') <=>
     r = M_success (LENGTH (get_arr s)) /\ s' = s`,
  RW[ml_monadBase_Marray_length_def] THEN METIS_TAC[]);;

let ml_monadBase_Marray_sub_success = prove
 (`!(get_arr:S->A list) (e:E) n s v s'.
     Marray_sub get_arr e n s = (M_success v,s') <=>
     n < LENGTH (get_arr s) /\ v = EL n (get_arr s) /\ s' = s`,
  RW[ml_monadBase_Marray_sub_def] THEN
  CASES_ON `n < LENGTH ((get_arr:S->A list) s)` THEN
  FS[ml_monadBase_Msub_eq; ml_monadBase_Msub_exn_eq; GE; GSYM NOT_LT] THEN
  METIS_TAC[]);;

let ml_monadBase_Marray_sub_failure = prove
 (`!(get_arr:S->A list) (e:E) n s e' s'.
     Marray_sub get_arr e n s = (M_failure e',s') <=>
     n >= LENGTH (get_arr s) /\ e' = e /\ s' = s`,
  RW[ml_monadBase_Marray_sub_def] THEN
  CASES_ON `n < LENGTH ((get_arr:S->A list) s)` THEN
  FS[ml_monadBase_Msub_eq; ml_monadBase_Msub_exn_eq; GE; GSYM NOT_LT] THEN
  METIS_TAC[]);;

let ml_monadBase_Marray_sub_eq = prove
 (`!(get_arr:S->A list) (e:E) n s r s'.
     Marray_sub get_arr e n s = (r,s') <=>
     (n < LENGTH (get_arr s) /\ s' = s /\ r = M_success (EL n (get_arr s))) \/
     (n >= LENGTH (get_arr s) /\ s' = s /\ r = M_failure e)`,
  REPEAT GEN_TAC THEN CASES_ON `r:(A,E)exc` THEN
  CASES_ON `n < LENGTH ((get_arr:S->A list) s)` THEN
  FS[ml_monadBase_Marray_sub_success; ml_monadBase_Marray_sub_failure; GE;
     GSYM NOT_LT] THEN
  MESON_TAC[]);;

let ml_monadBase_Marray_update_success = prove
 (`!(get_arr:S->A list) (set_arr:A list->S->S) (e:E) n x s s' v.
     Marray_update get_arr set_arr e n x s = (M_success v,s') <=>
     n < LENGTH (get_arr s) /\ v = one /\ s' = set_arr (LUPDATE x n (get_arr s)) s`,
  RW[ml_monadBase_Marray_update_def] THEN
  CASES_ON `n < LENGTH ((get_arr:S->A list) s)` THEN
  FS[ml_monadBase_Mupdate_eq; ml_monadBase_Mupdate_exn_eq; GE; GSYM NOT_LT] THEN
  MESON_TAC[one]);;

let ml_monadBase_Marray_update_failure = prove
 (`!(get_arr:S->A list) (set_arr:A list->S->S) (e:E) e' n x s s'.
     Marray_update get_arr set_arr e n x s = (M_failure e',s') <=>
     n >= LENGTH (get_arr s) /\ e' = e /\ s' = s`,
  RW[ml_monadBase_Marray_update_def] THEN
  CASES_ON `n < LENGTH ((get_arr:S->A list) s)` THEN
  FS[ml_monadBase_Mupdate_eq; ml_monadBase_Mupdate_exn_eq; GE; GSYM NOT_LT] THEN
  MESON_TAC[]);;

let ml_monadBase_Marray_update_eq = prove
 (`!(get_arr:S->A list) (set_arr:A list->S->S) (e:E) n x s r s'.
     Marray_update get_arr set_arr e n x s = (r,s') <=>
     (n < LENGTH (get_arr s) /\
      s' = set_arr (LUPDATE x n (get_arr s)) s /\
      r = M_success one) \/
     (n >= LENGTH (get_arr s) /\
      s' = s /\
      r = M_failure e)`,
  REPEAT GEN_TAC THEN CASES_ON `r:(1,E)exc` THEN
  CASES_ON `n < LENGTH ((get_arr:S->A list) s)` THEN
  FS[ml_monadBase_Marray_update_success; ml_monadBase_Marray_update_failure; GE;
     GSYM NOT_LT] THEN
  MESON_TAC[one]);;

let ml_monadBase_Marray_alloc_success = prove
 (`!(set_arr:A list->S->S) n x s (r:(1,E)exc) s'.
     Marray_alloc set_arr n x s = (r,s') <=>
     r = M_success one /\ s' = set_arr (REPLICATE n x) s`,
  RW[ml_monadBase_Marray_alloc_def] THEN MESON_TAC[]);;

(* HOL4 LIST_CONJ is end_itlist CONJ *)
let monad_eqs = end_itlist CONJ
  [ml_monadBase_st_ex_return_success; ml_monadBase_st_ex_bind_success;
   otherwise_eq; can_success; ml_monadBase_Marray_length_success;
   ml_monadBase_Marray_sub_eq; ml_monadBase_Marray_update_eq;
   ml_monadBase_Marray_alloc_success];;

(* Run *)

(* HOL4 run: ml_monadBase_run in the port, a common word (see                *)
(* doc/CONVENTIONS.md)                                                       *)
let ml_monadBase_run_def = cake_def
  `ml_monadBase_run (x:A->(B,C)exc#A) state = FST (x state)`;;
