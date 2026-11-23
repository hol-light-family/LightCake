(* ========================================================================= *)
(* bvl_jump: port of HOL4 compiler/backend/bvl_jumpScript.sml (CakeML v3479).*)
(* A function for generating efficient switch-like jumps in BVL.            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/bvl.ml";;

type_invention_error := true;;

(* HOL4: Termination WF_REL_TAC `measure (LENGTH o SND)`; both calls are on *)
(* TAKE and DROP of half of a list with at least two elements              *)

let JumpList_def = cake_def_wf
  `MEASURE ((LENGTH:bvl_exp list->num) o (SND:num#bvl_exp list->bvl_exp list))`
  (REWRITE_TAC[measure_THM; o_THM; FST; SND; LENGTH_TAKE_EQ; LENGTH_DROP] THEN
   REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN ASM_ARITH_TAC)
  `JumpList n (xs:bvl_exp list) =
     let l = LENGTH xs in
     if l = 0 then bvl_Op (IntOp (clos_Const (&0))) [] else
     if l = 1 then HD xs else
     let k = l DIV 2 in
     let ys = TAKE k xs in
     let zs = DROP k xs in
     let lt = (if n + l < 1000000 /\ n + k < 1000000
               then bvl_Op (IntOp (LessConstSmall (n + k))) [bvl_Var 0]
               else bvl_Op (IntOp clos_Less)
                      [bvl_Op (IntOp (clos_Const (&(n + k)))) []; bvl_Var 0]) in
     bvl_If lt (JumpList n ys) (JumpList (n + k) zs)`;;

let JumpList_ind = cake_ind "JumpList";;

(* HOL4: Jump *)

let bvl_jump_Jump_def = cake_def
  `bvl_jump_Jump (x:bvl_exp) xs = bvl_Let [x] (JumpList 0 xs)`;;
