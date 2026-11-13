(* ========================================================================= *)
(* word_remove: port of HOL4 compiler/backend/word_removeScript.sml          *)
(* (CakeML v3479).                                                           *)
(* This simple compiler phase removes MustTerminate, which is a semantic     *)
(* device used to help keep the logical clocks in sync in the data_to_word   *)
(* correctness proofs.                                                       *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The wordLang constructors are wl_... (notes/naming/names.tsv).          *)
(* - HOL4's pmatch case expressions are written with match like all others, *)
(*   so remove_must_terminate_pmatch restates the definition in match form.  *)
(* - The catch-all clause is completed as HOL4's TFL does (sem1aux_def).     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/wordLang.ml";;

type_invention_error := true;;

(* Removes MustTerminate *)

let remove_must_terminate_def = sem1aux_def
  `(remove_must_terminate (wl_Seq p0 p1:(A)wl_prog) =
      wl_Seq (remove_must_terminate p0) (remove_must_terminate p1)) /\
   (remove_must_terminate (wl_If cmp r1 ri e2 e3) =
      wl_If cmp r1 ri (remove_must_terminate e2) (remove_must_terminate e3)) /\
   (remove_must_terminate (MustTerminate p) = remove_must_terminate p) /\
   (remove_must_terminate (wl_Call ret dest args h) =
      let ret = (match ret with
                   NONE -> NONE
                 | SOME (v,cutset,ret_handler,l1,l2) ->
                     SOME (v,cutset,remove_must_terminate ret_handler,l1,l2)) in
      let h = (match h with
                 NONE -> NONE
               | SOME (v,prog,l1,l2) -> SOME (v,remove_must_terminate prog,l1,l2)) in
      wl_Call ret dest args h) /\
   (remove_must_terminate (wl_Loop names body exit_names) =
      wl_Loop names (remove_must_terminate body) exit_names) /\
   (remove_must_terminate prog = prog)`;;

let remove_must_terminate_ind = cake_ind "remove_must_terminate";;

let remove_must_terminate_pmatch = prove
 (CASE_TERM
  `!prog:(A)wl_prog.
     remove_must_terminate prog =
     match prog with
       wl_Seq p0 p1 -> wl_Seq (remove_must_terminate p0) (remove_must_terminate p1)
     | wl_If cmp r1 ri e2 e3 ->
         wl_If cmp r1 ri (remove_must_terminate e2) (remove_must_terminate e3)
     | MustTerminate p -> remove_must_terminate p
     | wl_Call ret dest args h ->
         (let ret = (match ret with
                       NONE -> NONE
                     | SOME (v,cutset,ret_handler,l1,l2) ->
                         SOME (v,cutset,remove_must_terminate ret_handler,l1,l2)) in
          let h = (match h with
                     NONE -> NONE
                   | SOME (v,prog,l1,l2) -> SOME (v,remove_must_terminate prog,l1,l2)) in
          wl_Call ret dest args h)
     | wl_Loop names body exit_names ->
         wl_Loop names (remove_must_terminate body) exit_names
     | prog -> prog`,
  REPEAT GEN_TAC THEN
  REPEAT (TOP_CASE_TAC THEN
          ASM_REWRITE_TAC[remove_must_terminate_def; LET_DEF; LET_END_DEF]) THEN
  FS[remove_must_terminate_def; LET_DEF; LET_END_DEF]);;
