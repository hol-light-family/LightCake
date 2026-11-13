(* ========================================================================= *)
(* word_elim: port of HOL4 compiler/backend/word_elimScript.sml              *)
(* (CakeML v3479).                                                           *)
(* Implementation for wordLang dead-code elimination.  Analyses code to give *)
(* a next-step function as a num_set num_map, uses the spt_closure functions *)
(* to close the next-step function and give a set of reachable functions,   *)
(* and removes unreachable functions from the code.                          *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The wordLang constructors are wl_... (notes/naming/names.tsv); HOL4 ()  *)
(*   is one; num_set is 1 spt and num_map A spt.                             *)
(* - The catch-all clause of find_word_ref is completed as HOL4's TFL does  *)
(*   (sem1aux_def).                                                          *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/sptree.ml";;
needs "hol4/spt_closure.ml";;
needs "compiler/backend/wordLang.ml";;

type_invention_error := true;;

let find_word_loc_def = cake_def
  `find_word_loc (name:num, (_:A), (_:B)) = name`;;

let find_word_ref_def = sem1aux_def
  `(find_word_ref (MustTerminate p:(A)wl_prog) = find_word_ref p) /\
   (find_word_ref (wl_Call ret target _ handler) =
      union
        (match target with NONE -> LN | SOME n -> insert n one LN)
        (union
           (match ret with
              NONE -> LN
            | SOME (_,_,ret_handler,l1,_) ->
                insert l1 one (find_word_ref ret_handler))
           (match handler with
              NONE -> LN
            | SOME (_,ex_handler,_,_) -> find_word_ref ex_handler))) /\
   (find_word_ref (wl_Seq p1 p2) = union (find_word_ref p1) (find_word_ref p2)) /\
   (find_word_ref (wl_If _ _ _ p1 p2) =
      union (find_word_ref p1) (find_word_ref p2)) /\
   (find_word_ref (wl_LocValue _ n) = insert n one LN) /\
   (find_word_ref (wl_Loop names body exit_names) = find_word_ref body) /\
   (find_word_ref _ = LN:1 spt)`;;

let find_word_ref_ind = cake_ind "find_word_ref";;

let analyse_word_code_def = cake_def
  `(analyse_word_code [] = LN:(1 spt)spt) /\
   (analyse_word_code (CONS (n, (args:B), (prog:(A)wl_prog)) t) =
      insert n (find_word_ref prog) (analyse_word_code t))`;;

let remove_word_code_def = cake_def
  `remove_word_code (reachable:A spt) (l:(num#B)list) =
     FILTER (\x. IS_SOME (lookup (FST x) reachable)) l`;;

let remove_word_prog_def = cake_def
  `remove_word_prog (n:num) (code:(num#B#(A)wl_prog)list) =
     let t = analyse_word_code code in
     let reachable = closure_spt (insert n one (LN:1 spt)) t in
     remove_word_code reachable code`;;
