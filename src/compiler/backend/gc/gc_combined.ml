(* ========================================================================= *)
(* gc_combined: port of HOL4 compiler/backend/gc/gc_combinedScript.sml       *)
(* (CakeML v3479).  One function that can run any of the GC algorithms.     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/copying_gc.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "compiler/backend/gc/gen_gc_partial.ml";;
needs "compiler/backend/data_to_word.ml";;

type_invention_error := true;;

let gen_state_INDUCT,gen_state_RECURSION = cake_type
  "gen_state = GenState num (num list)";;

let make_partial_conf_def = cake_def
  `make_partial_conf (conf:A gen_gc_conf) (GenState _ gen_starts) rs =
     gen_gc_partial_conf_REC (gen_gc_conf_limit conf) (gen_gc_conf_isRef conf)
       (HD gen_starts) rs`;;

let gc_combined_def = cake_def
  `(gc_combined (conf:B gen_gc_conf) data_to_word_None
      (roots:(A heap_address)list,heap:((A,B)heap_element)list,gs:gen_state,
       (_:num),(_:bool)) =
      (roots,heap,0,0,gs,T)) /\
   (gc_combined conf data_to_word_Simple (roots,heap,gs,_,_) =
      (let (roots,heap,a,c) = full_gc (roots,heap,gen_gc_conf_limit conf) in
       (roots,APPEND heap (heap_expand (gen_gc_conf_limit conf - a)),a,
        gen_gc_conf_limit conf - a,gs,c))) /\
   (gc_combined conf (Generational limits) (roots,heap,gs,rs,do_partial) =
      if do_partial then
        (let partial_conf = make_partial_conf conf gs rs in
         let (roots,state) = partial_gc partial_conf (roots,heap) in
         (roots,
          APPEND (APPEND (APPEND (gc_state_old state) (gc_state_h1 state))
                         (heap_expand (gc_state_n state)))
                 (gc_state_r1 state),
          gc_state_a state, gc_state_n state,
          GenState 0 (MAP (K (gc_state_a state)) limits), gc_state_ok state))
      else
        (let (roots,state) = gen_gc conf (roots,heap) in
         (roots,
          APPEND (APPEND (gc_state_h1 state) (heap_expand (gc_state_n state)))
                 (gc_state_r1 state),
          gc_state_a state, gc_state_n state,
          GenState 0 (MAP (K (gc_state_a state)) limits), gc_state_ok state)))`;;
