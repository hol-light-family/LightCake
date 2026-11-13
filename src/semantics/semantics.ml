(* ========================================================================= *)
(* semantics: port of HOL4 semantics/semanticsScript.sml (CakeML v3479).     *)
(* The top-level semantics of CakeML programs.                               *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's record type state (hidden after its definition) is              *)
(*   semantics_state (notes/naming/names.tsv), fields semantics_state_tenv,  *)
(*   semantics_state_type_ids, semantics_state_sem_st and                    *)
(*   semantics_state_sem_env; its literal is semantics_state_REC tenv        *)
(*   type_ids sem_st sem_env (fields in order).                              *)
(* - mkNT is INL; TOK ## I is PAIR_MAP TOK I (vocab.ml); some is the binder *)
(*   of vocab.ml; fromList of llist is llist_fromList; a set is a predicate. *)
(* - semantics_prog is defined with sem1aux_def (one equation by cases on    *)
(*   the behaviour, then HOL4's three clauses).                              *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/lexer_fun.ml";;
needs "semantics/cmlPtreeConversion.ml";;
needs "semantics/primTypes.ml";;
needs "hol4/lprefix_lub.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

let parse_def = cake_def
  `parse (toks:(token#locs)list) =
     match some pt. valid_lptree cmlG pt /\
                    ptree_head pt = NT (INL nTopLevelDecs) /\
                    real_fringe pt = MAP (TOK ## I) toks with
       NONE -> NONE
     | SOME p -> ptree_TopLevelDecs p`;;

(* the type system state (tenv, type_ids) and the semantics state (sem_st,  *)
(* sem_env)                                                                  *)

let semantics_state_INFO = cake_record "semantics_state"
  ["tenv","type_env";
   "type_ids","type_ident->bool";
   "sem_st","(FFI)state";
   "sem_env","(v)sem_env"];;

let semantics_state_component_equality =
  semantics_state_INFO.ri_component_equality;;

let can_type_prog_def = cake_def
  `can_type_prog (state:(FFI)semantics_state) (prog:dec list) <=>
     ?new_tids new_tenv.
       DISJOINT (semantics_state_type_ids state) new_tids /\
       type_ds T (semantics_state_tenv state) prog new_tids new_tenv`;;

let evaluate_prog_with_clock_def = cake_def
  `evaluate_prog_with_clock (st:(FFI)state) (env:v sem_env) (k:num)
                            (prog:dec list) =
     let (st',r) = evaluate_decs (state_clock_fupd (K k) st) env prog in
     (state_ffi st',r)`;;

(* Terminate: there is a clock for which evaluation terminates, either      *)
(* internally or via FFI, and the accumulated io events match the given     *)
(* io_list.  Diverge: for all clocks, evaluation times out, and the         *)
(* io_trace is the least upper bound of the set of traces produced for each *)
(* clock.  Fail: there is a clock for which evaluation produces a runtime   *)
(* type error.                                                               *)

let semantics_prog_def = sem1aux_def
  `(semantics_prog (st:(FFI)state) (env:v sem_env) (prog:dec list)
                   (Terminate outcome io_list) <=>
      ?k ffi r.
        evaluate_prog_with_clock st env k prog = (ffi,r) /\
        (match r with
           Rerr (Rabort (Rffi_error outcome')) -> outcome = FFI_outcome outcome'
         | r -> ~(r = Rerr (Rabort Rtimeout_error)) /\ outcome = Success) /\
        io_list = ffi_state_io_events ffi /\
        ~(r = Rerr (Rabort Rtype_error))) /\
   (semantics_prog st env prog (Diverge io_trace) <=>
      (!k. ?ffi.
         evaluate_prog_with_clock st env k prog =
         (ffi,Rerr (Rabort Rtimeout_error))) /\
      lprefix_lub
        (IMAGE
           (\k. llist_fromList
                  (ffi_state_io_events
                     (FST (evaluate_prog_with_clock st env k prog))))
           UNIV)
        io_trace) /\
   (semantics_prog st env prog Fail <=>
      ?k. SND (evaluate_prog_with_clock st env k prog) = Rerr (Rabort Rtype_error))`;;

let semantics_INDUCT,semantics_RECURSION = cake_type
  "semantics = CannotParse | IllTyped | Execute (behaviour->bool)";;

let semantics_def = cake_def
  `semantics (state:(FFI)semantics_state) (prelude:dec list) (input:string) =
     match parse (lexer_fun input) with
       NONE -> CannotParse
     | SOME prog ->
         if can_type_prog state (APPEND prelude prog)
         then Execute (semantics_prog (semantics_state_sem_st state)
                         (semantics_state_sem_env state) (APPEND prelude prog))
         else IllTyped`;;

let semantics_init_def = cake_def
  `semantics_init (ffi:(FFI)ffi_state) =
     semantics (semantics_state_REC prim_tenv prim_type_ids
                  (FST (THE (prim_sem_env ffi)))
                  (SND (THE (prim_sem_env ffi))))`;;
