(* ========================================================================= *)
(* ffi: port of HOL4 semantics/ffi/ffiScript.sml (CakeML v3479).             *)
(* Definition of the FFI type.                                               *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The HOL4 type variable 'ffi is FFI; word8 is byte; the mlstring        *)
(*   literal of the empty string is implode "".                              *)
(* - HOL4's type abbreviations oracle_function and oracle have a type        *)
(*   variable, which HOL Light abbreviations cannot have: they are expanded  *)
(*   where they are used (the field oracle of ffi_state).                    *)
(* - Record fields st.oracle, st.ffi_state, st.io_events are                 *)
(*   ffi_state_oracle st, ffi_state_ffi_state st, ffi_state_io_events st;    *)
(*   the literal with oracle, ffi_state and io_events is ffi_state_REC.      *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;
needs "hol4/llist.ml";;
needs "hol4/words4.ml";;

type_invention_error := true;;

(* An oracle says how to perform an FFI call based on its internal state,   *)
(* represented by the type variable FFI (HOL4 'ffi).                        *)

let ffi_outcome_INDUCT,ffi_outcome_RECURSION = cake_type
  "ffi_outcome = FFI_failed | FFI_diverged";;

let oracle_result_INDUCT,oracle_result_RECURSION = cake_type
  "oracle_result = Oracle_return FFI (byte list) | Oracle_final ffi_outcome";;

let shmem_op_INDUCT,shmem_op_RECURSION = cake_type
  "shmem_op = MappedRead | MappedWrite";;

let ffiname_INDUCT,ffiname_RECURSION = cake_type
  "ffiname = ExtCall mlstring | SharedMem shmem_op";;

(* HOL4: Type oracle_function =                                              *)
(*   :'ffi -> word8 list -> word8 list -> 'ffi oracle_result                *)
(* HOL4: Type oracle = :ffiname -> 'ffi oracle_function                      *)
(* (both expanded at use: ffiname->FFI->byte list->byte list->               *)
(* (FFI)oracle_result)                                                       *)

(* An I/O event, IO_event s bytes bytes2, represents the call of FFI        *)
(* function s with immutable input bytes and mutable input MAP FST bytes2,  *)
(* returning MAP SND bytes2 in the mutable array.                            *)

let io_event_INDUCT,io_event_RECURSION = cake_type
  "io_event = IO_event ffiname (byte list) ((byte#byte) list)";;

let final_event_INDUCT,final_event_RECURSION = cake_type
  "final_event = Final_event ffiname (byte list) (byte list) ffi_outcome";;

let ffi_state_INFO = cake_record "ffi_state"
  ["oracle","ffiname->FFI->byte list->byte list->(FFI)oracle_result";
   "ffi_state","FFI";
   "io_events","io_event list"];;

let ffi_state_component_equality =
  (record_info "ffi_state").ri_component_equality;;

let initial_ffi_state_def = cake_def
  `initial_ffi_state
     (oc:ffiname->FFI->byte list->byte list->(FFI)oracle_result) (ffi:FFI) =
   ffi_state_REC oc ffi []`;;

let ffi_result_INDUCT,ffi_result_RECURSION = cake_type
  "ffi_result = FFI_return ((FFI)ffi_state) (byte list) | FFI_final final_event";;

let call_FFI_def = cake_def
  `call_FFI (st:(FFI)ffi_state) s conf bytes =
     if ~(s = ExtCall (implode "")) then
       match ffi_state_oracle st s (ffi_state_ffi_state st) conf bytes with
         Oracle_return ffi' bytes' ->
           if LENGTH bytes' = LENGTH bytes then
             FFI_return
               (ffi_state_ffi_state_fupd (K ffi')
                  (ffi_state_io_events_fupd
                     (K (APPEND (ffi_state_io_events st)
                                [IO_event s conf (ZIP bytes bytes')])) st))
               bytes'
           else FFI_final (Final_event s conf bytes FFI_failed)
       | Oracle_final outcome ->
           FFI_final (Final_event s conf bytes outcome)
     else FFI_return st bytes`;;

let outcome_INDUCT,outcome_RECURSION = cake_type
  "outcome = Success | Resource_limit_hit | FFI_outcome final_event";;

(* A program can Diverge, Terminate, or Fail.  We prove that Fail is        *)
(* avoided.  For Diverge and Terminate, we keep track of what I/O events    *)
(* are valid I/O events for this behaviour.                                  *)
(* - Diverge: there cannot be any non-returning FFI calls in a diverging    *)
(*   execution.  The list of I/O events can be finite or infinite, hence    *)
(*   the llist (lazy list) type.                                            *)
(* - Terminate: terminating executions can only perform a finite number of  *)
(*   FFI calls.  The execution can be terminated by a non-returning FFI     *)
(*   call.                                                                  *)
(* - Fail: failure is a behaviour which we prove cannot occur for any       *)
(*   well-typed program.                                                    *)

let behaviour_INDUCT,behaviour_RECURSION = cake_type
  "behaviour = Diverge (io_event llist) | Terminate outcome (io_event list) | Fail";;

(* trace-based semantics can be recovered as an instance of oracle-based    *)
(* semantics as follows.                                                     *)

let trace_oracle_def = cake_def
  `trace_oracle (s:ffiname) (io_trace:io_event llist) (conf:byte list)
                (input:byte list) =
     match LHD io_trace with
       NONE -> Oracle_final FFI_failed
     | SOME (IO_event s' conf' bytes2) ->
         if s = s' /\ MAP FST bytes2 = input /\ conf = conf' then
           Oracle_return (THE (LTL io_trace)) (MAP SND bytes2)
         else Oracle_final FFI_failed`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas used by several later files.                                       *)
(* ------------------------------------------------------------------------- *)

let SEM2AUX_call_FFI_io_events = prove
 (`!(st:(FFI)ffi_state) s conf bytes st' bytes'.
     call_FFI st s conf bytes = FFI_return st' bytes' ==>
     isPREFIX (ffi_state_io_events st) (ffi_state_io_events st')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[call_FFI_def] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[injectivity "ffi_result"; distinctness "ffi_result"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN SIMP[IS_PREFIX_APPEND3; IS_PREFIX_REFL]);;
