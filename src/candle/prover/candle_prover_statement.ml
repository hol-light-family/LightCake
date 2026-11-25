(* ========================================================================= *)
(* The headline statement of the Candle theorem prover in the HOL Light     *)
(* port of CakeML v3479: HOL4 candle/prover/                                 *)
(* candle_prover_semanticsScript.sml                                         *)
(*   semantics_thm   (line 423)                                              *)
(* bound as the OCaml term candle_prover_semantics_statement, and the        *)
(* stronger corollary without the hypothesis prog_syntax_ok candle_code      *)
(* (decision D8, not in HOL4: that hypothesis is proved by evaluation)       *)
(*   semantics_thm_strong                                                    *)
(* bound as candle_prover_semantics_strong_statement.                        *)
(* candle_prover_semantics.ml loads this file, proves both theorems and     *)
(* checks at its end, failing loudly otherwise, that each has no hypotheses *)
(* and that its conclusion is alpha-equivalent to the term here.             *)
(*                                                                           *)
(* In words: run the Candle program candle_code (the CakeML basis library   *)
(* and the Candle kernel module, made by the translator) followed by any     *)
(* program prog that is safe (safe_dec: it neither builds values with the   *)
(* constructor names of the kernel's types nor writes to the kernel's FFI   *)
(* channel), from the initial state with any eval state es that is ok and  *)
(* an FFI state with no events yet.  If the result is not Fail, every event *)
(* of the terminating or diverging run is ok (ok_event: what is written on  *)
(* the kernel's channel is the bytes of a theorem th, provable in a context *)
(* ctxt that extends init_ctxt).                                             *)
(*                                                                           *)
(* The statement is HOL4's (the hypothesis prog_syntax_ok candle_code       *)
(* included, decision D8), with its free variables quantified in the order  *)
(* of their first occurrence; like HOL4's theorem it is polymorphic: HOL4's *)
(* 'ffi is FFI.  HOL4's notation as the port writes it:                      *)
(*   init_state ffi with eval_state := es                                    *)
(*                 state_eval_state_fupd (K es) (ml_init_state ffi)          *)
(*   init_env      ml_init_env                                               *)
(*   l1 ++ l2      APPEND l1 l2                                              *)
(*   eval_state_ok candle_eval_state_ok                                      *)
(*   EVERY         ALL                                                       *)
(*   ffi.io_events ffi_state_io_events ffi                                   *)
(*   every         llist_every                                               *)
(*                                                                           *)
(* Notions used, with the files of the port that define them (paths under   *)
(* src/):                                                                    *)
(*   semantics_prog, evaluate_prog_with_clock: semantics/semantics.ml        *)
(*   evaluate_decs (below semantics_prog): semantics/evaluate.ml             *)
(*   state and its fields (state_eval_state_fupd), eval_state:              *)
(*     semantics/semanticPrimitives.ml                                       *)
(*   behaviour (Terminate, Diverge, Fail), ffi_state and                     *)
(*     ffi_state_io_events, io_event (IO_event), ffiname (ExtCall):          *)
(*     semantics/ffi/ffi.ml                                                  *)
(*   ml_init_state, ml_init_env, prog_syntax_ok: translator/ml_prog.ml;      *)
(*     check_cons_dec_list (below prog_syntax_ok): translator/evaluate_dec.ml *)
(*   candle_code (the program; candle_prog_thm states that it evaluates to   *)
(*     candle_init_env and candle_init_state):                               *)
(*     candle/prover/candle_kernelProg.ml, from the kernel translation of    *)
(*     candle/standard/ml_kernel/ml_hol_kernel_funsProg.ml and the basis     *)
(*     program basisProg_basis of basis/basisProg.ml                         *)
(*   candle_eval_state_ok, safe_dec, safe_exp:                               *)
(*     candle/prover/candle_prover_inv.ml; every_exp: semantics/ast.ml;      *)
(*     every_dec: candle/prover/ast_extras.ml; id_to_n:                      *)
(*     semantics/namespace.ml                                                *)
(*   ok_event, kernel_ctors, kernel_ffi, thm2bytes:                          *)
(*     candle/prover/candle_kernel_vals.ml; thm_to_string:                   *)
(*     candle/standard/ml_kernel/print_thm.ml; holKernelProof_THM:           *)
(*     candle/standard/monadic/holKernelProof.ml; extends, init_ctxt:        *)
(*     candle/standard/syntax/holSyntax.ml                                   *)
(*   llist_every: hol4/llist.ml; ALL, APPEND: HOL Light's lists.ml           *)
(* ========================================================================= *)

needs "semantics/semantics.ml";;
needs "translator/ml_prog.ml";;
needs "candle/prover/candle_kernelProg.ml";;
needs "candle/prover/candle_kernel_vals.ml";;
needs "candle/prover/candle_prover_inv.ml";;
needs "hol4/llist.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4 semantics_thm (candle_prover_semanticsScript.sml line 423) *)
let candle_prover_semantics_statement =
  `!(ffi:(FFI)ffi_state) (es:(eval_state)option) (prog:dec list) (res:behaviour).
     semantics_prog (state_eval_state_fupd (K es) (ml_init_state ffi)) ml_init_env
                    (APPEND candle_code prog) res /\
     candle_eval_state_ok es /\
     prog_syntax_ok candle_code /\
     ALL safe_dec prog /\
     ffi_state_io_events ffi = [] /\
     ~(res = Fail)
     ==> (!outcome io_list. res = Terminate outcome io_list ==> ALL ok_event io_list) /\
         (!io_trace. res = Diverge io_trace ==> llist_every ok_event io_trace)`;;

(* the corollary of decision D8: semantics_thm without the hypothesis        *)
(* prog_syntax_ok candle_code (candle_prover_semantics.ml proves it,         *)
(* prog_syntax_ok_candle_code, by evaluation)                                *)
let candle_prover_semantics_strong_statement =
  `!(ffi:(FFI)ffi_state) (es:(eval_state)option) (prog:dec list) (res:behaviour).
     semantics_prog (state_eval_state_fupd (K es) (ml_init_state ffi)) ml_init_env
                    (APPEND candle_code prog) res /\
     candle_eval_state_ok es /\
     ALL safe_dec prog /\
     ffi_state_io_events ffi = [] /\
     ~(res = Fail)
     ==> (!outcome io_list. res = Terminate outcome io_list ==> ALL ok_event io_list) /\
         (!io_trace. res = Diverge io_trace ==> llist_every ok_event io_trace)`;;
