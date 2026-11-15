(* ========================================================================= *)
(* source_to_sourceProof: port of HOL4 compiler/backend/proofs/              *)
(* source_to_sourceProofScript.sml (CakeML v3479).  Correctness of the       *)
(* phase that collects the source-to-source transformations.                 *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/semantics.ml";;
needs "compiler/backend/source_to_source.ml";;
needs "compiler/backend/proofs/source_evalProof.ml";;
needs "compiler/backend/proofs/source_letProof.ml";;

type_invention_error := true;;

let source_to_sourceProof_compile_semantics = prove
 (`~semantics_prog (s:(FFI)state) env prog Fail /\ semantics_prog s env prog outcome ==>
   semantics_prog s env (source_to_source_compile prog) outcome`,
  REWRITE_TAC[source_to_source_compile_def] THEN
  MATCH_ACCEPT_TAC source_letProof_compile_semantics);;

let source_to_sourceProof_compile_semantics_oracle = prove
 (`!f. is_insert_oracle (ci:(C)compiler_instance) f (state_eval_state (s:(FFI)state)) /\
       ~semantics_prog s env prog Fail /\
       semantics_prog s env prog outcome ==>
       semantics_prog
         (state_eval_state_fupd (adjust_oracle ci (source_to_source_compile o f)) s)
         env prog outcome`,
  REWRITE_TAC[source_to_source_compile_def] THEN
  MATCH_ACCEPT_TAC source_letProof_compile_semantics_oracle);;
