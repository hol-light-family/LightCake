(* ========================================================================= *)
(* backend_common: port of HOL4 compiler/backend/backend_commonScript.sml    *)
(* (CakeML v3479).                                                           *)
(* Definitions that are common for many parts of the compiler backend.       *)
(* ========================================================================= *)

needs "hol4/sptree.ml";;
needs "hol4/words4.ml";;
needs "misc/misc.ml";;

prioritize_num();;
type_invention_error := true;;

let opw_INDUCT,opw_RECURSION = cake_type
  "opw = Andw | Orw | backend_common_Xor | backend_common_Add | backend_common_Sub";;

(* Small general definition *)
let small_enough_int_def = cake_def
  `small_enough_int (i:int) <=> --(&268435457) <= i /\ i <= &268435457`;;

(* these must match what the prim_types_program generates *)

let bind_tag_def = cake_def
  `bind_tag = 0`;;

let chr_tag_def = cake_def
  `chr_tag = 1`;;

let div_tag_def = cake_def
  `div_tag = 2`;;

let subscript_tag_def = cake_def
  `subscript_tag = 3`;;

let false_tag_def = cake_def
  `false_tag = 0`;;

let true_tag_def = cake_def
  `true_tag = 1`;;

let nil_tag_def = cake_def
  `nil_tag = 0`;;

let cons_tag_def = cake_def
  `cons_tag = 0`;;

let none_tag_def = cake_def
  `none_tag = 0`;;

let some_tag_def = cake_def
  `some_tag = 0`;;

let tuple_tag_def = cake_def
  `tuple_tag = 0`;;

let closure_tag_def = cake_def
  `closure_tag = 30`;;

let partial_app_tag_def = cake_def
  `partial_app_tag = 31`;;

let clos_tag_shift_def = cake_def
  `clos_tag_shift tag = if tag < 30 then tag else tag + 2`;;

(* Trace of an expression through the compiler, for exploring             *)
(* transformations: SourceLoc start-row start-col end-row end-col;         *)
(* backend_common_None is the dead trace (do not make traces at all).      *)

let tra_INDUCT,tra_RECURSION = cake_type
  "tra = SourceLoc num num num num
       | backend_common_Cons tra num
       | backend_common_Union tra tra
       | backend_common_None";;

(* HOL4 writes backend_common_Cons as an infix (an overload of a symbol). *)

(* An orphan expression is one that originates directly from a            *)
(* declaration (in source_to_mod and con_to_dec): declarations do not come *)
(* annotated with their source locations.  This trace is a basis for the   *)
(* traces of orphan expressions; its structure guarantees that it does not *)
(* conflict with any trace originating from source.                        *)

let orphan_trace_def = cake_def
  `orphan_trace = SourceLoc 2 2 1 1`;;

(* Create new Cons trace, unless original trace is None, indicating traces *)
(* are turned off.                                                         *)

let mk_cons_def = cake_def
  `mk_cons tr (n:num) =
     match tr with
       backend_common_None -> backend_common_None
     | _ -> backend_common_Cons tr n`;;

(* HOL4 writes mk_cons as an infix (an overload of a symbol). *)

(* Create new Cons trace, unless any of the original traces are None,      *)
(* indicating traces are turned off.                                       *)

let mk_union_def = cake_def
  `mk_union tr1 tr2 =
     match tr1 with
       backend_common_None -> backend_common_None
     | _ -> (match tr2 with
               backend_common_None -> backend_common_None
             | _ -> backend_common_Union tr1 tr2)`;;

let bool_to_tag_def = cake_def
  `bool_to_tag b = if b then true_tag else false_tag`;;

let stack_num_stubs_def = cake_def
  `stack_num_stubs = 5`;;

(* the stubs: raise, store consts *)
let word_num_stubs_def = cake_def
  `word_num_stubs = (stack_num_stubs + 1) + 1`;;

(* the stubs: general 32, bignum 23 *)
let data_num_stubs_def = cake_def
  `data_num_stubs = (word_num_stubs + 32) + 23`;;

(* the last 1 is a dummy to make it a multiple of 4 *)
let bvl_num_stubs_def = cake_def
  `bvl_num_stubs = (data_num_stubs + 9) + 1`;;

let bvl_to_bvi_namespaces_def = cake_def
  `bvl_to_bvi_namespaces = 4`;;

let data_num_stubs_EVEN = prove
 (`EVEN data_num_stubs`,
  REWRITE_TAC[data_num_stubs_def; word_num_stubs_def; stack_num_stubs_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let bvl_num_stub_MOD = prove
 (`bvl_num_stubs MOD bvl_to_bvi_namespaces = 0`,
  REWRITE_TAC[bvl_num_stubs_def; data_num_stubs_def; word_num_stubs_def;
              stack_num_stubs_def; bvl_to_bvi_namespaces_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* shift values, per dimindex(:A).  This could be defined as               *)
(* LOG 2 (dimindex(:A)) - 3, but LOG should not end up in the generated    *)
(* CakeML code.  HOL4 word_shift (:A) takes the type as argument: here the *)
(* argument is the universe (:A), as for dimword; the definition is        *)
(* backend_common_word_shift_DEF and the HOL4 statement                    *)
(* backend_common_word_shift_def.                                          *)

let backend_common_word_shift_DEF = new_definition
  `backend_common_word_shift (s:A->bool) =
     if dimindex(:A) = 32 then 2 else 3`;;

let backend_common_word_shift_def = prove
 (`backend_common_word_shift (:A) = if dimindex(:A) = 32 then 2 else 3`,
  REWRITE_TAC[backend_common_word_shift_DEF]);;

let upper_w2w_def = cake_def
  `upper_w2w (w:A word) =
     if dimindex(:A) = 32 then word_shl (word_zx w:int64) 32
     else word_zx w:int64`;;

let word_add_carry_def = cake_def
  `word_add_carry (l:A word) (r:A word) (c:A word) =
     let res = (val l + val r) + (if c = word 0 then 0 else 1) in
     (word res:A word, if dimword(:A) <= res then word 1:A word else word 0)`;;

(* HOL4 TODO: prefer this over ITLIST delete?  Consider upstreaming this   *)
(* and its associated lemmas (e.g. domain_list_delete in loop_liveProof).  *)

let list_delete_def = cake_def
  `(list_delete [] (s:A spt) = s) /\
   (list_delete (CONS (v:num) vs) s = list_delete vs (delete v s))`;;

let lookup_list_delete = prove
 (`!xs (l:A spt) n. lookup n (list_delete xs l) =
                    if MEM n xs then NONE else lookup n l`,
  LIST_INDUCT_TAC THEN RW[list_delete_def; lookup_delete; MEM] THEN FS[]);;
