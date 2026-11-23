(* ========================================================================= *)
(* stack_rawcall: port of HOL4 compiler/backend/stack_rawcallScript.sml      *)
(* (CakeML v3479).                                                           *)
(* This compiler phase introduces calls past the stack allocation code that *)
(* is present at almost every start of function. A call past stack          *)
(* allocation is called a RawCall. RawCalls are introduced to shortcut some *)
(* bookkeeping during tail-calls to known locations, i.e. Call NONE (INL    *)
(* dest) ...                                                                 *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/stackLang.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - HOL4 lists data_to_word among the Ancestors, but the theory uses no    *)
(*   name of it, so only stackLang is loaded.                                *)
(* - The HOL4 _pmatch theorems state the definitions with pmatch for case;  *)
(*   both are written as match here and compile to the same case constants, *)
(*   so each states its definition again.                                   *)

(* collect stack allocation information *)

let seq_stack_alloc_def = cake_def
  `seq_stack_alloc (p:(A)stack_prog) =
     match p with stack_Seq (StackAlloc k) _ -> SOME k | _ -> NONE`;;

let seq_stack_alloc_pmatch = prove
 (CASE_TERM
  `seq_stack_alloc (p:(A)stack_prog) =
     match p with stack_Seq (StackAlloc k) _ -> SOME k | _ -> NONE`,
  REWRITE_TAC[seq_stack_alloc_def]);;

let collect_info_def = cake_def
  `(collect_info ([]:(num#(A)stack_prog)list) (f:num spt) = f) /\
   (collect_info (CONS (n,b) xs) f =
      collect_info xs
        (match seq_stack_alloc b with NONE -> f | SOME k -> insert n k f))`;;

(* optimise based on stack allocation information *)

let dest_case_def = cake_def
  `dest_case (p1:(A)stack_prog) (p2:(A)stack_prog) =
     match p1 with
       StackFree k ->
         (match p2 with stack_Call NONE (INL d) NONE -> SOME (k,d) | _ -> NONE)
     | _ -> NONE`;;

let dest_case_pmatch = prove
 (CASE_TERM
  `dest_case (p1:(A)stack_prog) (p2:(A)stack_prog) =
     match p1 with
       StackFree k ->
         (match p2 with stack_Call NONE (INL d) NONE -> SOME (k,d) | _ -> NONE)
     | _ -> NONE`,
  REWRITE_TAC[dest_case_def]);;

let comp_seq_def = cake_def
  `comp_seq (p1:(A)stack_prog) (p2:(A)stack_prog) (i:num spt)
            (default:(A)stack_prog) =
     match dest_case p1 p2 with
       SOME (k,dest) ->
         (match lookup dest i with
            NONE -> default
          | SOME l ->
              if l = k then RawCall dest else
              if l < k then stack_Seq (StackFree (k - l)) (RawCall dest) else
                stack_Seq stack_Tick (stack_Seq (StackAlloc (l - k)) (RawCall dest)))
     | _ -> default`;;

(* HOL4: comp_def (HOL4 proves termination automatically, with the size of *)
(* the program)                                                              *)

let stack_rawcall_comp_def = cake_def_wf
  `MEASURE (\(i:num spt,p:(A)stack_prog). stack_prog_size (\x:A. 0) p)`
  TERM_TAC
  `stack_rawcall_comp (i:num spt) (p:(A)stack_prog) =
     match p with
       stack_Seq p1 p2 ->
         comp_seq p1 p2 i
           (stack_Seq (stack_rawcall_comp i p1) (stack_rawcall_comp i p2))
     | stack_If c r ri p1 p2 ->
         stack_If c r ri (stack_rawcall_comp i p1) (stack_rawcall_comp i p2)
     | stack_Loop p1 -> stack_Loop (stack_rawcall_comp i p1)
     | stack_Call (SOME (p1,lr,l1,l2)) dest NONE ->
         stack_Call (SOME (stack_rawcall_comp i p1,lr,l1,l2)) dest NONE
     | stack_Call (SOME (p1,lr,l1,l2)) dest (SOME (p2,k1,k2)) ->
         stack_Call (SOME (stack_rawcall_comp i p1,lr,l1,l2)) dest
                    (SOME (stack_rawcall_comp i p2,k1,k2))
     | _ -> p`;;

let stack_rawcall_comp_ind = cake_ind "stack_rawcall_comp";;

(* HOL4: comp_pmatch *)

let stack_rawcall_comp_pmatch = prove
 (concl stack_rawcall_comp_def,
  ACCEPT_TAC stack_rawcall_comp_def);;

let comp_top_def = cake_def
  `comp_top (i:num spt) (p:(A)stack_prog) =
     match p with
       stack_Seq p1 p2 ->
         stack_Seq (stack_rawcall_comp i p1) (stack_rawcall_comp i p2)
     | _ -> stack_rawcall_comp i p`;;

let comp_top_pmatch = prove
 (CASE_TERM
  `comp_top (i:num spt) (p:(A)stack_prog) =
     match p with
       stack_Seq p1 p2 ->
         stack_Seq (stack_rawcall_comp i p1) (stack_rawcall_comp i p2)
     | _ -> stack_rawcall_comp i p`,
  REWRITE_TAC[comp_top_def]);;

(* HOL4: compile_def *)

let stack_rawcall_compile_def = cake_def
  `stack_rawcall_compile (prog:(num#(A)stack_prog)list) =
     let i = collect_info prog LN in
     MAP (\(n,b:(A)stack_prog). (n,comp_top i b)) prog`;;
