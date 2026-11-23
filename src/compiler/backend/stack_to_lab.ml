(* ========================================================================= *)
(* stack_to_lab: port of HOL4 compiler/backend/stack_to_labScript.sml        *)
(* (CakeML v3479).                                                           *)
(* This compiler phase maps stackLang programs, which have structure such   *)
(* as If, While, Return etc, to labLang programs that are a soup of         *)
(* goto-like jumps.                                                          *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: stack_to_lab_flatten,                      *)
(*   stack_to_lab_config (fields stack_to_lab_config_reg_names, ..._jump,    *)
(*   ..._perf_calls) and stack_to_lab_compile carry the theory prefix.      *)
(* - The local HOL4 Overloads are written out: Asm a (an asm instruction)   *)
(*   is Asm (Asmi a), ++ is misc_Append (left-associative, as in HOL4).      *)
(* - 0w is word 0; the stackLang, labLang and asm constructors that clash   *)
(*   with other ILs carry their prefixes (stack_Seq, lab_Label, lab_Jump,    *)
(*   asm_Less, ...).                                                         *)
(* - HOL4 flatten_pmatch states flatten with PMATCH; here every match is    *)
(*   compiled to case constants, so it is the definition itself.             *)
(* - The prog_comp of compile_no_stubs are stack_remove's (applied to jump, *)
(*   offset, sp) and stack_alloc's (on the pairs), as their types say.       *)
(* - HOL4 negate is stack_to_lab_negate (a short or common word), and        *)
(*   negate_def is stack_to_lab_negate_def.                                  *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/labLang.ml";;
needs "compiler/backend/stack_alloc.ml";;
needs "compiler/backend/stack_remove.ml";;
needs "compiler/backend/stack_names.ml";;
needs "compiler/backend/bvl_to_bvi.ml";;
needs "compiler/backend/stack_rawcall.ml";;
needs "semantics/sem1aux_tfl.ml";;

prioritize_num();;
type_invention_error := true;;

let compile_jump_def = cake_def
  `(compile_jump (INL n) = LabAsm (lab_Jump (lab_Lab n 0)) (word 0) [] 0:(A)line) /\
   (compile_jump (INR r) = Asm (Asmi (JumpReg r)) [] 0)`;;

let stack_to_lab_negate_def = cake_def
  `(stack_to_lab_negate asm_Less = NotLess) /\
   (stack_to_lab_negate asm_Equal = NotEqual) /\
   (stack_to_lab_negate Lower = NotLower) /\
   (stack_to_lab_negate asm_Test = NotTest) /\
   (stack_to_lab_negate NotLess = asm_Less) /\
   (stack_to_lab_negate NotEqual = asm_Equal) /\
   (stack_to_lab_negate NotLower = Lower) /\
   (stack_to_lab_negate NotTest = asm_Test)`;;

let _ = cake_add_simps [stack_to_lab_negate_def];;

let find_lab_def = cake_def
  `find_lab n labs =
     match oEL n labs with
       NONE -> 0:num
     | SOME k -> k`;;

(* HOL4: flatten_def (the size of the program decreases) *)

let stack_to_lab_flatten_def = cake_def_wf
  `MEASURE (\(t:bool,p:(A)stack_prog,n:num,m:num,conts:num list,breaks:num list).
              stack_prog_size (\x:A. 0) p)`
  TERM_TAC
  `stack_to_lab_flatten t (p:(A)stack_prog) n m conts breaks =
     match p with
       stack_Tick -> (misc_List [Asm (Asmi (asm_Inst asm_Skip)) [] 0],F,m)
     | stack_Inst a -> (misc_List [Asm (Asmi (asm_Inst a)) [] 0],F,m)
     | stack_Halt _ -> (misc_List [LabAsm lab_Halt (word 0) [] 0],T,m)
     | stack_Seq p1 p2 ->
         let (xs,nr1,m) = stack_to_lab_flatten F p1 n m conts breaks in
         let (ys,nr2,m) = stack_to_lab_flatten F p2 n m conts breaks in
         if t then (misc_Append (misc_Append xs (misc_List [lab_Label n 1 0])) ys,
                    (nr1 \/ nr2),m)
         else (misc_Append xs ys,(nr1 \/ nr2),m)
     | stack_If c r ri p1 p2 ->
         let (xs,nr1,m) = stack_to_lab_flatten F p1 n m conts breaks in
         let (ys,nr2,m) = stack_to_lab_flatten F p2 n m conts breaks in
         if p1 = stack_Skip /\ p2 = stack_Skip then (misc_List [],F,m)
         else if p1 = stack_Skip then
           (misc_Append
              (misc_Append
                 (misc_List [LabAsm (lab_JumpCmp c r ri (lab_Lab n m)) (word 0) [] 0]) ys)
              (misc_List [lab_Label n m 0]),F,m + 1)
         else if p2 = stack_Skip then
           (misc_Append
              (misc_Append
                 (misc_List [LabAsm (lab_JumpCmp (stack_to_lab_negate c) r ri (lab_Lab n m))
                               (word 0) [] 0]) xs)
              (misc_List [lab_Label n m 0]),F,m + 1)
         else if nr1 then
           (misc_Append
              (misc_Append
                 (misc_Append
                    (misc_List [LabAsm (lab_JumpCmp (stack_to_lab_negate c) r ri (lab_Lab n m))
                                  (word 0) [] 0]) xs)
                 (misc_List [lab_Label n m 0])) ys,nr2,m + 1)
         else if nr2 then
           (misc_Append
              (misc_Append
                 (misc_Append
                    (misc_List [LabAsm (lab_JumpCmp c r ri (lab_Lab n m)) (word 0) [] 0])
                    ys)
                 (misc_List [lab_Label n m 0])) xs,nr1,m + 1)
         else
           (misc_Append
              (misc_Append
                 (misc_Append
                    (misc_Append
                       (misc_List [LabAsm (lab_JumpCmp c r ri (lab_Lab n m)) (word 0) [] 0])
                       ys)
                    (misc_List [LabAsm (lab_Jump (lab_Lab n (m + 1))) (word 0) [] 0;
                                lab_Label n m 0]))
                 xs)
              (misc_List [lab_Label n (m + 1) 0]),(nr1 /\ nr2),m + 2)
     | stack_Loop p1 ->
         let cont_lab = m in
         let break_lab = m + 1 in
         let (xs,nr,m) = stack_to_lab_flatten F p1 n (m + 2) (CONS cont_lab conts)
                           (CONS break_lab breaks) in
         (misc_Append
            (misc_Append (misc_List [lab_Label n cont_lab 0]) xs)
            (misc_List [LabAsm (lab_Jump (lab_Lab n cont_lab)) (word 0) [] 0;
                        lab_Label n break_lab 0]),F,m)
     | stack_Raise r -> (misc_List [Asm (Asmi (JumpReg r)) [] 0],T,m)
     | stack_Return r -> (misc_List [Asm (Asmi (JumpReg r)) [] 0],T,m)
     | stack_Break k ->
         (misc_List [LabAsm (lab_Jump (lab_Lab n (find_lab k breaks))) (word 0) [] 0],T,m)
     | stack_Continue k ->
         (misc_List [LabAsm (lab_Jump (lab_Lab n (find_lab k conts))) (word 0) [] 0],T,m)
     | RawCall n -> (misc_List [LabAsm (lab_Jump (lab_Lab n 1)) (word 0) [] 0],T,m)
     | stack_Call NONE dest handler -> (misc_List [compile_jump dest],T,m)
     | stack_Call (SOME (p1,lr,l1,l2)) dest handler ->
         let (xs,nr1,m) = stack_to_lab_flatten F p1 n m conts breaks in
         let prefix =
           misc_Append
             (misc_List [LabAsm (lab_LocValue lr (lab_Lab l1 l2)) (word 0) [] 0;
                         compile_jump dest; lab_Label l1 l2 0]) xs in
         (match handler with
            NONE -> (prefix,nr1,m)
          | SOME (p2,k1,k2) ->
              let (ys,nr2,m) = stack_to_lab_flatten F p2 n m conts breaks in
              (misc_Append prefix
                 (misc_Append
                    (misc_Append
                       (misc_List [LabAsm (lab_Jump (lab_Lab n m)) (word 0) [] 0;
                                   lab_Label k1 k2 0]) ys)
                    (misc_List [lab_Label n m 0])),(nr1 /\ nr2),m + 1))
     | JumpLower r1 r2 target ->
         (misc_List [LabAsm (lab_JumpCmp Lower r1 (Reg r2) (lab_Lab target 0))
                       (word 0) [] 0],F,m)
     | stack_FFI ffi_index _ _ _ _ lr ->
         (misc_List [LabAsm (lab_LocValue lr (lab_Lab n m)) (word 0) [] 0;
                     LabAsm (CallFFI ffi_index) (word 0) [] 0;
                     lab_Label n m 0],F,m + 1)
     | stack_LocValue i l1 l2 ->
         (misc_List [LabAsm (lab_LocValue i (lab_Lab l1 l2)) (word 0) [] 0],F,m)
     | stack_Install _ _ _ _ ret ->
         (misc_List [LabAsm (lab_LocValue ret (lab_Lab n m)) (word 0) [] 0;
                     LabAsm lab_Install (word 0) [] 0;
                     lab_Label n m 0],F,m + 1)
     | ShMemOp op r ad -> (misc_List [Asm (ShareMem op r ad) [] 0],F,m)
     | stack_CodeBufferWrite r1 r2 -> (misc_List [Asm (Cbw r1 r2) [] 0],F,m)
     | _ -> (misc_List [],F,m)`;;

let stack_to_lab_flatten_ind = cake_ind "stack_to_lab_flatten";;

(* HOL4 flatten_pmatch: the definition with PMATCH for case (see the       *)
(* header)                                                                   *)

let flatten_pmatch =
  GENL [`p:(A)stack_prog`; `n:num`; `m:num`; `conts:num list`; `breaks:num list`]
    (SPEC_ALL stack_to_lab_flatten_def);;

let is_Seq_def = sem1aux_def
  `(is_Seq (stack_Seq p1 p2:(A)stack_prog) <=> T) /\
   (is_Seq _ <=> F)`;;

let prog_to_section_def = cake_def
  `prog_to_section (n,p:(A)stack_prog) =
     let (lines,nr,m) = stack_to_lab_flatten T p n (next_lab p 2) [] [] in
     Section n (append (misc_Append lines
                          (misc_List [lab_Label n (if is_Seq p then m else 1) 0])))`;;

let is_gen_gc_def = cake_def
  `(is_gen_gc (Generational l) <=> T) /\
   (is_gen_gc _ <=> F)`;;

(* jump: whether to compile to JumpLower or If Lower ... in stack_remove;   *)
(* perf_calls: unverified: emit C-stack shadowing for perf call graphs     *)
(* (x64 only)                                                                *)

let stack_to_lab_config_INFO = cake_record "stack_to_lab_config"
  ["reg_names","num spt"; "jump","bool"; "perf_calls","bool"];;

let stack_to_lab_config_component_equality =
  stack_to_lab_config_INFO.ri_component_equality;;

let stack_to_lab_compile_def = cake_def
  `stack_to_lab_compile (stack_conf:stack_to_lab_config) (data_conf:data_to_word_config)
       max_heap sp (offset:A word#A word) (prog:(num#(A)stack_prog)list) =
     let prog = stack_rawcall_compile prog in
     let prog = stack_alloc_compile data_conf prog in
     let prog = stack_remove_compile (stack_to_lab_config_jump stack_conf) offset
                  (is_gen_gc (data_to_word_config_gc_kind data_conf))
                  max_heap sp InitGlobals_location prog in
     let prog = stack_names_compile (stack_to_lab_config_reg_names stack_conf) prog in
     MAP prog_to_section prog`;;

let compile_no_stubs_def = cake_def
  `compile_no_stubs f jump (offset:A word#A word) sp (prog:(num#(A)stack_prog)list) =
     MAP prog_to_section
       (stack_names_compile f
          (MAP (stack_remove_prog_comp jump offset sp)
             (MAP stack_alloc_prog_comp prog)))`;;
