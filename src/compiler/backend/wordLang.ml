(* ========================================================================= *)
(* wordLang: port of HOL4 compiler/backend/wordLangScript.sml               *)
(* (CakeML v3479).                                                           *)
(* The wordLang intermediate language consists of structured programs that  *)
(* operate over machine words, a list-like stack and a flat memory. This is  *)
(* the language where register allocation is performed.                     *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names: the prefix wl_ for the constructors and constants that clash     *)
(*   with other ILs (wl_exp, wl_prog, wl_Var, wl_Call, wl_every_var, ...), as *)
(*   notes/naming/names.tsv says.                                            *)
(* - HOL4 Type shift = ast$shift is the type abbreviation wl_shift (the     *)
(*   type shift of ast); Type cutsets = num_set # num_set is the type       *)
(*   abbreviation cutsets.                                                   *)
(* - HOL4 exp1_size (the size of an exp list) is list_size (wl_exp_size l). *)
(* - Words: n2w = word, ~0w = word_not (word 0), - = word_sub, << = word_shl,*)
(*   >>> = word_ushr, >> = word_ishr; FOLDR f e l = ITLIST f l e.             *)
(* - Definitions with a catch-all clause are made with sem1aux_def (HOL4's  *)
(*   TFL completion); HOL4's induction theorems of the non-recursive ones   *)
(*   (every_var_inst_ind, max_var_inst_ind: case analyses) come from the     *)
(*   kit's derive_induction with no termination conditions (IL2AUX_case_ind).*)
(* - The HOL4 Overloads ShiftN and shift are written out where used:         *)
(*     ShiftN sh e n = wl_Shift sh e (wl_Const (word n))                     *)
(*     shift = backend_common_word_shift                                     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/stackLang.ml";;
needs "semantics/sem1aux_tfl.ml";;

prioritize_num();;
type_invention_error := true;;

(* the induction theorem (a case analysis) that HOL4 makes for a            *)
(* non-recursive definition by patterns: one case per clause of the         *)
(* definition theorem def (the completed clauses)                          *)

let IL2AUX_case_ind (def:thm) : thm =
  let cls = map (fun cl -> let vs,eq = strip_forall cl in
                           let c,args = strip_comb(lhs eq) in vs,c,args)
                (conjuncts(concl def)) in
  let _,c,args0 = hd cls in
  let tty = mk_tuple_ty (map type_of args0) in
  let wfth = ISPEC (mk_abs(mk_var("x",tty),`0`)) WF_MEASURE in
  derive_induction c (map (fun (vs,_,args) -> vs,args) cls) [] wfth;;

new_type_abbrev("wl_shift",`:shift`);;

let wl_exp_INDUCT,wl_exp_RECURSION = cake_type
  "wl_exp = wl_Const (A word)
          | wl_Var num
          | Lookup store_name
          | wl_Load wl_exp
          | wl_Op binop (wl_exp list)
          | wl_Shift shift wl_exp wl_exp";;

(* HOL4: Overload ShiftN = \sh e n. Shift sh e (Const (n2w n)) (written     *)
(* out where used)                                                          *)

(* HOL4: MEM_IMP_exp_size *)

let wl_MEM_IMP_exp_size = prove
 (`!xs (a:(A)wl_exp). MEM a xs ==> wl_exp_size l a < list_size (wl_exp_size l) xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; list_size] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `a:(A)wl_exp`) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC]);;

(* non-GCed cutset, GCed cutset *)

new_type_abbrev("cutsets",`:num_set#num_set`);;

(* wl_Call: return vars, cut-set, return-handler code, labels l1,l2; target *)
(* of call; arguments; handler: varname, exception-handler code, labels     *)
(* l1,l2.  wl_Return: return lab, return values.  wl_OpCurrHeap: special    *)
(* case compiled well in stackLang.  wl_LocValue: assign v1 := Loc v2 0.    *)
(* wl_Install: code buffer start, length of new code, data buffer start,    *)
(* length of new data, cut-set.  wl_CodeBufferWrite: code buffer address,   *)
(* byte to write.  wl_DataBufferWrite: data buffer address, word to write.  *)
(* wl_FFI: FFI name, conf_ptr, conf_len, array_ptr, array_len, cut-set.     *)
(* ShareInst: memory operation, varname, expression for memory address.     *)

let wl_prog_INDUCT,wl_prog_RECURSION = cake_type
  "wl_prog = wl_Skip
           | wl_Move num ((num#num) list)
           | wl_Inst ((A)inst)
           | wl_Assign num ((A)wl_exp)
           | wl_Get num store_name
           | wl_Set store_name ((A)wl_exp)
           | wl_Store ((A)wl_exp) num
           | MustTerminate wl_prog
           | wl_Call ((num list#cutsets#wl_prog#num#num) option) (num option)
                     (num list) ((num#wl_prog#num#num) option)
           | wl_Seq wl_prog wl_prog
           | wl_If cmp num ((A)reg_imm) wl_prog wl_prog
           | wl_Loop num_set wl_prog num_set
           | wl_Alloc num cutsets
           | wl_StoreConsts num num num num ((bool#A word) list)
           | wl_Raise num
           | wl_Return num (num list)
           | wl_Break num
           | wl_Continue num
           | wl_Tick
           | wl_OpCurrHeap binop num num
           | wl_LocValue num num
           | wl_Install num num num num cutsets
           | wl_CodeBufferWrite num num
           | wl_DataBufferWrite num num
           | wl_FFI mlstring num num num num cutsets
           | ShareInst memop num ((A)wl_exp)";;

let raise_stub_location_def = cake_def
  `raise_stub_location = word_num_stubs - 2`;;

let wl_store_consts_stub_location_def = cake_def
  `wl_store_consts_stub_location = word_num_stubs - 1`;;

(* HOL4: EVAL ``raise_stub_location`` *)

let raise_stub_location_eq = prove
 (`raise_stub_location = 5`,
  REWRITE_TAC[raise_stub_location_def; word_num_stubs_def;
              stack_num_stubs_def] THEN ARITH_TAC);;

(* HOL4: EVAL ``store_consts_stub_location`` *)

let wl_store_consts_stub_location_eq = prove
 (`wl_store_consts_stub_location = 6`,
  REWRITE_TAC[wl_store_consts_stub_location_def; word_num_stubs_def;
              stack_num_stubs_def] THEN ARITH_TAC);;

(* wordLang uses syntactic invariants compared to stackLang that uses       *)
(* semantic flags.  Some of these are also used to EVAL (e.g. for the       *)
(* oracle).                                                                  *)

(* Recursors for variables *)

let every_var_exp_def = sem1aux_def
  `(every_var_exp P (wl_Var num:(A)wl_exp) <=> P num) /\
   (every_var_exp P (wl_Load exp) <=> every_var_exp P exp) /\
   (every_var_exp P (wl_Op wop ls) <=> ALL (every_var_exp P) ls) /\
   (every_var_exp P (wl_Shift sh e1 e2) <=>
      every_var_exp P e1 /\ every_var_exp P e2) /\
   (every_var_exp P expr <=> T)`;;

let every_var_exp_ind = cake_ind "every_var_exp";;

let every_var_imm_def = sem1aux_def
  `(every_var_imm P (Reg r:(A)reg_imm) <=> P r) /\
   (every_var_imm P (_:(A)reg_imm) <=> T)`;;

let every_var_inst_def = sem1aux_def
  `(every_var_inst P (asm_Const reg (w:A word)) <=> P reg) /\
   (every_var_inst P (asm_Arith (Binop bop r1 r2 ri)) <=>
      P r1 /\ P r2 /\ every_var_imm P ri) /\
   (every_var_inst P (asm_Arith (asm_Shift shift r1 r2 ri)) <=>
      P r1 /\ P r2 /\ every_var_imm P ri) /\
   (every_var_inst P (asm_Arith (asm_Div r1 r2 r3)) <=> P r1 /\ P r2 /\ P r3) /\
   (every_var_inst P (asm_Arith (asm_AddCarry r1 r2 r3 r4)) <=>
      P r1 /\ P r2 /\ P r3 /\ P r4) /\
   (every_var_inst P (asm_Arith (AddOverflow r1 r2 r3 r4)) <=>
      P r1 /\ P r2 /\ P r3 /\ P r4) /\
   (every_var_inst P (asm_Arith (SubOverflow r1 r2 r3 r4)) <=>
      P r1 /\ P r2 /\ P r3 /\ P r4) /\
   (every_var_inst P (asm_Arith (LongMul r1 r2 r3 r4)) <=>
      P r1 /\ P r2 /\ P r3 /\ P r4) /\
   (every_var_inst P (asm_Arith (LongDiv r1 r2 r3 r4 r5)) <=>
      P r1 /\ P r2 /\ P r3 /\ P r4 /\ P r5) /\
   (every_var_inst P (Mem asm_Load r (Addr a w)) <=> P r /\ P a) /\
   (every_var_inst P (Mem asm_Store r (Addr a w)) <=> P r /\ P a) /\
   (every_var_inst P (Mem asm_Load32 r (Addr a w)) <=> P r /\ P a) /\
   (every_var_inst P (Mem asm_Store32 r (Addr a w)) <=> P r /\ P a) /\
   (every_var_inst P (Mem Load8 r (Addr a w)) <=> P r /\ P a) /\
   (every_var_inst P (Mem Store8 r (Addr a w)) <=> P r /\ P a) /\
   (every_var_inst P (FP (FPLess r d1 d2)) <=> P r) /\
   (every_var_inst P (FP (FPLessEqual r d1 d2)) <=> P r) /\
   (every_var_inst P (FP (FPEqual r d1 d2)) <=> P r) /\
   (every_var_inst P (FP (FPMovToReg r1 r2 d):(A)inst) <=>
      if dimindex(:A) = 64 then P r1 else P r1 /\ P r2) /\
   (every_var_inst P (FP (FPMovFromReg d r1 r2)) <=>
      if dimindex(:A) = 64 then P r1 else P r1 /\ P r2) /\
   (every_var_inst P inst <=> T)`;;

let every_var_inst_ind = IL2AUX_case_ind every_var_inst_def;;

let every_name_def = cake_def
  `every_name P (t:cutsets) <=>
     ALL P (MAP FST (toAList (FST t))) /\ ALL P (MAP FST (toAList (SND t)))`;;

(* the clauses are parsed apart: names is a cutsets in some and a num_set   *)
(* in others                                                                 *)

let wl_every_var_def = sem1aux_def (list_mk_conj
 [`wl_every_var (P:num->bool) (wl_Skip:(A)wl_prog) <=> T`;
  `wl_every_var (P:num->bool) (wl_Move pri ls:(A)wl_prog) <=>
     ALL P (MAP FST ls) /\ ALL P (MAP SND ls)`;
  `wl_every_var (P:num->bool) (wl_Inst i:(A)wl_prog) <=> every_var_inst P i`;
  `wl_every_var (P:num->bool) (wl_Assign num exp:(A)wl_prog) <=>
     P num /\ every_var_exp P exp`;
  `wl_every_var (P:num->bool) (wl_Get num store:(A)wl_prog) <=> P num`;
  `wl_every_var (P:num->bool) (wl_Store exp num:(A)wl_prog) <=>
     P num /\ every_var_exp P exp`;
  `wl_every_var (P:num->bool) (wl_LocValue r _:(A)wl_prog) <=> P r`;
  `wl_every_var (P:num->bool) (wl_Install r1 r2 r3 r4 names:(A)wl_prog) <=>
     P r1 /\ P r2 /\ P r3 /\ P r4 /\ every_name P names`;
  `wl_every_var (P:num->bool) (wl_CodeBufferWrite r1 r2:(A)wl_prog) <=> P r1 /\ P r2`;
  `wl_every_var (P:num->bool) (wl_DataBufferWrite r1 r2:(A)wl_prog) <=> P r1 /\ P r2`;
  `wl_every_var (P:num->bool) (wl_FFI ffi_index cptr clen ptr len names:(A)wl_prog) <=>
     P cptr /\ P clen /\ P ptr /\ P len /\ every_name P names`;
  `wl_every_var (P:num->bool) (MustTerminate s1:(A)wl_prog) <=> wl_every_var P s1`;
  `wl_every_var (P:num->bool) (wl_Call ret dest args h:(A)wl_prog) <=>
     ALL P args /\
     (match ret with
        NONE -> T
      | SOME (v,cutset,ret_handler,l1,l2) ->
          ALL P v /\ every_name P cutset /\ wl_every_var P ret_handler /\
          (match h with
             NONE -> T
           | SOME (v,prog,l1,l2) -> P v /\ wl_every_var P prog))`;
  `wl_every_var (P:num->bool) (wl_Seq s1 s2:(A)wl_prog) <=>
     wl_every_var P s1 /\ wl_every_var P s2`;
  `wl_every_var (P:num->bool) (wl_If cmp r1 ri e2 e3:(A)wl_prog) <=>
     P r1 /\ every_var_imm P ri /\ wl_every_var P e2 /\ wl_every_var P e3`;
  `wl_every_var (P:num->bool) (wl_Alloc num numset:(A)wl_prog) <=>
     P num /\ every_name P numset`;
  `wl_every_var (P:num->bool) (wl_StoreConsts a b c d ws:(A)wl_prog) <=>
     P a /\ P b /\ P c /\ P d`;
  `wl_every_var (P:num->bool) (wl_Raise num:(A)wl_prog) <=> P num`;
  `wl_every_var (P:num->bool) (wl_Return num1 ns:(A)wl_prog) <=> P num1 /\ ALL P ns`;
  `wl_every_var (P:num->bool) (wl_OpCurrHeap _ num1 num2:(A)wl_prog) <=> P num1 /\ P num2`;
  `wl_every_var (P:num->bool) (wl_Tick:(A)wl_prog) <=> T`;
  `wl_every_var (P:num->bool) (wl_Set n exp:(A)wl_prog) <=> every_var_exp P exp`;
  `wl_every_var (P:num->bool) (ShareInst op num exp:(A)wl_prog) <=>
     P num /\ every_var_exp P exp`;
  `wl_every_var (P:num->bool) (wl_Loop names body exit_names:(A)wl_prog) <=>
     ALL P (MAP FST (toAList names)) /\ wl_every_var P body /\
     ALL P (MAP FST (toAList exit_names))`;
  `wl_every_var (P:num->bool) (p:(A)wl_prog) <=> T`]);;

let wl_every_var_ind = cake_ind "wl_every_var";;

(* Recursor for stack variables *)

let every_stack_var_def = sem1aux_def (list_mk_conj
 [`every_stack_var (P:num->bool) (wl_FFI ffi_index cptr clen ptr len names:(A)wl_prog) <=>
     every_name P names`;
  `every_stack_var (P:num->bool) (wl_Install _ _ _ _ names:(A)wl_prog) <=>
     every_name P names`;
  (* does not check the case where Calls are ill-formed *)
  `every_stack_var (P:num->bool) (wl_Call ret dest args h:(A)wl_prog) <=>
     (match ret with
        NONE -> T
      | SOME (v,cutset,ret_handler,l1,l2) ->
          every_name P cutset /\ every_stack_var P ret_handler /\
          (match h with
             NONE -> T
           | SOME (v,prog,l1,l2) -> every_stack_var P prog))`;
  `every_stack_var (P:num->bool) (wl_Alloc num numset:(A)wl_prog) <=> every_name P numset`;
  `every_stack_var (P:num->bool) (MustTerminate s1:(A)wl_prog) <=> every_stack_var P s1`;
  `every_stack_var (P:num->bool) (wl_Seq s1 s2:(A)wl_prog) <=>
     every_stack_var P s1 /\ every_stack_var P s2`;
  `every_stack_var (P:num->bool) (wl_If cmp r1 ri e2 e3:(A)wl_prog) <=>
     every_stack_var P e2 /\ every_stack_var P e3`;
  `every_stack_var (P:num->bool) (wl_Loop names body exit_names:(A)wl_prog) <=>
     every_stack_var P body`;
  `every_stack_var (P:num->bool) (p:(A)wl_prog) <=> T`]);;

let every_stack_var_ind = cake_ind "every_stack_var";;

(* Find the maximum variable *)

let max_var_exp_def = sem1aux_def
  `(max_var_exp (wl_Var num:(A)wl_exp) = num) /\
   (max_var_exp (wl_Load exp) = max_var_exp exp) /\
   (max_var_exp (wl_Op wop ls) = MAX_LIST (MAP max_var_exp ls)) /\
   (max_var_exp (wl_Shift sh exp1 exp2) =
      MAX (max_var_exp exp1) (max_var_exp exp2)) /\
   (max_var_exp exp = 0)`;;

let max_var_exp_ind = cake_ind "max_var_exp";;

let max_var_inst_def = sem1aux_def
  `(max_var_inst (asm_Skip:(A)inst) = 0) /\
   (max_var_inst (asm_Const reg w) = reg) /\
   (max_var_inst (asm_Arith (Binop bop r1 r2 ri)) =
      match ri with Reg r -> max3 r1 r2 r | _ -> MAX r1 r2) /\
   (max_var_inst (asm_Arith (asm_Shift shift r1 r2 n)) =
      match n with Reg r -> max3 r1 r2 r | _ -> MAX r1 r2) /\
   (max_var_inst (asm_Arith (asm_Div r1 r2 r3)) = max3 r1 r2 r3) /\
   (max_var_inst (asm_Arith (asm_AddCarry r1 r2 r3 r4)) =
      MAX (MAX r1 r2) (MAX r3 r4)) /\
   (max_var_inst (asm_Arith (AddOverflow r1 r2 r3 r4)) =
      MAX (MAX r1 r2) (MAX r3 r4)) /\
   (max_var_inst (asm_Arith (SubOverflow r1 r2 r3 r4)) =
      MAX (MAX r1 r2) (MAX r3 r4)) /\
   (max_var_inst (asm_Arith (LongMul r1 r2 r3 r4)) =
      MAX (MAX r1 r2) (MAX r3 r4)) /\
   (max_var_inst (asm_Arith (LongDiv r1 r2 r3 r4 r5)) =
      MAX (MAX (MAX r1 r2) (MAX r3 r4)) r5) /\
   (max_var_inst (Mem asm_Load r (Addr a w)) = MAX a r) /\
   (max_var_inst (Mem asm_Store r (Addr a w)) = MAX a r) /\
   (max_var_inst (Mem asm_Load32 r (Addr a w)) = MAX a r) /\
   (max_var_inst (Mem asm_Store32 r (Addr a w)) = MAX a r) /\
   (max_var_inst (Mem Load8 r (Addr a w)) = MAX a r) /\
   (max_var_inst (Mem Store8 r (Addr a w)) = MAX a r) /\
   (max_var_inst (FP (FPLess r f1 f2)) = r) /\
   (max_var_inst (FP (FPLessEqual r f1 f2)) = r) /\
   (max_var_inst (FP (FPEqual r f1 f2)) = r) /\
   (max_var_inst (FP (FPMovToReg r1 r2 d):(A)inst) =
      if dimindex(:A) = 64 then r1 else MAX r1 r2) /\
   (max_var_inst (FP (FPMovFromReg d r1 r2):(A)inst) =
      if dimindex(:A) = 64 then r1 else MAX r1 r2) /\
   (max_var_inst (_:(A)inst) = 0)`;;

let max_var_inst_ind = IL2AUX_case_ind max_var_inst_def;;

let cutsets_max_def = cake_def
  `cutsets_max (c:cutsets) =
     MAX (MAX_LIST (MAP FST (toAList (FST c))))
         (MAX_LIST (MAP FST (toAList (SND c))))`;;

let _ = cake_add_simps [cutsets_max_def];;

let max_var_def = sem1aux_def (list_mk_conj
 [`max_var (wl_Skip:(A)wl_prog) = 0`;
  `max_var (wl_Move pri ls:(A)wl_prog) =
     MAX_LIST (APPEND (MAP FST ls) (MAP SND ls))`;
  `max_var (wl_Inst i:(A)wl_prog) = max_var_inst i`;
  `max_var (wl_Assign num exp:(A)wl_prog) = MAX num (max_var_exp exp)`;
  `max_var (wl_Get num store:(A)wl_prog) = num`;
  `max_var (wl_Store exp num:(A)wl_prog) = MAX num (max_var_exp exp)`;
  `max_var (wl_Call ret dest args h:(A)wl_prog) =
     let n = MAX_LIST args in
     match ret with
       NONE -> n
     | SOME (v,cutset,ret_handler,l1,l2) ->
         let cutset_max = MAX n (cutsets_max cutset) in
         let ret_max = max3 (MAX_LIST v) cutset_max (max_var ret_handler) in
         (match h with
            NONE -> ret_max
          | SOME (v,prog,l1,l2) -> max3 v ret_max (max_var prog))`;
  `max_var (wl_Seq s1 s2:(A)wl_prog) = MAX (max_var s1) (max_var s2)`;
  `max_var (MustTerminate s1:(A)wl_prog) = max_var s1:num`;
  `max_var (wl_If cmp r1 ri e2 e3:(A)wl_prog) =
     let r = (match ri with Reg r -> MAX r r1 | _ -> r1) in
     max3 r (max_var e2) (max_var e3)`;
  `max_var (wl_Alloc num numset:(A)wl_prog) = MAX num (cutsets_max numset)`;
  `max_var (wl_StoreConsts a b c d ws:(A)wl_prog) = MAX_LIST [a;b;c;d]`;
  `max_var (wl_Install r1 r2 r3 r4 numset:(A)wl_prog) =
     MAX_LIST [r1;r2;r3;r4;cutsets_max numset]`;
  `max_var (wl_CodeBufferWrite r1 r2:(A)wl_prog) = MAX r1 r2`;
  `max_var (wl_DataBufferWrite r1 r2:(A)wl_prog) = MAX r1 r2`;
  `max_var (wl_FFI ffi_index ptr1 len1 ptr2 len2 numset:(A)wl_prog) =
     MAX_LIST [ptr1;len1;ptr2;len2;cutsets_max numset]`;
  `max_var (wl_Raise num:(A)wl_prog) = num`;
  `max_var (wl_OpCurrHeap _ num1 num2:(A)wl_prog) = MAX num1 num2`;
  `max_var (wl_Return num1 ns:(A)wl_prog) = MAX_LIST (CONS num1 ns)`;
  `max_var (wl_Tick:(A)wl_prog) = 0`;
  `max_var (wl_LocValue r l1:(A)wl_prog) = r`;
  `max_var (wl_Set n exp:(A)wl_prog) = max_var_exp exp`;
  `max_var (ShareInst op num exp:(A)wl_prog) = MAX num (max_var_exp exp)`;
  `max_var (wl_Loop names body exit_names:(A)wl_prog) =
     max3 (MAX_LIST (MAP FST (toAList names)))
          (max_var body)
          (MAX_LIST (MAP FST (toAList exit_names)))`;
  `max_var (p:(A)wl_prog) = 0`]);;

let max_var_ind = cake_ind "max_var";;

let word_op_def = cake_def
  `word_op op (ws:(A word) list) =
     match (op,ws) with
       (asm_And,ws) -> SOME (ITLIST word_and ws (word_not (word 0)))
     | (asm_Add,ws) -> SOME (ITLIST word_add ws (word 0))
     | (asm_Or,ws) -> SOME (ITLIST word_or ws (word 0))
     | (asm_Xor,ws) -> SOME (ITLIST word_xor ws (word 0))
     | (asm_Sub,[w1;w2]) -> SOME (word_sub w1 w2)
     | _ -> NONE`;;

let word_sh_def = cake_def
  `word_sh sh (w:A word) n =
     if ~(n = 0) /\ n >= dimindex(:A) then NONE else
     match sh with
       Lsl -> SOME (word_shl w n)
     | Lsr -> SOME (word_ushr w n)
     | Asr -> SOME (word_ishr w n)
     | Ror -> SOME (word_ror w n)`;;

let exp_to_addr_def = sem1aux_def
  `(exp_to_addr (wl_Var ad) = SOME (Addr ad (word 0)):((A)addr)option) /\
   (exp_to_addr (wl_Op asm_Add [wl_Var ad; wl_Const offset]) =
      SOME (Addr ad offset)) /\
   (exp_to_addr _ = NONE)`;;

(* HOL4: Overload shift = backend_common$word_shift (written out where used:*)
(* backend_common_word_shift)                                               *)

let word_loc_INDUCT,word_loc_RECURSION = cake_type
  "word_loc = wl_Word (A word) | wl_Loc num num";;
