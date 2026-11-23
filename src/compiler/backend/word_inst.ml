(* ========================================================================= *)
(* word_inst: port of HOL4 compiler/backend/word_instScript.sml              *)
(* (CakeML v3479).                                                           *)
(* This compiler phase implements instruction selection. It uses the         *)
(* Maximal Munch strategy.                                                   *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: the wordLang constructors wl_...,          *)
(*   the asm constructors asm_Add, asm_Load, asm_Shift, ..., and             *)
(*   word_inst_is_const (HOL4 is_const).  HOL4 brings wordLang's Shift to    *)
(*   the front of its overloads: wl_Shift on expressions, asm_Shift inside   *)
(*   Arith.                                                                  *)
(* - HOL4's pmatch case expressions are written with match like all others, *)
(*   so the NAME_pmatch theorems restate the definitions in match form.      *)
(* - Words: n2w = word, w2n = val, -w = word_neg w, w1 - w2 = word_sub w1 w2,*)
(*   ~0w = word_not (word 0); c.valid_imm = asm_config_valid_imm c; the      *)
(*   overloads addr_offset_ok, hw_offset_ok and byte_offset_ok are written   *)
(*   out (asm_offset_ok 0 (asm_config_addr_offset c), ...).                  *)
(* - HOL4 exp_size ARB is wl_exp_size (\x. 0).                               *)
(* - Definitions with catch-all clauses are made with sem1aux_def(_wf)       *)
(*   (HOL4's TFL completion); convert_sub_ind (a case analysis) comes from  *)
(*   wordLang's IL2AUX_case_ind.                                             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/stackLang.ml";;
needs "hol4/sorting.ml";;

type_invention_error := true;;

(* Scheme:                                                                   *)
(* 1) Pull all nested ops and consts as far up as possible and convert       *)
(*    Sub [x; Const w] to Add [x; Const -w]                                  *)
(* 2) Flatten to binary branching expressions                                *)
(* 3) inst select, assuming binary branches                                  *)
(* 4) 3->2 regs if necessary                                                 *)

(* Pull all nested arguments with the same op up *)

let pull_ops_def = cake_def
  `(pull_ops (op:binop) [] acc = acc:((A)wl_exp)list) /\
   (pull_ops op (CONS x xs) acc =
      match x with
        wl_Op op' ls ->
          if op = op' then pull_ops op xs (APPEND ls acc)
          else pull_ops op xs (CONS x acc)
      | _ -> pull_ops op xs (CONS x acc))`;;

(* HOL4: is_const *)

let word_inst_is_const_def = sem1aux_def
  `(word_inst_is_const (wl_Const (w:A word)) <=> T) /\
   (word_inst_is_const (_:(A)wl_exp) <=> F)`;;

(* the second clause makes it total *)

let rm_const_def = sem1aux_def
  `(rm_const (wl_Const w) = w:A word) /\
   (rm_const (_:(A)wl_exp) = word 0)`;;

let convert_sub_def = sem1aux_def
  `(convert_sub [wl_Const w1; wl_Const w2] = wl_Const (word_sub w1 w2):(A)wl_exp) /\
   (convert_sub [x; wl_Const w] = wl_Op asm_Add [wl_Const (word_neg w); x]) /\
   (convert_sub ls = wl_Op asm_Sub ls)`;;

let convert_sub_ind = IL2AUX_case_ind convert_sub_def;;

let convert_sub_pmatch = prove
 (CASE_TERM
  `!l. convert_sub l =
       match l with
         [wl_Const w1; wl_Const w2] -> wl_Const (word_sub w1 w2):(A)wl_exp
       | [x; wl_Const w] -> wl_Op asm_Add [wl_Const (word_neg w); x]
       | ls -> wl_Op asm_Sub ls`,
  REPEAT GEN_TAC THEN REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[convert_sub_def]) THEN
  FS[convert_sub_def]);;

let op_consts_def = sem1aux_def
  `(op_consts asm_And = wl_Const (word_not (word 0)):(A)wl_exp) /\
   (op_consts _ = wl_Const (word 0))`;;

let op_consts_pmatch = prove
 (CASE_TERM
  `!op. op_consts op =
        match op with
          asm_And -> wl_Const (word_not (word 0)):(A)wl_exp
        | _ -> wl_Const (word 0)`,
  GEN_TAC THEN CASES_ON `op:binop` THEN CASE_REWRITE_TAC[op_consts_def]);;

(* Returns a definite value *)

let reduce_const_def = cake_def
  `reduce_const op (w:A word) rest =
     if w = word 0 then
       if op = asm_Add \/ op = asm_Or \/ op = asm_Xor then
         match rest with
           [] -> wl_Const w
         | [x] -> x
         | _ -> wl_Op op rest
       else if op = asm_And then wl_Const (word 0)
       else wl_Op op (CONS (wl_Const w) rest)
     else wl_Op op (CONS (wl_Const w) rest)`;;

let optimize_consts_def = cake_def
  `optimize_consts op (ls:((A)wl_exp)list) =
     let (const_ls,nconst_ls) = PARTITION word_inst_is_const ls in
     match const_ls with
       [] -> wl_Op op nconst_ls
     | _ ->
         let w = THE (word_op op (MAP rm_const const_ls)) in
         reduce_const op w nconst_ls`;;

(* If this expression contains a constant it should be head of the output  *)
(* operation list                                                           *)

(* the termination conditions: as the kit's TERM_TAC, after splitting a     *)
(* MEM over an explicit list (MEM x (CONS a (CONS b l))) into its cases     *)

let WORDP1AUX_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ; MEM] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  REPEAT (FIRST_X_ASSUM (DISJ_CASES_THEN ASSUME_TAC)) THEN
  RVEQ_TAC THEN TERM_TAC;;

(* the fourth clause: first pull all the inner expressions, then pull at  *)
(* the topmost                                                              *)

let pull_exp_def = sem1aux_def_wf `MEASURE (wl_exp_size (\x:A. 0))` WORDP1AUX_TC_TAC
  `(pull_exp (wl_Op asm_Sub ls) =
      let new_ls = MAP pull_exp ls in
      convert_sub new_ls) /\
   (pull_exp (wl_Op op []) = op_consts op) /\
   (pull_exp (wl_Op op [x]) = pull_exp x) /\
   (pull_exp (wl_Op op ls) =
      let new_ls = MAP pull_exp ls in
      let pull_ls = pull_ops op new_ls [] in
      optimize_consts op pull_ls) /\
   (pull_exp (wl_Load exp) = wl_Load (pull_exp exp)) /\
   (pull_exp (wl_Shift shift exp nexp) =
      wl_Shift shift (pull_exp exp) (pull_exp nexp)) /\
   (pull_exp (exp:(A)wl_exp) = exp)`;;

let pull_exp_ind = cake_ind "pull_exp";;

let pull_exp_pmatch = prove
 (CASE_TERM
  `!exp:(A)wl_exp.
     pull_exp exp =
     match exp with
       wl_Op asm_Sub ls -> (let new_ls = MAP pull_exp ls in convert_sub new_ls)
     | wl_Op op [] -> op_consts op
     | wl_Op op [x] -> pull_exp x
     | wl_Op op ls ->
         (let new_ls = MAP pull_exp ls in
          let pull_ls = pull_ops op new_ls [] in
          optimize_consts op pull_ls)
     | wl_Load exp -> wl_Load (pull_exp exp)
     | wl_Shift sh exp nexp -> wl_Shift sh (pull_exp exp) (pull_exp nexp)
     | exp -> exp`,
  REPEAT GEN_TAC THEN REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[pull_exp_def]) THEN
  FS[pull_exp_def]);;

(* Flatten list expressions to trees of the form                            *)
(* Op op [Op op [Op op [c; d]; b]; a]                                         *)

let flatten_exp_def = sem1aux_def
  `(flatten_exp (wl_Op asm_Sub exps) = wl_Op asm_Sub (MAP flatten_exp exps)) /\
   (flatten_exp (wl_Op op []) = op_consts op) /\
   (flatten_exp (wl_Op op [x]) = flatten_exp x) /\
   (flatten_exp (wl_Op op (CONS x xs)) =
      wl_Op op [flatten_exp (wl_Op op xs); flatten_exp x]) /\
   (flatten_exp (wl_Load exp) = wl_Load (flatten_exp exp)) /\
   (flatten_exp (wl_Shift shift exp nexp) =
      wl_Shift shift (flatten_exp exp) (flatten_exp nexp)) /\
   (flatten_exp (exp:(A)wl_exp) = exp)`;;

let flatten_exp_ind = cake_ind "flatten_exp";;

let is_Lookup_CurrHeap_def = sem1aux_def
  `(is_Lookup_CurrHeap (Lookup CurrHeap:(A)wl_exp) <=> T) /\
   (is_Lookup_CurrHeap (_:(A)wl_exp) <=> F)`;;

let is_Lookup_CurrHeap_pmatch = prove
 (CASE_TERM
  `is_Lookup_CurrHeap (e:(A)wl_exp) <=>
     (match e with Lookup CurrHeap -> T | _ -> F)`,
  REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[is_Lookup_CurrHeap_def]) THEN
  FS[is_Lookup_CurrHeap_def]);;

(* Maximal Munch instruction selection on (binary) expressions; c is an    *)
(* asm_config to check validity of imms.  Optimized munches (assumes Consts *)
(* are on the RIGHT): Load [Op Add [exp; Const w]], Op op [exp; Const w],   *)
(* Store exp var.  Instruction selection assumes the input is binary        *)
(* branching; each step takes tar and temp, where temporaries may be stored *)
(* in temp and the value of the whole expression must be saved in tar.      *)
(* HOL4 addr_offset_ok c is asm_offset_ok 0 (asm_config_addr_offset c).     *)
(* The last clause makes it total.                                           *)

let inst_select_exp_def = sem1aux_def_wf
  `MEASURE (\x:(A)asm_config#num#num#(A)wl_exp.
              wl_exp_size (\x:A. 0) (SND (SND (SND x))))`
  WORDP1AUX_TC_TAC
  `(inst_select_exp (c:(A)asm_config) (tar:num) (temp:num) (wl_Load exp) =
      match exp with
        wl_Op asm_Add [exp'; wl_Const w] ->
          if asm_offset_ok 0 (asm_config_addr_offset c) w then
            let prog = inst_select_exp c temp temp exp' in
            wl_Seq prog (wl_Inst (Mem asm_Load tar (Addr temp w)))
          else
            let prog = inst_select_exp c temp temp exp in
            wl_Seq prog (wl_Inst (Mem asm_Load tar (Addr temp (word 0))))
      | _ ->
          let prog = inst_select_exp c temp temp exp in
          wl_Seq prog (wl_Inst (Mem asm_Load tar (Addr temp (word 0))))) /\
   (inst_select_exp c tar temp (wl_Const w) = wl_Inst (asm_Const tar w)) /\
   (inst_select_exp c tar temp (wl_Var v) = wl_Move 0 [tar,v]) /\
   (inst_select_exp c tar temp (Lookup store_name) = wl_Get tar store_name) /\
   (inst_select_exp c tar temp (wl_Op op [e1;e2]) =
      if is_Lookup_CurrHeap e2 then
        (let p1 = inst_select_exp c temp temp e1 in
         wl_Seq p1 (wl_OpCurrHeap op tar temp))
      else if is_Lookup_CurrHeap e1 /\ ~(op = asm_Sub) then
        (let p2 = inst_select_exp c temp temp e2 in
         wl_Seq p2 (wl_OpCurrHeap op tar temp))
      else
      let p1 = inst_select_exp c temp temp e1 in
      match e2 with
        wl_Const w ->
          if asm_config_valid_imm c (INL op) w then
            wl_Seq p1 (wl_Inst (asm_Arith (Binop op tar temp (Imm w))))
          else if op = asm_Add /\ asm_config_valid_imm c (INL asm_Sub) (word_neg w)
          then
            wl_Seq p1 (wl_Inst (asm_Arith (Binop asm_Sub tar temp (Imm (word_neg w)))))
          else
            let p2 = wl_Inst (asm_Const (temp+1) w) in
            wl_Seq p1 (wl_Seq p2 (wl_Inst (asm_Arith
                                    (Binop op tar temp (Reg (temp+1))))))
      | _ ->
          let p2 = inst_select_exp c (temp+1) (temp+1) e2 in
          wl_Seq p1 (wl_Seq p2 (wl_Inst (asm_Arith
                                  (Binop op tar temp (Reg (temp+1))))))) /\
   (inst_select_exp c tar temp (wl_Shift sh exp e1) =
      match e1 with
        wl_Const shift_len ->
          let n = val shift_len in
          if n < dimindex(:A) then
            (let prog = inst_select_exp c temp temp exp in
             if n = 0 then wl_Seq prog (wl_Move 0 [tar,temp])
             else wl_Seq prog (wl_Inst (asm_Arith (asm_Shift sh tar temp (Imm (word n))))))
          else wl_Inst (asm_Const tar (word 0))
      | _ ->
          let p = inst_select_exp c temp temp exp in
          let p1 = inst_select_exp c (temp+1) (temp+1) e1 in
          wl_Seq p (wl_Seq p1 (wl_Inst (asm_Arith
                                 (asm_Shift sh tar temp (Reg (temp+1))))))) /\
   (inst_select_exp _ _ _ _ = wl_Skip)`;;

let inst_select_exp_ind = cake_ind "inst_select_exp";;

let inst_select_exp_pmatch = prove
 (CASE_TERM
  `!(c:(A)asm_config) tar temp (exp:(A)wl_exp).
     inst_select_exp c tar temp exp =
     match exp with
       wl_Load (wl_Op asm_Add [exp'; wl_Const w]) ->
         if asm_offset_ok 0 (asm_config_addr_offset c) w then
           let prog = inst_select_exp c temp temp exp' in
           wl_Seq prog (wl_Inst (Mem asm_Load tar (Addr temp w)))
         else
           (let prog = inst_select_exp c temp temp (wl_Op asm_Add [exp'; wl_Const w]) in
            wl_Seq prog (wl_Inst (Mem asm_Load tar (Addr temp (word 0)))))
     | wl_Load exp ->
         (let prog = inst_select_exp c temp temp exp in
          wl_Seq prog (wl_Inst (Mem asm_Load tar (Addr temp (word 0)))))
     | wl_Const w -> wl_Inst (asm_Const tar w)
     | wl_Var v -> wl_Move 0 [tar,v]
     | Lookup store_name -> wl_Get tar store_name
     | wl_Op op [e1;e2] ->
         (if is_Lookup_CurrHeap e2 then
            (let p1 = inst_select_exp c temp temp e1 in
             wl_Seq p1 (wl_OpCurrHeap op tar temp))
          else if is_Lookup_CurrHeap e1 /\ ~(op = asm_Sub) then
            (let p2 = inst_select_exp c temp temp e2 in
             wl_Seq p2 (wl_OpCurrHeap op tar temp))
          else
            match e2 with
              wl_Const w ->
                if asm_config_valid_imm c (INL op) w then
                  wl_Seq (inst_select_exp c temp temp e1)
                    (wl_Inst (asm_Arith (Binop op tar temp (Imm w))))
                else if op = asm_Add /\
                        asm_config_valid_imm c (INL asm_Sub) (word_neg w) then
                  wl_Seq (inst_select_exp c temp temp e1)
                    (wl_Inst (asm_Arith (Binop asm_Sub tar temp (Imm (word_neg w)))))
                else
                  let p2 = wl_Inst (asm_Const (temp+1) w) in
                  wl_Seq (inst_select_exp c temp temp e1)
                    (wl_Seq p2 (wl_Inst (asm_Arith
                                  (Binop op tar temp (Reg (temp+1))))))
            | _ ->
                let p2 = inst_select_exp c (temp+1) (temp+1) e2 in
                wl_Seq (inst_select_exp c temp temp e1)
                  (wl_Seq p2 (wl_Inst (asm_Arith
                                (Binop op tar temp (Reg (temp+1)))))))
     | wl_Shift sh exp e1 ->
         (match e1 with
            wl_Const shift_len ->
              let n = val shift_len in
              if n < dimindex(:A) then
                (let prog = inst_select_exp c temp temp exp in
                 if n = 0 then wl_Seq prog (wl_Move 0 [tar,temp])
                 else wl_Seq prog (wl_Inst (asm_Arith
                                    (asm_Shift sh tar temp (Imm (word n))))))
              else wl_Inst (asm_Const tar (word 0))
          | _ ->
              let p = inst_select_exp c temp temp exp in
              let p1 = inst_select_exp c (temp+1) (temp+1) e1 in
              wl_Seq p (wl_Seq p1 (wl_Inst (asm_Arith
                                     (asm_Shift sh tar temp (Reg (temp+1)))))))
     | _ -> wl_Skip`,
  REPEAT GEN_TAC THEN
  REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[inst_select_exp_def; LET_DEF; LET_END_DEF]) THEN
  FS[inst_select_exp_def; LET_DEF; LET_END_DEF]);;

(* Flattens all expressions in program, temp must a fresh var.  The clauses *)
(* are parsed apart: names is a cutsets in one clause and a num_set in      *)
(* another, n a num list and a num.  HOL4 hw_offset_ok c and byte_offset_ok *)
(* c are asm_offset_ok 0 (asm_config_hw_offset c) and                        *)
(* asm_offset_ok 0 (asm_config_byte_offset c).                              *)

let inst_select_def = sem1aux_def (list_mk_conj
 [`inst_select (c:(A)asm_config) (temp:num) (wl_Assign v exp:(A)wl_prog) =
     (inst_select_exp c v temp o flatten_exp o pull_exp) exp`;
  `inst_select (c:(A)asm_config) (temp:num) (wl_Set store exp:(A)wl_prog) =
     let prog = (inst_select_exp c temp temp o flatten_exp o pull_exp) exp in
     wl_Seq prog (wl_Set store (wl_Var temp))`;
  `inst_select (c:(A)asm_config) (temp:num) (wl_Store exp var:(A)wl_prog) =
     let exp = (flatten_exp o pull_exp) exp in
     match exp with
       wl_Op asm_Add [exp'; wl_Const w] ->
         if asm_offset_ok 0 (asm_config_addr_offset c) w then
           let prog = inst_select_exp c temp temp exp' in
           wl_Seq prog (wl_Inst (Mem asm_Store var (Addr temp w)))
         else
           let prog = inst_select_exp c temp temp exp in
           wl_Seq prog (wl_Inst (Mem asm_Store var (Addr temp (word 0))))
     | _ ->
         let prog = inst_select_exp c temp temp exp in
         wl_Seq prog (wl_Inst (Mem asm_Store var (Addr temp (word 0))))`;
  `inst_select (c:(A)asm_config) (temp:num) (wl_Seq p1 p2:(A)wl_prog) =
     wl_Seq (inst_select c temp p1) (inst_select c temp p2):(A)wl_prog`;
  `inst_select (c:(A)asm_config) (temp:num) (MustTerminate p1:(A)wl_prog) =
     MustTerminate (inst_select c temp p1):(A)wl_prog`;
  `inst_select (c:(A)asm_config) (temp:num) (ShareInst op v exp:(A)wl_prog) =
     let exp = (flatten_exp o pull_exp) exp in
     match exp with
       wl_Op asm_Add [exp'; wl_Const w] ->
         if ((op = asm_Load \/ op = asm_Store) /\
             asm_offset_ok 0 (asm_config_addr_offset c) w) \/
            ((op = asm_Load32 \/ op = asm_Store32) /\
             asm_offset_ok 0 (asm_config_addr_offset c) w) \/
            ((op = Load16 \/ op = Store16) /\
             asm_offset_ok 0 (asm_config_hw_offset c) w) \/
            ((op = Load8 \/ op = Store8) /\
             asm_offset_ok 0 (asm_config_byte_offset c) w) then
           let prog = inst_select_exp c temp temp exp' in
           wl_Seq prog (ShareInst op v (wl_Op asm_Add [wl_Var temp; wl_Const w]))
         else
           let prog = inst_select_exp c temp temp exp in
           wl_Seq prog (ShareInst op v (wl_Var temp))
     | _ ->
         let prog = inst_select_exp c temp temp exp in
         wl_Seq prog (ShareInst op v (wl_Var temp))`;
  `inst_select (c:(A)asm_config) (temp:num) (wl_If cmp r1 ri c1 c2:(A)wl_prog) =
     wl_If cmp r1 ri (inst_select c temp c1) (inst_select c temp c2):(A)wl_prog`;
  `inst_select (c:(A)asm_config) (temp:num)
               (wl_Call ret dest args handler:(A)wl_prog) =
     let retsel =
       match ret with
         NONE -> NONE
       | SOME (n,names,ret_handler,l1,l2) ->
           SOME (n,names,inst_select c temp ret_handler,l1,l2) in
     let handlersel =
       match handler with
         NONE -> NONE
       | SOME (n,h,l1,l2) -> SOME (n,inst_select c temp h,l1,l2) in
     wl_Call retsel dest args handlersel:(A)wl_prog`;
  `inst_select (c:(A)asm_config) (temp:num)
               (wl_Loop names body exit_names:(A)wl_prog) =
     wl_Loop names (inst_select c temp body) exit_names:(A)wl_prog`;
  `inst_select (c:(A)asm_config) (temp:num) (prog:(A)wl_prog) = prog`]);;

let inst_select_ind = cake_ind "inst_select";;

let inst_select_pmatch = prove
 (CASE_TERM
  `!(c:(A)asm_config) temp (prog:(A)wl_prog).
     inst_select c temp prog =
     match prog with
       wl_Assign v exp -> (inst_select_exp c v temp o flatten_exp o pull_exp) exp
     | wl_Set store exp ->
         (let prog = (inst_select_exp c temp temp o flatten_exp o pull_exp) exp in
          wl_Seq prog (wl_Set store (wl_Var temp)))
     | wl_Store exp var ->
         (let exp = (flatten_exp o pull_exp) exp in
          match exp with
            wl_Op asm_Add [exp'; wl_Const w] ->
              if asm_offset_ok 0 (asm_config_addr_offset c) w then
                let prog = inst_select_exp c temp temp exp' in
                wl_Seq prog (wl_Inst (Mem asm_Store var (Addr temp w)))
              else
                let prog = inst_select_exp c temp temp exp in
                wl_Seq prog (wl_Inst (Mem asm_Store var (Addr temp (word 0))))
          | _ ->
              let prog = inst_select_exp c temp temp exp in
              wl_Seq prog (wl_Inst (Mem asm_Store var (Addr temp (word 0)))))
     | wl_Seq p1 p2 -> wl_Seq (inst_select c temp p1) (inst_select c temp p2)
     | MustTerminate p1 -> MustTerminate (inst_select c temp p1)
     | wl_If cmp r1 ri c1 c2 ->
         wl_If cmp r1 ri (inst_select c temp c1) (inst_select c temp c2)
     | ShareInst op var exp ->
         (let exp = (flatten_exp o pull_exp) exp in
          match exp with
            wl_Op asm_Add [exp'; wl_Const w] ->
              if ((op = asm_Load \/ op = asm_Store) /\
                  asm_offset_ok 0 (asm_config_addr_offset c) w) \/
                 ((op = asm_Load32 \/ op = asm_Store32) /\
                  asm_offset_ok 0 (asm_config_addr_offset c) w) \/
                 ((op = Load16 \/ op = Store16) /\
                  asm_offset_ok 0 (asm_config_hw_offset c) w) \/
                 ((op = Load8 \/ op = Store8) /\
                  asm_offset_ok 0 (asm_config_byte_offset c) w) then
                let prog = inst_select_exp c temp temp exp' in
                wl_Seq prog (ShareInst op var (wl_Op asm_Add [wl_Var temp; wl_Const w]))
              else
                let prog = inst_select_exp c temp temp exp in
                wl_Seq prog (ShareInst op var (wl_Var temp))
          | _ ->
              let prog = inst_select_exp c temp temp exp in
              wl_Seq prog (ShareInst op var (wl_Var temp)))
     | wl_Call ret dest args handler ->
         (let retsel =
            match ret with
              NONE -> NONE
            | SOME (n,names,ret_handler,l1,l2) ->
                SOME (n,names,inst_select c temp ret_handler,l1,l2) in
          let handlersel =
            match handler with
              NONE -> NONE
            | SOME (n,h,l1,l2) -> SOME (n,inst_select c temp h,l1,l2) in
          wl_Call retsel dest args handlersel)
     | wl_Loop names body exit_names ->
         wl_Loop names (inst_select c temp body) exit_names
     | prog -> prog`,
  REPEAT GEN_TAC THEN
  REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[inst_select_def; LET_DEF; LET_END_DEF]) THEN
  FS[inst_select_def; LET_DEF; LET_END_DEF]);;

(* Convert all 3 register instructions to 2 register instructions.  The     *)
(* clauses are parsed apart (names is a cutsets and a num_set, n a num list, *)
(* a num and a reg_imm).                                                     *)

let three_to_two_reg_def = sem1aux_def (list_mk_conj
 [`three_to_two_reg (wl_Inst (asm_Arith (Binop bop r1 r2 ri)):(A)wl_prog) =
     wl_Seq (wl_Move 0 [r1,r2]) (wl_Inst (asm_Arith (Binop bop r1 r1 ri))):(A)wl_prog`;
  `three_to_two_reg (wl_Inst (asm_Arith (asm_Shift l r1 r2 n)):(A)wl_prog) =
     wl_Seq (wl_Move 0 [r1,r2]) (wl_Inst (asm_Arith (asm_Shift l r1 r1 n))):(A)wl_prog`;
  `three_to_two_reg (wl_Inst (asm_Arith (asm_AddCarry r1 r2 r3 r4)):(A)wl_prog) =
     wl_Seq (wl_Move 0 [r1,r2])
       (wl_Inst (asm_Arith (asm_AddCarry r1 r1 r3 r4))):(A)wl_prog`;
  `three_to_two_reg (wl_Inst (asm_Arith (AddOverflow r1 r2 r3 r4)):(A)wl_prog) =
     wl_Seq (wl_Move 0 [r1,r2])
       (wl_Inst (asm_Arith (AddOverflow r1 r1 r3 r4))):(A)wl_prog`;
  `three_to_two_reg (wl_Inst (asm_Arith (SubOverflow r1 r2 r3 r4)):(A)wl_prog) =
     wl_Seq (wl_Move 0 [r1,r2])
       (wl_Inst (asm_Arith (SubOverflow r1 r1 r3 r4))):(A)wl_prog`;
  `three_to_two_reg (wl_OpCurrHeap bop r1 r2:(A)wl_prog) =
     wl_Seq (wl_Move 0 [r1,r2]) (wl_OpCurrHeap bop r1 r1):(A)wl_prog`;
  `three_to_two_reg (wl_Seq p1 p2:(A)wl_prog) =
     wl_Seq (three_to_two_reg p1) (three_to_two_reg p2):(A)wl_prog`;
  `three_to_two_reg (MustTerminate p1:(A)wl_prog) =
     MustTerminate (three_to_two_reg p1):(A)wl_prog`;
  `three_to_two_reg (wl_If cmp r1 ri c1 c2:(A)wl_prog) =
     wl_If cmp r1 ri (three_to_two_reg c1) (three_to_two_reg c2):(A)wl_prog`;
  `three_to_two_reg (wl_Call ret dest args handler:(A)wl_prog) =
     let retsel =
       match ret with
         NONE -> NONE
       | SOME (n,names,ret_handler,l1,l2) ->
           SOME (n,names,three_to_two_reg ret_handler,l1,l2) in
     let handlersel =
       match handler with
         NONE -> NONE
       | SOME (n,h,l1,l2) -> SOME (n,three_to_two_reg h,l1,l2) in
     wl_Call retsel dest args handlersel:(A)wl_prog`;
  `three_to_two_reg (wl_Loop names body exit_names:(A)wl_prog) =
     wl_Loop names (three_to_two_reg body) exit_names:(A)wl_prog`;
  `three_to_two_reg (prog:(A)wl_prog) = prog`]);;

let three_to_two_reg_ind = cake_ind "three_to_two_reg";;

let three_to_two_reg_pmatch = prove
 (CASE_TERM
  `!prog:(A)wl_prog.
     three_to_two_reg prog =
     match prog with
       wl_Inst (asm_Arith (Binop bop r1 r2 ri)) ->
         wl_Seq (wl_Move 0 [r1,r2]) (wl_Inst (asm_Arith (Binop bop r1 r1 ri)))
     | wl_Inst (asm_Arith (asm_Shift l r1 r2 n)) ->
         wl_Seq (wl_Move 0 [r1,r2]) (wl_Inst (asm_Arith (asm_Shift l r1 r1 n)))
     | wl_Inst (asm_Arith (asm_AddCarry r1 r2 r3 r4)) ->
         wl_Seq (wl_Move 0 [r1,r2]) (wl_Inst (asm_Arith (asm_AddCarry r1 r1 r3 r4)))
     | wl_Inst (asm_Arith (AddOverflow r1 r2 r3 r4)) ->
         wl_Seq (wl_Move 0 [r1,r2]) (wl_Inst (asm_Arith (AddOverflow r1 r1 r3 r4)))
     | wl_Inst (asm_Arith (SubOverflow r1 r2 r3 r4)) ->
         wl_Seq (wl_Move 0 [r1,r2]) (wl_Inst (asm_Arith (SubOverflow r1 r1 r3 r4)))
     | wl_OpCurrHeap bop r1 r2 ->
         wl_Seq (wl_Move 0 [r1,r2]) (wl_OpCurrHeap bop r1 r1)
     | wl_Seq p1 p2 -> wl_Seq (three_to_two_reg p1) (three_to_two_reg p2)
     | MustTerminate p1 -> MustTerminate (three_to_two_reg p1)
     | wl_If cmp r1 ri c1 c2 ->
         wl_If cmp r1 ri (three_to_two_reg c1) (three_to_two_reg c2)
     | wl_Call ret dest args handler ->
         (let retsel =
            match ret with
              NONE -> NONE
            | SOME (n,names,ret_handler,l1,l2) ->
                SOME (n,names,three_to_two_reg ret_handler,l1,l2) in
          let handlersel =
            match handler with
              NONE -> NONE
            | SOME (n,h,l1,l2) -> SOME (n,three_to_two_reg h,l1,l2) in
          wl_Call retsel dest args handlersel)
     | wl_Loop names body exit_names ->
         wl_Loop names (three_to_two_reg body) exit_names
     | prog -> prog`,
  REPEAT GEN_TAC THEN
  REPEAT (TOP_CASE_TAC THEN
          ASM_REWRITE_TAC[three_to_two_reg_def; LET_DEF; LET_END_DEF]) THEN
  FS[three_to_two_reg_def; LET_DEF; LET_END_DEF]);;

let three_to_two_reg_prog_def = cake_def
  `three_to_two_reg_prog b (prog:(A)wl_prog) =
     if b then three_to_two_reg prog else prog`;;
