(* ========================================================================= *)
(* loop_to_word: port of HOL4 pancake/loop_to_wordScript.sml (CakeML v3479). *)
(* Compilation from loopLang to wordLang.                                    *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as notes/naming/names.tsv says: find_var, comp, comp_func,        *)
(*   compile_prog and compile get the prefix loop_to_word_.                  *)
(* - loopLang constructors are loop_Const, loop_Var, ... (Mark and LocValue  *)
(*   keep their names); wordLang's are wl_Const, wl_Var, ..., Lookup and     *)
(*   ShareInst; asm's AddCarry, Div, Load32, Store32, Add, Inst are          *)
(*   asm_AddCarry, asm_Div, asm_Load32, asm_Store32, asm_Add, wl_Inst;       *)
(*   panLang's AddCarry (the primop) is panLang_AddCarry.                    *)
(* - () is one, 0w is word 0, 1w is word 1; the HOL4 let blocks are nested   *)
(*   lets; HOL4's paired lambda in compile_prog is a paired lambda.          *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "pancake/loopLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/backend_common.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4: find_var_def *)

let loop_to_word_find_var_def = cake_def
  `loop_to_word_find_var (ctxt:num spt) v =
     match lookup v ctxt with
       NONE -> 0
     | SOME n -> (n:num)`;;

let find_reg_imm_def = cake_def
  `(find_reg_imm ctxt (Imm (w:A word)) = Imm w) /\
   (find_reg_imm ctxt (Reg n) = Reg (loop_to_word_find_var ctxt n))`;;

let comp_exp_def = cake_def_wf
  `measure (\(ctxt:num spt,e:(A)loop_exp). loop_exp_size (\x:A. 0) e)`
  TERM_TAC
  `(comp_exp ctxt (loop_Const (w:A word)) = wl_Const w) /\
   (comp_exp ctxt (loop_Var n) = wl_Var (loop_to_word_find_var ctxt n)) /\
   (comp_exp ctxt (loop_Lookup m) = Lookup (Temp m)) /\
   (comp_exp ctxt loop_BaseAddr = Lookup CurrHeap) /\
   (comp_exp ctxt loop_TopAddr =
      wl_Op asm_Add [Lookup CurrHeap;
                     wl_Shift Lsl (Lookup HeapLength) (wl_Const (word 1))]) /\
   (comp_exp ctxt (loop_Load exp) = wl_Load (comp_exp ctxt exp)) /\
   (comp_exp ctxt (loop_Shift s exp1 exp2) =
      wl_Shift s (comp_exp ctxt exp1) (comp_exp ctxt exp2)) /\
   (comp_exp ctxt (loop_Op op wexps) =
      let wexps = MAP (comp_exp ctxt) wexps in
      wl_Op op wexps)`;;

let comp_exp_ind = cake_ind "comp_exp";;

let toNumSet_def = cake_def
  `(toNumSet [] = (LN:num_set)) /\
   (toNumSet (CONS n ns) = insert n one (toNumSet ns))`;;

let fromNumSet_def = cake_def
  `fromNumSet (t:num_set) = MAP FST (toAList t)`;;

let mk_new_cutset_def = cake_def
  `mk_new_cutset ctxt (l:num_set) =
     insert 0 one (toNumSet (MAP (loop_to_word_find_var ctxt) (fromNumSet l)))`;;

(* HOL4: comp_def.  The recursion is on the size of the loopLang program. *)
(* The global name a of HOL4's SetGlobal clause is g here (one quotation   *)
(* gives a variable one type; a is a num in the Load32 clauses).           *)

let loop_to_word_comp_def = cake_def_wf
  `measure (\(ctxt:num spt,p:(A)loop_prog,l:num#num). loop_prog_size (\x:A. 0) p)`
  TERM_TAC
  `(loop_to_word_comp ctxt (loop_Skip:(A)loop_prog) l = (wl_Skip:(A)wl_prog,l)) /\
   (loop_to_word_comp ctxt (loop_Assign n e) l =
      (wl_Assign (loop_to_word_find_var ctxt n) (comp_exp ctxt e),l)) /\
   (loop_to_word_comp ctxt (loop_Primitive lhss pop rhss) l =
      match pop with
        panLang_AddCarry ->
          if LENGTH lhss = 2 /\ LENGTH rhss = 3 then
            let res = EL 0 lhss in
            let co = EL 1 lhss in
            let li = EL 0 rhss in
            let ri = EL 1 rhss in
            let ci = EL 2 rhss in
            let scratch_ci = 1 in
            let scratch_res = 3 in
              (wl_Seq (wl_Assign scratch_ci (wl_Var (loop_to_word_find_var ctxt ci)))
              (wl_Seq (wl_Inst (asm_Arith (asm_AddCarry scratch_res
                                         (loop_to_word_find_var ctxt li)
                                         (loop_to_word_find_var ctxt ri)
                                         scratch_ci)))
              (wl_Seq (wl_Assign (loop_to_word_find_var ctxt co) (wl_Var scratch_ci))
                      (wl_Assign (loop_to_word_find_var ctxt res) (wl_Var scratch_res)))),
               l)
          else (wl_Skip,l)) /\
   (loop_to_word_comp ctxt (loop_Arith arith) l =
      match arith with
        LLongMul r1 r2 r3 r4 ->
          (wl_Inst (asm_Arith (LongMul (loop_to_word_find_var ctxt r1)
                     (loop_to_word_find_var ctxt r2)
                     (loop_to_word_find_var ctxt r3)
                     (loop_to_word_find_var ctxt r4))),l)
      | LLongDiv r1 r2 r3 r4 r5 ->
          (wl_Inst (asm_Arith (LongDiv (loop_to_word_find_var ctxt r1)
                     (loop_to_word_find_var ctxt r2)
                     (loop_to_word_find_var ctxt r3)
                     (loop_to_word_find_var ctxt r4)
                     (loop_to_word_find_var ctxt r5))),l)
      | LDiv r1 r2 r3 ->
          (wl_Inst (asm_Arith (asm_Div (loop_to_word_find_var ctxt r1)
                     (loop_to_word_find_var ctxt r2)
                     (loop_to_word_find_var ctxt r3))),l)) /\
   (loop_to_word_comp ctxt (loop_Store e v) l =
      (wl_Store (comp_exp ctxt e) (loop_to_word_find_var ctxt v),l)) /\
   (loop_to_word_comp ctxt (loop_SetGlobal g e) l =
      (wl_Set (Temp g) (comp_exp ctxt e),l)) /\
   (loop_to_word_comp ctxt (loop_Load32 a v) l =
      (wl_Inst (Mem asm_Load32 (loop_to_word_find_var ctxt v)
                 (Addr (loop_to_word_find_var ctxt a) (word 0))),l)) /\
   (loop_to_word_comp ctxt (loop_LoadByte a v) l =
      (wl_Inst (Mem Load8 (loop_to_word_find_var ctxt v)
                 (Addr (loop_to_word_find_var ctxt a) (word 0))),l)) /\
   (loop_to_word_comp ctxt (loop_Store32 a v) l =
      (wl_Inst (Mem asm_Store32 (loop_to_word_find_var ctxt v)
                 (Addr (loop_to_word_find_var ctxt a) (word 0))),l)) /\
   (loop_to_word_comp ctxt (loop_StoreByte a v) l =
      (wl_Inst (Mem Store8 (loop_to_word_find_var ctxt v)
                 (Addr (loop_to_word_find_var ctxt a) (word 0))),l)) /\
   (loop_to_word_comp ctxt (loop_Seq p q) l =
      let (wp,l) = loop_to_word_comp ctxt p l in
      let (wq,l) = loop_to_word_comp ctxt q l in
        (wl_Seq wp wq,l)) /\
   (loop_to_word_comp ctxt (loop_If c n ri p q l1) l =
      let (wp,l) = loop_to_word_comp ctxt p l in
      let (wq,l) = loop_to_word_comp ctxt q l in
        (wl_Seq (wl_If c (loop_to_word_find_var ctxt n) (find_reg_imm ctxt ri) wp wq)
                wl_Tick,l)) /\
   (loop_to_word_comp ctxt (loop_Loop l1 body l2) l =
      let (wbody,l) = loop_to_word_comp ctxt body l in
        (wl_Seq wl_Tick
           (wl_Seq (wl_Loop (mk_new_cutset ctxt l1) wbody (mk_new_cutset ctxt l2))
                   wl_Tick),l)) /\
   (loop_to_word_comp ctxt (loop_Break n) l = (wl_Break n,l)) /\
   (loop_to_word_comp ctxt (loop_Continue n) l = (wl_Continue n,l)) /\
   (loop_to_word_comp ctxt (loop_Raise v) l =
      (wl_Raise (loop_to_word_find_var ctxt v),l)) /\
   (loop_to_word_comp ctxt (loop_Return vs) l =
      (wl_Return 0 (MAP (loop_to_word_find_var ctxt) vs),l)) /\
   (loop_to_word_comp ctxt loop_Tick l = (wl_Tick,l)) /\
   (loop_to_word_comp ctxt (Mark p) l = loop_to_word_comp ctxt p l) /\
   (loop_to_word_comp ctxt loop_Fail l = (wl_Skip,l)) /\
   (loop_to_word_comp ctxt (LocValue n m) l =
      (wl_LocValue (loop_to_word_find_var ctxt n) m,l)) /\
   (loop_to_word_comp ctxt (loop_Call ret dest args handler) l =
      let args = MAP (loop_to_word_find_var ctxt) args in
      match ret with
        NONE -> (wl_Call NONE dest (CONS 0 args) NONE,l)
      | SOME (vs,live) ->
          let vs = MAP (loop_to_word_find_var ctxt) vs in
          let live = mk_new_cutset ctxt live in
          let new_l = (FST l,SND l + 1) in
          match handler with
            NONE ->
              (wl_Call (SOME (vs,(live,LN),wl_Skip,l)) dest args NONE,new_l)
          | SOME (n,p1,p2,_) ->
              let (p1,l1) = loop_to_word_comp ctxt p1 new_l in
              let (p2,l1) = loop_to_word_comp ctxt p2 l1 in
              let new_l = (FST l1,SND l1 + 1) in
                (wl_Seq (wl_Call (SOME (vs,(live,LN),p2,l)) dest args
                           (SOME (loop_to_word_find_var ctxt n,p1,l1))) wl_Tick,
                 new_l)) /\
   (loop_to_word_comp ctxt (loop_FFI f ptr1 len1 ptr2 len2 live) l =
      let live = mk_new_cutset ctxt live in
        (wl_FFI f (loop_to_word_find_var ctxt ptr1) (loop_to_word_find_var ctxt len1)
                (loop_to_word_find_var ctxt ptr2) (loop_to_word_find_var ctxt len2)
                (live,LN),l)) /\
   (loop_to_word_comp ctxt (loop_ShMem memop n e) l =
      (ShareInst memop (loop_to_word_find_var ctxt n) (comp_exp ctxt e),l))`;;

let loop_to_word_comp_ind = cake_ind "loop_to_word_comp";;

let make_ctxt_def = cake_def
  `(make_ctxt n [] (l:num spt) = l) /\
   (make_ctxt n (CONS x xs) l = make_ctxt (n + 2) xs (insert x n l))`;;

(* acc_vars body LN: accumulates the assigned variable with the given       *)
(* num_set.  The main function below is make_ctxt; we take the difference  *)
(* so that we do not replicate the parameters (variable names) that we are *)
(* providing with the existing assigned variables present in the body of   *)
(* the program already.                                                     *)

(* HOL4: comp_func_def *)

let loop_to_word_comp_func_def = cake_def
  `loop_to_word_comp_func name params (body:(A)loop_prog) =
     let vs = fromNumSet (difference (acc_vars body LN) (toNumSet params)) in
     let ctxt = make_ctxt 2 (APPEND params vs) LN in
       FST (loop_to_word_comp ctxt body (name,2))`;;

(* HOL4: compile_prog_def *)

let loop_to_word_compile_prog_def = cake_def
  `loop_to_word_compile_prog (p:(num # num list # (A)loop_prog) list) =
     MAP (\(name,params,body).
            (name,LENGTH params + 1,loop_to_word_comp_func name params body)) p`;;

(* HOL4: compile_def *)

let loop_to_word_compile_def = cake_def
  `loop_to_word_compile (p:(num # num list # (A)loop_prog) list) =
     loop_to_word_compile_prog p`;;
