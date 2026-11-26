(* ========================================================================= *)
(* word_simp: port of HOL4 compiler/backend/word_simpScript.sml              *)
(* (CakeML v3479).                                                           *)
(* This compiler phase performs lightweight optimisations on wordLang        *)
(* programs. It is in particular designed to clean up some awkward patterns  *)
(* that can be produced by the data_to_word compiler.                        *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: the wordLang constructors wl_...,          *)
(*   word_simp_dest_Seq and word_simp_compile_exp (clashing constants), and  *)
(*   word_simp_Seq_assoc_def/_ind/_pmatch (Seq_assoc_def cannot be bound by  *)
(*   OCaml); the constant Seq_assoc keeps its name.                          *)
(* - HOL4's pmatch case expressions are written with match like all others, *)
(*   so the NAME_pmatch theorems restate the definitions in match form; the  *)
(*   NAME_def theorems that HOL4 derives from a NAME_pmatch_def by           *)
(*   PMATCH_ELIM_CONV (dest_Raise_num_def, is_simple_def) are the same       *)
(*   theorems here.                                                          *)
(* - The bool patterns T and F of HOL4 case expressions (push_out_if_aux)    *)
(*   are written as conditionals (HOL4's bool case is the conditional).     *)
(* - Words: n2w = word, w2n = val, && = word_and; FOLDR f e l = ITLIST f l e.*)
(* - Definitions with catch-all clauses are made with sem1aux_def (HOL4's    *)
(*   TFL completion); dest_Seq_ind (a case analysis) comes from wordLang's  *)
(*   IL2AUX_case_ind.                                                        *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "hol4/sptree.ml";;

type_invention_error := true;;

(* function that makes all Seq associate to the left *)

let SmartSeq_def = cake_def
  `SmartSeq p1 (p2:(A)wl_prog) = if p1 = wl_Skip then p2 else wl_Seq p1 p2`;;

let word_simp_Seq_assoc_def = sem1aux_def
  `(Seq_assoc p1 (wl_Skip:(A)wl_prog) = p1) /\
   (Seq_assoc p1 (wl_Seq q1 q2) = Seq_assoc (Seq_assoc p1 q1) q2) /\
   (Seq_assoc p1 (wl_If v n r q1 q2) =
      SmartSeq p1 (wl_If v n r (Seq_assoc wl_Skip q1) (Seq_assoc wl_Skip q2))) /\
   (Seq_assoc p1 (MustTerminate q) =
      SmartSeq p1 (MustTerminate (Seq_assoc wl_Skip q))) /\
   (Seq_assoc p1 (wl_Call ret_prog dest args handler) =
      SmartSeq p1
        (wl_Call (match ret_prog with
                    NONE -> NONE
                  | SOME (x1,x2,q1,x3,x4) -> SOME (x1,x2,Seq_assoc wl_Skip q1,x3,x4))
                 dest args
                 (match handler with
                    NONE -> NONE
                  | SOME (y1,q2,y2,y3) -> SOME (y1,Seq_assoc wl_Skip q2,y2,y3)))) /\
   (Seq_assoc p1 (wl_Loop names body exit_names) =
      SmartSeq p1 (wl_Loop names (Seq_assoc wl_Skip body) exit_names)) /\
   (Seq_assoc p1 other = SmartSeq p1 other)`;;

let word_simp_Seq_assoc_ind = cake_ind "Seq_assoc";;

let word_simp_Seq_assoc_pmatch = prove
 (CASE_TERM
  `!p1 (prog:(A)wl_prog).
     Seq_assoc p1 prog =
     match prog with
       wl_Skip -> p1
     | wl_Seq q1 q2 -> Seq_assoc (Seq_assoc p1 q1) q2
     | wl_If v n r q1 q2 ->
         SmartSeq p1 (wl_If v n r (Seq_assoc wl_Skip q1) (Seq_assoc wl_Skip q2))
     | MustTerminate q -> SmartSeq p1 (MustTerminate (Seq_assoc wl_Skip q))
     | wl_Call ret_prog dest args handler ->
         SmartSeq p1
           (wl_Call (match ret_prog with
                       NONE -> NONE
                     | SOME (x1,x2,q1,x3,x4) -> SOME (x1,x2,Seq_assoc wl_Skip q1,x3,x4))
                    dest args
                    (match handler with
                       NONE -> NONE
                     | SOME (y1,q2,y2,y3) -> SOME (y1,Seq_assoc wl_Skip q2,y2,y3)))
     | wl_Loop names body exit_names ->
         SmartSeq p1 (wl_Loop names (Seq_assoc wl_Skip body) exit_names)
     | other -> SmartSeq p1 other`,
  GEN_TAC THEN GEN_TAC THEN CASES_ON `prog:(A)wl_prog` THEN
  CAKE_REWRITE_TAC[word_simp_Seq_assoc_def]);;

(* optimise certain consecutive If statements that arise from data-to-word *)
(*   If something (q1 ; n := X) (q2 ; n := Y) ;                             *)
(*   If (n == Z) p1 p2                                                       *)
(* --> (in case X <> Y and Z == X)                                           *)
(*   If something (q1 ; n := X ; p1) (q2 ; n := Y ; p2) ;                    *)
(* similarly if Z == Y and X <> Y                                            *)

(* HOL4: dest_Seq *)

let word_simp_dest_Seq_def = sem1aux_def
  `(word_simp_dest_Seq (wl_Seq p1 p2) = (p1,p2:(A)wl_prog)) /\
   (word_simp_dest_Seq p = (wl_Skip,p))`;;

let word_simp_dest_Seq_ind = IL2AUX_case_ind word_simp_dest_Seq_def;;

let word_simp_dest_Seq_pmatch = prove
 (CASE_TERM
  `!p. word_simp_dest_Seq p =
       match p with wl_Seq p1 p2 -> (p1,p2:(A)wl_prog) | p -> (wl_Skip,p)`,
  GEN_TAC THEN CASES_ON `p:(A)wl_prog` THEN
  CAKE_REWRITE_TAC[word_simp_dest_Seq_def]);;

let dest_If_def = sem1aux_def
  `(dest_If (wl_If x1 x2 x3 p1 p2) = SOME (x1,x2,x3,p1,p2:(A)wl_prog)) /\
   (dest_If (_:(A)wl_prog) = NONE)`;;

let dest_If_pmatch = prove
 (CASE_TERM
  `!p. dest_If p =
       match p with
         wl_If x1 x2 x3 p1 p2 -> SOME (x1,x2,x3,p1,p2:(A)wl_prog)
       | _ -> NONE`,
  GEN_TAC THEN CASES_ON `p:(A)wl_prog` THEN CAKE_REWRITE_TAC[dest_If_def]);;

let dest_If_Eq_Imm_def = cake_def
  `dest_If_Eq_Imm (p:(A)wl_prog) =
     match dest_If p with
       SOME (asm_Equal,n,Imm w,p1,p2) -> SOME (n,w,p1,p2)
     | _ -> NONE`;;

let dest_If_Eq_Imm_pmatch = prove
 (CASE_TERM
  `!p. dest_If_Eq_Imm (p:(A)wl_prog) =
       match dest_If p with
         SOME (asm_Equal,n,Imm w,p1,p2) -> SOME (n,w,p1,p2)
       | _ -> NONE`,
  REWRITE_TAC[dest_If_Eq_Imm_def]);;

let dest_Seq_Assign_Const_def = cake_def
  `dest_Seq_Assign_Const n (p:(A)wl_prog) =
     let (p1,p2) = word_simp_dest_Seq p in
     match p2 with
       wl_Assign m (wl_Const w) -> if m = n then SOME (p1,w) else NONE
     | _ -> NONE`;;

let dest_Seq_Assign_Const_pmatch = prove
 (CASE_TERM
  `!n p. dest_Seq_Assign_Const n (p:(A)wl_prog) =
     let (p1,p2) = word_simp_dest_Seq p in
     match p2 with
       wl_Assign m (wl_Const w) -> if m = n then SOME (p1,w) else NONE
     | _ -> NONE`,
  REWRITE_TAC[dest_Seq_Assign_Const_def]);;

(* Constant folding and propagation optimization, e.g.                      *)
(*   x := 1; y := x + 4; z := y;   becomes   x := 1; y := 5; z := 5;         *)
(* Limitation: the current implementation forgets all constant values after *)
(* a function call with a handler (for easier implementation and proofs).   *)

let strip_const_def = sem1aux_def
  `(strip_const [] = SOME ([]:(A word) list)) /\
   (strip_const (CONS (wl_Const w) cs) =
      match strip_const cs with
        SOME ws -> SOME (CONS w ws)
      | _ -> NONE) /\
   (strip_const (_:((A)wl_exp)list) = NONE)`;;

let const_fp_exp_def = sem1aux_def
  `(const_fp_exp (wl_Var v) (cs:(A word)spt) =
      match lookup v cs with
        SOME x -> wl_Const x
      | NONE -> wl_Var v) /\
   (const_fp_exp (wl_Op op args) cs =
      let const_fp_args = MAP (\a. const_fp_exp a cs) args in
      match strip_const const_fp_args with
        SOME ws -> (match word_op op ws with
                      SOME w -> wl_Const w
                    | _ -> wl_Op op (MAP wl_Const ws))
      | _ -> wl_Op op const_fp_args) /\
   (const_fp_exp (wl_Shift sh e e1) cs =
      let const_fp_exp_e = const_fp_exp e cs in
      let const_fp_exp_e1 = const_fp_exp e1 cs in
      match (const_fp_exp_e, const_fp_exp_e1) with
        (wl_Const c, wl_Const c1) ->
          (match word_sh sh c (val c1) with
             SOME w -> wl_Const w
           | _ -> wl_Shift sh (wl_Const c) (wl_Const c1))
      | _ -> wl_Shift sh const_fp_exp_e const_fp_exp_e1) /\
   (const_fp_exp e _ = e)`;;

let const_fp_exp_ind = cake_ind "const_fp_exp";;

let const_fp_move_cs_def = cake_def
  `(const_fp_move_cs [] (_:A spt) (cs:A spt) = cs) /\
   (const_fp_move_cs (CONS (m:num#num) ms) ocs ncs =
      let v = FST m in
      let nncs = (match lookup (SND m) ocs with
                    SOME c -> insert v c ncs
                  | _ -> delete v ncs) in
      const_fp_move_cs ms ocs nncs)`;;

let const_fp_inst_cs_def = sem1aux_def
  `(const_fp_inst_cs (asm_Const r _) (cs:B spt) = delete r cs) /\
   (const_fp_inst_cs (asm_Arith (Binop _ r _ _)) cs = delete r cs) /\
   (const_fp_inst_cs (asm_Arith (asm_Shift _ r _ _)) cs = delete r cs) /\
   (const_fp_inst_cs (asm_Arith (asm_AddCarry r1 _ _ r2)) cs =
      delete r2 (delete r1 cs)) /\
   (const_fp_inst_cs (asm_Arith (AddOverflow r1 _ _ r2)) cs =
      delete r2 (delete r1 cs)) /\
   (const_fp_inst_cs (asm_Arith (SubOverflow r1 _ _ r2)) cs =
      delete r2 (delete r1 cs)) /\
   (const_fp_inst_cs (asm_Arith (LongMul r1 r2 _ _)) cs =
      delete r1 (delete r2 cs)) /\
   (const_fp_inst_cs (asm_Arith (LongDiv r1 r2 _ _ _)) cs =
      delete r1 (delete r2 cs)) /\
   (const_fp_inst_cs (asm_Arith (asm_Div r1 _ _)) cs = delete r1 cs) /\
   (const_fp_inst_cs (Mem asm_Load r _) cs = delete r cs) /\
   (const_fp_inst_cs (Mem asm_Load32 r _) cs = delete r cs) /\
   (const_fp_inst_cs (Mem Load8 r _) cs = delete r cs) /\
   (const_fp_inst_cs (FP (FPLess r f1 f2)) cs = delete r cs) /\
   (const_fp_inst_cs (FP (FPLessEqual r f1 f2)) cs = delete r cs) /\
   (const_fp_inst_cs (FP (FPEqual r f1 f2)) cs = delete r cs) /\
   (const_fp_inst_cs (FP (FPMovToReg r1 r2 d):(A)inst) cs =
      if dimindex(:A) = 64 then delete r1 cs
      else delete r2 (delete r1 cs)) /\
   (const_fp_inst_cs _ cs = cs)`;;

let get_var_imm_cs_def = cake_def
  `(get_var_imm_cs (Reg r) (cs:(A word)spt) = lookup r cs) /\
   (get_var_imm_cs (Imm i) (_:(A word)spt) = SOME (i:A word))`;;

let is_gc_const_def = cake_def
  `is_gc_const (c:A word) <=> word_and c (word 1) = word 0`;;

let all_names_def = cake_def
  `all_names (n,m) = sptree_union n (m:A spt)`;;

let _ = cake_add_simps [all_names_def];;

(* HOL4: Overload delete_all[local] = \n l. FOLDR delete l n  (written out  *)
(* where used: ITLIST delete n l)                                           *)

(* We only drop constants that can potentially be in registers *)

let drop_consts_def = cake_def
  `(drop_consts (cs:(A word)spt) [] = wl_Skip:(A)wl_prog) /\
   (drop_consts cs (CONS n ns) =
      match lookup n cs with
        NONE -> drop_consts cs ns
      | SOME w -> SmartSeq (drop_consts cs ns) (wl_Assign n (wl_Const w)))`;;

(* the clauses are parsed apart: names is a cutsets in some clauses and a  *)
(* num_set in others, n a num list in one and a num in another            *)

let const_fp_loop_def = sem1aux_def (list_mk_conj
 [`const_fp_loop (wl_Move pri moves:(A)wl_prog) (cs:(A word)spt) =
     (wl_Move pri moves:(A)wl_prog, const_fp_move_cs moves cs cs)`;
  `const_fp_loop (wl_Inst i:(A)wl_prog) (cs:(A word)spt) =
     (wl_Inst i:(A)wl_prog, const_fp_inst_cs i cs)`;
  `const_fp_loop (wl_Assign v e:(A)wl_prog) (cs:(A word)spt) =
     let const_fp_e = const_fp_exp e cs in
     match const_fp_e with
       wl_Const c -> (wl_Assign v const_fp_e:(A)wl_prog, insert v c cs)
     | _ -> (wl_Assign v const_fp_e, delete v cs)`;
  `const_fp_loop (wl_Get v name:(A)wl_prog) (cs:(A word)spt) =
     (wl_Get v name:(A)wl_prog, delete v cs)`;
  `const_fp_loop (wl_OpCurrHeap b v w:(A)wl_prog) (cs:(A word)spt) =
     (wl_OpCurrHeap b v w:(A)wl_prog, delete v cs)`;
  `const_fp_loop (MustTerminate p:(A)wl_prog) (cs:(A word)spt) =
     let (p', cs') = const_fp_loop p cs in
     (MustTerminate p':(A)wl_prog, cs':(A word)spt)`;
  `const_fp_loop (wl_Seq p1 p2:(A)wl_prog) (cs:(A word)spt) =
     let (p1', cs') = const_fp_loop p1 cs in
     let (p2', cs'') = const_fp_loop p2 cs' in
     (wl_Seq p1' p2':(A)wl_prog, cs'':(A word)spt)`;
  `const_fp_loop (wl_If cmp lhs rhs p1 p2:(A)wl_prog) (cs:(A word)spt) =
     match (lookup lhs cs, get_var_imm_cs rhs cs) with
       (SOME clhs, SOME crhs) ->
         (if asm_word_cmp cmp clhs crhs then const_fp_loop p1 cs
          else const_fp_loop p2 cs)
     | _ -> (let (p1', p1cs) = const_fp_loop p1 cs in
             let (p2', p2cs) = const_fp_loop p2 cs in
             (wl_If cmp lhs rhs p1' p2':(A)wl_prog, inter_eq p1cs p2cs:(A word)spt))`;
  `const_fp_loop (wl_Call ret dest args handler:(A)wl_prog) (cs:(A word)spt) =
     match ret with
       NONE -> (SmartSeq (drop_consts cs args) (wl_Call ret dest args handler),
                filter_v is_gc_const cs)
     | SOME (n, names, ret_handler, l1, l2) ->
         (if handler = NONE then
            (let cs' = ITLIST delete n
                         (filter_v is_gc_const (sptree_inter cs (all_names names))) in
             let (ret_handler', cs'') = const_fp_loop ret_handler cs' in
             (SmartSeq (drop_consts cs args)
                (wl_Call (SOME (n, names, ret_handler', l1, l2)) dest args handler),
              cs'':(A word)spt))
          else
            (SmartSeq (drop_consts cs args) (wl_Call ret dest args handler), LN))`;
  `const_fp_loop (wl_FFI x0 x1 x2 x3 x4 names:(A)wl_prog) (cs:(A word)spt) =
     (SmartSeq (drop_consts cs [x1;x2;x3;x4]) (wl_FFI x0 x1 x2 x3 x4 names),
      sptree_inter cs (all_names names))`;
  `const_fp_loop (wl_LocValue v x3:(A)wl_prog) (cs:(A word)spt) =
     (wl_LocValue v x3:(A)wl_prog, delete v cs)`;
  `const_fp_loop (wl_Alloc n names:(A)wl_prog) (cs:(A word)spt) =
     (SmartSeq (drop_consts cs [n]) (wl_Alloc n names),
      filter_v is_gc_const (sptree_inter cs (all_names names)))`;
  `const_fp_loop (wl_StoreConsts a b c d ws:(A)wl_prog) (cs:(A word)spt) =
     (wl_StoreConsts a b c d ws:(A)wl_prog,
      delete a (delete b (delete c (delete d cs))))`;
  `const_fp_loop (wl_Install r1 r2 r3 r4 names:(A)wl_prog) (cs:(A word)spt) =
     (SmartSeq (drop_consts cs [r1;r2;r3;r4]) (wl_Install r1 r2 r3 r4 names),
      delete r1 (filter_v is_gc_const (sptree_inter cs (all_names names))))`;
  `const_fp_loop (wl_Store e v:(A)wl_prog) (cs:(A word)spt) =
     (wl_Store (const_fp_exp e cs) v:(A)wl_prog, cs)`;
  `const_fp_loop (ShareInst asm_Load v e:(A)wl_prog) (cs:(A word)spt) =
     (ShareInst asm_Load v (const_fp_exp e cs):(A)wl_prog, delete v cs)`;
  `const_fp_loop (ShareInst Load8 v e:(A)wl_prog) (cs:(A word)spt) =
     (ShareInst Load8 v (const_fp_exp e cs):(A)wl_prog, delete v cs)`;
  `const_fp_loop (ShareInst Load16 v e:(A)wl_prog) (cs:(A word)spt) =
     (ShareInst Load16 v (const_fp_exp e cs):(A)wl_prog, delete v cs)`;
  `const_fp_loop (ShareInst asm_Load32 v e:(A)wl_prog) (cs:(A word)spt) =
     (ShareInst asm_Load32 v (const_fp_exp e cs):(A)wl_prog, delete v cs)`;
  `const_fp_loop (ShareInst asm_Store v e:(A)wl_prog) (cs:(A word)spt) =
     (ShareInst asm_Store v (const_fp_exp e cs):(A)wl_prog, cs)`;
  `const_fp_loop (ShareInst Store8 v e:(A)wl_prog) (cs:(A word)spt) =
     (ShareInst Store8 v (const_fp_exp e cs):(A)wl_prog, cs)`;
  `const_fp_loop (ShareInst Store16 v e:(A)wl_prog) (cs:(A word)spt) =
     (ShareInst Store16 v (const_fp_exp e cs):(A)wl_prog, cs)`;
  `const_fp_loop (ShareInst asm_Store32 v e:(A)wl_prog) (cs:(A word)spt) =
     (ShareInst asm_Store32 v (const_fp_exp e cs):(A)wl_prog, cs)`;
  `const_fp_loop (wl_Loop names body exit_names:(A)wl_prog) (cs:(A word)spt) =
     (wl_Loop names (FST (const_fp_loop body LN)) exit_names:(A)wl_prog,
      LN:(A word)spt)`;
  `const_fp_loop (p:(A)wl_prog) (cs:(A word)spt) = (p, cs)`]);;

let const_fp_loop_ind = cake_ind "const_fp_loop";;

let const_fp_def = cake_def
  `const_fp (p:(A)wl_prog) = FST (const_fp_loop p LN)`;;

(* Optimise near-consecutive If/If pairs into a single If when there are   *)
(* only two possible control-flow paths:                                     *)
(*   (if C then X else Y) ; Zs ; (if C2 then X2 else Y2)                     *)
(* where the number of intermediate Zs is small, (X ; Zs) guarantees either  *)
(* C2 or not C2, and (Y ; Zs) guarantees the opposite.  The second If is     *)
(* removed at the cost of duplicating the Zs: (1) recognise the case, (2)    *)
(* expand the first If to cover everything, hoisting copies of the second If *)
(* into both branches, (3) re-run const_fp to simplify each branch.          *)

let rewrite_duplicate_if_max_reassoc_def = cake_def
  `rewrite_duplicate_if_max_reassoc = 8`;;

(* HOL4 defines dest_Raise_num and is_simple with pmatch (NAME_pmatch_def)  *)
(* and derives NAME_def by PMATCH_ELIM_CONV; here both are match, compiled  *)
(* into the same case constant, so NAME_def is the same theorem            *)

let dest_Raise_num_pmatch_def = cake_def
  `dest_Raise_num (p:(A)wl_prog) = match p with wl_Raise n -> n | _ -> 0`;;

let dest_Raise_num_def = dest_Raise_num_pmatch_def;;

let is_simple_pmatch_def = cake_def
  `is_simple (p:(A)wl_prog) <=>
     match p with
       wl_Tick -> T
     | wl_Skip -> T
     | wl_Move _ _ -> T
     | wl_Assign _ _ -> T
     | _ -> F`;;

let is_simple_def = is_simple_pmatch_def;;

let try_if_hoist2_def = cake_def
  `try_if_hoist2 N p1 interm dummy (p2:(A)wl_prog) =
     if N = 0 then NONE
     else match p1 with
       wl_If cmp lhs rhs br1 br2 ->
         let res1 = dest_Raise_num (SND (word_simp_dest_Seq
                      (const_fp (wl_Seq (wl_Seq br1 interm) dummy)))) in
         if res1 = 0 then NONE
         else
         let res2 = dest_Raise_num (SND (word_simp_dest_Seq
                      (const_fp (wl_Seq (wl_Seq br2 interm) dummy)))) in
         if ~(res1 + res2 = 3) then NONE
         else SOME (const_fp (wl_If cmp lhs rhs (wl_Seq (wl_Seq br1 interm) p2)
                                (wl_Seq (wl_Seq br2 interm) p2)))
     | wl_Seq p3 p4 ->
         (match dest_If p4 with
            SOME (cmp, lhs, rhs, br1, br2) ->
              let res1 = dest_Raise_num (SND (word_simp_dest_Seq
                           (const_fp (wl_Seq (wl_Seq br1 interm) dummy)))) in
              if res1 = 0 then NONE
              else
              let res2 = dest_Raise_num (SND (word_simp_dest_Seq
                           (const_fp (wl_Seq (wl_Seq br2 interm) dummy)))) in
              if ~(res1 + res2 = 3) then NONE
              else SOME (wl_Seq p3 (const_fp (wl_If cmp lhs rhs
                                   (wl_Seq (wl_Seq br1 interm) p2)
                                   (wl_Seq (wl_Seq br2 interm) p2))))
          | NONE ->
              if is_simple p4
              then try_if_hoist2 (N - 1) p3 (wl_Seq p4 interm) dummy p2
              else NONE)
     | _ -> NONE`;;

let try_if_hoist2_ind = cake_ind "try_if_hoist2";;

let try_if_hoist1_def = cake_def
  `try_if_hoist1 p1 (p2:(A)wl_prog) =
     match dest_If p2 with
       NONE -> NONE
     | SOME (cmp, lhs, rhs, _, _) ->
         let dummy = wl_If cmp lhs rhs (wl_Raise 1) (wl_Raise 2) in
         try_if_hoist2 rewrite_duplicate_if_max_reassoc p1 wl_Skip dummy p2`;;

let simp_duplicate_if_def = cake_def
  `simp_duplicate_if (p:(A)wl_prog) =
     match p with
       MustTerminate q -> MustTerminate (simp_duplicate_if q)
     | wl_Call ret_prog dest args handler ->
         wl_Call (match ret_prog with
                    NONE -> NONE
                  | SOME (x1,x2,q1,x3,x4) -> SOME (x1,x2,simp_duplicate_if q1,x3,x4))
                 dest args
                 (match handler with
                    NONE -> NONE
                  | SOME (y1,q2,y2,y3) -> SOME (y1,simp_duplicate_if q2,y2,y3))
     | wl_If cmp lhs rhs br1 br2 ->
         wl_If cmp lhs rhs (simp_duplicate_if br1) (simp_duplicate_if br2)
     | wl_Seq p1 p2 ->
         (let p1x = simp_duplicate_if p1 in
          let p2x = simp_duplicate_if p2 in
          match try_if_hoist1 p1x p2x with
            NONE -> wl_Seq p1x p2x
          | SOME p3 -> Seq_assoc wl_Skip p3)
     | wl_Loop names body exit_names ->
         wl_Loop names (simp_duplicate_if body) exit_names
     | _ -> p`;;

let simp_duplicate_if_ind = cake_ind "simp_duplicate_if";;

(* Optimize pairs where one side is known to terminate due to a Raise or a  *)
(* Return; the flag is T when it is known to halt and F otherwise          *)

let push_out_if_aux_def = cake_def
  `push_out_if_aux (p:(A)wl_prog) =
     match p with
       MustTerminate q ->
         (match push_out_if_aux q with (c,b) -> (MustTerminate c,b))
     | wl_Return _ _ -> (p,T)
     | wl_Raise _ -> (p,T)
     | wl_Call NONE _ _ _ -> (p,T)
     | wl_If cmp r1 ri c1 c2 ->
         (match (push_out_if_aux c1,push_out_if_aux c2) with
            ((c1',b1),(c2',b2)) ->
              if b1 then
                if b2 then (wl_If cmp r1 ri c1' c2', T)
                else (wl_Seq (wl_If cmp r1 ri c1' wl_Skip) c2', F)
              else if b2 then (wl_Seq (wl_If cmp r1 ri wl_Skip c2') c1', F)
              else (wl_If cmp r1 ri c1' c2', F))
     | wl_Seq c1 c2 ->
         (match push_out_if_aux c1 with
            (c1',b1) ->
              if b1 then (wl_Seq c1' c2, T)
              else (match push_out_if_aux c2 with (c2',b) -> (wl_Seq c1' c2', b)))
     | wl_Loop names body exit_names ->
         (wl_Loop names (FST (push_out_if_aux body)) exit_names, F)
     | _ -> (p,F)`;;

let push_out_if_aux_ind = cake_ind "push_out_if_aux";;

let push_out_if_def = cake_def
  `push_out_if (p:(A)wl_prog) = FST (push_out_if_aux p)`;;

(* HOL4: compile_exp *)

let word_simp_compile_exp_def = cake_def
  `word_simp_compile_exp (e:(A)wl_prog) =
     let e = Seq_assoc wl_Skip e in
     let e = const_fp e in
     let e = simp_duplicate_if e in
     let e = push_out_if e in
     e`;;
