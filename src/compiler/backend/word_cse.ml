(* ========================================================================= *)
(* word_cse: port of HOL4 compiler/backend/word_cseScript.sml (CakeML        *)
(* v3479).                                                                   *)
(* Defines a common sub-expression elimination pass on a wordLang program.  *)
(* This pass is to run immediately after the SSA-like renaming.             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/balanced_map.ml";;
needs "hol4/sptree.ml";;
needs "compiler/backend/wordLang.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - HOL4 Less, Equal, Greater (ordering) are LESS, EQUAL, GREATER;         *)
(*   balanced_map$lookup, insert, empty are balanced_map_lookup,             *)
(*   balanced_map_insert, balanced_map_empty; num_map is num spt; the       *)
(*   alist (store_name, num) alist is (store_name#num) list.                 *)
(* - wordLang constructors carry the prefix wl_ (wl_Inst, wl_Move, ...),     *)
(*   asm constructors asm_ where names.tsv says so (asm_Skip, asm_Const,     *)
(*   asm_Arith, asm_Shift, asm_Div, asm_AddCarry, asm_Load, asm_Store, ...). *)
(* - r with <| f1 := x; f2 := y |> is f1_fupd (K x) (f2_fupd (K y) r).      *)
(* - w2n is val; ++ is APPEND; EVERY is ALL.                                  *)

(* DATA

  The to_canonical field maps register name r to a canonical name c
  such that registers r and c hold the same value.

  The to_latest field maps canonical name to latest register name
  that has that value. The latest name should always be emitted to
  generate code with as short live ranges as possible (helps register
  allocation).

  The gets_mem field maps store names to canonical registers.

  The instrs_mem field maps instructions to canonical register holding
  the value of that this instruction produces. Note that instructions
  are stored with canonical names only.

  The loads_mem field maps load instructions (keyed by width, canonical
  address register and offset) to the canonical register holding the
  value last loaded from that address. It is kept separate from
  instrs_mem because memory writes must invalidate exactly the load
  facts: a store clears loads_mem and leaves all register-only facts
  intact.

  Conventions:

   - The domain of to_canonical include all names that are mentioned
     anywhere in the data state.

   - The data must be reset to empty, in case we encounter an
     assignment to a name that is in the main of to_canonical, because
     such assignments can make the optimisers state out-of-date.

   - All names in the domain and range of to_canonical must be ODD, so
     that pre-register-allocated registers are not touched.

   - Every register mentioned by a stored fact (including registers an
     instruction only reads) must be in the domain of to_canonical, so
     that a later write to it resets the data. Reads are entered as
     self-mappings (registered) when a fact is stored.
*)

let knowledge_INFO = cake_record "knowledge"
  ["to_canonical","num spt";
   "to_latest","num spt";
   "gets_mem","(store_name#num) list";
   "instrs_mem","(num list,num)balanced_map";
   "loads_mem","(num list,num)balanced_map"];;

let knowledge_component_equality = knowledge_INFO.ri_component_equality;;

(* LIST COMPARISON *)

let listCmp_def = cake_def
  `(listCmp (CONS (hd1:num) tl1) (CONS (hd2:num) tl2) =
      if hd1 = hd2 then listCmp tl1 tl2
      else if hd1 > hd2 then GREATER else LESS) /\
   (listCmp [] [] = EQUAL) /\
   (listCmp (CONS hd1 tl1) [] = GREATER) /\
   (listCmp [] (CONS hd2 tl2) = LESS)`;;

let listCmp_ind = cake_ind "listCmp";;

let empty_data_def = cake_def
  `empty_data =
     knowledge_REC LN LN [] balanced_map_empty balanced_map_empty`;;

(* Whether we are allowed to keep the data after writing to this register *)

let keep_data_def = cake_def
  `keep_data (canon:A spt) (write_to_reg:num) <=>
     IS_NONE (lookup write_to_reg canon)`;;

let invalidate_data_def = cake_def
  `invalidate_data (data:knowledge) (write_to_reg:num) =
     if keep_data (knowledge_to_canonical data) write_to_reg
     then data
     else empty_data`;;

(* Invalidate after writing each register in a list (e.g. multi-output     *)
(* instructions); empties the data if any of them is tracked.              *)

let invalidate_regs_def = cake_def
  `(invalidate_regs (data:knowledge) [] = data) /\
   (invalidate_regs data (CONS (r:num) rs) =
      invalidate_regs (invalidate_data data r) rs)`;;

let invalidate_regs_ind = cake_ind "invalidate_regs";;

(* Enter an odd register that a stored fact reads into the tracked set as  *)
(* a self-mapping, so that a later write to it resets the data. Registers  *)
(* already tracked, and pre-allocated (EVEN) registers, are left alone.    *)

let register_read_def = cake_def
  `register_read (data:knowledge) (r:num) =
     if ~EVEN r /\ keep_data (knowledge_to_canonical data) r
     then knowledge_to_canonical_fupd
            (K (insert r r (knowledge_to_canonical data))) data
     else data`;;

let register_reads_def = cake_def
  `(register_reads (data:knowledge) [] = data) /\
   (register_reads data (CONS (r:num) rs) =
      register_reads (register_read data r) rs)`;;

let register_reads_ind = cake_ind "register_reads";;

(* REGISTER TRANSFORMATIONS *)

let canonicalRegs_def = cake_def
  `canonicalRegs (data:knowledge) (r:num) =
     lookup_any r (knowledge_to_canonical data) r`;;

let canonicalRegs'_def = cake_def
  `canonicalRegs' (avoid:num) (data:knowledge) (r:num) =
     let n = canonicalRegs data r in
     if n = avoid then r else n`;;

let canonicalImmReg_def = cake_def
  `(canonicalImmReg (data:knowledge) (Reg r:(A)reg_imm) =
      Reg (canonicalRegs data r)) /\
   (canonicalImmReg data (Imm w) = Imm w)`;;

let canonicalImmReg'_def = cake_def
  `(canonicalImmReg' (avoid:num) (data:knowledge) (Reg r:(A)reg_imm) =
      Reg (canonicalRegs' avoid data r)) /\
   (canonicalImmReg' avoid data (Imm w) = Imm w)`;;

let canonicalMultRegs_def = cake_def
  `canonicalMultRegs (data:knowledge) (regs:num list) =
     MAP (canonicalRegs data) regs`;;

let map_insert_def = cake_def
  `(map_insert [] (m:A spt) = m) /\
   (map_insert (CONS ((x:num),(y:A)) xs) m = insert x y (map_insert xs m))`;;

let map_insert_ind = cake_ind "map_insert";;

(* Register the sources first: a register that is both a source and a     *)
(* destination is then tracked and fails the keep_data check below, so no *)
(* equivalence is recorded across a self-interfering parallel move.       *)

let canonicalMoveRegs_def = cake_def
  `canonicalMoveRegs (data:knowledge) (moves:(num#num) list) =
     let data = register_reads data (MAP SND moves) in
     if ALL (keep_data (knowledge_to_canonical data)) (MAP FST moves)
     then
       let xs = FILTER (\(a,b). ~EVEN a /\ ~EVEN b) moves in
       let ys = MAP (\(a,b). (a,canonicalRegs data b)) xs in
       let to_c = map_insert ys (knowledge_to_canonical data) in
       let zs = MAP (\(a,b). (b,a)) ys in
       let to_l = map_insert zs (knowledge_to_latest data) in
       knowledge_to_canonical_fupd (K to_c)
         (knowledge_to_latest_fupd (K to_l) data)
     else empty_data`;;

(* the clauses are parsed apart: r3 is a reg_imm in one and a num in others *)

let canonicalArith_def = cake_def_clauses
 [`canonicalArith (data:knowledge) (Binop op r1 r2 r3:(A)asm_arith) =
     Binop op r1 (canonicalRegs' r1 data r2) (canonicalImmReg' r1 data r3)`;
  `canonicalArith (data:knowledge) (asm_Shift s r1 r2 ri:(A)asm_arith) =
     asm_Shift s r1 (canonicalRegs' r1 data r2) (canonicalImmReg' r1 data ri)`;
  `canonicalArith (data:knowledge) (asm_Div r1 r2 r3:(A)asm_arith) =
     asm_Div r1 (canonicalRegs data r2) (canonicalRegs data r3):(A)asm_arith`;
  `canonicalArith (data:knowledge) (LongMul r1 r2 r3 r4:(A)asm_arith) =
     LongMul r1 r2 (canonicalRegs data r3) (canonicalRegs data r4):(A)asm_arith`;
  `canonicalArith (data:knowledge) (LongDiv r1 r2 r3 r4 r5:(A)asm_arith) =
     LongDiv r1 r2 (canonicalRegs data r3) (canonicalRegs data r4)
             (canonicalRegs data r5):(A)asm_arith`;
  `canonicalArith (data:knowledge) (asm_AddCarry r1 r2 r3 r4:(A)asm_arith) =
     asm_AddCarry r1 (canonicalRegs' r1 data r2) (canonicalRegs' r1 data r3) r4:(A)asm_arith`;
  `canonicalArith (data:knowledge) (AddOverflow r1 r2 r3 r4:(A)asm_arith) =
     AddOverflow r1 (canonicalRegs' r1 data r2) (canonicalRegs' r1 data r3) r4:(A)asm_arith`;
  `canonicalArith (data:knowledge) (SubOverflow r1 r2 r3 r4:(A)asm_arith) =
     SubOverflow r1 (canonicalRegs' r1 data r2) (canonicalRegs' r1 data r3) r4:(A)asm_arith`];;

let canonicalFp_def = cake_def
  `(canonicalFp (data:knowledge) (FPLess r1 r2 r3) =
      FPLess r1 (canonicalRegs data r2) (canonicalRegs data r3)) /\
   (canonicalFp data (FPLessEqual r1 r2 r3) =
      FPLessEqual r1 (canonicalRegs data r2) (canonicalRegs data r3)) /\
   (canonicalFp data (FPEqual r1 r2 r3) =
      FPEqual r1 (canonicalRegs data r2) (canonicalRegs data r3)) /\
   (canonicalFp data (FPAbs r1 r2) = FPAbs r1 (canonicalRegs data r2)) /\
   (canonicalFp data (FPNeg r1 r2) = FPNeg r1 (canonicalRegs data r2)) /\
   (canonicalFp data (FPSqrt r1 r2) = FPSqrt r1 (canonicalRegs data r2)) /\
   (canonicalFp data (FPAdd r1 r2 r3) =
      FPAdd r1 (canonicalRegs data r2) (canonicalRegs data r3)) /\
   (canonicalFp data (FPSub r1 r2 r3) =
      FPSub r1 (canonicalRegs data r2) (canonicalRegs data r3)) /\
   (canonicalFp data (FPMul r1 r2 r3) =
      FPMul r1 (canonicalRegs data r2) (canonicalRegs data r3)) /\
   (canonicalFp data (FPDiv r1 r2 r3) =
      FPDiv r1 (canonicalRegs data r2) (canonicalRegs data r3)) /\
   (canonicalFp data (FPFma r1 r2 r3) =
      FPFma r1 (canonicalRegs data r2) (canonicalRegs data r3)) /\
   (canonicalFp data (FPMov r1 r2) = FPMov r1 (canonicalRegs data r2)) /\
   (canonicalFp data (FPMovToReg r1 r2 r3) =
      FPMovToReg r1 (canonicalRegs data r2) (canonicalRegs data r3)) /\
   (canonicalFp data (FPMovFromReg r1 r2 r3) =
      FPMovFromReg r1 (canonicalRegs data r2) (canonicalRegs data r3)) /\
   (canonicalFp data (FPToInt r1 r2) = FPToInt r1 (canonicalRegs data r2)) /\
   (canonicalFp data (FPFromInt r1 r2) =
      FPFromInt r1 (canonicalRegs data r2))`;;

(* SEEN INSTRUCTIONS MEMORY *)

let wordToNum_def = cake_def
  `wordToNum (w:A word) = val w`;;

let shiftToNum_def = cake_def
  `(shiftToNum Lsl = 40) /\
   (shiftToNum Lsr = 41) /\
   (shiftToNum Asr = 42) /\
   (shiftToNum Ror = 43)`;;

let arithOpToNum_def = cake_def
  `(arithOpToNum asm_Add = 35) /\
   (arithOpToNum asm_Sub = 36) /\
   (arithOpToNum asm_And = 37) /\
   (arithOpToNum asm_Or = 38) /\
   (arithOpToNum asm_Xor = 39)`;;

let regImmToNumList_def = cake_def
  `(regImmToNumList (Reg r:(A)reg_imm) = [33; r + 100]) /\
   (regImmToNumList (Imm w) = [34; wordToNum w])`;;

let arithToNumList_def = cake_def
  `(arithToNumList (Binop op r1 r2 ri:(A)asm_arith) =
      APPEND [25; arithOpToNum op; r2 + 100] (regImmToNumList ri)) /\
   (arithToNumList (LongMul r1 r2 r3 r4) = [26; r3 + 100; r4 + 100]) /\
   (arithToNumList (LongDiv r1 r2 r3 r4 r5) =
      [27; r3 + 100; r4 + 100; r5 + 100]) /\
   (arithToNumList (asm_Shift s r1 r2 ri) =
      APPEND [28; shiftToNum s; r2 + 100] (regImmToNumList ri)) /\
   (arithToNumList (asm_Div r1 r2 r3) = [29; r2 + 100; r3 + 100]) /\
   (arithToNumList (asm_AddCarry r1 r2 r3 r4) = [30; r2 + 100; r3 + 100]) /\
   (arithToNumList (AddOverflow r1 r2 r3 r4) = [31; r2 + 100; r3 + 100]) /\
   (arithToNumList (SubOverflow r1 r2 r3 r4) = [32; r2 + 100; r3 + 100])`;;

let memOpToNum_def = cake_def
  `(memOpToNum asm_Load = 21) /\
   (memOpToNum Load8 = 22) /\
   (memOpToNum Load16 = 46) /\
   (memOpToNum asm_Load32 = 44) /\
   (memOpToNum asm_Store = 23) /\
   (memOpToNum Store8 = 47) /\
   (memOpToNum Store16 = 24) /\
   (memOpToNum asm_Store32 = 45)`;;

(* Key for a load fact (kept in the separate loads_mem map): the memop head *)
(* distinguishes the load widths; the address register is stored           *)
(* canonically.                                                             *)

let loadToNumList_def = cake_def
  `loadToNumList op (a:num) (ofs:A word) =
     [memOpToNum op; a + 100; wordToNum ofs]`;;

let fpToNumList_def = cake_def
  `(fpToNumList (FPLess r1 r2 r3) = [5; r2 + 100; r3 + 100]) /\
   (fpToNumList (FPLessEqual r1 r2 r3) = [6; r2 + 100; r3 + 100]) /\
   (fpToNumList (FPEqual r1 r2 r3) = [7; r2 + 100; r3 + 100]) /\
   (fpToNumList (FPAbs r1 r2) = [8; r2 + 100]) /\
   (fpToNumList (FPNeg r1 r2) = [9; r2 + 100]) /\
   (fpToNumList (FPSqrt r1 r2) = [10; r2 + 100]) /\
   (fpToNumList (FPAdd r1 r2 r3) = [11; r2 + 100; r3 + 100]) /\
   (fpToNumList (FPSub r1 r2 r3) = [12; r2 + 100; r3 + 100]) /\
   (fpToNumList (FPMul r1 r2 r3) = [13; r2 + 100; r3 + 100]) /\
   (fpToNumList (FPDiv r1 r2 r3) = [14; r2 + 100; r3 + 100]) /\
   (fpToNumList (FPFma r1 r2 r3) = [15; r1 + 100; r2 + 100; r3 + 100]) /\
   (fpToNumList (FPMov r1 r2) = [16; r2 + 100]) /\
   (fpToNumList (FPMovToReg r1 r2 r3) = [17; r2 + 100; r3 + 100]) /\
   (fpToNumList (FPMovFromReg r1 r2 r3) = [18; r2 + 100; r3 + 100]) /\
   (fpToNumList (FPToInt r1 r2) = [19; r2 + 100]) /\
   (fpToNumList (FPFromInt r1 r2) = [20; r2 + 100])`;;

(* (the FPFma list is never matched again) *)

let instToNumList_def = sem1aux_def
  `(instToNumList (asm_Const r w:(A)inst) = [2; wordToNum w]) /\
   (instToNumList (asm_Arith a:(A)inst) = CONS 3 (arithToNumList a)) /\
   (instToNumList (FP fp:(A)inst) = CONS 4 (fpToNumList fp)) /\
   (instToNumList (_:(A)inst) = [1])`;;

(*
Principle:
Each unique instruction is converted to a unique num list.
Numbers between 0 and 99 corresponds to a unique identifier of an instruction.
Numbers above 99 corresponds to a register or a word value.
*)

let OpCurrHeapToNumList_def = cake_def
  `OpCurrHeapToNumList op (r2:num) = [0; arithOpToNum op; r2 + 100]`;;

(* WORD CSE FUNCTIONS *)

let firstRegOfArith_def = cake_def
  `(firstRegOfArith (Binop _ r _ _:(A)asm_arith) = r) /\
   (firstRegOfArith (asm_Shift _ r _ _) = r) /\
   (firstRegOfArith (asm_Div r _ _) = r) /\
   (firstRegOfArith (LongMul r _ _ _) = r) /\
   (firstRegOfArith (LongDiv r _ _ _ _) = r) /\
   (firstRegOfArith (asm_AddCarry r _ _ _) = r) /\
   (firstRegOfArith (AddOverflow r _ _ _) = r) /\
   (firstRegOfArith (SubOverflow r _ _ _) = r)`;;

(* All registers an arith instruction writes (multi-output ops write two), *)
(* so that every written register is invalidated.                          *)

let arithWrites_def = cake_def
  `(arithWrites (Binop _ r _ _:(A)asm_arith) = [r]) /\
   (arithWrites (asm_Shift _ r _ _) = [r]) /\
   (arithWrites (asm_Div r _ _) = [r]) /\
   (arithWrites (LongMul r1 r2 _ _) = [r1; r2]) /\
   (arithWrites (LongDiv r1 r2 _ _ _) = [r1; r2]) /\
   (arithWrites (asm_AddCarry r1 _ _ r4) = [r1; r4]) /\
   (arithWrites (AddOverflow r1 _ _ r4) = [r1; r4]) /\
   (arithWrites (SubOverflow r1 _ _ r4) = [r1; r4])`;;

(* All registers an arith instruction reads (AddCarry also reads the       *)
(* carry-flag register r4).                                                *)

let arithReads_def = cake_def
  `(arithReads (Binop _ _ r2 (Reg r3):(A)asm_arith) = [r2; r3]) /\
   (arithReads (Binop _ _ r2 (Imm _)) = [r2]) /\
   (arithReads (asm_Shift _ _ r2 (Reg r3)) = [r2; r3]) /\
   (arithReads (asm_Shift _ _ r2 (Imm _)) = [r2]) /\
   (arithReads (asm_Div _ r2 r3) = [r2; r3]) /\
   (arithReads (LongMul _ _ r3 r4) = [r3; r4]) /\
   (arithReads (LongDiv _ _ r3 r4 r5) = [r3; r4; r5]) /\
   (arithReads (asm_AddCarry _ r2 r3 r4) = [r2; r3; r4]) /\
   (arithReads (AddOverflow _ r2 r3 _) = [r2; r3]) /\
   (arithReads (SubOverflow _ r2 r3 _) = [r2; r3])`;;

(* The general-purpose registers an fp instruction writes. Most write only *)
(* fp-registers (disjoint from the tracked state), hence [].               *)

let fpWrites_def = sem1aux_def
  `(fpWrites (FPLess r _ _) = [r]) /\
   (fpWrites (FPLessEqual r _ _) = [r]) /\
   (fpWrites (FPEqual r _ _) = [r]) /\
   (fpWrites (FPMovToReg r1 r2 _) = [r1; r2]) /\
   (fpWrites _ = [])`;;

let add_to_data_aux_def = cake_def
  `add_to_data_aux (data:knowledge) (r:num) (i:num list) (x:(A)wl_prog) =
     match balanced_map_lookup listCmp i (knowledge_instrs_mem data) with
       SOME r' ->
         let k = lookup_any r' (knowledge_to_latest data) r' in
         if EVEN r then (data,wl_Move 0 [(r,k)])
         else
           (knowledge_to_canonical_fupd
              (K (insert r r' (knowledge_to_canonical data)))
              (knowledge_to_latest_fupd
                 (K (insert r' r (knowledge_to_latest data))) data),
            wl_Move 0 [(r,k)])
     | NONE ->
         if EVEN r then (data,x)
         else
           (knowledge_instrs_mem_fupd
              (K (balanced_map_insert listCmp i r (knowledge_instrs_mem data)))
              (knowledge_to_canonical_fupd
                 (K (insert r r (knowledge_to_canonical data)))
                 (knowledge_to_latest_fupd
                    (K (insert r r (knowledge_to_latest data))) data)),
            x)`;;

let add_to_data_def = cake_def
  `add_to_data (data:knowledge) (r:num) (adjusted:(A)inst) (x:(A)inst) =
     let i = instToNumList adjusted in
     add_to_data_aux data r i (wl_Inst x)`;;

(* As add_to_data, but for constants: a constant is rematerialisable for    *)
(* free, so a repeated Const is NOT replaced by a Move (which would only    *)
(* extend the live range of the holder). The register equivalence is still *)
(* recorded, so later instructions reading r are still canonicalised and   *)
(* can be CSE'd. Caller guards ODD r.                                       *)

let add_to_data_const_def = cake_def
  `add_to_data_const (data:knowledge) (r:num) (w:A word) =
     let i = instToNumList (asm_Const r w:(A)inst) in
     match balanced_map_lookup listCmp i (knowledge_instrs_mem data) with
       SOME r' ->
         (knowledge_to_canonical_fupd
            (K (insert r r' (knowledge_to_canonical data)))
            (knowledge_to_latest_fupd
               (K (insert r' r (knowledge_to_latest data))) data),
          wl_Inst (asm_Const r w))
     | NONE ->
         (knowledge_instrs_mem_fupd
            (K (balanced_map_insert listCmp i r (knowledge_instrs_mem data)))
            (knowledge_to_canonical_fupd
               (K (insert r r (knowledge_to_canonical data)))
               (knowledge_to_latest_fupd
                  (K (insert r r (knowledge_to_latest data))) data)),
          wl_Inst (asm_Const r w))`;;

(* As add_to_data_aux, but for the load-fact map. *)

let add_to_load_aux_def = cake_def
  `add_to_load_aux (data:knowledge) (r:num) (i:num list) (x:(A)wl_prog) =
     match balanced_map_lookup listCmp i (knowledge_loads_mem data) with
       SOME r' ->
         let k = lookup_any r' (knowledge_to_latest data) r' in
         if EVEN r then (data,wl_Move 0 [(r,k)])
         else
           (knowledge_to_canonical_fupd
              (K (insert r r' (knowledge_to_canonical data)))
              (knowledge_to_latest_fupd
                 (K (insert r' r (knowledge_to_latest data))) data),
            wl_Move 0 [(r,k)])
     | NONE ->
         if EVEN r then (data,x)
         else
           (knowledge_loads_mem_fupd
              (K (balanced_map_insert listCmp i r (knowledge_loads_mem data)))
              (knowledge_to_canonical_fupd
                 (K (insert r r (knowledge_to_canonical data)))
                 (knowledge_to_latest_fupd
                    (K (insert r r (knowledge_to_latest data))) data)),
            x)`;;

let can_mem_arith_def = sem1aux_def
  `(can_mem_arith (Binop _ _ r1 (Reg r2):(A)asm_arith) <=> ODD r1 /\ ODD r2) /\
   (can_mem_arith (Binop _ _ r1 (Imm _)) <=> ODD r1) /\
   (can_mem_arith (asm_Div _ r1 r2) <=> ODD r1 /\ ODD r2) /\
   (can_mem_arith (asm_Shift _ _ r (Imm _)) <=> ODD r) /\
   (can_mem_arith _ <=> F)`;;

let is_store_def = cake_def
  `(is_store asm_Load <=> F) /\
   (is_store Load8 <=> F) /\
   (is_store Load16 <=> F) /\
   (is_store asm_Load32 <=> F) /\
   (is_store asm_Store <=> T) /\
   (is_store Store8 <=> T) /\
   (is_store Store16 <=> T) /\
   (is_store asm_Store32 <=> T)`;;

(* In the Arith case a fact whose reads include the written register would *)
(* not describe the post-state, so it is not stored.  In the Mem case a    *)
(* store writes no register, but it writes memory: all load facts are      *)
(* invalidated (register-only facts survive); a load fact whose address is *)
(* the written register (a = r) would not describe the post-state; EVEN    *)
(* names are never tracked.                                                 *)

(* the clauses are parsed apart: a is an asm_arith in one and a num in     *)
(* another                                                                 *)

let word_cseInst_def = cake_def_clauses
 [`word_cseInst (data:knowledge) (asm_Skip:(A)inst) =
     (data,wl_Inst (asm_Skip:(A)inst))`;
  `word_cseInst (data:knowledge) (asm_Const r w:(A)inst) =
     let data = invalidate_data data r in
     if EVEN r then (data,wl_Inst (asm_Const r w))
     else add_to_data_const data r w`;
  `word_cseInst (data:knowledge) (asm_Arith a:(A)inst) =
     let r = firstRegOfArith a in
     let data = invalidate_regs data (arithWrites a) in
     let a' = canonicalArith data a in
     let rds = arithReads a' in
     if can_mem_arith a' /\ ~MEM r rds then
       add_to_data (register_reads data rds) r (asm_Arith a') (asm_Arith a)
     else (data,wl_Inst (asm_Arith a))`;
  `word_cseInst (data:knowledge) (Mem op r (Addr a ofs):(A)inst) =
     if is_store op then
       (knowledge_loads_mem_fupd (K balanced_map_empty) data,
        wl_Inst (Mem op r (Addr a ofs)))
     else
       let data = invalidate_data data r in
       if EVEN r \/ EVEN a \/ a = r then (data,wl_Inst (Mem op r (Addr a ofs)))
       else
         let a' = canonicalRegs' r data a in
         add_to_load_aux (register_read data a') r (loadToNumList op a' ofs)
                         (wl_Inst (Mem op r (Addr a ofs)))`;
  `word_cseInst (data:knowledge) (FP fp:(A)inst) =
     (invalidate_regs data (fpWrites fp),wl_Inst (FP fp):(A)wl_prog)`];;

(* HOL4 word_cseInst_ind (a case analysis): the kit's derive_induction, as  *)
(* wordLang.ml does for every_var_inst_ind                                  *)

let word_cseInst_ind = IL2AUX_case_ind word_cseInst_def;;

let dest_Var_def = sem1aux_def
  `(dest_Var (wl_Var v:(A)wl_exp) = SOME v) /\
   (dest_Var (_:(A)wl_exp) = NONE)`;;

(* IF-JOIN MERGE

  Knowledge valid after an If is the set of facts that hold after either
  branch: exactly the entries present with equal value on both sides. *)

(* First-order equality-intersection for the instruction map (written      *)
(* without higher-order functions so it can be translated by cv_trans).    *)

let bm_inter_eq_acc_def = cake_def
  `(bm_inter_eq_acc (m2:(num list,A)balanced_map) Tip acc = acc) /\
   (bm_inter_eq_acc m2 (Bin n k v l r) acc =
      bm_inter_eq_acc m2 l
        (bm_inter_eq_acc m2 r
           (if balanced_map_lookup listCmp k m2 = SOME v
            then balanced_map_insert listCmp k v acc
            else acc)))`;;

let bm_inter_eq_acc_ind = cake_ind "bm_inter_eq_acc";;

let bm_inter_eq_def = cake_def
  `bm_inter_eq (m1:(num list,A)balanced_map) m2 =
     bm_inter_eq_acc m2 m1 balanced_map_empty`;;

(* to_latest is reset: its entries must stay within the domain of the      *)
(* merged to_canonical, and they regenerate as soon as new facts are       *)
(* stored.                                                                  *)

let merge_data_def = cake_def
  `merge_data (d1:knowledge) (d2:knowledge) =
     knowledge_REC
       (inter_eq (knowledge_to_canonical d1) (knowledge_to_canonical d2))
       LN
       (FILTER (\(x,v). ALOOKUP (knowledge_gets_mem d2) x = SOME v)
               (knowledge_gets_mem d1))
       (bm_inter_eq (knowledge_instrs_mem d1) (knowledge_instrs_mem d2))
       (bm_inter_eq (knowledge_loads_mem d1) (knowledge_loads_mem d2))`;;

(*
Principle:
  We keep track of a map containing all instructions already dealt with,
    and we explore the program to find instructions matching one in the map.
  If we find one, we change the instruction by a simple move and we keep track
    of the registers equivalence.
  If we do not find any, depending on the instruction, we store it into the map
    under the shape of an num list.
Signification of the terms:
    r -> registers or imm_registers
    rs-> multiple registers associations ((num # num) list) (For the Move)
    i -> instructions
    e -> expressions
    x -> store_name
    p -> programs
    c -> comparisons
    m -> num_set
    b -> binop
    s -> string
*)

(* Comments of the HOL4 clauses: Set: only ODD source registers are        *)
(* tracked; storing a fact about a pre-allocated (EVEN) register would      *)
(* later reset all knowledge on any write to it, for a fact of little       *)
(* value.  OpCurrHeap: r2 = r1 reads the register the instruction           *)
(* overwrites; such a fact would not describe the post-state, so it is not  *)
(* stored.  LocValue: Loc l 0 is a constant determined by l, so CSE it like *)
(* an immediate; tag 48 is distinct from every other stored hash head (0,   *)
(* 2, 3).  Store cannot occur in flat code, but it writes memory, so be     *)
(* sound: drop the load facts, keep the register-only facts.  Buffer writes *)
(* touch only the code/data buffers, nothing we track.  FFI cuts the local  *)
(* environment, so all knowledge is stale.  StoreConsts writes (or unsets)  *)
(* only its four register args and memory; the memory writes invalidate the *)
(* load facts.  ShareInst: a load writes its var; a store writes no         *)
(* register; shared memory (sh_mdomain) is disjoint from the heap memory    *)
(* that load facts describe, so loads_mem survives both.  Loop:             *)
(* conservative, optimise the loop body from empty state.                   *)
(* The clauses are parsed apart (p, c and m have different types in         *)
(* different clauses).                                                       *)

let word_cse_def = sem1aux_def (list_mk_conj
 [`(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_Move r rs) =
     let data' = canonicalMoveRegs data rs in
     (data',wl_Move r rs)`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_Inst i) =
     let (data',p) = word_cseInst data i in
     (data',p)`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_Get r x) =
     let data = invalidate_data data r in
     match ALOOKUP (knowledge_gets_mem data) x with
       NONE ->
         if EVEN r then (data,wl_Get r x) else
         (knowledge_gets_mem_fupd (K (CONS (x,r) (knowledge_gets_mem data)))
            (knowledge_to_canonical_fupd
               (K (insert r r (knowledge_to_canonical data)))
               (knowledge_to_latest_fupd
                  (K (insert r r (knowledge_to_latest data))) data)),
          wl_Get r x)
     | SOME k ->
         if EVEN r
         then (data,wl_Move 1 [(r,lookup_any k (knowledge_to_latest data) k)])
         else
           (knowledge_to_canonical_fupd
              (K (insert r k (knowledge_to_canonical data)))
              (knowledge_to_latest_fupd
                 (K (insert k r (knowledge_to_latest data))) data),
            wl_Move 1 [(r,lookup_any k (knowledge_to_latest data) k)])`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_Set x e) =
     if x = CurrHeap then (empty_data,wl_Set x e)
     else
       let new_gets_mem = FILTER (\(m,n). ~(m = x)) (knowledge_gets_mem data) in
       match dest_Var e with
         NONE -> (knowledge_gets_mem_fupd (K new_gets_mem) data,wl_Set x e)
       | SOME v ->
           if EVEN v
           then (knowledge_gets_mem_fupd (K new_gets_mem) data,wl_Set x e)
           else
             (knowledge_gets_mem_fupd
                (K (CONS (x,canonicalRegs data v) new_gets_mem))
                (knowledge_to_canonical_fupd
                   (K (insert v (lookup_any v (knowledge_to_canonical data) v)
                         (knowledge_to_canonical data))) data),
              wl_Set x e)`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (MustTerminate p) =
     let (data',p') = word_cse data p in
     (data',MustTerminate p')`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_Call ret dest args handler) =
     (empty_data,wl_Call ret dest args handler)`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_Seq p1 p2) =
     let (data1,p1') = word_cse data p1 in
     let (data2,p2') = word_cse data1 p2 in
     (data2,wl_Seq p1' p2')`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_If c r1 r2 p1 p2) =
     let (data1,p1') = word_cse data p1 in
     let (data2,p2') = word_cse data p2 in
     (merge_data data1 data2,wl_If c r1 r2 p1' p2')`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_OpCurrHeap b r1 r2) =
     let data = invalidate_data data r1 in
     if EVEN r2 \/ r2 = r1 then (data,wl_OpCurrHeap b r1 r2) else
     let r2' = canonicalRegs' r1 data r2 in
     let pL = OpCurrHeapToNumList b r2' in
     add_to_data_aux (register_read data r2') r1 pL (wl_OpCurrHeap b r1 r2)`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_LocValue r l) =
     let data = invalidate_data data r in
     add_to_data_aux data r [48; l] (wl_LocValue r l)`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     wl_Skip = (data,wl_Skip)`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_Store e r) =
     (knowledge_loads_mem_fupd (K balanced_map_empty) data,wl_Store e r)`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_Assign r e) =
     (data,wl_Assign r e)`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_Raise r) = (data,wl_Raise r)`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_Return r1 r2) =
     (data,wl_Return r1 r2)`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     wl_Tick = (data,wl_Tick)`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_Alloc r m) =
     (empty_data,wl_Alloc r m)`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_Install p l dp dl m) =
     (empty_data,wl_Install p l dp dl m)`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_CodeBufferWrite r1 r2) =
     (data,wl_CodeBufferWrite r1 r2)`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_DataBufferWrite r1 r2) =
     (data,wl_DataBufferWrite r1 r2)`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_FFI s p1 l1 p2 l2 m) =
     (empty_data,wl_FFI s p1 l1 p2 l2 m)`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_StoreConsts r1 r2 r3 r4 payload) =
     (let data = invalidate_regs data [r1; r2; r3; r4] in
      (knowledge_loads_mem_fupd (K balanced_map_empty) data,
       wl_StoreConsts r1 r2 r3 r4 payload))`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (ShareInst op r exp) =
     let data = (if is_store op then data else invalidate_data data r) in
     (data,ShareInst op r exp)`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_Loop names c exit_names) =
     let (data1,c') = word_cse empty_data c in
     (empty_data,wl_Loop names c' exit_names)`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_Break k) = (data,wl_Break k)`;
  `(word_cse:knowledge->(A)wl_prog->knowledge#(A)wl_prog) data
     (wl_Continue k) =
     (data,wl_Continue k)`]);;

let word_cse_ind = cake_ind "word_cse";;

let word_common_subexp_elim_def = cake_def
  `word_common_subexp_elim (prog:(A)wl_prog) =
     let (data,new_prog) = word_cse empty_data prog in
     new_prog`;;

(* tests *)

(* HOL4 deletes the constant Seqs after its tests (Theory.delete_const);    *)
(* here it stays, under the name word_cse_Seqs.                             *)

let word_cse_Seqs_def = cake_def
  `(word_cse_Seqs [] = (wl_Skip:(A)wl_prog)) /\
   (word_cse_Seqs [x] = x) /\
   (word_cse_Seqs (CONS x (CONS y xs)) = wl_Seq x (word_cse_Seqs (CONS y xs)))`;;

let word_cse_Seqs_ind = cake_ind "word_cse_Seqs";;
