(* ========================================================================= *)
(* word_copy: port of HOL4 compiler/backend/word_copyScript.sml (CakeML      *)
(* v3479).                                                                   *)
(* This compilation pass performs a copy propagation phase.                 *)
(* NOTE: Copy propagation may be incomplete if input is not in SSA form.    *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - num_map is num spt; the alist (store_name, num) alist is               *)
(*   (store_name#num) list; EVERY is ALL.                                    *)
(* - wordLang constructors carry the prefix wl_ (wl_Inst, wl_Move, ...),     *)
(*   asm constructors asm_ where names.tsv says so (asm_Skip, asm_Const,     *)
(*   asm_Arith, asm_Shift, asm_Div, asm_AddCarry, asm_Load, asm_Store, ...). *)
(* - The record literal <| to_eq := a; from_eq := b; store_to_eq := c;       *)
(*   next := d |> is copy_state_REC a b c d.                                 *)
(* - HOL4 let a = x; b = y in t is written let a = x in let b = y in t.      *)

(*
  The copy propagator does the propagation but
    does not delete the old copy, i.e.:

  {a}
  b := a
  {b}
  c := b
  {c}
  (any future use of a or b would be replaced by c)

  The propagator state consists of
  1) a map from vars to its equivalence class
  2) a map from equivalence class to its representative
  3) a counter to generate fresh equivalences
  4) a partial map from store_names to a vars holding its value

  Only alloc vars (is_alloc_var) are ever stored in
    this mapping because we never want to
    copy propagate the others.
*)

(* to_eq maps var to its equivalence class; from_eq maps equivalence class  *)
(* to its representative; store_to_eq maps store names to an equivalence    *)
(* class                                                                     *)

let copy_state_INFO = cake_record "copy_state"
  ["to_eq","num spt";
   "from_eq","num spt";
   "store_to_eq","(store_name#num) list";
   "next","num"];;

let copy_state_component_equality = copy_state_INFO.ri_component_equality;;

let empty_eq_def = cake_def
  `empty_eq = copy_state_REC LN LN [] 0`;;

(* lookup representative of eq class, if it exists                          *)
(* otherwise it is just the var itself                                       *)

let lookup_eq_def = cake_def
  `lookup_eq (cs:copy_state) (v:num) =
     match lookup v (copy_state_to_eq cs) with
       NONE -> v
     | SOME c ->
         (match lookup c (copy_state_from_eq cs) with
            NONE -> v
          | SOME v' -> v')`;;

let lookup_eq_imm_def = cake_def
  `lookup_eq_imm (cs:copy_state) (vi:(A)reg_imm) =
     match vi with
       Reg v -> Reg (lookup_eq cs v)
     | _ -> vi`;;

(* remove v from its equivalence class,                                      *)
(*     possibly destroying the entire class                                  *)
(* In SSA, this should never happen, so                                      *)
(* we simply drop the entire eq state if it does                             *)

let remove_eq_def = cake_def
  `remove_eq (cs:copy_state) (v:num) =
     match lookup v (copy_state_to_eq cs) with
       NONE -> cs
     | SOME c -> empty_eq`;;

let remove_eqs_def = cake_def
  `(remove_eqs (cs:copy_state) [] = cs) /\
   (remove_eqs cs (CONS (v:num) vs) = remove_eqs (remove_eq cs v) vs)`;;

let remove_eqs_ind = cake_ind "remove_eqs";;

(* AddCarry: r4 is both read from and written to.  The last two clauses    *)
(* are catch-alls: all FP, and (should not happen) the rest.               *)

let copy_prop_inst_def = sem1aux_def
  `(copy_prop_inst (asm_Skip:(A)inst) (cs:copy_state) =
      (wl_Skip:(A)wl_prog,cs)) /\
   (copy_prop_inst (asm_Const reg w) cs =
      (wl_Inst (asm_Const reg w),remove_eq cs reg)) /\
   (copy_prop_inst (asm_Arith (Binop bop r1 r2 ri)) cs =
      let cs' = remove_eq cs r1 in
      let r2' = lookup_eq cs r2 in
      let ri' = lookup_eq_imm cs ri in
      let ri'' = if ri' = Reg r1 then ri else ri' in
      (wl_Inst (asm_Arith (Binop bop r1 r2' ri'')),cs')) /\
   (copy_prop_inst (asm_Arith (asm_Shift shift r1 r2 n)) cs =
      let cs' = remove_eq cs r1 in
      let r2' = lookup_eq cs r2 in
      let n' = lookup_eq_imm cs n in
      let n'' = if n' = Reg r1 then n else n' in
      (wl_Inst (asm_Arith (asm_Shift shift r1 r2' n'')),cs')) /\
   (copy_prop_inst (asm_Arith (asm_Div r1 r2 r3)) cs =
      let r2' = lookup_eq cs r2 in
      let r3' = lookup_eq cs r3 in
      (wl_Inst (asm_Arith (asm_Div r1 r2' r3')),remove_eq cs r1)) /\
   (copy_prop_inst (asm_Arith (asm_AddCarry r1 r2 r3 r4)) cs =
      let cs' = remove_eqs cs [r1; r4] in
      let r2' = lookup_eq cs r2 in
      let r3' = lookup_eq cs r3 in
      let r3'' = if r3' = r1 then r3 else r3' in
      (wl_Inst (asm_Arith (asm_AddCarry r1 r2' r3'' r4)),cs')) /\
   (copy_prop_inst (asm_Arith (AddOverflow r1 r2 r3 r4)) cs =
      let cs' = remove_eqs cs [r1; r4] in
      let r2' = lookup_eq cs r2 in
      let r3' = lookup_eq cs r3 in
      let r3'' = if r3' = r1 then r3 else r3' in
      (wl_Inst (asm_Arith (AddOverflow r1 r2' r3'' r4)),cs')) /\
   (copy_prop_inst (asm_Arith (SubOverflow r1 r2 r3 r4)) cs =
      let cs' = remove_eqs cs [r1; r4] in
      let r2' = lookup_eq cs r2 in
      let r3' = lookup_eq cs r3 in
      let r3'' = if r3' = r1 then r3 else r3' in
      (wl_Inst (asm_Arith (SubOverflow r1 r2' r3'' r4)),cs')) /\
   (copy_prop_inst (asm_Arith (LongMul r1 r2 r3 r4)) cs =
      let r3' = lookup_eq cs r3 in
      let r4' = lookup_eq cs r4 in
      (wl_Inst (asm_Arith (LongMul r1 r2 r3 r4)),remove_eqs cs [r1; r2])) /\
   (copy_prop_inst (asm_Arith (LongDiv r1 r2 r3 r4 r5)) cs =
      let r3' = lookup_eq cs r3 in
      let r4' = lookup_eq cs r4 in
      let r5' = lookup_eq cs r5 in
      (wl_Inst (asm_Arith (LongDiv r1 r2 r3' r4' r5')),remove_eqs cs [r2; r1])) /\
   (copy_prop_inst (Mem asm_Load r (Addr a w)) cs =
      let a' = lookup_eq cs a in
      (wl_Inst (Mem asm_Load r (Addr a' w)),remove_eq cs r)) /\
   (copy_prop_inst (Mem asm_Store r (Addr a w)) cs =
      let a' = lookup_eq cs a in
      let r' = lookup_eq cs r in
      (wl_Inst (Mem asm_Store r' (Addr a' w)),cs)) /\
   (copy_prop_inst (Mem Load8 r (Addr a w)) cs =
      let a' = lookup_eq cs a in
      (wl_Inst (Mem Load8 r (Addr a' w)),remove_eq cs r)) /\
   (copy_prop_inst (Mem Store8 r (Addr a w)) cs =
      let a' = lookup_eq cs a in
      let r' = lookup_eq cs r in
      (wl_Inst (Mem Store8 r' (Addr a' w)),cs)) /\
   (copy_prop_inst (Mem Load16 r (Addr a w)) cs =
      let a' = lookup_eq cs a in
      (wl_Inst (Mem Load16 r (Addr a' w)),remove_eq cs r)) /\
   (copy_prop_inst (Mem Store16 r (Addr a w)) cs =
      let a' = lookup_eq cs a in
      let r' = lookup_eq cs r in
      (wl_Inst (Mem Store16 r' (Addr a' w)),cs)) /\
   (copy_prop_inst (Mem asm_Load32 r (Addr a w)) cs =
      let a' = lookup_eq cs a in
      (wl_Inst (Mem asm_Load32 r (Addr a' w)),remove_eq cs r)) /\
   (copy_prop_inst (Mem asm_Store32 r (Addr a w)) cs =
      let a' = lookup_eq cs a in
      let r' = lookup_eq cs r in
      (wl_Inst (Mem asm_Store32 r' (Addr a' w)),cs)) /\
   (copy_prop_inst (FP (FPLess r f1 f2)) cs =
      (wl_Inst (FP (FPLess r f1 f2)),remove_eq cs r)) /\
   (copy_prop_inst (FP (FPLessEqual r f1 f2)) cs =
      (wl_Inst (FP (FPLessEqual r f1 f2)),remove_eq cs r)) /\
   (copy_prop_inst (FP (FPEqual r f1 f2)) cs =
      (wl_Inst (FP (FPEqual r f1 f2)),remove_eq cs r)) /\
   (copy_prop_inst (FP (FPMovToReg r1 r2 d)) cs =
      (wl_Inst (FP (FPMovToReg r1 r2 d)),remove_eqs cs [r1; r2])) /\
   (copy_prop_inst (FP (FPMovFromReg d r1 r2)) cs =
      let r1' = lookup_eq cs r1 in
      let r2' = lookup_eq cs r2 in
      let (r1'',r2'') = if r1' = r2' then (r1,r2) else (r1',r2') in
      (wl_Inst (FP (FPMovFromReg d r1'' r2'')),cs)) /\
   (copy_prop_inst (FP x) cs = (wl_Inst (FP x),cs)) /\
   (copy_prop_inst _ cs = ARB)`;;

let copy_prop_inst_ind = IL2AUX_case_ind copy_prop_inst_def;;

(* handle x := y by making x the new                                         *)
(*   class representative of y.                                              *)
(*   x must be guaranteed to not have to_eq                                  *)

let set_eq_def = cake_def
  `set_eq (cs:copy_state) (x:num) (y:num) =
     if is_alloc_var x /\ is_alloc_var y
     then
       match (match lookup y (copy_state_to_eq cs) with
                NONE -> NONE
              | SOME c ->
                  if lookup c (copy_state_from_eq cs) = NONE then NONE
                  else SOME c) with
         NONE ->
           copy_state_REC
             (insert x (copy_state_next cs)
                (insert y (copy_state_next cs) (copy_state_to_eq cs)))
             (insert (copy_state_next cs) x (copy_state_from_eq cs))
             (copy_state_store_to_eq cs)
             (copy_state_next cs + 1)
       | SOME c ->
           copy_state_REC
             (insert x c (copy_state_to_eq cs))
             (insert c x (copy_state_from_eq cs))
             (copy_state_store_to_eq cs)
             (copy_state_next cs)
     else cs`;;

(* Handle Store <- y                                                         *)
(*   If y has no equivalence class,                                          *)
(*     create a singleton equivalence class for y                            *)
(*   Otherwise, reuse the existing class for y.                              *)
(*   Note: SSA ensures y is always an alloc_var, so the else branch is dead  *)
(*   code.                                                                   *)

let set_store_eq_def = cake_def
  `set_store_eq (cs:copy_state) (s:store_name) (y:num) =
     if is_alloc_var y
     then
       match (match lookup y (copy_state_to_eq cs) with
                NONE -> NONE
              | SOME c ->
                  if lookup c (copy_state_from_eq cs) = NONE then NONE
                  else SOME c) with
         NONE ->
           copy_state_REC
             (insert y (copy_state_next cs) (copy_state_to_eq cs))
             (insert (copy_state_next cs) y (copy_state_from_eq cs))
             (CONS (s,copy_state_next cs) (copy_state_store_to_eq cs))
             (copy_state_next cs + 1)
       | SOME c ->
           copy_state_store_to_eq_fupd
             (combin_K (CONS (s,c) (copy_state_store_to_eq cs))) cs
     else empty_eq`;;

let lookup_store_eq_def = cake_def
  `lookup_store_eq (cs:copy_state) (s:store_name) =
     match ALOOKUP (copy_state_store_to_eq cs) s with
       NONE -> NONE
     | SOME c ->
         (match lookup c (copy_state_from_eq cs) with
            NONE -> NONE
          | SOME (v':num) -> SOME v')`;;

(* conservatively merge two equivalence classes *)

let merge_eqs_def = cake_def
  `merge_eqs (cs:copy_state) (ds:copy_state) =
     copy_state_REC
       (inter_eq (copy_state_to_eq cs) (copy_state_to_eq ds))
       (inter_eq (copy_state_from_eq cs) (copy_state_from_eq ds))
       (FILTER (\(s,c). ALOOKUP (copy_state_store_to_eq cs) s = SOME c /\
                        ALOOKUP (copy_state_store_to_eq ds) s = SOME c)
               (copy_state_store_to_eq cs))
       (MAX (copy_state_next cs) (copy_state_next ds))`;;

(* should not matter whether we put y or y' in set_eq? *)

let copy_prop_move_def = cake_def
  `(copy_prop_move [] (cs:copy_state) = ([]:(num#num)list,cs)) /\
   (copy_prop_move (CONS (x,y) xs) cs =
      let y' = lookup_eq cs y in
      let (ms,cs') = copy_prop_move xs cs in
      let cs'' = set_eq (remove_eq cs' x) x y in
      (CONS (x,y') ms,cs''))`;;

let copy_prop_move_ind = cake_ind "copy_prop_move";;

let copy_prop_share_def = cake_def
  `copy_prop_share (exp:(A)wl_exp) (cs:copy_state) =
     match exp with
       wl_Var r -> wl_Var (lookup_eq cs r)
     | wl_Op asm_Add [wl_Var r; wl_Const c] ->
         wl_Op asm_Add [wl_Var (lookup_eq cs r); wl_Const c]
     | _ -> exp`;;

(* Move: set (MAP FST xs) INTER set (MAP SND xs) = EMPTY.  If: TODO: same    *)
(* mapping going in.  Set: the catch-all is a flat_exp.  Call: args will be  *)
(* 0,2,4,...; TODO: are handlers worth analyzing?  Loop: conservative,       *)
(* optimizes body from empty state; could be smarter by tracking copy facts  *)
(* across iterations via Break/Continue flow.  The last clause: impossible?  *)
(* The clauses are parsed apart (b, c and i have different types in          *)
(* different clauses).                                                        *)

let copy_prop_prog_def = sem1aux_def (list_mk_conj
 [`(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     wl_Skip cs = (wl_Skip,cs)`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (wl_Move pri xs) cs =
     let tt = MAP FST xs in
     let ss = MAP SND xs in
     if ALL (\t. ~MEM t ss) tt then
       let (xs',cs') = copy_prop_move xs cs in
       (wl_Move pri xs',cs')
     else (wl_Move pri xs,empty_eq)`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (wl_Inst i) cs = copy_prop_inst i cs`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (wl_Return v1 v2) cs =
     let v1' = lookup_eq cs v1 in
     let v2' = MAP (lookup_eq cs) v2 in
     (wl_Return v1' v2',cs)`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (wl_Raise v) cs =
     let v' = lookup_eq cs v in
     (wl_Raise v',cs)`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (wl_OpCurrHeap b dst src) cs =
     let src' = lookup_eq cs src in
     let src'' = if src' = dst then src else src' in
     (wl_OpCurrHeap b dst src'',remove_eq cs dst)`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     wl_Tick cs = (wl_Tick,cs)`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (MustTerminate p1) cs =
     let (p1',cs') = copy_prop_prog p1 cs in
     (MustTerminate p1',cs')`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (wl_Seq p1 p2) cs =
     let (q1,cs') = copy_prop_prog p1 cs in
     let (q2,cs'') = copy_prop_prog p2 cs' in
     (wl_Seq q1 q2,cs'')`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (wl_If cmp r ri p1 p2) cs =
     let r' = lookup_eq cs r in
     let ri' = lookup_eq_imm cs ri in
     let (q1,cs') = copy_prop_prog p1 cs in
     let (q2,cs'') = copy_prop_prog p2 cs in
     (wl_If cmp r' ri' q1 q2,merge_eqs cs' cs'')`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (wl_Set name exp) cs =
     match exp with
       wl_Var n ->
         let n' = lookup_eq cs n in
         (wl_Set name (wl_Var n'),set_store_eq cs name n)
     | _ -> (wl_Set name exp,empty_eq)`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (wl_Get n name) cs =
     match lookup_store_eq cs name with
       NONE -> (wl_Get n name,set_store_eq (remove_eq cs n) name n)
     | SOME v ->
         if ~(v = n) then
           let (xs',cs') = copy_prop_move [(n,v)] cs in
           (wl_Move 0 xs',cs')
         else (wl_Skip,cs)`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (wl_Call ret dest args handler) cs =
     (wl_Call ret dest args handler,empty_eq)`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (wl_Alloc r live) cs = (wl_Alloc r live,empty_eq)`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (wl_StoreConsts a b c d ws) cs =
     (wl_StoreConsts a b c d ws,remove_eqs cs [a; b; c; d])`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (wl_LocValue r l1) cs = (wl_LocValue r l1,remove_eq cs r)`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (wl_Install r1 r2 r3 r4 live) cs =
     (wl_Install r1 r2 r3 r4 live,empty_eq)`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (wl_CodeBufferWrite r1 r2) cs =
     let r1' = lookup_eq cs r1 in
     let r2' = lookup_eq cs r2 in
     (wl_CodeBufferWrite r1' r2',cs)`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (wl_DataBufferWrite r1 r2) cs =
     let r1' = lookup_eq cs r1 in
     let r2' = lookup_eq cs r2 in
     (wl_DataBufferWrite r1' r2',cs)`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (wl_FFI i r1 r2 r3 r4 live) cs =
     (wl_FFI i r1 r2 r3 r4 live,empty_eq)`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (ShareInst op v exp) cs =
     let exp' = copy_prop_share exp cs in
     (ShareInst op v exp',remove_eq cs v)`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (wl_Loop names c exit_names) cs =
     let (c',cs') = copy_prop_prog c empty_eq in
     (wl_Loop names c' exit_names,empty_eq)`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (wl_Break k) cs = (wl_Break k,cs)`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     (wl_Continue k) cs = (wl_Continue k,cs)`;
  `(copy_prop_prog:(A)wl_prog->copy_state->(A)wl_prog#copy_state)
     prog cs = (prog,empty_eq)`]);;

let copy_prop_prog_ind = cake_ind "copy_prop_prog";;

let copy_prop_def = cake_def
  `copy_prop (e:(A)wl_prog) = FST (copy_prop_prog e empty_eq)`;;
