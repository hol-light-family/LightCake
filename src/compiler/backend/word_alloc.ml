(* ========================================================================= *)
(* word_alloc: port of HOL4 compiler/backend/word_allocScript.sml            *)
(* (CakeML v3479).  This is the compiler's register allocator. It supports  *)
(* different modes: 0) simple allocator, no spill heuristics; 1) simple      *)
(* allocator + spill heuristics; 2) IRC allocator, no spill heuristics       *)
(* (default); 3) IRC allocator + spill heuristics; 4) linear scan register   *)
(* allocator.                                                                *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - wordLang and asm names as in doc/names.tsv (wl_Seq, wl_Move,            *)
(*   asm_Arith, Mem asm_Load, ...); the clash_tree constructors of reg_alloc *)
(*   are Delta, reg_alloc_Set, reg_alloc_Branch, reg_alloc_Seq.              *)
(* - HOL4's Overloads Move0 and Move1 (Move 0 and Move 1) are written out.   *)
(* - HOL4 GENLIST f is list_of_seq f, FOLDR f e l is ITLIST f l e, ++ is     *)
(*   APPEND (left associative in HOL4), $ is application; HOL4 () is one and *)
(*   a pattern () is (_:1); n2w n is word n, dimindex(:'a) is dimindex(:A). *)
(* - Paired lambdas (\(x,y). t) are (\xy. match xy with (x,y) -> t).        *)
(* - Definitions with many clauses or a catch-all clause are made with       *)
(*   sem1aux_def (semantics/sem1aux_tfl.ml), clauses parsed one by one as   *)
(*   in wordLang.ml; the induction theorems of the non-recursive ones come   *)
(*   from IL2AUX_case_ind of wordLang.ml.                                    *)
(* - The theorems get_writes_pmatch, get_prefs_pmatch and get_forced_pmatch  *)
(*   (HOL4 PMATCH forms of the definitions, for the translator) are stated  *)
(*   with HOL Light's match, compiled by the kit into case constants.       *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mllist.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/reg_alloc/linear_scan.ml";;

prioritize_num();;
type_invention_error := true;;

(*SSA form*)
let apply_nummap_key_def = cake_def
  `apply_nummap_key f (names:A spt) =
     fromAList (MAP (\xy. match xy with (x,y) -> (f x,y)) (toAList names))`;;
let _ = cake_add_simps [apply_nummap_key_def];;

let apply_nummaps_key_def = cake_def
  `apply_nummaps_key f (names:A spt#B spt) =
     (fromAList (MAP (\xy. match xy with (x,y) -> (f x,y)) (toAList (FST names))),
      fromAList (MAP (\xy. match xy with (x,y) -> (f x,y)) (toAList (SND names))))`;;

let option_lookup_def = cake_def
  `option_lookup t v = match lookup v t with NONE -> 0 | SOME x -> x`;;

let even_list_def = cake_def
  `even_list = list_of_seq (\x. 2 * x)`;;

(*Consistently sets up the next alloc variable rename for v*)
let next_var_rename_def = cake_def
  `next_var_rename v ssa (na:num) = (na,insert v na ssa,na + 4)`;;

(* written this way to make it ascending (can also use acc passing) *)
let list_next_var_rename_def = cake_def
  `(list_next_var_rename [] ssa (na:num) = ([],ssa,na)) /\
   (list_next_var_rename (CONS x xs) ssa na =
      let (y,ssa',na') = next_var_rename x ssa na in
      let (ys,ssa'',na'') = list_next_var_rename xs ssa' na' in
      (CONS y ys,ssa'',na''))`;;

let fake_move_def = cake_def
  `fake_move v = (wl_Inst (asm_Const v (word 0)):(A)wl_prog)`;;

(*Do the merging moves only*)
(* HOL4: merge_moves *)
let word_alloc_merge_moves_def = cake_def
  `(word_alloc_merge_moves [] ssa_L ssa_R (na:num) = ([],[],na,ssa_L,ssa_R)) /\
   (word_alloc_merge_moves (CONS x xs) ssa_L ssa_R na =
      let (seqL,seqR,na',ssa_L',ssa_R') =
        word_alloc_merge_moves xs ssa_L ssa_R na in
      let optLx = lookup x ssa_L' in
      let optLy = lookup x ssa_R' in
      match (optLx,optLy) with
        (SOME Lx,SOME Ly) ->
          if Lx = Ly then (seqL,seqR,na',ssa_L',ssa_R')
          else
            let Lmove = (na',Lx) in
            let Rmove = (na',Ly) in
            (CONS Lmove seqL,CONS Rmove seqR,na' + 4,insert x na' ssa_L',
             insert x na' ssa_R')
      | _ -> (seqL,seqR,na',ssa_L',ssa_R'))`;;

(* tracking priority of moves
  0 = unprioritized
  1 = base high priority
  2 = higher priority than base

  T, INL <- left side
  F, INR <- right side
*)
let priority_def = cake_def
  `(priority NONE (b:bool) = 1) /\
   (priority (SOME (INL (_:1))) b = if b then 2 else 1) /\
   (priority (SOME (INR (_:1))) b = if b then 1 else 2)`;;

(*Separately do the fake moves*)
let fake_moves_def = cake_def
  `(fake_moves prio [] ssa_L ssa_R (na:num) =
      (wl_Skip:(A)wl_prog,wl_Skip:(A)wl_prog,na,ssa_L,ssa_R)) /\
   (fake_moves prio (CONS x xs) ssa_L ssa_R na =
      let (seqL,seqR,na',ssa_L',ssa_R') =
        fake_moves prio xs ssa_L ssa_R na in
      let optLx = lookup x ssa_L' in
      let optLy = lookup x ssa_R' in
      match (optLx,optLy) with
        (NONE,SOME Ly) ->
          let Lmove = wl_Seq seqL (fake_move na') in
          let Rmove = wl_Seq seqR (wl_Move (priority prio F) [(na',Ly)]) in
          (Lmove,Rmove,na' + 4,insert x na' ssa_L',insert x na' ssa_R')
      | (SOME Lx,NONE) ->
          let Lmove = wl_Seq seqL (wl_Move (priority prio T) [(na',Lx)]) in
          let Rmove = wl_Seq seqR (fake_move na') in
          (Lmove,Rmove,na' + 4,insert x na' ssa_L',insert x na' ssa_R')
      | _ -> (seqL,seqR,na',ssa_L',ssa_R'))`;;

let fix_inconsistencies_def = cake_def
  `fix_inconsistencies prio ssa_L ssa_R na =
     let var_union = MAP FST (toAList (sptree_union ssa_L ssa_R)) in
     let (Lmov,Rmov,na',ssa_L',ssa_R') =
       word_alloc_merge_moves var_union ssa_L ssa_R na in
     let (Lseq,Rseq,na'',ssa_L'',ssa_R'') =
       fake_moves prio var_union ssa_L' ssa_R' na' in
     (wl_Seq (wl_Move (priority prio T) Lmov) Lseq:(A)wl_prog,
      wl_Seq (wl_Move (priority prio F) Rmov) Rseq:(A)wl_prog,na'',ssa_L'')`;;

(*ssa_cc_trans_inst does not need to interact with stack*)
(* Note: this needs to return a prog to support specific registers for     *)
(* AddCarry and other special insts.  For AddOverflow and SubOverflow,      *)
(* setting r4 to 0 is not necessary; however, this helps with              *)
(* word_to_stack which currently only spills one register on writes.  The  *)
(* catch-all clause is for future instructions and all other FP.           *)
let ssa_cc_trans_inst_def = sem1aux_def (list_mk_conj
 [`ssa_cc_trans_inst (asm_Skip:(A)inst) (ssa:num spt) (na:num) = (wl_Skip:(A)wl_prog,ssa,na)`;
  `ssa_cc_trans_inst (asm_Const reg (w:A word)) (ssa:num spt) (na:num) =
     let (reg',ssa',na') = next_var_rename reg ssa na in
     (wl_Inst (asm_Const reg' w):(A)wl_prog,ssa',na')`;
  `ssa_cc_trans_inst (asm_Arith (Binop bop r1 r2 ri):(A)inst) (ssa:num spt) (na:num) =
     match ri with
       Reg r3 ->
         let r3' = option_lookup ssa r3 in
         let r2' = option_lookup ssa r2 in
         let (r1',ssa',na') = next_var_rename r1 ssa na in
         (wl_Inst (asm_Arith (Binop bop r1' r2' (Reg r3'))):(A)wl_prog,ssa',na')
     | _ ->
         let r2' = option_lookup ssa r2 in
         let (r1',ssa',na') = next_var_rename r1 ssa na in
         (wl_Inst (asm_Arith (Binop bop r1' r2' ri)),ssa',na')`;
  `ssa_cc_trans_inst (asm_Arith (asm_Shift shift r1 r2 ri):(A)inst) (ssa:num spt) (na:num) =
     match ri with
       Reg r3 ->
         let r3' = option_lookup ssa r3 in
         let r2' = option_lookup ssa r2 in
         let mov_in = wl_Move 1 [(8,r3')] in
         let (r1',ssa',na') = next_var_rename r1 ssa na in
         (wl_Seq mov_in (wl_Inst (asm_Arith (asm_Shift shift r1' r2' (Reg 8)))):
            (A)wl_prog,ssa',na')
     | _ ->
         let r2' = option_lookup ssa r2 in
         let (r1',ssa',na') = next_var_rename r1 ssa na in
         (wl_Inst (asm_Arith (asm_Shift shift r1' r2' ri)),ssa',na')`;
  `ssa_cc_trans_inst (asm_Arith (asm_Div r1 r2 r3):(A)inst) (ssa:num spt) (na:num) =
     let r2' = option_lookup ssa r2 in
     let r3' = option_lookup ssa r3 in
     let (r1',ssa',na') = next_var_rename r1 ssa na in
     (wl_Inst (asm_Arith (asm_Div r1' r2' r3')):(A)wl_prog,ssa',na')`;
  `ssa_cc_trans_inst (asm_Arith (asm_AddCarry r1 r2 r3 r4):(A)inst) (ssa:num spt) (na:num) =
     let r2' = option_lookup ssa r2 in
     let r3' = option_lookup ssa r3 in
     let r4' = option_lookup ssa r4 in
     let (r1',ssa',na') = next_var_rename r1 ssa na in
     let mov_in = wl_Move 1 [(0,r4')] in
     let (r4'',ssa'',na'') = next_var_rename r4 ssa' na' in
     let mov_out = wl_Move 1 [(r4'',0)] in
     (wl_Seq mov_in (wl_Seq (wl_Inst (asm_Arith (asm_AddCarry r1' r2' r3' 0))) mov_out):
        (A)wl_prog,ssa'',na'')`;
  `ssa_cc_trans_inst (asm_Arith (AddOverflow r1 r2 r3 r4):(A)inst) (ssa:num spt) (na:num) =
     let r2' = option_lookup ssa r2 in
     let r3' = option_lookup ssa r3 in
     let (r1',ssa',na') = next_var_rename r1 ssa na in
     let (r4'',ssa'',na'') = next_var_rename r4 ssa' na' in
     let mov_out = wl_Move 1 [(r4'',0)] in
     (wl_Seq (wl_Inst (asm_Arith (AddOverflow r1' r2' r3' 0))) mov_out:(A)wl_prog,
      ssa'',na'')`;
  `ssa_cc_trans_inst (asm_Arith (SubOverflow r1 r2 r3 r4):(A)inst) (ssa:num spt) (na:num) =
     let r2' = option_lookup ssa r2 in
     let r3' = option_lookup ssa r3 in
     let (r1',ssa',na') = next_var_rename r1 ssa na in
     let (r4'',ssa'',na'') = next_var_rename r4 ssa' na' in
     let mov_out = wl_Move 1 [(r4'',0)] in
     (wl_Seq (wl_Inst (asm_Arith (SubOverflow r1' r2' r3' 0))) mov_out:(A)wl_prog,
      ssa'',na'')`;
  `ssa_cc_trans_inst (asm_Arith (LongMul r1 r2 r3 r4):(A)inst) (ssa:num spt) (na:num) =
     let r3' = option_lookup ssa r3 in
     let r4' = option_lookup ssa r4 in
     let mov_in = wl_Move 1 [(0,r3');(4,r4')] in
     let (r1',ssa',na') = next_var_rename r1 ssa na in
     let (r2',ssa'',na'') = next_var_rename r2 ssa' na' in
     let mov_out = wl_Move 1 [(r2',0);(r1',6)] in
     (wl_Seq mov_in (wl_Seq (wl_Inst (asm_Arith (LongMul 6 0 0 4))) mov_out):(A)wl_prog,
      ssa'',na'')`;
  `ssa_cc_trans_inst (asm_Arith (LongDiv r1 r2 r3 r4 r5):(A)inst) (ssa:num spt) (na:num) =
     let r3' = option_lookup ssa r3 in
     let r4' = option_lookup ssa r4 in
     let r5' = option_lookup ssa r5 in
     let mov_in = wl_Move 1 [(6,r3');(0,r4')] in
     let (r2',ssa',na') = next_var_rename r2 ssa na in
     let (r1',ssa'',na'') = next_var_rename r1 ssa' na' in
     let mov_out = wl_Move 1 [(r2',6);(r1',0)] in
     (wl_Seq mov_in (wl_Seq (wl_Inst (asm_Arith (LongDiv 0 6 6 0 r5'))) mov_out):
        (A)wl_prog,ssa'',na'')`;
  `ssa_cc_trans_inst (Mem asm_Load r (Addr a (w:A word))) (ssa:num spt) (na:num) =
     let a' = option_lookup ssa a in
     let (r',ssa',na') = next_var_rename r ssa na in
     (wl_Inst (Mem asm_Load r' (Addr a' w)):(A)wl_prog,ssa',na')`;
  `ssa_cc_trans_inst (Mem asm_Store r (Addr a (w:A word))) (ssa:num spt) (na:num) =
     let a' = option_lookup ssa a in
     let r' = option_lookup ssa r in
     (wl_Inst (Mem asm_Store r' (Addr a' w)):(A)wl_prog,ssa,na)`;
  `ssa_cc_trans_inst (Mem asm_Load32 r (Addr a (w:A word))) (ssa:num spt) (na:num) =
     let a' = option_lookup ssa a in
     let (r',ssa',na') = next_var_rename r ssa na in
     (wl_Inst (Mem asm_Load32 r' (Addr a' w)):(A)wl_prog,ssa',na')`;
  `ssa_cc_trans_inst (Mem asm_Store32 r (Addr a (w:A word))) (ssa:num spt) (na:num) =
     let a' = option_lookup ssa a in
     let r' = option_lookup ssa r in
     (wl_Inst (Mem asm_Store32 r' (Addr a' w)):(A)wl_prog,ssa,na)`;
  `ssa_cc_trans_inst (Mem Load8 r (Addr a (w:A word))) (ssa:num spt) (na:num) =
     let a' = option_lookup ssa a in
     let (r',ssa',na') = next_var_rename r ssa na in
     (wl_Inst (Mem Load8 r' (Addr a' w)):(A)wl_prog,ssa',na')`;
  `ssa_cc_trans_inst (Mem Store8 r (Addr a (w:A word))) (ssa:num spt) (na:num) =
     let a' = option_lookup ssa a in
     let r' = option_lookup ssa r in
     (wl_Inst (Mem Store8 r' (Addr a' w)):(A)wl_prog,ssa,na)`;
  `ssa_cc_trans_inst (FP (FPLess r f1 f2):(A)inst) (ssa:num spt) (na:num) =
     let (r',ssa',na') = next_var_rename r ssa na in
     (wl_Inst (FP (FPLess r' f1 f2)):(A)wl_prog,ssa',na')`;
  `ssa_cc_trans_inst (FP (FPLessEqual r f1 f2):(A)inst) (ssa:num spt) (na:num) =
     let (r',ssa',na') = next_var_rename r ssa na in
     (wl_Inst (FP (FPLessEqual r' f1 f2)):(A)wl_prog,ssa',na')`;
  `ssa_cc_trans_inst (FP (FPEqual r f1 f2):(A)inst) (ssa:num spt) (na:num) =
     let (r',ssa',na') = next_var_rename r ssa na in
     (wl_Inst (FP (FPEqual r' f1 f2)):(A)wl_prog,ssa',na')`;
  `ssa_cc_trans_inst (FP (FPMovToReg r1 r2 d):(A)inst) (ssa:num spt) (na:num) =
     if dimindex(:A) = 64 then
       let (r1',ssa',na') = next_var_rename r1 ssa na in
       (wl_Inst (FP (FPMovToReg r1' r2 d)):(A)wl_prog,ssa',na')
     else
       let (r1',ssa',na') = next_var_rename r1 ssa na in
       let (r2',ssa'',na'') = next_var_rename r2 ssa' na' in
       (wl_Inst (FP (FPMovToReg r1' r2' d)),ssa'',na'')`;
  `ssa_cc_trans_inst (FP (FPMovFromReg d r1 r2):(A)inst) (ssa:num spt) (na:num) =
     if dimindex(:A) = 64 then
       let r1' = option_lookup ssa r1 in
       (wl_Inst (FP (FPMovFromReg d r1' 0)):(A)wl_prog,ssa,na)
     else
       let r1' = option_lookup ssa r1 in
       let r2' = option_lookup ssa r2 in
       if r1' = r2' then
         let (r2'',ssa',na') = next_var_rename r2 ssa na in
         let mov_in = wl_Move 0 [(r2'',r2')] in
         (wl_Seq mov_in (wl_Inst (FP (FPMovFromReg d r1' r2''))),ssa',na')
       else
         (wl_Inst (FP (FPMovFromReg d r1' r2')),ssa,na)`;
  `ssa_cc_trans_inst (x:(A)inst) (ssa:num spt) (na:num) = (wl_Inst x:(A)wl_prog,ssa,na)`]);;

let ssa_cc_trans_inst_ind = IL2AUX_case_ind ssa_cc_trans_inst_def;;

(*Expressions only ever need to lookup a variable's current ssa map
  so it doesn't need the other parts *)
let ssa_cc_trans_exp_def = sem1aux_def
  `(ssa_cc_trans_exp t (wl_Var num:(A)wl_exp) = wl_Var (option_lookup t num)) /\
   (ssa_cc_trans_exp t (wl_Load exp) = wl_Load (ssa_cc_trans_exp t exp)) /\
   (ssa_cc_trans_exp t (wl_Op wop ls) = wl_Op wop (MAP (ssa_cc_trans_exp t) ls)) /\
   (ssa_cc_trans_exp t (wl_Shift sh exp nexp) =
      wl_Shift sh (ssa_cc_trans_exp t exp) (ssa_cc_trans_exp t nexp)) /\
   (ssa_cc_trans_exp t expr = expr)`;;

(*Attempt to pull out renaming moves
  This takes a current name map and updates the names of all the vars
  Intended for Alloc,Call cutset restoration moves
*)
let list_next_var_rename_move_def = cake_def
  `list_next_var_rename_move ssa n ls =
     let cur_ls = MAP (option_lookup ssa) ls in
     let (new_ls,ssa',n') = list_next_var_rename ls ssa n in
     (wl_Move 0 (ZIP new_ls cur_ls):(A)wl_prog,ssa',n')`;;

(* force the renaming map to send x -> y unless
  x is already remapped *)
let force_rename_def = cake_def
  `(force_rename [] (ssa:num spt) = ssa) /\
   (force_rename (CONS (x,y) xs) ssa = force_rename xs (insert x y ssa))`;;

let mk_prio_def = cake_def
  `mk_prio (el:(A)wl_prog) (er:(A)wl_prog) =
     if el = wl_Skip then SOME (INL one)
     else if er = wl_Skip then SOME (INR one)
     else NONE`;;

(*Generate reconciliation moves from current ssa to target ssa for vars in ns.

  For v IN ns INTER domain cur_ssa: emit a Move from cur_ssa(v) to tgt_ssa(v)
  (skipped if they happen to be the same register).

  For v IN ns with v NOTIN domain cur_ssa: emit nothing. Such v are vacuous
  in strong_locals_rel (ssa_locals_rel ==> v NOTIN domain st.locals), and when
  the enclosing Loop's cut_state reads tgt_ssa(v), it either succeeds
  because v was added to cur_ssa later (so Case 3 in the proof analysis
  applies: position tgt_ssa(v) = v gets moved), or the source cut also
  fails, making the theorem vacuous.*)
let ssa_reconcile_def = cake_def
  `ssa_reconcile cur_ssa tgt_ssa (ns:A spt) =
     let vars = MAP FST (toAList ns) in
     let moves = FILTER (\ab. match ab with (a,b) -> ~(a = b))
       (FLAT (MAP (\v. match lookup v cur_ssa with
                         NONE -> []
                       | SOME cur_v -> [(option_lookup tgt_ssa v,cur_v)]) vars)) in
     if moves = [] then (wl_Skip:(B)wl_prog) else wl_Move 1 moves`;;

(* Loop entry setup: refresh ssa for vars in (names UNION exit_names) so that
   option_lookup ssa_refreshed is INJ on each. For vars already in ssa we
   emit a real Move; for vars not in ssa we allocate fresh ssa entries
   and fake_move-initialise the corresponding target registers. *)
let loop_setup_def = cake_def
  `loop_setup (names:1 spt) (exit_names:1 spt) ssa na =
     let all_vars_ls = MAP FST (toAList (sptree_union names exit_names)) in
     let extend_ls = FILTER (\v. lookup v ssa = NONE) all_vars_ls in
     let refresh_ls = FILTER (\v. IS_SOME (lookup v ssa)) all_vars_ls in
     let (fresh_pos_ls,ssa_ext,na_ext) =
       list_next_var_rename extend_ls ssa na in
     let fake_prog = ITLIST wl_Seq (MAP (\r. fake_move r) fresh_pos_ls)
                       (wl_Skip:(A)wl_prog) in
     let (refresh_mov,ssa_refreshed,na_refreshed) =
       list_next_var_rename_move ssa_ext na_ext refresh_ls in
     (wl_Seq fake_prog refresh_mov,ssa_refreshed,na_refreshed)`;;

(* ssa_cc_trans.  If: we need to merge the ssa results from both branches   *)
(* by unSSA-ing the phi functions (ssa is the copy for both branches, but   *)
(* the second branch continues with na2; original skips are prioritized).   *)
(* Alloc and the other cutset instructions restart the ssa mapping to       *)
(* maintain consistency, starting from the next available stack location    *)
(* (na is an alloc var).  Call: ret_mov restores the cutset; the returning  *)
(* handler and the exception handler are renamed recursively.  Loop:        *)
(* loop_setup refreshes ssa for (names UNION exit_names) before the Loop,   *)
(* establishing INJ on their domains by construction; the body sees ssa     *)
(* restricted to names; lt carries ssa_refreshed (full) for Break/Continue  *)
(* reconciliation.  Break n reconciles the current ssa with the target exit *)
(* ssa, Continue n with the target entry ssa.                               *)
let ssa_cc_trans_def = sem1aux_def_wf
  `MEASURE (\(p:(A)wl_prog,ssa:num spt,na:num,lt:(num spt#1 spt#1 spt)list).
              wl_prog_size (\x:A. 0) p)`
  SEM1AUX_TC_TAC (list_mk_conj
 [`ssa_cc_trans (wl_Skip:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) = (wl_Skip:(A)wl_prog,ssa,na)`;
  `ssa_cc_trans (wl_Move pri ls:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let ls_1 = MAP FST ls in
     let ls_2 = MAP SND ls in
     let ren_ls2 = MAP (option_lookup ssa) ls_2 in
     let (ren_ls1,ssa',na') = list_next_var_rename ls_1 ssa na in
     let force = FILTER (\xy. match xy with (x,y) -> ~MEM x ls_1) (ZIP ls_2 ren_ls1) in
     (wl_Move pri (ZIP ren_ls1 ren_ls2):(A)wl_prog,force_rename force ssa',na')`;
  `ssa_cc_trans (wl_StoreConsts a b c d ws:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let c1 = option_lookup ssa c in
     let d1 = option_lookup ssa d in
     let (d2,ssa',na') = next_var_rename d ssa na in
     let (c2,ssa'',na'') = next_var_rename c ssa' na' in
     let prog = wl_Seq (wl_Move 1 [(4,c1);(6,d1)])
                  (wl_Seq (wl_StoreConsts 0 2 4 6 ws)
                          (wl_Move 1 [(c2,4);(d2,6)])) in
     (prog:(A)wl_prog,ssa'',na'')`;
  `ssa_cc_trans (wl_Inst i:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let (i',ssa',na') = ssa_cc_trans_inst i ssa na in
     (i':(A)wl_prog,ssa',na')`;
  `ssa_cc_trans (wl_Assign num exp:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let exp' = ssa_cc_trans_exp ssa exp in
     let (num',ssa',na') = next_var_rename num ssa na in
     (wl_Assign num' exp':(A)wl_prog,ssa',na')`;
  `ssa_cc_trans (wl_Get num store:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let (num',ssa',na') = next_var_rename num ssa na in
     (wl_Get num' store:(A)wl_prog,ssa',na')`;
  `ssa_cc_trans (wl_Store exp num:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let exp' = ssa_cc_trans_exp ssa exp in
     let num' = option_lookup ssa num in
     (wl_Store exp' num':(A)wl_prog,ssa,na)`;
  `ssa_cc_trans (wl_Seq s1 s2:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let (s1',ssa',na') = ssa_cc_trans s1 ssa na lt in
     let (s2',ssa'',na'') = ssa_cc_trans s2 ssa' na' lt in
     (wl_Seq s1' s2':(A)wl_prog,ssa'',na'')`;
  `ssa_cc_trans (MustTerminate s1:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let (s1',ssa',na') = ssa_cc_trans s1 ssa na lt in
     (MustTerminate s1':(A)wl_prog,ssa':num spt,na':num)`;
  `ssa_cc_trans (wl_If cmp r1 ri e2 e3:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let r1' = option_lookup ssa r1 in
     let ri' = (match ri with Reg r -> Reg (option_lookup ssa r) | Imm v -> Imm v) in
     let (e2',ssa2,na2) = ssa_cc_trans e2 ssa na lt in
     let (e3',ssa3,na3) = ssa_cc_trans e3 ssa na2 lt in
     let prio = mk_prio e2' e3' in
     let (e2_cons,e3_cons,na_fin,ssa_fin) =
       fix_inconsistencies prio ssa2 ssa3 na3 in
     (wl_If cmp r1' ri' (wl_Seq e2' e2_cons) (wl_Seq e3' e3_cons):(A)wl_prog,
      ssa_fin,na_fin)`;
  `ssa_cc_trans (wl_Alloc num numset:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let names_all = sptree_union (FST numset) (SND numset) in
     let ls = MAP FST (toAList names_all) in
     let (stack_mov,ssa',na') = list_next_var_rename_move ssa (na + 2) ls in
     let num' = option_lookup ssa' num in
     let stack_set = apply_nummaps_key (option_lookup ssa') numset in
     let ssa_cut = sptree_inter ssa' names_all in
     let (ret_mov,ssa'',na'') =
       list_next_var_rename_move ssa_cut (na' + 2) ls in
     let prog = wl_Seq stack_mov
                  (wl_Seq (wl_Move 1 [(2,num')])
                  (wl_Seq (wl_Alloc 2 stack_set) ret_mov)) in
     (prog:(A)wl_prog,ssa'',na'')`;
  `ssa_cc_trans (wl_Raise num:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let num' = option_lookup ssa num in
     let mov = wl_Move 1 [(2,num')] in
     (wl_Seq mov (wl_Raise 2):(A)wl_prog,ssa,na)`;
  `ssa_cc_trans (wl_OpCurrHeap b dst src:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let src' = option_lookup ssa src in
     let (dst',ssa',na') = next_var_rename dst ssa na in
     (wl_OpCurrHeap b dst' src':(A)wl_prog,ssa',na')`;
  `ssa_cc_trans (wl_Return num nums:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let num' = option_lookup ssa num in
     let nums' = MAP (option_lookup ssa) nums in
     let rets = list_of_seq (\x. 2 * (x + 1)) (LENGTH nums') in
     let mov = wl_Move 0 (ZIP rets nums') in
     (wl_Seq mov (wl_Return num' rets):(A)wl_prog,ssa,na)`;
  `ssa_cc_trans (wl_Tick:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) = (wl_Tick:(A)wl_prog,ssa,na)`;
  `ssa_cc_trans (wl_Set n exp:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let exp' = ssa_cc_trans_exp ssa exp in
     (wl_Set n exp':(A)wl_prog,ssa,na)`;
  `ssa_cc_trans (wl_LocValue r l1:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let (r',ssa',na') = next_var_rename r ssa na in
     (wl_LocValue r' l1:(A)wl_prog,ssa',na')`;
  `ssa_cc_trans (wl_Install ptr len dptr dlen numset:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let names_all = sptree_union (FST numset) (SND numset) in
     let ls = MAP FST (toAList names_all) in
     let (stack_mov,ssa',na') = list_next_var_rename_move ssa (na + 2) ls in
     let stack_set = apply_nummaps_key (option_lookup ssa') numset in
     let ptr' = option_lookup ssa' ptr in
     let len' = option_lookup ssa' len in
     let dptr' = option_lookup ssa' dptr in
     let dlen' = option_lookup ssa' dlen in
     let ssa_cut = sptree_inter ssa' names_all in
     let (ptr'',ssa'',na'') = next_var_rename ptr ssa_cut (na' + 2) in
     let (ret_mov,ssa''',na''') = list_next_var_rename_move ssa'' na'' ls in
     let prog = wl_Seq stack_mov
                  (wl_Seq (wl_Move 1 [(2,ptr');(4,len')])
                  (wl_Seq (wl_Install 2 4 dptr' dlen' stack_set)
                  (wl_Seq (wl_Move 1 [(ptr'',2)]) ret_mov))) in
     (prog:(A)wl_prog,ssa''',na''')`;
  `ssa_cc_trans (wl_CodeBufferWrite r1 r2:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let r1' = option_lookup ssa r1 in
     let r2' = option_lookup ssa r2 in
     (wl_CodeBufferWrite r1' r2':(A)wl_prog,ssa,na)`;
  `ssa_cc_trans (wl_DataBufferWrite r1 r2:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let r1' = option_lookup ssa r1 in
     let r2' = option_lookup ssa r2 in
     (wl_DataBufferWrite r1' r2':(A)wl_prog,ssa,na)`;
  `ssa_cc_trans (wl_FFI ffi_index ptr1 len1 ptr2 len2 numset:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let names_all = sptree_union (FST numset) (SND numset) in
     let ls = MAP FST (toAList names_all) in
     let (stack_mov,ssa',na') = list_next_var_rename_move ssa (na + 2) ls in
     let stack_set = apply_nummaps_key (option_lookup ssa') numset in
     let cptr1 = option_lookup ssa' ptr1 in
     let clen1 = option_lookup ssa' len1 in
     let cptr2 = option_lookup ssa' ptr2 in
     let clen2 = option_lookup ssa' len2 in
     let ssa_cut = sptree_inter ssa' names_all in
     let (ret_mov,ssa'',na'') =
       list_next_var_rename_move ssa_cut (na' + 2) ls in
     let prog = wl_Seq stack_mov
                  (wl_Seq (wl_Move 1 [(2,cptr1);(4,clen1);(6,cptr2);(8,clen2)])
                  (wl_Seq (wl_FFI ffi_index 2 4 6 8 stack_set) ret_mov)) in
     (prog:(A)wl_prog,ssa'',na'')`;
  `ssa_cc_trans (wl_Call NONE dest args h:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let names = MAP (option_lookup ssa) args in
     let conv_args = list_of_seq (\x. 2 * x) (LENGTH names) in
     let move_args = wl_Move 1 (ZIP conv_args names) in
     let prog = wl_Seq move_args (wl_Call NONE dest conv_args h) in
     (prog:(A)wl_prog,ssa,na)`;
  `ssa_cc_trans (wl_Call (SOME (ret,numset,ret_handler,l1,l2)) dest args h:(A)wl_prog)
     (ssa:num spt) (na:num) (lt:(num spt#1 spt#1 spt)list) =
     let names_all = sptree_union (FST numset) (SND numset) in
     let ls = MAP FST (toAList names_all) in
     let (stack_mov,ssa',na') = list_next_var_rename_move ssa (na + 2) ls in
     let stack_set = apply_nummaps_key (option_lookup ssa') numset in
     let names = MAP (option_lookup ssa) args in
     let conv_args = list_of_seq (\x. 2 * (x + 1)) (LENGTH names) in
     let move_args = wl_Move 1 (ZIP conv_args names) in
     let ssa_cut = sptree_inter ssa' names_all in
     let (ret_mov,ssa'',na'') =
       list_next_var_rename_move ssa_cut (na' + 2) ls in
     let (ret',ssa_2_p,na_2_p) = list_next_var_rename ret ssa'' na'' in
     let (ren_ret_handler,ssa_2,na_2) =
       ssa_cc_trans ret_handler ssa_2_p na_2_p lt in
     let regs = list_of_seq (\x. 2 * (x + 1)) (LENGTH ret) in
     let mov_ret_handler =
       wl_Seq ret_mov (wl_Seq (wl_Move 1 (ZIP ret' regs)) ren_ret_handler) in
     match h with
       NONE ->
         let prog =
           wl_Seq stack_mov (wl_Seq move_args
             (wl_Call (SOME (regs,stack_set,mov_ret_handler,l1,l2))
                dest conv_args NONE)) in
         (prog:(A)wl_prog,ssa_2,na_2)
     | SOME (n,h,l1',l2') ->
         let (n',ssa_3_p,na_3_p) = next_var_rename n ssa'' na_2 in
         let (ren_exc_handler,ssa_3,na_3) = ssa_cc_trans h ssa_3_p na_3_p lt in
         let mov_exc_handler =
           wl_Seq ret_mov (wl_Seq (wl_Move 1 [(n',2)]) ren_exc_handler) in
         let prio = mk_prio mov_ret_handler mov_exc_handler in
         let (ret_cons,exc_cons,na_fin,ssa_fin) =
           fix_inconsistencies prio ssa_2 ssa_3 na_3 in
         let cons_ret_handler = wl_Seq mov_ret_handler ret_cons in
         let cons_exc_handler = wl_Seq mov_exc_handler exc_cons in
         let prog =
           wl_Seq stack_mov (wl_Seq move_args
             (wl_Call (SOME (regs,stack_set,cons_ret_handler,l1,l2))
                dest conv_args (SOME (2,cons_exc_handler,l1',l2')))) in
         (prog,ssa_fin,na_fin)`;
  `ssa_cc_trans (ShareInst op v exp:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let exp' = ssa_cc_trans_exp ssa exp in
     if op = asm_Store \/ op = Store8 \/ op = Store16 \/ op = asm_Store32 then
       (ShareInst op (option_lookup ssa v) exp':(A)wl_prog,ssa,na)
     else
       let (v',ssa',na') = next_var_rename v ssa na in
       (ShareInst op v' exp',ssa',na')`;
  `ssa_cc_trans (wl_Loop names body exit_names:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     let (setup_prog,ssa_refreshed,na_refreshed) =
       loop_setup names exit_names ssa na in
     let ssa_names = apply_nummap_key (option_lookup ssa_refreshed) names in
     let ssa_exit = apply_nummap_key (option_lookup ssa_refreshed) exit_names in
     let ssa_body = sptree_inter ssa_refreshed names in
     let (body',ssa',na') =
       ssa_cc_trans body ssa_body na_refreshed
         (CONS (ssa_refreshed,names,exit_names) lt) in
     let back_moves = ssa_reconcile ssa' ssa_refreshed names in
     let body_final = if back_moves = wl_Skip then body'
                      else wl_Seq body' back_moves in
     (wl_Seq setup_prog (wl_Loop ssa_names body_final ssa_exit):(A)wl_prog,
      sptree_inter ssa_refreshed exit_names,na':num)`;
  `ssa_cc_trans (wl_Break n:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     match oEL n lt with
       NONE -> (wl_Break n:(A)wl_prog,ssa,na)
     | SOME (tgt_ssa,names,exit_names) ->
         let moves = ssa_reconcile ssa tgt_ssa exit_names in
         ((if moves = wl_Skip then wl_Break n else wl_Seq moves (wl_Break n)),ssa,na)`;
  `ssa_cc_trans (wl_Continue n:(A)wl_prog) (ssa:num spt) (na:num)
     (lt:(num spt#1 spt#1 spt)list) =
     match oEL n lt with
       NONE -> (wl_Continue n:(A)wl_prog,ssa,na)
     | SOME (tgt_ssa,names,exit_names) ->
         let moves = ssa_reconcile ssa tgt_ssa names in
         ((if moves = wl_Skip then wl_Continue n else wl_Seq moves (wl_Continue n)),
          ssa,na)`]);;

let ssa_cc_trans_ind = cake_ind "ssa_cc_trans";;

(*Recursively applying colours to a program*)

let apply_colour_exp_def = sem1aux_def
  `(apply_colour_exp f (wl_Var num:(A)wl_exp) = wl_Var (f num)) /\
   (apply_colour_exp f (wl_Load exp) = wl_Load (apply_colour_exp f exp)) /\
   (apply_colour_exp f (wl_Op wop ls) = wl_Op wop (MAP (apply_colour_exp f) ls)) /\
   (apply_colour_exp f (wl_Shift sh exp nexp) =
      wl_Shift sh (apply_colour_exp f exp) (apply_colour_exp f nexp)) /\
   (apply_colour_exp f expr = expr)`;;
let apply_colour_exp_ind = cake_ind "apply_colour_exp";;
let _ = cake_add_simps [apply_colour_exp_def];;

let apply_colour_imm_def = sem1aux_def
  `(apply_colour_imm f (Reg n:(A)reg_imm) = Reg (f n)) /\
   (apply_colour_imm f (x:(A)reg_imm) = x)`;;
let _ = cake_add_simps [apply_colour_imm_def];;

(* Catchall -- for future instructions to be added *)
let apply_colour_inst_def = sem1aux_def
  `(apply_colour_inst f (asm_Skip:(A)inst) = asm_Skip) /\
   (apply_colour_inst f (asm_Const reg (w:A word)) = asm_Const (f reg) w) /\
   (apply_colour_inst f (asm_Arith (Binop bop r1 r2 ri):(A)inst) =
      asm_Arith (Binop bop (f r1) (f r2) (apply_colour_imm f ri))) /\
   (apply_colour_inst f (asm_Arith (asm_Shift shift r1 r2 ri)) =
      asm_Arith (asm_Shift shift (f r1) (f r2) (apply_colour_imm f ri))) /\
   (apply_colour_inst f (asm_Arith (asm_Div r1 r2 r3)) =
      asm_Arith (asm_Div (f r1) (f r2) (f r3))) /\
   (apply_colour_inst f (asm_Arith (asm_AddCarry r1 r2 r3 r4)) =
      asm_Arith (asm_AddCarry (f r1) (f r2) (f r3) (f r4))) /\
   (apply_colour_inst f (asm_Arith (AddOverflow r1 r2 r3 r4)) =
      asm_Arith (AddOverflow (f r1) (f r2) (f r3) (f r4))) /\
   (apply_colour_inst f (asm_Arith (SubOverflow r1 r2 r3 r4)) =
      asm_Arith (SubOverflow (f r1) (f r2) (f r3) (f r4))) /\
   (apply_colour_inst f (asm_Arith (LongMul r1 r2 r3 r4)) =
      asm_Arith (LongMul (f r1) (f r2) (f r3) (f r4))) /\
   (apply_colour_inst f (asm_Arith (LongDiv r1 r2 r3 r4 r5)) =
      asm_Arith (LongDiv (f r1) (f r2) (f r3) (f r4) (f r5))) /\
   (apply_colour_inst f (Mem asm_Load r (Addr a w)) = Mem asm_Load (f r) (Addr (f a) w)) /\
   (apply_colour_inst f (Mem asm_Store r (Addr a w)) =
      Mem asm_Store (f r) (Addr (f a) w)) /\
   (apply_colour_inst f (Mem asm_Load32 r (Addr a w)) =
      Mem asm_Load32 (f r) (Addr (f a) w)) /\
   (apply_colour_inst f (Mem asm_Store32 r (Addr a w)) =
      Mem asm_Store32 (f r) (Addr (f a) w)) /\
   (apply_colour_inst f (Mem Load8 r (Addr a w)) = Mem Load8 (f r) (Addr (f a) w)) /\
   (apply_colour_inst f (Mem Store8 r (Addr a w)) = Mem Store8 (f r) (Addr (f a) w)) /\
   (apply_colour_inst f (FP (FPLess r f1 f2)) = FP (FPLess (f r) f1 f2)) /\
   (apply_colour_inst f (FP (FPLessEqual r f1 f2)) = FP (FPLessEqual (f r) f1 f2)) /\
   (apply_colour_inst f (FP (FPEqual r f1 f2)) = FP (FPEqual (f r) f1 f2)) /\
   (apply_colour_inst f (FP (FPMovToReg r1 r2 d)) = FP (FPMovToReg (f r1) (f r2) d)) /\
   (apply_colour_inst f (FP (FPMovFromReg d r1 r2)) =
      FP (FPMovFromReg d (f r1) (f r2))) /\
   (apply_colour_inst f x = x)`;;
let _ = cake_add_simps [apply_colour_inst_def];;

let apply_colour_def = sem1aux_def_wf
  `MEASURE (\(f:num->num,p:(A)wl_prog). wl_prog_size (\x:A. 0) p)`
  SEM1AUX_TC_TAC (list_mk_conj
 [`(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog) f (wl_Skip:(A)wl_prog) = wl_Skip`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog) f (wl_Move pri ls:(A)wl_prog) =
     wl_Move pri (ZIP (MAP (f o FST) ls) (MAP (f o SND) ls))`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog)
      f (wl_Inst i:(A)wl_prog) = wl_Inst (apply_colour_inst f i)`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog) f (wl_Assign num exp:(A)wl_prog) =
     wl_Assign (f num) (apply_colour_exp f exp)`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog)
      f (wl_Get num store:(A)wl_prog) = wl_Get (f num) store`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog) f (wl_Store exp num:(A)wl_prog) =
     wl_Store (apply_colour_exp f exp) (f num)`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog) f (wl_Call ret dest args h:(A)wl_prog) =
     let ret = (match ret with
                  NONE -> NONE
                | SOME (vs,cutset,ret_handler,l1,l2) ->
                    SOME (MAP f vs,apply_nummaps_key f cutset,
                          apply_colour f ret_handler,l1,l2)) in
     let args = MAP f args in
     let h = (match h with
                NONE -> NONE
              | SOME (v,prog,l1,l2) -> SOME (f v,apply_colour f prog,l1,l2)) in
     wl_Call ret dest args h`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog) f (wl_Seq s1 s2:(A)wl_prog) =
     wl_Seq (apply_colour f s1) (apply_colour f s2)`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog)
      f (MustTerminate s1:(A)wl_prog) = MustTerminate (apply_colour f s1)`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog) f (wl_If cmp r1 ri e2 e3:(A)wl_prog) =
     wl_If cmp (f r1) (apply_colour_imm f ri) (apply_colour f e2) (apply_colour f e3)`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog) f (wl_Install r1 r2 r3 r4 numset:(A)wl_prog) =
     wl_Install (f r1) (f r2) (f r3) (f r4) (apply_nummaps_key f numset)`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog) f (wl_CodeBufferWrite r1 r2:(A)wl_prog) =
     wl_CodeBufferWrite (f r1) (f r2)`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog) f (wl_DataBufferWrite r1 r2:(A)wl_prog) =
     wl_DataBufferWrite (f r1) (f r2)`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog)
      f (wl_FFI ffi_index ptr1 len1 ptr2 len2 numset:(A)wl_prog) =
     wl_FFI ffi_index (f ptr1) (f len1) (f ptr2) (f len2) (apply_nummaps_key f numset)`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog)
      f (wl_LocValue r l1:(A)wl_prog) = wl_LocValue (f r) l1`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog) f (wl_Alloc num numset:(A)wl_prog) =
     wl_Alloc (f num) (apply_nummaps_key f numset)`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog) f (wl_StoreConsts a b c d ws:(A)wl_prog) =
     wl_StoreConsts (f a) (f b) (f c) (f d) ws`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog)
      f (wl_Raise num:(A)wl_prog) = wl_Raise (f num)`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog)
      f (wl_Return num1 nums:(A)wl_prog) = wl_Return (f num1) (MAP f nums)`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog) f (wl_Tick:(A)wl_prog) = wl_Tick`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog)
      f (wl_Set n exp:(A)wl_prog) = wl_Set n (apply_colour_exp f exp)`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog)
      f (wl_OpCurrHeap b n1 n2:(A)wl_prog) = wl_OpCurrHeap b (f n1) (f n2)`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog) f (ShareInst op v exp:(A)wl_prog) =
     ShareInst op (f v) (apply_colour_exp f exp)`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog) f (wl_Loop names body exit_names:(A)wl_prog) =
     wl_Loop (apply_nummap_key f names) (apply_colour f body)
             (apply_nummap_key f exit_names)`;
  `(apply_colour:(num->num)->(A)wl_prog->(A)wl_prog) f (p:(A)wl_prog) = p`]);;
let apply_colour_ind = cake_ind "apply_colour";;
let _ = cake_add_simps [apply_colour_def];;

(* Liveness Analysis*)

(*Writes made by any inst as a sptree*)
let get_writes_inst_def = sem1aux_def
  `(get_writes_inst (asm_Const reg (w:A word)) = insert reg one LN) /\
   (get_writes_inst (asm_Arith (Binop bop r1 r2 ri):(A)inst) = insert r1 one LN) /\
   (get_writes_inst (asm_Arith (asm_Shift shift r1 r2 ri)) = insert r1 one LN) /\
   (get_writes_inst (asm_Arith (asm_Div r1 r2 r3)) = insert r1 one LN) /\
   (get_writes_inst (asm_Arith (asm_AddCarry r1 r2 r3 r4)) =
      insert r4 one (insert r1 one LN)) /\
   (get_writes_inst (asm_Arith (AddOverflow r1 r2 r3 r4)) =
      insert r4 one (insert r1 one LN)) /\
   (get_writes_inst (asm_Arith (SubOverflow r1 r2 r3 r4)) =
      insert r4 one (insert r1 one LN)) /\
   (get_writes_inst (asm_Arith (LongMul r1 r2 r3 r4)) =
      insert r2 one (insert r1 one LN)) /\
   (get_writes_inst (asm_Arith (LongDiv r1 r2 r3 r4 r5)) =
      insert r2 one (insert r1 one LN)) /\
   (get_writes_inst (Mem asm_Load r (Addr a w)) = insert r one LN) /\
   (get_writes_inst (Mem asm_Load32 r (Addr a w)) = insert r one LN) /\
   (get_writes_inst (Mem Load8 r (Addr a w)) = insert r one LN) /\
   (get_writes_inst (FP (FPLess r f1 f2)) = insert r one LN) /\
   (get_writes_inst (FP (FPLessEqual r f1 f2)) = insert r one LN) /\
   (get_writes_inst (FP (FPEqual r f1 f2)) = insert r one LN) /\
   (get_writes_inst (FP (FPMovToReg r1 r2 d):(A)inst) =
      if dimindex(:A) = 64 then insert r1 one LN
      else insert r2 one (insert r1 one LN)) /\
   (get_writes_inst (inst:(A)inst) = LN)`;;

(*Liveness for instructions, follows liveness equations
  live-sets are num_sets a.k.a. unit-sptrees*)
(* (AddCarry: r4 is live anyway; the catch-all is for future instructions) *)
let get_live_inst_def = sem1aux_def
  `(get_live_inst (asm_Skip:(A)inst) (live:1 spt) = live) /\
   (get_live_inst (asm_Const reg (w:A word)) live = delete reg live) /\
   (get_live_inst (asm_Arith (Binop bop r1 r2 ri):(A)inst) live =
      match ri with
        Reg r3 -> insert r2 one (insert r3 one (delete r1 live))
      | _ -> insert r2 one (delete r1 live)) /\
   (get_live_inst (asm_Arith (asm_Shift shift r1 r2 ri)) live =
      match ri with
        Reg r3 -> insert r2 one (insert r3 one (delete r1 live))
      | _ -> insert r2 one (delete r1 live)) /\
   (get_live_inst (asm_Arith (asm_Div r1 r2 r3)) live =
      insert r3 one (insert r2 one (delete r1 live))) /\
   (get_live_inst (asm_Arith (asm_AddCarry r1 r2 r3 r4)) live =
      insert r4 one (insert r3 one (insert r2 one (delete r1 live)))) /\
   (get_live_inst (asm_Arith (AddOverflow r1 r2 r3 r4)) live =
      insert r3 one (insert r2 one (delete r4 (delete r1 live)))) /\
   (get_live_inst (asm_Arith (SubOverflow r1 r2 r3 r4)) live =
      insert r3 one (insert r2 one (delete r4 (delete r1 live)))) /\
   (get_live_inst (asm_Arith (LongMul r1 r2 r3 r4)) live =
      insert r4 one (insert r3 one (delete r2 (delete r1 live)))) /\
   (get_live_inst (asm_Arith (LongDiv r1 r2 r3 r4 r5)) live =
      insert r5 one (insert r4 one (insert r3 one (delete r2 (delete r1 live))))) /\
   (get_live_inst (Mem asm_Load r (Addr a w)) live = insert a one (delete r live)) /\
   (get_live_inst (Mem asm_Store r (Addr a w)) live = insert a one (insert r one live)) /\
   (get_live_inst (Mem asm_Load32 r (Addr a w)) live = insert a one (delete r live)) /\
   (get_live_inst (Mem asm_Store32 r (Addr a w)) live =
      insert a one (insert r one live)) /\
   (get_live_inst (Mem Load8 r (Addr a w)) live = insert a one (delete r live)) /\
   (get_live_inst (Mem Store8 r (Addr a w)) live = insert a one (insert r one live)) /\
   (get_live_inst (FP (FPLess r f1 f2)) live = delete r live) /\
   (get_live_inst (FP (FPLessEqual r f1 f2)) live = delete r live) /\
   (get_live_inst (FP (FPEqual r f1 f2)) live = delete r live) /\
   (get_live_inst (FP (FPMovToReg r1 r2 d):(A)inst) live =
      if dimindex(:A) = 64 then delete r1 live
      else delete r1 (delete r2 live)) /\
   (get_live_inst (FP (FPMovFromReg d r1 r2):(A)inst) live =
      if dimindex(:A) = 64 then insert r1 one live
      else insert r2 one (insert r1 one live)) /\
   (get_live_inst (x:(A)inst) live = live)`;;

let big_union_def = cake_def
  `big_union (ls:(A spt)list) = ITLIST (\x y. sptree_union x y) ls LN`;;

let get_live_exp_def = sem1aux_def
  `(get_live_exp (wl_Var num:(A)wl_exp) = insert num one LN) /\
   (get_live_exp (wl_Load exp) = get_live_exp exp) /\
   (get_live_exp (wl_Op wop ls) = big_union (MAP get_live_exp ls)) /\
   (get_live_exp (wl_Shift sh exp nexp) =
      sptree_union (get_live_exp exp) (get_live_exp nexp)) /\
   (get_live_exp expr = LN)`;;
let get_live_exp_ind = cake_ind "get_live_exp";;

(* HOL4: numset_list_insert *)
let word_alloc_numset_list_insert_def = cake_def
  `(word_alloc_numset_list_insert [] (t:1 spt) = t) /\
   (word_alloc_numset_list_insert (CONS x xs) t =
      insert x one (word_alloc_numset_list_insert xs t))`;;

(* get_live.  Move: all SNDs are read and all FSTs are written.  Assign:    *)
(* num is written, exp is read.  Store: everything is read.  Seq: find the  *)
(* liveset just before s2, which is the input liveset to s1.  If: get the   *)
(* livesets for e2 and e3, union them, add the if variable, then pass the   *)
(* resulting liveset upwards.  Loop: entry-live is names (for cut_state);   *)
(* the body's entry-live must be covered by the cut state (domain names),   *)
(* handled via strong_locals_rel extension at proof time; Break/Continue    *)
(* handle exit_names/names via lt (exit_names / names of the enclosing Loop *)
(* at nesting level n).  Call: the cut-set must be live, args input must be *)
(* live; for tail calls, there shouldn't be a liveset since control flow    *)
(* will never return into the same instance; otherwise, both args and       *)
(* cutsets are live.  (The second StoreConsts clause is HOL4's: it is       *)
(* shadowed by the first.)                                                  *)
let get_live_def = sem1aux_def_wf
  `MEASURE (\(p:(A)wl_prog,live:1 spt,lt:(1 spt#1 spt)list). wl_prog_size (\x:A. 0) p)`
  SEM1AUX_TC_TAC (list_mk_conj
 [`(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_Skip:(A)wl_prog) (live:1 spt) (lt:(1 spt#1 spt)list) = live`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_Move pri ls:(A)wl_prog) (live:1 spt) (lt:(1 spt#1 spt)list) =
     let killed = ITLIST delete (MAP FST ls) live in
     word_alloc_numset_list_insert (MAP SND ls) killed`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_Inst i:(A)wl_prog) (live:1 spt) (lt:(1 spt#1 spt)list) =
     get_live_inst i live`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_Assign num exp:(A)wl_prog) (live:1 spt) (lt:(1 spt#1 spt)list) =
     let sub = get_live_exp exp in
     sptree_union sub (delete num live)`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_Get num store:(A)wl_prog) (live:1 spt) (lt:(1 spt#1 spt)list) =
     delete num live`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_Store exp num:(A)wl_prog) (live:1 spt) (lt:(1 spt#1 spt)list) =
     insert num one (sptree_union (get_live_exp exp) live)`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_Seq s1 s2:(A)wl_prog) (live:1 spt) (lt:(1 spt#1 spt)list) =
     get_live s1 (get_live s2 live lt) lt`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (MustTerminate s1:(A)wl_prog) (live:1 spt) (lt:(1 spt#1 spt)list) =
     get_live s1 live lt`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_If cmp r1 ri e2 e3:(A)wl_prog) (live:1 spt) (lt:(1 spt#1 spt)list) =
     let e2_live = get_live e2 live lt in
     let e3_live = get_live e3 live lt in
     let union_live = sptree_union e2_live e3_live in
     match ri with
       Reg r2 -> insert r2 one (insert r1 one union_live)
     | _ -> insert r1 one union_live`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_Alloc num numset:(A)wl_prog) (live:1 spt) (lt:(1 spt#1 spt)list) =
     insert num one (sptree_union (FST numset) (SND numset))`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_StoreConsts a b c d ws:(A)wl_prog) (live:1 spt)
     (lt:(1 spt#1 spt)list) =
     insert c one (insert d one (delete a (delete b live)))`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_Install r1 r2 r3 r4 numset:(A)wl_prog) (live:1 spt)
     (lt:(1 spt#1 spt)list) =
     list_insert [r1;r2;r3;r4] (sptree_union (FST numset) (SND numset))`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_CodeBufferWrite r1 r2:(A)wl_prog) (live:1 spt)
     (lt:(1 spt#1 spt)list) = list_insert [r1;r2] live`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_DataBufferWrite r1 r2:(A)wl_prog) (live:1 spt)
     (lt:(1 spt#1 spt)list) = list_insert [r1;r2] live`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_FFI ffi_index ptr1 len1 ptr2 len2 numset:(A)wl_prog) (live:1 spt)
     (lt:(1 spt#1 spt)list) =
     insert ptr1 one (insert len1 one
       (insert ptr2 one (insert len2 one (sptree_union (FST numset) (SND numset)))))`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_StoreConsts a b c d ws:(A)wl_prog) (live:1 spt)
     (lt:(1 spt#1 spt)list) = insert c one (insert d one live)`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_Raise num:(A)wl_prog) (live:1 spt) (lt:(1 spt#1 spt)list) =
     insert num one live`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_Return num1 nums:(A)wl_prog) (live:1 spt) (lt:(1 spt#1 spt)list) =
     insert num1 one (word_alloc_numset_list_insert nums live)`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_Tick:(A)wl_prog) (live:1 spt) (lt:(1 spt#1 spt)list) = live`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_LocValue r l1:(A)wl_prog) (live:1 spt) (lt:(1 spt#1 spt)list) =
     delete r live`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_Set n exp:(A)wl_prog) (live:1 spt) (lt:(1 spt#1 spt)list) =
     sptree_union (get_live_exp exp) live`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_OpCurrHeap b n1 n2:(A)wl_prog) (live:1 spt) (lt:(1 spt#1 spt)list) =
     insert n2 one (delete n1 live)`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (ShareInst mop v exp:(A)wl_prog) (live:1 spt) (lt:(1 spt#1 spt)list) =
     let sub = get_live_exp exp in
     if mop = asm_Store \/ mop = Store8 \/ mop = Store16 \/ mop = asm_Store32
     then sptree_union sub (insert v one live)
     else sptree_union sub (delete v live)`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_Loop names body exit_names:(A)wl_prog) (live:1 spt)
     (lt:(1 spt#1 spt)list) = names`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_Break n:(A)wl_prog) (live:1 spt) (lt:(1 spt#1 spt)list) =
     match oEL n lt with
       NONE -> LN
     | SOME (names,exit_names) -> exit_names`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_Continue n:(A)wl_prog) (live:1 spt) (lt:(1 spt#1 spt)list) =
     match oEL n lt with
       NONE -> LN
     | SOME (names,exit_names) -> names`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_Call NONE dest args h:(A)wl_prog) (live:1 spt)
     (lt:(1 spt#1 spt)list) = word_alloc_numset_list_insert args LN`;
  `(get_live:(A)wl_prog->1 spt->(1 spt#1 spt)list->1 spt)
      (wl_Call (SOME (_,cutset,_)) dest args h:(A)wl_prog) (live:1 spt)
     (lt:(1 spt#1 spt)list) =
     sptree_union (sptree_union (FST cutset) (SND cutset)) (word_alloc_numset_list_insert args LN)`]);;

(* Dead instruction removal; catchall -- for other instructions *)
let remove_dead_inst_def = sem1aux_def
  `(remove_dead_inst (asm_Skip:(A)inst) (live:1 spt) <=> T) /\
   (remove_dead_inst (asm_Const reg (w:A word)) live <=> lookup reg live = NONE) /\
   (remove_dead_inst (asm_Arith (Binop bop r1 r2 ri):(A)inst) live <=>
      lookup r1 live = NONE) /\
   (remove_dead_inst (asm_Arith (asm_Shift shift r1 r2 n)) live <=>
      lookup r1 live = NONE) /\
   (remove_dead_inst (asm_Arith (asm_Div r1 r2 r3)) live <=> lookup r1 live = NONE) /\
   (remove_dead_inst (asm_Arith (asm_AddCarry r1 r2 r3 r4)) live <=>
      lookup r1 live = NONE /\ lookup r4 live = NONE) /\
   (remove_dead_inst (asm_Arith (AddOverflow r1 r2 r3 r4)) live <=>
      lookup r1 live = NONE /\ lookup r4 live = NONE) /\
   (remove_dead_inst (asm_Arith (SubOverflow r1 r2 r3 r4)) live <=>
      lookup r1 live = NONE /\ lookup r4 live = NONE) /\
   (remove_dead_inst (asm_Arith (LongMul r1 r2 r3 r4)) live <=>
      lookup r1 live = NONE /\ lookup r2 live = NONE) /\
   (remove_dead_inst (asm_Arith (LongDiv r1 r2 r3 r4 r5)) live <=>
      lookup r1 live = NONE /\ lookup r2 live = NONE) /\
   (remove_dead_inst (Mem asm_Load r (Addr a w)) live <=> lookup r live = NONE) /\
   (remove_dead_inst (Mem asm_Load32 r (Addr a w)) live <=> lookup r live = NONE) /\
   (remove_dead_inst (Mem Load8 r (Addr a w)) live <=> lookup r live = NONE) /\
   (remove_dead_inst (FP (FPLess r f1 f2)) live <=> lookup r live = NONE) /\
   (remove_dead_inst (FP (FPLessEqual r f1 f2)) live <=> lookup r live = NONE) /\
   (remove_dead_inst (FP (FPEqual r f1 f2)) live <=> lookup r live = NONE) /\
   (remove_dead_inst (FP (FPMovToReg r1 r2 d):(A)inst) live <=>
      if dimindex(:A) = 64 then lookup r1 live = NONE
      else lookup r1 live = NONE /\ lookup r2 live = NONE) /\
   (remove_dead_inst (x:(A)inst) live <=> F)`;;

(* Delete dead code, w.r.t. a set of live variables.
  The liveset is a tuple (live,nlive):
  - live is an sptree of live variables
  - nlive is a list of globals which are NOT live

  This code is written assuming flat_exp_conventions,
    so many trivial cases are omitted.
  (MustTerminate: this can technically be optimized away if it was a Skip,
  but MustTerminate should never wrap completely dead code.  The ShareInst
  Load instructions are not removed: they produce an ffi event even if the
  variable is not in the live set.  In the cases after the top level Call
  either nlive is returned unchanged or [] because of control flow.  Loop:
  conservative, nlive is reset to [] at the Loop boundary so all stores are
  treated as live across loop iterations (otherwise backward nlive analysis
  could eliminate Sets whose overwrites live on a later iteration); cost: no
  store-DCE across Loops; ordinary locals-DCE inside the body still applies.
  Break/Continue reset nlive to [] because they jump past whatever follows,
  so store-DCE cannot propagate dead-set info across them.)
*)
let remove_dead_def = sem1aux_def_wf
  `MEASURE (\(p:(A)wl_prog,live:1 spt,nlive:store_name list,lt:(1 spt#1 spt)list).
              wl_prog_size (\x:A. 0) p)`
  SEM1AUX_TC_TAC (list_mk_conj
 [`(remove_dead:(A)wl_prog->1 spt->store_name list->(1 spt#1 spt)list->(A)wl_prog#1 spt#store_name list)
      (wl_Move pri ls:(A)wl_prog) (live:1 spt) (nlive:store_name list)
     (lt:(1 spt#1 spt)list) =
     let ls = FILTER (\xy. match xy with (x,y) -> lookup x live = SOME one) ls in
     if ls = [] then (wl_Skip:(A)wl_prog,live,nlive)
     else
       let killed = ITLIST delete (MAP FST ls) live in
       (wl_Move pri ls,word_alloc_numset_list_insert (MAP SND ls) killed,nlive)`;
  `(remove_dead:(A)wl_prog->1 spt->store_name list->(1 spt#1 spt)list->(A)wl_prog#1 spt#store_name list)
      (wl_Inst i:(A)wl_prog) (live:1 spt) (nlive:store_name list)
     (lt:(1 spt#1 spt)list) =
     if remove_dead_inst i live then (wl_Skip:(A)wl_prog,live,nlive)
     else (wl_Inst i,get_live_inst i live,nlive)`;
  `(remove_dead:(A)wl_prog->1 spt->store_name list->(1 spt#1 spt)list->(A)wl_prog#1 spt#store_name list)
      (wl_Get num store:(A)wl_prog) (live:1 spt) (nlive:store_name list)
     (lt:(1 spt#1 spt)list) =
     if lookup num live = NONE then (wl_Skip:(A)wl_prog,live,nlive)
     else (wl_Get num store,delete num live,FILTER (\s. ~(store = s)) nlive)`;
  `(remove_dead:(A)wl_prog->1 spt->store_name list->(1 spt#1 spt)list->(A)wl_prog#1 spt#store_name list)
      (wl_OpCurrHeap b num src:(A)wl_prog) (live:1 spt)
     (nlive:store_name list) (lt:(1 spt#1 spt)list) =
     if lookup num live = NONE then (wl_Skip:(A)wl_prog,live,nlive)
     else (wl_OpCurrHeap b num src,insert src one (delete num live),
           FILTER (\s. ~(CurrHeap = s)) nlive)`;
  `(remove_dead:(A)wl_prog->1 spt->store_name list->(1 spt#1 spt)list->(A)wl_prog#1 spt#store_name list)
      (wl_LocValue r l1:(A)wl_prog) (live:1 spt) (nlive:store_name list)
     (lt:(1 spt#1 spt)list) =
     if lookup r live = NONE then (wl_Skip:(A)wl_prog,live,nlive)
     else (wl_LocValue r l1,delete r live,nlive)`;
  `(remove_dead:(A)wl_prog->1 spt->store_name list->(1 spt#1 spt)list->(A)wl_prog#1 spt#store_name list)
      (wl_Set store_name exp:(A)wl_prog) (live:1 spt)
     (nlive:store_name list) (lt:(1 spt#1 spt)list) =
     match exp with
       wl_Var r ->
         if MEM store_name nlive then (wl_Skip:(A)wl_prog,live,nlive)
         else (wl_Set store_name (wl_Var r),insert r one live,CONS store_name nlive)
     | _ ->
         let prog = wl_Set store_name exp in
         (prog,get_live prog live lt,[])`;
  `(remove_dead:(A)wl_prog->1 spt->store_name list->(1 spt#1 spt)list->(A)wl_prog#1 spt#store_name list)
      (wl_Seq s1 s2:(A)wl_prog) (live:1 spt) (nlive:store_name list)
     (lt:(1 spt#1 spt)list) =
     let (s2,s2live,s2nlive) = remove_dead s2 live nlive lt in
     let (s1,s1live,s1nlive) = remove_dead s1 s2live s2nlive lt in
     let prog = if s1 = wl_Skip then s2
                else if s2 = wl_Skip then s1
                else wl_Seq s1 s2 in
     (prog,s1live,s1nlive)`;
  `(remove_dead:(A)wl_prog->1 spt->store_name list->(1 spt#1 spt)list->(A)wl_prog#1 spt#store_name list)
      (MustTerminate s1:(A)wl_prog) (live:1 spt) (nlive:store_name list)
     (lt:(1 spt#1 spt)list) =
     let (s1,s1live,s1nlive) = remove_dead s1 live nlive lt in
     (MustTerminate s1,s1live,s1nlive)`;
  `(remove_dead:(A)wl_prog->1 spt->store_name list->(1 spt#1 spt)list->(A)wl_prog#1 spt#store_name list)
      (wl_If cmp r1 ri e2 e3:(A)wl_prog) (live:1 spt)
     (nlive:store_name list) (lt:(1 spt#1 spt)list) =
     let (e2,e2_live,e2_nlive) = remove_dead e2 live nlive lt in
     let (e3,e3_live,e3_nlive) = remove_dead e3 live nlive lt in
     let union_live = sptree_union e2_live e3_live in
     let liveset = (match ri with
                      Reg r2 -> insert r2 one (insert r1 one union_live)
                    | _ -> insert r1 one union_live) in
     let nliveset = FILTER (\s. MEM s e3_nlive) e2_nlive in
     let prog = if e2 = wl_Skip /\ e3 = wl_Skip then wl_Skip
                else wl_If cmp r1 ri e2 e3 in
     (prog,liveset,nliveset)`;
  `(remove_dead:(A)wl_prog->1 spt->store_name list->(1 spt#1 spt)list->(A)wl_prog#1 spt#store_name list)
      (wl_Call (SOME (v,cutsets,ret_handler,l1,l2)) dest args h:(A)wl_prog)
     (live:1 spt) (nlive:store_name list) (lt:(1 spt#1 spt)list) =
     let args_set = word_alloc_numset_list_insert args LN in
     let cutset = sptree_union (FST cutsets) (SND cutsets) in
     let live_set = sptree_union cutset args_set in
     let (ret_handler,_) = remove_dead ret_handler live nlive lt in
     let h = (match h with
                NONE -> NONE
              | SOME (v',prog,l1,l2) ->
                  SOME (v',FST (remove_dead prog live nlive lt),l1,l2)) in
     (wl_Call (SOME (v,cutsets,ret_handler,l1,l2)) dest args h,(live_set,[]))`;
  `(remove_dead:(A)wl_prog->1 spt->store_name list->(1 spt#1 spt)list->(A)wl_prog#1 spt#store_name list)
      (wl_Call NONE a b c:(A)wl_prog) (live:1 spt) (nlive:store_name list)
     (lt:(1 spt#1 spt)list) =
     let prog = wl_Call NONE a b c in
     (prog,get_live prog live lt,[])`;
  `(remove_dead:(A)wl_prog->1 spt->store_name list->(1 spt#1 spt)list->(A)wl_prog#1 spt#store_name list)
      (wl_Alloc a b:(A)wl_prog) (live:1 spt) (nlive:store_name list)
     (lt:(1 spt#1 spt)list) =
     let prog = wl_Alloc a b in
     (prog,get_live prog live lt,[])`;
  `(remove_dead:(A)wl_prog->1 spt->store_name list->(1 spt#1 spt)list->(A)wl_prog#1 spt#store_name list)
      (wl_Raise a:(A)wl_prog) (live:1 spt) (nlive:store_name list)
     (lt:(1 spt#1 spt)list) =
     let prog = wl_Raise a in
     (prog,get_live prog live lt,[])`;
  `(remove_dead:(A)wl_prog->1 spt->store_name list->(1 spt#1 spt)list->(A)wl_prog#1 spt#store_name list)
      (wl_Return a b:(A)wl_prog) (live:1 spt) (nlive:store_name list)
     (lt:(1 spt#1 spt)list) =
     let prog = wl_Return a b in
     (prog,get_live prog live lt,[])`;
  `(remove_dead:(A)wl_prog->1 spt->store_name list->(1 spt#1 spt)list->(A)wl_prog#1 spt#store_name list)
      (wl_Loop names body exit_names:(A)wl_prog) (live:1 spt)
     (nlive:store_name list) (lt:(1 spt#1 spt)list) =
     let lt' = CONS (names,exit_names) lt in
     let (body',_,_) = remove_dead body names [] lt' in
     (wl_Loop names body' exit_names,names,[])`;
  `(remove_dead:(A)wl_prog->1 spt->store_name list->(1 spt#1 spt)list->(A)wl_prog#1 spt#store_name list)
      (wl_Break n:(A)wl_prog) (live:1 spt) (nlive:store_name list)
     (lt:(1 spt#1 spt)list) =
     let prog = wl_Break n in
     (prog,get_live prog live lt,[])`;
  `(remove_dead:(A)wl_prog->1 spt->store_name list->(1 spt#1 spt)list->(A)wl_prog#1 spt#store_name list)
      (wl_Continue n:(A)wl_prog) (live:1 spt) (nlive:store_name list)
     (lt:(1 spt#1 spt)list) =
     let prog = wl_Continue n in
     (prog,get_live prog live lt,[])`;
  `(remove_dead:(A)wl_prog->1 spt->store_name list->(1 spt#1 spt)list->(A)wl_prog#1 spt#store_name list)
      (prog:(A)wl_prog) (live:1 spt) (nlive:store_name list)
     (lt:(1 spt#1 spt)list) = (prog,get_live prog live lt,nlive)`]);;
let remove_dead_ind = cake_ind "remove_dead";;

let remove_dead_prog_def = cake_def
  `remove_dead_prog (prog:(A)wl_prog) = FST (remove_dead prog LN [] [])`;;

(*Single step immediate writes by a prog*)
let get_writes_def = sem1aux_def (list_mk_conj
 [`(get_writes:(A)wl_prog->1 spt)
      (wl_Move pri ls:(A)wl_prog) = word_alloc_numset_list_insert (MAP FST ls) LN`;
  `(get_writes:(A)wl_prog->1 spt) (wl_Inst i:(A)wl_prog) = get_writes_inst i`;
  `(get_writes:(A)wl_prog->1 spt) (wl_Assign num exp:(A)wl_prog) = insert num one LN`;
  `(get_writes:(A)wl_prog->1 spt) (wl_Get num store:(A)wl_prog) = insert num one LN`;
  `(get_writes:(A)wl_prog->1 spt) (wl_LocValue r l1:(A)wl_prog) = insert r one LN`;
  `(get_writes:(A)wl_prog->1 spt) (wl_Install r1 _ _ _ _:(A)wl_prog) = insert r1 one LN`;
  `(get_writes:(A)wl_prog->1 spt) (wl_OpCurrHeap b r1 _:(A)wl_prog) = insert r1 one LN`;
  `(get_writes:(A)wl_prog->1 spt) (wl_StoreConsts a b c d _:(A)wl_prog) =
     insert a one (insert b one (insert c one (insert d one LN)))`;
  `(get_writes:(A)wl_prog->1 spt) (ShareInst asm_Load v _:(A)wl_prog) = insert v one LN`;
  `(get_writes:(A)wl_prog->1 spt) (ShareInst Load8 v _:(A)wl_prog) = insert v one LN`;
  `(get_writes:(A)wl_prog->1 spt) (ShareInst Load16 v _:(A)wl_prog) = insert v one LN`;
  `(get_writes:(A)wl_prog->1 spt) (ShareInst asm_Load32 v _:(A)wl_prog) = insert v one LN`;
  `(get_writes:(A)wl_prog->1 spt) (prog:(A)wl_prog) = LN`]);;

let get_writes_pmatch = prove
 (CASE_TERM
  `!inst:(A)wl_prog.
     get_writes inst =
       match inst with
         wl_Move pri ls -> word_alloc_numset_list_insert (MAP FST ls) LN
       | wl_Inst i -> get_writes_inst i
       | wl_Assign num exp -> insert num one LN
       | wl_Get num store -> insert num one LN
       | wl_LocValue r l1 -> insert r one LN
       | wl_Install r1 _ _ _ _ -> insert r1 one LN
       | wl_OpCurrHeap b r1 _ -> insert r1 one LN
       | wl_StoreConsts a b c d _ ->
           insert a one (insert b one (insert c one (insert d one LN)))
       | ShareInst asm_Load v _ -> insert v one LN
       | ShareInst Load8 v _ -> insert v one LN
       | ShareInst Load16 v _ -> insert v one LN
       | ShareInst asm_Load32 v _ -> insert v one LN
       | prog -> LN`,
  GEN_TAC THEN EVERY_CASE_TAC THEN REWRITE_TAC[get_writes_def]);;

(* Potentially more efficient liveset representation for checking / allocation *)
(* (catchall -- for future instructions to be added)                         *)
let get_delta_inst_def = sem1aux_def
  `(get_delta_inst (asm_Skip:(A)inst) = Delta [] []) /\
   (get_delta_inst (asm_Const reg (w:A word)) = Delta [reg] []) /\
   (get_delta_inst (asm_Arith (Binop bop r1 r2 ri):(A)inst) =
      match ri with Reg r3 -> Delta [r1] [r2;r3] | _ -> Delta [r1] [r2]) /\
   (get_delta_inst (asm_Arith (asm_Shift shift r1 r2 ri)) =
      match ri with Reg r3 -> Delta [r1] [r2;r3] | _ -> Delta [r1] [r2]) /\
   (get_delta_inst (asm_Arith (asm_Div r1 r2 r3)) = Delta [r1] [r3;r2]) /\
   (get_delta_inst (asm_Arith (asm_AddCarry r1 r2 r3 r4)) = Delta [r1;r4] [r4;r3;r2]) /\
   (get_delta_inst (asm_Arith (AddOverflow r1 r2 r3 r4)) = Delta [r1;r4] [r3;r2]) /\
   (get_delta_inst (asm_Arith (SubOverflow r1 r2 r3 r4)) = Delta [r1;r4] [r3;r2]) /\
   (get_delta_inst (asm_Arith (LongMul r1 r2 r3 r4)) = Delta [r1;r2] [r4;r3]) /\
   (get_delta_inst (asm_Arith (LongDiv r1 r2 r3 r4 r5)) = Delta [r1;r2] [r5;r4;r3]) /\
   (get_delta_inst (Mem asm_Load r (Addr a w)) = Delta [r] [a]) /\
   (get_delta_inst (Mem asm_Store r (Addr a w)) = Delta [] [r;a]) /\
   (get_delta_inst (Mem asm_Load32 r (Addr a w)) = Delta [r] [a]) /\
   (get_delta_inst (Mem asm_Store32 r (Addr a w)) = Delta [] [r;a]) /\
   (get_delta_inst (Mem Load8 r (Addr a w)) = Delta [r] [a]) /\
   (get_delta_inst (Mem Store8 r (Addr a w)) = Delta [] [r;a]) /\
   (get_delta_inst (FP (FPLess r f1 f2)) = Delta [r] []) /\
   (get_delta_inst (FP (FPLessEqual r f1 f2)) = Delta [r] []) /\
   (get_delta_inst (FP (FPEqual r f1 f2)) = Delta [r] []) /\
   (get_delta_inst (FP (FPMovToReg r1 r2 d):(A)inst) =
      if dimindex(:A) = 64 then Delta [r1] [] else Delta [r1;r2] []) /\
   (get_delta_inst (FP (FPMovFromReg d r1 r2):(A)inst) =
      if dimindex(:A) = 64 then Delta [] [r1] else Delta [] [r1;r2]) /\
   (get_delta_inst (x:(A)inst) = Delta [] [])`;;

let get_reads_exp_def = sem1aux_def
  `(get_reads_exp (wl_Var num:(A)wl_exp) = [num]) /\
   (get_reads_exp (wl_Load exp) = get_reads_exp exp) /\
   (get_reads_exp (wl_Op wop ls) = FLAT (MAP get_reads_exp ls)) /\
   (get_reads_exp (wl_Shift sh exp nexp) =
      APPEND (get_reads_exp exp) (get_reads_exp nexp)) /\
   (get_reads_exp expr = [])`;;
let get_reads_exp_ind = cake_ind "get_reads_exp";;

(* Loop: names and exit_names; Break n: the exit_names vars must all be     *)
(* live; Continue n: the names vars must all be live; Call: might be        *)
(* inefficient                                                               *)
let get_clash_tree_def = sem1aux_def_wf
  `MEASURE (\(p:(A)wl_prog,lt:(1 spt#1 spt)list). wl_prog_size (\x:A. 0) p)`
  SEM1AUX_TC_TAC (list_mk_conj
 [`(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_Skip:(A)wl_prog) (lt:(1 spt#1 spt)list) = Delta [] []`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_Move pri ls:(A)wl_prog) (lt:(1 spt#1 spt)list) =
     Delta (MAP FST ls) (MAP SND ls)`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_Inst i:(A)wl_prog) (lt:(1 spt#1 spt)list) = get_delta_inst i`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_Assign num exp:(A)wl_prog) (lt:(1 spt#1 spt)list) =
     Delta [num] (get_reads_exp exp)`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_Get num store:(A)wl_prog) (lt:(1 spt#1 spt)list) =
     Delta [num] []`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_Store exp num:(A)wl_prog) (lt:(1 spt#1 spt)list) =
     Delta [] (CONS num (get_reads_exp exp))`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_Seq s1 s2:(A)wl_prog) (lt:(1 spt#1 spt)list) =
     reg_alloc_Seq (get_clash_tree s1 lt) (get_clash_tree s2 lt)`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_If cmp r1 ri e2 e3:(A)wl_prog) (lt:(1 spt#1 spt)list) =
     let e2t = get_clash_tree e2 lt in
     let e3t = get_clash_tree e3 lt in
     match ri with
       Reg r2 -> reg_alloc_Seq (Delta [] [r1;r2]) (reg_alloc_Branch NONE e2t e3t)
     | _ -> reg_alloc_Seq (Delta [] [r1]) (reg_alloc_Branch NONE e2t e3t)`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (MustTerminate s:(A)wl_prog) (lt:(1 spt#1 spt)list) =
     get_clash_tree s lt`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_Alloc num numset:(A)wl_prog) (lt:(1 spt#1 spt)list) =
     reg_alloc_Seq (Delta [] [num]) (reg_alloc_Set (sptree_union (FST numset) (SND numset)))`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_Install r1 r2 r3 r4 numset:(A)wl_prog) (lt:(1 spt#1 spt)list) =
     reg_alloc_Seq (Delta [] [r4;r3;r2;r1])
       (reg_alloc_Seq (reg_alloc_Set (sptree_union (FST numset) (SND numset)))
          (Delta [r1] []))`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_CodeBufferWrite r1 r2:(A)wl_prog) (lt:(1 spt#1 spt)list) =
     Delta [] [r2;r1]`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_DataBufferWrite r1 r2:(A)wl_prog) (lt:(1 spt#1 spt)list) =
     Delta [] [r2;r1]`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_FFI ffi_index ptr1 len1 ptr2 len2 numset:(A)wl_prog)
     (lt:(1 spt#1 spt)list) =
     reg_alloc_Seq (Delta [] [ptr1;len1;ptr2;len2])
       (reg_alloc_Set (sptree_union (FST numset) (SND numset)))`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_Raise num:(A)wl_prog) (lt:(1 spt#1 spt)list) = Delta [] [num]`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_Return num1 nums:(A)wl_prog) (lt:(1 spt#1 spt)list) =
     Delta [] (CONS num1 nums)`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_Tick:(A)wl_prog) (lt:(1 spt#1 spt)list) = Delta [] []`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_LocValue r l1:(A)wl_prog) (lt:(1 spt#1 spt)list) = Delta [r] []`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_Set n exp:(A)wl_prog) (lt:(1 spt#1 spt)list) =
     Delta [] (get_reads_exp exp)`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_OpCurrHeap b dst src:(A)wl_prog) (lt:(1 spt#1 spt)list) =
     Delta [dst] [src]`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_StoreConsts a b c d ws:(A)wl_prog) (lt:(1 spt#1 spt)list) =
     Delta [a;b;c;d] [c;d]`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (ShareInst op v exp:(A)wl_prog) (lt:(1 spt#1 spt)list) =
     if op = asm_Store \/ op = Store8 \/ op = Store16 \/ op = asm_Store32
     then Delta [] (CONS v (get_reads_exp exp))
     else Delta [v] (get_reads_exp exp)`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_Loop names body exit_names:(A)wl_prog) (lt:(1 spt#1 spt)list) =
     reg_alloc_Seq (reg_alloc_Set names)
       (reg_alloc_Seq (reg_alloc_Set exit_names)
         (reg_alloc_Seq (get_clash_tree body (CONS (names,exit_names) lt))
            (reg_alloc_Set names)))`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_Break n:(A)wl_prog) (lt:(1 spt#1 spt)list) =
     match oEL n lt with
       NONE -> reg_alloc_Set LN
     | SOME (names,exit_names) -> reg_alloc_Set exit_names`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_Continue n:(A)wl_prog) (lt:(1 spt#1 spt)list) =
     match oEL n lt with
       NONE -> reg_alloc_Set LN
     | SOME (names,exit_names) -> reg_alloc_Set names`;
  `(get_clash_tree:(A)wl_prog->(1 spt#1 spt)list->clash_tree)
      (wl_Call ret dest args h:(A)wl_prog) (lt:(1 spt#1 spt)list) =
     let args_set = word_alloc_numset_list_insert args LN in
     match ret with
       NONE -> reg_alloc_Set args_set
     | SOME (vs,cutsets,ret_handler,_,_) ->
         let cutset = sptree_union (FST cutsets) (SND cutsets) in
         let live_set = sptree_union cutset args_set in
         let ret_tree = reg_alloc_Seq
                          (reg_alloc_Set (word_alloc_numset_list_insert vs cutset))
                          (get_clash_tree ret_handler lt) in
         match h with
           NONE -> reg_alloc_Seq (reg_alloc_Set live_set) ret_tree
         | SOME (v',prog,_,_) ->
             let handler_tree =
               reg_alloc_Seq (reg_alloc_Set (insert v' one cutset))
                 (get_clash_tree prog lt) in
             reg_alloc_Branch (SOME live_set) ret_tree handler_tree`]);;
let get_clash_tree_ind = cake_ind "get_clash_tree";;

(* Preference edges
  The allocator tries hard to coalesce these edges
*)
let get_prefs_def = sem1aux_def_wf
  `MEASURE (\(p:(A)wl_prog,acc:(num#num#num)list). wl_prog_size (\x:A. 0) p)`
  SEM1AUX_TC_TAC (list_mk_conj
 [`(get_prefs:(A)wl_prog->(num#num#num)list->(num#num#num)list) (wl_Move pri ls:(A)wl_prog) acc =
     APPEND (MAP (\xy. match xy with (x,y) -> (pri,x,y)) ls) acc`;
  `(get_prefs:(A)wl_prog->(num#num#num)list->(num#num#num)list)
      (MustTerminate s1:(A)wl_prog) acc = get_prefs s1 acc`;
  `(get_prefs:(A)wl_prog->(num#num#num)list->(num#num#num)list)
      (wl_Seq s1 s2:(A)wl_prog) acc = get_prefs s1 (get_prefs s2 acc)`;
  `(get_prefs:(A)wl_prog->(num#num#num)list->(num#num#num)list)
      (wl_If cmp num rimm e2 e3:(A)wl_prog) acc =
     get_prefs e2 (get_prefs e3 acc)`;
  `(get_prefs:(A)wl_prog->(num#num#num)list->(num#num#num)list)
      (wl_Call (SOME (v,cutset,ret_handler,l1,l2)) dest args h:(A)wl_prog) acc =
     match h with
       NONE -> get_prefs ret_handler acc
     | SOME (v,prog,l1,l2) -> get_prefs prog (get_prefs ret_handler acc)`;
  `(get_prefs:(A)wl_prog->(num#num#num)list->(num#num#num)list)
      (wl_Loop names body exit_names:(A)wl_prog) acc = get_prefs body acc`;
  `(get_prefs:(A)wl_prog->(num#num#num)list->(num#num#num)list)
      (prog:(A)wl_prog) (acc:(num#num#num)list) = acc`]);;
let get_prefs_ind = cake_ind "get_prefs";;

let get_prefs_pmatch = prove
 (CASE_TERM
  `!(s:(A)wl_prog) acc.
     get_prefs s acc =
       match s with
         wl_Move pri ls -> APPEND (MAP (\xy. match xy with (x,y) -> (pri,x,y)) ls) acc
       | MustTerminate s1 -> get_prefs s1 acc
       | wl_Seq s1 s2 -> get_prefs s1 (get_prefs s2 acc)
       | wl_If cmp num rimm e2 e3 -> get_prefs e2 (get_prefs e3 acc)
       | wl_Call (SOME (v,cutset,ret_handler,l1,l2)) dest args NONE ->
           get_prefs ret_handler acc
       | wl_Call (SOME (v,cutset,ret_handler,l1,l2)) dest args (SOME (_,prog,_,_)) ->
           get_prefs prog (get_prefs ret_handler acc)
       | wl_Loop names body exit_names -> get_prefs body acc
       | prog -> acc`,
  REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN RW[get_prefs_def]);;

(*
  For each var, we collect 5 tuples indicating the number of
  instructions in which it is involved in:
    (lhs const,lhs reg,lhs memory, rhs reg, rhs memory)

  Currently, this just treats FP as a reg instruction

  This is meant to be small and quick to compute, because it has to be applied
  to the entire program just before register allocation, which can be huge.

*)

new_type_abbrev("heu_data",`:num#num#num#num#num`);;

(* HOL4 hides the constant mem here (Parse.hide); HOL Light has none *)

let add1_lhs_const_def = cake_def
  `add1_lhs_const x (t:(heu_data)spt) =
     match lookup x t with
       NONE -> insert x (1,0,0,0,0) t
     | SOME (const,reg,mem,rreg,rmem) -> insert x (const + 1,reg,mem,rreg,rmem) t`;;

let add1_lhs_reg_def = cake_def
  `add1_lhs_reg x (t:(heu_data)spt) =
     match lookup x t with
       NONE -> insert x (0,1,0,0,0) t
     | SOME (const,reg,mem,rreg,rmem) -> insert x (const,reg + 1,mem,rreg,rmem) t`;;

let add1_lhs_mem_def = cake_def
  `add1_lhs_mem x (t:(heu_data)spt) =
     match lookup x t with
       NONE -> insert x (0,0,1,0,0) t
     | SOME (const,reg,mem,rreg,rmem) -> insert x (const,reg,mem + 1,rreg,rmem) t`;;

let add1_rhs_reg_def = cake_def
  `add1_rhs_reg x (t:(heu_data)spt) =
     match lookup x t with
       NONE -> insert x (0,0,0,1,0) t
     | SOME (const,reg,mem,rreg,rmem) -> insert x (const,reg,mem,rreg + 1,rmem) t`;;

let add1_rhs_mem_def = cake_def
  `add1_rhs_mem x (t:(heu_data)spt) =
     match lookup x t with
       NONE -> insert x (0,0,0,0,1) t
     | SOME (const,reg,mem,rreg,rmem) -> insert x (const,reg,mem,rreg,rmem + 1) t`;;

(* r1 := r2 op r3 for Binop and Shift with a register; AddCarry: r1,r4 :=   *)
(* r2,r3,r4; AddOverflow, SubOverflow: r1,r4 := r2,r3; LongMul: r1,r2 :=    *)
(* r3,r4; LongDiv: r1,r2 := r3,r4,r5; catchall -- for future instructions   *)
(* to be added, and all other FP                                            *)
let get_heu_inst_def = sem1aux_def
  `(get_heu_inst (asm_Skip:(A)inst) (tup:(heu_data)spt) = tup) /\
   (get_heu_inst (asm_Const reg (w:A word)) lr = add1_lhs_const reg lr) /\
   (get_heu_inst (asm_Arith (Binop bop r1 r2 ri):(A)inst) lr =
      match ri with
        Reg r3 -> add1_lhs_reg r1 (add1_rhs_reg r3 (add1_rhs_reg r2 lr))
      | _ -> add1_lhs_reg r1 (add1_rhs_reg r2 lr)) /\
   (get_heu_inst (asm_Arith (asm_Shift shift r1 r2 ri)) lr =
      match ri with
        Reg r3 -> add1_lhs_reg r1 (add1_rhs_reg r3 (add1_rhs_reg r2 lr))
      | _ -> add1_lhs_reg r1 (add1_rhs_reg r2 lr)) /\
   (get_heu_inst (asm_Arith (asm_Div r1 r2 r3)) lr =
      add1_lhs_reg r1 (add1_rhs_reg r3 (add1_rhs_reg r2 lr))) /\
   (get_heu_inst (asm_Arith (asm_AddCarry r1 r2 r3 r4)) lr =
      add1_lhs_reg r4 (add1_lhs_reg r1
        (add1_rhs_reg r4 (add1_rhs_reg r3 (add1_rhs_reg r2 lr))))) /\
   (get_heu_inst (asm_Arith (AddOverflow r1 r2 r3 r4)) lr =
      add1_lhs_reg r4 (add1_lhs_reg r1 (add1_rhs_reg r3 (add1_rhs_reg r2 lr)))) /\
   (get_heu_inst (asm_Arith (SubOverflow r1 r2 r3 r4)) lr =
      add1_lhs_reg r4 (add1_lhs_reg r1 (add1_rhs_reg r3 (add1_rhs_reg r2 lr)))) /\
   (get_heu_inst (asm_Arith (LongMul r1 r2 r3 r4)) lr =
      add1_lhs_reg r2 (add1_lhs_reg r1 (add1_rhs_reg r4 (add1_rhs_reg r3 lr)))) /\
   (get_heu_inst (asm_Arith (LongDiv r1 r2 r3 r4 r5)) lr =
      add1_lhs_reg r2 (add1_lhs_reg r1
        (add1_rhs_reg r5 (add1_rhs_reg r4 (add1_rhs_reg r3 lr))))) /\
   (get_heu_inst (Mem asm_Load r (Addr a w)) lr = add1_lhs_mem r lr) /\
   (get_heu_inst (Mem asm_Store r (Addr a w)) lr = add1_rhs_mem r lr) /\
   (get_heu_inst (Mem asm_Load32 r (Addr a w)) lr = add1_lhs_mem r lr) /\
   (get_heu_inst (Mem Load8 r (Addr a w)) lr = add1_lhs_mem r lr) /\
   (get_heu_inst (Mem asm_Store32 r (Addr a w)) lr = add1_rhs_mem r lr) /\
   (get_heu_inst (Mem Store8 r (Addr a w)) lr = add1_rhs_mem r lr) /\
   (get_heu_inst (FP (FPLess r f1 f2)) lr = add1_lhs_reg r lr) /\
   (get_heu_inst (FP (FPLessEqual r f1 f2)) lr = add1_lhs_reg r lr) /\
   (get_heu_inst (FP (FPEqual r f1 f2)) lr = add1_lhs_reg r lr) /\
   (get_heu_inst (FP (FPMovToReg r1 r2 d)) lr = add1_lhs_reg r2 (add1_lhs_reg r1 lr)) /\
   (get_heu_inst (FP (FPMovFromReg d r1 r2)) lr =
      add1_rhs_reg r2 (add1_rhs_reg r1 lr)) /\
   (get_heu_inst (x:(A)inst) lr = lr)`;;

(* For Ifs, as a heuristic we take the max over branching paths *)
let heu_max_def = cake_def
  `heu_max (c1,r1,m1,rr1,rm1) (c2,r2,m2,rr2,rm2) =
     (MAX c1 c2,MAX r1 r2,MAX m1 m2,MAX rr1 rr2,MAX rm1 rm2)`;;

(* t1r: everything in t1 not already in t2 *)
let heu_max_all_def = cake_def
  `heu_max_all (t1:(heu_data)spt) t2 =
     let t1r = difference t1 t2 in
     sptree_union t1r
       (mapi (\k v. match lookup k t1 with
                      NONE -> v
                    | SOME v' -> heu_max v v') t2)`;;

let heu_merge_call_def = cake_def
  `heu_merge_call (t1:1 spt) t2 = sptree_union t1 t2`;;

(* We use lr to approximate any new vars not already tracked in calls *)
let add_call_def = cake_def
  `add_call (lr:A spt) (calls:1 spt) = sptree_union (sptree_map (\v. one) lr) calls`;;

(* The remaining ones are exps, or otherwise unimportant from the pov of    *)
(* register allocation, since all their temps are already forced into       *)
(* specific registers.  Omitted: Skip, Assign, Store, FFI, Alloc, Raise,    *)
(* Tick, Call NONE.  (A general Set exp is ignored.)                        *)
let get_heu_def = sem1aux_def_wf
  `MEASURE (\(fc:num,p:(A)wl_prog,lr:(heu_data)spt#1 spt). wl_prog_size (\x:A. 0) p)`
  SEM1AUX_TC_TAC (list_mk_conj
 [`(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fc:num) (wl_Move pri ls:(A)wl_prog) (lr:(heu_data)spt,calls:1 spt) =
     (ITLIST add1_lhs_reg (MAP FST ls) (ITLIST add1_rhs_reg (MAP SND ls) lr),calls)`;
  `(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fc:num) (wl_Inst i:(A)wl_prog) (lr:(heu_data)spt,calls:1 spt) =
     (get_heu_inst i lr,calls)`;
  `(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fc:num) (wl_Get num store:(A)wl_prog) (lr:(heu_data)spt,calls:1 spt) =
     (add1_lhs_mem num lr,calls)`;
  `(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fc:num) (wl_Set _ exp:(A)wl_prog) (lr:(heu_data)spt,calls:1 spt) =
     match exp with
       wl_Var r -> (add1_rhs_mem r lr,calls)
     | _ -> (lr,calls)`;
  `(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fc:num) (wl_OpCurrHeap b dst src:(A)wl_prog)
     (lr:(heu_data)spt,calls:1 spt) =
     (add1_lhs_reg dst (add1_rhs_reg src lr),calls)`;
  `(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fc:num) (wl_LocValue r l1:(A)wl_prog) (lr:(heu_data)spt,calls:1 spt) =
     (add1_lhs_reg r lr,calls)`;
  `(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fc:num) (wl_Seq s1 s2:(A)wl_prog) (lr:(heu_data)spt#1 spt) =
     get_heu fc s2 (get_heu fc s1 lr)`;
  `(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fc:num) (MustTerminate s1:(A)wl_prog) (lr:(heu_data)spt#1 spt) =
     get_heu fc s1 lr`;
  `(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fc:num) (wl_If cmp r1 ri e2 e3:(A)wl_prog) (lr:(heu_data)spt#1 spt) =
     let (lr2,calls2) = get_heu fc e2 lr in
     let (lr3,calls3) = get_heu fc e3 lr in
     let lr = heu_max_all lr2 lr3 in
     let calls = heu_merge_call calls2 calls3 in
     ((match ri with
         Reg r2 -> add1_rhs_reg r1 (add1_rhs_reg r2 lr)
       | _ -> add1_rhs_reg r1 lr),calls)`;
  `(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fc:num) (wl_Call NONE dest args h:(A)wl_prog)
     (lr:(heu_data)spt,calls:1 spt) =
     match dest with
       NONE -> (lr,calls)
     | SOME p -> if p = fc then (lr,add_call lr calls) else (lr,calls)`;
  `(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fc:num) (wl_Call (SOME (_,_,e2,_,_)) dest args h:(A)wl_prog)
     (lr:(heu_data)spt,calls:1 spt) =
     let calls = (match dest with
                    NONE -> calls
                  | SOME p -> if p = fc then add_call lr calls else calls) in
     let (lr2,calls2) = get_heu fc e2 (lr,calls) in
     match h with
       NONE -> (lr2,calls)
     | SOME (_,e3,_,_) ->
         let (lr3,calls3) = get_heu fc e3 (lr,calls) in
         (heu_max_all lr2 lr3,heu_merge_call calls2 calls3)`;
  `(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fs:num) (ShareInst asm_Load r _:(A)wl_prog)
     (lr:(heu_data)spt,calls:1 spt) = (add1_lhs_mem r lr,calls)`;
  `(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fs:num) (ShareInst Load8 r _:(A)wl_prog)
     (lr:(heu_data)spt,calls:1 spt) = (add1_lhs_mem r lr,calls)`;
  `(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fs:num) (ShareInst Load16 r _:(A)wl_prog)
     (lr:(heu_data)spt,calls:1 spt) = (add1_lhs_mem r lr,calls)`;
  `(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fs:num) (ShareInst asm_Load32 r _:(A)wl_prog)
     (lr:(heu_data)spt,calls:1 spt) = (add1_lhs_mem r lr,calls)`;
  `(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fs:num) (ShareInst asm_Store r _:(A)wl_prog)
     (lr:(heu_data)spt,calls:1 spt) = (add1_rhs_mem r lr,calls)`;
  `(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fs:num) (ShareInst Store8 r _:(A)wl_prog)
     (lr:(heu_data)spt,calls:1 spt) = (add1_rhs_mem r lr,calls)`;
  `(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fs:num) (ShareInst Store16 r _:(A)wl_prog)
     (lr:(heu_data)spt,calls:1 spt) = (add1_rhs_mem r lr,calls)`;
  `(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fs:num) (ShareInst asm_Store32 r _:(A)wl_prog)
     (lr:(heu_data)spt,calls:1 spt) = (add1_rhs_mem r lr,calls)`;
  `(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fc:num) (wl_Loop names body exit_names:(A)wl_prog)
     (lr:(heu_data)spt#1 spt) = get_heu fc body lr`;
  `(get_heu:num->(A)wl_prog->(heu_data)spt#1 spt->(heu_data)spt#1 spt)
      (fc:num) (f:(A)wl_prog) (lrc:(heu_data)spt#1 spt) = lrc`]);;

(* Forced edges for certain instructions *)
let get_forced_def = sem1aux_def_wf
  `MEASURE (\(c:(A)asm_config,p:(A)wl_prog,acc:(num#num)list). wl_prog_size (\x:A. 0) p)`
  SEM1AUX_TC_TAC (list_mk_conj
 [`(get_forced:(A)asm_config->(A)wl_prog->(num#num)list->(num#num)list)
      (c:(A)asm_config) (wl_Inst i:(A)wl_prog) acc =
     match i with
       asm_Arith (asm_AddCarry r1 r2 r3 r4) ->
         if asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V then
           APPEND (APPEND (if r1 = r3 then [] else [(r1,r3)])
                          (if r1 = r4 then [] else [(r1,r4)])) acc
         else acc
     | asm_Arith (AddOverflow r1 r2 r3 r4) ->
         if asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V then
           APPEND (if r1 = r3 then [] else [(r1,r3)]) acc
         else acc
     | asm_Arith (SubOverflow r1 r2 r3 r4) ->
         if asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V then
           APPEND (if r1 = r3 then [] else [(r1,r3)]) acc
         else acc
     | asm_Arith (LongMul r1 r2 r3 r4) ->
         if asm_config_ISA c = ARMv7 then
           APPEND (if r1 = r2 then [] else [(r1,r2)]) acc
         else if asm_config_ISA c = ARMv8 \/ asm_config_ISA c = RISC_V \/
                 asm_config_ISA c = Ag32 then
           APPEND (APPEND (if r1 = r3 then [] else [(r1,r3)])
                          (if r1 = r4 then [] else [(r1,r4)])) acc
         else acc
     | FP (FPMovToReg r1 r2 d) ->
         APPEND (if dimindex(:A) = 32 /\ ~(r1 = r2) then [(r1,r2)] else []) acc
     | FP (FPMovFromReg d r1 r2) ->
         APPEND (if dimindex(:A) = 32 /\ ~(r1 = r2) then [(r1,r2)] else []) acc
     | _ -> acc`;
  `(get_forced:(A)asm_config->(A)wl_prog->(num#num)list->(num#num)list)
      (c:(A)asm_config) (MustTerminate s1:(A)wl_prog) acc =
     get_forced c s1 acc`;
  `(get_forced:(A)asm_config->(A)wl_prog->(num#num)list->(num#num)list)
      (c:(A)asm_config) (wl_Seq s1 s2:(A)wl_prog) acc =
     get_forced c s1 (get_forced c s2 acc)`;
  `(get_forced:(A)asm_config->(A)wl_prog->(num#num)list->(num#num)list)
      (c:(A)asm_config) (wl_If cmp num rimm e2 e3:(A)wl_prog) acc =
     get_forced c e2 (get_forced c e3 acc)`;
  `(get_forced:(A)asm_config->(A)wl_prog->(num#num)list->(num#num)list) (c:(A)asm_config)
     (wl_Call (SOME (v,cutset,ret_handler,l1,l2)) dest args h:(A)wl_prog) acc =
     match h with
       NONE -> get_forced c ret_handler acc
     | SOME (v,prog,l1,l2) -> get_forced c prog (get_forced c ret_handler acc)`;
  `(get_forced:(A)asm_config->(A)wl_prog->(num#num)list->(num#num)list)
      (c:(A)asm_config) (wl_Loop names body exit_names:(A)wl_prog) acc =
     get_forced c body acc`;
  `(get_forced:(A)asm_config->(A)wl_prog->(num#num)list->(num#num)list)
      (c:(A)asm_config) (prog:(A)wl_prog) (acc:(num#num)list) = acc`]);;
let get_forced_ind = cake_ind "get_forced";;

let get_forced_pmatch = prove
 (CASE_TERM
  `!(c:(A)asm_config) (prog:(A)wl_prog) acc.
     get_forced c prog acc =
       match prog with
         wl_Inst (asm_Arith (asm_AddCarry r1 r2 r3 r4)) ->
           if asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V then
             APPEND (APPEND (if r1 = r3 then [] else [(r1,r3)])
                            (if r1 = r4 then [] else [(r1,r4)])) acc
           else acc
       | wl_Inst (asm_Arith (AddOverflow r1 r2 r3 r4)) ->
           if asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V then
             APPEND (if r1 = r3 then [] else [(r1,r3)]) acc
           else acc
       | wl_Inst (asm_Arith (SubOverflow r1 r2 r3 r4)) ->
           if asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V then
             APPEND (if r1 = r3 then [] else [(r1,r3)]) acc
           else acc
       | wl_Inst (asm_Arith (LongMul r1 r2 r3 r4)) ->
           if asm_config_ISA c = ARMv7 then
             APPEND (if r1 = r2 then [] else [(r1,r2)]) acc
           else if asm_config_ISA c = ARMv8 \/ asm_config_ISA c = RISC_V \/
                   asm_config_ISA c = Ag32 then
             APPEND (APPEND (if r1 = r3 then [] else [(r1,r3)])
                            (if r1 = r4 then [] else [(r1,r4)])) acc
           else acc
       | wl_Inst (FP (FPMovToReg r1 r2 d)) ->
           APPEND (if dimindex(:A) = 32 /\ ~(r1 = r2) then [(r1,r2)] else []) acc
       | wl_Inst (FP (FPMovFromReg d r1 r2)) ->
           APPEND (if dimindex(:A) = 32 /\ ~(r1 = r2) then [(r1,r2)] else []) acc
       | MustTerminate s1 -> get_forced c s1 acc
       | wl_Seq s1 s2 -> get_forced c s1 (get_forced c s2 acc)
       | wl_If cmp num rimm e2 e3 -> get_forced c e2 (get_forced c e3 acc)
       | wl_Call (SOME (v,cutset,ret_handler,l1,l2)) dest args NONE ->
           get_forced c ret_handler acc
       | wl_Call (SOME (v,cutset,ret_handler,l1,l2)) dest args (SOME (_,prog,_,_)) ->
           get_forced c prog (get_forced c ret_handler acc)
       | wl_Loop names body exit_names -> get_forced c body acc
       | _ -> acc`,
  REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN RW[get_forced_def]);;

(*col is injective over every cut set*)
let check_colouring_ok_alt_def = cake_def
  `(check_colouring_ok_alt (col:num->B) ([]:(A spt)list) <=> T) /\
   (check_colouring_ok_alt col (CONS x xs) <=>
      let names = MAP (col o FST) (toAList x) in
      ALL_DISTINCT names /\ check_colouring_ok_alt col xs)`;;

let every_even_colour_def = cake_def
  `every_even_colour col <=>
     ALL (\xy. match xy with (x,y) -> if is_phy_var x then y = x DIV 2 else T)
         (toAList col)`;;

(*Extract a colouring function from the generated sptree*)
let total_colour_def = cake_def
  `total_colour col x =
     match lookup x col with
       NONE -> if is_phy_var x then x else 0
     | SOME x -> 2 * x`;;

let total_colour_alt = prove
 (`!col. total_colour col = (\x. 2 * x) o sp_default col`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; total_colour_def; sp_default_def] THEN
  REPEAT GEN_TAC THEN TOP_CASE_TAC THEN SIMP[] THEN
  COND_CASES_TAC THEN SIMP[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[is_phy_var_def]) THEN
  MP_TAC(SPECL [`x:num`; `2`] DIVISION) THEN ARITH_TAC);;

(*Check that the oracle provided colour (if it exists) is okay*)
(* (possibly avoid these checks and instead check the oracle domain        *)
(* directly; HOL4 also has the check every_var is_phy_var prog commented   *)
(* out)                                                                     *)
let oracle_colour_ok_def = cake_def
  `oracle_colour_ok k col_opt tree (prog:(A)wl_prog) ls =
     match col_opt with
       NONE -> NONE
     | SOME col ->
         let tcol = total_colour col in
         if every_even_colour col /\ ~(check_clash_tree tcol tree LN LN = NONE) then
           let prog = apply_colour tcol prog in
           if every_stack_var (\x. x >= 2 * k) prog /\
              ALL (\xy. match xy with (x,y) -> ~(tcol x = tcol y)) ls
           then SOME prog
           else NONE
         else NONE`;;

(* Returns
  1) a lookup table
    v -> spill cost
  2) the move list, with associated priorities

  For now, the spill cost metric is just 6 magic numbers
*)
(*
  Canonize by flipping moves (all move x<=y)
  Filter some obviously impossible ones out
  Then SORT them by lexicographic order, and count
  returns (num, maxpriority, (x,y))
*)
let canonize_moves_aux_def = cake_def
  `(canonize_moves_aux curp (curm:A) ctr [] acc = CONS (ctr,curp,curm) acc) /\
   (canonize_moves_aux curp curm ctr (CONS (p,m) xs) acc =
      if curm = m then canonize_moves_aux (MAX curp p) m (ctr + 1) xs acc
      else canonize_moves_aux p m 1 xs (CONS (ctr,curp,curm) acc))`;;

let canonize_moves_def = cake_def
  `canonize_moves ls =
     let can1 = MAP (\pxy. match pxy with
                             (p:num,(x:num,y:num)) ->
                               if x <= y then (p,(x,y)) else (p,(y,x))) ls in
     let can2 = sort
       (\pxy1 pxy2. match pxy1 with
                      (p1,(x1,y1)) ->
                        (match pxy2 with
                           (p2,(x2,y2)) ->
                             if x1 = x2 then
                               if y1 = y2 then p1 < p2 else y1 < y2
                             else x1 < x2)) can1 in
     match can2 with
       [] -> []
     | CONS (p,m) xs -> canonize_moves_aux p m 1 xs []`;;

(* TODO: ALL of these magic numbers must be adjusted!! *)

let get_spillcost_def = cake_def
  `get_spillcost (c,lr,lm,rr,rm) istail =
     ((((c + 2 * lr) + 4 * lm) + 2 * rr) + 4 * rm) * (if istail then 5 else 1)`;;

(*
  Prioritize moves that happen a lot, and have high max priority
  also give some weight to the spill cost of their endpoints
*)
let get_coalescecost_def = cake_def
  `get_coalescecost (spillcost:A spt) (n,p,(x,y)) =
     let xcost = if lookup x spillcost = NONE then 0 else 1 in
     let ycost = if lookup y spillcost = NONE then 0 else 1 in
     (n * (((10 * (p + 1)) + xcost) + ycost),(x,y))`;;

let get_heuristics_def = cake_def
  `get_heuristics alg fc (prog:(A)wl_prog) =
     if alg MOD 2 = 1 then
       let (lr,calls) = get_heu fc prog (LN,LN) in
       let moves = get_prefs prog [] in
       let spillcosts = mapi (\k v. get_spillcost v (lookup k calls = NONE)) lr in
       let canon_moves = canonize_moves moves in
       let heu_moves = MAP (get_coalescecost spillcosts) canon_moves in
       (heu_moves,SOME spillcosts)
     else
       let moves = get_prefs prog [] in
       (moves,NONE)`;;

let select_reg_alloc_def = cake_def
  `select_reg_alloc alg spillcosts k heu_moves tree forced fs =
     if 4 <= alg then linear_scan_reg_alloc k heu_moves tree forced
     else reg_alloc (if alg <= 1 then reg_alloc_Simple else IRC)
                    spillcosts k heu_moves tree forced fs`;;

(* For a move x <- y
  if x is a register, then y should not be forced stack
  else,
    if y is a stack variable or forced stack,
    then we mark x as forced stack as well
*)
let merge_stack_only_def = cake_def
  `merge_stack_only (x,y) (ts:1 spt,fs:1 spt) =
     if lookup x ts = SOME one then
       let ts = if is_alloc_var y then insert y one ts else ts in
       let fs = if is_phy_var y then fs else insert x one fs in
       (ts,fs)
     else if is_stack_var x then
       let ts = if is_alloc_var y then insert y one ts else ts in
       (ts,fs)
     else (delete y ts,fs)`;;

let merge_stack_sets_def = cake_def
  `merge_stack_sets (ts:A spt,fs:B) (tsL:C spt,fsL:D spt) (tsR,fsR) =
     let keep1 = sptree_inter tsR (sptree_inter tsL ts) in
     let keep2 = sptree_union (difference tsL ts) (difference tsR ts) in
     (sptree_union keep1 keep2,sptree_union fsL fsR)`;;

let remove_temp_stack_def = cake_def
  `remove_temp_stack ls (ts:A spt,fs:B) = (ITLIST delete ls ts,fs)`;;

(* Alloc variables that are already stack or
  only ever involved in stack moves *)
let get_stack_only_aux_def = sem1aux_def_wf
  `MEASURE (\(tfs:1 spt#1 spt,p:(A)wl_prog). wl_prog_size (\x:A. 0) p)`
  SEM1AUX_TC_TAC (list_mk_conj
 [`(get_stack_only_aux:1 spt#1 spt->(A)wl_prog->1 spt#1 spt)
      (tfs:1 spt#1 spt) (wl_Move pri ls:(A)wl_prog) =
     ITLIST merge_stack_only ls tfs`;
  `(get_stack_only_aux:1 spt#1 spt->(A)wl_prog->1 spt#1 spt)
      (tfs:1 spt#1 spt) (wl_Seq s1 s2:(A)wl_prog) =
     get_stack_only_aux (get_stack_only_aux tfs s2) s1`;
  `(get_stack_only_aux:1 spt#1 spt->(A)wl_prog->1 spt#1 spt)
      (tfs:1 spt#1 spt) (wl_If cmp r1 ri e2 e3:(A)wl_prog) =
     let tfsL = get_stack_only_aux tfs e2 in
     let tfsR = get_stack_only_aux tfs e3 in
     let tfsM = merge_stack_sets tfs tfsL tfsR in
     match ri with
       Reg r2 -> remove_temp_stack [r1;r2] tfsM
     | _ -> remove_temp_stack [r1] tfsM`;
  `(get_stack_only_aux:1 spt#1 spt->(A)wl_prog->1 spt#1 spt)
      (tfs:1 spt#1 spt) (MustTerminate s:(A)wl_prog) =
     get_stack_only_aux tfs s`;
  `(get_stack_only_aux:1 spt#1 spt->(A)wl_prog->1 spt#1 spt)
      (tfs:1 spt#1 spt) (wl_Call ret dest args h:(A)wl_prog) =
     match ret with
       NONE -> tfs
     | SOME (v,cutset,ret_handler,_,_) ->
         let rettfs = get_stack_only_aux tfs ret_handler in
         match h with
           NONE -> rettfs
         | SOME (v',handler,_,_) ->
             let handlertfs = get_stack_only_aux tfs handler in
             merge_stack_sets tfs rettfs handlertfs`;
  `(get_stack_only_aux:1 spt#1 spt->(A)wl_prog->1 spt#1 spt)
      (tfs:1 spt#1 spt) (wl_Loop names body exit_names:(A)wl_prog) =
     get_stack_only_aux tfs body`;
  `(get_stack_only_aux:1 spt#1 spt->(A)wl_prog->1 spt#1 spt) (tfs:1 spt#1 spt) (prog:(A)wl_prog) =
     match get_clash_tree prog [] with
       Delta ws rs -> remove_temp_stack (APPEND ws rs) tfs
     | _ -> tfs`]);;

let get_stack_only_def = cake_def
  `get_stack_only (prog:(A)wl_prog) = SND (get_stack_only_aux (LN,LN) prog)`;;

(*
  fc is the current prog number
  alg is the allocation algorithm,
    0: simple allocator, no spill heuristics
    1: simple allocator + spill heuristics
    2: IRC allocator, no spill heuristics (default)
    3: IRC allocator + spill heuristics
  >=4: linear scan register allocator
  k is the number of registers
  prog is the program to be colored
  col_opt is an optional oracle colour
  (M_failure cannot happen; HOL4 also has a commented-out
  let moves = get_prefs_sp prog [])
*)
let word_alloc_def = cake_def
  `word_alloc fc (c:(A)asm_config) alg k (prog:(A)wl_prog) col_opt =
     let tree = get_clash_tree prog [] in
     let fs = get_stack_only prog in
     let forced = get_forced c prog [] in
     match oracle_colour_ok k col_opt tree prog forced with
       NONE ->
         let (heu_moves,spillcosts) = get_heuristics alg fc prog in
         (match select_reg_alloc alg spillcosts k heu_moves tree forced fs with
            M_success col -> apply_colour (total_colour col) prog
          | M_failure _ -> prog)
     | SOME col_prog -> col_prog`;;

(*The initial move, ssa and limit vars*)
let setup_ssa_def = cake_def
  `setup_ssa n lim (prog:(A)wl_prog) =
     let args = even_list n in
     let (new_ls,ssa',n') = list_next_var_rename args LN lim in
     (wl_Move 1 (ZIP new_ls args):(A)wl_prog,ssa',n')`;;

let limit_var_def = cake_def
  `limit_var (prog:(A)wl_prog) =
     let x = max_var prog in
     (x + (4 - x MOD 4)) + 1`;;

let full_ssa_cc_trans_def = cake_def
  `full_ssa_cc_trans n (prog:(A)wl_prog) =
     let lim = limit_var prog in
     let (mov,ssa,na) = setup_ssa n lim prog in
     let (prog',ssa',na') = ssa_cc_trans prog ssa na [] in
     wl_Seq mov prog'`;;
