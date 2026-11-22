(* ========================================================================= *)
(* loop_live: port of HOL4 pancake/loop_liveScript.sml (CakeML v3479).       *)
(* Liveness analysis for loopLang.                                           *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as notes/naming/names.tsv says: shrink is loop_live_shrink, comp  *)
(*   is loop_live_comp; HOL4 Definition arith_vars (no _def) is the theorem  *)
(*   arith_vars.                                                             *)
(* - HOL4 size (of an sptree) is sptree's size (theorem sptree_size_def);    *)
(*   () is one; oEL is list's oEL; exp_size ARB is loop_exp_size (\x. 0).    *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "pancake/loopLang.ml";;
needs "pancake/loop_call.ml";;

prioritize_num();;
type_invention_error := true;;

let vars_of_exp_def = cake_def
  `(vars_of_exp (loop_Var v:(A)loop_exp) (l:num_set) = insert v one l) /\
   (vars_of_exp (loop_Const _) l = l) /\
   (vars_of_exp loop_BaseAddr l = l) /\
   (vars_of_exp loop_TopAddr l = l) /\
   (vars_of_exp (loop_Lookup _) l = l) /\
   (vars_of_exp (loop_Load a) l = vars_of_exp a l) /\
   (vars_of_exp (loop_Op op vs) l = vars_of_exp_list vs l) /\
   (vars_of_exp (loop_Shift _ x y) l = vars_of_exp x (vars_of_exp y l)) /\
   (vars_of_exp_list xs l =
      match xs with
        [] -> l
      | CONS x xs -> vars_of_exp x (vars_of_exp_list xs l))`;;

let vars_of_exp_ind = cake_ind "vars_of_exp";;

let size_mk_BN = prove
 (`!t1 t2:A spt. size (mk_BN t1 t2) = size (BN t1 t2)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `t1:A spt` (cases "spt")) THEN
  STRUCT_CASES_TAC (ISPEC `t2:A spt` (cases "spt")) THEN
  REWRITE_TAC[mk_BN_def; sptree_size_def; ADD_CLAUSES]);;

let size_mk_BS = prove
 (`!t1 t2 (x:A). size (mk_BS t1 x t2) = size (BS t1 x t2)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `t1:A spt` (cases "spt")) THEN
  STRUCT_CASES_TAC (ISPEC `t2:A spt` (cases "spt")) THEN
  REWRITE_TAC[mk_BS_def; sptree_size_def; ADD_CLAUSES]);;

let size_inter = prove
 (`!(l1:A spt) (l2:B spt). size (inter l1 l2) <= size l1`,
  MATCH_MP_TAC spt_INDUCT THEN REWRITE_TAC[inter_def; sptree_size_def; LE_REFL] THEN
  REPEAT STRIP_TAC THEN
  STRUCT_CASES_TAC (ISPEC `l2:B spt` (cases "spt")) THEN
  REWRITE_TAC[spt_CASE; size_mk_BN; size_mk_BS; sptree_size_def] THEN
  ASM_MESON_TAC[ARITH_RULE `n1 <= m1 /\ n2 <= m2
                            ==> n1 + n2 <= m1 + m2 /\ n1 + n2 <= m1 + m2 + 1 /\
                                n1 + n2 + 1 <= m1 + m2 + 1`;
                ARITH_RULE `0 <= n /\ 0 <= n + 1 /\ 1 <= 1 /\ 1 <= n + m + 1`]);;

let arith_vars = cake_def
  `(arith_vars (LLongMul r1 r2 r3 r4) (l:num_set) =
      insert r3 one (insert r4 one (delete r1 (delete r2 l)))) /\
   (arith_vars (LDiv r1 r2 r3) l = insert r2 one (insert r3 one (delete r1 l))) /\
   (arith_vars (LLongDiv r1 r2 r3 r4 r5) l =
      insert r3 one (insert r4 one (insert r5 one (delete r1 (delete r2 l)))))`;;

(* This optimisation shrinks all cutsets and also deletes assignments to    *)
(* unused variables.  The Loop case is the interesting one: an auxiliary   *)
(* function is used to find a fixed-point.                                  *)

let PLOOPAUX_shrink_rel =
  `inv_image (measure I LEX measure I LEX measure I)
     (\x:((num_set#num_set)list#(A)loop_prog#num_set) +
         ((num_set#num_set)list#num_set#num_set#num_set#(A)loop_prog).
        sum_CASE x
          (\p. (loop_prog_size (\a:A. 0) (FST (SND p)), 0, 0))
          (\p. (loop_prog_size (\a:A. 0) (SND (SND (SND (SND p)))), 1,
                size (FST (SND p)) - size (FST (SND (SND p))))))`;;

(* the termination conditions: the sizes, and size (inter l1 l2) <= size l1 *)
(* for the recursive call of fixedpoint                                     *)

let PLOOPAUX_SIZE_INTER_TAC : tactic = fun (asl,w as g) ->
  let is_inter t =
    try let f,args = strip_comb t in
        fst(dest_const f) = "inter" && length args = 2
    with Failure _ -> false in
  MAP_EVERY (fun t -> match snd(strip_comb t) with
                        [a;b] -> MP_TAC(ISPECL [a;b] size_inter)
                      | _ -> ALL_TAC)
    (find_terms is_inter w) g;;

let PLOOPAUX_SHRINK_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  REWRITE_TAC(WF_REL_THMS @ [sum_CASE; FST; SND; I_THM;
                             type_size_def "loop_prog"]) THEN
  PLOOPAUX_SIZE_INTER_TAC THEN DECIDE_TAC;;

let PLOOPAUX_shrink_clauses =
 `(loop_live_shrink (lt:(num_set#num_set)list) (loop_Seq p1 p2:(A)loop_prog)
                    (l:num_set) =
     let (p2,l) = loop_live_shrink lt p2 l in
     let (p1,l) = loop_live_shrink lt p1 l in
       (loop_Seq p1 p2, l)) /\
  (loop_live_shrink lt (loop_Loop live_in body live_out) l =
     let l2 = inter live_out l in
     let bex = union live_in l2 in
       match fixedpoint lt live_in LN bex body with
         SOME (body,l0) ->
           (let l = inter live_in l0 in (loop_Loop l body l2, l))
       | NONE ->
           let (b,_) = loop_live_shrink (CONS (live_in,l2) lt) body bex in
             (loop_Loop live_in b l2, live_in)) /\
  (loop_live_shrink lt (loop_If x1 x2 x3 p1 p2 l1) l =
     let l = inter l l1 in
     let (p1,l1) = loop_live_shrink lt p1 l in
     let (p2,l2) = loop_live_shrink lt p2 l in
     let l3 = (match x3 with Reg r -> insert r one LN | _ -> LN) in
       (loop_If x1 x2 x3 p1 p2 l, insert x2 one (union l3 (union l1 l2)))) /\
  (loop_live_shrink lt (Mark p1) l = loop_live_shrink lt p1 l) /\
  (loop_live_shrink lt (loop_Break n) l =
     (loop_Break n, match oEL n lt with SOME (_, brk) -> brk | NONE -> LN)) /\
  (loop_live_shrink lt (loop_Continue n) l =
     (loop_Continue n, match oEL n lt with SOME (cont, _) -> cont | NONE -> LN)) /\
  (loop_live_shrink lt loop_Fail l = (loop_Fail,LN)) /\
  (loop_live_shrink lt loop_Skip l = (loop_Skip,l)) /\
  (loop_live_shrink lt (loop_Return vs) l = (loop_Return vs, list_insert vs LN)) /\
  (loop_live_shrink lt (loop_Raise v) l = (loop_Raise v, insert v one LN)) /\
  (loop_live_shrink lt (loop_Arith arith) l =
     (loop_Arith arith, arith_vars arith l)) /\
  (loop_live_shrink b (loop_Primitive lhss pop rhss) l =
     (loop_Primitive lhss pop rhss, list_insert rhss (list_delete lhss l))) /\
  (loop_live_shrink lt (LocValue n m) l =
     match lookup n l with
       NONE -> (loop_Skip,l)
     | SOME _ -> (LocValue n m, delete n l)) /\
  (loop_live_shrink lt (loop_Assign n e) l =
     match lookup n l with
       NONE -> (loop_Skip,l)
     | SOME _ -> (loop_Assign n e, vars_of_exp e (delete n l))) /\
  (loop_live_shrink lt (loop_ShMem op r ad) l =
     (loop_ShMem op r ad, vars_of_exp ad (insert r one l))) /\
  (loop_live_shrink lt (loop_Store e n) l =
     (loop_Store e n, vars_of_exp e (insert n one l))) /\
  (loop_live_shrink lt (loop_SetGlobal name e) l =
     (loop_SetGlobal name e, vars_of_exp e l)) /\
  (loop_live_shrink lt (loop_Call ret dest args handler) l =
     let a = fromAList (MAP (\x. (x,one)) args) in
     match ret with
       NONE -> (loop_Call NONE dest args NONE, union a l)
     | SOME (ns,l1) ->
         (match handler with
            NONE ->
              let l3 = list_delete ns (inter l l1) in
                (loop_Call (SOME (ns,l3)) dest args NONE, union a l3)
          | SOME (e,h,r,live_out) ->
              let (r,l2) = loop_live_shrink lt r l in
              let (h,l3) = loop_live_shrink lt h l in
              let l1 = inter l1 (union (list_delete ns l2) (delete e l3)) in
                (loop_Call (SOME (ns,l1)) dest args
                   (SOME (e,h,r,inter l live_out)),
                 union a l1))) /\
  (loop_live_shrink lt (loop_FFI fi r1 r2 r3 r4 l1) l =
     (loop_FFI fi r1 r2 r3 r4 (inter l1 l),
      insert r1 one (insert r2 one (insert r3 one (insert r4 one (inter l1 l)))))) /\
  (loop_live_shrink lt (loop_Load32 x y) l =
     (loop_Load32 x y, insert x one (delete y l))) /\
  (loop_live_shrink lt (loop_LoadByte x y) l =
     (loop_LoadByte x y, insert x one (delete y l))) /\
  (loop_live_shrink lt (loop_Store32 x y) l =
     (loop_Store32 x y, insert x one (insert y one l))) /\
  (loop_live_shrink lt (loop_StoreByte x y) l =
     (loop_StoreByte x y, insert x one (insert y one l))) /\
  (loop_live_shrink lt prog l = (prog,l)) /\
  (fixedpoint lt live_in l1 l2 body =
     let (b,l0) = loop_live_shrink (CONS (inter live_in l1,l2) lt) body l2 in
     let l0' = inter live_in l0 in
       if l0' = l1 then SOME (b,l0) else
       if size l0' <= size l1 then NONE else
         fixedpoint lt live_in l0' l2 body)`;;

(* HOL4: shrink_def (the clauses of shrink and fixedpoint) *)

let loop_live_shrink_def =
  cake_def_wf PLOOPAUX_shrink_rel PLOOPAUX_SHRINK_TC_TAC PLOOPAUX_shrink_clauses;;

let loop_live_shrink_ind = cake_ind "loop_live_shrink";;

let exp_ind =
  let th = ISPECL [`\(x:(A)loop_exp) (l:num_set). (P:(A)loop_exp->bool) x`;
                   `\(x:((A)loop_exp)list) (l:num_set).
                       (Q:((A)loop_exp)list->bool) x`] vars_of_exp_ind in
  GENL [`P:(A)loop_exp->bool`; `Q:((A)loop_exp)list->bool`]
    (REWRITE_RULE[] (BETA_RULE th));;

let PLOOPAUX_inter_inter = prove
 (`!(a:A spt) (b:B spt). inter a (inter a b) = inter a b`,
  REWRITE_TAC[inter_eq; lookup_inter] THEN REPEAT GEN_TAC THEN
  EVERY_CASE_TAC THEN ASM_REWRITE_TAC[]);;

(* the fixedpoint clause of loop_live_shrink_def *)

let PLOOPAUX_fixedpoint_eq =
  find (fun th -> try fst(dest_const(fst(strip_comb(lhs(snd(strip_forall(concl th))))))) =
                      "fixedpoint"
                  with Failure _ -> false)
       (CONJUNCTS loop_live_shrink_def);;

let fixedpoint_thm = prove
 (`!lt live_in l1 l2 (body:(A)loop_prog) l0 b.
     fixedpoint lt live_in l1 l2 body = SOME (b, l0) ==>
     loop_live_shrink (CONS (inter live_in l0, l2) lt) body l2 = (b, l0)`,
  MP_TAC(ISPECL [`\(lt:(num_set#num_set)list) (prog:(A)loop_prog) (l:num_set). T`;
                 `\lt live_in l1 l2 (body:(A)loop_prog). !l0 b.
                     fixedpoint lt live_in l1 l2 body = SOME (b, l0) ==>
                     loop_live_shrink (CONS (inter live_in l0, l2) lt) body l2 =
                     (b, l0)`]
           loop_live_shrink_ind) THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [PLOOPAUX_fixedpoint_eq] THEN
  PAIRARG_TAC THEN FS[] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PLOOPAUX_inter_inter]) THEN ASM_REWRITE_TAC[];
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[]]);;

let mark_all_def = cake_def
  `(mark_all (loop_Seq p1 p2:(A)loop_prog) =
      let (p1,t1) = mark_all p1 in
      let (p2,t2) = mark_all p2 in
      let t3 = (t1 /\ t2) in
        ((if t3 then Mark (loop_Seq p1 p2) else loop_Seq p1 p2), t3)) /\
   (mark_all (loop_Loop l1 body l2) =
      let (body,t1) = mark_all body in
        (loop_Loop l1 body l2, F)) /\
   (mark_all (loop_If x1 x2 x3 p1 p2 l1) =
      let (p1,t1) = mark_all p1 in
      let (p2,t2) = mark_all p2 in
      let p3 = loop_If x1 x2 x3 p1 p2 l1 in
      let t3 = (t1 /\ t2) in
        ((if t3 then Mark p3 else p3), t3)) /\
   (mark_all (Mark p1) = mark_all p1) /\
   (mark_all (loop_Call ret dest args handler) =
      match handler with
        NONE -> (Mark (loop_Call ret dest args handler), T)
      | SOME (ns,p1,p2,l) ->
          let (p1,t1) = mark_all p1 in
          let (p2,t2) = mark_all p2 in
          let t3 = (t1 /\ t2) in
          let p3 = loop_Call ret dest args (SOME (ns,p1,p2,l)) in
            ((if t3 then Mark p3 else p3), t3)) /\
   (mark_all prog = (Mark prog,T))`;;

let mark_all_ind = cake_ind "mark_all";;

(* HOL4: comp *)

let loop_live_comp_def = cake_def
  `loop_live_comp (prog:(A)loop_prog) =
     FST (mark_all (FST (loop_live_shrink [] prog LN)))`;;

let optimise_def = cake_def
  `optimise (prog:(A)loop_prog) =
     (loop_live_comp o FST o loop_call_comp LN) prog`;;
