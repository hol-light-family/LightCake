(* ========================================================================= *)
(* word_depth: port of HOL4 compiler/backend/word_depthScript.sml            *)
(* (CakeML v3479).                                                           *)
(* Computes the call graph for wordLang program with an acyclic call graph.  *)
(* This graph is in turn used to compute the max stack depth used by the     *)
(* wordLang program.                                                         *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: the call_tree constructors                 *)
(*   word_depth_Leaf, Unknown, word_depth_Const, word_depth_Call and         *)
(*   word_depth_Branch; the wordLang constructors wl_....                    *)
(* - HOL4 prog_size (K 0) is wl_prog_size (K 0); the termination relation    *)
(*   of call_graph is HOL4's, on the tupled arguments written with FST/SND.  *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/wordLang.ml";;

type_invention_error := true;;

(* representation of acyclic call graph, i.e. call tree *)

let call_tree_INDUCT,call_tree_RECURSION = cake_type
  "call_tree = word_depth_Leaf
             | Unknown
             | word_depth_Const num call_tree
             | word_depth_Call num call_tree
             | word_depth_Branch call_tree call_tree";;

(* computing the max stack depth *)

let max_depth_def = cake_def
  `(max_depth (frame_sizes:num spt) word_depth_Leaf = SOME 0) /\
   (max_depth frame_sizes Unknown = NONE) /\
   (max_depth frame_sizes (word_depth_Const n t) =
      OPTION_MAP ((+) n) (max_depth frame_sizes t)) /\
   (max_depth frame_sizes (word_depth_Branch t1 t2) =
      OPTION_MAP2 MAX (max_depth frame_sizes t1) (max_depth frame_sizes t2)) /\
   (max_depth frame_sizes (word_depth_Call n t) =
      OPTION_MAP2 (+) (lookup n frame_sizes) (max_depth frame_sizes t))`;;

(* computing the call graph *)

let mk_Branch_def = cake_def
  `mk_Branch t1 t2 =
     if t1 = t2 then t1 else
     if t1 = word_depth_Leaf then t2 else
     if t2 = word_depth_Leaf then t1 else
     if t1 = Unknown then t1 else
     if t2 = Unknown then t2 else
     word_depth_Branch t1 t2`;;

(* the termination conditions of call_graph: HOL4's fs [size_delete] and     *)
(* imp_res_tac lookup_zero, then the kit's TERM_TAC                           *)

let WORDP1AUX_CG_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  (fun (asl,_ as g) ->
     MAP_EVERY (fun (_,th) ->
                  try ASSUME_TAC (MATCH_MP lookup_zero th) with Failure _ ->
                  try ASSUME_TAC (MATCH_MP lookup_zero (SYM th)) with Failure _ ->
                  ALL_TAC) asl g) THEN
  RULE_ASSUM_TAC(REWRITE_RULE(WF_REL_THMS @ [FST; SND; I_THM])) THEN
  ASM_REWRITE_TAC(WF_REL_THMS @ [FST; SND; I_THM; LENGTH; size_delete; option_DISTINCT]) THEN
  TERM_TAC;;

(* call_graph is defined by its clauses with the let of the call clause   *)
(* inlined (sem1aux's clause induction does not see the context            *)
(* new_funs = delete d funs of a let); call_graph_def, HOL4's clauses with  *)
(* the let, is proved from them                                             *)

let WORDP1AUX_call_graph_def = sem1aux_def_wf
  `inv_image (MEASURE I LEX MEASURE I LEX MEASURE I)
     (\x:((num#(A)wl_prog)spt)#num#(num list)#num#(A)wl_prog.
        (sptree_size (FST x), FST (SND (SND (SND x))) - LENGTH (FST (SND (SND x))),
         wl_prog_size (combin_K 0) (SND (SND (SND (SND x))))))`
  WORDP1AUX_CG_TAC
  `(call_graph funs n ns total' (wl_Seq p1 p2:(A)wl_prog) =
      mk_Branch (call_graph funs n ns total' p1) (call_graph funs n ns total' p2)) /\
   (call_graph funs n ns total' (wl_If _ _ _ p1 p2) =
      mk_Branch (call_graph funs n ns total' p1) (call_graph funs n ns total' p2)) /\
   (call_graph funs n ns total' (wl_Call ret dest args handler) =
      match dest with
        NONE -> Unknown
      | SOME d ->
          if MEM d ns /\ ret = NONE then word_depth_Leaf else
          match lookup d funs with
            NONE -> Unknown
          | SOME (a:num,body) ->
              match ret with
                NONE ->
                  (if LENGTH ns < total' then
                     mk_Branch (word_depth_Call d word_depth_Leaf)
                       (call_graph funs d (CONS d ns) total' body)
                   else word_depth_Leaf)
              | SOME (_,_,ret_prog,_,_) ->
                  match handler with
                    NONE ->
                      word_depth_Branch
                        (word_depth_Call n (word_depth_Call d word_depth_Leaf))
                        (mk_Branch
                           (word_depth_Call n (call_graph (delete d funs) d [d] total' body))
                           (call_graph funs n ns total' ret_prog))
                  | SOME (_,p,_,_) ->
                      word_depth_Branch
                        (word_depth_Call n
                           (word_depth_Const 3 (word_depth_Call d word_depth_Leaf)))
                        (mk_Branch
                           (word_depth_Call n
                              (word_depth_Const 3 (call_graph (delete d funs) d [d] total' body)))
                           (mk_Branch (call_graph funs n ns total' p)
                                      (call_graph funs n ns total' ret_prog)))) /\
   (call_graph funs n ns total' (MustTerminate p) = call_graph funs n ns total' p) /\
   (call_graph funs n ns total' (wl_Alloc _ _) = word_depth_Call n word_depth_Leaf) /\
   (call_graph funs n ns total' (wl_Install _ _ _ _ _) = Unknown) /\
   (call_graph funs n ns total' (wl_Loop _ body _) = call_graph funs n ns total' body) /\
   (call_graph funs n ns _ _ = word_depth_Leaf)`;;

let call_graph_ind = cake_ind "call_graph";;

let WORDP1AUX_call_graph_Call = prove
 (CASE_TERM
  `!funs n ns total' ret dest args handler.
   call_graph funs n ns total' (wl_Call ret dest args handler:(A)wl_prog) =
      match dest with
        NONE -> Unknown
      | SOME d ->
          if MEM d ns /\ ret = NONE then word_depth_Leaf else
          match lookup d funs with
            NONE -> Unknown
          | SOME (a:num,body) ->
              match ret with
                NONE ->
                  (if LENGTH ns < total' then
                     mk_Branch (word_depth_Call d word_depth_Leaf)
                       (call_graph funs d (CONS d ns) total' body)
                   else word_depth_Leaf)
              | SOME (_,_,ret_prog,_,_) ->
                  let new_funs = delete d funs in
                  match handler with
                    NONE ->
                      word_depth_Branch
                        (word_depth_Call n (word_depth_Call d word_depth_Leaf))
                        (mk_Branch
                           (word_depth_Call n (call_graph new_funs d [d] total' body))
                           (call_graph funs n ns total' ret_prog))
                  | SOME (_,p,_,_) ->
                      word_depth_Branch
                        (word_depth_Call n
                           (word_depth_Const 3 (word_depth_Call d word_depth_Leaf)))
                        (mk_Branch
                           (word_depth_Call n
                              (word_depth_Const 3 (call_graph new_funs d [d] total' body)))
                           (mk_Branch (call_graph funs n ns total' p)
                                      (call_graph funs n ns total' ret_prog)))`,
  REWRITE_TAC[WORDP1AUX_call_graph_def; LET_DEF; LET_END_DEF]);;

let call_graph_def =
  let is_call th =
    let l = lhs(snd(strip_forall(concl th))) in
    (try fst(dest_const(fst(strip_comb(rand l)))) = "wl_Call"
     with Failure _ -> false) in
  end_itlist CONJ
    (map (fun th -> if is_call th then WORDP1AUX_call_graph_Call else th)
         (CONJUNCTS WORDP1AUX_call_graph_def));;

let full_call_graph_def = cake_def
  `full_call_graph n (funs:(num#(A)wl_prog)spt) =
     match lookup n funs with
       NONE -> Unknown
     | SOME (a,prog) ->
         word_depth_Branch (word_depth_Call n word_depth_Leaf)
                           (call_graph funs n [n] (sptree_size funs) prog)`;;

let max_depth_graphs_def = cake_def
  `(max_depth_graphs ss [] all (funs:(num#(A)wl_prog)spt)
                     (all_funs:(B#(A)wl_prog)spt) = SOME 0) /\
   (max_depth_graphs ss (CONS n ns) all funs all_funs =
      match lookup n all_funs with
        NONE -> NONE
      | SOME (a,body) ->
          OPTION_MAP2 MAX (lookup n ss)
            (OPTION_MAP2 MAX
               (max_depth ss (call_graph funs n all (sptree_size all_funs) body))
               (max_depth_graphs ss ns all funs all_funs)))`;;
