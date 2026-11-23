(* ========================================================================= *)
(* word_unreach: port of HOL4 compiler/backend/word_unreachScript.sml        *)
(* (CakeML v3479).                                                           *)
(* This compilation pass removes trivially unreachable code.                 *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: the wordLang constructors wl_...,          *)
(*   word_unreach_merge_moves (HOL4 merge_moves) and                         *)
(*   word_unreach_Seq_assoc_right_def/_ind (Seq_assoc_right_def cannot be    *)
(*   bound by OCaml); the constant Seq_assoc_right keeps its name.           *)
(* - HOL4's paired lambda (UNCURRY) in merge_moves is written               *)
(*   \p. match p with (x,y) -> ..., i.e. pair_CASE.                          *)
(* - Definitions with catch-all clauses are made with sem1aux_def (HOL4's    *)
(*   TFL completion); dest_Seq_Move_ind (a case analysis) comes from         *)
(*   wordLang's IL2AUX_case_ind.                                             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/wordLang.ml";;

type_invention_error := true;;

(* function that makes all Seq associate to the right *)

let dest_Seq_Move_def = sem1aux_def
  `(dest_Seq_Move (wl_Move n l:(A)wl_prog) = SOME (n,l,wl_Skip:(A)wl_prog)) /\
   (dest_Seq_Move (wl_Seq (wl_Move n l) rest) = SOME (n,l,rest)) /\
   (dest_Seq_Move (_:(A)wl_prog) = NONE)`;;

let dest_Seq_Move_ind = IL2AUX_case_ind dest_Seq_Move_def;;

(* HOL4: merge_moves *)

let word_unreach_merge_moves_def = cake_def
  `word_unreach_merge_moves (l1:(num#num)list) (l2:(num#num)list) =
     let l2' = MAP (\p. match p with
                          (x,y) -> (match ALOOKUP l1 y with
                                      NONE -> (x,y)
                                    | SOME v -> (x,v))) l2 in
     anub (APPEND l2' l1) ([]:num list)`;;

let SimpSeq_def = cake_def
  `SimpSeq p1 (p2:(A)wl_prog) =
     let default = wl_Seq p1 p2 in
     if p2 = wl_Skip then p1 else
     match p1 with
       wl_Skip -> p2
     | wl_Raise _ -> p1
     | wl_Return _ _ -> p1
     | wl_Break _ -> p1
     | wl_Continue _ -> p1
     | wl_Move n1 l1 ->
         (match dest_Seq_Move p2 with
            NONE -> default
          | SOME (n2,l2,rest) ->
              let l = word_unreach_merge_moves l1 l2 in
              if rest = wl_Skip
              then wl_Move (MAX n1 n2) l
              else wl_Seq (wl_Move (MAX n1 n2) l) rest)
     | _ -> default`;;

(* HOL4: Seq_assoc_right_def, Seq_assoc_right_ind *)

let word_unreach_Seq_assoc_right_def = sem1aux_def
  `(Seq_assoc_right (wl_Skip:(A)wl_prog) acc = acc) /\
   (Seq_assoc_right (wl_Seq q1 q2) acc =
      Seq_assoc_right q1 (Seq_assoc_right q2 acc)) /\
   (Seq_assoc_right (wl_If v n r q1 q2) acc =
      SimpSeq (wl_If v n r (Seq_assoc_right q1 wl_Skip)
                           (Seq_assoc_right q2 wl_Skip)) acc) /\
   (Seq_assoc_right (MustTerminate q) acc =
      SimpSeq (MustTerminate (Seq_assoc_right q wl_Skip)) acc) /\
   (Seq_assoc_right (wl_Call ret_prog dest args handler) acc =
      match ret_prog with
        NONE -> wl_Call ret_prog dest args handler
      | SOME (x1,x2,q1,x3,x4) ->
          SimpSeq (wl_Call (SOME (x1,x2,Seq_assoc_right q1 wl_Skip,x3,x4))
                     dest args
                     (match handler with
                        NONE -> NONE
                      | SOME (y1,q2,y2,y3) ->
                          SOME (y1,Seq_assoc_right q2 wl_Skip,y2,y3))) acc) /\
   (Seq_assoc_right (wl_Loop names body exit_names) acc =
      SimpSeq (wl_Loop names (Seq_assoc_right body wl_Skip) exit_names) acc) /\
   (Seq_assoc_right p1 acc = SimpSeq p1 acc)`;;

let word_unreach_Seq_assoc_right_ind = cake_ind "Seq_assoc_right";;

let remove_unreach_def = cake_def
  `remove_unreach (e:(A)wl_prog) = Seq_assoc_right e wl_Skip`;;

(* HOL4: [local], proved by EVAL_TAC *)

let remove_unreach_test = prove
 (`remove_unreach (wl_Seq (wl_Move 1 [(1,11);(2,22);(3,33)])
                          (wl_Move 1 [(3,1);(2,99)]):(A)wl_prog) =
   wl_Move 1 [(3,11); (2,99); (1,11)]`,
  REWRITE_TAC[remove_unreach_def; word_unreach_Seq_assoc_right_def] THEN
  REWRITE_TAC[SimpSeq_def; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[dest_Seq_Move_def] THEN
  REWRITE_TAC[word_unreach_merge_moves_def; LET_DEF; LET_END_DEF; MAP; APPEND;
              ALOOKUP_DEF] THEN
  REPEAT (CHANGED_TAC (CONV_TAC(DEPTH_CONV NUM_EQ_CONV) THEN CASE_REWRITE_TAC[])) THEN
  REPEAT (CHANGED_TAC (ONCE_REWRITE_TAC[anub_def] THEN REWRITE_TAC[MEM] THEN
                       CONV_TAC(DEPTH_CONV NUM_EQ_CONV) THEN REWRITE_TAC[])) THEN
  REWRITE_TAC[ARITH_RULE `MAX 1 1 = 1`]);;
