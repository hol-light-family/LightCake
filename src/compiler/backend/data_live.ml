(* ========================================================================= *)
(* data_live: port of HOL4 compiler/backend/data_liveScript.sml             *)
(* (CakeML v3479).                                                           *)
(* This compiler phase minimises the live-var annotations that are attached  *)
(* to MakeSpace, Assign and Call in dataLang programs. This phase also       *)
(* locally deletes code that has no observable effect.                       *)
(*                                                                           *)
(* Notes on the rendering: is_pure (a catch-all clause completed into one    *)
(* clause per remaining constructor, as HOL4's TFL does) and compile (many   *)
(* clauses) are defined with sem1aux_def (semantics/sem1aux_tfl.ml);         *)
(* HOL4's pmatch is a match (case constants).  HOL4 () is one.               *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/dataLang.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* the arithmetic operations would be pure if space usage were not tracked *)
(* (a switch in the semantics could do it); are the comparisons really    *)
(* impure?                                                                 *)

let data_live_is_pure_def = sem1aux_def
  `(data_live_is_pure (clos_FFI _) <=> F) /\
   (data_live_is_pure (IntOp clos_Add) <=> F) /\
   (data_live_is_pure (IntOp clos_Sub) <=> F) /\
   (data_live_is_pure (IntOp Mult) <=> F) /\
   (data_live_is_pure (IntOp clos_Div) <=> F) /\
   (data_live_is_pure (IntOp clos_Mod) <=> F) /\
   (data_live_is_pure (IntOp clos_Less) <=> F) /\
   (data_live_is_pure (IntOp LessEq) <=> F) /\
   (data_live_is_pure (WordOp (WordOpw W64 _)) <=> F) /\
   (data_live_is_pure (WordOp (WordShift W64 _ _)) <=> F) /\
   (data_live_is_pure (WordOp WordFromInt) <=> F) /\
   (data_live_is_pure (WordOp WordToInt) <=> F) /\
   (data_live_is_pure (WordOp (WordFromWord b)) <=> F) /\
   (data_live_is_pure (WordOp (FP_uop _)) <=> F) /\
   (data_live_is_pure (WordOp (FP_bop _)) <=> F) /\
   (data_live_is_pure (WordOp (FP_top _)) <=> F) /\
   (data_live_is_pure (BlockOp (Build _)) <=> F) /\
   (data_live_is_pure (BlockOp (clos_Cons _)) <=> F) /\
   (data_live_is_pure (BlockOp (ConsExtend _)) <=> F) /\
   (data_live_is_pure (BlockOp (FromList _)) <=> F) /\
   (data_live_is_pure (BlockOp clos_ListAppend) <=> F) /\
   (data_live_is_pure (BlockOp clos_Equal) <=> F) /\
   (data_live_is_pure (GlobOp (SetGlobal _)) <=> F) /\
   (data_live_is_pure (GlobOp SetGlobalsPtr) <=> F) /\
   (data_live_is_pure (MemOp clos_Ref) <=> F) /\
   (data_live_is_pure (MemOp (RefByte _)) <=> F) /\
   (data_live_is_pure (MemOp RefArray) <=> F) /\
   (data_live_is_pure (MemOp Update) <=> F) /\
   (data_live_is_pure (MemOp (MutCons _ _)) <=> F) /\
   (data_live_is_pure (MemOp UpdateCons) <=> F) /\
   (data_live_is_pure (MemOp FinaliseCons) <=> F) /\
   (data_live_is_pure (MemOp UpdateByte) <=> F) /\
   (data_live_is_pure (MemOp FromListByte) <=> F) /\
   (data_live_is_pure (MemOp (CopyByte _)) <=> F) /\
   (data_live_is_pure (MemOp XorByte) <=> F) /\
   (data_live_is_pure (MemOp clos_ConfigGC) <=> F) /\
   (data_live_is_pure clos_Install <=> F) /\
   (data_live_is_pure (clos_ThunkOp _) <=> F) /\
   (data_live_is_pure _ <=> T)`;;

(* HOL4: is_pure_pmatch *)

let is_pure_pmatch = prove
 (CASE_TERM
  `!op. data_live_is_pure op =
     match op with
       clos_FFI _ -> F
     | GlobOp (SetGlobal _) -> F
     | GlobOp SetGlobalsPtr -> F
     | WordOp (WordOpw W64 _) -> F
     | WordOp (WordShift W64 _ _) -> F
     | WordOp WordFromInt -> F
     | WordOp WordToInt -> F
     | WordOp (WordFromWord b) -> F
     | WordOp (FP_uop _) -> F
     | WordOp (FP_bop _) -> F
     | WordOp (FP_top _) -> F
     | BlockOp (Build _) -> F
     | BlockOp (clos_Cons _) -> F
     | BlockOp (ConsExtend _) -> F
     | BlockOp (FromList _) -> F
     | BlockOp clos_ListAppend -> F
     | BlockOp clos_Equal -> F
     | MemOp clos_Ref -> F
     | MemOp (RefByte _) -> F
     | MemOp RefArray -> F
     | MemOp Update -> F
     | MemOp (MutCons _ _) -> F
     | MemOp UpdateCons -> F
     | MemOp FinaliseCons -> F
     | MemOp UpdateByte -> F
     | MemOp FromListByte -> F
     | MemOp (CopyByte _) -> F
     | MemOp XorByte -> F
     | IntOp clos_Add -> F
     | IntOp clos_Sub -> F
     | IntOp Mult -> F
     | IntOp clos_Div -> F
     | IntOp clos_Mod -> F
     | IntOp clos_Less -> F
     | IntOp LessEq -> F
     | clos_Install -> F
     | MemOp clos_ConfigGC -> F
     | clos_ThunkOp _ -> F
     | _ -> T`,
  GEN_TAC THEN EVERY_CASE_TAC THEN REWRITE_TAC[data_live_is_pure_def]);;

let data_live_compile_def = sem1aux_def
  `(data_live_compile data_Skip live = (data_Skip,live)) /\
   (data_live_compile (data_Return ns) live = (data_Return ns,list_insert ns LN)) /\
   (data_live_compile (data_Raise n) live = (data_Raise n,insert n one LN)) /\
   (data_live_compile (data_Move n1 n2) live =
      (data_Move n1 n2,insert n2 one (delete n1 live))) /\
   (data_live_compile (data_Seq c1 c2) live =
      let (d2,l2) = data_live_compile c2 live in
      let (d1,l1) = data_live_compile c1 l2 in
        (data_Seq d1 d2,l1)) /\
   (data_live_compile data_Tick live = (data_Tick,live)) /\
   (data_live_compile (MakeSpace k names) live =
      let l1 = inter names live in (MakeSpace k l1,l1)) /\
   (data_live_compile (data_Assign v op vs NONE) live =
      if IS_NONE (lookup v live) /\ data_live_is_pure op then (data_Skip,live) else
        let l1 = list_insert vs (delete v live) in
          (data_Assign v op vs NONE,l1)) /\
   (data_live_compile (data_Assign v op vs (SOME names)) live =
      let l1 = inter names (delete v live) in
        (data_Assign v op vs (SOME l1),list_insert vs l1)) /\
   (data_live_compile (data_If n c2 c3) live =
      let (d3,l3) = data_live_compile c3 live in
      let (d2,l2) = data_live_compile c2 live in
        (data_If n d2 d3,insert n one (union l2 l3))) /\
   (data_live_compile (data_Force NONE loc src) live =
      (data_Force NONE loc src,insert src one LN)) /\
   (data_live_compile (data_Force (SOME (n,names)) loc src) live =
      let l1 = inter names (delete n live) in
      let l2 = insert src one l1 in
        (data_Force (SOME (n,l1)) loc src,l2)) /\
   (data_live_compile (data_Call NONE dest vs handler) live =
      (data_Call NONE dest vs handler,list_to_num_set vs)) /\
   (data_live_compile (data_Call (SOME (ns,names)) dest vs NONE) live =
      let l1 = inter names (list_delete ns live) in
      let l2 = list_insert vs l1 in
        (data_Call (SOME (ns,l1)) dest vs NONE,l2)) /\
   (data_live_compile (data_Call (SOME (ns,names)) dest vs (SOME (v,c))) live =
      let (d,l3) = data_live_compile c live in
      let l0 = union (list_delete ns live) (delete v l3) in
      let l1 = inter names l0 in
      let l2 = list_insert vs l1 in
        (data_Call (SOME (ns,l1)) dest vs (SOME (v,d)),l2))`;;

let data_live_compile_ind = cake_ind "data_live_compile";;
