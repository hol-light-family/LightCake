(* ========================================================================= *)
(* bvl_to_bvi: port of HOL4 compiler/backend/bvl_to_bviScript.sml (CakeML    *)
(* v3479).                                                                   *)
(* A compiler phase that transforms BVL programs into BVI programs. As part  *)
(* of this phase, certain primitive operations map to "stubs" code          *)
(* implemented in BVI; numeric constants are split into smaller ones to     *)
(* ease code generation later; Handle is fused with Call; and very large    *)
(* expressions are split into smaller ones (in order to protect the         *)
(* register allocator from overly large inputs).                            *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 ++ on app_lists (local overload) is SmartAppend; List is          *)
(*   misc_List; num_stubs is bvl_num_stubs and nss bvl_to_bvi_namespaces;    *)
(*   s1 ^ s2 on mlstrings is strcat s1 s2; HOL4 exp1_size (bvl) is           *)
(*   list_size bvl_exp_size.                                                 *)
(* - Definitions with catch-all or overlapping clauses are made with         *)
(*   sem1aux_def(_wf) (HOL4's TFL completion).                               *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/bvl.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvl_inline.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/bvl_handle.ml";;
needs "compiler/backend/bvi_let.ml";;
needs "compiler/backend/bvi_tailrec.ml";;
needs "compiler/backend/bvi_inline.ml";;
needs "compiler/backend/bvi_tmc.ml";;
needs "compiler/backend/dataLang.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

let destLet_def = sem1aux_def
  `(destLet (bvl_Let xs b) = (xs,b)) /\
   (destLet _ = ([],bvl_Var 0))`;;

let destLet_pmatch = prove
 (CASE_TERM
  `!exp. destLet exp =
         match exp with
           bvl_Let xs b -> (xs,b)
         | _ -> ([],bvl_Var 0)`,
  GEN_TAC THEN CASES_ON `exp:bvl_exp` THEN REWRITE_TAC[destLet_def] THEN
  CASE_REWRITE_TAC[]);;

(* large_int = 268435457 = 2**28-1 *)

let compile_int_def = cake_def
  `compile_int (i:int) =
     bvi_Op (if -- &268435457 <= i /\ i <= &268435457 then IntOp (clos_Const i)
             else BlockOp (Build [clos_Int i])) []`;;

let alloc_glob_count_def = sem1aux_def_wf
  `MEASURE (\xs:bvl_exp list. list_size bvl_exp_size xs)`
  SEM1AUX_TC_TAC
  `(alloc_glob_count [] = 0) /\
   (alloc_glob_count (CONS x (CONS y xs)) =
      alloc_glob_count [x] + alloc_glob_count (CONS y xs)) /\
   (alloc_glob_count [bvl_Var _] = 0) /\
   (alloc_glob_count [bvl_If x y z] =
      alloc_glob_count [x] + alloc_glob_count [y] + alloc_glob_count [z]) /\
   (alloc_glob_count [bvl_Handle x y] =
      alloc_glob_count [x] + alloc_glob_count [y]) /\
   (alloc_glob_count [bvl_Tick x] = alloc_glob_count [x]) /\
   (alloc_glob_count [bvl_Force loc v] = 0) /\
   (alloc_glob_count [bvl_Raise x] = alloc_glob_count [x]) /\
   (alloc_glob_count [bvl_Let xs x] = alloc_glob_count (CONS x xs)) /\
   (alloc_glob_count [bvl_Call _ _ xs] = alloc_glob_count xs) /\
   (alloc_glob_count [bvl_Op op xs] =
      if op = GlobOp AllocGlobal then 1 + alloc_glob_count xs
      else alloc_glob_count xs) /\
   (alloc_glob_count [_] = 0)`;;

let alloc_glob_count_ind = cake_ind "alloc_glob_count";;

let global_count_sing_def = sem1aux_def_wf
  `MEASURE (\x:bvl_exp + bvl_exp list.
              sum_CASE x (\e. bvl_exp_size e) (\es. list_size bvl_exp_size es))`
  SEM1AUX_TC_TAC
  `(global_count_sing (bvl_Var _) = 0) /\
   (global_count_sing (bvl_If x y z) =
      global_count_sing x + global_count_sing y + global_count_sing z) /\
   (global_count_sing (bvl_Handle x y) =
      global_count_sing x + global_count_sing y) /\
   (global_count_sing (bvl_Force loc v) = 0) /\
   (global_count_sing (bvl_Tick x) = global_count_sing x) /\
   (global_count_sing (bvl_Raise x) = global_count_sing x) /\
   (global_count_sing (bvl_Let xs x) =
      global_count_sing x + global_count_list xs) /\
   (global_count_sing (bvl_Call _ _ xs) = global_count_list xs) /\
   (global_count_sing (bvl_Op op xs) =
      if op = GlobOp AllocGlobal then 1 + global_count_list xs
      else global_count_list xs) /\
   (global_count_list [] = 0) /\
   (global_count_list (CONS x xs) = global_count_sing x + global_count_list xs)`;;

let global_count_sing_ind = cake_ind "global_count_sing";;

(* alloc_glob_count of a CONS (the two list clauses of HOL4's definition) *)

let BVIPAUX_B2B_alloc_glob_count_CONS = prove
 (`!h t. alloc_glob_count (CONS h t) = alloc_glob_count [h] + alloc_glob_count t`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[alloc_glob_count_def; ADD_CLAUSES]);;

let alloc_glob_count_eq_global_count_list = prove
 (`(!e. global_count_sing e = alloc_glob_count [e]) /\
   (!es. global_count_list es = alloc_glob_count es)`,
  MATCH_MP_TAC bvl_exp_INDUCT THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[global_count_sing_def; alloc_glob_count_def] THEN
  GEN_REWRITE_TAC RAND_CONV [BVIPAUX_B2B_alloc_glob_count_CONS] THEN
  REFL_TAC);;

let AllocGlobal_location_def = cake_def
  `AllocGlobal_location = data_num_stubs`;;
let CopyGlobals_location_def = cake_def
  `CopyGlobals_location = AllocGlobal_location + 1`;;
let InitGlobals_location_def = cake_def
  `InitGlobals_location = CopyGlobals_location + 1`;;
let ListLength_location_def = cake_def
  `ListLength_location = InitGlobals_location + 1`;;
let FromListByte_location_def = cake_def
  `FromListByte_location = ListLength_location + 1`;;
let ToListByte_location_def = cake_def
  `ToListByte_location = FromListByte_location + 1`;;
let SumListLength_location_def = cake_def
  `SumListLength_location = ToListByte_location + 1`;;
let ConcatByte_location_def = cake_def
  `ConcatByte_location = SumListLength_location + 1`;;

(* HOL4: the _eq theorems are EVAL of the locations *)

let BVIPAUX_B2B_LOC_TAC =
  REWRITE_TAC[ConcatByte_location_def; SumListLength_location_def;
              ToListByte_location_def; FromListByte_location_def;
              ListLength_location_def; InitGlobals_location_def;
              CopyGlobals_location_def; AllocGlobal_location_def;
              data_num_stubs_def; word_num_stubs_def; stack_num_stubs_def] THEN
  CONV_TAC NUM_REDUCE_CONV;;

let AllocGlobal_location_eq = prove
 (`AllocGlobal_location = 62`, BVIPAUX_B2B_LOC_TAC);;
let CopyGlobals_location_eq = prove
 (`CopyGlobals_location = 63`, BVIPAUX_B2B_LOC_TAC);;
let InitGlobals_location_eq = prove
 (`InitGlobals_location = 64`, BVIPAUX_B2B_LOC_TAC);;
let ListLength_location_eq = prove
 (`ListLength_location = 65`, BVIPAUX_B2B_LOC_TAC);;
let FromListByte_location_eq = prove
 (`FromListByte_location = 66`, BVIPAUX_B2B_LOC_TAC);;
let ToListByte_location_eq = prove
 (`ToListByte_location = 67`, BVIPAUX_B2B_LOC_TAC);;
let SumListLength_location_eq = prove
 (`SumListLength_location = 68`, BVIPAUX_B2B_LOC_TAC);;
let ConcatByte_location_eq = prove
 (`ConcatByte_location = 69`, BVIPAUX_B2B_LOC_TAC);;

let AllocGlobal_code_def = cake_def
  `AllocGlobal_code = (1:num,
     bvi_Let [bvi_Op (GlobOp GlobalsPtr) []]
      (bvi_Let [bvi_Op (MemOp clos_El) [bvi_Op (IntOp (clos_Const (&0))) [];
                                         bvi_Var 0]]
       (bvi_Let [bvi_Op (IntOp clos_Add) [bvi_Var 0; bvi_Var 2]]
        (bvi_Let [bvi_Op (MemOp Length) [bvi_Var 2]]
         (bvi_Let [bvi_Op (MemOp Update)
                     [bvi_Var 1; bvi_Op (IntOp (clos_Const (&0))) []; bvi_Var 3]]
          (bvi_If (bvi_Op (IntOp clos_Less) [bvi_Var 1; bvi_Var 2]) (bvi_Var 0)
            (bvi_Let [bvi_Op (MemOp RefArray)
                        [bvi_Op (IntOp (clos_Const (&0))) [];
                         bvi_Op (IntOp clos_Add) [bvi_Var 2; bvi_Var 2]]]
             (bvi_Let [bvi_Op (GlobOp SetGlobalsPtr) [bvi_Var 0]]
               (bvi_Call 0 (SOME CopyGlobals_location)
                  [bvi_Var 1; bvi_Var 6;
                   bvi_Op (IntOp clos_Sub)
                     [bvi_Op (IntOp (clos_Const (&1))) []; bvi_Var 3]] NONE)))))))))`;;

(* ptr to new array, ptr to old array, index to copy *)

let CopyGlobals_code_def = cake_def
  `CopyGlobals_code = (3:num,
     bvi_Let [bvi_Op (MemOp Update)
                [bvi_Op (MemOp clos_El) [bvi_Var 2; bvi_Var 1]; bvi_Var 2;
                 bvi_Var 0]]
       (bvi_If (bvi_Op (BlockOp clos_Equal)
                  [bvi_Op (IntOp (clos_Const (&0))) []; bvi_Var 3]) (bvi_Var 0)
          (bvi_Call 0 (SOME CopyGlobals_location)
             [bvi_Var 1; bvi_Var 2;
              bvi_Op (IntOp clos_Sub)
                [bvi_Op (IntOp (clos_Const (&1))) []; bvi_Var 3]] NONE)))`;;

let InitGlobals_max_def = cake_def
  `InitGlobals_max = 10000`;;

let InitGlobals_code_def = cake_def
  `InitGlobals_code start n = (0:num,
     let n = MIN (MAX n 1) InitGlobals_max in
       bvi_Let [bvi_Op (MemOp RefArray) [bvi_Op (IntOp (clos_Const (&0))) [];
                                         bvi_Op (IntOp (clos_Const (&n))) []]]
         (bvi_Let [bvi_Op (MemOp Update)
                     [bvi_Op (IntOp (clos_Const (&1))) [];
                      bvi_Op (IntOp (clos_Const (&0))) []; bvi_Var 0]]
            (bvi_Let [bvi_Op (GlobOp SetGlobalsPtr) [bvi_Var 1]]
               (bvi_Call 0 (SOME start) [] (SOME (bvi_Var 0))))))`;;

(* ptr to array, accumulated length *)

let ListLength_code_def = cake_def
  `ListLength_code = (2,
     bvi_If (bvi_Op (BlockOp (clos_TagLenEq nil_tag 0)) [bvi_Var 0])
       (bvi_Var 1)
       (bvi_Call 0 (SOME ListLength_location)
          [bvi_Op (MemOp clos_El) [bvi_Op (IntOp (clos_Const (&1))) []; bvi_Var 0];
           bvi_Op (IntOp clos_Add) [bvi_Var 1; bvi_Op (IntOp (clos_Const (&1))) []]]
          NONE))`;;

(* list, current index, byte array *)

let FromListByte_code_def = cake_def
  `FromListByte_code = (3,
     bvi_If (bvi_Op (BlockOp (clos_TagLenEq nil_tag 0)) [bvi_Var 0]) (bvi_Var 2)
       (bvi_Let [bvi_Op (MemOp UpdateByte)
                   [bvi_Op (MemOp clos_El)
                      [bvi_Op (IntOp (clos_Const (&0))) []; bvi_Var 0];
                    bvi_Var 1; bvi_Var 2]]
          (bvi_Call 0 (SOME FromListByte_location)
             [bvi_Op (MemOp clos_El) [bvi_Op (IntOp (clos_Const (&1))) []; bvi_Var 1];
              bvi_Op (IntOp clos_Add) [bvi_Var 2; bvi_Op (IntOp (clos_Const (&1))) []];
              bvi_Var 3] NONE)))`;;

(* list, current index, byte array *)

let ToListByte_code_def = cake_def
  `ToListByte_code = (3,
     bvi_If (bvi_Op (BlockOp (EqualConst (clos_Int (&0)))) [bvi_Var 1]) (bvi_Var 0)
       (bvi_Let [bvi_Op (IntOp clos_Sub) [bvi_Op (IntOp (clos_Const (&1))) [];
                                          bvi_Var 1]]
          (bvi_Let [bvi_Op (MemOp DerefByte) [bvi_Var 0; bvi_Var 3]]
             (bvi_Call 0 (SOME ToListByte_location)
                [bvi_Op (BlockOp (clos_Cons 0)) [bvi_Var 2; bvi_Var 0];
                 bvi_Var 1;
                 bvi_Var 4] NONE))))`;;

(* ptr to list, accumulated length *)

let SumListLength_code_def = cake_def
  `SumListLength_code = (2,
     bvi_If (bvi_Op (BlockOp (clos_TagLenEq nil_tag 0)) [bvi_Var 0])
       (bvi_Var 1)
       (bvi_Call 0 (SOME SumListLength_location)
          [bvi_Op (MemOp clos_El) [bvi_Op (IntOp (clos_Const (&1))) []; bvi_Var 0];
           bvi_Op (IntOp clos_Add)
             [bvi_Var 1;
              bvi_Op (MemOp LengthByte)
                [bvi_Op (MemOp clos_El)
                   [bvi_Op (IntOp (clos_Const (&0))) []; bvi_Var 0]]]] NONE))`;;

(* list, current index, destination *)

let ConcatByte_code_def = cake_def
  `ConcatByte_code = (3,
     bvi_If (bvi_Op (BlockOp (clos_TagLenEq nil_tag 0)) [bvi_Var 0]) (bvi_Var 2)
       (bvi_Let [bvi_Op (MemOp clos_El) [bvi_Op (IntOp (clos_Const (&0))) [];
                                          bvi_Var 0]]
          (bvi_Let [bvi_Op (MemOp LengthByte) [bvi_Var 0]]
             (bvi_Let [bvi_Op (MemOp (CopyByte F))
                         [bvi_Var 3; bvi_Var 4; bvi_Var 0;
                          bvi_Op (IntOp (clos_Const (&0))) []; bvi_Var 1]]
                (bvi_Call 0 (SOME ConcatByte_location)
                   [bvi_Op (MemOp clos_El)
                      [bvi_Op (IntOp (clos_Const (&1))) []; bvi_Var 3];
                    bvi_Op (IntOp clos_Add) [bvi_Var 4; bvi_Var 1];
                    bvi_Var 5] NONE)))))`;;

let bvl_to_bvi_stubs_def = cake_def
  `bvl_to_bvi_stubs start n =
     [(AllocGlobal_location,AllocGlobal_code);
      (CopyGlobals_location,CopyGlobals_code);
      (InitGlobals_location,InitGlobals_code start n);
      (ListLength_location,ListLength_code);
      (FromListByte_location,FromListByte_code);
      (ToListByte_location,ToListByte_code);
      (SumListLength_location,SumListLength_code);
      (ConcatByte_location,ConcatByte_code)]`;;

(* the cases MutCons, UpdateCons and FinaliseCons are reserved for         *)
(* bvi_tmc; bvlSem do_app is Error on these, so they are compiled out     *)

let bvl_to_bvi_compile_op_def = cake_def
  `bvl_to_bvi_compile_op op c1 =
     match op with
       IntOp (clos_Const i) ->
         (match c1 with
            [] -> compile_int i
          | _ -> bvi_Let [bvi_Op (IntOp (clos_Const (&0))) c1] (compile_int i))
     | GlobOp (clos_Global n) ->
         (if NULL c1 then bvi_Op (GlobOp (clos_Global (n + 1))) []
          else bvi_Let c1 (bvi_Op (MemOp clos_El)
                 [bvi_Op (IntOp clos_Add) [bvi_Op (IntOp (clos_Const (&2))) [];
                                           bvi_Var 0];
                  bvi_Op (GlobOp GlobalsPtr) []]))
     | GlobOp (SetGlobal n) -> bvi_Op (GlobOp (SetGlobal (n + 1))) c1
     | GlobOp AllocGlobal -> bvi_Call 0 (SOME AllocGlobal_location) c1 NONE
     | BlockOp (FromList n) ->
         bvi_Let (if NULL c1 then [bvi_Op (IntOp (clos_Const (&0))) []] else c1)
           (bvi_Op (BlockOp (FromList n))
              [bvi_Var 0;
               bvi_Call 0 (SOME ListLength_location)
                 [bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []] NONE])
     | clos_Install ->
         bvi_Let
           (if ~(LENGTH c1 = 2)
            then [bvi_Let c1 (bvi_Op (IntOp (clos_Const (&0))) []);
                  bvi_Op (IntOp (clos_Const (&0))) []]
            else c1)
           (bvi_Op clos_Install
              [bvi_Call 0 (SOME ListLength_location)
                 [bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []] NONE;
               bvi_Call 0 (SOME ListLength_location)
                 [bvi_Var 1; bvi_Op (IntOp (clos_Const (&0))) []] NONE;
               bvi_Var 0; bvi_Var 1])
     | MemOp FromListByte ->
         bvi_Let (if NULL c1 then [bvi_Op (IntOp (clos_Const (&0))) []] else c1)
           (bvi_Call 0 (SOME FromListByte_location)
              [bvi_Var 0;
               bvi_Op (IntOp (clos_Const (&0))) [];
               bvi_Op (MemOp (RefByte T))
                 [bvi_Op (IntOp (clos_Const (&0))) [];
                  bvi_Call 0 (SOME ListLength_location)
                    [bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []] NONE]]
              NONE)
     | MemOp ToListByte ->
         bvi_Let (if NULL c1 then [bvi_Op (IntOp (clos_Const (&0))) []] else c1)
           (bvi_Call 0 (SOME ToListByte_location)
              [bvi_Op (BlockOp (clos_Cons 0)) [];
               bvi_Op (MemOp LengthByte) [bvi_Var 0];
               bvi_Var 0]
              NONE)
     | MemOp ConcatByteVec ->
         bvi_Let (if NULL c1 then [bvi_Op (IntOp (clos_Const (&0))) []] else c1)
           (bvi_Call 0 (SOME ConcatByte_location)
              [bvi_Var 0;
               bvi_Op (IntOp (clos_Const (&0))) [];
               bvi_Op (MemOp (RefByte T))
                 [bvi_Op (IntOp (clos_Const (&0))) [];
                  bvi_Call 0 (SOME SumListLength_location)
                    [bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []] NONE]] NONE)
     | MemOp (CopyByte T) ->
         bvi_Let (if LENGTH c1 < 3
                  then APPEND c1 (REPLICATE 3 (bvi_Op (IntOp (clos_Const (&0))) []))
                  else c1)
           (bvi_Let [bvi_Op (MemOp (RefByte T))
                       [bvi_Op (IntOp (clos_Const (&0))) []; bvi_Var 0]]
              (bvi_Let [bvi_Op (MemOp (CopyByte F))
                          [bvi_Op (IntOp (clos_Const (&0))) []; bvi_Var 0; bvi_Var 1;
                           bvi_Var 2; bvi_Var 3]]
                 (bvi_Var 1)))
     | clos_Label l ->
         bvi_Op (clos_Label (bvl_num_stubs + bvl_to_bvi_namespaces * l)) c1
     | BlockOp (Build ps) -> bvi_Op (BlockOp (Build ps)) c1
     | BlockOp (EqualConst p) -> bvi_Op (BlockOp (EqualConst p)) c1
     | MemOp (MutCons tag i) -> bvi_Let c1 (bvi_Op (IntOp (clos_Const (&0))) [])
     | MemOp UpdateCons -> bvi_Let c1 (bvi_Op (IntOp (clos_Const (&0))) [])
     | MemOp FinaliseCons -> bvi_Let c1 (bvi_Op (IntOp (clos_Const (&0))) [])
     | _ -> bvi_Op op c1`;;

let bvl_to_bvi_compile_op_pmatch = prove
 (CASE_TERM
  `!op c1.
     bvl_to_bvi_compile_op op c1 =
     match op with
       IntOp (clos_Const i) ->
         (match c1 with
            [] -> compile_int i
          | _ -> bvi_Let [bvi_Op (IntOp (clos_Const (&0))) c1] (compile_int i))
     | GlobOp (clos_Global n) ->
         (if NULL c1 then bvi_Op (GlobOp (clos_Global (n + 1))) []
          else bvi_Let c1 (bvi_Op (MemOp clos_El)
                 [bvi_Op (IntOp clos_Add) [bvi_Op (IntOp (clos_Const (&2))) [];
                                           bvi_Var 0];
                  bvi_Op (GlobOp GlobalsPtr) []]))
     | GlobOp (SetGlobal n) -> bvi_Op (GlobOp (SetGlobal (n + 1))) c1
     | GlobOp AllocGlobal -> bvi_Call 0 (SOME AllocGlobal_location) c1 NONE
     | BlockOp (FromList n) ->
         bvi_Let (if NULL c1 then [bvi_Op (IntOp (clos_Const (&0))) []] else c1)
           (bvi_Op (BlockOp (FromList n))
              [bvi_Var 0;
               bvi_Call 0 (SOME ListLength_location)
                 [bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []] NONE])
     | clos_Install ->
         bvi_Let
           (if ~(LENGTH c1 = 2)
            then [bvi_Let c1 (bvi_Op (IntOp (clos_Const (&0))) []);
                  bvi_Op (IntOp (clos_Const (&0))) []]
            else c1)
           (bvi_Op clos_Install
              [bvi_Call 0 (SOME ListLength_location)
                 [bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []] NONE;
               bvi_Call 0 (SOME ListLength_location)
                 [bvi_Var 1; bvi_Op (IntOp (clos_Const (&0))) []] NONE;
               bvi_Var 0; bvi_Var 1])
     | MemOp FromListByte ->
         bvi_Let (if NULL c1 then [bvi_Op (IntOp (clos_Const (&0))) []] else c1)
           (bvi_Call 0 (SOME FromListByte_location)
              [bvi_Var 0;
               bvi_Op (IntOp (clos_Const (&0))) [];
               bvi_Op (MemOp (RefByte T))
                 [bvi_Op (IntOp (clos_Const (&0))) [];
                  bvi_Call 0 (SOME ListLength_location)
                    [bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []] NONE]]
              NONE)
     | MemOp ToListByte ->
         bvi_Let (if NULL c1 then [bvi_Op (IntOp (clos_Const (&0))) []] else c1)
           (bvi_Call 0 (SOME ToListByte_location)
              [bvi_Op (BlockOp (clos_Cons 0)) [];
               bvi_Op (MemOp LengthByte) [bvi_Var 0];
               bvi_Var 0]
              NONE)
     | MemOp ConcatByteVec ->
         bvi_Let (if NULL c1 then [bvi_Op (IntOp (clos_Const (&0))) []] else c1)
           (bvi_Call 0 (SOME ConcatByte_location)
              [bvi_Var 0;
               bvi_Op (IntOp (clos_Const (&0))) [];
               bvi_Op (MemOp (RefByte T))
                 [bvi_Op (IntOp (clos_Const (&0))) [];
                  bvi_Call 0 (SOME SumListLength_location)
                    [bvi_Var 0; bvi_Op (IntOp (clos_Const (&0))) []] NONE]] NONE)
     | MemOp (CopyByte T) ->
         bvi_Let (if LENGTH c1 < 3
                  then APPEND c1 (REPLICATE 3 (bvi_Op (IntOp (clos_Const (&0))) []))
                  else c1)
           (bvi_Let [bvi_Op (MemOp (RefByte T))
                       [bvi_Op (IntOp (clos_Const (&0))) []; bvi_Var 0]]
              (bvi_Let [bvi_Op (MemOp (CopyByte F))
                          [bvi_Op (IntOp (clos_Const (&0))) []; bvi_Var 0; bvi_Var 1;
                           bvi_Var 2; bvi_Var 3]]
                 (bvi_Var 1)))
     | clos_Label l ->
         bvi_Op (clos_Label (bvl_num_stubs + bvl_to_bvi_namespaces * l)) c1
     | BlockOp (Build ps) -> bvi_Op (BlockOp (Build ps)) c1
     | BlockOp (EqualConst p) -> bvi_Op (BlockOp (EqualConst p)) c1
     | MemOp (MutCons tag i) -> bvi_Let c1 (bvi_Op (IntOp (clos_Const (&0))) [])
     | MemOp UpdateCons -> bvi_Let c1 (bvi_Op (IntOp (clos_Const (&0))) [])
     | MemOp FinaliseCons -> bvi_Let c1 (bvi_Op (IntOp (clos_Const (&0))) [])
     | _ -> bvi_Op op c1`,
  REWRITE_TAC[bvl_to_bvi_compile_op_def]);;

let compile_aux_def = cake_def
  `compile_aux (k,args:A,p) =
     misc_List [(bvl_num_stubs + bvl_to_bvi_namespaces * k + 1,args,
                 bvi_let_compile_exp p)]`;;

let BVIPAUX_B2B_destLet_size = prove
 (`!x (args:bvl_exp list) x0.
     destLet x = (args,x0) ==>
     list_size bvl_exp_size args < bvl_exp_size x /\
     bvl_exp_size x0 <= bvl_exp_size x`,
  GEN_TAC THEN CASES_ON `x:bvl_exp` THEN REWRITE_TAC[destLet_def; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[type_size_def "bvl_exp"] THEN REWRITE_TAC(size_aux_eqs "bvl_exp") THEN
  REWRITE_TAC[list_size] THEN ARITH_TAC);;

(* the termination tactic: TERM_TAC with the size facts of the assumptions *)
(* destLet e = (args,x0) (HOL4: Cases_on x1 / x2 with destLet_def)          *)

let BVIPAUX_B2B_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    let th' = try MATCH_MP BVIPAUX_B2B_destLet_size th with Failure _ ->
              MATCH_MP BVIPAUX_B2B_destLet_size (SYM th) in
    MP_TAC th')) THEN
  (TERM_TAC ORELSE (PRINT_GOAL_TAC THEN NO_TAC));;

let bvl_to_bvi_compile_exps_def = sem1aux_def_wf
  `MEASURE (\p:num # bvl_exp list. list_size bvl_exp_size (SND p))`
  BVIPAUX_B2B_TC_TAC
  `(bvl_to_bvi_compile_exps n [] = ([],Nil,n)) /\
   (bvl_to_bvi_compile_exps n (CONS x (CONS y xs)) =
      let (c1,aux1,n1) = bvl_to_bvi_compile_exps n [x] in
      let (c2,aux2,n2) = bvl_to_bvi_compile_exps n1 (CONS y xs) in
        (APPEND c1 c2,SmartAppend aux1 aux2,n2)) /\
   (bvl_to_bvi_compile_exps n [bvl_Var v] = ([bvi_Var v],Nil,n)) /\
   (bvl_to_bvi_compile_exps n [bvl_If x1 x2 x3] =
      let (c1,aux1,n1) = bvl_to_bvi_compile_exps n [x1] in
      let (c2,aux2,n2) = bvl_to_bvi_compile_exps n1 [x2] in
      let (c3,aux3,n3) = bvl_to_bvi_compile_exps n2 [x3] in
        ([bvi_If (HD c1) (HD c2) (HD c3)],
         SmartAppend (SmartAppend aux1 aux2) aux3,n3)) /\
   (bvl_to_bvi_compile_exps n [bvl_Let xs x2] =
      if NULL xs then
        let (args,x0) = destLet x2 in
        let (c1,aux1,n1) = bvl_to_bvi_compile_exps n args in
        let (c2,aux2,n2) = bvl_to_bvi_compile_exps n1 [x0] in
        let n3 = n2 + 1 in
          ([bvi_Call 0 (SOME (bvl_num_stubs + bvl_to_bvi_namespaces * n2 + 1))
              c1 NONE],
           SmartAppend (SmartAppend aux1 aux2)
             (compile_aux (n2,LENGTH args,HD c2)),n3)
      else
        let (c1,aux1,n1) = bvl_to_bvi_compile_exps n xs in
        let (c2,aux2,n2) = bvl_to_bvi_compile_exps n1 [x2] in
          ([bvi_Let c1 (HD c2)],SmartAppend aux1 aux2,n2)) /\
   (bvl_to_bvi_compile_exps n [bvl_Raise x1] =
      let (c1,aux1,n1) = bvl_to_bvi_compile_exps n [x1] in
        ([bvi_Raise (HD c1)],aux1,n1)) /\
   (bvl_to_bvi_compile_exps n [bvl_Tick x1] =
      let (c1,aux1,n1) = bvl_to_bvi_compile_exps n [x1] in
        ([bvi_Tick (HD c1)],aux1,n1)) /\
   (bvl_to_bvi_compile_exps n [bvl_Force loc v] =
      ([bvi_Force (bvl_num_stubs + bvl_to_bvi_namespaces * loc) v],Nil,n)) /\
   (bvl_to_bvi_compile_exps n [bvl_Op op xs] =
      let (c1,aux1,n1) = bvl_to_bvi_compile_exps n xs in
        ([bvl_to_bvi_compile_op op c1],aux1,n1)) /\
   (bvl_to_bvi_compile_exps n [bvl_Handle x1 x2] =
      let (args,x0) = destLet x1 in
      let (c1,aux1,n1) = bvl_to_bvi_compile_exps n args in
      let (c2,aux2,n2) = bvl_to_bvi_compile_exps n1 [x0] in
      let (c3,aux3,n3) = bvl_to_bvi_compile_exps n2 [x2] in
      let aux4 = compile_aux (n3,LENGTH args,HD c2) in
      let n4 = n3 + 1 in
        ([bvi_Call 0 (SOME (bvl_num_stubs + bvl_to_bvi_namespaces * n3 + 1)) c1
            (SOME (HD c3))],
         SmartAppend (SmartAppend (SmartAppend aux1 aux2) aux3) aux4,n4)) /\
   (bvl_to_bvi_compile_exps n [bvl_Call ticks dest xs] =
      let (c1,aux1,n1) = bvl_to_bvi_compile_exps n xs in
        ([bvi_Call ticks
            (match dest with
               NONE -> NONE
             | SOME n -> SOME (bvl_num_stubs + bvl_to_bvi_namespaces * n)) c1 NONE],
         aux1,n1))`;;

let bvl_to_bvi_compile_exps_ind = cake_ind "bvl_to_bvi_compile_exps";;

let compile_exps_sing_def = sem1aux_def_wf
  `MEASURE (\x:(num # bvl_exp) + (num # bvl_exp list).
              sum_CASE x (\p. bvl_exp_size (SND p))
                         (\p. list_size bvl_exp_size (SND p)))`
  BVIPAUX_B2B_TC_TAC
  `(compile_exps_sing n (bvl_Var v) = (bvi_Var v,Nil,n)) /\
   (compile_exps_sing n (bvl_If x1 x2 x3) =
      let (c1,aux1,n1) = compile_exps_sing n x1 in
      let (c2,aux2,n2) = compile_exps_sing n1 x2 in
      let (c3,aux3,n3) = compile_exps_sing n2 x3 in
        (bvi_If c1 c2 c3,SmartAppend (SmartAppend aux1 aux2) aux3,n3)) /\
   (compile_exps_sing n (bvl_Let xs x2) =
      if NULL xs then
        let (args,x0) = destLet x2 in
        let (c1,aux1,n1) = compile_exps_list n args in
        let (c2,aux2,n2) = compile_exps_sing n1 x0 in
        let n3 = n2 + 1 in
          (bvi_Call 0 (SOME (bvl_num_stubs + bvl_to_bvi_namespaces * n2 + 1)) c1
             NONE,
           SmartAppend (SmartAppend aux1 aux2) (compile_aux (n2,LENGTH args,c2)),
           n3)
      else
        let (c1,aux1,n1) = compile_exps_list n xs in
        let (c2,aux2,n2) = compile_exps_sing n1 x2 in
          (bvi_Let c1 c2,SmartAppend aux1 aux2,n2)) /\
   (compile_exps_sing n (bvl_Raise x1) =
      let (c1,aux1,n1) = compile_exps_sing n x1 in
        (bvi_Raise c1,aux1,n1)) /\
   (compile_exps_sing n (bvl_Tick x1) =
      let (c1,aux1,n1) = compile_exps_sing n x1 in
        (bvi_Tick c1,aux1,n1)) /\
   (compile_exps_sing n (bvl_Force loc v) =
      (bvi_Force (bvl_num_stubs + bvl_to_bvi_namespaces * loc) v,Nil,n)) /\
   (compile_exps_sing n (bvl_Op op xs) =
      let (c1,aux1,n1) = compile_exps_list n xs in
        (bvl_to_bvi_compile_op op c1,aux1,n1)) /\
   (compile_exps_sing n (bvl_Handle x1 x2) =
      let (args,x0) = destLet x1 in
      let (c1,aux1,n1) = compile_exps_list n args in
      let (c2,aux2,n2) = compile_exps_sing n1 x0 in
      let (c3,aux3,n3) = compile_exps_sing n2 x2 in
      let aux4 = compile_aux (n3,LENGTH args,c2) in
      let n4 = n3 + 1 in
        (bvi_Call 0 (SOME (bvl_num_stubs + bvl_to_bvi_namespaces * n3 + 1)) c1
           (SOME c3),
         SmartAppend (SmartAppend (SmartAppend aux1 aux2) aux3) aux4,n4)) /\
   (compile_exps_sing n (bvl_Call ticks dest xs) =
      let (c1,aux1,n1) = compile_exps_list n xs in
        (bvi_Call ticks
           (match dest with
              NONE -> NONE
            | SOME n -> SOME (bvl_num_stubs + bvl_to_bvi_namespaces * n)) c1 NONE,
         aux1,n1)) /\
   (compile_exps_list n [] = ([],Nil,n)) /\
   (compile_exps_list n (CONS x xs) =
      let (c1,aux1,n1) = compile_exps_sing n x in
      let (c2,aux2,n2) = compile_exps_list n1 xs in
        (CONS c1 c2,SmartAppend aux1 aux2,n2))`;;

let compile_exps_sing_ind = cake_ind "compile_exps_sing";;

(* the cases of compile_exps_sing: split the calls of compile_exps_sing,   *)
(* instantiate the induction hypotheses (rewriting compile_exps_list into  *)
(* bvl_to_bvi_compile_exps with the list hypotheses), then evaluate        *)

let BVIPAUX_B2B_LISTEQ_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `compile_exps_list a b = bvl_to_bvi_compile_exps a b`)
         (concl th) then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC));;

let BVIPAUX_B2B_SING_TAC : tactic =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `compile_exps_sing a b = (c,d,e)`) (concl th))) THEN
  REWRITE_TAC[compile_exps_sing_def] THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FS[] THEN
  RES_TAC THEN BVIPAUX_B2B_LISTEQ_TAC THEN RES_TAC THEN BVIPAUX_B2B_LISTEQ_TAC THEN
  RES_TAC THEN BVIPAUX_B2B_LISTEQ_TAC THEN RES_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && is_pair (lhs c) && not (is_pair (rhs c)) then SYM th else th) THEN
  REWRITE_TAC[bvl_to_bvi_compile_exps_def] THEN
  ASM CASE_REWRITE_TAC [HD; LET_DEF; LET_END_DEF];;

let BVIPAUX_B2B_compile_exps_sing = prove
 (`(!n e c au m. compile_exps_sing n e = (c,au,m) ==>
                 bvl_to_bvi_compile_exps n [e] = ([c],au,m)) /\
   (!n es. compile_exps_list n es = bvl_to_bvi_compile_exps n es)`,
  MATCH_MP_TAC compile_exps_sing_ind THEN REPEAT STRIP_TAC THEN
  TRY(BVIPAUX_B2B_SING_TAC THEN NO_TAC) THEN
  TRY(REWRITE_TAC[compile_exps_sing_def; bvl_to_bvi_compile_exps_def] THEN
      NO_TAC) THEN
  REWRITE_TAC[compile_exps_sing_def] THEN REPEAT PAIRARG_TAC THEN FS[] THEN
  RES_TAC THEN RES_TAC THEN
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && is_pair (lhs c) && not (is_pair (rhs c)) then SYM th else th) THEN
  CASES_ON `xs:bvl_exp list` THEN
  FS[bvl_to_bvi_compile_exps_def; SmartAppend_Nil; PAIR_EQ] THEN
  TRY RVEQ_TAC THEN ASM CASE_REWRITE_TAC [APPEND; SmartAppend_Nil]);;

let compile_exps_sing = prove
 (CASE_TERM
  `(!n e. bvl_to_bvi_compile_exps n [e] =
          let (x,y,z) = compile_exps_sing n e in ([x],y,z)) /\
   (!n es. compile_exps_list n es = bvl_to_bvi_compile_exps n es)`,
  REWRITE_TAC[CONJUNCT2 BVIPAUX_B2B_compile_exps_sing] THEN REPEAT GEN_TAC THEN
  REPEAT PAIRARG_TAC THEN
  FIRST_ASSUM(ACCEPT_TAC o MATCH_MP (CONJUNCT1 BVIPAUX_B2B_compile_exps_sing)));;

let compile_exps_LENGTH_lemma = prove
 (`!n xs. LENGTH (FST (bvl_to_bvi_compile_exps n xs)) = LENGTH xs`,
  MATCH_MP_TAC bvl_to_bvi_compile_exps_ind THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[bvl_to_bvi_compile_exps_def] THEN
  REPEAT(PAIRARG_TAC THEN TRY(GVS[])) THEN
  TRY COND_CASES_TAC THEN REPEAT(PAIRARG_TAC THEN TRY(GVS[])) THEN
  GVS[LENGTH; LENGTH_APPEND] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o snd o strip_forall o concl))) THEN
  ASM_SIMP_TAC[FST; LENGTH] THEN ARITH_TAC);;

let bvl_to_bvi_compile_exps_LENGTH = prove
 (`!n xs ys aux n1.
     bvl_to_bvi_compile_exps n xs = (ys,aux,n1) ==> LENGTH ys = LENGTH xs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `xs:bvl_exp list`] compile_exps_LENGTH_lemma) THEN
  ASM_REWRITE_TAC[FST]);;

let bvl_to_bvi_compile_exps_SING = prove
 (`!n x c aux n1.
     bvl_to_bvi_compile_exps n [x] = (c,aux,n1) ==> ?y. c = [y]`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP bvl_to_bvi_compile_exps_LENGTH) THEN
  CASES_ON `c:bvi_exp list` THEN REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ] THEN
  REWRITE_TAC[LENGTH_EQ_NIL; CONS_11] THEN MESON_TAC[]);;

let bvl_to_bvi_compile_single_def = cake_def
  `bvl_to_bvi_compile_single n (name,arg_count,exp) =
     let (c,aux,n1) = bvl_to_bvi_compile_exps n [exp] in
       (SmartAppend
          (misc_List [(bvl_num_stubs + bvl_to_bvi_namespaces * name,arg_count,
                       bvi_let_compile_exp (HD c))]) aux,n1)`;;

let compile_single_eq = prove
 (CASE_TERM
  `!n name arg_count exp.
     bvl_to_bvi_compile_single n (name,arg_count,exp) =
     let (c,aux,n1) = compile_exps_sing n exp in
       (SmartAppend
          (misc_List [(bvl_num_stubs + bvl_to_bvi_namespaces * name,arg_count,
                       bvi_let_compile_exp c)]) aux,n1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_to_bvi_compile_single_def; CONJUNCT1 compile_exps_sing] THEN
  SPEC_TAC(`compile_exps_sing n exp`,
           `p:bvi_exp # (num # num # bvi_exp) app_list # num`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[HD]);;

let bvl_to_bvi_compile_list_def = cake_def
  `(bvl_to_bvi_compile_list n [] = (misc_List [],n)) /\
   (bvl_to_bvi_compile_list n (CONS p progs) =
      let (code1,n1) = bvl_to_bvi_compile_single n p in
      let (code2,n2) = bvl_to_bvi_compile_list n1 progs in
        (SmartAppend code1 code2,n2))`;;

(* incremental version used by Install *)

let bvl_to_bvi_compile_inc_def = cake_def
  `bvl_to_bvi_compile_inc n prog =
     let (p1,n1) = bvl_to_bvi_compile_list n prog in
       (n1,append p1)`;;

let bvl_to_bvi_compile_prog_def = cake_def
  `bvl_to_bvi_compile_prog start n prog =
     let k = alloc_glob_count (MAP (\x. match x with (_,_,p) -> p) prog) in
     let (code,n1) = bvl_to_bvi_compile_list n prog in
       (InitGlobals_location,
        APPEND (bvl_to_bvi_stubs (bvl_num_stubs + bvl_to_bvi_namespaces * start) k)
          (append code),
        n1)`;;

(* HOL4: compile_prog_eq = compile_prog_def |> SRULE [GSYM                  *)
(* alloc_glob_count_eq_global_count_list]                                    *)

let bvl_to_bvi_compile_prog_eq =
  REWRITE_RULE[GSYM (CONJUNCT2 alloc_glob_count_eq_global_count_list)]
    bvl_to_bvi_compile_prog_def;;

(* zero inline_size_limit disables inlining; a huge exp_cut effectively     *)
(* disables exp splitting; split_main_at_seq splits the main expression at  *)
(* Seqs; there should be as many next_name fields as                        *)
(* bvl_to_bvi_namespaces - 1                                                 *)

let bvl_to_bvi_config_INFO = cake_record "bvl_to_bvi_config"
  ["inline_size_limit","num";
   "exp_cut","num";
   "split_main_at_seq","bool";
   "next_name1","num";
   "next_name2","num";
   "next_name3","num";
   "do_tailrec","bool";
   "do_tmc","bool";
   "inlines","(num#bvl_exp)spt";
   "bvi_inlines","(num#bvi_exp)spt"];;

let bvl_to_bvi_config_component_equality =
  bvl_to_bvi_config_INFO.ri_component_equality;;

let bvl_to_bvi_default_config_def = cake_def
  `bvl_to_bvi_default_config =
     bvl_to_bvi_config_REC 10 1000 T (bvl_num_stubs + 1) (bvl_num_stubs + 2)
       (bvl_num_stubs + 3) T T LN LN`;;

let bvl_to_bvi_get_names_def = cake_def
  `bvl_to_bvi_get_names final_nums old_names =
     fromAList (MAP (\n. (n,
       if n = InitGlobals_location then implode "start" else
       if n = AllocGlobal_location then implode "AllocGlobal" else
       if n = CopyGlobals_location then implode "CopyGlobals" else
       if n = ListLength_location then implode "ListLength" else
       if n = FromListByte_location then implode "FromListByte" else
       if n = ToListByte_location then implode "ToListByte" else
       if n = SumListLength_location then implode "SumListLength" else
       if n = ConcatByte_location then implode "ConcatByte" else
       if n < bvl_num_stubs then implode "bvi_unknown" else
         let k = n - bvl_num_stubs in
         let kd = k DIV bvl_to_bvi_namespaces in
         let km = k MOD bvl_to_bvi_namespaces in
         let n = (match lookup kd old_names with
                    NONE -> implode "bvi_unmapped"
                  | SOME name -> name) in
         let aux = (if km = 0 then implode "" else implode "_bvi_aux") in
           strcat n aux)) final_nums)`;;

let bvl_to_bvi_compile_def = cake_def
  `bvl_to_bvi_compile start c names prog =
     let (inlines,prog) =
       bvl_inline_compile_prog (bvl_to_bvi_config_inline_size_limit c)
         (bvl_to_bvi_config_split_main_at_seq c) (bvl_to_bvi_config_exp_cut c)
         prog in
     let (loc,code,n1) = bvl_to_bvi_compile_prog start 0 prog in
     let (n2,code') =
       bvi_tailrec_compile_prog (bvl_to_bvi_config_do_tailrec c)
         (bvl_num_stubs + 2) code in
     let (n3,code') =
       bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc c) (bvl_num_stubs + 3)
         code' in
     let (bvi_inlines,code') = bvi_inline_compile_prog code' in
       (loc,code',inlines,bvi_inlines,n1,n2,n3,
        bvl_to_bvi_get_names (MAP FST code') names)`;;

let bvl_to_bvi_compile_inc_all_def = cake_def
  `bvl_to_bvi_compile_inc_all c p =
     let (inl,p) =
       bvl_inline_compile_inc (bvl_to_bvi_config_inline_size_limit c)
         (bvl_to_bvi_config_split_main_at_seq c) (bvl_to_bvi_config_exp_cut c)
         (bvl_to_bvi_config_inlines c) p in
     let c = bvl_to_bvi_config_inlines_fupd (K inl) c in
     let (nn1,p) = bvl_to_bvi_compile_inc (bvl_to_bvi_config_next_name1 c) p in
     let c = bvl_to_bvi_config_next_name1_fupd (K nn1) c in
     let (nn2,p) =
       bvi_tailrec_compile_prog (bvl_to_bvi_config_do_tailrec c)
         (bvl_to_bvi_config_next_name2 c) p in
     let c = bvl_to_bvi_config_next_name2_fupd (K nn2) c in
     let (nn3,p) =
       bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc c)
         (bvl_to_bvi_config_next_name3 c) p in
     let c = bvl_to_bvi_config_next_name3_fupd (K nn3) c in
     let (bvi_inlines,p) =
       bvi_inline_compile_inc (bvl_to_bvi_config_bvi_inlines c) p in
     let c = bvl_to_bvi_config_bvi_inlines_fupd (K bvi_inlines) c in
       (c,p)`;;
