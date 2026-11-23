(* ========================================================================= *)
(* data_space: port of HOL4 compiler/backend/data_spaceScript.sml           *)
(* (CakeML v3479).                                                           *)
(* This dataLang phase lumps together MakeSpace operations. Each MakeSpace   *)
(* operations corresponds to a memory allocation in the later wordLang code. *)
(* By lumping together MakeSpace operations we turn several calls to the     *)
(* memory allocator into a single efficient call.                            *)
(*                                                                           *)
(* Notes on the rendering: Num (ABS i) is num_of_int (abs i); HOL4 () is     *)
(* one; HOL4's pmatch is a match (case constants); op_space_req and space  *)
(* (catch-all clauses completed into one clause per remaining constructor)  *)
(* are defined with sem1aux_def (semantics/sem1aux_tfl.ml).                  *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/dataLang.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

let num_size_def = cake_def_wf `MEASURE (\n:num. n)`
  (REWRITE_TAC[measure_THM] THEN CONV_TAC NUM_REDUCE_CONV THEN
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC)
  `num_size (n:num) =
     if n < 2 EXP 32 then 2 else 1 + num_size (n DIV 2 EXP 32)`;;

let num_size_ind = cake_ind "num_size";;

let part_space_req_def = cake_def_clauses
  [`part_space_req (clos_W64 s) = 3`;
   `part_space_req (clos_Int i) =
      if num_of_int (abs i) < 2 EXP 29 then 0 else num_size (num_of_int (abs i))`;
   `part_space_req (clos_Str s) = strlen s DIV 4 + 2`;
   `part_space_req (clos_Con t ns) =
      let l = LENGTH ns in if l = 0 then 0 else l + 1`];;

(* HOL4's clause op_space_req (WordOp (WordFromWord F)) _ = 3 has the       *)
(* literal pattern F, whose catch-all completion (the clause for T) the     *)
(* definition package does not make: the definition takes the two cases as *)
(* one clause with an if, and op_space_req_def has HOL4's clauses for F and *)
(* T instead of it                                                          *)

let op_space_req_def =
  let th = sem1aux_def
   `(op_space_req (MemOp clos_Ref) l = l + 1) /\
    (op_space_req (MemOp (MutCons tag k)) l = l + 1) /\
    (op_space_req (BlockOp (clos_Cons _)) l = if l = 0 then 0 else l + 1) /\
    (op_space_req (BlockOp (Build parts)) l = SUM (MAP part_space_req parts)) /\
    (op_space_req (WordOp (WordOpw W64 _)) _ = 3) /\
    (op_space_req (WordOp (WordShift W64 _ _)) _ = 3) /\
    (op_space_req (WordOp WordFromInt) _ = 3) /\
    (op_space_req (WordOp WordToInt) _ = 3) /\
    (op_space_req (WordOp (WordFromWord b)) _ = if b then 0 else 3) /\
    (op_space_req (WordOp (FP_uop _)) _ = 3) /\
    (op_space_req (WordOp (FP_bop _)) _ = 3) /\
    (op_space_req (WordOp (FP_top _)) _ = 3) /\
    (op_space_req (clos_ThunkOp (AllocThunk _)) l = l + 1) /\
    (op_space_req _ _ = 0)` in
  let is_wfw c =
    can (find_term (fun t -> is_comb t && rator t = `WordFromWord` &&
                             is_var (rand t))) (concl c) in
  let split c =
    if not (is_wfw c) then [c] else
    let c0 = SPEC_ALL c in
    let b = rand (find_term (fun t -> is_comb t && rator t = `WordFromWord`)
                   (concl c0)) in
    map (fun v -> GEN_ALL (REWRITE_RULE[] (INST [v,b] c0))) [`F`; `T`] in
  end_itlist CONJ (flat (map split (CONJUNCTS th)));;

let pMakeSpace_def = cake_def
  `(pMakeSpace (INL c) = c) /\
   (pMakeSpace (INR (k,names,c)) = data_Seq (MakeSpace k names) c)`;;

let space_def = sem1aux_def
  `(space (MakeSpace k names) = INR (k,names,data_Skip)) /\
   (space (data_Seq c1 c2) =
      let d1 = pMakeSpace (space c1) in
      let x2 = space c2 in
        match x2 with
          INL c4 ->
            (match c1 with
               MakeSpace k names -> INR (k,names,c4)
             | data_Skip -> INL c4
             | _ -> INL (data_Seq d1 c4))
        | INR (k2,names2,c4) ->
            (match c1 with
               data_Skip -> INR (k2,names2,c4)
             | MakeSpace k1 names1 -> INR (k2,sptree_inter names1 names2,c4)
             | data_Move dest src ->
                 INR (k2,insert src one (delete dest names2),
                      data_Seq (data_Move dest src) c4)
             | data_Assign dest op args NONE ->
                 INR (op_space_req op (LENGTH args) + k2,
                      list_insert args (delete dest names2),
                      data_Seq (data_Assign dest op args NONE) c4)
             | _ -> INL (data_Seq d1 (pMakeSpace x2)))) /\
   (space (data_If n c2 c3) =
      INL (data_If n (pMakeSpace (space c2)) (pMakeSpace (space c3)))) /\
   (space c = INL c)`;;

let space_ind = cake_ind "space";;

(* HOL4: space_pmatch *)

let space_pmatch = prove
 (CASE_TERM
  `!c. space c =
     match c with
       MakeSpace k names -> INR (k,names,data_Skip)
     | data_Seq c1 c2 ->
         (let d1 = pMakeSpace (space c1) in
          let x2 = space c2 in
            match x2 with
              INL c4 ->
                (match c1 with
                   MakeSpace k names -> INR (k,names,c4)
                 | data_Skip -> INL c4
                 | _ -> INL (data_Seq d1 c4))
            | INR (k2,names2,c4) ->
                (match c1 with
                   data_Skip -> INR (k2,names2,c4)
                 | MakeSpace k1 names1 -> INR (k2,sptree_inter names1 names2,c4)
                 | data_Move dest src ->
                     INR (k2,insert src one (delete dest names2),
                          data_Seq (data_Move dest src) c4)
                 | data_Assign dest op args NONE ->
                     INR (op_space_req op (LENGTH args) + k2,
                          list_insert args (delete dest names2),
                          data_Seq (data_Assign dest op args NONE) c4)
                 | _ -> INL (data_Seq d1 (pMakeSpace x2))))
     | data_If n c2 c3 ->
         INL (data_If n (pMakeSpace (space c2)) (pMakeSpace (space c3)))
     | c -> INL c`,
  GEN_TAC THEN CASES_ON `c:data_prog` THEN REWRITE_TAC[space_def] THEN
  CASE_REWRITE_TAC[]);;

let data_space_compile_def = cake_def
  `data_space_compile c = pMakeSpace (space c)`;;
