(* ========================================================================= *)
(* bvlSem: port of HOL4 compiler/backend/semantics/bvlSemScript.sml         *)
(* (CakeML v3479).  The formal semantics of BVL.                             *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 num_map is A spt; word8 is byte, word64 is int64.                  *)
(* - HOL4 r with <| f1 := x; f2 := y |> is f1_fupd (K x) (f2_fupd (K y) r);  *)
(*   Error is Rerr (Rabort Rtype_error), written out.                        *)
(* - Clauses whose variables have different types in different clauses are  *)
(*   parsed in separate quotations (HOL4 types each clause on its own).     *)
(* - Lemmas named CLOSSEMAUX_ are helpers of the unit (not HOL4 names).     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/sptree.ml";;
needs "hol4/lprefix_lub.ml";;
needs "semantics/ffi/ffi.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/bvl.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* --- Semantics of BVL --- *)

(* ByteArray T = compare-by-contents, immutable; ByteArray F =               *)
(* compare-by-pointer, mutable.  In closLang all are ByteArray F, ByteArray *)
(* T is introduced in BVL to implement ByteVector                           *)

let bvl_ref_INDUCT,bvl_ref_RECURSION = cake_type
  "bvl_ref = bvl_ValueArray (A list)
           | bvl_ByteArray bool (byte list)
           | bvl_Thunk thunk_mode A
           | MutBlock num bool (A list) A (A list)";;

(* these parts are shared by bytecode and, if bytecode is to be supported,  *)
(* need to move to a common ancestor                                         *)

(* bvl_Number: integer; bvl_Word64: 64-bit word; bvl_Block: cons block, tag *)
(* and payload; bvl_CodePtr: code pointer; bvl_RefPtr: pointer to ref cell, *)
(* the bool is T if the Eq test is allowed                                   *)

let bvl_v_INDUCT,bvl_v_RECURSION = cake_type
  "bvl_v = bvl_Number int
         | bvl_Word64 int64
         | bvl_Block num (bvl_v list)
         | bvl_CodePtr num
         | bvl_RefPtr bool num";;

let bvl_Boolv_def = cake_def
  `bvl_Boolv b = bvl_Block (bool_to_tag b) []`;;

let bvl_Unit_def = cake_def
  `bvl_Unit = bvl_Block tuple_tag []`;;

let bvl_state_INFO = cake_record "bvl_state"
  ["globals","(bvl_v option) list";
   "refs","(num,(bvl_v)bvl_ref)fmap";
   "clock","num";
   "compile","C -> (num # num # bvl_exp) list -> (byte list # int64 list # C) option";
   "compile_oracle","num -> C # (num # num # bvl_exp) list";
   "code","(num # bvl_exp) spt";
   "ffi","(FFI)ffi_state"];;

let bvl_state_component_equality = bvl_state_INFO.ri_component_equality;;

let bvl_v_to_list_def = sem1aux_def_wf
  `MEASURE bvl_v_size`
  SEM1AUX_TC_TAC
  `(bvl_v_to_list (bvl_Block tag []) =
      if tag = nil_tag then SOME [] else NONE) /\
   (bvl_v_to_list (bvl_Block tag [h; bt]) =
      if tag = cons_tag then
        (match bvl_v_to_list bt with
           SOME t -> SOME (CONS h t)
         | _ -> NONE)
      else NONE) /\
   (bvl_v_to_list _ = NONE)`;;

let bvl_v_to_list_ind = cake_ind "bvl_v_to_list";;

let bvl_list_to_v_def = cake_def
  `(bvl_list_to_v [] = bvl_Block nil_tag []) /\
   (bvl_list_to_v (CONS v vs) = bvl_Block cons_tag [v; bvl_list_to_v vs])`;;

let bvl_isClos_def = cake_def
  `bvl_isClos t1 (l1:A list) <=>
     (t1 = closure_tag \/ t1 = partial_app_tag) /\ ~(l1 = [])`;;

(* HOL4 infers the most general type: refs is a map to (A)bvl_ref *)

let bvl_do_eq_def = sem1aux_def_wf
  `inv_image (<)
     (\x:((num,(A)bvl_ref)fmap # bvl_v # bvl_v) +
         ((num,(A)bvl_ref)fmap # bvl_v list # bvl_v list).
        sum_CASE x (\t. bvl_v_size (FST (SND t)))
                   (\t. list_size bvl_v_size (FST (SND t))))`
  SEM1AUX_TC_TAC
  (list_mk_conj
  [`bvl_do_eq (_:(num,(A)bvl_ref)fmap) (bvl_CodePtr _) (_:bvl_v) = Eq_type_error`;
   `bvl_do_eq (_:(num,(A)bvl_ref)fmap) (_:bvl_v) (bvl_CodePtr _) = Eq_type_error`;
   `bvl_do_eq (_:(num,(A)bvl_ref)fmap) (bvl_Number n1) (bvl_Number n2) =
      Eq_val (n1 = n2)`;
   `bvl_do_eq (_:(num,(A)bvl_ref)fmap) (bvl_Number _) (_:bvl_v) = Eq_type_error`;
   `bvl_do_eq (_:(num,(A)bvl_ref)fmap) (_:bvl_v) (bvl_Number _) = Eq_type_error`;
   `bvl_do_eq (_:(num,(A)bvl_ref)fmap) (bvl_Word64 w1) (bvl_Word64 w2) =
      Eq_val (w1 = w2)`;
   `bvl_do_eq (_:(num,(A)bvl_ref)fmap) (bvl_Word64 _) (_:bvl_v) = Eq_type_error`;
   `bvl_do_eq (_:(num,(A)bvl_ref)fmap) (_:bvl_v) (bvl_Word64 _) = Eq_type_error`;
   `bvl_do_eq (refs:(num,(A)bvl_ref)fmap) (bvl_RefPtr b1 n1) (bvl_RefPtr b2 n2) =
      if b1 /\ b2 then
        (match (FLOOKUP refs n1, FLOOKUP refs n2) with
           (SOME (bvl_ByteArray T bs1), SOME (bvl_ByteArray T bs2)) ->
             Eq_val (bs1 = bs2)
         | (SOME (bvl_ByteArray T bs1), _) -> Eq_type_error
         | (_, SOME (bvl_ByteArray T bs2)) -> Eq_type_error
         | _ -> Eq_val (n1 = n2))
      else Eq_type_error`;
   `bvl_do_eq (_:(num,(A)bvl_ref)fmap) (bvl_RefPtr _ _) (_:bvl_v) = Eq_type_error`;
   `bvl_do_eq (_:(num,(A)bvl_ref)fmap) (_:bvl_v) (bvl_RefPtr _ _) = Eq_type_error`;
   `bvl_do_eq (refs:(num,(A)bvl_ref)fmap) (bvl_Block t1 l1) (bvl_Block t2 l2) =
      if bvl_isClos t1 l1 \/ bvl_isClos t2 l2
      then if bvl_isClos t1 l1 /\ bvl_isClos t2 l2 then Eq_val T else Eq_type_error
      else if t1 = t2 /\ LENGTH l1 = LENGTH l2
           then bvl_do_eq_list refs l1 l2
           else Eq_val F`;
   `bvl_do_eq_list (_:(num,(A)bvl_ref)fmap) ([]:bvl_v list) ([]:bvl_v list) =
      Eq_val T`;
   `bvl_do_eq_list (refs:(num,(A)bvl_ref)fmap) (CONS (v1:bvl_v) vs1) (CONS (v2:bvl_v) vs2) =
      match bvl_do_eq refs v1 v2 with
        Eq_val T -> bvl_do_eq_list refs vs1 vs2
      | Eq_val F -> Eq_val F
      | bad -> bad`;
   `bvl_do_eq_list (_:(num,(A)bvl_ref)fmap) (_:bvl_v list) (_:bvl_v list) =
      Eq_val F`]);;
let _ = cake_add_simps [bvl_do_eq_def];;

let bvl_do_eq_ind = cake_ind "bvl_do_eq";;

(* HOL4: Overload Error[local] = Rerr (Rabort Rtype_error) (written out) *)

let bvl_v_to_bytes_def = cake_def
  `bvl_v_to_bytes lv = some ns:byte list.
     bvl_v_to_list lv = SOME (MAP (bvl_Number o int_of_num o val) ns)`;;

let bvl_v_to_words_def = cake_def
  `bvl_v_to_words lv = some ns:int64 list.
     bvl_v_to_list lv = SOME (MAP bvl_Word64 ns)`;;

(* HOL4 infers the most general type: the exception type E is free *)
let bvl_do_install_def = cake_def
  `bvl_do_install vs (s:(C,FFI)bvl_state) =
     match vs with
       [v1; v2] ->
         (match (bvl_v_to_bytes v1, bvl_v_to_words v2) with
            (SOME bytes, SOME data) ->
              let (cfg,progs) = bvl_state_compile_oracle s 0 in
              let new_oracle = shift_seq 1 (bvl_state_compile_oracle s) in
              (if DISJOINT (domain (bvl_state_code s)) (set_of_list (MAP FST progs)) /\
                  ALL_DISTINCT (MAP FST progs) then
               (match (bvl_state_compile s cfg progs, progs) with
                  (SOME (bytes',data',cfg'), CONS (k,prog) _) ->
                    if bytes = bytes' /\ data = data' /\ FST (new_oracle 0) = cfg' then
                      let s' =
                        bvl_state_code_fupd (K (sptree_union (bvl_state_code s) (fromAList progs)))
                          (bvl_state_compile_oracle_fupd (K new_oracle) s)
                      in
                        Rval (bvl_CodePtr k, s')
                    else Rerr (Rabort Rtype_error)
                | _ -> Rerr (Rabort Rtype_error))
               else Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | _ -> (Rerr (Rabort Rtype_error):(bvl_v # (C,FFI)bvl_state,E)result)`;;

let bvl_do_part_def = sem1aux_def (list_mk_conj
  [`bvl_do_part (m:num->bvl_v) (clos_Int i) (refs:(num,(bvl_v)bvl_ref)fmap) =
      (bvl_Number i, refs)`;
   `bvl_do_part (m:num->bvl_v) (clos_W64 w) (refs:(num,(bvl_v)bvl_ref)fmap) =
      (bvl_Word64 w, refs)`;
   `bvl_do_part (m:num->bvl_v) (clos_Con t ns) (refs:(num,(bvl_v)bvl_ref)fmap) =
      (bvl_Block t (MAP m ns), refs)`;
   `bvl_do_part (m:num->bvl_v) (clos_Str t) (refs:(num,(bvl_v)bvl_ref)fmap) =
      let ptr = (minimal ptr. ~(ptr IN FDOM refs)) in
      let bytes = MAP (word o ORD) (explode t) in
        (bvl_RefPtr T ptr, refs |+ (ptr,(bvl_ByteArray T bytes:(bvl_v)bvl_ref)))`]);;

let bvl_do_build_def = cake_def
  `(bvl_do_build (m:num->bvl_v) i [] (refs:(num,(bvl_v)bvl_ref)fmap) =
      (m (i - 1), refs)) /\
   (bvl_do_build m i (CONS p rest) refs =
      let (x,refs1) = bvl_do_part m p refs in
        bvl_do_build ((i =+ x) m) (i + 1) rest refs1)`;;

let bvl_do_build_const_def = cake_def
  `bvl_do_build_const xs (refs:(num,(bvl_v)bvl_ref)fmap) =
     bvl_do_build (\x. bvl_Number (&0)) 0 xs refs`;;

(* same as closSem's do_int_app *)
let bvl_do_int_app_def = sem1aux_def (list_mk_conj
  [`bvl_do_int_app (clos_Const n) ([]:bvl_v list) = SOME (bvl_Number n)`;
   `bvl_do_int_app clos_Add [bvl_Number n1; bvl_Number n2] =
      SOME (bvl_Number (n1 + n2))`;
   `bvl_do_int_app clos_Sub [bvl_Number n1; bvl_Number n2] =
      SOME (bvl_Number (n1 - n2))`;
   `bvl_do_int_app Mult [bvl_Number n1; bvl_Number n2] =
      SOME (bvl_Number (n1 * n2))`;
   `bvl_do_int_app clos_Div [bvl_Number n1; bvl_Number n2] =
      (if n2 = &0 then NONE else SOME (bvl_Number (int_div n1 n2)))`;
   `bvl_do_int_app clos_Mod [bvl_Number n1; bvl_Number n2] =
      (if n2 = &0 then NONE else SOME (bvl_Number (integer_int_mod n1 n2)))`;
   `bvl_do_int_app clos_Less [bvl_Number n1; bvl_Number n2] =
      SOME (bvl_Boolv (n1 < n2))`;
   `bvl_do_int_app LessEq [bvl_Number n1; bvl_Number n2] =
      SOME (bvl_Boolv (n1 <= n2))`;
   `bvl_do_int_app Greater [bvl_Number n1; bvl_Number n2] =
      SOME (bvl_Boolv (n1 > n2))`;
   `bvl_do_int_app GreaterEq [bvl_Number n1; bvl_Number n2] =
      SOME (bvl_Boolv (n1 >= n2))`;
   `bvl_do_int_app (LessConstSmall n) [bvl_Number i] =
      (if &0 <= i /\ i <= &1000000 /\ n < 1000000 then
         SOME (bvl_Boolv (i < &n)) else NONE)`;
   `bvl_do_int_app (op:int_op) (vs:bvl_v list) = (NONE:bvl_v option)`]);;

(* The induction theorem of a definition without recursion, with one case  *)
(* per completed clause (HOL4 TFL makes one for multi-clause definitions);   *)
(* derived from the clauses with the kit's derive_induction                  *)

let CLOSSEMAUX_cases_ind (def:thm) =
  let cls = map (fun c -> let vs,eq = strip_forall(concl c) in
                          let _,args = strip_comb(lhs eq) in vs,args)
                (CONJUNCTS def) in
  let c = fst(strip_comb(lhs(snd(strip_forall(concl(hd(CONJUNCTS def))))))) in
  let tty = mk_tuple_ty (map type_of (snd(hd cls))) in
  let wfth = ISPEC (mk_abs(mk_var("p",tty),`0`)) WF_MEASURE in
  derive_induction c cls [] wfth;;

let CLOSSEMAUX_do_int_app_cases = CLOSSEMAUX_cases_ind bvl_do_int_app_def;;

let CLOSSEMAUX_do_int_app_some = prove
 (`!op vs res.
     bvl_do_int_app op vs = SOME res ==>
     (?n. op = clos_Const n /\ vs = [] /\ res = bvl_Number n) \/
     (?n1 n2. op = clos_Add /\ vs = [bvl_Number n1; bvl_Number n2] /\
              res = bvl_Number (n1 + n2)) \/
     (?n1 n2. op = clos_Sub /\ vs = [bvl_Number n1; bvl_Number n2] /\
              res = bvl_Number (n1 - n2)) \/
     (?n1 n2. op = Mult /\ vs = [bvl_Number n1; bvl_Number n2] /\
              res = bvl_Number (n1 * n2)) \/
     (?n1 n2. op = clos_Div /\ vs = [bvl_Number n1; bvl_Number n2] /\ ~(n2 = &0) /\
              res = bvl_Number (int_div n1 n2)) \/
     (?n1 n2. op = clos_Mod /\ vs = [bvl_Number n1; bvl_Number n2] /\ ~(n2 = &0) /\
              res = bvl_Number (integer_int_mod n1 n2)) \/
     (?n1 n2. op = clos_Less /\ vs = [bvl_Number n1; bvl_Number n2] /\
              res = bvl_Boolv (n1 < n2)) \/
     (?n1 n2. op = LessEq /\ vs = [bvl_Number n1; bvl_Number n2] /\
              res = bvl_Boolv (n1 <= n2)) \/
     (?n1 n2. op = Greater /\ vs = [bvl_Number n1; bvl_Number n2] /\
              res = bvl_Boolv (n1 > n2)) \/
     (?n1 n2. op = GreaterEq /\ vs = [bvl_Number n1; bvl_Number n2] /\
              res = bvl_Boolv (n1 >= n2)) \/
     (?n i. op = LessConstSmall n /\ vs = [bvl_Number i] /\ &0 <= i /\
            i <= &1000000 /\ n < 1000000 /\ res = bvl_Boolv (i < &n))`,
  MATCH_MP_TAC CLOSSEMAUX_do_int_app_cases THEN
  REWRITE_TAC[bvl_do_int_app_def; option_DISTINCT; option_INJ] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY COND_CASES_TAC THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[]);;

let do_int_app_eq_some = prove
 (`!vs res.
     (!n. bvl_do_int_app (clos_Const n) vs = SOME res ==>
          vs = [] /\ res = bvl_Number n) /\
     (bvl_do_int_app clos_Add vs = SOME res ==>
      ?n1 n2. vs = [bvl_Number n1; bvl_Number n2] /\ res = bvl_Number (n1 + n2)) /\
     (bvl_do_int_app clos_Sub vs = SOME res ==>
      ?n1 n2. vs = [bvl_Number n1; bvl_Number n2] /\ res = bvl_Number (n1 - n2)) /\
     (bvl_do_int_app Mult vs = SOME res ==>
      ?n1 n2. vs = [bvl_Number n1; bvl_Number n2] /\ res = bvl_Number (n1 * n2)) /\
     (bvl_do_int_app clos_Div vs = SOME res ==>
      ?n1 n2. vs = [bvl_Number n1; bvl_Number n2] /\ ~(n2 = &0) /\
              res = bvl_Number (int_div n1 n2)) /\
     (bvl_do_int_app clos_Mod vs = SOME res ==>
      ?n1 n2. vs = [bvl_Number n1; bvl_Number n2] /\ ~(n2 = &0) /\
              res = bvl_Number (integer_int_mod n1 n2)) /\
     (bvl_do_int_app clos_Less vs = SOME res ==>
      ?n1 n2. vs = [bvl_Number n1; bvl_Number n2] /\ res = bvl_Boolv (n1 < n2)) /\
     (bvl_do_int_app LessEq vs = SOME res ==>
      ?n1 n2. vs = [bvl_Number n1; bvl_Number n2] /\ res = bvl_Boolv (n1 <= n2)) /\
     (bvl_do_int_app Greater vs = SOME res ==>
      ?n1 n2. vs = [bvl_Number n1; bvl_Number n2] /\ res = bvl_Boolv (n1 > n2)) /\
     (bvl_do_int_app GreaterEq vs = SOME res ==>
      ?n1 n2. vs = [bvl_Number n1; bvl_Number n2] /\ res = bvl_Boolv (n1 >= n2)) /\
     (!n. bvl_do_int_app (LessConstSmall n) vs = SOME res ==>
          ?i. vs = [bvl_Number i] /\ &0 <= i /\ i <= &1000000 /\ n < 1000000 /\
              res = bvl_Boolv (i < &n))`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP CLOSSEMAUX_do_int_app_some) THEN
  REWRITE_TAC[distinctness "int_op"; injectivity "int_op"] THEN
  MESON_TAC[]);;

(* same as closSem's do_word_app; HOL4's clauses for WordFromWord T and     *)
(* WordFromWord F (literal patterns) are written with WordFromWord b and a  *)
(* condition (the kit does not complete clauses with literal patterns)      *)

let bvl_do_word_app_def = sem1aux_def (list_mk_conj
  [`bvl_do_word_app (WordOpw W8 opw) [bvl_Number n1; bvl_Number n2] =
      (match some (w1:byte,w2:byte). n1 = &(val w1) /\ n2 = &(val w2) with
         NONE -> NONE
       | SOME (w1,w2) -> SOME (bvl_Number (&(val (opw_lookup opw w1 w2)))))`;
   `bvl_do_word_app (WordOpw W64 opw) [bvl_Word64 w1; bvl_Word64 w2] =
      SOME (bvl_Word64 (opw_lookup opw w1 w2))`;
   `bvl_do_word_app (WordTest W8 test) [bvl_Number n1; bvl_Number n2] =
      (if &0 <= n1 /\ n1 < &256 /\ &0 <= n2 /\ n2 < &256 then
         (match test with
            Equal -> SOME (bvl_Boolv (n1 = n2))
          | Compare cmp -> SOME (bvl_Boolv (int_cmp cmp n1 n2))
          | _ -> NONE)
       else NONE)`;
   `bvl_do_word_app (WordShift W8 sh n) [bvl_Number i] =
      (match some (w:byte). i = &(val w) with
         NONE -> NONE
       | SOME w -> SOME (bvl_Number (&(val (shift_lookup sh w n)))))`;
   `bvl_do_word_app (WordShift W64 sh n) [bvl_Word64 w] =
      SOME (bvl_Word64 (shift_lookup sh w n))`;
   `bvl_do_word_app WordFromInt [bvl_Number i] =
      SOME (bvl_Word64 (iword i))`;
   `bvl_do_word_app WordToInt [bvl_Word64 w] =
      SOME (bvl_Number (&(val w)))`;
   `bvl_do_word_app (WordFromWord b) [bvl_Word64 w] =
      if b then SOME (bvl_Number (&(val ((word_zx:int64->byte) w))))
      else NONE`;
   `bvl_do_word_app (WordFromWord b) [bvl_Number n] =
      if b then NONE else
      (match some (w:byte). n = &(val w) with
         NONE -> NONE
       | SOME w -> SOME (bvl_Word64 (word_zx w)))`;
   `bvl_do_word_app (FP_top t_op) ws =
      (match ws with
         [bvl_Word64 w1; bvl_Word64 w2; bvl_Word64 w3] ->
           SOME (bvl_Word64 (fp_top_comp t_op w1 w2 w3))
       | _ -> NONE)`;
   `bvl_do_word_app (FP_bop bop) ws =
      (match ws with
         [bvl_Word64 w1; bvl_Word64 w2] ->
           SOME (bvl_Word64 (fp_bop_comp bop w1 w2))
       | _ -> NONE)`;
   `bvl_do_word_app (FP_uop uop) ws =
      (match ws with
         [bvl_Word64 w] -> SOME (bvl_Word64 (fp_uop_comp uop w))
       | _ -> NONE)`;
   `bvl_do_word_app (FP_cmp cmp) ws =
      (match ws with
         [bvl_Word64 w1; bvl_Word64 w2] ->
           SOME (bvl_Boolv (fp_cmp_comp cmp w1 w2))
       | _ -> NONE)`;
   `bvl_do_word_app (op:word_op) (vs:bvl_v list) = (NONE:bvl_v option)`]);;

(* HOL4's do_word_app_ind (the case split of the completed clauses) *)
let bvl_do_word_app_ind = CLOSSEMAUX_cases_ind bvl_do_word_app_def;;

let bvl_dest_thunk_ret_INDUCT,bvl_dest_thunk_ret_RECURSION = cake_type
  "bvl_dest_thunk_ret = bvl_BadRef
                      | bvl_NotThunk
                      | bvl_IsThunk thunk_mode bvl_v";;

let bvl_dest_thunk_def = sem1aux_def
  `(bvl_dest_thunk (bvl_RefPtr b ptr) (refs:(num,(bvl_v)bvl_ref)fmap) =
      match FLOOKUP refs ptr with
        NONE -> bvl_BadRef
      | SOME (bvl_Thunk Evaluated v) ->
          if b then bvl_BadRef else bvl_IsThunk Evaluated v
      | SOME (bvl_Thunk NotEvaluated v) ->
          if b then bvl_BadRef else bvl_IsThunk NotEvaluated v
      | SOME _ -> bvl_NotThunk) /\
   (bvl_dest_thunk _ refs = bvl_NotThunk)`;;

let bvl_bad_thunk_update_def = cake_def
  `bvl_bad_thunk_update m v (refs:(num,(bvl_v)bvl_ref)fmap) <=>
     m = Evaluated /\ ~(bvl_dest_thunk v refs = bvl_NotThunk)`;;

(* same as closSem's do_app, except: LengthByteVec and DerefByteVec are     *)
(* removed; FromListByte, ToListByte, String, ConcatByteVec and CopyByte    *)
(* work on ByteArrays rather than ByteVectors; Build now has full           *)
(* semantics, i.e. can handle all cases; Label is added                     *)

let bvl_do_app_def = cake_def
  `bvl_do_app (op:clos_op) (vs:bvl_v list) (s:(C,FFI)bvl_state) =
     match (op,vs) with
       (GlobOp (clos_Global n),[]) ->
         (match get_global n (bvl_state_globals s) with
            SOME (SOME v) -> Rval (v,s)
          | _ -> Rerr (Rabort Rtype_error))
     | (GlobOp (clos_Global _),[bvl_Number i]) ->
         (if i < &0 then Rerr (Rabort Rtype_error) else
          match get_global (num_of_int i + num_added_globals) (bvl_state_globals s) with
            SOME (SOME v) -> Rval (v,s)
          | _ -> Rerr (Rabort Rtype_error))
     | (GlobOp (SetGlobal n),[v]) ->
         (match get_global n (bvl_state_globals s) with
            SOME _ -> Rval (bvl_Unit,
              bvl_state_globals_fupd (K (LUPDATE (SOME v) n (bvl_state_globals s))) s)
          | _ -> Rerr (Rabort Rtype_error))
     | (GlobOp AllocGlobal,[bvl_Number i]) ->
         (if i < &0 then Rerr (Rabort Rtype_error)
          else Rval (bvl_Unit, bvl_state_globals_fupd
                 (K (APPEND (bvl_state_globals s) (REPLICATE (num_of_int i) NONE))) s))
     | (clos_Install,vs) -> bvl_do_install vs s
     | (BlockOp (clos_Cons tag),xs) -> Rval (bvl_Block tag xs, s)
     | (BlockOp (BoolTest test),[v1; v2]) ->
         (if ~(v1 = bvl_Boolv T) /\ ~(v1 = bvl_Boolv F) then Rerr (Rabort Rtype_error)
          else if ~(v2 = bvl_Boolv T) /\ ~(v2 = bvl_Boolv F) then
            Rerr (Rabort Rtype_error)
          else Rval (bvl_Boolv (v1 = v2), s))
     | (BlockOp BoolNot,[v1]) ->
         (if v1 = bvl_Boolv T then Rval (bvl_Boolv F, s) else
          if v1 = bvl_Boolv F then Rval (bvl_Boolv T, s) else Rerr (Rabort Rtype_error))
     | (BlockOp (Build parts),[]) ->
         (let (v,rs) = bvl_do_build_const parts (bvl_state_refs s) in
            Rval (v, bvl_state_refs_fupd (K rs) s))
     | (BlockOp (ConsExtend tag),
        CONS (bvl_Block _ xs') (CONS (bvl_Number lower) (CONS (bvl_Number len)
          (CONS (bvl_Number tot) xs)))) ->
         if lower < &0 \/ len < &0 \/ lower + len > &(LENGTH xs') \/
            tot = &0 \/ ~(tot = &(LENGTH xs) + len) then
           Rerr (Rabort Rtype_error)
         else
           Rval (bvl_Block tag (APPEND xs (TAKE (num_of_int len)
                                             (DROP (num_of_int lower) xs'))), s)
     | (BlockOp (ConsExtend tag),_) -> Rerr (Rabort Rtype_error)
     | (MemOp clos_El,[bvl_Block tag xs; bvl_Number i]) ->
         if &0 <= i /\ num_of_int i < LENGTH xs then Rval (EL (num_of_int i) xs, s)
         else Rerr (Rabort Rtype_error)
     | (MemOp clos_El,[bvl_RefPtr _ ptr; bvl_Number i]) ->
         (match FLOOKUP (bvl_state_refs s) ptr with
            SOME (bvl_ValueArray xs) ->
              (if &0 <= i /\ i < &(LENGTH xs)
               then Rval (EL (num_of_int i) xs, s)
               else Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp (ElemAt n),[bvl_Block tag xs]) ->
         if n < LENGTH xs then Rval (EL n xs, s) else Rerr (Rabort Rtype_error)
     | (BlockOp (ElemAt n),[bvl_RefPtr _ ptr]) ->
         (match FLOOKUP (bvl_state_refs s) ptr with
            SOME (bvl_ValueArray xs) ->
              (if n < LENGTH xs
               then Rval (EL n xs, s)
               else Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp clos_ListAppend,[x1; x2]) ->
         (match (bvl_v_to_list x1, bvl_v_to_list x2) with
            (SOME xs, SOME ys) -> Rval (bvl_list_to_v (APPEND xs ys),s)
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp LengthBlock,[bvl_Block tag xs]) ->
         Rval (bvl_Number (&(LENGTH xs)), s)
     | (MemOp Length,[bvl_RefPtr _ ptr]) ->
         (match FLOOKUP (bvl_state_refs s) ptr with
            SOME (bvl_ValueArray xs) -> Rval (bvl_Number (&(LENGTH xs)), s)
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp LengthByte,[bvl_RefPtr _ ptr]) ->
         (match FLOOKUP (bvl_state_refs s) ptr with
            SOME (bvl_ByteArray _ xs) -> Rval (bvl_Number (&(LENGTH xs)), s)
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp (RefByte F),[bvl_Number i; bvl_Number b]) ->
         if &0 <= i /\ (?w:byte. b = &(val w)) then
           let ptr = (minimal ptr. ~(ptr IN FDOM (bvl_state_refs s))) in
             Rval (bvl_RefPtr T ptr, bvl_state_refs_fupd (K (bvl_state_refs s |+
               (ptr,bvl_ByteArray F (REPLICATE (num_of_int i) (iword b))))) s)
         else Rerr (Rabort Rtype_error)
     | (MemOp RefArray,[bvl_Number i; v]) ->
         if &0 <= i then
           let ptr = (minimal ptr. ~(ptr IN FDOM (bvl_state_refs s))) in
             Rval (bvl_RefPtr T ptr, bvl_state_refs_fupd (K (bvl_state_refs s |+
               (ptr,bvl_ValueArray (REPLICATE (num_of_int i) v)))) s)
         else Rerr (Rabort Rtype_error)
     | (MemOp DerefByte,[bvl_RefPtr _ ptr; bvl_Number i]) ->
         (match FLOOKUP (bvl_state_refs s) ptr with
            SOME (bvl_ByteArray _ ws) ->
              (if &0 <= i /\ i < &(LENGTH ws)
               then Rval (bvl_Number (&(val (EL (num_of_int i) ws))),s)
               else Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp UpdateByte,[bvl_RefPtr _ ptr; bvl_Number i; bvl_Number b]) ->
         (match FLOOKUP (bvl_state_refs s) ptr with
            SOME (bvl_ByteArray f bs) ->
              (if &0 <= i /\ i < &(LENGTH bs) /\ (?w:byte. b = &(val w))
               then
                 Rval (bvl_Unit, bvl_state_refs_fupd (K (bvl_state_refs s |+
                   (ptr, bvl_ByteArray f (LUPDATE (iword b) (num_of_int i) bs)))) s)
               else Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp ConcatByteVec,[lv]) ->
         (match (some wss. ?ps.
                   bvl_v_to_list lv = SOME (MAP (bvl_RefPtr T) ps) /\
                   MAP (FLOOKUP (bvl_state_refs s)) ps =
                   MAP (SOME o bvl_ByteArray T) wss) with
            SOME wss ->
              let ptr = (minimal ptr. ~(ptr IN FDOM (bvl_state_refs s))) in
                Rval (bvl_RefPtr T ptr, bvl_state_refs_fupd (K (bvl_state_refs s |+
                        (ptr,bvl_ByteArray T (FLAT wss)))) s)
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp (FromList n),[lv]) ->
         (match bvl_v_to_list lv with
            SOME vs -> Rval (bvl_Block n vs, s)
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp FromListByte,[lv]) ->
         (match some ns. bvl_v_to_list lv = SOME (MAP (bvl_Number o int_of_num) ns) /\
                         ALL (\n. n < 256) ns with
            SOME ns ->
              let ptr = (minimal ptr. ~(ptr IN FDOM (bvl_state_refs s))) in
                Rval (bvl_RefPtr T ptr, bvl_state_refs_fupd (K (bvl_state_refs s |+
                        (ptr,bvl_ByteArray T (MAP word ns)))) s)
          | NONE -> Rerr (Rabort Rtype_error))
     | (MemOp ToListByte,[bvl_RefPtr _ ptr]) ->
         (match FLOOKUP (bvl_state_refs s) ptr with
            SOME (bvl_ByteArray f bs) ->
              (Rval (bvl_list_to_v (MAP (\b. bvl_Number (&(val b))) bs), s))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp (CopyByte F),[bvl_RefPtr _ src; bvl_Number srcoff; bvl_Number len;
                            bvl_RefPtr _ dst; bvl_Number dstoff]) ->
         (match (FLOOKUP (bvl_state_refs s) src, FLOOKUP (bvl_state_refs s) dst) with
            (SOME (bvl_ByteArray _ ws), SOME (bvl_ByteArray fl ds)) ->
              (match copy_array (ws,srcoff) len (SOME (ds,dstoff)) with
                 SOME ds -> Rval (bvl_Unit, bvl_state_refs_fupd
                              (K (bvl_state_refs s |+ (dst, bvl_ByteArray fl ds))) s)
               | NONE -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp (CopyByte T),[bvl_RefPtr _ src; bvl_Number srcoff; bvl_Number len]) ->
         (match FLOOKUP (bvl_state_refs s) src with
            SOME (bvl_ByteArray _ ws) ->
              (match copy_array (ws,srcoff) len NONE with
                 SOME ds ->
                   let ptr = (minimal ptr. ~(ptr IN FDOM (bvl_state_refs s))) in
                   Rval (bvl_RefPtr T ptr, bvl_state_refs_fupd
                           (K (bvl_state_refs s |+ (ptr, bvl_ByteArray T ds))) s)
               | _ -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp XorByte,[bvl_RefPtr _ dst; bvl_RefPtr _ src]) ->
         (match (FLOOKUP (bvl_state_refs s) src, FLOOKUP (bvl_state_refs s) dst) with
            (SOME (bvl_ByteArray _ ws), SOME (bvl_ByteArray fl ds)) ->
              (match xor_bytes ws ds with
                 SOME ds1 -> Rval (bvl_Unit, bvl_state_refs_fupd
                               (K (bvl_state_refs s |+ (dst, bvl_ByteArray fl ds1))) s)
               | NONE -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp (StringCmp b cmp),[bvl_RefPtr _ s1; bvl_RefPtr _ s2]) ->
         (match (FLOOKUP (bvl_state_refs s) s1, FLOOKUP (bvl_state_refs s) s2) with
            (SOME (bvl_ByteArray _ ws1), SOME (bvl_ByteArray _ ws2)) ->
              (let s1 = implode (MAP (CHR o val) ws1) in
               let s2 = implode (MAP (CHR o val) ws2) in
                 Rval (bvl_Boolv (str_cmp b cmp s1 s2), s))
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp (TagEq n),[bvl_Block tag xs]) ->
         Rval (bvl_Boolv (tag = n), s)
     | (BlockOp (clos_LenEq l),[bvl_Block tag xs]) ->
         Rval (bvl_Boolv (LENGTH xs = l),s)
     | (BlockOp (clos_TagLenEq n l),[bvl_Block tag xs]) ->
         Rval (bvl_Boolv (tag = n /\ LENGTH xs = l),s)
     | (BlockOp (EqualConst p),[x1]) ->
         (match p with
            clos_Int i ->
              (match x1 with
                 bvl_Number j -> Rval (bvl_Boolv (i = j), s)
               | _ -> Rerr (Rabort Rtype_error))
          | clos_W64 i ->
              (match x1 with
                 bvl_Word64 j -> Rval (bvl_Boolv (i = j), s)
               | _ -> Rerr (Rabort Rtype_error))
          | clos_Str i ->
              (match x1 with
                 bvl_RefPtr _ p ->
                   (match FLOOKUP (bvl_state_refs s) p with
                      SOME (bvl_ByteArray T j) ->
                        Rval (bvl_Boolv (j = MAP (word o ORD) (explode i)), s)
                    | _ -> Rerr (Rabort Rtype_error))
               | _ -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp clos_Equal,[x1; x2]) ->
         (match bvl_do_eq (bvl_state_refs s) x1 x2 with
            Eq_val b -> Rval (bvl_Boolv b, s)
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp clos_Ref,xs) ->
         let ptr = (minimal ptr. ~(ptr IN FDOM (bvl_state_refs s))) in
           Rval (bvl_RefPtr T ptr, bvl_state_refs_fupd
                   (K (bvl_state_refs s |+ (ptr,bvl_ValueArray xs))) s)
     | (MemOp Update,[bvl_RefPtr _ ptr; bvl_Number i; x]) ->
         (match FLOOKUP (bvl_state_refs s) ptr with
            SOME (bvl_ValueArray xs) ->
              (if &0 <= i /\ i < &(LENGTH xs)
               then Rval (bvl_Unit, bvl_state_refs_fupd (K (bvl_state_refs s |+
                           (ptr,bvl_ValueArray (LUPDATE x (num_of_int i) xs)))) s)
               else Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (clos_Label n,[]) ->
         if n IN domain (bvl_state_code s) then Rval (bvl_CodePtr n, s)
         else Rerr (Rabort Rtype_error)
     | (IntOp intop, vs) ->
         (match bvl_do_int_app intop vs with
            SOME res -> Rval (res,s)
          | _ -> Rerr (Rabort Rtype_error))
     | (WordOp wordop, vs) ->
         (match bvl_do_word_app wordop vs with
            SOME res -> Rval (res,s)
          | _ -> Rerr (Rabort Rtype_error))
     | (clos_FFI n, [bvl_RefPtr _ cptr; bvl_RefPtr _ ptr]) ->
         (match (FLOOKUP (bvl_state_refs s) cptr, FLOOKUP (bvl_state_refs s) ptr) with
            (SOME (bvl_ByteArray T cws), SOME (bvl_ByteArray F ws)) ->
              (match call_FFI (bvl_state_ffi s) (ExtCall n) cws ws with
                 FFI_return ffi' ws' ->
                   Rval (bvl_Unit,
                         bvl_state_refs_fupd (K (bvl_state_refs s |+ (ptr,bvl_ByteArray F ws')))
                           (bvl_state_ffi_fupd (K ffi') s))
               | FFI_final outcome ->
                   Rerr (Rabort (Rffi_error outcome)))
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp BoundsCheckBlock,xs) ->
         (match xs with
            [bvl_Block tag ys; bvl_Number i] ->
              Rval (bvl_Boolv (&0 <= i /\ i < &(LENGTH ys)),s)
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp (BoundsCheckByte loose),xs) ->
         (match xs with
            [bvl_RefPtr _ ptr; bvl_Number i] ->
              (match FLOOKUP (bvl_state_refs s) ptr with
                 SOME (bvl_ByteArray _ ws) ->
                   Rval (bvl_Boolv (&0 <= i /\
                                    (if loose then (<=) else (<)) i (&(LENGTH ws))),s)
               | _ -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp BoundsCheckArray,xs) ->
         (match xs with
            [bvl_RefPtr _ ptr; bvl_Number i] ->
              (match FLOOKUP (bvl_state_refs s) ptr with
                 SOME (bvl_ValueArray ws) ->
                   Rval (bvl_Boolv (&0 <= i /\ i < &(LENGTH ws)),s)
               | _ -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp clos_ConfigGC,[bvl_Number _; bvl_Number _]) -> (Rval (bvl_Unit, s))
     | (clos_ThunkOp th_op, vs) ->
         (match (th_op,vs) with
            (AllocThunk m, [v]) ->
              (if bvl_bad_thunk_update m v (bvl_state_refs s) then
                 Rerr (Rabort Rtype_error) else
               let ptr = (minimal ptr. ~(ptr IN FDOM (bvl_state_refs s))) in
                 Rval (bvl_RefPtr F ptr, bvl_state_refs_fupd
                         (K (bvl_state_refs s |+ (ptr,bvl_Thunk m v))) s))
          | (UpdateThunk m, [bvl_RefPtr F ptr; v]) ->
              (if bvl_bad_thunk_update m v (bvl_state_refs s) then
                 Rerr (Rabort Rtype_error) else
               match FLOOKUP (bvl_state_refs s) ptr with
                 SOME (bvl_Thunk NotEvaluated _) ->
                   Rval (bvl_Unit, bvl_state_refs_fupd
                           (K (bvl_state_refs s |+ (ptr,bvl_Thunk m v))) s)
               | _ -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | _ -> (Rerr (Rabort Rtype_error):(bvl_v # (C,FFI)bvl_state,bvl_v)result)`;;

let bvl_dec_clock_def = cake_def
  `bvl_dec_clock n (s:(C,FFI)bvl_state) =
     bvl_state_clock_fupd (K (bvl_state_clock s - n)) s`;;

(* Functions for looking up function definitions *)

let bvl_find_code_def = cake_def
  `(bvl_find_code (SOME p) (args:bvl_v list) (code:(num # A) spt) =
      match lookup p code with
        NONE -> NONE
      | SOME (arity,exp) -> if LENGTH args = arity then SOME (args,exp) else NONE) /\
   (bvl_find_code NONE args code =
      if args = [] then NONE else
        match LAST args with
          bvl_CodePtr loc ->
            (match lookup loc code with
               NONE -> NONE
             | SOME (arity,exp) -> if LENGTH args = arity + 1
                                   then SOME (BUTLAST args,exp)
                                   else NONE)
        | other -> NONE)`;;

(* The evaluation is defined as a clocked functional version of a          *)
(* conventional big-step operational semantics.                             *)

(* Proving termination of the evaluator directly is tricky. We make our     *)
(* life simpler by forcing the clock to stay good using fix_clock. At the   *)
(* bottom of this file, we remove all occurrences of fix_clock.             *)

(* HOL4 infers the most general type: s and s1 are states of independent   *)
(* types                                                                     *)
let bvl_fix_clock_def = cake_def
  `bvl_fix_clock (s:(A,B)bvl_state) ((res:R),(s1:(C,D)bvl_state)) =
     (res,bvl_state_clock_fupd (K (MIN (bvl_state_clock s) (bvl_state_clock s1))) s1)`;;

(* HOL4 [local] *)
let bvl_fix_clock_IMP = prove
 (`!(s:(A,B)bvl_state) (x:R#(C,D)bvl_state) res s1.
     bvl_fix_clock s x = (res,s1) ==> bvl_state_clock s1 <= bvl_state_clock s`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `x:R#(C,D)bvl_state` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:R` (X_CHOOSE_THEN `s':(C,D)bvl_state` SUBST1_TAC)) THEN
  REWRITE_TAC[bvl_fix_clock_def; PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; K_THM] THEN ARITH_TAC);;

(* The semantics of expression evaluation is defined next. For convenience *)
(* of subsequent proofs, the evaluation function is defined to evaluate a   *)
(* list of exp expressions.                                                  *)

let CLOSSEMAUX_bvl_evaluate_clauses =
  `(bvl_evaluate ([]:bvl_exp list,env:bvl_v list,s:(C,FFI)bvl_state) =
      (Rval [],s)) /\
   (bvl_evaluate (CONS x (CONS y xs),env,s) =
      match bvl_fix_clock s (bvl_evaluate ([x],env,s)) with
        (Rval v1,s1) ->
          (match bvl_evaluate (CONS y xs,env,s1) with
             (Rval vs,s2) -> (Rval (CONS (HD v1) vs),s2)
           | res -> res)
      | res -> res) /\
   (bvl_evaluate ([bvl_Var n],env,s) =
      if n < LENGTH env then (Rval [EL n env],s)
      else (Rerr (Rabort Rtype_error),s)) /\
   (bvl_evaluate ([bvl_If x1 x2 x3],env,s) =
      match bvl_fix_clock s (bvl_evaluate ([x1],env,s)) with
        (Rval vs,s1) ->
          if bvl_Boolv T = HD vs then bvl_evaluate ([x2],env,s1) else
          if bvl_Boolv F = HD vs then bvl_evaluate ([x3],env,s1) else
            (Rerr (Rabort Rtype_error),s1)
      | res -> res) /\
   (bvl_evaluate ([bvl_Let xs x2],env,s) =
      match bvl_fix_clock s (bvl_evaluate (xs,env,s)) with
        (Rval vs,s1) -> bvl_evaluate ([x2],APPEND vs env,s1)
      | res -> res) /\
   (bvl_evaluate ([bvl_Raise x1],env,s) =
      match bvl_evaluate ([x1],env,s) with
        (Rval vs,s) -> (Rerr (Rraise (HD vs)),s)
      | res -> res) /\
   (bvl_evaluate ([bvl_Handle x1 x2],env,s1) =
      match bvl_fix_clock s1 (bvl_evaluate ([x1],env,s1)) with
        (Rerr (Rraise v),s) -> bvl_evaluate ([x2],CONS v env,s)
      | res -> res) /\
   (bvl_evaluate ([bvl_Op op xs],env,s) =
      match bvl_fix_clock s (bvl_evaluate (xs,env,s)) with
        (Rval vs,s) ->
          (match bvl_do_app op (REVERSE vs) s with
             Rerr err -> (Rerr err,s)
           | Rval (v,s) -> (Rval [v],s))
      | res -> res) /\
   (bvl_evaluate ([bvl_Tick x],env,s) =
      if bvl_state_clock s = 0 then (Rerr (Rabort Rtimeout_error),s)
      else bvl_evaluate ([x],env,bvl_dec_clock 1 s)) /\
   (bvl_evaluate ([bvl_Force force_loc n],env,s) =
      if ~(n < LENGTH env) then (Rerr (Rabort Rtype_error),s) else
        let thunk_v = EL n env in
          (match bvl_dest_thunk thunk_v (bvl_state_refs s) with
             bvl_BadRef -> (Rerr (Rabort Rtype_error),s)
           | bvl_NotThunk -> (Rerr (Rabort Rtype_error),s)
           | bvl_IsThunk Evaluated v -> (Rval [v],s)
           | bvl_IsThunk NotEvaluated f ->
               (match bvl_find_code (SOME force_loc) [thunk_v; f] (bvl_state_code s) with
                  NONE -> (Rerr (Rabort Rtype_error),s)
                | SOME (args,exp) ->
                    if bvl_state_clock s = 0 then
                      (Rerr (Rabort Rtimeout_error),bvl_state_clock_fupd (K 0) s)
                    else
                      bvl_evaluate ([exp],args,bvl_dec_clock 1 s)))) /\
   (bvl_evaluate ([bvl_Call ticks dest xs],env,s1) =
      match bvl_fix_clock s1 (bvl_evaluate (xs,env,s1)) with
        (Rval vs,s) ->
          (match bvl_find_code dest vs (bvl_state_code s) with
             NONE -> (Rerr (Rabort Rtype_error),s)
           | SOME (args,exp) ->
               if bvl_state_clock s < ticks + 1 then
                 (Rerr (Rabort Rtimeout_error),bvl_state_clock_fupd (K 0) s)
               else
                 bvl_evaluate ([exp],args,bvl_dec_clock (ticks + 1) s))
      | res -> res)`;;

(* HOL4's termination relation:                                              *)
(*   inv_image (measure I LEX measure (list_size exp_size))                  *)
(*             (\(xs,env,s). (s.clock,xs))                                   *)

let CLOSSEMAUX_bvl_evaluate_rel =
  `inv_image (MEASURE (I:num->num) LEX MEASURE (list_size bvl_exp_size))
     (\x:bvl_exp list # bvl_v list # (C,FFI)bvl_state.
        bvl_state_clock (SND (SND x)),FST x)`;;

(* HOL4: rpt strip_tac \\ simp[dec_clock_def] \\ imp_res_tac fix_clock_IMP  *)
(* \\ FULL_SIMP_TAC (srw_ss()) [] \\ decide_tac                              *)

let CLOSSEMAUX_bvl_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP bvl_fix_clock_IMP)) THEN
  REPEAT GEN_TAC THEN
  (fun g -> let ths = [inv_image_THM; LEX_DEF; FST; SND; I_THM; measure_THM;
                       bvl_dec_clock_def; bvl_state_INFO.ri_accfupds; K_THM;
                       list_size; LENGTH] @
                      !the_size_defs @ flat (map snd (!the_size_aux_eqs)) in
            (RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths) g) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSSEMAUX_is_num_fact o concl))) THEN
  ARITH_TAC;;

(* HOL4 evaluate_def (the first one, with fix_clock) *)
let CLOSSEMAUX_bvl_evaluate_fix_def =
  sem1aux_def_wf CLOSSEMAUX_bvl_evaluate_rel CLOSSEMAUX_bvl_TC_TAC
    CLOSSEMAUX_bvl_evaluate_clauses;;

(* HOL4's first evaluate_ind *)
let CLOSSEMAUX_bvl_evaluate_fix_ind = cake_ind "bvl_evaluate";;

(* We prove that the clock never increases. *)

(* HOL4: pair_case_eq, bool_case_eq and the case_eq theorems of list,       *)
(* option, op, v, ref, word_op, block_op, glob_op, mem_op, word_size,       *)
(* eq_result and ffi_result                                                  *)
let bvl_case_eq_thms = end_itlist CONJ
  ([pair_case_eq; COND_CASE_EQ; list_case_eq; option_case_eq] @
   map case_eq ["clos_op"; "bvl_v"; "bvl_ref"; "word_op"; "block_op"; "glob_op";
                "mem_op"; "word_size"; "eq_result"; "ffi_result"]);;

let bvl_do_app_const = prove
 (`!op args (s1:(C,FFI)bvl_state) res s2.
     bvl_do_app op args s1 = Rval (res,s2) ==>
     bvl_state_clock s2 = bvl_state_clock s1 /\
     (~(op = clos_Install) ==>
      bvl_state_code s2 = bvl_state_code s1 /\
      bvl_state_compile s2 = bvl_state_compile s1 /\
      bvl_state_compile_oracle s2 = bvl_state_compile_oracle s1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_app_def; bvl_do_install_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ;
              distinctness "clos_op"] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; K_THM]);;

let bvl_do_app_Ref = prove
 (`!vs (s:(C,FFI)bvl_state).
     bvl_do_app (MemOp clos_Ref) vs s =
     Rval (bvl_RefPtr T (minimal ptr. ~(ptr IN FDOM (bvl_state_refs s))),
           bvl_state_refs_fupd
             (K (bvl_state_refs s |+
                 ((minimal ptr. ~(ptr IN FDOM (bvl_state_refs s))),bvl_ValueArray vs)))
             s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_app_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CASE_REWRITE_TAC[]);;
let _ = cake_add_simps [bvl_do_app_Ref];;

let bvl_do_app_Cons = prove
 (`!tag vs (s:(C,FFI)bvl_state).
     bvl_do_app (BlockOp (clos_Cons tag)) vs s = Rval (bvl_Block tag vs,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_app_def] THEN CASE_REWRITE_TAC[]);;
let _ = cake_add_simps [bvl_do_app_Cons];;

(* HOL4: recInduct evaluate_ind >> rw[evaluate_def] >> every_case_tac >>    *)
(* full_simp_tac(srw_ss())[dec_clock_def] >> rw[] >> rfs[] >>               *)
(* imp_res_tac fix_clock_IMP >> fs[] >> imp_res_tac do_app_const >> fs[]    *)

let CLOSSEMAUX_BVL_CLOCK_TAC : tactic =
  REWRITE_TAC[SND] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[CLOSSEMAUX_bvl_evaluate_fix_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  FS[PAIR_EQ] THEN
  RES_TAC THEN RES_TAC THEN
  IMP_RES_TAC bvl_fix_clock_IMP THEN
  IMP_RES_TAC bvl_do_app_const THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvl_dec_clock_def; bvl_state_INFO.ri_accfupds; K_THM]) THEN
  REWRITE_TAC[bvl_dec_clock_def; bvl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSSEMAUX_is_num_fact o concl))) THEN
  ARITH_TAC;;

let bvl_evaluate_clock = prove
 (`!xs env (s1:(C,FFI)bvl_state) vs s2.
     bvl_evaluate (xs,env,s1) = (vs,s2) ==> bvl_state_clock s2 <= bvl_state_clock s1`,
  SUBGOAL_THEN
   `!tup vs (s2:(C,FFI)bvl_state).
      bvl_evaluate tup = (vs,s2) ==>
      bvl_state_clock s2 <= bvl_state_clock (SND (SND tup))`
   (fun th -> MESON_TAC[th; SND]) THEN
  MATCH_MP_TAC CLOSSEMAUX_bvl_evaluate_fix_ind THEN REPEAT CONJ_TAC THEN
  CLOSSEMAUX_BVL_CLOCK_TAC);;

let bvl_fix_clock_evaluate = prove
 (`!(s:(C,FFI)bvl_state) xs env.
     bvl_fix_clock s (bvl_evaluate (xs,env,s)) = bvl_evaluate (xs,env,s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `bvl_evaluate (xs,env,s:(C,FFI)bvl_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `s1:(C,FFI)bvl_state` (fun th -> ASSUME_TAC th THEN
                                                  REWRITE_TAC[th]))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvl_evaluate_clock) THEN
  REWRITE_TAC[bvl_fix_clock_def; PAIR_EQ; bvl_state_component_equality;
              bvl_state_INFO.ri_accfupds; K_THM] THEN
  ASM_ARITH_TAC);;

(* Finally, we remove fix_clock from the induction and definition theorems. *)

let bvl_evaluate_def =
  REWRITE_RULE[bvl_fix_clock_evaluate] CLOSSEMAUX_bvl_evaluate_fix_def;;

let bvl_evaluate_ind =
  REWRITE_RULE[bvl_fix_clock_evaluate] CLOSSEMAUX_bvl_evaluate_fix_ind;;

(* cake_ind returns HOL4's final induction theorem *)
let () = cake_ind_store := ("bvl_evaluate",bvl_evaluate_ind) :: !cake_ind_store;;

(* observational semantics *)

let bvl_initial_state_def = cake_def
  `bvl_initial_state (ffi:(FFI)ffi_state) code (co:num -> C # (num # num # bvl_exp) list)
                     cc k =
     bvl_state_REC [] FEMPTY k cc co code ffi`;;

let bvl_semantics_def = cake_def
  `bvl_semantics (init_ffi:(FFI)ffi_state) code
                 (co:num -> C # (num # num # bvl_exp) list) cc start =
     let es = [bvl_Call 0 (SOME start) []] in
     let init = bvl_initial_state init_ffi code co cc in
       if ?k. FST (bvl_evaluate (es,[],init k)) = Rerr (Rabort Rtype_error)
       then Fail
       else
       (match some res.
          ?k s r outcome.
            bvl_evaluate (es,[],init k) = (r,s) /\
            (match r with
               Rerr (Rabort Rtimeout_error) -> F
             | Rerr (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
             | _ -> outcome = Success) /\
            res = Terminate outcome (ffi_state_io_events (bvl_state_ffi s))
        with
          SOME res -> res
        | NONE ->
            Diverge
              (build_lprefix_lub
                (IMAGE (\k. llist_fromList
                          (ffi_state_io_events
                             (bvl_state_ffi (SND (bvl_evaluate (es,[],init k))))))
                       UNIV)))`;;
