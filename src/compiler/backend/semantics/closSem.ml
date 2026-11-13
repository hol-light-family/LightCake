(* ========================================================================= *)
(* closSem: port of HOL4 compiler/backend/semantics/closSemScript.sml        *)
(* (CakeML v3479).  The formal semantics of closLang.                        *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/lprefix_lub.ml";;
needs "semantics/ffi/ffi.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/flatLang.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* differs from store_v by removing the single value Refv, also, adds flag *)
(* to ByteArray for equality semantics                                     *)

let clos_ref_INDUCT,clos_ref_RECURSION = cake_type
  "clos_ref = clos_ValueArray (A list)
            | clos_ByteArray (byte list)
            | clos_Thunk thunk_mode A";;

(* --- Semantics of ClosLang --- *)

let clos_v_INDUCT,clos_v_RECURSION = cake_type
  "clos_v = clos_Number int
          | clos_Word64 int64
          | clos_Block num (clos_v list)
          | ByteVector (byte list)
          | clos_RefPtr bool num
          | clos_Closure (num option) (clos_v list) (clos_v list) num clos_exp
          | clos_Recclosure (num option) (clos_v list) (clos_v list)
                            ((num # clos_exp) list) num";;

(* HOL4: Type clos_co = ``:num -> 'c # clos_prog`` (written out where used, *)
(* as num -> C # clos_prog; clos_cc of closLang is                          *)
(* C -> clos_prog -> (byte list # int64 list # C) option)                   *)

let clos_state_INFO = cake_record "clos_state"
  ["globals","(clos_v option) list";
   "refs","(num,(clos_v)clos_ref)fmap";
   "ffi","(FFI)ffi_state";
   "clock","num";
   "compile","C -> clos_prog -> (byte list # int64 list # C) option";
   "compile_oracle","num -> C # clos_prog";
   "code","(num,num # clos_exp)fmap";
   "max_app","num"];;

let clos_state_component_equality = clos_state_INFO.ri_component_equality;;

(* helper functions *)

let get_global_def = cake_def
  `get_global n (globals:A list) =
     if n < LENGTH globals then SOME (EL n globals) else NONE`;;

let clos_Boolv_def = cake_def
  `clos_Boolv b = clos_Block (if b then true_tag else false_tag) []`;;

let clos_do_eq_def = sem1aux_def_wf
  `inv_image (<)
     (\x:(clos_v # clos_v) + (clos_v list # clos_v list).
        sum_CASE x (\t. clos_v_size (FST t)) (\t. list_size clos_v_size (FST t)))`
  SEM1AUX_TC_TAC
  `(clos_do_eq x y =
      match x with
        clos_Number i ->
          (match y with
             clos_Number j -> Eq_val (i = j)
           | _ -> Eq_type_error)
      | clos_Word64 v ->
          (match y with
             clos_Word64 w -> Eq_val (v = w)
           | _ -> Eq_type_error)
      | clos_Block t1 xs ->
          (match y with
             clos_Block t2 ys -> if t1 = t2 /\ LENGTH xs = LENGTH ys then
                                   clos_do_eq_list xs ys
                                 else Eq_val F
           | _ -> Eq_type_error)
      | ByteVector cs ->
          (match y with
             ByteVector ds -> Eq_val (cs = ds)
           | _ -> Eq_type_error)
      | clos_RefPtr bi i ->
          (match y with
             clos_RefPtr bj j -> (if bi /\ bj then Eq_val (i = j) else Eq_type_error)
           | _ -> Eq_type_error)
      | _ ->
          (match y with
             clos_Number _ -> Eq_type_error
           | clos_Word64 _ -> Eq_type_error
           | clos_Block _ _ -> Eq_type_error
           | ByteVector _ -> Eq_type_error
           | clos_RefPtr _ _ -> Eq_type_error
           | _ -> Eq_val T)) /\
   (clos_do_eq_list [] [] = Eq_val T) /\
   (clos_do_eq_list (CONS x xs) (CONS y ys) =
      match clos_do_eq x y with
        Eq_val T -> clos_do_eq_list xs ys
      | res -> res) /\
   (clos_do_eq_list _ _ = Eq_val F)`;;

let clos_do_eq_ind = cake_ind "clos_do_eq";;

let clos_v_to_list_def = sem1aux_def_wf
  `measure clos_v_size`
  SEM1AUX_TC_TAC
  `(clos_v_to_list (clos_Block tag []) =
      if tag = nil_tag then SOME [] else NONE) /\
   (clos_v_to_list (clos_Block tag [h; bt]) =
      if tag = cons_tag then
        (match clos_v_to_list bt with
           SOME t -> SOME (CONS h t)
         | _ -> NONE)
      else NONE) /\
   (clos_v_to_list _ = NONE)`;;

let clos_v_to_list_ind = cake_ind "clos_v_to_list";;

let clos_list_to_v_def = cake_def
  `(clos_list_to_v [] = clos_Block nil_tag []) /\
   (clos_list_to_v (CONS x xs) = clos_Block cons_tag [x; clos_list_to_v xs])`;;

let clos_Unit_def = cake_def
  `clos_Unit = clos_Block tuple_tag []`;;

(* HOL4: Overload Error[local] = Rerr (Rabort Rtype_error) (written out) *)

let clos_v_to_bytes_def = cake_def
  `clos_v_to_bytes lv = some ns:byte list.
     clos_v_to_list lv = SOME (MAP (clos_Number o int_of_num o val) ns)`;;

let clos_v_to_words_def = cake_def
  `clos_v_to_words lv = some ns:int64 list.
     clos_v_to_list lv = SOME (MAP clos_Word64 ns)`;;

(* HOL4 r with <| f1 := x; f2 := y |> is f1_fupd (K x) (f2_fupd (K y) r) *)

let clos_do_install_def = cake_def
  `clos_do_install vs (s:(C,FFI)clos_state) =
     match vs with
       [v1; v2] ->
         (match (clos_v_to_bytes v1, clos_v_to_words v2) with
            (SOME bytes, SOME data) ->
              let (cfg,progs) = clos_state_compile_oracle s 0 in
              let new_oracle = shift_seq 1 (clos_state_compile_oracle s) in
              (if DISJOINT (FDOM (clos_state_code s))
                           (set_of_list (MAP FST (SND progs))) /\
                  ALL_DISTINCT (MAP FST (SND progs)) then
               (match (clos_state_compile s cfg progs, progs) with
                  (SOME (bytes',data',cfg'), (exps,aux)) ->
                    if bytes = bytes' /\ data = data' /\
                       FST (new_oracle 0) = cfg' /\ ~(exps = []) then
                     (let s' =
                        clos_state_code_fupd (K (clos_state_code s |++ aux))
                          (clos_state_compile_oracle_fupd (K new_oracle)
                            (clos_state_clock_fupd (K (clos_state_clock s - 1)) s))
                      in
                        if clos_state_clock s = 0
                        then (Rerr (Rabort Rtimeout_error),s')
                        else (Rval exps, s'))
                    else ((Rerr (Rabort Rtype_error):(clos_exp list,clos_v)result),s)
                | _ -> (Rerr (Rabort Rtype_error),s))
               else (Rerr (Rabort Rtype_error),s))
          | _ -> (Rerr (Rabort Rtype_error),s))
     | _ -> (Rerr (Rabort Rtype_error),s)`;;

let make_const_def = cake_def_wf
  `measure const_size`
  TERM_TAC
  `(make_const (ConstInt i) = clos_Number i) /\
   (make_const (ConstStr s) = ByteVector (MAP (word o ORD) (explode s))) /\
   (make_const (ConstWord64 w) = clos_Word64 w) /\
   (make_const (ConstCons t cs) = clos_Block t (MAP make_const cs))`;;

let make_const_ind = cake_ind "make_const";;

let clos_do_int_app_def = sem1aux_def (list_mk_conj
  [`clos_do_int_app (clos_Const n) ([]:clos_v list) = SOME (clos_Number n)`;
   `clos_do_int_app clos_Add [clos_Number n1; clos_Number n2] =
      SOME (clos_Number (n1 + n2))`;
   `clos_do_int_app clos_Sub [clos_Number n1; clos_Number n2] =
      SOME (clos_Number (n1 - n2))`;
   `clos_do_int_app Mult [clos_Number n1; clos_Number n2] =
      SOME (clos_Number (n1 * n2))`;
   `clos_do_int_app clos_Div [clos_Number n1; clos_Number n2] =
      (if n2 = &0 then NONE else SOME (clos_Number (int_div n1 n2)))`;
   `clos_do_int_app clos_Mod [clos_Number n1; clos_Number n2] =
      (if n2 = &0 then NONE else SOME (clos_Number (integer_int_mod n1 n2)))`;
   `clos_do_int_app clos_Less [clos_Number n1; clos_Number n2] =
      SOME (clos_Boolv (n1 < n2))`;
   `clos_do_int_app LessEq [clos_Number n1; clos_Number n2] =
      SOME (clos_Boolv (n1 <= n2))`;
   `clos_do_int_app Greater [clos_Number n1; clos_Number n2] =
      SOME (clos_Boolv (n1 > n2))`;
   `clos_do_int_app GreaterEq [clos_Number n1; clos_Number n2] =
      SOME (clos_Boolv (n1 >= n2))`;
   `clos_do_int_app (LessConstSmall n) [clos_Number i] =
      (if &0 <= i /\ i <= &1000000 /\ n < 1000000 then
         SOME (clos_Boolv (i < &n)) else NONE)`;
   `clos_do_int_app (op:int_op) (vs:clos_v list) = (NONE:clos_v option)`])
;;

let opw_lookup_def = cake_def
  `(opw_lookup Andw = (word_and:N word->N word->N word)) /\
   (opw_lookup Orw = (word_or:N word->N word->N word)) /\
   (opw_lookup backend_common_Xor = (word_xor:N word->N word->N word)) /\
   (opw_lookup backend_common_Add = (word_add:N word->N word->N word)) /\
   (opw_lookup backend_common_Sub = (word_sub:N word->N word->N word))`;;
let _ = cake_add_simps [opw_lookup_def];;

(* HOL4's clauses for WordFromWord T and WordFromWord F (literal patterns)  *)
(* are written with WordFromWord b and a condition (the kit does not        *)
(* complete clauses with literal patterns)                                  *)

let clos_do_word_app_def = sem1aux_def (list_mk_conj
  [`clos_do_word_app (WordOpw W8 opw) [clos_Number n1; clos_Number n2] =
      (match some (w1:byte,w2:byte). n1 = &(val w1) /\ n2 = &(val w2) with
         NONE -> NONE
       | SOME (w1,w2) -> SOME (clos_Number (&(val (opw_lookup opw w1 w2)))))`;
   `clos_do_word_app (WordOpw W64 opw) [clos_Word64 w1; clos_Word64 w2] =
      SOME (clos_Word64 (opw_lookup opw w1 w2))`;
   `clos_do_word_app (WordTest W8 test) [clos_Number n1; clos_Number n2] =
      (if &0 <= n1 /\ n1 < &256 /\ &0 <= n2 /\ n2 < &256 then
         (match test with
            Equal -> SOME (clos_Boolv (n1 = n2))
          | Compare cmp -> SOME (clos_Boolv (int_cmp cmp n1 n2))
          | _ -> NONE)
       else NONE)`;
   `clos_do_word_app (WordShift W8 sh n) [clos_Number i] =
      (match some (w:byte). i = &(val w) with
         NONE -> NONE
       | SOME w -> SOME (clos_Number (&(val (shift_lookup sh w n)))))`;
   `clos_do_word_app (WordShift W64 sh n) [clos_Word64 w] =
      SOME (clos_Word64 (shift_lookup sh w n))`;
   `clos_do_word_app WordFromInt [clos_Number i] =
      SOME (clos_Word64 (iword i))`;
   `clos_do_word_app WordToInt [clos_Word64 w] =
      SOME (clos_Number (&(val w)))`;
   `clos_do_word_app (WordFromWord b) [clos_Word64 w] =
      if b then SOME (clos_Number (&(val ((word_zx:int64->byte) w))))
      else NONE`;
   `clos_do_word_app (WordFromWord b) [clos_Number n] =
      if b then NONE else
      (match some (w:byte). n = &(val w) with
         NONE -> NONE
       | SOME w -> SOME (clos_Word64 (word_zx w)))`;
   `clos_do_word_app (FP_top t_op) ws =
      (match ws with
         [clos_Word64 w1; clos_Word64 w2; clos_Word64 w3] ->
           SOME (clos_Word64 (fp_top_comp t_op w1 w2 w3))
       | _ -> NONE)`;
   `clos_do_word_app (FP_bop bop) ws =
      (match ws with
         [clos_Word64 w1; clos_Word64 w2] ->
           SOME (clos_Word64 (fp_bop_comp bop w1 w2))
       | _ -> NONE)`;
   `clos_do_word_app (FP_uop uop) ws =
      (match ws with
         [clos_Word64 w] -> SOME (clos_Word64 (fp_uop_comp uop w))
       | _ -> NONE)`;
   `clos_do_word_app (FP_cmp cmp) ws =
      (match ws with
         [clos_Word64 w1; clos_Word64 w2] ->
           SOME (clos_Boolv (fp_cmp_comp cmp w1 w2))
       | _ -> NONE)`;
   `clos_do_word_app (op:word_op) (vs:clos_v list) = (NONE:clos_v option)`])
;;

let clos_dest_thunk_ret_INDUCT,clos_dest_thunk_ret_RECURSION = cake_type
  "clos_dest_thunk_ret = clos_BadRef
                       | clos_NotThunk
                       | clos_IsThunk thunk_mode clos_v";;

let clos_dest_thunk_def = sem1aux_def
  `(clos_dest_thunk [clos_RefPtr b ptr] (refs:(num,(clos_v)clos_ref)fmap) =
      match FLOOKUP refs ptr with
        NONE -> clos_BadRef
      | SOME (clos_Thunk Evaluated v) ->
          if b then clos_BadRef else clos_IsThunk Evaluated v
      | SOME (clos_Thunk NotEvaluated v) ->
          if b then clos_BadRef else clos_IsThunk NotEvaluated v
      | SOME _ -> clos_NotThunk) /\
   (clos_dest_thunk vs refs = clos_NotThunk)`;;

let store_thunk_def = cake_def
  `store_thunk (ptr:B) (v:(A)clos_ref) (refs:(B,(A)clos_ref)fmap) =
     match FLOOKUP refs ptr with
       SOME (clos_Thunk NotEvaluated _) -> SOME (refs |+ (ptr,v))
     | _ -> NONE`;;

(* HOL4's first clause has the pattern RefPtr F ptr (so that its completion *)
(* has a clause for RefPtr T ptr); here RefPtr b ptr with if b then NONE    *)
(* (the kit does not complete clauses with literal patterns)               *)

let clos_update_thunk_def = sem1aux_def
  `(clos_update_thunk [clos_RefPtr b ptr] (refs:(num,(clos_v)clos_ref)fmap) [v] =
      if b then NONE else
      match clos_dest_thunk [v] refs with
        clos_NotThunk -> store_thunk ptr (clos_Thunk Evaluated v) refs
      | _ -> NONE) /\
   (clos_update_thunk _ _ _ = NONE)`;;

let clos_bad_thunk_update_def = cake_def
  `clos_bad_thunk_update m v (refs:(num,(clos_v)clos_ref)fmap) <=>
     m = Evaluated /\ ~(clos_dest_thunk [v] refs = clos_NotThunk)`;;

(* HOL4: Error is Rerr (Rabort Rtype_error); r with refs := x is            *)
(* clos_state_refs_fupd (K x) r; HOL4's variable word_op is wordop here      *)
(* (word_op is a constant of wordLang)                                       *)

let clos_do_app_def = cake_def
  `clos_do_app (op:clos_op) (vs:clos_v list) (s:(C,FFI)clos_state) =
     match (op,vs) with
       (GlobOp (clos_Global n),[]) ->
         (match get_global n (clos_state_globals s) with
            SOME (SOME v) -> Rval (v,s)
          | _ -> Rerr (Rabort Rtype_error))
     | (GlobOp (clos_Global _),[clos_Number i]) ->
         (if i < &0 then Rerr (Rabort Rtype_error) else
          match get_global (num_of_int i) (clos_state_globals s) with
            SOME (SOME v) -> Rval (v,s)
          | _ -> Rerr (Rabort Rtype_error))
     | (GlobOp (SetGlobal n),[v]) ->
         (match get_global n (clos_state_globals s) with
            SOME NONE -> Rval (clos_Unit,
              clos_state_globals_fupd (K (LUPDATE (SOME v) n (clos_state_globals s))) s)
          | _ -> Rerr (Rabort Rtype_error))
     | (GlobOp AllocGlobal,[clos_Number i]) ->
         (if i < &0 then Rerr (Rabort Rtype_error)
          else Rval (clos_Unit, clos_state_globals_fupd
                 (K (APPEND (clos_state_globals s) (REPLICATE (num_of_int i) NONE))) s))
     | (BlockOp (Constant c),[]) -> Rval (make_const c, s)
     | (BlockOp (clos_Cons tag),xs) -> Rval (clos_Block tag xs, s)
     | (BlockOp (ConsExtend tag),
        CONS (clos_Block _ xs') (CONS (clos_Number lower) (CONS (clos_Number len)
          (CONS (clos_Number tot) xs)))) ->
         if lower < &0 \/ len < &0 \/ &(LENGTH xs') < lower + len \/
            tot = &0 \/ ~(tot = &(LENGTH xs) + len) then
           Rerr (Rabort Rtype_error)
         else
           Rval (clos_Block tag (APPEND xs (TAKE (num_of_int len)
                                              (DROP (num_of_int lower) xs'))), s)
     | (BlockOp (ConsExtend tag),_) -> Rerr (Rabort Rtype_error)
     | (MemOp clos_El,[clos_Block tag xs; clos_Number i]) ->
         if &0 <= i /\ num_of_int i < LENGTH xs then Rval (EL (num_of_int i) xs, s)
         else Rerr (Rabort Rtype_error)
     | (MemOp clos_El,[clos_RefPtr _ ptr; clos_Number i]) ->
         (match FLOOKUP (clos_state_refs s) ptr with
            SOME (clos_ValueArray xs) ->
              (if &0 <= i /\ i < &(LENGTH xs)
               then Rval (EL (num_of_int i) xs, s)
               else Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp (BoolTest test),[v1; v2]) ->
         (if ~(v1 = clos_Boolv T) /\ ~(v1 = clos_Boolv F) then Rerr (Rabort Rtype_error)
          else if ~(v2 = clos_Boolv T) /\ ~(v2 = clos_Boolv F) then
            Rerr (Rabort Rtype_error)
          else Rval (clos_Boolv (v1 = v2), s))
     | (BlockOp BoolNot,[v1]) ->
         (if v1 = clos_Boolv T then Rval (clos_Boolv F, s) else
          if v1 = clos_Boolv F then Rval (clos_Boolv T, s) else Rerr (Rabort Rtype_error))
     | (BlockOp (ElemAt n),[clos_Block tag xs]) ->
         if n < LENGTH xs then Rval (EL n xs, s) else Rerr (Rabort Rtype_error)
     | (BlockOp clos_ListAppend,[x1; x2]) ->
         (match (clos_v_to_list x1, clos_v_to_list x2) with
            (SOME xs, SOME ys) -> Rval (clos_list_to_v (APPEND xs ys), s)
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp LengthBlock,[clos_Block tag xs]) ->
         Rval (clos_Number (&(LENGTH xs)), s)
     | (MemOp Length,[clos_RefPtr _ ptr]) ->
         (match FLOOKUP (clos_state_refs s) ptr with
            SOME (clos_ValueArray xs) -> Rval (clos_Number (&(LENGTH xs)), s)
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp LengthByte,[clos_RefPtr _ ptr]) ->
         (match FLOOKUP (clos_state_refs s) ptr with
            SOME (clos_ByteArray xs) -> Rval (clos_Number (&(LENGTH xs)), s)
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp (RefByte F),[clos_Number i; clos_Number b]) ->
         if &0 <= i /\ (?w:byte. b = &(val w)) then
           let ptr = (minimal ptr. ~(ptr IN FDOM (clos_state_refs s))) in
             Rval (clos_RefPtr T ptr, clos_state_refs_fupd (K (clos_state_refs s |+
               (ptr,clos_ByteArray (REPLICATE (num_of_int i) (iword b))))) s)
         else Rerr (Rabort Rtype_error)
     | (MemOp RefArray,[clos_Number i; v]) ->
         if &0 <= i then
           let ptr = (minimal ptr. ~(ptr IN FDOM (clos_state_refs s))) in
             Rval (clos_RefPtr T ptr, clos_state_refs_fupd (K (clos_state_refs s |+
               (ptr,clos_ValueArray (REPLICATE (num_of_int i) v)))) s)
         else Rerr (Rabort Rtype_error)
     | (MemOp DerefByte,[clos_RefPtr _ ptr; clos_Number i]) ->
         (match FLOOKUP (clos_state_refs s) ptr with
            SOME (clos_ByteArray ws) ->
              (if &0 <= i /\ i < &(LENGTH ws)
               then Rval (clos_Number (&(val (EL (num_of_int i) ws))),s)
               else Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp UpdateByte,[clos_RefPtr _ ptr; clos_Number i; clos_Number b]) ->
         (match FLOOKUP (clos_state_refs s) ptr with
            SOME (clos_ByteArray bs) ->
              (if &0 <= i /\ i < &(LENGTH bs) /\ (?w:byte. b = &(val w))
               then
                 Rval (clos_Unit, clos_state_refs_fupd (K (clos_state_refs s |+
                   (ptr, clos_ByteArray (LUPDATE (iword b) (num_of_int i) bs)))) s)
               else Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp ConcatByteVec,[lv]) ->
         (match (some wss. clos_v_to_list lv = SOME (MAP ByteVector wss)) with
            SOME wss -> Rval (ByteVector (FLAT wss), s)
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp (FromList n),[lv]) ->
         (match clos_v_to_list lv with
            SOME vs -> Rval (clos_Block n vs, s)
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp FromListByte,[lv]) ->
         (match some ns. clos_v_to_list lv = SOME (MAP (clos_Number o int_of_num) ns) /\
                         ALL (\n. n < 256) ns with
            SOME ns -> Rval (ByteVector (MAP word ns), s)
          | NONE -> Rerr (Rabort Rtype_error))
     | (MemOp ToListByte,[ByteVector bs]) ->
         (Rval (clos_list_to_v (MAP (\b. clos_Number (&(val b))) bs), s))
     | (MemOp LengthByteVec,[ByteVector bs]) ->
         (Rval (clos_Number (&(LENGTH bs)), s))
     | (MemOp DerefByteVec,[ByteVector bs; clos_Number i]) ->
         (if &0 <= i /\ i < &(LENGTH bs) then
            Rval (clos_Number (&(val (EL (num_of_int i) bs))), s)
          else Rerr (Rabort Rtype_error))
     | (MemOp (CopyByte F),[ByteVector ws; clos_Number srcoff; clos_Number len;
                            clos_RefPtr _ dst; clos_Number dstoff]) ->
         (match FLOOKUP (clos_state_refs s) dst with
            SOME (clos_ByteArray ds) ->
              (match copy_array (ws,srcoff) len (SOME (ds,dstoff)) with
                 SOME ds -> Rval (clos_Unit, clos_state_refs_fupd
                              (K (clos_state_refs s |+ (dst, clos_ByteArray ds))) s)
               | NONE -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp (CopyByte F),[clos_RefPtr _ src; clos_Number srcoff; clos_Number len;
                            clos_RefPtr _ dst; clos_Number dstoff]) ->
         (match (FLOOKUP (clos_state_refs s) src, FLOOKUP (clos_state_refs s) dst) with
            (SOME (clos_ByteArray ws), SOME (clos_ByteArray ds)) ->
              (match copy_array (ws,srcoff) len (SOME (ds,dstoff)) with
                 SOME ds -> Rval (clos_Unit, clos_state_refs_fupd
                              (K (clos_state_refs s |+ (dst, clos_ByteArray ds))) s)
               | NONE -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp (CopyByte T),[ByteVector ws; clos_Number srcoff; clos_Number len]) ->
         (match copy_array (ws,srcoff) len NONE with
            SOME ds -> Rval (ByteVector ds, s)
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp (CopyByte T),[clos_RefPtr _ src; clos_Number srcoff; clos_Number len]) ->
         (match FLOOKUP (clos_state_refs s) src with
            SOME (clos_ByteArray ws) ->
              (match copy_array (ws,srcoff) len NONE with
                 SOME ds -> Rval (ByteVector ds, s)
               | _ -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp XorByte,[clos_RefPtr _ dst; ByteVector ws]) ->
         (match FLOOKUP (clos_state_refs s) dst with
            SOME (clos_ByteArray ds) ->
              (match xor_bytes ws ds with
                 SOME ds1 -> Rval (clos_Unit, clos_state_refs_fupd
                               (K (clos_state_refs s |+ (dst, clos_ByteArray ds1))) s)
               | _ -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp (StringCmp b cmp),[ByteVector b1; ByteVector b2]) ->
         (let s1 = implode (MAP (CHR o val) b1) in
          let s2 = implode (MAP (CHR o val) b2) in
            Rval (clos_Boolv (str_cmp b cmp s1 s2), s))
     | (BlockOp (TagEq n),[clos_Block tag xs]) ->
         Rval (clos_Boolv (tag = n), s)
     | (BlockOp (clos_LenEq l),[clos_Block tag xs]) ->
         Rval (clos_Boolv (LENGTH xs = l),s)
     | (BlockOp (clos_TagLenEq n l),[clos_Block tag xs]) ->
         Rval (clos_Boolv (tag = n /\ LENGTH xs = l),s)
     | (BlockOp (EqualConst p),[x1]) ->
         (match p with
            clos_Int i ->
              (match x1 with
                 clos_Number j -> Rval (clos_Boolv (i = j), s)
               | _ -> Rerr (Rabort Rtype_error))
          | clos_W64 i ->
              (match x1 with
                 clos_Word64 j -> Rval (clos_Boolv (i = j), s)
               | _ -> Rerr (Rabort Rtype_error))
          | clos_Str i ->
              (match x1 with
                 ByteVector j -> Rval (clos_Boolv (j = MAP (word o ORD) (explode i)), s)
               | _ -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp clos_Equal,[x1; x2]) ->
         (match clos_do_eq x1 x2 with
            Eq_val b -> Rval (clos_Boolv b, s)
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp clos_Ref,xs) ->
         let ptr = (minimal ptr. ~(ptr IN FDOM (clos_state_refs s))) in
           Rval (clos_RefPtr T ptr, clos_state_refs_fupd
                   (K (clos_state_refs s |+ (ptr,clos_ValueArray xs))) s)
     | (MemOp Update,[clos_RefPtr _ ptr; clos_Number i; x]) ->
         (match FLOOKUP (clos_state_refs s) ptr with
            SOME (clos_ValueArray xs) ->
              (if &0 <= i /\ i < &(LENGTH xs)
               then Rval (clos_Unit, clos_state_refs_fupd (K (clos_state_refs s |+
                           (ptr,clos_ValueArray (LUPDATE x (num_of_int i) xs)))) s)
               else Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (IntOp int_op, vs) ->
         (match clos_do_int_app int_op vs with
            SOME res -> Rval (res,s)
          | _ -> Rerr (Rabort Rtype_error))
     | (WordOp wordop, vs) ->
         (match clos_do_word_app wordop vs with
            SOME res -> Rval (res,s)
          | _ -> Rerr (Rabort Rtype_error))
     | (clos_FFI n, [ByteVector conf; clos_RefPtr _ ptr]) ->
         (match FLOOKUP (clos_state_refs s) ptr with
            SOME (clos_ByteArray ws) ->
              (match call_FFI (clos_state_ffi s) (ExtCall n) conf ws with
                 FFI_return ffi' ws' ->
                   Rval (clos_Unit,
                         clos_state_refs_fupd (K (clos_state_refs s |+ (ptr,clos_ByteArray ws')))
                           (clos_state_ffi_fupd (K ffi') s))
               | FFI_final outcome ->
                   Rerr (Rabort (Rffi_error outcome)))
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp BoundsCheckBlock,[clos_Block tag ys; clos_Number i]) ->
         Rval (clos_Boolv (&0 <= i /\ i < &(LENGTH ys)),s)
     | (MemOp (BoundsCheckByte loose),[ByteVector bs; clos_Number i]) ->
         Rval (clos_Boolv (&0 <= i /\ (if loose then (<=) else (<)) i (&(LENGTH bs))),s)
     | (MemOp (BoundsCheckByte loose),[clos_RefPtr _ ptr; clos_Number i]) ->
         (match FLOOKUP (clos_state_refs s) ptr with
            SOME (clos_ByteArray ws) ->
              Rval (clos_Boolv (&0 <= i /\ (if loose then (<=) else (<)) i (&(LENGTH ws))),s)
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp BoundsCheckArray,[clos_RefPtr _ ptr; clos_Number i]) ->
         (match FLOOKUP (clos_state_refs s) ptr with
            SOME (clos_ValueArray ws) ->
              Rval (clos_Boolv (&0 <= i /\ i < &(LENGTH ws)),s)
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp clos_ConfigGC,[clos_Number _; clos_Number _]) -> (Rval (clos_Unit, s))
     | (clos_ThunkOp th_op, vs) ->
         (match (th_op,vs) with
            (AllocThunk m, [v]) ->
              (if clos_bad_thunk_update m v (clos_state_refs s) then
                 Rerr (Rabort Rtype_error) else
               let ptr = (minimal ptr. ~(ptr IN FDOM (clos_state_refs s))) in
                 Rval (clos_RefPtr F ptr, clos_state_refs_fupd
                         (K (clos_state_refs s |+ (ptr,clos_Thunk m v))) s))
          | (UpdateThunk m, [clos_RefPtr F ptr; v]) ->
              (if clos_bad_thunk_update m v (clos_state_refs s) then
                 Rerr (Rabort Rtype_error) else
               match FLOOKUP (clos_state_refs s) ptr with
                 SOME (clos_Thunk NotEvaluated _) ->
                   Rval (clos_Unit, clos_state_refs_fupd
                           (K (clos_state_refs s |+ (ptr,clos_Thunk m v))) s)
               | _ -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | _ -> (Rerr (Rabort Rtype_error):(clos_v # (C,FFI)clos_state,clos_v)result)`;;

let clos_dec_clock_def = cake_def
  `clos_dec_clock n (s:(C,FFI)clos_state) =
     clos_state_clock_fupd (K (clos_state_clock s - n)) s`;;

(* HOL4 [local] *)
let clos_LESS_EQ_dec_clock = prove
 (`!(r:(C,FFI)clos_state) n (s:(C,FFI)clos_state).
     clos_state_clock r <= clos_state_clock (clos_dec_clock n s)
     ==> clos_state_clock r <= clos_state_clock s`,
  REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  ARITH_TAC);;

let clos_find_code_def = cake_def
  `clos_find_code (p:A) (args:B list) (code:(A,num # C)fmap) =
     match FLOOKUP code p with
       NONE -> NONE
     | SOME (arity,exp) -> if LENGTH args = arity then SOME (args,exp) else NONE`;;

(* The evaluation is defined as a clocked functional version of a          *)
(* conventional big-step operational semantics.                             *)

(* Proving termination of the evaluator directly is tricky. We make our     *)
(* life simpler by forcing the clock to stay good using fix_clock. At the   *)
(* bottom of this file, we remove all occurrences of fix_clock.             *)

(* HOL4 infers the most general type: s and s1 are states of independent   *)
(* types                                                                     *)
let clos_fix_clock_def = cake_def
  `clos_fix_clock (s:(A,B)clos_state) ((res:R),(s1:(C,D)clos_state)) =
     (res,clos_state_clock_fupd (K (MIN (clos_state_clock s) (clos_state_clock s1))) s1)`;;

(* HOL4 [local] *)
let clos_fix_clock_IMP = prove
 (`!(s:(A,B)clos_state) (x:R#(C,D)clos_state) res s1.
     clos_fix_clock s x = (res,s1) ==> clos_state_clock s1 <= clos_state_clock s`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `x:R#(C,D)clos_state` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:R` (X_CHOOSE_THEN `s':(C,D)clos_state` SUBST1_TAC)) THEN
  REWRITE_TAC[clos_fix_clock_def; PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM] THEN ARITH_TAC);;

(* The semantics of expression evaluation is defined next. For convenience *)
(* of subsequent proofs, the evaluation function is defined to evaluate a   *)
(* list of clos_exp expressions.                                            *)

let check_loc_def = cake_def
  `(check_loc (max_app:num) (NONE:A option) (loc:A option) (num_params:num)
              (num_args:num) (so_far:num) <=> num_args <= max_app) /\
   (check_loc max_app (SOME p) loc num_params num_args so_far <=>
      num_params = num_args /\ so_far = 0 /\ SOME p = loc)`;;

let app_kind_INDUCT,app_kind_RECURSION = cake_type
  "app_kind = Partial_app clos_v
            | Full_app clos_exp (clos_v list) (clos_v list)";;

let dest_closure_def = cake_def
  `dest_closure max_app loc_opt f (args:clos_v list) =
     match f with
       clos_Closure loc arg_env clo_env num_args exp ->
         if check_loc max_app loc_opt loc num_args (LENGTH args) (LENGTH arg_env) /\
            LENGTH arg_env < num_args then
           if ~(LENGTH args + LENGTH arg_env < num_args) then
             SOME (Full_app exp
                     (APPEND (APPEND (REVERSE (TAKE (num_args - LENGTH arg_env)
                                                    (REVERSE args)))
                                     arg_env) clo_env)
                     (REVERSE (DROP (num_args - LENGTH arg_env) (REVERSE args))))
           else
             SOME (Partial_app (clos_Closure loc (APPEND args arg_env) clo_env
                                             num_args exp))
         else
           NONE
     | clos_Recclosure loc arg_env clo_env fns i ->
         let (num_args,exp) = EL i fns in
           if LENGTH fns <= i \/
              ~check_loc max_app loc_opt (OPTION_MAP ((+) (2 * i)) loc) num_args
                         (LENGTH args) (LENGTH arg_env) \/
              ~(LENGTH arg_env < num_args)
           then NONE
           else
             let rs = list_of_seq (clos_Recclosure loc [] clo_env fns) (LENGTH fns) in
               if ~(LENGTH args + LENGTH arg_env < num_args) then
                 SOME (Full_app exp
                         (APPEND (APPEND (APPEND (REVERSE (TAKE (num_args - LENGTH arg_env)
                                                                (REVERSE args)))
                                                 arg_env) rs) clo_env)
                         (REVERSE (DROP (num_args - LENGTH arg_env) (REVERSE args))))
               else
                 SOME (Partial_app (clos_Recclosure loc (APPEND args arg_env) clo_env
                                                    fns i))
     | _ -> NONE`;;

let dest_closure_length = prove
 (`!max_app loc_opt f args exp args1 args2 (so_far:num).
     dest_closure max_app loc_opt f args = SOME (Full_app exp args1 args2)
     ==> LENGTH args2 < LENGTH args`,
  REPEAT GEN_TAC THEN CASES_ON `f:clos_v` THEN REWRITE_TAC[dest_closure_def] THEN
  SIMP[] THEN TRY PAIRARG_TAC THEN RW[] THEN
  FS[LENGTH_REVERSE; LENGTH_DROP; DE_MORGAN_THM] THEN
  MATCH_MP_TAC (ARITH_RULE `~(a + b < c) /\ b < c ==> a - (c - b) < a`) THEN
  ASM_REWRITE_TAC[]);;
let clos_env_def = cake_def
  `clos_env restrict names (env:A list) =
     if restrict then lookup_vars names env else SOME env`;;

let build_recc_def = cake_def
  `build_recc restrict loc env names fns =
     match clos_env restrict names env with
       SOME env1 -> SOME (list_of_seq (clos_Recclosure loc [] env1 fns) (LENGTH fns))
     | NONE -> NONE`;;

(* HOL4: CaseEq for const_part, op, int_op, word_op, block_op, glob_op,     *)
(* mem_op, thunk_op, list, option, v, ref, result, error_result, eq_result, *)
(* app_kind and word_size                                                   *)
let clos_case_eq_thms = end_itlist CONJ
  (map case_eq ["const_part"; "clos_op"; "int_op"; "word_op"; "block_op";
                "glob_op"; "mem_op"; "thunk_op"] @
   [list_case_eq; option_case_eq] @
   map case_eq ["clos_v"; "clos_ref"; "result"; "error_result"; "eq_result";
                "app_kind"; "word_size"]);;

let do_install_clock = prove
 (`!vs (s:(C,FFI)clos_state) e s'.
     clos_do_install vs s = (Rval e,s') ==>
     0 < clos_state_clock s /\ clos_state_clock s' = clos_state_clock s - 1`,
  RW[clos_do_install_def; clos_case_eq_thms] THEN
  TRY PAIRARG_TAC THEN GVS[clos_case_eq_thms; pair_case_eq; COND_CASE_EQ] THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`]);;

let do_install_clock_less_eq = prove
 (`!vs (s:(C,FFI)clos_state) res s'.
     clos_do_install vs s = (res,s') ==> clos_state_clock s' <= clos_state_clock s`,
  RW[clos_do_install_def; clos_case_eq_thms] THEN FS[] THEN
  TRY PAIRARG_TAC THEN GVS[clos_case_eq_thms; pair_case_eq; COND_CASE_EQ] THEN
  ARITH_TAC);;

let clos_AppUnit_def = cake_def
  `clos_AppUnit x =
     clos_App backend_common_None NONE x
       [clos_Op backend_common_None (BlockOp (clos_Cons 0)) []]`;;

(* HOL4 exp_alt_size, exp1_alt_size (on (num # exp) list), exp2_alt_size    *)
(* (on num # exp) and exp3_alt_size (on exp list): primitive recursion on   *)
(* the nested datatype, by instantiating clos_exp_RECURSION (HOL Light's    *)
(* new_recursive_definition cannot tell the [] of the two list types apart) *)

let CLOSSEMAUX_exp_alt_size_spec =
  let th = ISPECL
   [`\(a0:tra) (a1:num). 1 + (tra_size a0 + a1)`;
    `\(a0:tra) (a1:clos_exp) (a2:clos_exp) (a3:clos_exp) (r1:num) (r2:num) (r3:num).
        1 + (tra_size a0 + (r1 + (r2 + r3)))`;
    `\(a0:tra) (a1:clos_exp list) (a2:clos_exp) (r1:num) (r2:num).
        1 + (tra_size a0 + (r1 + r2))`;
    `\(a0:tra) (a1:clos_exp) (r1:num). 1 + (tra_size a0 + r1)`;
    `\(a0:tra) (a1:clos_exp) (a2:clos_exp) (r1:num) (r2:num).
        1 + (tra_size a0 + (r1 + r2))`;
    `\(a0:tra) (a1:clos_exp) (r1:num). 1 + (tra_size a0 + r1)`;
    `\(a0:tra) (a1:num) (a2:num) (a3:clos_exp list) (r1:num).
        1 + (tra_size a0 + (a1 + (a2 + r1)))`;
    `\(a0:tra) (a1:num option) (a2:clos_exp) (a3:clos_exp list) (r1:num) (r2:num).
        1 + (tra_size a0 + (option_size (\x. x) a1 + (r1 + r2)))`;
    `\(a0:mlstring) (a1:num option) (a2:(num list) option) (a3:num) (a4:clos_exp)
      (r1:num).
        1 + (mlstring_size a0 +
             (option_size (\x. x) a1 +
              (option_size (list_size (\x. x)) a2 + (a3 + r1))))`;
    `\(a0:mlstring list) (a1:num option) (a2:(num list) option)
      (a3:(num # clos_exp) list) (a4:clos_exp) (r1:num) (r2:num).
        1 + (list_size mlstring_size a0 +
             (option_size (\x. x) a1 +
              (option_size (list_size (\x. x)) a2 + (r1 + r2))))`;
    `\(a0:tra) (a1:clos_op) (a2:clos_exp list) (r1:num).
        1 + (tra_size a0 + (clos_op_size a1 + r1)) +
        (if a1 = clos_ThunkOp ForceThunk then 100 else 0)`;
    `0`;
    `\(a0:clos_exp) (a1:clos_exp list) (r0:num) (r1:num). 1 + (r0 + r1)`;
    `0`;
    `\(a0:num # clos_exp) (a1:(num # clos_exp) list) (r0:num) (r1:num). 1 + (r0 + r1)`;
    `\(a0:num) (a1:clos_exp) (r1:num). 1 + (a0 + r1)`] clos_exp_RECURSION in
  new_specification ["clos_exp_alt_size"; "clos_exp3_alt_size";
                     "clos_exp1_alt_size"; "clos_exp2_alt_size"]
    (CONV_RULE (DEPTH_CONV BETA_CONV) th);;

let clos_exp_alt_size_def = prove
 (end_itlist (curry mk_conj)
  [`!a0 a1. clos_exp_alt_size (clos_Var a0 a1) = 1 + (tra_size a0 + a1)`;
   `!a0 a1 a2 a3. clos_exp_alt_size (clos_If a0 a1 a2 a3) =
      1 + (tra_size a0 + (clos_exp_alt_size a1 +
                          (clos_exp_alt_size a2 + clos_exp_alt_size a3)))`;
   `!a0 a1 a2. clos_exp_alt_size (clos_Let a0 a1 a2) =
      1 + (tra_size a0 + (clos_exp3_alt_size a1 + clos_exp_alt_size a2))`;
   `!a0 a1. clos_exp_alt_size (clos_Raise a0 a1) =
      1 + (tra_size a0 + clos_exp_alt_size a1)`;
   `!a0 a1 a2. clos_exp_alt_size (clos_Handle a0 a1 a2) =
      1 + (tra_size a0 + (clos_exp_alt_size a1 + clos_exp_alt_size a2))`;
   `!a0 a1. clos_exp_alt_size (clos_Tick a0 a1) =
      1 + (tra_size a0 + clos_exp_alt_size a1)`;
   `!a0 a1 a2 a3. clos_exp_alt_size (clos_Call a0 a1 a2 a3) =
      1 + (tra_size a0 + (a1 + (a2 + clos_exp3_alt_size a3)))`;
   `!a0 a1 a2 a3. clos_exp_alt_size (clos_App a0 a1 a2 a3) =
      1 + (tra_size a0 + (option_size (\x. x) a1 +
                          (clos_exp_alt_size a2 + clos_exp3_alt_size a3)))`;
   `!a0 a1 a2 a3 a4. clos_exp_alt_size (Fn a0 a1 a2 a3 a4) =
      1 + (mlstring_size a0 +
           (option_size (\x. x) a1 +
            (option_size (list_size (\x. x)) a2 + (a3 + clos_exp_alt_size a4))))`;
   `!a0 a1 a2 a3 a4. clos_exp_alt_size (clos_Letrec a0 a1 a2 a3 a4) =
      1 + (list_size mlstring_size a0 +
           (option_size (\x. x) a1 +
            (option_size (list_size (\x. x)) a2 +
             (clos_exp1_alt_size a3 + clos_exp_alt_size a4))))`;
   `!a0 a1 a2. clos_exp_alt_size (clos_Op a0 a1 a2) =
      1 + (tra_size a0 + (clos_op_size a1 + clos_exp3_alt_size a2)) +
      (if a1 = clos_ThunkOp ForceThunk then 100 else 0)`;
   `clos_exp1_alt_size [] = 0`;
   `!a0 a1. clos_exp1_alt_size (CONS a0 a1) =
      1 + (clos_exp2_alt_size a0 + clos_exp1_alt_size a1)`;
   `!a0 a1. clos_exp2_alt_size (a0,a1) = 1 + (a0 + clos_exp_alt_size a1)`;
   `clos_exp3_alt_size [] = 0`;
   `!a0 a1. clos_exp3_alt_size (CONS a0 a1) =
      1 + (clos_exp_alt_size a0 + clos_exp3_alt_size a1)`],
  REWRITE_TAC[CLOSSEMAUX_exp_alt_size_spec]);;
let _ = cake_add_simps [clos_exp_alt_size_def];;

(* HOL4 [local,simp]: not registered (descendants do not see it in HOL4) *)
let exp3_alt_size = prove
 (`!xs. clos_exp3_alt_size xs = list_size clos_exp_alt_size xs`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[clos_exp_alt_size_def; list_size]);;

(* ------------------------------------------------------------------------- *)
(* The semantics (HOL4 evaluate_def before the clean-up below).  The         *)
(* clauses are parsed in two quotations (HOL4 types each clause on its own:  *)
(* args is an expression list in the clause for App and a value list in     *)
(* evaluate_app).  HOL4's let build_rc e = t in b is written                *)
(* let build_rc = \e. t in b (the same term in HOL4; HOL Light parses the    *)
(* first form as a pattern abstraction, which its recursion package cannot  *)
(* handle).                                                                  *)
(* ------------------------------------------------------------------------- *)

let CLOSSEMAUX_evaluate_clauses1 =
  `(clos_evaluate ([]:clos_exp list,env:clos_v list,s:(C,FFI)clos_state) =
      (Rval [],s)) /\
   (clos_evaluate (CONS x (CONS y xs),env,s) =
      match clos_fix_clock s (clos_evaluate ([x],env,s)) with
        (Rval v1,s1) ->
          (match clos_evaluate (CONS y xs,env,s1) with
             (Rval vs,s2) -> (Rval (CONS (HD v1) vs),s2)
           | res -> res)
      | res -> res) /\
   (clos_evaluate ([clos_Var _ n],env,s) =
      if n < LENGTH env then (Rval [EL n env],s)
      else (Rerr (Rabort Rtype_error),s)) /\
   (clos_evaluate ([clos_If _ x1 x2 x3],env,s) =
      match clos_fix_clock s (clos_evaluate ([x1],env,s)) with
        (Rval vs,s1) ->
          if clos_Boolv T = HD vs then clos_evaluate ([x2],env,s1) else
          if clos_Boolv F = HD vs then clos_evaluate ([x3],env,s1) else
            (Rerr (Rabort Rtype_error),s1)
      | res -> res) /\
   (clos_evaluate ([clos_Let _ xs x2],env,s) =
      match clos_fix_clock s (clos_evaluate (xs,env,s)) with
        (Rval vs,s1) -> clos_evaluate ([x2],APPEND vs env,s1)
      | res -> res) /\
   (clos_evaluate ([clos_Raise _ x1],env,s) =
      match clos_evaluate ([x1],env,s) with
        (Rval vs,s) -> (Rerr (Rraise (HD vs)),s)
      | res -> res) /\
   (clos_evaluate ([clos_Handle _ x1 x2],env,s1) =
      match clos_fix_clock s1 (clos_evaluate ([x1],env,s1)) with
        (Rerr (Rraise v),s) -> clos_evaluate ([x2],CONS v env,s)
      | res -> res) /\
   (clos_evaluate ([clos_Op _ op xs],env,s) =
      match clos_fix_clock s (clos_evaluate (xs,env,s)) with
        (Rval vs,s) ->
          if op = clos_Install then
            (match clos_do_install (REVERSE vs) s with
               (Rval es,s) ->
                 (match clos_evaluate (es,[],s) with
                    (Rval vs,s) -> (Rval [LAST vs],s)
                  | res -> res)
             | (Rerr err,s) -> (Rerr err,s))
          else if op = clos_ThunkOp ForceThunk then
            (match clos_dest_thunk vs (clos_state_refs s) with
               clos_BadRef -> (Rerr (Rabort Rtype_error),s)
             | clos_NotThunk -> (Rerr (Rabort Rtype_error),s)
             | clos_IsThunk Evaluated v -> (Rval [v],s)
             | clos_IsThunk NotEvaluated f ->
                 (match clos_evaluate ([clos_AppUnit (clos_Var backend_common_None 0)],
                                       [f],s) with
                    (Rval vs2,s) ->
                      (match clos_update_thunk vs (clos_state_refs s) vs2 with
                         NONE -> (Rerr (Rabort Rtype_error),s)
                       | SOME refs -> (Rval vs2,clos_state_refs_fupd (K refs) s))
                  | (Rerr e,s) -> (Rerr e,s)))
          else
            (match clos_do_app op (REVERSE vs) s with
               Rerr err -> (Rerr err,s)
             | Rval (v,s) -> (Rval [v],s))
      | res -> res) /\
   (clos_evaluate ([Fn _ loc vsopt num_args exp],env,s) =
      if num_args <= clos_state_max_app s /\ ~(num_args = 0) then
        (match vsopt with
           NONE -> (Rval [clos_Closure loc [] env num_args exp], s)
         | SOME vs ->
             (match lookup_vars vs env with
                NONE -> (Rerr (Rabort Rtype_error),s)
              | SOME env' -> (Rval [clos_Closure loc [] env' num_args exp], s)))
      else
        (Rerr (Rabort Rtype_error), s)) /\
   (clos_evaluate ([clos_Letrec _ loc namesopt fns exp],env,s) =
      if ALL (\p. match p with
                    (num_args,e) -> num_args <= clos_state_max_app s /\
                                    ~(num_args = 0)) fns then
        let build_rc = \e. list_of_seq (clos_Recclosure loc [] e fns) (LENGTH fns) in
        let envdelta =
          (match namesopt with
             NONE -> SOME (build_rc env)
           | SOME names -> OPTION_MAP build_rc (lookup_vars names env)) in
        (match envdelta with
           NONE -> (Rerr (Rabort Rtype_error),s)
         | SOME ed -> clos_evaluate ([exp],APPEND ed env,s))
      else
        (Rerr (Rabort Rtype_error), s)) /\
   (clos_evaluate ([clos_App _ loc_opt x1 args],env,s) =
      if LENGTH args > 0 then
        (match clos_fix_clock s (clos_evaluate (args,env,s)) with
           (Rval y2,s1) ->
             (match clos_fix_clock s1 (clos_evaluate ([x1],env,s1)) with
                (Rval y1,s2) -> evaluate_app loc_opt (HD y1) y2 s2
              | res -> res)
         | res -> res)
      else
        (Rerr (Rabort Rtype_error), s)) /\
   (clos_evaluate ([clos_Tick _ x],env,s) =
      if clos_state_clock s = 0 then (Rerr (Rabort Rtimeout_error),s)
      else clos_evaluate ([x],env,clos_dec_clock 1 s)) /\
   (clos_evaluate ([clos_Call _ ticks dest xs],env,s1) =
      match clos_fix_clock s1 (clos_evaluate (xs,env,s1)) with
        (Rval vs,s) ->
          (match clos_find_code dest vs (clos_state_code s) with
             NONE -> (Rerr (Rabort Rtype_error),s)
           | SOME (args,exp) ->
               if clos_state_clock s < ticks + 1 then
                 (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (K 0) s)
               else
                 clos_evaluate ([exp],args,clos_dec_clock (ticks + 1) s))
      | res -> res)`;;

let CLOSSEMAUX_evaluate_clauses2 =
  `(evaluate_app (loc_opt:num option) (f:clos_v) [] (s:(C,FFI)clos_state) =
      (Rval [f]:(clos_v list,clos_v)result, s)) /\
   (evaluate_app loc_opt f args s =
      match dest_closure (clos_state_max_app s) loc_opt f args with
        NONE -> (Rerr (Rabort Rtype_error),s)
      | SOME (Partial_app v) ->
          if clos_state_clock s < LENGTH args
          then (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (K 0) s)
          else (Rval [v], clos_dec_clock (LENGTH args) s)
      | SOME (Full_app exp env rest_args) ->
          if clos_state_clock s < LENGTH args - LENGTH rest_args
          then (Rerr (Rabort Rtimeout_error),clos_state_clock_fupd (K 0) s)
          else
            (match clos_fix_clock (clos_dec_clock (LENGTH args - LENGTH rest_args) s)
                     (clos_evaluate ([exp],env,
                                     clos_dec_clock (LENGTH args - LENGTH rest_args) s)) with
               (Rval [v], s1) -> evaluate_app loc_opt v rest_args s1
             | res -> res))`;;

let CLOSSEMAUX_evaluate_clauses =
  list_mk_conj (conjuncts CLOSSEMAUX_evaluate_clauses1 @
                conjuncts CLOSSEMAUX_evaluate_clauses2);;

(* HOL4's termination relation:                                              *)
(*   inv_image (measure I LEX measure I LEX measure I)                       *)
(*     (\x. case x of INL (xs,env,s) => (s.clock,list_size exp_alt_size xs,0)*)
(*                  | INR (l,f,args,s) => (s.clock,0,LENGTH args))           *)

let CLOSSEMAUX_evaluate_rel =
  `inv_image (measure (I:num->num) LEX measure (I:num->num) LEX measure (I:num->num))
     (\x:(clos_exp list # clos_v list # (C,FFI)clos_state) +
         (num option # clos_v # clos_v list # (C,FFI)clos_state).
        sum_CASE x
          (\t. clos_state_clock (SND (SND t)),list_size clos_exp_alt_size (FST t),0)
          (\t. clos_state_clock (SND (SND (SND t))),0,LENGTH (FST (SND (SND t)))))`;;

(* ------------------------------------------------------------------------- *)
(* The termination tactic (HOL4: rpt strip_tac \\ simp[dec_clock_def] \\     *)
(* imp_res_tac fix_clock_IMP \\ fs[] \\ imp_res_tac do_install_clock \\      *)
(* imp_res_tac dest_closure_length \\ imp_res_tac LESS_EQ_dec_clock \\ fs[]  *)
(* \\ simp [AppUnit_def] \\ IF_CASES_TAC \\ gvs []).  It handles both kinds  *)
(* of termination conditions (R a' a, and !y. R y a' ==> R y a for a tail   *)
(* call).                                                                    *)
(* ------------------------------------------------------------------------- *)

let CLOSSEMAUX_is_num_fact tm =
  let t = if is_neg tm then dest_neg tm else tm in
  try let h,args = strip_comb t in
      length args = 2 && type_of (hd args) = `:num` &&
      mem (fst(dest_const h)) ["="; "<"; "<="; ">"; ">="]
  with Failure _ -> false;;

let CLOSSEMAUX_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP clos_fix_clock_IMP)) THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP do_install_clock)) THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP dest_closure_length)) THEN
  REPEAT GEN_TAC THEN
  (fun g -> let ths = [inv_image_THM; LEX_DEF; sum_CASE; FST; SND; I_THM;
                       measure_THM; clos_dec_clock_def; clos_state_INFO.ri_accfupds;
                       K_THM; clos_exp_alt_size_def; exp3_alt_size; clos_AppUnit_def;
                       list_size; LENGTH; distinctness "clos_op"] @
                      !the_size_defs @ flat (map snd (!the_size_aux_eqs)) in
            (RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths) g) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONJ_ASSOC]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then
                                   STRIP_ASSUME_TAC th else NO_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSSEMAUX_is_num_fact o concl))) THEN
  ARITH_TAC;;

(* HOL4 evaluate_def (the first one, with fix_clock); defined with          *)
(* sem1aux_def_wf (semantics/sem1aux_tfl.ml); about 4 minutes               *)

let CLOSSEMAUX_evaluate_fix_def =
  sem1aux_def_wf CLOSSEMAUX_evaluate_rel CLOSSEMAUX_TC_TAC CLOSSEMAUX_evaluate_clauses;;

(* HOL4's first evaluate_ind *)
let CLOSSEMAUX_evaluate_fix_ind = cake_ind "clos_evaluate";;

let evaluate_app_NIL = prove
 (`!loc v (s:(C,FFI)clos_state). evaluate_app loc v [] s = (Rval [v],s)`,
  REWRITE_TAC[CLOSSEMAUX_evaluate_fix_def]);;
let _ = cake_add_simps [evaluate_app_NIL];;

(* We prove that the clock never increases. *)

let clos_do_app_const = prove
 (`!op args (s1:(C,FFI)clos_state) res s2.
     clos_do_app op args s1 = Rval (res,s2) ==>
     clos_state_clock s2 = clos_state_clock s1 /\
     clos_state_max_app s2 = clos_state_max_app s1 /\
     clos_state_code s2 = clos_state_code s1 /\
     clos_state_compile_oracle s2 = clos_state_compile_oracle s1 /\
     clos_state_compile s2 = clos_state_compile s1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_do_app_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM]);;

(* HOL4: ho_match_mp_tac evaluate_ind \\ REPEAT STRIP_TAC \\ POP_ASSUM       *)
(* MP_TAC \\ ONCE_REWRITE_TAC [evaluate_def] \\ ... \\ EVERY_CASE_TAC \\     *)
(* ... \\ RES_TAC \\ IMP_RES_TAC fix_clock_IMP \\ ... \\ IMP_RES_TAC          *)
(* do_app_const \\ IMP_RES_TAC do_install_clock_less_eq \\ ... DECIDE_TAC   *)

let CLOSSEMAUX_CLOCK_TAC : tactic =
  REWRITE_TAC[SND] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[CLOSSEMAUX_evaluate_fix_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  FS[PAIR_EQ] THEN
  RES_TAC THEN RES_TAC THEN
  IMP_RES_TAC clos_fix_clock_IMP THEN
  IMP_RES_TAC clos_do_app_const THEN
  IMP_RES_TAC do_install_clock_less_eq THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM]) THEN
  REWRITE_TAC[clos_dec_clock_def; clos_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSSEMAUX_is_num_fact o concl))) THEN
  ARITH_TAC;;

(* HOL4 [local] *)
let evaluate_clock_help = prove
 (`(!tup vs (s2:(C,FFI)clos_state).
      clos_evaluate tup = (vs,s2) ==>
      clos_state_clock s2 <= clos_state_clock (SND (SND tup))) /\
   (!loc_opt f args (s1:(C,FFI)clos_state) vs s2.
      evaluate_app loc_opt f args s1 = (vs,s2) ==>
      clos_state_clock s2 <= clos_state_clock s1)`,
  MATCH_MP_TAC CLOSSEMAUX_evaluate_fix_ind THEN REPEAT CONJ_TAC THEN
  CLOSSEMAUX_CLOCK_TAC);;

let clos_evaluate_clock = prove
 (`(!xs env (s1:(C,FFI)clos_state) vs s2.
      clos_evaluate (xs,env,s1) = (vs,s2) ==>
      clos_state_clock s2 <= clos_state_clock s1) /\
   (!loc_opt f args (s1:(C,FFI)clos_state) vs s2.
      evaluate_app loc_opt f args s1 = (vs,s2) ==>
      clos_state_clock s2 <= clos_state_clock s1)`,
  MESON_TAC[evaluate_clock_help; SND]);;

let clos_fix_clock_evaluate = prove
 (`!(s:(C,FFI)clos_state) xs env.
     clos_fix_clock s (clos_evaluate (xs,env,s)) = clos_evaluate (xs,env,s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `clos_evaluate (xs,env,s:(C,FFI)clos_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s1:(C,FFI)clos_state` (fun th -> ASSUME_TAC th THEN
                                                   REWRITE_TAC[th]))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (CONJUNCT1 clos_evaluate_clock)) THEN
  REWRITE_TAC[clos_fix_clock_def; PAIR_EQ; clos_state_component_equality;
              clos_state_INFO.ri_accfupds; K_THM] THEN
  ASM_ARITH_TAC);;

(* Finally, we remove fix_clock from the induction and definition theorems. *)

let clos_evaluate_def = REWRITE_RULE[clos_fix_clock_evaluate] CLOSSEMAUX_evaluate_fix_def;;

let clos_evaluate_ind = REWRITE_RULE[clos_fix_clock_evaluate] CLOSSEMAUX_evaluate_fix_ind;;

(* cake_ind returns HOL4's final induction theorem *)
let () =
  cake_ind_store := ["clos_evaluate",clos_evaluate_ind;
                     "evaluate_app",clos_evaluate_ind] @ !cake_ind_store;;

(* observational semantics *)

let clos_initial_state_def = cake_def
  `clos_initial_state (ffi:(FFI)ffi_state) ma code (co:num -> C # clos_prog) cc k =
     clos_state_REC [] FEMPTY ffi k cc co code ma`;;

let clos_semantics_def = cake_def
  `clos_semantics (ffi:(FFI)ffi_state) ma code (co:num -> C # clos_prog) cc es =
     let st = clos_initial_state ffi ma code co cc in
       if ?k. FST (clos_evaluate (es,[],st k)) = Rerr (Rabort Rtype_error)
       then Fail
       else
       (match some res.
          ?k r s outcome.
            clos_evaluate (es,[],st k) = (r,s) /\
            (match r with
               Rerr (Rabort Rtimeout_error) -> F
             | Rerr (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
             | _ -> outcome = Success) /\
            res = Terminate outcome (ffi_state_io_events (clos_state_ffi s))
        with
          SOME res -> res
        | NONE ->
            Diverge
              (build_lprefix_lub
                (IMAGE (\k. llist_fromList
                          (ffi_state_io_events
                             (clos_state_ffi (SND (clos_evaluate (es,[],st k))))))
                       UNIV)))`;;
