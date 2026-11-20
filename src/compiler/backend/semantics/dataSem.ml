(* ========================================================================= *)
(* dataSem: port of HOL4 compiler/backend/semantics/dataSemScript.sml        *)
(* (CakeML v3479).  The formal semantics of dataLang.                        *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 num_map is A spt, num_set is 1 spt; word8 is byte, word64 int64;   *)
(*   n2w/w2n/i2w/w2w are word/val/iword/word_zx; LEAST is minimal; Num is    *)
(*   num_of_int; int / and % are int_div and integer_int_mod.                *)
(* - HOL4 r with <| f1 := x; f2 := y |> is f1_fupd (K x) (f2_fupd (K y) r);  *)
(*   the overloads (Error, add_space_safe, heap_peak, bignum_limit,         *)
(*   do_space_safe, do_space_peak, ...) are written out where used.          *)
(* - size_of_stack takes its list argument (HOL4: point-free FOLDR).         *)
(* - The first size_of_def/size_of_ind (with check_res) and evaluate_def/    *)
(*   evaluate_ind (with fix_clock) are DSEMAUX_size_of_check_def/ind and     *)
(*   DSEMAUX_evaluate_fix_def/ind; size_of_def, data_evaluate_def etc. are  *)
(*   the final HOL4 theorems.  In evaluate's Force and Call clauses HOL4's   *)
(*   let s1 = call_env args1 ss (push_env env .. (dec_clock s)) is written   *)
(*   out at its uses.                                                        *)
(* - DSEMAUX_ names are local helpers of this file.                         *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/sptree.ml";;
needs "hol4/lprefix_lub.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/sem1aux_tfl.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_simp.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/data_space.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/word_depth.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/semantics/backendProps.ml";;

type_invention_error := true;;

(* The induction theorem of a definition without recursion, with one case  *)
(* per completed clause (HOL4 TFL makes one for multi-clause definitions);   *)
(* derived from the clauses with the kit's derive_induction (as bvlSem's    *)
(* CLOSSEMAUX_cases_ind)                                                     *)

let data_v_INDUCT,data_v_RECURSION = cake_type
  "data_v = data_Number int
          | data_Word64 int64
          | data_Block num num (data_v list)
          | data_CodePtr num
          | data_RefPtr bool num";;

let data_Boolv_def = cake_def
  `data_Boolv b = data_Block 0 (bool_to_tag b) []`;;

let data_Unit_def = cake_def
  `data_Unit = data_Block 0 tuple_tag []`;;

let stack_INDUCT,stack_RECURSION = cake_type
  "stack = data_Env (num option) (data_v spt)
         | Exc (num option) (data_v spt) num";;

let limits_INFO = cake_record "limits"
  ["heap_limit","num";
   "length_limit","num";
   "stack_limit","num";
   "arch_64_bit","bool";
   "has_fp_ops","bool";
   "has_fp_tops","bool"];;

let limits_component_equality = limits_INFO.ri_component_equality;;

let data_state_INFO = cake_record "data_state"
  ["locals","data_v spt";
   "locals_size","num option";
   "stack","stack list";
   "stack_max","num option";
   "stack_frame_sizes","num spt";
   "global","num option";
   "handler","num";
   "refs","((data_v)bvl_ref)spt";
   "compile","C -> (num # num # data_prog) list -> (byte list # int64 list # C) option";
   "clock","num";
   "code","(num # data_prog) spt";
   "ffi","(FFI)ffi_state";
   "space","num";
   "tstamps","num option";
   "limits","limits";
   "safe_for_space","bool";
   "peak_heap_length","num";
   "compile_oracle","num -> C # (num # num # data_prog) list"];;

let data_state_component_equality = data_state_INFO.ri_component_equality;;

let arch_size_def = cake_def
  `arch_size lims = if limits_arch_64_bit lims then 64 else 32`;;

(* HOL4 infers the most general type *)
let check_res_def = cake_def
  `check_res (r:A spt) ((n:B),(refs:A spt),(seen:C)) =
     if size refs <= size r then (n,refs,seen) else (n,r,seen)`;;

let check_res_IMP = prove
 (`!(y:B#A spt#C) (n:B) (r:A spt) (s:C) (t:A spt).
     (n,r,s) = check_res t y ==> size r <= size t`,
  REWRITE_TAC[FORALL_PAIR_THM; check_res_def] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)]) THEN
  ASM_ARITH_TAC);;

let small_num_def = cake_def
  `small_num arch64 (i:int) <=>
     if arch64 then --((&2:int) pow 61) <= i /\ i < (&2:int) pow 61
     else --((&2:int) pow 29) <= i /\ i < (&2:int) pow 29`;;

let bignum_digits_def = cake_def_wf
  `measure (\p:bool#num. SND p)`
  (REWRITE_TAC[measure_THM; FST; SND; LET_DEF; LET_END_DEF] THEN REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
   COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC)
  `bignum_digits arch64 n =
     if n = 0 then 0 else
       let d = if arch64 then 64 else 32 in
         1 + bignum_digits arch64 (n DIV 2 EXP d)`;;

let bignum_size_def = cake_def
  `bignum_size arch64 (i:int) = 1 + bignum_digits arch64 (num_of_int (abs i))`;;

(* HOL4's termination relation:                                              *)
(*   inv_image (measure I LEX measure (list_size v_size))                    *)
(*             (\(lims,vs,refs,seen). (sptree$size refs,vs))                 *)

let DSEMAUX_size_of_rel =
  `inv_image (measure (I:num->num) LEX measure (list_size data_v_size))
     (\x:limits # data_v list # ((data_v)bvl_ref)spt # num_set.
        size (FST (SND (SND x))),FST (SND x))`;;

let DSEMAUX_size_of_clauses =
  `(size_of (lims:limits) ([]:data_v list) (refs:((data_v)bvl_ref)spt)
            (seen:num_set) = (0,refs,seen)) /\
   (size_of lims (CONS x (CONS y ys)) refs seen =
      let (n1,refs1,seen1) = check_res refs (size_of lims (CONS y ys) refs seen) in
      let (n2,refs2,seen2) = size_of lims [x] refs1 seen1 in
        (n1 + n2,refs2,seen2)) /\
   (size_of lims [data_Word64 _] refs seen = (3,refs,seen)) /\
   (size_of lims [data_Number i] refs seen =
      ((if small_num (limits_arch_64_bit lims) i then 0
        else bignum_size (limits_arch_64_bit lims) i),refs,seen)) /\
   (size_of lims [data_CodePtr _] refs seen = (0,refs,seen)) /\
   (size_of lims [data_RefPtr _ r] refs seen =
      match lookup r refs with
        NONE -> (0,refs,seen)
      | SOME (bvl_ByteArray _ bs) ->
          (LENGTH bs DIV (arch_size lims DIV 8) + 2,delete r refs,seen)
      | SOME (bvl_ValueArray vs) ->
          let (n,refs,seen) = size_of lims vs (delete r refs) seen in
            (n + LENGTH vs + 1,refs,seen)
      | SOME (bvl_Thunk _ v) ->
          let (n,refs,seen) = size_of lims [v] (delete r refs) seen in
            (n + 2,refs,seen)
      | SOME (MutBlock tg fin ls c rs) ->
          let (n,refs,seen) = size_of lims (APPEND (APPEND ls [c]) rs)
                                      (delete r refs) seen in
            (n + LENGTH ls + LENGTH rs + 2,refs,seen)) /\
   (size_of lims [data_Block ts tag []] refs seen = (0,refs,seen)) /\
   (size_of lims [data_Block ts tag vs] refs seen =
      if IS_SOME (lookup ts seen) then (0,refs,seen) else
        let (n,refs,seen) = size_of lims vs refs (insert ts one seen) in
          (n + LENGTH vs + 1,refs,seen))`;;

(* HOL4: rpt strip_tac \\ fs [sptreeTheory.size_delete]                      *)
(*   \\ imp_res_tac miscTheory.lookup_zero \\ fs [] \\ rw [] \\ fs []         *)
(*   \\ imp_res_tac check_res_IMP \\ fs []                                    *)

let DSEMAUX_SIZE_OF_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN REPEAT GEN_TAC THEN
  (fun (asl,w) ->
     MAP_EVERY (fun (_,th) ->
        (try ASSUME_TAC (MATCH_MP lookup_zero th) with Failure _ -> ALL_TAC) THEN
        (try ASSUME_TAC (MATCH_MP check_res_IMP (SYM th)) with Failure _ -> ALL_TAC))
       asl (asl,w)) THEN
  REWRITE_TAC[inv_image_THM; LEX_DEF; FST; SND; I_THM; measure_THM; size_delete] THEN
  ASM_REWRITE_TAC[option_DISTINCT] THEN
  REWRITE_TAC (!the_size_defs @ flat (map snd (!the_size_aux_eqs)) @
               [list_size; LENGTH; APPEND]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSSEMAUX_is_num_fact o concl))) THEN
  ARITH_TAC;;

(* HOL4's first size_of_def and size_of_ind (with check_res) *)
let DSEMAUX_size_of_check_def =
  cake_def_wf DSEMAUX_size_of_rel DSEMAUX_SIZE_OF_TC_TAC DSEMAUX_size_of_clauses;;

let DSEMAUX_size_of_check_ind = cake_ind "size_of";;

let DSEMAUX_size_of_refs = prove
 (`!lims vs refs seen.
     size (FST (SND (size_of lims vs refs seen))) <=
     size (refs:((data_v)bvl_ref)spt)`,
  MATCH_MP_TAC DSEMAUX_size_of_check_ind THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THENL
   [REWRITE_TAC[DSEMAUX_size_of_check_def; FST; SND; LE_REFL];
    STRIP_TAC THEN ONCE_REWRITE_TAC[DSEMAUX_size_of_check_def] THEN
    MP_TAC(ISPEC `check_res (refs:((data_v)bvl_ref)spt)
                    (size_of lims (CONS y ys) refs seen)` PAIR_SURJECTIVE) THEN
    REWRITE_TAC[EXISTS_PAIR_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `refs1:((data_v)bvl_ref)spt`
      (X_CHOOSE_THEN `seen1:num_set` ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[pair_CASE_def] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`n1:num`; `refs1:((data_v)bvl_ref)spt`; `seen1:num_set`]) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `size_of lims [x] (refs1:((data_v)bvl_ref)spt) seen1`
             PAIR_SURJECTIVE) THEN
    REWRITE_TAC[EXISTS_PAIR_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `n2:num` (X_CHOOSE_THEN `refs2:((data_v)bvl_ref)spt`
      (X_CHOOSE_THEN `seen2:num_set` ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[pair_CASE_def; FST; SND] THEN
    MP_TAC(ISPECL [`size_of lims (CONS y ys) (refs:((data_v)bvl_ref)spt) seen`;
                   `n1:num`; `refs1:((data_v)bvl_ref)spt`; `seen1:num_set`;
                   `refs:((data_v)bvl_ref)spt`] check_res_IMP) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    REWRITE_TAC[DSEMAUX_size_of_check_def; FST; SND; LE_REFL];
    REWRITE_TAC[DSEMAUX_size_of_check_def; FST; SND; LE_REFL];
    REWRITE_TAC[DSEMAUX_size_of_check_def; FST; SND; LE_REFL];
    STRIP_TAC THEN ONCE_REWRITE_TAC[DSEMAUX_size_of_check_def] THEN
    TOP_CASE_TAC THEN REWRITE_TAC[FST; SND; LE_REFL] THEN
    SUBGOAL_THEN `size (delete r (refs:((data_v)bvl_ref)spt)) <= size refs`
      ASSUME_TAC THENL [REWRITE_TAC[size_delete] THEN ARITH_TAC; ALL_TAC] THEN
    TOP_CASE_TAC THEN REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[] THEN
    REPEAT PAIRARG_TAC THEN GVS[] THEN ASM_ARITH_TAC;
    REWRITE_TAC[DSEMAUX_size_of_check_def; FST; SND; LE_REFL];
    STRIP_TAC THEN ONCE_REWRITE_TAC[DSEMAUX_size_of_check_def] THEN
    COND_CASES_TAC THEN REWRITE_TAC[FST; SND; LE_REFL] THEN
    REPEAT PAIRARG_TAC THEN ASM_REWRITE_TAC[FST; SND] THEN
    RES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 [local] *)
let check_res_size_of = prove
 (`!lims vs refs seen.
     check_res refs (size_of lims vs refs seen) = size_of lims vs refs seen`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`lims:limits`; `vs:data_v list`; `refs:((data_v)bvl_ref)spt`;
                `seen:num_set`] DSEMAUX_size_of_refs) THEN
  MP_TAC(ISPEC `size_of lims vs (refs:((data_v)bvl_ref)spt) seen` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[EXISTS_PAIR_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FST; SND; check_res_def] THEN SIMP_TAC[]);;

let size_of_def = REWRITE_RULE[check_res_size_of] DSEMAUX_size_of_check_def;;

let size_of_ind = REWRITE_RULE[check_res_size_of] DSEMAUX_size_of_check_ind;;

let () = cake_ind_store := ("size_of",size_of_ind) :: !cake_ind_store;;

let extract_stack_def = cake_def
  `(extract_stack (data_Env _ env) = toList env) /\
   (extract_stack (Exc _ env _) = toList env)`;;

let global_to_vs_def = cake_def
  `(global_to_vs NONE = []) /\
   (global_to_vs (SOME n) = [data_RefPtr T n])`;;

let stack_to_vs_def = cake_def
  `stack_to_vs (s:(C,FFI)data_state) =
     APPEND (APPEND (toList (data_state_locals s))
                    (FLAT (MAP extract_stack (data_state_stack s))))
            (global_to_vs (data_state_global s))`;;

(* Measures the amount of space everything in a dataLang heap would need   *)
(* to fit in wordLang memory (over-approximation)                            *)

let size_of_heap_def = cake_def
  `size_of_heap (s:(C,FFI)data_state) =
     match size_of (data_state_limits s) (stack_to_vs s) (data_state_refs s) LN with
       (n,_,_) -> n`;;

let no_thunks_in_refs_def = cake_def
  `no_thunks_in_refs (refs:((A)bvl_ref)spt) <=>
     !k e v. ~(lookup k refs = SOME (bvl_Thunk e v))`;;

(* HOL4 overloads add_space_safe and heap_peak, written out:               *)
(*   add_space_safe k s = s.safe_for_space /\ no_thunks_in_refs s.refs /\  *)
(*                        size_of_heap s + k <= s.limits.heap_limit        *)
(*   heap_peak k s = MAX s.peak_heap_length (size_of_heap s + k)           *)

let add_space_def = cake_def
  `add_space (s:(C,FFI)data_state) k =
     data_state_space_fupd (K k)
       (data_state_safe_for_space_fupd
          (K (data_state_safe_for_space s /\
              no_thunks_in_refs (data_state_refs s) /\
              size_of_heap s + k <= limits_heap_limit (data_state_limits s)))
          (data_state_peak_heap_length_fupd
             (K (MAX (data_state_peak_heap_length s) (size_of_heap s + k))) s))`;;

(* Args-aware variant: cost reflects op_args + non-arg locals as the GC-root *)
(* set, matching wordSem's view at the op's inner Alloc. stack_to_vs         *)
(* already covers s.locals (which, when the dataLang evaluator hands the     *)
(* state to do_app, is the NARROW cut without args).                         *)

let size_of_heap_args_def = cake_def
  `size_of_heap_args op_args (s:(C,FFI)data_state) =
     match size_of (data_state_limits s) (APPEND op_args (stack_to_vs s))
                   (data_state_refs s) LN with
       (n,_,_) -> n`;;

(* HOL4 overloads add_space_safe_args and heap_peak_args (unused here) *)

let consume_space_def = cake_def
  `consume_space k (s:(C,FFI)data_state) =
     if data_state_space s < k then NONE
     else SOME (data_state_space_fupd (K (data_state_space s - k)) s)`;;

(* Determines which operations are safe for space *)

let allowed_op_def = cake_def
  `allowed_op op (_:A) <=>
     ~(op = clos_Install) /\ !t i. ~(op = MemOp (MutCons t i))`;;

let data_v_to_list_def = sem1aux_def_wf
  `measure data_v_size`
  SEM1AUX_TC_TAC
  `(data_v_to_list (data_Block ts tag []) =
      if tag = nil_tag then SOME [] else NONE) /\
   (data_v_to_list (data_Block ts tag [h; bt]) =
      if tag = cons_tag then
        (match data_v_to_list bt with
           SOME t -> SOME (CONS h t)
         | _ -> NONE)
      else NONE) /\
   (data_v_to_list _ = NONE)`;;

let data_v_to_list_ind = cake_ind "data_v_to_list";;

(* HOL4 overload bignum_limit[local], written out:                           *)
(*   bignum_limit i1 i2 s = let il = bignum_size s.limits.arch_64_bit i1 in  *)
(*                          let jl = bignum_size s.limits.arch_64_bit i2 in  *)
(*                            2 * il + 2 * jl                                *)

(* Gives an upper bound to the memory consuption of an operation *)

let space_consumed_def = sem1aux_def
  `(space_consumed (s:(C,FFI)data_state) (BlockOp (ConsExtend tag))
      (CONS (data_Block _ _ xs') (CONS (data_Number lower) (CONS (data_Number len)
        (CONS (data_Number tot) xs)))) =
      LENGTH (APPEND xs (TAKE (num_of_int len) (DROP (num_of_int lower) xs'))) + 1) /\
   (space_consumed s (MemOp RefArray) [data_Number len; _] = num_of_int len + 1) /\
   (space_consumed s (MemOp (RefByte _)) [data_Number len; _] =
      num_of_int len DIV (arch_size (data_state_limits s) DIV 8) + 2) /\
   (space_consumed s (BlockOp (FromList n)) [data_Number len; lv] =
      num_of_int len + 1) /\
   (space_consumed s (IntOp clos_Add) [data_Number i1; data_Number i2] =
      if small_num (limits_arch_64_bit (data_state_limits s)) i1 /\
         small_num (limits_arch_64_bit (data_state_limits s)) i2 /\
         small_num (limits_arch_64_bit (data_state_limits s)) (i1 + i2)
      then 0 else
        let il = bignum_size (limits_arch_64_bit (data_state_limits s)) i1 in
        let jl = bignum_size (limits_arch_64_bit (data_state_limits s)) i2 in
          2 * il + 2 * jl) /\
   (space_consumed s (IntOp clos_Sub) [data_Number i1; data_Number i2] =
      if small_num (limits_arch_64_bit (data_state_limits s)) i1 /\
         small_num (limits_arch_64_bit (data_state_limits s)) i2 /\
         small_num (limits_arch_64_bit (data_state_limits s)) (i1 - i2)
      then 0 else
        let il = bignum_size (limits_arch_64_bit (data_state_limits s)) i1 in
        let jl = bignum_size (limits_arch_64_bit (data_state_limits s)) i2 in
          2 * il + 2 * jl) /\
   (space_consumed s (IntOp Mult) [data_Number i1; data_Number i2] =
      if small_num (limits_arch_64_bit (data_state_limits s)) i1 /\ &0 <= i1 /\
         small_num (limits_arch_64_bit (data_state_limits s)) i2 /\ &0 <= i2 /\
         small_num (limits_arch_64_bit (data_state_limits s)) (i1 * i2)
      then 0 else
        let il = bignum_size (limits_arch_64_bit (data_state_limits s)) i1 in
        let jl = bignum_size (limits_arch_64_bit (data_state_limits s)) i2 in
          2 * il + 2 * jl) /\
   (space_consumed s (IntOp clos_Div) [data_Number i1; data_Number i2] =
      if small_num (limits_arch_64_bit (data_state_limits s)) i1 /\ &0 <= i1 /\
         small_num (limits_arch_64_bit (data_state_limits s)) i2 /\ &0 <= i2 /\
         small_num (limits_arch_64_bit (data_state_limits s)) (int_div i1 i2)
      then 0 else
        let il = bignum_size (limits_arch_64_bit (data_state_limits s)) i1 in
        let jl = bignum_size (limits_arch_64_bit (data_state_limits s)) i2 in
          2 * il + 2 * jl) /\
   (space_consumed s (IntOp clos_Mod) [data_Number i1; data_Number i2] =
      if small_num (limits_arch_64_bit (data_state_limits s)) i1 /\ &0 <= i1 /\
         small_num (limits_arch_64_bit (data_state_limits s)) i2 /\ &0 <= i2 /\
         small_num (limits_arch_64_bit (data_state_limits s)) (integer_int_mod i1 i2)
      then 0 else
        let il = bignum_size (limits_arch_64_bit (data_state_limits s)) i1 in
        let jl = bignum_size (limits_arch_64_bit (data_state_limits s)) i2 in
          2 * il + 2 * jl) /\
   (space_consumed s (BlockOp clos_ListAppend) [lv1; lv2] =
      match data_v_to_list lv1 with
        SOME l -> SUC (LENGTH l) * 3
      | NONE -> 0) /\
   (space_consumed s (op:clos_op) (vs:data_v list) = 0)`;;

let space_consumed_ind = CLOSSEMAUX_cases_ind space_consumed_def;;

let vb_size_def = cake_def
  `(vb_size (data_Block ts t ls) = 1 + t + SUM (MAP vb_size ls) + LENGTH ls) /\
   (vb_size _ = 1)`;;

let vs_depth_def = cake_def
  `(vs_depth (data_Block ts t ls) = vs_depth_list ls) /\
   (vs_depth _ = 0) /\
   (vs_depth_list [] = 0) /\
   (vs_depth_list (CONS x xs) = MAX (1 + vs_depth x) (vs_depth_list xs))`;;

let eq_code_stack_max_def = cake_def
  `eq_code_stack_max n (tsz:num spt) =
     OPTION_MAP (( * ) n)
       (OPTION_MAP2 MAX
          (lookup Equal_location tsz)
          (OPTION_MAP2 MAX
             (lookup Equal1_location tsz)
             (lookup Compare1_location tsz)))`;;

let stack_consumed_def = sem1aux_def
  `(stack_consumed (sfs:num spt) (lims:limits) (MemOp (CopyByte _)) (vs:data_v list) =
      OPTION_MAP2 MAX
        (lookup ByteCopy_location sfs)
        (OPTION_MAP2 MAX
           (lookup ByteCopyAdd_location sfs)
           (lookup ByteCopySub_location sfs))) /\
   (stack_consumed sfs lims (MemOp (RefByte _)) vs =
      OPTION_MAP2 MAX
        (lookup RefByte_location sfs)
        (lookup Replicate_location sfs)) /\
   (stack_consumed sfs lims (MemOp RefArray) vs =
      OPTION_MAP2 MAX
        (lookup RefArray_location sfs)
        (lookup Replicate_location sfs)) /\
   (stack_consumed sfs lims (MemOp XorByte) vs =
      lookup XorLoop_location sfs) /\
   (stack_consumed sfs lims (MemOp (StringCmp b cmp)) vs =
      lookup StringCmpLoop_location sfs) /\
   (stack_consumed sfs lims (BlockOp (ConsExtend _)) vs =
      lookup MemCopy_location sfs) /\
   (stack_consumed sfs lims (BlockOp (FromList _)) vs =
      OPTION_MAP2 MAX
        (lookup FromList_location sfs)
        (lookup FromList1_location sfs)) /\
   (stack_consumed sfs lims (BlockOp clos_ListAppend) vs =
      OPTION_MAP2 MAX
        (lookup Append_location sfs)
        (OPTION_MAP2 MAX
           (lookup AppendLenLoop_location sfs)
           (lookup AppendMainLoop_location sfs))) /\
   (stack_consumed sfs lims (IntOp clos_Div) [data_Number n1; data_Number n2] =
      if small_num (limits_arch_64_bit lims) n1 /\ &0 <= n1 /\
         small_num (limits_arch_64_bit lims) n2 /\ &0 <= n2 /\
         small_num (limits_arch_64_bit lims) (int_div n1 n2)
      then
        OPTION_MAP2 MAX
          (lookup LongDiv_location sfs)
          (lookup LongDiv1_location sfs)
      else
        OPTION_MAP2 MAX (lookup Div_location sfs)
          (max_depth sfs AnyArith_call_tree)) /\
   (stack_consumed sfs lims (IntOp clos_Mod) [data_Number n1; data_Number n2] =
      if small_num (limits_arch_64_bit lims) n1 /\ &0 <= n1 /\
         small_num (limits_arch_64_bit lims) n2 /\ &0 <= n2 /\
         small_num (limits_arch_64_bit lims) (integer_int_mod n1 n2)
      then
        OPTION_MAP2 MAX
          (lookup LongDiv_location sfs)
          (lookup LongDiv1_location sfs)
      else
        OPTION_MAP2 MAX (lookup Mod_location sfs)
          (max_depth sfs AnyArith_call_tree)) /\
   (stack_consumed sfs lims (IntOp Mult) [data_Number n1; data_Number n2] =
      if small_num (limits_arch_64_bit lims) n1 /\ &0 <= n1 /\
         small_num (limits_arch_64_bit lims) n2 /\ &0 <= n2 /\
         small_num (limits_arch_64_bit lims) (n1 * n2)
      then SOME 0 else
        OPTION_MAP2 MAX (lookup Mul_location sfs)
          (max_depth sfs AnyArith_call_tree)) /\
   (stack_consumed sfs lims (BlockOp clos_Equal) [v1; v2] =
      eq_code_stack_max (MIN (vs_depth v1 + 1) (vs_depth v2 + 1)) sfs) /\
   (stack_consumed sfs lims (IntOp clos_Sub) [data_Number n1; data_Number n2] =
      if small_num (limits_arch_64_bit lims) n1 /\
         small_num (limits_arch_64_bit lims) n2 /\
         small_num (limits_arch_64_bit lims) (n1 - n2)
      then SOME 0 else
        OPTION_MAP2 MAX (lookup Sub_location sfs)
          (max_depth sfs AnyArith_call_tree)) /\
   (stack_consumed sfs lims (IntOp clos_Add) [data_Number n1; data_Number n2] =
      if small_num (limits_arch_64_bit lims) n1 /\
         small_num (limits_arch_64_bit lims) n2 /\
         small_num (limits_arch_64_bit lims) (n1 + n2)
      then SOME 0 else
        OPTION_MAP2 MAX (lookup Add_location sfs)
          (max_depth sfs AnyArith_call_tree)) /\
   (stack_consumed sfs lims (IntOp LessEq) vs =
      OPTION_MAP2 MAX
        (lookup Compare_location sfs)
        (lookup Compare1_location sfs)) /\
   (stack_consumed sfs lims (IntOp clos_Less) vs =
      OPTION_MAP2 MAX
        (lookup Compare_location sfs)
        (lookup Compare1_location sfs)) /\
   (stack_consumed sfs lims p vs =
      if allowed_op p (LENGTH vs) then SOME 0 else NONE)`;;

let stack_consumed_ind = CLOSSEMAUX_cases_ind stack_consumed_def;;

(* HOL4 overloads do_space_safe and do_space_peak, written out:             *)
(*   do_space_safe op vs s =                                                 *)
(*     if op_space_reset op                                                  *)
(*     then s.safe_for_space /\ no_thunks_in_refs s.refs /\                  *)
(*          size_of_heap_args vs s + space_consumed s op vs                  *)
(*            <= s.limits.heap_limit                                         *)
(*     else s.safe_for_space                                                 *)
(*   do_space_peak op vs s =                                                 *)
(*     if op_space_reset op                                                  *)
(*     then MAX s.peak_heap_length                                           *)
(*              (size_of_heap_args vs s + space_consumed s op vs)            *)
(*     else s.peak_heap_length                                               *)

let do_space_def = cake_def
  `do_space op vs (s:(C,FFI)data_state) =
     if op_space_reset op
     then SOME (data_state_space_fupd (K 0)
                 (data_state_safe_for_space_fupd
                    (K (if op_space_reset op
                        then data_state_safe_for_space s /\
                             no_thunks_in_refs (data_state_refs s) /\
                             size_of_heap_args vs s + space_consumed s op vs
                               <= limits_heap_limit (data_state_limits s)
                        else data_state_safe_for_space s))
                    (data_state_peak_heap_length_fupd
                       (K (if op_space_reset op
                           then MAX (data_state_peak_heap_length s)
                                    (size_of_heap_args vs s + space_consumed s op vs)
                           else data_state_peak_heap_length s)) s)))
     else if op_space_req op (LENGTH vs) = 0 then SOME s
     else consume_space (op_space_req op (LENGTH vs)) s`;;

let size_of_stack_frame_def = cake_def
  `(size_of_stack_frame (data_Env n _) = n) /\
   (size_of_stack_frame (Exc n _ _) = OPTION_MAP ((+) 3) n)`;;

(* HOL4: size_of_stack = FOLDR (OPTION_MAP2 $+ o size_of_stack_frame)      *)
(*   (SOME 1), point-free; FOLDR f e l is ITLIST f l e                       *)

let size_of_stack_def = cake_def
  `size_of_stack (l:stack list) =
     ITLIST (OPTION_MAP2 (+) o size_of_stack_frame) l (SOME 1)`;;

let do_stack_def = cake_def
  `do_stack op vs (s:(C,FFI)data_state) =
     let new_stack =
       OPTION_MAP2 (+)
         (stack_consumed (data_state_stack_frame_sizes s) (data_state_limits s) op vs)
         (OPTION_MAP2 (+) (size_of_stack (data_state_stack s))
                          (data_state_locals_size s)) in
     data_state_safe_for_space_fupd
       (K (data_state_safe_for_space s /\
           the F (OPTION_MAP ((>) (limits_stack_limit (data_state_limits s)))
                             new_stack)))
       (data_state_stack_max_fupd
          (K (OPTION_MAP2 MAX (data_state_stack_max s) new_stack)) s)`;;

let data_v_to_bytes_def = cake_def
  `data_v_to_bytes lv = some ns:byte list.
     data_v_to_list lv = SOME (MAP (data_Number o int_of_num o val) ns)`;;

let data_v_to_words_def = cake_def
  `data_v_to_words lv = some ns:int64 list.
     data_v_to_list lv = SOME (MAP data_Word64 ns)`;;

let data_isClos_def = cake_def
  `data_isClos t1 (l1:A list) <=>
     (t1 = closure_tag \/ t1 = partial_app_tag) /\ ~(l1 = [])`;;

(* HOL4 infers the most general type: refs is a map to (A)bvl_ref *)

let data_do_eq_def = sem1aux_def_wf
  `inv_image (<)
     (\x:(((A)bvl_ref)spt # data_v # data_v) +
         (((A)bvl_ref)spt # data_v list # data_v list).
        sum_CASE x (\t. data_v_size (FST (SND t)))
                   (\t. list_size data_v_size (FST (SND t))))`
  SEM1AUX_TC_TAC
  (list_mk_conj
  [`data_do_eq (_:((A)bvl_ref)spt) (data_CodePtr _) (_:data_v) = Eq_type_error`;
   `data_do_eq (_:((A)bvl_ref)spt) (_:data_v) (data_CodePtr _) = Eq_type_error`;
   `data_do_eq (_:((A)bvl_ref)spt) (data_Number n1) (data_Number n2) =
      Eq_val (n1 = n2)`;
   `data_do_eq (_:((A)bvl_ref)spt) (data_Number _) (_:data_v) = Eq_type_error`;
   `data_do_eq (_:((A)bvl_ref)spt) (_:data_v) (data_Number _) = Eq_type_error`;
   `data_do_eq (_:((A)bvl_ref)spt) (data_Word64 w1) (data_Word64 w2) =
      Eq_val (w1 = w2)`;
   `data_do_eq (_:((A)bvl_ref)spt) (data_Word64 _) (_:data_v) = Eq_type_error`;
   `data_do_eq (_:((A)bvl_ref)spt) (_:data_v) (data_Word64 _) = Eq_type_error`;
   `data_do_eq (refs:((A)bvl_ref)spt) (data_RefPtr b1 n1) (data_RefPtr b2 n2) =
      if b1 /\ b2 then
        (match (lookup n1 refs, lookup n2 refs) with
           (SOME (bvl_ByteArray T bs1), SOME (bvl_ByteArray T bs2)) ->
             Eq_val (bs1 = bs2)
         | (SOME (bvl_ByteArray T bs1), _) -> Eq_type_error
         | (_, SOME (bvl_ByteArray T bs2)) -> Eq_type_error
         | _ -> Eq_val (n1 = n2))
      else Eq_type_error`;
   `data_do_eq (_:((A)bvl_ref)spt) (data_RefPtr _ _) (_:data_v) = Eq_type_error`;
   `data_do_eq (_:((A)bvl_ref)spt) (_:data_v) (data_RefPtr _ _) = Eq_type_error`;
   `data_do_eq (refs:((A)bvl_ref)spt) (data_Block _ t1 l1) (data_Block _ t2 l2) =
      if data_isClos t1 l1 \/ data_isClos t2 l2
      then if data_isClos t1 l1 /\ data_isClos t2 l2 then Eq_val T else Eq_type_error
      else if t1 = t2 /\ LENGTH l1 = LENGTH l2
           then data_do_eq_list refs l1 l2
           else Eq_val F`;
   `data_do_eq_list (_:((A)bvl_ref)spt) ([]:data_v list) ([]:data_v list) =
      Eq_val T`;
   `data_do_eq_list (refs:((A)bvl_ref)spt) (CONS (v1:data_v) vs1) (CONS (v2:data_v) vs2) =
      match data_do_eq refs v1 v2 with
        Eq_val T -> data_do_eq_list refs vs1 vs2
      | Eq_val F -> Eq_val F
      | bad -> bad`;
   `data_do_eq_list (_:((A)bvl_ref)spt) (_:data_v list) (_:data_v list) =
      Eq_val F`]);;
let _ = cake_add_simps [data_do_eq_def];;

let data_do_eq_ind = cake_ind "data_do_eq";;

(* HOL4: Overload Error[local] = Rerr (Rabort Rtype_error) (written out) *)

(* HOL4 infers the most general type: the exception type E is free *)
let data_do_install_def = cake_def
  `data_do_install vs (s:(C,FFI)data_state) =
     match vs with
       [v1; v2; vl1; vl2] ->
         (match (data_v_to_bytes v1, data_v_to_words v2) with
            (SOME bytes, SOME data) ->
              if ~(vl1 = data_Number (&(LENGTH bytes))) \/
                 ~(vl2 = data_Number (&(LENGTH data)))
              then Rerr (Rabort Rtype_error) else
              let (cfg,progs) = data_state_compile_oracle s 0 in
              let new_oracle = shift_seq 1 (data_state_compile_oracle s) in
                (match (data_state_compile s cfg progs, progs) with
                   (SOME (bytes',data',cfg'), CONS (k,prog) _) ->
                     if bytes = bytes' /\ data = data' /\ FST (new_oracle 0) = cfg' then
                       let s' =
                         data_state_safe_for_space_fupd (K F)
                           (data_state_code_fupd
                              (K (union (data_state_code s) (fromAList progs)))
                              (data_state_compile_oracle_fupd (K new_oracle) s))
                       in
                         Rval (data_CodePtr k, s')
                     else Rerr (Rabort Rtype_error)
                 | _ -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | _ -> (Rerr (Rabort Rtype_error):(data_v # (C,FFI)data_state,E)result)`;;

let data_list_to_v_def = cake_def
  `(data_list_to_v ts (t:data_v) [] = t) /\
   (data_list_to_v ts t (CONS h l) =
      data_Block ts cons_tag [h; data_list_to_v (ts + 1) t l])`;;

let with_fresh_ts_def = cake_def
  `with_fresh_ts (s:(C,FFI)data_state) n (f:num->(C,FFI)data_state->A) =
     match data_state_tstamps s with
       SOME ts -> f ts (data_state_tstamps_fupd (K (SOME (ts + n))) s)
     | NONE -> f 0 s`;;

let lim_safe_part_def = cake_def
  `(lim_safe_part lims (clos_Con tag xs) <=>
      if xs = []
      then tag < 2 EXP (arch_size lims) DIV 16
      else
        LENGTH xs < 2 EXP limits_length_limit lims /\
        LENGTH xs < 2 EXP (arch_size lims - 4) /\
        4 * tag < 2 EXP (arch_size lims) DIV 16 /\
        4 * tag < 2 EXP (arch_size lims - limits_length_limit lims - 2)) /\
   (lim_safe_part lims (clos_Int i) <=>
      (if small_num (limits_arch_64_bit lims) i
       then T else
         let il = bignum_size (limits_arch_64_bit lims) i in
           il <= 2 EXP limits_length_limit lims)) /\
   (lim_safe_part lims (clos_Str s) <=>
      (let i = strlen s in
         i DIV (arch_size lims DIV 8) < 2 EXP (arch_size lims) DIV arch_size lims /\
         i DIV (arch_size lims DIV 8) + 1 < 2 EXP limits_length_limit lims /\
         small_num (limits_arch_64_bit lims) (&i))) /\
   (lim_safe_part lims (clos_W64 w) <=> 1 < limits_length_limit lims)`;;
let _ = cake_add_simps [lim_safe_part_def];;

(* the clause for MutCons is parsed separately (its i is a num, the i of  *)
(* other clauses an int; HOL4 types each clause on its own)                *)

let lim_safe_def = sem1aux_def (list_mk_conj
  [`(lim_safe lims (BlockOp (clos_Cons tag)) (xs:data_v list) <=>
      if xs = []
      then tag < 2 EXP (arch_size lims) DIV 16
      else
        LENGTH xs < 2 EXP limits_length_limit lims /\
        LENGTH xs < 2 EXP (arch_size lims - 4) /\
        4 * tag < 2 EXP (arch_size lims) DIV 16 /\
        4 * tag < 2 EXP (arch_size lims - limits_length_limit lims - 2))`;
   `(lim_safe (lims:limits) (MemOp (MutCons tag i)) (xs:data_v list) <=>
      (LENGTH xs < 2 EXP limits_length_limit lims /\
       LENGTH xs < 2 EXP (arch_size lims - 4) /\
       4 * tag < 2 EXP (arch_size lims) DIV 16 /\
       4 * tag < 2 EXP (arch_size lims - limits_length_limit lims - 2)))`;
   `(lim_safe lims (BlockOp (FromList tag)) (xs:data_v list) <=>
      (match xs with
         [len; lv] ->
           (match data_v_to_list lv with
              SOME n ->
                if len = data_Number (&(LENGTH n))
                then small_num (limits_arch_64_bit lims) (&(LENGTH n)) /\
                     LENGTH n < 2 EXP limits_length_limit lims /\
                     LENGTH n < arch_size lims DIV 16 /\
                     4 * tag < 2 EXP (arch_size lims - limits_length_limit lims - 2) /\
                     4 * tag < 2 EXP (arch_size lims) DIV 16
                else T
            | _ -> T)
       | _ -> T)) /\
   (lim_safe lims (BlockOp clos_ListAppend) [x1; x2] <=>
      (match (data_v_to_list x1, data_v_to_list x2) with
         (SOME xs, SOME ys) ->
           1 < limits_length_limit lims /\
           3 * SUC (LENGTH xs) < 2 EXP (arch_size lims) DIV 8
       | _ -> T)) /\
   (lim_safe lims (BlockOp (ConsExtend tag))
      (CONS (data_Block _ _ xs') (CONS (data_Number lower) (CONS (data_Number len)
        (CONS (data_Number tot) xs)))) <=>
      if lower < &0 \/ len < &0 \/ lower + len > &(LENGTH xs') \/
         tot = &0 \/ ~(tot = &(LENGTH xs) + len) then T
      else LENGTH (APPEND xs (TAKE (num_of_int len) (DROP (num_of_int lower) xs')))
             < 2 EXP limits_length_limit lims /\
           LENGTH (APPEND xs (TAKE (num_of_int len) (DROP (num_of_int lower) xs')))
             < 2 EXP (arch_size lims) DIV 16 /\
           4 * tag < 2 EXP (arch_size lims) DIV 16 /\
           4 * tag < 2 EXP (arch_size lims - limits_length_limit lims - 2)) /\
   (lim_safe lims (IntOp clos_Add) [data_Number i1; data_Number i2] <=>
      (if small_num (limits_arch_64_bit lims) i1 /\
          small_num (limits_arch_64_bit lims) i2 /\
          small_num (limits_arch_64_bit lims) (i1 + i2)
       then T else
         let il = bignum_size (limits_arch_64_bit lims) i1 in
         let jl = bignum_size (limits_arch_64_bit lims) i2 in
           il + jl <= 2 EXP limits_length_limit lims)) /\
   (lim_safe lims (IntOp clos_Sub) [data_Number i1; data_Number i2] <=>
      (if small_num (limits_arch_64_bit lims) i1 /\
          small_num (limits_arch_64_bit lims) i2 /\
          small_num (limits_arch_64_bit lims) (i1 - i2)
       then T else
         let il = bignum_size (limits_arch_64_bit lims) i1 in
         let jl = bignum_size (limits_arch_64_bit lims) i2 in
           il + jl <= 2 EXP limits_length_limit lims)) /\
   (lim_safe lims (IntOp Mult) [data_Number i1; data_Number i2] <=>
      (if small_num (limits_arch_64_bit lims) i1 /\ &0 <= i1 /\
          small_num (limits_arch_64_bit lims) i2 /\ &0 <= i2 /\
          small_num (limits_arch_64_bit lims) (i1 * i2)
       then T else
         let il = bignum_size (limits_arch_64_bit lims) i1 in
         let jl = bignum_size (limits_arch_64_bit lims) i2 in
           il + jl <= 2 EXP limits_length_limit lims)) /\
   (lim_safe lims (IntOp clos_Div) [data_Number i1; data_Number i2] <=>
      (if small_num (limits_arch_64_bit lims) i1 /\ &0 <= i1 /\
          small_num (limits_arch_64_bit lims) i2 /\ &0 <= i2 /\
          small_num (limits_arch_64_bit lims) (int_div i1 i2)
       then T else
         let il = bignum_size (limits_arch_64_bit lims) i1 in
         let jl = bignum_size (limits_arch_64_bit lims) i2 in
           il + jl <= 2 EXP limits_length_limit lims)) /\
   (lim_safe lims (IntOp clos_Mod) [data_Number i1; data_Number i2] <=>
      (if small_num (limits_arch_64_bit lims) i1 /\ &0 <= i1 /\
          small_num (limits_arch_64_bit lims) i2 /\ &0 <= i2 /\
          small_num (limits_arch_64_bit lims) (integer_int_mod i1 i2)
       then T else
         let il = bignum_size (limits_arch_64_bit lims) i1 in
         let jl = bignum_size (limits_arch_64_bit lims) i2 in
           il + jl <= 2 EXP limits_length_limit lims)) /\
   (lim_safe lims (MemOp RefArray) [data_Number i; v] <=>
      (&0 <= i /\
       num_of_int i < 2 EXP (arch_size lims) DIV 16 /\
       num_of_int i < 2 EXP limits_length_limit lims)) /\
   (lim_safe lims (MemOp (RefByte _)) (CONS (data_Number i) xs) <=>
      (&0 <= i /\
       num_of_int i DIV (arch_size lims DIV 8) < 2 EXP (arch_size lims) DIV arch_size lims /\
       num_of_int i DIV (arch_size lims DIV 8) + 1 < 2 EXP limits_length_limit lims /\
       small_num (limits_arch_64_bit lims) i)) /\
   (lim_safe lims (MemOp clos_Ref) xs <=>
      (LENGTH xs < 2 EXP limits_length_limit lims /\
       LENGTH xs < 2 EXP arch_size lims DIV 16)) /\
   (lim_safe lims (BlockOp (Build parts1)) _ <=>
      ALL (lim_safe_part lims) parts1) /\
   (lim_safe lims (WordOp WordToInt) _ <=> 1 < limits_length_limit lims) /\
   (lim_safe lims (WordOp WordFromInt) _ <=> 1 < limits_length_limit lims) /\
   (lim_safe lims (WordOp (WordOpw W64 _)) _ <=> 1 < limits_length_limit lims) /\
   (lim_safe lims (WordOp (WordShift W64 _ _)) _ <=> 1 < limits_length_limit lims) /\
   (lim_safe lims (WordOp (WordFromWord _)) _ <=> 1 < limits_length_limit lims) /\
   (lim_safe lims (WordOp (FP_cmp _)) _ <=> limits_has_fp_ops lims) /\
   (lim_safe lims (WordOp (FP_uop _)) _ <=>
      (limits_has_fp_ops lims /\
       (limits_arch_64_bit lims \/ 1 < limits_length_limit lims))) /\
   (lim_safe lims (WordOp (FP_bop _)) _ <=>
      (limits_has_fp_ops lims /\
       (limits_arch_64_bit lims \/ 1 < limits_length_limit lims))) /\
   (lim_safe lims (WordOp (FP_top _)) _ <=>
      (limits_has_fp_ops lims /\ limits_has_fp_tops lims /\
       (limits_arch_64_bit lims \/ 1 < limits_length_limit lims))) /\
   (lim_safe lims _ _ <=> T)`]);;
let _ = cake_add_simps [lim_safe_def];;

let lim_safe_ind = CLOSSEMAUX_cases_ind lim_safe_def;;

let do_lim_safe = cake_def
  `do_lim_safe (s:(C,FFI)data_state) op vs =
     data_state_safe_for_space_fupd
       (K (lim_safe (data_state_limits s) op vs /\ data_state_safe_for_space s)) s`;;
let _ = cake_add_simps [do_lim_safe];;

let check_lim_def = cake_def
  `check_lim (s:(C,FFI)data_state) n =
     data_state_safe_for_space_fupd
       (K (n < 2 EXP limits_length_limit (data_state_limits s) /\
           data_state_safe_for_space s)) s`;;

(* HOL4 infers the most general type: s is a map to (A)bvl_ref *)
(* the clauses are parsed separately (t is a num in the Con clause and a  *)
(* string in the Str clause; HOL4 types each clause on its own)           *)

let data_do_part_def = cake_def_clauses
  [`data_do_part (m:num->data_v) (clos_Int i) (s:((A)bvl_ref)spt)
                 (ts:num option) = (data_Number i,s,ts)`;
   `data_do_part (m:num->data_v) (clos_W64 w) (s:((A)bvl_ref)spt)
                 (ts:num option) = (data_Word64 w,s,ts)`;
   `data_do_part (m:num->data_v) (clos_Con t ns) (s:((A)bvl_ref)spt)
                 (ts:num option) =
      (if ns = [] then (data_Block 0 t [],s,ts)
       else match ts with
              NONE -> (data_Block 0 t (MAP m ns),s,ts)
            | SOME n -> (data_Block n t (MAP m ns),s,SOME (n + 1)))`;
   `data_do_part (m:num->data_v) (clos_Str t) (s:((A)bvl_ref)spt)
                 (ts:num option) =
      let ptr = (minimal ptr. ~(ptr IN domain s)) in
      let bytes = MAP (word o ORD) (explode t) in
        (data_RefPtr T ptr,insert ptr (bvl_ByteArray T bytes) s,ts)`];;

let data_do_build_def = cake_def
  `(data_do_build (m:num->data_v) i [] (s:((A)bvl_ref)spt) (ts:num option) =
      (m (i - 1),s,ts)) /\
   (data_do_build m i (CONS p rest) s ts =
      let (x,s1,ts1) = data_do_part m p s ts in
        data_do_build ((i =+ x) m) (i + 1) rest s1 ts1)`;;

let data_do_build_const_def = cake_def
  `data_do_build_const xs (s:((A)bvl_ref)spt) (ts:num option) =
     data_do_build (\x. data_Number (&0)) 0 xs s ts`;;

let data_do_int_app_def = sem1aux_def (list_mk_conj
  [`data_do_int_app (clos_Const n) ([]:data_v list) =
      (if small_enough_int n then SOME (data_Number n) else NONE)`;
   `data_do_int_app clos_Add [data_Number n1; data_Number n2] =
      SOME (data_Number (n1 + n2))`;
   `data_do_int_app clos_Sub [data_Number n1; data_Number n2] =
      SOME (data_Number (n1 - n2))`;
   `data_do_int_app Mult [data_Number n1; data_Number n2] =
      SOME (data_Number (n1 * n2))`;
   `data_do_int_app clos_Div [data_Number n1; data_Number n2] =
      (if n2 = &0 then NONE else SOME (data_Number (int_div n1 n2)))`;
   `data_do_int_app clos_Mod [data_Number n1; data_Number n2] =
      (if n2 = &0 then NONE else SOME (data_Number (integer_int_mod n1 n2)))`;
   `data_do_int_app clos_Less [data_Number n1; data_Number n2] =
      SOME (data_Boolv (n1 < n2))`;
   `data_do_int_app LessEq [data_Number n1; data_Number n2] =
      SOME (data_Boolv (n1 <= n2))`;
   `data_do_int_app Greater [data_Number n1; data_Number n2] =
      SOME (data_Boolv (n1 > n2))`;
   `data_do_int_app GreaterEq [data_Number n1; data_Number n2] =
      SOME (data_Boolv (n1 >= n2))`;
   `data_do_int_app (LessConstSmall n) [data_Number i] =
      (if &0 <= i /\ i <= &1000000 /\ n < 1000000 then
         SOME (data_Boolv (i < &n)) else NONE)`;
   `data_do_int_app (op:int_op) (vs:data_v list) = (NONE:data_v option)`]);;

(* HOL4's clauses for WordFromWord T and WordFromWord F (literal patterns)  *)
(* are written with WordFromWord b and a condition (the kit does not        *)
(* complete clauses with literal patterns), as bvlSem does                  *)

let data_do_word_app_def = sem1aux_def (list_mk_conj
  [`data_do_word_app (WordOpw W8 opw) [data_Number n1; data_Number n2] =
      (match some (w1:byte,w2:byte). n1 = &(val w1) /\ n2 = &(val w2) with
         NONE -> NONE
       | SOME (w1,w2) -> SOME (data_Number (&(val (opw_lookup opw w1 w2)))))`;
   `data_do_word_app (WordOpw W64 opw) [data_Word64 w1; data_Word64 w2] =
      SOME (data_Word64 (opw_lookup opw w1 w2))`;
   `data_do_word_app (WordTest W8 test) [data_Number n1; data_Number n2] =
      (if &0 <= n1 /\ n1 < &256 /\ &0 <= n2 /\ n2 < &256 then
         (match test with
            Equal -> SOME (data_Boolv (n1 = n2))
          | Compare Lt -> SOME (data_Boolv (n1 < n2))
          | Compare Leq -> SOME (data_Boolv (n1 <= n2))
          | _ -> NONE)
       else NONE)`;
   `data_do_word_app (WordShift W8 sh n) [data_Number i] =
      (match some (w:byte). i = &(val w) with
         NONE -> NONE
       | SOME w -> SOME (data_Number (&(val (shift_lookup sh w n)))))`;
   `data_do_word_app (WordShift W64 sh n) [data_Word64 w] =
      SOME (data_Word64 (shift_lookup sh w n))`;
   `data_do_word_app WordFromInt [data_Number i] =
      SOME (data_Word64 (iword i))`;
   `data_do_word_app WordToInt [data_Word64 w] =
      SOME (data_Number (&(val w)))`;
   `data_do_word_app (WordFromWord b) [data_Word64 w] =
      if b then SOME (data_Number (&(val ((word_zx:int64->byte) w))))
      else NONE`;
   `data_do_word_app (WordFromWord b) [data_Number n] =
      if b then NONE else
      (match some (w:byte). n = &(val w) with
         NONE -> NONE
       | SOME w -> SOME (data_Word64 (word_zx w)))`;
   `data_do_word_app (FP_top t_op) ws =
      (match ws with
         [data_Word64 w1; data_Word64 w2; data_Word64 w3] ->
           SOME (data_Word64 (fp_top_comp t_op w1 w2 w3))
       | _ -> NONE)`;
   `data_do_word_app (FP_bop bop) ws =
      (match ws with
         [data_Word64 w1; data_Word64 w2] ->
           SOME (data_Word64 (fp_bop_comp bop w1 w2))
       | _ -> NONE)`;
   `data_do_word_app (FP_uop uop) ws =
      (match ws with
         [data_Word64 w] -> SOME (data_Word64 (fp_uop_comp uop w))
       | _ -> NONE)`;
   `data_do_word_app (FP_cmp cmp) ws =
      (match ws with
         [data_Word64 w1; data_Word64 w2] ->
           SOME (data_Boolv (fp_cmp_comp cmp w1 w2))
       | _ -> NONE)`;
   `data_do_word_app (op:word_op) (vs:data_v list) = (NONE:data_v option)`]);;

let dest_Boolv_def = cake_def
  `(dest_Boolv (data_Block _ tag xs) =
      (if xs = [] /\ tag < 2 then SOME (tag = 1) else NONE)) /\
   (dest_Boolv _ = NONE)`;;

let data_dest_thunk_ret_INDUCT,data_dest_thunk_ret_RECURSION = cake_type
  "data_dest_thunk_ret = data_BadRef
                       | data_NotThunk
                       | data_IsThunk thunk_mode data_v";;

let data_dest_thunk_def = sem1aux_def
  `(data_dest_thunk (data_RefPtr b ptr) (refs:((data_v)bvl_ref)spt) =
      match lookup ptr refs with
        NONE -> data_BadRef
      | SOME (bvl_Thunk Evaluated v) ->
          if b then data_BadRef else data_IsThunk Evaluated v
      | SOME (bvl_Thunk NotEvaluated v) ->
          if b then data_BadRef else data_IsThunk NotEvaluated v
      | SOME _ -> data_NotThunk) /\
   (data_dest_thunk _ refs = data_NotThunk)`;;

let data_bad_thunk_update_def = cake_def
  `data_bad_thunk_update m v (refs:((data_v)bvl_ref)spt) <=>
     m = Evaluated /\ ~(data_dest_thunk v refs = data_NotThunk)`;;

(* mirrors bviSem's finalise_cons, but threads the timestamp counter so    *)
(* that each block produced by the finalisation gets a fresh time stamp    *)

let data_finalise_cons_def = cake_def_wf
  `measure ((size:((data_v)bvl_ref)spt->num) o FST o
            (SND:data_v # ((data_v)bvl_ref)spt # num option ->
                 ((data_v)bvl_ref)spt # num option))`
  (REWRITE_TAC[measure_THM; o_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
   RVEQ_TAC THEN ASM_REWRITE_TAC[size_delete; option_DISTINCT] THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP lookup_zero) THEN ASM_ARITH_TAC)
  `(data_finalise_cons (data_RefPtr b ptr) (refs:((data_v)bvl_ref)spt)
                       (ts:num option) =
      match lookup ptr refs with
        SOME (MutBlock tag finalised l c r) ->
          if ~finalised then
            (match data_finalise_cons c (delete ptr refs) ts with
               SOME (c',refs',ts') ->
                 SOME (data_Block (match ts' with NONE -> 0 | SOME n -> n) tag
                         (APPEND (APPEND l [c']) r),
                       insert ptr (MutBlock tag T l c r) refs',
                       OPTION_MAP SUC ts')
             | NONE -> NONE)
          else NONE
      | SOME res -> SOME (data_RefPtr b ptr,refs,ts)
      | NONE -> NONE) /\
   (data_finalise_cons v refs ts = SOME (v,refs,ts))`;;

let data_finalise_cons_ind = cake_ind "data_finalise_cons";;

(* bvi part first, then the bvl part (from Build on) *)
let data_do_app_aux_def = cake_def
  `data_do_app_aux (op:clos_op) (vs:data_v list) (s:(C,FFI)data_state) =
     match (op,vs) with
       (clos_Label l,xs) ->
         (match xs with
            [] -> if l IN domain (data_state_code s) then
                    Rval (data_CodePtr l, s)
                  else Rerr (Rabort Rtype_error)
          | _ -> Rerr (Rabort Rtype_error))
     | (GlobOp GlobalsPtr,xs) ->
         (match xs with
            [] -> (match data_state_global s with
                     SOME p -> Rval (data_RefPtr T p, s)
                   | NONE -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (GlobOp (clos_Global n),xs) ->
         (match xs with
            [] -> (match data_state_global s with
                     SOME ptr ->
                       (match lookup ptr (data_state_refs s) with
                          SOME (bvl_ValueArray xs) ->
                            (if n < LENGTH xs
                             then Rval (EL n xs, s)
                             else Rerr (Rabort Rtype_error))
                        | _ -> Rerr (Rabort Rtype_error))
                   | NONE -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (GlobOp (SetGlobal n),xs) ->
         (match xs with
            [x] -> (match data_state_global s with
                      SOME ptr ->
                        (match lookup ptr (data_state_refs s) with
                           SOME (bvl_ValueArray xs) ->
                             (if n < LENGTH xs
                              then Rval (data_Unit, data_state_refs_fupd (K (insert ptr
                                     (bvl_ValueArray (LUPDATE x n xs)) (data_state_refs s))) s)
                              else Rerr (Rabort Rtype_error))
                         | _ -> Rerr (Rabort Rtype_error))
                    | NONE -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (GlobOp SetGlobalsPtr,xs) ->
         (match xs with
            [data_RefPtr T p] -> Rval (data_Unit, data_state_global_fupd (K (SOME p)) s)
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp (FromList n), xs) ->
         (match xs with
            [len; lv] ->
              (match data_v_to_list lv with
                 SOME [] -> if len = data_Number (&0)
                            then Rval (data_Block 0 n [],s)
                            else Rerr (Rabort Rtype_error)
               | SOME vs -> if len = data_Number (&(LENGTH vs))
                            then with_fresh_ts s 1
                              (\ts s'. Rval (data_Block ts n vs,
                                             check_lim s' (LENGTH vs)))
                            else Rerr (Rabort Rtype_error)
               | _ -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp (RefByte f), xs) ->
         (match xs with
            [data_Number i; data_Number b] ->
              if &0 <= i /\ (?w:byte. b = &(val w)) then
                let ptr = (minimal ptr. ~(ptr IN domain (data_state_refs s))) in
                  Rval (data_RefPtr T ptr, data_state_refs_fupd (K (insert ptr
                    (bvl_ByteArray f (REPLICATE (num_of_int i) (iword b)))
                    (data_state_refs s))) s)
              else Rerr (Rabort Rtype_error)
          | _ -> Rerr (Rabort Rtype_error))
     | (GlobOp AllocGlobal, _) -> Rerr (Rabort Rtype_error)
     | (MemOp FromListByte, _) -> Rerr (Rabort Rtype_error)
     | (MemOp ConcatByteVec, _) -> Rerr (Rabort Rtype_error)
     | (MemOp (CopyByte T), _) -> Rerr (Rabort Rtype_error)
     | (BlockOp (Build parts1),[]) ->
         (match data_do_build_const parts1 (data_state_refs s) (data_state_tstamps s) with
            (v,s1,ts1) -> Rval (v,data_state_refs_fupd (K s1)
                                    (data_state_tstamps_fupd (K ts1) s)))
     | (BlockOp (clos_Cons tag),xs) ->
         (if xs = []
          then Rval (data_Block 0 tag [],s)
          else with_fresh_ts s 1
                 (\ts s'. Rval (data_Block ts tag xs, check_lim s' (LENGTH xs))))
     | (BlockOp (ConsExtend tag),
        CONS (data_Block x y xs') (CONS (data_Number lower) (CONS (data_Number len)
          (CONS (data_Number tot) xs)))) ->
         if lower < &0 \/ len < &0 \/ lower + len > &(LENGTH xs') \/
            tot = &0 \/ ~(tot = &(LENGTH xs) + len) then
           Rerr (Rabort Rtype_error)
         else with_fresh_ts s 1
                (\ts s'.
                   let l = APPEND xs (TAKE (num_of_int len) (DROP (num_of_int lower) xs'))
                   in Rval (data_Block ts tag l, check_lim s' (LENGTH l)))
     | (BlockOp (ConsExtend tag),_) -> Rerr (Rabort Rtype_error)
     | (MemOp clos_El,[data_Block _ tag xs; data_Number i]) ->
         if &0 <= i /\ num_of_int i < LENGTH xs then Rval (EL (num_of_int i) xs, s)
         else Rerr (Rabort Rtype_error)
     | (MemOp clos_El,[data_RefPtr _ ptr; data_Number i]) ->
         (match lookup ptr (data_state_refs s) with
            SOME (bvl_ValueArray xs) ->
              (if &0 <= i /\ i < &(LENGTH xs)
               then Rval (EL (num_of_int i) xs, s)
               else Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp (ElemAt n),[data_Block _ tag xs]) ->
         if n < LENGTH xs then Rval (EL n xs, s) else Rerr (Rabort Rtype_error)
     | (BlockOp (ElemAt n),[data_RefPtr _ ptr]) ->
         (match lookup ptr (data_state_refs s) with
            SOME (bvl_ValueArray xs) ->
              (if n < LENGTH xs
               then Rval (EL n xs, s)
               else Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp (BoolTest test),[v1; v2]) ->
         (match (dest_Boolv v1, dest_Boolv v2) with
            (SOME b1, SOME b2) -> Rval (data_Boolv (b1 = b2), s)
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp BoolNot,[v1]) ->
         (match dest_Boolv v1 with
            SOME b1 -> Rval (data_Boolv (~b1), s)
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp clos_ListAppend,[x1; x2]) ->
         (match (data_v_to_list x1, data_v_to_list x2) with
            (SOME xs, SOME ys) ->
              with_fresh_ts s (LENGTH xs)
                (\ts s'. Rval (data_list_to_v ts x2 xs, check_lim s' 2))
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp LengthBlock,[data_Block _ tag xs]) ->
         Rval (data_Number (&(LENGTH xs)), s)
     | (MemOp Length,[data_RefPtr _ ptr]) ->
         (match lookup ptr (data_state_refs s) with
            SOME (bvl_ValueArray xs) -> Rval (data_Number (&(LENGTH xs)), s)
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp LengthByte,[data_RefPtr _ ptr]) ->
         (match lookup ptr (data_state_refs s) with
            SOME (bvl_ByteArray _ xs) -> Rval (data_Number (&(LENGTH xs)), s)
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp RefArray,[data_Number i; v]) ->
         if &0 <= i then
           let ptr = (minimal ptr. ~(ptr IN domain (data_state_refs s))) in
             Rval (data_RefPtr T ptr, data_state_refs_fupd (K (insert ptr
                     (bvl_ValueArray (REPLICATE (num_of_int i) v)) (data_state_refs s))) s)
         else Rerr (Rabort Rtype_error)
     | (MemOp DerefByte,[data_RefPtr _ ptr; data_Number i]) ->
         (match lookup ptr (data_state_refs s) with
            SOME (bvl_ByteArray _ ws) ->
              (if &0 <= i /\ i < &(LENGTH ws)
               then Rval (data_Number (&(val (EL (num_of_int i) ws))),s)
               else Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp UpdateByte,[data_RefPtr _ ptr; data_Number i; data_Number b]) ->
         (match lookup ptr (data_state_refs s) with
            SOME (bvl_ByteArray f bs) ->
              (if &0 <= i /\ i < &(LENGTH bs) /\ (?w:byte. b = &(val w))
               then
                 Rval (data_Unit, data_state_refs_fupd (K (insert ptr
                   (bvl_ByteArray f (LUPDATE (iword b) (num_of_int i) bs))
                   (data_state_refs s))) s)
               else Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp XorByte,[data_RefPtr _ dst; data_RefPtr _ src]) ->
         (match (lookup src (data_state_refs s), lookup dst (data_state_refs s)) with
            (SOME (bvl_ByteArray _ ws), SOME (bvl_ByteArray f ds)) ->
              (match xor_bytes ws ds with
                 SOME ds1 -> Rval (data_Unit, data_state_refs_fupd (K (insert dst
                               (bvl_ByteArray f ds1) (data_state_refs s))) s)
               | NONE -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp (StringCmp b cmp),[data_RefPtr _ s1; data_RefPtr _ s2]) ->
         (match (lookup s1 (data_state_refs s), lookup s2 (data_state_refs s)) with
            (SOME (bvl_ByteArray _ ws1), SOME (bvl_ByteArray _ ws2)) ->
              (let s1 = implode (MAP (CHR o val) ws1) in
               let s2 = implode (MAP (CHR o val) ws2) in
                 Rval (data_Boolv (str_cmp b cmp s1 s2), s))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp (CopyByte F),[data_RefPtr _ src; data_Number srcoff; data_Number len;
                            data_RefPtr _ dst; data_Number dstoff]) ->
         (match (lookup src (data_state_refs s), lookup dst (data_state_refs s)) with
            (SOME (bvl_ByteArray _ ws), SOME (bvl_ByteArray fl ds)) ->
              (match copy_array (ws,srcoff) len (SOME (ds,dstoff)) with
                 SOME ds -> Rval (data_Unit, data_state_refs_fupd (K (insert dst
                              (bvl_ByteArray fl ds) (data_state_refs s))) s)
               | NONE -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp (TagEq n),[data_Block _ tag xs]) ->
         Rval (data_Boolv (tag = n), s)
     | (BlockOp (clos_LenEq l),[data_Block _ tag xs]) ->
         Rval (data_Boolv (LENGTH xs = l),s)
     | (BlockOp (clos_TagLenEq n l),[data_Block _ tag xs]) ->
         Rval (data_Boolv (tag = n /\ LENGTH xs = l),s)
     | (BlockOp (EqualConst p),[x1]) ->
         (match p with
            clos_Int i ->
              (match x1 with
                 data_Number j -> Rval (data_Boolv (i = j), s)
               | _ -> Rerr (Rabort Rtype_error))
          | clos_W64 i ->
              (match x1 with
                 data_Word64 j -> Rval (data_Boolv (i = j), s)
               | _ -> Rerr (Rabort Rtype_error))
          | clos_Str i ->
              (match x1 with
                 data_RefPtr _ p ->
                   (match lookup p (data_state_refs s) with
                      SOME (bvl_ByteArray T j) ->
                        Rval (data_Boolv (j = MAP (word o ORD) (explode i)), s)
                    | _ -> Rerr (Rabort Rtype_error))
               | _ -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp clos_Equal,[x1; x2]) ->
         (match data_do_eq (data_state_refs s) x1 x2 with
            Eq_val b -> Rval (data_Boolv b, s)
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp clos_Ref,xs) ->
         let ptr = (minimal ptr. ~(ptr IN domain (data_state_refs s))) in
           Rval (data_RefPtr T ptr, data_state_refs_fupd (K (insert ptr
                   (bvl_ValueArray xs) (data_state_refs s))) s)
     | (MemOp Update,[data_RefPtr _ ptr; data_Number i; x]) ->
         (match lookup ptr (data_state_refs s) with
            SOME (bvl_ValueArray xs) ->
              (if &0 <= i /\ i < &(LENGTH xs)
               then Rval (data_Unit, data_state_refs_fupd (K (insert ptr
                           (bvl_ValueArray (LUPDATE x (num_of_int i) xs))
                           (data_state_refs s))) s)
               else Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp (MutCons tag i),xs) ->
         (let ptr = (minimal ptr. ~(ptr IN domain (data_state_refs s))) in
            if i >= LENGTH xs then Rerr (Rabort Rtype_error) else
              let l = TAKE i xs in
              let c = EL i xs in
              let r = DROP (i + 1) xs in
                Rval (data_RefPtr F ptr,
                      data_state_refs_fupd (K (insert ptr (MutBlock tag F l c r)
                                                 (data_state_refs s))) s))
     | (MemOp UpdateCons,[data_RefPtr _ ptr; data_Number i; x]) ->
         (match lookup ptr (data_state_refs s) with
            SOME (MutBlock tag finalised l c r) ->
              if ~(i = &(LENGTH l)) \/ finalised then Rerr (Rabort Rtype_error) else
                Rval (data_Unit, data_state_refs_fupd (K (insert ptr
                        (MutBlock tag F l x r) (data_state_refs s))) s)
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp FinaliseCons,[x]) ->
         (match data_finalise_cons x (data_state_refs s) (data_state_tstamps s) with
            SOME (v,refs',ts') ->
              Rval (v, data_state_refs_fupd (K refs') (data_state_tstamps_fupd (K ts') s))
          | NONE -> Rerr (Rabort Rtype_error))
     | (IntOp intop, vs) ->
         (match data_do_int_app intop vs with
            SOME res -> Rval (res,s)
          | _ -> Rerr (Rabort Rtype_error))
     | (WordOp wordop, vs) ->
         (match data_do_word_app wordop vs with
            SOME res -> Rval (res,s)
          | _ -> Rerr (Rabort Rtype_error))
     | (clos_FFI n, [data_RefPtr _ cptr; data_RefPtr _ ptr]) ->
         (match (lookup cptr (data_state_refs s), lookup ptr (data_state_refs s)) with
            (SOME (bvl_ByteArray T cws), SOME (bvl_ByteArray F ws)) ->
              (match call_FFI (data_state_ffi s) (ExtCall n) cws ws with
                 FFI_return ffi' ws' ->
                   Rval (data_Unit,
                         data_state_refs_fupd (K (insert ptr (bvl_ByteArray F ws')
                                                    (data_state_refs s)))
                           (data_state_ffi_fupd (K ffi') s))
               | FFI_final outcome ->
                   Rerr (Rabort (Rffi_error outcome)))
          | _ -> Rerr (Rabort Rtype_error))
     | (BlockOp BoundsCheckBlock,xs) ->
         (match xs with
            [data_Block _ tag ys; data_Number i] ->
              Rval (data_Boolv (&0 <= i /\ i < &(LENGTH ys)),s)
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp (BoundsCheckByte loose),xs) ->
         (match xs with
            [data_RefPtr _ ptr; data_Number i] ->
              (match lookup ptr (data_state_refs s) with
                 SOME (bvl_ByteArray _ ws) ->
                   Rval (data_Boolv (&0 <= i /\
                                     (if loose then (<=) else (<)) i (&(LENGTH ws))),s)
               | _ -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp BoundsCheckArray,xs) ->
         (match xs with
            [data_RefPtr _ ptr; data_Number i] ->
              (match lookup ptr (data_state_refs s) with
                 SOME (bvl_ValueArray ws) ->
                   Rval (data_Boolv (&0 <= i /\ i < &(LENGTH ws)),s)
               | _ -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | (MemOp clos_ConfigGC,[data_Number _; data_Number _]) -> (Rval (data_Unit, s))
     | (clos_ThunkOp th_op,vs) ->
         (match (th_op,vs) with
            (AllocThunk m, [v]) ->
              (if data_bad_thunk_update m v (data_state_refs s) then
                 Rerr (Rabort Rtype_error) else
               let ptr = (minimal ptr. ~(ptr IN domain (data_state_refs s))) in
                 Rval (data_RefPtr F ptr, data_state_refs_fupd (K (insert ptr
                         (bvl_Thunk m v) (data_state_refs s))) s))
          | (UpdateThunk m, [data_RefPtr F ptr; v]) ->
              (if data_bad_thunk_update m v (data_state_refs s) then
                 Rerr (Rabort Rtype_error) else
               match lookup ptr (data_state_refs s) with
                 SOME (bvl_Thunk NotEvaluated _) ->
                   Rval (data_Unit, data_state_refs_fupd (K (insert ptr
                           (bvl_Thunk m v) (data_state_refs s))) s)
               | _ -> Rerr (Rabort Rtype_error))
          | _ -> Rerr (Rabort Rtype_error))
     | _ -> (Rerr (Rabort Rtype_error):(data_v # (C,FFI)data_state,data_v)result)`;;

(* HOL4 overloads do_app_safe and do_app_peak are not used here *)

let data_do_app_def = cake_def
  `data_do_app op vs (s:(C,FFI)data_state) =
     if op = clos_Install then
       data_do_install vs (data_state_stack_max_fupd (K NONE)
                             (data_state_stack_frame_sizes_fupd (K LN) s)) else
     if MEM op [IntOp Greater; IntOp GreaterEq] then
       (Rerr (Rabort Rtype_error):(data_v # (C,FFI)data_state,data_v)result) else
     match do_space op vs s with
       NONE -> Rerr (Rabort Rtype_error)
     | SOME s1 -> data_do_app_aux op vs (do_stack op vs (do_lim_safe s1 op vs))`;;

let data_get_var_def = cake_def
  `data_get_var (v:num) = (lookup v:A spt->A option)`;;

let data_get_vars_def = cake_def
  `(data_get_vars [] (s:A spt) = SOME []) /\
   (data_get_vars (CONS v vs) s =
      match data_get_var v s with
        NONE -> NONE
      | SOME x -> (match data_get_vars vs s with
                     NONE -> NONE
                   | SOME xs -> SOME (CONS x xs)))`;;

let data_set_var_def = cake_def
  `data_set_var v x (s:(C,FFI)data_state) =
     data_state_locals_fupd (K (insert v x (data_state_locals s))) s`;;

let data_dec_clock_def = cake_def
  `data_dec_clock (s:(C,FFI)data_state) =
     data_state_clock_fupd (K (data_state_clock s - 1)) s`;;

(* HOL4 infers the most general type: s and s1 are states of independent   *)
(* types                                                                     *)
let data_fix_clock_def = cake_def
  `data_fix_clock (s:(A,B)data_state) ((res:R),(s1:(C,D)data_state)) =
     (res,data_state_clock_fupd
            (K (MIN (data_state_clock s) (data_state_clock s1))) s1)`;;

(* HOL4 [local] *)
let data_fix_clock_IMP = prove
 (`!(s:(A,B)data_state) (x:R#(C,D)data_state) res s1.
     data_fix_clock s x = (res,s1) ==> data_state_clock s1 <= data_state_clock s`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `x:R#(C,D)data_state` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:R` (X_CHOOSE_THEN `s':(C,D)data_state` SUBST1_TAC)) THEN
  REWRITE_TAC[data_fix_clock_def; PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM] THEN ARITH_TAC);;

(* HOL4 [local] *)
let data_LESS_EQ_dec_clock = prove
 (`!(r:(A,B)data_state) (s:(C,FFI)data_state).
     data_state_clock r <= data_state_clock (data_dec_clock s)
     ==> data_state_clock r <= data_state_clock s`,
  REWRITE_TAC[data_dec_clock_def; data_state_INFO.ri_accfupds; K_THM] THEN
  ARITH_TAC);;

let data_flush_state_def = cake_def
  `(data_flush_state T (s:(C,FFI)data_state) =
      data_state_locals_fupd (K LN)
        (data_state_stack_fupd (K [])
           (data_state_locals_size_fupd (K (SOME 0)) s))) /\
   (data_flush_state F s =
      data_state_locals_fupd (K LN)
        (data_state_locals_size_fupd (K (SOME 0)) s))`;;

let data_call_env_def = cake_def
  `data_call_env args (size':num option) (s:(C,FFI)data_state) =
     let new_stack_max = OPTION_MAP2 MAX (data_state_stack_max s)
                           (OPTION_MAP2 (+) (size_of_stack (data_state_stack s)) size') in
     let stack_safe = the F (OPTION_MAP ((>) (limits_stack_limit (data_state_limits s)))
                                        new_stack_max) in
       data_state_locals_fupd (K (fromList args))
         (data_state_locals_size_fupd (K size')
            (data_state_stack_max_fupd (K new_stack_max)
               (data_state_safe_for_space_fupd
                  (K (data_state_safe_for_space s /\ stack_safe)) s)))`;;

let data_push_env_def = cake_def
  `(data_push_env env F (s:(C,FFI)data_state) =
      let stack = CONS (data_Env (data_state_locals_size s) env) (data_state_stack s) in
      let stack_max = OPTION_MAP2 MAX (data_state_stack_max s) (size_of_stack stack) in
      let stack_safe = the F (OPTION_MAP ((>) (limits_stack_limit (data_state_limits s)))
                                         stack_max) in
        data_state_stack_fupd (K stack)
          (data_state_stack_max_fupd (K stack_max)
             (data_state_safe_for_space_fupd
                (K (data_state_safe_for_space s /\ stack_safe)) s))) /\
   (data_push_env env T s =
      let stack = CONS (Exc (data_state_locals_size s) env (data_state_handler s))
                       (data_state_stack s) in
      let stack_max = OPTION_MAP2 MAX (data_state_stack_max s) (size_of_stack stack) in
      let stack_safe = the F (OPTION_MAP ((>) (limits_stack_limit (data_state_limits s)))
                                         stack_max) in
        data_state_stack_fupd (K stack)
          (data_state_stack_max_fupd (K stack_max)
             (data_state_handler_fupd (K (LENGTH (data_state_stack s)))
                (data_state_safe_for_space_fupd
                   (K (data_state_safe_for_space s /\ stack_safe)) s))))`;;

let data_pop_env_def = cake_def
  `data_pop_env (s:(C,FFI)data_state) =
     match data_state_stack s with
       CONS (data_Env ss e) xs ->
         SOME (data_state_locals_fupd (K e)
                 (data_state_stack_fupd (K xs)
                    (data_state_locals_size_fupd (K ss) s)))
     | CONS (Exc ss e n) xs ->
         SOME (data_state_locals_fupd (K e)
                 (data_state_stack_fupd (K xs)
                    (data_state_locals_size_fupd (K ss)
                       (data_state_handler_fupd (K n) s))))
     | _ -> NONE`;;

let data_jump_exc_def = cake_def
  `data_jump_exc (s:(C,FFI)data_state) =
     if data_state_handler s < LENGTH (data_state_stack s) then
       match LASTN (data_state_handler s + 1) (data_state_stack s) with
         CONS (Exc ss e n) xs ->
           SOME (data_state_handler_fupd (K n)
                   (data_state_locals_fupd (K e)
                      (data_state_stack_fupd (K xs)
                         (data_state_locals_size_fupd (K ss) s))))
       | _ -> NONE
     else NONE`;;

let data_cut_env_def = cake_def
  `data_cut_env (name_set:num_set) (env:A spt) =
     if domain name_set SUBSET domain env
     then SOME (mk_wf (inter env name_set))
     else NONE`;;

let data_cut_state_def = cake_def
  `data_cut_state names (s:(C,FFI)data_state) =
     match data_cut_env names (data_state_locals s) with
       NONE -> NONE
     | SOME env -> SOME (data_state_locals_fupd (K env) s)`;;

let data_cut_state_opt_def = cake_def
  `data_cut_state_opt names (s:(C,FFI)data_state) =
     match names with
       NONE -> SOME s
     | SOME names -> data_cut_state names s`;;

(* HOL4 [local] *)
let data_pop_env_clock = prove
 (`!(s:(C,FFI)data_state) s1.
     data_pop_env s = SOME s1 ==> data_state_clock s1 = data_state_clock s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_pop_env_def] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds]);;

(* HOL4 [local] *)
let data_push_env_clock = prove
 (`!env b (s:(C,FFI)data_state).
     data_state_clock (data_push_env env b s) = data_state_clock s`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[data_push_env_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds]);;

let data_find_code_def = cake_def
  `(data_find_code (SOME p) (args:data_v list) (code:(num # A) spt) (ssize:B spt) =
      match lookup p code with
        NONE -> NONE
      | SOME (arity,exp) -> if LENGTH args = arity
                            then SOME (args,exp,lookup p ssize)
                            else NONE) /\
   (data_find_code NONE args code ssize =
      if args = [] then NONE else
        match LAST args with
          data_CodePtr loc ->
            (match lookup loc code with
               NONE -> NONE
             | SOME (arity,exp) -> if LENGTH args = arity + 1
                                   then SOME (BUTLAST args,exp,lookup loc ssize)
                                   else NONE)
        | other -> NONE)`;;

let isBool_def = cake_def
  `(isBool b (data_Block _ tag []) <=> (bool_to_tag b = tag)) /\
   (isBool _ _ <=> F)`;;

let install_sfs_def = cake_def
  `install_sfs op (s:(C,FFI)data_state) =
     data_state_safe_for_space_fupd
       (K (~(op = clos_Install) /\ data_state_safe_for_space s)) s`;;
let _ = cake_add_simps [install_sfs_def];;

(* HOL4's ZIP truncates the longer list; HOL Light's ZIP l1 l2 is HOL4's   *)
(* ZIP (l1,l2) when the lengths agree (the only case evaluate uses)        *)

let data_set_vars_def = cake_def
  `data_set_vars ns vs (s:(C,FFI)data_state) =
     data_state_locals_fupd (K (union (fromAList (ZIP ns vs)) (data_state_locals s))) s`;;

(* HOL4 [local]: helpers for the termination proof of evaluate *)

let DSEMAUX_call_env_clock = prove
 (`!args (size':num option) (s:(C,FFI)data_state).
     data_state_clock (data_call_env args size' s) = data_state_clock s`,
  REWRITE_TAC[data_call_env_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds]);;

let DSEMAUX_set_var_clock = prove
 (`!v x (s:(C,FFI)data_state).
     data_state_clock (data_set_var v x s) = data_state_clock s`,
  REWRITE_TAC[data_set_var_def; data_state_INFO.ri_accfupds]);;

(* HOL4's termination relation:                                              *)
(*   inv_image (measure I LEX measure prog_size) (\(xs,s). (s.clock,xs))     *)
(* HOL4's tactic: rpt strip_tac \\ simp[dec_clock_def]                       *)
(*   \\ imp_res_tac fix_clock_IMP \\ imp_res_tac (GSYM fix_clock_IMP)        *)
(*   \\ FULL_SIMP_TAC (srw_ss()) [set_var_def,push_env_clock,call_env_def,   *)
(*      LET_THM] \\ fs [dec_clock_def]                                       *)

let DSEMAUX_evaluate_rel =
  `inv_image (measure (I:num->num) LEX measure data_prog_size)
     (\x:data_prog # (C,FFI)data_state. data_state_clock (SND x),FST x)`;;

let DSEMAUX_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP data_fix_clock_IMP)) THEN
  REPEAT GEN_TAC THEN
  (fun g -> let ths = [inv_image_THM; LEX_DEF; FST; SND; I_THM; measure_THM;
                       data_dec_clock_def; data_state_INFO.ri_accfupds; K_THM;
                       DSEMAUX_call_env_clock; DSEMAUX_set_var_clock;
                       data_push_env_clock; LET_DEF; LET_END_DEF] @
                      !the_size_defs @ flat (map snd (!the_size_aux_eqs)) in
            (RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths) g) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSSEMAUX_is_num_fact o concl))) THEN
  ARITH_TAC;;

(* the clauses are parsed separately (HOL4 types each clause on its own:  *)
(* ret, dest and res have different types in different clauses).  HOL4's  *)
(* let s1 = call_env args1 ss (push_env env .. (dec_clock s)) in .. of the *)
(* Force and Call clauses is written out at its three uses (sem1aux_def_wf *)
(* drops the binding of a let from the contexts of the induction theorem). *)

let DSEMAUX_evaluate_clauses = list_mk_conj
  [`(data_evaluate:data_prog # (C,FFI)data_state ->
                   ((data_v list,data_v)result)option # (C,FFI)data_state)
      (data_Skip,(s:(C,FFI)data_state)) = (NONE,s)`;
   `(data_evaluate:data_prog # (C,FFI)data_state ->
                   ((data_v list,data_v)result)option # (C,FFI)data_state)
      (data_Move dest src,(s:(C,FFI)data_state)) =
      match data_get_var src (data_state_locals s) with
        NONE -> (SOME (Rerr (Rabort Rtype_error)),s)
      | SOME v -> (NONE, data_set_var dest v s)`;
   `(data_evaluate:data_prog # (C,FFI)data_state ->
                   ((data_v list,data_v)result)option # (C,FFI)data_state)
      (data_Assign dest op args names_opt,(s:(C,FFI)data_state)) =
      if op_requires_names op = IS_NONE names_opt then
        (SOME (Rerr (Rabort Rtype_error)),s)
      else
        (match data_get_vars args (data_state_locals s) with
           NONE -> (SOME (Rerr (Rabort Rtype_error)),s)
         | SOME xs ->
             (match data_cut_state_opt names_opt s with
                NONE -> (SOME (Rerr (Rabort Rtype_error)),s)
              | SOME s ->
                  (match data_do_app op xs s with
                     Rerr e -> (SOME (Rerr e),data_flush_state T (install_sfs op s))
                   | Rval (v,s) ->
                       (NONE, data_set_var dest v (install_sfs op s)))))`;
   `(data_evaluate:data_prog # (C,FFI)data_state ->
                   ((data_v list,data_v)result)option # (C,FFI)data_state)
      (data_Tick,(s:(C,FFI)data_state)) =
      if data_state_clock s = 0
      then (SOME (Rerr (Rabort Rtimeout_error)),data_flush_state T s)
      else (NONE,data_dec_clock s)`;
   `(data_evaluate:data_prog # (C,FFI)data_state ->
                   ((data_v list,data_v)result)option # (C,FFI)data_state)
      (MakeSpace k names,(s:(C,FFI)data_state)) =
      match data_cut_env names (data_state_locals s) with
        NONE -> (SOME (Rerr (Rabort Rtype_error)),s)
      | SOME env -> (NONE,add_space (data_state_locals_fupd (K env) s) k)`;
   `(data_evaluate:data_prog # (C,FFI)data_state ->
                   ((data_v list,data_v)result)option # (C,FFI)data_state)
      (data_Raise n,(s:(C,FFI)data_state)) =
      match data_get_var n (data_state_locals s) with
        NONE -> (SOME (Rerr (Rabort Rtype_error)),s)
      | SOME x ->
          (match data_jump_exc s with
             NONE -> (SOME (Rerr (Rabort Rtype_error)),s)
           | SOME s -> (SOME (Rerr (Rraise x)),s))`;
   `(data_evaluate:data_prog # (C,FFI)data_state ->
                   ((data_v list,data_v)result)option # (C,FFI)data_state)
      (data_Return ns,(s:(C,FFI)data_state)) =
      match data_get_vars ns (data_state_locals s) with
        NONE -> (SOME (Rerr (Rabort Rtype_error)),s)
      | SOME xs -> (SOME (Rval xs),data_flush_state F s)`;
   `(data_evaluate:data_prog # (C,FFI)data_state ->
                   ((data_v list,data_v)result)option # (C,FFI)data_state)
      (data_Seq c1 c2,(s:(C,FFI)data_state)) =
      let (res,s1) = data_fix_clock s (data_evaluate (c1,s)) in
        if res = NONE then data_evaluate (c2,s1) else (res,s1)`;
   `(data_evaluate:data_prog # (C,FFI)data_state ->
                   ((data_v list,data_v)result)option # (C,FFI)data_state)
      (data_If n c1 c2,(s:(C,FFI)data_state)) =
      match data_get_var n (data_state_locals s) with
        NONE -> (SOME (Rerr (Rabort Rtype_error)),s)
      | SOME x -> if isBool T x then data_evaluate (c1,s) else
                  if isBool F x then data_evaluate (c2,s) else
                    (SOME (Rerr (Rabort Rtype_error)),s)`;
   `(data_evaluate:data_prog # (C,FFI)data_state ->
                   ((data_v list,data_v)result)option # (C,FFI)data_state)
      (data_Force ret loc src,(s:(C,FFI)data_state)) =
      match data_get_var src (data_state_locals s) with
        NONE -> (SOME (Rerr (Rabort Rtype_error)),s)
      | SOME thunk_v ->
          (match data_dest_thunk thunk_v (data_state_refs s) with
             data_BadRef -> (SOME (Rerr (Rabort Rtype_error)),s)
           | data_NotThunk -> (SOME (Rerr (Rabort Rtype_error)),s)
           | data_IsThunk Evaluated v ->
               (match ret with
                  NONE -> (SOME (Rval [v]),data_flush_state F s)
                | SOME (dest,names) ->
                    (match data_cut_env names (data_state_locals s) with
                       NONE -> (SOME (Rerr (Rabort Rtype_error)),s)
                     | SOME env ->
                         (NONE, data_set_var dest v (data_state_locals_fupd (K env) s))))
           | data_IsThunk NotEvaluated f ->
               (match data_find_code (SOME loc) [thunk_v; f] (data_state_code s)
                        (data_state_stack_frame_sizes s) with
                  NONE -> (SOME (Rerr (Rabort Rtype_error)),s)
                | SOME (args1,prog,ss) ->
                    (match ret with
                       NONE ->
                         (if data_state_clock s = 0 then
                            (SOME (Rerr (Rabort Rtimeout_error)),
                             data_state_stack_fupd (K [])
                               (data_state_locals_fupd (K LN) s))
                          else
                            (match data_evaluate (prog, data_call_env args1 ss
                                                          (data_dec_clock s)) with
                               (NONE,s) -> (SOME (Rerr (Rabort Rtype_error)),s)
                             | (SOME res,s) -> (SOME res,s)))
                     | SOME (dest,names) ->
                         (match data_cut_env names (data_state_locals s) with
                            NONE -> (SOME (Rerr (Rabort Rtype_error)),s)
                          | SOME env ->
                                if data_state_clock s = 0 then
                                  (SOME (Rerr (Rabort Rtimeout_error)),
                                   data_state_stack_fupd (K [])
                                     (data_state_locals_fupd (K LN)
                                        (data_call_env args1 ss
                                           (data_push_env env F (data_dec_clock s)))))
                                else
                                  (match data_fix_clock
                                           (data_call_env args1 ss
                                              (data_push_env env F (data_dec_clock s)))
                                           (data_evaluate (prog, data_call_env args1 ss
                                              (data_push_env env F (data_dec_clock s)))) with
                                     (SOME (Rval xs),s2) ->
                                       (if LENGTH xs = 1 then
                                          (match data_pop_env s2 with
                                             NONE -> (SOME (Rerr (Rabort Rtype_error)),s2)
                                           | SOME s1 -> (NONE, data_set_var dest (HD xs) s1))
                                        else
                                          (SOME (Rerr (Rabort Rtype_error)),s2))
                                   | (NONE,s) -> (SOME (Rerr (Rabort Rtype_error)),s)
                                   | res -> res)))))`;
   `(data_evaluate:data_prog # (C,FFI)data_state ->
                   ((data_v list,data_v)result)option # (C,FFI)data_state)
      (data_Call ret dest args handler,(s:(C,FFI)data_state)) =
      match data_get_vars args (data_state_locals s) with
        NONE -> (SOME (Rerr (Rabort Rtype_error)),s)
      | SOME xs ->
          (match data_find_code dest xs (data_state_code s)
                   (data_state_stack_frame_sizes s) with
             NONE -> (SOME (Rerr (Rabort Rtype_error)),s)
           | SOME (args1,prog,ss) ->
               (match ret with
                  NONE ->
                    (if handler = NONE then
                       (if data_state_clock s = 0
                        then (SOME (Rerr (Rabort Rtimeout_error)),data_flush_state T s)
                        else
                          (match data_evaluate (prog, data_call_env args1 ss
                                                        (data_dec_clock s)) with
                             (NONE,s) -> (SOME (Rerr (Rabort Rtype_error)),s)
                           | (SOME res,s) -> (SOME res,s)))
                     else (SOME (Rerr (Rabort Rtype_error)),s))
                | SOME (ns,names) ->
                    (if ~ALL_DISTINCT ns then (SOME (Rerr (Rabort Rtype_error)),s) else
                     (match data_cut_env names (data_state_locals s) with
                        NONE -> (SOME (Rerr (Rabort Rtype_error)),s)
                      | SOME env ->
                            if data_state_clock s = 0
                            then (SOME (Rerr (Rabort Rtimeout_error)),
                                  data_state_stack_fupd (K [])
                                    (data_state_locals_fupd (K LN)
                                       (data_call_env args1 ss
                                          (data_push_env env (IS_SOME handler)
                                             (data_dec_clock s)))))
                            else
                              (match data_fix_clock
                                       (data_call_env args1 ss
                                          (data_push_env env (IS_SOME handler)
                                             (data_dec_clock s)))
                                       (data_evaluate (prog, data_call_env args1 ss
                                          (data_push_env env (IS_SOME handler)
                                             (data_dec_clock s)))) with
                                 (SOME (Rval xs),s2) ->
                                   (if LENGTH xs = LENGTH ns then
                                      (match data_pop_env s2 with
                                         NONE -> (SOME (Rerr (Rabort Rtype_error)),s2)
                                       | SOME s1 -> (NONE, data_set_vars ns xs s1))
                                    else
                                      (SOME (Rerr (Rabort Rtype_error)),s2))
                               | (SOME (Rerr (Rraise x)),s2) ->
                                   (match handler with
                                      NONE -> (SOME (Rerr (Rraise x)),s2)
                                    | SOME (n,h) -> data_evaluate (h, data_set_var n x s2))
                               | (NONE,s) -> (SOME (Rerr (Rabort Rtype_error)),s)
                               | res -> res)))))`];;

(* HOL4 evaluate_def (the first one, with fix_clock) *)
let DSEMAUX_evaluate_fix_def =
  sem1aux_def_wf DSEMAUX_evaluate_rel DSEMAUX_TC_TAC DSEMAUX_evaluate_clauses;;

(* HOL4's first evaluate_ind *)
let DSEMAUX_evaluate_fix_ind = cake_ind "data_evaluate";;

let evaluate_safe_def = cake_def
  `evaluate_safe c (s:(C,FFI)data_state) =
     let (x,s1) = data_evaluate (c,s) in data_state_safe_for_space s1`;;

let evaluate_peak_def = cake_def
  `evaluate_peak c (s:(C,FFI)data_state) =
     let (x,s1) = data_evaluate (c,s) in data_state_peak_heap_length s1`;;

(* We prove that the clock never increases. *)

(* HOL4: pair_case_eq, bool_case_eq and the case_eq theorems of list,       *)
(* option, op, v, ref, word_size, eq_result and ffi_result                  *)
let data_case_eq_thms = end_itlist CONJ
  ([pair_case_eq; COND_CASE_EQ; list_case_eq; option_case_eq] @
   map case_eq ["clos_op"; "data_v"; "bvl_ref"; "word_size"; "eq_result";
                "ffi_result"]);;

let do_stack_clock = prove
 (`!op args (s1:(C,FFI)data_state).
     data_state_clock (do_stack op args s1) = data_state_clock s1`,
  REWRITE_TAC[do_stack_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds]);;

(* the clock fact of do_app_aux (HOL4 proves do_app_clock by unfolding    *)
(* do_app, do_app_aux and the helpers at once)                            *)

let DSEMAUX_do_app_aux_clock = prove
 (`!op vs (s:(C,FFI)data_state) res s2.
     data_do_app_aux op vs s = Rval (res,s2) ==>
     data_state_clock s2 = data_state_clock s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_do_app_aux_def] THEN
  REWRITE_TAC[with_fresh_ts_def; check_lim_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  TRY(DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2)) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; K_THM]);;

let do_app_clock = prove
 (`!op args (s1:(C,FFI)data_state) res s2.
     data_do_app op args s1 = Rval (res,s2) ==>
     data_state_clock s2 <= data_state_clock s1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_do_app_def] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[data_do_install_def; LET_DEF; LET_END_DEF] THEN
    REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
    REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    REWRITE_TAC[data_state_INFO.ri_accfupds; LE_REFL];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[distinctness "result"] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[distinctness "result"] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DSEMAUX_do_app_aux_clock) THEN
  REWRITE_TAC[do_stack_clock; do_lim_safe; data_state_INFO.ri_accfupds] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[do_space_def; consume_space_def] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[data_state_INFO.ri_accfupds; LE_REFL]);;

(* HOL4 [local,simp] *)
let set_vars_clock = prove
 (`!ns vs (s:(C,FFI)data_state).
     data_state_clock (data_set_vars ns vs s) = data_state_clock s`,
  REWRITE_TAC[data_set_vars_def; data_state_INFO.ri_accfupds]);;
let _ = cake_add_simps [set_vars_clock];;

(* the proof of evaluate_clock: the clock facts of the helpers, then the    *)
(* induction hypotheses instantiated at the evaluate assumptions (the      *)
(* method of wordSem's evaluate_clock)                                      *)

let DSEMAUX_cut_state_opt_clock = prove
 (`!names (s:(C,FFI)data_state) s1.
     data_cut_state_opt names s = SOME s1 ==>
     data_state_clock s1 = data_state_clock s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[data_cut_state_opt_def; data_cut_state_def] THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[data_state_INFO.ri_accfupds]);;

let DSEMAUX_jump_exc_clock = prove
 (`!(s:(C,FFI)data_state) s1.
     data_jump_exc s = SOME s1 ==> data_state_clock s1 = data_state_clock s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[data_jump_exc_def] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[data_state_INFO.ri_accfupds]);;

let DSEMAUX_clock_rws =
  [data_state_INFO.ri_accfupds; K_THM; data_dec_clock_def; DSEMAUX_call_env_clock;
   DSEMAUX_set_var_clock; set_vars_clock; data_push_env_clock;
   install_sfs_def; add_space_def; data_flush_state_def];;

let DSEMAUX_clock_case_eqs =
  [pair_case_eq; option_case_eq; list_case_eq; COND_CASE_EQ] @
  map case_eq ["result"; "error_result"; "data_dest_thunk_ret"; "thunk_mode"];;

let DSEMAUX_is_eval_eq tm =
  is_eq tm &&
  (try fst(dest_const(fst(strip_comb(lhs tm)))) = "data_evaluate"
   with Failure _ -> false);;

(* prove ?vs. A1 /\ ... /\ An from the assumptions: each existential      *)
(* variable is found by matching a conjunct with an assumption (or the two *)
(* sides of an equation), the instantiated conjunction is proved by        *)
(* rewriting with the assumptions (wordSem's IL2AUX_EXISTS_ASM_TAC)        *)

let DSEMAUX_EXISTS_ASM_TAC : tactic = fun (asl,w as g) ->
  let vs,body = strip_exists w in
  let facts = map (concl o snd) asl in
  let rec go theta cjs =
    match cjs with
      [] -> theta
    | c::rest ->
        let c' = vsubst theta c in
        let fvs = filter (fun v -> mem v vs && not (can (rev_assoc v) theta))
                         (frees c') in
        if fvs = [] then go theta rest else
        let try_m p t =
          let (_,tmi,tyi) = term_match [] p t in
          if forall (fun (t,v) -> mem v fvs || t = v) tmi &&
             forall (fun (a,b) -> a = b) tyi
          then filter (fun (t,v) -> mem v fvs) tmi else failwith "" in
        let tmi = try tryfind (try_m c') facts
                  with Failure _ ->
                    try let l,r = dest_eq c' in
                        (try try_m r l with Failure _ -> try_m l r)
                    with Failure _ -> [] in
        go (tmi @ theta) rest in
  let theta = go [] (conjuncts body) in
  let wits = map (fun v -> try rev_assoc v theta with Failure _ -> v) vs in
  (MAP_EVERY EXISTS_TAC wits THEN ASM_REWRITE_TAC[]) g;;

(* for every assumption data_evaluate p = (v,t) and every induction        *)
(* hypothesis whose evaluate antecedent matches it, add the instance of    *)
(* its conclusion when its other antecedents follow from the assumptions   *)
(* (wordSem's IL2AUX_USE_IHS_TAC)                                          *)

let DSEMAUX_USE_IHS_TAC : tactic = fun (asl,w as g) ->
  let evs = filter (fun th -> DSEMAUX_is_eval_eq (concl th)) (map snd asl) in
  let ihs = mapfilter (fun (_,th) ->
      let th' = REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] th in
      let vs,bod = strip_forall (concl th') in
      if is_imp bod && exists DSEMAUX_is_eval_eq (conjuncts(fst(dest_imp bod)))
      then th' else failwith "") asl in
  let avoid = freesl (w :: map (concl o snd) asl) in
  let inst_of ih0 e =
    let vs0,_ = strip_forall (concl ih0) in
    let vs1 = rev(itlist (fun v acc -> variant (acc @ avoid) v :: acc) (rev vs0) []) in
    let ih = GENL vs1 (SPECL vs1 ih0) in
    let vs,bod = strip_forall (concl ih) in
    let ant,_ = dest_imp bod in
    let cj = find DSEMAUX_is_eval_eq (conjuncts ant) in
    let (_,tmi,tyi) = term_match [] cj (concl e) in
    if exists (fun (a,b) -> not (a = b)) tyi ||
       exists (fun (t,v) -> not (mem v vs) && not (t = v)) tmi then failwith "" else
    let ihi = INST tmi (SPEC_ALL ih) in
    let a,c = dest_imp (concl ihi) in
    let rest = filter (fun v -> mem v vs) (subtract (frees a) (frees c)) in
    c, GENL rest ihi in
  let insts = flat (map (fun e -> mapfilter (fun ih -> inst_of ih e) ihs) evs) in
  MAP_EVERY (fun (c,th) ->
      TRY (SUBGOAL_THEN c STRIP_ASSUME_TAC THENL
            [MATCH_MP_TAC th THEN DSEMAUX_EXISTS_ASM_TAC THEN NO_TAC; ALL_TAC]))
    insts g;;

let DSEMAUX_CLOCK_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[DSEMAUX_evaluate_fix_def] THEN
  REWRITE_TAC(DSEMAUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  DSEMAUX_USE_IHS_TAC THEN
  MAP_EVERY (fun th -> REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC_ALL o MATCH_MP th)))
    [data_fix_clock_IMP; data_pop_env_clock; DSEMAUX_cut_state_opt_clock;
     DSEMAUX_jump_exc_clock; do_app_clock] THEN
  (fun g -> let ths = DSEMAUX_clock_rws in
            (RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths) g) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSSEMAUX_is_num_fact o concl))) THEN
  ARITH_TAC;;

(* the If case (the condition isBool of the value is a context of the IHs) *)

let DSEMAUX_CLOCK_IF_TAC : tactic =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[DSEMAUX_evaluate_fix_def] THEN
  REWRITE_TAC[option_case_eq; COND_CASE_EQ; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN ASM_MESON_TAC[];;

let DSEMAUX_evaluate_clock = prove
 (`!p vs (s2:(C,FFI)data_state).
     data_evaluate p = (vs,s2) ==> data_state_clock s2 <= data_state_clock (SND p)`,
  MATCH_MP_TAC DSEMAUX_evaluate_fix_ind THEN REWRITE_TAC[SND] THEN
  REPEAT CONJ_TAC THEN FIRST [DSEMAUX_CLOCK_TAC; DSEMAUX_CLOCK_IF_TAC]);;

let data_evaluate_clock = prove
 (`!xs (s1:(C,FFI)data_state) vs s2.
     data_evaluate (xs,s1) = (vs,s2) ==> data_state_clock s2 <= data_state_clock s1`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP DSEMAUX_evaluate_clock) THEN
  REWRITE_TAC[SND]);;

let data_fix_clock_evaluate = prove
 (`!xs (s:(C,FFI)data_state).
     data_fix_clock s (data_evaluate (xs,s)) = data_evaluate (xs,s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `data_evaluate (xs,s:(C,FFI)data_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((data_v list,data_v)result)option`
    (X_CHOOSE_THEN `s1:(C,FFI)data_state` (fun th -> ASSUME_TAC th THEN
                                                  REWRITE_TAC[th]))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP data_evaluate_clock) THEN
  REWRITE_TAC[data_fix_clock_def; PAIR_EQ; data_state_component_equality;
              data_state_INFO.ri_accfupds; K_THM] THEN
  ASM_ARITH_TAC);;

(* Finally, we remove fix_clock from the induction and definition theorems. *)

let data_evaluate_def =
  REWRITE_RULE[data_fix_clock_evaluate] DSEMAUX_evaluate_fix_def;;

let data_evaluate_ind =
  REWRITE_RULE[data_fix_clock_evaluate] DSEMAUX_evaluate_fix_ind;;

(* cake_ind returns HOL4's final induction theorem *)
let () = cake_ind_store := ("data_evaluate",data_evaluate_ind) :: !cake_ind_store;;

(* observational semantics *)

let data_initial_state_def = cake_def
  `data_initial_state (ffi:(FFI)ffi_state) code
                      (coracle:num -> C # (num # num # data_prog) list) cc stamps
                      lims ss k =
     data_state_REC LN (SOME 0) [] (SOME 1) ss NONE 0 LN cc k code ffi 0
       (if stamps then SOME 0 else NONE) lims (if stamps then T else F) 0 coracle`;;

let data_semantics_def = cake_def
  `data_semantics (init_ffi:(FFI)ffi_state) code
                  (coracle:num -> C # (num # num # data_prog) list) cc lims ss start =
     let p = data_Call NONE (SOME start) [] NONE in
     let init = data_initial_state init_ffi code coracle cc T lims ss in
       if ?k. match FST (data_evaluate (p,init k)) with
                SOME (Rerr e) -> ~(e = Rabort Rtimeout_error) /\
                                 (!f. ~(e = Rabort (Rffi_error f)))
              | NONE -> T
              | _ -> F
       then Fail
       else
       (match some res.
          ?k s r outcome.
            data_evaluate (p,init k) = (SOME r,s) /\
            (match r with
               Rerr (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
             | Rval _ -> outcome = Success
             | _ -> F) /\
            res = Terminate outcome (ffi_state_io_events (data_state_ffi s))
        with
          SOME res -> res
        | NONE ->
            Diverge
              (build_lprefix_lub
                (IMAGE (\k. llist_fromList
                          (ffi_state_io_events
                             (data_state_ffi (SND (data_evaluate (p,init k))))))
                       UNIV)))`;;

let data_lang_safe_for_space_def = cake_def
  `data_lang_safe_for_space (init_ffi:(FFI)ffi_state) code (lims:limits)
                            (ss:num spt) start <=>
     !ck.
       let p = data_Call NONE (SOME start) [] NONE in
       let init = data_initial_state init_ffi code ARB ARB T lims ss in
       let (res,s) = data_evaluate (p,(init ck:(1,FFI)data_state)) in
         data_state_safe_for_space s`;;

let compute_limits_def = cake_def
  `compute_limits len_bits a64 fpops fptops (stack_heap_limit:num#num) =
     limits_REC (SND stack_heap_limit) len_bits (FST stack_heap_limit) a64 fpops fptops`;;
