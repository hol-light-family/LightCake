(* ========================================================================= *)
(* panSem: port of HOL4 pancake/semantics/panSemScript.sml (CakeML v3479).  *)
(* Semantics of panLang.                                                     *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: pan_v (constructors pan_Val,               *)
(*   pan_RStruct, pan_NStruct), pan_state (fields pan_state_locals, ...),    *)
(*   pan_result (pan_Error, pan_TimeOut, ...), pan_eval, pan_evaluate, ...   *)
(* - The HOL4 Overload ValWord w = Val (Word w) is written out as            *)
(*   pan_Val (Word w).                                                       *)
(* - HOL4 r.f is RECTYPE_f r; r with f := v is RECTYPE_f_fupd (K v) r;       *)
(*   HOL4 aligned is alignment_aligned; 1w is word 1; w2w is word_zx; w2n   *)
(*   is val; n2w is word; word_cmp is asm_word_cmp; LIST_REL is ALL2; EVERY *)
(*   is ALL; ZIP (a,b) is ZIP a b (used on lists of equal lengths only);    *)
(*   fromList is llist_fromList; UNIV is (:num).                             *)
(* - Local helpers that are not HOL4 theorems are PSEMAUX_.                  *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/finite_map.ml";;
needs "hol4/lprefix_lub.ml";;
needs "hol4/libext.ml";;
needs "semantics/ffi/ffi.ml";;
needs "compiler/backend/wordLang.ml";;
needs "pancake/panLang.ml";;

prioritize_num();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Values, states and results.                                               *)
(* ------------------------------------------------------------------------- *)

(* HOL4: TODO: rename or remove *)

let word_lab_INDUCT,word_lab_RECURSION = cake_type
  "word_lab = Word (A word)";;

let pan_v_INDUCT,pan_v_RECURSION = cake_type
  "pan_v = pan_Val ((A)word_lab)
         | pan_RStruct (pan_v list)
         | pan_NStruct stcname ((fldname # pan_v) list)";;

(* HOL4 Overload ValWord = \w. Val (Word w): written pan_Val (Word w) *)

(* HOL4's second clause isWord _ = F is redundant (word_lab has one        *)
(* constructor): HOL4 and the kit drop it                                  *)

let pan_isWord_def = cake_def
  `(pan_isWord (Word (_:A word)) <=> T) /\
   (pan_isWord (_:(A)word_lab) <=> F)`;;

let pan_theWord_def = cake_def
  `pan_theWord (Word (w:A word)) = w`;;

let isValWord_def = cake_def
  `(isValWord (pan_Val (Word (_:A word))) <=> T) /\
   (isValWord _ <=> F)`;;

let theValWord_def = cake_def
  `theValWord (pan_Val (Word (w:A word))) = w`;;

(* code: arguments (with shape), body, return shape *)

let pan_state_INFO = cake_record "pan_state"
  ["locals","(varname,(A)pan_v)fmap";
   "globals","(varname,(A)pan_v)fmap";
   "structs","(stcname#struct_info)list";
   "code","(funname,(varname#shape)list#(A)panLang_prog#shape)fmap";
   "eshapes","(eid,shape)fmap";
   "memory","A word->(A)word_lab";
   "memaddrs","A word->bool";
   "sh_memaddrs","A word->bool";
   "clock","num";
   "be","bool";
   "ffi","(FFI)ffi_state";
   "base_addr","A word";
   "top_addr","A word"];;

let pan_state_component_equality = pan_state_INFO.ri_component_equality;;

let pan_result_INDUCT,pan_result_RECURSION = cake_type
  "pan_result = pan_Error
              | pan_TimeOut
              | pan_Break
              | pan_Continue
              | pan_Return ((A)pan_v)
              | pan_Exception mlstring ((A)pan_v)
              | pan_FinalFFI final_event";;

let shape_of_def = cake_def
  `(shape_of (pan_Val (Word (_:A word))) = One) /\
   (shape_of (pan_RStruct vs) = Comb (MAP shape_of vs)) /\
   (shape_of (pan_NStruct nm (_:(fldname#(A)pan_v)list)) = Named nm)`;;

(* ------------------------------------------------------------------------- *)
(* Memory loads.                                                             *)
(* ------------------------------------------------------------------------- *)

let pan_mem_load_byte_def = cake_def
  `pan_mem_load_byte (m:A word->(A)word_lab) dm be (w:A word) =
     match m (byte_align w) with
       Word v -> if byte_align w IN dm then SOME (get_byte w v be) else NONE`;;

let pan_mem_load_32_def = cake_def
  `pan_mem_load_32 (m:A word->(A)word_lab) dm be (w:A word) =
     if alignment_aligned 2 w
     then match m (byte_align w) with
            Word v ->
              if byte_align w IN dm
              then SOME (word_of_bytes be (word 0:int32)
                           [get_byte w v be; get_byte (word_add w (word 1)) v be;
                            get_byte (word_add w (word 2)) v be;
                            get_byte (word_add w (word 3)) v be])
              else NONE
     else NONE`;;

let pan_mem_load_32_alt = prove
 (CASE_TERM `pan_mem_load_32 (m:A word->(A)word_lab) dm be (w:A word) =
   if alignment_aligned 2 w
   then match m (byte_align w) with
          Word v ->
            if byte_align w IN dm
            then
              let b0 = get_byte w v be in
              let b1 = get_byte (word_add w (word 1)) v be in
              let b2 = get_byte (word_add w (word 2)) v be in
              let b3 = get_byte (word_add w (word 3)) v be in
              let v' =
                  (if be
                   then word_or (word_or (word_or (word_shl (word_zx b0) 24)
                                                  (word_shl (word_zx b1) 16))
                                         (word_shl (word_zx b2) 8))
                                (word_zx b3)
                   else word_or (word_or (word_or (word_zx b0)
                                                  (word_shl (word_zx b1) 8))
                                         (word_shl (word_zx b2) 16))
                                (word_shl (word_zx b3) 24)) in
              SOME (v':int32)
            else NONE
   else NONE`,
  REWRITE_TAC[pan_mem_load_32_def; WORDSAUX_word_of_bytes_32] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REFL_TAC);;

(* mem_load, mem_loads, mem_load_flds.  HOL4's case (mem_load .., mem_loads *)
(* ..) of (SOME v, SOME vs) => .. | _ => NONE is a case on the pair of the  *)
(* two calls (pair_CASE); it is written so here (the kit would otherwise    *)
(* compile it into a case on the first call with the second inside its     *)
(* SOME arm, and pan_mem_load_ind would then have the second call's         *)
(* hypothesis under mem_load .. = SOME v, unlike HOL4's), and the stored     *)
(* pan_mem_load_def has the pair case reduced (nested cases).  HOL4's        *)
(* variable fields of the last clause is flds here (fields is mlstring's     *)
(* constant).                                                                *)

(* HOL4: rw [] >> disj1_tac >> irule LESS_LESS_EQ_TRANS >> irule_at Any     *)
(* LENGTH_dropWhile_LESS_EQ >> ... *)

let PSEMAUX_MEM_LOAD_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP LIBXAUX_dropWhile_CONS)) THEN
  REWRITE_TAC[inv_image_THM; sum_CASE; FST; SND; MAP] THEN TERM_TAC;;

let PSEMAUX_mem_load_def = cake_def_wf
  (CASE_TERM
   `inv_image (MEASURE LENGTH LEX
               MEASURE (\x:shape + shape list.
                          match x with INL x -> shape_size x
                                     | INR x -> list_size shape_size x))
      (\x:(shape#A word#(A word->bool)#(A word->(A)word_lab)#
           (mlstring#struct_info)list) +
          ((shape list)#A word#(A word->bool)#(A word->(A)word_lab)#
           (mlstring#struct_info)list) +
          (((mlstring#shape)list)#A word#(A word->bool)#(A word->(A)word_lab)#
           (mlstring#struct_info)list).
         match x with
           INL x -> (SND (SND (SND (SND x))), INL (FST x))
         | INR (INL x) -> (SND (SND (SND (SND x))), INR (FST x))
         | INR (INR x) -> (SND (SND (SND (SND x))), INR (MAP SND (FST x))))`)
  PSEMAUX_MEM_LOAD_TC_TAC
  `(pan_mem_load sh (addr:A word) dm (m:A word->(A)word_lab)
                 (stcs:(stcname#struct_info)list) =
      match sh with
        One -> if addr IN dm then SOME (pan_Val (m addr)) else NONE
      | Comb shapes ->
          (match mem_loads shapes addr dm m stcs with
             SOME vs -> SOME (pan_RStruct vs)
           | NONE -> NONE)
      | Named nm ->
          (match dropWhile (\p. match p with (n,i) -> ~(n = nm)) stcs with
             CONS (nm,info) stcs' ->
               (match mem_load_flds (struct_info_fields info) addr dm m stcs' with
                  SOME vflds -> SOME (pan_NStruct nm vflds)
                | NONE -> NONE)
           | _ -> NONE)) /\
   (mem_loads [] addr dm m stcs = SOME []) /\
   (mem_loads (CONS shape shapes) addr dm m stcs =
      pair_CASE
        (pan_mem_load shape addr dm m stcs,
         mem_loads shapes
           (word_add addr (word_mul bytes_in_word
                             (word (size_of_sh_with_ctxt stcs shape))))
           dm m stcs)
        (\r1 r2. match (r1,r2) with
                   (SOME v, SOME vs) -> SOME (CONS v vs)
                 | _ -> NONE)) /\
   (mem_load_flds [] addr dm m stcs = SOME []) /\
   (mem_load_flds (CONS (fld,shape) flds) addr dm m stcs =
      pair_CASE
        (pan_mem_load shape addr dm m stcs,
         mem_load_flds flds
           (word_add addr (word_mul bytes_in_word
                             (word (size_of_sh_with_ctxt stcs shape))))
           dm m stcs)
        (\r1 r2. match (r1,r2) with
                   (SOME v, SOME vflds) -> SOME (CONS (fld,v) vflds)
                 | _ -> NONE))`;;

let pan_mem_load_def =
  CONV_RULE (DEPTH_CONV BETA_CONV) (REWRITE_RULE[pair_CASE] PSEMAUX_mem_load_def);;

let pan_mem_load_ind = cake_ind "pan_mem_load";;

let pan_op_def = cake_def
  `(pan_op panLang_Mul [w1:A word; w2] = SOME (word_mul w1 w2)) /\
   (pan_op _ (_:(A word)list) = NONE)`;;

let pan_primop_def = cake_def
  `pan_primop panLang_AddCarry (args:((A)pan_v)list) =
     if LENGTH args = 3 /\ ALL isValWord args then
       let l = theValWord (EL 0 args) in
       let r = theValWord (EL 1 args) in
       let ci = theValWord (EL 2 args) in
       let (res,co) = word_add_carry l r ci in
       SOME (pan_RStruct [pan_Val (Word res); pan_Val (Word co)])
     else NONE`;;

(* eval.  Cmp and Shift: as in pan_mem_load, HOL4's case on the pair of the *)
(* two calls is written with pair_CASE, so that pan_eval_ind has HOL4's      *)
(* hypotheses P s e1 /\ P s e2; the stored pan_eval_def has the pair case    *)
(* reduced.  The clauses are parsed in two quotations (op is a binop in Op  *)
(* and a panop in Panop).  HOL4's termination tactic: gs [UNZIP_MAP] >> fs  *)
(* [MEM_SPLIT, ...]: a call on a member of the field expressions MAP SND    *)
(* eflds is on SND x for some MEM x eflds, which panLang_MEM_IMP_exp_size   *)
(* bounds; then the kit's TERM_TAC.                                          *)

let PSEMAUX_EVAL_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[UNZIP_DEF; PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[MEM_MAP]) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC)) THEN RVEQ_TAC THEN
  (fun (asl,w as g) ->
     let th0 = INST [`ARB:A->num`,`l:A->num`]
                    (CONJUNCT2 panLang_MEM_IMP_exp_size) in
     MAP_EVERY ASSUME_TAC (mapfilter (fun (_,th) -> MATCH_MP th0 th) asl) g) THEN
  TERM_TAC;;

let PSEMAUX_eval_def = cake_def_wf_clauses
  `MEASURE (\p:(A,FFI)pan_state#(A)panLang_exp. panLang_exp_size ARB (SND p))`
  PSEMAUX_EVAL_TC_TAC
  [`(pan_eval (s:(A,FFI)pan_state) (panLang_Const w) = SOME (pan_Val (Word w))) /\
    (pan_eval s (panLang_Var panLang_Local v) = FLOOKUP (pan_state_locals s) v) /\
    (pan_eval s (panLang_Var panLang_Global v) = FLOOKUP (pan_state_globals s) v) /\
    (pan_eval s (RStruct es) =
       match OPT_MMAP (pan_eval s) es with
         SOME vs -> SOME (pan_RStruct vs)
       | NONE -> NONE) /\
    (pan_eval s (RField index e) =
       match pan_eval s e with
         SOME (pan_RStruct vs) ->
           if index < LENGTH vs then SOME (EL index vs) else NONE
       | _ -> NONE) /\
    (pan_eval s (NStruct nm eflds) =
       let (field_names,field_exps) = UNZIP eflds in
       match ALOOKUP (pan_state_structs s) nm with
         SOME info ->
           let (field_names',field_shapes) = UNZIP (struct_info_fields info) in
           if field_names' = field_names then
             match OPT_MMAP (pan_eval s) field_exps with
               SOME field_vals ->
                 if ALL (\p. match p with (s,v) -> s = shape_of v)
                        (ZIP field_shapes field_vals)
                 then SOME (pan_NStruct nm (ZIP field_names field_vals))
                 else NONE
             | NONE -> NONE
           else NONE
       | NONE -> NONE) /\
    (pan_eval s (NField fld e) =
       match pan_eval s e with
         SOME (pan_NStruct nm vflds) ->
           if ~(ALOOKUP (pan_state_structs s) nm = NONE)
           then ALOOKUP vflds fld else NONE
       | _ -> NONE) /\
    (pan_eval s (panLang_Load shape addr) =
       if is_wf_shape (pan_state_structs s) shape then
         match pan_eval s addr with
           SOME (pan_Val (Word w)) ->
             pan_mem_load shape w (pan_state_memaddrs s) (pan_state_memory s)
                          (pan_state_structs s)
         | _ -> NONE
       else NONE) /\
    (pan_eval s (panLang_Load32 addr) =
       match pan_eval s addr with
         SOME (pan_Val (Word w)) ->
           (match pan_mem_load_32 (pan_state_memory s) (pan_state_memaddrs s)
                                  (pan_state_be s) w with
              NONE -> NONE
            | SOME w -> SOME (pan_Val (Word (word_zx w))))
       | _ -> NONE) /\
    (pan_eval s (LoadByte addr) =
       match pan_eval s addr with
         SOME (pan_Val (Word w)) ->
           (match pan_mem_load_byte (pan_state_memory s) (pan_state_memaddrs s)
                                    (pan_state_be s) w with
              NONE -> NONE
            | SOME w -> SOME (pan_Val (Word (word_zx w))))
       | _ -> NONE) /\
    (pan_eval s (panLang_Op op es) =
       match OPT_MMAP (pan_eval s) es with
         SOME ws ->
           if ALL (\w. match w with pan_Val (Word _) -> T | _ -> F) ws
           then OPTION_MAP (\w. pan_Val (Word w))
                  (word_op op (MAP (\w. match w with pan_Val (Word n) -> n) ws))
           else NONE
       | _ -> NONE)`;
   `(pan_eval (s:(A,FFI)pan_state) (Panop op (es:((A)panLang_exp)list)) =
       match OPT_MMAP (pan_eval s) es with
         SOME ws ->
           if ALL (\w. match w with pan_Val (Word _) -> T | _ -> F) ws
           then OPTION_MAP (\w. pan_Val (Word w))
                  (pan_op op (MAP (\w. match w with pan_Val (Word n) -> n) ws))
           else NONE
       | _ -> NONE) /\
    (pan_eval s (Cmp cmp e1 e2) =
       pair_CASE (pan_eval s e1, pan_eval s e2)
         (\r1 r2. match (r1,r2) with
                    (SOME (pan_Val (Word w1)), SOME (pan_Val (Word w2))) ->
                      SOME (pan_Val (Word (if asm_word_cmp cmp w1 w2 then word 1
                                           else word 0)))
                  | _ -> NONE)) /\
    (pan_eval s (panLang_Shift sh e1 e2) =
       pair_CASE (pan_eval s e1, pan_eval s e2)
         (\r1 r2. match (r1,r2) with
                    (SOME (pan_Val (Word w1)), SOME (pan_Val (Word w2))) ->
                      OPTION_MAP (\w. pan_Val (Word w)) (word_sh sh w1 (val w2))
                  | _ -> NONE)) /\
    (pan_eval s BaseAddr = SOME (pan_Val (Word (pan_state_base_addr s)))) /\
    (pan_eval s TopAddr = SOME (pan_Val (Word (pan_state_top_addr s)))) /\
    (pan_eval s BytesInWord = SOME (pan_Val (Word bytes_in_word)))`];;

let pan_eval_def =
  CONV_RULE (DEPTH_CONV BETA_CONV) (REWRITE_RULE[pair_CASE] PSEMAUX_eval_def);;

let pan_eval_ind = cake_ind "pan_eval";;

(* ------------------------------------------------------------------------- *)
(* Memory stores.                                                            *)
(* ------------------------------------------------------------------------- *)

(* HOL4: TODISC: why NONE is returned here on write failure *)

let pan_mem_store_byte_def = cake_def
  `pan_mem_store_byte (m:A word->(A)word_lab) dm be (w:A word) (b:byte) =
     match m (byte_align w) with
       Word v ->
         if byte_align w IN dm
         then SOME ((byte_align w =+ Word (set_byte w b v be)) m)
         else NONE`;;

let pan_write_bytearray_def = cake_def
  `(pan_write_bytearray (a:A word) [] (m:A word->(A)word_lab) dm be = m) /\
   (pan_write_bytearray a (CONS (b:byte) bs) m dm be =
      match pan_mem_store_byte (pan_write_bytearray (word_add a (word 1)) bs m dm be)
              dm be a b with
        SOME m -> m
      | NONE -> m)`;;

let pan_mem_store_32_def = cake_def
  `pan_mem_store_32 (m:A word->(A)word_lab) dm be (w:A word) (hw:int32) =
     if alignment_aligned 2 w
     then match m (byte_align w) with
            Word v ->
              if byte_align w IN dm
              then
                let v0 = set_byte w (get_byte (word 0:int32) hw be) v be in
                let v1 = set_byte (word_add w (word 1)) (get_byte (word 1) hw be)
                           v0 be in
                let v2 = set_byte (word_add w (word 2)) (get_byte (word 2) hw be)
                           v1 be in
                let v3 = set_byte (word_add w (word 3)) (get_byte (word 3) hw be)
                           v2 be in
                  SOME ((byte_align w =+ Word v3) m)
              else NONE
     else NONE`;;

let pan_mem_store_32_alt = prove
 (CASE_TERM `pan_mem_store_32 (m:A word->(A)word_lab) dm be (w:A word) (hw:int32) =
   if alignment_aligned 2 w
   then match m (byte_align w) with
          Word v ->
            if byte_align w IN dm
            then
              if be
              then
                let v0 = set_byte w (word_zx (word_ushr hw 24)) v be in
                let v1 = set_byte (word_add w (word 1)) (word_zx (word_ushr hw 16))
                           v0 be in
                let v2 = set_byte (word_add w (word 2)) (word_zx (word_ushr hw 8))
                           v1 be in
                let v3 = set_byte (word_add w (word 3)) (word_zx hw) v2 be in
                  SOME ((byte_align w =+ Word v3) m)
              else
                let v0 = set_byte w (word_zx hw) v be in
                let v1 = set_byte (word_add w (word 1)) (word_zx (word_ushr hw 8))
                           v0 be in
                let v2 = set_byte (word_add w (word 2)) (word_zx (word_ushr hw 16))
                           v1 be in
                let v3 = set_byte (word_add w (word 3)) (word_zx (word_ushr hw 24))
                           v2 be in
                  SOME ((byte_align w =+ Word v3) m)
            else NONE
   else NONE`,
  REWRITE_TAC[pan_mem_store_32_def; WORDSAUX_get_byte_32] THEN
  BOOL_CASES_TAC `be:bool` THEN REWRITE_TAC[]);;

let pan_mem_store_def = cake_def
  `pan_mem_store (addr:A word) (w:(A)word_lab) dm m =
     if addr IN dm then SOME ((addr =+ w) m) else NONE`;;

let mem_stores_def = cake_def
  `(mem_stores (a:A word) [] dm (m:A word->(A)word_lab) = SOME m) /\
   (mem_stores a (CONS w ws) dm m =
      match pan_mem_store a w dm m with
        SOME m' -> mem_stores (word_add a bytes_in_word) ws dm m'
      | NONE -> NONE)`;;

(* HOL4's termination tactic: fs [MEM_SPLIT, ...]; here a call on a member *)
(* of MAP SND flds is on SND x for some MEM x flds, which                    *)
(* PSEMAUX_MEM_IMP_v_size bounds; then the kit's TERM_TAC                    *)

let PSEMAUX_MEM_IMP_v_size = prove
 (`!(f:A->num) xs (a:mlstring#(A)pan_v).
      MEM a xs ==>
      pan_v_size f (SND a) < list_size (pair_size mlstring_size (pan_v_size f)) xs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`pair_size mlstring_size (pan_v_size (f:A->num))`;
                 `xs:(mlstring#(A)pan_v)list`; `a:mlstring#(A)pan_v`]
                MEM_LIST_SIZE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBST1_TAC(GSYM(ISPEC `a:mlstring#(A)pan_v` PAIR)) THEN
  REWRITE_TAC[pair_size] THEN ARITH_TAC);;

let PSEMAUX_V_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MEM_MAP]) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC)) THEN RVEQ_TAC THEN
  (fun (asl,w as g) ->
     let th0 = ISPEC `ARB:A->num` PSEMAUX_MEM_IMP_v_size in
     MAP_EVERY ASSUME_TAC (mapfilter (fun (_,th) -> MATCH_MP th0 th) asl) g) THEN
  TERM_TAC;;

let flatten_def = cake_def_wf
  `MEASURE (pan_v_size (ARB:A->num))`
  PSEMAUX_V_TC_TAC
  `(flatten (pan_Val (w:(A)word_lab)) = [w]) /\
   (flatten (pan_RStruct vs) = FLAT (MAP flatten vs)) /\
   (flatten (pan_NStruct nm flds) = FLAT (MAP flatten (MAP SND flds)))`;;

let flatten_ind = cake_ind "flatten";;

(* ------------------------------------------------------------------------- *)
(* Variables, clocks, calls.                                                 *)
(* ------------------------------------------------------------------------- *)

let pan_set_var_def = cake_def
  `pan_set_var (v:varname) (value:(A)pan_v) (s:(A,FFI)pan_state) =
     pan_state_locals_fupd (combin_K (pan_state_locals s |+ (v,value))) s`;;

let pan_set_global_def = cake_def
  `pan_set_global (v:varname) (value:(A)pan_v) (s:(A,FFI)pan_state) =
     pan_state_globals_fupd (combin_K (pan_state_globals s |+ (v,value))) s`;;

let pan_set_kvar_def = cake_def
  `pan_set_kvar vk (v:varname) (value:(A)pan_v) (s:(A,FFI)pan_state) =
     match vk with
       panLang_Local -> pan_set_var v value s
     | panLang_Global -> pan_set_global v value s`;;

let pan_lookup_kvar_def = cake_def
  `pan_lookup_kvar vk (v:varname) (s:(A,FFI)pan_state) =
     match vk with
       panLang_Local -> FLOOKUP (pan_state_locals s) v
     | panLang_Global -> FLOOKUP (pan_state_globals s) v`;;

let kvar_simps = prove
 (`(pan_set_kvar panLang_Local v value (s:(A,FFI)pan_state) =
      pan_set_var v value s) /\
   (pan_set_kvar panLang_Global v value s = pan_set_global v value s) /\
   (pan_lookup_kvar panLang_Local v s = FLOOKUP (pan_state_locals s) v) /\
   (pan_lookup_kvar panLang_Global v s = FLOOKUP (pan_state_globals s) v)`,
  SIMP[pan_set_kvar_def; pan_lookup_kvar_def]);;

let _ = cake_add_simps [kvar_simps];;

let pan_upd_locals_def = cake_def
  `pan_upd_locals varargs (s:(A,FFI)pan_state) =
     pan_state_locals_fupd (combin_K (FEMPTY |++ varargs)) s`;;

let pan_empty_locals_def = cake_def
  `pan_empty_locals (s:(A,FFI)pan_state) = pan_state_locals_fupd (combin_K FEMPTY) s`;;

let pan_dec_clock_def = cake_def
  `pan_dec_clock (s:(A,FFI)pan_state) =
     pan_state_clock_fupd (combin_K (pan_state_clock s - 1)) s`;;

let pan_fix_clock_def = cake_def
  `pan_fix_clock (old_s:(A,FFI)pan_state) (res:B,new_s:(A,FFI)pan_state) =
     (res, pan_state_clock_fupd
             (combin_K (if pan_state_clock old_s < pan_state_clock new_s
                 then pan_state_clock old_s else pan_state_clock new_s)) new_s)`;;

let pan_fix_clock_IMP_LESS_EQ = prove
 (`!x. pan_fix_clock (s:(A,FFI)pan_state) x = (res:B,s1)
       ==> pan_state_clock s1 <= pan_state_clock s`,
  REWRITE_TAC[FORALL_PAIR_THM; pan_fix_clock_def; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN SIMP[] THEN ARITH_TAC);;

let pan_lookup_code_def = cake_def
  `pan_lookup_code (code:(funname,(varname#shape)list#(A)panLang_prog#shape)fmap)
                   fname (args:((A)pan_v)list) =
     match FLOOKUP code fname with
       SOME (vshapes,prog,rshape) ->
         if ALL_DISTINCT (MAP FST vshapes) /\
            ALL2 (\vshape arg. SND vshape = shape_of arg) vshapes args
         then SOME (prog, FEMPTY |++ ZIP (MAP FST vshapes) args, rshape)
         else NONE
     | _ -> NONE`;;

let pan_is_valid_value_def = cake_def
  `pan_is_valid_value (s:(A,FFI)pan_state) vk v (value:(A)pan_v) <=>
     match pan_lookup_kvar vk v s with
       SOME w -> shape_of value = shape_of w
     | NONE -> F`;;

let is_valid_value_simps = prove
 (CASE_TERM
  `(pan_is_valid_value (s:(A,FFI)pan_state) panLang_Local v value <=>
      match FLOOKUP (pan_state_locals s) v with
        SOME w -> shape_of value = shape_of w
      | NONE -> F) /\
   (pan_is_valid_value s panLang_Global v value <=>
      match FLOOKUP (pan_state_globals s) v with
        SOME w -> shape_of value = shape_of w
      | NONE -> F)`,
  SIMP[pan_is_valid_value_def; pan_lookup_kvar_def]);;

let is_valid_value_simps2 = prove
 (`(pan_is_valid_value (pan_state_clock_fupd (combin_K k) (s:(A,FFI)pan_state)) vk v vl =
      pan_is_valid_value s vk v vl) /\
   (pan_is_valid_value (pan_state_ffi_fupd (combin_K ffi) s) vk v vl =
      pan_is_valid_value s vk v vl) /\
   (pan_is_valid_value (pan_state_code_fupd (combin_K cd) s) vk v vl =
      pan_is_valid_value s vk v vl) /\
   (pan_is_valid_value (pan_state_memory_fupd (combin_K m) s) vk v vl =
      pan_is_valid_value s vk v vl) /\
   (pan_lookup_kvar vk v (pan_state_clock_fupd (combin_K k) s) = pan_lookup_kvar vk v s) /\
   (pan_lookup_kvar vk v (pan_state_ffi_fupd (combin_K ffi) s) = pan_lookup_kvar vk v s) /\
   (pan_lookup_kvar vk v (pan_state_code_fupd (combin_K cd) s) = pan_lookup_kvar vk v s) /\
   (pan_lookup_kvar vk v (pan_state_memory_fupd (combin_K m) s) = pan_lookup_kvar vk v s)`,
  SIMP[pan_is_valid_value_def; pan_lookup_kvar_def]);;

let _ = cake_add_simps [is_valid_value_simps2];;

let kvar_defs = end_itlist CONJ [pan_set_var_def; pan_set_global_def; pan_set_kvar_def;
                           pan_is_valid_value_def; pan_lookup_kvar_def];;

let pan_res_var_def = cake_def
  `(pan_res_var (lc:(varname,(A)pan_v)fmap) (n,NONE) = lc \\ n) /\
   (pan_res_var lc (n,SOME v) = lc |+ (n,v))`;;

(* the result type of pan_sh_mem_load and pan_sh_mem_store is (B)pan_result *)
(* option, as HOL4 infers it (not tied to the word size A of the state)    *)

let pan_sh_mem_load_def = cake_def
  `pan_sh_mem_load vk (v:varname) (addr:A word) nb (s:(A,FFI)pan_state) =
     if nb = 0 then
       (if addr IN pan_state_sh_memaddrs s then
          (match call_FFI (pan_state_ffi s) (SharedMem MappedRead) [word nb]
                          (word_to_bytes addr F) with
             FFI_final outcome ->
               (SOME (pan_FinalFFI outcome:(B)pan_result), pan_empty_locals s)
           | FFI_return new_ffi new_bytes ->
               (NONE, pan_state_ffi_fupd (combin_K new_ffi)
                        (pan_set_kvar vk v
                           (pan_Val (Word (word_of_bytes F (word 0) new_bytes))) s)))
        else (SOME pan_Error, s))
     else
       (if byte_align addr IN pan_state_sh_memaddrs s then
          (match call_FFI (pan_state_ffi s) (SharedMem MappedRead) [word nb]
                          (word_to_bytes addr F) with
             FFI_final outcome -> (SOME (pan_FinalFFI outcome), pan_empty_locals s)
           | FFI_return new_ffi new_bytes ->
               (NONE, pan_state_ffi_fupd (combin_K new_ffi)
                        (pan_set_kvar vk v
                           (pan_Val (Word (word_of_bytes F (word 0) new_bytes))) s)))
        else (SOME pan_Error, s))`;;

let pan_sh_mem_store_def = cake_def
  `pan_sh_mem_store (w:A word) (addr:A word) nb (s:(A,FFI)pan_state) =
     if nb = 0 then
       (if addr IN pan_state_sh_memaddrs s then
          (match call_FFI (pan_state_ffi s) (SharedMem MappedWrite) [word nb]
                          (APPEND (word_to_bytes w F) (word_to_bytes addr F)) with
             FFI_final outcome -> (SOME (pan_FinalFFI outcome:(B)pan_result), s)
           | FFI_return new_ffi new_bytes -> (NONE, pan_state_ffi_fupd (combin_K new_ffi) s))
        else (SOME pan_Error, s))
     else
       (if byte_align addr IN pan_state_sh_memaddrs s then
          (match call_FFI (pan_state_ffi s) (SharedMem MappedWrite) [word nb]
                          (APPEND (TAKE nb (word_to_bytes w F))
                                  (word_to_bytes addr F)) with
             FFI_final outcome -> (SOME (pan_FinalFFI outcome), s)
           | FFI_return new_ffi new_bytes -> (NONE, pan_state_ffi_fupd (combin_K new_ffi) s))
        else (SOME pan_Error, s))`;;

let nb_op_def = cake_def
  `(nb_op Op8 = 1) /\
   (nb_op Op16 = 2) /\
   (nb_op OpW = 0) /\
   (nb_op Op32 = 4)`;;

(* ------------------------------------------------------------------------- *)
(* The evaluation of programs.                                               *)
(* ------------------------------------------------------------------------- *)

(* HOL4's termination: WF_REL_TAC (inv_image (measure I LEX measure          *)
(* (prog_size (K 0))) (\(xs,s). (s.clock,xs))) >> rw[] >> gvs[set_var_def,  *)
(* upd_locals_def, dec_clock_def, UNCURRY_eq_pair, oneline fix_clock_def,   *)
(* AllCaseEqs()]: the clock does not grow through pan_fix_clock             *)
(* (pan_fix_clock_IMP_LESS_EQ), and decreases at calls and loop iterations. *)

let PSEMAUX_clock_rws =
  [pan_dec_clock_def; pan_set_var_def; pan_state_INFO.ri_accfupds; K_THM; I_THM];;

let PSEMAUX_is_num_fact tm =
  let t = if is_neg tm then dest_neg tm else tm in
  try let h,args = strip_comb t in
      length args = 2 && type_of (hd args) = `:num` &&
      mem (fst(dest_const h)) ["="; "<"; "<="; ">"; ">="]
  with Failure _ -> false;;

let PSEMAUX_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP pan_fix_clock_IMP_LESS_EQ)) THEN
  REPEAT GEN_TAC THEN
  (fun g -> let ths = WF_REL_THMS @ [FST; SND; type_size_def "panLang_prog"] @
                      PSEMAUX_clock_rws in
            (RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths) g) THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (PSEMAUX_is_num_fact o concl))) THEN
  ARITH_TAC;;

let PSEMAUX_evaluate_rel =
  `inv_image (MEASURE I LEX MEASURE (panLang_prog_size (\x:A. 0)))
     (\p:(A)panLang_prog#(A,FFI)pan_state. (pan_state_clock (SND p), FST p))`;;

(* the clauses, parsed in four quotations *)

let PSEMAUX_evaluate_clauses = list_mk_conj
 [`(pan_evaluate (panLang_Skip:(A)panLang_prog, s:(A,FFI)pan_state) =
      (NONE:((A)pan_result)option, s)) /\
   (pan_evaluate (Dec v sh e prog, s) =
      match pan_eval s e with
        SOME value ->
          if sh = shape_of value then
            let (res,st) =
              pan_evaluate (prog, pan_state_locals_fupd
                                    (combin_K (pan_state_locals s |+ (v,value))) s) in
            (res, pan_state_locals_fupd
                    (combin_K (pan_res_var (pan_state_locals st)
                          (v, FLOOKUP (pan_state_locals s) v))) st)
          else (SOME pan_Error, s)
      | NONE -> (SOME pan_Error, s)) /\
   (pan_evaluate (panLang_Assign vk v src, s) =
      match pan_eval s src with
        SOME value ->
          if pan_is_valid_value s vk v value then
            (NONE, pan_set_kvar vk v value s)
          else (SOME pan_Error, s)
      | NONE -> (SOME pan_Error, s)) /\
   (pan_evaluate (Primitive v pop es, s) =
      match OPT_MMAP (pan_eval s) es with
        SOME vs ->
          (match pan_primop pop vs with
             SOME value ->
               if pan_is_valid_value s panLang_Local v value
               then (NONE, pan_set_var v value s)
               else (SOME pan_Error, s)
           | NONE -> (SOME pan_Error, s))
      | _ -> (SOME pan_Error, s)) /\
   (pan_evaluate (panLang_Store dst src, s) =
      match (pan_eval s dst, pan_eval s src) with
        (SOME (pan_Val (Word addr)), SOME value) ->
          (match mem_stores addr (flatten value) (pan_state_memaddrs s)
                   (pan_state_memory s) with
             SOME m -> (NONE, pan_state_memory_fupd (combin_K m) s)
           | NONE -> (SOME pan_Error, s))
      | _ -> (SOME pan_Error, s)) /\
   (pan_evaluate (panLang_Store32 dst src, s) =
      match (pan_eval s dst, pan_eval s src) with
        (SOME (pan_Val (Word adr)), SOME (pan_Val (Word w))) ->
          (match pan_mem_store_32 (pan_state_memory s) (pan_state_memaddrs s)
                   (pan_state_be s) adr (word_zx w) with
             SOME m -> (NONE, pan_state_memory_fupd (combin_K m) s)
           | NONE -> (SOME pan_Error, s))
      | _ -> (SOME pan_Error, s)) /\
   (pan_evaluate (StoreByte dst src, s) =
      match (pan_eval s dst, pan_eval s src) with
        (SOME (pan_Val (Word adr)), SOME (pan_Val (Word w))) ->
          (match pan_mem_store_byte (pan_state_memory s) (pan_state_memaddrs s)
                   (pan_state_be s) adr (word_zx w) with
             SOME m -> (NONE, pan_state_memory_fupd (combin_K m) s)
           | NONE -> (SOME pan_Error, s))
      | _ -> (SOME pan_Error, s)) /\
   (pan_evaluate (ShMemLoad op vk v ad, s) =
      match pan_eval s ad with
        SOME (pan_Val (Word addr)) ->
          (match pan_lookup_kvar vk v s with
             SOME (pan_Val (Word _)) -> pan_sh_mem_load vk v addr (nb_op op) s
           | _ -> (SOME pan_Error, s))
      | _ -> (SOME pan_Error, s)) /\
   (pan_evaluate (ShMemStore op ad e, s) =
      match (pan_eval s ad, pan_eval s e) with
        (SOME (pan_Val (Word addr)), SOME (pan_Val (Word bytes))) ->
          pan_sh_mem_store bytes addr (nb_op op) s
      | _ -> (SOME pan_Error, s))`;
  `(pan_evaluate (panLang_Seq c1 c2:(A)panLang_prog, s:(A,FFI)pan_state) =
      let (res,s1) = pan_fix_clock s (pan_evaluate (c1,s)) in
      if res = NONE then pan_evaluate (c2,s1) else (res,s1)) /\
   (pan_evaluate (panLang_If e c1 c2, s) =
      match pan_eval s e with
        SOME (pan_Val (Word w)) ->
          pan_evaluate ((if ~(w = word 0) then c1 else c2), s)
      | _ -> (SOME pan_Error, s)) /\
   (pan_evaluate (panLang_Break, s) = (SOME pan_Break, s)) /\
   (pan_evaluate (panLang_Continue, s) = (SOME pan_Continue, s)) /\
   (pan_evaluate (While e c, s) =
      match pan_eval s e with
        SOME (pan_Val (Word w)) ->
          if ~(w = word 0) then
            (if pan_state_clock s = 0 then (SOME pan_TimeOut, pan_empty_locals s)
             else
               let (res,s1) = pan_fix_clock (pan_dec_clock s)
                                (pan_evaluate (c, pan_dec_clock s)) in
               match res with
                 SOME pan_Continue -> pan_evaluate (While e c, s1)
               | NONE -> pan_evaluate (While e c, s1)
               | SOME pan_Break -> (NONE, s1)
               | _ -> (res, s1))
          else (NONE, s)
      | _ -> (SOME pan_Error, s)) /\
   (pan_evaluate (panLang_Return e, s) =
      match pan_eval s e with
        SOME value ->
          if size_of_sh_with_ctxt (pan_state_structs s) (shape_of value) <= 32
          then (SOME (pan_Return value), pan_empty_locals s)
          else (SOME pan_Error, s)
      | _ -> (SOME pan_Error, s)) /\
   (pan_evaluate (panLang_Raise eid e, s) =
      match (FLOOKUP (pan_state_eshapes s) eid, pan_eval s e) with
        (SOME sh, SOME value) ->
          if shape_of value = sh /\
             size_of_sh_with_ctxt (pan_state_structs s) (shape_of value) <= 32
          then (SOME (pan_Exception eid value), pan_empty_locals s)
          else (SOME pan_Error, s)
      | _ -> (SOME pan_Error, s)) /\
   (pan_evaluate (panLang_Tick, s) =
      if pan_state_clock s = 0 then (SOME pan_TimeOut, pan_empty_locals s)
      else (NONE, pan_dec_clock s)) /\
   (pan_evaluate (Annot _ _, s) = (NONE, s))`;
  `pan_evaluate (panLang_Call caltyp fname argexps:(A)panLang_prog,
                 s:(A,FFI)pan_state) =
     match OPT_MMAP (pan_eval s) argexps with
       SOME args ->
         (match pan_lookup_code (pan_state_code s) fname args with
            SOME (prog, newlocals, return_sh) ->
              if pan_state_clock s = 0 then (SOME pan_TimeOut, pan_empty_locals s)
              else
              let eval_prog =
                pan_fix_clock (pan_state_locals_fupd (combin_K newlocals) (pan_dec_clock s))
                  (pan_evaluate (prog, pan_state_locals_fupd (combin_K newlocals)
                                         (pan_dec_clock s))) in
              (match eval_prog with
                 (NONE,st) -> (SOME pan_Error, st)
               | (SOME pan_Break,st) -> (SOME pan_Error, st)
               | (SOME pan_Continue,st) -> (SOME pan_Error, st)
               | (SOME (pan_Return retv),st) ->
                   (if ~(shape_of retv = return_sh) then (SOME pan_Error, st) else
                    (match caltyp with
                       NONE -> (SOME (pan_Return retv), pan_empty_locals st)
                     | SOME (NONE, _) ->
                         (NONE, pan_state_locals_fupd (combin_K (pan_state_locals s)) st)
                     | SOME (SOME (rk, rt), _) ->
                         if pan_is_valid_value s rk rt retv
                         then (NONE, pan_set_kvar rk rt retv
                                       (pan_state_locals_fupd
                                          (combin_K (pan_state_locals s)) st))
                         else (SOME pan_Error, st)))
               | (SOME (pan_Exception eid exn),st) ->
                   (match caltyp with
                      NONE -> (SOME (pan_Exception eid exn), pan_empty_locals st)
                    | SOME (_, NONE) ->
                        (SOME (pan_Exception eid exn), pan_empty_locals st)
                    | SOME (_, SOME (eid', evar, p)) ->
                        if eid = eid' then
                          (match FLOOKUP (pan_state_eshapes s) eid with
                             SOME sh ->
                               if shape_of exn = sh /\
                                  pan_is_valid_value s panLang_Local evar exn then
                                 pan_evaluate (p, pan_set_var evar exn
                                                    (pan_state_locals_fupd
                                                       (combin_K (pan_state_locals s)) st))
                               else (SOME pan_Error, st)
                           | NONE -> (SOME pan_Error, st))
                        else (SOME (pan_Exception eid exn), pan_empty_locals st))
               | (res,st) -> (res, pan_empty_locals st))
          | _ -> (SOME pan_Error, s))
     | _ -> (SOME pan_Error, s)`;
  `(pan_evaluate (DecCall rt shape fname argexps prog1:(A)panLang_prog,
                  s:(A,FFI)pan_state) =
      match OPT_MMAP (pan_eval s) argexps with
        SOME args ->
          (match pan_lookup_code (pan_state_code s) fname args with
             SOME (prog, newlocals, return_sh) ->
               (if pan_state_clock s = 0 then (SOME pan_TimeOut, pan_empty_locals s)
                else
                let eval_prog =
                  pan_fix_clock (pan_state_locals_fupd (combin_K newlocals) (pan_dec_clock s))
                    (pan_evaluate (prog, pan_state_locals_fupd (combin_K newlocals)
                                           (pan_dec_clock s))) in
                (match eval_prog with
                   (NONE,st) -> (SOME pan_Error, st)
                 | (SOME pan_Break,st) -> (SOME pan_Error, st)
                 | (SOME pan_Continue,st) -> (SOME pan_Error, st)
                 | (SOME (pan_Return retv),st) ->
                     (if shape_of retv = shape /\ shape_of retv = return_sh then
                        let (res',st') =
                          pan_evaluate (prog1, pan_set_var rt retv
                                                 (pan_state_locals_fupd
                                                    (combin_K (pan_state_locals s)) st)) in
                        (res', pan_state_locals_fupd
                                 (combin_K (pan_res_var (pan_state_locals st')
                                       (rt, FLOOKUP (pan_state_locals s) rt))) st')
                      else (SOME pan_Error, st))
                 | (res,st) -> (res, pan_empty_locals st)))
           | _ -> (SOME pan_Error, s))
      | _ -> (SOME pan_Error, s)) /\
   (pan_evaluate (panLang_ExtCall ffi_index ptr1 len1 ptr2 len2, s) =
      match (pan_eval s ptr1, pan_eval s len1, pan_eval s ptr2, pan_eval s len2) with
        (SOME (pan_Val (Word sz1)), SOME (pan_Val (Word ad1)),
         SOME (pan_Val (Word sz2)), SOME (pan_Val (Word ad2))) ->
          (match (read_bytearray sz1 (val ad1)
                    (pan_mem_load_byte (pan_state_memory s) (pan_state_memaddrs s)
                                       (pan_state_be s)),
                  read_bytearray sz2 (val ad2)
                    (pan_mem_load_byte (pan_state_memory s) (pan_state_memaddrs s)
                                       (pan_state_be s))) with
             (SOME bytes, SOME bytes2) ->
               (match call_FFI (pan_state_ffi s) (ExtCall ffi_index) bytes bytes2 with
                  FFI_final outcome ->
                    (SOME (pan_FinalFFI outcome), pan_empty_locals s)
                | FFI_return new_ffi new_bytes ->
                    let nmem = pan_write_bytearray sz2 new_bytes (pan_state_memory s)
                                 (pan_state_memaddrs s) (pan_state_be s) in
                    (NONE, pan_state_memory_fupd (combin_K nmem)
                             (pan_state_ffi_fupd (combin_K new_ffi) s)))
           | _ -> (SOME pan_Error, s))
      | res -> (SOME pan_Error, s))`];;

(* HOL4 evaluate_def and evaluate_ind (the first ones, with fix_clock) *)

let PSEMAUX_evaluate_fix_def =
  cake_def_wf PSEMAUX_evaluate_rel PSEMAUX_TC_TAC PSEMAUX_evaluate_clauses;;

let PSEMAUX_evaluate_fix_ind = cake_ind "pan_evaluate";;

let vshapes_args_rel_imp_eq_len_MAP = prove
 (`!vshapes (args:((A)pan_v)list).
     ALL2 (\vshape arg. SND vshape = shape_of arg) (vshapes:(varname#shape)list) args
     ==> LENGTH vshapes = LENGTH args /\ MAP SND vshapes = MAP shape_of args`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; LENGTH; MAP; SUC_INJ; CONS_11] THEN ASM_MESON_TAC[]);;

(* HOL4 (commented out): evaluate_main_def *)

let pan_evaluate_clock = prove
 (`!prog (s:(A,FFI)pan_state) r s'.
     pan_evaluate (prog,s) = (r,s') ==> pan_state_clock s' <= pan_state_clock s`,
  REC_IND_TAC PSEMAUX_evaluate_fix_ind THEN REPEAT STRIP_TAC THEN
  QPAT_X_ASSUM "pan_evaluate _ = _" MP_TAC THEN
  RW[ONCE PSEMAUX_evaluate_fix_def] THEN
  GVS(all_case_eqs() @
      [pan_set_var_def; pan_set_global_def; pan_upd_locals_def;
       pan_empty_locals_def; pan_dec_clock_def; pan_sh_mem_load_def;
       pan_sh_mem_store_def; pan_lookup_kvar_def; ONELINE pan_fix_clock_def;
       pan_set_kvar_def]) THEN
  DECIDE_TAC);;

let pan_fix_clock_evaluate = prove
 (`pan_fix_clock (s:(A,FFI)pan_state) (pan_evaluate (prog,s)) =
   pan_evaluate (prog,s)`,
  QCASES_ON "pan_evaluate (prog,s)" THEN FS[pan_fix_clock_def] THEN
  IMP_RES_TAC pan_evaluate_clock THEN
  FS[GSYM NOT_LT; pan_state_component_equality]);;

(* we save evaluate theorems without fix_clock *)

(* HOL4: evaluate_ind[allow_rebind] = REWRITE_RULE [fix_clock_evaluate]     *)
(* evaluate_ind *)

let pan_evaluate_ind = REWRITE_RULE[pan_fix_clock_evaluate] PSEMAUX_evaluate_fix_ind;;

(* HOL4: evaluate_def[allow_rebind,compute] = REWRITE_RULE                  *)
(* [fix_clock_evaluate] evaluate_def *)

let pan_evaluate_def = REWRITE_RULE[pan_fix_clock_evaluate] PSEMAUX_evaluate_fix_def;;

let () = cake_ind_store := ("pan_evaluate",pan_evaluate_ind) :: !cake_ind_store;;

(* ------------------------------------------------------------------------- *)
(* Observational semantics.                                                  *)
(* ------------------------------------------------------------------------- *)

let pan_semantics_def = cake_def
  `pan_semantics (s:(A,FFI)pan_state) start =
     let prog = panLang_Call NONE start [] in
     if ?k. match FST (pan_evaluate (prog, pan_state_clock_fupd (combin_K k) s)) with
              SOME pan_TimeOut -> F
            | SOME (pan_FinalFFI _) -> F
            | SOME (pan_Return _) -> F
            | _ -> T
     then Fail
     else
       match (some res.
                ?k t r outcome.
                  pan_evaluate (prog, pan_state_clock_fupd (combin_K k) s) = (r,t) /\
                  (match r with
                     SOME (pan_FinalFFI e) -> outcome = FFI_outcome e
                   | SOME (pan_Return _) -> outcome = Success
                   | _ -> F) /\
                  res = Terminate outcome (ffi_state_io_events (pan_state_ffi t))) with
         SOME res -> res
       | NONE ->
           Diverge
             (build_lprefix_lub
                (IMAGE (\k. llist_fromList
                              (ffi_state_io_events
                                 (pan_state_ffi
                                    (SND (pan_evaluate
                                            (prog, pan_state_clock_fupd (combin_K k) s))))))
                       (:num)))`;;

(* ------------------------------------------------------------------------- *)
(* Declaration semantics.                                                    *)
(* ------------------------------------------------------------------------- *)

let evaluate_decls_def = cake_def
  `(evaluate_decls (s:(A,FFI)pan_state) [] = SOME s) /\
   (evaluate_decls s (CONS (Name nm flds) ds) = evaluate_decls s ds) /\
   (evaluate_decls s (CONS (Decl sh v e) ds) =
      match pan_eval (pan_state_locals_fupd (combin_K FEMPTY) s) e with
        SOME res ->
          (if sh = shape_of res then
             evaluate_decls
               (pan_state_globals_fupd (combin_K (pan_state_globals s |+ (v,res))) s) ds
           else NONE)
      | NONE -> NONE) /\
   (evaluate_decls s (CONS (Function fi) ds) =
      if ALL (is_wf_shape (pan_state_structs s) o SND) (fun_decl_params fi) /\
         is_wf_shape (pan_state_structs s) (fun_decl_return fi) then
        evaluate_decls
          (pan_state_code_fupd
             (combin_K (pan_state_code s |+
                   (fun_decl_name fi,
                    (fun_decl_params fi,(fun_decl_body fi,fun_decl_return fi))))) s)
          ds
      else NONE) /\
   (evaluate_decls s (CONS (ExnDecl eid sh) ds) =
      if FLOOKUP (pan_state_eshapes s) eid = NONE /\
         is_wf_shape (pan_state_structs s) sh then
        evaluate_decls (pan_state_eshapes_fupd (combin_K (pan_state_eshapes s |+ (eid,sh))) s)
          ds
      else NONE)`;;

let evaluate_decls_ind = cake_ind "evaluate_decls";;

let decs_stcnames_def = cake_def
  `(decs_stcnames (st_ctxt:(stcname#struct_info)list) ([]:((A)decl)list) =
      SOME st_ctxt) /\
   (decs_stcnames st_ctxt (CONS (Name nm flds) ds) =
      match ALOOKUP st_ctxt nm with
        SOME info -> NONE
      | NONE ->
          if ALL_DISTINCT (MAP FST flds) then
            let shs = MAP SND flds in
            if ALL (is_wf_shape st_ctxt) shs then
              let info = struct_info_REC flds (size_of_sh_with_ctxt st_ctxt (Comb shs)) in
              decs_stcnames (CONS (nm,info) st_ctxt) ds
            else NONE
          else NONE) /\
   (decs_stcnames st_ctxt (CONS (Decl sh v e) ds) = decs_stcnames st_ctxt ds) /\
   (decs_stcnames st_ctxt (CONS (Function fi) ds) = decs_stcnames st_ctxt ds) /\
   (decs_stcnames st_ctxt (CONS (ExnDecl eid sh) ds) = decs_stcnames st_ctxt ds)`;;

let decs_stcnames_ind = cake_ind "decs_stcnames";;

let semantics_decls_def = cake_def
  `semantics_decls (s:(A,FFI)pan_state) start (decls:((A)decl)list) =
     match decs_stcnames [] decls with
       NONE -> Fail
     | SOME st_ctxt ->
         match evaluate_decls (pan_state_structs_fupd (combin_K st_ctxt) s) decls with
           NONE -> Fail
         | SOME s' -> pan_semantics s' start`;;
