(* ========================================================================= *)
(* word_gcFunctions: port of HOL4                                            *)
(* compiler/backend/proofs/word_gcFunctionsScript.sml (CakeML v3479).        *)
(* Shallow embedding of garbage collector implementation.                   *)
(*                                                                           *)
(* Notes on the port:                                                        *)
(* - HOL4 shift (:'a) (backend_common word_shift) is                        *)
(*   backend_common_word_shift (:A); HOL4 (h -- l) w is word_bits h l w;     *)
(*   HOL4 word_bit i w is bit i w.                                           *)
(* - HOL4 conf with <| has_fp_ops := b1; has_fp_tern := b2 |> is             *)
(*   data_to_word_config_has_fp_ops_fupd (K b1)                              *)
(*     (data_to_word_config_has_fp_tern_fupd (K b2) conf).                   *)
(* - HOL4 gc_fun_type (wordSem) is written out in full.                      *)
(* - The functions that recurse on a word or a counter are defined with     *)
(*   cake_def_wf and the measure that HOL4 finds by itself.                  *)
(* - WSIMPPAUX_ names are local helpers of this file.                        *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/proofs/word_simpProof.ml";;

prioritize_num();;
type_invention_error := true;;

(* move candidates *)

let bytes_in_word_mul_eq_shift = prove
 (`good_dimindex (:A) ==>
   word_mul bytes_in_word (w:A word) = word_shl w (backend_common_word_shift (:A))`,
  REWRITE_TAC[good_dimindex_def; bytes_in_word_def; backend_common_word_shift_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[WORD_MUL_LSL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

(* HOL4: word_or_eq_0 *)

let word_gcFunctions_word_or_eq_0 = prove
 (`word_or (w:A word) v = word 0 <=> w = word 0 /\ v = word 0`,
  REWRITE_TAC[WORD_OR_EQ_0]);;

let shift_length_has_fp_ops = prove
 (`shift_length (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                   (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) =
   shift_length conf`,
  SIMP[shift_length_def]);;

cake_add_simps [shift_length_has_fp_ops];;

(* ------------------------------------------------------------------------- *)
(* definition and verification of GC functions                              *)
(* ------------------------------------------------------------------------- *)

let ptr_to_addr_def = cake_def
  `ptr_to_addr (conf:data_to_word_config) (base:A word) (w:A word) =
     word_add base (word_mul (word_ushr w (shift_length conf)) bytes_in_word)`;;

let update_addr_def = cake_def
  `update_addr (conf:data_to_word_config) (fwd_ptr:A word) (old_addr:A word) =
     word_or (word_shl fwd_ptr (shift_length conf))
             (word_bits (small_shift_length conf - 1) 0 old_addr)`;;

(* termination: HOL4 finds the measure val w by itself *)

let WSIMPPAUX_val_word_pred = prove
 (`!w:A word. ~(w = word 0) ==> val (word_sub w (word 1)) < val w`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_SUB_CASES; VAL_WORD_1] THEN
  DISCH_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* as in HOL4, the counter w may have another word size, and the memory    *)
(* m any range type                                                        *)

let memcpy_def = cake_def_wf
  `MEASURE (\x:B word#A word#A word#(A word->C)#(A word->bool). val (FST x))`
  (REWRITE_TAC[measure_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[LT_TRANS; WSIMPPAUX_val_word_pred])
  `memcpy (w:B word) (a:A word) (b:A word) (m:A word->C) (dm:A word->bool) =
     if w = word 0 then (b,m,T) else
       let (b1,m1,c1) = memcpy (word_sub w (word 1)) (word_add a bytes_in_word)
                          (word_add b bytes_in_word) ((b =+ m a) m) dm in
         (b1,m1,(c1 /\ a IN dm /\ b IN dm))`;;

(* decode_length is also used by the data_to_word proofs *)

let decode_length_def = cake_def
  `decode_length (conf:data_to_word_config) (w:A word) =
     word_ushr w (dimindex (:A) - data_to_word_config_len_size conf)`;;

let word_gc_move_def = cake_def
  `(word_gc_move (conf:data_to_word_config)
     (wl_Loc l1 l2,i:A word,pa:A word,old:A word,m:A word->(A)word_loc,
      dm:A word->bool) = (wl_Loc l1 l2,i,pa,m,(l2 = 0))) /\
   (word_gc_move conf (wl_Word w,i,pa,old,m,dm) =
      if word_and w (word 1) = word 0 then (wl_Word w,i,pa,m,T) else
        let c = (ptr_to_addr conf old w IN dm) in
        let v = m (ptr_to_addr conf old w) in
          if is_fwd_ptr v then
            (wl_Word (update_addr conf (word_ushr (theWord v) 2) w),i,pa,m,c)
          else
            let header_addr = ptr_to_addr conf old w in
            let c = (c /\ header_addr IN dm /\ isWord (m header_addr)) in
            let len = decode_length conf (theWord (m header_addr)) in
            let v = word_add (word_add i len) (word 1) in
            let (pa1,m1,c1) = memcpy (word_add len (word 1)) header_addr pa m dm in
            let c = (c /\ header_addr IN dm /\ c1) in
            let m1 = (header_addr =+ wl_Word (word_shl i 2)) m1 in
              (wl_Word (update_addr conf i w),v,pa1,m1,c))`;;

let word_gen_gc_partial_move_def = cake_def
  `(word_gen_gc_partial_move (conf:data_to_word_config)
     (wl_Loc l1 l2,i:A word,pa:A word,old:A word,m:A word->(A)word_loc,
      dm:A word->bool,gs:A word,rs:A word) = (wl_Loc l1 l2,i,pa,m,(l2 = 0))) /\
   (word_gen_gc_partial_move conf (wl_Word w,i,pa,old,m,dm,gs,rs) =
      if word_and w (word 1) = word 0 then (wl_Word w,i,pa,m,T) else
        let header_addr = ptr_to_addr conf old w in
        let tmp = word_sub header_addr old in
          if word_ult tmp gs \/ word_ule rs tmp then
            (wl_Word w,i,pa,m,T)
          else
            let c = (ptr_to_addr conf old w IN dm) in
            let v = m (ptr_to_addr conf old w) in
              if is_fwd_ptr v then
                (wl_Word (update_addr conf (word_ushr (theWord v) 2) w),i,pa,m,c)
              else
                let c = (c /\ header_addr IN dm /\ isWord (m header_addr)) in
                let len = decode_length conf (theWord (m header_addr)) in
                let v = word_add (word_add i len) (word 1) in
                let (pa1,m1,c1) = memcpy (word_add len (word 1)) header_addr pa m dm in
                let c = (c /\ header_addr IN dm /\ c1) in
                let m1 = (header_addr =+ wl_Word (word_shl i 2)) m1 in
                  (wl_Word (update_addr conf i w),v,pa1,m1,c))`;;

let word_gc_move_roots_def = cake_def
  `(word_gc_move_roots (conf:data_to_word_config)
     ([],i:A word,pa:A word,old:A word,m:A word->(A)word_loc,dm:A word->bool) =
     ([],i,pa,m,T)) /\
   (word_gc_move_roots conf (CONS w ws,i,pa,old,m,dm) =
      let (w1,i1,pa1,m1,c1) = word_gc_move conf (w,i,pa,old,m,dm) in
      let (ws2,i2,pa2,m2,c2) = word_gc_move_roots conf (ws,i1,pa1,old,m1,dm) in
        (CONS w1 ws2,i2,pa2,m2,(c1 /\ c2)))`;;

let word_gc_move_roots_ind = cake_ind "word_gc_move_roots";;

let word_gc_move_list_def = cake_def_wf
  `MEASURE (\x:data_to_word_config#A word#A word#A word#A word#A word#
               (A word->(A)word_loc)#(A word->bool). val (FST (SND (SND x))))`
  (REWRITE_TAC[measure_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[LT_TRANS; WSIMPPAUX_val_word_pred])
  `word_gc_move_list (conf:data_to_word_config)
     (a:A word,l:A word,i:A word,pa:A word,old:A word,m:A word->(A)word_loc,
      dm:A word->bool) =
     if l = word 0 then (a,i,pa,m,T) else
       let w = (m a):(A)word_loc in
       let (w1,i1,pa1,m1,c1) = word_gc_move conf (w,i,pa,old,m,dm) in
       let m1 = (a =+ w1) m1 in
       let (a2,i2,pa2,m2,c2) = word_gc_move_list conf
             (word_add a bytes_in_word,word_sub l (word 1),i1,pa1,old,m1,dm) in
         (a2,i2,pa2,m2,(a IN dm /\ c1 /\ c2))`;;

let word_gc_move_list_ind = cake_ind "word_gc_move_list";;

let word_gen_gc_partial_move_roots_def = cake_def
  `(word_gen_gc_partial_move_roots (conf:data_to_word_config)
     ([],i:A word,pa:A word,old:A word,m:A word->(A)word_loc,dm:A word->bool,
      gs:A word,rs:A word) = ([],i,pa,m,T)) /\
   (word_gen_gc_partial_move_roots conf (CONS w ws,i,pa,old,m,dm,gs,rs) =
      let (w1,i1,pa1,m1,c1) = word_gen_gc_partial_move conf (w,i,pa,old,m,dm,gs,rs) in
      let (ws2,i2,pa2,m2,c2) =
            word_gen_gc_partial_move_roots conf (ws,i1,pa1,old,m1,dm,gs,rs) in
        (CONS w1 ws2,i2,pa2,m2,(c1 /\ c2)))`;;

let word_gen_gc_partial_move_roots_ind = cake_ind "word_gen_gc_partial_move_roots";;

let word_gen_gc_partial_move_list_def = cake_def_wf
  `MEASURE (\x:data_to_word_config#A word#A word#A word#A word#A word#
               (A word->(A)word_loc)#(A word->bool)#A word#A word.
              val (FST (SND (SND x))))`
  (REWRITE_TAC[measure_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[LT_TRANS; WSIMPPAUX_val_word_pred])
  `word_gen_gc_partial_move_list (conf:data_to_word_config)
     (a:A word,l:A word,i:A word,pa:A word,old:A word,m:A word->(A)word_loc,
      dm:A word->bool,gs:A word,rs:A word) =
     if l = word 0 then (a,i,pa,m,T) else
       let w = (m a):(A)word_loc in
       let (w1,i1,pa1,m1,c1) = word_gen_gc_partial_move conf (w,i,pa,old,m,dm,gs,rs) in
       let m1 = (a =+ w1) m1 in
       let (a2,i2,pa2,m2,c2) = word_gen_gc_partial_move_list conf
             (word_add a bytes_in_word,word_sub l (word 1),i1,pa1,old,m1,dm,gs,rs) in
         (a2,i2,pa2,m2,(a IN dm /\ c1 /\ c2))`;;

let word_gen_gc_partial_move_list_ind = cake_ind "word_gen_gc_partial_move_list";;

let word_gen_gc_partial_move_list_zero = prove
 (`word_gen_gc_partial_move_list (conf:data_to_word_config)
     (a:A word,word 0,i:A word,pa:A word,old:A word,m:A word->(A)word_loc,
      dm:A word->bool,gs:A word,rs:A word) = (a,i,pa,m,T)`,
  GEN_REWRITE_TAC LAND_CONV [word_gen_gc_partial_move_list_def] THEN
  REWRITE_TAC[]);;

let word_gen_gc_partial_move_list_suc = prove
 (CASE_TERM
  `word_gen_gc_partial_move_list (conf:data_to_word_config)
     (a:A word,(word (SUC l):A word),i:A word,pa:A word,old:A word,
      m:A word->(A)word_loc,dm:A word->bool,gs:A word,rs:A word) =
   if word (SUC l) = (word 0:A word) then (a,i,pa,m,T) else
     let w = m a in
     let (w1,i1,pa1,m1,c1) = word_gen_gc_partial_move conf (w,i,pa,old,m,dm,gs,rs) in
     let m1 = (a =+ w1) m1 in
     let (a2,i2,pa2,m2,c2) = word_gen_gc_partial_move_list conf
           (word_add a bytes_in_word,word l,i1,pa1,old,m1,dm,gs,rs) in
       (a2,i2,pa2,m2,(a IN dm /\ c1 /\ c2))`,
  GEN_REWRITE_TAC LAND_CONV [word_gen_gc_partial_move_list_def] THEN
  REWRITE_TAC[n2w_SUC; WORD_ADD_SUB]);;

(* split the first call of the constant cname that does not contain bound   *)
(* variables: it is abstracted to a tuple of new variables, as with HOL4's  *)
(* pairarg_tac on all its occurrences                                        *)

let WSIMPPAUX_GC_ABS_TAC (cname:string) : tactic = fun (asl,w as g) ->
  let is_cand t =
    is_comb t &&
    (let h,_ = strip_comb t in is_const h && fst(dest_const h) = cname) &&
    free_in t w in
  let t = find_term is_cand w in
  let v = variant (frees w) (mk_var("r",type_of t)) in
  (SPEC_TAC(t,v) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
   CAKE_REWRITE_TAC[]) g;;

(* the kit's PAIRARG_TAC, but only for a pair_CASE whose scrutinee is not   *)
(* itself a case expression: nested lets are split from the inside out      *)

let WSIMPPAUX_PAIRARG_TAC : tactic =
  fun (asl,w as gl) ->
    let whole = list_mk_conj(w :: map (concl o snd) asl) in
    let is_cand t =
      is_case_app t &&
      (let c,x,fs = dest_case_app t in
       fst(dest_const c) = "pair_CASE" && not (is_pair x) &&
       not (is_case_app x) && free_in x whole) in
    let t = find_term is_cand whole in
    let _,x,fs = dest_case_app t in
    let f = hd fs in
    let tya,tyb = match dest_type(type_of x) with
        "prod",[a;b] -> a,b | _ -> failwith "WSIMPPAUX_PAIRARG_TAC" in
    let n1,n2 =
      try let a,b = dest_abs f in let b1,_ = dest_abs b in
          fst(dest_var a),fst(dest_var b1)
      with Failure _ -> "p1","p2" in
    let avoid = itlist (union o thm_frees o snd) asl (frees whole) in
    let v1 = variant avoid (mk_var(n1,tya)) in
    let v2 = variant (v1::avoid) (mk_var(n2,tyb)) in
    let nch = ISPEC x (nchotomy_of_type (type_of x)) in
    (MP_TAC nch THEN
     DISCH_THEN(X_CHOOSE_THEN v1 (X_CHOOSE_THEN v2
       (fun th -> if is_var x then SUBST_ALL_TAC th
                  else SUBST_ALL_TAC th THEN ASSUME_TAC th))) THEN
     CASE_ASM_TIDY_TAC THEN CAKE_REWRITE_TAC[]) gl;;

let word_gen_gc_partial_move_list_append = prove
 (CASE_TERM
  `!a l l' i pa old m dm gs rs conf.
     l + l' < dimword (:A) ==>
     word_gen_gc_partial_move_list (conf:data_to_word_config)
       (a:A word,(word (l + l'):A word),i:A word,pa:A word,old:A word,
        m:A word->(A)word_loc,dm:A word->bool,gs:A word,rs:A word) =
     let (a2,i2,pa2,m2,c2) =
           word_gen_gc_partial_move_list conf (a,word l,i,pa,old,m,dm,gs,rs) in
     let (a3,i3,pa3,m3,c3) =
           word_gen_gc_partial_move_list conf (a2,word l',i2,pa2,old,m2,dm,gs,rs) in
       (a3,i3,pa3,m3,(c2 /\ c3))`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; word_gen_gc_partial_move_list_zero] THEN
    DISCH_TAC THEN CAKE_REWRITE_TAC[] THEN
    WSIMPPAUX_GC_ABS_TAC "word_gen_gc_partial_move_list" THEN REWRITE_TAC[];
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
    SUBGOAL_THEN `l + l' < dimword(:A) /\ SUC l < dimword(:A)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[word_gen_gc_partial_move_list_suc; LBIGAUX_WORD_SUC_NZ] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    WSIMPPAUX_GC_ABS_TAC "word_gen_gc_partial_move" THEN
    WSIMPPAUX_GC_ABS_TAC "word_gen_gc_partial_move_list" THEN
    WSIMPPAUX_GC_ABS_TAC "word_gen_gc_partial_move_list" THEN
    REWRITE_TAC[PAIR_EQ; CONJ_ACI]]);;

let word_gc_move_loop_def = cake_def_wf
  `MEASURE (\x:num#data_to_word_config#A word#A word#A word#A word#
               (A word->(A)word_loc)#(A word->bool)#bool. FST x)`
  (REWRITE_TAC[measure_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[LT_TRANS; ARITH_RULE `!k. ~(k = 0) ==> k - 1 < k`])
  `word_gc_move_loop k (conf:data_to_word_config)
     (pb:A word,i:A word,pa:A word,old:A word,m:A word->(A)word_loc,
      dm:A word->bool,c:bool) =
     if pb = pa then (i,pa,m,c) else
     if k = 0 then (i,pa,m,F) else
       let w = m pb in
       let c = (c /\ pb IN dm /\ isWord w) in
       let len = decode_length conf (theWord w) in
         if bit 2 (theWord w) then
           let pb = word_add pb (word_mul (word_add len (word 1)) bytes_in_word) in
             word_gc_move_loop (k - 1) conf (pb,i,pa,old,m,dm,c)
         else
           let pb = word_add pb bytes_in_word in
           let (pb,i1,pa1,m1,c1) = word_gc_move_list conf (pb,len,i,pa,old,m,dm) in
             word_gc_move_loop (k - 1) conf (pb,i1,pa1,old,m1,dm,(c /\ c1))`;;

let word_full_gc_def = cake_def
  `word_full_gc (conf:data_to_word_config)
     (all_roots,new:A word,old:A word,m:A word->(A)word_loc,dm:A word->bool) =
     let (rs,i1,pa1,m1,c1) = word_gc_move_roots conf (all_roots,word 0,new,old,m,dm) in
     let (i1,pa1,m1,c2) =
           word_gc_move_loop (dimword(:A)) conf (new,i1,pa1,old,m1,dm,c1)
     in (rs,i1,pa1,m1,c2)`;;

let word_gc_fun_assum_def = cake_def
  `word_gc_fun_assum (conf:data_to_word_config) (s:(store_name,(A)word_loc)fmap) <=>
     {Globals, CurrHeap, OtherHeap, HeapLength,
      TriggerGC, GenStart, EndOfHeap} SUBSET FDOM s /\
     isWord (FAPPLY s OtherHeap) /\
     isWord (FAPPLY s CurrHeap) /\
     isWord (FAPPLY s TriggerGC) /\
     isWord (FAPPLY s HeapLength) /\
     isWord (FAPPLY s GenStart) /\
     isWord (FAPPLY s EndOfHeap) /\
     isWord (FAPPLY s Globals) /\
     good_dimindex (:A) /\
     ~(data_to_word_config_len_size conf = 0) /\
     data_to_word_config_len_size conf + 2 < dimindex (:A) /\
     shift_length conf < dimindex (:A)`;;

(* A partial collection is allowed if the last condition is true. This    *)
(* condition guarantees that even if nothing is collected by the partial  *)
(* collection, the requested space still exists.                          *)

let word_gen_gc_can_do_partial_def = cake_def
  `word_gen_gc_can_do_partial (gen_sizes:B list) (s:(store_name,(A)word_loc)fmap) <=>
     ~(gen_sizes = []) /\
     let allo = theWord (FAPPLY s AllocSize) in
     let trig = theWord (FAPPLY s TriggerGC) in
     let endh = theWord (FAPPLY s EndOfHeap) in
       word_ule allo (word_sub endh trig)`;;

(* the cases: allocation smaller than gen; allocation too big; aligned    *)
(* (should always be the case); otherwise (very unlikely, a bad choice)   *)

let new_trig_def = cake_def
  `new_trig (heap_space:A word) (alloc_pref:A word) gs =
     let a = val alloc_pref in
     let g = val ((get_gen_size gs):A word) in
     let h = val heap_space in
       if a <= g then word (MIN h g) else
       if h < a then word h else
       if byte_aligned alloc_pref
       then alloc_pref else word h`;;

let refs_to_addresses_def = cake_def
  `(refs_to_addresses ([]:((A,B)heap_element)list) = []:(A heap_address)list) /\
   (refs_to_addresses (CONS (DataElement ptrs _ _) refs) =
      APPEND ptrs (refs_to_addresses refs)) /\
   (refs_to_addresses (CONS _ refs) = refs_to_addresses refs)`;;

let word_gen_gc_partial_move_ref_list_def = cake_def_wf
  `MEASURE (\x:num#data_to_word_config#A word#A word#A word#A word#
               (A word->(A)word_loc)#(A word->bool)#bool#A word#A word#A word. FST x)`
  (REWRITE_TAC[measure_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[LT_TRANS; ARITH_RULE `!k. ~(k = 0) ==> k - 1 < k`])
  `word_gen_gc_partial_move_ref_list k (conf:data_to_word_config)
     (pb:A word,i:A word,pa:A word,old:A word,m:A word->(A)word_loc,
      dm:A word->bool,c:bool,gs:A word,rs:A word,re:A word) =
     if pb = re then (i,pa,m,c) else
     if k = 0 then (i,pa,m,F) else
       let w = m pb in
       let c = (c /\ pb IN dm /\ isWord w) in
       let len = decode_length conf (theWord w) in
       let pb = word_add pb bytes_in_word in
       let (pb,i1,pa1,m1,c1) =
             word_gen_gc_partial_move_list conf (pb,len,i,pa,old,m,dm,gs,rs) in
         word_gen_gc_partial_move_ref_list (k - 1) conf
           (pb,i1,pa1,old,m1,dm,(c /\ c1),gs,rs,re)`;;

let word_gen_gc_partial_move_data_def = cake_def_wf
  `MEASURE (\x:data_to_word_config#num#A word#A word#A word#A word#
               (A word->(A)word_loc)#(A word->bool)#A word#A word. FST (SND x))`
  (REWRITE_TAC[measure_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[LT_TRANS; ARITH_RULE `!k. ~(k = 0) ==> k - 1 < k`])
  `word_gen_gc_partial_move_data (conf:data_to_word_config) k
     (h2a:A word,i:A word,pa:A word,old:A word,m:A word->(A)word_loc,
      dm:A word->bool,gs:A word,rs:A word) =
     if h2a = pa then (i,pa,m,T) else
     if k = 0 then (i,pa,m,F) else
       let c = (h2a IN dm) in
       let v = m h2a in
       let c = (c /\ isWord v) in
       let l = decode_length conf (theWord v) in
         if bit 2 (theWord v) then
           let h2a = word_add h2a (word_mul (word_add l (word 1)) bytes_in_word) in
           let (i,pa,m,c2) = word_gen_gc_partial_move_data conf (k - 1)
                               (h2a,i,pa,old,m,dm,gs,rs) in
             (i,pa,m,(c /\ c2))
         else
           let (h2a,i,pa,m,c1) = word_gen_gc_partial_move_list conf
                               (word_add h2a bytes_in_word,l,i,pa,old,m,dm,gs,rs) in
           let (i,pa,m,c2) = word_gen_gc_partial_move_data conf (k - 1)
                               (h2a,i,pa,old,m,dm,gs,rs) in
             (i,pa,m,(c /\ c1 /\ c2))`;;

let word_gen_gc_partial_def = cake_def
  `word_gen_gc_partial (conf:data_to_word_config)
     (roots,(curr:A word),new:A word,len:A word,m:A word->(A)word_loc,
      dm:A word->bool,gs:A word,rs:A word) =
     let refs_end = word_add curr len in
     let gen_start = word_ushr gs (backend_common_word_shift (:A)) in
     let (roots,i,pa,m,c1) = word_gen_gc_partial_move_roots conf
                     (roots,gen_start,new,curr,m,dm,gs,rs) in
     let (i,pa,m,c2) = word_gen_gc_partial_move_ref_list (dimword (:A)) conf
                     (word_add curr rs,i,pa,curr,m,dm,c1,gs,rs,refs_end) in
     let (i,pa,m,c3) = word_gen_gc_partial_move_data conf (dimword (:A))
                     (new,i,pa,curr,m,dm,gs,rs) in
       (roots,i,pa,m,(c2 /\ c3))`;;

let word_gen_gc_partial_full_def = cake_def
  `word_gen_gc_partial_full (conf:data_to_word_config)
     (roots,(curr:A word),new:A word,len:A word,m:A word->(A)word_loc,
      dm:A word->bool,gs:A word,rs:A word) =
     let (roots,i,pa,m,c1) = word_gen_gc_partial conf (roots,curr,new,len,m,dm,gs,rs) in
     let cpy_length = word_ushr (word_sub pa new) (backend_common_word_shift (:A)) in
     let (b1,m,c2) = memcpy cpy_length new (word_add curr gs) m dm in
       (roots,i,b1,m,(c1 /\ c2))`;;

let is_ref_header_def = cake_def
  `is_ref_header (v:A word) <=> (word_and v (word 12) = word 8)`;;

let word_gen_gc_move_def = cake_def
  `(word_gen_gc_move (conf:data_to_word_config)
      (wl_Loc l1 l2,i:A word,pa:A word,ib:A word,pb:A word,old:A word,
       m:A word->(A)word_loc,dm:A word->bool) =
      (wl_Loc l1 l2,i,pa,ib,pb,m,(l2 = 0))) /\
   (word_gen_gc_move conf (wl_Word w,i,pa,ib,pb,old,m,dm) =
      if word_and (word 1) w = word 0 then (wl_Word w,i,pa,ib,pb,m,T) else
        let c = (ptr_to_addr conf old w IN dm) in
        let v = m (ptr_to_addr conf old w) in
        let c = (c /\ isWord v) in
          if is_fwd_ptr v then
            (wl_Word (update_addr conf (word_ushr (theWord v) 2) w),i,pa,ib,pb,m,c)
          else
            let header_addr = ptr_to_addr conf old w in
            let c = (c /\ header_addr IN dm /\ isWord (m header_addr)) in
            let len = decode_length conf (theWord (m header_addr)) in
              if is_ref_header (theWord v) then
                let v = word_sub ib (word_add len (word 1)) in
                let pb1 = word_sub pb (word_mul (word_add len (word 1)) bytes_in_word) in
                let (b0,m1,c1) = memcpy (word_add len (word 1)) header_addr pb1 m dm in
                let c = (c /\ header_addr IN dm /\ c1) in
                let m1 = (header_addr =+ wl_Word (word_shl v 2)) m1 in
                  (wl_Word (update_addr conf v w),i,pa,v,pb1,m1,c)
              else
                let v = word_add (word_add i len) (word 1) in
                let (pa1,m1,c1) = memcpy (word_add len (word 1)) header_addr pa m dm in
                let c = (c /\ header_addr IN dm /\ c1) in
                let m1 = (header_addr =+ wl_Word (word_shl i 2)) m1 in
                  (wl_Word (update_addr conf i w),v,pa1,ib,pb,m1,c))`;;

let word_gen_gc_move_roots_def = cake_def
  `(word_gen_gc_move_roots (conf:data_to_word_config)
      ([],i:A word,pa:A word,ib:A word,pb:A word,old:A word,
       m:A word->(A)word_loc,dm:A word->bool) = ([],i,pa,ib,pb,m,T)) /\
   (word_gen_gc_move_roots conf (CONS w ws,i,pa,ib,pb,old,m,dm) =
      let (w1,i1,pa1,ib,pb,m1,c1) = word_gen_gc_move conf (w,i,pa,ib,pb,old,m,dm) in
      let (ws2,i2,pa2,ib,pb,m2,c2) =
            word_gen_gc_move_roots conf (ws,i1,pa1,ib,pb,old,m1,dm) in
        (CONS w1 ws2,i2,pa2,ib,pb,m2,(c1 /\ c2)))`;;

let word_gen_gc_move_roots_ind = cake_ind "word_gen_gc_move_roots";;

let word_gen_gc_move_list_def = cake_def_wf
  `MEASURE (\x:data_to_word_config#A word#A word#A word#A word#A word#A word#
               A word#(A word->(A)word_loc)#(A word->bool). val (FST (SND (SND x))))`
  (REWRITE_TAC[measure_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[LT_TRANS; WSIMPPAUX_val_word_pred])
  `word_gen_gc_move_list (conf:data_to_word_config)
     (a:A word,l:A word,i:A word,pa:A word,ib:A word,pb:A word,old:A word,
      m:A word->(A)word_loc,dm:A word->bool) =
     if l = word 0 then (a,i,pa,ib,pb,m,T) else
       let w = (m a):(A)word_loc in
       let (w1,i1,pa1,ib,pb,m1,c1) = word_gen_gc_move conf (w,i,pa,ib,pb,old,m,dm) in
       let m1 = (a =+ w1) m1 in
       let (a2,i2,pa2,ib,pb,m2,c2) = word_gen_gc_move_list conf
             (word_add a bytes_in_word,word_sub l (word 1),i1,pa1,ib,pb,old,m1,dm) in
         (a2,i2,pa2,ib,pb,m2,(a IN dm /\ c1 /\ c2))`;;

let word_gen_gc_move_list_ind = cake_ind "word_gen_gc_move_list";;

let word_gen_gc_move_data_def = cake_def_wf
  `MEASURE (\x:data_to_word_config#num#A word#A word#A word#A word#A word#
               A word#(A word->(A)word_loc)#(A word->bool). FST (SND x))`
  (REWRITE_TAC[measure_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[LT_TRANS; ARITH_RULE `!k. ~(k = 0) ==> k - 1 < k`])
  `word_gen_gc_move_data (conf:data_to_word_config) k
     (h2a:A word,i:A word,pa:A word,ib:A word,pb:A word,old:A word,
      m:A word->(A)word_loc,dm:A word->bool) =
     if h2a = pa then (i,pa,ib,pb,m,T) else
     if k = 0 then (i,pa,ib,pb,m,F) else
       let c = (h2a IN dm) in
       let v = m h2a in
       let c = (c /\ isWord v) in
       let l = decode_length conf (theWord v) in
         if bit 2 (theWord v) then
           let h2a = word_add h2a (word_mul (word_add l (word 1)) bytes_in_word) in
           let (i,pa,ib,pb,m,c2) = word_gen_gc_move_data conf (k - 1)
                                     (h2a,i,pa,ib,pb,old,m,dm) in
             (i,pa,ib,pb,m,(c /\ c2))
         else
           let (h2a,i,pa,ib,pb,m,c1) = word_gen_gc_move_list conf
                                     (word_add h2a bytes_in_word,l,i,pa,ib,pb,old,m,dm) in
           let (i,pa,ib,pb,m,c2) = word_gen_gc_move_data conf (k - 1)
                                     (h2a,i,pa,ib,pb,old,m,dm) in
             (i,pa,ib,pb,m,(c /\ c1 /\ c2))`;;

let word_gen_gc_move_refs_def = cake_def_wf
  `MEASURE (\x:data_to_word_config#num#A word#A word#A word#A word#A word#
               A word#A word#(A word->(A)word_loc)#(A word->bool). FST (SND x))`
  (REWRITE_TAC[measure_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[LT_TRANS; ARITH_RULE `!k. ~(k = 0) ==> k - 1 < k`])
  `word_gen_gc_move_refs (conf:data_to_word_config) k
     (r2a:A word,r1a:A word,i:A word,pa:A word,ib:A word,pb:A word,old:A word,
      m:A word->(A)word_loc,dm:A word->bool) =
     if r2a = r1a then (r2a,i,pa,ib,pb,m,T) else
     if k = 0 then (r2a,i,pa,ib,pb,m,F) else
       let c = (r2a IN dm) in
       let v = m r2a in
       let c = (c /\ isWord v) in
       let l = decode_length conf (theWord v) in
       let (r2a,i,pa,ib,pb,m,c1) = word_gen_gc_move_list conf
                                     (word_add r2a bytes_in_word,l,i,pa,ib,pb,old,m,dm) in
       let (r2a,i,pa,ib,pb,m,c2) = word_gen_gc_move_refs conf (k - 1)
                                     (r2a,r1a,i,pa,ib,pb,old,m,dm) in
         (r2a,i,pa,ib,pb,m,(c /\ c1 /\ c2))`;;

let word_gen_gc_move_loop_def = cake_def_wf
  `MEASURE (\x:data_to_word_config#num#A word#A word#A word#A word#A word#
               A word#A word#(A word->(A)word_loc)#(A word->bool). FST (SND x))`
  (REWRITE_TAC[measure_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
   ASM_MESON_TAC[LT_TRANS; ARITH_RULE `!k. ~(k = 0) ==> k - 1 < k`])
  `word_gen_gc_move_loop (conf:data_to_word_config) k
     (pax:A word,i:A word,pa:A word,ib:A word,pb:A word,pbx:A word,old:A word,
      m:A word->(A)word_loc,dm:A word->bool) =
     if pbx = pb then
       if pax = pa then
         (i,pa,ib,pb,m,T)
       else
         let (i,pa,ib,pb,m,c1) = word_gen_gc_move_data conf (dimword (:A))
                                   (pax,i,pa,ib,pb,old,m,dm) in
           if k = 0 then (i,pa,ib,pb,m,F) else
             let (i,pa,ib,pb,m,c2) = word_gen_gc_move_loop conf (k - 1)
                                       (pa,i,pa,ib,pb,pbx,old,m,dm) in
               (i,pa,ib,pb,m,(c1 /\ c2))
     else
       let (pbx,i,pa,ib,pb',m,c1) = word_gen_gc_move_refs conf (dimword (:A))
                                      (pb,pbx,i,pa,ib,pb,old,m,dm) in
         if k = 0 then (i,pa,ib,pb,m,F) else
           let (i,pa,ib,pb,m,c2) = word_gen_gc_move_loop conf (k - 1)
                                     (pax,i,pa,ib,pb',pb,old,m,dm) in
             (i,pa,ib,pb,m,(c1 /\ c2))`;;

let word_gen_gc_def = cake_def
  `word_gen_gc (conf:data_to_word_config)
     (roots,curr:A word,new:A word,len:A word,m:A word->(A)word_loc,dm:A word->bool) =
     let new_end = word_add new len in
     let len = word_ushr len (backend_common_word_shift (:A)) in
     let (roots,i,pa,ib,pb,m,c1) = word_gen_gc_move_roots conf
                     (roots,word 0,new,len,new_end,curr,m,dm) in
     let (i,pa,ib,pb,m,c2) = word_gen_gc_move_loop conf (val len)
                                  (new,i,pa,ib,pb,new_end,curr,m,dm) in
       (roots,i,pa,ib,pb,m,(c1 /\ c2))`;;

let glob_real_def = cake_def
  `(glob_real (c:data_to_word_config) (curr:A word) (wl_Word (w:A word)) =
      wl_Word (word_add curr (word_shl (word_ushr w (shift_length c))
                                       (backend_common_word_shift (:A))))) /\
   (glob_real c curr (x:(A)word_loc) = x)`;;

let word_gc_fun_def = cake_def
  `word_gc_fun (conf:data_to_word_config) =
     ((\(roots,m,dm,s).
       let c1 = word_gc_fun_assum conf s in
       let new = theWord (FAPPLY s OtherHeap) in
       let old = theWord (FAPPLY s CurrHeap) in
       let len = theWord (FAPPLY s HeapLength) in
       let all_roots = CONS (FAPPLY s Globals) roots in
         match data_to_word_config_gc_kind conf with
           data_to_word_None ->
            (let s1 = s |++ [(NextFree, wl_Word old);
                             (TriggerGC, wl_Word old);
                             (EndOfHeap, wl_Word old)] in
               if c1 then SOME (roots,m,s1) else NONE)
         | data_to_word_Simple ->
            (let (roots1,i1,pa1,m1,c2) =
               word_full_gc conf (all_roots,new,old,m,dm) in
             let s1 = s |++ [(CurrHeap, wl_Word new);
                             (OtherHeap, wl_Word old);
                             (NextFree, wl_Word pa1);
                             (TriggerGC, wl_Word (word_add new len));
                             (EndOfHeap, wl_Word (word_add new len));
                             (Globals, HD roots1);
                             (GlobReal, glob_real conf new (HD roots1))] in
               if c1 /\ c2 then SOME (TL roots1,m1,s1) else NONE)
         | Generational gen_sizes ->
            if ~c1 then NONE else
            if word_gen_gc_can_do_partial gen_sizes s then
              (let gs = theWord (FAPPLY s GenStart) in
               let rs = word_sub (theWord (FAPPLY s EndOfHeap)) (theWord (FAPPLY s CurrHeap)) in
               let len = theWord (FAPPLY s HeapLength) in
               let endh = theWord (FAPPLY s EndOfHeap) in
               let (roots1,i1,pa1,m1,c2) =
                 word_gen_gc_partial_full conf (all_roots,old,new,len,m,dm,gs,rs) in
               let a = theWord (FAPPLY s AllocSize) in
               let s1 = s |++ [(CurrHeap, wl_Word old);
                               (OtherHeap, wl_Word new);
                               (NextFree, wl_Word pa1);
                               (GenStart, wl_Word (word_sub pa1 old));
                               (TriggerGC, wl_Word (word_add pa1
                                  (new_trig (word_sub endh pa1) a gen_sizes)));
                               (Globals, HD roots1);
                               (GlobReal, glob_real conf old (HD roots1));
                               (Temp (word 0), wl_Word (word 0));
                               (Temp (word 1), wl_Word (word 0))] in
               let c3 = (word_ule a (word_sub endh pa1) /\
                         word_ule a (new_trig (word_sub endh pa1) a gen_sizes)) in
                 if c2 /\ c3 then SOME (TL roots1,m1,s1) else NONE)
            else
              (let (roots1,i1,pa1,ib1,pb1,m1,c2) =
                 word_gen_gc conf (all_roots,old,new,len,m,dm) in
               let a = theWord (FAPPLY s AllocSize) in
               let s1 = s |++ [(CurrHeap, wl_Word new);
                               (OtherHeap, wl_Word old);
                               (NextFree, wl_Word pa1);
                               (GenStart, wl_Word (word_sub pa1 new));
                               (TriggerGC, wl_Word (word_add pa1
                                  (new_trig (word_sub pb1 pa1) a gen_sizes)));
                               (EndOfHeap, wl_Word pb1);
                               (Globals, HD roots1);
                               (GlobReal, glob_real conf new (HD roots1));
                               (Temp (word 0), wl_Word (word 0));
                               (Temp (word 1), wl_Word (word 0));
                               (Temp (word 2), wl_Word (word 0));
                               (Temp (word 3), wl_Word (word 0));
                               (Temp (word 4), wl_Word (word 0));
                               (Temp (word 5), wl_Word (word 0));
                               (Temp (word 6), wl_Word (word 0))] in
                 if c2 then SOME (TL roots1,m1,s1) else NONE))
      :((A)word_loc)list#(A word->(A)word_loc)#(A word->bool)#
       (store_name,(A)word_loc)fmap->
       (((A)word_loc)list#(A word->(A)word_loc)#(store_name,(A)word_loc)fmap)option)`;;

(* ------------------------------------------------------------------------- *)
(* the roots after a GC: words stay words, constants are not changed        *)
(* ------------------------------------------------------------------------- *)

(* the property of word_gc_move that the IMP_EVERY2 theorems lift to lists *)

let WSIMPPAUX_word_gc_move_IMP = prove
 (`!c x i pa old m dm y i1 pa1 m1 c1.
     word_gc_move c (x:(A)word_loc,i,pa,old,m,dm) = (y,i1,pa1,m1,c1) ==>
     (isWord x <=> isWord y) /\ (is_gc_word_const x ==> x = y)`,
  GEN_TAC THEN MATCH_MP_TAC word_loc_INDUCT THEN
  SIMP[word_gc_move_def; is_gc_word_const_def; is_gc_const_def] THEN
  REPEAT GEN_TAC THEN RW[] THEN REPEAT(PAIRARG_TAC THEN FS[]) THEN
  RVEQ_TAC THEN SIMP[isWord_def]);;

(* word_gen_gc_move tests word_and (word 1) w, is_gc_const word_and w (word 1) *)

let WSIMPPAUX_word_and_1 = prove
 (`!w:A word. word_and (word 1) w = word_and w (word 1)`,
  REWRITE_TAC[WORD_AND_SYM]);;

let WSIMPPAUX_word_gen_gc_move_IMP = prove
 (`!c x i pa ib pb old m dm y i1 pa1 ib1 pb1 m1 c1.
     word_gen_gc_move c (x:(A)word_loc,i,pa,ib,pb,old,m,dm) =
       (y,i1,pa1,ib1,pb1,m1,c1) ==>
     (isWord x <=> isWord y) /\ (is_gc_word_const x ==> x = y)`,
  GEN_TAC THEN MATCH_MP_TAC word_loc_INDUCT THEN
  SIMP[word_gen_gc_move_def; is_gc_word_const_def; is_gc_const_def;
       WSIMPPAUX_word_and_1] THEN
  REPEAT GEN_TAC THEN RW[] THEN REPEAT(PAIRARG_TAC THEN FS[]) THEN
  RVEQ_TAC THEN SIMP[isWord_def]);;

let WSIMPPAUX_word_gen_gc_partial_move_IMP = prove
 (`!c x i pa old m dm gs rs y i1 pa1 m1 c1.
     word_gen_gc_partial_move c (x:(A)word_loc,i,pa,old,m,dm,gs,rs) =
       (y,i1,pa1,m1,c1) ==>
     (isWord x <=> isWord y) /\ (is_gc_word_const x ==> x = y)`,
  GEN_TAC THEN MATCH_MP_TAC word_loc_INDUCT THEN
  SIMP[word_gen_gc_partial_move_def; is_gc_word_const_def; is_gc_const_def] THEN
  REPEAT GEN_TAC THEN RW[] THEN REPEAT(PAIRARG_TAC THEN FS[]) THEN
  RVEQ_TAC THEN SIMP[isWord_def]);;

let word_gc_move_roots_IMP_EVERY2 = prove
 (`!xs ys pa m i c1 m1 pa1 i1 old dm c.
     word_gc_move_roots c (xs:((A)word_loc)list,i,pa,old,m,dm) = (ys,i1,pa1,m1,c1) ==>
     ALL2 (\x y. (isWord x <=> isWord y) /\ (is_gc_word_const x ==> x = y)) xs ys`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[word_gc_move_roots_def] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[ALL2];
    REPLICATE_TAC 8 PAIRARG_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[ALL2] THEN CONJ_TAC THENL
     [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP WSIMPPAUX_word_gc_move_IMP);
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]]);;

let word_gen_gc_move_roots_IMP_EVERY2 = prove
 (`!xs ys pa m i ib pb c1 m1 pa1 i1 ib1 pb1 old dm c.
     word_gen_gc_move_roots c (xs:((A)word_loc)list,i,pa,ib,pb,old,m,dm) =
       (ys,i1,pa1,ib1,pb1,m1,c1) ==>
     ALL2 (\x y. (isWord x <=> isWord y) /\ (is_gc_word_const x ==> x = y)) xs ys`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[word_gen_gc_move_roots_def] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[ALL2];
    REPLICATE_TAC 12 PAIRARG_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[ALL2] THEN CONJ_TAC THENL
     [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP WSIMPPAUX_word_gen_gc_move_IMP);
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]]);;

let word_gen_gc_partial_move_roots_IMP_EVERY2 = prove
 (`!xs ys pa m i gs rs c1 m1 pa1 i1 old dm c.
     word_gen_gc_partial_move_roots c (xs:((A)word_loc)list,i,pa,old,m,dm,gs,rs) =
       (ys,i1,pa1,m1,c1) ==>
     ALL2 (\x y. (isWord x <=> isWord y) /\ (is_gc_word_const x ==> x = y)) xs ys`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[word_gen_gc_partial_move_roots_def] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[ALL2];
    REPLICATE_TAC 8 PAIRARG_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[ALL2] THEN CONJ_TAC THENL
     [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP WSIMPPAUX_word_gen_gc_partial_move_IMP);
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]]);;

let word_gc_IMP_EVERY2 = prove
 (`word_gc_fun c (xs,m,dm,st) = SOME (ys,m1,s1) ==>
   ALL2 (\x y. (isWord x <=> isWord y) /\ (is_gc_word_const x ==> x = y))
        xs (ys:((A)word_loc)list)`,
  REWRITE_TAC[word_gc_fun_def; word_full_gc_def; word_gen_gc_def;
              word_gen_gc_partial_def; word_gen_gc_partial_full_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CASES_ON `data_to_word_config_gc_kind c` THEN CAKE_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN
    REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN
    STRIP_TAC THEN RVEQ_TAC THEN MATCH_MP_TAC EVERY2_refl THEN REWRITE_TAC[];
    REWRITE_TAC[word_gc_move_roots_def];
    COND_CASES_TAC THEN REWRITE_TAC[distinctness "option"] THEN
    REWRITE_TAC[word_gen_gc_move_roots_def; word_gen_gc_partial_move_roots_def] THEN
    COND_CASES_TAC] THEN
  REPEAT WSIMPPAUX_PAIRARG_TAC THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "option"; injectivity "option"; PAIR_EQ] THEN
  STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check(is_conj o concl))) THEN
  RVEQ_TAC THEN REWRITE_TAC[TL] THEN
  MAP_FIRST (fun th -> FIRST_ASSUM(ACCEPT_TAC o MATCH_MP th))
    [word_gc_move_roots_IMP_EVERY2; word_gen_gc_move_roots_IMP_EVERY2;
     word_gen_gc_partial_move_roots_IMP_EVERY2]);;

let word_gc_fun_LENGTH = prove
 (`word_gc_fun c (xs,m,dm,s) = SOME (zs,m1,s1) ==>
   LENGTH xs = LENGTH (zs:((A)word_loc)list)`,
  DISCH_THEN(MP_TAC o MATCH_MP word_gc_IMP_EVERY2) THEN
  MATCH_ACCEPT_TAC EVERY2_LENGTH);;

(* ------------------------------------------------------------------------- *)
(* lemmas about has_fp_ops                                                   *)
(* ------------------------------------------------------------------------- *)

let word_gc_fun_assum_has_fp_ops = prove
 (`word_gc_fun_assum (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                        (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf))
                     (s:(store_name,(A)word_loc)fmap) =
   word_gc_fun_assum conf s`,
  SIMP[word_gc_fun_assum_def]);;

cake_add_simps [word_gc_fun_assum_has_fp_ops];;

let word_gc_move_has_fp_ops = prove
 (`!x. word_gc_move (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                       (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) x =
       word_gc_move conf
         (x:(A)word_loc#A word#A word#A word#(A word->(A)word_loc)#(A word->bool))`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN MATCH_MP_TAC word_loc_INDUCT THEN
  SIMP[word_gc_move_def; ptr_to_addr_def; update_addr_def; small_shift_length_def;
       decode_length_def]);;

cake_add_simps [word_gc_move_has_fp_ops];;

let word_gen_gc_move_has_fp_ops = prove
 (`!x. word_gen_gc_move (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                           (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) x =
       word_gen_gc_move conf
         (x:(A)word_loc#A word#A word#A word#A word#A word#(A word->(A)word_loc)#
            (A word->bool))`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN MATCH_MP_TAC word_loc_INDUCT THEN
  SIMP[word_gen_gc_move_def; ptr_to_addr_def; update_addr_def; small_shift_length_def;
       decode_length_def]);;

cake_add_simps [word_gen_gc_move_has_fp_ops];;

let word_gen_gc_partial_move_has_fp_ops = prove
 (`!x. word_gen_gc_partial_move (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                           (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) x =
       word_gen_gc_partial_move conf
         (x:(A)word_loc#A word#A word#A word#(A word->(A)word_loc)#(A word->bool)#
            A word#A word)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN MATCH_MP_TAC word_loc_INDUCT THEN
  SIMP[word_gen_gc_partial_move_def; ptr_to_addr_def; update_addr_def;
       small_shift_length_def; decode_length_def]);;

cake_add_simps [word_gen_gc_partial_move_has_fp_ops];;

(* the parts of the configuration that the GC functions use *)

let WSIMPPAUX_conf_has_fp_ops = prove
 (`ptr_to_addr (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) =
     (ptr_to_addr conf:A word->A word->A word) /\
   update_addr (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) =
     (update_addr conf:A word->A word->A word) /\
   decode_length (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) =
     (decode_length conf:A word->A word) /\
   data_to_word_config_gc_kind (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) =
     data_to_word_config_gc_kind conf`,
  REWRITE_TAC[FUN_EQ_THM] THEN
  SIMP[ptr_to_addr_def; update_addr_def; decode_length_def; small_shift_length_def]);;

let WSIMPPAUX_conf_has_fp_ops_moves = CONJ word_gc_move_has_fp_ops
  (CONJ word_gen_gc_move_has_fp_ops word_gen_gc_partial_move_has_fp_ops);;

let word_gc_move_list_has_fp_ops = prove
 (`!conf x. word_gc_move_list (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) x =
            word_gc_move_list conf
              (x:A word#A word#A word#A word#A word#(A word->(A)word_loc)#(A word->bool))`,
  MATCH_MP_TAC word_gc_move_list_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC BINOP_CONV [word_gc_move_list_def] THEN
  REWRITE_TAC[WSIMPPAUX_conf_has_fp_ops_moves] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPLICATE_TAC 4 PAIRARG_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

cake_add_simps [word_gc_move_list_has_fp_ops];;

let word_gen_gc_move_list_has_fp_ops = prove
 (`!conf x. word_gen_gc_move_list (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) x =
            word_gen_gc_move_list conf
              (x:A word#A word#A word#A word#A word#A word#A word#(A word->(A)word_loc)#
                 (A word->bool))`,
  MATCH_MP_TAC word_gen_gc_move_list_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC BINOP_CONV [word_gen_gc_move_list_def] THEN
  REWRITE_TAC[WSIMPPAUX_conf_has_fp_ops_moves] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPLICATE_TAC 6 PAIRARG_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

cake_add_simps [word_gen_gc_move_list_has_fp_ops];;

let word_gen_gc_partial_move_list_has_fp_ops = prove
 (`!conf x. word_gen_gc_partial_move_list (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) x =
            word_gen_gc_partial_move_list conf
              (x:A word#A word#A word#A word#A word#(A word->(A)word_loc)#(A word->bool)#
                 A word#A word)`,
  MATCH_MP_TAC word_gen_gc_partial_move_list_ind THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC BINOP_CONV [word_gen_gc_partial_move_list_def] THEN
  REWRITE_TAC[WSIMPPAUX_conf_has_fp_ops_moves] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPLICATE_TAC 4 PAIRARG_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

cake_add_simps [word_gen_gc_partial_move_list_has_fp_ops];;

let word_gc_move_roots_has_fp_ops = prove
 (`!conf x. word_gc_move_roots (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) x =
            word_gc_move_roots conf
              (x:((A)word_loc)list#A word#A word#A word#(A word->(A)word_loc)#(A word->bool))`,
  MATCH_MP_TAC word_gc_move_roots_ind THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[word_gc_move_roots_def];
    DISCH_TAC THEN REWRITE_TAC[word_gc_move_roots_def; WSIMPPAUX_conf_has_fp_ops_moves] THEN
    REPLICATE_TAC 4 PAIRARG_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

cake_add_simps [word_gc_move_roots_has_fp_ops];;

let word_gen_gc_move_roots_has_fp_ops = prove
 (`!conf x. word_gen_gc_move_roots (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) x =
            word_gen_gc_move_roots conf
              (x:((A)word_loc)list#A word#A word#A word#A word#A word#
                 (A word->(A)word_loc)#(A word->bool))`,
  MATCH_MP_TAC word_gen_gc_move_roots_ind THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[word_gen_gc_move_roots_def];
    DISCH_TAC THEN REWRITE_TAC[word_gen_gc_move_roots_def; WSIMPPAUX_conf_has_fp_ops_moves] THEN
    REPLICATE_TAC 6 PAIRARG_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

cake_add_simps [word_gen_gc_move_roots_has_fp_ops];;

let word_gen_gc_partial_move_roots_has_fp_ops = prove
 (`!conf x. word_gen_gc_partial_move_roots (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) x =
            word_gen_gc_partial_move_roots conf
              (x:((A)word_loc)list#A word#A word#A word#(A word->(A)word_loc)#
                 (A word->bool)#A word#A word)`,
  MATCH_MP_TAC word_gen_gc_partial_move_roots_ind THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[word_gen_gc_partial_move_roots_def];
    DISCH_TAC THEN REWRITE_TAC[word_gen_gc_partial_move_roots_def; WSIMPPAUX_conf_has_fp_ops_moves] THEN
    REPLICATE_TAC 4 PAIRARG_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

cake_add_simps [word_gen_gc_partial_move_roots_has_fp_ops];;

let word_gc_move_loop_has_fp_ops = prove
 (`!n conf x. word_gc_move_loop n (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) x =
              word_gc_move_loop n conf
                (x:A word#A word#A word#A word#(A word->(A)word_loc)#(A word->bool)#bool)`,
  INDUCT_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC BINOP_CONV [word_gc_move_loop_def] THEN
  ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; WSIMPPAUX_conf_has_fp_ops; word_gc_move_list_has_fp_ops]);;

cake_add_simps [word_gc_move_loop_has_fp_ops];;

let word_gen_gc_partial_move_data_has_fp_ops = prove
 (`!n conf x. word_gen_gc_partial_move_data (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) n x =
              word_gen_gc_partial_move_data conf n
                (x:A word#A word#A word#A word#(A word->(A)word_loc)#(A word->bool)#
                   A word#A word)`,
  INDUCT_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC BINOP_CONV [word_gen_gc_partial_move_data_def] THEN
  ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; WSIMPPAUX_conf_has_fp_ops; word_gen_gc_partial_move_list_has_fp_ops]);;

cake_add_simps [word_gen_gc_partial_move_data_has_fp_ops];;

let word_gen_gc_move_data_has_fp_ops = prove
 (`!n conf x. word_gen_gc_move_data (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) n x =
              word_gen_gc_move_data conf n
                (x:A word#A word#A word#A word#A word#A word#(A word->(A)word_loc)#
                   (A word->bool))`,
  INDUCT_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC BINOP_CONV [word_gen_gc_move_data_def] THEN
  ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; WSIMPPAUX_conf_has_fp_ops; word_gen_gc_move_list_has_fp_ops]);;

cake_add_simps [word_gen_gc_move_data_has_fp_ops];;

let word_gen_gc_move_refs_has_fp_ops = prove
 (`!n conf x. word_gen_gc_move_refs (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) n x =
              word_gen_gc_move_refs conf n
                (x:A word#A word#A word#A word#A word#A word#A word#
                   (A word->(A)word_loc)#(A word->bool))`,
  INDUCT_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC BINOP_CONV [word_gen_gc_move_refs_def] THEN
  ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; WSIMPPAUX_conf_has_fp_ops; word_gen_gc_move_list_has_fp_ops]);;

cake_add_simps [word_gen_gc_move_refs_has_fp_ops];;

let word_gen_gc_partial_move_ref_list_has_fp_ops = prove
 (`!n conf x. word_gen_gc_partial_move_ref_list n (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) x =
              word_gen_gc_partial_move_ref_list n conf
                (x:A word#A word#A word#A word#(A word->(A)word_loc)#(A word->bool)#bool#
                   A word#A word#A word)`,
  INDUCT_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC BINOP_CONV [word_gen_gc_partial_move_ref_list_def] THEN
  ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; WSIMPPAUX_conf_has_fp_ops; word_gen_gc_partial_move_list_has_fp_ops]);;

cake_add_simps [word_gen_gc_partial_move_ref_list_has_fp_ops];;

let word_gen_gc_move_loop_has_fp_ops = prove
 (`!n conf x. word_gen_gc_move_loop (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) n x =
              word_gen_gc_move_loop conf n
                (x:A word#A word#A word#A word#A word#A word#A word#
                   (A word->(A)word_loc)#(A word->bool))`,
  INDUCT_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC BINOP_CONV [word_gen_gc_move_loop_def] THEN
  ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; WSIMPPAUX_conf_has_fp_ops;
                   word_gen_gc_move_data_has_fp_ops; word_gen_gc_move_refs_has_fp_ops]);;

cake_add_simps [word_gen_gc_move_loop_has_fp_ops];;

let word_full_gc_has_fp_ops = prove
 (`!x. word_full_gc (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) x =
       word_full_gc conf
         (x:((A)word_loc)list#A word#A word#(A word->(A)word_loc)#(A word->bool))`,
  REWRITE_TAC[FORALL_PAIR_THM; word_full_gc_def; word_gc_move_roots_has_fp_ops;
              word_gc_move_loop_has_fp_ops]);;

cake_add_simps [word_full_gc_has_fp_ops];;

let word_gen_gc_partial_full_has_fp_ops = prove
 (`!x. word_gen_gc_partial_full (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) x =
       word_gen_gc_partial_full conf
         (x:((A)word_loc)list#A word#A word#A word#(A word->(A)word_loc)#(A word->bool)#
            A word#A word)`,
  REWRITE_TAC[FORALL_PAIR_THM; word_gen_gc_partial_full_def; word_gen_gc_partial_def;
              word_gen_gc_partial_move_roots_has_fp_ops;
              word_gen_gc_partial_move_ref_list_has_fp_ops;
              word_gen_gc_partial_move_data_has_fp_ops]);;

cake_add_simps [word_gen_gc_partial_full_has_fp_ops];;

let word_gen_gc_has_fp_ops = prove
 (`!x. word_gen_gc (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) x =
       word_gen_gc conf
         (x:((A)word_loc)list#A word#A word#A word#(A word->(A)word_loc)#(A word->bool))`,
  REWRITE_TAC[FORALL_PAIR_THM; word_gen_gc_def; word_gen_gc_move_roots_has_fp_ops;
              word_gen_gc_move_loop_has_fp_ops]);;

cake_add_simps [word_gen_gc_has_fp_ops];;

let glob_real_has_fp_ops = prove
 (`glob_real (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) x y =
   glob_real conf (x:A word) (y:(A)word_loc)`,
  STRUCT_CASES_TAC (ISPEC `y:(A)word_loc` (cases "word_loc")) THEN
  REWRITE_TAC[glob_real_def; shift_length_has_fp_ops]);;

cake_add_simps [glob_real_has_fp_ops];;

let word_gc_fun_has_fp_ops = prove
 (`word_gc_fun (data_to_word_config_has_fp_ops_fupd (combin_K b1)
                (data_to_word_config_has_fp_tern_fupd (combin_K b2) conf)) =
   word_gc_fun conf:((A)word_loc)list#(A word->(A)word_loc)#(A word->bool)#
                    (store_name,(A)word_loc)fmap->
                    (((A)word_loc)list#(A word->(A)word_loc)#(store_name,(A)word_loc)fmap)option`,
  REWRITE_TAC[word_gc_fun_def; WSIMPPAUX_conf_has_fp_ops; word_gc_fun_assum_has_fp_ops;
              word_full_gc_has_fp_ops; word_gen_gc_partial_full_has_fp_ops;
              word_gen_gc_has_fp_ops; glob_real_has_fp_ops]);;

cake_add_simps [word_gc_fun_has_fp_ops];;
