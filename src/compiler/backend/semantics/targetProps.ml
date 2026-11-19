(* ========================================================================= *)
(* targetProps: port of HOL4 compiler/backend/semantics/targetPropsScript.sml *)
(* (CakeML v3479).                                                           *)
(* Properties about the target semantics.                                   *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ffi/ffi.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/backend/semantics/targetSem.ml";;
needs "compiler/encoders/asm/asmSem.ml";;
needs "compiler/encoders/asm/asmProps.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - The type variables follow targetSem.ml: (A,B,C)machine_config has A     *)
(*   word addresses, machine states B and projections C (HOL4 writes         *)
(*   ('b,'a,'c) machine_config in find_next_interference); HOL4's datatype   *)
(*   interference_app ('a word addresses, 'state machine states) is          *)
(*   (A,B)interference_app.                                                  *)
(* - Records: mc.f is machine_config_f mc, mc.target.f is                    *)
(*   target_f (machine_config_target mc), s.f is asm_state_f s.              *)
(* - Words: n2w = word, w2n = val, + = word_add, - = word_neg; FUNPOW f n x *)
(*   is ITER n f x, FOLDR f e l is ITLIST f l e, set is set_of_list.         *)

let shift_interfer_def = cake_def
  `shift_interfer k (s:(A,B,C)machine_config) =
     machine_config_next_interfer_fupd
       (K (shift_seq k (machine_config_next_interfer s))) s`;;

(* HOL4 [local] *)

let shift_interfer_intro = prove
 (`shift_interfer k1 (shift_interfer k2 (c:(A,B,C)machine_config)) =
   shift_interfer (k1 + k2) c`,
  REWRITE_TAC[shift_interfer_def; shift_seq_def] THEN SIMP[ADD_ASSOC]);;

let bytes_in_memory_SUBSET = prove
 (`!p:A word.
     dm SUBSET dm2 /\ bytes_in_memory p xs m dm ==> bytes_in_memory p xs m dm2`,
  SPEC_TAC(`xs:byte list`,`xs:byte list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[bytes_in_memory_def; SUBSET] THEN ASM_MESON_TAC[SUBSET]);;

let bytes_in_memory_DIFF = prove
 (`!p:A word.
     dm = dm2 DIFF pcs /\ bytes_in_memory p xs m dm2 /\
     DISJOINT pcs {word_add p (word i) | i | i < LENGTH xs} ==>
     bytes_in_memory p xs m dm`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC bytes_in_memory_change_domain THEN
  EXISTS_TAC `dm2:A word->bool` THEN ASM_REWRITE_TAC[IN_DIFF] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
                              NOT_IN_EMPTY]) THEN
  ASM_MESON_TAC[]);;

let ffi_entry_pcs_disjoint_def = cake_def
  `ffi_entry_pcs_disjoint (mc:(A,B,C)machine_config) (s1:(A)asm_state) len <=>
     DISJOINT (set_of_list (machine_config_ffi_entry_pcs mc))
       {word_add (asm_state_pc s1) (word a) | a | a < len}`;;

(* -- the interference-application trace of a machine run -- *)

let interference_app_INDUCT,interference_app_RECURSION = cake_type
  "interference_app = FfiApp num (byte list) B B | CcApp (A word) (A word) B B";;

let is_ffi_app_def = cake_def
  `(is_ffi_app (FfiApp index new_bytes ms_pre ms_post:(A,B)interference_app) <=> T) /\
   (is_ffi_app (CcApp a1 a2 ms_pre ms_post:(A,B)interference_app) <=> F)`;;

let _ = cake_add_simps [is_ffi_app_def];;

let app_post_def = cake_def
  `(app_post (FfiApp index new_bytes ms_pre ms_post:(A,B)interference_app) = ms_post) /\
   (app_post (CcApp a1 a2 ms_pre ms_post:(A,B)interference_app) = ms_post)`;;

let _ = cake_add_simps [app_post_def];;

(* clocked clone of evaluate that stops at the first interference         *)
(* application (FFI, shared-memory or cache-clear) and returns its data     *)
(* together with the continuation configuration and ffi state (HOL4 proves  *)
(* termination by itself: k decreases)                                       *)
let find_next_interference_def = cake_def_wf
  `measure (\x:(A,B,C)machine_config#(FFI)ffi_state#num#B. FST (SND (SND x)))`
  TERM_TAC
  `find_next_interference (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) k (ms:B) =
     if k = 0 then (NONE:((A,B)interference_app#(A,B,C)machine_config#(FFI)ffi_state)option)
     else
       if target_get_pc (machine_config_target mc) ms IN
          (machine_config_prog_addresses mc DIFF
           set_of_list (machine_config_ffi_entry_pcs mc)) then
         if encoded_bytes_in_mem
              (target_config (machine_config_target mc))
              (target_get_pc (machine_config_target mc) ms)
              (target_get_byte (machine_config_target mc) ms)
              (machine_config_prog_addresses mc) then
           let ms1 = target_next (machine_config_target mc) ms in
           let (ms2,new_oracle) = apply_oracle (machine_config_next_interfer mc) ms1 in
           let mc = machine_config_next_interfer_fupd (K new_oracle) mc in
           if ALL (target_state_ok (machine_config_target mc)) [ms; ms1; ms2] /\
              (!x. ~(x IN machine_config_prog_addresses mc) ==>
                   target_get_byte (machine_config_target mc) ms1 x =
                   target_get_byte (machine_config_target mc) ms x)
           then find_next_interference mc ffi (k - 1) ms2
           else NONE
         else NONE
       else if target_get_pc (machine_config_target mc) ms = machine_config_halt_pc mc then
         NONE
       else if target_get_pc (machine_config_target mc) ms = machine_config_ccache_pc mc
       then
         let (ms1,new_oracle) =
           apply_oracle (machine_config_ccache_interfer mc)
             (target_get_reg (machine_config_target mc) ms (machine_config_ptr_reg mc),
              target_get_reg (machine_config_target mc) ms (machine_config_len_reg mc),
              ms) in
         SOME (CcApp (target_get_reg (machine_config_target mc) ms (machine_config_ptr_reg mc))
                     (target_get_reg (machine_config_target mc) ms (machine_config_len_reg mc))
                     ms ms1,
               machine_config_ccache_interfer_fupd (K new_oracle) mc,ffi)
       else
         match find_index (target_get_pc (machine_config_target mc) ms)
                 (machine_config_ffi_entry_pcs mc) 0 with
           NONE -> NONE
         | SOME ffi_index ->
             (match EL ffi_index (machine_config_ffi_names mc) with
                SharedMem op ->
                  (match ALOOKUP (machine_config_mmio_info mc) ffi_index with
                     NONE -> NONE
                   | SOME (nb,a,reg,pc') ->
                       (match op with
                          MappedRead ->
                            (match a with
                               Addr r off ->
                                 let ad = word_add (target_get_reg
                                            (machine_config_target mc) ms r) off in
                                 (if (if nb = word 0
                                      then val ad MOD (dimindex (:A) DIV 8) = 0 else T) /\
                                     ad IN machine_config_shared_addresses mc /\
                                     is_valid_mapped_read
                                       (target_get_pc (machine_config_target mc) ms)
                                       nb a reg pc' (machine_config_target mc) ms
                                       (machine_config_prog_addresses mc)
                                  then
                                    (match call_FFI ffi
                                             (EL ffi_index (machine_config_ffi_names mc))
                                             [nb] (word_to_bytes ad F) with
                                       FFI_final outcome -> NONE
                                     | FFI_return new_ffi new_bytes ->
                                         let (ms1,new_oracle) =
                                           apply_oracle (machine_config_ffi_interfer mc)
                                             (ffi_index,new_bytes,ms) in
                                         SOME (FfiApp ffi_index new_bytes ms ms1,
                                               machine_config_ffi_interfer_fupd
                                                 (K new_oracle) mc,
                                               new_ffi))
                                  else NONE))
                        | MappedWrite ->
                            (match a with
                               Addr r off ->
                                 let ad = word_add (target_get_reg
                                            (machine_config_target mc) ms r) off in
                                 (if (if nb = word 0
                                      then val ad MOD (dimindex (:A) DIV 8) = 0 else T) /\
                                     ad IN machine_config_shared_addresses mc /\
                                     is_valid_mapped_write
                                       (target_get_pc (machine_config_target mc) ms)
                                       nb a reg pc' (machine_config_target mc) ms
                                       (machine_config_prog_addresses mc)
                                  then
                                    (match call_FFI ffi
                                             (EL ffi_index (machine_config_ffi_names mc))
                                             [nb]
                                             (APPEND
                                                (let w = target_get_reg
                                                           (machine_config_target mc) ms reg in
                                                 if nb = word 0 then word_to_bytes w F
                                                 else word_to_bytes_aux (val nb) w F)
                                                (word_to_bytes ad F)) with
                                       FFI_final outcome -> NONE
                                     | FFI_return new_ffi new_bytes ->
                                         let (ms1,new_oracle) =
                                           apply_oracle (machine_config_ffi_interfer mc)
                                             (ffi_index,new_bytes,ms) in
                                         SOME (FfiApp ffi_index new_bytes ms ms1,
                                               machine_config_ffi_interfer_fupd
                                                 (K new_oracle) mc,
                                               new_ffi))
                                  else NONE))))
              | ExtCall _ ->
                  (match ALOOKUP (machine_config_mmio_info mc) ffi_index with
                     SOME _ -> NONE
                   | NONE ->
                       (match read_ffi_bytearrays mc ms with
                          (SOME bytes,SOME bytes2) ->
                            (match call_FFI ffi (EL ffi_index (machine_config_ffi_names mc))
                                     bytes bytes2 with
                               FFI_final outcome -> NONE
                             | FFI_return new_ffi new_bytes ->
                                 let (ms1,new_oracle) =
                                   apply_oracle (machine_config_ffi_interfer mc)
                                     (ffi_index,new_bytes,ms) in
                                 SOME (FfiApp ffi_index new_bytes ms ms1,
                                       machine_config_ffi_interfer_fupd (K new_oracle) mc,
                                       new_ffi))
                        | _ -> NONE)))`;;

let find_next_interference_ind = cake_ind "find_next_interference";;

(* the limit of find_next_interference over all clocks *)
let next_interference_def = cake_def
  `next_interference (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) =
     some res. ?k. find_next_interference mc ffi k ms = SOME res`;;

(* the sequence of interference applications of a run *)
let interference_app_seq_def = cake_def
  `(interference_app_seq (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) 0 =
      next_interference mc ffi ms) /\
   (interference_app_seq mc ffi ms (SUC n) =
      match next_interference mc ffi ms with
        NONE -> NONE
      | SOME (app,mc',ffi') -> interference_app_seq mc' ffi' (app_post app) n)`;;

let interference_app_seq_ind = cake_ind "interference_app_seq";;

(* number of applications satisfying P among the first n applications *)
let interference_count_def = cake_def
  `(interference_count (P:(A,B)interference_app->bool) (mc:(A,B,C)machine_config)
      (ffi:(FFI)ffi_state) (ms:B) 0 = 0) /\
   (interference_count P mc ffi ms (SUC n) =
      interference_count P mc ffi ms n +
      (match interference_app_seq mc ffi ms n with
         SOME (app,mc',ffi') -> if P app then 1 else 0
       | NONE -> 0))`;;

(* position in the application sequence of the k-th application           *)
(* satisfying P                                                              *)
let interference_pos_def = cake_def
  `interference_pos (P:(A,B)interference_app->bool) (mc:(A,B,C)machine_config)
     (ffi:(FFI)ffi_state) (ms:B) k =
     some n. interference_count P mc ffi ms n = k /\
             ?app mc' ffi'.
               interference_app_seq mc ffi ms n = SOME (app,mc',ffi') /\ P app`;;

(* the lab-level oracle sequences, constructed from the machine run:        *)
(* caller-saved register and FP-register residues are read off the post    *)
(* state of each application; callee-saved (and avoid / out-of-range)       *)
(* registers are marked NONE, i.e. preserved                                 *)
let target_io_regs_def = cake_def
  `target_io_regs (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) k
     (name:ffiname) r =
     match interference_pos is_ffi_app mc ffi ms k with
       NONE -> NONE
     | SOME n ->
         (match interference_app_seq mc ffi ms n with
            SOME (FfiApp index new_bytes ms_pre ms_post,mc',ffi') ->
              (if MEM r (machine_config_callee_saved_regs mc) \/
                  ~(r < asm_config_reg_count (target_config (machine_config_target mc))) \/
                  MEM r (asm_config_avoid_regs (target_config (machine_config_target mc)))
               then NONE
               else SOME (target_get_reg (machine_config_target mc) ms_post r))
          | _ -> NONE)`;;

let target_io_fp_regs_def = cake_def
  `target_io_fp_regs (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) k (i:num) =
     match interference_pos is_ffi_app mc ffi ms k with
       NONE -> (word 0:int64)
     | SOME n ->
         (match interference_app_seq mc ffi ms n with
            SOME (FfiApp index new_bytes ms_pre ms_post,mc',ffi') ->
              target_get_fp_reg (machine_config_target mc) ms_post i
          | _ -> word 0)`;;

let target_cc_regs_def = cake_def
  `target_cc_regs (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) k r =
     match interference_pos (\app. ~is_ffi_app app) mc ffi ms k with
       NONE -> NONE
     | SOME n ->
         (match interference_app_seq mc ffi ms n with
            SOME (CcApp a1 a2 ms_pre ms_post,mc',ffi') ->
              (if MEM r (machine_config_callee_saved_regs mc) \/
                  r = machine_config_ptr_reg mc \/
                  ~(r < asm_config_reg_count (target_config (machine_config_target mc))) \/
                  MEM r (asm_config_avoid_regs (target_config (machine_config_target mc)))
               then NONE
               else SOME (target_get_reg (machine_config_target mc) ms_post r))
          | _ -> NONE)`;;

let target_cc_fp_regs_def = cake_def
  `target_cc_fp_regs (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) k (i:num) =
     match interference_pos (\app. ~is_ffi_app app) mc ffi ms k with
       NONE -> (word 0:int64)
     | SOME n ->
         (match interference_app_seq mc ffi ms n with
            SOME (CcApp a1 a2 ms_pre ms_post,mc',ffi') ->
              target_get_fp_reg (machine_config_target mc) ms_post i
          | _ -> word 0)`;;

(* HOL4 DEEP_INTRO_TAC some_intro: abstract the goal over its first some  *)
(* term and use some_intro                                                 *)

let LABPROPSAUX_SOME_INTRO_TAC : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> is_comb t &&
                       (try fst(dest_const(rator t)) = "some" with Failure _ -> false)) w in
  let v = genvar(type_of t) in
  let th = BETA_CONV (mk_comb(mk_abs(v,subst [v,t] w),t)) in
  (CONV_TAC(K(SYM th)) THEN MATCH_MP_TAC some_intro THEN
   CONV_TAC(DEPTH_CONV BETA_CONV)) g;;

let find_next_interference_mono = prove
 (`!k (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) res i.
     find_next_interference mc ffi k ms = SOME res ==>
     find_next_interference mc ffi (k + i) ms = SOME res`,
  INDUCT_TAC THENL
   [ONCE_REWRITE_TAC[find_next_interference_def] THEN REWRITE_TAC[option_DISTINCT];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[find_next_interference_def] THEN
  REWRITE_TAC[ADD_CLAUSES; NOT_SUC; SUC_SUB1; apply_oracle_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT TOP_CASE_TAC THEN ASM_MESON_TAC[]);;

let find_next_interference_unique = prove
 (`find_next_interference (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) k1 (ms:B) =
     SOME res1 /\
   find_next_interference mc ffi k2 ms = SOME res2 ==>
   res1 = res2`,
  STRIP_TAC THEN
  SUBGOAL_THEN
   `SOME (res1:(A,B)interference_app#(A,B,C)machine_config#(FFI)ffi_state) = SOME res2`
    (fun th -> MESON_TAC[th; injectivity "option"]) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `find_next_interference (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state)
                (k1 + k2) (ms:B)` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC find_next_interference_mono THEN
    ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC find_next_interference_mono THEN
    ASM_REWRITE_TAC[]]);;

let next_interference_intro = prove
 (`find_next_interference (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) k (ms:B) =
     SOME res ==>
   next_interference mc ffi ms = SOME res`,
  REWRITE_TAC[next_interference_def] THEN DISCH_TAC THEN
  LABPROPSAUX_SOME_INTRO_TAC THEN REWRITE_TAC[injectivity "option"; option_DISTINCT] THEN
  ASM_MESON_TAC[find_next_interference_unique]);;

let next_interference_shift = prove
 (`(!k. find_next_interference (mc1:(A,B,C)machine_config) (ffi1:(FFI)ffi_state)
          (k + l) (ms1:B) =
        find_next_interference mc2 ffi2 k ms2) ==>
   next_interference mc1 ffi1 ms1 = next_interference mc2 ffi2 ms2`,
  REWRITE_TAC[next_interference_def] THEN DISCH_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[find_next_interference_mono]);;

let find_next_interference_const = prove
 (`!k (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) app mc' ffi'.
     find_next_interference mc ffi k ms = SOME (app,mc',ffi') ==>
     machine_config_target mc' = machine_config_target mc /\
     machine_config_callee_saved_regs mc' = machine_config_callee_saved_regs mc /\
     machine_config_ptr_reg mc' = machine_config_ptr_reg mc`,
  INDUCT_TAC THENL
   [ONCE_REWRITE_TAC[find_next_interference_def] THEN REWRITE_TAC[option_DISTINCT];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[find_next_interference_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; apply_oracle_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; injectivity "option"; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN SIMP[] THEN RES_TAC THEN FS[]);;

let next_interference_const = prove
 (`next_interference (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) =
     SOME (app,mc',ffi') ==>
   machine_config_target mc' = machine_config_target mc /\
   machine_config_callee_saved_regs mc' = machine_config_callee_saved_regs mc /\
   machine_config_ptr_reg mc' = machine_config_ptr_reg mc`,
  REWRITE_TAC[next_interference_def] THEN LABPROPSAUX_SOME_INTRO_TAC THEN
  REWRITE_TAC[injectivity "option"; option_DISTINCT] THEN
  MESON_TAC[find_next_interference_const]);;

let interference_app_seq_EQ = prove
 (`next_interference (mc1:(A,B,C)machine_config) (ffi1:(FFI)ffi_state) (ms1:B) =
   next_interference mc2 ffi2 ms2 ==>
   !n. interference_app_seq mc1 ffi1 ms1 n = interference_app_seq mc2 ffi2 ms2 n`,
  DISCH_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[interference_app_seq_def]);;

let interference_app_seq_tail = prove
 (`next_interference (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) =
     SOME (app,mc',ffi') ==>
   !n. interference_app_seq mc ffi ms (SUC n) =
       interference_app_seq mc' ffi' (app_post app) n`,
  DISCH_TAC THEN ASM_REWRITE_TAC[interference_app_seq_def] THEN CASE_REWRITE_TAC[]);;

let interference_count_mono = prove
 (`!i m. interference_count P (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) m <=
         interference_count P mc ffi ms (m + i)`,
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; LE_REFL; interference_count_def] THEN
  GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ARITH_TAC);;

let interference_count_lt = prove
 (`interference_app_seq (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) n =
     SOME (app,mc',ffi') /\ P app /\ n < n2 ==>
   interference_count P mc ffi ms n < interference_count P mc ffi ms n2`,
  STRIP_TAC THEN
  SUBGOAL_THEN `interference_count P (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state)
                  (ms:B) (SUC n) = interference_count P mc ffi ms n + 1`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[interference_count_def] THEN CASE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?i. n2 = SUC n + i` (X_CHOOSE_THEN `i:num` SUBST1_TAC) THENL
   [EXISTS_TAC `n2 - SUC n` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`P:(A,B)interference_app->bool`; `mc:(A,B,C)machine_config`;
                 `ffi:(FFI)ffi_state`; `ms:B`; `i:num`; `SUC n`]
    (GEN_ALL interference_count_mono)) THEN
  ASM_ARITH_TAC);;

let interference_pos_unique = prove
 (`interference_app_seq (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) n1 =
     SOME (app1,mc1',ffi1') /\ P app1 /\
   interference_app_seq mc ffi ms n2 = SOME (app2,mc2',ffi2') /\ P app2 /\
   interference_count P mc ffi ms n1 = interference_count P mc ffi ms n2 ==>
   n1 = n2`,
  REPEAT STRIP_TAC THEN CCONTR_TAC THEN
  SUBGOAL_THEN `n1 < n2 \/ n2 < n1` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    ASM_MESON_TAC[interference_count_lt; LT_REFL];
    ASM_MESON_TAC[interference_count_lt; LT_REFL]]);;

let interference_count_tail = prove
 (`next_interference (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) =
     SOME (app0,mcc,ffic) ==>
   !n. interference_count P mc ffi ms (SUC n) =
       (if P app0 then 1 else 0) + interference_count P mcc ffic (app_post app0) n`,
  DISCH_TAC THEN INDUCT_TAC THENL
   [ASM_REWRITE_TAC[interference_count_def; interference_app_seq_def] THEN
    CASE_REWRITE_TAC[] THEN ARITH_TAC;
    ONCE_REWRITE_TAC[interference_count_def] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP interference_app_seq_tail th]) THEN
    ARITH_TAC]);;

let interference_pos_head = prove
 (`next_interference (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) =
     SOME (app0,mcc,ffic) /\ P app0 ==>
   interference_pos P mc ffi ms 0 = SOME 0`,
  STRIP_TAC THEN
  SUBGOAL_THEN `interference_app_seq (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state)
                  (ms:B) 0 = SOME (app0,mcc,ffic)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[interference_app_seq_def]; ALL_TAC] THEN
  REWRITE_TAC[interference_pos_def] THEN LABPROPSAUX_SOME_INTRO_TAC THEN
  REWRITE_TAC[injectivity "option"; option_DISTINCT] THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN STRIP_TAC THEN CCONTR_TAC THEN
    SUBGOAL_THEN `0 < n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(MATCH_MP interference_count_lt (end_itlist CONJ
      [ASSUME `interference_app_seq (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state)
                 (ms:B) 0 = SOME (app0,mcc,ffic)`;
       ASSUME `(P:(A,B)interference_app->bool) app0`; ASSUME `0 < n`])) THEN
    ASM_REWRITE_TAC[interference_count_def; LT_REFL];
    DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[interference_count_def] THEN
    ASM_MESON_TAC[]]);;

let interference_pos_tail_hit = prove
 (`next_interference (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) =
     SOME (app0,mcc,ffic) /\ P app0 ==>
   interference_pos P mc ffi ms (SUC k) =
   OPTION_MAP SUC (interference_pos P mcc ffic (app_post app0) k)`,
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP interference_app_seq_tail) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP interference_count_tail) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[interference_pos_def] THEN LABPROPSAUX_SOME_INTRO_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THENL
     [REWRITE_TAC[interference_count_def; ARITH_RULE `~(0 = SUC k)`];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 + m = SUC k <=> m = k`] THEN STRIP_TAC THEN
    LABPROPSAUX_SOME_INTRO_TAC THEN
    REWRITE_TAC[OPTION_MAP_DEF; injectivity "option"; option_DISTINCT; SUC_INJ] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC(GEN_ALL interference_pos_unique) THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    DISCH_TAC THEN LABPROPSAUX_SOME_INTRO_TAC THEN
    REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC m`) THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 + m = SUC k <=> m = k`] THEN ASM_MESON_TAC[]]);;

let interference_pos_tail_miss = prove
 (`next_interference (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) =
     SOME (app0,mcc,ffic) /\ ~P app0 ==>
   interference_pos P mc ffi ms k =
   OPTION_MAP SUC (interference_pos P mcc ffic (app_post app0) k)`,
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP interference_app_seq_tail) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP interference_count_tail) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
  REWRITE_TAC[interference_pos_def] THEN LABPROPSAUX_SOME_INTRO_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THENL
     [ASM_REWRITE_TAC[interference_app_seq_def; injectivity "option"; PAIR_EQ] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    LABPROPSAUX_SOME_INTRO_TAC THEN
    REWRITE_TAC[OPTION_MAP_DEF; injectivity "option"; option_DISTINCT; SUC_INJ] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC(GEN_ALL interference_pos_unique) THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    DISCH_TAC THEN LABPROPSAUX_SOME_INTRO_TAC THEN
    REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC m`) THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* rewrite with the assumptions and thl and reduce case constants, until  *)
(* nothing changes                                                          *)

let LABPROPSAUX_NORM_TAC thl =
  REPEAT(CHANGED_TAC(ASM_REWRITE_TAC thl THEN CASE_REWRITE_TAC[]));;

(* a case split on OPTION_MAP f x is a case split on x *)

let LABPROPSAUX_option_CASE_MAP = prove
 (`!(f:A->B) x (n:C) s. option_CASE (OPTION_MAP f x) n s = option_CASE x n (\y. s (f y))`,
  GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[OPTION_MAP_DEF] THEN
  CASE_REWRITE_TAC[]);;

let constructed_oracles_ffi_step = prove
 (`next_interference (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) =
     SOME (FfiApp index new_bytes ms_pre ms_post,mc',ffi') ==>
   target_io_regs mc ffi ms 0 name r =
     (if MEM r (machine_config_callee_saved_regs mc) \/
         ~(r < asm_config_reg_count (target_config (machine_config_target mc))) \/
         MEM r (asm_config_avoid_regs (target_config (machine_config_target mc)))
      then NONE else SOME (target_get_reg (machine_config_target mc) ms_post r)) /\
   target_io_fp_regs mc ffi ms 0 i =
     target_get_fp_reg (machine_config_target mc) ms_post i /\
   target_io_regs mc ffi ms (SUC k) name r = target_io_regs mc' ffi' ms_post k name r /\
   target_io_fp_regs mc ffi ms (SUC k) i = target_io_fp_regs mc' ffi' ms_post k i /\
   target_cc_regs mc ffi ms k r = target_cc_regs mc' ffi' ms_post k r /\
   target_cc_fp_regs mc ffi ms k i = target_cc_fp_regs mc' ffi' ms_post k i`,
  DISCH_TAC THEN
  FIRST_ASSUM(fun hyp ->
    let app = `FfiApp index new_bytes ms_pre ms_post:(A,B)interference_app` in
    let th1 = EQT_ELIM(REWRITE_CONV[is_ffi_app_def]
                (mk_comb(`is_ffi_app:(A,B)interference_app->bool`,app))) in
    let th2 = EQT_ELIM(REWRITE_CONV[is_ffi_app_def]
                (mk_neg(mk_comb(`\app:(A,B)interference_app. ~is_ffi_app app`,app)))) in
    MAP_EVERY (ASSUME_TAC o REWRITE_RULE[app_post_def])
     [MATCH_MP next_interference_const hyp;
      MATCH_MP interference_pos_head (CONJ hyp th1);
      GEN `k:num` (MATCH_MP interference_pos_tail_hit (CONJ hyp th1));
      GEN `k:num` (MATCH_MP interference_pos_tail_miss (CONJ hyp th2));
      MATCH_MP interference_app_seq_tail hyp]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  REWRITE_TAC[target_io_regs_def; target_io_fp_regs_def; target_cc_regs_def;
              target_cc_fp_regs_def] THEN
  REPEAT CONJ_TAC THEN
  REPEAT(LABPROPSAUX_NORM_TAC [LABPROPSAUX_option_CASE_MAP; CONJUNCT1 interference_app_seq_def] THEN
         TOP_CASE_TAC) THEN
  LABPROPSAUX_NORM_TAC [LABPROPSAUX_option_CASE_MAP; CONJUNCT1 interference_app_seq_def]);;

let constructed_oracles_cc_step = prove
 (`next_interference (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) =
     SOME (CcApp a1 a2 ms_pre ms_post,mc',ffi') ==>
   target_cc_regs mc ffi ms 0 r =
     (if MEM r (machine_config_callee_saved_regs mc) \/ r = machine_config_ptr_reg mc \/
         ~(r < asm_config_reg_count (target_config (machine_config_target mc))) \/
         MEM r (asm_config_avoid_regs (target_config (machine_config_target mc)))
      then NONE else SOME (target_get_reg (machine_config_target mc) ms_post r)) /\
   target_cc_fp_regs mc ffi ms 0 i =
     target_get_fp_reg (machine_config_target mc) ms_post i /\
   target_cc_regs mc ffi ms (SUC k) r = target_cc_regs mc' ffi' ms_post k r /\
   target_cc_fp_regs mc ffi ms (SUC k) i = target_cc_fp_regs mc' ffi' ms_post k i /\
   target_io_regs mc ffi ms k name r = target_io_regs mc' ffi' ms_post k name r /\
   target_io_fp_regs mc ffi ms k i = target_io_fp_regs mc' ffi' ms_post k i`,
  DISCH_TAC THEN
  FIRST_ASSUM(fun hyp ->
    let app = `CcApp a1 a2 ms_pre ms_post:(A,B)interference_app` in
    let th1 = EQT_ELIM(REWRITE_CONV[is_ffi_app_def]
                (mk_comb(`\app:(A,B)interference_app. ~is_ffi_app app`,app))) in
    let th2 = EQT_ELIM(REWRITE_CONV[is_ffi_app_def]
                (mk_neg(mk_comb(`is_ffi_app:(A,B)interference_app->bool`,app)))) in
    MAP_EVERY (ASSUME_TAC o REWRITE_RULE[app_post_def])
     [MATCH_MP next_interference_const hyp;
      MATCH_MP interference_pos_head (CONJ hyp th1);
      GEN `k:num` (MATCH_MP interference_pos_tail_hit (CONJ hyp th1));
      GEN `k:num` (MATCH_MP interference_pos_tail_miss (CONJ hyp th2));
      MATCH_MP interference_app_seq_tail hyp]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  REWRITE_TAC[target_io_regs_def; target_io_fp_regs_def; target_cc_regs_def;
              target_cc_fp_regs_def] THEN
  REPEAT CONJ_TAC THEN
  REPEAT(LABPROPSAUX_NORM_TAC [LABPROPSAUX_option_CASE_MAP;
                               CONJUNCT1 interference_app_seq_def] THEN
         TOP_CASE_TAC) THEN
  LABPROPSAUX_NORM_TAC [LABPROPSAUX_option_CASE_MAP; CONJUNCT1 interference_app_seq_def]);;

let interference_count_EQ = prove
 (`next_interference (mc1:(A,B,C)machine_config) (ffi1:(FFI)ffi_state) (ms1:B) =
   next_interference mc2 ffi2 ms2 ==>
   !n. interference_count P mc1 ffi1 ms1 n = interference_count P mc2 ffi2 ms2 n`,
  DISCH_THEN(ASSUME_TAC o MATCH_MP interference_app_seq_EQ) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[interference_count_def]);;

let constructed_oracles_EQ = prove
 (`next_interference (mc1:(A,B,C)machine_config) (ffi1:(FFI)ffi_state) (ms1:B) =
   next_interference mc2 ffi2 ms2 /\
   machine_config_target mc1 = machine_config_target mc2 /\
   machine_config_callee_saved_regs mc1 = machine_config_callee_saved_regs mc2 /\
   machine_config_ptr_reg mc1 = machine_config_ptr_reg mc2 ==>
   target_io_regs mc1 ffi1 ms1 = target_io_regs mc2 ffi2 ms2 /\
   target_io_fp_regs mc1 ffi1 ms1 = target_io_fp_regs mc2 ffi2 ms2 /\
   target_cc_regs mc1 ffi1 ms1 = target_cc_regs mc2 ffi2 ms2 /\
   target_cc_fp_regs mc1 ffi1 ms1 = target_cc_fp_regs mc2 ffi2 ms2`,
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP interference_app_seq_EQ) THEN
  SUBGOAL_THEN `!P k. interference_pos P (mc1:(A,B,C)machine_config)
                        (ffi1:(FFI)ffi_state) (ms1:B) k =
                      interference_pos P (mc2:(A,B,C)machine_config)
                        (ffi2:(FFI)ffi_state) (ms2:B) k` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[interference_pos_def] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP interference_count_EQ th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM; target_io_regs_def; target_io_fp_regs_def; target_cc_regs_def;
              target_cc_fp_regs_def] THEN
  ASM_REWRITE_TAC[]);;

let target_io_regs_callee_saved = prove
 (`MEM r (machine_config_callee_saved_regs mc) ==>
   target_io_regs (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) k name r = NONE`,
  DISCH_TAC THEN REWRITE_TAC[target_io_regs_def] THEN
  REPEAT(LABPROPSAUX_NORM_TAC [] THEN TOP_CASE_TAC) THEN LABPROPSAUX_NORM_TAC []);;

let target_cc_regs_callee_saved = prove
 (`MEM r (machine_config_callee_saved_regs mc) ==>
   target_cc_regs (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) k r = NONE`,
  DISCH_TAC THEN REWRITE_TAC[target_cc_regs_def] THEN
  REPEAT(LABPROPSAUX_NORM_TAC [] THEN TOP_CASE_TAC) THEN LABPROPSAUX_NORM_TAC []);;

(* one step of find_next_interference from a state that interferes *)

let LABPROPSAUX_FNI_STEP_TAC : tactic =
  MATCH_MP_TAC(GEN_ALL next_interference_intro) THEN EXISTS_TAC `1` THEN
  ONCE_REWRITE_TAC[find_next_interference_def] THEN
  REWRITE_TAC[ARITH_RULE `~(1 = 0)`; apply_oracle_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN LABPROPSAUX_NORM_TAC [];;

(* rewrite the other assumptions with the assumptions EL i l = c *)

let LABPROPSAUX_EL_ASM_TAC : tactic = fun (asl,w as g) ->
  let ths = filter (fun th -> let c = concl th in is_eq c &&
                      (try fst(dest_const(fst(strip_comb(lhs c)))) = "EL"
                       with Failure _ -> false)) (map snd asl) in
  RULE_ASSUM_TAC(fun th -> if exists (fun t -> concl t = concl th) ths then th
                           else REWRITE_RULE ths th) g;;

let next_interference_ExtCall = prove
 (`~(target_get_pc (machine_config_target mc) ms IN
     machine_config_prog_addresses mc DIFF set_of_list (machine_config_ffi_entry_pcs mc)) /\
   ~(target_get_pc (machine_config_target mc) ms = machine_config_halt_pc mc) /\
   ~(target_get_pc (machine_config_target mc) ms = machine_config_ccache_pc mc) /\
   find_index (target_get_pc (machine_config_target mc) ms)
     (machine_config_ffi_entry_pcs mc) 0 = SOME index /\
   EL index (machine_config_ffi_names mc) = ExtCall name /\
   ALOOKUP (machine_config_mmio_info mc) index = NONE /\
   read_ffi_bytearrays mc ms = (SOME bytes,SOME bytes2) /\
   call_FFI ffi (ExtCall name) bytes bytes2 = FFI_return new_ffi new_bytes ==>
   next_interference (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) =
   SOME (FfiApp index new_bytes ms (machine_config_ffi_interfer mc 0 (index,new_bytes,ms)),
         machine_config_ffi_interfer_fupd (K (shift_seq 1 (machine_config_ffi_interfer mc)))
           mc,
         new_ffi)`,
  STRIP_TAC THEN LABPROPSAUX_FNI_STEP_TAC);;

let next_interference_ccache = prove
 (`~(target_get_pc (machine_config_target mc) ms IN
     machine_config_prog_addresses mc DIFF set_of_list (machine_config_ffi_entry_pcs mc)) /\
   ~(target_get_pc (machine_config_target mc) ms = machine_config_halt_pc mc) /\
   target_get_pc (machine_config_target mc) ms = machine_config_ccache_pc mc ==>
   next_interference (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) =
   SOME (CcApp (target_get_reg (machine_config_target mc) ms (machine_config_ptr_reg mc))
               (target_get_reg (machine_config_target mc) ms (machine_config_len_reg mc)) ms
               (machine_config_ccache_interfer mc 0
                  (target_get_reg (machine_config_target mc) ms (machine_config_ptr_reg mc),
                   target_get_reg (machine_config_target mc) ms (machine_config_len_reg mc),
                   ms)),
         machine_config_ccache_interfer_fupd
           (K (shift_seq 1 (machine_config_ccache_interfer mc))) mc,
         ffi)`,
  STRIP_TAC THEN LABPROPSAUX_FNI_STEP_TAC);;

let next_interference_MappedRead = prove
 (`~(target_get_pc (machine_config_target mc) ms IN
     machine_config_prog_addresses mc DIFF set_of_list (machine_config_ffi_entry_pcs mc)) /\
   ~(target_get_pc (machine_config_target mc) ms = machine_config_halt_pc mc) /\
   ~(target_get_pc (machine_config_target mc) ms = machine_config_ccache_pc mc) /\
   find_index (target_get_pc (machine_config_target mc) ms)
     (machine_config_ffi_entry_pcs mc) 0 = SOME index /\
   EL index (machine_config_ffi_names mc) = SharedMem MappedRead /\
   ALOOKUP (machine_config_mmio_info mc) index = SOME (nb,Addr r off,reg,pc') /\
   (nb = word 0 ==>
    val (word_add (target_get_reg (machine_config_target mc) ms r) off) MOD
      (dimindex (:A) DIV 8) = 0) /\
   word_add (target_get_reg (machine_config_target mc) ms r) off IN
     machine_config_shared_addresses mc /\
   is_valid_mapped_read (target_get_pc (machine_config_target mc) ms) nb (Addr r off)
     reg pc' (machine_config_target mc) ms (machine_config_prog_addresses mc) /\
   call_FFI ffi (EL index (machine_config_ffi_names mc)) [nb]
     (word_to_bytes (word_add (target_get_reg (machine_config_target mc) ms r) off) F) =
     FFI_return new_ffi new_bytes ==>
   next_interference (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) =
   SOME (FfiApp index new_bytes ms (machine_config_ffi_interfer mc 0 (index,new_bytes,ms)),
         machine_config_ffi_interfer_fupd (K (shift_seq 1 (machine_config_ffi_interfer mc)))
           mc,
         new_ffi)`,
  STRIP_TAC THEN ASM_CASES_TAC `nb:byte = word 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]); ALL_TAC] THEN
  LABPROPSAUX_EL_ASM_TAC THEN LABPROPSAUX_FNI_STEP_TAC);;

let next_interference_MappedWrite = prove
 (`~(target_get_pc (machine_config_target mc) ms IN
     machine_config_prog_addresses mc DIFF set_of_list (machine_config_ffi_entry_pcs mc)) /\
   ~(target_get_pc (machine_config_target mc) ms = machine_config_halt_pc mc) /\
   ~(target_get_pc (machine_config_target mc) ms = machine_config_ccache_pc mc) /\
   find_index (target_get_pc (machine_config_target mc) ms)
     (machine_config_ffi_entry_pcs mc) 0 = SOME index /\
   EL index (machine_config_ffi_names mc) = SharedMem MappedWrite /\
   ALOOKUP (machine_config_mmio_info mc) index = SOME (nb,Addr r off,reg,pc') /\
   (nb = word 0 ==>
    val (word_add (target_get_reg (machine_config_target mc) ms r) off) MOD
      (dimindex (:A) DIV 8) = 0) /\
   word_add (target_get_reg (machine_config_target mc) ms r) off IN
     machine_config_shared_addresses mc /\
   is_valid_mapped_write (target_get_pc (machine_config_target mc) ms) nb (Addr r off)
     reg pc' (machine_config_target mc) ms (machine_config_prog_addresses mc) /\
   call_FFI ffi (EL index (machine_config_ffi_names mc)) [nb]
     (APPEND (let w = target_get_reg (machine_config_target mc) ms reg in
              if nb = word 0 then word_to_bytes w F
              else word_to_bytes_aux (val nb) w F)
             (word_to_bytes (word_add (target_get_reg (machine_config_target mc) ms r)
                               off) F)) =
     FFI_return new_ffi new_bytes ==>
   next_interference (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) =
   SOME (FfiApp index new_bytes ms (machine_config_ffi_interfer mc 0 (index,new_bytes,ms)),
         machine_config_ffi_interfer_fupd (K (shift_seq 1 (machine_config_ffi_interfer mc)))
           mc,
         new_ffi)`,
  STRIP_TAC THEN RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  ASM_CASES_TAC `nb:byte = word 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]); ALL_TAC] THEN
  LABPROPSAUX_EL_ASM_TAC THEN LABPROPSAUX_FNI_STEP_TAC);;

let next_interference_SharedMem = prove
 (`~(target_get_pc (machine_config_target mc) ms IN
     machine_config_prog_addresses mc DIFF set_of_list (machine_config_ffi_entry_pcs mc)) /\
   ~(target_get_pc (machine_config_target mc) ms = machine_config_halt_pc mc) /\
   ~(target_get_pc (machine_config_target mc) ms = machine_config_ccache_pc mc) /\
   find_index (target_get_pc (machine_config_target mc) ms)
     (machine_config_ffi_entry_pcs mc) 0 = SOME index /\
   EL index (machine_config_ffi_names mc) = SharedMem op /\
   ALOOKUP (machine_config_mmio_info mc) index = SOME (nb,Addr r off,reg,pc') /\
   (nb = word 0 ==>
    val (word_add (target_get_reg (machine_config_target mc) ms r) off) MOD
      (dimindex (:A) DIV 8) = 0) /\
   word_add (target_get_reg (machine_config_target mc) ms r) off IN
     machine_config_shared_addresses mc /\
   (op = MappedRead ==>
    is_valid_mapped_read (target_get_pc (machine_config_target mc) ms) nb (Addr r off)
      reg pc' (machine_config_target mc) ms (machine_config_prog_addresses mc) /\
    call_FFI ffi (EL index (machine_config_ffi_names mc)) [nb]
      (word_to_bytes (word_add (target_get_reg (machine_config_target mc) ms r) off) F) =
      FFI_return new_ffi new_bytes) /\
   (op = MappedWrite ==>
    is_valid_mapped_write (target_get_pc (machine_config_target mc) ms) nb (Addr r off)
      reg pc' (machine_config_target mc) ms (machine_config_prog_addresses mc) /\
    call_FFI ffi (EL index (machine_config_ffi_names mc)) [nb]
      (APPEND (let w = target_get_reg (machine_config_target mc) ms reg in
               if nb = word 0 then word_to_bytes w F
               else word_to_bytes_aux (val nb) w F)
              (word_to_bytes (word_add (target_get_reg (machine_config_target mc) ms r)
                                off) F)) =
      FFI_return new_ffi new_bytes) ==>
   next_interference (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) =
   SOME (FfiApp index new_bytes ms (machine_config_ffi_interfer mc 0 (index,new_bytes,ms)),
         machine_config_ffi_interfer_fupd (K (shift_seq 1 (machine_config_ffi_interfer mc)))
           mc,
         new_ffi)`,
  CASES_ON `op:shmem_op` THEN REWRITE_TAC[distinctness "shmem_op"] THEN STRIP_TAC THENL
   [MATCH_MP_TAC(GEN_ALL next_interference_MappedRead);
    MATCH_MP_TAC(GEN_ALL next_interference_MappedWrite)] THEN
  ASM_MESON_TAC[]);;

(* helpers for evaluate_EQ_evaluate_lemma: the encoded instruction at a pc *)
(* inside it, and one step of target_evaluate and find_next_interference   *)

let LABPROPSAUX_encoded_bytes_in_mem = prove
 (`!(c:(A)asm_config) (pc:A word) m prog pcs i init_pc k.
     pc = word_add init_pc (word (k * 2 EXP asm_config_code_alignment c)) /\
     k * 2 EXP asm_config_code_alignment c < LENGTH (asm_config_encode c i) /\
     bytes_in_memory init_pc (asm_config_encode c i) m (prog DIFF pcs)
     ==> encoded_bytes_in_mem c pc m prog`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[encoded_bytes_in_mem_def] THEN
  MAP_EVERY EXISTS_TAC [`i:(A)asm`; `k:num`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(GEN_ALL bytes_in_memory_SUBSET) THEN
  EXISTS_TAC `prog DIFF pcs:A word->bool` THEN REWRITE_TAC[DIFF_SUBSET] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                         "bytes_in_memory" with Failure _ -> false)) THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o LAND_CONV)
    [GSYM(ISPECL [`k * 2 EXP asm_config_code_alignment (c:(A)asm_config)`;
                  `asm_config_encode (c:(A)asm_config) i`] TAKE_DROP)] THEN
  REWRITE_TAC[bytes_in_memory_APPEND] THEN
  ASM_SIMP_TAC[LENGTH_TAKE; LT_IMP_LE]);;

let LABPROPSAUX_target_step = prove
 (`!(c:(A,B,C)machine_config) (io:(FFI)ffi_state) ms1 K.
     target_get_pc (machine_config_target c) ms1 IN
       (machine_config_prog_addresses c DIFF set_of_list (machine_config_ffi_entry_pcs c)) /\
     encoded_bytes_in_mem (target_config (machine_config_target c))
       (target_get_pc (machine_config_target c) ms1)
       (target_get_byte (machine_config_target c) ms1) (machine_config_prog_addresses c) /\
     target_state_ok (machine_config_target c) ms1 /\
     target_state_ok (machine_config_target c) (target_next (machine_config_target c) ms1) /\
     target_state_ok (machine_config_target c)
       (machine_config_next_interfer c 0 (target_next (machine_config_target c) ms1)) /\
     (!x. ~(x IN machine_config_prog_addresses c) ==>
          target_get_byte (machine_config_target c) (target_next (machine_config_target c) ms1)
            x =
          target_get_byte (machine_config_target c) ms1 x)
     ==> target_evaluate c io (SUC K) ms1 =
         target_evaluate (shift_interfer 1 c) io K
           (machine_config_next_interfer c 0 (target_next (machine_config_target c) ms1)) /\
         find_next_interference c io (SUC K) ms1 =
         find_next_interference (shift_interfer 1 c) io K
           (machine_config_next_interfer c 0 (target_next (machine_config_target c) ms1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [target_evaluate_def];
    GEN_REWRITE_TAC LAND_CONV [find_next_interference_def]] THEN
  ASM_REWRITE_TAC[NOT_SUC; SUC_SUB1; apply_oracle_def; ALL; shift_interfer_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CASE_REWRITE_TAC[] THEN
  SIMP[] THEN ASM_REWRITE_TAC[]);;

(* the facts of the first step that the base case and the step case of   *)
(* evaluate_EQ_evaluate_lemma share                                        *)

let LABPROPSAUX_EQ_PRELIM_TAC : tactic =
  (* the projection is not changed by the interference oracle *)
  SUBGOAL_THEN `!i ms. target_proj (machine_config_target c) dm
                         (machine_config_next_interfer (c:(A,B,C)machine_config) i ms) =
                       target_proj (machine_config_target c) dm (ms:B)` ASSUME_TAC THENL
   [ASM_MESON_TAC[interference_ok_def]; ALL_TAC] THEN
  (* the bytes outside dm are not changed by the first step *)
  SUBGOAL_THEN `!x. ~(x IN machine_config_prog_addresses c) ==>
                    target_get_byte (machine_config_target c)
                      (target_next (machine_config_target c) ms1) x =
                    target_get_byte (machine_config_target (c:(A,B,C)machine_config))
                      (ms1:B) x` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
                    (ONCE_REWRITE_RULE[CONJ_SYM] asserts2_first)) o
                  check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                       "asserts2" with Failure _ -> false)) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the instruction is encoded at the pc *)
  SUBGOAL_THEN `encoded_bytes_in_mem (target_config (machine_config_target c))
                  (target_get_pc (machine_config_target c) ms1)
                  (target_get_byte (machine_config_target c) ms1)
                  (machine_config_prog_addresses (c:(A,B,C)machine_config))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LABPROPSAUX_encoded_bytes_in_mem THEN
    MAP_EVERY EXISTS_TAC [`set_of_list (machine_config_ffi_entry_pcs (c:(A,B,C)machine_config))`;
                          `i:(A)asm`; `init_pc:A word`; `k:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ALL_TAC;;

let evaluate_EQ_evaluate_lemma = prove
 (`!n ms1 (c:(A,B,C)machine_config).
      target_get_pc (machine_config_target c) ms1 IN
        (machine_config_prog_addresses c DIFF set_of_list (machine_config_ffi_entry_pcs c)) /\
      target_state_ok (machine_config_target c) ms1 /\
      machine_config_prog_addresses c = dm /\
      interference_ok (machine_config_next_interfer c)
        (target_proj (machine_config_target c) dm) /\
      (!s ms. target_state_rel (machine_config_target c) s ms
              ==> target_state_ok (machine_config_target c) ms) /\
      (!ms1 ms2.
         target_proj (machine_config_target c) dm ms1 =
         target_proj (machine_config_target c) dm ms2
         ==> (target_state_ok (machine_config_target c) ms1 <=>
              target_state_ok (machine_config_target c) ms2) /\
             target_get_pc (machine_config_target c) ms1 =
             target_get_pc (machine_config_target c) ms2 /\
             (!a. a IN dm ==> target_get_byte (machine_config_target c) ms1 a =
                              target_get_byte (machine_config_target c) ms2 a)) /\
      (!env. interference_ok env (target_proj (machine_config_target c) dm) ==>
         asserts n (\k s. env k (target_next (machine_config_target c) s)) ms1
           (\ms'. target_state_ok (machine_config_target c) ms' /\
                  (!pc. pc IN all_pcs (LENGTH (asm_config_encode
                                         (target_config (machine_config_target c)) i))
                                init_pc 0
                        ==> target_get_byte (machine_config_target c) ms' pc =
                            target_get_byte (machine_config_target c) ms1 pc) /\
                  target_get_pc (machine_config_target c) ms' IN
                    all_pcs (LENGTH (asm_config_encode
                               (target_config (machine_config_target c)) i)) init_pc
                      (asm_config_code_alignment (target_config (machine_config_target c))))
           (\ms'. target_state_rel (machine_config_target c) (s2:(A)asm_state) ms')) /\
      asserts2 (n + 1) (\k. machine_config_next_interfer c ((n + 1) - k))
        (target_next (machine_config_target c)) ms1
        (\ms1 ms2. !x. ~(x IN dm)
                       ==> target_get_byte (machine_config_target c) ms1 x =
                           target_get_byte (machine_config_target c) ms2 x) /\
      (?k. target_get_pc (machine_config_target c) ms1 =
             word_add init_pc
               (word (k * 2 EXP asm_config_code_alignment
                                  (target_config (machine_config_target c)))) /\
           k * 2 EXP asm_config_code_alignment (target_config (machine_config_target c)) <
             LENGTH (asm_config_encode (target_config (machine_config_target c)) i) /\
           bytes_in_memory init_pc
             (asm_config_encode (target_config (machine_config_target c)) i)
             (target_get_byte (machine_config_target c) ms1)
             (machine_config_prog_addresses c DIFF
              set_of_list (machine_config_ffi_entry_pcs c)))
      ==> ?ms2. !k.
            target_evaluate c (io:(FFI)ffi_state) (k + (n + 1)) ms1 =
            target_evaluate (shift_interfer (n + 1) c) io k ms2 /\
            find_next_interference c io (k + (n + 1)) ms1 =
            find_next_interference (shift_interfer (n + 1) c) io k ms2 /\
            target_state_rel (machine_config_target c) s2 ms2`
,
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN LABPROPSAUX_EQ_PRELIM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o
      SPEC `\i:num. machine_config_next_interfer (c:(A,B,C)machine_config) 0` o
      check (fun th -> is_forall(concl th) &&
                       fst(dest_var(fst(dest_forall(concl th)))) = "env")) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[interference_ok_def]; ALL_TAC] THEN
    REWRITE_TAC[asserts_def] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN DISCH_TAC THEN
    EXISTS_TAC `machine_config_next_interfer (c:(A,B,C)machine_config) 0
                  (target_next (machine_config_target c) ms1)` THEN
    X_GEN_TAC `kk:num` THEN
    ASM_REWRITE_TAC[ARITH_RULE `kk + 0 + 1 = SUC kk`; ARITH_RULE `0 + 1 = 1`] THEN
    MATCH_MP_TAC LABPROPSAUX_target_step THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `target_state_ok (machine_config_target c)
                    (machine_config_next_interfer (c:(A,B,C)machine_config) 0
                      (target_next (machine_config_target c) ms1))` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[]
  ;
    X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
    STRIP_TAC THEN LABPROPSAUX_EQ_PRELIM_TAC THEN
    (* the first step of the run with the oracle value next_interfer c 0 *)
    FIRST_ASSUM(MP_TAC o
      SPEC `\i:num. machine_config_next_interfer (c:(A,B,C)machine_config) 0` o
      check (fun th -> is_forall(concl th) &&
                       fst(dest_var(fst(dest_forall(concl th)))) = "env")) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[interference_ok_def]; ALL_TAC] THEN
    REWRITE_TAC[asserts_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (K ALL_TAC)) THEN
    USE_THEN "ih" (MP_TAC o SPECL
      [`machine_config_next_interfer (c:(A,B,C)machine_config) 0
          (target_next (machine_config_target c) ms1)`;
       `shift_interfer 1 (c:(A,B,C)machine_config)`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[shift_interfer_def; machine_config_INFO.ri_accfupds; K_THM] THEN
      REPEAT CONJ_TAC THENL
       [(* the pc is in the encoded instruction *)
        FIRST_ASSUM(MP_TAC o SPEC `asm_config_code_alignment
                                     (target_config (machine_config_target
                                       (c:(A,B,C)machine_config)))` o
          MATCH_MP bytes_in_memory_all_pcs o
          check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                               "bytes_in_memory" with Failure _ -> false)) THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        REWRITE_TAC[interference_ok_def; shift_seq_def] THEN BETA_TAC THEN
        ASM_REWRITE_TAC[];
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        (* the asserts of the remaining steps *)
        X_GEN_TAC `env:num->B->B` THEN DISCH_TAC THEN
        FIRST_ASSUM(MP_TAC o
          SPEC `\k:num. if k = SUC n then machine_config_next_interfer
                                            (c:(A,B,C)machine_config) 0
                        else (env:num->B->B) k` o
          check (fun th -> is_forall(concl th) &&
                           fst(dest_var(fst(dest_forall(concl th)))) = "env")) THEN
        ANTS_TAC THENL
         [UNDISCH_TAC `interference_ok (env:num->B->B)
                         (target_proj (machine_config_target (c:(A,B,C)machine_config)) dm)` THEN
          REWRITE_TAC[interference_ok_def] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
          BETA_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[asserts_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o CONJUNCT2) THEN MATCH_MP_TAC asserts_WEAKEN THEN
        X_GEN_TAC `j:num` THEN DISCH_TAC THEN CONJ_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN BETA_TAC THEN
          COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
          BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
        (* the asserts2 of the remaining steps *)
        FIRST_X_ASSUM(MP_TAC o
          check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                               "asserts2" with Failure _ -> false)) THEN
        GEN_REWRITE_TAC LAND_CONV [asserts2_def] THEN
        REWRITE_TAC[ARITH_RULE `~(SUC n + 1 = 0)`; ARITH_RULE `(SUC n + 1) - 1 = n + 1`] THEN
        CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[SUB_REFL] THEN
        DISCH_THEN(MP_TAC o CONJUNCT2) THEN
        DISCH_THEN(fun th -> MATCH_MP_TAC
          (MATCH_MP (REWRITE_RULE[IMP_CONJ] asserts2_change_interfer) th)) THEN
        REWRITE_TAC[shift_seq_def] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
        AP_TERM_TAC THEN ASM_ARITH_TAC;
        (* the pc of the next state *)
        FIRST_ASSUM(MP_TAC o
          check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "IN" &&
                               can (find_term (fun t -> try fst(dest_const t) = "all_pcs"
                                                        with Failure _ -> false)) (concl th) &&
                               not (is_forall (concl th))
                           with Failure _ -> false)) THEN
        REWRITE_TAC[all_pcs_thm; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `x:num` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC bytes_in_memory_change_mem THEN
        EXISTS_TAC `target_get_byte (machine_config_target (c:(A,B,C)machine_config)) ms1` THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[all_pcs_thm; IN_ELIM_THM] THEN EXISTS_TAC `j:num` THEN
        ASM_REWRITE_TAC[EXP; MULT_CLAUSES]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `ms2:B`) THEN EXISTS_TAC `ms2:B` THEN X_GEN_TAC `kk:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `kk:num` o
      check (fun th -> is_forall (concl th) &&
                       fst(dest_var(fst(dest_forall(concl th)))) = "k")) THEN
    REWRITE_TAC[shift_interfer_intro; ARITH_RULE `(n + 1) + 1 = SUC n + 1`] THEN
    SUBGOAL_THEN `machine_config_target (shift_interfer 1 c) =
                  machine_config_target (c:(A,B,C)machine_config)` SUBST1_TAC THENL
     [REWRITE_TAC[shift_interfer_def; machine_config_INFO.ri_accfupds]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `kk + SUC n + 1 = SUC (kk + n + 1)`] THEN
    MP_TAC(SPECL [`c:(A,B,C)machine_config`; `io:(FFI)ffi_state`; `ms1:B`; `kk + n + 1`]
      LABPROPSAUX_target_step) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])]
  ]);;

(* HOL4 [local] *)

let enc_ok_not_empty = prove
 (`enc_ok (c:(A)asm_config) /\ asm_ok w c ==> ~(asm_config_encode c w = [])`,
  REWRITE_TAC[enc_ok_def] THEN MESON_TAC[LENGTH_EQ_NIL]);;

let asm_step_IMP_evaluate_step_find_next = prove
 (`!(c:(A,B,C)machine_config) (s1:(A)asm_state) (ms1:B) (io:(FFI)ffi_state) i.
      encoder_correct (machine_config_target c) /\
      machine_config_prog_addresses c = asm_state_mem_domain s1 /\
      ffi_entry_pcs_disjoint c s1
        (LENGTH (asm_config_encode (target_config (machine_config_target c)) i)) /\
      interference_ok (machine_config_next_interfer c)
        (target_proj (machine_config_target c) (asm_state_mem_domain s1)) /\
      asm_step (target_config (machine_config_target c)) s1 i
        (asm i (word_add (asm_state_pc s1)
                  (word (LENGTH (asm_config_encode (target_config (machine_config_target c))
                                   i)))) s1) /\
      target_state_rel (machine_config_target c) s1 ms1 ==>
      ?l ms2. !k.
        target_evaluate c io (k + l) ms1 =
        target_evaluate (shift_interfer l c) io k ms2 /\
        find_next_interference c io (k + l) ms1 =
        find_next_interference (shift_interfer l c) io k ms2 /\
        target_state_rel (machine_config_target c)
          (asm i (word_add (asm_state_pc s1)
                    (word (LENGTH (asm_config_encode
                                     (target_config (machine_config_target c)) i)))) s1)
          ms2 /\
        ~(l = 0)`
,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[encoder_correct_def] o
    check (fun th -> try fst(dest_const(rator(concl th))) = "encoder_correct"
                     with Failure _ -> false)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o REWRITE_RULE[target_ok_def])
    (MP_TAC o SPECL [`s1:(A)asm_state`; `i:(A)asm`;
      `asm i (word_add (asm_state_pc s1)
                (word (LENGTH (asm_config_encode
                                 (target_config (machine_config_target
                                   (c:(A,B,C)machine_config))) i)))) (s1:(A)asm_state)`;
      `ms1:B`])) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[asm_step_def] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "asm_step"
                     with Failure _ -> false)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[target_state_rel_def] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "target_state_rel"
                     with Failure _ -> false)) THEN
  SUBGOAL_THEN `~(asm_config_encode (target_config (machine_config_target
                    (c:(A,B,C)machine_config))) i = [])` ASSUME_TAC THENL
   [MATCH_MP_TAC enc_ok_not_empty THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `ms1:B`; `c:(A,B,C)machine_config`]
    (INST [`asm_state_mem_domain (s1:(A)asm_state)`,`dm:A word->bool`;
           `asm_state_pc (s1:(A)asm_state)`,`init_pc:A word`;
           `asm i (word_add (asm_state_pc s1)
                     (word (LENGTH (asm_config_encode
                                      (target_config (machine_config_target
                                        (c:(A,B,C)machine_config))) i))))
                  (s1:(A)asm_state)`,`s2:(A)asm_state`]
     evaluate_EQ_evaluate_lemma)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [(* the pc is a program address and not an FFI entry *)
      ASM_REWRITE_TAC[IN_DIFF; IN_SET_OF_LIST] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`asm_state_pc (s1:(A)asm_state)`;
                       `asm_config_encode (target_config (machine_config_target
                          (c:(A,B,C)machine_config))) i`;
                       `asm_state_mem (s1:(A)asm_state)`;
                       `asm_state_mem_domain (s1:(A)asm_state)`; `0`]
          bytes_in_memory_in_domain) THEN
        ASM_REWRITE_TAC[WORD_ADD_0; LT_NZ; LENGTH_EQ_NIL];
        FIRST_X_ASSUM(MP_TAC o
          REWRITE_RULE[ffi_entry_pcs_disjoint_def; DISJOINT; EXTENSION; IN_INTER;
                       IN_ELIM_THM; NOT_IN_EMPTY; IN_SET_OF_LIST] o
          check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                               "ffi_entry_pcs_disjoint" with Failure _ -> false)) THEN
        DISCH_THEN(MP_TAC o SPEC `asm_state_pc (s1:(A)asm_state)`) THEN
        MATCH_MP_TAC(TAUT `b ==> ~(a /\ b) ==> ~a`) THEN EXISTS_TAC `0` THEN
        ASM_REWRITE_TAC[WORD_ADD_0; LT_NZ; LENGTH_EQ_NIL]];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[target_state_rel_def] THEN MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`m1:B`; `m2:B`] THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPECL [`m1:B`; `m2:B`; `s1:(A)asm_state`] o
        check (fun th -> is_forall(concl th) &&
                         fst(dest_var(fst(dest_forall(concl th)))) = "ms1")) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
      (* the asserts of the encoder, with the environment reversed *)
      X_GEN_TAC `env:num->B->B` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `\k:num. (env:num->B->B) (n - k)` o
        check (fun th -> is_forall(concl th) &&
                         fst(dest_var(fst(dest_forall(concl th)))) = "env")) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `interference_ok (env:num->B->B)
          (target_proj (machine_config_target (c:(A,B,C)machine_config))
             (asm_state_mem_domain (s1:(A)asm_state)))` THEN
        REWRITE_TAC[interference_ok_def] THEN SIMP_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN MATCH_MP_TAC asserts_WEAKEN THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[ARITH_RULE `j <= n ==> n - (n - j) = j`];
      (* the asserts2 of the encoder with the oracle of the configuration *)
      FIRST_ASSUM(MP_TAC o SPEC `machine_config_next_interfer (c:(A,B,C)machine_config)` o
        check (fun th -> is_forall(concl th) &&
                         fst(dest_var(fst(dest_forall(concl th)))) = "env")) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
      (* the first byte of the encoded instruction is at the pc *)
      EXISTS_TAC `0` THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; LT_NZ; LENGTH_EQ_NIL] THEN
      SUBGOAL_THEN
       `bytes_in_memory (asm_state_pc s1)
          (asm_config_encode (target_config (machine_config_target
            (c:(A,B,C)machine_config))) i)
          (target_get_byte (machine_config_target c) ms1)
          (asm_state_mem_domain (s1:(A)asm_state))` ASSUME_TAC THENL
       [MATCH_MP_TAC bytes_in_memory_change_mem THEN
        EXISTS_TAC `asm_state_mem (s1:(A)asm_state)` THEN ASM_REWRITE_TAC[] THEN
        REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        MATCH_MP_TAC bytes_in_memory_in_domain THEN
        MAP_EVERY EXISTS_TAC
         [`asm_config_encode (target_config (machine_config_target
             (c:(A,B,C)machine_config))) i`;
          `asm_state_mem (s1:(A)asm_state)`] THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC(GEN_ALL bytes_in_memory_DIFF) THEN
        MAP_EVERY EXISTS_TAC
         [`asm_state_mem_domain (s1:(A)asm_state)`;
          `set_of_list (machine_config_ffi_entry_pcs (c:(A,B,C)machine_config))`] THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[ffi_entry_pcs_disjoint_def] o
          check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                               "ffi_entry_pcs_disjoint" with Failure _ -> false)) THEN
        REWRITE_TAC[]]];
    DISCH_THEN(X_CHOOSE_TAC `ms2:B`) THEN
    MAP_EVERY EXISTS_TAC [`n + 1`; `ms2:B`] THEN
    ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ]]
);;

let asm_step_IMP_evaluate_step = prove
 (`!(c:(A,B,C)machine_config) (s1:(A)asm_state) (ms1:B) (io:(FFI)ffi_state) i.
     encoder_correct (machine_config_target c) /\
     machine_config_prog_addresses c = asm_state_mem_domain s1 /\
     ffi_entry_pcs_disjoint c s1
       (LENGTH (asm_config_encode (target_config (machine_config_target c)) i)) /\
     interference_ok (machine_config_next_interfer c)
       (target_proj (machine_config_target c) (asm_state_mem_domain s1)) /\
     asm_step (target_config (machine_config_target c)) s1 i
       (asm i (word_add (asm_state_pc s1)
                 (word (LENGTH (asm_config_encode (target_config (machine_config_target c))
                                  i)))) s1) /\
     target_state_rel (machine_config_target c) s1 ms1 ==>
     ?l ms2.
       (!k. target_evaluate c io (k + l) ms1 =
            target_evaluate (shift_interfer l c) io k ms2) /\
       target_state_rel (machine_config_target c)
         (asm i (word_add (asm_state_pc s1)
                   (word (LENGTH (asm_config_encode
                                    (target_config (machine_config_target c)) i)))) s1)
         ms2 /\
       ~(l = 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:(A,B,C)machine_config`; `s1:(A)asm_state`; `ms1:B`;
                `io:(FFI)ffi_state`; `i:(A)asm`] asm_step_IMP_evaluate_step_find_next) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* basic properties *)

(* HOL4: evaluate_add_clock *)

let target_evaluate_add_clock = prove
 (`!(mc_conf:(A,B,C)machine_config) (ffi:(FFI)ffi_state) k (ms:B) k1 r ms1 st1.
     target_evaluate mc_conf ffi k ms = (r,ms1,st1) /\ ~(r = target_TimeOut) ==>
     target_evaluate mc_conf ffi (k + k1) ms = (r,ms1,st1)`,
  SUBGOAL_THEN
   `!k (mc_conf:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) k1 r ms1 st1.
      target_evaluate mc_conf ffi k ms = (r,ms1,st1) /\ ~(r = target_TimeOut) ==>
      target_evaluate mc_conf ffi (k + k1) ms = (r,ms1,st1)`
    (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [(* unfold only the run with clock 0 (it times out) *)
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [target_evaluate_def] THEN
    REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
  ONCE_REWRITE_TAC[target_evaluate_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; apply_oracle_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT TOP_CASE_TAC THEN ASM_MESON_TAC[]);;

(* a call_FFI that returns only extends the io_events *)

let LABPROPSAUX_target_call_FFI_io = prove
 (`call_FFI (st:(FFI)ffi_state) n conf bytes = FFI_return st' t ==>
   ffi_state_io_events st <<= ffi_state_io_events st'`,
  REWRITE_TAC[call_FFI_def] THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[injectivity "ffi_result"; distinctness "ffi_result"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN SIMP[IS_PREFIX_REFL; IS_PREFIX_APPEND] THEN
  MESON_TAC[]);;

(* HOL4: evaluate_io_events_mono *)

let target_evaluate_io_events_mono = prove
 (`!(mc_conf:(A,B,C)machine_config) (ffi:(FFI)ffi_state) k (ms:B).
     ffi_state_io_events ffi <<=
     ffi_state_io_events (SND (SND (target_evaluate mc_conf ffi k ms)))`,
  SUBGOAL_THEN
   `!k (mc_conf:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B).
      ffi_state_io_events ffi <<=
      ffi_state_io_events (SND (SND (target_evaluate mc_conf ffi k ms)))`
    (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [ONCE_REWRITE_TAC[target_evaluate_def] THEN REWRITE_TAC[SND; IS_PREFIX_REFL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[target_evaluate_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; apply_oracle_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[SND; IS_PREFIX_REFL] THEN
  ASM_MESON_TAC[IS_PREFIX_TRANS; LABPROPSAUX_target_call_FFI_io]);;

(* HOL4: evaluate_add_clock_io_events_mono *)

let target_evaluate_add_clock_io_events_mono = prove
 (`!(mc_conf:(A,B,C)machine_config) (ffi:(FFI)ffi_state) k (ms:B) k'.
     k <= k' ==>
     ffi_state_io_events (SND (SND (target_evaluate mc_conf ffi k ms))) <<=
     ffi_state_io_events (SND (SND (target_evaluate mc_conf ffi k' ms)))`,
  SUBGOAL_THEN
   `!k (mc_conf:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) k'.
      k <= k' ==>
      ffi_state_io_events (SND (SND (target_evaluate mc_conf ffi k ms))) <<=
      ffi_state_io_events (SND (SND (target_evaluate mc_conf ffi k' ms)))`
    (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV)
      [target_evaluate_def] THEN
    REWRITE_TAC[SND; target_evaluate_io_events_mono];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?k''. k' = SUC k'' /\ k <= k''` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `k' - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ONCE_REWRITE_TAC[target_evaluate_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; apply_oracle_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT TOP_CASE_TAC THEN REWRITE_TAC[SND; IS_PREFIX_REFL] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let machine_sem_total = prove
 (`?b. machine_sem (mc:(A,B,C)machine_config) (st:(FFI)ffi_state) (ms:B) b`,
  ASM_CASES_TAC `?k t. FST (target_evaluate (mc:(A,B,C)machine_config)
                             (st:(FFI)ffi_state) k (ms:B)) = target_Halt t` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` (X_CHOOSE_TAC `t:outcome`)) THEN
    EXISTS_TAC `Terminate t (ffi_state_io_events (SND (SND
                  (target_evaluate (mc:(A,B,C)machine_config) (st:(FFI)ffi_state) k
                     (ms:B)))))` THEN
    REWRITE_TAC[machine_sem_def] THEN
    MAP_EVERY EXISTS_TAC
     [`k:num`;
      `FST (SND (target_evaluate (mc:(A,B,C)machine_config) (st:(FFI)ffi_state) k
                  (ms:B)))`;
      `SND (SND (target_evaluate (mc:(A,B,C)machine_config) (st:(FFI)ffi_state) k
                  (ms:B)))`] THEN
    REWRITE_TAC[] THEN POP_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  ASM_CASES_TAC `?k. FST (target_evaluate (mc:(A,B,C)machine_config)
                           (st:(FFI)ffi_state) k (ms:B)) = target_Error` THENL
   [EXISTS_TAC `Fail` THEN ASM_REWRITE_TAC[machine_sem_def]; ALL_TAC] THEN
  EXISTS_TAC `Diverge (build_lprefix_lub
                (IMAGE (\k. llist_fromList (ffi_state_io_events (SND (SND
                   (target_evaluate (mc:(A,B,C)machine_config) (st:(FFI)ffi_state) k
                      (ms:B)))))) (:num)))` THEN
  REWRITE_TAC[machine_sem_def] THEN CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN
    MAP_EVERY EXISTS_TAC
     [`FST (SND (target_evaluate (mc:(A,B,C)machine_config) (st:(FFI)ffi_state) k
                  (ms:B)))`;
      `SND (SND (target_evaluate (mc:(A,B,C)machine_config) (st:(FFI)ffi_state) k
                  (ms:B)))`] THEN
    SUBGOAL_THEN `FST (target_evaluate (mc:(A,B,C)machine_config) (st:(FFI)ffi_state) k
                         (ms:B)) = target_TimeOut`
      (fun th -> REWRITE_TAC[GSYM th; PAIR]) THEN
    MP_TAC(ISPEC `FST (target_evaluate (mc:(A,B,C)machine_config) (st:(FFI)ffi_state) k
                         (ms:B))` (cases "machine_result")) THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC build_lprefix_lub_thm THEN
    SUBGOAL_THEN
     `IMAGE (\k. llist_fromList (ffi_state_io_events (SND (SND
        (target_evaluate (mc:(A,B,C)machine_config) (st:(FFI)ffi_state) k (ms:B)))))) (:num) =
      IMAGE llist_fromList
        (IMAGE (\k. ffi_state_io_events (SND (SND (target_evaluate mc st k ms)))) (:num))`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC prefix_chain_lprefix_chain THEN
    REWRITE_TAC[prefix_chain_def; FORALL_IN_IMAGE_2; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`k1:num`; `k2:num`] THEN
    DISJ_CASES_TAC(SPECL [`k1:num`; `k2:num`] LE_CASES) THEN
    ASM_SIMP_TAC[target_evaluate_add_clock_io_events_mono]]);;

(* two runs that stop before the clock runs out have the same result *)

let LABPROPSAUX_target_evaluate_det = prove
 (`~(FST (target_evaluate (mc:(A,B,C)machine_config) (st:(FFI)ffi_state) k1 (ms:B)) =
      target_TimeOut) /\
   ~(FST (target_evaluate mc st k2 ms) = target_TimeOut) ==>
   target_evaluate mc st k1 ms = target_evaluate mc st k2 ms`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`mc:(A,B,C)machine_config`; `st:(FFI)ffi_state`; `k1:num`; `ms:B`; `k2:num`;
                `FST (target_evaluate (mc:(A,B,C)machine_config) (st:(FFI)ffi_state) k1
                        (ms:B))`;
                `FST (SND (target_evaluate (mc:(A,B,C)machine_config) (st:(FFI)ffi_state)
                             k1 (ms:B)))`;
                `SND (SND (target_evaluate (mc:(A,B,C)machine_config) (st:(FFI)ffi_state)
                             k1 (ms:B)))`] target_evaluate_add_clock) THEN
  MP_TAC(SPECL [`mc:(A,B,C)machine_config`; `st:(FFI)ffi_state`; `k2:num`; `ms:B`; `k1:num`;
                `FST (target_evaluate (mc:(A,B,C)machine_config) (st:(FFI)ffi_state) k2
                        (ms:B))`;
                `FST (SND (target_evaluate (mc:(A,B,C)machine_config) (st:(FFI)ffi_state)
                             k2 (ms:B)))`;
                `SND (SND (target_evaluate (mc:(A,B,C)machine_config) (st:(FFI)ffi_state)
                             k2 (ms:B)))`] target_evaluate_add_clock) THEN
  ASM_REWRITE_TAC[PAIR] THEN REWRITE_TAC[ISPECL [`k2:num`; `k1:num`] ADD_SYM] THEN
  MESON_TAC[]);;

(* the cases of machine_sem_unique: a diverging run against another     *)
(* behaviour, or two runs that stop                                      *)

let LABPROPSAUX_MSEM_TAC : tactic = fun (asl,w as g) ->
  if exists (fun (_,th) -> is_forall (concl th)) asl then
    ASM_MESON_TAC[unique_lprefix_lub; PAIR_EQ; FST; distinctness "machine_result"] g
  else
    (MP_TAC(INST [`k:num`,`k1:num`; `k':num`,`k2:num`; `ffi:(FFI)ffi_state`,`st:(FFI)ffi_state`]
              LABPROPSAUX_target_evaluate_det) THEN
     ASM_REWRITE_TAC[FST; distinctness "machine_result"] THEN
     ASM_MESON_TAC[PAIR_EQ; FST; distinctness "machine_result";
                   injectivity "machine_result"]) g;;

let machine_sem_unique = prove
 (`machine_sem (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) (ms:B) b1 /\
   machine_sem mc ffi ms b2 ==> b1 = b2`,
  MAP_EVERY (fun t -> STRUCT_CASES_TAC (ISPEC t (cases "behaviour")))
    [`b1:behaviour`; `b2:behaviour`] THEN
  REWRITE_TAC[machine_sem_def; distinctness "behaviour"; injectivity "behaviour"] THEN
  REPEAT STRIP_TAC THEN LABPROPSAUX_MSEM_TAC);;

let read_ffi_bytearray_IMP_SUBSET_prog_addresses = prove
 (`read_ffi_bytearray (mc:(A,B,C)machine_config) a l (ms:B) = SOME bytes ==>
   all_words (target_get_reg (machine_config_target mc) ms a) (LENGTH bytes) SUBSET
     machine_config_prog_addresses mc`,
  REWRITE_TAC[read_ffi_bytearray_def] THEN
  SPEC_TAC(`target_get_reg (machine_config_target (mc:(A,B,C)machine_config)) (ms:B) a`,
           `x:A word`) THEN
  SPEC_TAC(`val (target_get_reg (machine_config_target (mc:(A,B,C)machine_config)) (ms:B)
              l)`,`n:num`) THEN
  SPEC_TAC(`bytes:byte list`,`res:byte list`) THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  REWRITE_TAC[read_bytearray_def] THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[injectivity "option"] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[LENGTH; all_words_def; EMPTY_SUBSET];
    ALL_TAC] THEN
  REPEAT(TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; injectivity "option"]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LENGTH; all_words_def; INSERT_SUBSET] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[option_DISTINCT]; ASM_MESON_TAC[]]);;

let encoder_correct_asm_step_target_state_rel = prove
 (`encoder_correct (t:(A,B,C)target) /\ target_state_rel t s1 (ms:B) /\
   asm_step (target_config t) s1 i s2
   ==> ?n. target_state_rel t s2 (ITER n (target_next t) ms) /\
           (!j. j < n ==>
                (!pc. pc IN all_pcs (LENGTH (asm_config_encode (target_config t) i))
                              (asm_state_pc s1) 0
                      ==> target_get_byte t (ITER j (target_next t) ms) pc =
                          target_get_byte t ms pc) /\
                target_get_pc t (ITER j (target_next t) ms) IN
                  all_pcs (LENGTH (asm_config_encode (target_config t) i))
                    (asm_state_pc s1) (asm_config_code_alignment (target_config t)) /\
                target_state_ok t (ITER j (target_next t) ms)) /\
           (!j x. j <= n /\ ~(x IN asm_state_mem_domain s1)
                  ==> target_get_byte t (ITER j (target_next t) ms) x =
                      target_get_byte t ms x)`,
  REWRITE_TAC[encoder_correct_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s1:(A)asm_state`; `i:(A)asm`; `s2:(A)asm_state`; `ms:B`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `n:num`
    (MP_TAC o SPEC `\k:num (x:B). x`)) THEN
  REWRITE_TAC[interference_ok_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ETA_AX] THEN STRIP_TAC THEN
  EXISTS_TAC `SUC n` THEN REPEAT CONJ_TAC THENL
   [(* the final state *)
    FIRST_ASSUM(MP_TAC o MATCH_MP asserts_IMP_FOLDR_COUNT_LIST) THEN
    REWRITE_TAC[FOLDR_FUNPOW; LENGTH_COUNT_LIST; ITER_ALT] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[];
    (* the states on the way *)
    X_GEN_TAC `j:num` THEN STRUCT_CASES_TAC(SPEC `j:num` num_CASES) THENL
     [DISCH_TAC THEN REWRITE_TAC[ITER] THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[target_state_rel_def] o
        check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                             "target_state_rel" &&
                             rand(concl th) = `ms:B` with Failure _ -> false)) THEN
      ASM_REWRITE_TAC[all_pcs_thm; IN_ELIM_THM] THEN EXISTS_TAC `0` THEN
      REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; LT_NZ; LENGTH_EQ_NIL] THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[target_ok_def; enc_ok_def] o
        check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "target_ok"
                         with Failure _ -> false)) THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[asm_step_def] o
        check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "asm_step"
                         with Failure _ -> false)) THEN
      ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL];
      REWRITE_TAC[LT_SUC] THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP asserts_IMP_FOLDR_COUNT_LIST_LESS o
        C CONJ (ASSUME `n' < n`) o
        check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "asserts"
                         with Failure _ -> false)) THEN
      REWRITE_TAC[FOLDR_FUNPOW; LENGTH_REVERSE; LENGTH_LIST_OF_SEQ] THEN
      CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP_TAC[]];
    (* the bytes outside the memory domain *)
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] asserts2_every) o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "asserts2"
                       with Failure _ -> false)) THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `x:A word`] THEN STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN
    MP_TAC(INST [`\ms1 ms2:B. !x. ~(x IN asm_state_mem_domain (s1:(A)asm_state)) ==>
                    target_get_byte (t:(A,B,C)target) ms1 x = target_get_byte t ms2 x`,
                 `P:B->B->bool`;
                 `target_next (t:(A,B,C)target)`,`f:B->B`]
      (INST_TYPE [`:B`,`:A`] FUNPOW_refl_trans_chain)) THEN
    REWRITE_TAC[transitive_DEF; reflexive_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ANTS_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`j:num`; `ms:B`]) THEN ANTS_TAC THENL
     [X_GEN_TAC `j':num` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `j':num`) THEN
      REWRITE_TAC[I_O_ID; o_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[]]]);;

let encoder_correct_RTC_asm_step_target_state_rel = prove
 (`encoder_correct (t:(A,B,C)target) /\ target_state_rel t s1 (ms:B) /\
   RTC (\s1 s2. ?i. asm_step (target_config t) s1 i s2) s1 s2
   ==> ?n. target_state_rel t s2 (ITER n (target_next t) ms)`,
  STRIP_TAC THEN
  MP_TAC(INST [`\s:(A)asm_state. ?n. target_state_rel (t:(A,B,C)target) s
                  (ITER n (target_next t) (ms:B))`,`P:(A)asm_state->bool`;
               `\s1 s2. ?i. asm_step (target_config (t:(A,B,C)target)) s1 i s2`,
               `R:(A)asm_state->(A)asm_state->bool`]
    (INST_TYPE [`:(A)asm_state`,`:A`] RTC_lifts_invariants)) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:(A)asm_state`; `y:(A)asm_state`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `m:num`) (X_CHOOSE_TAC `i:(A)asm`)) THEN
    MP_TAC(INST [`x:(A)asm_state`,`s1:(A)asm_state`; `y:(A)asm_state`,`s2:(A)asm_state`;
                 `ITER m (target_next (t:(A,B,C)target)) (ms:B)`,`ms:B`]
             encoder_correct_asm_step_target_state_rel) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (ASSUME_TAC o CONJUNCT1)) THEN
    EXISTS_TAC `n + m:num` THEN ASM_REWRITE_TAC[FUNPOW_ADD];
    DISCH_THEN(MP_TAC o SPECL [`s1:(A)asm_state`; `s2:(A)asm_state`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[ITER]]);;

(* -- interface lemmas for the interference contracts -- *)

let ffi_interfer_ok_post_ffi_asm = prove
 (CASE_TERM `ffi_interfer_ok pc (mc_conf:(A,B,C)machine_config) /\
   index < LENGTH (machine_config_ffi_names mc_conf) /\
   mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i /\
   index < i /\
   machine_config_prog_addresses mc_conf = asm_state_mem_domain t1 /\
   read_ffi_bytearrays mc_conf (ms2:B) = (SOME bytes,SOME bytes2) /\
   LENGTH new_bytes = LENGTH bytes2 /\
   (EL index (machine_config_ffi_names mc_conf) = ExtCall (implode "") ==>
    new_bytes = bytes2) /\
   target_state_rel (machine_config_target mc_conf)
     (asm_state_pc_fupd (K (word_add (word_neg (word ((3 + index) * ffi_offset))) pc)) t1)
     ms2 /\
   alignment_aligned
     (asm_config_code_alignment (target_config (machine_config_target mc_conf)))
     (asm_state_regs t1
        (match asm_config_link_reg (target_config (machine_config_target mc_conf)) with
           NONE -> 0
         | SOME n -> n))
   ==>
   target_state_rel (machine_config_target mc_conf)
     (post_ffi_asm mc_conf t1 new_bytes
        (machine_config_ffi_interfer mc_conf k (index,new_bytes,ms2)))
     (machine_config_ffi_interfer mc_conf k (index,new_bytes,ms2))`,
  REWRITE_TAC[ffi_interfer_ok_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ms2:B`; `k:num`; `index:num`; `new_bytes:byte list`;
                                `t1:(A)asm_state`; `bytes:byte list`; `bytes2:byte list`;
                                `i:num`]) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  REWRITE_TAC[target_state_rel_def; post_ffi_asm_def] THEN SIMP[] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let ccache_interfer_ok_post_ccache_asm = prove
 (CASE_TERM `ccache_interfer_ok pc (mc_conf:(A,B,C)machine_config) /\
   target_state_rel (machine_config_target mc_conf)
     (asm_state_pc_fupd (K (word_add (word_neg (word (2 * ffi_offset))) pc)) t1) (ms2:B) /\
   alignment_aligned
     (asm_config_code_alignment (target_config (machine_config_target mc_conf)))
     (asm_state_regs t1
        (match asm_config_link_reg (target_config (machine_config_target mc_conf)) with
           NONE -> 0
         | SOME n -> n))
   ==>
   target_state_rel (machine_config_target mc_conf)
     (post_ccache_asm mc_conf t1 (machine_config_ccache_interfer mc_conf k (a1,a2,ms2)))
     (machine_config_ccache_interfer mc_conf k (a1,a2,ms2))`,
  REWRITE_TAC[ccache_interfer_ok_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ms2:B`; `t1:(A)asm_state`; `k:num`; `a1:A word`;
                                `a2:A word`]) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  REWRITE_TAC[target_state_rel_def; post_ccache_asm_def] THEN SIMP[] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;
