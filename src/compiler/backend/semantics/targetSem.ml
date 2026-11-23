(* ========================================================================= *)
(* targetSem: port of HOL4 compiler/backend/semantics/targetSemScript.sml    *)
(* (CakeML v3479).                                                           *)
(* The formal semantics of the target machine language. This semantics is  *)
(* parametrised by the target configuration, which includes the next state  *)
(* function of the target architecture.                                     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/set_sep.ml";;
needs "hol4/llist.ml";;
needs "hol4/lprefix_lub.ml";;
needs "semantics/ffi/ffi.ml";;
needs "compiler/encoders/asm/asmSem.ml";;
needs "compiler/encoders/asm/asmProps.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/lab_to_target.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - HOL4 lists wordSem and evaluateProps among the Ancestors, but the       *)
(*   theory uses no name of them (word_loc and Word are wordLang's), so they *)
(*   are not loaded.                                                         *)
(* - Records: mc.f is machine_config_f mc, t.f is asm_state_f t,             *)
(*   mc.target.f is target_f (machine_config_target mc), c.f is              *)
(*   asm_config_f c, rec.f is shmem_info_num_f rec, st.io_events is          *)
(*   ffi_state_io_events st; HOL4 r with <| f1 := x; f2 := y |> is           *)
(*   f1_fupd (K x) (f2_fupd (K y) r).                                        *)
(* - Words: n2w = word, w2n = val, x + y = word_add, x - y = word_sub, -x =  *)
(*   word_neg, && = word_and, <=+ = word_ule, <+ = word_ult, HOL4 aligned =  *)
(*   alignment_aligned; word8 is byte; 2 ** n is 2 EXP n.                    *)
(* - HOL4 set is set_of_list, EVERY is ALL, GENLIST is list_of_seq, ZIP     *)
(*   (l1,l2) is ZIP l1 l2 (equal lengths here), fromList is llist_fromList,  *)
(*   the separating conjunction * is STAR, an mlstring literal is implode.   *)
(* - The type variables follow HOL4's machine_config: (A,B,C)machine_config *)
(*   has A word addresses, machine states B and projections C. The unused    *)
(*   argument pc' of is_valid_mapped_read/write has its own type D, as in    *)
(*   HOL4.                                                                   *)

(* -- execute target machine with interference from environment -- *)

let machine_result_INDUCT,machine_result_RECURSION = cake_type
  "machine_result = target_Halt outcome | target_Error | target_TimeOut";;

(* ffi_interfer: major interference by FFI calls; next_interfer: minor      *)
(* interference during execution; halt_pc: program exits successfully at    *)
(* halt_pc; ccache_pc: entry point for calling clear_cache;                 *)
(* ccache_interfer: major interference by calling clear_cache; target:     *)
(* target next-state function etc.; mmio_info: ffi_index -> byte_size,      *)
(* address, register to be updated/stored, new pc value                     *)

let machine_config_INFO = cake_record "machine_config"
  ["prog_addresses","A word->bool";
   "shared_addresses","A word->bool";
   "ffi_entry_pcs","(A word)list";
   "ffi_names","ffiname list";
   "ptr_reg","num";
   "len_reg","num";
   "ptr2_reg","num";
   "len2_reg","num";
   "ffi_interfer","num->num#byte list#B->B";
   "callee_saved_regs","num list";
   "next_interfer","num->B->B";
   "halt_pc","A word";
   "ccache_pc","A word";
   "ccache_interfer","num->A word#A word#B->B";
   "target","(A,B,C)target";
   "mmio_info","(num#(byte#(A)addr#num#A word))list"];;

let machine_config_component_equality =
  machine_config_INFO.ri_component_equality;;

let apply_oracle_def = cake_def
  `apply_oracle (oracle:num->A->B) x = (oracle 0 x,shift_seq 1 oracle)`;;

let encoded_bytes_in_mem_def = cake_def
  `encoded_bytes_in_mem (c:(A)asm_config) (pc:B word) m md <=>
     ?i k. k * 2 EXP asm_config_code_alignment c < LENGTH (asm_config_encode c i) /\
           bytes_in_memory pc
             (DROP (k * 2 EXP asm_config_code_alignment c) (asm_config_encode c i))
             m md`;;

let read_ffi_bytearray_def = cake_def
  `read_ffi_bytearray (mc:(A,B,C)machine_config) ptr_reg len_reg ms =
     read_bytearray (target_get_reg (machine_config_target mc) ms ptr_reg)
       (val (target_get_reg (machine_config_target mc) ms len_reg))
       (\a. if a IN machine_config_prog_addresses mc
            then SOME (target_get_byte (machine_config_target mc) ms a)
            else NONE)`;;

let read_ffi_bytearrays_def = cake_def
  `read_ffi_bytearrays (mc:(A,B,C)machine_config) ms =
     (read_ffi_bytearray mc (machine_config_ptr_reg mc) (machine_config_len_reg mc) ms,
      read_ffi_bytearray mc (machine_config_ptr2_reg mc) (machine_config_len2_reg mc)
        ms)`;;

let is_valid_mapped_read_def = cake_def
  `is_valid_mapped_read pc (nb:byte) (ad:(A)addr) r (pc':D)
                        (t:(A,B,C)target) ms md <=>
     if nb = word 1
     then bytes_in_memory pc
            (asm_config_encode (target_config t) (asm_Inst (Mem Load8 r ad)))
            (target_get_byte t ms) md
     else if nb = word 0
     then bytes_in_memory pc
            (asm_config_encode (target_config t) (asm_Inst (Mem asm_Load r ad)))
            (target_get_byte t ms) md
     else if nb = word 2
     then bytes_in_memory pc
            (asm_config_encode (target_config t) (asm_Inst (Mem Load16 r ad)))
            (target_get_byte t ms) md
     else if nb = word 4
     then bytes_in_memory pc
            (asm_config_encode (target_config t) (asm_Inst (Mem asm_Load32 r ad)))
            (target_get_byte t ms) md
     else F`;;

let is_valid_mapped_write_def = cake_def
  `is_valid_mapped_write pc (nb:byte) (ad:(A)addr) r (pc':D)
                         (t:(A,B,C)target) ms md <=>
     if nb = word 1
     then bytes_in_memory pc
            (asm_config_encode (target_config t) (asm_Inst (Mem Store8 r ad)))
            (target_get_byte t ms) md
     else if nb = word 0
     then bytes_in_memory pc
            (asm_config_encode (target_config t) (asm_Inst (Mem asm_Store r ad)))
            (target_get_byte t ms) md
     else if nb = word 2
     then bytes_in_memory pc
            (asm_config_encode (target_config t) (asm_Inst (Mem Store16 r ad)))
            (target_get_byte t ms) md
     else if nb = word 4
     then bytes_in_memory pc
            (asm_config_encode (target_config t) (asm_Inst (Mem asm_Store32 r ad)))
            (target_get_byte t ms) md
     else F`;;

(* HOL4: evaluate_def (HOL4 proves termination automatically: the clock k *)
(* decreases); the measure is given here, which is ten times faster than    *)
(* the kit's own search and gives the induction theorem                     *)

let target_evaluate_def = cake_def_wf
  `MEASURE (\x:(A,B,C)machine_config#(FFI)ffi_state#num#B. FST (SND (SND x)))`
  TERM_TAC
  `target_evaluate (mc:(A,B,C)machine_config) (ffi:(FFI)ffi_state) k (ms:B) =
     if k = 0 then (target_TimeOut,ms,ffi)
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
           then target_evaluate mc ffi (k - 1) ms2
           else (target_Error,ms,ffi)
         else (target_Error,ms,ffi)
       else if target_get_pc (machine_config_target mc) ms = machine_config_halt_pc mc then
         ((if target_get_reg (machine_config_target mc) ms (machine_config_ptr_reg mc) =
              word 0
           then target_Halt Success else target_Halt Resource_limit_hit),ms,ffi)
       else if target_get_pc (machine_config_target mc) ms = machine_config_ccache_pc mc
       then
         let (ms1,new_oracle) =
           apply_oracle (machine_config_ccache_interfer mc)
             (target_get_reg (machine_config_target mc) ms (machine_config_ptr_reg mc),
              target_get_reg (machine_config_target mc) ms (machine_config_len_reg mc),
              ms) in
         let mc = machine_config_ccache_interfer_fupd (K new_oracle) mc in
         target_evaluate mc ffi (k - 1) ms1
       else
         match find_index (target_get_pc (machine_config_target mc) ms)
                 (machine_config_ffi_entry_pcs mc) 0 with
           NONE -> (target_Error,ms,ffi)
         | SOME ffi_index ->
             (match EL ffi_index (machine_config_ffi_names mc) with
                SharedMem op ->
                  (match ALOOKUP (machine_config_mmio_info mc) ffi_index with
                     NONE -> (target_Error,ms,ffi)
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
                                       FFI_final outcome ->
                                         (target_Halt (FFI_outcome outcome),ms,ffi)
                                     | FFI_return new_ffi new_bytes ->
                                         let (ms1,new_oracle) =
                                           apply_oracle (machine_config_ffi_interfer mc)
                                             (ffi_index,new_bytes,ms) in
                                         let mc = machine_config_ffi_interfer_fupd
                                                    (K new_oracle) mc in
                                         target_evaluate mc new_ffi (k - 1) ms1)
                                  else (target_Error,ms,ffi)))
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
                                       FFI_final outcome ->
                                         (target_Halt (FFI_outcome outcome),ms,ffi)
                                     | FFI_return new_ffi new_bytes ->
                                         let (ms1,new_oracle) =
                                           apply_oracle (machine_config_ffi_interfer mc)
                                             (ffi_index,new_bytes,ms) in
                                         let mc = machine_config_ffi_interfer_fupd
                                                    (K new_oracle) mc in
                                         target_evaluate mc new_ffi (k - 1) ms1)
                                  else (target_Error,ms,ffi)))))
              | ExtCall _ ->
                  (match ALOOKUP (machine_config_mmio_info mc) ffi_index with
                     SOME _ -> (target_Error,ms,ffi)
                   | NONE ->
                       (match read_ffi_bytearrays mc ms with
                          (SOME bytes,SOME bytes2) ->
                            (match call_FFI ffi (EL ffi_index (machine_config_ffi_names mc))
                                     bytes bytes2 with
                               FFI_final outcome ->
                                 (target_Halt (FFI_outcome outcome),ms,ffi)
                             | FFI_return new_ffi new_bytes ->
                                 let (ms1,new_oracle) =
                                   apply_oracle (machine_config_ffi_interfer mc)
                                     (ffi_index,new_bytes,ms) in
                                 let mc = machine_config_ffi_interfer_fupd
                                            (K new_oracle) mc in
                                 target_evaluate mc new_ffi (k - 1) ms1)
                        | _ -> (target_Error,ms,ffi))))`;;

let target_evaluate_ind = cake_ind "target_evaluate";;

let machine_sem_def = cake_def
  `(machine_sem (mc:(A,B,C)machine_config) (st:(FFI)ffi_state) ms
                (Terminate t io_list) <=>
      ?k ms' st'.
        target_evaluate mc st k ms = (target_Halt t,ms',st') /\
        ffi_state_io_events st' = io_list) /\
   (machine_sem mc st ms (Diverge io_trace) <=>
      (!k. ?ms' st'. target_evaluate mc st k ms = (target_TimeOut,ms',st')) /\
      lprefix_lub
        (IMAGE (\k. llist_fromList
                      (ffi_state_io_events (SND (SND (target_evaluate mc st k ms)))))
               UNIV)
        io_trace) /\
   (machine_sem mc st ms Fail <=>
      ?k. FST (target_evaluate mc st k ms) = target_Error)`;;

(* define what it means for code to be loaded and ready to run *)

let code_loaded_def = cake_def
  `code_loaded (bytes:byte list) (mc:(A,B,C)machine_config) (ms:B) <=>
     read_bytearray (target_get_pc (machine_config_target mc) ms) (LENGTH bytes)
       (\a. if a IN machine_config_prog_addresses mc
            then SOME (target_get_byte (machine_config_target mc) ms a) else NONE) =
     SOME bytes`;;

(* target_configured: target and mc_conf are compatible; will be proved at  *)
(* the top-level by creating an appropriate t (HOL4 keeps an alignment and  *)
(* two byte_aligned conditions commented out)                               *)

let target_configured_def = cake_def
  `target_configured (t:(A)asm_state) (mc_conf:(A,B,C)machine_config) <=>
     ~asm_state_failed t /\
     asm_state_be t =
       asm_config_big_endian (target_config (machine_config_target mc_conf)) /\
     asm_state_align t =
       asm_config_code_alignment (target_config (machine_config_target mc_conf)) /\
     asm_state_mem_domain t = machine_config_prog_addresses mc_conf /\
     (match asm_config_link_reg (target_config (machine_config_target mc_conf)) with
        NONE -> T
      | SOME r -> asm_state_lr t = r)`;;

let get_reg_value_def = cake_def
  `(get_reg_value NONE (w:A) (f:B->A) = w) /\
   (get_reg_value (SOME v) _ f = f v)`;;

let mmio_pcs_min_index_def = cake_def
  `mmio_pcs_min_index ffi_names =
     some x.
       x <= LENGTH ffi_names /\
       (!j. j < x ==> ?s. EL j ffi_names = ExtCall s) /\
       (!j. x <= j /\ j < LENGTH ffi_names ==> ?op. EL j ffi_names = SharedMem op)`;;

(* start_pc_ok: machine configuration's saved pcs and initial pc are ok *)

let start_pc_ok_def = cake_def
  `start_pc_ok (mc_conf:(A,B,C)machine_config) pc <=>
     ~(machine_config_halt_pc mc_conf IN machine_config_prog_addresses mc_conf) /\
     ~(machine_config_ccache_pc mc_conf IN machine_config_prog_addresses mc_conf) /\
     ~(machine_config_halt_pc mc_conf IN machine_config_shared_addresses mc_conf) /\
     ~(machine_config_ccache_pc mc_conf IN machine_config_shared_addresses mc_conf) /\
     word_sub pc (word ffi_offset) = machine_config_halt_pc mc_conf /\
     word_sub pc (word (2 * ffi_offset)) = machine_config_ccache_pc mc_conf /\
     word_and (word 1) pc = word 0 /\
     ?i. mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i /\
         (!index.
            index < i ==>
            ~(word_sub pc (word ((3 + index) * ffi_offset)) IN
              machine_config_prog_addresses mc_conf) /\
            ~(word_sub pc (word ((3 + index) * ffi_offset)) IN
              machine_config_shared_addresses mc_conf) /\
            ~(word_sub pc (word ((3 + index) * ffi_offset)) =
              machine_config_halt_pc mc_conf) /\
            ~(word_sub pc (word ((3 + index) * ffi_offset)) =
              machine_config_ccache_pc mc_conf) /\
            find_index (word_sub pc (word ((3 + index) * ffi_offset)))
              (machine_config_ffi_entry_pcs mc_conf) 0 = SOME index) /\
         (!index.
            index < LENGTH (machine_config_ffi_names mc_conf) /\ i <= index ==>
            ~(machine_config_halt_pc mc_conf =
              EL index (machine_config_ffi_entry_pcs mc_conf)) /\
            ~(machine_config_ccache_pc mc_conf =
              EL index (machine_config_ffi_entry_pcs mc_conf))) /\
         LENGTH (machine_config_ffi_names mc_conf) =
         LENGTH (machine_config_ffi_entry_pcs mc_conf)`;;

(* ffi_interfer_ok: the FFI interference oracle is ok: an ExtCall           *)
(* transition must satisfy the per-call promises of the calling convention *)
(* (the machine invariants hold, control returns to the link-register      *)
(* address, the byte array is written and no other program memory changes, *)
(* and callee-saved registers are preserved; all other registers,          *)
(* including all FP registers, are unconstrained); a SharedMem transition  *)
(* performs the mapped load/store and touches nothing else (a side effect  *)
(* on other registers is possible, as target_state_rel ignores avoid_regs; *)
(* the byte array is assumed to be little endian)                          *)

let ffi_interfer_ok_def = cake_def
  `ffi_interfer_ok pc (mc_conf:(A,B,C)machine_config) <=>
     (!ms2 k index new_bytes t1 bytes bytes2 i.
        index < LENGTH (machine_config_ffi_names mc_conf) /\
        mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i /\
        machine_config_prog_addresses mc_conf = asm_state_mem_domain t1 ==>
        (index < i ==>
         read_ffi_bytearrays mc_conf ms2 = (SOME bytes,SOME bytes2) /\
         LENGTH new_bytes = LENGTH bytes2 /\
         (EL index (machine_config_ffi_names mc_conf) = ExtCall (implode "") ==>
          new_bytes = bytes2) /\
         target_state_rel (machine_config_target mc_conf)
           (asm_state_pc_fupd
              (K (word_add (word_neg (word ((3 + index) * ffi_offset))) pc)) t1)
           ms2 /\
         alignment_aligned
           (asm_config_code_alignment (target_config (machine_config_target mc_conf)))
           (asm_state_regs t1
              (match asm_config_link_reg
                       (target_config (machine_config_target mc_conf)) with
                 NONE -> 0
               | SOME n -> n))
         ==>
         (let ms' = machine_config_ffi_interfer mc_conf k (index,new_bytes,ms2) in
          target_state_ok (machine_config_target mc_conf) ms' /\
          target_get_pc (machine_config_target mc_conf) ms' =
            asm_state_regs t1
              (match asm_config_link_reg
                       (target_config (machine_config_target mc_conf)) with
                 NONE -> 0
               | SOME n -> n) /\
          (!a. a IN asm_state_mem_domain t1 ==>
               target_get_byte (machine_config_target mc_conf) ms' a =
               asm_write_bytearray
                 (asm_state_regs t1 (machine_config_ptr2_reg mc_conf))
                 new_bytes (asm_state_mem t1) a) /\
          (!r. MEM r (machine_config_callee_saved_regs mc_conf) /\
               r < asm_config_reg_count
                     (target_config (machine_config_target mc_conf)) /\
               ~MEM r (asm_config_avoid_regs
                         (target_config (machine_config_target mc_conf))) ==>
               target_get_reg (machine_config_target mc_conf) ms' r =
               asm_state_regs t1 r))) /\
        (i <= index /\
         target_state_rel (machine_config_target mc_conf)
           (asm_state_pc_fupd
              (K (EL index (machine_config_ffi_entry_pcs mc_conf))) t1)
           ms2 ==>
         (?info. ALOOKUP (machine_config_mmio_info mc_conf) index = SOME info /\
                 (EL index (machine_config_ffi_names mc_conf) = SharedMem MappedRead ==>
                  !new_bytes.
                    target_state_rel (machine_config_target mc_conf)
                      (asm_state_pc_fupd (K (SND (SND (SND info))))
                         (asm_state_regs_fupd
                            (K (\n. if n = FST (SND (SND info))
                                    then word_of_bytes F (word 0) new_bytes
                                    else asm_state_regs t1 n)) t1))
                      (machine_config_ffi_interfer mc_conf k (index,new_bytes,ms2))) /\
                 (EL index (machine_config_ffi_names mc_conf) = SharedMem MappedWrite ==>
                  target_state_rel (machine_config_target mc_conf)
                    (asm_state_pc_fupd (K (SND (SND (SND info)))) t1)
                    (machine_config_ffi_interfer mc_conf k
                       (index,new_bytes,ms2))))))`;;

(* ccache_interfer_ok: a cache-clear transition must satisfy the same      *)
(* per-call promises, additionally preserving ptr_reg and leaving all       *)
(* program memory unchanged                                                 *)

let ccache_interfer_ok_def = cake_def
  `ccache_interfer_ok pc (mc_conf:(A,B,C)machine_config) <=>
     (!ms2 t1 k a1 a2.
        target_state_rel (machine_config_target mc_conf)
          (asm_state_pc_fupd (K (word_add (word_neg (word (2 * ffi_offset))) pc)) t1)
          ms2 /\
        alignment_aligned
          (asm_config_code_alignment (target_config (machine_config_target mc_conf)))
          (asm_state_regs t1
             (match asm_config_link_reg
                      (target_config (machine_config_target mc_conf)) with
                NONE -> 0
              | SOME n -> n)) ==>
        (let ms' = machine_config_ccache_interfer mc_conf k (a1,a2,ms2) in
         target_state_ok (machine_config_target mc_conf) ms' /\
         target_get_pc (machine_config_target mc_conf) ms' =
           asm_state_regs t1
             (match asm_config_link_reg
                      (target_config (machine_config_target mc_conf)) with
                NONE -> 0
              | SOME n -> n) /\
         (!a. a IN asm_state_mem_domain t1 ==>
              target_get_byte (machine_config_target mc_conf) ms' a =
              asm_state_mem t1 a) /\
         (!r. (MEM r (machine_config_callee_saved_regs mc_conf) \/
               r = machine_config_ptr_reg mc_conf) /\
              r < asm_config_reg_count
                    (target_config (machine_config_target mc_conf)) /\
              ~MEM r (asm_config_avoid_regs
                        (target_config (machine_config_target mc_conf))) ==>
              target_get_reg (machine_config_target mc_conf) ms' r =
              asm_state_regs t1 r)))`;;

(* post_ffi_asm / post_ccache_asm: the canonical asm-level successor state *)
(* after an FFI / cache-clear transition: caller-saved registers and all   *)
(* FP registers are taken from the machine state                           *)

let post_ffi_asm_def = cake_def
  `post_ffi_asm (mc_conf:(A,B,C)machine_config) (t1:(A)asm_state) new_bytes (ms':B) =
     asm_state_regs_fupd
       (K (\a. if MEM a (machine_config_callee_saved_regs mc_conf) \/
                  ~(a < asm_config_reg_count
                          (target_config (machine_config_target mc_conf))) \/
                  MEM a (asm_config_avoid_regs
                           (target_config (machine_config_target mc_conf)))
               then asm_state_regs t1 a
               else target_get_reg (machine_config_target mc_conf) ms' a))
     (asm_state_fp_regs_fupd
        (K (\i. target_get_fp_reg (machine_config_target mc_conf) ms' i))
     (asm_state_mem_fupd
        (K (asm_write_bytearray (asm_state_regs t1 (machine_config_ptr2_reg mc_conf))
              new_bytes (asm_state_mem t1)))
     (asm_state_pc_fupd
        (K (asm_state_regs t1
              (match asm_config_link_reg
                       (target_config (machine_config_target mc_conf)) with
                 NONE -> 0
               | SOME n -> n)))
        t1)))`;;

let post_ccache_asm_def = cake_def
  `post_ccache_asm (mc_conf:(A,B,C)machine_config) (t1:(A)asm_state) (ms':B) =
     asm_state_regs_fupd
       (K (\a. if MEM a (machine_config_callee_saved_regs mc_conf) \/
                  a = machine_config_ptr_reg mc_conf \/
                  ~(a < asm_config_reg_count
                          (target_config (machine_config_target mc_conf))) \/
                  MEM a (asm_config_avoid_regs
                           (target_config (machine_config_target mc_conf)))
               then asm_state_regs t1 a
               else target_get_reg (machine_config_target mc_conf) ms' a))
     (asm_state_fp_regs_fupd
        (K (\i. target_get_fp_reg (machine_config_target mc_conf) ms' i))
     (asm_state_pc_fupd
        (K (asm_state_regs t1
              (match asm_config_link_reg
                       (target_config (machine_config_target mc_conf)) with
                 NONE -> 0
               | SOME n -> n)))
        t1))`;;

(* good_init_state: intermediate invariant describing how code (bytes) and *)
(* ffi is installed in the machine (mc_conf, ms) using labLang (m, dm,     *)
(* cbspace) and target semantics (t) information as an intermediary; these *)
(* are all destined to be assumptions on the top-level correctness theorem. *)
(* The conjuncts: starting pc assumptions, interference, the code memory   *)
(* relation, the data memory relation (which implies that m contains no    *)
(* labels), code buffer constraints.                                        *)

let good_init_state_def = cake_def
  `good_init_state (mc_conf:(A,B,C)machine_config) ms bytes cbspace
                   (t:(A)asm_state) (m:A word->(A)word_loc) dm sdm <=>
     target_state_rel (machine_config_target mc_conf) t ms /\
     target_configured t mc_conf /\
     asm_state_pc t = target_get_pc (machine_config_target mc_conf) ms /\
     start_pc_ok mc_conf (asm_state_pc t) /\
     word_and (word (2 EXP asm_state_align t - 1)) (asm_state_pc t) = word 0 /\
     interference_ok (machine_config_next_interfer mc_conf)
       (target_proj (machine_config_target mc_conf)
          (machine_config_prog_addresses mc_conf)) /\
     ffi_interfer_ok (asm_state_pc t) mc_conf /\
     ccache_interfer_ok (asm_state_pc t) mc_conf /\
     code_loaded bytes mc_conf ms /\
     bytes_in_mem (asm_state_pc t) bytes (asm_state_mem t)
       (asm_state_mem_domain t) dm /\
     dm SUBSET asm_state_mem_domain t /\
     (!a. byte_align a IN dm ==> a IN dm) /\
     sdm = machine_config_shared_addresses mc_conf /\
     (!a. byte_align a IN sdm ==> a IN sdm) /\
     DISJOINT (machine_config_prog_addresses mc_conf)
       (machine_config_shared_addresses mc_conf) /\
     (!a. ?w. asm_state_mem t a =
              get_byte a w
                (asm_config_big_endian (target_config (machine_config_target mc_conf))) /\
              m (byte_align a) = wl_Word w) /\
     (!n. n < cbspace ==>
          word_add (word (n + LENGTH bytes)) (asm_state_pc t) IN
            asm_state_mem_domain t /\
          ~(word_add (word (n + LENGTH bytes)) (asm_state_pc t) IN dm)) /\
     cbspace + LENGTH bytes < dimword(:A)`;;

(* CakeML code, bytes, and code buffer space, cbspace, and FFI functions,   *)
(* ffi, are installed into the machine, mc_conf + ms; r1 and r2 are the     *)
(* names of registers containing the first address of the CakeML heap and  *)
(* the first address past the CakeML stack, i.e. the range of the data      *)
(* memory                                                                    *)

let installed_def = cake_def
  `installed bytes cbspace (bitmaps:(A word)list) data_sp ffi_names (r1,r2)
             (mc_conf:(A,B,C)machine_config) shmem_extra ms <=>
     ?t m bitmap_ptr bitmaps_dm sdm.
       let heap_stack_dm = {w | word_ule (asm_state_regs t r1) w /\
                                word_ult w (asm_state_regs t r2)} in
       good_init_state mc_conf ms bytes cbspace t m (heap_stack_dm UNION bitmaps_dm)
         sdm /\
       byte_aligned (asm_state_regs t r1) /\
       byte_aligned (asm_state_regs t r2) /\
       byte_aligned bitmap_ptr /\
       word_ule (asm_state_regs t r1) (asm_state_regs t r2) /\
       word_ule (word_mul (word 1024) bytes_in_word)
         (word_sub (asm_state_regs t r2) (asm_state_regs t r1)) /\
       DISJOINT heap_stack_dm bitmaps_dm /\
       m (asm_state_regs t r1) = wl_Word bitmap_ptr /\
       m (word_add (asm_state_regs t r1) bytes_in_word) =
         wl_Word (word_add bitmap_ptr (word_mul bytes_in_word (word (LENGTH bitmaps)))) /\
       m (word_add (asm_state_regs t r1) (word_mul (word 2) bytes_in_word)) =
         wl_Word (word_add (word_add bitmap_ptr (word_mul bytes_in_word (word data_sp)))
                   (word_mul bytes_in_word (word (LENGTH bitmaps)))) /\
       m (word_add (asm_state_regs t r1) (word_mul (word 3) bytes_in_word)) =
         wl_Word (word_add (target_get_pc (machine_config_target mc_conf) ms)
                   (word (LENGTH bytes))) /\
       m (word_add (asm_state_regs t r1) (word_mul (word 4) bytes_in_word)) =
         wl_Word (word_add (word_add (target_get_pc (machine_config_target mc_conf) ms)
                              (word cbspace))
                   (word (LENGTH bytes))) /\
       (misc_word_list bitmap_ptr (MAP wl_Word bitmaps) STAR
        word_list_exists
          (word_add bitmap_ptr (word_mul bytes_in_word (word (LENGTH bitmaps)))) data_sp)
         (fun2set (m,byte_aligned INTER bitmaps_dm)) /\
       ffi_names = SOME (machine_config_ffi_names mc_conf) /\
       (!i. mmio_pcs_min_index (machine_config_ffi_names mc_conf) = SOME i ==>
            MAP (\rec. val (target_get_pc (machine_config_target mc_conf) ms) +
                       shmem_info_num_entry_pc rec) shmem_extra =
            DROP i (MAP val (machine_config_ffi_entry_pcs mc_conf)) /\
            machine_config_mmio_info mc_conf =
            ZIP (list_of_seq (\index. index + i) (LENGTH shmem_extra))
                (MAP (\rec. (shmem_info_num_nbytes rec,
                             Addr (shmem_info_num_addr_reg rec)
                                  (word (shmem_info_num_addr_off rec)),
                             shmem_info_num_reg rec,
                             word_add (word (shmem_info_num_exit_pc rec))
                               (target_get_pc (machine_config_target mc_conf) ms)))
                     shmem_extra) /\
            (cbspace + LENGTH bytes) + ffi_offset * (i + 3) < dimword(:A))`;;
