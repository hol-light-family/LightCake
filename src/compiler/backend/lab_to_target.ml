(* ========================================================================= *)
(* lab_to_target: port of HOL4 compiler/backend/lab_to_targetScript.sml      *)
(* (CakeML v3479).                                                           *)
(* This compiler phase generates concrete (ARM, x64, ag32, RISC-V, MIPS)    *)
(* machine code from labLang assembly programs. This phase is the CakeML    *)
(* compiler's assembler: it computes label offsets and encodes all          *)
(* instructions according to the instruction encoder stored in the          *)
(* compiler configuration.                                                   *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/labLang.ml";;
needs "compiler/backend/lab_filter.ml";;
needs "semantics/ffi/ffi.ml";;

prioritize_num();;
type_invention_error := true;;

(* Notes on the rendering:                                                   *)
(* - num num_map num_map is (num spt)spt, num_set is 1 spt, () is one,       *)
(*   word8 is byte; n2w = word, w2n = val, 0w - x = word_sub (word 0) x.     *)
(* - HOL4 c.encode is asm_config_encode c; EVERY is ALL, FOLDR f e l is      *)
(*   ITLIST f l e.                                                           *)
(* - HOL4 Overload all_enc_ok_light c ls = EVERY (sec_ok_light c) ls is      *)
(*   written out where used.                                                 *)
(* - The HOL4 variable done is isdone (done was a constructor of the type    *)
(*   kont of hol4/pegexec.ml, now pegexec_done; the induction theorem        *)
(*   unprimes variables, so done' would have come out as done there).        *)
(* - HOL4 r with <| f1 := x; f2 := y |> is f1_fupd (K x) (f2_fupd (K y) r).  *)

(* Number of bytes per FFI *)

let ffi_offset_def = cake_def
  `ffi_offset = 16`;;

(* basic assemble function *)

let lab_inst_def = cake_def
  `(lab_inst (w:A word) (lab_Jump _) = asm_Jump w) /\
   (lab_inst w (lab_JumpCmp c r ri _) = asm_JumpCmp c r ri w) /\
   (lab_inst w (lab_Call _) = asm_Call w) /\
   (lab_inst w (lab_LocValue r _) = asm_Loc r w) /\
   (lab_inst w lab_Halt = asm_Jump w) /\
   (lab_inst w lab_Install = asm_Jump w) /\
   (lab_inst w (CallFFI n) = asm_Jump w)`;;

let cbw_to_asm_def = cake_def
  `cbw_to_asm (a:(A)asm_or_cbw) =
     match a with
       Asmi a -> a
     | Cbw r1 r2 -> asm_Inst (Mem Store8 r2 (Addr r1 (word 0)))
     | ShareMem m r ad -> asm_Inst (Mem m r ad)`;;

let _ = cake_add_simps [cbw_to_asm_def];;

let enc_line_def = cake_def
  `(enc_line (enc:(A)asm->byte list) skip_len (lab_Label n1 n2 n3) =
      lab_Label n1 n2 skip_len) /\
   (enc_line enc skip_len (Asm a _ _) =
      let bs = enc (cbw_to_asm a) in Asm a bs (LENGTH bs)) /\
   (enc_line enc skip_len (LabAsm l _ _ _) =
      let bs = enc (lab_inst (word 0) l) in
      LabAsm l (word 0) bs (LENGTH bs))`;;

let enc_sec_def = cake_def
  `enc_sec (enc:(A)asm->byte list) skip_len (Section k xs) =
     Section k (MAP (enc_line enc skip_len) xs)`;;

let enc_sec_list_def = cake_def
  `enc_sec_list (enc:(A)asm->byte list) xs =
     let skip_len = LENGTH (enc (asm_Inst asm_Skip)) in
     MAP (enc_sec enc skip_len) xs`;;

(* compute labels; labels with second part 0 are ignored *)

let section_labels_def = cake_def
  `(section_labels pos ([]:((A)line)list) labs = (pos,labs)) /\
   (section_labels pos (CONS (lab_Label _ l2 len) xs) labs =
      if l2 = 0 then
        section_labels (pos + len) xs labs
      else
        section_labels (pos + len) xs (CONS (l2,pos + len) labs)) /\
   (section_labels pos (CONS (Asm _ _ len) xs) labs =
      section_labels (pos + len) xs labs) /\
   (section_labels pos (CONS (LabAsm _ _ _ len) xs) labs =
      section_labels (pos + len) xs labs)`;;

let section_labels_ind = cake_ind "section_labels";;

let compute_labels_alt_def = cake_def
  `(compute_labels_alt pos ([]:((A)sec)list) (labs:(num spt)spt) = labs) /\
   (compute_labels_alt pos (CONS (Section k lines) rest) labs =
      let (new_pos,sec_labs) = section_labels pos lines [] in
      compute_labels_alt new_pos rest
        (insert k (fromAList (CONS (0,pos) sec_labs)) labs))`;;

let compute_labels_alt_ind = cake_ind "compute_labels_alt";;

(* update code, but not label lengths *)

let find_pos_def = cake_def
  `find_pos (lab_Lab k1 k2) (labs:(num spt)spt) =
     lookup_any k2 (lookup_any k1 labs LN) 0`;;

let get_label_def = cake_def
  `(get_label (lab_Jump l:(A)asm_with_lab) = l) /\
   (get_label (lab_JumpCmp c r ri l) = l) /\
   (get_label (lab_Call l) = l) /\
   (get_label (lab_LocValue r l) = l) /\
   (get_label _ = lab_Lab 0 0)`;;

(* It should never happen that get_ffi_index returns the default 0;         *)
(* nonetheless, having a default prevents the translator from generating    *)
(* painful side conditions.                                                  *)

let get_ffi_index_def = cake_def
  `get_ffi_index (ffis:A list) s = misc_the 0 (find_index s ffis 0)`;;

let get_jump_offset_def = cake_def
  `(get_jump_offset (CallFFI s:(A)asm_with_lab) ffis (labs:(num spt)spt) pos =
      word_sub (word 0)
        (word (pos + (3 + get_ffi_index ffis (ExtCall s)) * ffi_offset)):B word) /\
   (get_jump_offset lab_Install ffis labs pos =
      word_sub (word 0) (word (pos + 2 * ffi_offset))) /\
   (get_jump_offset lab_Halt ffis labs pos =
      word_sub (word 0) (word (pos + ffi_offset))) /\
   (get_jump_offset a ffis labs pos =
      word_sub (word (find_pos (get_label a) labs)) (word pos))`;;

let enc_lines_again_def = cake_def
  `(enc_lines_again (labs:(num spt)spt) ffis pos (enc:(A)asm->byte list) []
                    (acc,ok) = (REVERSE acc,pos,ok:bool)) /\
   (enc_lines_again labs ffis pos enc (CONS (lab_Label k1 k2 l) xs) (acc,ok) =
      enc_lines_again labs ffis (pos + l) enc xs
        (CONS (lab_Label k1 k2 l) acc,ok)) /\
   (enc_lines_again labs ffis pos enc (CONS (Asm x1 x2 l) xs) (acc,ok) =
      enc_lines_again labs ffis (pos + l) enc xs (CONS (Asm x1 x2 l) acc,ok)) /\
   (enc_lines_again labs ffis pos enc (CONS (LabAsm a w bytes l) xs) (acc,ok) =
      let w1 = get_jump_offset a ffis labs pos in
      if w = w1 then
        enc_lines_again labs ffis (pos + l) enc xs
          (CONS (LabAsm a w bytes l) acc,ok)
      else
        let bs = enc (lab_inst w1 a) in
        let l1 = MAX (LENGTH bs) l in
        enc_lines_again labs ffis (pos + l1) enc xs
          (CONS (LabAsm a w1 bs l1) acc,(ok /\ l1 = l)))`;;

let enc_lines_again_ind = cake_ind "enc_lines_again";;

let enc_secs_again_def = cake_def
  `(enc_secs_again pos (labs:(num spt)spt) ffis (enc:(A)asm->byte list) [] =
      ([],T)) /\
   (enc_secs_again pos labs ffis enc (CONS (Section s lines) rest) =
      let (lines1,pos1,ok) = enc_lines_again labs ffis pos enc lines ([],T) in
      let (rest1,ok1) = enc_secs_again pos1 labs ffis enc rest in
      (CONS (Section s lines1) rest1,(ok /\ ok1)))`;;

let enc_secs_again_ind = cake_ind "enc_secs_again";;

(* update labels *)

let lines_upd_lab_len_def = cake_def
  `(lines_upd_lab_len pos ([]:((A)line)list) acc = (REVERSE acc,pos)) /\
   (lines_upd_lab_len pos (CONS (lab_Label k1 k2 l) xs) acc =
      let l1 = if EVEN pos then 0 else 1 in
      lines_upd_lab_len (pos + l1) xs (CONS (lab_Label k1 k2 l1) acc)) /\
   (lines_upd_lab_len pos (CONS (Asm x1 x2 l) xs) acc =
      lines_upd_lab_len (pos + l) xs (CONS (Asm x1 x2 l) acc)) /\
   (lines_upd_lab_len pos (CONS (LabAsm a w bytes l) xs) acc =
      lines_upd_lab_len (pos + l) xs (CONS (LabAsm a w bytes l) acc))`;;

let lines_upd_lab_len_ind = cake_ind "lines_upd_lab_len";;

let upd_lab_len_def = cake_def
  `(upd_lab_len pos ([]:((A)sec)list) = []) /\
   (upd_lab_len pos (CONS (Section s lines) rest) =
      let (lines1,pos1) = lines_upd_lab_len pos lines [] in
      let rest1 = upd_lab_len pos1 rest in
      CONS (Section s lines1) rest1)`;;

let upd_lab_len_ind = cake_ind "upd_lab_len";;

(* checking that all labelled asm instructions are asm_ok *)

let line_ok_light_def = cake_def
  `(line_ok_light (c:(A)asm_config) (lab_Label _ _ l) <=> T) /\
   (line_ok_light c (Asm b bytes l) <=> T) /\
   (line_ok_light c (LabAsm lab_Halt w bytes l) <=> asm_ok (asm_Jump w) c) /\
   (line_ok_light c (LabAsm lab_Install w bytes l) <=> asm_ok (asm_Jump w) c) /\
   (line_ok_light c (LabAsm (CallFFI index) w bytes l) <=>
      asm_ok (asm_Jump w) c) /\
   (line_ok_light c (LabAsm (lab_Call v24) w bytes l) <=> F) /\
   (line_ok_light c (LabAsm a w bytes l) <=> asm_ok (lab_inst w a) c)`;;

let sec_ok_light_def = cake_def
  `sec_ok_light (c:(A)asm_config) (Section k ls) <=> ALL (line_ok_light c) ls`;;

let _ = cake_add_simps [sec_ok_light_def];;

(* pad with nop byte, and nop instruction *)

let pad_bytes_def = cake_def
  `pad_bytes (bytes:byte list) len nop =
     let len_bytes = LENGTH bytes in
     if len <= len_bytes then bytes else
       TAKE len (APPEND bytes (FLAT (REPLICATE len nop)))`;;

let add_nop_def = cake_def
  `(add_nop (nop:byte list) ([]:((A)line)list) = []) /\
   (add_nop nop (CONS (lab_Label l1 l2 len) xs) =
      CONS (lab_Label l1 l2 len) (add_nop nop xs)) /\
   (add_nop nop (CONS (Asm x bytes len) xs) =
      CONS (Asm x (APPEND bytes nop) (len + 1)) xs) /\
   (add_nop nop (CONS (LabAsm y w bytes len) xs) =
      CONS (LabAsm y w (APPEND bytes nop) (len + 1)) xs)`;;

let add_nop_ind = cake_ind "add_nop";;

let pad_section_def = cake_def
  `(pad_section (nop:byte list) ([]:((A)line)list) aux = REVERSE aux) /\
   (pad_section nop (CONS (lab_Label l1 l2 len) xs) aux =
      pad_section nop xs
        (CONS (lab_Label l1 l2 0) (if len = 0 then aux else add_nop nop aux))) /\
   (pad_section nop (CONS (Asm x bytes len) xs) aux =
      pad_section nop xs (CONS (Asm x (pad_bytes bytes len nop) len) aux)) /\
   (pad_section nop (CONS (LabAsm y w bytes len) xs) aux =
      pad_section nop xs (CONS (LabAsm y w (pad_bytes bytes len nop) len) aux))`;;

let pad_section_ind = cake_ind "pad_section";;

let pad_code_def = cake_def
  `(pad_code (nop:byte list) ([]:((A)sec)list) = []) /\
   (pad_code nop (CONS (Section n xs) ys) =
      CONS (Section n (pad_section nop xs [])) (pad_code nop ys))`;;

let pad_code_ind = cake_ind "pad_code";;

let pad_code_MAP = prove
 (`pad_code nop =
   MAP (\x:(A)sec. Section (Section_num x) (pad_section nop (Section_lines x) []))`,
  REWRITE_TAC[FUN_EQ_THM] THEN LIST_INDUCT_TAC THEN SIMP[pad_code_def; MAP] THEN
  CASES_ON `h:(A)sec` THEN SIMP[pad_code_def; MAP]);;

let sec_length_def = cake_def
  `(sec_length ([]:((A)line)list) k = k) /\
   (sec_length (CONS (lab_Label _ _ l) xs) k = sec_length xs (k + l)) /\
   (sec_length (CONS (Asm x1 x2 l) xs) k = sec_length xs (k + l)) /\
   (sec_length (CONS (LabAsm a w bytes l) xs) k = sec_length xs (k + l))`;;

let sec_length_ind = cake_ind "sec_length";;

let get_symbols_def = cake_def
  `(get_symbols pos ([]:((A)sec)list) = []) /\
   (get_symbols pos (CONS (Section k l) secs) =
      let len = sec_length l 0 in
      CONS (k,pos,len) (get_symbols (pos + len) secs))`;;

(* Compute the labels whose second part is 0 *)

let zero_labs_acc_of_def = cake_def
  `(zero_labs_acc_of (lab_LocValue _ (lab_Lab n1 n2):(A)asm_with_lab)
                     (acc:num_set) =
      if n2 = 0 then insert n1 one acc else acc) /\
   (zero_labs_acc_of (lab_Jump (lab_Lab n1 n2)) acc =
      if n2 = 0 then insert n1 one acc else acc) /\
   (zero_labs_acc_of (lab_JumpCmp _ _ _ (lab_Lab n1 n2)) acc =
      if n2 = 0 then insert n1 one acc else acc) /\
   (zero_labs_acc_of _ acc = acc)`;;

let _ = cake_add_simps [zero_labs_acc_of_def];;

let line_get_zero_labs_acc_def = cake_def
  `(line_get_zero_labs_acc (LabAsm a _ _ _:(A)line) acc =
      zero_labs_acc_of a acc) /\
   (line_get_zero_labs_acc _ acc = acc)`;;

let sec_get_zero_labs_acc_def = cake_def
  `sec_get_zero_labs_acc (Section _ lines:(A)sec) acc =
     ITLIST line_get_zero_labs_acc lines acc`;;

let get_zero_labs_acc_def = cake_def
  `get_zero_labs_acc (code:((A)sec)list) =
     ITLIST sec_get_zero_labs_acc code LN`;;

let zero_labs_acc_exist_def = cake_def
  `zero_labs_acc_exist (labs:(num spt)spt) (code:((A)sec)list) <=>
     let zlabs = toAList (get_zero_labs_acc code) in
     ALL (\(n,u:1).
            match lookup n labs with
              NONE -> F
            | SOME l -> ~(lookup 0 l = NONE)) zlabs`;;

(* top-level assembler function; init_clock puts an upper limit on the      *)
(* number of times the lengths can be adjusted                              *)

let remove_labels_loop_def = cake_def
  `remove_labels_loop clock (c:(A)asm_config) pos init_labs ffis sec_list =
     let labs = compute_labels_alt pos sec_list init_labs in
     let (sec_list,isdone) =
       enc_secs_again pos labs ffis (asm_config_encode c) sec_list in
     if isdone then
       let sec_list = upd_lab_len pos sec_list in
       let labs = compute_labels_alt pos sec_list init_labs in
       let (sec_list,isdone) =
         enc_secs_again pos labs ffis (asm_config_encode c) sec_list in
       let sec_list = pad_code (asm_config_encode c (asm_Inst asm_Skip)) sec_list in
       if isdone /\ ALL (sec_ok_light c) sec_list /\
          zero_labs_acc_exist labs sec_list
       then SOME (sec_list,labs)
       else NONE
     else
       if clock = 0 then NONE else
         remove_labels_loop (clock - 1) c pos init_labs ffis sec_list`;;

let remove_labels_loop_ind = cake_ind "remove_labels_loop";;

let remove_labels_def = cake_def
  `remove_labels init_clock (c:(A)asm_config) pos labs ffis sec_list =
     remove_labels_loop init_clock c pos labs ffis
       (enc_sec_list (asm_config_encode c) sec_list)`;;

(* code extraction *)

let line_bytes_def = cake_def
  `(line_bytes (lab_Label _ _ _:(A)line) = []) /\
   (line_bytes (Asm _ bytes _) = bytes) /\
   (line_bytes (LabAsm _ _ bytes _) = bytes)`;;

let prog_to_bytes_def = cake_def
  `(prog_to_bytes ([]:((A)sec)list) = []) /\
   (prog_to_bytes (CONS (Section k []) xs) = prog_to_bytes xs) /\
   (prog_to_bytes (CONS (Section k (CONS y ys)) xs) =
      APPEND (line_bytes y) (prog_to_bytes (CONS (Section k ys) xs)))`;;

let prog_to_bytes_ind = cake_ind "prog_to_bytes";;

let prog_to_bytes_MAP = prove
 (`!ls:((A)sec)list.
     prog_to_bytes ls = FLAT (MAP (FLAT o MAP line_bytes o Section_lines) ls)`,
  MATCH_MP_TAC prog_to_bytes_ind THEN
  RW[prog_to_bytes_def; MAP; FLAT; o_THM; APPEND_ASSOC]);;

(* compile labels *)

let shmem_info_num_INFO = cake_record "shmem_info_num"
  ["entry_pc","num";
   "nbytes","byte";
   "addr_reg","num";
   "addr_off","num";
   "reg","num";
   "exit_pc","num"];;

let shmem_info_num_component_equality =
  shmem_info_num_INFO.ri_component_equality;;

(* HOL4: config *)

let lab_to_target_config_INFO = cake_record "lab_to_target_config"
  ["labels","(num spt)spt";
   "sec_pos_len","(num#num#num)list";
   "pos","num";
   "init_clock","num";
   "ffi_names","(ffiname list)option";
   "shmem_extra","shmem_info_num list";
   "hash_size","num"];;

let lab_to_target_config_component_equality =
  lab_to_target_config_INFO.ri_component_equality;;

let list_add_if_fresh_def = cake_def
  `(list_add_if_fresh (e:A) [] = [e]) /\
   (list_add_if_fresh e (CONS f r) =
      if e = f then CONS f r else CONS f (list_add_if_fresh e r))`;;

let find_ffi_names_def = cake_def
  `(find_ffi_names ([]:((A)sec)list) = []) /\
   (find_ffi_names (CONS (Section k []) rest) = find_ffi_names rest) /\
   (find_ffi_names (CONS (Section k (CONS x xs)) rest) =
      match x with
        LabAsm (CallFFI s) _ _ _ ->
          list_add_if_fresh (ExtCall s) (find_ffi_names (CONS (Section k xs) rest))
      | _ -> find_ffi_names (CONS (Section k xs) rest))`;;

let find_ffi_names_ind = cake_ind "find_ffi_names";;

let get_memop_info_def = cake_def
  `(get_memop_info asm_Load = (MappedRead,word 0:byte)) /\
   (get_memop_info asm_Load32 = (MappedRead,word 4)) /\
   (get_memop_info Load16 = (MappedRead,word 2)) /\
   (get_memop_info Load8 = (MappedRead,word 1)) /\
   (get_memop_info asm_Store = (MappedWrite,word 0)) /\
   (get_memop_info asm_Store32 = (MappedWrite,word 4)) /\
   (get_memop_info Store16 = (MappedWrite,word 2)) /\
   (get_memop_info Store8 = (MappedWrite,word 1))`;;

(* produce a list of ffi_names for shared memory instructions and a list of *)
(* shmem_infos (e.g. pc of the shared memory instruction)                   *)

(* HOL4 proves termination automatically; the measure below is the size of *)
(* the program (three times faster than the kit's own search)               *)

let get_shmem_info_def = cake_def_wf
  `MEASURE (\(code:((A)sec)list,pos:num,ffi_names:ffiname list,
              shmem_info:shmem_info_num list). list_size (sec_size (\x:A. 0)) code)`
  TERM_TAC
  `(get_shmem_info ([]:((A)sec)list) pos ffi_names
                   (shmem_info:shmem_info_num list) = (ffi_names,shmem_info)) /\
   (get_shmem_info (CONS (Section k []) rest) pos ffi_names shmem_info =
      get_shmem_info rest pos ffi_names shmem_info) /\
   (get_shmem_info (CONS (Section k (CONS (lab_Label _ _ _) xs)) rest) pos
                   ffi_names shmem_info =
      get_shmem_info (CONS (Section k xs) rest) pos ffi_names shmem_info) /\
   (get_shmem_info (CONS (Section k (CONS (Asm (ShareMem m r ad) bytes _) xs))
                         rest) pos ffi_names shmem_info =
      let (name,nb) = get_memop_info m in
      get_shmem_info (CONS (Section k xs) rest) (pos + LENGTH bytes)
        (APPEND ffi_names [SharedMem name])
        (APPEND shmem_info
           [shmem_info_num_REC pos nb (match ad with Addr r off -> r)
              (match ad with Addr r off -> val off) r (pos + LENGTH bytes)])) /\
   (get_shmem_info (CONS (Section k (CONS (LabAsm _ _ bytes _) xs)) rest) pos
                   ffi_names shmem_info =
      get_shmem_info (CONS (Section k xs) rest) (pos + LENGTH bytes) ffi_names
        shmem_info) /\
   (get_shmem_info (CONS (Section k (CONS (Asm _ bytes _) xs)) rest) pos
                   ffi_names shmem_info =
      get_shmem_info (CONS (Section k xs) rest) (pos + LENGTH bytes) ffi_names
        shmem_info)`;;

let get_shmem_info_ind = cake_ind "get_shmem_info";;

let compile_lab_def = cake_def
  `compile_lab (asm_conf:(A)asm_config) c sec_list =
     let current_ffis = find_ffi_names sec_list in
     let (ffis,ffis_ok) =
       (match lab_to_target_config_ffi_names c with
          SOME ffis -> (ffis,list_subset current_ffis ffis)
        | _ -> (current_ffis,T)) in
     if ffis_ok then
       match remove_labels (lab_to_target_config_init_clock c) asm_conf
               (lab_to_target_config_pos c) (lab_to_target_config_labels c) ffis
               sec_list with
         SOME (sec_list,l1) ->
           let bytes = prog_to_bytes sec_list in
           let (new_ffis,shmem_infos) =
             get_shmem_info sec_list (lab_to_target_config_pos c) [] [] in
           SOME (bytes,
                 lab_to_target_config_labels_fupd (combin_K l1)
                   (lab_to_target_config_pos_fupd
                      (combin_K (LENGTH bytes + lab_to_target_config_pos c))
                   (lab_to_target_config_sec_pos_len_fupd
                      (combin_K (get_symbols (lab_to_target_config_pos c) sec_list))
                   (lab_to_target_config_ffi_names_fupd
                      (combin_K (SOME (APPEND ffis new_ffis)))
                   (lab_to_target_config_shmem_extra_fupd (combin_K shmem_infos) c)))))
       | NONE -> NONE
     else NONE`;;

(* compile labLang *)

(* HOL4: compile_def *)

let lab_to_target_compile_def = cake_def
  `lab_to_target_compile (asm_conf:(A)asm_config) c sec_list =
     compile_lab asm_conf c (filter_skip sec_list)`;;
