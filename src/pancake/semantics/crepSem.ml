(* ========================================================================= *)
(* crepSem: port of HOL4 pancake/semantics/crepSemScript.sml (CakeML        *)
(* v3479).  Semantics of crepLang.                                           *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: the state record crep_state                *)
(*   (fields crep_state_locals, ...), the result type crep_result            *)
(*   (crep_Error, crep_TimeOut, crepSem_Break, crepSem_Continue,             *)
(*   crepSem_Return, crep_Exception, crep_FinalFFI), crep_eval,              *)
(*   crep_evaluate, crep_semantics, ...; HOL4 Type varname = num and         *)
(*   funname = mlstring are the type abbreviations crepSem_varname and       *)
(*   crepSem_funname.  panSem's word_lab (Word), isWord, theWord,            *)
(*   mem_load_byte, ... are pan_isWord, pan_theWord, pan_mem_load_byte, ...  *)
(* - s.f is crep_state_f s; s with f := v is crep_state_f_fupd (K v) s;      *)
(*   0w is word 0, n2w is word, w2n is val, w2w is word_zx, + on words is    *)
(*   word_add, * is word_mul; HOL4 word_cmp (asm) is asm_word_cmp; ZIP       *)
(*   (xs,ys) is ZIP xs ys (equal lengths in every use: the lengths are      *)
(*   tested first); EVERY is ALL; fromList is llist_fromList; UNIV is (:num). *)
(* - HOL4 infers the most general types for lookup_code, fix_clock and       *)
(*   res_var; they are kept (independent type variables).                   *)
(* - HOL4 binds evaluate_def and evaluate_ind twice: first the definition    *)
(*   with fix_clock (here PCREPAUX_evaluate_fix_def and                      *)
(*   PCREPAUX_evaluate_fix_ind), then, after fix_clock_evaluate, the         *)
(*   versions without it (crep_evaluate_def, crep_evaluate_ind; cake_ind     *)
(*   "crep_evaluate" returns the latter).                                    *)
(* - clock_eq_simp is [local,simp] in HOL4: it is not registered here (the   *)
(*   kit has no theory-local simpset); the proofs that need it name it.      *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "pancake/crepLang.ml";;
needs "pancake/semantics/panSem.ml";;
needs "compiler/backend/wordLang.ml";;
needs "semantics/ffi/ffi.ml";;
needs "hol4/lprefix_lub.ml";;

prioritize_num();;
type_invention_error := true;;

(* re-defining them again to avoid varname from panSem *)

new_type_abbrev("crepSem_varname",`:num`);;

new_type_abbrev("crepSem_funname",`:mlstring`);;

let crep_state_INFO = cake_record "crep_state"
  ["locals","(crepSem_varname,(A)word_lab)fmap";
   "globals","((5)word,(A)word_lab)fmap";
   "code","(crepSem_funname,(crepSem_varname)list#(A)crep_prog)fmap";
   "memory","A word->(A)word_lab";
   "memaddrs","A word->bool";
   "sh_memaddrs","A word->bool";
   "clock","num";
   "be","bool";
   "ffi","(FFI)ffi_state";
   "base_addr","A word";
   "top_addr","A word"];;

let crep_state_component_equality = crep_state_INFO.ri_component_equality;;

let crep_result_INDUCT,crep_result_RECURSION = cake_type
  "crep_result = crep_Error
               | crep_TimeOut
               | crepSem_Break num
               | crepSem_Continue num
               | crepSem_Return (((A)word_lab) list)
               | crep_Exception (A word)
               | crep_FinalFFI final_event";;

let crep_mem_load_def = cake_def
  `crep_mem_load (addr:A word) (s:(A,FFI)crep_state) =
     if addr IN crep_state_memaddrs s
     then SOME (crep_state_memory s addr) else NONE`;;

let crep_set_var_def = cake_def
  `crep_set_var v w (s:(A,FFI)crep_state) =
     crep_state_locals_fupd (combin_K (crep_state_locals s |+ (v,w))) s`;;

(* gv: global variable *)

let crep_set_globals_def = cake_def
  `crep_set_globals gv w (s:(A,FFI)crep_state) =
     crep_state_globals_fupd (combin_K (crep_state_globals s |+ (gv,w))) s`;;

let crep_upd_locals_def = cake_def
  `crep_upd_locals varargs (s:(A,FFI)crep_state) =
     crep_state_locals_fupd (combin_K (FEMPTY |++ varargs)) s`;;

let crep_empty_locals_def = cake_def
  `crep_empty_locals (s:(A,FFI)crep_state) =
     crep_state_locals_fupd (combin_K FEMPTY) s`;;

let crep_lookup_code_def = cake_def
  `crep_lookup_code (code:(K,(N)list#P)fmap) (fname:K) (args:(V)list) (len:L) =
     match FLOOKUP code fname with
       SOME (ns,prog) ->
         if LENGTH ns = LENGTH args /\ ALL_DISTINCT ns
         then SOME (prog,FEMPTY |++ ZIP ns args) else NONE
     | _ -> NONE`;;

let crep_op_def = cake_def
  `(crep_op crep_Mul [w1:A word; w2] = SOME (word_mul w1 w2)) /\
   (crep_op _ _ = NONE)`;;

(* termination: HOL4 measure (exp_size ARB o SND), MEM_IMP_exp_size *)

(* the clauses are parsed in two quotations: op is a binop in crep_Op and a *)
(* crepop in Crepop                                                         *)

let crep_eval_def = cake_def_wf
  `MEASURE ((crep_exp_size ARB o SND):(A,FFI)crep_state#(A)crep_exp->num)`
  (REWRITE_TAC[measure_THM; o_THM] THEN TERM_TAC)
  (list_mk_conj
  [`(crep_eval (s:(A,FFI)crep_state) (crep_Const w:(A)crep_exp) =
      SOME (Word w)) /\
   (crep_eval s (crep_Var v) = FLOOKUP (crep_state_locals s) v) /\
   (crep_eval s (crep_Load addr) =
      match crep_eval s addr with
        SOME (Word w) -> crep_mem_load w s
      | _ -> NONE) /\
   (crep_eval s (crep_Load32 addr) =
      match crep_eval s addr with
        SOME (Word w) ->
          (match pan_mem_load_32 (crep_state_memory s) (crep_state_memaddrs s)
                   (crep_state_be s) w with
             NONE -> NONE
           | SOME w -> SOME (Word (word_zx w)))
      | _ -> NONE) /\
   (crep_eval s (crep_LoadByte addr) =
      match crep_eval s addr with
        SOME (Word w) ->
          (match pan_mem_load_byte (crep_state_memory s) (crep_state_memaddrs s)
                   (crep_state_be s) w with
             NONE -> NONE
           | SOME w -> SOME (Word (word_zx w)))
      | _ -> NONE) /\
   (crep_eval s (LoadGlob gadr) = FLOOKUP (crep_state_globals s) gadr) /\
   (crep_eval s (crep_Op op es) =
      match OPT_MMAP (crep_eval s) es with
        SOME ws ->
          if ALL (\w. match w with Word _ -> T | _ -> F) ws
          then OPTION_MAP Word
                 (word_op op (MAP (\w. match w with Word n -> n) ws))
          else NONE
      | _ -> NONE)`;
   `(crep_eval (s:(A,FFI)crep_state) (Crepop op es:(A)crep_exp) =
      match OPT_MMAP (crep_eval s) es with
        SOME ws ->
          if ALL (\w. match w with Word _ -> T | _ -> F) ws
          then OPTION_MAP Word
                 (crep_op op (MAP (\w. match w with Word n -> n) ws))
          else NONE
      | _ -> NONE) /\
   (crep_eval s (crep_Cmp cmp e1 e2) =
      match (crep_eval s e1,crep_eval s e2) with
        (SOME (Word w1),SOME (Word w2)) ->
          SOME (Word (v2w [asm_word_cmp cmp w1 w2]))
      | _ -> NONE) /\
   (crep_eval s (crep_Shift sh e1 e2) =
      match (crep_eval s e1,crep_eval s e2) with
        (SOME (Word w1),SOME (Word w2)) ->
          OPTION_MAP Word (word_sh sh w1 (val w2))
      | _ -> NONE) /\
   (crep_eval s crep_BaseAddr = SOME (Word (crep_state_base_addr s))) /\
   (crep_eval s crep_TopAddr = SOME (Word (crep_state_top_addr s)))`]);;

(* HOL4 eval_ind.  The kit's induction theorem of crep_eval gives the case *)
(* crep_Cmp (and crep_Shift) the hypothesis for e2 only under              *)
(* crep_eval s e1 = SOME (Word w1) (the pair scrutinee is compiled into     *)
(* nested cases); HOL4's has P s e1 /\ P s e2.  The recursion is            *)
(* structural on the expression, so HOL4's theorem is proved from the       *)
(* structural induction; cake_ind "crep_eval" returns it.                   *)

let crep_eval_ind = prove
 (`!P. (!s w. P s (crep_Const w)) /\
       (!s v. P s (crep_Var v)) /\
       (!s addr. P s addr ==> P s (crep_Load addr)) /\
       (!s addr. P s addr ==> P s (crep_Load32 addr)) /\
       (!s addr. P s addr ==> P s (crep_LoadByte addr)) /\
       (!s gadr. P s (LoadGlob gadr)) /\
       (!s op es. (!y. MEM y es ==> P s y) ==> P s (crep_Op op es)) /\
       (!s op es. (!y. MEM y es ==> P s y) ==> P s (Crepop op es)) /\
       (!s cmp e1 e2. P s e1 /\ P s e2 ==> P s (crep_Cmp cmp e1 e2)) /\
       (!s sh e1 e2. P s e1 /\ P s e2 ==> P s (crep_Shift sh e1 e2)) /\
       (!s. P s crep_BaseAddr) /\
       (!s. P s crep_TopAddr)
       ==> !(x1:(A,FFI)crep_state) (x2:(A)crep_exp). P x1 x2`,
  GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:(A,FFI)crep_state` THEN
  MP_TAC(ISPECL [`(P:(A,FFI)crep_state->(A)crep_exp->bool) s`;
                 `\es. !y. MEM y es ==> (P:(A,FFI)crep_state->(A)crep_exp->bool) s y`]
          crep_exp_INDUCT) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[MEM] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_MESON_TAC[]) THEN MESON_TAC[];
    MESON_TAC[]]);;

let () = cake_ind_store := ("crep_eval",crep_eval_ind) :: !cake_ind_store;;

let crep_dec_clock_def = cake_def
  `crep_dec_clock (s:(A,FFI)crep_state) =
     crep_state_clock_fupd (combin_K (crep_state_clock s - 1)) s`;;

(* HOL4 infers the most general type: old_s and new_s are states of        *)
(* independent types                                                         *)

let crep_fix_clock_def = cake_def
  `crep_fix_clock (old_s:(A,FFI)crep_state) (res:B,(new_s:(C,D)crep_state)) =
     (res,
      crep_state_clock_fupd
        (combin_K (if crep_state_clock old_s < crep_state_clock new_s
            then crep_state_clock old_s else crep_state_clock new_s))
        new_s)`;;

let crep_fix_clock_IMP_LESS_EQ = prove
 (`!x. crep_fix_clock (s:(A,FFI)crep_state) x = (res:B,(s1:(C,D)crep_state))
       ==> crep_state_clock s1 <= crep_state_clock s`,
  REWRITE_TAC[FORALL_PAIR_THM; crep_fix_clock_def; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN SIMP[] THEN ARITH_TAC);;

let crep_res_var_def = cake_def
  `(crep_res_var (lc:(K,V)fmap) (n,NONE) = lc \\ n) /\
   (crep_res_var lc (n,SOME v) = lc |+ (n,v))`;;

(* HOL4 infers the most general type for sh_mem_load, sh_mem_store and     *)
(* sh_mem_op: the type variable of the result (B) is independent of the     *)
(* state's                                                                  *)

let crep_sh_mem_load_def = cake_def
  `crep_sh_mem_load v (addr:A word) nb (s:(A,FFI)crep_state) =
     if nb = 0 then
       (if addr IN crep_state_sh_memaddrs s then
          (match call_FFI (crep_state_ffi s) (SharedMem MappedRead) [word nb]
                   (word_to_bytes addr F) with
             FFI_final outcome ->
               (SOME (crep_FinalFFI outcome:(B)crep_result),crep_empty_locals s)
           | FFI_return new_ffi new_bytes ->
               (NONE,crep_state_ffi_fupd (combin_K new_ffi)
                       (crep_set_var v (Word (word_of_bytes F (word 0) new_bytes))
                          s)))
        else (SOME crep_Error,s))
     else
       (if byte_align addr IN crep_state_sh_memaddrs s then
          (match call_FFI (crep_state_ffi s) (SharedMem MappedRead) [word nb]
                   (word_to_bytes addr F) with
             FFI_final outcome ->
               (SOME (crep_FinalFFI outcome),crep_empty_locals s)
           | FFI_return new_ffi new_bytes ->
               (NONE,crep_state_ffi_fupd (combin_K new_ffi)
                       (crep_set_var v (Word (word_of_bytes F (word 0) new_bytes))
                          s)))
        else (SOME crep_Error,s))`;;

let crep_sh_mem_store_def = cake_def
  `crep_sh_mem_store v (addr:A word) nb (s:(A,FFI)crep_state) =
     match FLOOKUP (crep_state_locals s) v with
       SOME (Word w) ->
         (if nb = 0 then
            (if addr IN crep_state_sh_memaddrs s then
               (match call_FFI (crep_state_ffi s) (SharedMem MappedWrite) [word nb]
                        (APPEND (word_to_bytes w F) (word_to_bytes addr F)) with
                  FFI_final outcome -> (SOME (crep_FinalFFI outcome:(B)crep_result),s)
                | FFI_return new_ffi new_bytes ->
                    (NONE,crep_state_ffi_fupd (combin_K new_ffi) s))
             else (SOME crep_Error,s))
          else
            (if byte_align addr IN crep_state_sh_memaddrs s then
               (match call_FFI (crep_state_ffi s) (SharedMem MappedWrite) [word nb]
                        (APPEND (TAKE nb (word_to_bytes w F))
                                (word_to_bytes addr F)) with
                  FFI_final outcome -> (SOME (crep_FinalFFI outcome),s)
                | FFI_return new_ffi new_bytes ->
                    (NONE,crep_state_ffi_fupd (combin_K new_ffi) s))
             else (SOME crep_Error,s)))
     | _ -> (SOME crep_Error,s)`;;

let crep_sh_mem_op_def = cake_def
  `(crep_sh_mem_op asm_Load r (ad:A word) (s:(A,FFI)crep_state) =
      crep_sh_mem_load r ad 0 s:((B)crep_result)option#(A,FFI)crep_state) /\
   (crep_sh_mem_op asm_Store r ad s = crep_sh_mem_store r ad 0 s) /\
   (crep_sh_mem_op Load8 r ad s = crep_sh_mem_load r ad 1 s) /\
   (crep_sh_mem_op Store8 r ad s = crep_sh_mem_store r ad 1 s) /\
   (crep_sh_mem_op Load16 r ad s = crep_sh_mem_load r ad 2 s) /\
   (crep_sh_mem_op Store16 r ad s = crep_sh_mem_store r ad 2 s) /\
   (crep_sh_mem_op asm_Load32 r ad s = crep_sh_mem_load r ad 4 s) /\
   (crep_sh_mem_op asm_Store32 r ad s = crep_sh_mem_store r ad 4 s)`;;

let crep_primop_def = cake_def
  `crep_primop panLang_AddCarry (args:((A)word_lab)list) =
     if LENGTH args = 3 /\ ALL pan_isWord args then
       let l = pan_theWord (EL 0 args) in
       let r = pan_theWord (EL 1 args) in
       let ci = pan_theWord (EL 2 args) in
       let (res,co) = word_add_carry l r ci in
         SOME [Word res; Word co]
     else NONE`;;

let crep_exit_loop_def = cake_def
  `(crep_exit_loop (SOME (crepSem_Break n):((A)crep_result)option) =
      SOME (crepSem_Break (n - 1))) /\
   (crep_exit_loop (SOME (crepSem_Continue n)) = SOME (crepSem_Continue (n - 1))) /\
   (crep_exit_loop res = res)`;;

let _ = cake_add_simps [crep_exit_loop_def];;

(* ------------------------------------------------------------------------- *)
(* evaluate.  The termination tactic (HOL4: fix_clock_IMP_LESS_EQ, the       *)
(* clock rewrites of set_var, set_globals, upd_locals, dec_clock, then       *)
(* arithmetic) handles both kinds of termination conditions.                 *)
(* ------------------------------------------------------------------------- *)

let PCREPAUX_is_num_fact tm =
  let t = if is_neg tm then dest_neg tm else tm in
  try let h,args = strip_comb t in
      length args = 2 && type_of (hd args) = `:num` &&
      mem (fst(dest_const h)) ["="; "<"; "<="; ">"; ">="]
  with Failure _ -> false;;

let PCREPAUX_TC_TAC : tactic =
  let ths = WF_REL_THMS @ [FST; SND; type_size_def "crep_prog";
             crep_set_var_def; crep_set_globals_def; crep_upd_locals_def;
             crep_dec_clock_def; crep_empty_locals_def;
             crep_state_INFO.ri_accfupds; K_THM; I_THM] in
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP crep_fix_clock_IMP_LESS_EQ)) THEN
  REPEAT GEN_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths THEN
  REPEAT COND_CASES_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (PCREPAUX_is_num_fact o concl))) THEN
  ARITH_TAC;;

let PCREPAUX_evaluate_rel =
  `inv_image (MEASURE I LEX MEASURE (crep_prog_size (combin_K 0)))
     (\p:(A)crep_prog#(A,FFI)crep_state. (crep_state_clock (SND p),FST p))`;;

(* the clauses, parsed in four quotations (HOL4 types each clause on its    *)
(* own: w is a word_lab in Assign, Store and StoreGlob and a word in        *)
(* Store32, StoreByte, If, While and ExtCall; dst is an expression in Store *)
(* and a 5 word in StoreGlob)                                               *)

let PCREPAUX_evaluate_clauses = list_mk_conj
 [`(crep_evaluate (crep_Skip:(A)crep_prog,s:(A,FFI)crep_state) =
      (NONE:((A)crep_result)option,s)) /\
   (crep_evaluate (crep_Dec v e prog,s) =
      match crep_eval s e with
        SOME value ->
          let (res,st) =
            crep_evaluate
              (prog,crep_state_locals_fupd (combin_K (crep_state_locals s |+ (v,value))) s) in
          (res,crep_state_locals_fupd
                 (combin_K (crep_res_var (crep_state_locals st)
                       (v,FLOOKUP (crep_state_locals s) v))) st)
      | NONE -> (SOME crep_Error,s)) /\
   (crep_evaluate (crep_Primitive lhss pop rhss,s) =
      match OPT_MMAP (FLOOKUP (crep_state_locals s)) rhss with
        SOME ws ->
          (match crep_primop pop ws with
             SOME res_ws ->
               if LENGTH lhss = LENGTH res_ws /\
                  ALL (\v. IS_SOME (FLOOKUP (crep_state_locals s) v)) lhss /\
                  ALL_DISTINCT lhss
               then (NONE,crep_state_locals_fupd
                            (combin_K (crep_state_locals s |++ ZIP lhss res_ws)) s)
               else (SOME crep_Error,s)
           | NONE -> (SOME crep_Error,s))
      | NONE -> (SOME crep_Error,s)) /\
   (crep_evaluate (crep_Assign v src,s) =
      match crep_eval s src with
        NONE -> (SOME crep_Error,s)
      | SOME w ->
          (match FLOOKUP (crep_state_locals s) v with
             SOME _ ->
               (NONE,crep_state_locals_fupd (combin_K (crep_state_locals s |+ (v,w))) s)
           | _ -> (SOME crep_Error,s))) /\
   (crep_evaluate (crep_Store dst src,s) =
      match (crep_eval s dst,crep_eval s src) with
        (SOME (Word adr),SOME w) ->
          (match pan_mem_store adr w (crep_state_memaddrs s) (crep_state_memory s) with
             SOME m -> (NONE,crep_state_memory_fupd (combin_K m) s)
           | NONE -> (SOME crep_Error,s))
      | _ -> (SOME crep_Error,s))`;
  `(crep_evaluate (crep_Store32 dst src:(A)crep_prog,s:(A,FFI)crep_state) =
      match (crep_eval s dst,crep_eval s src) with
        (SOME (Word adr),SOME (Word w)) ->
          (match pan_mem_store_32 (crep_state_memory s) (crep_state_memaddrs s)
                   (crep_state_be s) adr (word_zx w) with
             SOME m -> (NONE:((A)crep_result)option,crep_state_memory_fupd (combin_K m) s)
           | NONE -> (SOME crep_Error,s))
      | _ -> (SOME crep_Error,s)) /\
   (crep_evaluate (crep_StoreByte dst src,s) =
      match (crep_eval s dst,crep_eval s src) with
        (SOME (Word adr),SOME (Word w)) ->
          (match pan_mem_store_byte (crep_state_memory s) (crep_state_memaddrs s)
                   (crep_state_be s) adr (word_zx w) with
             SOME m -> (NONE,crep_state_memory_fupd (combin_K m) s)
           | NONE -> (SOME crep_Error,s))
      | _ -> (SOME crep_Error,s))`;
  `(crep_evaluate (StoreGlob dst src:(A)crep_prog,s:(A,FFI)crep_state) =
      match crep_eval s src with
        SOME w -> (NONE:((A)crep_result)option,crep_set_globals dst w s)
      | _ -> (SOME crep_Error,s)) /\
   (crep_evaluate (crep_ShMem op v ad,s) =
      match crep_eval s ad with
        SOME (Word addr) ->
          (if is_load op then
             (match FLOOKUP (crep_state_locals s) v with
                SOME _ -> crep_sh_mem_op op v addr s
              | _ -> (SOME crep_Error,s))
           else
             (match FLOOKUP (crep_state_locals s) v with
                SOME (Word _) -> crep_sh_mem_op op v addr s
              | _ -> (SOME crep_Error,s)))
      | _ -> (SOME crep_Error,s)) /\
   (crep_evaluate (crep_Seq c1 c2,s) =
      let (res,s1) = crep_fix_clock s (crep_evaluate (c1,s)) in
      if res = NONE then crep_evaluate (c2,s1) else (res,s1))`;
  `(crep_evaluate (crep_If e c1 c2:(A)crep_prog,s:(A,FFI)crep_state) =
      match crep_eval s e with
        SOME (Word w) -> crep_evaluate ((if ~(w = word 0) then c1 else c2),s)
      | _ -> (SOME (crep_Error:(A)crep_result),s)) /\
   (crep_evaluate (crep_Break n,s) = (SOME (crepSem_Break n),s)) /\
   (crep_evaluate (crep_Continue n,s) = (SOME (crepSem_Continue n),s)) /\
   (crep_evaluate (crep_While e c,s) =
      match crep_eval s e with
        SOME (Word w) ->
          if ~(w = word 0) then
            (if crep_state_clock s = 0 then (SOME crep_TimeOut,crep_empty_locals s)
             else
               let (res,s1) =
                 crep_fix_clock (crep_dec_clock s)
                   (crep_evaluate (c,crep_dec_clock s)) in
               match res with
                 SOME (crepSem_Continue 0) -> crep_evaluate (crep_While e c,s1)
               | NONE -> crep_evaluate (crep_While e c,s1)
               | SOME (crepSem_Break 0) -> (NONE,s1)
               | res -> (crep_exit_loop res,s1))
          else (NONE,s)
      | _ -> (SOME crep_Error,s)) /\
   (crep_evaluate (crep_Return es,s) =
      match OPT_MMAP (crep_eval s) es with
        SOME ws -> (SOME (crepSem_Return ws),crep_empty_locals s)
      | _ -> (SOME crep_Error,s)) /\
   (crep_evaluate (crep_Raise eid,s) =
      (SOME (crep_Exception eid),crep_empty_locals s)) /\
   (crep_evaluate (crep_Tick,s) =
      if crep_state_clock s = 0 then (SOME crep_TimeOut,crep_empty_locals s)
      else (NONE,crep_dec_clock s)) /\
   (crep_evaluate (crep_Call caltyp fname argexps,s) =
      match OPT_MMAP (crep_eval s) argexps with
        SOME args ->
          (match crep_lookup_code (crep_state_code s) fname args (LENGTH args) with
             SOME (prog,newlocals) ->
               if (match caltyp with
                     NONE -> F
                   | SOME (rts,_) -> ~ALL_DISTINCT rts)
               then (SOME crep_Error,s) else
               (if crep_state_clock s = 0
                then (SOME crep_TimeOut,crep_empty_locals s) else
                let eval_prog =
                  crep_fix_clock
                    (crep_state_locals_fupd (combin_K newlocals) (crep_dec_clock s))
                    (crep_evaluate
                       (prog,crep_state_locals_fupd (combin_K newlocals)
                               (crep_dec_clock s))) in
                match eval_prog with
                  (NONE,st) -> (SOME crep_Error,st)
                | (SOME (crepSem_Break n),st) -> (SOME crep_Error,st)
                | (SOME (crepSem_Continue n),st) -> (SOME crep_Error,st)
                | (SOME (crepSem_Return retvs),st) ->
                    (match caltyp with
                       NONE -> (SOME (crepSem_Return retvs),crep_empty_locals st)
                     | SOME (rts,_) ->
                         if ~(LENGTH retvs = LENGTH rts) then (SOME crep_Error,st)
                         else
                           (match OPT_MMAP (FLOOKUP (crep_state_locals s)) rts with
                              SOME _ ->
                                (NONE,crep_state_locals_fupd
                                        (combin_K (crep_state_locals s |++ ZIP rts retvs))
                                        st)
                            | _ -> (SOME crep_Error,st)))
                | (SOME (crep_Exception eid),st) ->
                    (match caltyp with
                       NONE -> (SOME (crep_Exception eid),crep_empty_locals st)
                     | SOME (_,NONE) -> (SOME (crep_Exception eid),crep_empty_locals st)
                     | SOME (_,SOME (eid',p)) ->
                         if eid = eid' then
                           crep_evaluate
                             (p,crep_state_locals_fupd (combin_K (crep_state_locals s)) st)
                         else (SOME (crep_Exception eid),crep_empty_locals st))
                | (res,st) -> (res,crep_empty_locals st))
           | _ -> (SOME crep_Error,s))
      | _ -> (SOME crep_Error,s)) /\
   (crep_evaluate (crep_ExtCall ffi_index ptr1 len1 ptr2 len2,s) =
      match (FLOOKUP (crep_state_locals s) len1,FLOOKUP (crep_state_locals s) ptr1,
             FLOOKUP (crep_state_locals s) len2,FLOOKUP (crep_state_locals s) ptr2) with
        (SOME (Word w),SOME (Word w2),SOME (Word w3),SOME (Word w4)) ->
          (match (read_bytearray w2 (val w)
                    (pan_mem_load_byte (crep_state_memory s) (crep_state_memaddrs s)
                       (crep_state_be s)),
                  read_bytearray w4 (val w3)
                    (pan_mem_load_byte (crep_state_memory s) (crep_state_memaddrs s)
                       (crep_state_be s))) with
             (SOME bytes,SOME bytes2) ->
               (match call_FFI (crep_state_ffi s) (ExtCall ffi_index) bytes bytes2 with
                  FFI_final outcome -> (SOME (crep_FinalFFI outcome),s)
                | FFI_return new_ffi new_bytes ->
                    let nmem = pan_write_bytearray w4 new_bytes (crep_state_memory s)
                                 (crep_state_memaddrs s) (crep_state_be s) in
                    (NONE,crep_state_ffi_fupd (combin_K new_ffi)
                            (crep_state_memory_fupd (combin_K nmem) s)))
           | _ -> (SOME crep_Error,s))
      | res -> (SOME crep_Error,s))`];;

(* HOL4 evaluate_def and evaluate_ind (the first ones, with fix_clock) *)

let PCREPAUX_evaluate_fix_def =
  cake_def_wf PCREPAUX_evaluate_rel PCREPAUX_TC_TAC PCREPAUX_evaluate_clauses;;

let PCREPAUX_evaluate_fix_ind = cake_ind "crep_evaluate";;

(* HOL4: [local,simp] *)

let clock_eq_simp = prove
 (`crep_state_clock (crep_set_var v w (s:(A,FFI)crep_state)) = crep_state_clock s /\
   crep_state_clock (crep_empty_locals s) = crep_state_clock s /\
   crep_state_clock (crep_set_globals gv w s) = crep_state_clock s`,
  SIMP[crep_set_var_def; crep_empty_locals_def; crep_set_globals_def]);;

(* HOL4: [local] *)

let sh_mem_load_clock = prove
 (`crep_sh_mem_load v addr nb (s:(A,FFI)crep_state) = (r:((B)crep_result)option,s')
   ==> crep_state_clock s' = crep_state_clock s`,
  RW(ONELINE crep_sh_mem_load_def :: all_case_eqs()) THEN SIMP[clock_eq_simp]);;

(* HOL4: [local] *)

let sh_mem_store_clock = prove
 (`crep_sh_mem_store v addr nb (s:(A,FFI)crep_state) = (r:((B)crep_result)option,s')
   ==> crep_state_clock s' = crep_state_clock s`,
  RW(ONELINE crep_sh_mem_store_def :: all_case_eqs()) THEN SIMP[]);;

(* HOL4: sh_mem_op_clock [local] *)

let crep_sh_mem_op_clock = prove
 (`crep_sh_mem_op op v addr (s:(A,FFI)crep_state) = (r:((B)crep_result)option,s')
   ==> crep_state_clock s' = crep_state_clock s`,
  RW(ONELINE crep_sh_mem_op_def :: all_case_eqs()) THEN
  IMP_RES_TAC sh_mem_load_clock THEN IMP_RES_TAC sh_mem_store_clock THEN SIMP[]);;

(* HOL4: evaluate_clock *)

let crep_evaluate_clock = prove
 (`!prog (s:(A,FFI)crep_state) r s'.
     crep_evaluate (prog,s) = (r,s') ==> crep_state_clock s' <= crep_state_clock s`,
  REC_IND_TAC PCREPAUX_evaluate_fix_ind THEN REPEAT STRIP_TAC THEN
  QPAT_X_ASSUM "crep_evaluate _ = _" MP_TAC THEN
  ONCE_REWRITE_TAC[PCREPAUX_evaluate_fix_def] THEN RW[] THEN
  GVS([crep_dec_clock_def; clock_eq_simp] @ all_case_eqs()) THEN
  REPEAT(PAIRARG_TAC THEN GVS[]) THEN
  IMP_RES_TAC crep_sh_mem_op_clock THEN SIMP[] THEN
  IMP_RES_TAC crep_fix_clock_IMP_LESS_EQ THEN GVS(all_case_eqs()) THEN
  DECIDE_TAC);;

(* HOL4: fix_clock_evaluate [local] *)

let crep_fix_clock_evaluate = prove
 (`crep_fix_clock (s:(A,FFI)crep_state) (crep_evaluate (prog,s)) =
   crep_evaluate (prog,s)`,
  CASES_ON `crep_evaluate (prog:(A)crep_prog,s:(A,FFI)crep_state)` THEN
  FS[crep_fix_clock_def] THEN IMP_RES_TAC crep_evaluate_clock THEN
  FS[GSYM NOT_LESS; crep_state_component_equality]);;

(* HOL4: evaluate_ind[allow_rebind] = REWRITE_RULE [fix_clock_evaluate]     *)
(* evaluate_ind; cake_ind "crep_evaluate" returns it from here on           *)

let crep_evaluate_ind =
  REWRITE_RULE[crep_fix_clock_evaluate] PCREPAUX_evaluate_fix_ind;;

let () = cake_ind_store := ("crep_evaluate",crep_evaluate_ind) :: !cake_ind_store;;

(* HOL4: evaluate_def[allow_rebind,compute] = REWRITE_RULE                  *)
(* [fix_clock_evaluate] evaluate_def                                        *)

let crep_evaluate_def =
  REWRITE_RULE[crep_fix_clock_evaluate] PCREPAUX_evaluate_fix_def;;

(* observational semantics *)

let crep_semantics_def = cake_def
  `crep_semantics (s:(A,FFI)crep_state) start =
     let prog = crep_Call NONE start [] in
     if ?k. match FST (crep_evaluate (prog,crep_state_clock_fupd (combin_K k) s)) with
              SOME crep_TimeOut -> F
            | SOME (crep_FinalFFI _) -> F
            | SOME (crepSem_Return _) -> F
            | _ -> T
     then Fail
     else
       match (some res.
                ?k t r outcome.
                  crep_evaluate (prog,crep_state_clock_fupd (combin_K k) s) = (r,t) /\
                  (match r with
                     SOME (crep_FinalFFI e) -> outcome = FFI_outcome e
                   | SOME (crepSem_Return _) -> outcome = Success
                   | _ -> F) /\
                  res = Terminate outcome (ffi_state_io_events (crep_state_ffi t))) with
         SOME res -> res
       | NONE ->
           Diverge
             (build_lprefix_lub
                (IMAGE (\k. llist_fromList
                              (ffi_state_io_events
                                 (crep_state_ffi
                                    (SND (crep_evaluate
                                            (prog,crep_state_clock_fupd (combin_K k) s))))))
                       (:num)))`;;
