(* ========================================================================= *)
(* loopSem: port of HOL4 pancake/semantics/loopSemScript.sml (CakeML v3479). *)
(* The formal semantics of loopLang.                                         *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: loop_state (fields                         *)
(*   loop_state_locals, ...), loop_result (loop_Result, loop_Exception,      *)
(*   loopSem_Break, loopSem_Continue, loop_TimeOut, loop_FinalFFI,           *)
(*   loop_Error), loop_eval, loop_evaluate, loop_semantics, ...             *)
(* - wordSem's word_loc: Word = wl_Word, Loc = wl_Loc; asm's word_cmp is     *)
(*   asm_word_cmp; panLang's AddCarry is panLang_AddCarry.                   *)
(* - Words: n2w = word, w2n = val, w2w = word_zx, / = word_jdiv (HOL4        *)
(*   word_quot); 0w = word 0.  FRONT = BUTLAST; ZIP (a,b) = ZIP a b (the     *)
(*   uses have equal lengths); EVERY = ALL; s.f = loop_state_f s, s with     *)
(*   f := v = loop_state_f_fupd (K v) s; fromList (llist) = llist_fromList.  *)
(* - As in HOL4, evaluate is first defined with fix_clock (                  *)
(*   PLOOPAUX_evaluate_fix_def and PLOOPAUX_evaluate_fix_ind), and           *)
(*   loop_evaluate_def and loop_evaluate_ind are the theorems without it.    *)
(* - Local helpers that are not HOL4 theorems are PLOOPAUX_.                 *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/finite_map.ml";;
needs "hol4/lprefix_lub.ml";;
needs "semantics/ffi/ffi.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "pancake/loopLang.ml";;

prioritize_num();;
type_invention_error := true;;

let loop_state_INFO = cake_record "loop_state"
  ["locals","((A)word_loc)spt";
   "globals","(5 word,(A)word_loc)fmap";
   "memory","A word->(A)word_loc";
   "mdomain","A word->bool";
   "sh_mdomain","A word->bool";
   "clock","num";
   "code","(num list#(A)loop_prog)spt";
   "be","bool";
   "ffi","(FFI)ffi_state";
   "base_addr","A word";
   "top_addr","A word"];;

let loop_state_component_equality = loop_state_INFO.ri_component_equality;;

let loop_result_INDUCT,loop_result_RECURSION = cake_type
  "loop_result = loop_Result (((W)word_loc) list)
               | loop_Exception ((W)word_loc)
               | loopSem_Break num
               | loopSem_Continue num
               | loop_TimeOut
               | loop_FinalFFI final_event
               | loop_Error";;

let loop_dec_clock_def = cake_def
  `loop_dec_clock (s:(A,FFI)loop_state) =
     loop_state_clock_fupd (combin_K (loop_state_clock s - 1)) s`;;

let loop_fix_clock_def = cake_def
  `loop_fix_clock (old_s:(A,B)loop_state) (res:C,(new_s:(D,E)loop_state)) =
     (res, loop_state_clock_fupd
             (combin_K (if loop_state_clock old_s < loop_state_clock new_s
                 then loop_state_clock old_s else loop_state_clock new_s)) new_s)`;;

let loop_set_globals_def = cake_def
  `loop_set_globals gv w (s:(A,FFI)loop_state) =
     loop_state_globals_fupd (combin_K (loop_state_globals s |+ (gv,w))) s`;;

let loop_mem_store_def = cake_def
  `loop_mem_store (addr:A word) (w:(A)word_loc) (s:(A,FFI)loop_state) =
     if addr IN loop_state_mdomain s then
       SOME (loop_state_memory_fupd (combin_K ((addr =+ w) (loop_state_memory s))) s)
     else NONE`;;

let loop_mem_load_def = cake_def
  `loop_mem_load (addr:A word) (s:(A,FFI)loop_state) =
     if addr IN loop_state_mdomain s then
       SOME (loop_state_memory s addr)
     else NONE`;;

let loop_eval_def = cake_def
  `(loop_eval (s:(A,FFI)loop_state) (loop_Const w:(A)loop_exp) = SOME (wl_Word w)) /\
   (loop_eval s (loop_Var v) = lookup v (loop_state_locals s)) /\
   (loop_eval s (loop_Lookup name) = FLOOKUP (loop_state_globals s) name) /\
   (loop_eval s (loop_Load addr) =
      match loop_eval s addr with
        SOME (wl_Word w) -> loop_mem_load w s
      | _ -> NONE) /\
   (loop_eval s (loop_Op op wexps) =
      match the_words (MAP (loop_eval s) wexps) with
        SOME ws -> OPTION_MAP wl_Word (word_op op ws)
      | _ -> NONE) /\
   (loop_eval s (loop_Shift sh wexp1 wexp2) =
      match (loop_eval s wexp1, loop_eval s wexp2) with
        (SOME (wl_Word w1), SOME (wl_Word w2)) ->
          OPTION_MAP wl_Word (word_sh sh w1 (val w2))
      | _ -> NONE) /\
   (loop_eval s loop_BaseAddr = SOME (wl_Word (loop_state_base_addr s))) /\
   (loop_eval s loop_TopAddr = SOME (wl_Word (loop_state_top_addr s)))`;;

(* HOL4: eval_ind.  The kit's induction theorem has the context            *)
(* loop_eval s wexp1 = SOME (wl_Word w1) for the second argument of          *)
(* loop_Shift (the kit splits the tuple of the case expression); the        *)
(* recursion is structural, so HOL4's form follows from structural          *)
(* induction.                                                                *)

let loop_eval_ind = prove
 (`!P:(A,FFI)loop_state->(A)loop_exp->bool.
     (!s w. P s (loop_Const w)) /\
     (!s v. P s (loop_Var v)) /\
     (!s name. P s (loop_Lookup name)) /\
     (!s addr. P s addr ==> P s (loop_Load addr)) /\
     (!s op wexps. (!a. MEM a wexps ==> P s a) ==> P s (loop_Op op wexps)) /\
     (!s sh wexp1 wexp2.
        P s wexp1 /\ P s wexp2 ==> P s (loop_Shift sh wexp1 wexp2)) /\
     (!s. P s loop_BaseAddr) /\
     (!s. P s loop_TopAddr)
     ==> !v v1. P v v1`,
  GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN
   `(!e:(A)loop_exp. P (v:(A,FFI)loop_state) e) /\
    (!l:((A)loop_exp)list. !a. MEM a l ==> P v a)`
   (fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
  MATCH_MP_TAC loop_exp_INDUCT THEN REWRITE_TAC[MEM] THEN
  ASM_MESON_TAC[]);;

let () = cake_ind_store := ("loop_eval",loop_eval_ind) :: !cake_ind_store;;

let get_vars_def = cake_def
  `(get_vars [] (s:(A,FFI)loop_state) = SOME []) /\
   (get_vars (CONS v vs) s =
      match lookup v (loop_state_locals s) with
        NONE -> NONE
      | SOME x -> (match get_vars vs s with
                     NONE -> NONE
                   | SOME xs -> SOME (CONS x xs)))`;;

let loop_set_var_def = cake_def
  `loop_set_var v x (s:(A,FFI)loop_state) =
     loop_state_locals_fupd (combin_K (insert v x (loop_state_locals s))) s`;;

let set_vars_def = cake_def
  `set_vars vs xs (s:(A,FFI)loop_state) =
     loop_state_locals_fupd (combin_K (alist_insert vs xs (loop_state_locals s))) s`;;

let loop_arith_def = cake_def
  `(loop_arith (s:(A,FFI)loop_state) (LDiv r1 r2 r3) =
      match (lookup r3 (loop_state_locals s), lookup r2 (loop_state_locals s)) with
        (SOME (wl_Word q), SOME (wl_Word w2)) ->
          if ~(q = word 0) then
            SOME (loop_set_var r1 (wl_Word (word_jdiv w2 q)) s)
          else NONE
      | _ -> NONE) /\
   (loop_arith s (LLongMul r1 r2 r3 r4) =
      match (lookup r3 (loop_state_locals s), lookup r4 (loop_state_locals s)) with
        (SOME (wl_Word w3), SOME (wl_Word w4)) ->
          (let r = val w3 * val w4 in
             SOME (loop_set_var r2 (wl_Word (word r))
                     (loop_set_var r1 (wl_Word (word (r DIV dimword(:A)))) s)))
      | _ -> NONE) /\
   (loop_arith s (LLongDiv r1 r2 r3 r4 r5) =
      match (lookup r3 (loop_state_locals s), lookup r4 (loop_state_locals s),
             lookup r5 (loop_state_locals s)) with
        (SOME (wl_Word w3), SOME (wl_Word w4), SOME (wl_Word w5)) ->
          (let n = val w3 * dimword (:A) + val w4 in
           let d = val w5 in
           let q = n DIV d in
             if ~(d = 0) /\ q < dimword(:A) then
               SOME (loop_set_var r1 (wl_Word (word q))
                       (loop_set_var r2 (wl_Word (word (n MOD d))) s))
             else NONE)
      | _ -> NONE)`;;

let find_code_def = cake_def
  `(find_code (SOME p) (args:((A)word_loc)list)
              (code:(num list#(A)loop_prog)spt) =
      match lookup p code with
        NONE -> NONE
      | SOME (params,exp) ->
          if LENGTH args = LENGTH params
          then SOME (fromAList (ZIP params args),exp) else NONE) /\
   (find_code NONE args code =
      if args = [] then NONE else
        match LAST args with
          wl_Loc loc 0 ->
            (match lookup loc code with
               NONE -> NONE
             | SOME (params,exp) ->
                 if LENGTH args = LENGTH params + 1
                 then SOME (fromAList (ZIP params (BUTLAST args)),exp)
                 else NONE)
        | other -> NONE)`;;

let get_var_imm_def = cake_def
  `(get_var_imm (Reg n:(A)reg_imm) (s:(A,FFI)loop_state) =
      lookup n (loop_state_locals s)) /\
   (get_var_imm (Imm w) s = SOME (wl_Word w))`;;

(* HOL4: fix_clock_IMP_LESS_EQ *)

let loop_fix_clock_IMP_LESS_EQ = prove
 (`!x. loop_fix_clock (s:(A,FFI)loop_state) x = (res:B,(s1:(A,FFI)loop_state))
       ==> loop_state_clock s1 <= loop_state_clock s`,
  REWRITE_TAC[FORALL_PAIR_THM; loop_fix_clock_def; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  SIMP[] THEN ARITH_TAC);;

let call_env_def = cake_def
  `call_env args (s:(A,FFI)loop_state) =
     loop_state_locals_fupd (combin_K (fromList args)) s`;;

let cut_state_def = cake_def
  `cut_state (live:(B)spt) (s:(A,FFI)loop_state) =
     if domain live SUBSET domain (loop_state_locals s) then
       SOME (loop_state_locals_fupd (combin_K (sptree_inter (loop_state_locals s) live)) s)
     else NONE`;;

let cut_res_def = cake_def
  `cut_res (live:(B)spt) (res:((W)loop_result)option,(s:(A,FFI)loop_state)) =
     if ~(res = NONE) then (res,s) else
       match cut_state live s with
         NONE -> (SOME loop_Error,s)
       | SOME s -> if loop_state_clock s = 0
                   then (SOME loop_TimeOut,loop_state_locals_fupd (combin_K LN) s)
                   else (res,loop_dec_clock s)`;;

(* HOL4: sh_mem_load (its second FFI case has a redundant catch-all row) *)

let loop_sh_mem_load_def = cake_def
  `loop_sh_mem_load v (addr:A word) nb (s:(A,FFI)loop_state) =
     if nb = 0 then
       (if addr IN loop_state_sh_mdomain s then
          (match call_FFI (loop_state_ffi s) (SharedMem MappedRead) [word nb:byte]
                   (word_to_bytes addr F) with
             FFI_final outcome ->
               (SOME (loop_FinalFFI outcome:(W)loop_result), call_env [] s)
           | FFI_return new_ffi new_bytes ->
               (NONE, loop_state_ffi_fupd (combin_K new_ffi)
                        (loop_set_var v (wl_Word (word_of_bytes F (word 0) new_bytes)) s)))
        else (SOME loop_Error, s))
     else
       (if byte_align addr IN loop_state_sh_mdomain s then
          (match call_FFI (loop_state_ffi s) (SharedMem MappedRead) [word nb:byte]
                   (word_to_bytes addr F) with
             FFI_final outcome -> (SOME (loop_FinalFFI outcome), call_env [] s)
           | FFI_return new_ffi new_bytes ->
               (NONE, loop_state_ffi_fupd (combin_K new_ffi)
                        (loop_set_var v (wl_Word (word_of_bytes F (word 0) new_bytes)) s))
           | _ -> (SOME loop_Error, s))
        else (SOME loop_Error, s))`;;

let loop_sh_mem_store_def = cake_def
  `loop_sh_mem_store v (addr:A word) nb (s:(A,FFI)loop_state) =
     match lookup v (loop_state_locals s) with
       SOME (wl_Word w) ->
         (if nb = 0 then
            (if addr IN loop_state_sh_mdomain s then
               (match call_FFI (loop_state_ffi s) (SharedMem MappedWrite) [word nb:byte]
                        (APPEND (word_to_bytes w F) (word_to_bytes addr F)) with
                  FFI_final outcome ->
                    (SOME (loop_FinalFFI outcome:(W)loop_result), call_env [] s)
                | FFI_return new_ffi new_bytes ->
                    (NONE, loop_state_ffi_fupd (combin_K new_ffi) s))
             else (SOME loop_Error, s))
          else
            (if byte_align addr IN loop_state_sh_mdomain s then
               (match call_FFI (loop_state_ffi s) (SharedMem MappedWrite) [word nb:byte]
                        (APPEND (TAKE nb (word_to_bytes w F)) (word_to_bytes addr F)) with
                  FFI_final outcome -> (SOME (loop_FinalFFI outcome), call_env [] s)
                | FFI_return new_ffi new_bytes ->
                    (NONE, loop_state_ffi_fupd (combin_K new_ffi) s))
             else (SOME loop_Error, s)))
     | _ -> (SOME loop_Error, s)`;;

let loop_primop_def = cake_def
  `loop_primop panLang_AddCarry (args:((A)word_loc)list) =
     if LENGTH args = 3 /\ ALL isWord args then
       let l = theWord (EL 0 args) in
       let r = theWord (EL 1 args) in
       let ci = theWord (EL 2 args) in
       let (res,co) = word_add_carry l r ci in
         SOME [wl_Word res; wl_Word co]
     else NONE`;;

(* HOL4: sh_mem_op *)

let loop_sh_mem_op_def = cake_def
  `(loop_sh_mem_op asm_Load r (ad:A word) (s:(A,FFI)loop_state) =
      loop_sh_mem_load r ad 0 s:((W)loop_result)option#(A,FFI)loop_state) /\
   (loop_sh_mem_op asm_Store r ad s = loop_sh_mem_store r ad 0 s) /\
   (loop_sh_mem_op Load8 r ad s = loop_sh_mem_load r ad 1 s) /\
   (loop_sh_mem_op Store8 r ad s = loop_sh_mem_store r ad 1 s) /\
   (loop_sh_mem_op Load16 r ad s = loop_sh_mem_load r ad 2 s) /\
   (loop_sh_mem_op Store16 r ad s = loop_sh_mem_store r ad 2 s) /\
   (loop_sh_mem_op asm_Load32 r ad s = loop_sh_mem_load r ad 4 s) /\
   (loop_sh_mem_op asm_Store32 r ad s = loop_sh_mem_store r ad 4 s)`;;

(* HOL4: set_vars_clock *)

let loop_set_vars_clock = prove
 (`!ns vs (s:(A,FFI)loop_state).
     loop_state_clock (set_vars ns vs s) = loop_state_clock s`,
  REWRITE_TAC[set_vars_def] THEN SIMP[]);;

let _ = cake_add_simps [loop_set_vars_clock];;

(* HOL4: exit_loop *)

let loop_exit_loop_def = cake_def
  `(loop_exit_loop (SOME (loopSem_Break n):((W)loop_result)option) =
      SOME (loopSem_Break (n - 1))) /\
   (loop_exit_loop (SOME (loopSem_Continue n)) = SOME (loopSem_Continue (n - 1))) /\
   (loop_exit_loop res = res)`;;

let _ = cake_add_simps [loop_exit_loop_def];;

(* ------------------------------------------------------------------------- *)
(* The semantics.                                                            *)
(* ------------------------------------------------------------------------- *)

(* the termination conditions: the clock does not grow through fix_clock    *)
(* and cut_res, and cut_res decreases it when it returns NONE              *)

let PLOOPAUX_cut_res_clock = prove
 (`!live res (s:(A,FFI)loop_state) res1 s1.
     cut_res (live:(B)spt) (res:((W)loop_result)option,s) = (res1,s1)
     ==> loop_state_clock s1 <= loop_state_clock s /\
         (res1 = NONE ==> loop_state_clock s1 < loop_state_clock s)`,
  REWRITE_TAC[cut_res_def; cut_state_def; loop_dec_clock_def] THEN
  REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FS[] THEN ASM_ARITH_TAC);;

let PLOOPAUX_clock_rws =
  [call_env_def; loop_dec_clock_def; loop_set_var_def; set_vars_def;
   loop_state_INFO.ri_accfupds; K_THM; I_THM];;

let rec PLOOPAUX_is_num_fact tm =
  if is_neg tm then PLOOPAUX_is_num_fact (dest_neg tm) else
  if is_conj tm || is_disj tm || is_imp tm then
    let l,r = dest_comb tm in
    PLOOPAUX_is_num_fact (rand l) && PLOOPAUX_is_num_fact r
  else
  try let h,args = strip_comb tm in
      length args = 2 && type_of (hd args) = `:num` &&
      mem (fst(dest_const h)) ["="; "<"; "<="; ">"; ">="]
  with Failure _ -> false;;

let PLOOPAUX_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP loop_fix_clock_IMP_LESS_EQ)) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PLOOPAUX_cut_res_clock)) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  (fun g -> let ths = WF_REL_THMS @ [FST; SND; type_size_def "loop_prog"] @
                      PLOOPAUX_clock_rws in
            (RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths) g) THEN
  REWRITE_TAC[COND_RAND; COND_RATOR] THEN REPEAT COND_CASES_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (PLOOPAUX_is_num_fact o concl))) THEN
  ARITH_TAC;;

let PLOOPAUX_evaluate_rel =
  `inv_image (MEASURE I LEX MEASURE (loop_prog_size (\x:A. 0)))
     (\p:(A)loop_prog#(A,FFI)loop_state. (loop_state_clock (SND p), FST p))`;;

let PLOOPAUX_evaluate_clauses =
 `(loop_evaluate (loop_Skip:(A)loop_prog, s:(A,FFI)loop_state) =
     (NONE:((A)loop_result)option, s)) /\
  (loop_evaluate (loop_Fail, s) = (SOME loop_Error, s)) /\
  (loop_evaluate (loop_Assign v exp, s) =
     match loop_eval s exp with
       NONE -> (SOME loop_Error, s)
     | SOME w -> (NONE, loop_set_var v w s)) /\
  (loop_evaluate (loop_Primitive lhss pop rhss, s) =
     match get_vars rhss s with
       SOME ws ->
         (match loop_primop pop ws with
            SOME res_ws ->
              if LENGTH lhss = LENGTH res_ws
              then (NONE, set_vars lhss res_ws s)
              else (SOME loop_Error, s)
          | NONE -> (SOME loop_Error, s))
     | NONE -> (SOME loop_Error, s)) /\
  (loop_evaluate (loop_Arith arith, s) =
     match loop_arith s arith with
       NONE -> (SOME loop_Error, s)
     | SOME s' -> (NONE, s')) /\
  (loop_evaluate (loop_Store exp v, s) =
     match (loop_eval s exp, lookup v (loop_state_locals s)) with
       (SOME (wl_Word adr), SOME w) ->
         (match loop_mem_store adr w s with
            SOME st -> (NONE, st)
          | NONE -> (SOME loop_Error, s))
     | _ -> (SOME loop_Error, s)) /\
  (loop_evaluate (loop_SetGlobal dst exp, s) =
     match loop_eval s exp with
       SOME w -> (NONE, loop_set_globals dst w s)
     | _ -> (SOME loop_Error, s)) /\
  (loop_evaluate (loop_Load32 a v, s) =
     match lookup a (loop_state_locals s) with
       SOME (wl_Word w) ->
         (match mem_load_32 (loop_state_memory s) (loop_state_mdomain s)
                  (loop_state_be s) w with
            SOME b -> (NONE, loop_set_var v (wl_Word (word_zx b)) s)
          | _ -> (SOME loop_Error, s))
     | _ -> (SOME loop_Error, s)) /\
  (loop_evaluate (loop_LoadByte a v, s) =
     match lookup a (loop_state_locals s) with
       SOME (wl_Word w) ->
         (match mem_load_byte_aux (loop_state_memory s) (loop_state_mdomain s)
                  (loop_state_be s) w with
            SOME b -> (NONE, loop_set_var v (wl_Word (word_zx b)) s)
          | _ -> (SOME loop_Error, s))
     | _ -> (SOME loop_Error, s)) /\
  (loop_evaluate (loop_Store32 a w, s) =
     match (lookup a (loop_state_locals s), lookup w (loop_state_locals s)) with
       (SOME (wl_Word w), SOME (wl_Word b)) ->
         (match mem_store_32 (loop_state_memory s) (loop_state_mdomain s)
                  (loop_state_be s) w (word_zx b) with
            SOME m -> (NONE, loop_state_memory_fupd (combin_K m) s)
          | _ -> (SOME loop_Error, s))
     | _ -> (SOME loop_Error, s)) /\
  (loop_evaluate (loop_StoreByte a w, s) =
     match (lookup a (loop_state_locals s), lookup w (loop_state_locals s)) with
       (SOME (wl_Word w), SOME (wl_Word b)) ->
         (match mem_store_byte_aux (loop_state_memory s) (loop_state_mdomain s)
                  (loop_state_be s) w (word_zx b) with
            SOME m -> (NONE, loop_state_memory_fupd (combin_K m) s)
          | _ -> (SOME loop_Error, s))
     | _ -> (SOME loop_Error, s)) /\
  (loop_evaluate (loop_Seq c1 c2, s) =
     let (res,s1) = loop_fix_clock s (loop_evaluate (c1,s)) in
     if res = NONE then loop_evaluate (c2,s1) else (res,s1)) /\
  (loop_evaluate (loop_If cmp r1 ri c1 c2 live_out, s) =
     match (lookup r1 (loop_state_locals s), get_var_imm ri s) with
       (SOME (wl_Word x), SOME (wl_Word y)) ->
         let b = asm_word_cmp cmp x y in
           cut_res live_out (loop_evaluate ((if b then c1 else c2), s))
     | _ -> (SOME loop_Error, s)) /\
  (loop_evaluate (Mark p, s) = loop_evaluate (p, s)) /\
  (loop_evaluate (loop_Break k, s) = (SOME (loopSem_Break k), s)) /\
  (loop_evaluate (loop_Continue k, s) = (SOME (loopSem_Continue k), s)) /\
  (loop_evaluate (loop_Loop live_in body live_out, s) =
     match cut_res live_in (NONE, s) with
       (NONE, s) ->
         (match loop_fix_clock s (loop_evaluate (body, s)) with
            (NONE, s) -> loop_evaluate (loop_Loop live_in body live_out, s)
          | (SOME (loopSem_Continue 0), s) ->
              loop_evaluate (loop_Loop live_in body live_out, s)
          | (SOME (loopSem_Break 0), s) -> cut_res live_out (NONE, s)
          | (res, s) -> (loop_exit_loop res, s))
     | res -> res) /\
  (loop_evaluate (loop_Raise n, s) =
     match lookup n (loop_state_locals s) with
       NONE -> (SOME loop_Error, s)
     | SOME w -> (SOME (loop_Exception w), call_env [] s)) /\
  (loop_evaluate (loop_Return ns, s) =
     match get_vars ns s with
       SOME vs -> (SOME (loop_Result vs), call_env [] s)
     | _ -> (SOME loop_Error, s)) /\
  (loop_evaluate (loop_ShMem op v ad, s) =
     match loop_eval s ad with
       SOME (wl_Word addr) ->
         (if is_load op then
            (match lookup v (loop_state_locals s) with
               SOME _ -> loop_sh_mem_op op v addr s
             | _ -> (SOME loop_Error, s))
          else
            (match lookup v (loop_state_locals s) with
               SOME (wl_Word _) -> loop_sh_mem_op op v addr s
             | _ -> (SOME loop_Error, s)))
     | _ -> (SOME loop_Error, s)) /\
  (loop_evaluate (loop_Tick, s) =
     if loop_state_clock s = 0
     then (SOME loop_TimeOut, loop_state_locals_fupd (combin_K LN) s)
     else (NONE, loop_dec_clock s)) /\
  (loop_evaluate (LocValue r l1, s) =
     if l1 IN domain (loop_state_code s) then
       (NONE, loop_set_var r (wl_Loc l1 0) s)
     else (SOME loop_Error, s)) /\
  (loop_evaluate (loop_Call ret dest argvars handler, s) =
     match get_vars argvars s with
       NONE -> (SOME loop_Error, s)
     | SOME argvals ->
       (match find_code dest argvals (loop_state_code s) with
          NONE -> (SOME loop_Error, s)
        | SOME (env,prog) ->
          (match ret with
             NONE ->
               (if ~(handler = NONE) then (SOME loop_Error, s) else
                if loop_state_clock s = 0
                then (SOME loop_TimeOut, loop_state_locals_fupd (combin_K LN) s)
                else
                  (match loop_evaluate
                           (prog, loop_state_locals_fupd (combin_K env) (loop_dec_clock s)) with
                     (NONE, s) -> (SOME loop_Error, s)
                   | (SOME (loopSem_Continue _), s) -> (SOME loop_Error, s)
                   | (SOME (loopSem_Break _), s) -> (SOME loop_Error, s)
                   | (SOME res, s) -> (SOME res, s)))
           | SOME (ns,live) ->
               if ~ALL_DISTINCT ns then (SOME loop_Error, s) else
               (match cut_res live (NONE, s) with
                  (NONE, s) ->
                    (match loop_fix_clock (loop_state_locals_fupd (combin_K env) s)
                             (loop_evaluate (prog, loop_state_locals_fupd (combin_K env) s)) with
                       (SOME (loop_Result retvs), st) ->
                         if ~(LENGTH retvs = LENGTH ns) then (SOME loop_Error, st) else
                         (match handler with
                            NONE ->
                              (NONE, set_vars ns retvs
                                       (loop_state_locals_fupd (combin_K (loop_state_locals s)) st))
                          | SOME (_,_,r,live_out) ->
                              cut_res live_out
                                (loop_evaluate
                                   (r, set_vars ns retvs
                                         (loop_state_locals_fupd
                                            (combin_K (loop_state_locals s)) st))))
                     | (SOME (loop_Exception exn), st) ->
                         (match handler with
                            NONE ->
                              (SOME (loop_Exception exn), loop_state_locals_fupd (combin_K LN) st)
                          | SOME (n,h,_,live_out) ->
                              cut_res live_out
                                (loop_evaluate
                                   (h, loop_set_var n exn
                                         (loop_state_locals_fupd
                                            (combin_K (loop_state_locals s)) st))))
                     | (SOME (loopSem_Continue _), st) -> (SOME loop_Error, st)
                     | (SOME (loopSem_Break _), st) -> (SOME loop_Error, st)
                     | (NONE, st) -> (SOME loop_Error, st)
                     | res -> res)
                | res -> res)))) /\
  (loop_evaluate (loop_FFI ffi_index ptr1 len1 ptr2 len2 cutset, s) =
     match (lookup len1 (loop_state_locals s), lookup ptr1 (loop_state_locals s),
            lookup len2 (loop_state_locals s), lookup ptr2 (loop_state_locals s),
            cut_state cutset s) with
       (SOME (wl_Word w), SOME (wl_Word w2), SOME (wl_Word w3), SOME (wl_Word w4),
        SOME s) ->
         (match (read_bytearray w2 (val w)
                   (mem_load_byte_aux (loop_state_memory s) (loop_state_mdomain s)
                      (loop_state_be s)),
                 read_bytearray w4 (val w3)
                   (mem_load_byte_aux (loop_state_memory s) (loop_state_mdomain s)
                      (loop_state_be s))) with
            (SOME bytes, SOME bytes2) ->
              (match call_FFI (loop_state_ffi s) (ExtCall ffi_index) bytes bytes2 with
                 FFI_final outcome -> (SOME (loop_FinalFFI outcome), call_env [] s)
               | FFI_return new_ffi new_bytes ->
                   let new_m = write_bytearray w4 new_bytes (loop_state_memory s)
                                 (loop_state_mdomain s) (loop_state_be s) in
                     (NONE, loop_state_ffi_fupd (combin_K new_ffi)
                              (loop_state_memory_fupd (combin_K new_m) s)))
          | _ -> (SOME loop_Error, s))
     | res -> (SOME loop_Error, s))`;;

(* HOL4 evaluate_def (the first one, with fix_clock) *)

let PLOOPAUX_evaluate_fix_def =
  cake_def_wf PLOOPAUX_evaluate_rel PLOOPAUX_TC_TAC PLOOPAUX_evaluate_clauses;;

(* HOL4 evaluate_ind (the first one, with fix_clock) *)

let PLOOPAUX_evaluate_fix_ind = cake_ind "loop_evaluate";;

(* ------------------------------------------------------------------------- *)
(* We prove that the clock never increases.  The proof: the clock facts of   *)
(* the helpers, then the induction hypotheses instantiated at the evaluate   *)
(* assumptions (as for wordSem and stackSem), then arithmetic.               *)
(* ------------------------------------------------------------------------- *)

let PLOOPAUX_mem_store_clock = prove
 (`loop_mem_store a w (s:(A,FFI)loop_state) = SOME s1
   ==> loop_state_clock s1 = loop_state_clock s`,
  REWRITE_TAC[loop_mem_store_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[]);;

let PLOOPAUX_cut_state_clock = prove
 (`cut_state (live:(B)spt) (s:(A,FFI)loop_state) = SOME s1
   ==> loop_state_clock s1 = loop_state_clock s`,
  REWRITE_TAC[cut_state_def] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP[]);;

let PLOOPAUX_arith_clock = prove
 (`!arith s1. loop_arith (s:(A,FFI)loop_state) arith = SOME s1
              ==> loop_state_clock s1 = loop_state_clock s`,
  MATCH_MP_TAC loop_arith_INDUCT THEN
  REWRITE_TAC[loop_arith_def] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[loop_set_var_def] THEN SIMP[]);;

let PLOOPAUX_sh_mem_op_clock = prove
 (`!op r ad (s:(A,FFI)loop_state) res s1.
     loop_sh_mem_op op r ad s = (res:((W)loop_result)option,s1)
     ==> loop_state_clock s1 = loop_state_clock s`,
  MATCH_MP_TAC memop_INDUCT THEN
  REWRITE_TAC[loop_sh_mem_op_def; loop_sh_mem_load_def; loop_sh_mem_store_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[loop_set_var_def; call_env_def] THEN SIMP[]);;

let PLOOPAUX_clock_case_eqs =
  [pair_case_eq; option_case_eq; list_case_eq; COND_CASE_EQ] @
  map case_eq ["word_loc"; "loop_result"; "ffi_result"];;

let PLOOPAUX_is_eval_eq tm =
  is_eq tm &&
  (try fst(dest_const(fst(strip_comb(lhs tm)))) = "loop_evaluate"
   with Failure _ -> false);;

(* for every assumption loop_evaluate p = (v,t) and every induction         *)
(* hypothesis whose evaluate antecedent matches it, add the instance of its  *)
(* conclusion when its other antecedents follow from the assumptions        *)
(* (IL2AUX_EXISTS_ASM_TAC of wordSem finds the witnesses)                    *)

let PLOOPAUX_USE_IHS_TAC : tactic = fun (asl,w as g) ->
  let evs = filter (fun th -> PLOOPAUX_is_eval_eq (concl th)) (map snd asl) in
  let ihs = mapfilter (fun (_,th) ->
      let th' = REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] th in
      let vs,bod = strip_forall (concl th') in
      if is_imp bod && exists PLOOPAUX_is_eval_eq (conjuncts(fst(dest_imp bod)))
      then th' else failwith "") asl in
  let avoid = freesl (w :: map (concl o snd) asl @ flat (map (hyp o snd) asl)) in
  let inst_of ih0 e =
    let vs0,_ = strip_forall (concl ih0) in
    let vs1 = rev(itlist (fun v acc -> variant (acc @ avoid) v :: acc) (rev vs0) []) in
    let ih = GENL vs1 (SPECL vs1 ih0) in
    let vs,bod = strip_forall (concl ih) in
    let ant,_ = dest_imp bod in
    let cj = find PLOOPAUX_is_eval_eq (conjuncts ant) in
    let (_,tmi,tyi) = term_match [] cj (concl e) in
    if exists (fun (a,b) -> not (a = b)) tyi ||
       exists (fun (t,v) -> not (mem v vs) && not (t = v)) tmi then failwith "" else
    let ihi = INST tmi (SPEC_ALL ih) in
    let a,c = dest_imp (concl ihi) in
    let rest = filter (fun v -> mem v vs) (subtract (frees a) (frees c)) in
    c, GENL rest ihi in
  let insts = flat (map (fun e -> mapfilter (fun ih -> inst_of ih e) ihs) evs) in
  MAP_EVERY (fun (c,th) ->
      TRY (SUBGOAL_THEN c ASSUME_TAC THENL
            [MATCH_MP_TAC th THEN IL2AUX_EXISTS_ASM_TAC THEN NO_TAC; ALL_TAC]))
    insts g;;

(* an assumption cut_res l (loop_evaluate x) = r: name the result of the    *)
(* evaluation, so that the induction hypotheses can be used on it           *)

let PLOOPAUX_SPLIT_EVAL_TAC : tactic = fun (asl,w as g) ->
  let is_ev t =
    try fst(dest_const(fst(strip_comb t))) = "loop_evaluate"
    with Failure _ -> false in
  let tms = mapfilter (fun (_,th) ->
      let l = lhs(concl th) in
      if fst(dest_const(fst(strip_comb l))) = "cut_res" && is_ev (rand l)
      then rand l else failwith "") asl in
  MAP_EVERY (fun t -> PAIR_CASES_ON t) tms g;;

let PLOOPAUX_CLOCK_TAC : tactic =
  REPEAT (GEN_TAC ORELSE DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[PLOOPAUX_evaluate_fix_def] THEN
  REWRITE_TAC(PLOOPAUX_clock_case_eqs @ [PAIR_EQ; LET_DEF; LET_END_DEF]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  PLOOPAUX_SPLIT_EVAL_TAC THEN
  PLOOPAUX_USE_IHS_TAC THEN
  MAP_EVERY (fun th -> REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC_ALL o MATCH_MP th)))
    [loop_fix_clock_IMP_LESS_EQ; PLOOPAUX_cut_res_clock; PLOOPAUX_cut_state_clock;
     PLOOPAUX_mem_store_clock; PLOOPAUX_arith_clock; PLOOPAUX_sh_mem_op_clock] THEN
  (fun g -> let ths = PLOOPAUX_clock_rws @ [loop_set_globals_def] in
            (RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths) g) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (PLOOPAUX_is_num_fact o concl))) THEN
  ARITH_TAC;;

let PLOOPAUX_evaluate_clock = prove
 (`!p vs (s2:(A,FFI)loop_state).
     loop_evaluate p = (vs,s2)
     ==> loop_state_clock s2 <= loop_state_clock (SND p)`,
  MATCH_MP_TAC PLOOPAUX_evaluate_fix_ind THEN REWRITE_TAC[SND] THEN
  REPEAT CONJ_TAC THEN PLOOPAUX_CLOCK_TAC);;

(* HOL4: evaluate_clock *)

let loop_evaluate_clock = prove
 (`!xs (s1:(A,FFI)loop_state) vs s2.
     loop_evaluate (xs,s1) = (vs,s2)
     ==> loop_state_clock s2 <= loop_state_clock s1`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PLOOPAUX_evaluate_clock) THEN
  REWRITE_TAC[SND]);;

let PLOOPAUX_fix_clock_id = prove
 (`!(s:(A,FFI)loop_state) (x:B#(A,FFI)loop_state).
     loop_state_clock (SND x) <= loop_state_clock s ==> loop_fix_clock s x = x`,
  REWRITE_TAC[FORALL_PAIR_THM; loop_fix_clock_def; PAIR_EQ; SND] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[loop_state_component_equality] THEN
  SIMP[] THEN ASM_ARITH_TAC);;

(* HOL4: fix_clock_evaluate *)

let loop_fix_clock_evaluate = prove
 (`loop_fix_clock (s:(A,FFI)loop_state) (loop_evaluate (c1,s)) =
   loop_evaluate (c1,s)`,
  MATCH_MP_TAC PLOOPAUX_fix_clock_id THEN
  MP_TAC(ISPEC `loop_evaluate (c1:(A)loop_prog,s:(A,FFI)loop_state)`
           PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[SND] THEN
  MATCH_MP_TAC loop_evaluate_clock THEN ASM_MESON_TAC[]);;

(* we store the theorems without fix_clock *)

(* HOL4: evaluate_ind[allow_rebind] = REWRITE_RULE [fix_clock_evaluate]     *)
(* evaluate_ind *)

let loop_evaluate_ind =
  REWRITE_RULE[loop_fix_clock_evaluate] PLOOPAUX_evaluate_fix_ind;;

(* HOL4: evaluate_def[allow_rebind] = REWRITE_RULE [fix_clock_evaluate]     *)
(* evaluate_def *)

let loop_evaluate_def =
  REWRITE_RULE[loop_fix_clock_evaluate] PLOOPAUX_evaluate_fix_def;;

let () = cake_ind_store := ("loop_evaluate",loop_evaluate_ind) :: !cake_ind_store;;

(* observational semantics *)

(* keeping 0 as the initial parameter to be passed; if returned, it should   *)
(* always be to Loc 1 0; we generate Fail for NONE because it means that the *)
(* program ran out of the code, and didn't exit properly                     *)

let loop_semantics_def = cake_def
  `loop_semantics (s:(A,FFI)loop_state) start =
     let prog = loop_Call NONE (SOME start) [] NONE in
     if ?k. match FST (loop_evaluate (prog, loop_state_clock_fupd (combin_K k) s)) with
              SOME loop_TimeOut -> F
            | SOME (loop_FinalFFI _) -> F
            | SOME (loop_Result _) -> F
            | _ -> T
     then Fail
     else
       match (some res.
                ?k t r outcome.
                  loop_evaluate (prog, loop_state_clock_fupd (combin_K k) s) = (r,t) /\
                  (match r with
                     SOME (loop_FinalFFI e) -> outcome = FFI_outcome e
                   | SOME (loop_Result _) -> outcome = Success
                   | _ -> F) /\
                  res = Terminate outcome (ffi_state_io_events (loop_state_ffi t))) with
         SOME res -> res
       | NONE ->
           Diverge
             (build_lprefix_lub
                (IMAGE (\k. llist_fromList
                              (ffi_state_io_events
                                 (loop_state_ffi
                                    (SND (loop_evaluate
                                            (prog, loop_state_clock_fupd (combin_K k) s))))))
                       (:num)))`;;
