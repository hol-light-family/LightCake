(* ========================================================================= *)
(* pan_itreeSem: port of HOL4 pancake/semantics/pan_itreeSemScript.sml      *)
(* (CakeML v3479).  An itree semantics for Pancake.                          *)
(* HOL4 ext and bst are pan_itreeSem_ext and pan_itreeSem_bst (short or      *)
(* common words; ext captured variables of other files), with the theorems   *)
(* renamed alike (ext_def is pan_itreeSem_ext_def, ...).                     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/libext.ml";;
needs "hol4/itreeTau.ml";;
needs "pancake/semantics/panSem.ml";;

prioritize_num();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* States without clock and ffi.                                             *)
(* ------------------------------------------------------------------------- *)

let bstate_INFO = cake_record "bstate"
  ["locals","(varname,(A)pan_v)fmap";
   "globals","(varname,(A)pan_v)fmap";
   "structs","(stcname#struct_info)list";
   "code","(funname,(varname#shape)list#(A)panLang_prog#shape)fmap";
   "eshapes","(eid,shape)fmap";
   "memory","A word->(A)word_lab";
   "memaddrs","A word->bool";
   "sh_memaddrs","A word->bool";
   "be","bool";
   "base_addr","A word";
   "top_addr","A word"];;

let bstate_component_equality = bstate_INFO.ri_component_equality;;

let pan_itreeSem_empty_locals_def = cake_def
  `pan_itreeSem_empty_locals (s:(A)bstate) = bstate_locals_fupd (K FEMPTY) s`;;

let empty_locals_defs = CONJ pan_empty_locals_def pan_itreeSem_empty_locals_def;;

let pan_itreeSem_set_var_def = cake_def
  `pan_itreeSem_set_var (v:varname) (value:(A)pan_v) (s:(A)bstate) =
     bstate_locals_fupd (K (bstate_locals s |+ (v,value))) s`;;

let set_var_defs = CONJ pan_set_var_def pan_itreeSem_set_var_def;;

let pan_itreeSem_set_global_def = cake_def
  `pan_itreeSem_set_global (v:varname) (value:(A)pan_v) (s:(A)bstate) =
     bstate_globals_fupd (K (bstate_globals s |+ (v,value))) s`;;

let set_global_defs = CONJ pan_set_global_def pan_itreeSem_set_global_def;;

let pan_itreeSem_set_kvar_def = cake_def
  `pan_itreeSem_set_kvar vk (v:varname) (value:(A)pan_v) (s:(A)bstate) =
     match vk with
       panLang_Local -> pan_itreeSem_set_var v value s
     | panLang_Global -> pan_itreeSem_set_global v value s`;;

let set_kvar_defs = CONJ pan_set_kvar_def pan_itreeSem_set_kvar_def;;

let pan_itreeSem_lookup_kvar_def = cake_def
  `pan_itreeSem_lookup_kvar vk (v:varname) (s:(A)bstate) =
     match vk with
       panLang_Local -> FLOOKUP (bstate_locals s) v
     | panLang_Global -> FLOOKUP (bstate_globals s) v`;;

let lookup_kvar_defs = CONJ pan_lookup_kvar_def pan_itreeSem_lookup_kvar_def;;

let pan_itreeSem_is_valid_value_def = cake_def
  `pan_itreeSem_is_valid_value (s:(A)bstate) vk v (value:(A)pan_v) <=>
     match pan_itreeSem_lookup_kvar vk v s with
       SOME w -> shape_of value = shape_of w
     | NONE -> F`;;

let is_valid_value_defs =
  CONJ pan_is_valid_value_def pan_itreeSem_is_valid_value_def;;

let kvar_defs2 = end_itlist CONJ
  [is_valid_value_defs; set_kvar_defs; set_var_defs; set_global_defs;
   lookup_kvar_defs];;

(* ------------------------------------------------------------------------- *)
(* Expressions (as panSem's pan_eval, on bstate).                            *)
(* ------------------------------------------------------------------------- *)

(* HOL4's termination: measure (exp_size ARB o SND), as panSem's eval; the  *)
(* clauses are given in two groups (the variable w is a word in one, a     *)
(* value in the other) and Cmp and Shift are written with pair_CASE, as in *)
(* panSem.ml; pan_itreeSem_eval_def has the case constants of HOL4's.      *)

let PITRAUX_eval_def = cake_def_wf_clauses
  `MEASURE (\p:(A)bstate#(A)panLang_exp. panLang_exp_size ARB (SND p))`
  PSEMAUX_EVAL_TC_TAC
  [`(pan_itreeSem_eval (s:(A)bstate) (panLang_Const w) = SOME (pan_Val (Word w))) /\
    (pan_itreeSem_eval s (panLang_Var panLang_Local v) = FLOOKUP (bstate_locals s) v) /\
    (pan_itreeSem_eval s (panLang_Var panLang_Global v) =
       FLOOKUP (bstate_globals s) v) /\
    (pan_itreeSem_eval s (RStruct es) =
       match OPT_MMAP (pan_itreeSem_eval s) es with
         SOME vs -> SOME (pan_RStruct vs)
       | NONE -> NONE) /\
    (pan_itreeSem_eval s (RField index e) =
       match pan_itreeSem_eval s e with
         SOME (pan_RStruct vs) ->
           if index < LENGTH vs then SOME (EL index vs) else NONE
       | _ -> NONE) /\
    (pan_itreeSem_eval s (NStruct nm eflds) =
       let (field_names,field_exps) = UNZIP eflds in
       match ALOOKUP (bstate_structs s) nm with
         SOME info ->
           let (field_names',field_shapes) = UNZIP (struct_info_fields info) in
           if field_names' = field_names then
             match OPT_MMAP (pan_itreeSem_eval s) field_exps with
               SOME field_vals ->
                 if ALL (\p. match p with (s,v) -> s = shape_of v)
                        (ZIP field_shapes field_vals)
                 then SOME (pan_NStruct nm (ZIP field_names field_vals))
                 else NONE
             | NONE -> NONE
           else NONE
       | NONE -> NONE) /\
    (pan_itreeSem_eval s (NField fld e) =
       match pan_itreeSem_eval s e with
         SOME (pan_NStruct nm vflds) ->
           if ~(ALOOKUP (bstate_structs s) nm = NONE)
           then ALOOKUP vflds fld else NONE
       | _ -> NONE) /\
    (pan_itreeSem_eval s (panLang_Load shape addr) =
       if is_wf_shape (bstate_structs s) shape then
         match pan_itreeSem_eval s addr with
           SOME (pan_Val (Word w)) ->
             pan_mem_load shape w (bstate_memaddrs s) (bstate_memory s)
                          (bstate_structs s)
         | _ -> NONE
       else NONE) /\
    (pan_itreeSem_eval s (panLang_Load32 addr) =
       match pan_itreeSem_eval s addr with
         SOME (pan_Val (Word w)) ->
           (match pan_mem_load_32 (bstate_memory s) (bstate_memaddrs s)
                                  (bstate_be s) w with
              NONE -> NONE
            | SOME w -> SOME (pan_Val (Word (word_zx w))))
       | _ -> NONE) /\
    (pan_itreeSem_eval s (LoadByte addr) =
       match pan_itreeSem_eval s addr with
         SOME (pan_Val (Word w)) ->
           (match pan_mem_load_byte (bstate_memory s) (bstate_memaddrs s)
                                    (bstate_be s) w with
              NONE -> NONE
            | SOME w -> SOME (pan_Val (Word (word_zx w))))
       | _ -> NONE) /\
    (pan_itreeSem_eval s (panLang_Op op es) =
       match OPT_MMAP (pan_itreeSem_eval s) es with
         SOME ws ->
           if ALL (\w. match w with pan_Val (Word _) -> T | _ -> F) ws
           then OPTION_MAP (\w. pan_Val (Word w))
                  (word_op op (MAP (\w. match w with pan_Val (Word n) -> n) ws))
           else NONE
       | _ -> NONE)`;
   `(pan_itreeSem_eval (s:(A)bstate) (Panop op (es:((A)panLang_exp)list)) =
       match OPT_MMAP (pan_itreeSem_eval s) es with
         SOME ws ->
           if ALL (\w. match w with pan_Val (Word _) -> T | _ -> F) ws
           then OPTION_MAP (\w. pan_Val (Word w))
                  (pan_op op (MAP (\w. match w with pan_Val (Word n) -> n) ws))
           else NONE
       | _ -> NONE) /\
    (pan_itreeSem_eval s (Cmp cmp e1 e2) =
       pair_CASE (pan_itreeSem_eval s e1, pan_itreeSem_eval s e2)
         (\r1 r2. match (r1,r2) with
                    (SOME (pan_Val (Word w1)), SOME (pan_Val (Word w2))) ->
                      SOME (pan_Val (Word (if asm_word_cmp cmp w1 w2 then word 1
                                           else word 0)))
                  | _ -> NONE)) /\
    (pan_itreeSem_eval s (panLang_Shift sh e1 e2) =
       pair_CASE (pan_itreeSem_eval s e1, pan_itreeSem_eval s e2)
         (\r1 r2. match (r1,r2) with
                    (SOME (pan_Val (Word w1)), SOME (pan_Val (Word w2))) ->
                      OPTION_MAP (\w. pan_Val (Word w)) (word_sh sh w1 (val w2))
                  | _ -> NONE)) /\
    (pan_itreeSem_eval s BaseAddr = SOME (pan_Val (Word (bstate_base_addr s)))) /\
    (pan_itreeSem_eval s TopAddr = SOME (pan_Val (Word (bstate_top_addr s)))) /\
    (pan_itreeSem_eval s BytesInWord = SOME (pan_Val (Word bytes_in_word)))`];;

let pan_itreeSem_eval_def =
  CONV_RULE (DEPTH_CONV BETA_CONV) (REWRITE_RULE[pair_CASE] PITRAUX_eval_def);;

let pan_itreeSem_eval_ind = cake_ind "pan_itreeSem_eval";;

(* ------------------------------------------------------------------------- *)
(* Events and the recursion combinator mrec.                                 *)
(* ------------------------------------------------------------------------- *)

new_type_abbrev("ev",`:ffiname#byte list#byte list`);;

(* mrec rh t: the calls Vis (INL d) k of t are answered by the tree rh d     *)
(* (recursively), the events Vis (INR e) k are kept                          *)

let mrec_def = cake_def
 `mrec (rh:D->(A,D+B,A)itree) =
    itree_iter
      (\t:(A,D+B,R)itree.
         match t with
           itree_Ret r -> itree_Ret (INR r)
         | Tau t -> itree_Ret (INL t)
         | Vis (INL d) k -> itree_Ret (INL (itree_bind (rh d) k))
         | Vis (INR e) k -> Vis e (itree_Ret o INL o k))`;;

let mrec_simps = prove
 (`(!(rh:D->(A,D+B,A)itree) (r:R). mrec rh (itree_Ret r) = itree_Ret r) /\
   (!(rh:D->(A,D+B,A)itree) (u:(A,D+B,R)itree).
      mrec rh (Tau u) = Tau (mrec rh u)) /\
   (!(rh:D->(A,D+B,A)itree) seed (k:A->(A,D+B,R)itree).
      mrec rh (Vis (INL seed) k) = Tau (mrec rh (itree_bind (rh seed) k))) /\
   (!(rh:D->(A,D+B,A)itree) e (k:A->(A,D+B,R)itree).
      mrec rh (Vis (INR e) k) = Vis e (Tau o mrec rh o k))`,
  REWRITE_TAC[mrec_def] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [itree_iter_thm] THEN
  SIMP[o_DEF; FUN_EQ_THM]);;
let _ = cake_add_simps [mrec_simps];;

let mrec_bind = prove
 (`!(rh:D->(A,D+B,A)itree) ht (k:A->(A,D+B,A)itree).
     mrec rh (itree_bind ht k) = itree_bind (mrec rh ht) (mrec rh o k)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[itree_strong_bisimulation] THEN
  QEXISTS_TAC
   "\\x y. (?ht (k:A->(A,D+B,A)itree). x = mrec rh (itree_bind ht k) /\\
                    y = itree_bind (mrec rh ht) (mrec rh o k)) \\/
           (?ht (k:A->(A,D+B,A)itree). x = Tau (mrec rh (itree_bind ht k)) /\\
                    y = Tau (itree_bind (mrec rh ht) (mrec rh o k)))" THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   (let split =
      NAMED_CASES_ON "ht" ["r0"; "u0"; "e0 g0"] THEN FS[o_THM] THEN
      TRY(QCASES_ON "e0" THEN FS[o_THM]) THEN
      REWRITE_TAC[GSYM itree_bind_assoc] THEN ASM_MESON_TAC[] in
    [split; FS[]; split; FS[] THEN ASM_MESON_TAC[]; split; FS[]]));;
let _ = cake_add_simps [mrec_bind];;

(* ------------------------------------------------------------------------- *)
(* The handler h_prog.                                                       *)
(* ------------------------------------------------------------------------- *)

(* HOL4 leaves the types of the answers to the internal events and of the    *)
(* results of these handlers partly open (they are fixed where mrec h_prog   *)
(* is formed); here each handler has the type that h_prog gives it:         *)
(*   ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,                *)
(*    ((A)panLang_prog#(A)bstate)+ev,                                        *)
(*    (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree           *)

let h_prog_dec_def = cake_def
 `(h_prog_dec vname sh e (p:(A)panLang_prog) (s:(A)bstate):
     ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,
      ((A)panLang_prog#(A)bstate)+ev,
      (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) =
   match pan_itreeSem_eval s e with
     SOME value ->
       if sh = shape_of value
       then Vis (INL (p,bstate_locals_fupd (K (bstate_locals s |+ (vname,value))) s))
              (\a. itree_Ret (INR (match a with
                     INL _ -> (SOME pan_Error,s)
                   | INR (res,s') ->
                       (res,bstate_locals_fupd
                              (K (pan_res_var (bstate_locals s')
                                    (vname,FLOOKUP (bstate_locals s) vname))) s'))))
       else itree_Ret (INR (SOME pan_Error,s))
   | NONE -> itree_Ret (INR (SOME pan_Error,s))`;;

let h_prog_seq_def = cake_def
 `(h_prog_seq (p1:(A)panLang_prog) p2 (s:(A)bstate):
     ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,
      ((A)panLang_prog#(A)bstate)+ev,
      (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) =
   Vis (INL (p1,s))
     (\a. match a with
            INL _ -> itree_Ret (INR (SOME pan_Error,s))
          | INR (res,s') ->
              if res = NONE
              then Vis (INL (p2,s'))
                     (\a. itree_Ret (INR (match a with
                            INL _ -> (SOME pan_Error,s)
                          | INR (res,s') -> (res,s'))))
              else itree_Ret (INR (res,s')))`;;

let h_prog_assign_def = cake_def
 `(h_prog_assign vk vname e (s:(A)bstate):
     ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,
      ((A)panLang_prog#(A)bstate)+ev,
      (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) =
   itree_Ret (INR (match pan_itreeSem_eval s e with
                     SOME value ->
                       if pan_itreeSem_is_valid_value s vk vname value
                       then (NONE,pan_itreeSem_set_kvar vk vname value s)
                       else (SOME pan_Error,s)
                   | NONE -> (SOME pan_Error,s)))`;;

let h_prog_primitive_def = cake_def
 `(h_prog_primitive vname pop es (s:(A)bstate):
     ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,
      ((A)panLang_prog#(A)bstate)+ev,
      (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) =
   itree_Ret (INR (match OPT_MMAP (pan_itreeSem_eval s) es with
                     SOME vs ->
                       (match pan_primop pop vs with
                          SOME value ->
                            if pan_itreeSem_is_valid_value s panLang_Local vname value
                            then (NONE,pan_itreeSem_set_var vname value s)
                            else (SOME pan_Error,s)
                        | NONE -> (SOME pan_Error,s))
                   | _ -> (SOME pan_Error,s)))`;;

let h_prog_store_def = cake_def
 `(h_prog_store dst src (s:(A)bstate):
     ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,
      ((A)panLang_prog#(A)bstate)+ev,
      (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) =
   itree_Ret (INR (match (pan_itreeSem_eval s dst,pan_itreeSem_eval s src) with
                     (SOME (pan_Val (Word addr)),SOME value) ->
                       (match mem_stores addr (flatten value) (bstate_memaddrs s)
                                         (bstate_memory s) with
                          SOME m -> (NONE,bstate_memory_fupd (K m) s)
                        | NONE -> (SOME pan_Error,s))
                   | _ -> (SOME pan_Error,s)))`;;

let h_prog_store_byte_def = cake_def
 `(h_prog_store_byte dst src (s:(A)bstate):
     ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,
      ((A)panLang_prog#(A)bstate)+ev,
      (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) =
   itree_Ret (INR (match (pan_itreeSem_eval s dst,pan_itreeSem_eval s src) with
                     (SOME (pan_Val (Word addr)),SOME (pan_Val (Word w))) ->
                       (match pan_mem_store_byte (bstate_memory s) (bstate_memaddrs s)
                                (bstate_be s) addr (word_zx w) with
                          SOME m -> (NONE,bstate_memory_fupd (K m) s)
                        | NONE -> (SOME pan_Error,s))
                   | _ -> (SOME pan_Error,s)))`;;

let h_prog_store_32_def = cake_def
 `(h_prog_store_32 dst src (s:(A)bstate):
     ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,
      ((A)panLang_prog#(A)bstate)+ev,
      (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) =
   itree_Ret (INR (match (pan_itreeSem_eval s dst,pan_itreeSem_eval s src) with
                     (SOME (pan_Val (Word addr)),SOME (pan_Val (Word w))) ->
                       (match pan_mem_store_32 (bstate_memory s) (bstate_memaddrs s)
                                (bstate_be s) addr (word_zx w) with
                          SOME m -> (NONE,bstate_memory_fupd (K m) s)
                        | NONE -> (SOME pan_Error,s))
                   | _ -> (SOME pan_Error,s)))`;;

let h_prog_cond_def = cake_def
 `(h_prog_cond gexp (p1:(A)panLang_prog) p2 (s:(A)bstate):
     ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,
      ((A)panLang_prog#(A)bstate)+ev,
      (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) =
   match pan_itreeSem_eval s gexp with
     SOME (pan_Val (Word g)) ->
       Vis (INL ((if ~(g = word 0) then p1 else p2),s))
         (\a. itree_Ret (INR (match a with
                INL _ -> (SOME pan_Error,s)
              | INR (res,s') -> (res,s'))))
   | _ -> itree_Ret (INR (SOME pan_Error,s))`;;

(* HOL4's paired lambda \(p,s). .. is written \ps. match ps with (p,s) -> ..*)

let h_prog_while_def = cake_def
 `(h_prog_while g (p:(A)panLang_prog) (s:(A)bstate):
     ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,
      ((A)panLang_prog#(A)bstate)+ev,
      (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) =
   itree_iter
     (\ps. match ps with
             (p,s) ->
               match pan_itreeSem_eval s g with
                 SOME (pan_Val (Word w)) ->
                   if ~(w = word 0)
                   then Vis (INL (p,s))
                          (\a. itree_Ret (match a with
                                 INL _ -> INR (INR (SOME pan_Error,s))
                               | INR (res,s') ->
                                   (match res with
                                      SOME pan_Break -> INR (INR (NONE,s'))
                                    | SOME pan_Continue -> INL (p,s')
                                    | NONE -> INL (p,s')
                                    | _ -> INR (INR (res,s')))))
                   else itree_Ret (INR (INR (NONE,s)))
               | _ -> itree_Ret (INR (INR (SOME pan_Error,s))))
     (p,s)`;;

let h_handle_call_ret_def = cake_def
 `(h_handle_call_ret calltyp rsh (s:(A)bstate)
     (INL _:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate) =
     (itree_Ret (INR (SOME pan_Error,s)):
        ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,
         ((A)panLang_prog#(A)bstate)+ev,
         (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree)) /\
  (h_handle_call_ret calltyp rsh s (INR (NONE,s')) =
     itree_Ret (INR (SOME pan_Error,s'))) /\
  (h_handle_call_ret calltyp rsh s (INR (SOME pan_Break,s')) =
     itree_Ret (INR (SOME pan_Error,s'))) /\
  (h_handle_call_ret calltyp rsh s (INR (SOME pan_Continue,s')) =
     itree_Ret (INR (SOME pan_Error,s'))) /\
  (h_handle_call_ret calltyp rsh s (INR (SOME (pan_Return retv),s')) =
     if ~(shape_of retv = rsh) then itree_Ret (INR (SOME pan_Error,s')) else
     match calltyp with
       NONE -> itree_Ret (INR (SOME (pan_Return retv),pan_itreeSem_empty_locals s'))
     | SOME (NONE,_) ->
         itree_Ret (INR (NONE,bstate_locals_fupd (K (bstate_locals s)) s'))
     | SOME (SOME (rk,rt),_) ->
         if pan_itreeSem_is_valid_value s rk rt retv
         then itree_Ret (INR (NONE,pan_itreeSem_set_kvar rk rt retv
                                     (bstate_locals_fupd (K (bstate_locals s)) s')))
         else itree_Ret (INR (SOME pan_Error,s'))) /\
  (h_handle_call_ret calltyp rsh s (INR (SOME (pan_Exception eid exn),s')) =
     match calltyp with
       NONE -> itree_Ret (INR (SOME (pan_Exception eid exn),
                               pan_itreeSem_empty_locals s'))
     | SOME (_,NONE) -> itree_Ret (INR (SOME (pan_Exception eid exn),
                                        pan_itreeSem_empty_locals s'))
     | SOME (_,SOME (eid',evar,p)) ->
         if eid = eid'
         then
           (match FLOOKUP (bstate_eshapes s) eid with
              SOME sh ->
                if shape_of exn = sh /\
                   pan_itreeSem_is_valid_value s panLang_Local evar exn
                then Vis (INL (p,pan_itreeSem_set_var evar exn
                                   (bstate_locals_fupd (K (bstate_locals s)) s')))
                       (\a. itree_Ret (INR (match a with
                              INL _ -> (SOME pan_Error,s')
                            | INR (res,s') -> (res,s'))))
                else itree_Ret (INR (SOME pan_Error,s'))
            | NONE -> itree_Ret (INR (SOME pan_Error,s')))
         else itree_Ret (INR (SOME (pan_Exception eid exn),
                              pan_itreeSem_empty_locals s'))) /\
  (h_handle_call_ret calltyp rsh s (INR (res,s')) =
     itree_Ret (INR (res,pan_itreeSem_empty_locals s')))`;;

let h_prog_call_def = cake_def
 `(h_prog_call calltyp fname argexps (s:(A)bstate):
     ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,
      ((A)panLang_prog#(A)bstate)+ev,
      (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) =
   match OPT_MMAP (pan_itreeSem_eval s) argexps with
     SOME args ->
       (match pan_lookup_code (bstate_code s) fname args with
          SOME (callee_prog,newlocals,rshape) ->
            Vis (INL (callee_prog,bstate_locals_fupd (K newlocals) s))
                (h_handle_call_ret calltyp rshape s)
        | _ -> itree_Ret (INR (SOME pan_Error,s)))
   | _ -> itree_Ret (INR (SOME pan_Error,s))`;;

let h_handle_deccall_ret_def = cake_def
 `(h_handle_deccall_ret rt shape (prog1:(A)panLang_prog) rsh (s:(A)bstate)
     (INL _:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate) =
     (itree_Ret (INR (SOME pan_Error,s)):
        ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,
         ((A)panLang_prog#(A)bstate)+ev,
         (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree)) /\
  (h_handle_deccall_ret rt shape prog1 rsh s (INR (NONE,s')) =
     itree_Ret (INR (SOME pan_Error,s'))) /\
  (h_handle_deccall_ret rt shape prog1 rsh s (INR (SOME pan_Break,s')) =
     itree_Ret (INR (SOME pan_Error,s'))) /\
  (h_handle_deccall_ret rt shape prog1 rsh s (INR (SOME pan_Continue,s')) =
     itree_Ret (INR (SOME pan_Error,s'))) /\
  (h_handle_deccall_ret rt shape prog1 rsh s (INR (SOME (pan_Return retv),s')) =
     if shape_of retv = shape /\ shape_of retv = rsh then
       Vis (INL (prog1,pan_itreeSem_set_var rt retv
                         (bstate_locals_fupd (K (bstate_locals s)) s')))
         (\a. itree_Ret (INR (match a with
                INL _ -> (SOME pan_Error,s')
              | INR (res',s') ->
                  (res',bstate_locals_fupd
                          (K (pan_res_var (bstate_locals s')
                                (rt,FLOOKUP (bstate_locals s) rt))) s'))))
     else itree_Ret (INR (SOME pan_Error,s'))) /\
  (h_handle_deccall_ret rt shape prog1 rsh s (INR (res,s')) =
     itree_Ret (INR (res,pan_itreeSem_empty_locals s')))`;;

let h_prog_deccall_def = cake_def
 `(h_prog_deccall rt shape fname argexps (prog1:(A)panLang_prog) (s:(A)bstate):
     ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,
      ((A)panLang_prog#(A)bstate)+ev,
      (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) =
   match OPT_MMAP (pan_itreeSem_eval s) argexps with
     SOME args ->
       (match pan_lookup_code (bstate_code s) fname args with
          SOME (callee_prog,newlocals,rshape) ->
            Vis (INL (callee_prog,bstate_locals_fupd (K newlocals) s))
                (h_handle_deccall_ret rt shape prog1 rshape s)
        | _ -> itree_Ret (INR (SOME pan_Error,s)))
   | _ -> itree_Ret (INR (SOME pan_Error,s))`;;

let h_prog_ext_call_def = cake_def
 `(h_prog_ext_call ffi_name conf_ptr conf_len array_ptr array_len (s:(A)bstate):
     ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,
      ((A)panLang_prog#(A)bstate)+ev,
      (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) =
   match (pan_itreeSem_eval s conf_ptr,pan_itreeSem_eval s conf_len,
          pan_itreeSem_eval s array_ptr,pan_itreeSem_eval s array_len) with
     (SOME (pan_Val (Word conf_ptr_adr)),SOME (pan_Val (Word conf_sz)),
      SOME (pan_Val (Word array_ptr_adr)),SOME (pan_Val (Word array_sz))) ->
       (match (read_bytearray conf_ptr_adr (val conf_sz)
                 (pan_mem_load_byte (bstate_memory s) (bstate_memaddrs s) (bstate_be s)),
               read_bytearray array_ptr_adr (val array_sz)
                 (pan_mem_load_byte (bstate_memory s) (bstate_memaddrs s) (bstate_be s)))
        with
          (SOME conf_bytes,SOME array_bytes) ->
            if ~(explode ffi_name = "") then
              Vis (INR (ExtCall ffi_name,conf_bytes,array_bytes))
                (\res. itree_Ret (INR
                   (match res with
                      INL x ->
                        (match x with
                           INL outcome ->
                             (SOME (pan_FinalFFI (Final_event (ExtCall ffi_name)
                                                    conf_bytes array_bytes outcome)),
                              pan_itreeSem_empty_locals s)
                         | INR new_bytes ->
                             if LENGTH new_bytes = LENGTH array_bytes
                             then
                               (let nmem = pan_write_bytearray array_ptr_adr new_bytes
                                             (bstate_memory s) (bstate_memaddrs s)
                                             (bstate_be s) in
                                (NONE,bstate_memory_fupd (K nmem) s))
                             else
                               (SOME (pan_FinalFFI (Final_event (ExtCall ffi_name)
                                                      conf_bytes array_bytes FFI_failed)),
                                pan_itreeSem_empty_locals s))
                    | INR _ -> (SOME pan_Error,s))))
            else itree_Ret (INR
                   (NONE,bstate_memory_fupd
                           (K (pan_write_bytearray array_ptr_adr array_bytes
                                 (bstate_memory s) (bstate_memaddrs s) (bstate_be s))) s))
        | _ -> itree_Ret (INR (SOME pan_Error,s)))
   | _ -> itree_Ret (INR (SOME pan_Error,s))`;;

let h_prog_raise_def = cake_def
 `(h_prog_raise eid e (s:(A)bstate):
     ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,
      ((A)panLang_prog#(A)bstate)+ev,
      (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) =
   itree_Ret (INR (match (FLOOKUP (bstate_eshapes s) eid,pan_itreeSem_eval s e) with
                     (SOME sh,SOME value) ->
                       if shape_of value = sh /\
                          size_of_sh_with_ctxt (bstate_structs s) (shape_of value) <= 32
                       then (SOME (pan_Exception eid value),pan_itreeSem_empty_locals s)
                       else (SOME pan_Error,s)
                   | _ -> (SOME pan_Error,s)))`;;

let h_prog_return_def = cake_def
 `(h_prog_return e (s:(A)bstate):
     ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,
      ((A)panLang_prog#(A)bstate)+ev,
      (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) =
   itree_Ret (INR (match pan_itreeSem_eval s e with
                     SOME value ->
                       if size_of_sh_with_ctxt (bstate_structs s) (shape_of value) <= 32
                       then (SOME (pan_Return value),pan_itreeSem_empty_locals s)
                       else (SOME pan_Error,s)
                   | _ -> (SOME pan_Error,s)))`;;

let h_prog_sh_mem_load_def = cake_def
 `(h_prog_sh_mem_load op vk v ad (s:(A)bstate):
     ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,
      ((A)panLang_prog#(A)bstate)+ev,
      (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) =
   match pan_itreeSem_eval s ad with
     SOME (pan_Val (Word addr)) ->
       (match pan_itreeSem_lookup_kvar vk v s with
          SOME (pan_Val _) ->
            (let nb = nb_op op in
             let bytes = word_to_bytes addr F in
             if nb = 0 then
               (if addr IN bstate_sh_memaddrs s
                then
                  Vis (INR (SharedMem MappedRead,[word nb],bytes))
                    (\res. itree_Ret (INR
                       (match res with
                          INL x ->
                            (match x with
                               INL outcome ->
                                 (SOME (pan_FinalFFI (Final_event (SharedMem MappedRead)
                                                        [word nb] bytes outcome)),
                                  pan_itreeSem_empty_locals s)
                             | INR new_bytes ->
                                 if LENGTH new_bytes = LENGTH bytes
                                 then
                                   (NONE,pan_itreeSem_set_kvar vk v
                                           (pan_Val (Word (word_of_bytes F (word 0)
                                                             new_bytes))) s)
                                 else
                                   (SOME (pan_FinalFFI (Final_event (SharedMem MappedRead)
                                                          [word nb] bytes FFI_failed)),
                                    pan_itreeSem_empty_locals s))
                        | INR _ -> (SOME pan_Error,s))))
                else itree_Ret (INR (SOME pan_Error,s)))
             else
               (if byte_align addr IN bstate_sh_memaddrs s then
                  Vis (INR (SharedMem MappedRead,[word nb],bytes))
                    (\res. itree_Ret (INR
                       (match res with
                          INL x ->
                            (match x with
                               INL outcome ->
                                 (SOME (pan_FinalFFI (Final_event (SharedMem MappedRead)
                                                        [word nb] bytes outcome)),
                                  pan_itreeSem_empty_locals s)
                             | INR new_bytes ->
                                 if LENGTH new_bytes = LENGTH bytes
                                 then
                                   (NONE,pan_itreeSem_set_kvar vk v
                                           (pan_Val (Word (word_of_bytes F (word 0)
                                                             new_bytes))) s)
                                 else
                                   (SOME (pan_FinalFFI (Final_event (SharedMem MappedRead)
                                                          [word nb] bytes FFI_failed)),
                                    pan_itreeSem_empty_locals s))
                        | INR _ -> (SOME pan_Error,s))))
                else itree_Ret (INR (SOME pan_Error,s))))
        | _ -> itree_Ret (INR (SOME pan_Error,s)))
   | _ -> itree_Ret (INR (SOME pan_Error,s))`;;

let h_prog_sh_mem_store_def = cake_def
 `(h_prog_sh_mem_store op ad e (s:(A)bstate):
     ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,
      ((A)panLang_prog#(A)bstate)+ev,
      (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) =
   match (pan_itreeSem_eval s ad,pan_itreeSem_eval s e) with
     (SOME (pan_Val (Word addr)),SOME (pan_Val (Word w))) ->
       (let nb = nb_op op in
        if nb = 0 then
          (if addr IN bstate_sh_memaddrs s then
             let bytes = APPEND (word_to_bytes w F) (word_to_bytes addr F) in
             Vis (INR (SharedMem MappedWrite,[word nb],bytes))
               (\res. itree_Ret (INR
                  (match res with
                     INL x ->
                       (match x with
                          INL outcome ->
                            (SOME (pan_FinalFFI (Final_event (SharedMem MappedWrite)
                                                   [word nb] bytes outcome)),s)
                        | INR new_bytes ->
                            if LENGTH new_bytes = LENGTH bytes
                            then (NONE,s)
                            else
                              (SOME (pan_FinalFFI (Final_event (SharedMem MappedWrite)
                                                     [word nb] bytes FFI_failed)),s))
                   | INR _ -> (SOME pan_Error,s))))
           else itree_Ret (INR (SOME pan_Error,s)))
        else
          (if byte_align addr IN bstate_sh_memaddrs s then
             let bytes = APPEND (TAKE nb (word_to_bytes w F)) (word_to_bytes addr F) in
             Vis (INR (SharedMem MappedWrite,[word nb],bytes))
               (\res. itree_Ret (INR
                  (match res with
                     INL x ->
                       (match x with
                          INL outcome ->
                            (SOME (pan_FinalFFI (Final_event (SharedMem MappedWrite)
                                                   [word nb] bytes outcome)),s)
                        | INR new_bytes ->
                            if LENGTH new_bytes = LENGTH bytes
                            then (NONE,s)
                            else
                              (SOME (pan_FinalFFI (Final_event (SharedMem MappedWrite)
                                                     [word nb] bytes FFI_failed)),s))
                   | INR _ -> (SOME pan_Error,s))))
           else itree_Ret (INR (SOME pan_Error,s))))
   | _ -> itree_Ret (INR (SOME pan_Error,s))`;;

let h_prog_def = cake_def
 `(h_prog (panLang_Skip,(s:(A)bstate)) =
     (itree_Ret (INR (NONE,s)):
        ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,
         ((A)panLang_prog#(A)bstate)+ev,
         (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree)) /\
  (h_prog (Annot _ _,s) = itree_Ret (INR (NONE,s))) /\
  (h_prog (Dec vname sh e p,s) = h_prog_dec vname sh e p s) /\
  (h_prog (panLang_Assign vk vname e,s) = h_prog_assign vk vname e s) /\
  (h_prog (Primitive vname pop es,s) = h_prog_primitive vname pop es s) /\
  (h_prog (panLang_Store dst src,s) = h_prog_store dst src s) /\
  (h_prog (panLang_Store32 dst src,s) = h_prog_store_32 dst src s) /\
  (h_prog (StoreByte dst src,s) = h_prog_store_byte dst src s) /\
  (h_prog (ShMemLoad op vk v ad,s) = h_prog_sh_mem_load op vk v ad s) /\
  (h_prog (ShMemStore op ad e,s) = h_prog_sh_mem_store op ad e s) /\
  (h_prog (panLang_Seq p1 p2,s) = h_prog_seq p1 p2 s) /\
  (h_prog (panLang_If gexp p1 p2,s) = h_prog_cond gexp p1 p2 s) /\
  (h_prog (While gexp p,s) = h_prog_while gexp p s) /\
  (h_prog (panLang_Break,s) = itree_Ret (INR (SOME pan_Break,s))) /\
  (h_prog (panLang_Continue,s) = itree_Ret (INR (SOME pan_Continue,s))) /\
  (h_prog (panLang_Call calltyp tgtexp argexps,s) =
     h_prog_call calltyp tgtexp argexps s) /\
  (h_prog (DecCall rt shape tgtexp argexps prog1,s) =
     h_prog_deccall rt shape tgtexp argexps prog1 s) /\
  (h_prog (panLang_ExtCall ffi_name conf_ptr conf_len array_ptr array_len,s) =
     h_prog_ext_call ffi_name conf_ptr conf_len array_ptr array_len s) /\
  (h_prog (panLang_Raise eid e,s) = h_prog_raise eid e s) /\
  (h_prog (panLang_Return e,s) = h_prog_return e s) /\
  (h_prog (panLang_Tick,s) = itree_Ret (INR (NONE,s)))`;;

(* ------------------------------------------------------------------------- *)
(* The itree semantics.                                                      *)
(* ------------------------------------------------------------------------- *)

let itree_evaluate_def = cake_def
 `itree_evaluate ((p:(A)panLang_prog),(s:(A)bstate)) =
    let g = (\x. match x with
                   INR (r:((A)pan_result)option#(A)bstate) -> r
                 | INL (l:ffi_outcome+byte list) -> (SOME pan_Error,s)) in
    itree_unfold (\x. match x with
                        itree_Ret r -> Ret' (g r)
                      | Tau t -> Tau' t
                      | Vis e f -> Vis' e (\y. f (INL y)))
                 (mrec h_prog (h_prog (p,s)))`;;

let h_prog_simple_defs = end_itlist CONJ
  [h_prog_def; h_prog_assign_def; h_prog_primitive_def; h_prog_store_def;
   h_prog_store_32_def; h_prog_store_byte_def; h_prog_raise_def;
   h_prog_return_def];;

(* HOL4: Type ptree = :((ffi_outcome + word8 list) + 'a result option #     *)
(*   'a bstate, ev, (ffi_outcome + word8 list) + 'a result option #         *)
(*   'a bstate) itree  and  Type fst = :(ffiname -> 'b -> word8 list ->      *)
(*   word8 list -> 'b oracle_result) # 'b  (expanded at use)                 *)

(* HOL4: move to itreeTauTheory *)

let itree_unfold_FUNPOW_Tau = prove
 (`!(f:(A,E,R)itree->(B,C,D,(A,E,R)itree)itree_next) n t.
     (!u. f (Tau u) = Tau' u) ==>
     itree_unfold f (ITER n Tau t) = ITER n Tau (itree_unfold f t)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [itree_unfold] THEN SIMP[]);;

let pan_itreeSem_ext_def = cake_def
 `pan_itreeSem_ext (s:(A)bstate) k (ffi:(B)ffi_state) =
    pan_state_REC (bstate_locals s) (bstate_globals s) (bstate_structs s)
      (bstate_code s) (bstate_eshapes s) (bstate_memory s) (bstate_memaddrs s)
      (bstate_sh_memaddrs s) k (bstate_be s) ffi (bstate_base_addr s)
      (bstate_top_addr s)`;;

let ext_access = prove
 (`!(t:(A)bstate) k (ffi:(B)ffi_state).
     pan_state_locals (pan_itreeSem_ext t k ffi) = bstate_locals t /\
     pan_state_globals (pan_itreeSem_ext t k ffi) = bstate_globals t /\
     pan_state_structs (pan_itreeSem_ext t k ffi) = bstate_structs t /\
     pan_state_code (pan_itreeSem_ext t k ffi) = bstate_code t /\
     pan_state_eshapes (pan_itreeSem_ext t k ffi) = bstate_eshapes t /\
     pan_state_memory (pan_itreeSem_ext t k ffi) = bstate_memory t /\
     pan_state_memaddrs (pan_itreeSem_ext t k ffi) = bstate_memaddrs t /\
     pan_state_sh_memaddrs (pan_itreeSem_ext t k ffi) = bstate_sh_memaddrs t /\
     pan_state_be (pan_itreeSem_ext t k ffi) = bstate_be t /\
     pan_state_ffi (pan_itreeSem_ext t k ffi) = ffi /\
     pan_state_base_addr (pan_itreeSem_ext t k ffi) = bstate_base_addr t /\
     pan_state_top_addr (pan_itreeSem_ext t k ffi) = bstate_top_addr t /\
     pan_state_clock (pan_itreeSem_ext t k ffi) = k`,
  RW[pan_itreeSem_ext_def]);;
let _ = cake_add_simps [ext_access];;

let eval_ext = prove
 (`!(s:(A)bstate) e t (ffi:(B)ffi_state).
     pan_eval (pan_itreeSem_ext s t ffi) e = pan_itreeSem_eval s e`,
  REC_IND_TAC pan_itreeSem_eval_ind THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[pan_eval_def; pan_itreeSem_eval_def; ext_access] THEN
  SIMP[CONGR OPT_MMAP_CONG; ETA_AX] THEN REWRITE_TAC[ETA_AX] THEN
  REPEAT(TOP_CASE_TAC THEN FS[CONGR OPT_MMAP_CONG; ETA_AX] THEN
         REWRITE_TAC[ETA_AX]));;
let _ = cake_add_simps [eval_ext];;

let opt_mmap_eval_ext = prove
 (`!(s:(A)bstate) t (ffi:(B)ffi_state) es.
     OPT_MMAP (pan_eval (pan_itreeSem_ext s t ffi)) es = OPT_MMAP (pan_itreeSem_eval s) es`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC OPT_MMAP_CONG THEN REWRITE_TAC[eval_ext]);;
let _ = cake_add_simps [opt_mmap_eval_ext];;

(* HOL4 dec_clock is panSem's (pan_dec_clock) *)

let ext_normalise = prove
 (`!(s:(A)bstate) t (f:(B)ffi_state) x m k k' (ffi:(B)ffi_state) ffi'.
     pan_state_locals_fupd (K x) (pan_itreeSem_ext s t f) = pan_itreeSem_ext (bstate_locals_fupd (K x) s) t f /\
     pan_state_memory_fupd (K m) (pan_itreeSem_ext s t f) = pan_itreeSem_ext (bstate_memory_fupd (K m) s) t f /\
     pan_state_clock_fupd (K k') (pan_itreeSem_ext s k ffi) = pan_itreeSem_ext s k' ffi /\
     pan_state_ffi_fupd (K ffi') (pan_itreeSem_ext s k ffi) = pan_itreeSem_ext s k ffi' /\
     pan_dec_clock (pan_itreeSem_ext s k f) = pan_itreeSem_ext s (k - 1) f`,
  RW[pan_itreeSem_ext_def; pan_dec_clock_def]);;
let _ = cake_add_simps [ext_normalise];;

let pan_itreeSem_bst_def = cake_def
 `pan_itreeSem_bst (s:(A,B)pan_state) =
    bstate_REC (pan_state_locals s) (pan_state_globals s) (pan_state_structs s)
      (pan_state_code s) (pan_state_eshapes s) (pan_state_memory s)
      (pan_state_memaddrs s) (pan_state_sh_memaddrs s) (pan_state_be s)
      (pan_state_base_addr s) (pan_state_top_addr s)`;;

let bst_access = prove
 (`!t:(A,B)pan_state.
     bstate_locals (pan_itreeSem_bst t) = pan_state_locals t /\
     bstate_globals (pan_itreeSem_bst t) = pan_state_globals t /\
     bstate_structs (pan_itreeSem_bst t) = pan_state_structs t /\
     bstate_code (pan_itreeSem_bst t) = pan_state_code t /\
     bstate_eshapes (pan_itreeSem_bst t) = pan_state_eshapes t /\
     bstate_memory (pan_itreeSem_bst t) = pan_state_memory t /\
     bstate_memaddrs (pan_itreeSem_bst t) = pan_state_memaddrs t /\
     bstate_sh_memaddrs (pan_itreeSem_bst t) = pan_state_sh_memaddrs t /\
     bstate_be (pan_itreeSem_bst t) = pan_state_be t /\
     bstate_base_addr (pan_itreeSem_bst t) = pan_state_base_addr t /\
     bstate_top_addr (pan_itreeSem_bst t) = pan_state_top_addr t`,
  RW[pan_itreeSem_bst_def]);;
let _ = cake_add_simps [bst_access];;

(* HOL4 s with <|locals := x; clock := k|> is written with the locals       *)
(* update outermost (the simpset's order of updates)                        *)

let bst_normalise = prove
 (`!(s:(A,B)pan_state) x m k.
     bstate_locals_fupd (K x) (pan_itreeSem_bst s) = pan_itreeSem_bst (pan_state_locals_fupd (K x) s) /\
     bstate_globals_fupd (K x) (pan_itreeSem_bst s) = pan_itreeSem_bst (pan_state_globals_fupd (K x) s) /\
     bstate_memory_fupd (K m) (pan_itreeSem_bst s) = pan_itreeSem_bst (pan_state_memory_fupd (K m) s) /\
     pan_itreeSem_bst (pan_state_locals_fupd (K x) (pan_state_clock_fupd (K k) s)) =
       pan_itreeSem_bst (pan_state_locals_fupd (K x) s) /\
     pan_itreeSem_bst (pan_state_globals_fupd (K x) (pan_state_clock_fupd (K k) s)) =
       pan_itreeSem_bst (pan_state_globals_fupd (K x) s) /\
     pan_itreeSem_bst (pan_state_memory_fupd (K m) (pan_state_clock_fupd (K k) s)) =
       pan_itreeSem_bst (pan_state_memory_fupd (K m) s) /\
     pan_itreeSem_bst (pan_state_clock_fupd (K k) s) = pan_itreeSem_bst s`,
  RW[pan_itreeSem_bst_def]);;
let _ = cake_add_simps [bst_normalise];;

let eval_bst = prove
 (`!(s:(A,B)pan_state) e. pan_itreeSem_eval (pan_itreeSem_bst s) e = pan_eval s e`,
  REC_IND_TAC pan_eval_ind THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[pan_eval_def; pan_itreeSem_eval_def; bst_access] THEN
  SIMP[CONGR OPT_MMAP_CONG; ETA_AX] THEN REWRITE_TAC[ETA_AX] THEN
  REPEAT(TOP_CASE_TAC THEN FS[CONGR OPT_MMAP_CONG; ETA_AX] THEN
         REWRITE_TAC[ETA_AX]));;
let _ = cake_add_simps [eval_bst];;

let opt_mmap_eval_bst = prove
 (`!(s:(A,B)pan_state) es.
     OPT_MMAP (pan_itreeSem_eval (pan_itreeSem_bst s)) es = OPT_MMAP (pan_eval s) es`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC OPT_MMAP_CONG THEN REWRITE_TAC[eval_bst]);;
let _ = cake_add_simps [opt_mmap_eval_bst];;

(* HOL4 s with <|clock := k; ffi := ffi|> is written with the clock update  *)
(* outermost (the simpset's order of updates)                               *)

let ext_bst_id = prove
 (`!(s:(A,B)pan_state) x m k (ffi:(B)ffi_state).
     pan_itreeSem_ext (pan_itreeSem_bst s) (pan_state_clock s) (pan_state_ffi s) = s /\
     pan_itreeSem_ext (bstate_locals_fupd (K x) (pan_itreeSem_bst s)) (pan_state_clock s) (pan_state_ffi s) =
       pan_state_locals_fupd (K x) s /\
     pan_itreeSem_ext (bstate_globals_fupd (K x) (pan_itreeSem_bst s)) (pan_state_clock s) (pan_state_ffi s) =
       pan_state_globals_fupd (K x) s /\
     pan_itreeSem_ext (bstate_memory_fupd (K m) (pan_itreeSem_bst s)) (pan_state_clock s) (pan_state_ffi s) =
       pan_state_memory_fupd (K m) s /\
     pan_itreeSem_ext (pan_itreeSem_empty_locals (pan_itreeSem_bst s)) (pan_state_clock s) (pan_state_ffi s) =
       pan_empty_locals s /\
     pan_itreeSem_ext (pan_itreeSem_bst s) k (pan_state_ffi s) = pan_state_clock_fupd (K k) s /\
     pan_itreeSem_ext (pan_itreeSem_bst s) (pan_state_clock s) ffi = pan_state_ffi_fupd (K ffi) s /\
     pan_itreeSem_ext (pan_itreeSem_bst s) k ffi = pan_state_clock_fupd (K k) (pan_state_ffi_fupd (K ffi) s)`,
  RW[pan_itreeSem_bst_def; pan_itreeSem_ext_def; pan_state_component_equality; empty_locals_defs]);;
let _ = cake_add_simps [ext_bst_id];;

let bst_ext_id = prove
 (`!(s:(A)bstate) t (f:(B)ffi_state) x m k (ffi:(B)ffi_state).
     pan_itreeSem_bst (pan_itreeSem_ext s t f) = s /\
     pan_itreeSem_bst (pan_state_locals_fupd (K x) (pan_itreeSem_ext s t f)) = bstate_locals_fupd (K x) s /\
     pan_itreeSem_bst (pan_state_globals_fupd (K x) (pan_itreeSem_ext s t f)) = bstate_globals_fupd (K x) s /\
     pan_itreeSem_bst (pan_state_memory_fupd (K m) (pan_itreeSem_ext s t f)) = bstate_memory_fupd (K m) s /\
     pan_itreeSem_bst (pan_empty_locals (pan_itreeSem_ext s k ffi)) = pan_itreeSem_empty_locals s /\
     pan_itreeSem_bst (pan_dec_clock (pan_itreeSem_ext s k ffi)) = s`,
  RW[pan_itreeSem_bst_def; pan_itreeSem_ext_def; bstate_component_equality; empty_locals_defs;
     pan_dec_clock_def]);;
let _ = cake_add_simps [bst_ext_id];;

let eval_eq = prove
 (`!(s:(A)bstate) (s':(A,B)pan_state) e.
     (s = pan_itreeSem_bst s' ==> pan_itreeSem_eval s e = pan_eval s' e) /\
     (!t f. s' = pan_itreeSem_ext s t f ==> pan_itreeSem_eval s e = pan_eval s' e)`,
  RW[eval_bst; eval_ext]);;
let _ = cake_add_simps [eval_eq];;

(* ------------------------------------------------------------------------- *)
(* mrec h_prog: results and loops.                                           *)
(* ------------------------------------------------------------------------- *)

(* HOL4: Overload mrec_sem = \p s. mrec h_prog (h_prog (p,s)) (written out) *)

let mrec_Ret_INR = prove
 (`!p (s:(A)bstate) x. mrec h_prog (h_prog (p,s)) = itree_Ret x ==> ?y. x = INR y`,
  GEN_TAC THEN QCASES_ON "p" THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[h_prog_simple_defs; h_prog_call_def; h_prog_deccall_def;
    h_prog_dec_def; h_prog_seq_def; h_prog_cond_def; h_prog_ext_call_def;
    h_prog_sh_mem_load_def; h_prog_sh_mem_store_def; h_prog_while_def] THEN
  TRY(GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [itree_iter_thm]) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE] THEN
  REPEAT(TOP_CASE_TAC THEN SIMP[]) THEN SIMP[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MESON_TAC[]);;

(* HOL4 proves mrec_While by a case split on mrec h_prog (h_prog (p,s)) and *)
(* mrec_Ret_INR; here mrec_bind gives the bind directly                     *)

let mrec_While = prove(CASE_TERM
 `!e (p:(A)panLang_prog) (s:(A)bstate).
   mrec h_prog (h_prog (While e p,s)) =
   match pan_itreeSem_eval s e with
     SOME (pan_Val (Word w)) ->
       if w = word 0 then itree_Ret (INR (NONE,s))
       else
         Tau (itree_bind (mrec h_prog (h_prog (p,s)))
                (\a. match a with
                       INL l -> itree_Ret (INR (SOME pan_Error,s))
                     | INR (res,s') ->
                         match res with
                           NONE -> Tau (mrec h_prog (h_prog (While e p,s')))
                         | SOME pan_Break -> itree_Ret (INR (NONE,s'))
                         | SOME pan_Continue ->
                             Tau (mrec h_prog (h_prog (While e p,s')))
                         | _ -> itree_Ret (INR (res,s'))))
   | _ -> itree_Ret (INR (SOME pan_Error,s))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [h_prog_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [h_prog_while_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [itree_iter_thm] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE] THEN
  REPEAT(TOP_CASE_TAC THEN SIMP[]) THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  REWRITE_TAC[FORALL_SUM; FORALL_PAIR_THM; FORALL_OPTION_THM; o_THM] THEN
  SIMP[] THEN REPEAT STRIP_TAC THEN REPEAT(CASE_TAC THEN SIMP[]) THEN
  REWRITE_TAC[h_prog_def; h_prog_while_def]);;

(* ------------------------------------------------------------------------- *)
(* Taus before a result or an event (HOL4: move to itreeTauTheory).          *)
(* ------------------------------------------------------------------------- *)

let FUNPOW_Ret_strip = prove
 (`!n (t:(A,E,R)itree) m x.
     ITER n Tau t = ITER m Tau (itree_Ret x)
     ==> n <= m /\ t = ITER (m - n) Tau (itree_Ret x)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[ITER; LE_0; SUB_0] THEN
  QCASES_ON "m" THEN SIMP[ITER; LE_SUC; SUB_SUC] THEN ASM_MESON_TAC[]);;

let FUNPOW_Ret_simp = prove
 (`!n (t:(A,E,R)itree) m x.
     ITER n Tau t = ITER m Tau (itree_Ret x) <=>
     n <= m /\ t = ITER (m - n) Tau (itree_Ret x)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[FUNPOW_Ret_strip] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ITER_ADD] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let FUNPOW_Tau_Ret_eq_simp = prove
 (`!n (x:R) m y.
     ITER n Tau (itree_Ret x:(A,E,R)itree) = ITER m Tau (itree_Ret y) <=>
     n = m /\ x = y`,
  MESON_TAC[FUNPOW_Tau_Ret_eq]);;
let _ = cake_add_simps [FUNPOW_Tau_Ret_eq_simp];;

(* HOL4 proves bind_FUNPOW_Ret with strip_tau; here by induction on n       *)

let bind_FUNPOW_Ret = prove
 (`!n (ht:(A,E,R)itree) (k:R->(A,E,B)itree) x.
     itree_bind ht k = ITER n Tau (itree_Ret x)
     ==> ?r n' m. ht = ITER n' Tau (itree_Ret r) /\
                  k r = ITER m Tau (itree_Ret x) /\ n = n' + m`,
  INDUCT_TAC THEN GEN_TAC THEN QCASES_ON "ht" THEN SIMP[ITER] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[ITER; ADD_CLAUSES]);;

let FUNPOW_Ret_simp2 = prove
 (`!n (x:R) r.
     (ITER n Tau (itree_Ret x:(A,E,R)itree) = itree_Ret r <=> n = 0 /\ x = r) /\
     (itree_Ret r = ITER n Tau (itree_Ret x:(A,E,R)itree) <=> n = 0 /\ r = x)`,
  INDUCT_TAC THEN SIMP[ITER; NOT_SUC]);;
let _ = cake_add_simps [FUNPOW_Ret_simp2];;

let FUNPOW_Tau_Vis_eq_simp = prove
 (`!n (e:E) (k:A->(A,E,R)itree) m e' k'.
     ITER n Tau (Vis e k) = ITER m Tau (Vis e' k') <=> n = m /\ e = e' /\ k = k'`,
  MESON_TAC[FUNPOW_Tau_Vis_eq]);;
let _ = cake_add_simps [FUNPOW_Tau_Vis_eq_simp];;

let FUNPOW_Vis_strip = prove
 (`!n (t:(A,E,R)itree) m e k.
     ITER n Tau t = ITER m Tau (Vis e k)
     ==> n <= m /\ t = ITER (m - n) Tau (Vis e k)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[ITER; LE_0; SUB_0] THEN
  QCASES_ON "m" THEN SIMP[ITER; LE_SUC; SUB_SUC] THEN ASM_MESON_TAC[]);;

let FUNPOW_Vis_simp = prove
 (`!n (t:(A,E,R)itree) m e k.
     ITER n Tau t = ITER m Tau (Vis e k) <=>
     n <= m /\ t = ITER (m - n) Tau (Vis e k)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[FUNPOW_Vis_strip] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ITER_ADD] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* HOL4 proves bind_FUNPOW_Vis with strip_tau; here by induction on n       *)

let bind_FUNPOW_Vis = prove
 (`!n (ht:(A,E,R)itree) (t:R->(A,E,B)itree) e k.
     itree_bind ht t = ITER n Tau (Vis e k)
     ==> (?g. ht = ITER n Tau (Vis e g) /\ k = (\x. itree_bind (g x) t)) \/
         (?x m. ht = ITER m Tau (itree_Ret x) /\
                t x = ITER (n - m) Tau (Vis e k) /\ m <= n)`,
  INDUCT_TAC THEN GEN_TAC THEN QCASES_ON "ht" THEN SIMP[ITER] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:(A,E,R)itree`; `t:R->(A,E,B)itree`; `e:E`;
                                `k:A->(A,E,B)itree`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [DISJ1_TAC THEN ASM_MESON_TAC[];
    DISJ2_TAC THEN MAP_EVERY QEXISTS_TAC ["x"; "SUC m"] THEN
    ASM_REWRITE_TAC[ITER; SUB_SUC; LE_SUC]]);;

let itree_bind_cases = prove
 (`!(t:(A,E,R)itree) (k:R->(A,E,B)itree) t'.
     itree_bind t k = t' <=>
     (?r n. t = ITER n Tau (itree_Ret r) /\ t' = ITER n Tau (k r)) \/
     (?a g n. t = ITER n Tau (Vis a g) /\
              t' = ITER n Tau (Vis a (\x. itree_bind (g x) k))) \/
     (t = itree_spin /\ t' = itree_spin)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_CASES_TAC `?ht:(A,E,R)itree. strip_tau t ht` THENL
     [FIRST_X_ASSUM(X_CHOOSE_TAC `ht:(A,E,R)itree`) THEN
      FIRST_ASSUM(X_CHOOSE_TAC `n:num` o MATCH_MP strip_tau_FUNPOW) THEN
      UNDISCH_TAC `strip_tau (t:(A,E,R)itree) ht` THEN
      ASM_REWRITE_TAC[FUNPOW_Tau_bind] THEN QCASES_ON "ht" THEN
      SIMP[] THEN MESON_TAC[];
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP strip_tau_spin o
                  REWRITE_RULE[NOT_EXISTS_THM]) THEN
      ASM_REWRITE_TAC[spin_bind]];
    STRIP_TAC THEN ASM_REWRITE_TAC[FUNPOW_Tau_bind; spin_bind] THEN SIMP[]]);;

(* ------------------------------------------------------------------------- *)
(* Simplification rules for mrec h_prog (HOL4: simp rules).  They come      *)
(* before mrec_FUNPOW_Ret_INR here (HOL4 has them after Skip_loop_spin):    *)
(* the proof of mrec_FUNPOW_Ret_INR below uses them.                         *)
(* ------------------------------------------------------------------------- *)

(* the tactic of the rules with a recursive call: unfold, push mrec through *)
(* the binds, and compare the continuations pointwise                       *)

let PITRAUX_MREC_TAC defs =
  REPEAT GEN_TAC THEN REWRITE_TAC(h_prog_def :: defs) THEN SIMP[] THEN
  REPEAT(TOP_CASE_TAC THEN SIMP[]) THEN
  TRY(AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
      REWRITE_TAC[FORALL_SUM; FORALL_PAIR_THM; FORALL_OPTION_THM; o_THM] THEN
      SIMP[o_DEF] THEN REPEAT STRIP_TAC THEN REPEAT(CASE_TAC THEN SIMP[o_DEF]));;

let mrec_Seq = prove(CASE_TERM
 `!(p:(A)panLang_prog) q (s:(A)bstate).
    mrec h_prog (h_prog (panLang_Seq p q,s)) =
    Tau (itree_bind (mrec h_prog (h_prog (p,s)))
           (\a. match a with
                  INL l -> itree_Ret (INR (SOME pan_Error,s))
                | INR (NONE,s') ->
                    Tau (itree_bind (mrec h_prog (h_prog (q,s')))
                           (\a. itree_Ret (INR (match a with
                                  INL v -> (SOME pan_Error,s)
                                | INR (res,s') -> (res,s')))))
                | INR (SOME res,s') -> itree_Ret (INR (SOME res,s'))))`,
  PITRAUX_MREC_TAC [h_prog_seq_def]);;

let mrec_Dec = prove(CASE_TERM
 `!x sh e (p:(A)panLang_prog) (s:(A)bstate).
    mrec h_prog (h_prog (Dec x sh e p,s)) =
    match pan_itreeSem_eval s e with
      SOME v ->
        if shape_of v = sh
        then Tau (itree_bind
               (mrec h_prog (h_prog (p,bstate_locals_fupd
                                        (K (bstate_locals s |+ (x,v))) s)))
               (\a. itree_Ret (INR (match a with
                      INL l -> (SOME pan_Error,s)
                    | INR (res,s') ->
                        (res,bstate_locals_fupd
                               (K (pan_res_var (bstate_locals s')
                                     (x,FLOOKUP (bstate_locals s) x))) s')))))
        else itree_Ret (INR (SOME pan_Error,s))
    | _ -> itree_Ret (INR (SOME pan_Error,s))`,
  PITRAUX_MREC_TAC [h_prog_dec_def] THEN ASM_MESON_TAC[]);;

(* HOL4's bound variable v of SOME v (a value) is value here: the program's *)
(* expression is also called v                                              *)

let mrec_Assign = prove(CASE_TERM
 `!vk x v (s:(A)bstate).
    mrec h_prog (h_prog (panLang_Assign vk x v,s)) =
    match pan_itreeSem_eval s v with
      SOME value ->
        itree_Ret (INR (if pan_itreeSem_is_valid_value s vk x value
                        then (NONE,pan_itreeSem_set_kvar vk x value s)
                        else (SOME pan_Error,s)))
    | _ -> itree_Ret (INR (SOME pan_Error,s))`,
  PITRAUX_MREC_TAC [h_prog_assign_def]);;

let mrec_Primitive = prove(CASE_TERM
 `!vname pop es (s:(A)bstate).
    mrec h_prog (h_prog (Primitive vname pop es,s)) =
    itree_Ret (INR (match OPT_MMAP (pan_itreeSem_eval s) es with
                      SOME vs ->
                        (match pan_primop pop vs with
                           SOME value ->
                             if pan_itreeSem_is_valid_value s panLang_Local vname value
                             then (NONE,pan_itreeSem_set_var vname value s)
                             else (SOME pan_Error,s)
                         | NONE -> (SOME pan_Error,s))
                    | _ -> (SOME pan_Error,s)))`,
  PITRAUX_MREC_TAC [h_prog_primitive_def]);;

let mrec_If = prove(CASE_TERM
 `!e (p:(A)panLang_prog) q (s:(A)bstate).
    mrec h_prog (h_prog (panLang_If e p q,s)) =
    match pan_itreeSem_eval s e with
      SOME (pan_Val (Word v)) ->
        Tau (itree_bind (mrec h_prog (h_prog ((if ~(v = word 0) then p else q),s)))
               (\a. itree_Ret (INR (match a with
                      INL l -> (SOME pan_Error,s)
                    | INR (res,s') -> (res,s')))))
    | _ -> itree_Ret (INR (SOME pan_Error,s))`,
  PITRAUX_MREC_TAC [h_prog_cond_def]);;

let mrec_Store = prove(CASE_TERM
 `!dst src (s:(A)bstate).
    mrec h_prog (h_prog (panLang_Store dst src,s)) =
    itree_Ret (INR (match (pan_itreeSem_eval s dst,pan_itreeSem_eval s src) with
      (NONE,v3) -> (SOME pan_Error,s)
    | (SOME (pan_Val (Word ad)),NONE) -> (SOME pan_Error,s)
    | (SOME (pan_Val (Word ad)),SOME v) ->
        (match mem_stores ad (flatten v) (bstate_memaddrs s) (bstate_memory s) with
           NONE -> (SOME pan_Error,s)
         | SOME m -> (NONE,bstate_memory_fupd (K m) s))
    | _ -> (SOME pan_Error,s)))`,
  PITRAUX_MREC_TAC [h_prog_store_def]);;

let mrec_StoreByte = prove(CASE_TERM
 `!dst src (s:(A)bstate).
    mrec h_prog (h_prog (StoreByte dst src,s)) =
    itree_Ret (INR (match (pan_itreeSem_eval s dst,pan_itreeSem_eval s src) with
      (NONE,v3) -> (SOME pan_Error,s)
    | (SOME (pan_Val (Word ad)),NONE) -> (SOME pan_Error,s)
    | (SOME (pan_Val (Word ad)),SOME (pan_Val (Word v))) ->
        (match pan_mem_store_byte (bstate_memory s) (bstate_memaddrs s) (bstate_be s)
                 ad (word_zx v) with
           NONE -> (SOME pan_Error,s)
         | SOME m -> (NONE,bstate_memory_fupd (K m) s))
    | _ -> (SOME pan_Error,s)))`,
  PITRAUX_MREC_TAC [h_prog_store_byte_def]);;

let mrec_Store32 = prove(CASE_TERM
 `!dst src (s:(A)bstate).
    mrec h_prog (h_prog (panLang_Store32 dst src,s)) =
    itree_Ret (INR (match (pan_itreeSem_eval s dst,pan_itreeSem_eval s src) with
      (NONE,v3) -> (SOME pan_Error,s)
    | (SOME (pan_Val (Word ad)),NONE) -> (SOME pan_Error,s)
    | (SOME (pan_Val (Word ad)),SOME (pan_Val (Word v))) ->
        (match pan_mem_store_32 (bstate_memory s) (bstate_memaddrs s) (bstate_be s)
                 ad (word_zx v) with
           NONE -> (SOME pan_Error,s)
         | SOME m -> (NONE,bstate_memory_fupd (K m) s))
    | _ -> (SOME pan_Error,s)))`,
  PITRAUX_MREC_TAC [h_prog_store_32_def]);;

(* HOL4's simp knows LENGTH (word_to_bytes w be) (byteTheory); a local copy *)

let PITRAUX_LENGTH_word_to_bytes = prove
 (`!(w:A word) be. LENGTH (word_to_bytes w be) = dimindex(:A) DIV 8`,
  REWRITE_TAC[word_to_bytes_def; WORDSAUX_LENGTH_word_to_bytes_aux]);;
let _ = cake_add_simps [PITRAUX_LENGTH_word_to_bytes];;

let mrec_ShMemLoad = prove(CASE_TERM
 `!op vk v addr (s:(A)bstate).
    mrec h_prog (h_prog (ShMemLoad op vk v addr,s)) =
    match (pan_itreeSem_eval s addr,pan_itreeSem_lookup_kvar vk v s) with
      (SOME (pan_Val (Word ad)),SOME (pan_Val _)) ->
        (if nb_op op = 0 then
           (if ad IN bstate_sh_memaddrs s then
              Vis (SharedMem MappedRead,[word 0],word_to_bytes ad F)
                (Tau o mrec h_prog o
                   (\res. itree_Ret (INR
                      (match res with
                         INL (INL outcome) ->
                           (SOME (pan_FinalFFI (Final_event (SharedMem MappedRead)
                                    [word 0] (word_to_bytes ad F) outcome)),
                            pan_itreeSem_empty_locals s)
                       | INL (INR new_bytes) ->
                           if LENGTH new_bytes = dimindex(:A) DIV 8 then
                             (NONE,pan_itreeSem_set_kvar vk v
                                     (pan_Val (Word (word_of_bytes F (word 0) new_bytes))) s)
                           else
                             (SOME (pan_FinalFFI (Final_event (SharedMem MappedRead)
                                      [word 0] (word_to_bytes ad F) FFI_failed)),
                              pan_itreeSem_empty_locals s)
                       | INR _ -> (SOME pan_Error,s)))))
            else itree_Ret (INR (SOME pan_Error,s)))
         else if byte_align ad IN bstate_sh_memaddrs s then
           Vis (SharedMem MappedRead,[word (nb_op op)],word_to_bytes ad F)
             (Tau o mrec h_prog o
                (\res. itree_Ret (INR
                   (match res with
                      INL (INL outcome) ->
                        (SOME (pan_FinalFFI (Final_event (SharedMem MappedRead)
                                 [word (nb_op op)] (word_to_bytes ad F) outcome)),
                         pan_itreeSem_empty_locals s)
                    | INL (INR new_bytes) ->
                        if LENGTH new_bytes = dimindex(:A) DIV 8 then
                          (NONE,pan_itreeSem_set_kvar vk v
                                  (pan_Val (Word (word_of_bytes F (word 0) new_bytes))) s)
                        else
                          (SOME (pan_FinalFFI (Final_event (SharedMem MappedRead)
                                   [word (nb_op op)] (word_to_bytes ad F) FFI_failed)),
                           pan_itreeSem_empty_locals s)
                    | INR _ -> (SOME pan_Error,s)))))
         else itree_Ret (INR (SOME pan_Error,s)))
    | _ -> itree_Ret (INR (SOME pan_Error,s))`,
  PITRAUX_MREC_TAC [h_prog_sh_mem_load_def]);;

let mrec_ShMemStore = prove(CASE_TERM
 `!op addr e (s:(A)bstate).
    mrec h_prog (h_prog (ShMemStore op addr e,s)) =
    match (pan_itreeSem_eval s addr,pan_itreeSem_eval s e) with
      (SOME (pan_Val (Word ad)),SOME (pan_Val (Word w))) ->
        if nb_op op = 0 then
          if ad IN bstate_sh_memaddrs s then
            Vis (SharedMem MappedWrite,[word 0],
                 APPEND (word_to_bytes w F) (word_to_bytes ad F))
              (Tau o mrec h_prog o
                 (\res. itree_Ret (INR
                    (match res with
                       INL (INL outcome) ->
                         (SOME (pan_FinalFFI (Final_event (SharedMem MappedWrite) [word 0]
                                  (APPEND (word_to_bytes w F) (word_to_bytes ad F))
                                  outcome)),s)
                     | INL (INR new_bytes) ->
                         if LENGTH new_bytes = 2 * (dimindex(:A) DIV 8) then (NONE,s)
                         else
                           (SOME (pan_FinalFFI (Final_event (SharedMem MappedWrite) [word 0]
                                    (APPEND (word_to_bytes w F) (word_to_bytes ad F))
                                    FFI_failed)),s)
                     | INR _ -> (SOME pan_Error,s)))))
          else itree_Ret (INR (SOME pan_Error,s))
        else if byte_align ad IN bstate_sh_memaddrs s then
          Vis (SharedMem MappedWrite,[word (nb_op op)],
               APPEND (TAKE (nb_op op) (word_to_bytes w F)) (word_to_bytes ad F))
            (Tau o mrec h_prog o
               (\res. itree_Ret (INR
                  (match res with
                     INL (INL outcome) ->
                       (SOME (pan_FinalFFI (Final_event (SharedMem MappedWrite)
                                [word (nb_op op)]
                                (APPEND (TAKE (nb_op op) (word_to_bytes w F))
                                        (word_to_bytes ad F)) outcome)),s)
                   | INL (INR new_bytes) ->
                       if LENGTH new_bytes =
                          LENGTH (TAKE (nb_op op) (word_to_bytes w F)) +
                          dimindex(:A) DIV 8
                       then (NONE,s)
                       else
                         (SOME (pan_FinalFFI (Final_event (SharedMem MappedWrite)
                                  [word (nb_op op)]
                                  (APPEND (TAKE (nb_op op) (word_to_bytes w F))
                                          (word_to_bytes ad F)) FFI_failed)),s)
                   | INR v1 -> (SOME pan_Error,s)))))
        else itree_Ret (INR (SOME pan_Error,s))
    | _ -> itree_Ret (INR (SOME pan_Error,s))`,
  PITRAUX_MREC_TAC [h_prog_sh_mem_store_def; MULT_2]);;

let mrec_prog_triv = prove
 (`!(s:(A)bstate) x y.
     mrec h_prog (h_prog (panLang_Skip,s)) = itree_Ret (INR (NONE,s)) /\
     mrec h_prog (h_prog (panLang_Break,s)) = itree_Ret (INR (SOME pan_Break,s)) /\
     mrec h_prog (h_prog (panLang_Tick,s)) = itree_Ret (INR (NONE,s)) /\
     mrec h_prog (h_prog (Annot x y,s)) = itree_Ret (INR (NONE,s)) /\
     mrec h_prog (h_prog (panLang_Continue,s)) =
       itree_Ret (INR (SOME pan_Continue,s))`,
  SIMP[h_prog_def]);;

let mrec_Return = prove(CASE_TERM
 `!e (s:(A)bstate).
    mrec h_prog (h_prog (panLang_Return e,s)) =
    itree_Ret (INR (match pan_itreeSem_eval s e with
                      NONE -> (SOME pan_Error,s)
                    | SOME v ->
                        if size_of_sh_with_ctxt (bstate_structs s) (shape_of v) <= 32
                        then (SOME (pan_Return v),pan_itreeSem_empty_locals s)
                        else (SOME pan_Error,s)))`,
  PITRAUX_MREC_TAC [h_prog_return_def]);;

let mrec_Raise = prove(CASE_TERM
 `!eid e (s:(A)bstate).
    mrec h_prog (h_prog (panLang_Raise eid e,s)) =
    itree_Ret (INR (match (FLOOKUP (bstate_eshapes s) eid,pan_itreeSem_eval s e) with
                      (SOME sh,SOME v) ->
                        if shape_of v = sh /\
                           size_of_sh_with_ctxt (bstate_structs s) (shape_of v) <= 32
                        then (SOME (pan_Exception eid v),pan_itreeSem_empty_locals s)
                        else (SOME pan_Error,s)
                    | _ -> (SOME pan_Error,s)))`,
  PITRAUX_MREC_TAC [h_prog_raise_def]);;

let mrec_prog_simps = end_itlist CONJ
  [mrec_prog_triv; mrec_Return; mrec_Raise; mrec_Dec; mrec_Assign;
   mrec_Primitive; mrec_Store; mrec_Store32; mrec_StoreByte];;

(* HOL4's statements of mrec_Call and mrec_DecCall have one more, redundant *)
(* row  | _ => Ret (INR (SOME Error,s))  after SOME (q,r,rsh); left out     *)

let mrec_Call = prove(CASE_TERM
 `!typ fname aexps (s:(A)bstate).
    mrec h_prog (h_prog (panLang_Call typ fname aexps,s)) =
    match OPT_MMAP (pan_itreeSem_eval s) aexps with
      NONE -> itree_Ret (INR (SOME pan_Error,s))
    | SOME args ->
        match pan_lookup_code (bstate_code s) fname args with
          NONE -> itree_Ret (INR (SOME pan_Error,s))
        | SOME (q,r,rsh) ->
            Tau (itree_bind (mrec h_prog (h_prog (q,bstate_locals_fupd (K r) s)))
                   (mrec h_prog o h_handle_call_ret typ rsh s))`,
  PITRAUX_MREC_TAC [h_prog_call_def]);;

let mrec_DecCall = prove(CASE_TERM
 `!rt sh fname aexps (prog:(A)panLang_prog) (s:(A)bstate).
    mrec h_prog (h_prog (DecCall rt sh fname aexps prog,s)) =
    match OPT_MMAP (pan_itreeSem_eval s) aexps with
      NONE -> itree_Ret (INR (SOME pan_Error,s))
    | SOME args ->
        match pan_lookup_code (bstate_code s) fname args with
          NONE -> itree_Ret (INR (SOME pan_Error,s))
        | SOME (q,r,rsh) ->
            Tau (itree_bind (mrec h_prog (h_prog (q,bstate_locals_fupd (K r) s)))
                   (mrec h_prog o h_handle_deccall_ret rt sh prog rsh s))`,
  PITRAUX_MREC_TAC [h_prog_deccall_def]);;

(* HOL4's pattern variable res of INR (res,s') (a result) is r here: the     *)
(* argument (an answer) is also called res                                   *)

let mrec_h_handle_call_ret_lemma = prove(CASE_TERM
 `!ct rsh (s:(A)bstate) res.
   mrec h_prog (h_handle_call_ret ct rsh s res) =
   match res with
     INR (NONE,s') -> itree_Ret (INR (SOME pan_Error,s'))
   | INR (SOME pan_Break,s') -> itree_Ret (INR (SOME pan_Error,s'))
   | INR (SOME pan_Continue,s') -> itree_Ret (INR (SOME pan_Error,s'))
   | INR (SOME (pan_Exception eid exn),s') ->
       (match ct with
          SOME (_,SOME (eid',evar,p)) ->
            (if eid' = eid
             then
               (match FLOOKUP (bstate_eshapes s) eid with
                  SOME sh ->
                    (if shape_of exn = sh /\
                        pan_itreeSem_is_valid_value s panLang_Local evar exn
                     then Tau (itree_bind
                            (mrec h_prog (h_prog (p,pan_itreeSem_set_var evar exn
                               (bstate_locals_fupd (K (bstate_locals s)) s'))))
                            (mrec h_prog o (\a. itree_Ret (INR
                               (match a with
                                  INL _ -> (SOME pan_Error,s')
                                | INR (q,t) -> (q,t))))))
                     else itree_Ret (INR (SOME pan_Error,s')))
                | NONE -> itree_Ret (INR (SOME pan_Error,s')))
             else itree_Ret (INR (SOME (pan_Exception eid exn),
                                  pan_itreeSem_empty_locals s')))
        | _ -> itree_Ret (INR (SOME (pan_Exception eid exn),
                               pan_itreeSem_empty_locals s')))
   | INR (SOME (pan_Return retv),s') ->
       (if ~(shape_of retv = rsh) then itree_Ret (INR (SOME pan_Error,s')) else
        (match ct with
           NONE -> itree_Ret (INR (SOME (pan_Return retv),pan_itreeSem_empty_locals s'))
         | SOME (NONE,_) ->
             itree_Ret (INR (NONE,bstate_locals_fupd (K (bstate_locals s)) s'))
         | SOME (SOME (rk,rt),_) ->
             if pan_itreeSem_is_valid_value s rk rt retv
             then itree_Ret (INR (NONE,pan_itreeSem_set_kvar rk rt retv
                                         (bstate_locals_fupd (K (bstate_locals s)) s')))
             else itree_Ret (INR (SOME pan_Error,s'))))
   | INR (r,s') -> itree_Ret (INR (r,pan_itreeSem_empty_locals s'))
   | INL _ -> itree_Ret (INR (SOME pan_Error,s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ONELINE h_handle_call_ret_def] THEN
  REPEAT(TOP_CASE_TAC THEN SIMP[]) THEN ASM_MESON_TAC[]);;

let mrec_h_handle_deccall_ret_lemma = prove(CASE_TERM
 `!rt sh (p:(A)panLang_prog) rsh (s:(A)bstate) res.
   mrec h_prog (h_handle_deccall_ret rt sh p rsh s res) =
   match res with
     INR (NONE,s') -> itree_Ret (INR (SOME pan_Error,s'))
   | INR (SOME pan_Break,s') -> itree_Ret (INR (SOME pan_Error,s'))
   | INR (SOME pan_Continue,s') -> itree_Ret (INR (SOME pan_Error,s'))
   | INR (SOME (pan_Return retv),s') ->
       (if shape_of retv = sh /\ shape_of retv = rsh then
          Tau (itree_bind
                 (mrec h_prog (h_prog (p,pan_itreeSem_set_var rt retv
                    (bstate_locals_fupd (K (bstate_locals s)) s'))))
                 (mrec h_prog o
                    (\a. itree_Ret (INR
                       (match a with
                          INL v -> (SOME pan_Error,s')
                        | INR (q,r') ->
                            (q,bstate_locals_fupd
                                 (K (pan_res_var (bstate_locals r')
                                       (rt,FLOOKUP (bstate_locals s) rt))) r'))))))
        else itree_Ret (INR (SOME pan_Error,s')))
   | INR (r,s') -> itree_Ret (INR (r,pan_itreeSem_empty_locals s'))
   | INL _ -> itree_Ret (INR (SOME pan_Error,s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ONELINE h_handle_deccall_ret_def] THEN
  REPEAT(TOP_CASE_TAC THEN SIMP[]) THEN ASM_MESON_TAC[]);;

let mrec_ExtCall = prove(CASE_TERM
 `!ffiname cptr clen aptr alen (s:(A)bstate).
    mrec h_prog (h_prog (panLang_ExtCall ffiname cptr clen aptr alen,s)) =
    match (pan_itreeSem_eval s cptr,pan_itreeSem_eval s clen,
           pan_itreeSem_eval s aptr,pan_itreeSem_eval s alen) with
      (SOME (pan_Val (Word c3)),SOME (pan_Val (Word c2)),
       SOME (pan_Val (Word c')),SOME (pan_Val (Word c))) ->
        (match read_bytearray c3 (val c2)
                 (pan_mem_load_byte (bstate_memory s) (bstate_memaddrs s) (bstate_be s))
         with
           SOME x' ->
             (match read_bytearray c' (val c)
                      (pan_mem_load_byte (bstate_memory s) (bstate_memaddrs s)
                                         (bstate_be s)) with
                SOME x ->
                  if ~(explode ffiname = "")
                  then
                    Vis (ExtCall ffiname,x',x)
                      (Tau o mrec h_prog o
                         (\res.
                            itree_Ret (INR
                              (match res with
                                 INL (INL outcome) ->
                                   (SOME (pan_FinalFFI (Final_event (ExtCall ffiname)
                                                          x' x outcome)),
                                    pan_itreeSem_empty_locals s)
                               | INL (INR new_bytes) ->
                                   if LENGTH new_bytes = LENGTH x then
                                     (NONE,bstate_memory_fupd
                                             (K (pan_write_bytearray c' new_bytes
                                                   (bstate_memory s) (bstate_memaddrs s)
                                                   (bstate_be s))) s)
                                   else
                                     (SOME (pan_FinalFFI (Final_event (ExtCall ffiname)
                                                            x' x FFI_failed)),
                                      pan_itreeSem_empty_locals s)
                               | INR _ -> (SOME pan_Error,s)))))
                  else itree_Ret (INR
                         (NONE,bstate_memory_fupd
                                 (K (pan_write_bytearray c' x (bstate_memory s)
                                       (bstate_memaddrs s) (bstate_be s))) s))
              | _ -> itree_Ret (INR (SOME pan_Error,s)))
         | _ -> itree_Ret (INR (SOME pan_Error,s)))
    | _ -> itree_Ret (INR (SOME pan_Error,s))`,
  PITRAUX_MREC_TAC [h_prog_ext_call_def]);;

let mrec_prog_nonrec = end_itlist CONJ
  [mrec_prog_simps; mrec_ShMemStore; mrec_ShMemLoad; mrec_Seq; mrec_Call;
   mrec_DecCall];;

(* ------------------------------------------------------------------------- *)
(* Results reached after Taus are INR; the loop While 1 Skip spins.          *)
(* ------------------------------------------------------------------------- *)

let PITRAUX_Tau_FUNPOW_Ret = prove
 (`!(t:(A,E,R)itree) n x.
     Tau t = ITER n Tau (itree_Ret x) <=>
     ?m. n = SUC m /\ t = ITER m Tau (itree_Ret x)`,
  GEN_TAC THEN INDUCT_TAC THEN SIMP[ITER; NOT_SUC; SUC_INJ]);;

let PITRAUX_bind_FUNPOW_Ret = prove
 (`!(ht:(A,E,R)itree) (k:R->(A,E,B)itree) n x.
     itree_bind ht k = ITER n Tau (itree_Ret x) <=>
     ?r n' m. ht = ITER n' Tau (itree_Ret r) /\
              k r = ITER m Tau (itree_Ret x) /\ n = n' + m`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[bind_FUNPOW_Ret] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FUNPOW_Tau_bind; itree_bind_thm; ITER_ADD]);;

(* HOL4 proves mrec_FUNPOW_Ret_INR by induction on n and on the program,   *)
(* unfolding the handlers; here by induction on n with the simp rules       *)
(* above (only the loop needs the induction hypothesis)                     *)

let mrec_FUNPOW_Ret_INR = prove
 (`!p (s:(A)bstate) n x.
     mrec h_prog (h_prog (p,s)) = ITER n Tau (itree_Ret x) ==> ?y. x = INR y`,
  SUBGOAL_THEN
   `!n p (s:(A)bstate) x.
      mrec h_prog (h_prog (p,s)) = ITER n Tau (itree_Ret x) ==> ?y. x = INR y`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  GEN_TAC THEN QCASES_ON "p" THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[mrec_prog_nonrec; mrec_If; mrec_ExtCall] THEN
  TRY(GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [mrec_While]) THEN
  REPEAT(TOP_CASE_TAC THEN SIMP[]) THEN REPEAT STRIP_TAC THEN
  GVS_ASM([PITRAUX_Tau_FUNPOW_Ret; PITRAUX_bind_FUNPOW_Ret; o_THM;
           mrec_h_handle_call_ret_lemma; mrec_h_handle_deccall_ret_lemma] @
          all_case_eqs()) THEN
  SIMP[] THEN ASM_MESON_TAC[ARITH_RULE `!a b. b <= SUC (a + b)`]);;

let PITRAUX_mrec_Skip_loop_unfold = prove
 (`!t:(A)bstate.
     mrec h_prog (h_prog (While (panLang_Const (word 1)) panLang_Skip,t)) =
     Tau (Tau (mrec h_prog (h_prog (While (panLang_Const (word 1)) panLang_Skip,t))))`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [mrec_While] THEN
  SIMP[pan_itreeSem_eval_def; WORD_NE_10; mrec_prog_triv]);;

let mrec_Skip_loop_spin = prove
 (`!s:(A)bstate.
     mrec h_prog (h_prog (While (panLang_Const (word 1)) panLang_Skip,s)) = itree_spin`,
  GEN_TAC THEN ONCE_REWRITE_TAC[itree_bisimulation] THEN
  QEXISTS_TAC
   "\\x y. y = itree_spin /\\
          ((?t. x = mrec h_prog (h_prog (While (panLang_Const (word 1)) panLang_Skip,
                                          t:(A)bstate))) \\/
           (?t. x = Tau (mrec h_prog (h_prog (While (panLang_Const (word 1))
                                                   panLang_Skip,t:(A)bstate)))))" THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRY(FIRST_X_ASSUM(fun th ->
        if fst(dest_const(fst(strip_comb(rhs(concl th))))) = "mrec"
        then ASSUME_TAC(ONCE_REWRITE_RULE[PITRAUX_mrec_Skip_loop_unfold] th)
        else failwith "unfold")) THEN
  FS[] THEN REWRITE_TAC[GSYM spin] THEN MESON_TAC[]);;

(* HOL4: Skip_loop_spin *)

let pan_itreeSem_Skip_loop_spin = prove
 (`!s:(A)bstate.
     itree_evaluate (While (panLang_Const (word 1)) panLang_Skip,s) = itree_spin`,
  GEN_TAC THEN
  REWRITE_TAC[itree_evaluate_def; mrec_Skip_loop_spin; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  MATCH_GOALSUB_ABBREV_TAC "itree_unfold uf itree_spin" THEN
  QBY "!u. uf (Tau u) = Tau' u" (EXPAND_TAC "uf" THEN SIMP[]) THEN
  QBY "itree_unfold uf itree_spin = Tau (itree_unfold uf itree_spin)"
    (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [spin] THEN
     GEN_REWRITE_TAC LAND_CONV [itree_unfold] THEN SIMP[]) THEN
  QPAT_X_ASSUM "itree_unfold uf itree_spin = _" (fun eq ->
    ONCE_REWRITE_TAC[itree_bisimulation] THEN
    QEXISTS_TAC "\\x y. x = itree_unfold uf itree_spin /\\ y = itree_spin" THEN
    REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[eq]) THEN FS[] THEN REWRITE_TAC[GSYM spin]));;

(* ------------------------------------------------------------------------- *)
(* Running the FFI oracle on a tree: ltree, comp_ffi, divergence.            *)
(* ------------------------------------------------------------------------- *)

(* HOL4's ltree leaves the answer and event types of its result open; here *)
(* its result is a ptree, as at every use (div_def and the theorems).      *)
(* HOL4's paired lambdas \(t,st). .. are \p. match p with (t,st) -> ..      *)

let ltree_def = cake_def
 `(ltree (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
         (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
             (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree):
     ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
      (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) =
   itree_iter
     (\p. match p with
            (t,st) ->
              match t with
                itree_Ret r -> itree_Ret (INR r)
              | Tau u -> itree_Ret (INL (u,st))
              | Vis (s,c,ws) g ->
                  (match FST fs s st c ws with
                     Oracle_return fs' ws' ->
                       if LENGTH ws = LENGTH ws'
                       then itree_Ret (INL (g (INL (INR ws')),fs'))
                       else itree_Ret (INL (g (INL (INL FFI_failed)),st))
                   | Oracle_final outcome ->
                       itree_Ret (INL (g (INL (INL outcome)),st))))
     (t,SND fs)`;;

let ltree_simps = prove(CASE_TERM
 `!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (r:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)
    (u:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree)
    s c ws
    (g:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
       ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
   ltree fs (itree_Ret r) = itree_Ret r /\
   ltree fs (Tau u) = Tau (ltree fs u) /\
   ltree fs (Vis (s,c,ws) g) =
     match FST fs s (SND fs) c ws with
       Oracle_return fs' ws' ->
         if LENGTH ws = LENGTH ws' then
           Tau (ltree (FST fs,fs') (g (INL (INR ws'))))
         else Tau (ltree fs (g (INL (INL FFI_failed))))
     | Oracle_final outcome -> Tau (ltree fs (g (INL (INL outcome))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ltree_def] THEN
  REPEAT CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [itree_iter_thm] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE] THEN
  SIMP[] THEN REPEAT(TOP_CASE_TAC THEN SIMP[FST; SND; PAIR]));;
let _ = cake_add_simps [ltree_simps];;

let comp_ffi_def = cake_def
 `comp_ffi (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
           (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
               (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) =
   WHILE
     (\p. match p with (t,st) -> match t with itree_Ret _ -> F | _ -> T)
     (\p. match p with
            (t,st) ->
              match t with
                itree_Ret _ -> (t,st)
              | Tau t -> (t,st)
              | Vis (s,c,ws) g ->
                  match FST fs s st c ws with
                    Oracle_return fs' ws' ->
                      if LENGTH ws = LENGTH ws' then (g (INL (INR ws')),fs')
                      else (g (INL (INL FFI_failed)),st)
                  | Oracle_final outcome -> (g (INL (INL outcome)),st))
     (t,SND fs)`;;

let comp_ffi_simps = prove(CASE_TERM
 `!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (r:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)
    (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree)
    s c ws
    (g:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
       ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
   comp_ffi fs (itree_Ret r) = (itree_Ret r,SND fs) /\
   comp_ffi fs (Tau t) = comp_ffi fs t /\
   comp_ffi fs (Vis (s,c,ws) g) =
     match FST fs s (SND fs) c ws with
       Oracle_return fs' ws' ->
         if LENGTH ws = LENGTH ws'
         then comp_ffi (FST fs,fs') (g (INL (INR ws')))
         else comp_ffi fs (g (INL (INL FFI_failed)))
     | Oracle_final outcome -> comp_ffi fs (g (INL (INL outcome)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[comp_ffi_def] THEN REPEAT CONJ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [WHILE] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE] THEN
  SIMP[] THEN REPEAT(TOP_CASE_TAC THEN SIMP[FST; SND; PAIR]));;
let _ = cake_add_simps [comp_ffi_simps];;

(* HOL4: div *)

let pan_itreeSem_div_def = cake_def
 `pan_itreeSem_div (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
                   (t:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                       (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) <=>
   !n r. ~(ltree fs t = ITER n Tau (itree_Ret r))`;;

let nondiv_eq_Ret = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (X:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
     ~pan_itreeSem_div fs X <=> ?n r. ltree fs X = ITER n Tau (itree_Ret r)`,
  REWRITE_TAC[pan_itreeSem_div_def] THEN MESON_TAC[]);;
let _ = cake_add_simps [nondiv_eq_Ret];;

let div_Tau = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (u:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
     pan_itreeSem_div fs (Tau u) <=> pan_itreeSem_div fs u`,
  REWRITE_TAC[pan_itreeSem_div_def; ltree_simps; PITRAUX_Tau_FUNPOW_Ret] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [div_Tau];;

let div_Ret = prove
 (`!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (r:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate).
     pan_itreeSem_div fs (itree_Ret r) <=> F`,
  REWRITE_TAC[pan_itreeSem_div_def; ltree_simps] THEN MESON_TAC[ITER]);;
let _ = cake_add_simps [div_Ret];;

(* ------------------------------------------------------------------------- *)
(* The I/O trace of a tree.                                                  *)
(* ------------------------------------------------------------------------- *)

(* HOL4's variable fst (an oracle state) is st here *)

let trace_prefix_def = cake_def
 `trace_prefix (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
               (th:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
                    (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree) =
   LFLATTEN (LUNFOLD
     (\p. match p with
            (st,t) ->
              match t with
                itree_Ret r -> NONE
              | Tau u -> SOME ((st,u),LNIL)
              | Vis (s,conf,ws) k ->
                  (match FST fs s st conf ws with
                     Oracle_return fs' ws' ->
                       if ~(LENGTH ws = LENGTH ws')
                       then SOME ((st,k (INL (INL FFI_failed))),LNIL)
                       else SOME ((fs',k (INL (INR ws'))),
                                  LCONS (IO_event s conf (ZIP ws ws')) LNIL)
                   | Oracle_final outcome ->
                       SOME ((st,k (INL (INL outcome))),LNIL)))
     (SND fs,th))`;;

let trace_prefix_simps = prove(CASE_TERM
 `!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
    (r:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)
    (u:((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree)
    s c ws
    (k:(ffi_outcome+byte list)+((A)pan_result)option#(A)bstate->
       ((ffi_outcome+byte list)+((A)pan_result)option#(A)bstate,ev,
        (ffi_outcome+byte list)+((A)pan_result)option#(A)bstate)itree).
   trace_prefix fs (itree_Ret r) = LNIL /\
   trace_prefix fs (Tau u) = trace_prefix fs u /\
   trace_prefix fs (Vis (s,c,ws) k) =
     match FST fs s (SND fs) c ws with
       Oracle_return fs' ws' ->
         if ~(LENGTH ws = LENGTH ws')
         then trace_prefix fs (k (INL (INL FFI_failed)))
         else LCONS (IO_event s c (ZIP ws ws'))
                    (trace_prefix (FST fs,fs') (k (INL (INR ws'))))
     | Oracle_final outcome -> trace_prefix fs (k (INL (INL outcome)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[trace_prefix_def] THEN REPEAT CONJ_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [LUNFOLD] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE] THEN
  SIMP[] THEN REPEAT(CASE_TAC THEN SIMP[FST; SND; PAIR; LFLATTEN_THM]));;
let _ = cake_add_simps [trace_prefix_simps];;

let trace_prefix0_def = cake_def
 `trace_prefix0 (fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B)
                (th:(ffi_outcome+byte list,ev,R)itree) =
   LFLATTEN (LUNFOLD
     (\p. match p with
            (st,t) ->
              match t with
                itree_Ret r -> NONE
              | Tau u -> SOME ((st,u),LNIL)
              | Vis (s,conf,ws) k ->
                  (match FST fs s st conf ws with
                     Oracle_return fs' ws' ->
                       if ~(LENGTH ws = LENGTH ws')
                       then SOME ((st,k (INL FFI_failed)),LNIL)
                       else SOME ((fs',k (INR ws')),
                                  LCONS (IO_event s conf (ZIP ws ws')) LNIL)
                   | Oracle_final outcome ->
                       SOME ((st,k (INL outcome)),LNIL)))
     (SND fs,th))`;;

let trace_prefix0_simps = prove(CASE_TERM
 `!(fs:(ffiname->B->byte list->byte list->(B)oracle_result)#B) (r:R)
    (u:(ffi_outcome+byte list,ev,R)itree) s c ws
    (k:ffi_outcome+byte list->(ffi_outcome+byte list,ev,R)itree).
   trace_prefix0 fs (itree_Ret r) = LNIL /\
   trace_prefix0 fs (Tau u) = trace_prefix0 fs u /\
   trace_prefix0 fs (Vis (s,c,ws) k) =
     match FST fs s (SND fs) c ws with
       Oracle_return fs' ws' ->
         if ~(LENGTH ws = LENGTH ws')
         then trace_prefix0 fs (k (INL FFI_failed))
         else LCONS (IO_event s c (ZIP ws ws'))
                    (trace_prefix0 (FST fs,fs') (k (INR ws')))
     | Oracle_final outcome -> trace_prefix0 fs (k (INL outcome))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[trace_prefix0_def] THEN REPEAT CONJ_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [LUNFOLD] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[pair_CASE] THEN
  SIMP[] THEN REPEAT(CASE_TAC THEN SIMP[FST; SND; PAIR; LFLATTEN_THM]));;
let _ = cake_add_simps [trace_prefix0_simps];;
