(* ========================================================================= *)
(* bviSem: port of HOL4 compiler/backend/semantics/bviSemScript.sml         *)
(* (CakeML v3479).  The formal semantics of BVI.                             *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's Overload num_stubs = bvl_num_stubs is not used in this file.     *)
(* - A HOL4 record literal that leaves fields out is an update chain on ARB *)
(*   (HOL4's parser builds f1_fupd (K v1) (... ARB)): bvi_to_bvl.            *)
(* - HOL4 r with <| f1 := x; f2 := y |> is f1_fupd (K x) (f2_fupd (K y) r);  *)
(*   word8 is byte, word64 is int64, num_map is A spt.                       *)
(* - Lemmas named CLOSSEMAUX_ are helpers of the unit (not HOL4 names).     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/sptree.ml";;
needs "hol4/lprefix_lub.ml";;
needs "semantics/ffi/ffi.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* exception or multi-value return *)
let exn_or_ret_INDUCT,exn_or_ret_RECURSION = cake_type
  "exn_or_ret = Exn bvl_v | Ret (bvl_v list)";;

new_type_abbrev("bvi_result",`:(bvl_v list,exn_or_ret)result`);;

let bvi_state_INFO = cake_record "bvi_state"
  ["refs","(num,(bvl_v)bvl_ref)fmap";
   "clock","num";
   "global","num option";
   "compile","C -> (num # num # bvi_exp) list -> (byte list # int64 list # C) option";
   "compile_oracle","num -> C # (num # num # bvi_exp) list";
   "code","(num # bvi_exp) spt";
   "ffi","(FFI)ffi_state"];;

let bvi_state_component_equality = bvi_state_INFO.ri_component_equality;;

let bvi_dec_clock_def = cake_def
  `bvi_dec_clock x (s:(C,FFI)bvi_state) =
     bvi_state_clock_fupd (K (bvi_state_clock s - x)) s`;;

(* HOL4 [local] *)
let bvi_LESS_EQ_dec_clock = prove
 (`!(r:(C,FFI)bvi_state) x (s:(C,FFI)bvi_state).
     bvi_state_clock r <= bvi_state_clock (bvi_dec_clock x s)
     ==> bvi_state_clock r <= bvi_state_clock s`,
  REWRITE_TAC[bvi_dec_clock_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
  ARITH_TAC);;

let bvi_to_bvl_def = cake_def
  `bvi_to_bvl (s:(C,FFI)bvi_state) =
     bvl_state_refs_fupd (K (bvi_state_refs s))
       (bvl_state_clock_fupd (K (bvi_state_clock s))
         (bvl_state_code_fupd (K (sptree_map (K (ARB:num # bvl_exp)) (bvi_state_code s)))
           (bvl_state_ffi_fupd (K (bvi_state_ffi s)) (ARB:(C,FFI)bvl_state))))`;;

let bvl_to_bvi_def = cake_def
  `bvl_to_bvi (s:(C,FFI)bvl_state) (t:(C,FFI)bvi_state) =
     bvi_state_refs_fupd (K (bvl_state_refs s))
       (bvi_state_clock_fupd (K (bvl_state_clock s))
         (bvi_state_ffi_fupd (K (bvl_state_ffi s)) t))`;;

(* HOL4: refs'<|ptr |-> x|> is refs' |+ (ptr,x); l ++ [c'] ++ r is         *)
(* APPEND (APPEND l [c']) r                                                  *)

let bvi_finalise_cons_def = sem1aux_def_wf
  `MEASURE (\p:bvl_v # (num,(bvl_v)bvl_ref)fmap. CARD (FDOM (SND p)))`
  (REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
   RVEQ_TAC THEN REWRITE_TAC[measure_THM; SND; FDOM_DOMSUB] THEN
   POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
   REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THEN
   REWRITE_TAC[option_DISTINCT] THEN DISCH_THEN(K ALL_TAC) THEN
   ASM_SIMP_TAC[CARD_DELETE; FDOM_FINITE] THEN
   MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> n - 1 < n`) THEN
   ASM_SIMP_TAC[CARD_EQ_0; FDOM_FINITE] THEN ASM SET_TAC[])
  `(bvi_finalise_cons (bvl_RefPtr b ptr) refs =
      match FLOOKUP refs ptr with
        SOME (MutBlock tag finalised l c r) ->
          if ~finalised then
            (match bvi_finalise_cons c (refs \\ ptr) with
               SOME (c',refs') ->
                 SOME (bvl_Block tag (APPEND (APPEND l [c']) r),
                       refs' |+ (ptr,MutBlock tag T l c r))
             | NONE -> NONE)
          else NONE
      | SOME res -> SOME (bvl_RefPtr b ptr,refs)
      | NONE -> NONE) /\
   (bvi_finalise_cons v refs = SOME (v,refs))`;;

let bvi_finalise_cons_ind = cake_ind "bvi_finalise_cons";;

let bvi_do_app_aux_def = cake_def
  `bvi_do_app_aux (op:clos_op) (vs:bvl_v list) (s:(C,FFI)bvi_state) =
     match (op,vs) with
       (IntOp (clos_Const i),xs) ->
         if small_enough_int i /\ NULL xs then
           SOME (SOME (bvl_Number i, s))
         else NONE
     | (clos_Label l,xs) ->
         (match xs with
            [] -> if l IN domain (bvi_state_code s) then
                    SOME (SOME (bvl_CodePtr l, s))
                  else NONE
          | _ -> NONE)
     | (GlobOp GlobalsPtr,xs) ->
         (match xs with
            [] -> (match bvi_state_global s with
                     SOME p -> SOME (SOME (bvl_RefPtr T p, s))
                   | NONE -> NONE)
          | _ -> NONE)
     | (GlobOp SetGlobalsPtr,xs) ->
         (match xs with
            [bvl_RefPtr T p] -> SOME (SOME (bvl_Unit, bvi_state_global_fupd (K (SOME p)) s))
          | _ -> NONE)
     | (GlobOp (clos_Global n), xs) ->
         (match xs with
            [] -> (match bvi_state_global s with
                     SOME ptr ->
                       (match FLOOKUP (bvi_state_refs s) ptr with
                          SOME (bvl_ValueArray xs) ->
                            (if n < LENGTH xs
                             then SOME (SOME (EL n xs, s))
                             else NONE)
                        | _ -> NONE)
                   | NONE -> NONE)
          | _ -> NONE)
     | (GlobOp (SetGlobal n), xs) ->
         (match xs with
            [x] -> (match bvi_state_global s with
                      SOME ptr ->
                        (match FLOOKUP (bvi_state_refs s) ptr with
                           SOME (bvl_ValueArray xs) ->
                             (if n < LENGTH xs
                              then SOME (SOME (bvl_Unit, bvi_state_refs_fupd
                                     (K (bvi_state_refs s |+
                                         (ptr, bvl_ValueArray (LUPDATE x n xs)))) s))
                              else NONE)
                         | _ -> NONE)
                    | NONE -> NONE)
          | _ -> NONE)
     | (BlockOp (FromList n), xs) ->
         (match xs with
            [len; lv] ->
              (match bvl_v_to_list lv with
                 SOME vs -> if len = bvl_Number (&(LENGTH vs))
                            then SOME (SOME (bvl_Block n vs, s))
                            else NONE
               | _ -> NONE)
          | _ -> NONE)
     | (MemOp (RefByte f), xs) ->
         (match xs with
            [bvl_Number i; bvl_Number b] ->
              if &0 <= i /\ (?w:byte. b = &(val w)) then
                let ptr = (minimal ptr. ~(ptr IN FDOM (bvi_state_refs s))) in
                  SOME (SOME (bvl_RefPtr T ptr, bvi_state_refs_fupd
                    (K (bvi_state_refs s |+
                        (ptr, bvl_ByteArray f (REPLICATE (num_of_int i) (iword b))))) s))
              else NONE
          | _ -> NONE)
     | (MemOp (MutCons tag i),xs) ->
         (let ptr = (minimal ptr. ~(ptr IN FDOM (bvi_state_refs s))) in
            if i >= LENGTH xs then NONE else
              let l = TAKE i xs in
              let c = EL i xs in
              let r = DROP (i + 1) xs in
              let b = MutBlock tag F l c r in
                SOME (SOME (bvl_RefPtr F ptr,
                            bvi_state_refs_fupd (K (bvi_state_refs s |+ (ptr,b))) s)))
     | (MemOp UpdateCons,[bvl_RefPtr _ ptr; bvl_Number i; x]) ->
         (match FLOOKUP (bvi_state_refs s) ptr with
            SOME (MutBlock tag finalised l c r) ->
              if ~(i = &(LENGTH l)) \/ finalised then NONE else
                SOME (SOME (bvl_Unit, bvi_state_refs_fupd
                  (K (bvi_state_refs s |+ (ptr,MutBlock tag F l x r))) s))
          | _ -> NONE)
     | (MemOp FinaliseCons,[x]) ->
         (match bvi_finalise_cons x (bvi_state_refs s) with
            SOME (v,refs') -> SOME (SOME (v,bvi_state_refs_fupd (K refs') s))
          | NONE -> NONE)
     | (GlobOp AllocGlobal, _) -> NONE
     | (MemOp FromListByte, _) -> NONE
     | (MemOp ToListByte, _) -> NONE
     | (MemOp ConcatByteVec, _) -> NONE
     | (MemOp (CopyByte T), _) -> NONE
     | _ -> (SOME NONE:((bvl_v # (C,FFI)bvi_state) option) option)`;;

(* HOL4 infers the most general type: the exception type E is free *)
let bvi_do_install_def = cake_def
  `bvi_do_install vs (s:(C,FFI)bvi_state) =
     match vs with
       [v1; v2; vl1; vl2] ->
         (match (bvl_v_to_bytes v1, bvl_v_to_words v2) with
            (SOME bytes, SOME data) ->
              if ~(vl1 = bvl_Number (&(LENGTH bytes))) \/
                 ~(vl2 = bvl_Number (&(LENGTH data)))
              then Rerr (Rabort Rtype_error) else
              let (cfg,progs) = bvi_state_compile_oracle s 0 in
              let new_oracle = shift_seq 1 (bvi_state_compile_oracle s) in
                if DISJOINT (domain (bvi_state_code s)) (set_of_list (MAP FST progs)) /\
                   ALL_DISTINCT (MAP FST progs) then
                (match (bvi_state_compile s cfg progs, progs) with
                   (SOME (bytes',data',cfg'), CONS (k,prog) _) ->
                     if bytes = bytes' /\ data = data' /\ FST (new_oracle 0) = cfg' then
                       let s' =
                         bvi_state_code_fupd (K (sptree_union (bvi_state_code s) (fromAList progs)))
                           (bvi_state_compile_oracle_fupd (K new_oracle) s)
                       in
                         Rval (bvl_CodePtr k, s')
                     else Rerr (Rabort Rtype_error)
                 | _ -> Rerr (Rabort Rtype_error))
                else Rerr (Rabort Rtype_error)
          | _ -> Rerr (Rabort Rtype_error))
     | _ -> (Rerr (Rabort Rtype_error):(bvl_v # (C,FFI)bvi_state,E)result)`;;

let bvi_do_app_def = cake_def
  `bvi_do_app (op:clos_op) vs (s:(C,FFI)bvi_state) =
     if op = clos_Install then bvi_do_install vs s else
     match bvi_do_app_aux op vs s with
       NONE -> Rerr (Rabort Rtype_error)
     | SOME (SOME (v,t)) -> Rval (v,t)
     | SOME NONE ->
         (match bvl_do_app op vs (bvi_to_bvl s) with
            Rval (v,t) -> Rval (v, bvl_to_bvi t s)
          | Rerr (Rabort a) -> Rerr (Rabort a)
          | Rerr (Rraise v) -> Rerr (Rraise (Exn v)))`;;

let bvi_dest_thunk_ret_INDUCT,bvi_dest_thunk_ret_RECURSION = cake_type
  "bvi_dest_thunk_ret = bvi_BadRef
                      | bvi_NotThunk
                      | bvi_IsThunk thunk_mode bvl_v";;

let bvi_dest_thunk_def = sem1aux_def
  `(bvi_dest_thunk (bvl_RefPtr b ptr) (refs:(num,(bvl_v)bvl_ref)fmap) =
      match FLOOKUP refs ptr with
        NONE -> bvi_BadRef
      | SOME (bvl_Thunk Evaluated v) ->
          if b then bvi_BadRef else bvi_IsThunk Evaluated v
      | SOME (bvl_Thunk NotEvaluated v) ->
          if b then bvi_BadRef else bvi_IsThunk NotEvaluated v
      | SOME _ -> bvi_NotThunk) /\
   (bvi_dest_thunk vs refs = bvi_NotThunk)`;;

(* The evaluation is defined as a clocked functional version of a          *)
(* conventional big-step operational semantics.                             *)

(* HOL4 infers the most general type: s and s1 are states of independent   *)
(* types                                                                     *)
let bvi_fix_clock_def = cake_def
  `bvi_fix_clock (s:(A,B)bvi_state) ((res:R),(s1:(C,D)bvi_state)) =
     (res,bvi_state_clock_fupd (K (MIN (bvi_state_clock s) (bvi_state_clock s1))) s1)`;;

(* HOL4 [local] *)
let bvi_fix_clock_IMP = prove
 (`!(s:(A,B)bvi_state) (x:R#(C,D)bvi_state) res s1.
     bvi_fix_clock s x = (res,s1) ==> bvi_state_clock s1 <= bvi_state_clock s`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `x:R#(C,D)bvi_state` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:R` (X_CHOOSE_THEN `s':(C,D)bvi_state` SUBST1_TAC)) THEN
  REWRITE_TAC[bvi_fix_clock_def; PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM] THEN ARITH_TAC);;

(* The semantics of expression evaluation is defined next. For convenience *)
(* of subsequent proofs, the evaluation function is defined to evaluate a   *)
(* list of bvi_exp expressions.                                              *)

let CLOSSEMAUX_bvi_evaluate_clauses1 =
  `(bvi_evaluate ([]:bvi_exp list,env:bvl_v list,s:(C,FFI)bvi_state) =
      (Rval [] : bvi_result,s)) /\
   (bvi_evaluate (CONS x (CONS y xs),env,s) =
      match bvi_fix_clock s (bvi_evaluate ([x],env,s)) with
        (Rval v1,s1) ->
          (match bvi_evaluate (CONS y xs,env,s1) with
             (Rval vs,s2) -> (Rval (CONS (HD v1) vs),s2)
           | res -> res)
      | res -> res) /\
   (bvi_evaluate ([bvi_Var n],env,s) =
      if n < LENGTH env then (Rval [EL n env],s)
      else (Rerr (Rabort Rtype_error),s)) /\
   (bvi_evaluate ([bvi_If x1 x2 x3],env,s) =
      match bvi_fix_clock s (bvi_evaluate ([x1],env,s)) with
        (Rval vs,s1) ->
          if bvl_Boolv T = HD vs then bvi_evaluate ([x2],env,s1) else
          if bvl_Boolv F = HD vs then bvi_evaluate ([x3],env,s1) else
            (Rerr (Rabort Rtype_error),s1)
      | res -> res) /\
   (bvi_evaluate ([bvi_Let xs x2],env,s) =
      match bvi_fix_clock s (bvi_evaluate (xs,env,s)) with
        (Rval vs,s1) -> bvi_evaluate ([x2],APPEND vs env,s1)
      | res -> res) /\
   (bvi_evaluate ([bvi_Raise x1],env,s) =
      match bvi_evaluate ([x1],env,s) with
        (Rval vs,s) -> (Rerr (Rraise (Exn (HD vs))),s)
      | res -> res) /\
   (bvi_evaluate ([bvi_Return xs],env,s) =
      match bvi_evaluate (xs,env,s) with
        (Rval vs,s) -> (Rerr (Rraise (Ret vs)),s)
      | res -> res) /\
   (bvi_evaluate ([bvi_Op op xs],env,s) =
      match bvi_fix_clock s (bvi_evaluate (xs,env,s)) with
        (Rval vs,s) ->
          (match bvi_do_app op (REVERSE vs) s with
             Rerr e -> (Rerr e,s)
           | Rval (v,s) -> (Rval [v],s))
      | res -> res) /\
   (bvi_evaluate ([bvi_Tick x],env,s) =
      if bvi_state_clock s = 0 then (Rerr (Rabort Rtimeout_error),s) else
        bvi_evaluate ([x],env,bvi_dec_clock 1 s)) /\
   (bvi_evaluate ([bvi_Force force_loc n],env,s) =
      if ~(n < LENGTH env) then (Rerr (Rabort Rtype_error),s) else
        let thunk_v = EL n env in
          (match bvi_dest_thunk thunk_v (bvi_state_refs s) with
             bvi_BadRef -> (Rerr (Rabort Rtype_error),s)
           | bvi_NotThunk -> (Rerr (Rabort Rtype_error),s)
           | bvi_IsThunk Evaluated v -> (Rval [v],s)
           | bvi_IsThunk NotEvaluated f ->
               (match bvl_find_code (SOME force_loc) [thunk_v; f] (bvi_state_code s) with
                  NONE -> (Rerr (Rabort Rtype_error),s)
                | SOME (args,exp) ->
                    if bvi_state_clock s = 0 then
                      (Rerr (Rabort Rtimeout_error),bvi_state_clock_fupd (K 0) s)
                    else
                      (match bvi_evaluate ([exp],args,bvi_dec_clock 1 s) with
                         (Rerr (Rraise (Ret _)),s1) -> (Rerr (Rabort Rtype_error),s1)
                       | res -> res)))) /\
   (bvi_evaluate ([bvi_Call ticks dest xs handler],env,s1) =
      if IS_NONE dest /\ IS_SOME handler then (Rerr (Rabort Rtype_error),s1) else
      match bvi_fix_clock s1 (bvi_evaluate (xs,env,s1)) with
        (Rval vs,s) ->
          (match bvl_find_code dest vs (bvi_state_code s) with
             NONE -> (Rerr (Rabort Rtype_error),s)
           | SOME (args,exp) ->
               if bvi_state_clock s < ticks + 1 then
                 (Rerr (Rabort Rtimeout_error),bvi_state_clock_fupd (K 0) s)
               else
                 (match bvi_fix_clock (bvi_dec_clock (ticks + 1) s)
                          (bvi_evaluate ([exp],args,bvi_dec_clock (ticks + 1) s)) with
                    (Rerr (Rraise (Exn v)),s) ->
                      (match handler with
                         SOME x ->
                           (match bvi_evaluate ([x],CONS v env,s) with
                              (Rerr (Rraise (Ret _)),s1) -> (Rerr (Rabort Rtype_error),s1)
                            | res -> res)
                       | NONE -> (Rerr (Rraise (Exn v)),s))
                  | (Rerr (Rraise _),s) -> (Rerr (Rabort Rtype_error),s)
                  | res -> res))
      | res -> res)`;;

(* the clause for LetCall in a second quotation: dest is a number here and *)
(* an option in the clause for Call                                         *)
let CLOSSEMAUX_bvi_evaluate_clauses2 =
  `(bvi_evaluate ([LetCall rets ticks dest xs y],env,s1) =
      match bvi_fix_clock s1
              ((bvi_evaluate:bvi_exp list # bvl_v list # (C,FFI)bvi_state ->
                             bvi_result # (C,FFI)bvi_state) (xs,env,s1)) with
        (Rval vs,s) ->
          (match bvl_find_code (SOME dest) vs (bvi_state_code s) with
             NONE -> (Rerr (Rabort Rtype_error),s)
           | SOME (args,exp) ->
               if bvi_state_clock s < ticks + 1 then
                 (Rerr (Rabort Rtimeout_error),bvi_state_clock_fupd (K 0) s)
               else
                 (match bvi_fix_clock (bvi_dec_clock (ticks + 1) s)
                          (bvi_evaluate ([exp],args,bvi_dec_clock (ticks + 1) s)) with
                    (Rval _,s) -> (Rerr (Rabort Rtype_error),s)
                  | (Rerr (Rraise (Ret ret_vs)),s) ->
                      if LENGTH ret_vs = rets then
                        bvi_evaluate ([y],APPEND ret_vs env,s)
                      else (Rerr (Rabort Rtype_error),s)
                  | res -> res))
      | res -> res)`;;

let CLOSSEMAUX_bvi_evaluate_clauses =
  list_mk_conj (conjuncts CLOSSEMAUX_bvi_evaluate_clauses1 @
                [CLOSSEMAUX_bvi_evaluate_clauses2]);;

(* HOL4's termination relation:                                              *)
(*   inv_image (measure I LEX measure (list_size exp_size))                  *)
(*             (\(xs,env,s). (s.clock,xs))                                   *)

let CLOSSEMAUX_bvi_evaluate_rel =
  `inv_image (MEASURE (I:num->num) LEX MEASURE (list_size bvi_exp_size))
     (\x:bvi_exp list # bvl_v list # (C,FFI)bvi_state.
        bvi_state_clock (SND (SND x)),FST x)`;;

(* HOL4: rpt strip_tac >> simp[dec_clock_def] >> imp_res_tac fix_clock_IMP  *)
(* >> imp_res_tac LESS_EQ_dec_clock >> rw[]                                  *)

let CLOSSEMAUX_bvi_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP bvi_fix_clock_IMP)) THEN
  REPEAT GEN_TAC THEN
  (fun g -> let ths = [inv_image_THM; LEX_DEF; FST; SND; I_THM; measure_THM;
                       bvi_dec_clock_def; bvi_state_INFO.ri_accfupds; K_THM;
                       list_size; LENGTH] @
                      !the_size_defs @ flat (map snd (!the_size_aux_eqs)) in
            (RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths) g) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSSEMAUX_is_num_fact o concl))) THEN
  ARITH_TAC;;

(* HOL4 evaluate_def (the first one, with fix_clock) *)
let CLOSSEMAUX_bvi_evaluate_fix_def =
  sem1aux_def_wf CLOSSEMAUX_bvi_evaluate_rel CLOSSEMAUX_bvi_TC_TAC
    CLOSSEMAUX_bvi_evaluate_clauses;;

(* HOL4's first evaluate_ind *)
let CLOSSEMAUX_bvi_evaluate_fix_ind = cake_ind "bvi_evaluate";;

(* We prove that the clock never increases. *)

(* the clock of the BVI-specific operations *)
let CLOSSEMAUX_bvi_do_app_aux_clock = prove
 (`!op vs (s:(C,FFI)bvi_state) v t.
     bvi_do_app_aux op vs s = SOME (SOME (v,t)) ==> bvi_state_clock t = bvi_state_clock s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_do_app_aux_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[option_INJ; option_DISTINCT; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM]);;

(* HOL4: SIMP_TAC std_ss [do_app_def,do_install_def] \\ IF_CASES_TAC \\ ... *)
(* \\ IMP_RES_TAC bvlSemTheory.do_app_const \\ ...                       *)
let bvi_do_app_const = prove
 (`!op args (s1:(C,FFI)bvi_state) res s2.
     bvi_do_app op args s1 = Rval (res,s2) ==>
     bvi_state_clock s2 = bvi_state_clock s1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_do_app_def] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[bvi_do_install_def; LET_DEF; LET_END_DEF] THEN
    REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
    REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  REPEAT TOP_CASE_TAC THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  IMP_RES_TAC CLOSSEMAUX_bvi_do_app_aux_clock THEN
  IMP_RES_TAC bvl_do_app_const THEN
  FS[bvl_to_bvi_def; bvi_to_bvl_def; bvi_state_INFO.ri_accfupds;
     bvl_state_INFO.ri_accfupds; K_THM]);;

(* HOL4: recInduct evaluate_ind >> rw[evaluate_def] >> every_case_tac >>    *)
(* fs[dec_clock_def] >> rw[] >> rfs[] >> imp_res_tac fix_clock_IMP >>       *)
(* imp_res_tac do_app_const >> fs[]                                          *)

let CLOSSEMAUX_BVI_CLOCK_TAC : tactic =
  REWRITE_TAC[SND] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[CLOSSEMAUX_bvi_evaluate_fix_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  FS[PAIR_EQ] THEN
  RES_TAC THEN RES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN RES_TAC THEN
  IMP_RES_TAC bvi_fix_clock_IMP THEN
  IMP_RES_TAC bvi_do_app_const THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvi_dec_clock_def; bvi_state_INFO.ri_accfupds; K_THM]) THEN
  REWRITE_TAC[bvi_dec_clock_def; bvi_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (CLOSSEMAUX_is_num_fact o concl))) THEN
  ARITH_TAC;;

let bvi_evaluate_clock = prove
 (`!xs env (s1:(C,FFI)bvi_state) vs s2.
     bvi_evaluate (xs,env,s1) = (vs,s2) ==> bvi_state_clock s2 <= bvi_state_clock s1`,
  SUBGOAL_THEN
   `!tup vs (s2:(C,FFI)bvi_state).
      bvi_evaluate tup = (vs,s2) ==>
      bvi_state_clock s2 <= bvi_state_clock (SND (SND tup))`
   (fun th -> MESON_TAC[th; SND]) THEN
  MATCH_MP_TAC CLOSSEMAUX_bvi_evaluate_fix_ind THEN REPEAT CONJ_TAC THEN
  CLOSSEMAUX_BVI_CLOCK_TAC);;

let bvi_fix_clock_evaluate = prove
 (`!(s:(C,FFI)bvi_state) xs env.
     bvi_fix_clock s (bvi_evaluate (xs,env,s)) = bvi_evaluate (xs,env,s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `bvi_evaluate (xs,env,s:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:bvi_result`
    (X_CHOOSE_THEN `s1:(C,FFI)bvi_state` (fun th -> ASSUME_TAC th THEN
                                                  REWRITE_TAC[th]))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvi_evaluate_clock) THEN
  REWRITE_TAC[bvi_fix_clock_def; PAIR_EQ; bvi_state_component_equality;
              bvi_state_INFO.ri_accfupds; K_THM] THEN
  ASM_ARITH_TAC);;

(* Finally, we remove fix_clock from the induction and definition theorems. *)

let bvi_evaluate_def =
  REWRITE_RULE[bvi_fix_clock_evaluate] CLOSSEMAUX_bvi_evaluate_fix_def;;

let bvi_evaluate_ind =
  REWRITE_RULE[bvi_fix_clock_evaluate] CLOSSEMAUX_bvi_evaluate_fix_ind;;

(* cake_ind returns HOL4's final induction theorem *)
let () = cake_ind_store := ("bvi_evaluate",bvi_evaluate_ind) :: !cake_ind_store;;

(* observational semantics *)

let bvi_initial_state_def = cake_def
  `bvi_initial_state (ffi:(FFI)ffi_state) code (co:num -> C # (num # num # bvi_exp) list)
                     cc k =
     bvi_state_REC FEMPTY k NONE cc co code ffi`;;

let bvi_semantics_def = cake_def
  `bvi_semantics (init_ffi:(FFI)ffi_state) code
                 (co:num -> C # (num # num # bvi_exp) list) cc start =
     let es = [bvi_Call 0 (SOME start) [] NONE] in
     let init = bvi_initial_state init_ffi code co cc in
       if ?k e. FST (bvi_evaluate (es,[],init k)) = Rerr e /\
                ~(e = Rabort Rtimeout_error) /\ (!f. ~(e = Rabort (Rffi_error f)))
       then Fail
       else
       (match some res.
          ?k s r outcome.
            bvi_evaluate (es,[],init k) = (r,s) /\
            (match r with
               Rerr (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
             | Rval _ -> outcome = Success
             | _ -> F) /\
            res = Terminate outcome (ffi_state_io_events (bvi_state_ffi s))
        with
          SOME res -> res
        | NONE ->
            Diverge
              (build_lprefix_lub
                (IMAGE (\k. llist_fromList
                          (ffi_state_io_events
                             (bvi_state_ffi (SND (bvi_evaluate (es,[],init k))))))
                       UNIV)))`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas used by several later files.                                       *)
(* ------------------------------------------------------------------------- *)

let CLOSSEMAUX_bvi_semantics_not_Fail_cond = prove
 (`!(ffi:(FFI)ffi_state) code (co:num -> C # (num#num#bvi_exp) list)
     (cc:C->(num#num#bvi_exp)list->(((8)word)list#((64)word)list#C)option) start.
     ~(bvi_semantics ffi code co cc start = Fail) ==>
     ~(?j e. FST (bvi_evaluate ([bvi_Call 0 (SOME start) [] NONE],[],
                    bvi_initial_state ffi code co cc j)) = Rerr e /\
             ~(e = Rabort Rtimeout_error) /\ (!f. ~(e = Rabort (Rffi_error f))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvi_semantics_def; LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;
