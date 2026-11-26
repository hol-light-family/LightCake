(* ========================================================================= *)
(* clos_to_bvlProof_p3: part 3 of 3 (HOL4 lines 6084-9258) of the port of    *)
(* HOL4 compiler/backend/proofs/clos_to_bvlProofScript.sml (CakeML v3479).   *)
(* Correctness proof for clos_to_bvl.                                        *)
(* The parts _p1 ... _p3 are loaded one after the other (each needs the     *)
(* previous one); the rendering notes are in the header of _p1.              *)
(* ========================================================================= *)

needs "compiler/backend/proofs/clos_to_bvlProof_p2.ml";;

prioritize_num();;
type_invention_error := true;;

(* C2BP3AUX_ names are local helpers. *)
(* ===== PART 3: HOL4 lines 6084-9258 ===== *)

(* HOL4 line 6084 *)
let clos_init_def = cake_def
  `clos_init max_app (s:(C,FFI)clos_state) <=>
     clos_state_globals s = [] /\ clos_state_refs s = FEMPTY /\
     clos_state_code s = FEMPTY /\ clos_state_max_app s = max_app`;;


(* HOL4 line 6089 *)
let clos_init_with_clock = prove
 (`!max_app (s:(C,FFI)clos_state) k.
     clos_init max_app (clos_state_clock_fupd (combin_K k) s) <=> clos_init max_app s`,
  REWRITE_TAC[clos_init_def; clos_state_INFO.ri_accfupds; K_THM]);;

let _ = cake_add_simps [clos_init_with_clock];;

(* HOL4 line 6096 *)
let code_installed_fromAList_strong = prove
 (`!ls ls'.
     ALL_DISTINCT (MAP FST ls) /\ IS_SUBLIST ls ls'
     ==> clos_to_bvlProof_code_installed ls' (fromAList ls)`,
  REWRITE_TAC[clos_to_bvlProof_code_installed_def; GSYM ALL_MEM; FORALL_PAIR_THM;
              lookup_fromAList] THEN
  MESON_TAC[ALOOKUP_ALL_DISTINCT_MEM; IS_SUBLIST_MEM]);;

(* HOL4 line 6126 *)
let evaluate_init1 = prove
 (`!mapp2 mapp1 tot (st:(C,FFI)bvl_state).
     (!n. n < mapp2 ==> partial_app_fn_location mapp1 tot n IN domain (bvl_state_code st))
     ==> bvl_evaluate
           (REVERSE (list_of_seq (\prev. bvl_Op (clos_Label (partial_app_fn_location mapp1 tot
                                                               prev)) []) mapp2),
            [bvl_Unit],st) =
         (Rval (REVERSE (list_of_seq (\prev. bvl_CodePtr (partial_app_fn_location mapp1 tot
                                                            prev)) mapp2)),st)`,
  INDUCT_TAC THEN REWRITE_TAC[list_of_seq; REVERSE; bvl_evaluate_def] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REVERSE_APPEND; REVERSE; APPEND] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN
  REWRITE_TAC[bvl_evaluate_def] THEN CAKE_REWRITE_TAC[REVERSE] THEN
  ASM_SIMP_TAC[C2BP1AUX_do_app_Label; ARITH_RULE `mapp2 < SUC mapp2`] THEN
  CAKE_REWRITE_TAC[HD] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`mapp1:num`; `tot:num`; `st:(C,FFI)bvl_state`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ARITH_RULE `n < mapp2 ==> n < SUC mapp2`]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN CAKE_REWRITE_TAC[]);;

(* HOL4 line 6141 *)
let evaluate_init = prove
 (`!mapp2 mapp1 (st:(C,FFI)bvl_state).
     (!m n. m < mapp2 /\ n < m
            ==> partial_app_fn_location mapp1 m n IN domain (bvl_state_code st))
     ==> bvl_evaluate
           (REVERSE (FLAT (list_of_seq (\tot. list_of_seq
              (\prev. bvl_Op (clos_Label (partial_app_fn_location mapp1 tot prev)) []) tot)
              mapp2)),
            [bvl_Unit],st) =
         (Rval (REVERSE (FLAT (list_of_seq (\tot. list_of_seq
                  (\prev. bvl_CodePtr (partial_app_fn_location mapp1 tot prev)) tot) mapp2))),
          st)`,
  INDUCT_TAC THEN REWRITE_TAC[list_of_seq; FLAT; REVERSE; bvl_evaluate_def] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[FLAT_APPEND; FLAT; APPEND_NIL; REVERSE_APPEND; bvl_evaluate_APPEND] THEN
  MP_TAC(SPECL [`mapp2:num`; `mapp1:num`; `mapp2:num`; `st:(C,FFI)bvl_state`]
           evaluate_init1) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ARITH_RULE `mapp2 < SUC mapp2`]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN CAKE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`mapp1:num`; `st:(C,FFI)bvl_state`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ARITH_RULE `m < mapp2 ==> m < SUC mapp2`]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN CAKE_REWRITE_TAC[]);;

(* HOL4 line 6161 *)
let clos_to_bvlProof_FST_EQ_LEMMA = prove
 (`!(x:A#B) y. FST x = y <=> ?y1. x = (y,y1)`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 line 6167: val evaluate_add_to_clock_io_events_mono_alt =           *)
(* closPropsTheory.evaluate_add_to_clock_io_events_mono |> ... (a derived   *)
(* theorem of closProps for the proofs; not stated)                          *)
(* HOL4 line 6173: val evaluate_add_to_clock_io_events_mono_alt_bvl (the    *)
(* same for bvlProps; not stated)                                            *)

(* HOL4 line 6179 *)
let clos_to_bvlProof_eval_sim_def = cake_def
  `clos_to_bvlProof_eval_sim (ffi:(FFI)ffi_state) max_app code1 (co1:num->C#clos_prog)
     cc1 es1 code2 (co2:num->C#(num#num#bvl_exp)list) cc2 start
     (rel:(num,num#clos_exp)fmap->(num->C#clos_prog)->
          (C->clos_prog->(byte list#int64 list#C)option)->clos_exp list->
          (num#bvl_exp)spt->(num->C#(num#num#bvl_exp)list)->
          (C->(num#num#bvl_exp)list->(byte list#int64 list#C)option)->num->bool) <=>
     !k res1 s2.
       clos_evaluate (es1,[],clos_initial_state ffi max_app code1 co1 cc1 k) = (res1,s2) /\
       ~(res1 = Rerr (Rabort Rtype_error)) /\
       rel code1 co1 cc1 es1 code2 co2 cc2 start
       ==> ?ck res2 t2.
             bvl_evaluate ([bvl_Call 0 (SOME start) []],[],
                           bvl_initial_state ffi code2 co2 cc2 (k + ck)) = (res2,t2) /\
             result_rel (\x y. T) (\x y. T) res1 res2 /\
             clos_state_ffi s2 = bvl_state_ffi t2`;;

(* HOL4 line 6191 *)
let clos_to_bvlProof_initial_state_with_clock = prove
 (`!(ffi:(FFI)ffi_state) ma code (co:num->C#clos_prog) cc k ck.
     clos_state_clock_fupd
       (combin_K (clos_state_clock (clos_initial_state ffi ma code co cc k) + ck))
       (clos_initial_state ffi ma code co cc k) =
     clos_initial_state ffi ma code co cc (k + ck)`,
  REWRITE_TAC[clos_initial_state_def; clos_state_INFO.ri_accessors;
              clos_state_INFO.ri_fupds; K_THM]);;

(* HOL4 line 6199 *)
let initial_state_with_clock_bvl = prove
 (`!(ffi:(FFI)ffi_state) code (co:num->C#(num#num#bvl_exp)list) cc k ck.
     bvl_state_clock_fupd (combin_K (bvl_state_clock (bvl_initial_state ffi code co cc k) + ck))
       (bvl_initial_state ffi code co cc k) =
     bvl_initial_state ffi code co cc (k + ck) /\
     bvl_inc_clock ck (bvl_initial_state ffi code co cc k) =
     bvl_initial_state ffi code co cc (k + ck)`,
  REWRITE_TAC[bvl_initial_state_def; bvl_inc_clock_def; bvl_state_INFO.ri_accessors;
              bvl_state_INFO.ri_fupds; K_THM]);;

(* local helpers for IMP_semantics_eq (as closProps' helpers for its        *)
(* IMP_semantics_eq, with bvlSem's semantics on one side)                   *)
let C2BP3AUX_bvl_sem_fail = prove
 (`!(ffi:(FFI)ffi_state) code (co:num->C#(num#num#bvl_exp)list) cc start.
     bvl_semantics ffi code co cc start = Fail <=>
     ?k. FST (bvl_evaluate ([bvl_Call 0 (SOME start) []],[],
                            bvl_initial_state ffi code co cc k)) =
         Rerr (Rabort Rtype_error)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_semantics_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[distinctness "behaviour"] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP BASICAUX_some_SOME) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[distinctness "behaviour"]);;

let C2BP3AUX_bvl_init_add = prove
 (`!es env (ffi:(FFI)ffi_state) code (co:num->C#(num#num#bvl_exp)list) cc k ck.
     ~(FST (bvl_evaluate (es,env,bvl_initial_state ffi code co cc k)) =
       Rerr (Rabort Rtimeout_error)) ==>
     FST (bvl_evaluate (es,env,bvl_initial_state ffi code co cc (k + ck))) =
     FST (bvl_evaluate (es,env,bvl_initial_state ffi code co cc k)) /\
     bvl_state_ffi (SND (bvl_evaluate (es,env,bvl_initial_state ffi code co cc (k + ck)))) =
     bvl_state_ffi (SND (bvl_evaluate (es,env,bvl_initial_state ffi code co cc k)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `bvl_evaluate (es,env,bvl_initial_state (ffi:(FFI)ffi_state) code
                                (co:num->C#(num#num#bvl_exp)list) cc k)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `s:(C,FFI)bvl_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`es:bvl_exp list`; `env:bvl_v list`; `ffi:(FFI)ffi_state`;
                `code:(num#bvl_exp)spt`; `co:num->C#(num#num#bvl_exp)list`;
                `cc:C->(num#num#bvl_exp)list->(byte list#int64 list#C)option`; `k:num`;
                `r:(bvl_v list,bvl_v)result`; `s:(C,FFI)bvl_state`]
               bvl_evaluate_add_clock_initial_state) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FST; SND; bvl_state_INFO.ri_accfupds]);;

let C2BP3AUX_bvl_init_mono = prove
 (`!es env (ffi:(FFI)ffi_state) code (co:num->C#(num#num#bvl_exp)list) cc k1 k2.
     k1 <= k2 ==>
     ffi_state_io_events (bvl_state_ffi
       (SND (bvl_evaluate (es,env,bvl_initial_state ffi code co cc k1)))) <<=
     ffi_state_io_events (bvl_state_ffi
       (SND (bvl_evaluate (es,env,bvl_initial_state ffi code co cc k2))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  MP_TAC(ISPECL [`es:bvl_exp list`; `env:bvl_v list`;
                 `bvl_initial_state (ffi:(FFI)ffi_state) code
                    (co:num->C#(num#num#bvl_exp)list) cc k1`;
                 `d:num`] bvl_evaluate_add_to_clock_io_events_mono) THEN
  REWRITE_TAC[initial_state_with_clock_bvl]);;

let C2BP3AUX_result_rel_T = prove
 (`!(r1:(clos_v list,clos_v)result) (r2:(bvl_v list,bvl_v)result).
     result_rel (\(x:clos_v list) (y:bvl_v list). T) (\(x:clos_v) (y:bvl_v). T) r1 r2 <=>
     (?a b. r1 = Rval a /\ r2 = Rval b) \/
     (?a b. r1 = Rerr (Rraise a) /\ r2 = Rerr (Rraise b)) \/
     (?a. r1 = Rerr (Rabort a) /\ r2 = Rerr (Rabort a))`,
  REPEAT GEN_TAC THEN CASES_ON `r1:(clos_v list,clos_v)result` THEN
  CASES_ON `r2:(bvl_v list,bvl_v)result` THEN
  REWRITE_TAC[result_rel_def; injectivity "result"; distinctness "result"] THEN
  TRY(CASES_ON `a:(clos_v)error_result` THEN CASES_ON `a':(bvl_v)error_result`) THEN
  REWRITE_TAC[exc_rel_def; injectivity "error_result"; distinctness "error_result"] THEN
  MESON_TAC[]);;

let C2BP3AUX_M_eq = prove
 (CASE_TERM `!(r1:(clos_v list,clos_v)result) (r2:(bvl_v list,bvl_v)result) outcome.
     result_rel (\(x:clos_v list) (y:bvl_v list). T) (\(x:clos_v) (y:bvl_v). T) r1 r2 ==>
     ((match r1 with
         Rerr (Rabort Rtimeout_error) -> F
       | Rerr (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
       | _ -> outcome = Success) <=>
      (match r2 with
         Rerr (Rabort Rtimeout_error) -> F
       | Rerr (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
       | _ -> outcome = Success))`,
  REWRITE_TAC[C2BP3AUX_result_rel_T] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[case_def "result"; case_def "error_result"]);;

let C2BP3AUX_term_pred_eq = prove
 (CASE_TERM `!(E1:num -> (clos_v list,clos_v)result # (A,FFI)clos_state)
     (E2:num -> (bvl_v list,bvl_v)result # (B,FFI)bvl_state).
     (!k. ~(FST (E1 k) = Rerr (Rabort Rtype_error))) /\
     (!k. ~(FST (E2 k) = Rerr (Rabort Rtype_error))) /\
     (!k. ?ck. result_rel (\(x:clos_v list) (y:bvl_v list). T) (\(x:clos_v) (y:bvl_v). T)
                 (FST (E1 k)) (FST (E2 (k + ck))) /\
               clos_state_ffi (SND (E1 k)) = bvl_state_ffi (SND (E2 (k + ck)))) /\
     (!k ck. ~(FST (E2 k) = Rerr (Rabort Rtimeout_error)) ==>
             FST (E2 (k + ck)) = FST (E2 k) /\
             bvl_state_ffi (SND (E2 (k + ck))) = bvl_state_ffi (SND (E2 k)))
     ==> !res. (?k s r outcome.
                  E2 k = (r,s) /\
                  (match r with
                     Rerr (Rabort Rtimeout_error) -> F
                   | Rerr (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
                   | _ -> outcome = Success) /\
                  res = Terminate outcome (ffi_state_io_events (bvl_state_ffi s))) <=>
               (?k r s outcome.
                  E1 k = (r,s) /\
                  (match r with
                     Rerr (Rabort Rtimeout_error) -> F
                   | Rerr (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
                   | _ -> outcome = Success) /\
                  res = Terminate outcome (ffi_state_io_events (clos_state_ffi s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `s:(B,FFI)bvl_state`
      (X_CHOOSE_THEN `r:(bvl_v list,bvl_v)result`
        (X_CHOOSE_THEN `outcome:outcome` STRIP_ASSUME_TAC)))) THEN
    MP_TAC(ISPEC `(E1:num -> (clos_v list,clos_v)result # (A,FFI)clos_state) k`
                 PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:(clos_v list,clos_v)result`
      (X_CHOOSE_THEN `s1:(A,FFI)clos_state` ASSUME_TAC)) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC o SPEC `k:num` o
      check (fun th -> is_exists (snd (dest_forall (concl th))))) THEN
    SUBGOAL_THEN `~(r = Rerr (Rabort Rtimeout_error):(bvl_v list,bvl_v)result)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[case_def "result"; case_def "error_result";
                                  case_def "abort"]) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `ck:num`] o
      check (fun th -> is_imp (snd (strip_forall (concl th))))) THEN
    ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
    SUBGOAL_THEN `result_rel (\(x:clos_v list) (y:bvl_v list). T) (\(x:clos_v) (y:bvl_v). T)
                    r1 r /\
                  clos_state_ffi (s1:(A,FFI)clos_state) = bvl_state_ffi (s:(B,FFI)bvl_state)`
      STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `result_rel (\(x:clos_v list) (y:bvl_v list). T) (\(x:clos_v) (y:bvl_v). T)
                     (FST ((E1:num -> (clos_v list,clos_v)result # (A,FFI)clos_state) k))
                     (FST ((E2:num -> (bvl_v list,bvl_v)result # (B,FFI)bvl_state) (k + ck)))` THEN
      UNDISCH_TAC `clos_state_ffi (SND ((E1:num -> (clos_v list,clos_v)result # (A,FFI)clos_state) k)) =
                   bvl_state_ffi (SND ((E2:num -> (bvl_v list,bvl_v)result # (B,FFI)bvl_state) (k + ck)))` THEN
      ASM_REWRITE_TAC[FST; SND] THEN MESON_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `r1:(clos_v list,clos_v)result`; `s1:(A,FFI)clos_state`;
                          `outcome:outcome`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`r1:(clos_v list,clos_v)result`; `r:(bvl_v list,bvl_v)result`;
                  `outcome:outcome`] C2BP3AUX_M_eq) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `r:(clos_v list,clos_v)result`
      (X_CHOOSE_THEN `s:(A,FFI)clos_state`
        (X_CHOOSE_THEN `outcome:outcome` STRIP_ASSUME_TAC)))) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC o SPEC `k:num` o
      check (fun th -> is_exists (snd (dest_forall (concl th))))) THEN
    MP_TAC(ISPEC `(E2:num -> (bvl_v list,bvl_v)result # (B,FFI)bvl_state) (k + ck)`
                 PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r2:(bvl_v list,bvl_v)result`
      (X_CHOOSE_THEN `s2:(B,FFI)bvl_state` ASSUME_TAC)) THEN
    SUBGOAL_THEN `result_rel (\(x:clos_v list) (y:bvl_v list). T) (\(x:clos_v) (y:bvl_v). T)
                    r r2 /\
                  clos_state_ffi (s:(A,FFI)clos_state) = bvl_state_ffi (s2:(B,FFI)bvl_state)`
      STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `result_rel (\(x:clos_v list) (y:bvl_v list). T) (\(x:clos_v) (y:bvl_v). T)
                     (FST ((E1:num -> (clos_v list,clos_v)result # (A,FFI)clos_state) k))
                     (FST ((E2:num -> (bvl_v list,bvl_v)result # (B,FFI)bvl_state) (k + ck)))` THEN
      UNDISCH_TAC `clos_state_ffi (SND ((E1:num -> (clos_v list,clos_v)result # (A,FFI)clos_state) k)) =
                   bvl_state_ffi (SND ((E2:num -> (bvl_v list,bvl_v)result # (B,FFI)bvl_state) (k + ck)))` THEN
      ASM_REWRITE_TAC[FST; SND] THEN MESON_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`k + ck:num`; `s2:(B,FFI)bvl_state`; `r2:(bvl_v list,bvl_v)result`;
                          `outcome:outcome`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`r:(clos_v list,clos_v)result`; `r2:(bvl_v list,bvl_v)result`;
                  `outcome:outcome`] C2BP3AUX_M_eq) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[]]);;

let C2BP3AUX_sem_eq = prove
 (`!(ffi:(FFI)ffi_state) max_app code1 (co1:num -> A # clos_prog) cc1 es1
     code2 (co2:num -> B # (num#num#bvl_exp)list) cc2 start.
     (!k. ~(FST (clos_evaluate (es1,[],clos_initial_state ffi max_app code1 co1 cc1 k)) =
            Rerr (Rabort Rtype_error))) /\
     (!k. ?ck. result_rel (\(x:clos_v list) (y:bvl_v list). T) (\(x:clos_v) (y:bvl_v). T)
                 (FST (clos_evaluate (es1,[],clos_initial_state ffi max_app code1 co1 cc1 k)))
                 (FST (bvl_evaluate ([bvl_Call 0 (SOME start) []],[],
                                     bvl_initial_state ffi code2 co2 cc2 (k + ck)))) /\
               clos_state_ffi (SND (clos_evaluate
                 (es1,[],clos_initial_state ffi max_app code1 co1 cc1 k))) =
               bvl_state_ffi (SND (bvl_evaluate ([bvl_Call 0 (SOME start) []],[],
                                     bvl_initial_state ffi code2 co2 cc2 (k + ck)))))
     ==> bvl_semantics ffi code2 co2 cc2 start =
         clos_semantics ffi max_app code1 co1 cc1 es1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. ~(FST (bvl_evaluate ([bvl_Call 0 (SOME start) []],[],
                         bvl_initial_state (ffi:(FFI)ffi_state) code2
                           (co2:num -> B # (num#num#bvl_exp)list) cc2 k)) =
                      Rerr (Rabort Rtype_error))` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `ck:num` MP_TAC o SPEC `k:num`) THEN
    MP_TAC(ISPECL [`[bvl_Call 0 (SOME start) []]`; `[]:bvl_v list`; `ffi:(FFI)ffi_state`;
                  `code2:(num#bvl_exp)spt`; `co2:num -> B # (num#num#bvl_exp)list`;
                  `cc2:B -> (num#num#bvl_exp)list -> (byte list # int64 list # B) option`;
                  `k:num`; `ck:num`] C2BP3AUX_bvl_init_add) THEN
    ASM_REWRITE_TAC[injectivity "result"; injectivity "error_result"; distinctness "abort"] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
    ASM_REWRITE_TAC[C2BP3AUX_result_rel_T; distinctness "result";
                    injectivity "result"; distinctness "error_result";
                    injectivity "error_result"] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\k. clos_evaluate (es1,[],clos_initial_state (ffi:(FFI)ffi_state)
                         max_app code1 (co1:num -> A # clos_prog) cc1 k)`;
                 `\k. bvl_evaluate ([bvl_Call 0 (SOME start) []],[],
                         bvl_initial_state (ffi:(FFI)ffi_state) code2
                           (co2:num -> B # (num#num#bvl_exp)list) cc2 k)`]
                C2BP3AUX_term_pred_eq) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[C2BP3AUX_bvl_init_add]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`\k. ffi_state_io_events (bvl_state_ffi (SND (bvl_evaluate
                         ([bvl_Call 0 (SOME start) []],[],
                          bvl_initial_state (ffi:(FFI)ffi_state) code2
                            (co2:num -> B # (num#num#bvl_exp)list) cc2 k))))`;
                 `\k. ffi_state_io_events (clos_state_ffi (SND (clos_evaluate
                         (es1,[],clos_initial_state (ffi:(FFI)ffi_state)
                            max_app code1 (co1:num -> A # clos_prog) cc1 k))))`]
                CLOSPROPSAUX_lub_eq) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CLOSPROPSAUX_init_mono; C2BP3AUX_bvl_init_mono] THEN
    CONJ_TAC THEN X_GEN_TAC `k:num` THENL
     [EXISTS_TAC `k:num` THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC o SPEC `k:num` o
        check (fun th -> is_exists (snd (dest_forall (concl th))))) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C2BP3AUX_bvl_init_mono THEN ARITH_TAC;
      FIRST_X_ASSUM(X_CHOOSE_THEN `ck:num` STRIP_ASSUME_TAC o SPEC `k:num` o
        check (fun th -> is_exists (snd (dest_forall (concl th))))) THEN
      EXISTS_TAC `k + ck:num` THEN ASM_REWRITE_TAC[IS_PREFIX_REFL]];
    DISCH_TAC] THEN
  REWRITE_TAC[clos_semantics_def; bvl_semantics_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM]);;

(* HOL4 line 6209 *)
let clos_to_bvlProof_IMP_semantics_eq = prove
 (`!(ffi:(FFI)ffi_state) max_app code1 (co1:num->C#clos_prog) cc1 es1 code2 co2 cc2 start rel.
     clos_to_bvlProof_eval_sim ffi max_app code1 co1 cc1 es1 code2 co2 cc2 start rel /\
     ~(clos_semantics ffi max_app code1 co1 cc1 es1 = Fail)
     ==> rel code1 co1 cc1 es1 code2 co2 cc2 start
     ==> bvl_semantics ffi code2 co2 cc2 start = clos_semantics ffi max_app code1 co1 cc1 es1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[clos_to_bvlProof_eval_sim_def; CLOSPROPSAUX_sem_fail; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN DISCH_TAC THEN MATCH_MP_TAC C2BP3AUX_sem_eq THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:num` THEN
  MP_TAC(ISPEC `clos_evaluate (es1,[],clos_initial_state (ffi:(FFI)ffi_state) max_app code1
                                (co1:num -> C # clos_prog) cc1 k)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s1:(C,FFI)clos_state` ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `r1:(clos_v list,clos_v)result`;
                                `s1:(C,FFI)clos_state`] o
    check (fun th -> is_imp (snd (strip_forall (concl th))))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN EXISTS_TAC `ck:num` THEN ASM_REWRITE_TAC[FST; SND]);;

(* HOL4 line 6362 (HOL4 tot + 1 - prev is (tot + 1) - prev) *)
let clos_to_bvlProof_init_code_def = cake_def
  `clos_to_bvlProof_init_code (code1:(num,num#clos_exp)fmap) (code2:(num#bvl_exp)spt)
     max_app <=>
     (!n. n < max_app
          ==> lookup (generic_app_fn_location n) code2 =
              SOME (n + 2,generate_generic_app max_app n)) /\
     (!tot prev.
        tot < max_app /\ prev < tot
        ==> lookup (partial_app_fn_location max_app tot prev) code2 =
            SOME ((tot + 1) - prev,generate_partial_app_closure_fn tot prev)) /\
     !name arity c.
       FLOOKUP code1 name = SOME (arity,c)
       ==> ?aux1 c2 aux2.
             clos_to_bvl_compile_exps max_app [c] aux1 = ([c2],aux2) /\
             lookup (name + num_stubs max_app) code2 = SOME (arity,c2) /\
             clos_to_bvlProof_code_installed aux2 code2`;;

(* HOL4 line 6380 (HOL4 Let None, Call None of closLang) *)
let chain_installed_def = cake_def
  `chain_installed start (es:clos_exp list) code <=>
     !i. i < LENGTH es
         ==> clos_find_code (start + i) ([]:clos_v list) code =
             SOME ([],if i + 1 < LENGTH es
                      then clos_Let backend_common_None [EL i es] (clos_Call backend_common_None 0 (start + i + 1) [])
                      else EL i es)`;;


(* HOL4 line 6388 *)
let chain_installed_cons = prove
 (`!start e es code.
     chain_installed start (CONS e es) code <=>
     clos_find_code start ([]:clos_v list) code =
       SOME ([],if es = [] then e else clos_Let backend_common_None [e] (clos_Call backend_common_None 0 (start + 1) [])) /\
     chain_installed (start + 1) es code`,
  REPEAT GEN_TAC THEN REWRITE_TAC[chain_installed_def; LENGTH] THEN
  SUBGOAL_THEN `0 + 1 < SUC (LENGTH (es:clos_exp list)) <=> ~(es = [])` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `start + SUC i = (start + 1) + i`;
              ARITH_RULE `start + SUC i + 1 = (start + 1) + i + 1`;
              ARITH_RULE `SUC i + 1 < SUC n <=> i + 1 < n`] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
      ASM_REWRITE_TAC[LT_0; ADD_CLAUSES; EL; HD; COND_SWAP];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `SUC i`) THEN
      ASM_REWRITE_TAC[LT_SUC; EL; TL] THEN
      REWRITE_TAC[ARITH_RULE `start + SUC i = (start + 1) + i`;
                  ARITH_RULE `start + SUC i + 1 = (start + 1) + i + 1`;
                  ARITH_RULE `SUC i + 1 < SUC n <=> i + 1 < n`]];
    STRIP_TAC THEN X_GEN_TAC `i:num` THEN
    STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THENL
     [ASM_REWRITE_TAC[ADD_CLAUSES; EL; HD; LT_0; COND_SWAP];
      REWRITE_TAC[LT_SUC; EL; TL] THEN
      REWRITE_TAC[ARITH_RULE `start + SUC i = (start + 1) + i`;
                  ARITH_RULE `start + SUC i + 1 = (start + 1) + i + 1`;
                  ARITH_RULE `SUC i + 1 < SUC n <=> i + 1 < n`] THEN
      ASM_REWRITE_TAC[]]]);;

(* HOL4 line 6399 *)
let chain_installed_SUBMAP = prove
 (`!start es code code'.
     chain_installed start es code /\ code SUBMAP code' ==> chain_installed start es code'`,
  REWRITE_TAC[chain_installed_def; clos_find_code_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`code:(num,num#clos_exp)fmap`; `code':(num,num#clos_exp)fmap`;
                 `start + i:num`] FLOOKUP_SUBMAP) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`FLOOKUP (code:(num,num#clos_exp)fmap) (start + i)`,`x:(num#clos_exp)option`) THEN
  GEN_TAC THEN CASES_ON `x:(num#clos_exp)option` THEN CAKE_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `a:num#clos_exp`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[]);;

let C2BP3AUX_K_o_K = prove
 (`!(a:A) (b:A). (combin_K a o (combin_K b:B->A)) = (combin_K a:B->A)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; K_THM]);;

(* HOL4 line 6411 (HOL4's unused binder code is left out) *)
let chain_installed_thm = prove
 (`!es start. ?e. !(st:(C,FFI)clos_state) res st'.
     chain_installed start es (clos_state_code st) /\
     clos_evaluate (es,[],st) = (res,st') /\
     0 < LENGTH es
     ==> ?k res1 st1.
           clos_find_code start ([]:clos_v list) (clos_state_code st) = SOME ([],e) /\
           clos_evaluate ([e],[],clos_state_clock_fupd (combin_K (clos_state_clock st + k)) st) =
             (res1,st1) /\
           result_rel (\x y. T) (\x y. T) res1 res /\
           clos_state_ffi st' = clos_state_ffi st1`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH; LT_REFL]; ALL_TAC] THEN
  X_GEN_TAC `start:num` THEN REWRITE_TAC[chain_installed_cons] THEN
  ASM_CASES_TAC `t:clos_exp list = []` THENL
   [EXISTS_TAC `h:clos_exp` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`0`; `res:(clos_v list,clos_v)result`; `st':(C,FFI)clos_state`] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock; CLOSPROPSAUX_result_rel_T_refl];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `e1:clos_exp` o SPEC `start + 1`) THEN
  EXISTS_TAC `clos_Let backend_common_None [h]
                (clos_Call backend_common_None 0 (start + 1) [])` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `clos_evaluate ([h],[],st:(C,FFI)clos_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s2:(C,FFI)clos_state` ASSUME_TAC)) THEN
  UNDISCH_TAC `clos_evaluate (CONS h t,[],st:(C,FFI)clos_state) = (res,st')` THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [clos_evaluate_CONS] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_evaluate_def] THEN
  CASES_ON `r1:(clos_v list,clos_v)result` THEN CAKE_REWRITE_TAC[] THENL
   [MP_TAC(ISPEC `clos_evaluate (t,[],s2:(C,FFI)clos_state)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r2:(clos_v list,clos_v)result`
      (X_CHOOSE_THEN `s1:(C,FFI)clos_state` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `chain_installed (start + 1) t (clos_state_code (s2:(C,FFI)clos_state))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC chain_installed_SUBMAP THEN
      EXISTS_TAC `clos_state_code (st:(C,FFI)clos_state)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC clos_evaluate_mono THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s2:(C,FFI)clos_state`; `r2:(clos_v list,clos_v)result`;
                                  `s1:(C,FFI)clos_state`] o
      check (fun th -> is_forall (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(t:clos_exp list = [])` THEN
      REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `res1:(clos_v list,clos_v)result`
      (X_CHOOSE_THEN `st1:(C,FFI)clos_state` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `k + 1` THEN
    MP_TAC(SPECL [`[h:clos_exp]`; `[]:clos_v list`; `st:(C,FFI)clos_state`;
                  `Rval a:(clos_v list,clos_v)result`; `s2:(C,FFI)clos_state`]
                 clos_evaluate_add_clock) THEN
    ASM_REWRITE_TAC[distinctness "result"] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM; clos_dec_clock_def;
                    clos_state_INFO.ri_fupdfupds] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `~(c + k + 1 < 0 + 1)`;
                ARITH_RULE `(c + k + 1) - (0 + 1) = c + k`] THEN
    REWRITE_TAC[C2BP3AUX_K_o_K] THEN
    MAP_EVERY EXISTS_TAC [`res1:(clos_v list,clos_v)result`; `st1:(C,FFI)clos_state`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `result_rel (\(x:clos_v list) (y:clos_v list). T) (\(x:clos_v) (y:clos_v). T)
                   res1 r2` THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `(res:(clos_v list,clos_v)result,st':(C,FFI)clos_state)`)) THEN
    CASES_ON `r2:(clos_v list,clos_v)result` THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    ASM_REWRITE_TAC[CLOSPROPSAUX_result_rel_T] THEN
    REWRITE_TAC[injectivity "result"; distinctness "result"] THEN MESON_TAC[];
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ADD_CLAUSES; clos_with_same_clock] THEN
    CAKE_REWRITE_TAC[] THEN MESON_TAC[CLOSPROPSAUX_result_rel_T_refl]]);;


(* HOL4 line 6455 *)
let chain_installed_chain_exps = prove
 (`!start es. chain_installed start es (alist_to_fmap (chain_exps start es))`,
  MATCH_MP_TAC chain_exps_ind THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[chain_installed_def; LENGTH; LT];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[chain_installed_def; chain_exps_def; LENGTH; alist_to_fmap_thm] THEN
    REWRITE_TAC[ARITH_RULE `i < SUC 0 <=> i = 0`] THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[clos_find_code_def; FLOOKUP_UPDATE; ADD_CLAUSES; EL; HD; LENGTH] THEN
    CAKE_REWRITE_TAC[] THEN ARITH_TAC;
    REPEAT GEN_TAC THEN REWRITE_TAC[chain_exps_def; alist_to_fmap_thm] THEN
    REWRITE_TAC[chain_installed_def] THEN DISCH_TAC THEN
    X_GEN_TAC `z:num` THEN STRUCT_CASES_TAC(SPEC `z:num` num_CASES) THENL
     [REWRITE_TAC[clos_find_code_def; FLOOKUP_UPDATE; ADD_CLAUSES; EL; HD; LENGTH] THEN
      CAKE_REWRITE_TAC[] THEN REWRITE_TAC[ARITH_RULE `1 < SUC (SUC n)`];
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
      REWRITE_TAC[LENGTH; LT_SUC] THEN
      REWRITE_TAC[EL; TL; clos_find_code_def; FLOOKUP_UPDATE;
                  ARITH_RULE `~(i = i + SUC n)`; ARITH_RULE `i + SUC n = (i + 1) + n`;
                  ARITH_RULE `SUC n + 1 < SUC m <=> n + 1 < m`;
                  ARITH_RULE `i + SUC n + 1 = (i + 1) + n + 1`]]]);;

let C2BP3AUX_find_code_nil = prove
 (`!p (code:(num,num#clos_exp)fmap) e.
     clos_find_code p ([]:clos_v list) code = SOME ([],e) <=> FLOOKUP code p = SOME (0,e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_find_code_def] THEN
  CASES_ON `FLOOKUP (code:(num,num#clos_exp)fmap) p` THEN CAKE_REWRITE_TAC[] THEN
  CASES_ON `a:num#clos_exp` THEN CAKE_REWRITE_TAC[LENGTH] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[injectivity "option"; distinctness "option"; PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 6470 (HOL4 $< is (<), alist_to_fmap ... FUNION code) *)
let chain_exps_semantics = prove
 (`!(ffi:(FFI)ffi_state) max_app code (co:num->C#clos_prog) cc es start.
     ~(clos_semantics ffi max_app code co cc es = Fail) /\
     DISJOINT (IMAGE ((+) start) (pred_set_count (LENGTH es))) (FDOM code) /\
     oracle_monotonic (set_of_list o MAP FST o SND o SND) (<)
       (IMAGE ((+) start) (pred_set_count (LENGTH es)) UNION FDOM code) co
     ==> ?e. clos_semantics ffi max_app (FUNION (alist_to_fmap (chain_exps start es)) code)
               co cc [e] =
             clos_semantics ffi max_app code co cc es /\
             ALOOKUP (chain_exps start es) start = SOME (0,e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `es:clos_exp list = []` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    EXISTS_TAC `clos_Op backend_common_None (IntOp (clos_Const (&0))) []` THEN
    REWRITE_TAC[chain_exps_def; ALOOKUP_THM] THEN
    MATCH_MP_TAC CLOSPROPSAUX_sem_eq THEN
    REWRITE_TAC[clos_evaluate_def; CLOSP1AUX_num_eval_const; FST; SND; distinctness "result"] THEN
    GEN_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[CLOSPROPSAUX_result_rel_T; ADD_CLAUSES; injectivity "result";
                distinctness "result"] THEN
    REWRITE_TAC[clos_initial_state_def; clos_state_INFO.ri_accessors] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `0 < LENGTH (es:clos_exp list)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LT_NZ; LENGTH_EQ_NIL]; ALL_TAC] THEN
  MP_TAC(SPECL [`es:clos_exp list`; `start:num`] chain_installed_thm) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:clos_exp` (LABEL_TAC "chain")) THEN
  EXISTS_TAC `e:clos_exp` THEN
  SUBGOAL_THEN `FDOM (alist_to_fmap (chain_exps start es)) =
                IMAGE ((+) start) (pred_set_count (LENGTH (es:clos_exp list)))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FDOM_alist_to_fmap; MAP_FST_chain_exps] THEN
    REWRITE_TAC[SET_OF_LIST_MAP; COUNT_LIST_COUNT];
    ALL_TAC] THEN
  SUBGOAL_THEN `chain_installed start es
                  (FUNION (alist_to_fmap (chain_exps start es)) (code:(num,num#clos_exp)fmap))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC chain_installed_SUBMAP THEN
    EXISTS_TAC `alist_to_fmap (chain_exps start es)` THEN
    REWRITE_TAC[chain_installed_chain_exps; SUBMAP_FUNION_ID];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `!k. ~(FST (clos_evaluate (es,[],clos_initial_state (ffi:(FFI)ffi_state)
                           max_app code (co:num->C#clos_prog) cc k)) = Rerr (Rabort Rtype_error))`
      (LABEL_TAC "nofail") THENL
     [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[CLOSPROPSAUX_sem_fail; NOT_EXISTS_THM] o
        check (fun th -> can (find_term ((=) `Fail`)) (concl th))) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CLOSPROPSAUX_sem_eq THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN
    MP_TAC(ISPEC `clos_evaluate (es,[],clos_initial_state (ffi:(FFI)ffi_state) max_app code
                                   (co:num->C#clos_prog) cc k)` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:(clos_v list,clos_v)result`
      (X_CHOOSE_THEN `s1:(C,FFI)clos_state` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[FST; SND] THEN
    SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` ASSUME_TAC THENL
     [REMOVE_THEN "nofail" (MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[FST];
      ALL_TAC] THEN
    SUBGOAL_THEN `SUBMAP_rel (clos_initial_state (ffi:(FFI)ffi_state) max_app code
                                (co:num->C#clos_prog) cc k)
                    (clos_initial_state ffi max_app
                       (FUNION (alist_to_fmap (chain_exps start es)) code) co cc k)`
      ASSUME_TAC THENL
     [REWRITE_TAC[SUBMAP_rel_def; clos_initial_state_def; clos_state_INFO.ri_accessors;
                  clos_state_INFO.ri_fupds; K_THM] THEN
      ASM_REWRITE_TAC[FDOM_FUNION] THEN MATCH_MP_TAC(CONJUNCT2 SUBMAP_FUNION_ID) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(es:clos_exp list,[]:clos_v list,
                     clos_initial_state (ffi:(FFI)ffi_state) max_app code
                       (co:num->C#clos_prog) cc k)`;
                   `es:clos_exp list`; `[]:clos_v list`;
                   `clos_initial_state (ffi:(FFI)ffi_state) max_app code
                      (co:num->C#clos_prog) cc k`;
                   `r1:(clos_v list,clos_v)result`; `s1:(C,FFI)clos_state`;
                   `s1:(C,FFI)clos_state`;
                   `clos_initial_state (ffi:(FFI)ffi_state) max_app
                      (FUNION (alist_to_fmap (chain_exps start es)) code)
                      (co:num->C#clos_prog) cc k`]
                  (CONJUNCT1 evaluate_code_SUBMAP)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s2:(C,FFI)clos_state` STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "chain" (MP_TAC o SPECL
      [`clos_initial_state (ffi:(FFI)ffi_state) max_app
          (FUNION (alist_to_fmap (chain_exps start es)) code) (co:num->C#clos_prog) cc k`;
       `r1:(clos_v list,clos_v)result`; `s2:(C,FFI)clos_state`]) THEN
    ASM_REWRITE_TAC[clos_initial_state_def; clos_state_INFO.ri_accessors] THEN
    REWRITE_TAC[GSYM clos_initial_state_def] THEN
    DISCH_THEN(X_CHOOSE_THEN `k':num` (X_CHOOSE_THEN `res1:(clos_v list,clos_v)result`
      (X_CHOOSE_THEN `st1:(C,FFI)clos_state` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `k':num` THEN
    SUBGOAL_THEN `clos_state_clock_fupd (combin_K (k + k'))
                    (clos_initial_state (ffi:(FFI)ffi_state) max_app
                       (FUNION (alist_to_fmap (chain_exps start es)) code)
                       (co:num->C#clos_prog) cc k) =
                  clos_initial_state ffi max_app
                    (FUNION (alist_to_fmap (chain_exps start es)) code) co cc (k + k')`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[clos_initial_state_def; clos_state_INFO.ri_fupds; K_THM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[FST; SND] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[SUBMAP_rel_def] o
      check (fun th ->
        can (find_term ((=) `SUBMAP_rel:(C,FFI)clos_state->(C,FFI)clos_state->bool`))
          (concl th) &&
        can (find_term ((=) `s2:(C,FFI)clos_state`)) (concl th))) THEN
    STRIP_TAC THEN
    UNDISCH_TAC `clos_state_ffi (s2:(C,FFI)clos_state) = clos_state_ffi (st1:(C,FFI)clos_state)` THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      is_eq (concl th) && lhs (concl th) = `s2:(C,FFI)clos_state`)) THEN
    REWRITE_TAC[clos_state_INFO.ri_accfupds] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `result_rel (\(x:clos_v list) (y:clos_v list). T) (\(x:clos_v) (y:clos_v). T)
                   res1 r1` THEN
    REWRITE_TAC[CLOSPROPSAUX_result_rel_T] THEN MESON_TAC[];
    REMOVE_THEN "chain" (MP_TAC o SPECL
      [`clos_state_code_fupd (combin_K (alist_to_fmap (chain_exps start es))) (ARB:(C,FFI)clos_state)`;
       `FST (clos_evaluate (es,[],clos_state_code_fupd (combin_K (alist_to_fmap (chain_exps start es)))
                                     (ARB:(C,FFI)clos_state)))`;
       `SND (clos_evaluate (es,[],clos_state_code_fupd (combin_K (alist_to_fmap (chain_exps start es)))
                                     (ARB:(C,FFI)clos_state)))`]) THEN
    ASM_REWRITE_TAC[clos_state_INFO.ri_accfupds; K_THM; chain_installed_chain_exps; PAIR] THEN
    REWRITE_TAC[C2BP3AUX_find_code_nil; ALOOKUP_EQ_FLOOKUP] THEN MESON_TAC[]]);;

(* HOL4 line 6545 *)
let chain_exps_semantics_call = prove
 (`!(ffi:(FFI)ffi_state) max_app code (co:num->C#clos_prog) cc es start.
     ~(clos_semantics ffi max_app code co cc es = Fail) /\
     DISJOINT (IMAGE ((+) start) (pred_set_count (LENGTH es))) (FDOM code) /\
     oracle_monotonic (set_of_list o MAP FST o SND o SND) (<)
       (IMAGE ((+) start) (pred_set_count (LENGTH es)) UNION FDOM code) co
     ==> clos_semantics ffi max_app (FUNION (alist_to_fmap (chain_exps start es)) code) co cc
           [clos_Call backend_common_None 0 start []] =
         clos_semantics ffi max_app code co cc es`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP chain_exps_semantics) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:clos_exp` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(clos_semantics (ffi:(FFI)ffi_state) max_app
                    (FUNION (alist_to_fmap (chain_exps start es)) code)
                    (co:num->C#clos_prog) cc [e] = Fail)` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CLOSPROPSAUX_sem_fail; NOT_EXISTS_THM] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
    can (find_term ((=) `[e:clos_exp]`)) (concl th))) THEN
  MATCH_MP_TAC CLOSPROPSAUX_sem_eq THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `clos_find_code start ([]:clos_v list)
                  (FUNION (alist_to_fmap (chain_exps start es))
                     (code:(num,num#clos_exp)fmap)) = SOME ([],e)` ASSUME_TAC THENL
   [REWRITE_TAC[C2BP3AUX_find_code_nil] THEN
    ASM_REWRITE_TAC[FLOOKUP_FUNION; ALOOKUP_EQ_FLOOKUP] THEN CAKE_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN EXISTS_TAC `1` THEN
  REWRITE_TAC[clos_evaluate_def] THEN CAKE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[clos_initial_state_def; clos_state_INFO.ri_accessors] THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `~(k + 1 < 0 + 1)`; clos_dec_clock_def; clos_state_INFO.ri_accessors;
              clos_state_INFO.ri_fupds; K_THM; ARITH_RULE `(k + 1) - (0 + 1) = k`] THEN
  REWRITE_TAC[CLOSPROPSAUX_result_rel_T_refl]);;

(* HOL4 line 6634 *)
let kcompile_csyntax_ok = prove
 (`!kc es x y.
     clos_known_compile kc es = (x,y)
     ==> clos_callProof_syntax_ok es
     ==> clos_callProof_syntax_ok y`,
  GEN_TAC THEN CASES_ON `kc:(clos_known_config)option` THEN
  REWRITE_TAC[clos_known_compile_def; PAIR_EQ] THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF; clos_fvs_compile_def] THEN
  MP_TAC(ISPEC `clos_known_known a (remove_fvs 0 es) [] LN` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `es1:(clos_exp#val_approx)list`
    (X_CHOOSE_THEN `g:(val_approx)spt` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[clos_callProof_syntax_ok_def; let_op_every_Fn_SOME; let_op_every_Fn_vs_NONE;
              remove_ticks_every_Fn_SOME; remove_ticks_every_Fn_vs_NONE;
              code_locs_let_op; code_locs_remove_ticks] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`a:clos_known_config`; `remove_fvs 0 es`; `[]:val_approx list`;
                 `LN:(val_approx)spt`] known_every_Fn_SOME) THEN
  MP_TAC(ISPECL [`a:clos_known_config`; `remove_fvs 0 es`; `[]:val_approx list`;
                 `LN:(val_approx)spt`] known_every_Fn_vs_NONE) THEN
  MP_TAC(ISPECL [`a:clos_known_config`; `remove_fvs 0 es`; `[]:val_approx list`;
                 `LN:(val_approx)spt`; `es1:(clos_exp#val_approx)list`; `g:(val_approx)spt`]
                known_code_locs_bag) THEN
  ASM_REWRITE_TAC[remove_fvs_every_Fn_SOME; remove_fvs_every_Fn_vs_NONE; ALL; FST; SND;
                  globals_approx_every_Fn_SOME_def; globals_approx_every_Fn_vs_NONE_def;
                  lookup_def; distinctness "option"; code_locs_remove_fvs] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM LIST_TO_BAG_DISTINCT] THEN MATCH_MP_TAC BAG_ALL_DISTINCT_SUB_BAG THEN
  EXISTS_TAC `LIST_TO_BAG (code_locs (es:clos_exp list))` THEN
  ASM_REWRITE_TAC[LIST_TO_BAG_DISTINCT]);;

let C2BP3AUX_fv_ALL2 = prove
 (`!xs ys. ALL2 (\e1 e2. !v. clos_fv1 v e1 <=> clos_fv1 v e2) xs ys ==> !v. clos_fv v xs <=> clos_fv v ys`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; fv_exists; EX] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `t':clos_exp list`) THEN
  ASM_REWRITE_TAC[fv_exists] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let C2BP3AUX_fv_letrec = prove
 (CASE_TERM `!(fns:(num#clos_exp)list) fns' (f:num->num).
     ALL2 (\e1 e2. !v. clos_fv1 v e1 <=> clos_fv1 v e2) fns' (MAP SND fns) ==>
     (EX (\p. match p with (a,x) -> clos_fv1 (f a) x) (ZIP (MAP FST fns) fns') <=>
      EX (\p. match p with (a,x) -> clos_fv1 (f a) x) fns)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; MAP; ZIP; EX] THEN
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t':clos_exp list`; `f:num->num`] o
    check (fun th -> can (find_term ((=) `t:(num#clos_exp)list`)) (concl th) &&
                     not (can (find_term ((=) `h:num#clos_exp`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `!v. clos_fv1 v h' <=> clos_fv1 v (SND (h:num#clos_exp))` THEN
  SPEC_TAC(`h:num#clos_exp`,`h:num#clos_exp`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CAKE_REWRITE_TAC[FST; SND] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 6660 (HOL4's unused outer binder v of the first conjunct is    *)
(* left out) *)
let renumber_code_locs_fv1 = prove
 (`(!n es. ALL2 (\e1 e2. !v. clos_fv1 v e1 <=> clos_fv1 v e2)
               (SND (renumber_code_locs_list n es)) es) /\
   (!n e v. clos_fv1 v (SND (renumber_code_locs n e)) <=> clos_fv1 v e)`,
  CLOSP1AUX_NUM_IND_TAC THEN
  (fun (asl,w as gl) ->
     MAP_EVERY ASSUME_TAC (mapfilter (fun (_,th) -> MATCH_MP C2BP3AUX_fv_ALL2 th) asl) gl) THEN
  REWRITE_TAC[ALL2] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[fv1_thm] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH (ZIP (MAP FST (fns:(num#clos_exp)list)) (fns':clos_exp list)) =
                LENGTH fns'` SUBST1_TAC THENL
   [MATCH_MP_TAC LENGTH_ZIP THEN ASM_REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  X_GEN_TAC `v:num` THEN
  MP_TAC(SPECL [`fns:(num#clos_exp)list`; `fns':clos_exp list`;
                `\a. (v + a) + LENGTH (fns':clos_exp list)`] C2BP3AUX_fv_letrec) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* HOL4 line 6679 *)
let renumber_code_locs_list_fv = prove
 (`!n es k es' x. renumber_code_locs_list n es = (k,es') ==> (clos_fv x es' <=> clos_fv x es)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `es:clos_exp list`] (CONJUNCT1 renumber_code_locs_fv1)) THEN
  ASM_REWRITE_TAC[SND] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP C2BP3AUX_fv_ALL2 th]));;

(* HOL4 line 6689 *)
let set_globals_SND_renumber_code_locs = prove
 (`!x y. clos_set_globals (SND (renumber_code_locs x y)) = clos_set_globals y`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC (CONJUNCT2 renumber_code_locs_elist_globals) THEN
  MAP_EVERY EXISTS_TAC [`x:num`; `FST (renumber_code_locs x y)`] THEN REWRITE_TAC[PAIR]);;

(* HOL4 line 6695 (HOL4 FOLDR f e l is ITLIST f l e; the empty bag is      *)
(* EMPTY_BAG) *)
let elist_globals_FLAT = prove
 (`!ls. clos_elist_globals (FLAT ls) = ITLIST BAG_UNION (MAP clos_elist_globals ls) EMPTY_BAG`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[FLAT; MAP; ITLIST; clos_set_globals_def; clos_elist_globals_append]);;

(* HOL4 line 6705 *)
let elist_globals_SND_renumber_code_locs_list = prove
 (`!x y. clos_elist_globals (SND (renumber_code_locs_list x y)) = clos_elist_globals y`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC (CONJUNCT1 renumber_code_locs_elist_globals) THEN
  MAP_EVERY EXISTS_TAC [`x:num`; `FST (renumber_code_locs_list x y)`] THEN REWRITE_TAC[PAIR]);;

(* HOL4 line 6711 *)
let elist_globals_SND_ncompile_inc = prove
 (`!x y. clos_elist_globals (SND (clos_number_compile_inc x y)) = clos_elist_globals y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_number_compile_inc_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  MP_TAC(SPECL [`make_even (x + MAX (LENGTH (y:clos_exp list)) 1)`; `y:clos_exp list`]
                elist_globals_SND_renumber_code_locs_list) THEN
  SPEC_TAC(`renumber_code_locs_list (make_even (x + MAX (LENGTH (y:clos_exp list)) 1)) y`,
           `p:num#clos_exp list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN CAKE_REWRITE_TAC[SND] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> REWRITE_TAC[clos_set_globals_def; clos_op_gbag_def; BAG_UNION_EMPTY; th]));;

let _ = cake_add_simps [elist_globals_SND_ncompile_inc];;

(* HOL4 line 6717 *)
let collect_apps_fv1 = prove
 (`!x y z v.
     clos_fv v (FST (collect_apps x y z)) \/ clos_fv1 v (SND (collect_apps x y z)) <=> clos_fv v y \/ clos_fv1 v z`,
  MATCH_MP_TAC collect_apps_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[collect_apps_def; FST; SND] THEN
  DISCH_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[FST; SND; fv1_thm; fv_append] THEN MESON_TAC[]);;

(* HOL4 line 6726 *)
let collect_args_fv1 = prove
 (`!m n e n' e' v. collect_args m n e = (n',e') ==> (clos_fv1 (n' + v) e' <=> clos_fv1 (n + v) e)`,
  MATCH_MP_TAC collect_args_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[collect_args_def; PAIR_EQ] THEN
  TRY(REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  DISCH_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n':num`; `e':clos_exp`; `v:num`]) THEN
    ASM_REWRITE_TAC[fv1_thm] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ARITH_RULE `(a + v) + b = (a + b) + v:num`];
    REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]]);;

let C2BP3AUX_MATCH_EQ_ASSUMS_TAC : thm_tactic = fun eq ->
  RULE_ASSUM_TAC(fun th -> try MATCH_MP th eq with Failure _ -> th);;

let C2BP3AUX_ALL2_intro_multi_sing = prove
 (`!(R:clos_exp->clos_exp->bool) max_app e.
     ALL2 R (intro_multi max_app [e]) [e] <=> R (HD (intro_multi max_app [e])) e`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM (GEN_ALL HD_intro_multi)] THEN REWRITE_TAC[ALL2; HD]);;

let C2BP3AUX_mti_letrec_EX = prove
 (CASE_TERM `!funs max_app v L.
     (!num_args e' num_args' e''.
        MEM (num_args,e') funs /\ collect_args max_app num_args e' = (num_args',e'')
        ==> !v. clos_fv1 v (HD (intro_multi max_app [e''])) <=> clos_fv1 v e'')
     ==> (EX (\p. match p with (num_args,x) -> clos_fv1 ((v + num_args) + L) x)
            (MAP (\p. match p with
                        (num_args,e) ->
                          (match collect_args max_app num_args e with
                             (num_args',e') -> (num_args',HD (intro_multi max_app [e']))))
                 funs) <=>
          EX (\p. match p with (num_args,x) -> clos_fv1 ((v + num_args) + L) x) funs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; EX; MEM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`max_app:num`; `v:num`; `L:num`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPEC `h:num#clos_exp` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `na:num` (X_CHOOSE_THEN `e0:clos_exp` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `collect_args max_app na e0` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `na':num` (X_CHOOSE_THEN `e0':clos_exp` ASSUME_TAC)) THEN
  CAKE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`na:num`; `e0:clos_exp`; `na':num`; `e0':clos_exp`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(SPECL [`max_app:num`; `na:num`; `e0:clos_exp`; `na':num`; `e0':clos_exp`;
                `v + L:num`] collect_args_fv1) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `(v + na) + L = na + v + L:num`]);;

(* HOL4 line 6736 *)
let intro_multi_fv1 = prove
 (`!max_app es. ALL2 (\e1 e2. !v. clos_fv1 v e1 <=> clos_fv1 v e2) (intro_multi max_app es) es`,
  MATCH_MP_TAC intro_multi_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[intro_multi_def] THEN
  REWRITE_TAC[C2BP3AUX_ALL2_intro_multi_sing; ALL2] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(BETA_RULE o REWRITE_RULE[C2BP3AUX_ALL2_intro_multi_sing]) THEN
  (fun (asl,w as gl) ->
     MAP_EVERY ASSUME_TAC (mapfilter (fun (_,th) -> MATCH_MP C2BP3AUX_fv_ALL2 th) asl) gl) THEN
  REWRITE_TAC[fv1_thm; intro_multi_length; LENGTH_MAP] THEN ASM_REWRITE_TAC[] THEN
  FIRST
   [W(fun (asl,w) -> if CLOS2AUX_CONST_IN "collect_apps" w then ALL_TAC else NO_TAC) THEN
    MP_TAC(ISPEC `collect_apps max_app es e` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `es':clos_exp list` (X_CHOOSE_THEN `e':clos_exp` ASSUME_TAC)) THEN
    FIRST_ASSUM C2BP3AUX_MATCH_EQ_ASSUMS_TAC THEN
    (fun (asl,w as gl) ->
       MAP_EVERY ASSUME_TAC (mapfilter (fun (_,th) -> MATCH_MP C2BP3AUX_fv_ALL2 th) asl) gl) THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[ALL2] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC[fv1_thm] THEN X_GEN_TAC `v:num` THEN
    MP_TAC(SPECL [`max_app:num`; `es:clos_exp list`; `e:clos_exp`; `v:num`]
                 collect_apps_fv1) THEN
    ASM_REWRITE_TAC[FST; SND] THEN MESON_TAC[];
    W(fun (asl,w) -> if CLOS2AUX_CONST_IN "Fn" w then ALL_TAC else NO_TAC) THEN
    MP_TAC(ISPEC `collect_args max_app num_args e` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `na':num` (X_CHOOSE_THEN `e':clos_exp` ASSUME_TAC)) THEN
    FIRST_ASSUM C2BP3AUX_MATCH_EQ_ASSUMS_TAC THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[ALL2] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC[fv1_thm] THEN X_GEN_TAC `v:num` THEN
    MP_TAC(SPECL [`max_app:num`; `num_args:num`; `e:clos_exp`; `na':num`; `e':clos_exp`;
                  `v:num`] collect_args_fv1) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[th]);
    MP_TAC(SPECL [`funs:(num#clos_exp)list`; `max_app:num`] C2BP3AUX_mti_letrec_EX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

(* HOL4 line 6788 *)
let compile_elist_globals = prove
 (`!do_mti max_app es.
     clos_elist_globals (clos_mti_compile do_mti max_app es) = clos_elist_globals es`,
  GEN_TAC THEN CASES_ON `do_mti:bool` THEN
  REWRITE_TAC[clos_mti_compile_def; intro_multi_preserves_elist_globals]);;

(* HOL4 line 6795 *)
let mcompile_inc_uncurry = prove
 (`!max_app (p:clos_prog).
     (clos_mti_compile_inc max_app p:clos_prog) = (intro_multi max_app (FST p),[])`,
  REWRITE_TAC[FORALL_PAIR_THM; clos_mti_compile_inc_def; FST]);;

let C2BP3AUX_pair_CASE_FST_SND = prove
 (CASE_TERM `!(p:A#B) (f:A->B->C). (match p with (x,y) -> f x y) = f (FST p) (SND p)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN CAKE_REWRITE_TAC[FST; SND]);;

(* HOL4 line 6801 *)
let kcompile_inc_uncurry = prove
 (`!c g (p:clos_exp list#A).
     clos_known_compile_inc c g p =
     (SND (clos_known_known (reset_inline_factor c) (FST p) [] g),
      MAP FST (FST (clos_known_known (reset_inline_factor c) (FST p) [] g)),
      SND p)`,
  REWRITE_TAC[FORALL_PAIR_THM; clos_known_compile_inc_def; FST; SND] THEN
  REWRITE_TAC[C2BP3AUX_pair_CASE_FST_SND]);;

(* HOL4 line 6811 *)
let acompile_inc_uncurry = prove
 (`!(p:clos_prog).
     clos_annotate_compile_inc p =
     (clos_annotate_annotate 0 (FST p),clos_annotate_compile (SND p))`,
  REWRITE_TAC[FORALL_PAIR_THM; clos_annotate_compile_inc_def; FST; SND]);;

(* HOL4 line 6818 *)
let ccompile_inc_uncurry = prove
 (`!g (p:clos_prog).
     clos_call_compile_inc g p =
     (FST (SND (clos_call_calls (FST p) (g,[]))),
      FST (clos_call_calls (FST p) (g,[])),
      SND (SND (clos_call_calls (FST p) (g,[]))))`,
  REWRITE_TAC[FORALL_PAIR_THM; clos_call_compile_inc_def; FST; SND] THEN
  REWRITE_TAC[C2BP3AUX_pair_CASE_FST_SND]);;

(* HOL4 line 6828 *)
let compile_inc_uncurry = prove
 (`!max_app (p:clos_prog).
     clos_to_bvl_compile_inc' max_app p =
     clos_to_bvl_compile_prog max_app
       (APPEND (chain_exps (FST (extract_name (FST p))) (SND (extract_name (FST p)))) (SND p))`,
  REWRITE_TAC[FORALL_PAIR_THM; clos_to_bvl_compile_inc'_def; FST; SND] THEN
  REWRITE_TAC[C2BP3AUX_pair_CASE_FST_SND]);;

(* HOL4 line 6836 *)
let fcompile_inc_uncurry = prove
 (`!(p:clos_prog). (clos_fvs_compile_inc p:clos_prog) = (clos_fvs_compile (FST p),[])`,
  REWRITE_TAC[FORALL_PAIR_THM; clos_fvs_compile_inc_def; FST]);;

(* HOL4 line 6842 *)
let elist_globals_sing = prove
 (`!x. clos_elist_globals [x] = clos_set_globals x`,
  REWRITE_TAC[clos_set_globals_def; BAG_UNION_EMPTY]);;

(* HOL4 line 6848 *)
let set_globals_HD_intro_multi = prove
 (`!x y. clos_set_globals (HD (intro_multi x [y])) = clos_set_globals y`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`x:num`; `[y:clos_exp]`] intro_multi_preserves_elist_globals) THEN
  ONCE_REWRITE_TAC[GSYM (GEN_ALL HD_intro_multi)] THEN
  REWRITE_TAC[elist_globals_sing; HD]);;

(* HOL4 line 6858 *)
let renumber_code_locs_list_csyntax_ok = prove
 (`!n es k es'.
     renumber_code_locs_list n es = (k,es') /\ every_Fn_vs_NONE es
     ==> clos_callProof_syntax_ok es'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[clos_callProof_syntax_ok_def] THEN
  MP_TAC(SPECL [`n:num`; `es:clos_exp list`] renumber_code_locs_list_distinct) THEN
  MP_TAC(SPECL [`n:num`; `es:clos_exp list`] (CONJUNCT1 renumber_code_locs_every_Fn_SOME)) THEN
  MP_TAC(SPECL [`n:num`; `es:clos_exp list`] (CONJUNCT1 renumber_code_locs_every_Fn_vs_NONE)) THEN
  ASM_REWRITE_TAC[SND] THEN SIMP_TAC[]);;

(* HOL4 line 6873 *)
let compile_every_Fn_vs_NONE = prove
 (`!do_mti max_app es.
     every_Fn_vs_NONE (clos_mti_compile do_mti max_app es) <=> every_Fn_vs_NONE es`,
  GEN_TAC THEN CASES_ON `do_mti:bool` THEN
  REWRITE_TAC[clos_mti_compile_def; every_Fn_vs_NONE_intro_multi]);;

let _ = cake_add_simps [compile_every_Fn_vs_NONE];;

(* HOL4 line 6880 *)
let compile_code_locs_ALL_DISTINCT = prove
 (`!do_call es xs g aux.
     clos_call_compile do_call es = (xs,g,aux) /\ ALL_DISTINCT (code_locs es)
     ==> ALL_DISTINCT (APPEND (code_locs xs) (code_locs (MAP (SND o SND) aux)))`,
  GEN_TAC THEN CASES_ON `do_call:bool` THEN REWRITE_TAC[clos_call_compile_def] THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPEC `clos_call_calls es (LN,[])` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `ys:clos_exp list`
      (X_CHOOSE_THEN `g1:num_set#(num#num#clos_exp)list` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP calls_code_locs_ALL_DISTINCT) THEN
    REWRITE_TAC[SND; MAP; code_locs_def; APPEND_NIL] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(g1:num_set#(num#num#clos_exp)list) = (g,aux)` THEN
    DISCH_THEN SUBST1_TAC THEN RVEQ_TAC THEN REWRITE_TAC[SND];
    REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[MAP; code_locs_def; APPEND_NIL]]);;

(* HOL4 line 6893 *)
let chain_exps_every_Fn_vs_NONE = prove
 (`!n xs. every_Fn_vs_NONE (MAP (SND o SND) (chain_exps n xs)) <=> every_Fn_vs_NONE xs`,
  MATCH_MP_TAC chain_exps_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[chain_exps_def; MAP; o_THM; SND] THEN
  REWRITE_TAC[every_Fn_vs_NONE_def] THEN
  ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] THEN REWRITE_TAC[ALL] THEN
  REWRITE_TAC[GSYM every_Fn_vs_NONE_EVERY; every_Fn_vs_NONE_def] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] THEN REWRITE_TAC[ALL] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[CONJ_ACI]);;

(* HOL4 line 6906 *)
let calls_compile_csyntax_ok = prove
 (`!p xs ys g aux.
     clos_call_compile p xs = (ys,g,aux)
     ==> clos_callProof_syntax_ok xs
     ==> every_Fn_vs_NONE ys /\ every_Fn_vs_NONE (MAP (SND o SND) aux)`,
  GEN_TAC THEN CASES_ON `p:bool` THEN REWRITE_TAC[clos_call_compile_def] THEN
  REWRITE_TAC[clos_callProof_syntax_ok_def] THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPEC `clos_call_calls xs (LN,[])` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `ys1:clos_exp list`
      (X_CHOOSE_THEN `g1:num_set#(num#num#clos_exp)list` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP calls_preserves_every_Fn_vs_NONE) THEN
    RVEQ_TAC THEN ASM_REWRITE_TAC[SND; MAP; every_Fn_vs_NONE_def];
    REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[MAP; every_Fn_vs_NONE_def]]);;

(* HOL4 line 6919 *)
let HD_FST_calls = prove
 (`!x y. [HD (FST (clos_call_calls [x] y))] = FST (clos_call_calls [x] y)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `clos_call_calls [x] y` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ys:clos_exp list`
    (X_CHOOSE_THEN `g:num_set#(num#num#clos_exp)list` ASSUME_TAC)) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `z:clos_exp` o MATCH_MP calls_sing) THEN
  ASM_REWRITE_TAC[FST; HD]);;

(* HOL4 line 6927 *)
let every_Fn_SOME_collect_apps = prove
 (`!max_app es e es' e'.
     collect_apps max_app es e = (es',e')
     ==> (every_Fn_SOME es' /\ every_Fn_SOME [e'] <=> every_Fn_SOME es /\ every_Fn_SOME [e])`,
  MATCH_MP_TAC collect_apps_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[collect_apps_def; PAIR_EQ] THEN
  TRY(REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [DISCH_TAC; STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`es':clos_exp list`; `e':clos_exp`] o C MP (ASSUME
    `LENGTH (args:clos_exp list) + LENGTH (es:clos_exp list) <= max_app`)) THEN
  ASM_REWRITE_TAC[every_Fn_SOME_APPEND; every_Fn_SOME_def] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONJ_ACI]);;

(* HOL4 line 6938 *)
let every_Fn_SOME_intro_multi = prove
 (`!max_app es. every_Fn_SOME (intro_multi max_app es) <=> every_Fn_SOME es`,
  MATCH_MP_TAC intro_multi_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[intro_multi_def] THEN REPEAT STRIP_TAC THEN
  TRY(W(fun (asl,w) -> if CLOS2AUX_CONST_IN "collect_apps" w then ALL_TAC else NO_TAC) THEN
      MP_TAC(ISPEC `collect_apps max_app es e` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `es':clos_exp list`
        (X_CHOOSE_THEN `e':clos_exp` ASSUME_TAC)) THEN
      FIRST_ASSUM C2BP3AUX_MATCH_EQ_ASSUMS_TAC THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP every_Fn_SOME_collect_apps) THEN
      ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]) THEN
  TRY(W(fun (asl,w) -> if CLOS2AUX_CONST_IN "collect_args" w then ALL_TAC else NO_TAC) THEN
      MP_TAC(ISPEC `collect_args max_app num_args e` PAIR_SURJECTIVE) THEN
      DISCH_THEN(X_CHOOSE_THEN `na':num` (X_CHOOSE_THEN `e':clos_exp` ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]) THEN
  ONCE_REWRITE_TAC[CLOSPROPSAUX_every_Fn_SOME_cons] THEN
  ONCE_REWRITE_TAC[CLOSPROPSAUX_every_Fn_SOME_cons] THEN
  REWRITE_TAC[every_Fn_SOME_def; IS_SOME_DEF; GEN_ALL HD_intro_multi] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[CLOSPROPSAUX_every_Fn_SOME_cons]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[every_Fn_SOME_def]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let _ = cake_add_simps [every_Fn_SOME_intro_multi];;

(* HOL4 line 6949 *)
let set_code_locs_collect_apps = prove
 (`!max_app es e es' e'.
     collect_apps max_app es e = (es',e')
     ==> set_of_list (code_locs [e']) UNION set_of_list (code_locs es') =
         set_of_list (code_locs [e]) UNION set_of_list (code_locs es)`,
  MATCH_MP_TAC collect_apps_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[collect_apps_def; PAIR_EQ] THEN
  TRY(REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ] THENL
   [DISCH_TAC; STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`es':clos_exp list`; `e':clos_exp`] o C MP (ASSUME
    `LENGTH (args:clos_exp list) + LENGTH (es:clos_exp list) <= max_app`)) THEN
  ASM_REWRITE_TAC[code_locs_append; code_locs_def; LET_DEF; LET_END_DEF;
                  SET_OF_LIST_APPEND] THEN
  DISCH_THEN SUBST1_TAC THEN SET_TAC[]);;

(* HOL4 line 6961 *)
let every_Fn_SOME_ncompile_inc = prove
 (`!x y. every_Fn_SOME (SND (clos_number_compile_inc x y))`,
  REWRITE_TAC[CLOSP1AUX_num_SND_compile_inc] THEN ONCE_REWRITE_TAC[CLOSPROPSAUX_every_Fn_SOME_cons] THEN
  REWRITE_TAC[every_Fn_SOME_def; renumber_code_locs_every_Fn_SOME]);;

let _ = cake_add_simps [every_Fn_SOME_ncompile_inc];;

(* HOL4 line 6970 *)
let every_Fn_vs_NONE_ncompile_inc = prove
 (`!x y. every_Fn_vs_NONE (SND (clos_number_compile_inc x y)) <=> every_Fn_vs_NONE y`,
  REWRITE_TAC[CLOSP1AUX_num_SND_compile_inc] THEN
  ONCE_REWRITE_TAC[CLOSPROPSAUX_every_Fn_vs_NONE_cons] THEN
  REWRITE_TAC[every_Fn_vs_NONE_def; renumber_code_locs_every_Fn_vs_NONE]);;

let _ = cake_add_simps [every_Fn_vs_NONE_ncompile_inc];;

(* HOL4 line 6979 *)
let ncompile_inc_code_locs_distinct = prove
 (`!x y. ALL_DISTINCT (code_locs (SND (clos_number_compile_inc x y)))`,
  REWRITE_TAC[CLOSP1AUX_num_SND_compile_inc] THEN ONCE_REWRITE_TAC[code_locs_cons] THEN
  REWRITE_TAC[code_locs_def; APPEND; renumber_code_locs_list_distinct]);;

let _ = cake_add_simps [ncompile_inc_code_locs_distinct];;

(* HOL4 line 6989 *)
let code_locs_FST_letop_compile_inc = prove
 (`!(x:clos_prog).
     code_locs (FST (clos_letop_compile_inc x:clos_prog)) = code_locs (FST x)`,
  REWRITE_TAC[FORALL_PAIR_THM; clos_letop_compile_inc_def; FST; code_locs_let_op]);;

let _ = cake_add_simps [code_locs_FST_letop_compile_inc];;

(* HOL4 line 6995 *)
let code_locs_FST_ticks_compile_inc = prove
 (`!(x:clos_prog).
     code_locs (FST (clos_ticks_compile_inc x:clos_prog)) = code_locs (FST x)`,
  REWRITE_TAC[FORALL_PAIR_THM; clos_ticks_compile_inc_def; FST; code_locs_remove_ticks]);;

let _ = cake_add_simps [code_locs_FST_ticks_compile_inc];;

(* HOL4 line 7001 (HOL4 bag <= is SUB_BAG) *)
let code_locs_FST_SND_kcompile_inc = prove
 (`!x y (z:clos_exp list#A).
     SUB_BAG (LIST_TO_BAG (code_locs (FST (SND (clos_known_compile_inc x y z)))))
       (LIST_TO_BAG (code_locs (FST z)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[kcompile_inc_uncurry; FST; SND] THEN
  MATCH_MP_TAC known_code_locs_bag THEN
  MAP_EVERY EXISTS_TAC [`reset_inline_factor x`; `[]:val_approx list`; `y:(val_approx)spt`;
                        `SND (clos_known_known (reset_inline_factor x) (FST (z:clos_exp list#A)) [] y)`] THEN
  REWRITE_TAC[PAIR]);;

(* HOL4 line 7012 *)
let every_Fn_vs_NONE_cond_call_compile_inc = prove
 (`!do_it x (y:clos_prog).
     (every_Fn_vs_NONE (FST y)
      ==> every_Fn_vs_NONE (FST (SND (cond_call_compile_inc do_it x y)))) /\
     (every_Fn_vs_NONE (FST y) /\ every_Fn_vs_NONE (MAP (SND o SND) (SND y))
      ==> every_Fn_vs_NONE (MAP (SND o SND) (SND (SND (cond_call_compile_inc do_it x y)))))`,
  GEN_TAC THEN CASES_ON `do_it:bool` THEN
  REWRITE_TAC[cond_call_compile_inc_def; CURRY_DEF; I_THM; FST; SND] THEN
  REWRITE_TAC[ccompile_inc_uncurry; FST; SND] THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`FST (y:clos_prog)`; `(x:num_set,[]:(num#num#clos_exp)list)`;
                 `FST (clos_call_calls (FST (y:clos_prog)) (x,[]))`;
                 `SND (clos_call_calls (FST (y:clos_prog)) (x,[]))`]
                calls_preserves_every_Fn_vs_NONE) THEN
  REWRITE_TAC[PAIR; SND; MAP; every_Fn_vs_NONE_def] THEN MESON_TAC[]);;

(* HOL4 line 7025 *)
let every_Fn_SOME_cond_call_compile_inc = prove
 (`!do_it x (y:clos_prog).
     (every_Fn_SOME (FST y) ==> every_Fn_SOME (FST (SND (cond_call_compile_inc do_it x y)))) /\
     (every_Fn_SOME (FST y) /\ every_Fn_SOME (MAP (SND o SND) (SND y))
      ==> every_Fn_SOME (MAP (SND o SND) (SND (SND (cond_call_compile_inc do_it x y)))))`,
  GEN_TAC THEN CASES_ON `do_it:bool` THEN
  REWRITE_TAC[cond_call_compile_inc_def; CURRY_DEF; I_THM; FST; SND] THEN
  REWRITE_TAC[ccompile_inc_uncurry; FST; SND] THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`FST (y:clos_prog)`; `(x:num_set,[]:(num#num#clos_exp)list)`;
                 `FST (clos_call_calls (FST (y:clos_prog)) (x,[]))`;
                 `SND (clos_call_calls (FST (y:clos_prog)) (x,[]))`]
                calls_preserves_every_Fn_SOME) THEN
  REWRITE_TAC[PAIR; SND; MAP; every_Fn_SOME_def] THEN MESON_TAC[]);;

(* HOL4 line 7038 *)
let compile_common_inc_def = cake_def
  `compile_common_inc (c:clos_to_bvl_config) (cc:B->clos_prog->(byte list#int64 list#B)option) =
     pure_cc (cond_mti_compile_inc (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c))
       (state_cc (ignore_table clos_number_compile_inc)
          (known_cc (clos_to_bvl_config_known_conf c)
             (state_cc (cond_call_compile_inc (clos_to_bvl_config_do_call c))
                (pure_cc clos_annotate_compile_inc cc))))`;;

(* HOL4 line 7047 *)
let clos_state_cc_def = cake_def
  `clos_state_cc (inc:A->clos_prog->A#clos_prog)
     (cc:B->clos_prog->(byte list#int64 list#B)option) =
     (state_cc inc cc:(A#B)->clos_prog->(byte list#int64 list#(A#B))option)`;;

(* HOL4 line 7051 *)
let semantics_cond_call_compile_inc = prove
 (CASE_TERM `!(ffi:(FFI)ffi_state) max_app (co:num->(num_set#B)#clos_prog)
     (cc:B->clos_prog->(byte list#int64 list#B)option) es do_call es' g aux code.
     ~(clos_semantics ffi max_app FEMPTY co
         (clos_state_cc (cond_call_compile_inc do_call) cc) es = Fail) /\
     clos_call_compile do_call es = (es',g,aux) /\
     code = alist_to_fmap aux /\
     (do_call
      ==> clos_callProof_syntax_ok es /\
          is_state_oracle clos_call_compile_inc co /\
          g = FST (FST (co 0)) /\
          oracle_monotonic (set_of_list o code_locs o FST o SND) (<)
            (set_of_list (code_locs es)) co /\
          (!k. let (cfg,exp,aux) = co k in clos_callProof_syntax_ok exp /\ aux = []))
     ==> clos_semantics ffi max_app code (state_co (cond_call_compile_inc do_call) co) cc es' =
         clos_semantics ffi max_app FEMPTY co
           (clos_state_cc (cond_call_compile_inc do_call) cc) es`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cond_call_compile_inc_def; clos_state_cc_def] THEN
  CASES_ON `do_call:bool` THEN REWRITE_TAC[] THENL
   [ALL_TAC;
    REWRITE_TAC[clos_call_compile_def; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[alist_to_fmap_thm] THEN MATCH_MP_TAC clos_semantics_CURRY_I THEN
    ASM_REWRITE_TAC[]] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `clos_call_calls es (LN,[]) = (es',(g,aux))` ASSUME_TAC THENL
   [UNDISCH_TAC `clos_call_compile T es = (es',g,aux)` THEN
    REWRITE_TAC[clos_call_compile_def] THEN
    REWRITE_TAC[C2BP3AUX_pair_CASE_FST_SND; PAIR] THEN REWRITE_TAC[PAIR_EQ] THEN
    MESON_TAC[PAIR];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP FST (aux:(num#num#clos_exp)list))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`es:clos_exp list`; `(LN:num_set,[]:(num#num#clos_exp)list)`;
                   `es':clos_exp list`; `(g:num_set,aux:(num#num#clos_exp)list)`]
                  calls_ALL_DISTINCT) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[clos_callProof_syntax_ok_def]) THEN
    ASM_REWRITE_TAC[SND; MAP; ALL_DISTINCT; set_of_list; DISJOINT_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `FEMPTY |++ (aux:(num#num#clos_exp)list) = alist_to_fmap aux` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FUPDATE_LIST_alist_to_fmap; FUNION_FEMPTY_2;
                 ALL_DISTINCT_alist_to_fmap_REVERSE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`T`; `g:num_set`; `aux:(num#num#clos_exp)list`;
                 `state_co (clos_call_compile_inc:num_set->clos_prog->num_set#clos_prog)
                    (co:num->(num_set#B)#clos_prog)`;
                 `cc:B->clos_prog->(byte list#int64 list#B)option`; `es':clos_exp list`;
                 `ffi:(FFI)ffi_state`; `max_app:num`; `co:num->(num_set#B)#clos_prog`;
                 `state_cc (clos_call_compile_inc:num_set->clos_prog->num_set#clos_prog)
                    (cc:B->clos_prog->(byte list#int64 list#B)option)`;
                 `es:clos_exp list`]
                (GEN_ALL clos_callProof_semantics_compile)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[code_inv_def] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  MAP_EVERY EXISTS_TAC [`g:num_set`; `aux:(num#num#clos_exp)list`] THEN
  ASM_REWRITE_TAC[distinctness "option"; IS_SOME_DEF] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`es:clos_exp list`; `(LN:num_set,[]:(num#num#clos_exp)list)`;
                   `es':clos_exp list`; `(g:num_set,aux:(num#num#clos_exp)list)`]
                  calls_wfg) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[clos_callProof_syntax_ok_def]) THEN
    ASM_REWRITE_TAC[SND; MAP; set_of_list; DISJOINT_EMPTY; wfg_def; FST;
                    domain_def; IMAGE_CLAUSES; ALL_DISTINCT];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> CLOS2AUX_CONST_IN "oracle_monotonic" (concl th))) THEN
    MATCH_MP_TAC oracle_monotonic_subset THEN REWRITE_TAC[SUBSET_REFL] THEN
    MP_TAC(ISPECL [`es:clos_exp list`; `(LN:num_set,[]:(num#num#clos_exp)list)`;
                   `es':clos_exp list`; `(g:num_set,aux:(num#num#clos_exp)list)`]
                  calls_domain_locs) THEN
    ASM_REWRITE_TAC[FST; domain_def] THEN SET_TAC[]]);;

(* HOL4 line 7098 *)
let semantics_cond_mti_compile_inc = prove
 (`!(ffi:(FFI)ffi_state) max_app (co:num->C#clos_prog) cc xs do_mti.
     ~(clos_semantics ffi max_app FEMPTY co
         (pure_cc (cond_mti_compile_inc do_mti max_app) cc) xs = Fail) /\
     (do_mti
      ==> (!n. SND (SND (co n)) = [] /\ ALL no_mti (FST (SND (co n)))) /\
          1 <= max_app /\ ALL no_mti xs)
     ==> clos_semantics ffi max_app FEMPTY
           (pure_co (cond_mti_compile_inc do_mti max_app) o co) cc
           (clos_mti_compile do_mti max_app xs) =
         clos_semantics ffi max_app FEMPTY co
           (pure_cc (cond_mti_compile_inc do_mti max_app) cc) xs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC (GEN_ALL clos_mtiProof_semantics_compile) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[cond_mti_compile_inc_def] THEN
  ASM_CASES_TAC `do_mti:bool` THEN ASM_REWRITE_TAC[pure_cc_I; pure_co_I]);;

(* HOL4 line 7118: fun expand_tup_def (an ML function) *)

let C2BP3AUX_letop_uncurry = prove
 (`!(p:clos_prog). (clos_letop_compile_inc p:clos_prog) = (clos_letop_let_op (FST p),[])`,
  REWRITE_TAC[FORALL_PAIR_THM; clos_letop_compile_inc_def; FST]);;

let C2BP3AUX_ticks_uncurry = prove
 (`!(p:clos_prog). (clos_ticks_compile_inc p:clos_prog) = (clos_ticks_remove_ticks (FST p),[])`,
  REWRITE_TAC[FORALL_PAIR_THM; clos_ticks_compile_inc_def; FST]);;

(* known_co at an index, unfolded *)
let C2BP3AUX_known_co_SOME = prove
 (`!kcfg (f:num->((val_approx)spt#B)#clos_prog) n.
     known_co (SOME kcfg) f n =
     (SND (FST (f n)),
      clos_letop_let_op (clos_ticks_remove_ticks
        (MAP FST (FST (clos_known_known (reset_inline_factor kcfg)
                        (clos_fvs_compile (FST (SND (f n)))) [] (FST (FST (f n))))))),
      [])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[known_co_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[o_THM; pure_co_def; PAIR_MAP; I_THM] THEN
  REWRITE_TAC[FST_state_co; SND_state_co] THEN
  REWRITE_TAC[o_THM; pure_co_def; PAIR_MAP; I_THM; FST; SND] THEN
  REWRITE_TAC[kcompile_inc_uncurry; fcompile_inc_uncurry; C2BP3AUX_letop_uncurry;
              C2BP3AUX_ticks_uncurry; FST; SND]);;

let C2BP3AUX_known_co_NONE = prove
 (`!(f:num->((val_approx)spt#B)#clos_prog) n.
     known_co NONE f n = (SND (FST (f n)),SND (f n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[known_co_def] THEN CAKE_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[PAIR_FST_SND_EQ] THEN
  REWRITE_TAC[GEN_ALL FST_state_co; GEN_ALL SND_state_co; CURRY_DEF; I_THM; FST; SND]);;

(* HOL4 line 7124 *)
let every_Fn_vs_NONE_known_co = prove
 (`!(f:num->((val_approx)spt#B)#clos_prog) n conf.
     (every_Fn_vs_NONE (FST (SND (f n))) /\
      globals_approx_every_Fn_vs_NONE (FST (FST (f n)))
      ==> every_Fn_vs_NONE (FST (SND (known_co conf f n)))) /\
     (every_Fn_vs_NONE (MAP (SND o SND) (SND (SND (f n))))
      ==> every_Fn_vs_NONE (MAP (SND o SND) (SND (SND (known_co conf f n)))))`,
  REPEAT GEN_TAC THEN CASES_ON `conf:(clos_known_config)option` THEN
  REWRITE_TAC[C2BP3AUX_known_co_NONE; C2BP3AUX_known_co_SOME; FST; SND; MAP;
              every_Fn_vs_NONE_def] THEN
  REWRITE_TAC[let_op_every_Fn_vs_NONE; remove_ticks_every_Fn_vs_NONE; clos_fvs_compile_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`reset_inline_factor a`; `remove_fvs 0 (FST (SND ((f:num->((val_approx)spt#B)#clos_prog) n)))`;
                 `[]:val_approx list`; `FST (FST ((f:num->((val_approx)spt#B)#clos_prog) n))`]
                known_every_Fn_vs_NONE) THEN
  ASM_REWRITE_TAC[remove_fvs_every_Fn_vs_NONE; ALL] THEN SIMP_TAC[]);;

(* HOL4 line 7142 *)
let every_Fn_SOME_known_co = prove
 (`!(f:num->((val_approx)spt#B)#clos_prog) n conf.
     (every_Fn_SOME (FST (SND (f n))) /\
      globals_approx_every_Fn_SOME (FST (FST (f n)))
      ==> every_Fn_SOME (FST (SND (known_co conf f n)))) /\
     (every_Fn_SOME (MAP (SND o SND) (SND (SND (f n))))
      ==> every_Fn_SOME (MAP (SND o SND) (SND (SND (known_co conf f n)))))`,
  REPEAT GEN_TAC THEN CASES_ON `conf:(clos_known_config)option` THEN
  REWRITE_TAC[C2BP3AUX_known_co_NONE; C2BP3AUX_known_co_SOME; FST; SND; MAP;
              every_Fn_SOME_def] THEN
  REWRITE_TAC[let_op_every_Fn_SOME; remove_ticks_every_Fn_SOME; clos_fvs_compile_def] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`reset_inline_factor a`; `remove_fvs 0 (FST (SND ((f:num->((val_approx)spt#B)#clos_prog) n)))`;
                 `[]:val_approx list`; `FST (FST ((f:num->((val_approx)spt#B)#clos_prog) n))`]
                known_every_Fn_SOME) THEN
  ASM_REWRITE_TAC[remove_fvs_every_Fn_SOME; ALL] THEN SIMP_TAC[]);;

(* HOL4 line 7160 *)
let alist_to_fmap_FEMPTY = prove
 (`!(xs:(A#B)list). ALL_DISTINCT (MAP FST xs) ==> alist_to_fmap xs = FEMPTY |++ xs`,
  SIMP_TAC[FUPDATE_LIST_alist_to_fmap; FUNION_FEMPTY_2; ALL_DISTINCT_alist_to_fmap_REVERSE]);;

(* HOL4 line 7167 *)
let obvious_arith_comm = prove
 (`!a b. a = b + a <=> b = 0`,
  ARITH_TAC);;

(* HOL4 line 7173 *)
let SND_SND_known_compile_inc = prove
 (`!conf app (es:clos_exp list#A). SND (SND (clos_known_compile_inc conf app es)) = SND es`,
  REWRITE_TAC[kcompile_inc_uncurry; SND]);;

(* HOL4 line 7179: val fvs_inc = clos_fvs$compile_inc : clos_prog ->       *)
(* clos_prog (written out: (clos_fvs_compile_inc:clos_prog->clos_prog))    *)

(* HOL4 line 7181 *)
let known_state_oracle_globals_approx = prove
 (`!cfg' (co:num->((val_approx)spt#B)#clos_prog) spt cfg exps k_exps.
     is_state_oracle (clos_known_compile_inc cfg') (pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o co) /\
     FST (FST (co 0)) = spt /\
     clos_known_known cfg exps [] LN = (k_exps,spt) /\
     every_Fn_vs_NONE exps /\ every_Fn_SOME exps /\
     (!k. every_Fn_vs_NONE (FST (SND (co k))) /\ every_Fn_SOME (FST (SND (co k))))
     ==> !k. globals_approx_every_Fn_vs_NONE (FST (FST (co k))) /\
             globals_approx_every_Fn_SOME (FST (FST (co k)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`cfg:clos_known_config`; `exps:clos_exp list`; `[]:val_approx list`;
                   `LN:(val_approx)spt`] known_every_Fn_vs_NONE) THEN
    MP_TAC(ISPECL [`cfg:clos_known_config`; `exps:clos_exp list`; `[]:val_approx list`;
                   `LN:(val_approx)spt`] known_every_Fn_SOME) THEN
    ASM_REWRITE_TAC[ALL; SND; globals_approx_every_Fn_SOME_def;
                    globals_approx_every_Fn_vs_NONE_def; lookup_def; distinctness "option"] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o REWRITE_RULE[is_state_oracle_def] o
    check (fun th -> CLOS2AUX_CONST_IN "is_state_oracle" (concl th))) THEN
  REWRITE_TAC[o_THM; pure_co_def; PAIR_MAP; I_THM; fcompile_inc_uncurry; kcompile_inc_uncurry;
              FST; SND; clos_fvs_compile_def] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall (concl th))) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`reset_inline_factor cfg'`;
                 `remove_fvs 0 (FST (SND ((co:num->((val_approx)spt#B)#clos_prog) k)))`;
                 `[]:val_approx list`; `FST (FST ((co:num->((val_approx)spt#B)#clos_prog) k))`]
                known_every_Fn_vs_NONE) THEN
  MP_TAC(ISPECL [`reset_inline_factor cfg'`;
                 `remove_fvs 0 (FST (SND ((co:num->((val_approx)spt#B)#clos_prog) k)))`;
                 `[]:val_approx list`; `FST (FST ((co:num->((val_approx)spt#B)#clos_prog) k))`]
                known_every_Fn_SOME) THEN
  ASM_REWRITE_TAC[ALL; remove_fvs_every_Fn_SOME; remove_fvs_every_Fn_vs_NONE] THEN
  MESON_TAC[]);;

(* HOL4 line 7224 (HOL4 $< is (<)) *)
let known_co_facts = prove
 (`!kc (co:num->((val_approx)spt#B)#clos_prog) exps kc' exps'.
     let co2 = known_co kc co in
     clos_known_compile kc exps = (kc',exps')
     ==> (IS_SOME kc
          ==> is_state_oracle (clos_known_compile_inc (THE kc))
                (pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o co) /\
              FST (FST (co 0)) = clos_known_config_val_approx_spt (THE kc') /\
              every_Fn_vs_NONE exps /\ every_Fn_SOME exps /\
              (!k. every_Fn_vs_NONE (FST (SND (co k))) /\ every_Fn_SOME (FST (SND (co k)))))
     ==> (oracle_monotonic (set_of_list o code_locs o FST o SND) (<)
            (set_of_list (code_locs exps)) co
          ==> oracle_monotonic (set_of_list o code_locs o FST o SND) (<)
                (set_of_list (code_locs exps')) co2) /\
         (!k. clos_callProof_syntax_ok (FST (SND (co k)))
              ==> clos_callProof_syntax_ok (FST (SND (co2 k)))) /\
         (!k. SND (SND (co k)) = [] ==> SND (SND (co2 k)) = []) /\
         (!k. (!k. every_Fn_SOME (FST (SND (co k))) /\ SND (SND (co k)) = [])
              ==> every_Fn_SOME (FST (SND (co2 k))) /\
                  every_Fn_SOME (MAP (SND o SND) (SND (SND (co2 k)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CASES_ON `kc:(clos_known_config)option` THEN
  REWRITE_TAC[clos_known_compile_def; IS_SOME_DEF; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THENL
   [REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[C2BP3AUX_known_co_NONE; FST; SND] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC oracle_monotonic_subset THEN
      REWRITE_TAC[SUBSET_REFL; o_THM; C2BP3AUX_known_co_NONE; FST; SND];
      REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num`) THEN
      ASM_REWRITE_TAC[MAP; every_Fn_SOME_def]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `clos_known_known a (clos_fvs_compile exps) [] LN` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `es:(clos_exp#val_approx)list`
    (X_CHOOSE_THEN `g:(val_approx)spt` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[THE_DEF; clos_known_config_INFO.ri_accfupds; K_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:clos_known_config`; `co:num->((val_approx)spt#B)#clos_prog`;
                 `g:(val_approx)spt`; `a:clos_known_config`; `clos_fvs_compile exps`;
                 `es:(clos_exp#val_approx)list`] known_state_oracle_globals_approx) THEN
  ASM_REWRITE_TAC[clos_fvs_compile_def; remove_fvs_every_Fn_SOME;
                  remove_fvs_every_Fn_vs_NONE] THEN
  DISCH_THEN(LABEL_TAC "glob") THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_fvs_compile_def]) THEN
  REWRITE_TAC[C2BP3AUX_known_co_SOME; FST; SND; MAP; every_Fn_SOME_def; code_locs_let_op;
              code_locs_remove_ticks; let_op_every_Fn_SOME; remove_ticks_every_Fn_SOME;
              clos_fvs_compile_def] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC oracle_monotonic_subset THEN
    REWRITE_TAC[o_THM; C2BP3AUX_known_co_SOME; FST; SND; code_locs_let_op;
                code_locs_remove_ticks; clos_fvs_compile_def] THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM (SPEC `0` code_locs_remove_fvs)] THEN
      MATCH_MP_TAC LIST_TO_BAG_SUBSET THEN MATCH_MP_TAC known_code_locs_bag THEN
      ASM_MESON_TAC[];
      GEN_TAC THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM (SPEC `0` code_locs_remove_fvs)] THEN
      MATCH_MP_TAC LIST_TO_BAG_SUBSET THEN MATCH_MP_TAC known_code_locs_bag THEN
      MESON_TAC[PAIR]];
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[clos_callProof_syntax_ok_def; let_op_every_Fn_SOME; let_op_every_Fn_vs_NONE;
              remove_ticks_every_Fn_SOME; remove_ticks_every_Fn_vs_NONE; code_locs_let_op;
              code_locs_remove_ticks] THEN
  STRIP_TAC THEN USE_THEN "glob" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num` o check (fun th ->
    is_forall (concl th) && CLOS2AUX_CONST_IN "every_Fn_vs_NONE" (concl th))) THEN
  MP_TAC(ISPECL [`reset_inline_factor a`;
                 `remove_fvs 0 (FST (SND ((co:num->((val_approx)spt#B)#clos_prog) k)))`;
                 `[]:val_approx list`; `FST (FST ((co:num->((val_approx)spt#B)#clos_prog) k))`]
                known_every_Fn_vs_NONE) THEN
  MP_TAC(ISPECL [`reset_inline_factor a`;
                 `remove_fvs 0 (FST (SND ((co:num->((val_approx)spt#B)#clos_prog) k)))`;
                 `[]:val_approx list`; `FST (FST ((co:num->((val_approx)spt#B)#clos_prog) k))`]
                known_every_Fn_SOME) THEN
  ASM_REWRITE_TAC[ALL; remove_fvs_every_Fn_SOME; remove_fvs_every_Fn_vs_NONE] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM LIST_TO_BAG_DISTINCT] THEN MATCH_MP_TAC BAG_ALL_DISTINCT_SUB_BAG THEN
  EXISTS_TAC `LIST_TO_BAG (code_locs (FST (SND ((co:num->((val_approx)spt#B)#clos_prog) k))))` THEN
  ASM_REWRITE_TAC[LIST_TO_BAG_DISTINCT] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM (SPEC `0` code_locs_remove_fvs)] THEN
  MATCH_MP_TAC known_code_locs_bag THEN MESON_TAC[PAIR]);;

(* HOL4 line 7285: val known_co_facts2 = known_co_facts |> SIMP_RULE ... |> *)
(* BODY_CONJUNCTS |> map IRULE_CANON ... (a list of theorems for IRULE in   *)
(* the proofs; derived from known_co_facts there)                            *)

let C2BP3AUX_ncompile_inc_FST = prove
 (`!x y. FST (clos_number_compile_inc x y) =
         FST (renumber_code_locs_list (make_even (x + MAX (LENGTH y) 1)) y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_number_compile_inc_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[C2BP3AUX_pair_CASE_FST_SND; FST]);;

(* HOL4 line 7295 *)
let MEM_number_compile_inc_locs = prove
 (`!x n exps.
     MEM x (code_locs (SND (clos_number_compile_inc n exps)))
     ==> n < x /\ x < FST (clos_number_compile_inc n exps)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSP1AUX_num_SND_compile_inc; C2BP3AUX_ncompile_inc_FST] THEN
  ONCE_REWRITE_TAC[code_locs_cons] THEN REWRITE_TAC[code_locs_def; APPEND] THEN
  MP_TAC(SPECL [`make_even (n + MAX (LENGTH (exps:clos_exp list)) 1)`; `exps:clos_exp list`]
               renumber_code_locs_list_distinct) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `make_even (n + MAX (LENGTH (exps:clos_exp list)) 1)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[make_even_def] THEN COND_CASES_TAC THEN ARITH_TAC; ASM_SIMP_TAC[]];
    REWRITE_TAC[GSYM GT] THEN ASM_SIMP_TAC[]]);;

let C2BP3AUX_FST_ignore_table = prove
 (`!(f:S->A->S#B) st (p:A#C). FST (ignore_table f st p) = FST (f st (FST p))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; ignore_table_def; FST] THEN
  REWRITE_TAC[C2BP3AUX_pair_CASE_FST_SND; FST]);;

(* HOL4 line 7317 *)
let number_oracle_FST_inc = prove
 (`!(co:num->(num#C)#clos_prog) j.
     is_state_oracle (ignore_table clos_number_compile_inc) co
     ==> FST (clos_number_compile_inc (FST (FST (co j))) (FST (SND (co j)))) =
         FST (FST (co (j + 1)))`,
  REWRITE_TAC[is_state_oracle_def; GSYM ADD1] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[C2BP3AUX_FST_ignore_table]);;

(* HOL4 line 7330 *)
let number_oracle_FST_strict_mono = prove
 (`!(co:num->(num#C)#clos_prog).
     is_state_oracle (ignore_table clos_number_compile_inc) co
     ==> !j i. i < j ==> FST (FST (co i)) < FST (FST (co j))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!j. FST (FST ((co:num->(num#C)#clos_prog) j)) < FST (FST (co (SUC j)))`
    ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(REWRITE_RULE[GSYM ADD1] (MATCH_MP number_oracle_FST_inc th))]) THEN
    REWRITE_TAC[C2BP3AUX_ncompile_inc_FST] THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `make_even (FST (FST ((co:num->(num#C)#clos_prog) j)) +
                           MAX (LENGTH (FST (SND (co j)))) 1)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[make_even_def] THEN COND_CASES_TAC THEN ARITH_TAC;
      REWRITE_TAC[renumber_code_locs_inc]];
    ALL_TAC] THEN
  INDUCT_TAC THEN REWRITE_TAC[LT] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `FST (FST ((co:num->(num#C)#clos_prog) j))` THEN
  ASM_SIMP_TAC[]);;

(* HOL4 line 7354 *)
let number_oracle_FST_mono = prove
 (`!(co:num->(num#C)#clos_prog).
     is_state_oracle (ignore_table clos_number_compile_inc) co
     ==> !j i. i <= j ==> FST (FST (co i)) <= FST (FST (co j))`,
  REWRITE_TAC[LE_LT] THEN MESON_TAC[number_oracle_FST_strict_mono]);;

(* HOL4 line 7363 *)
let SND_SND_ignore_table = prove
 (`!(f:S->A->S#B) st (p:A#C). SND (SND (ignore_table f st p)) = SND p`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; ignore_table_def; SND] THEN
  REWRITE_TAC[C2BP3AUX_pair_CASE_FST_SND; SND]);;

(* HOL4 line 7369 *)
let FST_SND_ignore_table = prove
 (`!(f:S->A->S#B) st (p:A#C). FST (SND (ignore_table f st p)) = SND (f st (FST p))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; ignore_table_def; FST; SND] THEN
  REWRITE_TAC[C2BP3AUX_pair_CASE_FST_SND; FST; SND]);;

(* HOL4 line 7375 *)
let renumber_code_locs_monotonic = prove
 (`!(co:num->(num#C)#clos_prog) n exps.
     is_state_oracle (ignore_table clos_number_compile_inc) co /\
     FST (FST (co 0)) >= FST (renumber_code_locs_list n exps)
     ==> oracle_monotonic (set_of_list o code_locs o FST o SND) (<)
           (set_of_list (code_locs (SND (renumber_code_locs_list n exps))))
           (state_co (ignore_table clos_number_compile_inc) co)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[oracle_monotonic_def; o_THM; GEN_ALL SND_state_co; FST_SND_ignore_table;
              IN_SET_OF_LIST] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP MEM_number_compile_inc_locs) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP MEM_number_compile_inc_locs) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP number_oracle_FST_inc th]) THEN
    FIRST_ASSUM(MP_TAC o SPECL [`j:num`; `i + 1`] o MATCH_MP number_oracle_FST_mono) THEN
    ASM_REWRITE_TAC[ARITH_RULE `i + 1 <= j <=> i < j`] THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o MATCH_MP MEM_number_compile_inc_locs) THEN
    MP_TAC(SPECL [`n:num`; `exps:clos_exp list`] renumber_code_locs_list_distinct) THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`i:num`; `0`] o MATCH_MP number_oracle_FST_mono) THEN
    UNDISCH_TAC `FST (FST ((co:num->(num#C)#clos_prog) 0)) >= FST (renumber_code_locs_list n exps)` THEN
    REWRITE_TAC[LE_0] THEN ARITH_TAC]);;

(* HOL4 line 7400 *)
let SND_cond_mti_compile_inc = prove
 (`!do_it ma (v:clos_exp list#A list).
     SND (cond_mti_compile_inc do_it ma v) = (if do_it then [] else SND v)`,
  GEN_TAC THEN CASES_ON `do_it:bool` THEN
  REWRITE_TAC[cond_mti_compile_inc_def; I_THM; FORALL_PAIR_THM; clos_mti_compile_inc_def;
              SND]);;

(* HOL4 line 7408 *)
let ccompile_aux_subset = prove
 (`!(c:clos_to_bvl_config) exps exps' g aux.
     clos_call_compile (clos_to_bvl_config_do_call c) exps = (exps',g,aux)
     ==> set_of_list (MAP FST aux) SUBSET IMAGE SUC (set_of_list (code_locs exps))`,
  GEN_TAC THEN SPEC_TAC(`clos_to_bvl_config_do_call c`,`b:bool`) THEN
  GEN_TAC THEN CASES_ON `b:bool` THEN REWRITE_TAC[clos_call_compile_def] THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPEC `clos_call_calls exps (LN,[])` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `ys:clos_exp list`
      (X_CHOOSE_THEN `g1:num_set#(num#num#clos_exp)list` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP calls_code_subset) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP calls_domain_locs) THEN
    UNDISCH_TAC `(g1:num_set#(num#num#clos_exp)list) = (g,aux)` THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[FST; SND; MAP; set_of_list; domain_def; UNION_EMPTY] THEN SET_TAC[];
    REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[MAP; set_of_list; EMPTY_SUBSET]]);;

(* HOL4 line 7421 *)
let ccompile_locs_subset = prove
 (`!(c:clos_to_bvl_config) exps exps' g aux.
     clos_call_compile (clos_to_bvl_config_do_call c) exps = (exps',g,aux)
     ==> set_of_list (code_locs (APPEND exps' (MAP (SND o SND) aux))) SUBSET
         set_of_list (code_locs exps)`,
  GEN_TAC THEN SPEC_TAC(`clos_to_bvl_config_do_call c`,`b:bool`) THEN
  GEN_TAC THEN CASES_ON `b:bool` THEN REWRITE_TAC[clos_call_compile_def] THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPEC `clos_call_calls exps (LN,[])` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `ys:clos_exp list`
      (X_CHOOSE_THEN `g1:num_set#(num#num#clos_exp)list` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP calls_code_locs_MEM) THEN
    UNDISCH_TAC `(g1:num_set#(num#num#clos_exp)list) = (g,aux)` THEN
    DISCH_THEN SUBST1_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[SND; MAP; code_locs_def; MEM; code_locs_append; SET_OF_LIST_APPEND;
                SUBSET; IN_UNION; IN_SET_OF_LIST; MEM_APPEND] THEN MESON_TAC[];
    REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[MAP; APPEND_NIL; SUBSET_REFL]]);;

(* HOL4 line 7432 *)
let number_compile_inc_esgc_free = prove
 (`!x y. ALL clos_esgc_free y ==> ALL clos_esgc_free (SND (clos_number_compile_inc x y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSP1AUX_num_SND_compile_inc; ALL; clos_esgc_free_def] THEN
  MATCH_MP_TAC (CONJUNCT1 renumber_code_locs_esgc_free) THEN
  MAP_EVERY EXISTS_TAC [`make_even (x + MAX (LENGTH (y:clos_exp list)) 1)`; `y:clos_exp list`;
                        `FST (renumber_code_locs_list (make_even (x + MAX (LENGTH (y:clos_exp list)) 1)) y)`] THEN
  ASM_REWRITE_TAC[PAIR]);;

(* HOL4 line 7442 *)
let number_monotonic_elist_globals = prove
 (`!St (co:num->(num#C)#clos_prog).
     oracle_monotonic (SET_OF_BAG o clos_elist_globals o FST o SND) (<) St co
     ==> oracle_monotonic (SET_OF_BAG o clos_elist_globals o FST o SND) (<) St
           (state_co (ignore_table clos_number_compile_inc) co)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC oracle_monotonic_subset THEN
  REWRITE_TAC[SUBSET_REFL; o_THM; GEN_ALL SND_state_co; FST_SND_ignore_table;
              elist_globals_SND_ncompile_inc]);;

(* HOL4 line 7451 *)
let cond_mti_monotonic_elist_globals = prove
 (`!exps (co:num->C#clos_prog) do_it ma.
     oracle_monotonic (SET_OF_BAG o clos_elist_globals o FST o SND) (<)
       (SET_OF_BAG (clos_elist_globals exps)) co
     ==> oracle_monotonic (SET_OF_BAG o clos_elist_globals o FST o SND) (<)
           (SET_OF_BAG (clos_elist_globals (clos_mti_compile do_it ma exps)))
           (pure_co (cond_mti_compile_inc do_it ma) o co)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC oracle_monotonic_subset THEN
  REWRITE_TAC[compile_elist_globals; SUBSET_REFL; o_THM; pure_co_def; PAIR_MAP; SND] THEN
  GEN_TAC THEN CASES_ON `do_it:bool` THEN
  REWRITE_TAC[cond_mti_compile_inc_def; I_THM; mcompile_inc_uncurry; FST;
              intro_multi_preserves_elist_globals; SUBSET_REFL]);;

(* HOL4 line 7466 *)
let DISJOINT_LE_GT = prove
 (`!a b n. (!x. x IN a ==> x <= n) /\ (!x. x IN b ==> n < x) ==> DISJOINT a b`,
  REWRITE_TAC[IN_DISJOINT] THEN MESON_TAC[NOT_LT]);;

(* HOL4 line 7475 *)
let oracle_monotonic_init_subset = prove
 (`!(f:A->B->bool) R St (co:num->A) St'.
     oracle_monotonic f R St co /\ St' SUBSET St ==> oracle_monotonic f R St' co`,
  MESON_TAC[oracle_monotonic_subset; SUBSET_REFL]);;

(* HOL4 line 7482 *)
let compile_inc_post_kcompile_def = cake_def
  `compile_inc_post_kcompile (c:clos_to_bvl_config) exps =
     clos_known_compile (clos_to_bvl_config_known_conf c)
       (SND (renumber_code_locs_list
               (make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH exps)))
               (clos_mti_compile (clos_to_bvl_config_do_mti c)
                  (clos_to_bvl_config_max_app c) exps)))`;;

(* HOL4 lines 7489-7500: fun promote_bool, val semantics_kcompile (from     *)
(* clos_knownProof's semantics_compile; for the proofs), fun conseq, val c0 *)
(* (ML helpers, not stated)                                                  *)


(* HOL4 line 7502 *)
let FST_known_co = prove
 (`!kc (co:num->((val_approx)spt#B)#clos_prog) n. FST (known_co kc co n) = SND (FST (co n))`,
  GEN_TAC THEN CASES_ON `kc:(clos_known_config)option` THEN
  REWRITE_TAC[C2BP3AUX_known_co_NONE; C2BP3AUX_known_co_SOME; FST]);;

let C2BP3AUX_common_def = REWRITE_RULE[GSYM EVEN_MOD2; GSYM make_even_def] compile_common_def;;

let C2BP3AUX_compile_common_parts = prove
 (`!c es1 c' code2.
     compile_common c es1 = (c',code2) ==>
     ?n es_n kc es_k es_c g aux.
       renumber_code_locs_list
         (make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH es1)))
         (clos_mti_compile (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c) es1) =
         (n,es_n) /\
       clos_known_compile (clos_to_bvl_config_known_conf c) es_n = (kc,es_k) /\
       clos_call_compile (clos_to_bvl_config_do_call c) es_k = (es_c,g,aux) /\
       code2 = clos_annotate_compile
                 (APPEND (chain_exps (clos_to_bvl_config_next_loc c) es_c) aux) /\
       c' = clos_to_bvl_config_start_fupd (combin_K (clos_to_bvl_config_next_loc c))
              (clos_to_bvl_config_next_loc_fupd (combin_K n)
                 (clos_to_bvl_config_known_conf_fupd (combin_K kc)
                    (clos_to_bvl_config_call_state_fupd (combin_K (g,aux)) c)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C2BP3AUX_common_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[clos_mtiProof_compile_length] THEN
  MP_TAC(ISPEC `renumber_code_locs_list
         (make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH (es1:clos_exp list))))
         (clos_mti_compile (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c) es1)`
         PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `es_n:clos_exp list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `clos_known_compile (clos_to_bvl_config_known_conf c) es_n` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `kc:(clos_known_config)option`
    (X_CHOOSE_THEN `es_k:clos_exp list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `clos_call_compile (clos_to_bvl_config_do_call c) es_k` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `es_c:clos_exp list`
    (X_CHOOSE_THEN `ga:num_set#(num#num#clos_exp)list` ASSUME_TAC)) THEN
  MP_TAC(ISPEC `ga:num_set#(num#num#clos_exp)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num_set` (X_CHOOSE_THEN `aux:(num#num#clos_exp)list` SUBST_ALL_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `es_n:clos_exp list`; `kc:(clos_known_config)option`;
                        `es_k:clos_exp list`; `es_c:clos_exp list`; `g:num_set`;
                        `aux:(num#num#clos_exp)list`] THEN
  ASM_REWRITE_TAC[]);;

let C2BP3AUX_annotate_Call = prove
 (`!t loc. clos_annotate_annotate 0 [clos_Call t 0 loc []] = [clos_Call t 0 loc []]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_annotate_annotate_def] THEN
  REWRITE_TAC[alt_free_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_annotate_shift_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF]);;

let C2BP3AUX_co_m = prove
 (`!dm ma (co1:num->A#clos_prog) n.
     FST ((pure_co (cond_mti_compile_inc dm ma) o co1) n) = FST (co1 n) /\
     FST (SND ((pure_co (cond_mti_compile_inc dm ma) o co1) n)) =
       clos_mti_compile dm ma (FST (SND (co1 n))) /\
     SND (SND ((pure_co (cond_mti_compile_inc dm ma) o co1) n)) =
       (if dm then [] else SND (SND (co1 n)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[o_THM; pure_co_def; PAIR_MAP; FST; SND] THEN
  CASES_ON `dm:bool` THEN
  REWRITE_TAC[cond_mti_compile_inc_def; clos_mti_compile_def; I_THM; mcompile_inc_uncurry; FST; SND]);;

let C2BP3AUX_co_n = prove
 (`!(co:num->(num#A)#clos_prog) n.
     FST (state_co (ignore_table clos_number_compile_inc) co n) = SND (FST (co n)) /\
     FST (SND (state_co (ignore_table clos_number_compile_inc) co n)) =
       SND (clos_number_compile_inc (FST (FST (co n))) (FST (SND (co n)))) /\
     SND (SND (state_co (ignore_table clos_number_compile_inc) co n)) = SND (SND (co n))`,
  REWRITE_TAC[GEN_ALL FST_state_co; GEN_ALL SND_state_co; FST_SND_ignore_table;
              SND_SND_ignore_table]);;

let C2BP3AUX_is_eq_app name th =
  let c = concl th in is_eq c && CLOS2AUX_CONST_IN name (lhand c) && is_pair (rand c);;

(* HOL4 line 7509 (HOL4 $< is (<); fvs_inc is clos_fvs_compile_inc at clos_prog->clos_prog) *)
let compile_common_semantics = prove
 (`!(ffi:(FFI)ffi_state) (c:clos_to_bvl_config) co1
     (cc:B->clos_prog->(byte list#int64 list#B)option) es1 c' code2.
     ~(clos_semantics ffi (clos_to_bvl_config_max_app c) FEMPTY co1
         (compile_common_inc c cc) es1 = Fail) /\
     compile_common c es1 = (c',code2) /\
     (!n. SND (SND (co1 n)) = []) /\
     (clos_to_bvl_config_do_mti c
      ==> 1 <= clos_to_bvl_config_max_app c /\ ALL no_mti es1 /\
          (!n. ALL no_mti (FST (SND (co1 n))))) /\
     (clos_to_bvl_config_do_call c
      ==> every_Fn_vs_NONE es1 /\
          is_state_oracle clos_call_compile_inc
            (known_co (clos_to_bvl_config_known_conf c)
               (state_co (ignore_table clos_number_compile_inc)
                  (pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
                              (clos_to_bvl_config_max_app c)) o co1))) /\
          FST (SND (SND (FST (co1 0)))) =
            FST (SND (clos_call_compile (clos_to_bvl_config_do_call c)
                        (SND (compile_inc_post_kcompile c es1))))) /\
     (IS_SOME (clos_to_bvl_config_known_conf c)
      ==> 1 <= clos_to_bvl_config_max_app c /\
          oracle_monotonic (SET_OF_BAG o clos_elist_globals o FST o SND) (<)
            (SET_OF_BAG (clos_elist_globals es1)) co1 /\
          is_state_oracle (clos_known_compile_inc (THE (clos_to_bvl_config_known_conf c)))
            (pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o
               state_co (ignore_table clos_number_compile_inc)
                 (pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
                             (clos_to_bvl_config_max_app c)) o co1)) /\
          FST (SND (FST (co1 0))) =
            clos_known_config_val_approx_spt (THE (FST (compile_inc_post_kcompile c es1))) /\
          (!n'. BAG_ALL_DISTINCT (clos_elist_globals (FST (SND (co1 n')))) /\
                ALL clos_esgc_free (FST (SND (co1 n'))))) /\
     ~contains_App_SOME (clos_to_bvl_config_max_app c) es1 /\
     clos_knownProof_syntax_ok es1 /\
     (!n. ~contains_App_SOME (clos_to_bvl_config_max_app c) (FST (SND (co1 n))) /\
          every_Fn_vs_NONE (FST (SND (co1 n)))) /\
     is_state_oracle (ignore_table clos_number_compile_inc)
       (pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
                   (clos_to_bvl_config_max_app c)) o co1) /\
     FST (FST (co1 0)) >=
       FST (renumber_code_locs_list
              (make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH es1)))
              (clos_mti_compile (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c)
                 es1)) /\
     oracle_monotonic (set_of_list o MAP FST o SND o SND) (<) (pred_set_count (FST (FST (co1 0))))
       (state_co (cond_call_compile_inc (clos_to_bvl_config_do_call c))
          (known_co (clos_to_bvl_config_known_conf c)
             (state_co (ignore_table clos_number_compile_inc)
                (pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
                            (clos_to_bvl_config_max_app c)) o co1))))
     ==> clos_semantics ffi (clos_to_bvl_config_max_app c) (alist_to_fmap code2)
           (pure_co clos_annotate_compile_inc o
            state_co (cond_call_compile_inc (clos_to_bvl_config_do_call c))
              (known_co (clos_to_bvl_config_known_conf c)
                 (state_co (ignore_table clos_number_compile_inc)
                    (pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
                                (clos_to_bvl_config_max_app c)) o co1))))
           cc [clos_Call backend_common_None 0 (clos_to_bvl_config_start c') []] =
         clos_semantics ffi (clos_to_bvl_config_max_app c) FEMPTY co1
           (compile_common_inc c cc) es1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C2BP3AUX_compile_common_parts) THEN
  ABBREV_TAC `co_m = pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
                     (clos_to_bvl_config_max_app c)) o (co1:num->(num#(val_approx)spt#num_set#B)#clos_prog)` THEN
  ABBREV_TAC `co_n = state_co (ignore_table clos_number_compile_inc) (co_m:num->(num#(val_approx)spt#num_set#B)#clos_prog)` THEN
  ABBREV_TAC `co_k = known_co (clos_to_bvl_config_known_conf c) (co_n:num->((val_approx)spt#num_set#B)#clos_prog)` THEN
  ABBREV_TAC `co_c = state_co (cond_call_compile_inc (clos_to_bvl_config_do_call c)) (co_k:num->(num_set#B)#clos_prog)` THEN
  SUBGOAL_THEN `!n. FST ((co_m:num->(num#(val_approx)spt#num_set#B)#clos_prog) n) = FST (co1 n) /\
                 FST (SND (co_m n)) =
                   clos_mti_compile (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c)
                     (FST (SND ((co1:num->(num#(val_approx)spt#num_set#B)#clos_prog) n))) /\
                 SND (SND (co_m n)) = []` (LABEL_TAC "com") THENL
   [EXPAND_TAC "co_m" THEN ASM_REWRITE_TAC[C2BP3AUX_co_m; COND_ID]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. FST ((co_n:num->((val_approx)spt#num_set#B)#clos_prog) n) =
                     SND (FST ((co1:num->(num#(val_approx)spt#num_set#B)#clos_prog) n)) /\
                 FST (SND (co_n n)) =
                   SND (clos_number_compile_inc (FST (FST (co1 n)))
                     (clos_mti_compile (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c)
                        (FST (SND (co1 n))))) /\
                 SND (SND (co_n n)) = []` (LABEL_TAC "con") THENL
   [EXPAND_TAC "co_n" THEN ASM_REWRITE_TAC[C2BP3AUX_co_n]; ALL_TAC] THEN
  ABBREV_TAC `cc_c = state_cc (cond_call_compile_inc (clos_to_bvl_config_do_call c))
                       (pure_cc clos_annotate_compile_inc
                          (cc:B->clos_prog->(byte list#int64 list#B)option))` THEN
  ABBREV_TAC `cc_k = known_cc (clos_to_bvl_config_known_conf c)
                       (cc_c:num_set#B->clos_prog->(byte list#int64 list#num_set#B)option)` THEN
  ABBREV_TAC `cc_n = state_cc (ignore_table clos_number_compile_inc)
                       (cc_k:(val_approx)spt#num_set#B->clos_prog->(byte list#int64 list#(val_approx)spt#num_set#B)option)` THEN
  SUBGOAL_THEN `compile_common_inc c (cc:B->clos_prog->(byte list#int64 list#B)option) =
                pure_cc (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
                           (clos_to_bvl_config_max_app c)) cc_n`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [REWRITE_TAC[compile_common_inc_def] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the clos_mti phase *)
  SUBGOAL_THEN `clos_semantics (ffi:(FFI)ffi_state) (clos_to_bvl_config_max_app c) FEMPTY
                  (co_m:num->(num#(val_approx)spt#num_set#B)#clos_prog)
                  (cc_n:(num#(val_approx)spt#num_set#B)->clos_prog->(byte list#int64 list#(num#(val_approx)spt#num_set#B))option)
                  (clos_mti_compile (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c) es1) =
                clos_semantics ffi (clos_to_bvl_config_max_app c) FEMPTY
                  (co1:num->(num#(val_approx)spt#num_set#B)#clos_prog)
                  (pure_cc (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
                              (clos_to_bvl_config_max_app c)) cc_n) es1` (LABEL_TAC "E1") THENL
   [EXPAND_TAC "co_m" THEN MATCH_MP_TAC semantics_cond_mti_compile_inc THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      CLOS2AUX_CONST_IN "no_mti" (concl th))) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(clos_semantics (ffi:(FFI)ffi_state) (clos_to_bvl_config_max_app c) FEMPTY
                  (co_m:num->(num#(val_approx)spt#num_set#B)#clos_prog)
                  (cc_n:(num#(val_approx)spt#num_set#B)->clos_prog->(byte list#int64 list#(num#(val_approx)spt#num_set#B))option)
                  (clos_mti_compile (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c) es1) = Fail)`
    (LABEL_TAC "F1") THENL [USE_THEN "E1" SUBST1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the clos_number phase *)
  SUBGOAL_THEN `clos_semantics (ffi:(FFI)ffi_state) (clos_to_bvl_config_max_app c) FEMPTY
                  (co_n:num->((val_approx)spt#num_set#B)#clos_prog)
                  (cc_k:(val_approx)spt#num_set#B->clos_prog->(byte list#int64 list#(val_approx)spt#num_set#B)option)
                  es_n =
                clos_semantics ffi (clos_to_bvl_config_max_app c) FEMPTY
                  (co_m:num->(num#(val_approx)spt#num_set#B)#clos_prog)
                  (cc_n:(num#(val_approx)spt#num_set#B)->clos_prog->(byte list#int64 list#(num#(val_approx)spt#num_set#B))option)
                  (clos_mti_compile (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c) es1)`
    (LABEL_TAC "E2") THENL
   [MP_TAC(ISPECL [`make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH (es1:clos_exp list)))`;
                   `ffi:(FFI)ffi_state`; `clos_to_bvl_config_max_app c`;
                   `co_m:num->(num#(val_approx)spt#num_set#B)#clos_prog`;
                   `cc_k:(val_approx)spt#num_set#B->clos_prog->(byte list#int64 list#(val_approx)spt#num_set#B)option`;
                   `clos_mti_compile (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c) es1`]
         (GEN_ALL semantics_number)) THEN
    FIRST_ASSUM(fun th -> if CLOS2AUX_CONST_IN "renumber_code_locs_list" (concl th) &&
                            is_eq (concl th) && is_pair (rhs (concl th))
                         then REWRITE_TAC[th; SND] else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "F1" MP_TAC THEN EXPAND_TAC "cc_n" THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[contains_App_SOME_compile];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(clos_semantics (ffi:(FFI)ffi_state) (clos_to_bvl_config_max_app c) FEMPTY
                  (co_n:num->((val_approx)spt#num_set#B)#clos_prog)
                  (cc_k:(val_approx)spt#num_set#B->clos_prog->(byte list#int64 list#(val_approx)spt#num_set#B)option)
                  es_n = Fail)` (LABEL_TAC "F2") THENL
   [USE_THEN "E2" SUBST1_TAC THEN USE_THEN "F1" ACCEPT_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if C2BP3AUX_is_eq_app "renumber_code_locs_list" th
                          then LABEL_TAC "ren" th else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if C2BP3AUX_is_eq_app "clos_known_compile" th
                          then LABEL_TAC "kco" th else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if C2BP3AUX_is_eq_app "clos_call_compile" th
                          then LABEL_TAC "cco" th else NO_TAC) THEN
  (* the clos_known phase *)
  SUBGOAL_THEN `clos_knownProof_syntax_ok es_n` (LABEL_TAC "S1") THENL
   [UNDISCH_TAC `clos_knownProof_syntax_ok es1` THEN
    REWRITE_TAC[clos_knownProof_syntax_ok_def] THEN STRIP_TAC THEN
    USE_THEN "ren" (fun th ->
      MP_TAC(REWRITE_RULE[th; SND] (SPECL
        [`make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH (es1:clos_exp list)))`;
         `clos_mti_compile (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c) es1`]
        (CONJUNCT1 renumber_code_locs_every_Fn_vs_NONE))) THEN
      MP_TAC(MATCH_MP (CONJUNCT1 renumber_code_locs_elist_globals) th) THEN
      MP_TAC(MATCH_MP (CONJUNCT1 renumber_code_locs_esgc_free) (CONJ th
        (MP (ISPECL [`clos_to_bvl_config_do_mti c`; `es1:clos_exp list`]
               (INST [`clos_to_bvl_config_max_app c`,`max_app:num`] compile_preserves_esgc_free))
            (ASSUME `ALL clos_esgc_free es1`))))) THEN
    REWRITE_TAC[compile_every_Fn_vs_NONE; compile_elist_globals] THEN
    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compile_inc_post_kcompile c es1 = (kc,es_k)` (LABEL_TAC "post") THENL
   [REWRITE_TAC[compile_inc_post_kcompile_def] THEN
    USE_THEN "ren" (fun th -> REWRITE_TAC[th; SND]) THEN USE_THEN "kco" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IS_SOME (clos_to_bvl_config_known_conf c)
                ==> clos_knownProof_syntax_oracle_ok (THE (clos_to_bvl_config_known_conf c)) es_n
                      (co_n:num->((val_approx)spt#num_set#B)#clos_prog)
                      (clos_known_config_val_approx_spt (THE kc)) /\
                    1 <= clos_to_bvl_config_max_app c` (LABEL_TAC "S2") THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      CLOS2AUX_CONST_IN "IS_SOME" (lhand (concl th)))) THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "post" (fun th -> REWRITE_TAC[th; FST]) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[clos_knownProof_syntax_oracle_ok_def] THEN
    USE_THEN "con" (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THENL
     [EXPAND_TAC "co_n" THEN MATCH_MP_TAC number_monotonic_elist_globals THEN
      USE_THEN "ren" (fun th ->
        REWRITE_TAC[MATCH_MP (CONJUNCT1 renumber_code_locs_elist_globals) th]) THEN
      EXPAND_TAC "co_m" THEN MATCH_MP_TAC cond_mti_monotonic_elist_globals THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    GEN_TAC THEN REWRITE_TAC[clos_knownProof_syntax_ok_def; every_Fn_vs_NONE_ncompile_inc;
      compile_every_Fn_vs_NONE; elist_globals_SND_ncompile_inc; compile_elist_globals] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC number_compile_inc_esgc_free THEN
    MATCH_MP_TAC (INST [`clos_to_bvl_config_max_app c`,`max_app:num`]
                    compile_preserves_esgc_free) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `clos_semantics (ffi:(FFI)ffi_state) (clos_to_bvl_config_max_app c) FEMPTY
                  (co_k:num->(num_set#B)#clos_prog)
                  (cc_c:num_set#B->clos_prog->(byte list#int64 list#num_set#B)option) es_k =
                clos_semantics ffi (clos_to_bvl_config_max_app c) FEMPTY
                  (co_n:num->((val_approx)spt#num_set#B)#clos_prog)
                  (cc_k:(val_approx)spt#num_set#B->clos_prog->(byte list#int64 list#(val_approx)spt#num_set#B)option)
                  es_n` (LABEL_TAC "E3") THENL
   [MP_TAC(ISPECL [`ffi:(FFI)ffi_state`; `clos_to_bvl_config_max_app c`;
                   `co_n:num->((val_approx)spt#num_set#B)#clos_prog`;
                   `cc_k:(val_approx)spt#num_set#B->clos_prog->(byte list#int64 list#(val_approx)spt#num_set#B)option`;
                   `es_n:clos_exp list`; `clos_to_bvl_config_known_conf c`;
                   `cc_c:num_set#B->clos_prog->(byte list#int64 list#num_set#B)option`;
                   `co_k:num->(num_set#B)#clos_prog`; `kc:(clos_known_config)option`;
                   `es_k:clos_exp list`] (GEN_ALL clos_knownProof_semantics_compile)) THEN
    REWRITE_TAC[IMP_IMP] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "F2" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "kco" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "S2" (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THEN FIRST_ASSUM(ACCEPT_TAC o SYM o check (fun th -> is_eq (concl th) &&
      is_var (rhs (concl th)) && (fst(dest_var(rhs(concl th))) = "cc_k" ||
                                  fst(dest_var(rhs(concl th))) = "co_k")));
    ALL_TAC] THEN
  SUBGOAL_THEN `~(clos_semantics (ffi:(FFI)ffi_state) (clos_to_bvl_config_max_app c) FEMPTY
                  (co_k:num->(num_set#B)#clos_prog)
                  (cc_c:num_set#B->clos_prog->(byte list#int64 list#num_set#B)option) es_k = Fail)`
    (LABEL_TAC "F3") THENL
   [USE_THEN "E3" SUBST1_TAC THEN USE_THEN "F2" ACCEPT_TAC; ALL_TAC] THEN
  (* facts on the oracle after clos_known *)
  SUBGOAL_THEN `!k. clos_callProof_syntax_ok (FST (SND ((co_n:num->((val_approx)spt#num_set#B)#clos_prog) k))) /\
                    every_Fn_vs_NONE (FST (SND (co_n k))) /\ every_Fn_SOME (FST (SND (co_n k))) /\
                    SND (SND (co_n k)) = []` (LABEL_TAC "conk") THENL
   [GEN_TAC THEN USE_THEN "con" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[clos_callProof_syntax_ok_def; every_Fn_SOME_ncompile_inc;
                every_Fn_vs_NONE_ncompile_inc; ncompile_inc_code_locs_distinct;
                compile_every_Fn_vs_NONE] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FST (FST ((co_n:num->((val_approx)spt#num_set#B)#clos_prog) 0)) =
                FST (SND (FST ((co1:num->(num#(val_approx)spt#num_set#B)#clos_prog) 0)))`
    (LABEL_TAC "con0") THENL [USE_THEN "con" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  MP_TAC(ISPECL [`clos_to_bvl_config_known_conf c`;
                 `co_n:num->((val_approx)spt#num_set#B)#clos_prog`;
                 `es_n:clos_exp list`; `kc:(clos_known_config)option`; `es_k:clos_exp list`]
                known_co_facts) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  USE_THEN "kco" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      CLOS2AUX_CONST_IN "IS_SOME" (lhand (concl th)) &&
      CLOS2AUX_CONST_IN "is_state_oracle" (concl th))) THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "post" (fun th -> REWRITE_TAC[th; FST]) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "S1" (MP_TAC o REWRITE_RULE[clos_knownProof_syntax_ok_def]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ren" (fun th -> REWRITE_TAC[REWRITE_RULE[th; SND]
      (SPECL [`make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH (es1:clos_exp list)))`;
              `clos_mti_compile (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c) es1`]
             (CONJUNCT1 renumber_code_locs_every_Fn_SOME))]);
    STRIP_TAC] THEN
  SUBGOAL_THEN `oracle_monotonic (set_of_list o code_locs o FST o SND) (<)
                  (set_of_list (code_locs es_n)) (co_n:num->((val_approx)spt#num_set#B)#clos_prog)`
    (LABEL_TAC "omn") THENL
   [MP_TAC(ISPECL [`co_m:num->(num#(val_approx)spt#num_set#B)#clos_prog`;
                   `make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH (es1:clos_exp list)))`;
                   `clos_mti_compile (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c) es1`]
                  renumber_code_locs_monotonic) THEN
    USE_THEN "ren" (fun th -> REWRITE_TAC[th; FST; SND]) THEN
    USE_THEN "com" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> CLOS2AUX_CONST_IN ">=" (concl th))) THEN
      USE_THEN "ren" (fun th -> REWRITE_TAC[th; FST]);
      ALL_TAC] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  (* the clos_call phase *)
  SUBGOAL_THEN `clos_callProof_syntax_ok es_k` (LABEL_TAC "csk") THENL
   [MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] kcompile_csyntax_ok) THEN
    MAP_EVERY EXISTS_TAC [`clos_to_bvl_config_known_conf c`; `es_n:clos_exp list`;
                          `kc:(clos_known_config)option`] THEN
    USE_THEN "kco" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC renumber_code_locs_list_csyntax_ok THEN
    MAP_EVERY EXISTS_TAC [`make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH (es1:clos_exp list)))`;
       `clos_mti_compile (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c) es1`;
       `n:num`] THEN
    USE_THEN "ren" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[compile_every_Fn_vs_NONE] THEN
    UNDISCH_TAC `clos_knownProof_syntax_ok es1` THEN
    SIMP_TAC[clos_knownProof_syntax_ok_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `clos_semantics (ffi:(FFI)ffi_state) (clos_to_bvl_config_max_app c) (alist_to_fmap aux)
                  (co_c:num->B#clos_prog)
                  (pure_cc clos_annotate_compile_inc (cc:B->clos_prog->(byte list#int64 list#B)option))
                  es_c =
                clos_semantics ffi (clos_to_bvl_config_max_app c) FEMPTY
                  (co_k:num->(num_set#B)#clos_prog)
                  (cc_c:num_set#B->clos_prog->(byte list#int64 list#num_set#B)option) es_k`
    (LABEL_TAC "E4") THENL
   [EXPAND_TAC "co_c" THEN EXPAND_TAC "cc_c" THEN REWRITE_TAC[GSYM clos_state_cc_def] THEN
    MATCH_MP_TAC semantics_cond_call_compile_inc THEN
    MAP_EVERY EXISTS_TAC [`g:num_set`] THEN
    USE_THEN "cco" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "F3" MP_TAC THEN EXPAND_TAC "cc_c" THEN REWRITE_TAC[GSYM clos_state_cc_def] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    EXISTS_TAC `aux:(num#num#clos_exp)list` THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "csk" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[C2BP3AUX_pair_CASE_FST_SND] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
        CLOS2AUX_CONST_IN "clos_call_compile_inc" (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
        CLOS2AUX_CONST_IN "clos_call_compile_inc" (concl th))) THEN
      USE_THEN "post" (fun th -> REWRITE_TAC[th; SND]) THEN
      USE_THEN "cco" (fun th -> REWRITE_TAC[th; FST; SND]) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      EXPAND_TAC "co_k" THEN REWRITE_TAC[FST_known_co] THEN
      USE_THEN "con" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp (concl th) &&
      CLOS2AUX_CONST_IN "oracle_monotonic" (concl th) &&
      CLOS2AUX_CONST_IN "code_locs" (concl th))) THEN
    USE_THEN "omn" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(clos_semantics (ffi:(FFI)ffi_state) (clos_to_bvl_config_max_app c) (alist_to_fmap aux)
                  (co_c:num->B#clos_prog)
                  (pure_cc clos_annotate_compile_inc (cc:B->clos_prog->(byte list#int64 list#B)option))
                  es_c = Fail)` (LABEL_TAC "F4") THENL
   [USE_THEN "E4" SUBST1_TAC THEN USE_THEN "F3" ACCEPT_TAC; ALL_TAC] THEN
  (* the locations, for chain_exps *)
  SUBGOAL_THEN `LENGTH (es_c:clos_exp list) = LENGTH (es1:clos_exp list)` (LABEL_TAC "lenc") THENL
   [USE_THEN "cco" (fun th -> REWRITE_TAC[GSYM(MATCH_MP clos_call_compile_LENGTH th)]) THEN
    USE_THEN "kco" (fun th -> REWRITE_TAC[MATCH_MP clos_knownProof_compile_LENGTH th]) THEN
    USE_THEN "ren" (fun th -> REWRITE_TAC[MATCH_MP renumber_code_locs_list_IMP_LENGTH th]) THEN
    REWRITE_TAC[clos_mtiProof_compile_length];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. MEM y (code_locs (es_n:clos_exp list)) ==>
                    make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH (es1:clos_exp list))) <= y /\
                    y < n /\ EVEN y` (LABEL_TAC "locsn") THENL
   [USE_THEN "ren" (fun th ->
      MP_TAC(REWRITE_RULE[th; FST; SND] (SPECL
        [`make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH (es1:clos_exp list)))`;
         `clos_mti_compile (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c) es1`]
        renumber_code_locs_list_distinct)) THEN
      MP_TAC(REWRITE_RULE[th; FST; SND; EVEN_make_even] (SPECL
        [`make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH (es1:clos_exp list)))`;
         `clos_mti_compile (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c) es1`]
        (CONJUNCT1 renumber_code_locs_EVEN)))) THEN
    REWRITE_TAC[GSYM ALL_MEM; GT] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `EVEN n` (LABEL_TAC "evn") THENL
   [USE_THEN "ren" (fun th ->
      MP_TAC(REWRITE_RULE[th; FST; SND; EVEN_make_even] (SPECL
        [`make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH (es1:clos_exp list)))`;
         `clos_mti_compile (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c) es1`]
        (CONJUNCT1 renumber_code_locs_EVEN)))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN FDOM (alist_to_fmap (aux:(num#num#clos_exp)list)) ==>
                    ?y. x = SUC y /\ MEM y (code_locs (es_n:clos_exp list))` (LABEL_TAC "auxl") THENL
   [REWRITE_TAC[FDOM_alist_to_fmap] THEN
    USE_THEN "cco" (MP_TAC o MATCH_MP ccompile_aux_subset) THEN
    USE_THEN "kco" (MP_TAC o MATCH_MP LIST_TO_BAG_SUBSET o MATCH_MP compile_code_locs_bag) THEN
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_SET_OF_LIST] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `clos_to_bvl_config_next_loc c + LENGTH (es1:clos_exp list) <=
                make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH es1)) /\
                make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH es1)) <= n /\
                n <= FST (FST ((co1:num->(num#(val_approx)spt#num_set#B)#clos_prog) 0))`
    (LABEL_TAC "bounds") THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[make_even_def] THEN COND_CASES_TAC THEN ARITH_TAC;
      USE_THEN "ren" (fun th -> MP_TAC(MATCH_MP (CONJUNCT1 renumber_code_locs_imp_inc) th)) THEN
      REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> CLOS2AUX_CONST_IN ">=" (concl th))) THEN
      USE_THEN "ren" (fun th -> REWRITE_TAC[th; FST]) THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE ((+) (clos_to_bvl_config_next_loc c)) (pred_set_count (LENGTH (es_c:clos_exp list))))
                  (FDOM (alist_to_fmap (aux:(num#num#clos_exp)list)))` (LABEL_TAC "D1") THENL
   [REWRITE_TAC[IN_DISJOINT; IN_IMAGE; IN_COUNT; NOT_EXISTS_THM] THEN
    X_GEN_TAC `x:num` THEN
    REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `x':num` THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `x IN FDOM (alist_to_fmap (aux:(num#num#clos_exp)list))` THEN
    USE_THEN "auxl" (fun th -> DISCH_THEN (MP_TAC o MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "locsn" (fun th -> MP_TAC (CONJUNCT1 (MATCH_MP th
      (ASSUME `MEM (y:num) (code_locs (es_n:clos_exp list))`)))) THEN
    USE_THEN "lenc" (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    USE_THEN "bounds" MP_TAC THEN
    UNDISCH_TAC `x' < LENGTH (es1:clos_exp list)` THEN
    UNDISCH_TAC `x = SUC y` THEN UNDISCH_TAC `x = clos_to_bvl_config_next_loc c + x'` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((+) (clos_to_bvl_config_next_loc c)) (pred_set_count (LENGTH (es_c:clos_exp list))) UNION
                FDOM (alist_to_fmap (aux:(num#num#clos_exp)list)) SUBSET
                pred_set_count (FST (FST ((co1:num->(num#(val_approx)spt#num_set#B)#clos_prog) 0)))`
    (LABEL_TAC "D2") THENL
   [REWRITE_TAC[SUBSET; IN_UNION; IN_IMAGE; IN_COUNT] THEN X_GEN_TAC `x:num` THEN
    STRIP_TAC THENL
     [USE_THEN "lenc" (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
      USE_THEN "bounds" MP_TAC THEN
      UNDISCH_TAC `x' < LENGTH (es1:clos_exp list)` THEN
      UNDISCH_TAC `x = clos_to_bvl_config_next_loc c + x'` THEN ARITH_TAC;
      UNDISCH_TAC `x IN FDOM (alist_to_fmap (aux:(num#num#clos_exp)list))` THEN
      USE_THEN "auxl" (fun th -> DISCH_THEN (MP_TAC o MATCH_MP th)) THEN
      DISCH_THEN(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
      USE_THEN "locsn" (fun th -> STRIP_ASSUME_TAC (MATCH_MP th
        (ASSUME `MEM (y:num) (code_locs (es_n:clos_exp list))`))) THEN
      SUBGOAL_THEN `~(SUC y = n)` ASSUME_TAC THENL
       [DISCH_TAC THEN USE_THEN "evn" MP_TAC THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[EVEN];
        ALL_TAC] THEN
      USE_THEN "bounds" MP_TAC THEN
      UNDISCH_TAC `~(SUC y = n)` THEN UNDISCH_TAC `y < n` THEN
      UNDISCH_TAC `x = SUC y` THEN ARITH_TAC];
    ALL_TAC] THEN
  (* the chain_exps phase *)
  SUBGOAL_THEN `clos_semantics (ffi:(FFI)ffi_state) (clos_to_bvl_config_max_app c)
                  (FUNION (alist_to_fmap (chain_exps (clos_to_bvl_config_next_loc c) es_c))
                     (alist_to_fmap (aux:(num#num#clos_exp)list)))
                  (co_c:num->B#clos_prog)
                  (pure_cc clos_annotate_compile_inc (cc:B->clos_prog->(byte list#int64 list#B)option))
                  [clos_Call backend_common_None 0 (clos_to_bvl_config_next_loc c) []] =
                clos_semantics ffi (clos_to_bvl_config_max_app c) (alist_to_fmap aux) co_c
                  (pure_cc clos_annotate_compile_inc cc) es_c` (LABEL_TAC "E5") THENL
   [MATCH_MP_TAC chain_exps_semantics_call THEN
    USE_THEN "F4" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "D1" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC oracle_monotonic_init_subset THEN
    EXISTS_TAC `pred_set_count (FST (FST ((co1:num->(num#(val_approx)spt#num_set#B)#clos_prog) 0)))` THEN
    USE_THEN "D2" (fun th -> REWRITE_TAC[th]) THEN
    FIRST_ASSUM(ACCEPT_TAC o check (fun th -> CLOS2AUX_CONST_IN "oracle_monotonic" (concl th) &&
      not (is_imp (concl th)) && CLOS2AUX_CONST_IN "pred_set_count" (concl th)));
    ALL_TAC] THEN
  (* the clos_annotate phase *)
  REWRITE_TAC[clos_to_bvl_config_INFO.ri_accfupds; K_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM C2BP3AUX_annotate_Call] THEN
  MP_TAC(ISPECL [`ffi:(FFI)ffi_state`; `clos_to_bvl_config_max_app c`;
                 `APPEND (chain_exps (clos_to_bvl_config_next_loc c) es_c) (aux:(num#num#clos_exp)list)`;
                 `co_c:num->B#clos_prog`; `cc:B->clos_prog->(byte list#int64 list#B)option`;
                 `[clos_Call backend_common_None 0 (clos_to_bvl_config_next_loc c) []]`]
                (GEN_ALL semantics_annotate)) THEN
  REWRITE_TAC[alist_to_fmap_APPEND] THEN
  USE_THEN "E5" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "F4" (fun th -> REWRITE_TAC[th]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[every_Fn_vs_NONE_def; MAP_APPEND; every_Fn_vs_NONE_APPEND;
                chain_exps_every_Fn_vs_NONE] THEN
    USE_THEN "cco" (fun th -> USE_THEN "csk" (fun th2 ->
      REWRITE_TAC[MATCH_MP (MATCH_MP calls_compile_csyntax_ok th) th2])) THEN
    X_GEN_TAC `k:num` THEN EXPAND_TAC "co_c" THEN
    REWRITE_TAC[GEN_ALL SND_state_co] THEN
    MP_TAC(ISPECL [`clos_to_bvl_config_do_call c`;
                   `FST (FST ((co_k:num->(num_set#B)#clos_prog) k))`;
                   `SND ((co_k:num->(num_set#B)#clos_prog) k)`]
                  every_Fn_vs_NONE_cond_call_compile_inc) THEN
    MP_TAC(SPEC `k:num` (ASSUME
      `!k. clos_callProof_syntax_ok (FST (SND ((co_k:num->(num_set#B)#clos_prog) k)))`)) THEN
    MP_TAC(SPEC `k:num` (ASSUME `!k. SND (SND ((co_k:num->(num_set#B)#clos_prog) k)) = []`)) THEN
    SIMP_TAC[clos_callProof_syntax_ok_def; MAP; every_Fn_vs_NONE_def];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN USE_THEN "E4" SUBST1_TAC THEN USE_THEN "E3" SUBST1_TAC THEN
  USE_THEN "E2" SUBST1_TAC THEN USE_THEN "E1" ACCEPT_TAC);;

(* HOL4 line 7681 *)
let REPLICATE_1 = prove
 (`!(x:A). REPLICATE 1 x = [x]`,
  REWRITE_TAC[num_CONV `1`; REPLICATE]);;

let _ = cake_add_simps [REPLICATE_1];;

let C2BP3AUX_do_app_Const = prove
 (`!i (s:(C,FFI)bvl_state). bvl_do_app (IntOp (clos_Const i)) [] s = Rval (bvl_Number i,s)`,
  REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvl_do_int_app_def] THEN CAKE_REWRITE_TAC[]);;

let C2BP3AUX_do_app_AllocGlobal = prove
 (`!i (s:(C,FFI)bvl_state).
     bvl_do_app (GlobOp AllocGlobal) [bvl_Number i] s =
     if i < &0 then Rerr (Rabort Rtype_error)
     else Rval (bvl_Unit, bvl_state_globals_fupd
                 (combin_K (APPEND (bvl_state_globals s) (REPLICATE (num_of_int i) NONE))) s)`,
  REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[]);;

let C2BP3AUX_do_app_SetGlobal = prove
 (CASE_TERM `!n v (s:(C,FFI)bvl_state).
     bvl_do_app (GlobOp (SetGlobal n)) [v] s =
     match get_global n (bvl_state_globals s) with
       SOME _ -> Rval (bvl_Unit,
                       bvl_state_globals_fupd (combin_K (LUPDATE (SOME v) n (bvl_state_globals s))) s)
     | NONE -> Rerr (Rabort Rtype_error)`,
  REWRITE_TAC[bvl_do_app_def] THEN CAKE_REWRITE_TAC[]);;

(* the code of init_globals, run on a state without globals *)
let C2BP3AUX_eval_init_globals = prove
 (`!max_app start_loc (st:(C,FFI)bvl_state).
     (!m n. m < max_app /\ n < m
            ==> partial_app_fn_location max_app m n IN domain (bvl_state_code st)) /\
     bvl_state_globals st = []
     ==> bvl_evaluate ([init_globals max_app start_loc],[],st) =
         bvl_evaluate ([bvl_Call 0 (SOME start_loc) []],[bvl_Unit; bvl_Unit],
                       bvl_state_globals_fupd (combin_K [SOME (global_table max_app)]) st)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[init_globals_def; mk_label_def] THEN
  SUBGOAL_THEN `bvl_evaluate ([bvl_Op (GlobOp AllocGlobal) [bvl_Op (IntOp (clos_Const (&1))) []]],[],
                              st:(C,FFI)bvl_state) =
                (Rval [bvl_Unit], bvl_state_globals_fupd (combin_K [NONE]) st)` ASSUME_TAC THENL
   [REWRITE_TAC[bvl_evaluate_def] THEN CAKE_REWRITE_TAC[REVERSE; APPEND] THEN
    REWRITE_TAC[C2BP3AUX_do_app_Const] THEN CAKE_REWRITE_TAC[REVERSE; APPEND] THEN
    REWRITE_TAC[C2BP3AUX_do_app_AllocGlobal] THEN CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN
    ASM_REWRITE_TAC[NUM_OF_INT_OF_NUM; REPLICATE_1; APPEND] THEN CAKE_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bvl_evaluate (REVERSE (FLAT (list_of_seq (\tot. list_of_seq
                   (\prev. bvl_Op (clos_Label (partial_app_fn_location max_app tot prev)) []) tot)
                   max_app)), [bvl_Unit], bvl_state_globals_fupd (combin_K [NONE]) (st:(C,FFI)bvl_state)) =
                (Rval (REVERSE (FLAT (list_of_seq (\tot. list_of_seq
                   (\prev. bvl_CodePtr (partial_app_fn_location max_app tot prev)) tot) max_app))),
                 bvl_state_globals_fupd (combin_K [NONE]) st)` ASSUME_TAC THENL
   [MATCH_MP_TAC evaluate_init THEN ASM_REWRITE_TAC[bvl_state_INFO.ri_accfupds];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [bvl_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CAKE_REWRITE_TAC[APPEND] THEN
  GEN_REWRITE_TAC LAND_CONV [bvl_evaluate_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [bvl_evaluate_def] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [bvl_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[REVERSE_REVERSE; bvl_do_app_Cons] THEN
  REWRITE_TAC[REVERSE; APPEND; C2BP3AUX_do_app_SetGlobal; partial_app_label_table_loc_def;
              bvl_state_INFO.ri_accfupds; K_THM; get_global_def; LENGTH; EL; HD;
              ARITH_RULE `0 < SUC 0`] THEN
  CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LUPDATE_def; bvl_state_INFO.ri_fupdfupds; C2BP3AUX_K_o_K; GSYM global_table_def] THEN
  GEN_REWRITE_TAC RAND_CONV [bvl_evaluate_def] THEN
  REWRITE_TAC[bvl_evaluate_def; bvl_state_INFO.ri_accfupds] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds]);;

(* HOL4 line 7687 *)
let clos_to_bvlProof_compile_prog_semantics = prove
 (`!(ffi:(FFI)ffi_state) max_app code1 (co1:num->C#clos_prog) cc1 start code2 prog1 prog2
     nsm1 (co2:num->C#(num#num#bvl_exp)list) cc2.
     ~(clos_semantics ffi max_app code1 co1 cc1 [clos_Call backend_common_None 0 start []] = Fail) /\
     (!name arity c.
        FLOOKUP code1 name = SOME (arity,c)
        ==> ?aux1 c2 aux2.
              clos_to_bvl_compile_exps max_app [c] aux1 = ([c2],aux2) /\
              lookup (name + num_stubs max_app) code2 = SOME (arity,c2) /\
              clos_to_bvlProof_code_installed aux2 code2) /\
     clos_to_bvl_compile_prog max_app prog1 = prog2 /\
     clos_to_bvlProof_init_code code1 code2 max_app /\
     FEVERY (\p. every_Fn_SOME [SND (SND p)]) code1 /\
     FEVERY (\p. every_Fn_vs_SOME [SND (SND p)]) code1 /\
     lookup nsm1 code2 = SOME (0,init_globals max_app (num_stubs max_app + start)) /\
     lookup (num_stubs max_app - 2) code2 = SOME (2,force_thunk_code) /\
     compile_oracle_inv max_app code1 cc1 co1 code2 cc2 co2 /\
     clos_to_bvlProof_code_installed prog2 code2
     ==> bvl_semantics ffi code2 co2 cc2 nsm1 =
         clos_semantics ffi max_app code1 co1 cc1 [clos_Call backend_common_None 0 start []]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C2BP3AUX_sem_eq THEN
  FIRST_ASSUM(fun th -> if CLOS2AUX_CONST_IN "Fail" (concl th)
     then REWRITE_TAC[REWRITE_RULE[CLOSPROPSAUX_sem_fail; NOT_EXISTS_THM] th] else NO_TAC) THEN
  X_GEN_TAC `k:num` THEN
  SUBGOAL_THEN `~(FST (clos_evaluate ([clos_Call backend_common_None 0 start []],[],
                    clos_initial_state (ffi:(FFI)ffi_state) max_app code1 (co1:num->C#clos_prog) cc1 k)) =
                  Rerr (Rabort Rtype_error))` MP_TAC THENL
   [FIRST_ASSUM(fun th -> if CLOS2AUX_CONST_IN "Fail" (concl th)
      then MP_TAC(REWRITE_RULE[CLOSPROPSAUX_sem_fail; NOT_EXISTS_THM] th) else NO_TAC) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. bvl_evaluate ([bvl_Call 0 (SOME nsm1) []],[],
                      bvl_initial_state (ffi:(FFI)ffi_state) code2 (co2:num->C#(num#num#bvl_exp)list) cc2 j) =
                  if j < 1 then (Rerr (Rabort Rtimeout_error),
                                 bvl_state_clock_fupd (combin_K 0) (bvl_initial_state ffi code2 co2 cc2 j))
                  else bvl_evaluate ([init_globals max_app (num_stubs max_app + start)],[],
                                     bvl_initial_state ffi code2 co2 cc2 (j - 1))`
    (LABEL_TAC "bcall") THENL
   [GEN_TAC THEN REWRITE_TAC[bvl_evaluate_def] THEN CAKE_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[bvl_find_code_def; bvl_initial_state_def; bvl_state_INFO.ri_accessors] THEN
    CAKE_REWRITE_TAC[LENGTH] THEN REWRITE_TAC[ADD_CLAUSES; bvl_dec_clock_def] THEN
    REWRITE_TAC[bvl_state_INFO.ri_fupds; bvl_state_INFO.ri_accessors; K_THM];
    ALL_TAC] THEN
  REWRITE_TAC[clos_evaluate_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[clos_find_code_def; clos_initial_state_def; clos_state_INFO.ri_accessors] THEN
  REWRITE_TAC[GSYM clos_initial_state_def] THEN
  CASES_ON `FLOOKUP (code1:(num,num#clos_exp)fmap) start` THEN CAKE_REWRITE_TAC[] THEN
  CASES_ON `a:num#clos_exp` THEN CAKE_REWRITE_TAC[LENGTH] THEN
  ASM_CASES_TAC `x = 0` THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN USE_THEN "bcall" (fun th -> REWRITE_TAC[th]) THEN
  ALL_TAC THEN
  DISCH_TAC THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[ARITH_RULE `0 < 0 + 1 /\ 0 + 0 < 1`; FST; SND] THEN
    REWRITE_TAC[C2BP3AUX_result_rel_T; clos_initial_state_def; bvl_initial_state_def;
                clos_state_INFO.ri_accfupds; bvl_state_INFO.ri_accfupds;
                clos_state_INFO.ri_accessors; bvl_state_INFO.ri_accessors] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `k < 0 + 1 <=> k = 0`]) THEN
  ASM_REWRITE_TAC[ARITH_RULE `k < 0 + 1 <=> k = 0`] THEN
  MP_TAC(ISPEC `clos_evaluate ([y],[],clos_dec_clock (0 + 1)
           (clos_initial_state (ffi:(FFI)ffi_state) max_app code1 (co1:num->C#clos_prog) cc1 k))`
         PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:(clos_v list,clos_v)result`
    (X_CHOOSE_THEN `s2:(C,FFI)clos_state` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST]) THEN
  FIRST_ASSUM(fun th -> if is_forall (concl th) && CLOS2AUX_CONST_IN "clos_to_bvl_compile_exps" (concl th) &&
                          CLOS2AUX_CONST_IN "FLOOKUP" (concl th)
     then MP_TAC(MATCH_MP th (ASSUME `FLOOKUP (code1:(num,num#clos_exp)fmap) start = SOME (0,y)`))
     else NO_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `aux1:(num#num#bvl_exp)list` (X_CHOOSE_THEN `c2:bvl_exp`
    (X_CHOOSE_THEN `aux2:(num#num#bvl_exp)list` STRIP_ASSUME_TAC))) THEN
  ALL_TAC THEN
  SUBGOAL_THEN `~(r1 = Rerr (Rabort Rtype_error):(clos_v list,clos_v)result)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
      CLOS2AUX_CONST_IN "clos_evaluate" (concl th))) THEN
    ASM_REWRITE_TAC[ARITH_RULE `k < 0 + 1 <=> k = 0`; FST];
    ALL_TAC] THEN
  ABBREV_TAC `T1 = bvl_state_globals_fupd (combin_K [SOME (global_table max_app)])
                     (bvl_initial_state (ffi:(FFI)ffi_state) code2
                        (co2:num->C#(num#num#bvl_exp)list) cc2 0)` THEN
  MP_TAC(ISPECL [`([y:clos_exp],[]:clos_v list,clos_dec_clock (0 + 1)
           (clos_initial_state (ffi:(FFI)ffi_state) max_app code1 (co1:num->C#clos_prog) cc1 k))`;
                 `[y:clos_exp]`; `[]:clos_v list`;
                 `clos_dec_clock (0 + 1)
                    (clos_initial_state (ffi:(FFI)ffi_state) max_app code1 (co1:num->C#clos_prog) cc1 k)`;
                 `aux1:(num#num#bvl_exp)list`; `T1:(C,FFI)bvl_state`; `[]:bvl_v list`;
                 `FEMPTY:(num,num)fmap`; `r1:(clos_v list,clos_v)result`; `s2:(C,FFI)clos_state`;
                 `[c2:bvl_exp]`; `aux2:(num#num#bvl_exp)list`]
                (CONJUNCT1 clos_to_bvlProof_compile_exps_correct)) THEN
  ALL_TAC THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[clos_dec_clock_def; clos_initial_state_def; clos_state_INFO.ri_accfupds;
                    clos_state_INFO.ri_accessors; K_THM] THEN
    REWRITE_TAC[GSYM clos_initial_state_def] THEN
    EXPAND_TAC "T1" THEN
    REWRITE_TAC[bvl_initial_state_def; bvl_state_INFO.ri_accfupds; bvl_state_INFO.ri_accessors;
                K_THM; clos_to_bvlProof_env_rel_def] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
   [MP_TAC(MATCH_MP FEVERY_FLOOKUP (CONJ
      (ASSUME `FEVERY (\p. every_Fn_SOME [SND (SND p)]) (code1:(num,num#clos_exp)fmap)`)
      (ASSUME `FLOOKUP (code1:(num,num#clos_exp)fmap) start = SOME (0,y)`))) THEN
    REWRITE_TAC[SND];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(MATCH_MP FEVERY_FLOOKUP (CONJ
      (ASSUME `FEVERY (\p. every_Fn_vs_SOME [SND (SND p)]) (code1:(num,num#clos_exp)fmap)`)
      (ASSUME `FLOOKUP (code1:(num,num#clos_exp)fmap) start = SOME (0,y)`))) THEN
    REWRITE_TAC[SND];
    ALL_TAC] THEN
  REWRITE_TAC[clos_to_bvlProof_state_rel_def; clos_initial_state_def; bvl_state_INFO.ri_accfupds;
              bvl_state_INFO.ri_accessors; clos_state_INFO.ri_accfupds; clos_state_INFO.ri_accessors;
              K_THM; num_added_globals_def; get_global_def] THEN
  REWRITE_TAC[FDOM_FEMPTY; FRANGE_FEMPTY; FLOOKUP_EMPTY; distinctness "option"; EMPTY_SUBSET;
              ALL2; DROP; LENGTH; EL; HD; ARITH_RULE `0 < SUC 0`; ONE] THEN
  ALL_TAC THEN
    REWRITE_TAC[INJ; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `clos_to_bvlProof_init_code code1 code2 max_app` THEN
  REWRITE_TAC[clos_to_bvlProof_init_code_def] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[injectivity "option"; PAIR_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ck:num` (X_CHOOSE_THEN `res':(bvl_v list,bvl_v)result`
    (X_CHOOSE_THEN `t2:(C,FFI)bvl_state` (X_CHOOSE_THEN `f2:(num,num)fmap` STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `ck + 1` THEN
  REWRITE_TAC[ARITH_RULE `~(k + ck + 1 < 1)`; ARITH_RULE `(k + ck + 1) - 1 = k + ck`] THEN
  SUBGOAL_THEN `bvl_evaluate ([init_globals max_app (num_stubs max_app + start)],[],
                  bvl_initial_state (ffi:(FFI)ffi_state) code2 (co2:num->C#(num#num#bvl_exp)list) cc2 (k + ck)) =
                (res',t2)` (fun th -> REWRITE_TAC[th; FST; SND]) THENL
   [MP_TAC(ISPECL [`max_app:num`; `num_stubs max_app + start`;
                   `bvl_initial_state (ffi:(FFI)ffi_state) code2
                      (co2:num->C#(num#num#bvl_exp)list) cc2 (k + ck)`]
                  C2BP3AUX_eval_init_globals) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[bvl_initial_state_def; bvl_state_INFO.ri_accessors; domain_lookup] THEN
      UNDISCH_TAC `clos_to_bvlProof_init_code code1 code2 max_app` THEN
      REWRITE_TAC[clos_to_bvlProof_init_code_def] THEN MESON_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[bvl_evaluate_def] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[bvl_find_code_def; bvl_initial_state_def; bvl_state_INFO.ri_accfupds;
                bvl_state_INFO.ri_accessors; K_THM] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] (ASSUME
      `lookup (start + num_stubs max_app) (code2:(num#bvl_exp)spt) = SOME (0,c2)`)] THEN
    CAKE_REWRITE_TAC[LENGTH] THEN
    ASM_REWRITE_TAC[ARITH_RULE `k + ck < 0 + 1 <=> k = 0 /\ ck = 0`] THEN
    FIRST_X_ASSUM(fun th -> if is_eq (concl th) && CLOS2AUX_CONST_IN "bvl_evaluate" (lhand (concl th))
       then MP_TAC th else NO_TAC) THEN
    MATCH_MP_TAC(MESON[] `(a:(bvl_v list,bvl_v)result#(C,FFI)bvl_state) = b ==> (a = c ==> b = c)`) THEN AP_TERM_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN EXPAND_TAC "T1" THEN
    REWRITE_TAC[bvl_dec_clock_def; bvl_initial_state_def; clos_dec_clock_def;
                clos_initial_state_def; bvl_state_INFO.ri_component_equality;
                bvl_state_INFO.ri_accfupds; bvl_state_INFO.ri_accessors;
                clos_state_INFO.ri_accfupds; clos_state_INFO.ri_accessors; K_THM] THEN
    UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CLOSP2AUX_letop_result_shape THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[clos_to_bvlProof_state_rel_def] o check (fun th ->
      CLOS2AUX_CONST_IN "clos_to_bvlProof_state_rel" (concl th))) THEN SIMP_TAC[]]);;

(* HOL4 line 7763 (HOL4 $< is (<); fvs_inc is clos_fvs_compile_inc at clos_prog->clos_prog) *)
let clos_to_bvlProof_syntax_oracle_ok_def = cake_def
  `clos_to_bvlProof_syntax_oracle_ok (c:clos_to_bvl_config) (c':clos_to_bvl_config) es
     (co:num->(num#(val_approx)spt#num_set#B)#clos_prog) <=>
     (!n. SND (SND (co n)) = []) /\
     (clos_to_bvl_config_do_mti c
      ==> 1 <= clos_to_bvl_config_max_app c /\ ALL no_mti es /\
          (!n. ALL no_mti (FST (SND (co n))))) /\
     (?v. FST (co 0) =
          (clos_to_bvl_config_next_loc c',
           option_val_approx_spt (clos_to_bvl_config_known_conf c'),
           FST (clos_to_bvl_config_call_state c'),v)) /\
     (clos_to_bvl_config_do_call c
      ==> every_Fn_vs_NONE es /\
          is_state_oracle clos_call_compile_inc
            (known_co (clos_to_bvl_config_known_conf c)
               (state_co (ignore_table clos_number_compile_inc)
                  (pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
                              (clos_to_bvl_config_max_app c)) o co)))) /\
     (IS_SOME (clos_to_bvl_config_known_conf c)
      ==> 1 <= clos_to_bvl_config_max_app c /\ every_Fn_vs_NONE es /\
          oracle_monotonic (SET_OF_BAG o clos_elist_globals o FST o SND) (<)
            (SET_OF_BAG (clos_elist_globals es)) co /\
          is_state_oracle (clos_known_compile_inc (THE (clos_to_bvl_config_known_conf c)))
            (pure_co (clos_fvs_compile_inc:clos_prog->clos_prog) o
               state_co (ignore_table clos_number_compile_inc)
                 (pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
                             (clos_to_bvl_config_max_app c)) o co)) /\
          (!n'. BAG_ALL_DISTINCT (clos_elist_globals (FST (SND (co n')))) /\
                ALL clos_esgc_free (FST (SND (co n'))))) /\
     ~contains_App_SOME (clos_to_bvl_config_max_app c) es /\
     clos_knownProof_syntax_ok es /\
     (!n. ~contains_App_SOME (clos_to_bvl_config_max_app c) (FST (SND (co n))) /\
          every_Fn_vs_NONE (FST (SND (co n)))) /\
     is_state_oracle (ignore_table clos_number_compile_inc)
       (pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
                   (clos_to_bvl_config_max_app c)) o co)`;;


(* HOL4 line 7792 *)
let compile_exps_IMP_acc = prove
 (`!max_app xs aux c aux1.
     clos_to_bvl_compile_exps max_app xs aux = (c,aux1)
     ==> LENGTH c = LENGTH xs /\ ?ys. aux1 = APPEND ys aux`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`max_app:num`; `xs:clos_exp list`; `aux:(num#num#bvl_exp)list`]
               compile_exps_acc) THEN
  ASM_REWRITE_TAC[pair_CASE]);;

(* HOL4 line 7800 *)
let build_aux_append_aux = prove
 (`!xs n aux aux_extra.
     build_aux n xs (APPEND aux aux_extra) =
     (\(ys,aux2). (ys,APPEND aux2 aux_extra)) (build_aux n xs aux)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[build_aux_def] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM(CONJUNCT2 APPEND)] THEN ASM_REWRITE_TAC[]);;

let C2BP3AUX_build_aux_append = prove
 (`!xs n aux aux_extra n2 aux2.
     build_aux n xs aux = (n2,aux2)
     ==> build_aux n xs (APPEND aux aux_extra) = (n2,APPEND aux2 aux_extra)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[build_aux_append_aux] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let C2BP3AUX_compile_exps_append_aux = prove
 (`!max_app xs aux aux_extra c aux1.
     clos_to_bvl_compile_exps max_app xs aux = (c,aux1)
     ==> clos_to_bvl_compile_exps max_app xs (APPEND aux aux_extra) =
         (c,APPEND aux1 aux_extra)`,
  MATCH_MP_TAC clos_to_bvl_compile_exps_ind THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    rhs (concl th) = `(c:bvl_exp list,aux1:(num#num#bvl_exp)list)`)) THEN
  (fun g -> if CLOS2AUX_CONST_IN "clos_Letrec" (snd g) then ALL_TAC g else
   (REWRITE_TAC[clos_to_bvl_compile_exps_def] THEN REPEAT (PAIRARG_TAC THEN GVS[]) THEN
    TRY(REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[APPEND])) g) THEN
  CASES_ON `fns:(num#clos_exp)list` THEN REWRITE_TAC[clos_to_bvl_compile_exps_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CAKE_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) && is_eq (lhand (concl th)) &&
      rand (lhand (concl th)) = `[]:(num#clos_exp)list`)) THEN REWRITE_TAC[] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  CASES_ON `a0:num#clos_exp` THEN CASES_ON `a1:(num#clos_exp)list` THEN CAKE_REWRITE_TAC[] THEN
  DISCH_TAC THEN REPEAT (PAIRARG_TAC THEN GVS[]) THENL
   [FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(fun eq -> MP_TAC(MATCH_MP ih eq))) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN SIMP_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `aux_extra:(num#num#bvl_exp)list`) THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    SIMP_TAC[];
    FIRST_ASSUM(fun th -> if is_eq (concl th) && CLOS2AUX_CONST_IN "build_aux" (lhs (concl th)) &&
                            not (CLOS2AUX_CONST_IN "APPEND" (lhs (concl th)))
       then MP_TAC (MATCH_MP C2BP3AUX_build_aux_append th) THEN
            FIRST_X_ASSUM(fun ih -> if is_forall (concl ih) &&
                                       CLOS2AUX_CONST_IN "build_aux" (concl ih)
               then MP_TAC (MATCH_MP ih th) else NO_TAC)
       else NO_TAC) THEN
    DISCH_THEN(fun ih -> FIRST_ASSUM(fun eq ->
      MP_TAC (SPEC `aux_extra:(num#num#bvl_exp)list` (MATCH_MP ih eq)))) THEN
    REPEAT DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    ASM_MESON_TAC[PAIR_EQ]]);;

(* HOL4 line 7808 (aux_extra is free in HOL4) *)
let compile_exps_append_aux = prove
 (`!max_app xs aux aux_extra.
     clos_to_bvl_compile_exps max_app xs (APPEND aux aux_extra) =
     (\(ys,aux2). (ys,APPEND aux2 aux_extra)) (clos_to_bvl_compile_exps max_app xs aux)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `clos_to_bvl_compile_exps max_app xs aux` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:bvl_exp list` (X_CHOOSE_THEN `a:(num#num#bvl_exp)list`
    ASSUME_TAC)) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP C2BP3AUX_compile_exps_append_aux th]) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

(* HOL4 line 7827 (HOL4 I compile_exps ... is I applied to compile_exps) *)
let compile_exps_eq_append = prove
 (`!max_app xs aux.
     clos_to_bvl_compile_exps max_app xs aux =
     (\(ys,aux2). (ys,APPEND aux2 aux)) (I clos_to_bvl_compile_exps max_app xs [])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[I_THM; GSYM compile_exps_append_aux; APPEND]);;

(* HOL4 line 7836: val compile_exps_code_locs2 = compile_exps_code_locs |>  *)
(* SPEC_ALL |> Q.GEN aux |> Q.SPEC [] |> SIMP_RULE list_ss [] |> GEN_ALL    *)
let compile_exps_code_locs2 = prove
 (`!max_app xs ys aux2.
     clos_to_bvl_compile_exps max_app xs [] = (ys,aux2)
     ==> MAP FST aux2 = MAP ((+) (num_stubs max_app)) (REVERSE (code_locs xs))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC compile_exps_code_locs THEN
  MAP_EVERY EXISTS_TAC [`[]:(num#num#bvl_exp)list`; `ys:bvl_exp list`] THEN
  ASM_REWRITE_TAC[APPEND_NIL]);;

(* the shape of the result of extract_name *)
let C2BP3AUX_extract_name_cases = prove
 (`!exps n real_es.
     extract_name exps = (n,real_es)
     ==> (n = 0 /\ real_es = exps) \/
         (?t xs'. exps = CONS (clos_Op t (IntOp (clos_Const (&n))) []) xs' /\
                  real_es = (if xs' = [] then exps else xs'))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[extract_name_def; PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `?n t. h = clos_Op t (IntOp (clos_Const (&n))) []` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `t0:tra` SUBST_ALL_TAC)) THEN
    SUBGOAL_THEN `(some n. ?t. clos_Op t0 (IntOp (clos_Const (&m))) [] =
                                clos_Op t (IntOp (clos_Const (&n))) []) = SOME m`
      SUBST1_TAC THENL
     [REWRITE_TAC[some_DEF; injectivity "clos_exp"; injectivity "clos_op";
                  injectivity "int_op"; INT_OF_NUM_EQ] THEN
      REWRITE_TAC[UNWIND_THM1] THEN REWRITE_TAC[MESON[] `!m:num. (?x. m = x) <=> T`] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN MESON_TAC[];
      ALL_TAC] THEN
    CAKE_REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`t0:tra`; `t:clos_exp list`] THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(some n. ?t. h = clos_Op t (IntOp (clos_Const (&n))) []) = NONE`
      SUBST1_TAC THENL
     [REWRITE_TAC[some_DEF] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    CAKE_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]]);;

(* HOL4 line 7839 *)
let extract_name_code_locs = prove
 (`!exps n real_es. extract_name exps = (n,real_es) ==> code_locs real_es = code_locs exps`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP C2BP3AUX_extract_name_cases) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[code_locs_cons] THEN REWRITE_TAC[code_locs_def; APPEND]);;

(* HOL4 line 7849 *)
let extracted_addrs_def = cake_def
  `extracted_addrs (exps:clos_exp list) =
     if exps = [] then [0]
     else (match extract_name exps with
             (n,real_es) -> MAP ((+) n) (COUNT_LIST (MAX 1 (LENGTH real_es))))`;;

(* HOL4 line 7855 (HOL4 a ++ b ++ c ++ ... is left-associative; the arities *)
(* of the code are of any type, as in HOL4) *)
let req_compile_inc_addrs_def = cake_def
  `req_compile_inc_addrs (extra:(num->num)list) (exps,(code:(num#A#clos_exp)list)) =
     APPEND (APPEND (APPEND (APPEND (extracted_addrs exps) (code_locs exps))
                       (MAP FST code)) (code_locs (MAP (SND o SND) code)))
       (FLAT (MAP (\f. MAP f (code_locs exps)) extra))`;;

(* HOL4 line 7861 *)
let can_extract_def = cake_def
  `can_extract exps <=>
     ?t n exps'. exps = CONS (clos_Op t (IntOp (clos_Const (&n))) []) exps'`;;

(* HOL4 line 7866 *)
let extract_name_MAP_FST_addrs = prove
 (`!exps n real_es.
     extract_name exps = (n,real_es) ==> MAP FST (chain_exps n real_es) = extracted_addrs exps`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[extracted_addrs_def; MAP_FST_chain_exps_any] THEN
  COND_CASES_TAC THENL
   [UNDISCH_TAC `extract_name exps = (n,real_es)` THEN
    ASM_REWRITE_TAC[extract_name_def; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[LENGTH; num_CONV `1`; COUNT_LIST_def; MAP; ADD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[num_CONV `1`; COUNT_LIST_def; MAP; ADD_CLAUSES];
    ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[]]);;

let C2BP3AUX_MAP_FST_MAP2 = prove
 (CASE_TERM `!(ls:(num#num#clos_exp)list) (es:bvl_exp list) m.
     LENGTH es = LENGTH ls
     ==> MAP FST (MAP2 (\p exp. match p with (loc,args,y) -> (loc + m,args,exp)) ls es) =
         MAP ((+) m) (MAP FST ls)`,
  REWRITE_TAC[] THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; MAP2; MAP; NOT_SUC; SUC_INJ] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  SPEC_TAC(`h:num#num#clos_exp`,`h:num#num#clos_exp`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CAKE_REWRITE_TAC[FST] THEN REWRITE_TAC[ADD_SYM]);;

let C2BP3AUX_MAP_FST_compile_prog = prove
 (`!max_app ls.
     MAP FST (clos_to_bvl_compile_prog max_app ls) =
     MAP ((+) (num_stubs max_app))
       (APPEND (MAP FST ls) (REVERSE (code_locs (MAP (SND o SND) ls))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_to_bvl_compile_prog_def] THEN
  MP_TAC(ISPEC `clos_to_bvl_compile_exps max_app (MAP (SND o SND) (ls:(num#num#clos_exp)list)) []`
         PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `es:bvl_exp list` (X_CHOOSE_THEN `aux:(num#num#bvl_exp)list`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP clos_to_bvl_compile_exps_LENGTH) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP compile_exps_code_locs2) THEN
  ASM_REWRITE_TAC[MAP_APPEND] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC C2BP3AUX_MAP_FST_MAP2 THEN ASM_REWRITE_TAC[LENGTH_MAP]);;

(* HOL4 line 7876 *)
let compile_inc_req_addrs = prove
 (`!prog max_app.
     (ALL_DISTINCT (req_compile_inc_addrs [] prog)
      ==> ALL_DISTINCT (MAP FST (clos_to_bvl_compile_inc' max_app prog))) /\
     set_of_list (MAP FST (clos_to_bvl_compile_inc' max_app prog)) SUBSET
     set_of_list (MAP ((+) (num_stubs max_app)) (req_compile_inc_addrs [] prog))`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`exps:clos_exp list`; `code:(num#num#clos_exp)list`; `max_app:num`] THEN
  REWRITE_TAC[compile_inc_uncurry; FST; SND; C2BP3AUX_MAP_FST_compile_prog;
              req_compile_inc_addrs_def; MAP; FLAT; APPEND_NIL] THEN
  MP_TAC(ISPEC `extract_name exps` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `real_es:clos_exp list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST; SND; MAP_APPEND; code_locs_append; chain_exps_code_locs] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP extract_name_code_locs th;
                                    MATCH_MP extract_name_MAP_FST_addrs th]) THEN
  REWRITE_TAC[GSYM MAP_APPEND] THEN CONJ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC[ALL_DISTINCT_APPEND; ALL_DISTINCT_REVERSE; MEM_APPEND; MEM_REVERSE] THEN
    MESON_TAC[];
    REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_MAP; MEM_APPEND; MEM_REVERSE] THEN
    MESON_TAC[]]);;

(* HOL4 line 7911 (HOL4 $< is (<)) *)
let compile_inc_monotonic = prove
 (`!max_app St (co:num->C#clos_prog).
     oracle_monotonic
       (set_of_list o MAP ((+) (num_stubs max_app)) o req_compile_inc_addrs [] o SND) (<)
       St co
     ==> oracle_monotonic (set_of_list o MAP FST o SND) (<) St
           (pure_co (clos_to_bvl_compile_inc' max_app) o co)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC oracle_monotonic_subset THEN
  REWRITE_TAC[SUBSET_REFL; o_THM; pure_co_def; PAIR_MAP; SND; compile_inc_req_addrs]);;

(* HOL4 line 7921: Theorem code_locs_Op_cons = GEN_ALL (Q.SPEC (Op a b c)   *)
(* code_locs_cons) |> REWRITE_RULE [code_locs_def] (its resulting statement) *)
let code_locs_Op_cons = prove
 (`!a b c xs. code_locs (CONS (clos_Op a b c) xs) = APPEND (code_locs c) (code_locs xs)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[code_locs_cons] THEN REWRITE_TAC[code_locs_def]);;

(* HOL4 line 7924 *)
let EXISTS_CONS_NOT_NULL = prove
 (`!(ys:A list). (?x xs. ys = CONS x xs) <=> ~NULL ys`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NULL; NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]);;

(* HOL4 line 7930 *)
let can_extract_to_case = prove
 (`!exps.
     can_extract exps
     ==> (?t n. exps = [clos_Op t (IntOp (clos_Const (&n))) []]) \/
         (?t n exp exps'.
            exps = CONS (clos_Op t (IntOp (clos_Const (&n))) []) (CONS exp exps'))`,
  REWRITE_TAC[can_extract_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[CONS_11] THEN
  STRUCT_CASES_TAC(ISPEC `exps':clos_exp list` list_CASES) THEN
  REWRITE_TAC[CONS_11; NOT_CONS_NIL] THEN MESON_TAC[]);;

(* HOL4 line 7937 [local] *)
let show_SUBSET = prove
 (`!(s:A->bool) t. (!x. x IN s ==> x IN t) ==> s SUBSET t`,
  REWRITE_TAC[SUBSET]);;

(* HOL4 line 7943 *)
let trivia_1 = prove
 (`!x xs (v:A).
     COUNT_LIST 1 = [0] /\ MAX 1 (SUC x) = SUC x /\
     LENGTH (if xs = [] then [v] else xs) = MAX 1 (LENGTH xs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[num_CONV `1`; COUNT_LIST_def; MAP] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THENL [ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `~(xs:A list = [])` THEN REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ARITH_TAC);;

(* HOL4 line 7952 *)
let subset_req_orac_to_oracle = prove
 (`!(orac1:num->A#clos_prog) (orac2:num->B#clos_prog) xs1 xs2 (f:num->C) R St.
     (!n. set_of_list (req_compile_inc_addrs xs2 (SND (orac2 n))) SUBSET
          set_of_list (req_compile_inc_addrs xs1 (SND (orac1 n)))) /\
     oracle_monotonic (set_of_list o MAP f o req_compile_inc_addrs xs1 o SND) R St orac1
     ==> oracle_monotonic (set_of_list o MAP f o req_compile_inc_addrs xs2 o SND) R St orac2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC oracle_monotonic_subset) THEN
  REWRITE_TAC[SUBSET_REFL; o_THM; SET_OF_LIST_MAP] THEN
  ASM_MESON_TAC[IMAGE_SUBSET]);;

(* HOL4 line 7965: fun mk_to_oracle (an ML function; its results           *)
(* annotate_compile_inc_req_oracle, cond_call_compile_inc_req_oracle and    *)
(* known_co_req_oracle are stated below)                                     *)

let C2BP3AUX_distinct_append_mono = prove
 (`!(a:A list) a' b b'.
     (set_of_list a' SUBSET set_of_list a /\ (ALL_DISTINCT a ==> ALL_DISTINCT a')) /\
     (set_of_list b' SUBSET set_of_list b /\ (ALL_DISTINCT b ==> ALL_DISTINCT b'))
     ==> set_of_list (APPEND a' b') SUBSET set_of_list (APPEND a b) /\
         (ALL_DISTINCT (APPEND a b) ==> ALL_DISTINCT (APPEND a' b'))`,
  REWRITE_TAC[SET_OF_LIST_APPEND; ALL_DISTINCT_APPEND; SUBSET; IN_UNION; IN_SET_OF_LIST;
              MEM_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 7974 *)
let annotate_compile_code_locs = prove
 (`!xs.
     set_of_list (code_locs (MAP (SND o SND) (clos_annotate_compile xs))) SUBSET
     set_of_list (code_locs (MAP (SND o SND) xs)) /\
     (ALL_DISTINCT (code_locs (MAP (SND o SND) xs))
      ==> ALL_DISTINCT (code_locs (MAP (SND o SND) (clos_annotate_compile xs))))`,
  REWRITE_TAC[clos_annotate_compile_def] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; code_locs_def; SUBSET_REFL; ALL_DISTINCT] THEN
  SPEC_TAC(`h:num#num#clos_exp`,`h:num#num#clos_exp`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [`n:num`; `args:num`; `e:clos_exp`] THEN
  CAKE_REWRITE_TAC[o_THM; SND] THEN ONCE_REWRITE_TAC[code_locs_cons] THEN
  REWRITE_TAC[HD_annotate_SING] THEN
  MATCH_MP_TAC C2BP3AUX_distinct_append_mono THEN
  ASM_REWRITE_TAC[annotate_code_locs]);;

(* HOL4 line 7987 *)
let LENGTH_annotate = prove
 (`!i xs. LENGTH (clos_annotate_annotate i xs) = LENGTH xs`,
  REWRITE_TAC[clos_annotate_annotate_def; shift_LENGTH_LEMMA; LENGTH_FST_alt_free]);;

(* HOL4 line 7994 *)
let annotate_Op_Const = prove
 (`!m t n ls.
     clos_annotate_annotate m (CONS (clos_Op t (IntOp (clos_Const n)) []) ls) =
     CONS (clos_Op t (IntOp (clos_Const n)) []) (clos_annotate_annotate m ls)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_annotate_annotate_def] THEN
  ONCE_REWRITE_TAC[alt_free_CONS] THEN ONCE_REWRITE_TAC[shift_CONS] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[alt_free_def] THEN CAKE_REWRITE_TAC[HD] THEN
  REWRITE_TAC[clos_annotate_shift_def] THEN CAKE_REWRITE_TAC[HD] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[HD]);;

let C2BP3AUX_some_Const = prove
 (`!t0 m. (some n. ?t. clos_Op t0 (IntOp (clos_Const (&m))) [] =
                         clos_Op t (IntOp (clos_Const (&n))) []) = SOME m`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[some_DEF; injectivity "clos_exp"; injectivity "clos_op";
              injectivity "int_op"; INT_OF_NUM_EQ] THEN
  REWRITE_TAC[UNWIND_THM1] THEN REWRITE_TAC[MESON[] `!m:num. (?x. m = x) <=> T`] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN MESON_TAC[]);;

let C2BP3AUX_extract_name_Op = prove
 (`!t n rest.
     extract_name (CONS (clos_Op t (IntOp (clos_Const (&n))) []) rest) =
     (n,if rest = [] then [clos_Op t (IntOp (clos_Const (&n))) []] else rest)`,
  REWRITE_TAC[extract_name_def; C2BP3AUX_some_Const] THEN CAKE_REWRITE_TAC[]);;

let C2BP3AUX_extracted_addrs_Op = prove
 (`!t n rest.
     extracted_addrs (CONS (clos_Op t (IntOp (clos_Const (&n))) []) rest) =
     MAP ((+) n) (COUNT_LIST (MAX 1 (LENGTH rest)))`,
  REWRITE_TAC[extracted_addrs_def; NOT_CONS_NIL; C2BP3AUX_extract_name_Op] THEN
  CAKE_REWRITE_TAC[trivia_1] THEN REWRITE_TAC[ARITH_RULE `MAX 1 (MAX 1 l) = MAX 1 l`]);;

(* HOL4 line 8005 *)
let annotate_compile_inc_req = prove
 (`!prog.
     can_extract (FST prog)
     ==> (ALL_DISTINCT (req_compile_inc_addrs [] prog)
          ==> ALL_DISTINCT (req_compile_inc_addrs [] (clos_annotate_compile_inc prog))) /\
         can_extract (FST (clos_annotate_compile_inc prog)) /\
         set_of_list (req_compile_inc_addrs [] (clos_annotate_compile_inc prog)) SUBSET
         set_of_list (req_compile_inc_addrs [] prog)`,
  REWRITE_TAC[FORALL_PAIR_THM; clos_annotate_compile_inc_def; FST; can_extract_def] THEN
  MAP_EVERY X_GEN_TAC [`exps:clos_exp list`; `code:(num#num#clos_exp)list`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[annotate_Op_Const] THEN
  CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [MESON_TAC[]; ALL_TAC]] THEN
  REWRITE_TAC[req_compile_inc_addrs_def; MAP; FLAT; APPEND_NIL; C2BP3AUX_extracted_addrs_Op;
              LENGTH_annotate; clos_annotateProof_MAP_FST_compile] THEN
  ONCE_REWRITE_TAC[code_locs_cons] THEN REWRITE_TAC[code_locs_def; APPEND] THEN
  MP_TAC(SPECL [`0`; `exps':clos_exp list`] annotate_code_locs) THEN
  MP_TAC(SPEC `code:(num#num#clos_exp)list` annotate_compile_code_locs) THEN
  REWRITE_TAC[SET_OF_LIST_APPEND; ALL_DISTINCT_APPEND; SUBSET; IN_UNION; IN_SET_OF_LIST;
              MEM_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 8035: val annotate_compile_inc_req_intros = ... CONJUNCTS |>   *)
(* map (IRULE_CANON o DISCH_ALL) (a list for IRULE in the proofs)            *)

(* HOL4 line 8038: val annotate_compile_inc_req_oracle = mk_to_oracle       *)
(* (\orac1. pure_co clos_annotate$compile_inc o orac1) [] (the resulting    *)
(* instance of subset_req_orac_to_oracle)                                    *)
let annotate_compile_inc_req_oracle = prove
 (`!(orac1:num->S#clos_prog) xs2 (f:num->C) R St.
     (!n. set_of_list (req_compile_inc_addrs xs2
                         (SND ((pure_co clos_annotate_compile_inc o orac1) n))) SUBSET
          set_of_list (req_compile_inc_addrs [] (SND (orac1 n)))) /\
     oracle_monotonic (set_of_list o MAP f o req_compile_inc_addrs [] o SND) R St orac1
     ==> oracle_monotonic (set_of_list o MAP f o req_compile_inc_addrs xs2 o SND) R St
           (pure_co clos_annotate_compile_inc o orac1)`,
  REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC (ISPECL
    [`orac1:num->S#clos_prog`; `pure_co clos_annotate_compile_inc o (orac1:num->S#clos_prog)`;
     `[]:(num->num)list`; `xs2:(num->num)list`; `f:num->C`; `R:C->C->bool`; `St:C->bool`]
    subset_req_orac_to_oracle));;

(* HOL4 line 8041 *)
let annotate_compile_every_Fn_vs_SOME = prove
 (`!es. every_Fn_vs_SOME (MAP (SND o SND) (clos_annotate_compile es))`,
  REWRITE_TAC[clos_annotate_compile_def] THEN ONCE_REWRITE_TAC[every_Fn_vs_SOME_EVERY] THEN
  REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  CAKE_REWRITE_TAC[o_THM; SND] THEN
  REWRITE_TAC[HD_annotate_SING; every_Fn_vs_SOME_annotate]);;

let C2BP3AUX_calls_Op_Const = prove
 (`!t n rest g.
     clos_call_calls (CONS (clos_Op t (IntOp (clos_Const (&n))) []) rest) g =
     (CONS (clos_Op t (IntOp (clos_Const (&n))) []) (FST (clos_call_calls rest g)),
      SND (clos_call_calls rest g))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!g. clos_call_calls [clos_Op t (IntOp (clos_Const (&n))) []] g =
                    ([clos_Op t (IntOp (clos_Const (&n))) []],g)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[clos_call_calls_def] THEN CAKE_REWRITE_TAC[]; ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `rest:clos_exp list` list_CASES) THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[clos_call_calls_def] THEN CAKE_REWRITE_TAC[FST; SND];
    REWRITE_TAC[clos_call_calls_def] THEN ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[C2BP3AUX_pair_CASE_FST_SND; APPEND]]);;

let C2BP3AUX_distinct_calls = prove
 (`!(E:num list) C C' F' D'.
     ALL_DISTINCT E /\ ALL_DISTINCT C' /\ ALL_DISTINCT D' /\ ALL_DISTINCT F' /\
     (!e. MEM e C' ==> ~MEM e D') /\
     (!x. MEM x C' \/ MEM x D' ==> MEM x C) /\
     (!x. MEM x F' ==> ?y. x = SUC y /\ MEM y C) /\
     (!e. MEM e E ==> ~MEM e C) /\
     (!e. MEM e E ==> ~(?x. MEM x C /\ e = SUC x)) /\
     (!e. MEM e C ==> ~(?x. MEM x C /\ e = SUC x))
     ==> ALL_DISTINCT (APPEND (APPEND (APPEND E C') F') D')`,
  REWRITE_TAC[ALL_DISTINCT_APPEND; MEM_APPEND] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[]);;
let C2BP3AUX_subset_calls = prove
 (`!(E:num list) C C' F' D' X Y.
     (!x. MEM x C' \/ MEM x D' ==> MEM x C) /\
     (!x. MEM x F' ==> ?y. x = SUC y /\ MEM y C)
     ==> set_of_list (APPEND (APPEND (APPEND E C') F') D') SUBSET
         set_of_list (APPEND (APPEND (APPEND (APPEND E C) X) Y) (MAP SUC C))`,
  REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_APPEND; MEM_MAP] THEN MESON_TAC[]);;

(* HOL4 line 8049 *)
let cond_call_compile_inc_req = prove
 (`!prog dc cfg.
     can_extract (FST prog)
     ==> (ALL_DISTINCT (req_compile_inc_addrs [SUC] prog)
          ==> ALL_DISTINCT (req_compile_inc_addrs []
                              (SND (cond_call_compile_inc dc cfg prog)))) /\
         can_extract (FST (SND (cond_call_compile_inc dc cfg prog))) /\
         set_of_list (req_compile_inc_addrs [] (SND (cond_call_compile_inc dc cfg prog))) SUBSET
         set_of_list (req_compile_inc_addrs [SUC] prog)`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; can_extract_def] THEN
  MAP_EVERY X_GEN_TAC [`exps:clos_exp list`; `code:(num#num#clos_exp)list`; `dc:bool`;
                       `cfg:num_set`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CASES_ON `dc:bool` THEN
  REWRITE_TAC[cond_call_compile_inc_def; CURRY_DEF; I_THM; SND; FST] THENL
   [ALL_TAC;
    REWRITE_TAC[req_compile_inc_addrs_def; MAP; FLAT; APPEND_NIL] THEN
    CONJ_TAC THENL [SIMP_TAC[ALL_DISTINCT_APPEND]; ALL_TAC] THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SET_OF_LIST_APPEND] THEN SET_TAC[]] THEN
  REWRITE_TAC[ccompile_inc_uncurry; FST; SND; C2BP3AUX_calls_Op_Const] THEN
  MP_TAC(ISPEC `clos_call_calls exps' (cfg,[])` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `ys:clos_exp list` (X_CHOOSE_THEN `gg:num_set#(num#num#clos_exp)list`
    ASSUME_TAC)) THEN
  MP_TAC(ISPEC `gg:num_set#(num#num#clos_exp)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num_set` (X_CHOOSE_THEN `aux:(num#num#clos_exp)list`
    SUBST_ALL_TAC)) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP calls_length) THEN
  REWRITE_TAC[req_compile_inc_addrs_def; MAP; FLAT; APPEND_NIL; C2BP3AUX_extracted_addrs_Op] THEN
  ONCE_REWRITE_TAC[code_locs_cons] THEN REWRITE_TAC[code_locs_def; APPEND] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(!x. MEM x (code_locs ys) \/ MEM x (code_locs (MAP (SND o SND) aux))
                     ==> MEM x (code_locs exps')) /\
                (!x. MEM x (MAP FST (aux:(num#num#clos_exp)list))
                     ==> ?y. x = SUC y /\ MEM y (code_locs exps'))` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP calls_code_locs_MEM) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP calls_add_SUC_code_locs) THEN
    REWRITE_TAC[SND; MAP; code_locs_def; MEM; set_of_list; UNION_EMPTY; EMPTY_UNION;
                SUBSET; IN_SET_OF_LIST; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC C2BP3AUX_distinct_calls THEN
    EXISTS_TAC `code_locs (exps':clos_exp list)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[ALL_DISTINCT_APPEND; MEM_APPEND; MEM_MAP] o
      check (fun th -> CLOS2AUX_CONST_IN "ALL_DISTINCT" (concl th) &&
                       CLOS2AUX_CONST_IN "SUC" (concl th))) THEN
    STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP calls_code_locs_ALL_DISTINCT) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] calls_ALL_DISTINCT)) THEN
    ASM_REWRITE_TAC[SND; MAP; code_locs_def; APPEND_NIL; ALL_DISTINCT; set_of_list;
                    DISJOINT_EMPTY; ALL_DISTINCT_APPEND; MEM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[MEM_MAP] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MEM_MAP]) THEN ASM_MESON_TAC[];
    MESON_TAC[];
    MATCH_MP_TAC C2BP3AUX_subset_calls THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 8092: val cond_call_compile_inc_req_intros (a list for IRULE)  *)

(* HOL4 line 8095: val cond_call_compile_inc_req_oracle = mk_to_oracle      *)
(* (\orac1. state_co (cond_call_compile_inc dc) orac1) [SUC] (the resulting *)
(* instance of subset_req_orac_to_oracle)                                    *)
let cond_call_compile_inc_req_oracle = prove
 (`!dc (orac1:num->(num_set#S)#clos_prog) xs2 (f:num->C) R St.
     (!n. set_of_list (req_compile_inc_addrs xs2
                         (SND (state_co (cond_call_compile_inc dc) orac1 n))) SUBSET
          set_of_list (req_compile_inc_addrs [SUC] (SND (orac1 n)))) /\
     oracle_monotonic (set_of_list o MAP f o req_compile_inc_addrs [SUC] o SND) R St orac1
     ==> oracle_monotonic (set_of_list o MAP f o req_compile_inc_addrs xs2 o SND) R St
           (state_co (cond_call_compile_inc dc) orac1)`,
  REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC (ISPECL
    [`orac1:num->(num_set#S)#clos_prog`;
     `state_co (cond_call_compile_inc dc) (orac1:num->(num_set#S)#clos_prog)`;
     `[SUC]`; `xs2:(num->num)list`; `f:num->C`; `R:C->C->bool`; `St:C->bool`]
    subset_req_orac_to_oracle));;

let C2BP3AUX_known_Op_Const_sing = prove
 (`!a tv i c d. clos_known_known a [clos_Op tv (IntOp (clos_Const i)) []] c d =
                ([clos_Op tv (IntOp (clos_Const i)) [],clos_known_Int i],d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clos_known_known_def] THEN CAKE_REWRITE_TAC[MAP; REVERSE] THEN
  REWRITE_TAC[known_op_def; isGlobal_def] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; clos_op_SmartOp_def; MAP] THEN
  REWRITE_TAC[SmartOp'_def] THEN CAKE_REWRITE_TAC[]);;

(* HOL4 line 8098 *)
let known_Op_Const = prove
 (`!a tv n b c d.
     clos_known_known a (CONS (clos_Op tv (IntOp (clos_Const (&n))) []) b) c d =
     ((CONS (clos_Op tv (IntOp (clos_Const (&n))) [],clos_known_Int (&n))) ## I)
       (clos_known_known a b c d)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `b:clos_exp list` list_CASES) THENL
   [REWRITE_TAC[C2BP3AUX_known_Op_Const_sing; clos_known_known_def; PAIR_MAP; FST; SND; I_THM];
    GEN_REWRITE_TAC LAND_CONV [clos_known_known_def] THEN REWRITE_TAC[C2BP3AUX_known_Op_Const_sing] THEN
    CAKE_REWRITE_TAC[] THEN
    REWRITE_TAC[C2BP3AUX_pair_CASE_FST_SND; PAIR_MAP; I_THM; APPEND]]);;

(* HOL4 line 8106 (HOL4 bag <= is SUB_BAG) *)
let BAG_IMAGE_SUB_BAG = prove
 (`!(x:A->num) y (f:A->B).
     SUB_BAG x y /\ FINITE_BAG x /\ FINITE_BAG y ==> SUB_BAG (BAG_IMAGE f x) (BAG_IMAGE f y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUB_BAG_LEQ; BAG_IMAGE_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN X_GEN_TAC `e:B` THEN
  ASM_SIMP_TAC[FINITE_BAG_FILTER] THEN MATCH_MP_TAC SUB_BAG_CARD THEN
  ASM_SIMP_TAC[FINITE_BAG_FILTER] THEN
  UNDISCH_TAC `SUB_BAG (x:A->num) y` THEN
  REWRITE_TAC[SUB_BAG_LEQ; BAG_FILTER_DEF] THEN DISCH_TAC THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LE_REFL]);;

(* HOL4 line 8118 *)
let BAG_UNION_MONO = prove
 (`!(a:A->num) b c d.
     SUB_BAG a b /\ SUB_BAG c d ==> SUB_BAG (BAG_UNION a c) (BAG_UNION b d)`,
  REWRITE_TAC[SUB_BAG_LEQ; BAG_UNION] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 8127 *)
let remove_ticks_Op_Const = prove
 (`!t n ls.
     clos_ticks_remove_ticks (CONS (clos_Op t (IntOp (clos_Const (&n))) []) ls) =
     CONS (clos_Op t (IntOp (clos_Const (&n))) []) (clos_ticks_remove_ticks ls)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `ls:clos_exp list` list_CASES) THEN
  REWRITE_TAC[clos_ticks_remove_ticks_def] THEN CAKE_REWRITE_TAC[HD]);;

(* HOL4 line 8134 *)
let let_op_Op_Const = prove
 (`!t n ls.
     clos_letop_let_op (CONS (clos_Op t (IntOp (clos_Const (&n))) []) ls) =
     CONS (clos_Op t (IntOp (clos_Const (&n))) []) (clos_letop_let_op ls)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `ls:clos_exp list` list_CASES) THEN
  REWRITE_TAC[clos_letop_let_op_def] THEN CAKE_REWRITE_TAC[HD]);;

let C2BP3AUX_remove_fvs_Op_Const = prove
 (`!fvs t n ls.
     remove_fvs fvs (CONS (clos_Op t (IntOp (clos_Const n)) []) ls) =
     CONS (clos_Op t (IntOp (clos_Const n)) []) (remove_fvs fvs ls)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `ls:clos_exp list` list_CASES) THEN
  REWRITE_TAC[remove_fvs_def; HD]);;

let C2BP3AUX_distinct_known = prove
 (`!(E:num list) C C' X Y.
     ALL_DISTINCT (APPEND (APPEND (APPEND (APPEND E C) X) Y) (MAP SUC C)) /\
     ALL_DISTINCT C' /\ (!x. MEM x C' ==> MEM x C)
     ==> ALL_DISTINCT (APPEND (APPEND E C') (MAP SUC C')) /\
         set_of_list (APPEND (APPEND E C') (MAP SUC C')) SUBSET
         set_of_list (APPEND (APPEND (APPEND (APPEND E C) X) Y) (MAP SUC C))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ALL_DISTINCT_APPEND; MEM_APPEND; SUBSET; IN_SET_OF_LIST] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [ASM_MESON_TAC[];
    MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN ASM_REWRITE_TAC[SUC_INJ] THEN MESON_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[MEM_MAP]) THEN REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[];
    REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[]]);;

(* HOL4 line 8140 *)
let known_co_req = prove
 (`!(orac:num->((val_approx)spt#B)#clos_prog) n kc.
     can_extract (FST (SND (orac n)))
     ==> (ALL_DISTINCT (req_compile_inc_addrs [SUC] (SND (orac n)))
          ==> ALL_DISTINCT (req_compile_inc_addrs [SUC] (SND (known_co kc orac n)))) /\
         can_extract (FST (SND (known_co kc orac n))) /\
         set_of_list (req_compile_inc_addrs [SUC] (SND (known_co kc orac n))) SUBSET
         set_of_list (req_compile_inc_addrs [SUC] (SND (orac n)))`,
  REPEAT GEN_TAC THEN CASES_ON `kc:(clos_known_config)option` THEN
  REWRITE_TAC[C2BP3AUX_known_co_NONE; C2BP3AUX_known_co_SOME; SND; FST; SUBSET_REFL] THEN
  MP_TAC(ISPEC `SND ((orac:num->((val_approx)spt#B)#clos_prog) n)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `exps:clos_exp list` (X_CHOOSE_THEN `code:(num#num#clos_exp)list`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[FST; SND; can_extract_def] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[clos_fvs_compile_def; C2BP3AUX_remove_fvs_Op_Const; known_Op_Const; PAIR_MAP;
                  FST; MAP; remove_ticks_Op_Const; let_op_Op_Const; CONS_11] THEN
  ABBREV_TAC `ks = MAP FST (FST (clos_known_known (reset_inline_factor a) (remove_fvs 0 exps') []
                                   (FST (FST ((orac:num->((val_approx)spt#B)#clos_prog) n)))))` THEN
  SUBGOAL_THEN `LENGTH (clos_letop_let_op (clos_ticks_remove_ticks ks)) =
                  LENGTH (exps':clos_exp list) /\
                code_locs (clos_letop_let_op (clos_ticks_remove_ticks ks)) = code_locs ks /\
                SUB_BAG (LIST_TO_BAG (code_locs ks)) (LIST_TO_BAG (code_locs exps'))`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ks" THEN
    REWRITE_TAC[clos_letop_LENGTH_let_op; clos_ticks_LENGTH_remove_ticks; LENGTH_MAP;
                known_LENGTH; clos_fvsProof_LENGTH_remove_fvs; code_locs_let_op;
                code_locs_remove_ticks] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM (SPEC `0` code_locs_remove_fvs)] THEN
    MATCH_MP_TAC known_code_locs_bag THEN MESON_TAC[PAIR];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[req_compile_inc_addrs_def; C2BP3AUX_extracted_addrs_Op; code_locs_Op_cons;
                  code_locs_def; MAP; FLAT; APPEND; APPEND_NIL] THEN
  CONJ_TAC THENL [ALL_TAC; CONJ_TAC THENL [MESON_TAC[]; ALL_TAC]] THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `ALL_DISTINCT (code_locs (ks:clos_exp list))` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM LIST_TO_BAG_DISTINCT] THEN MATCH_MP_TAC BAG_ALL_DISTINCT_SUB_BAG THEN
      EXISTS_TAC `LIST_TO_BAG (code_locs (exps':clos_exp list))` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LIST_TO_BAG_DISTINCT] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> CLOS2AUX_CONST_IN "ALL_DISTINCT" (concl th))) THEN
      SIMP_TAC[ALL_DISTINCT_APPEND];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`MAP ((+) n') (COUNT_LIST (MAX 1 (LENGTH (exps':clos_exp list))))`;
                   `code_locs (exps':clos_exp list)`; `code_locs (ks:clos_exp list)`;
                   `MAP FST (code:(num#num#clos_exp)list)`;
                   `code_locs (MAP (SND o SND) (code:(num#num#clos_exp)list))`]
                  C2BP3AUX_distinct_known) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP LIST_TO_BAG_SUBSET o check (fun th ->
        CLOS2AUX_CONST_IN "SUB_BAG" (concl th))) THEN
      REWRITE_TAC[SUBSET; IN_SET_OF_LIST];
      SIMP_TAC[]];
    MP_TAC(MATCH_MP LIST_TO_BAG_SUBSET (ASSUME
      `SUB_BAG (LIST_TO_BAG (code_locs (ks:clos_exp list)))
               (LIST_TO_BAG (code_locs (exps':clos_exp list)))`)) THEN
    REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_APPEND; MEM_MAP] THEN MESON_TAC[]]);;

(* HOL4 line 8229: val known_co_req_intros (a list for IRULE)               *)

(* HOL4 line 8232: val known_co_req_oracle = mk_to_oracle                   *)
(* (\orac. clos_knownProof$known_co kc orac) [SUC] (the resulting instance  *)
(* of subset_req_orac_to_oracle)                                             *)
let known_co_req_oracle = prove
 (`!kc (orac:num->((val_approx)spt#S)#clos_prog) xs2 (f:num->C) R St.
     (!n. set_of_list (req_compile_inc_addrs xs2 (SND (known_co kc orac n))) SUBSET
          set_of_list (req_compile_inc_addrs [SUC] (SND (orac n)))) /\
     oracle_monotonic (set_of_list o MAP f o req_compile_inc_addrs [SUC] o SND) R St orac
     ==> oracle_monotonic (set_of_list o MAP f o req_compile_inc_addrs xs2 o SND) R St
           (known_co kc orac)`,
  REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC (ISPECL
    [`orac:num->((val_approx)spt#S)#clos_prog`;
     `known_co kc (orac:num->((val_approx)spt#S)#clos_prog)`;
     `[SUC]`; `xs2:(num->num)list`; `f:num->C`; `R:C->C->bool`; `St:C->bool`]
    subset_req_orac_to_oracle));;

let C2BP3AUX_ignore_number = prove
 (`!n (exps:clos_exp list) (aux:A).
     SND (ignore_table clos_number_compile_inc n (exps,aux)) =
     (CONS (clos_Op backend_common_None (IntOp (clos_Const (&n))) [])
        (SND (renumber_code_locs_list (make_even (n + MAX (LENGTH exps) 1)) exps)),aux)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[PAIR_FST_SND_EQ] THEN
  REWRITE_TAC[FST_SND_ignore_table; SND_SND_ignore_table; FST; SND; CLOSP1AUX_num_SND_compile_inc]);;

let C2BP3AUX_distinct_number = prove
 (`!n L loc (C:num list).
     ALL_DISTINCT C /\ (!x. MEM x C ==> loc <= x /\ EVEN x) /\ n + MAX 1 L <= loc
     ==> ALL_DISTINCT (APPEND (APPEND (MAP ((+) n) (COUNT_LIST (MAX 1 L))) C) (MAP SUC C))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ALL_DISTINCT_APPEND; MEM_APPEND; MEM_MAP; MEM_COUNT_LIST] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN REWRITE_TAC[all_distinct_count_list] THEN ARITH_TAC;
    REPEAT STRIP_TAC THEN RES_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN ASM_REWRITE_TAC[SUC_INJ] THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN RES_TAC THEN TRY ASM_ARITH_TAC THEN ASM_MESON_TAC[EVEN]]);;

let C2BP3AUX_renumber_facts = prove
 (`!loc exps. EVEN loc ==>
     ALL_DISTINCT (code_locs (SND (renumber_code_locs_list loc exps))) /\
     (!x. MEM x (code_locs (SND (renumber_code_locs_list loc exps))) ==>
          loc <= x /\ x < FST (renumber_code_locs_list loc exps) /\ EVEN x) /\
     EVEN (FST (renumber_code_locs_list loc exps)) /\
     loc <= FST (renumber_code_locs_list loc exps) /\
     LENGTH (SND (renumber_code_locs_list loc exps)) = LENGTH exps`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`loc:num`; `exps:clos_exp list`] renumber_code_locs_list_distinct) THEN
  MP_TAC(SPECL [`loc:num`; `exps:clos_exp list`] (CONJUNCT1 renumber_code_locs_EVEN)) THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM; renumber_code_locs_inc; GT; renumber_code_locs_length] THEN
  MESON_TAC[]);;

(* HOL4 line 8235 *)
let number_compile_inc_req = prove
 (`!n (prog:clos_exp list#(num#A#clos_exp)list).
     let nprog = SND (ignore_table clos_number_compile_inc n prog) in
     SND prog = []
     ==> ALL_DISTINCT (req_compile_inc_addrs [SUC] nprog) /\ SND nprog = [] /\
         can_extract (FST nprog)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  MAP_EVERY X_GEN_TAC [`exps:clos_exp list`; `aux:(num#A#clos_exp)list`] THEN
  REWRITE_TAC[SND] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[C2BP3AUX_ignore_number; FST; SND; can_extract_def] THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  REWRITE_TAC[req_compile_inc_addrs_def; C2BP3AUX_extracted_addrs_Op; code_locs_Op_cons;
              code_locs_def; MAP; FLAT; APPEND; APPEND_NIL] THEN
  MP_TAC(SPECL [`make_even (n + MAX (LENGTH (exps:clos_exp list)) 1)`; `exps:clos_exp list`]
               C2BP3AUX_renumber_facts) THEN
  REWRITE_TAC[EVEN_make_even] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C2BP3AUX_distinct_number THEN
  EXISTS_TAC `make_even (n + MAX (LENGTH (exps:clos_exp list)) 1)` THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[make_even_def] THEN COND_CASES_TAC THEN ARITH_TAC);;

(* HOL4 line 8270: val number_compile_inc_req_intros (a list for IRULE)     *)

(* HOL4 line 8274 *)
let MEM_number_req = prove
 (`!x n (prog:clos_exp list#(num#A#clos_exp)list).
     MEM x (req_compile_inc_addrs [SUC] (SND (ignore_table clos_number_compile_inc n prog))) /\
     SND prog = []
     ==> n <= x /\ x < FST (clos_number_compile_inc n (FST prog))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`exps:clos_exp list`; `aux:(num#A#clos_exp)list`] THEN
  REWRITE_TAC[SND; FST] THEN STRIP_TAC THEN UNDISCH_TAC `aux = []:(num#A#clos_exp)list` THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `MEM x (req_compile_inc_addrs [SUC] (SND (ignore_table clos_number_compile_inc n
                  (exps,[]:(num#A#clos_exp)list))))` THEN
  REWRITE_TAC[C2BP3AUX_ignore_number; C2BP3AUX_ncompile_inc_FST] THEN
  REWRITE_TAC[req_compile_inc_addrs_def; C2BP3AUX_extracted_addrs_Op; code_locs_Op_cons;
              code_locs_def; MAP; FLAT; APPEND; APPEND_NIL; MEM_APPEND; MEM_MAP;
              MEM_COUNT_LIST] THEN
  MP_TAC(SPECL [`make_even (n + MAX (LENGTH (exps:clos_exp list)) 1)`; `exps:clos_exp list`]
               C2BP3AUX_renumber_facts) THEN
  REWRITE_TAC[EVEN_make_even] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `n + MAX 1 (LENGTH (exps:clos_exp list)) <=
                make_even (n + MAX (LENGTH exps) 1)` ASSUME_TAC THENL
   [REWRITE_TAC[make_even_def] THEN COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [ASM_ARITH_TAC;
    RES_TAC THEN ASM_ARITH_TAC;
    RES_TAC THEN
    SUBGOAL_THEN `~(SUC x' = FST (renumber_code_locs_list (make_even (n + MAX (LENGTH (exps:clos_exp list)) 1)) exps))`
      ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `EVEN (FST (renumber_code_locs_list
         (make_even (n + MAX (LENGTH (exps:clos_exp list)) 1)) exps))` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[EVEN];
      ASM_ARITH_TAC]]);;

(* HOL4 line 8306 (HOL4 $< is (<)) *)
let renumber_code_locs_monotonic_req = prove
 (`!(co:num->(num#C)#clos_prog) St offs.
     is_state_oracle (ignore_table clos_number_compile_inc) co /\
     (!x. x IN St ==> FST (FST (co 0)) + offs > x) /\
     (!n. SND (SND (co n)) = [])
     ==> oracle_monotonic (set_of_list o MAP ((+) offs) o req_compile_inc_addrs [SUC] o SND)
           (<) St (state_co (ignore_table clos_number_compile_inc) co)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[oracle_monotonic_def; o_THM; GEN_ALL SND_state_co; IN_SET_OF_LIST; MEM_MAP] THEN
  SUBGOAL_THEN `!i z. MEM z (req_compile_inc_addrs [SUC]
                       (SND (ignore_table clos_number_compile_inc
                          (FST (FST ((co:num->(num#C)#clos_prog) i))) (SND (co i)))))
                  ==> FST (FST (co i)) <= z /\ z < FST (FST (co (i + 1)))` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`z:num`; `FST (FST ((co:num->(num#C)#clos_prog) i))`; `SND ((co:num->(num#C)#clos_prog) i)`]
                  MEM_number_req) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP number_oracle_FST_inc th]);
    ALL_TAC] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN RES_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`j:num`; `i + 1`] o MATCH_MP number_oracle_FST_mono) THEN
    ASM_REWRITE_TAC[ARITH_RULE `i + 1 <= j <=> i < j`] THEN ASM_ARITH_TAC;
    FIRST_ASSUM(MP_TAC o SPECL [`i:num`; `0`] o MATCH_MP number_oracle_FST_mono) THEN
    REWRITE_TAC[LE_0] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (fun th -> CLOS2AUX_CONST_IN ">" (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* HOL4 line 8332 (HOL4 BIGUNION is UNIONS) *)
let domain_nth_code = prove
 (`!n (orac:num->C#(num#num#bvl_exp)list).
     domain (clos_to_bvlProof_nth_code orac n) =
     UNIONS (set_of_list (MAP (set_of_list o MAP FST o SND o orac) (COUNT_LIST n)))`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[clos_to_bvlProof_nth_code_def; COUNT_LIST_def; MAP; set_of_list;
                  domain_def; UNIONS_0; domain_union; domain_fromAList; UNIONS_INSERT] THEN
  GEN_TAC THEN REWRITE_TAC[MAP_MAP_o; o_THM] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; shift_seq_def; ADD1]);;

(* HOL4 line 8342 *)
let DISJOINT_nth_code_monotonic = prove
 (`!init (orac:num->C#(num#num#bvl_exp)list) v n.
     oracle_monotonic (set_of_list o MAP FST o SND) (<) (domain init) orac /\
     v = SND (orac n)
     ==> DISJOINT (domain (sptree_union init (clos_to_bvlProof_nth_code orac n)))
           (set_of_list (MAP FST v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[IN_DISJOINT; domain_union; domain_nth_code; IN_UNION; IN_UNIONS;
              IN_SET_OF_LIST; o_THM; MEM_COUNT_LIST] THEN
  ONCE_REWRITE_TAC[MEM_MAP] THEN REWRITE_TAC[o_THM; MEM_COUNT_LIST] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP oracle_monotonic_init) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP oracle_monotonic_step) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_THM; IN_SET_OF_LIST]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `x:num` THEN
  REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`] THEN STRIP_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:num`; `x:num`] o check (fun th ->
      length (fst (strip_forall (concl th))) = 3)) THEN ASM_REWRITE_TAC[LT_REFL] THEN
    REWRITE_TAC[MEM_MAP] THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_SET_OF_LIST]) THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`x':num`; `n:num`; `x:num`; `x:num`] o
      check (fun th -> length (fst (strip_forall (concl th))) = 4)) THEN
    ASM_REWRITE_TAC[LT_REFL] THEN REWRITE_TAC[MEM_MAP] THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 8364 (HOL4 UNCURRY_EQ; renamed: hol4/basic.ml binds UNCURRY_EQ) *)
let clos_to_bvlProof_UNCURRY_EQ = prove
 (`!(f:A->B->C). UNCURRY f = (\x. f (FST x) (SND x))`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; UNCURRY_DEF; FST; SND]);;

(* HOL4 line 8370 *)
let LENGTH_FST_cond_mti_compile_inc = prove
 (`!do_it ma (prog:clos_exp list#A list).
     LENGTH (FST (cond_mti_compile_inc do_it ma prog)) = LENGTH (FST prog)`,
  GEN_TAC THEN CASES_ON `do_it:bool` THEN
  REWRITE_TAC[cond_mti_compile_inc_def; I_THM; FORALL_PAIR_THM; clos_mti_compile_inc_def;
              FST; intro_multi_length]);;

(* HOL4 line 8378 *)
let every_Fn_vs_NONE_cond_mti_compile_inc = prove
 (`!do_it ma (prog:clos_exp list#A list).
     every_Fn_vs_NONE (FST (cond_mti_compile_inc do_it ma prog)) <=>
     every_Fn_vs_NONE (FST prog)`,
  GEN_TAC THEN CASES_ON `do_it:bool` THEN
  REWRITE_TAC[cond_mti_compile_inc_def; I_THM; FORALL_PAIR_THM; clos_mti_compile_inc_def;
              FST; every_Fn_vs_NONE_intro_multi]);;

(* HOL4 line 8387 *)
let clos_to_bvlProof_MAP_FST_compile_prog = prove
 (`!max_app ls.
     MAP FST (clos_to_bvl_compile_prog max_app ls) =
     MAP ((+) (num_stubs max_app))
       (APPEND (MAP FST ls) (REVERSE (code_locs (MAP (SND o SND) ls))))`,
  REWRITE_TAC[C2BP3AUX_MAP_FST_compile_prog]);;

(* HOL4 line 8407 *)
let IMAGE_ADD_SUBSET_count = prove
 (`!A n m. A SUBSET pred_set_count (n - m) ==> IMAGE ((+) m) A SUBSET pred_set_count n`,
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_COUNT] THEN REPEAT STRIP_TAC THEN RES_TAC THEN
  ASM_ARITH_TAC);;

(* HOL4 line 8415 *)
let compile_common_MAP_FST_compile_prog = prove
 (`!c es c' p.
     compile_common c es = (c',p)
     ==> set_of_list (MAP FST (clos_to_bvl_compile_prog (clos_to_bvl_config_max_app c) p)) SUBSET
         pred_set_count (clos_to_bvl_config_next_loc c' + num_stubs (clos_to_bvl_config_max_app c))`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP C2BP3AUX_compile_common_parts) THEN
  ASM_REWRITE_TAC[clos_to_bvl_config_INFO.ri_accfupds; K_THM; C2BP3AUX_MAP_FST_compile_prog] THEN
  REWRITE_TAC[SET_OF_LIST_MAP] THEN
  MATCH_MP_TAC IMAGE_ADD_SUBSET_count THEN REWRITE_TAC[ADD_SUB] THEN
  REWRITE_TAC[clos_annotateProof_MAP_FST_compile; SET_OF_LIST_APPEND; UNION_SUBSET;
              LIST_TO_SET_REVERSE; MAP_APPEND; MAP_FST_chain_exps_any] THEN
  ABBREV_TAC `loc = make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH (es:clos_exp list)))` THEN
  SUBGOAL_THEN `clos_to_bvl_config_next_loc c + MAX 1 (LENGTH (es:clos_exp list)) <= loc /\ EVEN loc`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "loc" THEN REWRITE_TAC[EVEN_make_even; make_even_def] THEN COND_CASES_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`loc:num`; `clos_mti_compile (clos_to_bvl_config_do_mti c)
                   (clos_to_bvl_config_max_app c) es`] C2BP3AUX_renumber_facts) THEN
  ASM_REWRITE_TAC[FST; SND; clos_mtiProof_compile_length] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP clos_call_compile_LENGTH) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP clos_knownProof_compile_LENGTH) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LIST_TO_BAG_SUBSET o MATCH_MP compile_code_locs_bag) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ccompile_aux_subset) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ccompile_locs_subset) THEN
  SUBGOAL_THEN `!y. y < n /\ EVEN y /\ EVEN n ==> SUC y < n` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC `SUC y = n` THENL [ASM_MESON_TAC[EVEN]; ASM_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_SET_OF_LIST; IN_COUNT; MEM_APPEND; code_locs_append; IN_IMAGE;
              MEM_MAP; MEM_COUNT_LIST] THEN
  REPEAT DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
    ASM_MESON_TAC[];
    X_GEN_TAC `x:num` THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[SUBSET; IN_SET_OF_LIST]
      (CONJUNCT1 (SPEC_ALL annotate_compile_code_locs)))) THEN
    REWRITE_TAC[MAP_APPEND; code_locs_append; MEM_APPEND; chain_exps_code_locs] THEN
    ASM_MESON_TAC[]]);;

(* HOL4 line 8476: fun abbrev_adj_tac (an ML tactic) *)

let C2BP3AUX_oinv_number = prove
 (`!(co1:num->(num#S)#clos_prog) k.
     SND (SND (co1 k)) = []
     ==> ALL_DISTINCT (req_compile_inc_addrs [SUC]
                         (SND (state_co (ignore_table clos_number_compile_inc) co1 k))) /\
         SND (SND (state_co (ignore_table clos_number_compile_inc) co1 k)) = [] /\
         can_extract (FST (SND (state_co (ignore_table clos_number_compile_inc) co1 k)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SND_state_co] THEN
  MP_TAC(ISPECL [`FST (FST ((co1:num->(num#S)#clos_prog) k))`;
                 `SND ((co1:num->(num#S)#clos_prog) k)`] number_compile_inc_req) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[]);;

let C2BP3AUX_oinv_known = prove
 (`!kc (co2:num->((val_approx)spt#S)#clos_prog).
     (!k. ALL_DISTINCT (req_compile_inc_addrs [SUC] (SND (co2 k))) /\
          can_extract (FST (SND (co2 k))))
     ==> !k. ALL_DISTINCT (req_compile_inc_addrs [SUC] (SND (known_co kc co2 k))) /\
             can_extract (FST (SND (known_co kc co2 k))) /\
             set_of_list (req_compile_inc_addrs [SUC] (SND (known_co kc co2 k))) SUBSET
             set_of_list (req_compile_inc_addrs [SUC] (SND (co2 k)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  MP_TAC(ISPECL [`co2:num->((val_approx)spt#S)#clos_prog`; `k:num`;
                 `kc:clos_known_config option`] known_co_req) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[]);;

let C2BP3AUX_oinv_call = prove
 (`!dc (co3:num->(num_set#S)#clos_prog).
     (!k. ALL_DISTINCT (req_compile_inc_addrs [SUC] (SND (co3 k))) /\
          can_extract (FST (SND (co3 k))))
     ==> !k. ALL_DISTINCT (req_compile_inc_addrs []
                             (SND (state_co (cond_call_compile_inc dc) co3 k))) /\
             can_extract (FST (SND (state_co (cond_call_compile_inc dc) co3 k))) /\
             set_of_list (req_compile_inc_addrs []
                            (SND (state_co (cond_call_compile_inc dc) co3 k))) SUBSET
             set_of_list (req_compile_inc_addrs [SUC] (SND (co3 k)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[SND_state_co] THEN
  MP_TAC(ISPECL [`SND ((co3:num->(num_set#S)#clos_prog) k)`; `dc:bool`;
                 `FST (FST ((co3:num->(num_set#S)#clos_prog) k))`]
         cond_call_compile_inc_req) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[]);;

let C2BP3AUX_oinv_annotate = prove
 (`!(co4:num->S#clos_prog).
     (!k. ALL_DISTINCT (req_compile_inc_addrs [] (SND (co4 k))) /\
          can_extract (FST (SND (co4 k))))
     ==> !k. ALL_DISTINCT (req_compile_inc_addrs []
                             (SND ((pure_co clos_annotate_compile_inc o co4) k))) /\
             set_of_list (req_compile_inc_addrs []
                            (SND ((pure_co clos_annotate_compile_inc o co4) k))) SUBSET
             set_of_list (req_compile_inc_addrs [] (SND (co4 k)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[o_THM; SND_pure_co] THEN
  MP_TAC(ISPEC `SND ((co4:num->S#clos_prog) k)` annotate_compile_inc_req) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let C2BP3AUX_ALL_every_Fn_SOME = prove
 (`!ps:(num#num#clos_exp)list.
     ALL (\p. every_Fn_SOME [SND (SND p)]) ps <=> every_Fn_SOME (MAP (SND o SND) ps)`,
  GEN_TAC THEN GEN_REWRITE_TAC (RAND_CONV) [every_Fn_SOME_EVERY] THEN
  REWRITE_TAC[ALL_MAP; o_DEF]);;

let C2BP3AUX_ALL_every_Fn_vs_SOME = prove
 (`!ps:(num#num#clos_exp)list.
     ALL (\p. every_Fn_vs_SOME [SND (SND p)]) ps <=> every_Fn_vs_SOME (MAP (SND o SND) ps)`,
  GEN_TAC THEN GEN_REWRITE_TAC (RAND_CONV) [every_Fn_vs_SOME_EVERY] THEN
  REWRITE_TAC[ALL_MAP; o_DEF]);;

(* HOL4 line 8485 (c'' and prog' are free in HOL4: c'' is not tied to c') *)
let syntax_oracle_ok_to_oracle_inv = prove
 (`!(cc:B->(num#num#bvl_exp)list->(byte list#int64 list#B)option) es
     (co:num->(num#(val_approx)spt#num_set#B)#clos_prog) c c' prog' c''.
     clos_to_bvlProof_syntax_oracle_ok c c' es co /\
     compile_common c es = (c',prog')
     ==> let co' = pure_co clos_annotate_compile_inc o
                   state_co (cond_call_compile_inc (clos_to_bvl_config_do_call c))
                     (known_co (clos_to_bvl_config_known_conf c)
                        (state_co (ignore_table clos_number_compile_inc)
                           (pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
                                       (clos_to_bvl_config_max_app c)) o co))) in
         compile_oracle_inv (clos_to_bvl_config_max_app c) (alist_to_fmap prog')
           (pure_cc (clos_to_bvl_compile_inc' (clos_to_bvl_config_max_app c)) cc) co'
           (fromAList
              (APPEND
                 (APPEND (toAList (clos_to_bvl_init_code (clos_to_bvl_config_max_app c)))
                    [(num_stubs (clos_to_bvl_config_max_app c) - 2,2,force_thunk_code);
                     (num_stubs (clos_to_bvl_config_max_app c) - 1,0,
                      init_globals (clos_to_bvl_config_max_app c)
                        (clos_to_bvl_config_start c'' + num_stubs (clos_to_bvl_config_max_app c)))])
                 (clos_to_bvl_compile_prog (clos_to_bvl_config_max_app c) prog')))
           cc (pure_co (clos_to_bvl_compile_inc' (clos_to_bvl_config_max_app c)) o co')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (MP_TAC o REWRITE_RULE[clos_to_bvlProof_syntax_oracle_ok_def]) (LABEL_TAC "cc")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s0") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s1") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:B` (LABEL_TAC "s2")) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s3") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s4") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s5") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s6") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s7") (LABEL_TAC "s8")) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[compile_oracle_inv_def] THEN
  ABBREV_TAC `co1 = pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
                     (clos_to_bvl_config_max_app c)) o
                   (co:num->(num#(val_approx)spt#num_set#B)#clos_prog)` THEN
  ABBREV_TAC `co2 = state_co (ignore_table clos_number_compile_inc)
                   (co1:num->(num#(val_approx)spt#num_set#B)#clos_prog)` THEN
  ABBREV_TAC `co3 = known_co (clos_to_bvl_config_known_conf c)
                   (co2:num->((val_approx)spt#num_set#B)#clos_prog)` THEN
  ABBREV_TAC `co4 = state_co (cond_call_compile_inc (clos_to_bvl_config_do_call c))
                   (co3:num->(num_set#B)#clos_prog)` THEN
  ABBREV_TAC `co5 = pure_co clos_annotate_compile_inc o (co4:num->B#clos_prog)` THEN
  ABBREV_TAC `tc = fromAList
              (APPEND
                 (APPEND (toAList (clos_to_bvl_init_code (clos_to_bvl_config_max_app c)))
                    [(num_stubs (clos_to_bvl_config_max_app c) - 2,2,force_thunk_code);
                     (num_stubs (clos_to_bvl_config_max_app c) - 1,0,
                      init_globals (clos_to_bvl_config_max_app c)
                        (clos_to_bvl_config_start c'' + num_stubs (clos_to_bvl_config_max_app c)))])
                 (clos_to_bvl_compile_prog (clos_to_bvl_config_max_app c) prog'))` THEN
  (* the number layer *)
  SUBGOAL_THEN `!k. SND (SND ((co1:num->(num#(val_approx)spt#num_set#B)#clos_prog) k)) = []`
    (LABEL_TAC "F1") THENL
   [X_GEN_TAC `k:num` THEN EXPAND_TAC "co1" THEN
    REWRITE_TAC[o_THM; SND_pure_co; SND_cond_mti_compile_inc] THEN
    USE_THEN "s0" (fun th -> REWRITE_TAC[th; COND_ID]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. ALL_DISTINCT (req_compile_inc_addrs [SUC]
                     (SND ((co2:num->((val_approx)spt#num_set#B)#clos_prog) k))) /\
                    SND (SND (co2 k)) = [] /\ can_extract (FST (SND (co2 k)))`
    (LABEL_TAC "F2") THENL
   [EXPAND_TAC "co2" THEN GEN_TAC THEN MATCH_MP_TAC C2BP3AUX_oinv_number THEN
    USE_THEN "F1" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. ALL_DISTINCT (req_compile_inc_addrs [SUC]
                     (SND ((co3:num->(num_set#B)#clos_prog) k))) /\
                    can_extract (FST (SND (co3 k))) /\
                    set_of_list (req_compile_inc_addrs [SUC] (SND (co3 k))) SUBSET
                    set_of_list (req_compile_inc_addrs [SUC]
                      (SND ((co2:num->((val_approx)spt#num_set#B)#clos_prog) k)))`
    (LABEL_TAC "F3") THENL
   [EXPAND_TAC "co3" THEN MATCH_MP_TAC C2BP3AUX_oinv_known THEN
    USE_THEN "F2" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. ALL_DISTINCT (req_compile_inc_addrs []
                     (SND ((co4:num->B#clos_prog) k))) /\
                    can_extract (FST (SND (co4 k))) /\
                    set_of_list (req_compile_inc_addrs [] (SND (co4 k))) SUBSET
                    set_of_list (req_compile_inc_addrs [SUC]
                      (SND ((co3:num->(num_set#B)#clos_prog) k)))`
    (LABEL_TAC "F4") THENL
   [EXPAND_TAC "co4" THEN MATCH_MP_TAC C2BP3AUX_oinv_call THEN
    USE_THEN "F3" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. ALL_DISTINCT (req_compile_inc_addrs []
                     (SND ((co5:num->B#clos_prog) k))) /\
                    set_of_list (req_compile_inc_addrs [] (SND (co5 k))) SUBSET
                    set_of_list (req_compile_inc_addrs [] (SND ((co4:num->B#clos_prog) k)))`
    (LABEL_TAC "F5") THENL
   [EXPAND_TAC "co5" THEN MATCH_MP_TAC C2BP3AUX_oinv_annotate THEN
    USE_THEN "F4" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  (* monotonicity, from the number layer up *)
  SUBGOAL_THEN `oracle_monotonic
                  (set_of_list o MAP ((+) (num_stubs (clos_to_bvl_config_max_app c))) o
                   req_compile_inc_addrs [SUC] o SND) (<) (domain (tc:(num#bvl_exp)spt))
                  (co2:num->((val_approx)spt#num_set#B)#clos_prog)`
    (LABEL_TAC "M2") THENL
   [EXPAND_TAC "co2" THEN MATCH_MP_TAC renumber_code_locs_monotonic_req THEN
    USE_THEN "s8" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "F1" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `FST (FST ((co1:num->(num#(val_approx)spt#num_set#B)#clos_prog) 0)) =
                  clos_to_bvl_config_next_loc c'` SUBST1_TAC THENL
     [EXPAND_TAC "co1" THEN REWRITE_TAC[o_THM; FST_pure_co] THEN
      USE_THEN "s2" (fun th -> REWRITE_TAC[th; FST]);
      ALL_TAC] THEN
    SUBGOAL_THEN `2 <= num_stubs (clos_to_bvl_config_max_app c)` ASSUME_TAC THENL
     [REWRITE_TAC[num_stubs_def] THEN ARITH_TAC; ALL_TAC] THEN
    USE_THEN "cc" (MP_TAC o MATCH_MP compile_common_MAP_FST_compile_prog) THEN
    MP_TAC(ISPEC `clos_to_bvl_config_max_app c` domain_init_code_lt_num_stubs) THEN
    EXPAND_TAC "tc" THEN
    REWRITE_TAC[domain_fromAList; MAP_APPEND; SET_OF_LIST_APPEND; IN_UNION; IN_SET_OF_LIST;
                toAList_domain; MAP; MEM; FST; SUBSET; IN_COUNT; GT] THEN
    REPEAT STRIP_TAC THEN RES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `oracle_monotonic
                  (set_of_list o MAP ((+) (num_stubs (clos_to_bvl_config_max_app c))) o
                   req_compile_inc_addrs [SUC] o SND) (<) (domain (tc:(num#bvl_exp)spt))
                  (co3:num->(num_set#B)#clos_prog)`
    (LABEL_TAC "M3") THENL
   [EXPAND_TAC "co3" THEN MATCH_MP_TAC known_co_req_oracle THEN
    USE_THEN "M2" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `oracle_monotonic
                  (set_of_list o MAP ((+) (num_stubs (clos_to_bvl_config_max_app c))) o
                   req_compile_inc_addrs [] o SND) (<) (domain (tc:(num#bvl_exp)spt))
                  (co4:num->B#clos_prog)`
    (LABEL_TAC "M4") THENL
   [EXPAND_TAC "co4" THEN MATCH_MP_TAC cond_call_compile_inc_req_oracle THEN
    USE_THEN "M3" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `oracle_monotonic
                  (set_of_list o MAP ((+) (num_stubs (clos_to_bvl_config_max_app c))) o
                   req_compile_inc_addrs [] o SND) (<) (domain (tc:(num#bvl_exp)spt))
                  (co5:num->B#clos_prog)`
    (LABEL_TAC "M5") THENL
   [EXPAND_TAC "co5" THEN MATCH_MP_TAC annotate_compile_inc_req_oracle THEN
    USE_THEN "M4" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* distinct names *)
    REPEAT GEN_TAC THEN REWRITE_TAC[o_THM] THEN
    DISCH_THEN(MP_TAC o AP_TERM `SND:B#(num#num#bvl_exp)list->(num#num#bvl_exp)list`) THEN
    REWRITE_TAC[SND_pure_co; SND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(CONJUNCT1(SPEC_ALL compile_inc_req_addrs)) THEN
    USE_THEN "F5" (fun th -> REWRITE_TAC[th]);
    (* disjointness *)
    GEN_TAC THEN MATCH_MP_TAC DISJOINT_nth_code_monotonic THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC compile_inc_monotonic THEN USE_THEN "M5" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  (* the every_Fn conditions, from the number layer up *)
  SUBGOAL_THEN `!k. every_Fn_SOME (FST (SND ((co2:num->((val_approx)spt#num_set#B)#clos_prog) k))) /\
                    every_Fn_vs_NONE (FST (SND (co2 k)))`
    (LABEL_TAC "E2") THENL
   [GEN_TAC THEN EXPAND_TAC "co2" THEN
    REWRITE_TAC[SND_state_co; FST_SND_ignore_table; every_Fn_SOME_ncompile_inc;
                every_Fn_vs_NONE_ncompile_inc] THEN
    EXPAND_TAC "co1" THEN
    REWRITE_TAC[o_THM; SND_pure_co; every_Fn_vs_NONE_cond_mti_compile_inc] THEN
    USE_THEN "s7" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. every_Fn_SOME (FST (SND ((co3:num->(num_set#B)#clos_prog) k))) /\
                    every_Fn_SOME (MAP (SND o SND) (SND (SND (co3 k))))`
    (LABEL_TAC "E3") THENL
   [USE_THEN "cc" (STRIP_ASSUME_TAC o MATCH_MP C2BP3AUX_compile_common_parts) THEN
    MP_TAC(ISPECL [`clos_to_bvl_config_known_conf c`;
                   `co2:num->((val_approx)spt#num_set#B)#clos_prog`;
                   `es_n:clos_exp list`; `kc:clos_known_config option`; `es_k:clos_exp list`]
           known_co_facts) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [DISCH_TAC THEN
      USE_THEN "s4" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `IS_SOME (clos_to_bvl_config_known_conf c)`))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "co2" THEN REWRITE_TAC[FST_state_co] THEN EXPAND_TAC "co1" THEN
        REWRITE_TAC[o_THM; FST_pure_co] THEN USE_THEN "s2" (fun th -> REWRITE_TAC[th; FST; SND]) THEN
        ASM_REWRITE_TAC[clos_to_bvl_config_INFO.ri_accfupds; K_THM] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP clos_knownProof_known_compile_IS_SOME) THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[IS_SOME_EXISTS] THEN
        DISCH_THEN(X_CHOOSE_THEN `kx:clos_known_config` SUBST1_TAC) THEN
        REWRITE_TAC[option_val_approx_spt_def; THE_DEF] THEN CAKE_REWRITE_TAC[];
        MP_TAC(ISPECL [`make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH (es:clos_exp list)))`;
                       `clos_mti_compile (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c) es`]
               (CONJUNCT1 renumber_code_locs_every_Fn_vs_NONE)) THEN
        ASM_REWRITE_TAC[SND; compile_every_Fn_vs_NONE];
        MP_TAC(ISPECL [`make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH (es:clos_exp list)))`;
                       `clos_mti_compile (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c) es`]
               (CONJUNCT1 renumber_code_locs_every_Fn_SOME)) THEN
        ASM_REWRITE_TAC[SND]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. every_Fn_SOME (FST (SND ((co4:num->B#clos_prog) k))) /\
                    every_Fn_SOME (MAP (SND o SND) (SND (SND (co4 k))))`
    (LABEL_TAC "E4") THENL
   [GEN_TAC THEN EXPAND_TAC "co4" THEN REWRITE_TAC[SND_state_co] THEN
    USE_THEN "E3" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    ASM_SIMP_TAC[every_Fn_SOME_cond_call_compile_inc];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN EXPAND_TAC "co5" THEN REWRITE_TAC[o_THM] THEN
  USE_THEN "E4" (MP_TAC o SPEC `n:num`) THEN
  SPEC_TAC(`(co4:num->B#clos_prog) n`,`q:B#clos_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; pure_co_def; PAIR_MAP_THM; I_THM; acompile_inc_uncurry;
              FST; SND; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  ASM_SIMP_TAC[C2BP3AUX_ALL_every_Fn_SOME; C2BP3AUX_ALL_every_Fn_vs_SOME;
               every_Fn_SOME_annotate; every_Fn_vs_SOME_annotate; every_Fn_SOME_ann;
               annotate_compile_every_Fn_vs_SOME]);;


(* HOL4 line 8576 *)
let compile_every_Fn_SOME = prove
 (`!es. every_Fn_SOME (MAP (SND o SND) es)
        ==> every_Fn_SOME (MAP (SND o SND) (clos_annotate_compile es))`,
  MATCH_ACCEPT_TAC every_Fn_SOME_ann);;

(* HOL4 line 8588 *)
let compile_common_max_app = prove
 (`!c es c' es'.
     compile_common c es = (c',es')
     ==> clos_to_bvl_config_max_app c' = clos_to_bvl_config_max_app c`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP C2BP3AUX_compile_common_parts) THEN
  ASM_REWRITE_TAC[clos_to_bvl_config_INFO.ri_accfupds]);;

let C2BP3AUX_every_Fn_vs_SOME_cons = prove
 (`!x xs. every_Fn_vs_SOME (CONS x xs) <=> every_Fn_vs_SOME [x] /\ every_Fn_vs_SOME xs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[every_Fn_vs_SOME_def]);;

(* HOL4 line 8596 (rebound at HOL4 line 9248, below) *)
let chain_exps_every_Fn_SOME = prove
 (`!x y. every_Fn_SOME (MAP (SND o SND) (chain_exps x y)) <=> every_Fn_SOME y`,
  MATCH_MP_TAC chain_exps_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[chain_exps_def; MAP; o_THM; every_Fn_SOME_def] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[CLOSPROPSAUX_every_Fn_SOME_cons] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[every_Fn_SOME_def] THEN
  MESON_TAC[CLOSPROPSAUX_every_Fn_SOME_cons]);;

(* HOL4 line 8606 *)
let chain_exps_every_Fn_vs_SOME = prove
 (`!x y. every_Fn_vs_SOME (MAP (SND o SND) (chain_exps x y)) <=> every_Fn_vs_SOME y`,
  MATCH_MP_TAC chain_exps_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[chain_exps_def; MAP; o_THM; every_Fn_vs_SOME_def] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[C2BP3AUX_every_Fn_vs_SOME_cons] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[every_Fn_vs_SOME_def] THEN
  MESON_TAC[C2BP3AUX_every_Fn_vs_SOME_cons]);;

(* HOL4 line 8616 *)
let ccompile_every_Fn_SOME = prove
 (`!es do_call es' g aux.
     every_Fn_SOME es /\ clos_call_compile do_call es = (es',g,aux)
     ==> every_Fn_SOME es' /\ every_Fn_SOME (MAP (SND o SND) aux)`,
  REPEAT GEN_TAC THEN CASES_ON `do_call:bool` THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `clos_call_calls es (LN,[]) = (es',(g,aux))` ASSUME_TAC THENL
     [UNDISCH_TAC `clos_call_compile T es = (es',g,aux)` THEN
      REWRITE_TAC[clos_call_compile_def] THEN
      REWRITE_TAC[C2BP3AUX_pair_CASE_FST_SND; PAIR] THEN REWRITE_TAC[PAIR_EQ] THEN
      MESON_TAC[PAIR];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`es:clos_exp list`; `(LN:num_set,[]:(num#num#clos_exp)list)`;
                   `es':clos_exp list`; `(g:num_set,aux:(num#num#clos_exp)list)`]
                  calls_preserves_every_Fn_SOME) THEN
    ASM_REWRITE_TAC[SND; MAP; every_Fn_SOME_def];
    REWRITE_TAC[clos_call_compile_def; PAIR_EQ] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
    ASM_REWRITE_TAC[MAP; every_Fn_SOME_def]]);;

(* HOL4 line 8630 [local] (HOL4 lambda pattern (loc,args,_) is (loc,args,x)) *)
let ALOOKUP_lemma = prove
 (`!(l1:(num#A#B)list) (l2:C list) n k v m.
     EL n l1 = (k,v) /\ ALL_DISTINCT (MAP FST l1) /\ n < LENGTH l1 /\
     LENGTH l2 = LENGTH l1
     ==> ALOOKUP (MAP2 (\(loc,args,x) exp. (loc + m,args,exp)) l1 l2) (k + m) =
         SOME (FST v,EL n l2)`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH; LT]; ALL_TAC] THEN
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `l2:C list` list_CASES) THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; MAP2; MAP; ALL_DISTINCT] THEN
  MP_TAC(ISPEC `h:num#A#B` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:num` (X_CHOOSE_THEN `q:A#B` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `q:A#B` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:A` (X_CHOOSE_THEN `p3:B` SUBST1_TAC)) THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[ALOOKUP_THM; EQ_ADD_RCANCEL; FST] THEN
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[EL; HD; TL; LT_SUC; LT_0] THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
    REWRITE_TAC[FST];
    STRIP_TAC THEN
    SUBGOAL_THEN `~(p1:num = k)` (fun th -> REWRITE_TAC[th]) THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~MEM (k:num) (MAP FST (t:(num#A#B)list))` THEN
      REWRITE_TAC[MEM_MAP] THEN EXISTS_TAC `(k:num,v:A#B)` THEN REWRITE_TAC[FST] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rand (concl th) = `(k:num,v:A#B)`)) THEN
      MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let C2BP3AUX_compile_prog_lam = prove
 (CASE_TERM `!m. (\p (exp:bvl_exp). match p with (loc,args,y) -> (loc + m,args,exp)) =
                 (\(loc,args,x:clos_exp) exp. (loc + m,(args:num),exp))`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN CAKE_REWRITE_TAC[]);;

(* HOL4 line 8652 *)
let ALOOKUP_compile_common = prove
 (`!c es c' prog name arity exp.
     compile_common c es = (c',prog) /\ ALOOKUP prog name = SOME (arity,exp)
     ==> ?aux1 exp2 aux2.
           clos_to_bvl_compile_exps (clos_to_bvl_config_max_app c) [exp] aux1 = ([exp2],aux2) /\
           ALOOKUP (clos_to_bvl_compile_prog (clos_to_bvl_config_max_app c) prog)
             (name + num_stubs (clos_to_bvl_config_max_app c)) = SOME (arity,exp2) /\
           clos_to_bvlProof_code_installed aux2
             (fromAList (clos_to_bvl_compile_prog (clos_to_bvl_config_max_app c) prog))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP compile_common_distinct_locs) THEN
  REWRITE_TAC[ALL_DISTINCT_APPEND] THEN STRIP_TAC THEN
  REWRITE_TAC[clos_to_bvl_compile_prog_def] THEN
  MP_TAC(ISPEC `clos_to_bvl_compile_exps (clos_to_bvl_config_max_app c)
                  (MAP (SND o SND) (prog:(num#num#clos_exp)list)) []` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `new_exps:bvl_exp list`
    (X_CHOOSE_THEN `aux:(num#num#bvl_exp)list` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[C2BP3AUX_compile_prog_lam] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ALOOKUP_MEM) THEN
  REWRITE_TAC[MEM_EXISTS_EL] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  MP_TAC(ISPECL [`MAP (SND o SND) (prog:(num#num#clos_exp)list)`; `[]:(num#num#bvl_exp)list`;
                 `new_exps:bvl_exp list`; `aux:(num#num#bvl_exp)list`; `n:num`;
                 `clos_to_bvl_config_max_app c`] compile_exps_EL) THEN
  ASM_SIMP_TAC[LENGTH_MAP; EL_MAP; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `auxn:(num#num#bvl_exp)list`
    (X_CHOOSE_THEN `aux2n:(num#num#bvl_exp)list` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`auxn:(num#num#bvl_exp)list`; `EL n (new_exps:bvl_exp list)`;
                        `aux2n:(num#num#bvl_exp)list`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP clos_to_bvl_compile_exps_LENGTH o
    check (fun th -> rand (lhs (concl th)) = `[]:(num#num#bvl_exp)list`)) THEN
  MP_TAC(ISPECL [`prog:(num#num#clos_exp)list`; `new_exps:bvl_exp list`; `n:num`; `name:num`;
                 `(arity:num,exp:clos_exp)`; `num_stubs (clos_to_bvl_config_max_app c)`]
         ALOOKUP_lemma) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; FST] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[ALOOKUP_APPEND; option_CASE] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP compile_exps_code_locs2 o
    check (fun th -> rand (lhs (concl th)) = `[]:(num#num#bvl_exp)list`)) THEN
  SUBGOAL_THEN `!x. MEM x (MAP FST (aux2n:(num#num#bvl_exp)list)) ==>
                    ?y. x = num_stubs (clos_to_bvl_config_max_app c) + y /\
                        MEM y (code_locs (MAP (SND o SND) (prog:(num#num#clos_exp)list)))`
    ASSUME_TAC THENL
   [UNDISCH_TAC `IS_SUBLIST (aux:(num#num#bvl_exp)list) aux2n` THEN
    REWRITE_TAC[IS_SUBLIST_APPEND] THEN STRIP_TAC THEN
    UNDISCH_TAC `MAP FST (aux:(num#num#bvl_exp)list) =
                 MAP ((+) (num_stubs (clos_to_bvl_config_max_app c)))
                   (REVERSE (code_locs (MAP (SND o SND) (prog:(num#num#clos_exp)list))))` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `MEM (x:num) (MAP FST (APPEND l (APPEND (aux2n:(num#num#bvl_exp)list) l')))`
      MP_TAC THENL [REWRITE_TAC[MAP_APPEND; MEM_APPEND] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[MEM_MAP; MEM_REVERSE] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[fromAList_append] THEN MATCH_MP_TAC code_installed_union THEN CONJ_TAC THENL
   [MATCH_MP_TAC code_installed_fromAList_strong THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN
    ASM_REWRITE_TAC[ALL_DISTINCT_REVERSE; EQ_ADD_LCANCEL] THEN MESON_TAC[];
    REWRITE_TAC[domain_fromAList; GSYM C2BP3AUX_compile_prog_lam] THEN
    MP_TAC(ISPECL [`prog:(num#num#clos_exp)list`; `new_exps:bvl_exp list`;
                   `num_stubs (clos_to_bvl_config_max_app c)`] C2BP3AUX_MAP_FST_MAP2) THEN
    ASM_REWRITE_TAC[LENGTH_MAP] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[IN_DISJOINT; IN_SET_OF_LIST; NOT_EXISTS_THM;
                ISPEC `(+) (num_stubs (clos_to_bvl_config_max_app c))` MEM_MAP] THEN
    X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (fun th ->
      can (find_term ((=) `aux2n:(num#num#bvl_exp)list`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[EQ_ADD_LCANCEL] THEN ASM_MESON_TAC[]]);;

(* HOL4 line 8720 *)
let set_code_locs_FST_calls_SUBSET = prove
 (`!x y.
     set_of_list (code_locs (FST (clos_call_calls x y))) SUBSET
     set_of_list (code_locs x) UNION set_of_list (code_locs (MAP (SND o SND) (SND y)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`x:clos_exp list`; `y:num_set#(num#num#clos_exp)list`;
                 `FST (clos_call_calls x y)`; `SND (clos_call_calls x y)`] calls_code_locs_MEM) THEN
  REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_UNION; IN_SET_OF_LIST] THEN MESON_TAC[]);;

let C2BP3AUX_renumber_list_sing = prove
 (`!n e. renumber_code_locs_list n [e] =
         (FST (renumber_code_locs n e),[SND (renumber_code_locs n e)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[renumber_code_locs_def] THEN REPEAT PAIRARG_TAC THEN
  ASM_REWRITE_TAC[FST; SND]);;

(* HOL4 line 8729 *)
let renumber_code_locs_sing = prove
 (`(!n es n' es'.
      LENGTH es = 1
      ==> (renumber_code_locs_list n es = (n',es') <=>
           LENGTH es' = 1 /\ renumber_code_locs n (HD es) = (n',HD es'))) /\
   (!n e n' e'.
      renumber_code_locs n e = (n',e') <=> renumber_code_locs_list n [e] = (n',[e']))`,
  REWRITE_TAC[C2BP3AUX_renumber_list_sing] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[ONE; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:clos_exp` (X_CHOOSE_THEN `t:clos_exp list` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[HD; C2BP3AUX_renumber_list_sing; PAIR_EQ] THEN
    STRUCT_CASES_TAC(ISPEC `es':clos_exp list` list_CASES) THEN
    REWRITE_TAC[NOT_CONS_NIL; CONS_11; HD; PAIR_FST_SND_EQ] THEN MESON_TAC[];
    REWRITE_TAC[PAIR_FST_SND_EQ; PAIR_EQ; CONS_11; FST; SND]]);;

(* HOL4 line 8746 (HOL4 a ++ b ++ c is left-associative) *)
let MAP_FST_compile_inc = prove
 (`!max_app p.
     MAP FST (clos_to_bvl_compile_inc' max_app p) =
     MAP ((+) (num_stubs max_app))
       (APPEND
          (APPEND
             (MAP ((+) (FST (extract_name (FST p))))
                (COUNT_LIST (MAX 1 (LENGTH (SND (extract_name (FST p)))))))
             (MAP FST (SND p)))
          (REVERSE (code_locs (MAP (SND o SND)
             (APPEND (chain_exps (FST (extract_name (FST p))) (SND (extract_name (FST p))))
                (SND p))))))`,
  REWRITE_TAC[compile_inc_uncurry; C2BP3AUX_MAP_FST_compile_prog; MAP_APPEND;
              MAP_FST_chain_exps_any; APPEND_ASSOC]);;

(* HOL4 line 8761 *)
let mcompile_inc_nil = prove
 (`!(p:clos_exp list#A) max_app.
     (FST p = [] ==> clos_mti_compile_inc max_app p = ([],[]:B list)) /\
     (~(FST p = []) ==> ~(FST (clos_mti_compile_inc max_app p:clos_exp list#B list) = []))`,
  REWRITE_TAC[FORALL_PAIR_THM; clos_mti_compile_inc_def; FST; PAIR_EQ] THEN
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; intro_multi_length; LENGTH]);;

(* HOL4 line 8769 *)
let renumber_code_locs_list_nil = prove
 (`!xs n.
     (xs = [] ==> SND (renumber_code_locs_list n xs) = []) /\
     (~(xs = []) ==> ~(SND (renumber_code_locs_list n xs) = []))`,
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; renumber_code_locs_length]);;

(* HOL4 line 8781 *)
let calls_nil = prove
 (`!xs p.
     (xs = [] ==> clos_call_calls xs p = ([],p)) /\
     (~(xs = []) ==> ~(FST (clos_call_calls xs p) = []))`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[clos_call_calls_def];
    REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
    MP_TAC(ISPECL [`xs:clos_exp list`; `p:num_set#(num#num#clos_exp)list`;
                   `FST (clos_call_calls xs p)`; `SND (clos_call_calls xs p)`] calls_length) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

(* HOL4 line 8793 *)
let annotate_nil = prove
 (`!xs n.
     (xs = [] ==> clos_annotate_annotate n xs = []) /\
     (~(xs = []) ==> ~(clos_annotate_annotate n xs = []))`,
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_annotate]);;

(* HOL4 line 8809 *)
let let_op_nil = prove
 (`!xs.
     (xs = [] ==> clos_letop_let_op xs = []) /\
     (~(xs = []) ==> ~(clos_letop_let_op xs = []))`,
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; clos_letop_LENGTH_let_op]);;

(* HOL4 line 8822 *)
let remove_ticks_nil = prove
 (`!xs.
     (xs = [] ==> clos_ticks_remove_ticks xs = []) /\
     (~(xs = []) ==> ~(clos_ticks_remove_ticks xs = []))`,
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; clos_ticks_LENGTH_remove_ticks]);;

(* HOL4 line 8835 *)
let known_nil = prove
 (`!b a c d.
     (b = [] ==> FST (clos_known_known a b c d) = []) /\
     (~(b = []) ==> ~(FST (clos_known_known a b c d) = []))`,
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; known_LENGTH]);;

(* HOL4 line 8844 *)
let ignore_table_uncurry = prove
 (`!(f:A->B->C#D) st (p:B#E).
     ignore_table f st p = (FST (f st (FST p)),SND (f st (FST p)),SND p)`,
  REWRITE_TAC[FORALL_PAIR_THM; ignore_table_def; FST; SND] THEN
  REWRITE_TAC[C2BP3AUX_pair_CASE_FST_SND]);;

(* HOL4 line 8850 *)
let LENGTH_FST_calls = prove
 (`!xs g0. LENGTH (FST (clos_call_calls xs g0)) = LENGTH xs`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC calls_length THEN
  EXISTS_TAC `g0:num_set#(num#num#clos_exp)list` THEN
  EXISTS_TAC `SND (clos_call_calls xs g0)` THEN REWRITE_TAC[]);;

(* HOL4 line 8857 (HOL4 $< is (<)) *)
let syntax_oracle_ok_call_FST_monotonic = prove
 (`!c c' es (co:num->(num#(val_approx)spt#num_set#B)#clos_prog) prog'.
     clos_to_bvlProof_syntax_oracle_ok c c' es co /\ compile_common c es = (c',prog')
     ==> oracle_monotonic (set_of_list o MAP FST o SND o SND) (<) (pred_set_count (FST (FST (co 0))))
           (state_co (cond_call_compile_inc (clos_to_bvl_config_do_call c))
              (known_co (clos_to_bvl_config_known_conf c)
                 (state_co (ignore_table clos_number_compile_inc)
                    (pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
                                (clos_to_bvl_config_max_app c)) o co))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (MP_TAC o REWRITE_RULE[clos_to_bvlProof_syntax_oracle_ok_def]) (LABEL_TAC "cc")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s0") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s1") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:B` (LABEL_TAC "s2")) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s3") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s4") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s5") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s6") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s7") (LABEL_TAC "s8")) THEN
  ABBREV_TAC `co1 = pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
                     (clos_to_bvl_config_max_app c)) o
                   (co:num->(num#(val_approx)spt#num_set#B)#clos_prog)` THEN
  ABBREV_TAC `co2 = state_co (ignore_table clos_number_compile_inc)
                   (co1:num->(num#(val_approx)spt#num_set#B)#clos_prog)` THEN
  ABBREV_TAC `co3 = known_co (clos_to_bvl_config_known_conf c)
                   (co2:num->((val_approx)spt#num_set#B)#clos_prog)` THEN
  ABBREV_TAC `co4 = state_co (cond_call_compile_inc (clos_to_bvl_config_do_call c))
                   (co3:num->(num_set#B)#clos_prog)` THEN
  SUBGOAL_THEN `!k. SND (SND ((co1:num->(num#(val_approx)spt#num_set#B)#clos_prog) k)) = []`
    (LABEL_TAC "F1") THENL
   [X_GEN_TAC `k:num` THEN EXPAND_TAC "co1" THEN
    REWRITE_TAC[o_THM; SND_pure_co; SND_cond_mti_compile_inc] THEN
    USE_THEN "s0" (fun th -> REWRITE_TAC[th; COND_ID]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. ALL_DISTINCT (req_compile_inc_addrs [SUC]
                     (SND ((co2:num->((val_approx)spt#num_set#B)#clos_prog) k))) /\
                    SND (SND (co2 k)) = [] /\ can_extract (FST (SND (co2 k)))`
    (LABEL_TAC "F2") THENL
   [EXPAND_TAC "co2" THEN GEN_TAC THEN MATCH_MP_TAC C2BP3AUX_oinv_number THEN
    USE_THEN "F1" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. ALL_DISTINCT (req_compile_inc_addrs [SUC]
                     (SND ((co3:num->(num_set#B)#clos_prog) k))) /\
                    can_extract (FST (SND (co3 k))) /\
                    set_of_list (req_compile_inc_addrs [SUC] (SND (co3 k))) SUBSET
                    set_of_list (req_compile_inc_addrs [SUC]
                      (SND ((co2:num->((val_approx)spt#num_set#B)#clos_prog) k)))`
    (LABEL_TAC "F3") THENL
   [EXPAND_TAC "co3" THEN MATCH_MP_TAC C2BP3AUX_oinv_known THEN
    USE_THEN "F2" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. ALL_DISTINCT (req_compile_inc_addrs []
                     (SND ((co4:num->B#clos_prog) k))) /\
                    can_extract (FST (SND (co4 k))) /\
                    set_of_list (req_compile_inc_addrs [] (SND (co4 k))) SUBSET
                    set_of_list (req_compile_inc_addrs [SUC]
                      (SND ((co3:num->(num_set#B)#clos_prog) k)))`
    (LABEL_TAC "F4") THENL
   [EXPAND_TAC "co4" THEN MATCH_MP_TAC C2BP3AUX_oinv_call THEN
    USE_THEN "F3" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `oracle_monotonic (set_of_list o MAP ((+) 0) o req_compile_inc_addrs [SUC] o SND)
                  (<) (pred_set_count (FST (FST ((co:num->(num#(val_approx)spt#num_set#B)#clos_prog) 0))))
                  (co2:num->((val_approx)spt#num_set#B)#clos_prog)`
    (LABEL_TAC "M2") THENL
   [EXPAND_TAC "co2" THEN MATCH_MP_TAC renumber_code_locs_monotonic_req THEN
    USE_THEN "s8" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "F1" (fun th -> REWRITE_TAC[th]) THEN
    EXPAND_TAC "co1" THEN REWRITE_TAC[o_THM; FST_pure_co; IN_COUNT; ADD_CLAUSES; GT];
    ALL_TAC] THEN
  SUBGOAL_THEN `oracle_monotonic (set_of_list o MAP ((+) 0) o req_compile_inc_addrs [SUC] o SND)
                  (<) (pred_set_count (FST (FST ((co:num->(num#(val_approx)spt#num_set#B)#clos_prog) 0))))
                  (co3:num->(num_set#B)#clos_prog)`
    (LABEL_TAC "M3") THENL
   [EXPAND_TAC "co3" THEN MATCH_MP_TAC known_co_req_oracle THEN
    USE_THEN "M2" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `oracle_monotonic (set_of_list o MAP ((+) 0) o req_compile_inc_addrs [] o SND)
                  (<) (pred_set_count (FST (FST ((co:num->(num#(val_approx)spt#num_set#B)#clos_prog) 0))))
                  (co4:num->B#clos_prog)`
    MP_TAC THENL
   [EXPAND_TAC "co4" THEN MATCH_MP_TAC cond_call_compile_inc_req_oracle THEN
    USE_THEN "M3" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC oracle_monotonic_subset THEN REWRITE_TAC[SUBSET_REFL; o_THM] THEN
  SUBGOAL_THEN `!l:num list. MAP ((+) 0) l = l` (fun th -> REWRITE_TAC[th]) THENL
   [LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ADD_CLAUSES]; ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN
  SPEC_TAC(`SND ((co4:num->B#clos_prog) k)`,`q:clos_prog`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; req_compile_inc_addrs_def; SND; SUBSET; IN_SET_OF_LIST;
              MEM_APPEND] THEN
  MESON_TAC[]);;


(* HOL4 line 8890 (HOL4 c' with start updated_by f) *)
let clos_to_bvlProof_syntax_oracle_ok_start = prove
 (`!c c' f es (co:num->(num#(val_approx)spt#num_set#B)#clos_prog).
     clos_to_bvlProof_syntax_oracle_ok c (clos_to_bvl_config_start_fupd f c') es co <=>
     clos_to_bvlProof_syntax_oracle_ok c c' es co`,
  REWRITE_TAC[clos_to_bvlProof_syntax_oracle_ok_def; clos_to_bvl_config_INFO.ri_accfupds]);;

let C2BP3AUX_ALOOKUP_APPEND_R = prove
 (`!(l1:(A#B)list) l2 k v.
     ALL_DISTINCT (MAP FST (APPEND l1 l2)) /\ ALOOKUP l2 k = SOME v
     ==> ALOOKUP (APPEND l1 l2) k = SOME v`,
  MESON_TAC[ALOOKUP_ALL_DISTINCT_MEM; ALOOKUP_MEM; MEM_APPEND]);;

let C2BP3AUX_code_installed_APPEND_R = prove
 (`!aux l1 l2.
     ALL_DISTINCT (MAP FST (APPEND l1 l2)) /\
     clos_to_bvlProof_code_installed aux (fromAList l2)
     ==> clos_to_bvlProof_code_installed aux (fromAList (APPEND l1 l2))`,
  REWRITE_TAC[clos_to_bvlProof_code_installed_def; GSYM ALL_MEM; FORALL_PAIR_THM;
              lookup_fromAList] THEN
  MESON_TAC[C2BP3AUX_ALOOKUP_APPEND_R]);;

let C2BP3AUX_cs_code = prove
 (`!c es c2 (p2:(num#num#clos_exp)list) l0.
     compile_common c es = (c2,p2) /\
     ALL_DISTINCT (MAP FST (APPEND l0
       (clos_to_bvl_compile_prog (clos_to_bvl_config_max_app c) p2)))
     ==> !name arity e.
           FLOOKUP (alist_to_fmap p2) name = SOME (arity,e)
           ==> ?aux1 e2 aux2.
                 clos_to_bvl_compile_exps (clos_to_bvl_config_max_app c) [e] aux1 = ([e2],aux2) /\
                 lookup (name + num_stubs (clos_to_bvl_config_max_app c))
                   (fromAList (APPEND l0
                      (clos_to_bvl_compile_prog (clos_to_bvl_config_max_app c) p2))) =
                 SOME (arity,e2) /\
                 clos_to_bvlProof_code_installed aux2
                   (fromAList (APPEND l0
                      (clos_to_bvl_compile_prog (clos_to_bvl_config_max_app c) p2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ALOOKUP_EQ_FLOOKUP] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:clos_to_bvl_config`; `es:clos_exp list`; `c2:clos_to_bvl_config`;
                 `p2:(num#num#clos_exp)list`; `name:num`; `arity:num`; `e:clos_exp`]
         ALOOKUP_compile_common) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`aux1:(num#num#bvl_exp)list`; `exp2:bvl_exp`;
                        `aux2:(num#num#bvl_exp)list`] THEN
  ASM_REWRITE_TAC[lookup_fromAList] THEN CONJ_TAC THENL
   [MATCH_MP_TAC C2BP3AUX_ALOOKUP_APPEND_R THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC C2BP3AUX_code_installed_APPEND_R THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 8897 (the first semantics is bvlSem's, the others closSem's) *)
let clos_to_bvlProof_compile_semantics = prove
 (`!(ffi:(FFI)ffi_state) c (co:num->(num#(val_approx)spt#num_set#B)#clos_prog) cc es c'
     prog names.
     ~(clos_semantics ffi (clos_to_bvl_config_max_app c) FEMPTY co
         (compile_common_inc c (pure_cc (clos_to_bvl_compile_inc' (clos_to_bvl_config_max_app c))
                                  cc)) es = Fail) /\
     clos_to_bvl_compile c es = (c',prog,names) /\
     clos_to_bvlProof_syntax_oracle_ok c c' es co
     ==> bvl_semantics ffi (fromAList prog)
           (pure_co (clos_to_bvl_compile_inc' (clos_to_bvl_config_max_app c)) o
            pure_co clos_annotate_compile_inc o
            state_co (cond_call_compile_inc (clos_to_bvl_config_do_call c))
              (known_co (clos_to_bvl_config_known_conf c)
                 (state_co (ignore_table clos_number_compile_inc)
                    (pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
                                (clos_to_bvl_config_max_app c)) o co))))
           cc (clos_to_bvl_config_start c') =
         clos_semantics ffi (clos_to_bvl_config_max_app c) FEMPTY co
           (compile_common_inc c (pure_cc (clos_to_bvl_compile_inc' (clos_to_bvl_config_max_app c))
                                    cc)) es`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nf") (CONJUNCTS_THEN2 (LABEL_TAC "cmp") (LABEL_TAC "sok"))) THEN
  USE_THEN "cmp" (ASSUME_TAC o MATCH_MP compile_all_distinct_locs) THEN
  MP_TAC(ISPEC `compile_common c es` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:clos_to_bvl_config` (X_CHOOSE_THEN `p2:(num#num#clos_exp)list`
    (LABEL_TAC "ccm"))) THEN
  USE_THEN "ccm" (LABEL_TAC "mapp" o MATCH_MP compile_common_max_app) THEN
  USE_THEN "cmp" (MP_TAC o REWRITE_RULE[clos_to_bvl_compile_def]) THEN
  USE_THEN "ccm" (fun th -> REWRITE_TAC[th]) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CAKE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN
  USE_THEN "mapp" (fun th -> REWRITE_TAC[th]) THEN
  ABBREV_TAC `ns = num_stubs (clos_to_bvl_config_max_app c)` THEN
  ABBREV_TAC `l0 = APPEND (APPEND
         (toAList (clos_to_bvl_init_code (clos_to_bvl_config_max_app c)))
         [ns - 2,2,force_thunk_code])
         [ns - 1,0,init_globals (clos_to_bvl_config_max_app c) (ns + clos_to_bvl_config_start c2)]` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM)
    (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (K ALL_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[clos_to_bvlProof_syntax_oracle_ok_start; ALL_DISTINCT_code_sort]) THEN
  ASM_SIMP_TAC[fromAList_code_sort] THEN
  REWRITE_TAC[clos_to_bvl_config_INFO.ri_accfupds; K_THM] THEN
  (* the semantics of the closLang phases *)
  MP_TAC(ISPECL [`ffi:(FFI)ffi_state`; `c:clos_to_bvl_config`;
                 `co:num->(num#(val_approx)spt#num_set#B)#clos_prog`;
                 `pure_cc (clos_to_bvl_compile_inc' (clos_to_bvl_config_max_app c))
                    (cc:B->(num#num#bvl_exp)list->(byte list#int64 list#B)option)`;
                 `es:clos_exp list`; `c2:clos_to_bvl_config`; `p2:(num#num#clos_exp)list`]
         compile_common_semantics) THEN
  ANTS_TAC THENL
   [USE_THEN "nf" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "ccm" (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`c:clos_to_bvl_config`; `c2:clos_to_bvl_config`; `es:clos_exp list`;
                   `co:num->(num#(val_approx)spt#num_set#B)#clos_prog`;
                   `p2:(num#num#clos_exp)list`] syntax_oracle_ok_call_FST_monotonic) THEN
    USE_THEN "sok" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "ccm" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "sok" (MP_TAC o REWRITE_RULE[clos_to_bvlProof_syntax_oracle_ok_def]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s0") MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s1") MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:B` (LABEL_TAC "s2")) MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s3") MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s4") MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s5") MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s6") MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s7") (LABEL_TAC "s8")) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "s2" (fun th -> REWRITE_TAC[th; FST; SND]) THEN
    REWRITE_TAC[compile_inc_post_kcompile_def] THEN
    USE_THEN "ccm" (STRIP_ASSUME_TAC o MATCH_MP C2BP3AUX_compile_common_parts) THEN
    ASM_REWRITE_TAC[FST; SND; clos_to_bvl_config_INFO.ri_accfupds; K_THM; GE; LE_REFL] THEN
    DISCH_TAC THEN
    USE_THEN "s4" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `IS_SOME (clos_to_bvl_config_known_conf c)`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP clos_knownProof_known_compile_IS_SOME) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IS_SOME_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `kx:clos_known_config` SUBST1_TAC) THEN
    REWRITE_TAC[option_val_approx_spt_def; THE_DEF] THEN CAKE_REWRITE_TAC[];
    DISCH_THEN(LABEL_TAC "ccs")] THEN
  (* the bvl semantics of the compiled program *)
  USE_THEN "ccs" (fun th -> REWRITE_TAC[GSYM th]) THEN
  MATCH_MP_TAC clos_to_bvlProof_compile_prog_semantics THEN
  EXISTS_TAC `p2:(num#num#clos_exp)list` THEN
  EXISTS_TAC `clos_to_bvl_compile_prog (clos_to_bvl_config_max_app c) p2` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `!name arity e.
                  FLOOKUP (alist_to_fmap p2) name = SOME (arity,e)
                  ==> ?aux1 e2 aux2.
                        clos_to_bvl_compile_exps (clos_to_bvl_config_max_app c) [e] aux1 =
                        ([e2],aux2) /\
                        lookup (name + num_stubs (clos_to_bvl_config_max_app c))
                          (fromAList (APPEND l0
                             (clos_to_bvl_compile_prog (clos_to_bvl_config_max_app c) p2))) =
                        SOME (arity,e2) /\
                        clos_to_bvlProof_code_installed aux2
                          (fromAList (APPEND l0
                             (clos_to_bvl_compile_prog (clos_to_bvl_config_max_app c) p2)))`
    (LABEL_TAC "code") THENL
   [MATCH_MP_TAC C2BP3AUX_cs_code THEN
    MAP_EVERY EXISTS_TAC [`es:clos_exp list`; `c2:clos_to_bvl_config`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "code" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "ccs" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "nf" (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* the init code *)
    REWRITE_TAC[clos_to_bvlProof_init_code_def] THEN USE_THEN "code" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[lookup_fromAList] THEN EXPAND_TAC "l0" THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; ALOOKUP_APPEND; ALOOKUP_toAList] THEN
    CONJ_TAC THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `clos_to_bvl_config_max_app c` init_code_ok) THEN
    (ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC]) THEN ASM_SIMP_TAC[option_CASE] THEN
    AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC;
    (* every_Fn_SOME *)
    MATCH_MP_TAC FEVERY_alist_to_fmap THEN REWRITE_TAC[C2BP3AUX_ALL_every_Fn_SOME] THEN
    USE_THEN "sok" (MP_TAC o REWRITE_RULE[clos_to_bvlProof_syntax_oracle_ok_def]) THEN
    REWRITE_TAC[clos_knownProof_syntax_ok_def] THEN STRIP_TAC THEN
    USE_THEN "ccm" (STRIP_ASSUME_TAC o MATCH_MP C2BP3AUX_compile_common_parts) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC compile_every_Fn_SOME THEN
    REWRITE_TAC[MAP_APPEND; every_Fn_SOME_APPEND; chain_exps_every_Fn_SOME] THEN
    MATCH_MP_TAC ccompile_every_Fn_SOME THEN
    MAP_EVERY EXISTS_TAC [`es_k:clos_exp list`; `clos_to_bvl_config_do_call c`; `g:num_set`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `clos_callProof_syntax_ok es_k` (fun th -> MP_TAC th THEN
      REWRITE_TAC[clos_callProof_syntax_ok_def] THEN SIMP_TAC[]) THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP kcompile_csyntax_ok) THEN
    MATCH_MP_TAC renumber_code_locs_list_csyntax_ok THEN
    MAP_EVERY EXISTS_TAC
      [`make_even (clos_to_bvl_config_next_loc c + MAX 1 (LENGTH (es:clos_exp list)))`;
       `clos_mti_compile (clos_to_bvl_config_do_mti c) (clos_to_bvl_config_max_app c) es`;
       `n:num`] THEN
    ASM_REWRITE_TAC[compile_every_Fn_vs_NONE];
    (* every_Fn_vs_SOME *)
    MATCH_MP_TAC FEVERY_alist_to_fmap THEN REWRITE_TAC[C2BP3AUX_ALL_every_Fn_vs_SOME] THEN
    USE_THEN "ccm" (STRIP_ASSUME_TAC o MATCH_MP C2BP3AUX_compile_common_parts) THEN
    ASM_REWRITE_TAC[annotate_compile_every_Fn_vs_SOME];
    (* the init globals *)
    REWRITE_TAC[lookup_fromAList] THEN MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "l0" THEN REWRITE_TAC[MEM_APPEND; MEM];
    (* the force stub *)
    REWRITE_TAC[lookup_fromAList] THEN MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "l0" THEN REWRITE_TAC[MEM_APPEND; MEM];
    (* the oracle invariant *)
    MP_TAC(ISPECL [`cc:B->(num#num#bvl_exp)list->(byte list#int64 list#B)option`;
                   `es:clos_exp list`; `co:num->(num#(val_approx)spt#num_set#B)#clos_prog`;
                   `c:clos_to_bvl_config`; `c2:clos_to_bvl_config`;
                   `p2:(num#num#clos_exp)list`; `c2:clos_to_bvl_config`]
           syntax_oracle_ok_to_oracle_inv) THEN
    USE_THEN "sok" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "ccm" (fun th -> REWRITE_TAC[th]) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN EXPAND_TAC "l0" THEN
    ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN REWRITE_TAC[ADD_SYM];
    (* the compiled code is installed *)
    MATCH_MP_TAC code_installed_fromAList THEN ASM_REWRITE_TAC[IS_SUBLIST_APPEND] THEN
    MAP_EVERY EXISTS_TAC [`l0:(num#num#bvl_exp)list`; `[]:(num#num#bvl_exp)list`] THEN
    REWRITE_TAC[APPEND_NIL]]);;


(* HOL4 line 9035 *)
let compile_inc_phases_all_distinct = prove
 (`!(orac:num->(num#(val_approx)spt#B)#clos_prog) i max_app dc c_st kc.
     SND (SND (orac i)) = []
     ==> ALL_DISTINCT (MAP FST (clos_to_bvl_compile_inc' max_app
           (clos_annotate_compile_inc
              (SND (cond_call_compile_inc dc c_st
                      (SND (known_co kc (state_co (ignore_table clos_number_compile_inc) orac)
                              i)))))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`orac:num->(num#(val_approx)spt#B)#clos_prog`; `i:num`]
         C2BP3AUX_oinv_number) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`state_co (ignore_table clos_number_compile_inc)
                   (orac:num->(num#(val_approx)spt#B)#clos_prog)`; `i:num`;
                 `kc:clos_known_config option`] known_co_req) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`SND (known_co kc (state_co (ignore_table clos_number_compile_inc)
                   (orac:num->(num#(val_approx)spt#B)#clos_prog)) i)`; `dc:bool`;
                 `c_st:num_set`] cond_call_compile_inc_req) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `SND (cond_call_compile_inc dc c_st
                  (SND (known_co kc (state_co (ignore_table clos_number_compile_inc)
                     (orac:num->(num#(val_approx)spt#B)#clos_prog)) i)))`
         annotate_compile_inc_req) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(CONJUNCT1(SPEC_ALL compile_inc_req_addrs)) THEN ASM_REWRITE_TAC[]);;

let C2BP3AUX_oinv_mono = prove
 (`!dm ma kc dc (co:num->(num#(val_approx)spt#num_set#B)#clos_prog) St offs.
     (!n. SND (SND (co n)) = []) /\
     is_state_oracle (ignore_table clos_number_compile_inc)
       (pure_co (cond_mti_compile_inc dm ma) o co) /\
     (!x. x IN St ==> FST (FST (co 0)) + offs > x)
     ==> oracle_monotonic (set_of_list o MAP ((+) offs) o req_compile_inc_addrs [] o SND) (<) St
           (pure_co clos_annotate_compile_inc o
            state_co (cond_call_compile_inc dc)
              (known_co kc (state_co (ignore_table clos_number_compile_inc)
                 (pure_co (cond_mti_compile_inc dm ma) o co))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s0") (CONJUNCTS_THEN2 (LABEL_TAC "s8") (LABEL_TAC "st"))) THEN
  ABBREV_TAC `co1 = pure_co (cond_mti_compile_inc dm ma) o
                   (co:num->(num#(val_approx)spt#num_set#B)#clos_prog)` THEN
  ABBREV_TAC `co2 = state_co (ignore_table clos_number_compile_inc)
                   (co1:num->(num#(val_approx)spt#num_set#B)#clos_prog)` THEN
  ABBREV_TAC `co3 = known_co kc (co2:num->((val_approx)spt#num_set#B)#clos_prog)` THEN
  ABBREV_TAC `co4 = state_co (cond_call_compile_inc dc) (co3:num->(num_set#B)#clos_prog)` THEN
  SUBGOAL_THEN `!k. SND (SND ((co1:num->(num#(val_approx)spt#num_set#B)#clos_prog) k)) = []`
    (LABEL_TAC "F1") THENL
   [X_GEN_TAC `k:num` THEN EXPAND_TAC "co1" THEN
    REWRITE_TAC[o_THM; SND_pure_co; SND_cond_mti_compile_inc] THEN
    USE_THEN "s0" (fun th -> REWRITE_TAC[th; COND_ID]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. ALL_DISTINCT (req_compile_inc_addrs [SUC]
                     (SND ((co2:num->((val_approx)spt#num_set#B)#clos_prog) k))) /\
                    SND (SND (co2 k)) = [] /\ can_extract (FST (SND (co2 k)))`
    (LABEL_TAC "F2") THENL
   [EXPAND_TAC "co2" THEN GEN_TAC THEN MATCH_MP_TAC C2BP3AUX_oinv_number THEN
    USE_THEN "F1" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. ALL_DISTINCT (req_compile_inc_addrs [SUC]
                     (SND ((co3:num->(num_set#B)#clos_prog) k))) /\
                    can_extract (FST (SND (co3 k))) /\
                    set_of_list (req_compile_inc_addrs [SUC] (SND (co3 k))) SUBSET
                    set_of_list (req_compile_inc_addrs [SUC]
                      (SND ((co2:num->((val_approx)spt#num_set#B)#clos_prog) k)))`
    (LABEL_TAC "F3") THENL
   [EXPAND_TAC "co3" THEN MATCH_MP_TAC C2BP3AUX_oinv_known THEN
    USE_THEN "F2" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. ALL_DISTINCT (req_compile_inc_addrs []
                     (SND ((co4:num->B#clos_prog) k))) /\
                    can_extract (FST (SND (co4 k))) /\
                    set_of_list (req_compile_inc_addrs [] (SND (co4 k))) SUBSET
                    set_of_list (req_compile_inc_addrs [SUC]
                      (SND ((co3:num->(num_set#B)#clos_prog) k)))`
    (LABEL_TAC "F4") THENL
   [EXPAND_TAC "co4" THEN MATCH_MP_TAC C2BP3AUX_oinv_call THEN
    USE_THEN "F3" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. ALL_DISTINCT (req_compile_inc_addrs []
                     (SND ((pure_co clos_annotate_compile_inc o (co4:num->B#clos_prog)) k))) /\
                    set_of_list (req_compile_inc_addrs []
                      (SND ((pure_co clos_annotate_compile_inc o co4) k))) SUBSET
                    set_of_list (req_compile_inc_addrs [] (SND (co4 k)))`
    (LABEL_TAC "F5") THENL
   [MATCH_MP_TAC C2BP3AUX_oinv_annotate THEN USE_THEN "F4" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `oracle_monotonic (set_of_list o MAP ((+) offs) o req_compile_inc_addrs [SUC] o SND)
                  (<) St (co2:num->((val_approx)spt#num_set#B)#clos_prog)`
    (LABEL_TAC "M2") THENL
   [EXPAND_TAC "co2" THEN MATCH_MP_TAC renumber_code_locs_monotonic_req THEN
    USE_THEN "s8" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "F1" (fun th -> REWRITE_TAC[th]) THEN
    EXPAND_TAC "co1" THEN REWRITE_TAC[o_THM; FST_pure_co] THEN
    USE_THEN "st" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `oracle_monotonic (set_of_list o MAP ((+) offs) o req_compile_inc_addrs [SUC] o SND)
                  (<) St (co3:num->(num_set#B)#clos_prog)`
    (LABEL_TAC "M3") THENL
   [EXPAND_TAC "co3" THEN MATCH_MP_TAC known_co_req_oracle THEN
    USE_THEN "M2" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `oracle_monotonic (set_of_list o MAP ((+) offs) o req_compile_inc_addrs [] o SND)
                  (<) St (co4:num->B#clos_prog)`
    (LABEL_TAC "M4") THENL
   [EXPAND_TAC "co4" THEN MATCH_MP_TAC cond_call_compile_inc_req_oracle THEN
    USE_THEN "M3" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC annotate_compile_inc_req_oracle THEN
  USE_THEN "M4" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "F5" (fun th -> REWRITE_TAC[th]));;

(* HOL4 line 9054 (HOL4 $< is (<); prog' is the pair of the code and the  *)
(* names of clos_to_bvl$compile) *)
let syntax_oracle_ok_bvl_FST_monotonic = prove
 (`!c c' es (co:num->(num#(val_approx)spt#num_set#B)#clos_prog) prog'.
     clos_to_bvlProof_syntax_oracle_ok c c' es co /\ clos_to_bvl_compile c es = (c',prog')
     ==> oracle_monotonic (set_of_list o MAP FST o SND) (<)
           (pred_set_count (FST (FST (co 0)) + num_stubs (clos_to_bvl_config_max_app c)))
           (pure_co (clos_to_bvl_compile_inc' (clos_to_bvl_config_max_app c)) o
            pure_co clos_annotate_compile_inc o
            state_co (cond_call_compile_inc (clos_to_bvl_config_do_call c))
              (known_co (clos_to_bvl_config_known_conf c)
                 (state_co (ignore_table clos_number_compile_inc)
                    (pure_co (cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
                                (clos_to_bvl_config_max_app c)) o co))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[clos_to_bvlProof_syntax_oracle_ok_def] o CONJUNCT1) THEN
  STRIP_TAC THEN MATCH_MP_TAC compile_inc_monotonic THEN
  MATCH_MP_TAC C2BP3AUX_oinv_mono THEN ASM_REWRITE_TAC[IN_COUNT; GT]);;


(* HOL4 line 9089 (HOL4 case ... of SOME n => ... | _ => ...; some is the  *)
(* binder of vocab.ml) *)
let assign_get_code_label_compile_op = prove
 (`!op.
     assign_get_code_label (clos_to_bvl_compile_op op) =
     (match (some n. op = clos_Label n) with SOME n -> {n} | NONE -> {})`,
  GEN_TAC THEN REWRITE_TAC[clos_to_bvl_compile_op_pmatch] THEN
  REPEAT (TOP_CASE_TAC THEN ASM_REWRITE_TAC[]) THEN
  RW[assign_get_code_label_def; compile_const_def] THEN
  CASES_ON `a':const` THEN REWRITE_TAC[compile_const_def; assign_get_code_label_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[assign_get_code_label_def] THEN
  REWRITE_TAC[C2BP3AUX_pair_CASE_FST_SND; assign_get_code_label_def]);;


(* HOL4 line 9098 (bvlProps' get_code_labels) *)
let recc_Lets_code_labels = prove
 (`!n nargs k rest.
     bvl_get_code_labels (recc_Lets n nargs k rest) =
     IMAGE (\j. n + 2 * j) (pred_set_count k) UNION bvl_get_code_labels rest`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  ONCE_REWRITE_TAC[recc_Lets_def] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; COUNT_ZERO; IMAGE_CLAUSES; UNION_EMPTY] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[bvl_get_code_labels_def; MAP; set_of_list; UNIONS_1; recc_Let_def;
                  mk_const_def; mk_label_def; assign_get_code_label_def; COUNT_SUC;
                  IMAGE_CLAUSES; UNIONS_INSERT; UNIONS_0; UNION_EMPTY] THEN
  SET_TAC[]);;


(* ML helpers for the proof of compile_exps_code_labels: C2BP3AUX_SING_TAC  *)
(* replaces the result c of each singleton compilation by [d];             *)
(* C2BP3AUX_IH_TAC lab resolves the induction hypothesis lab against the   *)
(* assumptions as far as possible and puts the result in the goal.          *)
let C2BP3AUX_SING_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = lhand(rand(concl th)) in
    if not (is_var c) then failwith "C2BP3AUX_SING_TAC" else
    let th' = MATCH_MP clos_to_bvl_compile_exps_SING th in
    MP_TAC th THEN CHOOSE_THEN SUBST_ALL_TAC th' THEN DISCH_TAC));;

let rec C2BP3AUX_chain th asl =
  match (try Some (tryfind (fun a -> MATCH_MP th a) asl) with Failure _ -> None) with
    Some th' -> C2BP3AUX_chain th' asl
  | None -> th;;

let C2BP3AUX_IH_TAC (lab:string) : tactic =
  USE_THEN lab (fun ih (asl,w as g) ->
    MP_TAC (C2BP3AUX_chain (REWRITE_RULE[IMP_CONJ] ih) (map snd asl)) g);;

let C2BP3AUX_PAIRARG_TAC : tactic =
  fun (asl,w as gl) ->
    let is_cand t =
      is_case_app t &&
      (let c,x,fs = dest_case_app t in
       fst(dest_const c) = "pair_CASE" && not (is_pair x) && free_in x w) in
    let t = find_term is_cand w in
    let _,x,fs = dest_case_app t in
    let f = hd fs in
    let tya,tyb = match dest_type(type_of x) with
        "prod",[a;b] -> a,b | _ -> failwith "C2BP3AUX_PAIRARG_TAC" in
    let n1,n2 =
      try let a,b = dest_abs f in let b1,_ = dest_abs b in
          fst(dest_var a),fst(dest_var b1)
      with Failure _ -> "p1","p2" in
    let avoid = itlist (union o thm_frees o snd) asl (frees w) in
    let v1 = variant avoid (mk_var(n1,tya)) in
    let v2 = variant (v1::avoid) (mk_var(n2,tyb)) in
    let nch = ISPEC x (nchotomy_of_type (type_of x)) in
    (MP_TAC nch THEN
     DISCH_THEN(X_CHOOSE_THEN v1 (X_CHOOSE_THEN v2
       (fun th -> SUBST1_TAC th THEN ASSUME_TAC th))) THEN
     CAKE_REWRITE_TAC[]) gl;;

let C2BP3AUX_ATOMS_SET_TAC : tactic = fun (asl,w as g) ->
  let is_atom t =
    type_of t = `:num->bool` &&
    (let h,_ = strip_comb t in is_const h &&
       mem (fst(dest_const h))
         ["IMAGE";"UNIONS";"bvl_get_code_labels";"clos_get_code_labels";"domain"]) in
  let ts = find_terms is_atom w in
  let maximal = filter (fun t -> not (exists (fun u -> not (u = t) && free_in t u) ts)) ts in
  let vars = map (fun t -> genvar (type_of t)) maximal in
  (MAP_EVERY (fun (t,v) -> SPEC_TAC(t,v)) (zip maximal vars) THEN SET_TAC[]) g;;

let C2BP3AUX_ALL_IH_TAC : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  let cands = filter (fun th -> let c = snd(strip_forall(concl th)) in is_imp c &&
                 can (find_term (fun t -> try fst(dest_const t) = "clos_to_bvl_compile_exps"
                                          with Failure _ -> false)) c) ths in
  let res = mapfilter (fun th ->
      let th' = C2BP3AUX_chain (REWRITE_RULE[IMP_CONJ] th) ths in
      if is_imp (snd(strip_forall(concl th'))) then failwith "unresolved" else th') cands in
  MAP_EVERY MP_TAC res g;;

let C2BP3AUX_labels_list_of_seq = prove
 (`!(f:num->bvl_exp) n.
     (!i. bvl_get_code_labels (f i) = {})
     ==> UNIONS (set_of_list (MAP bvl_get_code_labels (list_of_seq f n))) = {}`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[list_of_seq; MAP; MAP_APPEND; SET_OF_LIST_APPEND; set_of_list; UNIONS_UNION;
               UNIONS_INSERT; UNIONS_0; UNION_EMPTY]);;

let C2BP3AUX_labels_MAP_Var = prove
 (`!vs. UNIONS (set_of_list (MAP bvl_get_code_labels (MAP bvl_Var vs))) = {}`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; set_of_list; UNIONS_INSERT; UNIONS_0; UNION_EMPTY;
                  bvl_get_code_labels_def]);;

let C2BP3AUX_labels_REVERSE = prove
 (`!l. UNIONS (set_of_list (MAP bvl_get_code_labels (REVERSE l))) =
       UNIONS (set_of_list (MAP bvl_get_code_labels l))`,
  REWRITE_TAC[GSYM MAP_REVERSE; LIST_TO_SET_REVERSE]);;

let C2BP3AUX_labels_MAP_empty = prove
 (`!(f:A->bvl_exp) l.
     (!x. bvl_get_code_labels (f x) = {})
     ==> UNIONS (set_of_list (MAP bvl_get_code_labels (MAP f l))) = {}`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[MAP; set_of_list; UNIONS_INSERT; UNIONS_0; UNION_EMPTY]);;

let C2BP3AUX_MEM_MAP2 = prove
 (`!(f:A->B->C) l1 l2 y.
     LENGTH l1 = LENGTH l2 /\ MEM y (MAP2 f l1 l2)
     ==> ?a b. MEM a l1 /\ MEM b l2 /\ y = f a b`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; MAP2; MEM] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let C2BP3AUX_build_aux_labels = prove
 (`!n0 k nargs cs (aux1:(num#num#bvl_exp)list) n2 aux2.
     LENGTH nargs = LENGTH cs /\
     build_aux n0 (MAP2 (code_for_recc_case k) nargs cs) aux1 = (n2,aux2)
     ==> UNIONS (set_of_list (MAP (bvl_get_code_labels o SND o SND) aux2)) SUBSET
         UNIONS (set_of_list (MAP bvl_get_code_labels cs)) UNION
         UNIONS (set_of_list (MAP (bvl_get_code_labels o SND o SND) aux1))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_SET_OF_LIST; MEM_MAP] THEN
  X_GEN_TAC `x:num` THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `y:num#num#bvl_exp` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`n0:num`; `MAP2 (code_for_recc_case k) (nargs:num list) (cs:bvl_exp list)`;
                 `aux1:(num#num#bvl_exp)list`; `n2:num`; `aux2:(num#num#bvl_exp)list`;
                 `y:num#num#bvl_exp`] MEM_build_aux_imp_SND_MEM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`code_for_recc_case k`; `nargs:num list`; `cs:bvl_exp list`;
                   `SND (y:num#num#bvl_exp)`] C2BP3AUX_MEM_MAP2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `c:bvl_exp` STRIP_ASSUME_TAC)) THEN
    DISJ1_TAC THEN EXISTS_TAC `bvl_get_code_labels c` THEN CONJ_TAC THENL
     [EXISTS_TAC `c:bvl_exp` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(x:num) IN s` THEN ASM_REWRITE_TAC[o_THM] THEN
    REWRITE_TAC[code_for_recc_case_def; SND] THEN
    SIMP_TAC[bvl_get_code_labels_def; MAP; set_of_list; UNIONS_INSERT; UNIONS_0; UNION_EMPTY;
             MAP_APPEND; SET_OF_LIST_APPEND; UNIONS_UNION; assign_get_code_label_def;
             C2BP3AUX_labels_list_of_seq; IN_UNION; NOT_IN_EMPTY];
    DISJ2_TAC THEN EXISTS_TAC `s:num->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `y:num#num#bvl_exp` THEN ASM_REWRITE_TAC[]]);;

let C2BP3AUX_recc_labels = prove
 (`!l ns n.
     0 < n
     ==> ((l + ns) + 2 * (n - 1)) INSERT IMAGE (\j. (l + ns) + 2 * j) (pred_set_count (n - 1)) SUBSET
         IMAGE ((+) ns) (IMAGE (\k. l + 2 * k) (pred_set_count n))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_INSERT; IN_IMAGE; IN_COUNT] THEN X_GEN_TAC `x:num` THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THENL
   [EXISTS_TAC `l + 2 * (n - 1)` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `n - 1` THEN ASM_ARITH_TAC;
    EXISTS_TAC `l + 2 * j` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `j:num` THEN ASM_ARITH_TAC]);;

let C2BP3AUX_CL_NORM = [MAP; set_of_list; UNIONS_INSERT; UNIONS_0; UNION_EMPTY; MAP_APPEND;
  SET_OF_LIST_APPEND; UNIONS_UNION; IMAGE_UNION; IMAGE_CLAUSES; o_THM; ALL;
  bvl_get_code_labels_def; clos_get_code_labels_def; HD];;

let C2BP3AUX_CL_INTRO_TAC : tactic =
  REPEAT GEN_TAC THEN REPEAT (DISCH_THEN STRIP_ASSUME_TAC THEN REPEAT GEN_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; no_Labels_def; obeys_max_app_def; every_Fn_SOME_def]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[clos_to_bvl_compile_exps_def] o check (fun th ->
    let c = concl th in is_eq c && is_var (lhand (rand c)) && is_var (rand (rand c)) &&
    (try fst(dest_const(fst(strip_comb(lhand c)))) = "clos_to_bvl_compile_exps"
     with Failure _ -> false))) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT C2BP3AUX_PAIRARG_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(fun th g -> try CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) th g
                         with Failure _ -> ASSUME_TAC th g) THEN
  C2BP3AUX_SING_TAC THEN C2BP3AUX_ALL_IH_TAC;;

let C2BP3AUX_CL_FIN_TAC : tactic =
  REWRITE_TAC C2BP3AUX_CL_NORM THEN TRY(CAKE_REWRITE_TAC[]) THEN
  SIMP_TAC (C2BP3AUX_CL_NORM @ [C2BP3AUX_labels_list_of_seq; C2BP3AUX_labels_MAP_Var;
    C2BP3AUX_labels_REVERSE; assign_get_code_label_def; mk_const_def; mk_label_def;
    free_let_def; ADD_SYM]) THEN
  C2BP3AUX_ATOMS_SET_TAC;;

let C2BP3AUX_build_aux_labels' = prove
 (`!n0 k nargs cs (aux1:(num#num#bvl_exp)list) n2 aux2.
     build_aux n0 (MAP2 (code_for_recc_case k) nargs cs) aux1 = (n2,aux2)
     ==> LENGTH nargs = LENGTH cs
     ==> UNIONS (set_of_list (MAP (bvl_get_code_labels o SND o SND) aux2)) SUBSET
         UNIONS (set_of_list (MAP bvl_get_code_labels cs)) UNION
         UNIONS (set_of_list (MAP (bvl_get_code_labels o SND o SND) aux1))`,
  MESON_TAC[C2BP3AUX_build_aux_labels]);;

let C2BP3AUX_LETREC_ARG_TAC (f:term->tactic) : tactic = fun (asl,w as g) ->
  let t = find_term (fun t -> try let h,args = strip_comb t in
                                  fst(dest_const h) = "clos_Letrec" && length args = 5
                              with Failure _ -> false) w in
  f (el 3 (snd(strip_comb t))) g;;

let C2BP3AUX_DEDUP_TAC : tactic = fun (asl,w as g) ->
  let eqs = filter (fun th -> let c = concl th in is_eq c && is_pair (rand c)) (map snd asl) in
  let pairs = List.concat (map (fun th1 -> map (fun th2 -> (th1,th2)) eqs) eqs) in
  let th1,th2 =
    try List.find (fun (th1,th2) -> lhs(concl th1) = lhs(concl th2) &&
                                    not (rhs(concl th1) = rhs(concl th2))) pairs
    with Not_found -> failwith "C2BP3AUX_DEDUP_TAC" in
  let eth = REWRITE_RULE[PAIR_EQ; CONS_11] (TRANS (SYM th1) th2) in
  (MP_TAC eth THEN
   DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (fun th -> SUBST_ALL_TAC th ORELSE ASSUME_TAC th))) g;;

let C2BP3AUX_LR_NORM_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_CONS_NIL; distinctness "list"; injectivity "list"; PAIR_EQ;
    IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM1; FORALL_UNWIND_THM2; MAP; ALL; FST; SND;
    every_Fn_SOME_def]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  CAKE_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT C2BP3AUX_PAIRARG_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(fun th g -> try CONJUNCTS_THEN (SUBST_ALL_TAC o SYM) th g
                         with Failure _ -> ASSUME_TAC th g) THEN
  C2BP3AUX_SING_TAC THEN REPEAT C2BP3AUX_DEDUP_TAC THEN C2BP3AUX_ALL_IH_TAC;;

let C2BP3AUX_CL_FIN_LR_TAC (extra:thm list) : tactic =
  REWRITE_TAC (C2BP3AUX_CL_NORM @ [build_recc_lets_def; recc_Let0_def; recc_Lets_code_labels]) THEN
  TRY(CAKE_REWRITE_TAC[]) THEN
  SIMP_TAC (C2BP3AUX_CL_NORM @ extra @ [C2BP3AUX_labels_list_of_seq; C2BP3AUX_labels_MAP_Var;
    C2BP3AUX_labels_MAP_empty; C2BP3AUX_labels_REVERSE; assign_get_code_label_def; mk_const_def;
    mk_label_def; free_let_def; K_THM; recc_Lets_code_labels; ADD_SYM; MAP_o]) THEN
  C2BP3AUX_ATOMS_SET_TAC;;

(* HOL4 line 9112 (get_code_labels of bvl programs is bvlProps', of closLang *)
(* programs closProps'; HOL4 UNION is left-associative) *)
let compile_exps_code_labels = prove
 (`!app es1 aux1 es2 aux2.
     clos_to_bvl_compile_exps app es1 aux1 = (es2,aux2) /\
     ALL no_Labels es1 /\ 0 < app /\ ALL (obeys_max_app app) es1 /\ every_Fn_SOME es1
     ==> UNIONS (set_of_list (MAP bvl_get_code_labels es2)) UNION
         UNIONS (set_of_list (MAP (bvl_get_code_labels o SND o SND) aux2))
         SUBSET
         ((IMAGE ((+) (num_stubs app)) (UNIONS (set_of_list (MAP clos_get_code_labels es1))) UNION
           UNIONS (set_of_list (MAP (bvl_get_code_labels o SND o SND) aux1))) UNION
          domain (clos_to_bvl_init_code app)) UNION
         {num_stubs app - 2}`,
  MATCH_MP_TAC clos_to_bvl_compile_exps_ind THEN REPEAT CONJ_TAC THEN
  C2BP3AUX_CL_INTRO_TAC THENL
   [(* [] *) C2BP3AUX_CL_FIN_TAC;
    (* CONS *) C2BP3AUX_CL_FIN_TAC;
    (* Var *) C2BP3AUX_CL_FIN_TAC;
    (* If *) C2BP3AUX_CL_FIN_TAC;
    (* Let *) C2BP3AUX_CL_FIN_TAC;
    (* Raise *) C2BP3AUX_CL_FIN_TAC;
    (* Tick *) C2BP3AUX_CL_FIN_TAC;
    (* Op *) REPEAT COND_CASES_TAC THEN REWRITE_TAC C2BP3AUX_CL_NORM THEN
    ASM_REWRITE_TAC[assign_get_code_label_compile_op; some_F; assign_get_code_label_def] THEN
    C2BP3AUX_CL_FIN_TAC;
    (* App *) CASES_ON `loc_opt:num option` THEN REWRITE_TAC C2BP3AUX_CL_NORM THEN
    CAKE_REWRITE_TAC[] THENL
     [FIRST_ASSUM(ASSUME_TAC o MATCH_MP clos_to_bvl_compile_exps_LENGTH o check (fun th ->
        try lhand(lhand(concl th)) = `xs2:clos_exp list` with Failure _ -> false)) THEN
      SUBGOAL_THEN `LENGTH (c2:bvl_exp list) - 1 IN domain (clos_to_bvl_init_code max_app)`
        MP_TAC THENL
       [ASM_SIMP_TAC[domain_init_code; IN_COUNT] THEN
        MATCH_MP_TAC(ARITH_RULE `a < m ==> a < m + x`) THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[mk_cl_call_def; generic_app_fn_location_def; LENGTH_LIST_OF_SEQ] THEN
      C2BP3AUX_CL_FIN_TAC;
      C2BP3AUX_CL_FIN_TAC];
    (* Fn *) FIRST_X_ASSUM(X_CHOOSE_THEN `l:num` SUBST_ALL_TAC o REWRITE_RULE[IS_SOME_EXISTS] o
      check (fun th -> try fst(dest_const(rator(concl th))) = "IS_SOME" with Failure _ -> false)) THEN
    C2BP3AUX_CL_FIN_TAC;
    (* Letrec *)
    FIRST_X_ASSUM(X_CHOOSE_THEN `l:num` SUBST_ALL_TAC o REWRITE_RULE[IS_SOME_EXISTS] o
      check (fun th -> try fst(dest_const(rator(concl th))) = "IS_SOME" with Failure _ -> false)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_case_app(lhand(concl th)))) THEN
    C2BP3AUX_LETREC_ARG_TAC CASES_ON THENL
     [C2BP3AUX_LR_NORM_TAC THEN C2BP3AUX_CL_FIN_LR_TAC [LENGTH; COUNT_ZERO];
      C2BP3AUX_LETREC_ARG_TAC (CASES_ON o rand) THEN
      C2BP3AUX_LETREC_ARG_TAC (CASES_ON o rand o rator) THENL
       [C2BP3AUX_LR_NORM_TAC THEN
        C2BP3AUX_CL_FIN_LR_TAC [LENGTH; COUNT_SUC; COUNT_ZERO; MULT_CLAUSES; ADD_CLAUSES];
        C2BP3AUX_LR_NORM_TAC THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP C2BP3AUX_build_aux_labels') THEN
        ANTS_TAC THENL
         [ASSUM_LIST(fun ths -> REWRITE_TAC(mapfilter (MATCH_MP clos_to_bvl_compile_exps_LENGTH) ths)) THEN
          REWRITE_TAC[LENGTH; LENGTH_MAP];
          ALL_TAC] THEN
        C2BP3AUX_LETREC_ARG_TAC (fun fns -> MP_TAC(SPECL [`l:num`; `num_stubs max_app`;
          mk_comb(`LENGTH:(num#clos_exp)list->num`,fns)] C2BP3AUX_recc_labels)) THEN
        ANTS_TAC THENL [REWRITE_TAC[LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
        C2BP3AUX_CL_FIN_LR_TAC []]];
    (* Handle *) C2BP3AUX_CL_FIN_TAC;
    (* Call *) C2BP3AUX_CL_FIN_TAC]);;

let C2BP3AUX_MAP_labels_MAP2 = prove
 (CASE_TERM `!(ls:(num#num#clos_exp)list) (es:bvl_exp list) m.
     LENGTH es = LENGTH ls
     ==> MAP (bvl_get_code_labels o SND o SND)
           (MAP2 (\p exp. match p with (loc,args,y) -> (loc + m,args,exp)) ls es) =
         MAP bvl_get_code_labels es`,
  REWRITE_TAC[] THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; MAP2; MAP; NOT_SUC; SUC_INJ] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  SPEC_TAC(`h:num#num#clos_exp`,`h:num#num#clos_exp`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  CAKE_REWRITE_TAC[o_THM; SND]);;

(* HOL4 line 9210 *)
let clos_to_bvlProof_compile_prog_code_labels = prove
 (`!max_app prog.
     0 < max_app /\
     ALL no_Labels (MAP (SND o SND) prog) /\
     ALL (obeys_max_app max_app) (MAP (SND o SND) prog) /\
     every_Fn_SOME (MAP (SND o SND) prog)
     ==> UNIONS (set_of_list (MAP (bvl_get_code_labels o SND o SND)
                                (clos_to_bvl_compile_prog max_app prog))) SUBSET
         (IMAGE ((+) (num_stubs max_app))
            (UNIONS (set_of_list (MAP clos_get_code_labels (MAP (SND o SND) prog)))) UNION
          domain (clos_to_bvl_init_code max_app)) UNION
         {num_stubs max_app - 2}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[clos_to_bvl_compile_prog_def] THEN
  MP_TAC(ISPEC `clos_to_bvl_compile_exps max_app
                  (MAP (SND o SND) (prog:(num#num#clos_exp)list)) []` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `es:bvl_exp list` (X_CHOOSE_THEN `aux:(num#num#bvl_exp)list`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CAKE_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP clos_to_bvl_compile_exps_LENGTH) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_MAP]) THEN
  ASM_SIMP_TAC[MAP_APPEND; SET_OF_LIST_APPEND; UNIONS_UNION; C2BP3AUX_MAP_labels_MAP2] THEN
  MP_TAC(ISPECL [`max_app:num`; `MAP (SND o SND) (prog:(num#num#clos_exp)list)`;
                 `[]:(num#num#bvl_exp)list`; `es:bvl_exp list`; `aux:(num#num#bvl_exp)list`]
         compile_exps_code_labels) THEN
  ASM_REWRITE_TAC[MAP; set_of_list; UNIONS_0; UNION_EMPTY]);;


(* HOL4 line 9232 *)
let chain_exps_no_Labels = prove
 (`!es l. ALL no_Labels es ==> ALL no_Labels (MAP (SND o SND) (chain_exps l es))`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN MATCH_MP_TAC chain_exps_ind THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[chain_exps_def; MAP; o_THM; ALL; no_Labels_def; distinctness "clos_op"] THEN
  MESON_TAC[]);;

(* HOL4 line 9240 *)
let chain_exps_obeys_max_app = prove
 (`!es l k.
     ALL (obeys_max_app k) es ==> ALL (obeys_max_app k) (MAP (SND o SND) (chain_exps l es))`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN MATCH_MP_TAC chain_exps_ind THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[chain_exps_def; MAP; o_THM; ALL; obeys_max_app_def] THEN
  MESON_TAC[]);;

(* HOL4 line 9248 [allow_rebind] (rebinds the theorem of HOL4 line 8596) *)
let chain_exps_every_Fn_SOME = prove
 (`!es l. every_Fn_SOME es ==> every_Fn_SOME (MAP (SND o SND) (chain_exps l es))`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN MATCH_MP_TAC chain_exps_ind THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[chain_exps_def; MAP; o_THM; every_Fn_SOME_def] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[CLOSPROPSAUX_every_Fn_SOME_cons] THEN
  REWRITE_TAC[every_Fn_SOME_def] THEN ASM_MESON_TAC[CLOSPROPSAUX_every_Fn_SOME_cons]);;
