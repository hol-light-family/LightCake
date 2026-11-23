(* ========================================================================= *)
(* bvl_to_bviProof_p1: part 1 of 2 (HOL4 lines 1-2200) of bvl_to_bviProof,  *)
(* port of HOL4 compiler/backend/proofs/bvl_to_bviProofScript.sml (CakeML    *)
(* v3479).  Correctness proof for bvl_to_bvi: the value and state relations, *)
(* bv_ok, the stub code (CopyGlobals, AllocGlobal, ListLength, FromListByte, *)
(* ToListByte, SumListLength, ConcatByte) and the namespace lemmas.          *)
(* The part _p2 needs this part.  B2BP1AUX_ names are local helpers (not     *)
(* HOL4 names).                                                              *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Records: s.f (bvlSem state) is bvl_state_f s, t.f (bviSem state) is     *)
(*   bvi_state_f t, c.f (bvl_to_bvi config) is bvl_to_bvi_config_f c;        *)
(*   r with f := v is RECTYPE_f_fupd (K v) r; t with <| f1 := v1; f2 := v2 |> *)
(*   is RECTYPE_f1_fupd (K v1) (RECTYPE_f2_fupd (K v2) t); record literals   *)
(*   are RECTYPE_REC with the fields in declaration order.                   *)
(* - Constants of two theories with one HOL4 name: bvlSem's evaluate,        *)
(*   semantics, do_app, ... are bvl_ ones, bviSem's bvi_ ones (decided by    *)
(*   the types; Var, Call, Op of bvi programs are bvi_ constructors);         *)
(*   bvl_to_bvi$compile_inc (two arguments) is bvl_to_bvi_compile_inc,        *)
(*   compile_inc limit split cut is bvl_inline_compile_inc; get_code_labels  *)
(*   of bvl programs is bvl_get_code_labels, of bvi programs                 *)
(*   bvi_get_code_labels; free_names is bvi_tailrecProof's.                  *)
(* - HOL4 Overloads num_stubs, nss, in_ns_0, in_ns_1 are written out         *)
(*   (bvl_num_stubs, bvl_to_bvi_namespaces, n MOD bvl_to_bvi_namespaces = 0  *)
(*   and = 1).                                                               *)
(* - HOL4 Types: bvlSem states (num#C,FFI)bvl_state (state_rel) or           *)
(*   (C,FFI)bvl_state, bviSem states (C,FFI)bvi_state.                        *)
(* - HOL4 BIGUNION is UNIONS; set is set_of_list; EVERY is ALL; ++ is APPEND *)
(*   (left-associative in HOL4), + of nums is left-associative in HOL4 (the  *)
(*   sums are parenthesised where it matters to the reading); HOL4 UNION    *)
(*   is left-associative and binds tighter than INSERT; n2w is word, w2n is  *)
(*   val; $& is int_of_num; LEAST is minimal; HOL4 case is match (statements *)
(*   with match or paired let use CASE_TERM).                                *)
(* - Free variables of HOL4 statements are universally quantified, after    *)
(*   HOL4's explicit binders; unused bound variables are left out (comment). *)
(* - HOL4 theorems derived by rules (Theorem X = ..., val X = ... |> RULE)  *)
(*   are stated with their resulting statement; ML vals that are tactics,   *)
(*   abbreviations or prints are comments.                                   *)
(* - HOL4 in_ns is bvl_to_bviProof_in_ns (a short or common word), and       *)
(*   in_ns_def is bvl_to_bviProof_in_ns_def.                                 *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ffi/ffi.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/bvl_to_bvi.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/proofs/bvl_constProof.ml";;
needs "compiler/backend/proofs/bvl_handleProof.ml";;
needs "compiler/backend/proofs/bvi_letProof.ml";;
needs "compiler/backend/proofs/bvl_inlineProof.ml";;
needs "compiler/backend/proofs/bvi_tailrecProof.ml";;
needs "compiler/backend/proofs/bvi_inlineProof.ml";;
needs "compiler/backend/proofs/bvi_tmcProof.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 1: HOL4 lines 1-2200 ===== *)

(* HOL4 lines 15-20: simpset and parser settings (temp_delsimps,            *)
(* augment_srw_ss [rewrites [SNOC_APPEND]], Parse.hide str): not needed.    *)
(* HOL4 line 22: val handle_ok_def = bvl_handleProofTheory.handle_ok_def     *)
(* (the definition of bvl_handleProof, used by the proofs).                  *)
(* HOL4 lines 25-26: Overload num_stubs = bvl_num_stubs, nss =               *)
(* bvl_to_bvi_namespaces (written out).                                      *)

(* HOL4 line 28 (Termination: measure v_size o SND) *)
let adjust_bv_def = cake_def_wf
  `MEASURE (\(b:num->num,v:bvl_v). bvl_v_size v)`
  TERM_TAC
  `(adjust_bv b (bvl_Number i) = bvl_Number i) /\
   (adjust_bv b (bvl_Word64 w) = bvl_Word64 w) /\
   (adjust_bv b (bvl_RefPtr l r) = bvl_RefPtr l (b r)) /\
   (adjust_bv b (bvl_CodePtr c) = bvl_CodePtr (bvl_num_stubs + bvl_to_bvi_namespaces * c)) /\
   (adjust_bv b (bvl_Block tag vs) = bvl_Block tag (MAP (adjust_bv b) vs))`;;

(* HOL4 line 40: val adjust_bv_ind = theorem "adjust_bv_ind" *)
let adjust_bv_ind = cake_ind "adjust_bv";;

(* HOL4 line 42 [simp] *)
let adjust_bv_Unit = prove
 (`!x. adjust_bv x bvl_Unit = bvl_Unit`,
  REWRITE_TAC[bvl_Unit_def; adjust_bv_def; MAP]);;

let _ = cake_add_simps [adjust_bv_Unit];;

(* HOL4 line 48 [simp] *)
let adjust_bv_Boolv = prove
 (`!x b. adjust_bv x (bvl_Boolv b) = bvl_Boolv b`,
  REWRITE_TAC[bvl_Boolv_def; adjust_bv_def; MAP]);;

let _ = cake_add_simps [adjust_bv_Boolv];;

(* HOL4 line 54 (of the most general type, as in HOL4) *)
let aux_code_installed_def = cake_def
  `(aux_code_installed ([]:(num#A#B)list) (t:(A#B)spt) <=> T) /\
   (aux_code_installed (CONS (name,arg_count,body) rest) t <=>
      lookup name t = SOME (arg_count,body) /\
      aux_code_installed rest t)`;;

(* HOL4 line 61 [local] *)
let aux_code_installed_APPEND = prove
 (`!(xs:(num#A#B)list) ys code.
     aux_code_installed (APPEND xs ys) code
     ==> aux_code_installed xs code /\ aux_code_installed ys code`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[APPEND; aux_code_installed_def; FORALL_PROD] THEN
  MESON_TAC[]);;

(* HOL4 line 70 *)
let aux_code_installed_subspt = prove
 (`!(x:(num#A#B)list) c1 c2.
     aux_code_installed x c1 /\ subspt c1 c2 ==> aux_code_installed x c2`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[aux_code_installed_def; FORALL_PROD; subspt_lookup] THEN
  MESON_TAC[]);;

(* HOL4 lines 78-79: Overload in_ns_0 = (\n. n MOD bvl_to_bvi_namespaces =  *)
(* 0), in_ns_1 = (\n. n MOD bvl_to_bvi_namespaces = 1) (written out)         *)

(* HOL4 line 81 (of the most general type, as in HOL4) *)
let bvl_to_bviProof_names_ok_def = cake_def
  `bvl_to_bviProof_names_ok (s_code:(A)spt) (t_code:(B)spt)
     (s_oracle:num->(num#C)#(D#E#bvl_exp)list) <=>
     (!n k prog. s_oracle n = (k,prog)
                 ==> ALL (\(name,arity,exp). handle_ok [exp]) prog) /\
     (let next = FST (FST (s_oracle 0)) in
        !n. n IN domain t_code /\ bvl_num_stubs <= n
            ==> if n MOD bvl_to_bvi_namespaces = 1
                then n < bvl_num_stubs + bvl_to_bvi_namespaces * next
                else n MOD bvl_to_bvi_namespaces = 0 /\
                     (n - bvl_num_stubs) DIV bvl_to_bvi_namespaces IN domain s_code)`;;

(* HOL4 line 92 (compile_inc is bvl_to_bvi's; HOL4 Number 0 is              *)
(* bvl_Number (&0)) *)
let bvl_to_bviProof_state_rel_def = cake_def
  `bvl_to_bviProof_state_rel (b:num->num) (s:(num#C,FFI)bvl_state) (t:(C,FFI)bvi_state) <=>
     INJ b (FDOM (bvl_state_refs s)) (FDOM (bvi_state_refs t)) /\
     (!k. match FLOOKUP (bvl_state_refs s) k with
            NONE -> T
          | SOME (bvl_ValueArray vs) ->
              FLOOKUP (bvi_state_refs t) (b k) = SOME (bvl_ValueArray (MAP (adjust_bv b) vs))
          | SOME (bvl_Thunk m v) ->
              FLOOKUP (bvi_state_refs t) (b k) = SOME (bvl_Thunk m (adjust_bv b v))
          | SOME res -> FLOOKUP (bvi_state_refs t) (b k) = SOME res) /\
     bvl_state_ffi s = bvi_state_ffi t /\
     (!p. bvi_state_global t = SOME p
          ==> ~(p IN IMAGE b (FDOM (bvl_state_refs s))) /\
              ?z. FLOOKUP (bvi_state_refs t) p =
                    SOME (bvl_ValueArray
                      (CONS (bvl_Number (&(SUC (LENGTH (bvl_state_globals s)))))
                         (APPEND (MAP (misc_the (bvl_Number (&0)) o OPTION_MAP (adjust_bv b))
                                    (bvl_state_globals s))
                            (REPLICATE (z - SUC (LENGTH (bvl_state_globals s)))
                               (bvl_Number (&0)))))) /\
                  SUC (LENGTH (bvl_state_globals s)) <= z) /\
     bvl_state_clock s = bvi_state_clock t /\
     bvi_state_compile_oracle t = state_co bvl_to_bvi_compile_inc (bvl_state_compile_oracle s) /\
     bvl_state_compile s = state_cc bvl_to_bvi_compile_inc (bvi_state_compile t) /\
     lookup AllocGlobal_location (bvi_state_code t) = SOME AllocGlobal_code /\
     lookup CopyGlobals_location (bvi_state_code t) = SOME CopyGlobals_code /\
     lookup ListLength_location (bvi_state_code t) = SOME ListLength_code /\
     lookup FromListByte_location (bvi_state_code t) = SOME FromListByte_code /\
     lookup ToListByte_location (bvi_state_code t) = SOME ToListByte_code /\
     lookup SumListLength_location (bvi_state_code t) = SOME SumListLength_code /\
     lookup ConcatByte_location (bvi_state_code t) = SOME ConcatByte_code /\
     bvl_to_bviProof_names_ok (bvl_state_code s) (bvi_state_code t)
       (bvl_state_compile_oracle s) /\
     (!name arity exp.
        lookup name (bvl_state_code s) = SOME (arity,exp)
        ==> ?n. let (c1,aux1,n1) = bvl_to_bvi_compile_exps n [exp] in
                  lookup (bvl_num_stubs + bvl_to_bvi_namespaces * name) (bvi_state_code t) =
                    SOME (arity,bvi_let_compile_exp (HD c1)) /\
                  aux_code_installed (append aux1) (bvi_state_code t) /\
                  handle_ok [exp])`;;

(* HOL4 line 132 *)
let state_rel_FLOOKUP_byteArray = prove
 (`!b s (t:(C,FFI)bvi_state) m l n.
     bvl_to_bviProof_state_rel b s t /\
     FLOOKUP (bvl_state_refs s) n = SOME (bvl_ByteArray m l)
     ==> FLOOKUP (bvi_state_refs t) (b n) = SOME (bvl_ByteArray m l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bviProof_state_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `n:num` o CONJUNCT1 o CONJUNCT2)
    ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 141 *)
let state_rel_FLOOKUP_valueArray = prove
 (`!b s (t:(C,FFI)bvi_state) ptr vs.
     bvl_to_bviProof_state_rel b s t /\
     FLOOKUP (bvl_state_refs s) ptr = SOME (bvl_ValueArray vs)
     ==> FLOOKUP (bvi_state_refs t) (b ptr) = SOME (bvl_ValueArray (MAP (adjust_bv b) vs))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bviProof_state_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `ptr:num` o CONJUNCT1 o CONJUNCT2)
    ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 150 *)
let state_rel_FLOOKUP_MutBlock = prove
 (`!b s (t:(C,FFI)bvi_state) ptr tg fin l c r.
     bvl_to_bviProof_state_rel b s t /\
     FLOOKUP (bvl_state_refs s) ptr = SOME (MutBlock tg fin l c r)
     ==> FLOOKUP (bvi_state_refs t) (b ptr) = SOME (MutBlock tg fin l c r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bviProof_state_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `ptr:num` o CONJUNCT1 o CONJUNCT2)
    ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 159 *)
let state_rel_FLOOKUP_Thunk = prove
 (`!b s (t:(C,FFI)bvi_state) ptr m v.
     bvl_to_bviProof_state_rel b s t /\
     FLOOKUP (bvl_state_refs s) ptr = SOME (bvl_Thunk m v)
     ==> FLOOKUP (bvi_state_refs t) (b ptr) = SOME (bvl_Thunk m (adjust_bv b v))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bviProof_state_rel_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `ptr:num` o CONJUNCT1 o CONJUNCT2)
    ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 168 (Termination: measure v_size o SND) *)
let bv_ok_def = cake_def_wf
  `MEASURE (\(refs:(num,(bvl_v)bvl_ref)fmap,v:bvl_v). bvl_v_size v)`
  TERM_TAC
  `(bv_ok (refs:(num,(bvl_v)bvl_ref)fmap) (bvl_RefPtr l r) <=> r IN FDOM refs) /\
   (bv_ok refs (bvl_Block tag vs) <=> ALL (bv_ok refs) vs) /\
   (bv_ok refs _ <=> T)`;;

(* HOL4 line 178: val bv_ok_ind = theorem "bv_ok_ind" *)
let bv_ok_ind = cake_ind "bv_ok";;

(* HOL4 line 180 [local] *)
let bv_ok_SUBSET_IMP = prove
 (`!refs x (refs2:(num,(bvl_v)bvl_ref)fmap).
     bv_ok refs x /\ FDOM refs SUBSET FDOM refs2 ==> bv_ok refs2 x`,
  MATCH_MP_TAC bv_ok_ind THEN REWRITE_TAC[bv_ok_def; GSYM ALL_MEM] THEN
  MESON_TAC[SUBSET]);;

(* HOL4 line 188 [simp] *)
let bv_ok_Unit = prove
 (`!refs. bv_ok refs bvl_Unit`,
  REWRITE_TAC[bvl_Unit_def; bv_ok_def; ALL]);;

let _ = cake_add_simps [bv_ok_Unit];;

(* HOL4 line 194 [simp] *)
let bv_ok_Boolv = prove
 (`!refs b. bv_ok refs (bvl_Boolv b)`,
  REWRITE_TAC[bvl_Boolv_def; bv_ok_def; ALL]);;

let _ = cake_add_simps [bv_ok_Boolv];;

(* HOL4 line 200 [local] *)
let bv_ok_IMP_adjust_bv_eq = prove
 (`!b2 a1 b3 refs.
     bv_ok refs a1 /\ (!a. a IN FDOM refs ==> b2 a = b3 a)
     ==> adjust_bv b2 a1 = adjust_bv b3 a1`,
  MATCH_MP_TAC adjust_bv_ind THEN
  REWRITE_TAC[adjust_bv_def; bv_ok_def; GSYM ALL_MEM; injectivity "bvl_v"] THEN
  REPEAT STRIP_TAC THEN TRY (MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM]) THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 211 *)
let bvl_to_bviProof_state_ok_def = cake_def
  `bvl_to_bviProof_state_ok (s:(C,FFI)bvl_state) <=>
     ALL (\x. match x with NONE -> T | SOME v -> bv_ok (bvl_state_refs s) v)
       (bvl_state_globals s) /\
     !k. match FLOOKUP (bvl_state_refs s) k with
           SOME (bvl_ValueArray vs) -> ALL (bv_ok (bvl_state_refs s)) vs
         | SOME (bvl_Thunk _ v) -> bv_ok (bvl_state_refs s) v
         | _ -> T`;;

(* HOL4 line 222 [local] *)
let evaluate_ok_lemma = prove
 (`!n (s:(C,FFI)bvl_state).
     (bvl_to_bviProof_state_ok (bvl_dec_clock n s) <=> bvl_to_bviProof_state_ok s) /\
     bvl_state_refs (bvl_dec_clock n s) = bvl_state_refs s`,
  REWRITE_TAC[bvl_to_bviProof_state_ok_def; bvl_dec_clock_def;
              bvl_state_INFO.ri_accfupds; K_THM]);;

(* HOL4 line 229 [local] *)
let evaluate_IMP_bv_ok = prove
 (`!xs env (s:(C,FFI)bvl_state) res t a1 as.
     bvl_evaluate (xs,env,s) = (res,t)
     ==> (bv_ok (bvl_state_refs s) a1 ==> bv_ok (bvl_state_refs t) a1) /\
         (ALL (bv_ok (bvl_state_refs s)) as ==> ALL (bv_ok (bvl_state_refs t)) as)`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP bvl_evaluate_refs_SUBSET) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[bv_ok_SUBSET_IMP]);;

(* HOL4 line 239 [local] *)
let v_to_list_ok = prove
 (`!v x refs. bvl_v_to_list v = SOME x /\ bv_ok refs v ==> ALL (bv_ok refs) x`,
  MATCH_MP_TAC bvl_v_to_list_ind THEN REWRITE_TAC[bvl_v_to_list_def; bv_ok_def; ALL] THEN
  REPEAT STRIP_TAC THEN GVS(all_case_eqs()) THEN ASM_MESON_TAC[]);;

(* HOL4 line 249 *)
let list_to_v_ok = prove
 (`!xs refs. ALL (bv_ok refs) xs ==> bv_ok refs (bvl_list_to_v xs)`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[ALL; bvl_list_to_v_def; bv_ok_def]);;

(* HOL4 line 255 *)
let list_to_v_ok_APPEND = prove
 (`!xs ys refs.
     bv_ok refs (bvl_list_to_v xs) /\ bv_ok refs (bvl_list_to_v ys)
     ==> bv_ok refs (bvl_list_to_v (APPEND xs ys))`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[APPEND; ALL; bvl_list_to_v_def; bv_ok_def]);;

(* a local helper (not in HOL4): state_ok after one more ref, given that  *)
(* the new entry is ok with respect to the new refs                       *)
let B2BP1AUX_state_ok_refs_update = prove
 (`!(r:(C,FFI)bvl_state) p x.
     bvl_to_bviProof_state_ok r /\
     (!vs. x = bvl_ValueArray vs ==> ALL (bv_ok (bvl_state_refs r |+ (p,x))) vs) /\
     (!m v. x = bvl_Thunk m v ==> bv_ok (bvl_state_refs r |+ (p,x)) v)
     ==> bvl_to_bviProof_state_ok
           (bvl_state_refs_fupd (K (bvl_state_refs r |+ (p,x))) r)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!v. bv_ok (bvl_state_refs (r:(C,FFI)bvl_state)) v ==>
                    bv_ok (bvl_state_refs r |+ (p,x)) v` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC bv_ok_SUBSET_IMP THEN
    EXISTS_TAC `bvl_state_refs (r:(C,FFI)bvl_state)` THEN
    ASM_REWRITE_TAC[FDOM_FUPDATE] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[bvl_to_bviProof_state_ok_def; bvl_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
      fst (strip_comb (concl th)) = `ALL:(bvl_v option->bool)->(bvl_v option)list->bool`)) THEN
    MATCH_MP_TAC MONO_ALL THEN MATCH_MP_TAC option_INDUCT THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[FLOOKUP_UPDATE] THEN COND_CASES_TAC THENL
     [CASES_ON `x:(bvl_v)bvl_ref` THEN CASE_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
      SPEC_TAC(`FLOOKUP (bvl_state_refs (r:(C,FFI)bvl_state)) k`,
               `ox:((bvl_v)bvl_ref)option`) THEN
      MATCH_MP_TAC option_INDUCT THEN CASE_REWRITE_TAC[] THEN
      MATCH_MP_TAC bvl_ref_INDUCT THEN CASE_REWRITE_TAC[] THEN
      ASM_MESON_TAC[ALL_IMP]]]);;

(* a local helper for do_build_ok (not in HOL4): one part *)
let B2BP1AUX_do_part_ok = prove
 (`!m p (r:(C,FFI)bvl_state) x refs1.
     bvl_do_part m p (bvl_state_refs r) = (x,refs1) /\
     bvl_to_bviProof_state_ok r /\ (!k. bv_ok (bvl_state_refs r) (m k))
     ==> bvl_to_bviProof_state_ok (bvl_state_refs_fupd (K refs1) r) /\ bv_ok refs1 x`,
  GEN_TAC THEN MATCH_MP_TAC const_part_INDUCT THEN
  REWRITE_TAC[bvl_do_part_def; LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[bv_ok_def; FDOM_FUPDATE; IN_INSERT; ALL_MAP; o_DEF] THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM] THEN
  TRY (MATCH_MP_TAC B2BP1AUX_state_ok_refs_update THEN
       ASM_REWRITE_TAC[distinctness "bvl_ref"] THEN NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bvl_to_bviProof_state_ok_def]) THEN
  ASM_REWRITE_TAC[bvl_to_bviProof_state_ok_def; bvl_state_INFO.ri_accfupds; K_THM]);;

(* a local helper (not in HOL4): ASM_ARITH_TAC after dropping the        *)
(* assumptions that are not arithmetic                                    *)
let rec B2BP1AUX_is_numrel t =
  if is_neg t then B2BP1AUX_is_numrel (dest_neg t)
  else if is_conj t || is_disj t || is_imp t then
    B2BP1AUX_is_numrel (lhand t) && B2BP1AUX_is_numrel (rand t)
  else (is_eq t && type_of (lhs t) = `:num`) ||
       (try let c,args = strip_comb t in
            mem (fst(dest_const c)) ["<"; "<="; ">"; ">="] &&
            length args = 2 && type_of (hd args) = `:num`
        with Failure _ -> false);;

let B2BP1AUX_ARITH_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (K ALL_TAC o check (not o B2BP1AUX_is_numrel o concl))) THEN
  ASM_ARITH_TAC;;

(* HOL4 line 278 *)
let do_build_ok = prove
 (`!parts m n (r:(C,FFI)bvl_state) q rs.
     bvl_do_build m n parts (bvl_state_refs r) = (q,rs) /\
     bvl_to_bviProof_state_ok r /\ (!k. bv_ok (bvl_state_refs r) (m k))
     ==> bvl_to_bviProof_state_ok (bvl_state_refs_fupd (K rs) r) /\ bv_ok rs q`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[bvl_do_build_def] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[bvl_to_bviProof_state_ok_def]) THEN
    ASM_REWRITE_TAC[bvl_to_bviProof_state_ok_def; bvl_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  MP_TAC(ISPEC `bvl_do_part m h (bvl_state_refs (r:(C,FFI)bvl_state))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:bvl_v` (X_CHOOSE_THEN `refs1:(num,(bvl_v)bvl_ref)fmap`
    ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[pair_CASE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num->bvl_v`; `h:const_part`; `r:(C,FFI)bvl_state`;
                 `x:bvl_v`; `refs1:(num,(bvl_v)bvl_ref)fmap`] B2BP1AUX_do_part_ok) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BVLPROPSAUX_do_part_SUBSET) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(n =+ x) (m:num->bvl_v)`; `n + 1`;
    `bvl_state_refs_fupd (K refs1) (r:(C,FFI)bvl_state)`; `q:bvl_v`;
    `rs:(num,(bvl_v)bvl_ref)fmap`]) THEN
  ASM_REWRITE_TAC[bvl_state_INFO.ri_accfupds; K_THM] THEN ANTS_TAC THENL
   [REWRITE_TAC[APPLY_UPDATE_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC bv_ok_SUBSET_IMP THEN
    EXISTS_TAC `bvl_state_refs (r:(C,FFI)bvl_state)` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[bvl_to_bviProof_state_ok_def; bvl_state_INFO.ri_accfupds; K_THM]]);;

(* HOL4 line 318: fun cases_on_op (an ML tactic) *)

(* local helpers for do_app_ok_lemma (not in HOL4): state_ok and bv_ok   *)
(* under the state changes of do_app, and a tactic for the leaves of the  *)
(* case split of do_app (HOL4's proof splits the cases by hand)          *)
let B2BP1AUX_state_ok_fupds = prove
 (`(!f (r:(C,FFI)bvl_state).
      bvl_to_bviProof_state_ok (bvl_state_ffi_fupd f r) <=> bvl_to_bviProof_state_ok r) /\
   (!f (r:(C,FFI)bvl_state).
      bvl_to_bviProof_state_ok (bvl_state_code_fupd f r) <=> bvl_to_bviProof_state_ok r) /\
   (!f (r:(C,FFI)bvl_state).
      bvl_to_bviProof_state_ok (bvl_state_compile_oracle_fupd f r) <=>
      bvl_to_bviProof_state_ok r) /\
   (!f (r:(C,FFI)bvl_state).
      bvl_to_bviProof_state_ok (bvl_state_compile_fupd f r) <=>
      bvl_to_bviProof_state_ok r) /\
   (!f (r:(C,FFI)bvl_state).
      bvl_to_bviProof_state_ok (bvl_state_clock_fupd f r) <=> bvl_to_bviProof_state_ok r)`,
  REWRITE_TAC[bvl_to_bviProof_state_ok_def; bvl_state_INFO.ri_accfupds]);;

let B2BP1AUX_state_ok_globals_update = prove
 (CASE_TERM `!(r:(C,FFI)bvl_state) gs.
     bvl_to_bviProof_state_ok r /\
     ALL (\x. match x with NONE -> T | SOME v -> bv_ok (bvl_state_refs r) v) gs
     ==> bvl_to_bviProof_state_ok (bvl_state_globals_fupd (K gs) r)`,
  REWRITE_TAC[bvl_to_bviProof_state_ok_def; bvl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let B2BP1AUX_state_ok_refs_ffi_fupd = prove
 (`!R f (r:(C,FFI)bvl_state).
     bvl_to_bviProof_state_ok (bvl_state_refs_fupd (K R) (bvl_state_ffi_fupd f r)) <=>
     bvl_to_bviProof_state_ok (bvl_state_refs_fupd (K R) r)`,
  REWRITE_TAC[bvl_to_bviProof_state_ok_def; bvl_state_INFO.ri_accfupds; K_THM]);;

let B2BP1AUX_bv_ok_FUPDATE = prove
 (`!refs p (x:(bvl_v)bvl_ref) v vs.
     (bv_ok refs v ==> bv_ok (refs |+ (p,x)) v) /\
     (ALL (bv_ok refs) vs ==> ALL (bv_ok (refs |+ (p,x))) vs)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!v. bv_ok refs v ==> bv_ok (refs |+ (p,x:(bvl_v)bvl_ref)) v` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC bv_ok_SUBSET_IMP THEN
    EXISTS_TAC `refs:(num,(bvl_v)bvl_ref)fmap` THEN
    ASM_REWRITE_TAC[FDOM_FUPDATE] THEN SET_TAC[];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_ALL THEN ASM_REWRITE_TAC[]]);;

let B2BP1AUX_state_ok_FLOOKUP = prove
 (`!(r:(C,FFI)bvl_state) p vs m v.
     bvl_to_bviProof_state_ok r
     ==> (FLOOKUP (bvl_state_refs r) p = SOME (bvl_ValueArray vs)
          ==> ALL (bv_ok (bvl_state_refs r)) vs) /\
         (FLOOKUP (bvl_state_refs r) p = SOME (bvl_Thunk m v)
          ==> bv_ok (bvl_state_refs r) v)`,
  REWRITE_TAC[bvl_to_bviProof_state_ok_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let B2BP1AUX_state_ok_get_global = prove
 (`!(r:(C,FFI)bvl_state) n v.
     bvl_to_bviProof_state_ok r /\ get_global n (bvl_state_globals r) = SOME (SOME v)
     ==> bv_ok (bvl_state_refs r) v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bviProof_state_ok_def; get_global_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o CONJUNCT1) MP_TAC) THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_TAC THEN REWRITE_TAC[GSYM ALL_EL] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let B2BP1AUX_state_ok_lemmas = prove
 (`!(r:(C,FFI)bvl_state).
     bvl_to_bviProof_state_ok r
     ==> (!p vs. FLOOKUP (bvl_state_refs r) p = SOME (bvl_ValueArray vs)
                 ==> ALL (bv_ok (bvl_state_refs r)) vs) /\
         (!p m v. FLOOKUP (bvl_state_refs r) p = SOME (bvl_Thunk m v)
                  ==> bv_ok (bvl_state_refs r) v) /\
         (!n v. get_global n (bvl_state_globals r) = SOME (SOME v)
                ==> bv_ok (bvl_state_refs r) v)`,
  MESON_TAC[B2BP1AUX_state_ok_FLOOKUP; B2BP1AUX_state_ok_get_global]);;

let B2BP1AUX_do_int_app_ok = prove
 (`!op vs v. bvl_do_int_app op vs = SOME v ==> !refs. bv_ok refs v`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CLOSSEMAUX_do_int_app_some) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[bv_ok_def; bv_ok_Boolv]);;

let B2BP1AUX_do_word_app_ok = prove
 (`!op vs v. bvl_do_word_app op vs = SOME v ==> !refs. bv_ok refs v`,
  MATCH_MP_TAC bvl_do_word_app_ind THEN REWRITE_TAC[bvl_do_word_app_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[bv_ok_def; bv_ok_Boolv]);;

let B2BP1AUX_ALL_EL_IMP = prove
 (`!P (xs:A list) n. ALL P xs /\ n < LENGTH xs ==> P (EL n xs)`,
  MESON_TAC[ALL_EL]);;

let B2BP1AUX_FACTS_TAC : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  let is_sok th = try fst(dest_const(fst(strip_comb(concl th)))) =
                        "bvl_to_bviProof_state_ok" with Failure _ -> false in
  let lems = flat (map (fun th -> CONJUNCTS (MATCH_MP B2BP1AUX_state_ok_lemmas th))
                       (filter is_sok ths)) in
  let f1 = flat (map (fun lem -> mapfilter (MATCH_MP lem) ths) lems) in
  let f2 = flat (map (fun th1 -> mapfilter (fun th2 -> MATCH_MP v_to_list_ok (CONJ th1 th2))
                                   ths) ths) in
  MAP_EVERY ASSUME_TAC (f1 @ f2) g;;

let B2BP1AUX_DO_APP_OK_LEAF_TAC : tactic =
  STRIP_TAC THEN RVEQ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ALL; bv_ok_def; bv_ok_Boolv; bv_ok_Unit]) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  B2BP1AUX_FACTS_TAC THEN
  REWRITE_TAC[B2BP1AUX_state_ok_fupds; B2BP1AUX_state_ok_refs_ffi_fupd;
              bvl_state_INFO.ri_accfupds; K_THM; bv_ok_def; bv_ok_Boolv; bv_ok_Unit;
              FDOM_FUPDATE; IN_INSERT] THEN
  ASM_REWRITE_TAC[] THEN
  TRY (FIRST_X_ASSUM(fun th -> MP_TAC (MATCH_MP (REWRITE_RULE[IMP_CONJ] do_build_ok)
                                  (REWRITE_RULE[bvl_do_build_const_def] th))) THEN
       ASM_REWRITE_TAC[bv_ok_def] THEN SIMP_TAC[] THEN NO_TAC) THEN
  REPEAT CONJ_TAC THEN
  TRY (FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC (MATCH_MP B2BP1AUX_do_int_app_ok th))) THEN
  TRY (FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC (MATCH_MP B2BP1AUX_do_word_app_ok th))) THEN
  TRY (MATCH_MP_TAC B2BP1AUX_ALL_EL_IMP THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC BASICAUX_num_of_int_lt THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY (MATCH_MP_TAC list_to_v_ok THEN
       ASM_REWRITE_TAC[ALL_APPEND; ALL_MAP; o_DEF; bv_ok_def; ALL_T] THEN NO_TAC) THEN
  TRY (ASM_SIMP_TAC[ALL_APPEND; EVERY_TAKE; EVERY_DROP] THEN NO_TAC) THEN
  TRY (MATCH_MP_TAC B2BP1AUX_state_ok_globals_update THEN ASM_REWRITE_TAC[] THEN
       RULE_ASSUM_TAC(REWRITE_RULE[bvl_to_bviProof_state_ok_def]) THEN
       ASM_REWRITE_TAC[ALL_APPEND; EVERY_REPLICATE] THEN
       TRY (MATCH_MP_TAC IMP_EVERY_LUPDATE THEN ASM_REWRITE_TAC[]) THEN
       CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY (MATCH_MP_TAC B2BP1AUX_state_ok_refs_update THEN
       ASM_REWRITE_TAC[distinctness "bvl_ref"; injectivity "bvl_ref"] THEN
       REPEAT STRIP_TAC THEN RVEQ_TAC THEN
       ASM_SIMP_TAC[B2BP1AUX_bv_ok_FUPDATE; EVERY_REPLICATE] THEN
       TRY (MATCH_MP_TAC IMP_EVERY_LUPDATE THEN ASM_SIMP_TAC[B2BP1AUX_bv_ok_FUPDATE]) THEN
       NO_TAC);;

(* HOL4 line 321 [local] *)
let do_app_ok_lemma = prove
 (`!(r:(C,FFI)bvl_state) a op q t.
     bvl_to_bviProof_state_ok r /\ ALL (bv_ok (bvl_state_refs r)) a /\
     bvl_do_app op a r = Rval (q,t)
     ==> bvl_to_bviProof_state_ok t /\ bv_ok (bvl_state_refs t) q`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_do_app_def; bvl_do_install_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  B2BP1AUX_DO_APP_OK_LEAF_TAC);;

(* HOL4 line 585 *)
let do_app_ok = prove
 (`!(r:(C,FFI)bvl_state) a op q t env.
     bvl_to_bviProof_state_ok r /\ ALL (bv_ok (bvl_state_refs r)) a /\
     bvl_do_app op a r = Rval (q,t)
     ==> bvl_to_bviProof_state_ok t /\ bv_ok (bvl_state_refs t) q /\
         (ALL (bv_ok (bvl_state_refs r)) env ==> ALL (bv_ok (bvl_state_refs t)) env)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`r:(C,FFI)bvl_state`; `a:bvl_v list`; `op:clos_op`; `q:bvl_v`;
                `t:(C,FFI)bvl_state`] do_app_ok_lemma) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP bvl_do_app_refs_SUBSET) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[bv_ok_SUBSET_IMP]);;

(* HOL4 line 596: print (no statement) *)

(* HOL4 line 598 [local] *)
let bvl_to_bviProof_dec_clock_inc_clock = prove
 (`!c (t:(C,FFI)bvi_state).
     ~(c = 0) ==> bvi_dec_clock 1 (bvi_inc_clock c t) = bvi_inc_clock (c - 1) t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bvi_dec_clock_def; bvi_inc_clock_def; bvi_state_component_equality;
              bvi_state_INFO.ri_accfupds; K_THM] THEN
  ASM_ARITH_TAC);;

(* HOL4 line 605 (HOL4's s is the code) *)
let find_code_bv_ok = prove
 (`!dest vs (s:(num#A)spt) args e2 refs.
     bvl_find_code dest vs s = SOME (args,e2) /\ ALL (bv_ok refs) vs
     ==> ALL (bv_ok refs) args`,
  MATCH_MP_TAC option_INDUCT THEN REWRITE_TAC[bvl_find_code_def] THEN CONJ_TAC THEN
  REPEAT GEN_TAC THEN REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ALL (bv_ok refs) (vs:bvl_v list)` THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
    [GSYM (MATCH_MP APPEND_BUTLAST_LAST th)]) THEN
  SIMP_TAC[ALL_APPEND]);;

(* local helpers for evaluate_ok (not in HOL4): a resolution tactic for   *)
(* the induction over evaluate (HOL4 fs with the induction hypotheses,    *)
(* imp_res_tac evaluate_SING, evaluate_IMP_bv_ok, do_app_ok, ...)         *)
let B2BP1AUX_dest_thunk_ok = prove
 (`!(s:(C,FFI)bvl_state) v m w.
     bvl_to_bviProof_state_ok s /\ bvl_dest_thunk v (bvl_state_refs s) = bvl_IsThunk m w
     ==> bv_ok (bvl_state_refs s) w`,
  REPEAT GEN_TAC THEN CASES_ON `v:bvl_v` THEN REWRITE_TAC[bvl_dest_thunk_def] THEN
  CASE_REWRITE_TAC[distinctness "bvl_dest_thunk_ret"] THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[distinctness "bvl_dest_thunk_ret"; injectivity "bvl_dest_thunk_ret"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP B2BP1AUX_state_ok_lemmas) THEN
  ASM_MESON_TAC[]);;

let B2BP1AUX_eval_mono = prove
 (`!xs env (s:(C,FFI)bvl_state) res t.
     bvl_evaluate (xs,env,s) = (res,t)
     ==> (!v. bv_ok (bvl_state_refs s) v ==> bv_ok (bvl_state_refs t) v) /\
         (!l. ALL (bv_ok (bvl_state_refs s)) l ==> ALL (bv_ok (bvl_state_refs t)) l)`,
  MESON_TAC[evaluate_IMP_bv_ok]);;

let B2BP1AUX_RES_TAC (norms:thm list) (gens:thm list) : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let is_impth th = is_imp(snd(strip_forall(concl th))) in
  let rw th = try CASE_REWRITE_RULE[] (REWRITE_RULE norms th) with Failure _ -> th in
  let curry th = try PURE_REWRITE_RULE[IMP_CONJ] (rw th) with Failure _ -> rw th in
  let norm th = CONJUNCTS (rw th) in
  let known = ref (map concl asms) in
  let fresh th = concl th <> `T` &&
                 (if exists (aconv (concl th)) !known then false
                  else (known := concl th :: !known; true)) in
  let imps = map curry (filter is_impth asms @ gens) in
  let facts = flat (map norm (filter (not o is_impth) asms)) in
  let rec loop n imps facts acc =
    if n = 0 then acc else
    let res = flat (map (fun i -> mapfilter (fun f -> MATCH_MP i f) facts) imps) in
    let res = filter fresh (flat (map norm res)) in
    if res = [] then acc else
    let nf = filter (not o is_impth) res and ni = map curry (filter is_impth res) in
    loop (n-1) (imps @ ni) (facts @ nf) (acc @ res) in
  MAP_EVERY ASSUME_TAC (loop 15 imps facts []) gl;;

let B2BP1AUX_SING_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (fun th ->
    let th' = MATCH_MP bvl_evaluate_SING th in
    let v = fst(dest_exists(concl th')) in
    let a = lhs(snd(dest_exists(concl th'))) in
    if is_var a then
      ASSUME_TAC th THEN X_CHOOSE_THEN (variant (frees (concl th)) v) SUBST_ALL_TAC th'
    else failwith "")) ;;

let B2BP1AUX_DO_APP_ERR_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (fun th ->
    let th' = MATCH_MP bvl_do_app_err th in
    if is_var (rand(rhs(concl th))) then
      ASSUME_TAC th THEN STRIP_ASSUME_TAC th' THEN RVEQ_TAC
    else failwith ""));;

let B2BP1AUX_do_app_ok_imp = prove
 (`!op a (r:(C,FFI)bvl_state) q t.
     bvl_do_app op a r = Rval (q,t)
     ==> bvl_to_bviProof_state_ok r ==> ALL (bv_ok (bvl_state_refs r)) a
     ==> bvl_to_bviProof_state_ok t /\ bv_ok (bvl_state_refs t) q /\
         (!env. ALL (bv_ok (bvl_state_refs r)) env ==> ALL (bv_ok (bvl_state_refs t)) env)`,
  MESON_TAC[do_app_ok]);;

let B2BP1AUX_find_code_bv_ok_imp = prove
 (`!dest vs (s:(num#A)spt) args e2.
     bvl_find_code dest vs s = SOME (args,e2)
     ==> !refs. ALL (bv_ok refs) vs ==> ALL (bv_ok refs) args`,
  MESON_TAC[find_code_bv_ok]);;

let B2BP1AUX_dest_thunk_ok_imp = prove
 (`!(s:(C,FFI)bvl_state) v m w.
     bvl_dest_thunk v (bvl_state_refs s) = bvl_IsThunk m w
     ==> bvl_to_bviProof_state_ok s ==> bv_ok (bvl_state_refs s) w`,
  MESON_TAC[B2BP1AUX_dest_thunk_ok]);;

let B2BP1AUX_ALL_EL_imp = prove
 (`!P (l:A list). ALL P l ==> !n. n < LENGTH l ==> P (EL n l)`,
  MESON_TAC[B2BP1AUX_ALL_EL_IMP]);;

let B2BP1AUX_EV_NORMS = [ALL_APPEND; ALL; HD; EVERY_REVERSE; evaluate_ok_lemma;
  B2BP1AUX_state_ok_fupds; bvl_state_INFO.ri_accfupds; K_THM];;

let B2BP1AUX_EV_GENS = [B2BP1AUX_eval_mono; B2BP1AUX_do_app_ok_imp;
  B2BP1AUX_find_code_bv_ok_imp; B2BP1AUX_dest_thunk_ok_imp; B2BP1AUX_ALL_EL_imp];;

(* evaluate_ok in curried form, by induction (HOL4: recInduct evaluate_ind) *)
let B2BP1AUX_evaluate_ok = prove
 (CASE_TERM
  `!xs env (s:(C,FFI)bvl_state).
     bvl_to_bviProof_state_ok s /\ ALL (bv_ok (bvl_state_refs s)) env ==>
     !res t. bvl_evaluate (xs,env,s) = (res,t) ==>
     bvl_to_bviProof_state_ok t /\
         (match res with
            Rval vs -> ALL (bv_ok (bvl_state_refs t)) vs
          | Rerr (Rraise v) -> bv_ok (bvl_state_refs t) v
          | _ -> T) /\
         ALL (bv_ok (bvl_state_refs t)) env`,
  MATCH_MP_TAC BVLPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN BVLPROPSAUX_SPLIT_TAC THEN
  B2BP1AUX_SING_TAC THEN B2BP1AUX_DO_APP_ERR_TAC THEN
  B2BP1AUX_RES_TAC B2BP1AUX_EV_NORMS B2BP1AUX_EV_GENS THEN
  RULE_ASSUM_TAC(REWRITE_RULE B2BP1AUX_EV_NORMS) THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC B2BP1AUX_EV_NORMS);;

(* HOL4 line 616 *)
let evaluate_ok = prove
 (CASE_TERM
  `!xs env (s:(C,FFI)bvl_state) res t.
     bvl_evaluate (xs,env,s) = (res,t) /\
     bvl_to_bviProof_state_ok s /\ ALL (bv_ok (bvl_state_refs s)) env
     ==> bvl_to_bviProof_state_ok t /\
         (match res with
            Rval vs -> ALL (bv_ok (bvl_state_refs t)) vs
          | Rerr (Rraise v) -> bv_ok (bvl_state_refs t) v
          | _ -> T) /\
         ALL (bv_ok (bvl_state_refs t)) env`,
  MESON_TAC[B2BP1AUX_evaluate_ok]);;

(* HOL4 line 680: val evaluate_MAP_Var = Q.prove (...) |> INST_TYPE (its   *)
(* resulting statement; evaluate and Var are bviSem's) *)
let evaluate_MAP_Var = prove
 (`!l env vs b (s:(C,FFI)bvi_state).
     ALL isVar l /\ bvl_get_vars (MAP destVar l) env = SOME vs
     ==> bvi_evaluate (MAP (bvi_Var o destVar) l,MAP (adjust_bv b) env,s) =
         (Rval (MAP (adjust_bv b) vs),s)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAP; bvl_get_vars_def; option_INJ; bvi_evaluate_def] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[MAP];
    ALL_TAC] THEN
  CASES_ON `h:bvl_exp` THEN REWRITE_TAC[ALL; isVar_def] THEN
  REWRITE_TAC[MAP; destVar_def; o_THM; bvl_get_vars_def] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
  TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  STRIP_TAC THEN RVEQ_TAC THEN B2BP1AUX_RES_TAC [] [] THEN
  ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN
  ASM_SIMP_TAC[bvi_evaluate_def; LENGTH_MAP; EL_MAP] THEN
  CASE_REWRITE_TAC[HD; MAP]);;

(* HOL4 line 696: val evaluate_MAP_Var2 = Q.prove (...) |> SPEC_ALL |>     *)
(* INST_TYPE (its resulting statement) *)
let evaluate_MAP_Var2 = prove
 (`!args vs env (s:(C,FFI)bvi_state).
     bVarBound (LENGTH vs) args /\ ALL isVar args
     ==> ?ts. bvi_evaluate (MAP (bvi_Var o destVar) args,APPEND vs env,s) = (Rval ts,s) /\
              bvi_evaluate (MAP (bvi_Var o destVar) args,vs,s) = (Rval ts,s)`,
  REWRITE_TAC[IMP_CONJ] THEN ONCE_REWRITE_TAC[bVarBound_EVERY] THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAP; ALL; bvi_evaluate_def; PAIR_EQ; injectivity "result"] THEN
    EXISTS_TAC `[]:bvl_v list` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  CASES_ON `h:bvl_exp` THEN REWRITE_TAC[ALL; isVar_def; bVarBound_def] THEN
  REWRITE_TAC[MAP; destVar_def; o_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`vs:bvl_v list`; `env:bvl_v list`; `s:(C,FFI)bvi_state`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ts0:bvl_v list` STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN
  ASM_SIMP_TAC[bvi_evaluate_def; LENGTH_APPEND; EL_APPEND1;
               ARITH_RULE `n < a ==> n < a + b:num`] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[HD] THEN MESON_TAC[]);;

(* local helpers for bEval_bVarBound (not in HOL4): a case split of the   *)
(* evaluations that leaves the induction hypotheses unchanged, and one    *)
(* step of the proof (unfold, resolve, rewrite)                           *)
(* split the first evaluation that a pair case of the goal inspects:       *)
(* evaluate a = (Rval v,s1) or (Rerr e,s1) becomes an assumption; only the  *)
(* goal is rewritten (the induction hypotheses stay as they are)           *)
let B2BP1AUX_EV_SPLIT_TAC (evname:string) : tactic = fun (asl,w as gl) ->
  let is_ev_case t =
    try let c,args = strip_comb t in
        fst(dest_const c) = "pair_CASE" &&
        fst(dest_const(fst(strip_comb (hd args)))) = evname
    with Failure _ -> false in
  let t = find_term is_ev_case w in
  let ev = hd(snd(strip_comb t)) in
  let rty,sty = match dest_type (type_of ev) with
                  (_,[a;b]) -> a,b | _ -> failwith "B2BP1AUX_EV_SPLIT_TAC" in
  let avoid = itlist (union o frees o concl o snd) asl (frees w) in
  let r = variant avoid (mk_var("r",rty)) in
  let s1 = variant (r::avoid) (mk_var("s1",sty)) in
  let cth = ISPEC r (cases "result") in
  let d1,d2 = dest_disj (concl cth) in
  let v = variant (s1::r::avoid) (mk_var("v",type_of(fst(dest_exists d1)))) in
  let e = variant (s1::r::avoid) (mk_var("e",type_of(fst(dest_exists d2)))) in
  (X_CHOOSE_THEN r (X_CHOOSE_THEN s1 (fun th -> ASSUME_TAC th THEN
     REWRITE_TAC[th; pair_CASE])) (ISPEC ev PAIR_SURJECTIVE) THEN
   DISJ_CASES_THEN2 (X_CHOOSE_THEN v SUBST_ALL_TAC) (X_CHOOSE_THEN e SUBST_ALL_TAC)
     cth) gl;;

let B2BP1AUX_bVarBound_Let_gen = prove
 (`!n (xs:bvl_exp list) x2 (v:bvl_v list).
     bVarBound (n + LENGTH xs) [x2] ==> LENGTH xs = LENGTH v ==>
     bVarBound (LENGTH v + n) [x2]`,
  MESON_TAC[ADD_SYM]);;

let B2BP1AUX_BVB_NORMS = [LENGTH_APPEND; LENGTH; APPEND; GSYM APPEND_ASSOC; ADD1;
                          bVarBound_def];;

let B2BP1AUX_BVB_STEP : tactic =
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN BETA_TAC THEN
  B2BP1AUX_RES_TAC B2BP1AUX_BVB_NORMS [bvl_evaluate_IMP_LENGTH; B2BP1AUX_bVarBound_Let_gen] THEN
  ASM_SIMP_TAC[LENGTH_APPEND; EL_APPEND1; ARITH_RULE `n < a ==> n < a + b:num`] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];;

(* bEval_bVarBound in curried form, by induction (HOL4: recInduct          *)
(* evaluate_ind) *)
let B2BP1AUX_bEval_bVarBound = prove
 (`!xs vs (s:(C,FFI)bvl_state).
     bVarBound (LENGTH vs) xs
     ==> !env. bvl_evaluate (xs,APPEND vs env,s) = bvl_evaluate (xs,vs,s)`,
  MATCH_MP_TAC BVLPROPSAUX_evaluate_ind THEN REPEAT CONJ_TAC THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[bVarBound_def]) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  ONCE_REWRITE_TAC[bvl_evaluate_def] THEN B2BP1AUX_BVB_STEP THEN
  REPEAT ((B2BP1AUX_EV_SPLIT_TAC "bvl_evaluate" ORELSE COND_CASES_TAC ORELSE TOP_CASE_TAC)
          THEN B2BP1AUX_BVB_STEP));;

(* HOL4 line 709 [local] *)
let bEval_bVarBound = prove
 (`!xs vs (s:(C,FFI)bvl_state) env.
     bVarBound (LENGTH vs) xs
     ==> bvl_evaluate (xs,APPEND vs env,s) = bvl_evaluate (xs,vs,s)`,
  MESON_TAC[B2BP1AUX_bEval_bVarBound]);;

(* HOL4 lines 727-732: val iEval_def = bviSemTheory.evaluate_def, bEvalOp_def *)
(* = bvlSemTheory.do_app_def, iEvalOp_def = bviSemTheory.do_app_def          *)
(* (abbreviations for the proofs)                                            *)

(* local helpers for the stub code proofs (not in HOL4; HOL4 uses EVAL   *)
(* and simp with evaluate_def, do_app_def, ...): evaluation of do_app on *)
(* a concrete operation, and repeated unfolding of evaluate on concrete   *)
(* code                                                                   *)
let B2BP1AUX_DO_APP_CONV =
  REWRITE_CONV[bvi_do_app_def; distinctness "clos_op"] THENC
  REWRITE_CONV[bvi_do_app_aux_def] THENC CASE_REWRITE_CONV[] THENC
  REWRITE_CONV[bvl_do_app_def] THENC CASE_REWRITE_CONV[];;

let B2BP1AUX_EL_0 = prove
 (`!(h:A) t. EL 0 (CONS h t) = h`,
  REWRITE_TAC[EL; HD]);;

let B2BP1AUX_EL_SUC = prove
 (`!n (h:A) t. EL (SUC n) (CONS h t) = EL n t`,
  REWRITE_TAC[EL; TL]);;

(* EL k l for a numeral k and a list literal l *)
let rec B2BP1AUX_EL_CONV tm =
  match tm with
    Comb(Comb(Const("EL",_),n),l) when is_numeral n && is_cons l ->
      if dest_numeral n =/ num 0 then REWR_CONV B2BP1AUX_EL_0 tm
      else (RATOR_CONV(RAND_CONV num_CONV) THENC REWR_CONV B2BP1AUX_EL_SUC THENC
            B2BP1AUX_EL_CONV) tm
  | _ -> failwith "B2BP1AUX_EL_CONV";;

let B2BP1AUX_BVI_EV_TAC thl =
  REPEAT (CHANGED_TAC (
    ASM_REWRITE_TAC ([bvi_evaluate_def; REVERSE; APPEND; LENGTH; NULL; HD; TL] @ thl) THEN
    CASE_REWRITE_TAC[] THEN CONV_TAC (DEPTH_CONV B2BP1AUX_EL_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
    CONV_TAC B2BP1AUX_DO_APP_CONV));;

(* clock bookkeeping of a stub call, and the rewrites of the stub proofs *)
let B2BP1AUX_dec_inc_clock = prove
 (`!c (s:(C,FFI)bvi_state).
     bvi_dec_clock (0 + 1) (bvi_inc_clock (c + 1) s) = bvi_inc_clock c s /\
     bvi_dec_clock 1 (bvi_inc_clock (c + 1) s) = bvi_inc_clock c s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_dec_clock_def; bvi_inc_clock_def; bvi_state_component_equality;
              bvi_state_INFO.ri_accfupds; K_THM] THEN ARITH_TAC);;

let B2BP1AUX_dec_inc_clock_refs = prove
 (`!c f (s:(C,FFI)bvi_state).
     bvi_dec_clock (0 + 1) (bvi_state_refs_fupd f (bvi_inc_clock (c + 1) s)) =
     bvi_inc_clock c (bvi_state_refs_fupd f s) /\
     bvi_dec_clock 1 (bvi_state_refs_fupd f (bvi_inc_clock (c + 1) s)) =
     bvi_inc_clock c (bvi_state_refs_fupd f s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_dec_clock_def; bvi_inc_clock_def; bvi_state_component_equality;
              bvi_state_INFO.ri_accfupds; K_THM] THEN ARITH_TAC);;

let B2BP1AUX_SUC_SUB1 = prove
 (`!n. &(SUC n) - &1 = &n:int`,
  REWRITE_TAC[ADD1; GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC);;

let B2BP1AUX_STUB_RWS =
  [bvl_find_code_def; bvi_inc_clock_code; bvi_inc_clock_refs; bvi_inc_clock_clock;
   bvl_to_bvi_id; bvi_bvi_to_bvl_refs; nil_tag_def; cons_tag_def; tuple_tag_def;
   bvl_Boolv_11; bvl_do_int_app_def; small_enough_int_def;
   NUM_OF_INT_OF_NUM; INT_POS; INT_OF_NUM_LT; INT_OF_NUM_LE; INT_OF_NUM_EQ;
   IS_NONE_DEF; IS_SOME_DEF; ARITH_RULE `~(a + c + 1 < 1)`; B2BP1AUX_dec_inc_clock;
   INT_OF_NUM_ADD; bvl_to_bvi_with_refs; bvi_state_INFO.ri_accfupds; K_THM; bvl_do_eq_def;
   B2BP1AUX_dec_inc_clock_refs; B2BP1AUX_SUC_SUB1];;

(* list lemmas for CopyGlobals *)
let B2BP1AUX_copy_base = prove
 (`!(ls:A list) l1.
     0 < LENGTH ls /\ 0 < LENGTH l1
     ==> LUPDATE (EL 0 ls) 0 l1 = APPEND (TAKE 1 ls) (DROP 1 l1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ls:A list` list_CASES) THEN
  STRUCT_CASES_TAC (ISPEC `l1:A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; CONJUNCT1 LT; ONE; TAKE; DROP; EL; HD; RICHAUX_LUPDATE_CLAUSES;
              APPEND]);;

let B2BP1AUX_copy_step = prove
 (`!n (ls:A list) l1.
     n < LENGTH ls /\ n < LENGTH l1
     ==> APPEND (TAKE n ls) (DROP n (LUPDATE (EL n ls) n l1)) =
         APPEND (TAKE (SUC n) ls) (DROP (SUC n) l1)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ls:A list` list_CASES) THEN
  STRUCT_CASES_TAC (ISPEC `l1:A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; LT_0; CONJUNCT1 LT; LT_SUC; TAKE; DROP; EL; HD; TL;
              RICHAUX_LUPDATE_CLAUSES; APPEND] THEN
  ASM_SIMP_TAC[]);;

(* HOL4 line 734 [local] (p, ls, p1, b1 and b are free in HOL4) *)
let evaluate_CopyGlobals_code = prove
 (`!n l1 (s:(C,FFI)bvi_state) p ls p1 b1 b.
     lookup CopyGlobals_location (bvi_state_code s) = SOME (3,SND CopyGlobals_code) /\
     FLOOKUP (bvi_state_refs s) p = SOME (bvl_ValueArray ls) /\
     FLOOKUP (bvi_state_refs s) p1 = SOME (bvl_ValueArray l1) /\
     ~(p = p1) /\
     n < LENGTH ls /\ n < LENGTH l1
     ==> ?c. bvi_evaluate ([SND CopyGlobals_code],
                           [bvl_RefPtr b1 p1; bvl_RefPtr b p; bvl_Number (&n)],
                           bvi_inc_clock c s) =
             (Rval [bvl_Unit],
              bvi_state_refs_fupd
                (K (bvi_state_refs s |+
                    (p1,bvl_ValueArray (APPEND (TAKE (SUC n) ls) (DROP (SUC n) l1))))) s)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[inc_clock_ZERO; CopyGlobals_code_def; SND] THEN
    B2BP1AUX_BVI_EV_TAC B2BP1AUX_STUB_RWS THEN ASM_SIMP_TAC[B2BP1AUX_copy_base];
    FIRST_X_ASSUM(MP_TAC o SPECL [`LUPDATE (EL (SUC n) ls) (SUC n) (l1:bvl_v list)`;
      `bvi_state_refs_fupd (K (bvi_state_refs s |+ (p1,bvl_ValueArray
         (LUPDATE (EL (SUC n) ls) (SUC n) l1)))) (s:(C,FFI)bvi_state)`;
      `p:num`; `ls:bvl_v list`; `p1:num`; `b1:bool`; `b:bool`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE; LENGTH_LUPDATE] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `SUC n < LENGTH (ls:bvl_v list)` THEN
      UNDISCH_TAC `SUC n < LENGTH (l1:bvl_v list)` THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `c:num`) THEN EXISTS_TAC `c + 1` THEN
    REWRITE_TAC[CopyGlobals_code_def; SND] THEN
    B2BP1AUX_BVI_EV_TAC B2BP1AUX_STUB_RWS THEN
    REWRITE_TAC[FUPDATE_EQ; bvi_state_INFO.ri_fupdfupds; K_o_THM] THEN
    ASM_SIMP_TAC[B2BP1AUX_copy_step]]);;

(* HOL4 line 782: val evaluate_CopyGlobals_code = Q.GEN ls                  *)
(* evaluate_CopyGlobals_code (rebinds it with ls quantified first) *)
let evaluate_CopyGlobals_code = prove
 (`!ls n l1 (s:(C,FFI)bvi_state) p p1 b1 b.
     lookup CopyGlobals_location (bvi_state_code s) = SOME (3,SND CopyGlobals_code) /\
     FLOOKUP (bvi_state_refs s) p = SOME (bvl_ValueArray ls) /\
     FLOOKUP (bvi_state_refs s) p1 = SOME (bvl_ValueArray l1) /\
     ~(p = p1) /\
     n < LENGTH ls /\ n < LENGTH l1
     ==> ?c. bvi_evaluate ([SND CopyGlobals_code],
                           [bvl_RefPtr b1 p1; bvl_RefPtr b p; bvl_Number (&n)],
                           bvi_inc_clock c s) =
             (Rval [bvl_Unit],
              bvi_state_refs_fupd
                (K (bvi_state_refs s |+
                    (p1,bvl_ValueArray (APPEND (TAKE (SUC n) ls) (DROP (SUC n) l1))))) s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `l1:bvl_v list`; `s:(C,FFI)bvi_state`; `p:num`; `ls:bvl_v list`;
                `p1:num`; `b1:bool`; `b:bool`] evaluate_CopyGlobals_code) THEN
  REWRITE_TAC[]);;

(* HOL4 line 783: print (no statement) *)

(* a local helper for evaluate_AllocGlobal_code (not in HOL4): the clock  *)
(* of the call to CopyGlobals                                              *)
let B2BP1AUX_dec_inc_clock_gr = prove
 (`!c g f1 f2 (s:(C,FFI)bvi_state).
     bvi_dec_clock 1 (bvi_state_global_fupd g (bvi_state_refs_fupd f2
       (bvi_state_refs_fupd f1 (bvi_inc_clock (c + 1) s)))) =
     bvi_inc_clock c (bvi_state_global_fupd g (bvi_state_refs_fupd (f2 o f1) s))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvi_dec_clock_def; bvi_inc_clock_def; bvi_state_component_equality;
              bvi_state_INFO.ri_accfupds; K_THM; o_THM] THEN ARITH_TAC);;

(* HOL4 line 785 [local] (HOL4 s with <| global := g; refs := r |> is       *)
(* bvi_state_global_fupd (K g) (bvi_state_refs_fupd (K r) s)) *)
let evaluate_AllocGlobal_code = prove
 (`!(s:(C,FFI)bvi_state) p n ls k.
     FLOOKUP (bvi_state_refs s) p =
       SOME (bvl_ValueArray (CONS (bvl_Number (&(SUC n))) ls)) /\
     n <= LENGTH ls /\
     bvi_state_global s = SOME p /\
     lookup CopyGlobals_location (bvi_state_code s) = SOME (3,SND CopyGlobals_code)
     ==> ?p1 c extra.
           (~(p1 = p) ==> ~(p1 IN FDOM (bvi_state_refs s))) /\
           n + k + 1 <= LENGTH ls + extra /\
           bvi_evaluate ([SND AllocGlobal_code],[bvl_Number (&k)],bvi_inc_clock c s) =
             (Rval [bvl_Unit],
              bvi_state_global_fupd (K (SOME p1))
                (bvi_state_refs_fupd
                   (K (bvi_state_refs s |+
                       (p,bvl_ValueArray (CONS (bvl_Number (&(SUC (n + k)))) ls)) |+
                       (p1,bvl_ValueArray
                             (APPEND (CONS (bvl_Number (&(SUC (n + k)))) ls)
                                (REPLICATE extra (bvl_Number (&0))))))) s))`,
  (REPEAT GEN_TAC THEN STRIP_TAC) THEN
  (ASM_CASES_TAC `k + SUC n < SUC (LENGTH (ls:bvl_v list))`) THENL
  [(MAP_EVERY EXISTS_TAC [`p:num`; `0`; `0`] THEN REWRITE_TAC[inc_clock_ZERO; AllocGlobal_code_def; SND]) THEN
   B2BP1AUX_BVI_EV_TAC (B2BP1AUX_STUB_RWS @ [inc_clock_global; LT_0; LT_SUC; LET_DEF;
     LET_END_DEF; RICHAUX_LUPDATE_CLAUSES]) THEN
   (CONJ_TAC THENL [UNDISCH_TAC `k + SUC n < SUC (LENGTH (ls:bvl_v list))` THEN ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[bvi_state_component_equality; bvi_state_INFO.ri_accfupds; K_THM; FUPDATE_EQ;
     RICHAUX_LUPDATE_CLAUSES; REPLICATE; APPEND_NIL; ARITH_RULE `k + SUC n = SUC (n + k)`] THEN
   ASM_REWRITE_TAC[]);
   (REWRITE_TAC[ARITH_RULE `SUC (n + k) = k + SUC n`] THEN
   ABBREV_TAC `newp = minimal ptr. ~(ptr IN FDOM (bvi_state_refs (s:(C,FFI)bvi_state) |+
        (p,bvl_ValueArray (CONS (bvl_Number (&(k + SUC n))) ls))))` THEN
   SUBGOAL_THEN `~(newp = p) /\ ~(newp IN FDOM (bvi_state_refs (s:(C,FFI)bvi_state)))`
     STRIP_ASSUME_TAC THENL
    [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
     MP_TAC(ISPEC `bvi_state_refs (s:(C,FFI)bvi_state) |+
        (p,bvl_ValueArray (CONS (bvl_Number (&(k + SUC n))) ls))` LEAST_NOTIN_FDOM) THEN
     REWRITE_TAC[FDOM_FUPDATE; IN_INSERT; DE_MORGAN_THM];
     ALL_TAC] THEN
   ABBREV_TAC `s2 = bvi_state_global_fupd (K (SOME newp)) (bvi_state_refs_fupd
     (K (bvi_state_refs s |+ (p,bvl_ValueArray (CONS (bvl_Number (&(k + SUC n))) ls)) |+
         (newp, bvl_ValueArray (REPLICATE ((k + SUC n) + k + SUC n) (bvl_Number (&0))))))
     (s:(C,FFI)bvi_state))` THEN
   MP_TAC(SPECL [`CONS (bvl_Number (&(k + SUC n))) ls`; `LENGTH (ls:bvl_v list)`;
     `REPLICATE ((k + SUC n) + k + SUC n) (bvl_Number (&0))`; `s2:(C,FFI)bvi_state`; `p:num`;
     `newp:num`; `T`; `T`] evaluate_CopyGlobals_code) THEN
   ANTS_TAC THENL
    [EXPAND_TAC "s2" THEN
     REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE; LENGTH_REPLICATE;
                 LENGTH] THEN
     ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(k + SUC n < SUC (LENGTH (ls:bvl_v list)))` THEN
     ARITH_TAC;
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_TAC `c:num`) THEN
   MAP_EVERY EXISTS_TAC [`newp:num`; `c + 1`;
     `((k + SUC n) + k + SUC n) - SUC (LENGTH (ls:bvl_v list))`] THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[AllocGlobal_code_def; SND]) THEN
   B2BP1AUX_BVI_EV_TAC (B2BP1AUX_STUB_RWS @ [inc_clock_global; LT_0; LT_SUC; LET_DEF;
     LET_END_DEF; RICHAUX_LUPDATE_CLAUSES]) THEN
   (REWRITE_TAC[B2BP1AUX_dec_inc_clock_gr; K_o_THM] THEN ASM_REWRITE_TAC[] THEN
   CASE_REWRITE_TAC[] THEN
   CONJ_TAC THENL [UNDISCH_TAC `~(k + SUC n < SUC (LENGTH (ls:bvl_v list)))` THEN ARITH_TAC;
                   ALL_TAC] THEN
   EXPAND_TAC "s2" THEN
   REWRITE_TAC[PAIR_EQ; bvi_state_component_equality; bvi_state_INFO.ri_accfupds; K_THM;
               FUPDATE_EQ; DROP_REPLICATE] THEN
   REWRITE_TAC[TAKE; TAKE_LENGTH_ID; APPEND])]);;

(* HOL4 line 865 (HOL4's unused binder p1 of the conclusion is left out) *)
let evaluate_ListLength_code = prove
 (`!lv vs n (s:(C,FFI)bvi_state).
     lookup ListLength_location (bvi_state_code s) = SOME (2,SND ListLength_code) /\
     bvl_v_to_list lv = SOME vs
     ==> ?c. bvi_evaluate ([SND ListLength_code],[lv; bvl_Number (&n)],bvi_inc_clock c s) =
             (Rval [bvl_Number (&(n + LENGTH vs))],s)`,
  MATCH_MP_TAC bvl_v_to_list_ind THEN REWRITE_TAC[bvl_v_to_list_def; option_DISTINCT] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[inc_clock_ZERO; ListLength_code_def; SND] THEN
    B2BP1AUX_BVI_EV_TAC B2BP1AUX_STUB_RWS THEN REWRITE_TAC[ADD_CLAUSES];
    DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `tag = cons_tag`)) THEN DISCH_TAC THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:bvl_v list`; `1 + n`; `s:(C,FFI)bvi_state`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `c:num`) THEN EXISTS_TAC `c + 1` THEN
    REWRITE_TAC[ListLength_code_def; SND] THEN
    B2BP1AUX_BVI_EV_TAC B2BP1AUX_STUB_RWS THEN
    REWRITE_TAC[PAIR_EQ; injectivity "result"; CONS_11; injectivity "bvl_v"; INT_OF_NUM_EQ;
                LENGTH] THEN
    ARITH_TAC]);;

let B2BP1AUX_TAKE_LUPDATE = prove
 (`!m (bs:A list) x. m < LENGTH bs ==> TAKE (1 + m) (LUPDATE x m bs) = APPEND (TAKE m bs) [x]`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `bs:A list` list_CASES) THEN
  REWRITE_TAC[LENGTH; CONJUNCT1 LT; LT_SUC; ADD_CLAUSES; ONE; TAKE; RICHAUX_LUPDATE_CLAUSES;
              APPEND] THEN
  ASM_SIMP_TAC[GSYM ONE; ARITH_RULE `SUC m = 1 + m`]);;

(* local helpers for the stubs over lists (not in HOL4) *)
let B2BP1AUX_NIL_EQ_MAP = prove
 (`!(f:A->B) l. [] = MAP f l <=> l = []`,
  REPEAT GEN_TAC THEN CONV_TAC (LAND_CONV SYM_CONV) THEN REWRITE_TAC[MAP_EQ_NIL]);;

let B2BP1AUX_CONS_EQ_MAP = prove
 (`!(f:A->B) l h t. CONS h t = MAP f l <=> ?x0 t0. l = CONS x0 t0 /\ h = f x0 /\ t = MAP f t0`,
  REPEAT GEN_TAC THEN CONV_TAC (LAND_CONV SYM_CONV) THEN REWRITE_TAC[MAP_EQ_CONS] THEN
  MESON_TAC[]);;

(* HOL4 line 896 (HOL4 n2w is word) *)
let evaluate_FromListByte_code = prove
 (`!lv vs n bs (s:(C,FFI)bvi_state) p fl b.
     bvl_v_to_list lv = SOME (MAP (bvl_Number o int_of_num) vs) /\ LENGTH vs <= LENGTH bs /\
     lookup FromListByte_location (bvi_state_code s) = SOME (3,SND FromListByte_code) /\
     ALL (\n. n < 256) vs /\
     FLOOKUP (bvi_state_refs s) p = SOME (bvl_ByteArray fl bs) /\
     n = LENGTH bs - LENGTH vs
     ==> ?c. bvi_evaluate ([SND FromListByte_code],[lv; bvl_Number (&n); bvl_RefPtr b p],
                           bvi_inc_clock c s) =
             (Rval [bvl_RefPtr b p],
              bvi_state_refs_fupd
                (K (bvi_state_refs s |+
                    (p,bvl_ByteArray fl (APPEND (TAKE n bs) (MAP word vs))))) s)`,
  (MATCH_MP_TAC bvl_v_to_list_ind THEN REWRITE_TAC[bvl_v_to_list_def; option_DISTINCT] THEN
   REPEAT CONJ_TAC THEN REPEAT GEN_TAC) THENL
  [(COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
   REWRITE_TAC[B2BP1AUX_NIL_EQ_MAP] THEN
   REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   EXISTS_TAC `0` THEN
   REWRITE_TAC[inc_clock_ZERO; FromListByte_code_def; SND] THEN
   B2BP1AUX_BVI_EV_TAC B2BP1AUX_STUB_RWS THEN
   ASM_SIMP_TAC[MAP; APPEND_NIL; LENGTH; SUB_0; TAKE_LENGTH_ID; FMAPAUX_FUPDATE_FLOOKUP_ELIM] THEN
   REWRITE_TAC[bvi_state_component_equality; bvi_state_INFO.ri_accfupds; K_THM]);
   (DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
   REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `tag = cons_tag`)) THEN DISCH_TAC THEN
   REPEAT (POP_ASSUM MP_TAC) THEN
   TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; B2BP1AUX_CONS_EQ_MAP; o_THM] THEN
   REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ALL; LENGTH])) THEN
   (REWRITE_TAC[LENGTH; MAP] THEN
   ABBREV_TAC `m = LENGTH (bs:byte list) - SUC (LENGTH (t0:num list))` THEN
   SUBGOAL_THEN `m < LENGTH (bs:byte list)` ASSUME_TAC THENL
    [EXPAND_TAC "m" THEN UNDISCH_TAC `SUC (LENGTH (t0:num list)) <= LENGTH (bs:byte list)` THEN
     ARITH_TAC;
     ALL_TAC] THEN
   SUBGOAL_THEN `?w:byte. &x0 = &(val w):int` ASSUME_TAC THENL
    [EXISTS_TAC `word x0:byte` THEN REWRITE_TAC[INT_OF_NUM_EQ; VAL_WORD; DIMINDEX_8] THEN
     CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT];
     ALL_TAC]) THEN
   (FIRST_X_ASSUM(MP_TAC o SPECL [`t0:num list`; `1 + m`; `LUPDATE (word x0:byte) m bs`;
     `bvi_state_refs_fupd (K (bvi_state_refs s |+ (p,bvl_ByteArray fl
        (LUPDATE (word x0:byte) m bs)))) (s:(C,FFI)bvi_state)`; `p:num`; `fl:bool`; `b:bool`] o
     check (is_forall o concl)) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE; LENGTH_LUPDATE] THEN
     B2BP1AUX_ARITH_TAC;
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_TAC `c:num`) THEN EXISTS_TAC `c + 1` THEN
   REWRITE_TAC[FromListByte_code_def; SND]) THEN
   (B2BP1AUX_BVI_EV_TAC (i2w_pos :: B2BP1AUX_STUB_RWS)) THEN
   (REWRITE_TAC[FUPDATE_EQ; bvi_state_INFO.ri_fupdfupds; K_o_THM] THEN
   ASM_SIMP_TAC[B2BP1AUX_TAKE_LUPDATE; GSYM APPEND_ASSOC; APPEND])]);;

let B2BP1AUX_EL_SNOC_APPEND = prove
 (`!(bs:A list) x rest. EL (LENGTH bs) (APPEND (SNOC x bs) rest) = x`,
  REWRITE_TAC[SNOC_APPEND; GSYM APPEND_ASSOC; APPEND] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH; APPEND; EL; HD; TL]);;

(* HOL4 line 943 (the bound byte b of HOL4's lambdas is x here: b is also  *)
(* the free boolean of RefPtr b p) *)
let evaluate_ToListByte_code = prove
 (`!bs rest p (s:(C,FFI)bvi_state) fl b.
     lookup ToListByte_location (bvi_state_code s) = SOME (3,SND ToListByte_code) /\
     FLOOKUP (bvi_state_refs s) p = SOME (bvl_ByteArray fl (APPEND bs rest))
     ==> ?c. bvi_evaluate ([SND ToListByte_code],
                           [bvl_list_to_v (MAP (\x. bvl_Number (&(val x))) rest);
                            bvl_Number (&(LENGTH bs)); bvl_RefPtr b p],
                           bvi_inc_clock c s) =
             (Rval [bvl_list_to_v (APPEND (MAP (\x. bvl_Number (&(val x))) bs)
                                     (MAP (\x. bvl_Number (&(val x))) rest))],
              bvi_state_refs_fupd
                (K (bvi_state_refs s |+ (p,bvl_ByteArray fl (APPEND bs rest)))) s)`,
  MATCH_MP_TAC SNOC_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[inc_clock_ZERO; ToListByte_code_def; SND] THEN
    B2BP1AUX_BVI_EV_TAC B2BP1AUX_STUB_RWS THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND]) THEN
    ASM_SIMP_TAC[MAP; APPEND; FMAPAUX_FUPDATE_FLOOKUP_ELIM] THEN
    REWRITE_TAC[bvi_state_component_equality; bvi_state_INFO.ri_accfupds; K_THM];
    (GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (x:byte) rest`; `p:num`; `s:(C,FFI)bvi_state`;
     `fl:bool`; `b:bool`]) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SNOC_APPEND; GSYM APPEND_ASSOC; APPEND];
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_TAC `c:num`) THEN EXISTS_TAC `c + 1` THEN
   SUBGOAL_THEN `LENGTH (bs:byte list) < LENGTH (APPEND (SNOC x bs) rest)` ASSUME_TAC THENL
    [REWRITE_TAC[LENGTH_APPEND; LENGTH_SNOC] THEN ARITH_TAC; ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[MAP; bvl_list_to_v_def; cons_tag_def]) THEN
   REWRITE_TAC[ToListByte_code_def; SND; LENGTH_SNOC]) THEN
    (B2BP1AUX_BVI_EV_TAC (B2BP1AUX_EL_SNOC_APPEND :: ARITH_RULE `~(0 = SUC n)` ::
                        B2BP1AUX_STUB_RWS)) THEN
    (REWRITE_TAC[SNOC_APPEND; MAP_APPEND; MAP; GSYM APPEND_ASSOC; APPEND])]);;


(* HOL4 line 990 *)
let evaluate_SumListLength_code = prove
 (`!lv ps wss n (s:(C,FFI)bvi_state).
     lookup SumListLength_location (bvi_state_code s) = SOME (2,SND SumListLength_code) /\
     bvl_v_to_list lv = SOME (MAP (bvl_RefPtr T) ps) /\
     MAP (FLOOKUP (bvi_state_refs s)) ps = MAP (SOME o bvl_ByteArray T) wss
     ==> ?c. bvi_evaluate ([SND SumListLength_code],[lv; bvl_Number (&n)],
                           bvi_inc_clock c s) =
             (Rval [bvl_Number (&(n + LENGTH (FLAT wss)))],s)`,
  MATCH_MP_TAC bvl_v_to_list_ind THEN REWRITE_TAC[bvl_v_to_list_def; option_DISTINCT] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    REWRITE_TAC[B2BP1AUX_NIL_EQ_MAP] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAP; B2BP1AUX_NIL_EQ_MAP]) THEN RVEQ_TAC THEN
    EXISTS_TAC `0` THEN
    REWRITE_TAC[inc_clock_ZERO; SumListLength_code_def; SND] THEN
    B2BP1AUX_BVI_EV_TAC B2BP1AUX_STUB_RWS THEN REWRITE_TAC[FLAT; LENGTH; ADD_CLAUSES];
    DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `tag = cons_tag`)) THEN DISCH_TAC THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    REWRITE_TAC[GSYM MAP_EQ_CONS] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    REWRITE_TAC[MAP_EQ_CONS] THEN STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[MAP] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[MAP_EQ_CONS] THEN
    STRIP_TAC THEN RVEQ_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[EQ_SYM_EQ] o
      check (fun th -> is_eq (concl th) && is_cons (lhs (concl th)))) THEN
    REWRITE_TAC[MAP_EQ_CONS; o_THM] THEN STRIP_TAC THEN RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t0:num list`; `t0':(byte list)list`;
      `LENGTH (x0':byte list) + n`; `s:(C,FFI)bvi_state`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `c:num`) THEN EXISTS_TAC `c + 1` THEN
    REWRITE_TAC[SumListLength_code_def; SND] THEN
    B2BP1AUX_BVI_EV_TAC B2BP1AUX_STUB_RWS THEN
    REWRITE_TAC[FLAT; LENGTH_APPEND] THEN ARITH_TAC]);;

(* local helpers for evaluate_ConcatByte_code (not in HOL4) *)
let B2BP1AUX_copy_array_concat = prove
 (`!(w0:A list) ds1 ds2.
     LENGTH w0 <= LENGTH ds2
     ==> copy_array (w0,&0) (&(LENGTH w0)) (SOME (APPEND ds1 ds2,&(LENGTH ds1))) =
         SOME (APPEND (APPEND ds1 w0) (DROP (LENGTH w0) ds2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[copy_array_def; LET_DEF; LET_END_DEF] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[I_THM; INT_ADD_LID; INT_OF_NUM_ADD; INT_ABS_NUM; NUM_OF_INT_OF_NUM;
              INT_LT_REFL; INT_OF_NUM_LT; LT_REFL; LENGTH_APPEND; DROP_0;
              TAKE_LENGTH_ID; CONJUNCT1 LT; ARITH_RULE `a + b < a + c <=> b < c`] THEN
  ASM_REWRITE_TAC[GSYM NOT_LE] THEN
  SIMP_TAC[TAKE_LENGTH_APPEND; DROP_APPEND2; LE_ADD; ADD_SUB2]);;


let B2BP1AUX_MAP_FLOOKUP_UPDATE = prove
 (`!(f:(A,B)fmap) k v l. ~MEM k l ==> MAP (FLOOKUP (f |+ (k,v))) l = MAP (FLOOKUP f) l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MAP_EQ_f; FLOOKUP_UPDATE] THEN ASM_MESON_TAC[]);;


(* HOL4 line 1030 *)
let evaluate_ConcatByte_code = prove
 (`!lv ps wss (s:(C,FFI)bvi_state) ds1 ds2 n dst b.
     lookup SumListLength_location (bvi_state_code s) = SOME (2,SND SumListLength_code) /\
     lookup ConcatByte_location (bvi_state_code s) = SOME (3,SND ConcatByte_code) /\
     bvl_v_to_list lv = SOME (MAP (bvl_RefPtr T) ps) /\ ~(dst IN set_of_list ps) /\
     MAP (FLOOKUP (bvi_state_refs s)) ps = MAP (SOME o bvl_ByteArray T) wss /\
     FLOOKUP (bvi_state_refs s) dst = SOME (bvl_ByteArray T (APPEND ds1 ds2)) /\
     n = LENGTH ds1 /\ LENGTH (FLAT wss) = LENGTH ds2
     ==> ?c. bvi_evaluate ([SND ConcatByte_code],[lv; bvl_Number (&n); bvl_RefPtr b dst],
                           bvi_inc_clock c s) =
             (Rval [bvl_RefPtr b dst],
              bvi_state_refs_fupd
                (K (bvi_state_refs s |+ (dst,bvl_ByteArray T (APPEND ds1 (FLAT wss))))) s)`,
  (MATCH_MP_TAC bvl_v_to_list_ind THEN REWRITE_TAC[bvl_v_to_list_def; option_DISTINCT] THEN
   REPEAT CONJ_TAC THEN REPEAT GEN_TAC) THENL
  [(COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
   REWRITE_TAC[B2BP1AUX_NIL_EQ_MAP] THEN
   REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[MAP; B2BP1AUX_NIL_EQ_MAP; FLAT; LENGTH; LENGTH_EQ_NIL]) THEN
   RVEQ_TAC THEN EXISTS_TAC `0` THEN
   REWRITE_TAC[inc_clock_ZERO; ConcatByte_code_def; SND] THEN
   B2BP1AUX_BVI_EV_TAC B2BP1AUX_STUB_RWS) THEN
   (SUBGOAL_THEN `ds2:byte list = []` SUBST_ALL_TAC THENL
    [UNDISCH_TAC `LENGTH (FLAT ([]:(byte list)list)) = LENGTH (ds2:byte list)` THEN
     REWRITE_TAC[FLAT; LENGTH] THEN DISCH_THEN(MP_TAC o SYM) THEN
     REWRITE_TAC[LENGTH_EQ_NIL];
     ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL]) THEN
   ASM_SIMP_TAC[FLAT; APPEND_NIL; FMAPAUX_FUPDATE_FLOOKUP_ELIM] THEN
   REWRITE_TAC[bvi_state_component_equality; bvi_state_INFO.ri_accfupds; K_THM]);
   (DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
   REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `tag = cons_tag`)) THEN DISCH_TAC THEN
   REPEAT (POP_ASSUM MP_TAC) THEN
   TOP_CASE_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; B2BP1AUX_CONS_EQ_MAP] THEN
   REPEAT STRIP_TAC THEN RVEQ_TAC THEN
   FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[MAP; B2BP1AUX_CONS_EQ_MAP; o_THM] o
     check (fun th -> is_eq (concl th) &&
       (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "MAP" with Failure _ -> false) &&
       is_cons (rand (lhs (concl th))))) THEN
   STRIP_TAC THEN RVEQ_TAC) THEN
   (RULE_ASSUM_TAC(REWRITE_RULE[FLAT; LENGTH_APPEND; MEM; set_of_list; IN_INSERT;
     DE_MORGAN_THM]) THEN
   SUBGOAL_THEN `LENGTH (x0':byte list) <= LENGTH (ds2:byte list)` ASSUME_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
       can (find_term ((=) `LENGTH (ds2:byte list)`)) (concl th))) THEN ARITH_TAC;
     ALL_TAC] THEN
   FIRST_ASSUM(ASSUME_TAC o SPEC `ds1:byte list` o MATCH_MP B2BP1AUX_copy_array_concat)) THEN
   (FIRST_X_ASSUM(MP_TAC o SPECL [`t0:num list`; `t0':(byte list)list`;
     `bvi_state_refs_fupd (K (bvi_state_refs s |+ (dst,bvl_ByteArray T
        (APPEND (APPEND ds1 x0') (DROP (LENGTH (x0':byte list)) (ds2:byte list)))))) (s:(C,FFI)bvi_state)`;
     `APPEND ds1 (x0':byte list)`; `DROP (LENGTH (x0':byte list)) (ds2:byte list)`;
     `LENGTH (x0':byte list) + LENGTH (ds1:byte list)`; `dst:num`; `b:bool`] o
     check (is_forall o concl)) THEN
   ANTS_TAC) THENL
   [(REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE; LENGTH_APPEND;
               LENGTH_DROP] THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `~MEM (dst:num) t0` ASSUME_TAC THENL
    [ASM_MESON_TAC[IN_SET_OF_LIST]; ALL_TAC] THEN
   ASM_SIMP_TAC[B2BP1AUX_MAP_FLOOKUP_UPDATE] THEN B2BP1AUX_ARITH_TAC);
    (DISCH_THEN(X_CHOOSE_TAC `c:num`) THEN EXISTS_TAC `c + 1` THEN
   REWRITE_TAC[ConcatByte_code_def; SND]) THEN
    (B2BP1AUX_BVI_EV_TAC B2BP1AUX_STUB_RWS) THEN
    (REWRITE_TAC[FUPDATE_EQ; bvi_state_INFO.ri_fupdfupds; K_o_THM; FLAT; APPEND_ASSOC])]]);;

(* HOL4 lines 1086-1087: val bEval_def = bvlSemTheory.evaluate_def,          *)
(* iEval_append = bviPropsTheory.evaluate_APPEND (abbreviations)             *)

(* HOL4 line 1089 [local] *)
let compile_exps_Var_list = prove
 (`!l n.
     ALL isVar l
     ==> ?aux. bvl_to_bvi_compile_exps n l = (MAP (bvi_Var o destVar) l,aux,n) /\
               append aux = []`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[bvl_to_bvi_compile_exps_def; MAP] THEN MESON_TAC[append_thm];
    ALL_TAC] THEN
  CASES_ON `h:bvl_exp` THEN REWRITE_TAC[ALL; isVar_def] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `aux0:(num#num#bvi_exp)app_list`
    STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `bvl_to_bvi_compile_exps n t = MAP (bvi_Var o destVar) t,aux0,n` THEN
  SPEC_TAC(`t:bvl_exp list`,`t:bvl_exp list`) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[bvl_to_bvi_compile_exps_def; MAP; o_THM; destVar_def] THEN
  CASE_REWRITE_TAC[] THENL
   [DISCH_TAC THEN EXISTS_TAC `Nil:(num#num#bvi_exp)app_list` THEN REWRITE_TAC[append_thm];
    DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
    EXISTS_TAC `SmartAppend Nil (aux0:(num#num#bvi_exp)app_list)` THEN
    ASM_REWRITE_TAC[append_SmartAppend; append_thm; APPEND]]);;

(* HOL4 line 1098 [local] *)
let compile_int_thm = prove
 (`!i env (s:(C,FFI)bvi_state).
     bvi_evaluate ([compile_int i],env,s) = (Rval [bvl_Number i],s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[compile_int_def] THEN COND_CASES_TAC THEN
  B2BP1AUX_BVI_EV_TAC [small_enough_int_def; bvl_do_build_const_def; bvl_do_build_def;
    bvl_do_part_def; bvl_do_int_app_def; APPLY_UPDATE_THM; bvl_to_bvi_with_refs;
    bvl_to_bvi_id; bvi_bvi_to_bvl_refs] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[bvi_state_component_equality; bvi_state_INFO.ri_accfupds; K_THM]);;

(* compile_string_thm with an offset k (HOL4 proves it with a list vs of *)
(* length k and specialises vs to [])                                   *)
let B2BP1AUX_compile_string = prove
 (`!(str:char list) k ls ptr (s:(C,FFI)bvi_state) env b.
     FLOOKUP (bvi_state_refs s) ptr = SOME (bvl_ByteArray T ls) /\ k + LENGTH str = LENGTH ls
     ==> bvi_evaluate
           (MAPi (\n c. bvi_Op (MemOp UpdateByte)
                          [bvi_Op (IntOp (clos_Const (&(ORD c)))) []; compile_int (&(n + k));
                           bvi_Var 0]) str,
            CONS (bvl_RefPtr b ptr) env,s) =
         (Rval (REPLICATE (LENGTH str) bvl_Unit),
          bvi_state_refs_fupd
            (K (bvi_state_refs s |+
                (ptr,bvl_ByteArray T (APPEND (TAKE k ls) (MAP (word o ORD) str))))) s)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAPi_DEF; bvi_evaluate_def; LENGTH; REPLICATE; MAP; APPEND_NIL; ADD_CLAUSES] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    ASM_SIMP_TAC[TAKE_LENGTH_ID; FMAPAUX_FUPDATE_FLOOKUP_ELIM; PAIR_EQ] THEN
    REWRITE_TAC[bvi_state_component_equality; bvi_state_INFO.ri_accfupds; K_THM];
    (REPEAT GEN_TAC THEN STRIP_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]) THEN
   SUBGOAL_THEN `k < LENGTH (ls:byte list)` ASSUME_TAC THENL
    [UNDISCH_TAC `k + SUC (LENGTH (t:char list)) = LENGTH (ls:byte list)` THEN ARITH_TAC;
     ALL_TAC] THEN
   SUBGOAL_THEN `?w:byte. &(ORD h) = &(val w):int` ASSUME_TAC THENL
    [EXISTS_TAC `word (ORD h):byte` THEN REWRITE_TAC[INT_OF_NUM_EQ; VAL_WORD; DIMINDEX_8] THEN
     CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT; ORD_BOUND];
     ALL_TAC] THEN
   SUBGOAL_THEN `ORD h <= 268435457` ASSUME_TAC THENL
    [MP_TAC(SPEC `h:char` ORD_BOUND) THEN ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[MAPi_DEF] THEN ONCE_REWRITE_TAC[bvi_evaluate_CONS] THEN
   SUBGOAL_THEN
    `((\n c. bvi_Op (MemOp UpdateByte)
             [bvi_Op (IntOp (clos_Const (&(ORD c)))) []; compile_int (&(n + k));
              bvi_Var 0]) o SUC) =
     (\n c. bvi_Op (MemOp UpdateByte)
             [bvi_Op (IntOp (clos_Const (&(ORD c)))) []; compile_int (&(n + (k + 1)));
              bvi_Var 0])` SUBST1_TAC THENL
    [REWRITE_TAC[FUN_EQ_THM; o_THM; ARITH_RULE `SUC n + k = n + k + 1`]; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`k + 1`; `LUPDATE (word (ORD h):byte) k ls`; `ptr:num`;
     `bvi_state_refs_fupd (K (bvi_state_refs s |+ (ptr,bvl_ByteArray T
        (LUPDATE (word (ORD h):byte) k ls)))) (s:(C,FFI)bvi_state)`; `env:bvl_v list`; `b:bool`]) THEN
   ANTS_TAC THENL
    [REWRITE_TAC[bvi_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE; LENGTH_LUPDATE] THEN
     UNDISCH_TAC `k + SUC (LENGTH (t:char list)) = LENGTH (ls:byte list)` THEN ARITH_TAC;
     DISCH_TAC]) THEN
    (B2BP1AUX_BVI_EV_TAC (compile_int_thm :: i2w_pos :: LT_0 :: LT_SUC :: ADD_CLAUSES :: B2BP1AUX_STUB_RWS)) THEN
    (REWRITE_TAC[REPLICATE; FUPDATE_EQ; bvi_state_INFO.ri_fupdfupds; K_o_THM] THEN
   ONCE_REWRITE_TAC[ADD_SYM] THEN
   ASM_SIMP_TAC[B2BP1AUX_TAKE_LUPDATE; GSYM APPEND_ASSOC; APPEND; MAP; o_THM])]);;

(* HOL4 line 1105: val compile_string_thm = Q.prove (...) |> Q.SPECL [str, *)
(* s, ls, []] |> SIMP_RULE (srw_ss()) [] |> Q.GENL [str, ls, ptr, s, env]   *)
(* |> INST_TYPE (its resulting statement; b stays free in HOL4) *)
let compile_string_thm = prove
 (`!(str:char list) ls ptr (s:(C,FFI)bvi_state) env b.
     FLOOKUP (bvi_state_refs s) ptr = SOME (bvl_ByteArray T ls) /\
     LENGTH str = LENGTH ls
     ==> bvi_evaluate
           (MAPi (\n c. bvi_Op (MemOp UpdateByte)
                          [bvi_Op (IntOp (clos_Const (&(ORD c)))) []; compile_int (&n);
                           bvi_Var 0]) str,
            CONS (bvl_RefPtr b ptr) env,s) =
         (Rval (REPLICATE (LENGTH str) bvl_Unit),
          bvi_state_refs_fupd
            (K (bvi_state_refs s |+ (ptr,bvl_ByteArray T (MAP (word o ORD) str)))) s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`str:char list`; `0`; `ls:byte list`; `ptr:num`; `s:(C,FFI)bvi_state`;
                `env:bvl_v list`; `b:bool`] B2BP1AUX_compile_string) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; TAKE; APPEND]);;

(* HOL4 line 1138 *)
let HD_APPEND3 = prove
 (`!l1 l2 (l3:A list).
     0 < LENGTH (APPEND l1 l2) ==> HD (APPEND (APPEND l1 l2) l3) = HD (APPEND l1 l2)`,
  REPEAT GEN_TAC THEN SPEC_TAC(`APPEND (l1:A list) l2`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; LT_REFL; APPEND; HD]);;

(* local helpers for iEval_bVarBound (not in HOL4): induction case        *)
(* stripping, pair splits of compile_exps, the induction hypotheses for    *)
(* the compiled code, and the fact that the code of compile_op depends on  *)
(* the environment only through its arguments                              *)
(* strip a case of an induction theorem: the induction hypotheses become  *)
(* assumptions, then the hypothesis of the case (the last assumption)        *)
let B2BP1AUX_IND_STRIP_TAC : tactic =
  REPEAT GEN_TAC THEN
  (fun (asl,w as g) -> if is_imp w && is_forall(rand w)
                       then DISCH_THEN STRIP_ASSUME_TAC g else ALL_TAC g) THEN
  REPEAT GEN_TAC THEN DISCH_TAC;;

(* split the first value of the function named fname that a pair case of   *)
(* the goal inspects into a tuple of fresh variables (nested pairs too):    *)
(* the equation becomes an assumption, only the goal is rewritten          *)
let B2BP1AUX_PAIR_SPLIT_TAC (fname:string) : tactic = fun (asl,w as gl) ->
  let fw = frees w in
  let is_f_case t =
    try let c,args = strip_comb t in
        fst(dest_const c) = "pair_CASE" &&
        fst(dest_const(fst(strip_comb (hd args)))) = fname &&
        subset (frees (hd args)) fw
    with Failure _ -> false in
  let t = find_term is_f_case w in
  let e = hd(snd(strip_comb t)) in
  let avoid = itlist (union o frees o concl o snd) asl (frees w) in
  let rec vars avoid ty =
    match dest_type ty with
      ("prod",[a;b]) -> let v1 = variant avoid (mk_var("v",a)) in v1 :: vars (v1::avoid) b
    | _ -> [variant avoid (mk_var("v",ty))] in
  let rec comps e =
    match dest_type (type_of e) with
      ("prod",[_;_]) -> mk_comb(mk_const("FST",[fst(dest_prod_ty (type_of e)),`:A`;
                                                snd(dest_prod_ty (type_of e)),`:B`]),e) ::
                        comps (mk_comb(mk_const("SND",[fst(dest_prod_ty (type_of e)),`:A`;
                                                snd(dest_prod_ty (type_of e)),`:B`]),e))
    | _ -> [e]
  and dest_prod_ty ty = match dest_type ty with (_,[a;b]) -> a,b | _ -> failwith "" in
  let vs = vars avoid (type_of e) in
  let tup = end_itlist (curry mk_pair) vs in
  let eqth = prove(list_mk_exists(vs, mk_eq(e,tup)),
                   MAP_EVERY EXISTS_TAC (comps e) THEN REWRITE_TAC[PAIR]) in
  REPEAT_TCL CHOOSE_THEN (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th; pair_CASE])
    eqth gl;;

let B2BP1AUX_Let_env = prove
 (`!L body env1 env2 (s:(C,FFI)bvi_state).
     (!s':(C,FFI)bvi_state. bvi_evaluate (L,env1,s') = bvi_evaluate (L,env2,s')) /\
     (!vs (s':(C,FFI)bvi_state). LENGTH vs = LENGTH L
              ==> bvi_evaluate ([body],APPEND vs env1,s') =
                  bvi_evaluate ([body],APPEND vs env2,s'))
     ==> bvi_evaluate ([bvi_Let L body],env1,s) =
         bvi_evaluate ([bvi_Let L body],env2,s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`L:bvi_exp list`; `env2:bvl_v list`; `s:(C,FFI)bvi_state`]
    bvi_evaluate_IMP_LENGTH) THEN
  MP_TAC(ISPEC `bvi_evaluate (L,env2,s:(C,FFI)bvi_state)` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(bvl_v list,exn_or_ret)result` (X_CHOOSE_THEN
    `s1:(C,FFI)bvi_state` SUBST1_TAC)) THEN
  MP_TAC(ISPEC `r:(bvl_v list,exn_or_ret)result` (cases "result")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let B2BP1AUX_LENGTH_GE = prove
 (`!(vs:bvl_v list).
     (1 <= LENGTH vs ==> ?h0 t. vs = CONS h0 t) /\
     (2 <= LENGTH vs ==> ?h0 h1 t. vs = CONS h0 (CONS h1 t)) /\
     (3 <= LENGTH vs ==> ?h0 h1 h2 t. vs = CONS h0 (CONS h1 (CONS h2 t)))`,
  GEN_TAC THEN
  MP_TAC(ISPEC `vs:bvl_v list` list_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH; CONS_11; NOT_CONS_NIL] THEN TRY ARITH_TAC THEN
  MP_TAC(ISPEC `t:bvl_v list` list_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH; CONS_11; NOT_CONS_NIL] THEN TRY (CONJ_TAC THEN ARITH_TAC) THEN
  MP_TAC(ISPEC `t':bvl_v list` list_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH; CONS_11; NOT_CONS_NIL] THEN
  REPEAT CONJ_TAC THEN TRY ARITH_TAC THEN MESON_TAC[]);;

let B2BP1AUX_LT_SUCS = prove
 (`!n. 0 < SUC n /\ 1 < SUC (SUC n) /\ 2 < SUC (SUC (SUC n)) /\
       3 < SUC (SUC (SUC (SUC n)))`,
  ARITH_TAC);;

let B2BP1AUX_REPLICATE_3 = prove
 (`!x:A. REPLICATE 3 x = [x; x; x]`,
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`; REPLICATE]);;

let B2BP1AUX_ENV_EV_TAC : tactic =
  REPEAT (CHANGED_TAC (
    ASM_REWRITE_TAC[bvi_evaluate_def; bvi_evaluate_APPEND; B2BP1AUX_REPLICATE_3;
                    APPEND; LENGTH; B2BP1AUX_LT_SUCS; compile_int_thm] THEN
    CASE_REWRITE_TAC[] THEN CONV_TAC (DEPTH_CONV B2BP1AUX_EL_CONV)));;

let B2BP1AUX_VS_TAC : tactic =
  let ths = CONJUNCTS (SPEC `vs:bvl_v list` B2BP1AUX_LENGTH_GE) in
  let arith =
    RULE_ASSUM_TAC(REWRITE_RULE[NULL_EQ; GSYM LENGTH_EQ_NIL; LENGTH; LENGTH_APPEND;
                                LENGTH_REPLICATE]) THEN
    B2BP1AUX_ARITH_TAC in
  let try_k k =
    let th = el (k - 1) ths in
    SUBGOAL_THEN (lhand (concl th))
      (fun le -> REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC (MP th le)) THENL
    [arith; ALL_TAC] in
  FIRST [try_k 3; try_k 2; try_k 1; ALL_TAC];;


let B2BP1AUX_ENV_EV2_TAC : tactic =
  REPEAT (CHANGED_TAC (
    ASM_REWRITE_TAC[bvi_evaluate_def; bvi_evaluate_APPEND; B2BP1AUX_REPLICATE_3;
                    APPEND; LENGTH; B2BP1AUX_LT_SUCS; compile_int_thm] THEN
    CASE_REWRITE_TAC[] THEN CONV_TAC (DEPTH_CONV B2BP1AUX_EL_CONV)) ORELSE
    CASE_TAC);;
let B2BP1AUX_OPENV_LEAF_TAC : tactic =
  FIRST
   [ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    B2BP1AUX_ENV_EV_TAC THEN NO_TAC;
    MATCH_MP_TAC B2BP1AUX_Let_env THEN CONJ_TAC THENL
     [GEN_TAC THEN B2BP1AUX_ENV_EV_TAC THEN NO_TAC;
      REPEAT GEN_TAC THEN DISCH_TAC THEN B2BP1AUX_VS_TAC THEN
      B2BP1AUX_ENV_EV2_TAC THEN NO_TAC]];;

(* a local helper (not in HOL4): the code of compile_op depends on the  *)
(* environment only through its arguments c1                              *)
let B2BP1AUX_compile_op_env = prove
 (`!op c1 env1 env2 (s:(C,FFI)bvi_state).
     (!s':(C,FFI)bvi_state. bvi_evaluate (c1,env1,s') = bvi_evaluate (c1,env2,s'))
     ==> bvi_evaluate ([bvl_to_bvi_compile_op op c1],env1,s) =
         bvi_evaluate ([bvl_to_bvi_compile_op op c1],env2,s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_op_def] THEN
  REPEAT TOP_CASE_TAC THEN B2BP1AUX_OPENV_LEAF_TAC);;

let B2BP1AUX_IHEQ_TAC : tactic = fun (asl,w as g) ->
  let ths = map snd asl in
  let cexp t = is_comb t && is_comb (rator t) &&
               (try fst(dest_const(rator(rator t))) = "bvl_to_bvi_compile_exps"
                with Failure _ -> false) in
  let eqs = filter (fun th -> let c = concl th in is_eq c && cexp (lhs c)) ths in
  let ihs = filter (fun th -> let c = concl th in is_forall c &&
                      can (find_term cexp) c && is_imp (snd(strip_forall c))) ths in
  let mk ih eq =
    let n,b = dest_forall (concl ih) in
    let e = lhs (concl eq) in
    let x = rand e and nn = rand (rator e) in
    let ce = find_term (fun t -> cexp t && rand (rator t) = n) b in
    if rand ce = x then [REWRITE_RULE[eq; FST] (SPEC nn ih)] else [] in
  let new_ths = itlist (fun ih acc -> itlist (fun eq acc2 -> mk ih eq @ acc2) eqs acc) ihs [] in
  MAP_EVERY ASSUME_TAC new_ths g;;

let B2BP1AUX_PULL_IMP th =
  let c = concl th in
  let xs, b = strip_forall c in
  let p, q = dest_imp b in
  if exists (fun x -> free_in x p) xs then failwith "B2BP1AUX_PULL_IMP" else
  DISCH p (GENL xs (MP (SPECL xs th) (ASSUME p)));;

let B2BP1AUX_IHMP_TAC (t:term) : tactic =
  REPEAT (FIRST_X_ASSUM (fun th ->
    let c = concl th in
    let (v,_) = dest_forall c in
    if type_of v = type_of t && is_imp (snd (strip_forall c)) then
      MP_TAC (B2BP1AUX_PULL_IMP (ISPEC t th)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN NO_TAC; DISCH_TAC]
    else failwith "B2BP1AUX_IHMP_TAC"));;

let B2BP1AUX_CSING_TAC : tactic =
  REPEAT (FIRST_X_ASSUM (fun th (asl,w as g) ->
    let th' = MATCH_MP bvl_to_bvi_compile_exps_SING th in
    let v = fst(dest_exists(concl th')) in
    let a = lhs(snd(dest_exists(concl th'))) in
    if is_var a then
      let avoid = itlist (union o frees o concl o snd) asl (frees w) in
      (ASSUME_TAC th THEN
       X_CHOOSE_THEN (variant (frees (concl th) @ avoid) v) SUBST_ALL_TAC th') g
    else failwith ""));;

let B2BP1AUX_IEVB_STD_TAC : tactic =
  B2BP1AUX_IND_STRIP_TAC THEN
  POP_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[bVarBound_def; handle_ok_def]) THEN
  REWRITE_TAC[bvl_to_bvi_compile_exps_def] THEN
  REPEAT (B2BP1AUX_PAIR_SPLIT_TAC "bvl_to_bvi_compile_exps") THEN
  REWRITE_TAC[FST] THEN B2BP1AUX_IHEQ_TAC THEN
  B2BP1AUX_IHMP_TAC `vs:bvl_v list` THEN B2BP1AUX_CSING_TAC;;

let B2BP1AUX_IEVB_CLOSE_TAC : tactic =
  REWRITE_TAC[HD] THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];;

let B2BP1AUX_let_ok_imp = prove
 (`!x. let_ok x
       ==> ?ys b. x = bvl_Let ys b /\ ALL isVar ys /\ bVarBound (LENGTH ys) [b]`,
  GEN_TAC THEN CASES_ON `x:bvl_exp` THEN
  REWRITE_TAC[let_ok_def; injectivity "bvl_exp"; distinctness "bvl_exp"] THEN
  MESON_TAC[]);;

let B2BP1AUX_handle_ok_Handle = prove
 (`!x1 x2. handle_ok [bvl_Handle x1 x2]
           ==> ?xs b. x1 = bvl_Let xs b /\ ALL isVar xs /\ bVarBound (LENGTH xs) [b] /\
                      handle_ok [b] /\ handle_ok [x2]`,
  GEN_TAC THEN CASES_ON `x1:bvl_exp` THEN REWRITE_TAC[handle_ok_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[injectivity "bvl_exp"; distinctness "bvl_exp"] THEN
  MESON_TAC[]);;

let B2BP1AUX_Handle_env = prove
 (`!loc c1 d3 vs env (s:(C,FFI)bvi_state).
     (!s':(C,FFI)bvi_state.
        bvi_evaluate (c1,APPEND vs env,s') = bvi_evaluate (c1,vs,s')) /\
     (!v (s':(C,FFI)bvi_state).
        bvi_evaluate ([d3],CONS v (APPEND vs env),s') = bvi_evaluate ([d3],CONS v vs,s'))
     ==> bvi_evaluate ([bvi_Call 0 loc c1 (SOME d3)],APPEND vs env,s) =
         bvi_evaluate ([bvi_Call 0 loc c1 (SOME d3)],vs,s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 1145 [local] (HOL4 binds n twice: !(n:num) xs n ...) *)
let iEval_bVarBound = prove
 (`!xs n vs (s:(C,FFI)bvi_state) env.
     bVarBound (LENGTH vs) xs /\ handle_ok xs
     ==> bvi_evaluate (FST (bvl_to_bvi_compile_exps n xs),APPEND vs env,s) =
         bvi_evaluate (FST (bvl_to_bvi_compile_exps n xs),vs,s)`,
  SUBGOAL_THEN
   `!(m:num) es n vs (s:(C,FFI)bvi_state) env.
      bVarBound (LENGTH vs) es /\ handle_ok es
      ==> bvi_evaluate (FST (bvl_to_bvi_compile_exps n es),APPEND vs env,s) =
          bvi_evaluate (FST (bvl_to_bvi_compile_exps n es),vs,s)`
   (fun th -> MATCH_ACCEPT_TAC (SPEC `0` th)) THEN
  MATCH_MP_TAC bVarBound_ind THEN REPEAT CONJ_TAC THENL
  [(* [] *)
   REWRITE_TAC[bvl_to_bvi_compile_exps_def; bvi_evaluate_def];
   (* x::y::xs *)
   B2BP1AUX_IEVB_STD_TAC THEN REWRITE_TAC[bvi_evaluate_APPEND] THEN ASM_REWRITE_TAC[];
   (* Var *)
   REPEAT GEN_TAC THEN
   REWRITE_TAC[bVarBound_def; handle_ok_def; bvl_to_bvi_compile_exps_def; FST;
               bvi_evaluate_def; LENGTH_APPEND] THEN
   STRIP_TAC THEN ASM_SIMP_TAC[EL_APPEND1; ARITH_RULE `v < a ==> v < a + b:num`];
   (* If *)
   B2BP1AUX_IEVB_STD_TAC THEN B2BP1AUX_IEVB_CLOSE_TAC;
   (* Let *)
   X_GEN_TAC `m0:num` THEN X_GEN_TAC `xs:bvl_exp list` THEN X_GEN_TAC `x2:bvl_exp` THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   MAP_EVERY X_GEN_TAC [`n:num`; `vs:bvl_v list`; `s:(C,FFI)bvi_state`; `env:bvl_v list`] THEN
   DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[bVarBound_def; handle_ok_def]) THEN
   REWRITE_TAC[bvl_to_bvi_compile_exps_def] THEN
   ASM_CASES_TAC `xs:bvl_exp list = []` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH; ADD_CLAUSES]) THEN REWRITE_TAC[NULL] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 (X_CHOOSE_THEN `ys:bvl_exp list` (X_CHOOSE_THEN
      `b:bvl_exp` STRIP_ASSUME_TAC) o MATCH_MP B2BP1AUX_let_ok_imp) ASSUME_TAC o
      check (fun th -> is_conj (concl th) &&
                       can (find_term ((=) `let_ok`)) (concl th))) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[bVarBound_def]) THEN
    REWRITE_TAC[destLet_def] THEN CASE_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`ys:bvl_exp list`; `n:num`] compile_exps_Var_list) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    B2BP1AUX_PAIR_SPLIT_TAC "bvl_to_bvi_compile_exps" THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF; FST] THEN
    MP_TAC(ISPECL [`ys:bvl_exp list`; `vs:bvl_v list`; `env:bvl_v list`;
                   `s:(C,FFI)bvi_state`] evaluate_MAP_Var2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[bvi_evaluate_def] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[LENGTH_EQ_NIL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[NULL_EQ] THEN
    REPEAT (B2BP1AUX_PAIR_SPLIT_TAC "bvl_to_bvi_compile_exps") THEN REWRITE_TAC[FST] THEN
    B2BP1AUX_IHEQ_TAC THEN B2BP1AUX_IHMP_TAC `vs:bvl_v list` THEN B2BP1AUX_CSING_TAC THEN
    FIRST_ASSUM(fun th -> if is_eq (concl th) && rand (lhs (concl th)) = `xs:bvl_exp list`
                          then ASSUME_TAC (MATCH_MP bvl_to_bvi_compile_exps_LENGTH th)
                          else failwith "") THEN
    REWRITE_TAC[HD] THEN MATCH_MP_TAC B2BP1AUX_Let_env THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[];
     X_GEN_TAC `ws:bvl_v list` THEN X_GEN_TAC `s2:(C,FFI)bvi_state` THEN DISCH_TAC THEN
     REWRITE_TAC[APPEND_ASSOC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[LENGTH_APPEND] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[]]];
   (* Raise *)
   B2BP1AUX_IEVB_STD_TAC THEN B2BP1AUX_IEVB_CLOSE_TAC;
   (* Tick *)
   B2BP1AUX_IEVB_STD_TAC THEN B2BP1AUX_IEVB_CLOSE_TAC;
   (* Op *)
   B2BP1AUX_IEVB_STD_TAC THEN MATCH_MP_TAC B2BP1AUX_compile_op_env THEN ASM_REWRITE_TAC[];
   (* Force *)
   REPEAT GEN_TAC THEN
   REWRITE_TAC[bVarBound_def; handle_ok_def; bvl_to_bvi_compile_exps_def; FST] THEN
   STRIP_TAC THEN ONCE_REWRITE_TAC[bvi_evaluate_def] THEN
   ASM_SIMP_TAC[EL_APPEND1; LENGTH_APPEND; ARITH_RULE `v < a ==> v < a + b:num`];
   (* Handle *)
   X_GEN_TAC `m0:num` THEN X_GEN_TAC `x1:bvl_exp` THEN X_GEN_TAC `x2:bvl_exp` THEN
   DISCH_THEN STRIP_ASSUME_TAC THEN
   MAP_EVERY X_GEN_TAC [`n:num`; `vs:bvl_v list`; `s:(C,FFI)bvi_state`; `env:bvl_v list`] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o REWRITE_RULE[bVarBound_def])
     (X_CHOOSE_THEN `ys:bvl_exp list` (X_CHOOSE_THEN `b:bvl_exp` STRIP_ASSUME_TAC) o
      MATCH_MP B2BP1AUX_handle_ok_Handle)) THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
                                                  lhs (concl th) = `x1:bvl_exp`)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[bVarBound_def]) THEN
   REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
   REWRITE_TAC[bvl_to_bvi_compile_exps_def; destLet_def] THEN CASE_REWRITE_TAC[] THEN
   MP_TAC(SPECL [`ys:bvl_exp list`; `n:num`] compile_exps_Var_list) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   REPEAT (B2BP1AUX_PAIR_SPLIT_TAC "bvl_to_bvi_compile_exps") THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF; FST] THEN
   B2BP1AUX_IHEQ_TAC THEN B2BP1AUX_CSING_TAC THEN REWRITE_TAC[HD] THEN
   MATCH_MP_TAC B2BP1AUX_Handle_env THEN CONJ_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`ys:bvl_exp list`; `vs:bvl_v list`; `env:bvl_v list`;
                   `s':(C,FFI)bvi_state`] evaluate_MAP_Var2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[GSYM (CONJUNCT2 APPEND)] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LENGTH; ADD1]];
   (* Call *)
   B2BP1AUX_IEVB_STD_TAC THEN B2BP1AUX_IEVB_CLOSE_TAC]);;

(* HOL4 line 1313 [local] *)
let v_to_list_adjust = prove
 (`!x f. bvl_v_to_list (adjust_bv f x) = OPTION_MAP (MAP (adjust_bv f)) (bvl_v_to_list x)`,
  MATCH_MP_TAC bvl_v_to_list_ind THEN
  REWRITE_TAC[adjust_bv_def; MAP; bvl_v_to_list_def; OPTION_MAP_DEF] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF; MAP] THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `tag = cons_tag`)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SPEC_TAC(`bvl_v_to_list bt`,`o1:(bvl_v list)option`) THEN
  MATCH_MP_TAC option_INDUCT THEN CASE_REWRITE_TAC[OPTION_MAP_DEF; MAP]);;

let B2BP1AUX_isClos_MAP = prove
 (`!t (f:A->B) l. bvl_isClos t (MAP f l) <=> bvl_isClos t l`,
  REWRITE_TAC[bvl_isClos_def; MAP_EQ_NIL]);;

(* HOL4 line 1321 [local] (r, b2 and t2 are free in HOL4; do_eq on the     *)
(* bvi refs is bvlSem's) *)
let do_eq_adjust_lemma = prove
 (`!r b2 (t2:(C,FFI)bvi_state).
     (!refs x1 x2 b.
        refs = bvl_state_refs r /\
        bvl_do_eq refs x1 x2 = Eq_val b /\ bvl_to_bviProof_state_rel b2 r t2 /\
        bv_ok (bvl_state_refs r) x1 /\ bv_ok (bvl_state_refs r) x2
        ==> bvl_do_eq (bvi_state_refs t2) (adjust_bv b2 x1) (adjust_bv b2 x2) = Eq_val b) /\
     (!refs x1 x2 b.
        refs = bvl_state_refs r /\
        bvl_do_eq_list refs x1 x2 = Eq_val b /\ bvl_to_bviProof_state_rel b2 r t2 /\
        ALL (bv_ok (bvl_state_refs r)) x1 /\ ALL (bv_ok (bvl_state_refs r)) x2
        ==> bvl_do_eq_list (bvi_state_refs t2) (MAP (adjust_bv b2) x1) (MAP (adjust_bv b2) x2) =
            Eq_val b)`,
  (REPEAT GEN_TAC THEN MATCH_MP_TAC bvl_do_eq_ind THEN REPEAT CONJ_TAC THEN
   B2BP1AUX_IND_STRIP_TAC THEN POP_ASSUM STRIP_ASSUME_TAC THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) && is_var (lhs (concl th)))) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[bvl_do_eq_def; distinctness "eq_result";
     GSYM(distinctness "eq_result")]) THEN
   TRY (FIRST_ASSUM CONTR_TAC) THEN
   REWRITE_TAC[adjust_bv_def; MAP; bvl_do_eq_def] THEN ASM_REWRITE_TAC[]) THENL
  [(RULE_ASSUM_TAC(REWRITE_RULE[bv_ok_def]) THEN
   UNDISCH_TAC `bvl_to_bviProof_state_rel b2 r (t2:(C,FFI)bvi_state)` THEN
   REWRITE_TAC[bvl_to_bviProof_state_rel_def; INJ] THEN
   DISCH_THEN(fun th -> LABEL_TAC "refs" (CONJUNCT1(CONJUNCT2 th)) THEN
     LABEL_TAC "inj" (CONJUNCT2(CONJUNCT1 th))) THEN
   SUBGOAL_THEN `(b2:num->num) n1 = b2 n2 <=> n1 = n2` (fun th -> REWRITE_TAC[th]) THENL
    [EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `?x1. FLOOKUP (bvl_state_refs (r:(num#C,FFI)bvl_state)) n1 = SOME x1`
     (X_CHOOSE_THEN `x1:(bvl_v)bvl_ref` (LABEL_TAC "f1")) THENL
    [ASM_MESON_TAC[FLOOKUP_DEF]; ALL_TAC] THEN
   SUBGOAL_THEN `?x2. FLOOKUP (bvl_state_refs (r:(num#C,FFI)bvl_state)) n2 = SOME x2`
     (X_CHOOSE_THEN `x2:(bvl_v)bvl_ref` (LABEL_TAC "f2")) THENL
    [ASM_MESON_TAC[FLOOKUP_DEF]; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     can (find_term ((=) `Eq_val:bool->eq_result`)) (concl th))) THEN
   USE_THEN "refs" (MP_TAC o SPEC `n2:num`) THEN USE_THEN "refs" (MP_TAC o SPEC `n1:num`) THEN
   USE_THEN "f1" (fun f1 -> USE_THEN "f2" (fun f2 -> REWRITE_TAC[f1; f2])) THEN
   CASE_REWRITE_TAC[] THEN
   MAP_EVERY (fun t -> STRUCT_CASES_TAC (ISPEC t (cases "bvl_ref")))
     [`x1:(bvl_v)bvl_ref`; `x2:(bvl_v)bvl_ref`] THEN
   CASE_REWRITE_TAC[] THEN
   DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
   SIMP_TAC[]);
   (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     can (find_term ((=) `Eq_val:bool->eq_result`)) (concl th))) THEN
   REWRITE_TAC[B2BP1AUX_isClos_MAP; LENGTH_MAP] THEN
   ASM_CASES_TAC `bvl_isClos t1 (l1:bvl_v list) \/ bvl_isClos t2' (l2:bvl_v list)` THEN
   ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `t1:num = t2' /\ LENGTH (l1:bvl_v list) = LENGTH (l2:bvl_v list)` THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   RULE_ASSUM_TAC(REWRITE_RULE[bv_ok_def]) THEN
   FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);
   (FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
     can (find_term ((=) `Eq_val:bool->eq_result`)) (concl th))) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN
   REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
   MP_TAC(ISPEC `bvl_do_eq (bvl_state_refs (r:(num#C,FFI)bvl_state)) v1 v2` (cases "eq_result")) THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   REWRITE_TAC[distinctness "eq_result"; GSYM(distinctness "eq_result")] THEN
   B2BP1AUX_RES_TAC [] [] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
   ASM_CASES_TAC `a:bool` THEN ASM_REWRITE_TAC[] THEN
   TRY DISCH_TAC THEN B2BP1AUX_RES_TAC [] [] THEN ASM_REWRITE_TAC[])]);;

(* HOL4 line 1352 [local] *)
let do_eq_adjust = prove
 (`!r x1 x2 b b2 (t2:(C,FFI)bvi_state).
     bvl_do_eq (bvl_state_refs r) x1 x2 = Eq_val b /\ bvl_to_bviProof_state_rel b2 r t2 /\
     bv_ok (bvl_state_refs r) x1 /\ bv_ok (bvl_state_refs r) x2
     ==> bvl_do_eq (bvi_state_refs t2) (adjust_bv b2 x1) (adjust_bv b2 x2) = Eq_val b`,
  MESON_TAC[do_eq_adjust_lemma]);;

(* HOL4 line 1360 *)
let list_to_v_adjust = prove
 (`!xs b. bvl_list_to_v (MAP (adjust_bv b) xs) = adjust_bv b (bvl_list_to_v xs)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; bvl_list_to_v_def; adjust_bv_def]);;

(* HOL4 line 1367 (HOL4 states the same hypothesis twice) *)
let list_to_v_adjust_APPEND = prove
 (`!xs ys b.
     bvl_list_to_v (MAP (adjust_bv b) xs) = adjust_bv b (bvl_list_to_v xs) /\
     bvl_list_to_v (MAP (adjust_bv b) xs) = adjust_bv b (bvl_list_to_v xs)
     ==> bvl_list_to_v (MAP (adjust_bv b) (APPEND xs ys)) =
         adjust_bv b (bvl_list_to_v (APPEND xs ys))`,
  REWRITE_TAC[list_to_v_adjust]);;

(* local helpers for do_app_adjust (not in HOL4): the excluded operations, *)
(* do_int_app and do_word_app under adjust_bv, state_rel after an update of *)
(* a ref or of the ffi, and a case split of bvl do_app whose leaves compute *)
(* bviSem's do_app on the adjusted arguments                                *)
let B2BP1AUX_FORALL_NEQ = prove
 (`(!a:A. (!x. ~(x = a)) <=> F) /\ (!a:A. (!x. ~(a = x)) <=> F)`,
  MESON_TAC[]);;

let B2BP1AUX_OP_RWS =
  let tl = ["clos_op"; "int_op"; "block_op"; "glob_op"; "mem_op"; "thunk_op"] in
  flat (map (fun s -> (try [distinctness s] with Failure _ -> []) @
                      (try [injectivity s] with Failure _ -> [])) tl) @
  [B2BP1AUX_FORALL_NEQ];;

let B2BP1AUX_EXCL_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE B2BP1AUX_OP_RWS) THEN FIRST_ASSUM CONTR_TAC;;

let B2BP1AUX_do_int_app_adjust = prove
 (`!op vs v b. bvl_do_int_app op vs = SOME v
               ==> bvl_do_int_app op (MAP (adjust_bv b) vs) = SOME (adjust_bv b v)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CLOSSEMAUX_do_int_app_some) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[MAP; adjust_bv_def; adjust_bv_Boolv] THEN
  REWRITE_TAC[bvl_do_int_app_def] THEN CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let B2BP1AUX_do_word_app_adjust = prove
 (`!op vs v. bvl_do_word_app op vs = SOME v
             ==> !b. bvl_do_word_app op (MAP (adjust_bv b) vs) = SOME (adjust_bv b v)`,
  MATCH_MP_TAC bvl_do_word_app_ind THEN REWRITE_TAC[bvl_do_word_app_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT (TOP_CASE_TAC ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN GEN_TAC THEN
  REWRITE_TAC[MAP; adjust_bv_def; adjust_bv_Boolv; bvl_do_word_app_def] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let B2BP1AUX_state_rel_ffi_eq = prove
 (`!b s (t:(C,FFI)bvi_state).
     bvl_to_bviProof_state_rel b s t ==> bvi_state_ffi t = bvl_state_ffi s`,
  SIMP_TAC[bvl_to_bviProof_state_rel_def]);;

let B2BP1AUX_state_rel_ffi = prove
 (`!b s (t:(C,FFI)bvi_state) f.
     bvl_to_bviProof_state_rel b s t
     ==> bvl_to_bviProof_state_rel b (bvl_state_ffi_fupd (K f) s)
           (bvi_state_ffi_fupd (K f) t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bvl_to_bviProof_state_rel_def; bvl_state_INFO.ri_accfupds;
              bvi_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* a ref of s updated (HOL4 does it inline in each case of do_app_adjust) *)
let B2BP1AUX_STATE_REL_UPD_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
     (is_var (lhs (concl th)))))) THEN
  SUBGOAL_THEN `!a. a IN FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state))
                    ==> ((b:num->num) a = b ptr <=> a = ptr)` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[bvl_to_bviProof_state_rel_def; INJ]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `bvl_to_bviProof_state_rel b s (t:(C,FFI)bvi_state)` THEN
  REWRITE_TAC[bvl_to_bviProof_state_rel_def] THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; bvi_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN(fun th -> LABEL_TAC "refs" (CONJUNCT1(CONJUNCT2 th)) THEN
    LABEL_TAC "glob" (CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 th)))) THEN
    STRIP_ASSUME_TAC th) THEN
  SUBGOAL_THEN `(b:num->num) ptr IN FDOM (bvi_state_refs (t:(C,FFI)bvi_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[INJ]; ALL_TAC] THEN
  ASM_SIMP_TAC[FDOM_FUPDATE; ABSORPTION_RWT] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN REWRITE_TAC[FLOOKUP_UPDATE] THEN
    ASM_CASES_TAC `ptr:num = k` THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "refs" (MP_TAC o SPEC `k:num`) THEN
    TOP_CASE_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `k IN FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state))` ASSUME_TAC THENL
     [ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT]; ALL_TAC] THEN
    SUBGOAL_THEN `~((b:num->num) ptr = b k)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    USE_THEN "glob" (fun th -> MP_TAC (MATCH_MP (SPEC `p:num` th)
      (ASSUME `bvi_state_global (t:(C,FFI)bvi_state) = SOME p`))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~((b:num->num) ptr = p)` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_IMAGE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN EXISTS_TAC `z:num` THEN ASM_REWRITE_TAC[]];;

let B2BP1AUX_state_rel_upd_va = prove
 (`!b s (t:(C,FFI)bvi_state) ptr xs rs rt.
     bvl_to_bviProof_state_rel b s t /\ ptr IN FDOM (bvl_state_refs s) /\
     rs = bvl_state_refs s /\ rt = bvi_state_refs t
     ==> bvl_to_bviProof_state_rel b
           (bvl_state_refs_fupd (K (rs |+ (ptr,bvl_ValueArray xs))) s)
           (bvi_state_refs_fupd
              (K (rt |+ (b ptr,bvl_ValueArray (MAP (adjust_bv b) xs)))) t)`,
  B2BP1AUX_STATE_REL_UPD_TAC);;

let B2BP1AUX_state_rel_upd_ba = prove
 (`!b s (t:(C,FFI)bvi_state) ptr f ws rs rt.
     bvl_to_bviProof_state_rel b s t /\ ptr IN FDOM (bvl_state_refs s) /\
     rs = bvl_state_refs s /\ rt = bvi_state_refs t
     ==> bvl_to_bviProof_state_rel b
           (bvl_state_refs_fupd (K (rs |+ (ptr,bvl_ByteArray f ws))) s)
           (bvi_state_refs_fupd (K (rt |+ (b ptr,bvl_ByteArray f ws))) t)`,
  B2BP1AUX_STATE_REL_UPD_TAC);;

let B2BP1AUX_SPLIT_TAC : tactic = fun (asl,w as g) ->
  let x = first_case_scrutinee w w in
  if type_of x = bool_ty && is_var x then (ASM_CASES_TAC x THEN CASE_TIDY_TAC) g
  else TOP_CASE_TAC g;;

let B2BP1AUX_BOOL_DISJ_TAC : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_CLAUSES]) THEN
  REPEAT (FIRST_X_ASSUM (DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th ->
    let c = concl th in
    is_disj c && (let d1,d2 = dest_disj c in
                  is_eq d1 && is_var (lhs d1) && is_eq d2 && is_var (lhs d2) &&
                  type_of (lhs d1) = `:bvl_v`))));;

let B2BP1AUX_INTOP_CASES_TAC : tactic = fun (asl,w as g) ->
  try let v = find_term (fun t -> is_var t && type_of t = `:int_op`) w in
      (CASES_ON v THEN TRY (B2BP1AUX_EXCL_TAC THEN NO_TAC)) g
  with Failure _ -> ALL_TAC g;;

let B2BP1AUX_DAA_RW_TAC (thl:thm list) : tactic =
  REPEAT (CHANGED_TAC (ASM_REWRITE_TAC thl THEN CASE_REWRITE_TAC[]));;

let B2BP1AUX_DAA_LEAF_TAC : tactic =
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  B2BP1AUX_BOOL_DISJ_TAC THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN
  B2BP1AUX_RES_TAC [ALL]
    [state_rel_FLOOKUP_byteArray; state_rel_FLOOKUP_valueArray; do_eq_adjust;
     B2BP1AUX_do_int_app_adjust; B2BP1AUX_do_word_app_adjust;
     B2BP1AUX_state_rel_ffi_eq] THEN
  REWRITE_TAC[bvi_do_app_def; MAP; adjust_bv_def; adjust_bv_Boolv; adjust_bv_Unit] THEN
  REWRITE_TAC B2BP1AUX_OP_RWS THEN
  REWRITE_TAC[bvi_do_app_aux_def] THEN CASE_REWRITE_TAC[] THEN
  B2BP1AUX_INTOP_CASES_TAC THEN
  REWRITE_TAC[bvl_do_app_def; LET_DEF; LET_END_DEF] THEN
  B2BP1AUX_DAA_RW_TAC [LENGTH_MAP; v_to_list_adjust; OPTION_MAP_DEF; bvi_bvi_to_bvl_refs;
                       bvi_to_bvl_ffi; adjust_bv_Boolv; adjust_bv_Unit] THEN
  REWRITE_TAC[injectivity "result"; PAIR_EQ; GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM;
              UNWIND_THM1; bvl_to_bvi_id; bvl_to_bvi_with_refs; bvl_to_bvi_with_ffi;
              adjust_bv_def; adjust_bv_Boolv; adjust_bv_Unit] THEN
  ASM_SIMP_TAC[EL_MAP; BASICAUX_num_of_int_lt; GSYM MAP_APPEND; GSYM MAP_TAKE; GSYM MAP_DROP;
               GSYM LUPDATE_MAP; list_to_v_adjust] THEN
  TRY (MATCH_MP_TAC B2BP1AUX_state_rel_upd_va ORELSE
       MATCH_MP_TAC B2BP1AUX_state_rel_upd_ba) THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; bvi_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT CONJ_TAC THEN
  TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  TRY (FIRST_ASSUM (fun th -> MATCH_ACCEPT_TAC (MATCH_MP FMAPAUX_FLOOKUP_SOME_FDOM th))) THEN
  TRY (MATCH_MP_TAC B2BP1AUX_state_rel_ffi THEN FIRST_ASSUM ACCEPT_TAC);;

(* do_app_adjust for any argument list vs (HOL4's REVERSE a) *)
let B2BP1AUX_do_app_adjust_gen = prove
 (`!b2 s5 (t2:(C,FFI)bvi_state) op vs q r.
     bvl_to_bviProof_state_rel b2 s5 t2 /\
     (!i. ~(op = IntOp (clos_Const i))) /\ ~(op = MemOp clos_Ref) /\
     (!flag. ~(op = MemOp (RefByte flag))) /\ ~(op = MemOp RefArray) /\
     (!n. ~(op = GlobOp (clos_Global n))) /\ (!n. ~(op = GlobOp (SetGlobal n))) /\
     ~(op = GlobOp AllocGlobal) /\
     ~(op = clos_Install) /\
     (!t. ~(op = clos_ThunkOp t)) /\
     (!n. ~(op = BlockOp (FromList n))) /\ ~(op = MemOp FromListByte) /\
     ~(op = MemOp ToListByte) /\ (!c. ~(op = BlockOp (Build c))) /\ ~(op = MemOp XorByte) /\
     (!b. ~(op = MemOp (CopyByte b))) /\ ~(op = MemOp ConcatByteVec) /\
     (!n. ~(op = clos_Label n)) /\
     ALL (bv_ok (bvl_state_refs s5)) vs
     ==> bvl_do_app op vs s5 = Rval (q,r)
     ==> ?t3. bvi_do_app op (MAP (adjust_bv b2) vs) t2 = Rval (adjust_bv b2 q,t3) /\
              bvl_to_bviProof_state_rel b2 r t3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[bvl_do_app_def; LET_DEF; LET_END_DEF] THEN
  REPEAT (B2BP1AUX_SPLIT_TAC THEN TRY (B2BP1AUX_EXCL_TAC THEN NO_TAC)) THEN
  REWRITE_TAC[injectivity "result"; distinctness "result"; PAIR_EQ] THEN
  B2BP1AUX_DAA_LEAF_TAC);;

(* HOL4 line 1379 [local] (the second do_app is bviSem's) *)
let do_app_adjust = prove
 (`!b2 s5 (t2:(C,FFI)bvi_state) op a q r.
     bvl_to_bviProof_state_rel b2 s5 t2 /\
     (!i. ~(op = IntOp (clos_Const i))) /\ ~(op = MemOp clos_Ref) /\
     (!flag. ~(op = MemOp (RefByte flag))) /\ ~(op = MemOp RefArray) /\
     (!n. ~(op = GlobOp (clos_Global n))) /\ (!n. ~(op = GlobOp (SetGlobal n))) /\
     ~(op = GlobOp AllocGlobal) /\
     ~(op = clos_Install) /\
     (!t. ~(op = clos_ThunkOp t)) /\
     (!n. ~(op = BlockOp (FromList n))) /\ ~(op = MemOp FromListByte) /\
     ~(op = MemOp ToListByte) /\ (!c. ~(op = BlockOp (Build c))) /\ ~(op = MemOp XorByte) /\
     (!b. ~(op = MemOp (CopyByte b))) /\ ~(op = MemOp ConcatByteVec) /\
     (!n. ~(op = clos_Label n)) /\
     bvl_do_app op (REVERSE a) s5 = Rval (q,r) /\
     ALL (bv_ok (bvl_state_refs s5)) (REVERSE a)
     ==> ?t3. bvi_do_app op (MAP (adjust_bv b2) (REVERSE a)) t2 = Rval (adjust_bv b2 q,t3) /\
              bvl_to_bviProof_state_rel b2 r t3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b2:num->num`; `s5:(num#C,FFI)bvl_state`; `t2:(C,FFI)bvi_state`;
                `op:clos_op`; `REVERSE (a:bvl_v list)`; `q:bvl_v`;
                `r:(num#C,FFI)bvl_state`] B2BP1AUX_do_app_adjust_gen) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 1653 (evaluate is bvlSem's; bound variables of two types with *)
(* one HOL4 name are renamed: the thunk mode v1 of the Force case is m1,     *)
(* the pair v of the Call case is v', the bound variables of the conclusion  *)
(* are xs env s) *)
let eval_ind_alt = prove
 (`!P:bvl_exp list#bvl_v list#(C,FFI)bvl_state->bool.
     (!env s. P ([],env,s)) /\
     (!x y xs env s.
        (!v3 s1 v1. bvl_evaluate ([x],env,s) = (v3,s1) /\ v3 = Rval v1
                    ==> P (CONS y xs,env,s1)) /\
        P ([x],env,s)
        ==> P (CONS x (CONS y xs),env,s)) /\
     (!n env s. P ([bvl_Var n],env,s)) /\
     (!x1 x2 x3 env s.
        (!v2 s1 vs.
           bvl_evaluate ([x1],env,s) = (v2,s1) /\ v2 = Rval vs /\
           ~(bvl_Boolv T = HD vs) /\ bvl_Boolv F = HD vs
           ==> P ([x3],env,s1)) /\
        (!v2 s1 vs.
           bvl_evaluate ([x1],env,s) = (v2,s1) /\ v2 = Rval vs /\ bvl_Boolv T = HD vs
           ==> P ([x2],env,s1)) /\
        P ([x1],env,s)
        ==> P ([bvl_If x1 x2 x3],env,s)) /\
     (!xs x2 env s.
        (!ys v2 s1 vs.
           list_size bvl_exp_size ys <= bvl_exp_size x2 /\ bvl_evaluate (xs,env,s) = (v2,s1)
           ==> P (ys,vs,s1)) /\
        (!ys env. list_size bvl_exp_size ys <= bvl_exp_size x2 ==> P (ys,env,s)) /\
        (!v2 s1 vs.
           bvl_evaluate (xs,env,s) = (v2,s1) /\ v2 = Rval vs
           ==> P ([x2],APPEND vs env,s1)) /\
        P (xs,env,s)
        ==> P ([bvl_Let xs x2],env,s)) /\
     (!x1 env s. P ([x1],env,s) ==> P ([bvl_Raise x1],env,s)) /\
     (!op xs env s. P (xs,env,s) ==> P ([bvl_Op op xs],env,s)) /\
     (!x1 x2 env s1.
        (!v3 s v8 v.
           bvl_evaluate ([x1],env,s1) = (v3,s) /\ v3 = Rerr v8 /\ v8 = Rraise v
           ==> P ([x2],CONS v env,s)) /\
        (!xs env. list_size bvl_exp_size xs <= bvl_exp_size x1 ==> P (xs,env,s1))
        ==> P ([bvl_Handle x1 x2],env,s1)) /\
     (!force_loc n env s.
        (!thunk_v m1 v v' args exp.
           n < LENGTH env /\ thunk_v = EL n env /\
           bvl_dest_thunk thunk_v (bvl_state_refs s) = bvl_IsThunk m1 v /\
           m1 = NotEvaluated /\
           ~(bvl_state_clock s = 0) /\
           bvl_find_code (SOME force_loc) [thunk_v; v] (bvl_state_code s) = SOME v' /\
           v' = (args,exp) /\ ~(bvl_state_clock s = 0)
           ==> P ([exp],args,bvl_dec_clock 1 s))
        ==> P ([bvl_Force force_loc n],env,s)) /\
     (!x env s.
        (~(bvl_state_clock s = 0) ==> P ([x],env,bvl_dec_clock 1 s))
        ==> P ([bvl_Tick x],env,s)) /\
     (!ticks dest xs env s1.
        (!v2 s vs v' args exp.
           bvl_evaluate (xs,env,s1) = (v2,s) /\ v2 = Rval vs /\
           bvl_find_code dest vs (bvl_state_code s) = SOME v' /\ v' = (args,exp) /\
           ~(bvl_state_clock s < ticks + 1)
           ==> P ([exp],args,bvl_dec_clock (ticks + 1) s)) /\
        P (xs,env,s1)
        ==> P ([bvl_Call ticks dest xs],env,s1))
     ==> !xs env s. P (xs,env,s)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:bvl_exp list#bvl_v list#(C,FFI)bvl_state. P x`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC(REWRITE_RULE[WF_IND] (prove
   (`WF (inv_image (MEASURE (I:num->num) LEX MEASURE (list_size bvl_exp_size))
          (\x:bvl_exp list#bvl_v list#(C,FFI)bvl_state.
             bvl_state_clock (SND (SND x)),FST x))`, WF_TAC))) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`xs:bvl_exp list`; `env:bvl_v list`; `s:(C,FFI)bvl_state`] THEN
  STRUCT_CASES_TAC(ISPEC `xs:bvl_exp list` list_CASES) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `t:bvl_exp list` list_CASES) THENL
   [CASES_ON `h:bvl_exp`; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "ih") THEN
  (fun (asl,w as g) -> FIRST (map (fun (l,th) -> if l = "ih" then NO_TAC
                                  else (fun g -> (MATCH_ACCEPT_TAC th ORELSE
                                     (fun g1 -> MATCH_MP_TAC th g1)) g)) asl) g) THEN
  REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN TRY (DISCH_THEN STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "ih" MATCH_MP_TAC THEN
  REWRITE_TAC[inv_image_THM; LEX_THM; measure_THM; I_THM] THEN
  (fun (asl,w as g) -> MAP_EVERY (fun (_,th) -> try ASSUME_TAC (MATCH_MP bvl_evaluate_clock th)
                                                with Failure _ -> ALL_TAC) asl g) THEN
  REWRITE_TAC[bvl_dec_clock_def; bvl_state_INFO.ri_accfupds; K_THM; list_size;
              type_size_def "bvl_exp"] THEN
  REWRITE_TAC(size_aux_eqs "bvl_exp") THEN REWRITE_TAC[list_size] THEN
  B2BP1AUX_ARITH_TAC);;

(* HOL4 line 1729 *)
let EVERY_isVar_evaluate_Rval_MEM = prove
 (`!l env a (s:(C,FFI)bvl_state) r.
     ALL isVar l /\ bvl_evaluate (l,env,s) = (Rval a,r)
     ==> ALL (\x. MEM x env) a /\ s = r`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[bvl_evaluate_def; PAIR_EQ; injectivity "result"] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN REWRITE_TAC[ALL];
    ALL_TAC] THEN
  CASES_ON `h:bvl_exp` THEN REWRITE_TAC[ALL; isVar_def] THEN
  ONCE_REWRITE_TAC[bvl_evaluate_CONS] THEN REWRITE_TAC[bvl_evaluate_def] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; distinctness "result"] THEN STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN B2BP1AUX_EV_SPLIT_TAC "bvl_evaluate" THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; injectivity "result"; distinctness "result"] THEN
  STRIP_TAC THEN RVEQ_TAC THEN B2BP1AUX_RES_TAC [] [] THEN
  ASM_REWRITE_TAC[ALL; HD] THEN ASM_MESON_TAC[MEM_EL]);;

(* HOL4 line 1741 [local] (do_app is bviSem's) *)
let bvl_to_bviProof_do_app_Ref = prove
 (`!vs (s:(C,FFI)bvi_state).
     bvi_do_app (MemOp clos_Ref) vs s =
     Rval (bvl_RefPtr T (minimal ptr. ~(ptr IN FDOM (bvi_state_refs s))),
           bvl_to_bvi
             (bvl_state_refs_fupd
                (K (bvi_state_refs s |+
                    ((minimal ptr. ~(ptr IN FDOM (bvi_state_refs s))),bvl_ValueArray vs)))
                (bvi_to_bvl s)) s)`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV B2BP1AUX_DO_APP_CONV) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; bvi_bvi_to_bvl_refs] THEN CASE_REWRITE_TAC[]);;

(* local helpers for state_rel_add_bytearray and state_rel_add_thunk (not  *)
(* in HOL4): adjust_bv only depends on the refs of bv_ok values, and the   *)
(* common proof (a fresh ref pp of s is mapped to a fresh ref qq of t)     *)
let B2BP1AUX_globals_adjust_eq = prove
 (`!(s:(D,FFI)bvl_state) b b'.
     bvl_to_bviProof_state_ok s /\ (!a. a IN FDOM (bvl_state_refs s) ==> b' a = b a)
     ==> MAP (misc_the (bvl_Number (&0)) o OPTION_MAP (adjust_bv b')) (bvl_state_globals s) =
         MAP (misc_the (bvl_Number (&0)) o OPTION_MAP (adjust_bv b)) (bvl_state_globals s)`,
  REWRITE_TAC[bvl_to_bviProof_state_ok_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MAP_EQ THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb (concl th) &&
     (try fst(dest_const(fst(strip_comb(concl th)))) = "ALL" with Failure _ -> false))) THEN
  MATCH_MP_TAC MONO_ALL THEN MATCH_MP_TAC option_INDUCT THEN
  CASE_REWRITE_TAC[OPTION_MAP_DEF; o_THM] THEN
  ASM_MESON_TAC[bv_ok_IMP_adjust_bv_eq]);;

let B2BP1AUX_MAP_adjust_eq = prove
 (`!R b b' vs. ALL (bv_ok R) vs /\ (!v. bv_ok R v ==> adjust_bv b' v = adjust_bv b v)
               ==> MAP (adjust_bv b) vs = MAP (adjust_bv b') vs`,
  REWRITE_TAC[MAP_EQ_f; GSYM ALL_MEM] THEN MESON_TAC[]);;

let B2BP1AUX_STATE_REL_ADD_TAC : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a. a IN FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state))
                    ==> ((pp =+ qq) b) a = (b:num->num) a` ASSUME_TAC THENL
   [REWRITE_TAC[APPLY_UPDATE_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!a. a IN FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state))
                    ==> ~((b:num->num) a = qq)` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[bvl_to_bviProof_state_rel_def; INJ]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. bv_ok (bvl_state_refs (s:(num#C,FFI)bvl_state)) v
                    ==> adjust_bv ((pp =+ qq) b) v = adjust_bv b v` ASSUME_TAC THENL
   [ASM_MESON_TAC[bv_ok_IMP_adjust_bv_eq]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP B2BP1AUX_state_ok_lemmas) THEN
  MP_TAC(ISPECL [`s:(num#C,FFI)bvl_state`; `b:num->num`; `(pp =+ qq) (b:num->num)`]
    B2BP1AUX_globals_adjust_eq) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `bvl_to_bviProof_state_rel b s (t:(C,FFI)bvi_state)` THEN
  REWRITE_TAC[bvl_to_bviProof_state_rel_def] THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; bvi_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN(fun th -> LABEL_TAC "refs" (CONJUNCT1(CONJUNCT2 th)) THEN
    LABEL_TAC "glob" (CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 th)))) THEN
    STRIP_ASSUME_TAC th) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FDOM_FUPDATE] THEN MATCH_MP_TAC INJ_EXTEND THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `k:num` THEN REWRITE_TAC[FLOOKUP_UPDATE] THEN
    ASM_CASES_TAC `pp:num = k` THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
      ASM_REWRITE_TAC[APPLY_UPDATE_THM] THEN CASE_REWRITE_TAC[] THEN
      REWRITE_TAC[FLOOKUP_UPDATE];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "refs" (MP_TAC o SPEC `k:num`) THEN
    TOP_CASE_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `k IN FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state))` ASSUME_TAC THENL
     [ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT]; ALL_TAC] THEN
    SUBGOAL_THEN `(pp =+ qq) b k = (b:num->num) k /\ ~(qq = b k)`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    TOP_CASE_TAC THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[option_INJ; injectivity "bvl_ref"] THEN
    B2BP1AUX_RES_TAC [] [] THEN ASM_SIMP_TAC[] THEN
    TRY (MATCH_MP_TAC B2BP1AUX_MAP_adjust_eq THEN
         EXISTS_TAC `bvl_state_refs (s:(num#C,FFI)bvl_state)` THEN ASM_REWRITE_TAC[]);
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    USE_THEN "glob" (fun th -> MP_TAC (MATCH_MP (SPEC `p:num` th)
      (ASSUME `bvi_state_global (t:(C,FFI)bvi_state) = SOME p`))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~(qq = p:num)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT]; ALL_TAC] THEN
    ASM_REWRITE_TAC[FLOOKUP_UPDATE; FDOM_FUPDATE] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_INSERT] THEN ASM_MESON_TAC[APPLY_UPDATE_THM; IN_IMAGE];
      EXISTS_TAC `z:num` THEN ASM_REWRITE_TAC[]]];;

(* HOL4 line 1754 *)
let state_rel_add_bytearray = prove
 (`!b2 s5 (t2:(C,FFI)bvi_state) pp qq fl ws.
     bvl_to_bviProof_state_rel b2 s5 t2 /\
     bvl_to_bviProof_state_ok s5 /\
     ~(pp IN FDOM (bvl_state_refs s5)) /\
     ~(qq IN FDOM (bvi_state_refs t2))
     ==> bvl_to_bviProof_state_rel ((pp =+ qq) b2)
           (bvl_state_refs_fupd (K (bvl_state_refs s5 |+ (pp,bvl_ByteArray fl ws))) s5)
           (bvi_state_refs_fupd (K (bvi_state_refs t2 |+ (qq,bvl_ByteArray fl ws))) t2)`,
  MAP_EVERY X_GEN_TAC [`b:num->num`; `s:(num#C,FFI)bvl_state`; `t:(C,FFI)bvi_state`] THEN
  B2BP1AUX_STATE_REL_ADD_TAC);;

(* HOL4 line 1804 *)
let state_rel_add_thunk = prove
 (`!b s (t:(C,FFI)bvi_state) pp qq m v.
     bvl_to_bviProof_state_rel b s t /\
     bvl_to_bviProof_state_ok s /\
     ~(pp IN FDOM (bvl_state_refs s)) /\
     ~(qq IN FDOM (bvi_state_refs t))
     ==> bvl_to_bviProof_state_rel ((pp =+ qq) b)
           (bvl_state_refs_fupd (K (bvl_state_refs s |+ (pp,bvl_Thunk m v))) s)
           (bvi_state_refs_fupd
              (K (bvi_state_refs t |+ (qq,bvl_Thunk m (adjust_bv ((pp =+ qq) b) v)))) t)`,
  B2BP1AUX_STATE_REL_ADD_TAC);;

(* HOL4 line 1853 *)
let bvl_to_bviProof_state_rel_update_thunk = prove
 (`!b s (t:(C,FFI)bvi_state) ptr m v.
     bvl_to_bviProof_state_rel b s t /\
     bvl_to_bviProof_state_ok s /\
     ptr IN FDOM (bvl_state_refs s)
     ==> bvl_to_bviProof_state_rel b
           (bvl_state_refs_fupd (K (bvl_state_refs s |+ (ptr,bvl_Thunk m v))) s)
           (bvi_state_refs_fupd
              (K (bvi_state_refs t |+ (b ptr,bvl_Thunk m (adjust_bv b v)))) t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a. a IN FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state))
                    ==> ((b:num->num) a = b ptr <=> a = ptr)` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[bvl_to_bviProof_state_rel_def; INJ]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `bvl_to_bviProof_state_rel b s (t:(C,FFI)bvi_state)` THEN
  REWRITE_TAC[bvl_to_bviProof_state_rel_def] THEN
  REWRITE_TAC[bvl_state_INFO.ri_accfupds; bvi_state_INFO.ri_accfupds; K_THM] THEN
  DISCH_THEN(fun th -> LABEL_TAC "refs" (CONJUNCT1(CONJUNCT2 th)) THEN
    LABEL_TAC "glob" (CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 th)))) THEN
    STRIP_ASSUME_TAC th) THEN
  SUBGOAL_THEN `(b:num->num) ptr IN FDOM (bvi_state_refs (t:(C,FFI)bvi_state))` ASSUME_TAC THENL
   [ASM_MESON_TAC[INJ]; ALL_TAC] THEN
  ASM_SIMP_TAC[FDOM_FUPDATE; ABSORPTION_RWT] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN REWRITE_TAC[FLOOKUP_UPDATE] THEN
    ASM_CASES_TAC `ptr:num = k` THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[] THEN CASE_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "refs" (MP_TAC o SPEC `k:num`) THEN
    TOP_CASE_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `k IN FDOM (bvl_state_refs (s:(num#C,FFI)bvl_state))` ASSUME_TAC THENL
     [ASM_MESON_TAC[FLOOKUP_DEF; option_DISTINCT]; ALL_TAC] THEN
    SUBGOAL_THEN `~((b:num->num) ptr = b k)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    USE_THEN "glob" (fun th -> MP_TAC (MATCH_MP (SPEC `p:num` th)
      (ASSUME `bvi_state_global (t:(C,FFI)bvi_state) = SOME p`))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~((b:num->num) ptr = p)` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_IMAGE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN EXISTS_TAC `z:num` THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 1883 [local] (HOL4 binds n twice: !n xs n ...) *)
let iEval_bVarBound_extra = prove
 (`!xs n vs (s:(C,FFI)bvi_state) env d.
     bVarBound (LENGTH vs) xs /\ handle_ok xs /\ d = FST (bvl_to_bvi_compile_exps n xs)
     ==> bvi_evaluate (d,APPEND vs env,s) = bvi_evaluate (d,vs,s)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[iEval_bVarBound]);;

(* HOL4 line 1892 [local] *)
let MAP_Num_11 = prove
 (`!(ns:byte list) ns'.
     MAP (\x. bvl_Number (&(val x))) ns = MAP (\x. bvl_Number (&(val x))) ns' <=> ns' = ns`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11; injectivity "bvl_v"; INT_OF_NUM_EQ; VAL_EQ] THEN
  MESON_TAC[]);;

(* HOL4 line 1899 [local] *)
let MAP_Word_11 = prove
 (`!ns ns'. MAP bvl_Word64 ns = MAP bvl_Word64 ns' <=> ns' = ns`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; NOT_CONS_NIL; CONS_11; injectivity "bvl_v"] THEN MESON_TAC[]);;

(* HOL4 line 1905 (b2 is free in HOL4) *)
let IMP_v_to_bytes = prove
 (`!v1 ns b2.
     bvl_v_to_list v1 = SOME (MAP (bvl_Number o int_of_num o (val:byte->num)) ns)
     ==> bvl_v_to_bytes (adjust_bv b2 v1) = SOME ns`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[bvl_v_to_bytes_def; v_to_list_adjust; OPTION_MAP_DEF; MAP_MAP_o;
                  option_INJ] THEN
  REWRITE_TAC[o_DEF; adjust_bv_def] THEN REWRITE_TAC[GSYM o_DEF] THEN
  REWRITE_TAC[o_DEF; MAP_Num_11] THEN REWRITE_TAC[some_EQ]);;

(* HOL4 line 1913 *)
let IMP_v_to_words = prove
 (`!v2 ns' b2.
     bvl_v_to_list v2 = SOME (MAP bvl_Word64 ns')
     ==> bvl_v_to_words (adjust_bv b2 v2) = SOME ns'`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[bvl_v_to_words_def; v_to_list_adjust; OPTION_MAP_DEF; MAP_MAP_o;
                  option_INJ] THEN
  SUBGOAL_THEN `MAP (adjust_bv b2 o bvl_Word64) ns' = MAP bvl_Word64 ns'` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF; adjust_bv_def] THEN REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  REWRITE_TAC[MAP_Word_11; some_EQ]);;

(* HOL4 line 1921: val sorted_lt_append = Q.ISPEC (<) SORTED_APPEND |>      *)
(* SIMP_RULE std_ss [transitive_LESS] (its resulting statement) *)
let sorted_lt_append = prove
 (`!(L1:num list) L2.
     SORTED (<) (APPEND L1 L2) <=>
     SORTED (<) L1 /\ SORTED (<) L2 /\ (!x y. MEM x L1 ==> MEM y L2 ==> x < y)`,
  MATCH_ACCEPT_TAC(MATCH_MP SORTED_APPEND transitive_LESS));;

(* HOL4 line 1925 *)
let aux_code_installed_sublist = prove
 (`!(aux:(num#A#B)list) ls.
     IS_SUBLIST ls aux /\ ALL_DISTINCT (MAP FST ls)
     ==> aux_code_installed aux (fromAList ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[aux_code_installed_def] THEN
  SPEC_TAC(`h:num#A#B`,`h:num#A#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`name:num`; `arity:A`; `body:B`] THEN
  REWRITE_TAC[aux_code_installed_def; IS_SUBLIST_DEF] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[lookup_fromAList] THEN MATCH_MP_TAC ALOOKUP_ALL_DISTINCT_MEM THEN
    ASM_REWRITE_TAC[MEM_APPEND; MEM];
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[IS_SUBLIST_DEF] THEN
      MAP_EVERY EXISTS_TAC [`APPEND l [(name,arity,body):num#A#B]`; `l':(num#A#B)list`] THEN
      ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND];
      FIRST_ASSUM ACCEPT_TAC]]);;

(* local helpers for compile_exps_aux_sorted (not in HOL4): the invariant *)
(* of the aux code for SmartAppend and compile_aux                         *)
let B2BP1AUX_between_mono = prove
 (`!a b a' b' (l:num list).
     ALL (misc_between a b) l /\ a' <= a /\ b <= b' ==> ALL (misc_between a' b') l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_comb o concl) o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "ALL"
                     with Failure _ -> false)) THEN
  MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[misc_between_def] THEN ASM_ARITH_TAC);;

let B2BP1AUX_aux_Q_nil = prove
 (`!n. SORTED (<) (MAP FST (append (Nil:(num#num#bvi_exp)app_list))) /\
       ALL (\x. ?n. x = bvl_num_stubs + bvl_to_bvi_namespaces * n + 1)
         (MAP FST (append (Nil:(num#num#bvi_exp)app_list))) /\
       ALL (misc_between (bvl_num_stubs + bvl_to_bvi_namespaces * n)
              (bvl_num_stubs + bvl_to_bvi_namespaces * n))
         (MAP FST (append (Nil:(num#num#bvi_exp)app_list))) /\
       n <= n`,
  REWRITE_TAC[append_thm; MAP; ALL; SORTED_DEF; LE_REFL]);;

let B2BP1AUX_aux_Q_append = prove
 (`!n (a1:(num#num#bvi_exp)app_list) n1 a2 n2.
     (SORTED (<) (MAP FST (append a1)) /\
      ALL (\x. ?n. x = bvl_num_stubs + bvl_to_bvi_namespaces * n + 1) (MAP FST (append a1)) /\
      ALL (misc_between (bvl_num_stubs + bvl_to_bvi_namespaces * n)
             (bvl_num_stubs + bvl_to_bvi_namespaces * n1)) (MAP FST (append a1)) /\
      n <= n1) /\
     (SORTED (<) (MAP FST (append a2)) /\
      ALL (\x. ?n. x = bvl_num_stubs + bvl_to_bvi_namespaces * n + 1) (MAP FST (append a2)) /\
      ALL (misc_between (bvl_num_stubs + bvl_to_bvi_namespaces * n1)
             (bvl_num_stubs + bvl_to_bvi_namespaces * n2)) (MAP FST (append a2)) /\
      n1 <= n2)
     ==> SORTED (<) (MAP FST (append (SmartAppend a1 a2))) /\
         ALL (\x. ?n. x = bvl_num_stubs + bvl_to_bvi_namespaces * n + 1)
           (MAP FST (append (SmartAppend a1 a2))) /\
         ALL (misc_between (bvl_num_stubs + bvl_to_bvi_namespaces * n)
                (bvl_num_stubs + bvl_to_bvi_namespaces * n2))
           (MAP FST (append (SmartAppend a1 a2))) /\
         n <= n2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[append_SmartAppend; MAP_APPEND; ALL_APPEND] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[sorted_lt_append] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`ALL (misc_between (bvl_num_stubs + bvl_to_bvi_namespaces * n)
             (bvl_num_stubs + bvl_to_bvi_namespaces * n1)) (MAP FST (append (a1:(num#num#bvi_exp)app_list)))`;
      `ALL (misc_between (bvl_num_stubs + bvl_to_bvi_namespaces * n1)
             (bvl_num_stubs + bvl_to_bvi_namespaces * n2)) (MAP FST (append (a2:(num#num#bvi_exp)app_list)))`] THEN
    REWRITE_TAC[GSYM ALL_MEM; misc_between_def] THEN REPEAT STRIP_TAC THEN
    RES_TAC THEN B2BP1AUX_ARITH_TAC;
    MATCH_MP_TAC B2BP1AUX_between_mono THEN
    MAP_EVERY EXISTS_TAC [`bvl_num_stubs + bvl_to_bvi_namespaces * n`;
                          `bvl_num_stubs + bvl_to_bvi_namespaces * n1`] THEN
    ASM_REWRITE_TAC[LE_REFL; LE_ADD_LCANCEL] THEN
    REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN B2BP1AUX_ARITH_TAC;
    MATCH_MP_TAC B2BP1AUX_between_mono THEN
    MAP_EVERY EXISTS_TAC [`bvl_num_stubs + bvl_to_bvi_namespaces * n1`;
                          `bvl_num_stubs + bvl_to_bvi_namespaces * n2`] THEN
    ASM_REWRITE_TAC[LE_REFL; LE_ADD_LCANCEL] THEN
    REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN B2BP1AUX_ARITH_TAC;
    B2BP1AUX_ARITH_TAC]);;

let B2BP1AUX_aux_Q_aux = prove
 (`!n (a:(num#num#bvi_exp)app_list) n2 k e.
     (SORTED (<) (MAP FST (append a)) /\
      ALL (\x. ?n. x = bvl_num_stubs + bvl_to_bvi_namespaces * n + 1) (MAP FST (append a)) /\
      ALL (misc_between (bvl_num_stubs + bvl_to_bvi_namespaces * n)
             (bvl_num_stubs + bvl_to_bvi_namespaces * n2)) (MAP FST (append a)) /\
      n <= n2)
     ==> SORTED (<) (MAP FST (append (SmartAppend a (compile_aux (n2,k,e))))) /\
         ALL (\x. ?n. x = bvl_num_stubs + bvl_to_bvi_namespaces * n + 1)
           (MAP FST (append (SmartAppend a (compile_aux (n2,k,e))))) /\
         ALL (misc_between (bvl_num_stubs + bvl_to_bvi_namespaces * n)
                (bvl_num_stubs + bvl_to_bvi_namespaces * (n2 + 1)))
           (MAP FST (append (SmartAppend a (compile_aux (n2,k,e))))) /\
         n <= n2 + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC B2BP1AUX_aux_Q_append THEN
  EXISTS_TAC `n2:num` THEN ASM_REWRITE_TAC[compile_aux_def; append_thm; MAP; ALL;
    SORTED_DEF; misc_between_def] THEN
  REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN
  CONJ_TAC THENL [MESON_TAC[]; ARITH_TAC]);;

(* close a goal of the aux invariant (the conclusion of                     *)
(* compile_exps_aux_sorted) for a combination of SmartAppend and compile_aux *)
(* from the invariant facts of the parts in the assumptions                  *)
let B2BP1AUX_AUXQ_TAC : tactic =
  let lo_of m = mk_binop `(+):num->num->num` `bvl_num_stubs`
                  (mk_binop `( * ):num->num->num` `bvl_to_bvi_namespaces` m) in
  let name_of t = try fst(dest_const(fst(strip_comb t))) with Failure _ -> "" in
  let rec bound asl m a =
    try let is_fact (_,th) =
          try let c = concl th in
              name_of c = "ALL" &&
              lhand(rand(rator c)) = lo_of m && rand(rand(rand c)) = a
          with Failure _ -> false in
        let (_,th) = find is_fact asl in
        rand(rand(rand(rand(rator(concl th)))))
    with Failure _ ->
      if name_of a <> "SmartAppend" then failwith "bound" else
      let x = lhand a and y = rand a in
      let m1 = bound asl m x in
      if name_of y = "compile_aux"
      then mk_binop `(+):num->num->num` (fst(dest_pair(rand y))) `1`
      else bound asl m1 y in
  let rec tac : tactic = fun (asl,w as gl) ->
    let c3 = lhand(rand(rand w)) in
    let lo = lhand(rand(rator c3)) in
    let m = rand(rand lo) in
    let l = rand(rand(rand c3)) in
    if name_of l = "SmartAppend" then
      if name_of (rand l) = "compile_aux" then
        (MATCH_MP_TAC B2BP1AUX_aux_Q_aux THEN tac) gl
      else
        let m1 = bound asl m (lhand l) in
        (MATCH_MP_TAC B2BP1AUX_aux_Q_append THEN EXISTS_TAC m1 THEN
         CONJ_TAC THEN tac) gl
    else
      (MATCH_ACCEPT_TAC B2BP1AUX_aux_Q_nil ORELSE
       (REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC)) gl in
  tac;;

(* HOL4 line 1957 *)
let compile_exps_aux_sorted = prove
 (`!n es c aux n1.
     bvl_to_bvi_compile_exps n es = (c,aux,n1)
     ==> SORTED (<) (MAP FST (append aux)) /\
         ALL (\x. ?n. x = bvl_num_stubs + bvl_to_bvi_namespaces * n + 1) (MAP FST (append aux)) /\
         ALL (misc_between (bvl_num_stubs + bvl_to_bvi_namespaces * n)
                (bvl_num_stubs + bvl_to_bvi_namespaces * n1))
           (MAP FST (append aux)) /\
         n <= n1`,
  MATCH_MP_TAC bvl_to_bvi_compile_exps_ind THEN REPEAT CONJ_TAC THEN
  B2BP1AUX_IND_STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  PURE_ONCE_REWRITE_TAC[bvl_to_bvi_compile_exps_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT (B2BP1AUX_PAIR_SPLIT_TAC "bvl_to_bvi_compile_exps" ORELSE
          B2BP1AUX_PAIR_SPLIT_TAC "destLet" ORELSE COND_CASES_TAC) THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  B2BP1AUX_RES_TAC [] [] THEN B2BP1AUX_AUXQ_TAC);;

(* HOL4 line 1971 *)
let bvl_to_bviProof_in_ns_def = cake_def
  `bvl_to_bviProof_in_ns k n <=> n MOD bvl_to_bvi_namespaces = k`;;

(* local helpers for the namespace lemmas (not in HOL4): nss = 4 and    *)
(* num_stubs = 72 = 18 * 4                                                *)
let B2BP1AUX_NSS_RWS = [bvl_to_bviProof_in_ns_def; bvl_to_bvi_namespaces_def];;

let B2BP1AUX_num_stubs = prove
 (`bvl_num_stubs = 18 * 4`,
  REWRITE_TAC[bvl_num_stubs_def; data_num_stubs_def; word_num_stubs_def;
              stack_num_stubs_def] THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 1975 [simp] *)
let nss_in_ns = prove
 (`!k. bvl_to_bviProof_in_ns k bvl_to_bvi_namespaces <=> k = 0`,
  REWRITE_TAC B2BP1AUX_NSS_RWS THEN CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[]);;

let _ = cake_add_simps [nss_in_ns];;

(* HOL4 line 1981 [simp] *)
let mult_nss_in_ns = prove
 (`!k m. bvl_to_bviProof_in_ns k (m * bvl_to_bvi_namespaces) <=> k = 0`,
  REWRITE_TAC B2BP1AUX_NSS_RWS THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  SIMP_TAC[MOD_MULT; ARITH_EQ] THEN MESON_TAC[]);;

let _ = cake_add_simps [mult_nss_in_ns];;

(* HOL4 line 1987 [simp] *)
let mult_nss_in_ns_1 = prove
 (`!k m. bvl_to_bviProof_in_ns k (m * bvl_to_bvi_namespaces + 1) <=> k = 1`,
  REWRITE_TAC(MOD_MULT_ADD :: B2BP1AUX_NSS_RWS) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MESON_TAC[]);;

let _ = cake_add_simps [mult_nss_in_ns_1];;

(* HOL4 line 1993 [simp] *)
let mult_nss_in_ns_2 = prove
 (`!k m. bvl_to_bviProof_in_ns k (m * bvl_to_bvi_namespaces + 2) <=> k = 2`,
  REWRITE_TAC(MOD_MULT_ADD :: B2BP1AUX_NSS_RWS) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MESON_TAC[]);;

let _ = cake_add_simps [mult_nss_in_ns_2];;

(* HOL4 line 1999 *)
let in_ns_1_add_1 = prove
 (`!x. bvl_to_bviProof_in_ns 0 x ==> bvl_to_bviProof_in_ns 1 (x + 1)`,
  REWRITE_TAC B2BP1AUX_NSS_RWS THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 2007: val ODD_num_stubs = EVAL in_ns 0 num_stubs (its         *)
(* resulting statement) *)
let ODD_num_stubs = prove
 (`bvl_to_bviProof_in_ns 0 bvl_num_stubs <=> T`,
  REWRITE_TAC(B2BP1AUX_num_stubs :: B2BP1AUX_NSS_RWS) THEN CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 2009 [simp] *)
let in_ns_add_num_stubs = prove
 (`!k x. bvl_to_bviProof_in_ns k (bvl_num_stubs + x) <=> bvl_to_bviProof_in_ns k x`,
  REWRITE_TAC(B2BP1AUX_num_stubs :: MOD_MULT_ADD :: B2BP1AUX_NSS_RWS));;

let _ = cake_add_simps [in_ns_add_num_stubs];;

(* a local helper (not in HOL4): the names of the aux code are not of the   *)
(* form nss * name + num_stubs                                               *)
let B2BP1AUX_aux_ALOOKUP_NONE = prove
 (`!n0 e c aux n1 name.
     bvl_to_bvi_compile_exps n0 e = (c,aux,n1)
     ==> ALOOKUP (append aux) (bvl_to_bvi_namespaces * name + bvl_num_stubs) = NONE`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o
    MATCH_MP compile_exps_aux_sorted) THEN
  REWRITE_TAC[GSYM ALL_MEM; ALOOKUP_NONE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `name * bvl_to_bvi_namespaces = n * bvl_to_bvi_namespaces + 1` MP_TAC THENL
   [POP_ASSUM MP_TAC THEN ARITH_TAC;
    DISCH_THEN(MP_TAC o AP_TERM `bvl_to_bviProof_in_ns 0`) THEN
    REWRITE_TAC[mult_nss_in_ns; mult_nss_in_ns_1; ARITH_EQ]]);;

(* HOL4 line 2017 [local] *)
let compile_list_imp = prove
 (`!n prog code n' name arity exp.
     bvl_to_bvi_compile_list n prog = (code,n') /\ ALOOKUP prog name = SOME (arity,exp)
     ==> ?n0 c aux n1.
           bvl_to_bvi_compile_exps n0 [exp] = ([c],aux,n1) /\
           ALOOKUP (append code) (bvl_to_bvi_namespaces * name + bvl_num_stubs) =
             SOME (arity,bvi_let_compile_exp c) /\
           IS_SUBLIST (append code) (append aux)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALOOKUP_THM; option_DISTINCT] THEN
  SPEC_TAC(`h:num#num#bvl_exp`,`h:num#num#bvl_exp`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p0:num`; `p1:num`; `p2:bvl_exp`] THEN
  REWRITE_TAC[ALOOKUP_THM; bvl_to_bvi_compile_list_def; bvl_to_bvi_compile_single_def] THEN
  REPEAT GEN_TAC THEN
  B2BP1AUX_PAIR_SPLIT_TAC "bvl_to_bvi_compile_exps" THEN
  B2BP1AUX_PAIR_SPLIT_TAC "bvl_to_bvi_compile_list" THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  REWRITE_TAC[append_SmartAppend; append_thm; ALOOKUP_APPEND; ALOOKUP_THM] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `y:bvi_exp` o MATCH_MP bvl_to_bvi_compile_exps_SING) THEN
  SUBGOAL_THEN `bvl_num_stubs + bvl_to_bvi_namespaces * p0 =
                bvl_to_bvi_namespaces * name + bvl_num_stubs <=> p0 = name`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `p0:num = name` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; PAIR_EQ]) THEN
    REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC o check (is_conj o concl))) THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `y:bvi_exp`; `v':(num#num#bvi_exp)app_list`;
                          `v'':num`] THEN
    ASM_REWRITE_TAC[HD; IS_SUBLIST_DEF] THEN
    MAP_EVERY EXISTS_TAC [`[bvl_num_stubs + bvl_to_bvi_namespaces * name,(arity:num),
                            bvi_let_compile_exp y]`; `append (v''':(num#num#bvi_exp)app_list)`] THEN
    REWRITE_TAC[APPEND_ASSOC];
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(p0:num = name)`]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP B2BP1AUX_aux_ALOOKUP_NONE th]) THEN
    CASE_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`v'':num`; `v''':(num#num#bvi_exp)app_list`; `n':num`;
      `name:num`; `arity:num`; `exp:bvl_exp`]) THEN
    ASM_REWRITE_TAC[IS_SUBLIST_DEF] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`n0:num`; `c:bvi_exp`; `aux:(num#num#bvi_exp)app_list`; `n1:num`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`APPEND (APPEND [bvl_num_stubs + bvl_to_bvi_namespaces * p0,(p1:num),
                            bvi_let_compile_exp (HD [y])] (append (v':(num#num#bvi_exp)app_list))) l`;
                          `l':(num#num#bvi_exp)list`] THEN
    REWRITE_TAC[APPEND_ASSOC]]);;

(* HOL4 line 2061 [local] *)
let nss_lemma = prove
 (`!n k. ~(n * bvl_to_bvi_namespaces = k * bvl_to_bvi_namespaces + 1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD bvl_to_bvi_namespaces`) THEN
  REWRITE_TAC[MOD_MULT_ADD; bvl_to_bvi_namespaces_def] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN SIMP_TAC[MOD_MULT; ARITH_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* HOL4 line 2070 [local] *)
let in_ns_0_simp = prove
 (`!p_1. bvl_to_bviProof_in_ns 0 (bvl_to_bvi_namespaces * p_1 + bvl_num_stubs)`,
  REWRITE_TAC(B2BP1AUX_num_stubs :: B2BP1AUX_NSS_RWS) THEN GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `4 * p + 18 * 4 = (p + 18) * 4`; MOD_MULT_ADD] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN SIMP_TAC[MOD_MULT; ARITH_EQ]);;

(* local helpers for compile_inc_lemma (not in HOL4): names of the form     *)
(* num_stubs + nss * k are in namespace 0, aux names in namespace 1          *)
let B2BP1AUX_nss_comm = prove
 (`!m. bvl_to_bvi_namespaces * m = m * bvl_to_bvi_namespaces`,
  REWRITE_TAC[MULT_SYM]);;

let B2BP1AUX_in_ns_stub = prove
 (`(!k m. bvl_to_bviProof_in_ns k (bvl_num_stubs + bvl_to_bvi_namespaces * m) <=> k = 0) /\
   (!k m. bvl_to_bviProof_in_ns k (bvl_num_stubs + m * bvl_to_bvi_namespaces) <=> k = 0) /\
   (!k m. bvl_to_bviProof_in_ns k (bvl_num_stubs + bvl_to_bvi_namespaces * m + 1) <=> k = 1)`,
  REWRITE_TAC[in_ns_add_num_stubs; GSYM ADD_ASSOC; B2BP1AUX_nss_comm] THEN
  REWRITE_TAC[mult_nss_in_ns; mult_nss_in_ns_1]);;

let B2BP1AUX_in_ns_unique = prove
 (`!p. ~(bvl_to_bviProof_in_ns 0 p /\ bvl_to_bviProof_in_ns 1 p)`,
  REWRITE_TAC[bvl_to_bviProof_in_ns_def] THEN ARITH_TAC);;

let B2BP1AUX_stub_name_11 = prove
 (`!p q. bvl_num_stubs + p * bvl_to_bvi_namespaces = bvl_num_stubs + bvl_to_bvi_namespaces * q
         <=> p = q`,
  REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN ARITH_TAC);;

(* compile_inc_lemma for compile_list, by induction over the program (HOL4: *)
(* Induct_on prog1 in the proof of compile_inc_lemma) *)
let B2BP1AUX_compile_list_ok = prove
 (`!prog1 next1 p1 n1.
     bvl_to_bvi_compile_list next1 prog1 = (p1,n1)
     ==> (ALL_DISTINCT (MAP FST prog1) ==> ALL_DISTINCT (MAP FST (append p1))) /\
         next1 <= n1 /\
         (!p. MEM (bvl_num_stubs + p * bvl_to_bvi_namespaces) (MAP FST (append p1))
              ==> MEM p (MAP FST prog1)) /\
         (!p. MEM p (MAP FST (append p1))
              ==> if bvl_to_bviProof_in_ns 0 p then (?q. bvl_num_stubs + q * bvl_to_bvi_namespaces = p)
                  else (bvl_to_bviProof_in_ns 1 p /\ bvl_num_stubs + bvl_to_bvi_namespaces * next1 <= p /\
                        p < bvl_num_stubs + bvl_to_bvi_namespaces * n1))`,
  (LIST_INDUCT_TAC THENL
   [REWRITE_TAC[bvl_to_bvi_compile_list_def; PAIR_EQ] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[append_thm; MAP; MEM; ALL_DISTINCT; LE_REFL];
    ALL_TAC] THEN
  SPEC_TAC(`h:num#num#bvl_exp`,`h:num#num#bvl_exp`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`name:num`; `arity:num`; `exp:bvl_exp`] THEN
  REWRITE_TAC[bvl_to_bvi_compile_list_def; bvl_to_bvi_compile_single_def] THEN
  REPEAT GEN_TAC THEN
  B2BP1AUX_PAIR_SPLIT_TAC "bvl_to_bvi_compile_exps" THEN
  B2BP1AUX_PAIR_SPLIT_TAC "bvl_to_bvi_compile_list" THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP compile_exps_aux_sorted) THEN
  B2BP1AUX_RES_TAC [] [] THEN
  REWRITE_TAC[append_SmartAppend; append_thm; MAP_APPEND; MAP; APPEND; MEM_APPEND; MEM;
              ALL_DISTINCT; ALL_DISTINCT_APPEND]) THEN
  (RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM; misc_between_def]) THEN
   SUBGOAL_THEN `ALL_DISTINCT (MAP FST (append (v':(num#num#bvi_exp)app_list)))` ASSUME_TAC THENL
    [MATCH_MP_TAC(MATCH_MP SORTED_ALL_DISTINCT
       (prove(`irreflexive ((<):num->num->bool) /\ transitive ((<):num->num->bool)`,
              REWRITE_TAC[irreflexive_DEF; transitive_DEF] THEN ARITH_TAC))) THEN
     ASM_REWRITE_TAC[];
     ALL_TAC] THEN
   SUBGOAL_THEN `!e. MEM e (MAP FST (append (v':(num#num#bvi_exp)app_list))) ==> ~bvl_to_bviProof_in_ns 0 e`
     ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN RES_TAC THEN UNDISCH_TAC `bvl_to_bviProof_in_ns 0 e` THEN
     ASM_REWRITE_TAC[B2BP1AUX_in_ns_stub; ARITH_EQ];
     ALL_TAC] THEN
   SUBGOAL_THEN `!e. MEM e (MAP FST (append (v':(num#num#bvi_exp)app_list))) ==>
                     ~MEM e (MAP FST (append (v''':(num#num#bvi_exp)app_list)))`
     ASSUME_TAC THENL
    [REPEAT STRIP_TAC THEN RES_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
     B2BP1AUX_ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `~MEM (bvl_num_stubs + bvl_to_bvi_namespaces * name)
                     (MAP FST (append (v':(num#num#bvi_exp)app_list)))` ASSUME_TAC THENL
    [DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `bvl_num_stubs + bvl_to_bvi_namespaces * name` o
       check (fun th -> can (find_term (fun t -> t = `bvl_to_bviProof_in_ns 0`)) (concl th) &&
                        is_forall (concl th) && not (is_cond (rand(snd(strip_forall(concl th))))))) THEN
     ASM_REWRITE_TAC[B2BP1AUX_in_ns_stub];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC) THENL
  [(STRIP_TAC THEN CONJ_TAC THENL
    [DISCH_TAC THEN UNDISCH_TAC `~MEM name (MAP FST (t:(num#num#bvl_exp)list))` THEN
     REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[];
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);
   (B2BP1AUX_ARITH_TAC);
   (GEN_TAC THEN STRIP_TAC THENL
    [DISJ1_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[B2BP1AUX_stub_name_11]) THEN
     ASM_REWRITE_TAC[];
     MP_TAC(SPEC `bvl_num_stubs + p * bvl_to_bvi_namespaces` (ASSUME
       `!e. MEM e (MAP FST (append (v':(num#num#bvi_exp)app_list))) ==> ~bvl_to_bviProof_in_ns 0 e`)) THEN
     REWRITE_TAC[B2BP1AUX_in_ns_stub] THEN ASM_REWRITE_TAC[];
     DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);
   (GEN_TAC THEN STRIP_TAC THENL
    [ASM_REWRITE_TAC[B2BP1AUX_in_ns_stub] THEN EXISTS_TAC `name:num` THEN
     REWRITE_TAC[MULT_SYM];
     RES_TAC THEN ASM_REWRITE_TAC[B2BP1AUX_in_ns_stub; ARITH_EQ] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[bvl_to_bvi_namespaces_def]) THEN
     REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN B2BP1AUX_ARITH_TAC;
     FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
       `MEM p (MAP FST (append (v''':(num#num#bvi_exp)app_list)))`)) THEN
     COND_CASES_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[bvl_to_bvi_namespaces_def]) THEN
     REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN B2BP1AUX_ARITH_TAC])]);;

(* HOL4 line 2077 *)
let compile_inc_lemma = prove
 (`!next1 prog1 next2 prog2.
     bvl_to_bvi_compile_inc next1 prog1 = (next2,prog2)
     ==> (ALL_DISTINCT (MAP FST prog1) ==> ALL_DISTINCT (MAP FST prog2)) /\
         next1 <= next2 /\
         (!p. MEM (bvl_num_stubs + p * bvl_to_bvi_namespaces) (MAP FST prog2)
              ==> MEM p (MAP FST prog1)) /\
         (!p. MEM p (MAP FST prog2)
              ==> if bvl_to_bviProof_in_ns 0 p then (?q. bvl_num_stubs + q * bvl_to_bvi_namespaces = p)
                  else (bvl_to_bviProof_in_ns 1 p /\ bvl_num_stubs + bvl_to_bvi_namespaces * next1 <= p /\
                        p < bvl_num_stubs + bvl_to_bvi_namespaces * next2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bvl_to_bvi_compile_inc_def] THEN
  B2BP1AUX_PAIR_SPLIT_TAC "bvl_to_bvi_compile_list" THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN
  FIRST_X_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP B2BP1AUX_compile_list_ok));;

(* HOL4 line 2123 *)
let compile_inc_next = prove
 (`!next1 prog1 next2 prog2.
     bvl_to_bvi_compile_inc next1 prog1 = (next2,prog2) ==> next1 <= next2`,
  MESON_TAC[compile_inc_lemma]);;

(* HOL4 line 2130 *)
let compile_inc_DISTINCT = prove
 (`!next1 prog1 next2 prog2.
     bvl_to_bvi_compile_inc next1 prog1 = (next2,prog2) /\ ALL_DISTINCT (MAP FST prog1)
     ==> ALL_DISTINCT (MAP FST prog2)`,
  MESON_TAC[compile_inc_lemma]);;

(* HOL4 line 2138 (in_ns_1 x and in_ns_0 x written out) *)
let compile_inc_next_range = prove
 (`!next1 prog1 next2 prog2 x.
     bvl_to_bvi_compile_inc next1 prog1 = (next2,prog2) /\ MEM x (MAP FST prog2)
     ==> if x MOD bvl_to_bvi_namespaces = 1
         then bvl_num_stubs + bvl_to_bvi_namespaces * next1 <= x /\
              x < bvl_num_stubs + bvl_to_bvi_namespaces * next2
         else (x MOD bvl_to_bvi_namespaces = 0 /\ bvl_num_stubs <= x /\
               MEM ((x - bvl_num_stubs) DIV bvl_to_bvi_namespaces) (MAP FST prog1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP compile_inc_lemma) THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP
    (ASSUME `MEM x (MAP FST (prog2:(num#num#bvi_exp)list))`)) THEN
  REWRITE_TAC[bvl_to_bviProof_in_ns_def] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THENL
   [DISCH_THEN(X_CHOOSE_THEN `q:num` (SUBST_ALL_TAC o SYM)) THEN
    REWRITE_TAC[ADD_SUB2; LE_ADD] THEN
    SIMP_TAC[bvl_to_bvi_namespaces_def; DIV_MULT; ARITH_EQ; ONCE_REWRITE_RULE[MULT_SYM] DIV_MULT] THEN
    REWRITE_TAC[GSYM bvl_to_bvi_namespaces_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 2154 [local] *)
let not_in_ns_1 = prove
 (`!name. ~((bvl_num_stubs + name * bvl_to_bvi_namespaces) MOD bvl_to_bvi_namespaces = 1)`,
  REWRITE_TAC(B2BP1AUX_num_stubs :: B2BP1AUX_NSS_RWS) THEN GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `18 * 4 + n * 4 = (n + 18) * 4`] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN SIMP_TAC[MOD_MULT; ARITH_EQ]);;

(* HOL4 line 2160 [local] *)
let names_nss_DIV_nss = prove
 (`!name. (name * bvl_to_bvi_namespaces) DIV bvl_to_bvi_namespaces = name`,
  REWRITE_TAC[bvl_to_bvi_namespaces_def] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

(* HOL4 line 2169 [local] *)
let call_SOME_handler_result = prove
 (CASE_TERM
  `!(f:A->B) (g:C->bvl_v) r (t:D).
     (match map_result f (\v. Exn (g v)) r with
        Rval v6 -> (Rval v6,t)
      | Rerr (Rraise (Exn v14)) -> (Rerr (Rraise (Exn v14)),t)
      | Rerr (Rraise (Ret v15)) -> (Rerr (Rabort Rtype_error),t)
      | Rerr (Rabort v11) -> (Rerr (Rabort v11),t)) =
     (map_result f (\v. Exn (g v)) r,t)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `r:(A,C)result` (cases "result")) THEN
  REWRITE_TAC[map_result_def] THEN CASE_REWRITE_TAC[] THEN
  TRY (STRUCT_CASES_TAC(ISPEC `a:(C)error_result` (cases "error_result"))) THEN
  REWRITE_TAC[map_error_result_def] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 2182: fun note_tac (an ML tactic) *)
(* HOL4 line 2184: val goal (an ML term: the statement of                   *)
(* compile_exps_correct, part 2, as a lambda over (xs,env,s1))               *)
