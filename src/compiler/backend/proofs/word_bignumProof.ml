(* ========================================================================= *)
(* word_bignumProof: port of HOL4 compiler/backend/proofs/                   *)
(* word_bignumProofScript.sml (CakeML v3479).                                *)
(* Correctness proof for word_bignum.                                        *)
(* The 60 theorems mc_X_corr_thm (HOL4: made by the ML function             *)
(* derive_corr_thm) are derived by WBIGPAUX_derive_corr, a symbolic         *)
(* execution of the mini code; compile_thm is proved with one lemma per     *)
(* rule of Eval (WBIGPAUX_compile_Skip ... WBIGPAUX_compile_LoopBody2).     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mllist.ml";;
needs "semantics/ast.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "hol4/tailrec.ml";;
needs "hol4/mc_multiword.ml";;
needs "compiler/backend/backend_common.ml";;
needs "hol4/set_sep.ml";;
needs "compiler/backend/word_bignum.ml";;

prioritize_num();;
type_invention_error := true;;
(* ------------------------------------------------------------------------- *)
(* semantics of the little language                                          *)
(* ------------------------------------------------------------------------- *)

let word_bignumProof_state_INFO = cake_record "word_bignumProof_state"
  ["regs","(num,A word)fmap";
   "arrays","address->(A word)list";
   "clock","num"];;

let word_bignumProof_state_component_equality =
  word_bignumProof_state_INFO.ri_component_equality;;

let eval_exp_def = cake_def
  `(eval_exp (s:(A)word_bignumProof_state) (wl_Const w) = w) /\
   (eval_exp s (wl_Var v) = FAPPLY (word_bignumProof_state_regs s) v) /\
   (eval_exp s (wl_Op asm_Add [x1;x2]) = word_add (eval_exp s x1) (eval_exp s x2)) /\
   (eval_exp s (wl_Op asm_Sub [x1;x2]) = word_sub (eval_exp s x1) (eval_exp s x2)) /\
   (eval_exp s (wl_Op asm_And [x1;x2]) = word_and (eval_exp s x1) (eval_exp s x2)) /\
   (eval_exp s (wl_Op asm_Or [x1;x2]) = word_or (eval_exp s x1) (eval_exp s x2)) /\
   (eval_exp s (wl_Op asm_Xor [x1;x2]) = word_xor (eval_exp s x1) (eval_exp s x2)) /\
   (eval_exp s (wl_Shift Lsl x1 x2) = word_shl (eval_exp s x1) (val (eval_exp s x2))) /\
   (eval_exp s (wl_Shift Asr x1 x2) = word_ishr (eval_exp s x1) (val (eval_exp s x2))) /\
   (eval_exp s (wl_Shift Lsr x1 x2) = word_ushr (eval_exp s x1) (val (eval_exp s x2))) /\
   (eval_exp s (wl_Shift Ror x1 x2) = word_ror (eval_exp s x1) (val (eval_exp s x2)))`;;

let eval_exp_pre_def = cake_def
  `(eval_exp_pre (s:(A)word_bignumProof_state) (wl_Const w) <=> T) /\
   (eval_exp_pre s (wl_Var v) <=> v IN FDOM (word_bignumProof_state_regs s)) /\
   (eval_exp_pre s (wl_Op _ [x;y]) <=> eval_exp_pre s x /\ eval_exp_pre s y) /\
   (eval_exp_pre s (wl_Shift sh x1 x2) <=>
      eval_exp_pre s x1 /\ eval_exp_pre s x2 /\ val (eval_exp s x2) < 32) /\
   (eval_exp_pre s _ <=> F)`;;

let eval_ri_pre_def = cake_def
  `(eval_ri_pre (s:(A)word_bignumProof_state) (Reg r) <=>
      eval_exp_pre s (wl_Var r:(A)wl_exp)) /\
   (eval_ri_pre s (Imm (w:A word)) <=> T)`;;

let eval_ri_def = cake_def
  `(eval_ri (s:(A)word_bignumProof_state) (Reg r) = eval_exp s (wl_Var r)) /\
   (eval_ri s (Imm w) = w)`;;

let word_bignumProof_dec_clock_def = cake_def
  `word_bignumProof_dec_clock (s:(A)word_bignumProof_state) =
     word_bignumProof_state_clock_fupd (K (word_bignumProof_state_clock s - 1)) s`;;

let reg_write_def = cake_def
  `(reg_write v NONE (s:(A)word_bignumProof_state) =
      word_bignumProof_state_regs_fupd (K (word_bignumProof_state_regs s \\ v)) s) /\
   (reg_write n (SOME w) s =
      word_bignumProof_state_regs_fupd (K (word_bignumProof_state_regs s |+ (n,w))) s)`;;

let delete_vars_def = cake_def
  `(delete_vars [] (s:(A)word_bignumProof_state) = s) /\
   (delete_vars (CONS v vs) s = reg_write v NONE (delete_vars vs s))`;;

let array_write_def = cake_def
  `array_write n v (s:(A)word_bignumProof_state) =
     word_bignumProof_state_arrays_fupd (K ((n =+ v) (word_bignumProof_state_arrays s))) s`;;

let clock_write_def = cake_def
  `clock_write l (s:(A)word_bignumProof_state) = word_bignumProof_state_clock_fupd (K l) s`;;

let word_bignumProof_copy_vars_def = cake_def
  `(word_bignumProof_copy_vars [] (s:(num,A word)fmap) (t:(A)word_bignumProof_state) =
      SOME t) /\
   (word_bignumProof_copy_vars (CONS n ns) s t =
      match FLOOKUP s n with
        NONE -> NONE
      | SOME x -> word_bignumProof_copy_vars ns s (reg_write n (SOME x) t))`;;

let eval_rules,eval_ind,eval_cases,eval_strongind = cake_inductive
  `(!r (s:(A)word_bignumProof_state).
      word_bignumProof_Eval r s word_bignum_Skip (INR s)) /\
   (!r (s:(A)word_bignumProof_state).
      word_bignumProof_Eval r s word_bignum_Continue (INL s)) /\
   (!r vs (s:(A)word_bignumProof_state).
      word_bignumProof_Eval r s (Delete vs) (INR (delete_vars vs s))) /\
   (!r (s:(A)word_bignumProof_state) x n.
      eval_exp_pre s x
      ==> word_bignumProof_Eval r s (word_bignum_Assign n x)
            (INR (reg_write n (SOME (eval_exp s x)) s))) /\
   (!r (s1:(A)word_bignumProof_state) s2 s3 p1 p2.
      word_bignumProof_Eval r s1 p1 (INR s2) /\ word_bignumProof_Eval r s2 p2 s3
      ==> word_bignumProof_Eval r s1 (word_bignum_Seq p1 p2) s3) /\
   (!rec (s1:(A)word_bignumProof_state) c r ri p1 p2 s2.
      r IN FDOM (word_bignumProof_state_regs s1) /\ eval_ri_pre s1 ri /\
      word_bignumProof_Eval rec s1
        (if asm_word_cmp c (eval_exp s1 (wl_Var r)) (eval_ri s1 ri) then p1 else p2) s2
      ==> word_bignumProof_Eval rec s1 (word_bignum_If c r ri p1 p2) s2) /\
   (!rec (s:(A)word_bignumProof_state) r i a w.
      FLOOKUP (word_bignumProof_state_regs s) i = SOME w /\
      val w < LENGTH (word_bignumProof_state_arrays s a)
      ==> word_bignumProof_Eval rec s (word_bignum_Load r i a)
            (INR (reg_write r (SOME (EL (val w) (word_bignumProof_state_arrays s a))) s))) /\
   (!rec (s:(A)word_bignumProof_state) r i w wr.
      FLOOKUP (word_bignumProof_state_regs s) i = SOME w /\
      FLOOKUP (word_bignumProof_state_regs s) r = SOME wr /\
      val w < LENGTH (word_bignumProof_state_arrays s Out)
      ==> word_bignumProof_Eval rec s (word_bignum_Store r i)
            (INR (array_write Out
                    (LUPDATE wr (val w) (word_bignumProof_state_arrays s Out)) s))) /\
   (!r (s:(A)word_bignumProof_state).
      word_bignumProof_Eval r s Swap
        (INR (array_write In1 (word_bignumProof_state_arrays s In2)
               (array_write In2 (word_bignumProof_state_arrays s In1) s)))) /\
   (!r (s:(A)word_bignumProof_state) r1 r2 n1 n2 n3 n4 n5.
      n3 IN FDOM (word_bignumProof_state_regs s) /\ eval_ri_pre s n4 /\
      eval_ri_pre s n5 /\
      (~(eval_ri s n5 = word 0) ==> eval_ri s n5 = word 1) /\ ~(n1 = n2) /\
      single_add_word (FAPPLY (word_bignumProof_state_regs s) n3) (eval_ri s n4)
        (eval_ri s n5) = (r1,r2)
      ==> word_bignumProof_Eval r s (word_bignum_Add n1 n2 n3 n4 n5)
            (INR (reg_write n1 (SOME r1) (reg_write n2 (SOME r2) s)))) /\
   (!r (s:(A)word_bignumProof_state) n1 n2 n3 n4 n5 r1 r2.
      n3 IN FDOM (word_bignumProof_state_regs s) /\ eval_ri_pre s n4 /\
      eval_ri_pre s n5 /\
      (~(eval_ri s n5 = word 0) ==> eval_ri s n5 = word 1) /\ ~(n1 = n2) /\
      single_sub_word (FAPPLY (word_bignumProof_state_regs s) n3) (eval_ri s n4)
        (eval_ri s n5) = (r1,r2)
      ==> word_bignumProof_Eval r s (word_bignum_Sub n1 n2 n3 n4 n5)
            (INR (reg_write n1 (SOME r1) (reg_write n2 (SOME r2) s)))) /\
   (!r (s:(A)word_bignumProof_state) n1 n2 n3 n4.
      n3 IN FDOM (word_bignumProof_state_regs s) /\
      n4 IN FDOM (word_bignumProof_state_regs s) /\ ~(n1 = n2)
      ==> word_bignumProof_Eval r s (word_bignum_Mul n1 n2 n3 n4)
            (INR (reg_write n1
                    (SOME (FST (single_mul (FAPPLY (word_bignumProof_state_regs s) n3)
                                  (FAPPLY (word_bignumProof_state_regs s) n4) (word 0))))
                  (reg_write n2
                    (SOME (SND (single_mul (FAPPLY (word_bignumProof_state_regs s) n3)
                                  (FAPPLY (word_bignumProof_state_regs s) n4) (word 0))))
                    s)))) /\
   (!r (s:(A)word_bignumProof_state) n1 n2 n3 n4 n5.
      n3 IN FDOM (word_bignumProof_state_regs s) /\
      n4 IN FDOM (word_bignumProof_state_regs s) /\
      n5 IN FDOM (word_bignumProof_state_regs s) /\ ~(n1 = n2) /\
      single_div_pre (FAPPLY (word_bignumProof_state_regs s) n3)
        (FAPPLY (word_bignumProof_state_regs s) n4)
        (FAPPLY (word_bignumProof_state_regs s) n5)
      ==> word_bignumProof_Eval r s (word_bignum_Div n1 n2 n3 n4 n5)
            (INR (reg_write n1
                    (SOME (FST (single_div (FAPPLY (word_bignumProof_state_regs s) n3)
                                  (FAPPLY (word_bignumProof_state_regs s) n4)
                                  (FAPPLY (word_bignumProof_state_regs s) n5))))
                  (reg_write n2
                    (SOME (SND (single_div (FAPPLY (word_bignumProof_state_regs s) n3)
                                  (FAPPLY (word_bignumProof_state_regs s) n4)
                                  (FAPPLY (word_bignumProof_state_regs s) n5))))
                    s)))) /\
   (!r (s1:(A)word_bignumProof_state) p vs s2 rec.
      word_bignumProof_Eval (if rec then SOME p else NONE)
        (delete_vars vs (word_bignumProof_dec_clock s1)) (LoopBody p) (INR s2) /\
      ~(word_bignumProof_state_clock s1 = 0)
      ==> word_bignumProof_Eval r s1 (word_bignum_Loop rec vs p) (INR s2)) /\
   (!(s1:(A)word_bignumProof_state) save_regs vs p s2 s3.
      word_bignumProof_Eval (SOME p) (delete_vars vs (word_bignumProof_dec_clock s1))
        (LoopBody p) (INR s2) /\
      word_bignumProof_copy_vars save_regs (word_bignumProof_state_regs s1) s2 = SOME s3 /\
      ~(word_bignumProof_state_clock s1 = 0)
      ==> word_bignumProof_Eval (SOME p) s1 (Rec save_regs vs) (INR s3)) /\
   (!r (s1:(A)word_bignumProof_state) p s2.
      word_bignumProof_Eval r s1 p (INR s2)
      ==> word_bignumProof_Eval r s1 (LoopBody p) (INR s2)) /\
   (!r (s1:(A)word_bignumProof_state) s2 s3 p.
      word_bignumProof_Eval r s1 p (INL s2) /\ ~(word_bignumProof_state_clock s2 = 0) /\
      word_bignumProof_Eval r (word_bignumProof_dec_clock s2) (LoopBody p) (INR s3)
      ==> word_bignumProof_Eval r s1 (LoopBody p) (INR s3))`;;

(* the rules of Eval, one by one *)

let WBIGPAUX_eval_Skip, WBIGPAUX_eval_Continue, WBIGPAUX_eval_Delete, WBIGPAUX_eval_Assign,
    WBIGPAUX_eval_Seq, WBIGPAUX_eval_If, WBIGPAUX_eval_Load, WBIGPAUX_eval_Store,
    WBIGPAUX_eval_Swap, WBIGPAUX_eval_Add, WBIGPAUX_eval_Sub, WBIGPAUX_eval_Mul,
    WBIGPAUX_eval_Div, WBIGPAUX_eval_Loop, WBIGPAUX_eval_Rec, WBIGPAUX_eval_LoopBody1,
    WBIGPAUX_eval_LoopBody2 =
  match CONJUNCTS eval_rules with
    [t0; t1; t2; t3;
     t4; t5; t6; t7;
     t8; t9; t10; t11;
     t12; t13; t14; t15;
     t16] ->
      t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16
  | _ -> failwith "WBIGPAUX: eval_rules";;

(* HOL4 rebinds eval_cases (the ML value) to the case theorems of the 16  *)
(* constructors, simplified; eval_cases is the stored theorem, the ML      *)
(* value is WBIGPAUX_eval_cases                                            *)

let WBIGPAUX_eval_cases =
  let conv t = (ONCE_REWRITE_CONV[eval_cases] THENC CAKE_SIMP_CONV[]) t in
  end_itlist CONJ (map conv
   [`word_bignumProof_Eval rc (s1:(A)word_bignumProof_state) word_bignum_Skip res`;
    `word_bignumProof_Eval rc (s1:(A)word_bignumProof_state) word_bignum_Continue res`;
    `word_bignumProof_Eval rc (s1:(A)word_bignumProof_state) (Delete vs) res`;
    `word_bignumProof_Eval rc (s1:(A)word_bignumProof_state) (word_bignum_Seq p1 p2) res`;
    `word_bignumProof_Eval rc (s1:(A)word_bignumProof_state) (word_bignum_Assign n x) res`;
    `word_bignumProof_Eval rc (s1:(A)word_bignumProof_state)
       (word_bignum_If c r ri p1 p2) res`;
    `word_bignumProof_Eval rc (s1:(A)word_bignumProof_state) (word_bignum_Load r i a) res`;
    `word_bignumProof_Eval rc (s1:(A)word_bignumProof_state) (word_bignum_Store r i) res`;
    `word_bignumProof_Eval rc (s1:(A)word_bignumProof_state) Swap res`;
    `word_bignumProof_Eval rc (s1:(A)word_bignumProof_state)
       (word_bignum_Add n1 n2 n3 n4 n5) res`;
    `word_bignumProof_Eval rc (s1:(A)word_bignumProof_state)
       (word_bignum_Sub n1 n2 n3 n4 n5) res`;
    `word_bignumProof_Eval rc (s1:(A)word_bignumProof_state)
       (word_bignum_Mul n1 n2 n3 n4) res`;
    `word_bignumProof_Eval rc (s1:(A)word_bignumProof_state)
       (word_bignum_Div n1 n2 n3 n4 n5) res`;
    `word_bignumProof_Eval rc (s1:(A)word_bignumProof_state) (Rec save_regs vs) res`;
    `word_bignumProof_Eval rc (s1:(A)word_bignumProof_state) (word_bignum_Loop r vs p) res`;
    `word_bignumProof_Eval rc (s1:(A)word_bignumProof_state) (LoopBody p) res`]);;

let Eval_NONE_IMP = prove
 (`!s1 c s2 p. word_bignumProof_Eval NONE s1 c s2
               ==> word_bignumProof_Eval (SOME p) (s1:(A)word_bignumProof_state) c s2`,
  SUBGOAL_THEN
   `!r (s1:(A)word_bignumProof_state) c s2.
      word_bignumProof_Eval r s1 c s2 ==>
      word_bignumProof_Eval r s1 c s2 /\
      !p. r = NONE ==> word_bignumProof_Eval (SOME p) s1 c s2`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC eval_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[eval_rules] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[option_DISTINCT]) THEN
  ASM_MESON_TAC[eval_rules]);;

(* ------------------------------------------------------------------------- *)
(* verification of compiler to wordLang                                      *)
(* ------------------------------------------------------------------------- *)

let array_rel_def = cake_def
  `array_rel (arr:address->(A word)list) v1 v2 v3 (m:A word->(A)word_loc) dm frame <=>
     ?a1 a2 a3 rest1 rest2.
       v1 = SOME (wl_Word a1) /\
       v2 = SOME (wl_Word a2) /\
       v3 = SOME (wl_Word a3) /\
       (misc_word_list a1 (MAP wl_Word (arr In1)) STAR
        misc_word_list a3 (MAP wl_Word (arr Out)) STAR rest1) (fun2set (m,dm)) /\
       (misc_word_list a2 (MAP wl_Word (arr In2)) STAR
        misc_word_list a3 (MAP wl_Word (arr Out)) STAR rest2) (fun2set (m,dm)) /\
       (misc_word_list a3 (MAP wl_Word (arr Out)) STAR frame) (fun2set (m,dm))`;;

let code_subset_def = cake_def
  `code_subset (n1:A,cs1:(B#C)list) (n2:D,cs2) <=>
     !n v. ALOOKUP cs1 n = SOME v ==> ALOOKUP cs2 n = SOME v`;;

let word_bignumProof_code_rel_def = cake_def
  `word_bignumProof_code_rel (cs:num#((A)mini#num#(A)wl_prog)list) code <=>
     !prog n p2.
       ALOOKUP (SND cs) prog = SOME (n,p2) ==>
       ?cs1 l2 i2 cs2.
         word_bignum_compile n 2 1 cs1 prog = (p2,l2,i2,cs2) /\
         lookup n code = SOME (1,wl_Seq p2 (wl_Return 0 [0])) /\
         code_subset cs2 cs`;;

(* HOL4 div_code_assum (:'ffi) (:'c) code: the type arguments are the       *)
(* universes (:FFI) and (:C), as dimword (:A); WBIGPAUX_div_code_assum_DEF *)
(* is the definition with variables, div_code_assum_def the HOL4 form       *)

let WBIGPAUX_div_code_assum_DEF = new_definition
  `div_code_assum (ffi:FFI->bool) (c:C->bool) (code:(num#(A)wl_prog)spt) <=>
     !(t1:(A,C,FFI)wl_state) n l i0 i1 i2 i3 i4 w3 w4 w5 ret_val.
       0 < i0 /\ 0 < i1 /\ 0 < i2 /\ 0 < i3 /\ 0 < i4 /\
       ALL_DISTINCT [i0;i1;i2;i3;i4] /\
       wl_state_code t1 = code /\ ~(wl_state_termdep t1 = 0) /\
       wl_get_var 0 t1 = SOME ret_val /\ single_div_pre w3 w4 w5 ==>
       ?max.
         wl_evaluate
           (DivCode n l i0 i1 i2 i3 i4,
            wl_state_locals_fupd
              (K (insert i2 (wl_Word w3) (insert i3 (wl_Word w4)
                    (insert i4 (wl_Word w5) (wl_state_locals t1))))) t1) =
         (NONE,
          pair_CASE (single_div w3 w4 w5) (\w1 w2.
            (wl_set_var 0 ret_val o wl_set_var i1 (wl_Word w2) o
             wl_set_var i0 (wl_Word w1) o wl_set_store (Temp (word 28)) (wl_Word w2))
            (wl_state_permute_fupd (K (\n. wl_state_permute t1 (n + 1)))
              (wl_state_locals_fupd (K LN) (wl_state_stack_max_fupd (K max) t1)))))`;;

let div_code_assum_def = prove
 (`div_code_assum (:FFI) (:C) (code:(num#(A)wl_prog)spt) <=>
     !(t1:(A,C,FFI)wl_state) n l i0 i1 i2 i3 i4 w3 w4 w5 ret_val.
       0 < i0 /\ 0 < i1 /\ 0 < i2 /\ 0 < i3 /\ 0 < i4 /\
       ALL_DISTINCT [i0;i1;i2;i3;i4] /\
       wl_state_code t1 = code /\ ~(wl_state_termdep t1 = 0) /\
       wl_get_var 0 t1 = SOME ret_val /\ single_div_pre w3 w4 w5 ==>
       ?max.
         wl_evaluate
           (DivCode n l i0 i1 i2 i3 i4,
            wl_state_locals_fupd
              (K (insert i2 (wl_Word w3) (insert i3 (wl_Word w4)
                    (insert i4 (wl_Word w5) (wl_state_locals t1))))) t1) =
         (NONE,
          pair_CASE (single_div w3 w4 w5) (\w1 w2.
            (wl_set_var 0 ret_val o wl_set_var i1 (wl_Word w2) o
             wl_set_var i0 (wl_Word w1) o wl_set_store (Temp (word 28)) (wl_Word w2))
            (wl_state_permute_fupd (K (\n. wl_state_permute t1 (n + 1)))
              (wl_state_locals_fupd (K LN) (wl_state_stack_max_fupd (K max) t1)))))`,
  REWRITE_TAC[WBIGPAUX_div_code_assum_DEF]);;

(* HOL4 Overload max_var_name = 25n is written out *)

let word_bignumProof_state_rel_def = cake_def
  `word_bignumProof_state_rel (s:(A)word_bignumProof_state) (t:(A,C,FFI)wl_state)
      (cs:num#((A)mini#num#(A)wl_prog)list) (t0:(A,C,FFI)wl_state) frame <=>
     word_bignumProof_state_clock s = wl_state_clock t /\
     array_rel (word_bignumProof_state_arrays s)
       (FLOOKUP (wl_state_store t) TempIn1)
       (FLOOKUP (wl_state_store t) TempIn2)
       (FLOOKUP (wl_state_store t) TempOut) (wl_state_memory t) (wl_state_mdomain t)
       frame /\
     (!a v. FLOOKUP (word_bignumProof_state_regs s) a = SOME v ==>
            a < 25 /\ FLOOKUP (wl_state_store t) (Temp (word a)) = SOME (wl_Word v)) /\
     word_bignumProof_code_rel cs (wl_state_code t) /\
     div_code_assum (:FFI) (:C) (wl_state_code t) /\
     ~(wl_state_termdep t = 0) /\
     wl_state_gc_fun t0 = wl_state_gc_fun t /\
     wl_state_handler t0 = wl_state_handler t /\
     wl_state_termdep t0 = wl_state_termdep t /\
     wl_state_code t0 = wl_state_code t /\
     wl_state_be t0 = wl_state_be t /\
     wl_state_ffi t0 = wl_state_ffi t /\
     wl_state_compile t0 = wl_state_compile t /\
     wl_state_compile_oracle t0 = wl_state_compile_oracle t /\
     wl_state_code_buffer t0 = wl_state_code_buffer t /\
     wl_state_data_buffer t0 = wl_state_data_buffer t /\
     wl_state_stack_limit t0 = wl_state_stack_limit t /\
     wl_state_stack_size t0 = wl_state_stack_size t /\
     FLOOKUP (wl_state_store t) TempOut = FLOOKUP (wl_state_store t0) TempOut /\
     (!n. (!r. ~(n = Temp r)) ==>
          FLOOKUP (wl_state_store t) n = FLOOKUP (wl_state_store t0) n)`;;

(* early copies of four simp lemmas of the Corr part below, for the      *)
(* compile_thm part                                                        *)

let WBIGPAUX_reg_write_simp = prove
 (`word_bignumProof_state_regs (reg_write n NONE (s:(A)word_bignumProof_state)) =
   word_bignumProof_state_regs s \\ n /\
   word_bignumProof_state_regs (reg_write n (SOME w) s) =
   word_bignumProof_state_regs s |+ (n,w) /\
   word_bignumProof_state_arrays (reg_write n v s) = word_bignumProof_state_arrays s /\
   word_bignumProof_state_clock (reg_write n v s) = word_bignumProof_state_clock s`,
  STRUCT_CASES_TAC (ISPEC `v:(A word)option` (cases "option")) THEN
  REWRITE_TAC[reg_write_def; word_bignumProof_state_INFO.ri_accfupds; K_THM]);;

let WBIGPAUX_array_write_simp = prove
 (`word_bignumProof_state_regs (array_write n w (s:(A)word_bignumProof_state)) =
   word_bignumProof_state_regs s /\
   word_bignumProof_state_arrays (array_write n w s) =
   (n =+ w) (word_bignumProof_state_arrays s) /\
   word_bignumProof_state_clock (array_write n w s) = word_bignumProof_state_clock s`,
  REWRITE_TAC[array_write_def; word_bignumProof_state_INFO.ri_accfupds; K_THM]);;

let WBIGPAUX_dec_clock_write_simp = prove
 (`word_bignumProof_state_regs (word_bignumProof_dec_clock (s:(A)word_bignumProof_state)) =
   word_bignumProof_state_regs s /\
   word_bignumProof_state_arrays (word_bignumProof_dec_clock s) =
   word_bignumProof_state_arrays s /\
   word_bignumProof_state_clock (word_bignumProof_dec_clock s) =
   word_bignumProof_state_clock s - 1`,
  REWRITE_TAC[word_bignumProof_dec_clock_def; word_bignumProof_state_INFO.ri_accfupds;
              K_THM]);;

let WBIGPAUX_delete_vars_simp = prove
 (`!vs. word_bignumProof_state_clock (delete_vars vs (s:(A)word_bignumProof_state)) =
        word_bignumProof_state_clock s /\
        word_bignumProof_state_arrays (delete_vars vs s) =
        word_bignumProof_state_arrays s /\
        FLOOKUP (word_bignumProof_state_regs (delete_vars vs s)) n =
        (if MEM n vs then NONE else FLOOKUP (word_bignumProof_state_regs s) n) /\
        (n IN FDOM (word_bignumProof_state_regs (delete_vars vs s)) <=>
         if MEM n vs then F else n IN FDOM (word_bignumProof_state_regs s))`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[delete_vars_def; MEM; WBIGPAUX_reg_write_simp;
    DOMSUB_FLOOKUP_THM; FDOM_DOMSUB; IN_DELETE] THEN
  REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[]);;


(* HOL4: the first of the two [local] theorems state_rel_delete_vars *)
let WBIGPAUX_state_rel_SUBMAP = prove
 (`word_bignumProof_state_arrays s1 = word_bignumProof_state_arrays s2 /\
   word_bignumProof_state_clock s1 = word_bignumProof_state_clock s2 /\
   word_bignumProof_state_regs s2 SUBMAP word_bignumProof_state_regs s1 ==>
   word_bignumProof_state_rel (s1:(A)word_bignumProof_state) (t1:(A,C,FFI)wl_state)
     cs t0 frame ==>
   word_bignumProof_state_rel s2 t1 cs t0 frame`,
  REWRITE_TAC[word_bignumProof_state_rel_def; SUBMAP_FLOOKUP_EQN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th])
    (CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th]) ASSUME_TAC)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(MAP_EVERY ASSUME_TAC o filter (is_forall o concl)) THEN
  ASM_MESON_TAC[]);;

let state_rel_delete_vars = prove
 (`!vs. word_bignumProof_state_rel (s1:(A)word_bignumProof_state)
          (t1:(A,C,FFI)wl_state) cs t0 frame ==>
        word_bignumProof_state_rel (delete_vars vs s1) t1 cs t0 frame`,
  GEN_TAC THEN MATCH_MP_TAC WBIGPAUX_state_rel_SUBMAP THEN
  REWRITE_TAC[WBIGPAUX_delete_vars_simp; SUBMAP_FLOOKUP_EQN] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT]);;

let exp_ok_def = cake_def
  `(exp_ok (wl_Const (_:A word)) <=> T) /\
   (exp_ok (wl_Var i:(A)wl_exp) <=> i < 25) /\
   (exp_ok (wl_Op _ [x;y]:(A)wl_exp) <=> exp_ok x /\ exp_ok y) /\
   (exp_ok (wl_Shift sh e n:(A)wl_exp) <=> exp_ok e) /\
   (exp_ok (_:(A)wl_exp) <=> F)`;;


(* HOL4 syntax_ok_aux_def and syntax_ok_def (with TFL's completion of the  *)
(* catch-all clauses) are proved from definitions by a match: the kit's    *)
(* completion of these clauses over mini takes more than ten minutes       *)

let WBIGPAUX_syntax_ok_aux_match = cake_def
  `syntax_ok_aux (p:(A)mini) <=>
     match p with
       word_bignum_Loop r vs body -> syntax_ok_aux body
     | LoopBody body -> F
     | word_bignum_Seq p1 p2 -> syntax_ok_aux p1 /\ syntax_ok_aux p2
     | word_bignum_Assign t1 e -> t1 < 25 /\ exp_ok e
     | word_bignum_Load t1 t2 _ -> t1 < 25 /\ t2 < 25
     | word_bignum_Store t1 t2 -> t1 < 25 /\ t2 < 25
     | word_bignum_If c t2 t3 p1 p2 ->
         t2 < 25 /\ (!r. t3 = Reg r ==> r < 25) /\
         syntax_ok_aux p1 /\ syntax_ok_aux p2
     | word_bignum_Add n1 n2 n3 n4 n5 ->
         n1 < 25 /\ n2 < 25 /\ n3 < 25 /\
         (!r. n4 = Reg r ==> r < 25) /\ (!r. n5 = Reg r ==> r < 25)
     | word_bignum_Sub n1 n2 n3 n4 n5 ->
         n1 < 25 /\ n2 < 25 /\ n3 < 25 /\
         (!r. n4 = Reg r ==> r < 25) /\ (!r. n5 = Reg r ==> r < 25)
     | word_bignum_Mul n1 n2 n3 m4 -> n1 < 25 /\ n2 < 25 /\ n3 < 25 /\ m4 < 25
     | word_bignum_Div n1 n2 n3 m4 m5 ->
         n1 < 25 /\ n2 < 25 /\ n3 < 25 /\ m4 < 25 /\ m5 < 25
     | Rec save_regs _ -> ALL (\n. n < 25) save_regs /\ ALL_DISTINCT save_regs
     | _ -> T`;;

let syntax_ok_aux_def = prove
 (`(!r vs body. syntax_ok_aux (word_bignum_Loop r vs body:(A)mini) <=>
                syntax_ok_aux body) /\
   (!body. syntax_ok_aux (LoopBody body:(A)mini) <=> F) /\
   (!p1 p2. syntax_ok_aux (word_bignum_Seq p1 p2:(A)mini) <=>
            syntax_ok_aux p1 /\ syntax_ok_aux p2) /\
   (!t1 e. syntax_ok_aux (word_bignum_Assign t1 e:(A)mini) <=> t1 < 25 /\ exp_ok e) /\
   (!t1 t2 x. syntax_ok_aux (word_bignum_Load t1 t2 x:(A)mini) <=> t1 < 25 /\ t2 < 25) /\
   (!t1 t2. syntax_ok_aux (word_bignum_Store t1 t2:(A)mini) <=> t1 < 25 /\ t2 < 25) /\
   (!t1 t2 t3 p1 p2.
      syntax_ok_aux (word_bignum_If t1 t2 t3 p1 p2:(A)mini) <=>
      t2 < 25 /\ (!r. t3 = Reg r ==> r < 25) /\ syntax_ok_aux p1 /\ syntax_ok_aux p2) /\
   (!n1 n2 n3 n4 n5.
      syntax_ok_aux (word_bignum_Add n1 n2 n3 n4 n5:(A)mini) <=>
      n1 < 25 /\ n2 < 25 /\ n3 < 25 /\
      (!r. n4 = Reg r ==> r < 25) /\ (!r. n5 = Reg r ==> r < 25)) /\
   (!n1 n2 n3 n4 n5.
      syntax_ok_aux (word_bignum_Sub n1 n2 n3 n4 n5:(A)mini) <=>
      n1 < 25 /\ n2 < 25 /\ n3 < 25 /\
      (!r. n4 = Reg r ==> r < 25) /\ (!r. n5 = Reg r ==> r < 25)) /\
   (!n1 n2 n3 n4.
      syntax_ok_aux (word_bignum_Mul n1 n2 n3 n4:(A)mini) <=>
      n1 < 25 /\ n2 < 25 /\ n3 < 25 /\ n4 < 25) /\
   (!n1 n2 n3 n4 n5.
      syntax_ok_aux (word_bignum_Div n1 n2 n3 n4 n5:(A)mini) <=>
      n1 < 25 /\ n2 < 25 /\ n3 < 25 /\ n4 < 25 /\ n5 < 25) /\
   (!save_regs x.
      syntax_ok_aux (Rec save_regs x:(A)mini) <=>
      ALL (\n. n < 25) save_regs /\ ALL_DISTINCT save_regs) /\
   (syntax_ok_aux (word_bignum_Skip:(A)mini) <=> T) /\
   (!v3. syntax_ok_aux (Delete v3:(A)mini) <=> T) /\
   (syntax_ok_aux (Swap:(A)mini) <=> T) /\
   (syntax_ok_aux (word_bignum_Continue:(A)mini) <=> T)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [WBIGPAUX_syntax_ok_aux_match] THEN
  CASE_REWRITE_TAC[]);;

let WBIGPAUX_syntax_ok_match = cake_def
  `word_bignumProof_syntax_ok (p:(A)mini) <=>
     match p with LoopBody body -> syntax_ok_aux body | _ -> syntax_ok_aux p`;;

let word_bignumProof_syntax_ok_def = prove
 (`(!body. word_bignumProof_syntax_ok (LoopBody body:(A)mini) <=> syntax_ok_aux body) /\
   (word_bignumProof_syntax_ok (word_bignum_Skip:(A)mini) <=>
    syntax_ok_aux (word_bignum_Skip:(A)mini)) /\
   (!v2 v3. word_bignumProof_syntax_ok (word_bignum_Assign v2 v3:(A)mini) <=>
            syntax_ok_aux (word_bignum_Assign v2 v3:(A)mini)) /\
   (!v4. word_bignumProof_syntax_ok (Delete v4:(A)mini) <=>
         syntax_ok_aux (Delete v4:(A)mini)) /\
   (!v5 v6. word_bignumProof_syntax_ok (word_bignum_Seq v5 v6:(A)mini) <=>
            syntax_ok_aux (word_bignum_Seq v5 v6:(A)mini)) /\
   (!v7 v8 v9. word_bignumProof_syntax_ok (word_bignum_Load v7 v8 v9:(A)mini) <=>
               syntax_ok_aux (word_bignum_Load v7 v8 v9:(A)mini)) /\
   (!v10 v11. word_bignumProof_syntax_ok (word_bignum_Store v10 v11:(A)mini) <=>
              syntax_ok_aux (word_bignum_Store v10 v11:(A)mini)) /\
   (!v12 v13 v14 v15 v16.
      word_bignumProof_syntax_ok (word_bignum_If v12 v13 v14 v15 v16:(A)mini) <=>
      syntax_ok_aux (word_bignum_If v12 v13 v14 v15 v16:(A)mini)) /\
   (word_bignumProof_syntax_ok (Swap:(A)mini) <=> syntax_ok_aux (Swap:(A)mini)) /\
   (!v17 v18 v19 v20 v21.
      word_bignumProof_syntax_ok (word_bignum_Add v17 v18 v19 v20 v21:(A)mini) <=>
      syntax_ok_aux (word_bignum_Add v17 v18 v19 v20 v21:(A)mini)) /\
   (!v22 v23 v24 v25 v26.
      word_bignumProof_syntax_ok (word_bignum_Sub v22 v23 v24 v25 v26:(A)mini) <=>
      syntax_ok_aux (word_bignum_Sub v22 v23 v24 v25 v26:(A)mini)) /\
   (!v27 v28 v29 v30.
      word_bignumProof_syntax_ok (word_bignum_Mul v27 v28 v29 v30:(A)mini) <=>
      syntax_ok_aux (word_bignum_Mul v27 v28 v29 v30:(A)mini)) /\
   (!v31 v32 v33 v34 v35.
      word_bignumProof_syntax_ok (word_bignum_Div v31 v32 v33 v34 v35:(A)mini) <=>
      syntax_ok_aux (word_bignum_Div v31 v32 v33 v34 v35:(A)mini)) /\
   (!v36 v37 v38.
      word_bignumProof_syntax_ok (word_bignum_Loop v36 v37 v38:(A)mini) <=>
      syntax_ok_aux (word_bignum_Loop v36 v37 v38:(A)mini)) /\
   (word_bignumProof_syntax_ok (word_bignum_Continue:(A)mini) <=>
    syntax_ok_aux (word_bignum_Continue:(A)mini)) /\
   (!v39 v40. word_bignumProof_syntax_ok (Rec v39 v40:(A)mini) <=>
              syntax_ok_aux (Rec v39 v40:(A)mini))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [WBIGPAUX_syntax_ok_match] THEN
  CASE_REWRITE_TAC[]);;


(* the clauses of wordSem's evaluate used below *)

let WBIGPAUX_evaluate_clause c =
  find (fun th -> let l = lhs (concl (SPEC_ALL th)) in
                  fst (dest_const (fst (strip_comb (fst (dest_pair (rand l)))))) = c)
       (CONJUNCTS wl_evaluate_def);;

let WBIGPAUX_ev_Skip = WBIGPAUX_evaluate_clause "wl_Skip";;
let WBIGPAUX_ev_Seq = WBIGPAUX_evaluate_clause "wl_Seq";;
let WBIGPAUX_ev_Assign = WBIGPAUX_evaluate_clause "wl_Assign";;
let WBIGPAUX_ev_Set = WBIGPAUX_evaluate_clause "wl_Set";;
let WBIGPAUX_ev_Get = WBIGPAUX_evaluate_clause "wl_Get";;
let WBIGPAUX_ev_Inst = WBIGPAUX_evaluate_clause "wl_Inst";;
let WBIGPAUX_ev_Store = WBIGPAUX_evaluate_clause "wl_Store";;
let WBIGPAUX_ev_If = WBIGPAUX_evaluate_clause "wl_If";;
let WBIGPAUX_ev_Return = WBIGPAUX_evaluate_clause "wl_Return";;
let WBIGPAUX_ev_MustTerminate = WBIGPAUX_evaluate_clause "MustTerminate";;
let WBIGPAUX_ev_Call = WBIGPAUX_evaluate_clause "wl_Call";;

let evaluate_Seq_Seq = prove
 (`!p1 p2 p3 (t1:(A,C,FFI)wl_state).
     wl_evaluate (wl_Seq p1 (wl_Seq p2 p3),t1) =
     wl_evaluate (wl_Seq (wl_Seq p1 p2) p3,t1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WBIGPAUX_ev_Seq] THEN
  MP_TAC(ISPEC `wl_evaluate (p1:(A)wl_prog,t1:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r1:((A)wl_result)option`; `u1:(A,C,FFI)wl_state`] THEN
  DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[]);;


let WBIGPAUX_list_of_seq_1 = prove
 (`!f:num->A. list_of_seq f 1 = [f 0]`,
  REWRITE_TAC[num_CONV `1`; list_of_seq; APPEND]);;

let env_to_list_insert_0_LN = prove
 (`env_to_list (insert 0 (ret_val:(A)word_loc) LN) p = ([0,ret_val],(\n. p (n + 1)))`,
  REWRITE_TAC[env_to_list_def; LET_DEF; LET_END_DEF] THEN
  ONCE_REWRITE_TAC[insert_def] THEN
  REWRITE_TAC[toAList_def; foldi_def; sort_thm; mergesort_tail_def; LENGTH] THEN
  REWRITE_TAC[ARITH_RULE `SUC 0 = 1`; el 1 (CONJUNCTS mergesortN_tail_def)] THEN
  REWRITE_TAC[list_rearrange_def; LENGTH; ARITH_RULE `SUC 0 = 1`; PAIR_EQ] THEN
  COND_CASES_TAC THEN REWRITE_TAC[WBIGPAUX_list_of_seq_1] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [BIJ]) THEN
  REWRITE_TAC[INJ; IN_COUNT; ARITH_RULE `x < 1 <=> x = 0`] THEN
  DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT1) THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EL; HD]);;

let code_subset_refl = prove
 (`!c1:A#(B#C)list. code_subset c1 c1`,
  REWRITE_TAC[FORALL_PAIR_THM; code_subset_def]);;

let code_subset_trans = prove
 (`!c1:A#(B#C)list c2:D#(B#C)list c3:E#(B#C)list.
     code_subset c1 c2 /\ code_subset c2 c3 ==> code_subset c1 c3`,
  REWRITE_TAC[FORALL_PAIR_THM; code_subset_def] THEN MESON_TAC[]);;


let WBIGPAUX_code_subset_trans = prove
 (`!c1 c2 c3.
     code_subset (c1:num#((A)mini#num#(A)wl_prog)list)
                 (c2:num#((A)mini#num#(A)wl_prog)list) /\
     code_subset c2 (c3:num#((A)mini#num#(A)wl_prog)list) ==> code_subset c1 c3`,
  REWRITE_TAC[code_subset_trans]);;

let WBIGPAUX_DROP_FORALLS_TAC =
  POP_ASSUM_LIST(MAP_EVERY ASSUME_TAC o rev o filter (not o is_forall o concl));;

let WBIGPAUX_has_compiled_INR = prove
 (`!(p:A) n (l:(A#num#B)list) a.
     has_compiled p (n,l) = INR a <=> ALOOKUP l p = NONE /\ a = n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_compiled_def] THEN
  MP_TAC(ISPEC `ALOOKUP (l:(A#num#B)list) (p:A)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[injectivity "sum"] THEN MESON_TAC[];
    MP_TAC(ISPEC `a':num#B` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[distinctness "sum"]]);;

let WBIGPAUX_install_code_subset = prove
 (`!cs cs' (p:(A)mini) a (c:(A)wl_prog).
     has_compiled p (cs:num#((A)mini#num#(A)wl_prog)list) = INR a /\
     code_subset (code_acc_next cs) (cs':num#((A)mini#num#(A)wl_prog)list)
     ==> code_subset cs (install (p,a,c) cs')`,
  REWRITE_TAC[FORALL_PAIR_THM; WBIGPAUX_has_compiled_INR; code_acc_next_def;
              install_def; code_subset_def; ALOOKUP_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ASM_MESON_TAC[option_DISTINCT]; ASM_MESON_TAC[]]);;

let WBIGPAUX_EQS_TAC =
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM));;

let compile_IMP_code_subset = prove
 (`!prog n l i cs p1 l1 i1 cs1.
     word_bignum_compile n l i cs (prog:(A)mini) = (p1,l1,i1,cs1)
     ==> code_subset cs cs1 /\ i <= i1`,
  MATCH_MP_TAC mini_INDUCT THEN REWRITE_TAC[word_bignum_compile_def; PAIR_EQ] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  TRY (WBIGPAUX_EQS_TAC THEN REWRITE_TAC[code_subset_refl] THEN ARITH_TAC) THEN
  STRIP_TAC THEN REPEAT GEN_TAC THENL
   [REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN WBIGPAUX_EQS_TAC THEN
    RES_TAC THEN WBIGPAUX_DROP_FORALLS_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[WBIGPAUX_code_subset_trans]; ASM_ARITH_TAC];
    REPEAT PAIRARG_TAC THEN
    STRUCT_CASES_TAC (ISPEC `a2:(A)reg_imm` (cases "reg_imm")) THEN
    CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN WBIGPAUX_EQS_TAC THEN
    RES_TAC THEN WBIGPAUX_DROP_FORALLS_TAC THEN (CONJ_TAC THENL
     [ASM_MESON_TAC[WBIGPAUX_code_subset_trans]; ASM_ARITH_TAC]);
    MP_TAC(ISPEC `has_compiled (a2:(A)mini) (cs:num#((A)mini#num#(A)wl_prog)list)`
      (cases "sum")) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THENL
     [WBIGPAUX_EQS_TAC THEN REWRITE_TAC[code_subset_refl] THEN ARITH_TAC;
      REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN WBIGPAUX_EQS_TAC THEN
      RES_TAC THEN (CONJ_TAC THENL
       [MATCH_MP_TAC WBIGPAUX_install_code_subset THEN ASM_REWRITE_TAC[];
        ARITH_TAC])]]);;


let WBIGPAUX_has_compiled_INL = prove
 (`!(p:A) n (l:(A#num#B)list) x.
     has_compiled p (n,l) = INL x <=> ?c. ALOOKUP l p = SOME (x,c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_compiled_def] THEN
  MP_TAC(ISPEC `ALOOKUP (l:(A#num#B)list) (p:A)` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "sum"] THEN
  MP_TAC(ISPEC `a:num#B` PAIR_SURJECTIVE) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[injectivity "sum"; option_INJ; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 has a vacuous ?cs0 in front of the conclusion, dropped here *)

let has_compiled_lemma = prove
 (`word_bignumProof_state_rel (s1:(A)word_bignumProof_state) (t1:(A,C,FFI)wl_state)
     cs2 t0 frame /\
   has_compiled p (cs:num#((A)mini#num#(A)wl_prog)list) = INL x /\
   code_subset cs cs2 ==>
   ?p1 l1 i1 cs' cs1.
     word_bignum_compile x 2 1 cs' p = (p1,l1,i1,cs1) /\ code_subset cs1 cs2 /\
     lookup x (wl_state_code t1) = SOME (1,wl_Seq p1 (wl_Return 0 [0]))`,
  MAP_EVERY (fun t -> SPEC_TAC(t,t))
    [`cs:num#((A)mini#num#(A)wl_prog)list`; `cs2:num#((A)mini#num#(A)wl_prog)list`] THEN
  REWRITE_TAC[FORALL_PAIR_THM; WBIGPAUX_has_compiled_INL; code_subset_def;
              word_bignumProof_state_rel_def; word_bignumProof_code_rel_def] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl (SPEC_ALL th)) &&
    can (find_term (fun t -> t = `wl_Return 0 [0]:(A)wl_prog`)) (concl th))) THEN
  REWRITE_TAC[SND] THEN DISCH_THEN(MP_TAC o SPECL [`p:(A)mini`; `x:num`; `c:(A)wl_prog`]) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let state_rel_IN_FDOM = prove
 (`word_bignumProof_state_rel (s1:(A)word_bignumProof_state) (t1:(A,C,FFI)wl_state)
     cs2 t0 frame /\ r IN FDOM (word_bignumProof_state_regs s1) ==>
   Temp (word r) IN FDOM (wl_state_store t1) /\
   FAPPLY (wl_state_store t1) (Temp (word r)) =
   wl_Word (FAPPLY (word_bignumProof_state_regs s1) r)`,
  REWRITE_TAC[word_bignumProof_state_rel_def] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`r:num`; `FAPPLY (word_bignumProof_state_regs
                                  (s1:(A)word_bignumProof_state)) r`]) THEN
  ASM_REWRITE_TAC[FLOOKUP_DEF; option_INJ] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[]);;


let word_bignumProof_compile_exp_thm = prove
 (`word_bignumProof_state_rel (s1:(A)word_bignumProof_state) (t1:(A,C,FFI)wl_state)
     cs2 t0 frame /\ eval_exp_pre s1 x /\ good_dimindex (:A) ==>
   wl_word_exp t1 (word_bignum_compile_exp x) = SOME (wl_Word (eval_exp s1 (x:(A)wl_exp)))`,
  STRIP_TAC THEN UNDISCH_TAC `eval_exp_pre (s1:(A)word_bignumProof_state) x` THEN
  SUBGOAL_THEN
   `!(u:(A,C,FFI)wl_state) (x:(A)wl_exp). eval_exp_pre (s1:(A)word_bignumProof_state) x ==>
      wl_word_exp (t1:(A,C,FFI)wl_state) (word_bignum_compile_exp x) =
      SOME (wl_Word (eval_exp s1 x))`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC wl_word_exp_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[eval_exp_pre_def; word_bignum_compile_exp_def; eval_exp_def;
              wl_word_exp_def] THENL
   [REWRITE_TAC[wl_get_store_def; FLOOKUP_DEF] THEN DISCH_TAC THEN
    MP_TAC(INST [`u:num`,`r:num`] state_rel_IN_FDOM) THEN ASM_SIMP_TAC[];
    STRUCT_CASES_TAC (ISPEC `wexps:((A)wl_exp)list` list_CASES) THEN
    REWRITE_TAC[eval_exp_pre_def] THEN
    STRUCT_CASES_TAC (ISPEC `t:((A)wl_exp)list` list_CASES) THEN
    REWRITE_TAC[eval_exp_pre_def] THEN
    STRUCT_CASES_TAC (ISPEC `t':((A)wl_exp)list` list_CASES) THEN
    REWRITE_TAC[eval_exp_pre_def; MEM] THEN
    REWRITE_TAC[word_bignum_compile_exp_def; wl_word_exp_def; MAP] THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC(SPEC `h:(A)wl_exp` th) THEN
                         MP_TAC(SPEC `h':(A)wl_exp` th)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[the_words_def] THEN
    CASE_REWRITE_TAC[] THEN
    STRUCT_CASES_TAC (ISPEC `op:binop` (cases "binop")) THEN
    REWRITE_TAC[word_op_def; eval_exp_def; ITLIST; OPTION_MAP_DEF] THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[OPTION_MAP_DEF; option_INJ; injectivity "word_loc"] THEN
    REWRITE_TAC[WORD_ADD_0; WORD_OR_0; WORD_XOR_0; WORD_AND_NOT0];
    DISCH_THEN(fun ih -> STRIP_TAC THEN MP_TAC ih) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[word_sh_def] THEN
    SUBGOAL_THEN `~(val (eval_exp (s1:(A)word_bignumProof_state) wexp1) >= dimindex(:A))`
      (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `good_dimindex(:A)` THEN REWRITE_TAC[good_dimindex_def] THEN
      UNDISCH_TAC `val (eval_exp (s1:(A)word_bignumProof_state) wexp1) < 32` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    STRUCT_CASES_TAC (ISPEC `sh:shift` (cases "shift")) THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[eval_exp_def; OPTION_MAP_DEF]]);;


let evaluate_SeqTemp = prove
 (`wl_evaluate (SeqTemp i r p,(t:(A,C,FFI)wl_state)) =
   if Temp (word r) IN FDOM (wl_state_store t) then
     wl_evaluate (p,wl_set_var i (FAPPLY (wl_state_store t) (Temp (word r))) t)
   else wl_evaluate (SeqTemp i r p,t)`,
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[SeqTemp_def; WBIGPAUX_ev_Seq; WBIGPAUX_ev_Assign; wl_word_exp_def;
              wl_get_store_def; FLOOKUP_DEF] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

let evaluate_SeqTempImm = prove
 (CASE_TERM
  `wl_evaluate (SeqTempImm i ri p,(t:(A,C,FFI)wl_state)) =
   if !r. ri = Reg r ==> Temp (word r) IN FDOM (wl_state_store t) then
     wl_evaluate (p,wl_set_var i (match ri with Imm w -> wl_Word w
                                  | Reg r -> FAPPLY (wl_state_store t) (Temp (word r))) t)
   else wl_evaluate (SeqTempImm i ri p,t)`,
  STRUCT_CASES_TAC (ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN
  REWRITE_TAC[injectivity "reg_imm"; distinctness "reg_imm"; FORALL_UNWIND_THM1;
              FORALL_UNWIND_THM2] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[SeqTempImm_def] THENL
   [ONCE_REWRITE_TAC[evaluate_SeqTemp] THEN COND_CASES_TAC THEN REWRITE_TAC[];
    REWRITE_TAC[WBIGPAUX_ev_Seq; WBIGPAUX_ev_Assign; wl_word_exp_def] THEN
    CASE_REWRITE_TAC[]]);;

let WBIGPAUX_set_var_set_var = prove
 (`!i a b (t:(A,C,FFI)wl_state).
     wl_set_var i a (wl_set_var i b t) = wl_set_var i a t`,
  REWRITE_TAC[wl_set_var_def; wl_state_INFO.ri_accfupds; wl_state_INFO.ri_fupdfupds;
              K_THM; insert_shadow; o_DEF] THEN
  REWRITE_TAC[K_DEF]);;

let WBIGPAUX_WORD_XOR_NOT0 = prove
 (`!x:A word. word_xor x (word_not (word 0)) = word_not x`,
  CONV_TAC WORD_BITWISE_RULE);;

let evaluate_SeqTempImmNot = prove
 (CASE_TERM
  `wl_evaluate (SeqTempImmNot i ri p,(t:(A,C,FFI)wl_state)) =
   if !r. ri = Reg r ==> Temp (word r) IN FDOM (wl_state_store t) /\
                         ?w. FAPPLY (wl_state_store t) (Temp (word r)) = wl_Word w then
     wl_evaluate (p,wl_set_var i (match ri with Imm w -> wl_Word (word_not w)
                                  | Reg r -> (match FAPPLY (wl_state_store t) (Temp (word r))
                                              with wl_Word w -> wl_Word (word_not w))) t)
   else wl_evaluate (SeqTempImmNot i ri p,t)`,
  STRUCT_CASES_TAC (ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN
  REWRITE_TAC[injectivity "reg_imm"; distinctness "reg_imm"; FORALL_UNWIND_THM1;
              FORALL_UNWIND_THM2] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[SeqTempImmNot_def] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `w:A word`)) THEN
    ONCE_REWRITE_TAC[evaluate_SeqTemp] THEN ASM_REWRITE_TAC[] THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[WBIGPAUX_ev_Seq; WBIGPAUX_ev_Assign; wl_word_exp_def; MAP;
                wl_get_var_def; wl_set_var_def; wl_state_INFO.ri_accfupds; K_THM;
                lookup_insert; the_words_def] THEN
    CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[word_op_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[ITLIST; WORD_XOR_0; OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[wl_state_INFO.ri_fupdfupds; o_DEF; K_THM; insert_shadow;
                WBIGPAUX_WORD_XOR_NOT0] THEN
    REWRITE_TAC[K_DEF];
    REWRITE_TAC[WBIGPAUX_ev_Seq; WBIGPAUX_ev_Assign; wl_word_exp_def] THEN
    CASE_REWRITE_TAC[]]);;


let word_bignumProof_LESS_LENGTH_IMP_APPEND = prove
 (`!xs n. n < LENGTH xs ==>
          ?ys (z:A) zs. xs = APPEND ys (CONS z zs) /\ LENGTH ys = n`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN REWRITE_TAC[LT_SUC; LT_0] THENL
   [MAP_EVERY EXISTS_TAC [`[]:A list`; `h:A`; `t:A list`] THEN
    REWRITE_TAC[APPEND; LENGTH];
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`CONS (h:A) ys`; `z:A`; `zs:A list`] THEN
    ASM_REWRITE_TAC[APPEND; LENGTH]]);;

let word_bignumProof_word_list_APPEND = prove
 (`!xs ys (a:A word).
     misc_word_list a (APPEND xs ys:B list) =
     misc_word_list a xs STAR
     misc_word_list (word_add a (word_mul (word (LENGTH xs)) bytes_in_word)) ys`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[misc_word_list_def; APPEND; LENGTH; SEP_CLAUSES; STAR_ASSOC] THEN
  REWRITE_TAC[WORD_MUL_0; WORD_ADD_0] THEN REPEAT GEN_TAC THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ADD1; WORD_ADD] THEN CONV_TAC WORD_RULE);;

let shift_eq_bytes_in_word = prove
 (`good_dimindex (:A) ==>
   word_shl (w:A word) (backend_common_word_shift (:A) MOD dimword (:A)) =
   word_mul w bytes_in_word`,
  REWRITE_TAC[good_dimindex_def; backend_common_word_shift_def; bytes_in_word_def;
              dimword_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[WORD_MUL_LSL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_MUL_SYM]);;

let b2w_if = prove
 (`b2w b = if b then word 1 else (word 0:A word)`,
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[multiword_b2w_def; BITVAL_CLAUSES]);;

let b2n_if = prove
 (`bitval b = if ~b then 0 else 1`,
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[BITVAL_CLAUSES]);;


(* HOL4: Is this worth the hassle *)

let list_update_def = cake_def
  `(list_update [] (ys:A list) t = t) /\
   (list_update (CONS x xs) (CONS y ys) t = insert x y (list_update xs ys t)) /\
   (list_update (CONS x xs) [] t = insert x ARB (list_update xs [] t))`;;

let list_update_ind = cake_ind "list_update";;

let list_update_alist_insert = prove
 (`!xs (ys:A list) t.
     LENGTH xs = LENGTH ys ==> list_update xs ys t = alist_insert xs ys t`,
  MATCH_MP_TAC list_update_ind THEN
  REWRITE_TAC[list_update_def; alist_insert_def; LENGTH; NOT_SUC; SUC_INJ] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);;

(* the relation does not depend on the locals and a few more fields *)

let WBIGPAUX_state_rel_locals = prove
 (`!f s (t:(A,C,FFI)wl_state) cs t0 frame.
     word_bignumProof_state_rel s (wl_state_locals_fupd f t) cs t0 frame <=>
     word_bignumProof_state_rel s t cs t0 frame`,
  REWRITE_TAC[word_bignumProof_state_rel_def; wl_state_INFO.ri_accfupds]);;

let WBIGPAUX_set_var_locals = prove
 (`!v x (s:(A,C,FFI)wl_state).
     wl_set_var v x s = wl_state_locals_fupd (K (insert v x (wl_state_locals s))) s`,
  REWRITE_TAC[wl_set_var_def]);;

let WBIGPAUX_list_update_insert = prove
 (`!xs (ys:A list) t k v.
     ~MEM k xs ==>
     list_update xs ys (insert k v t) = insert k v (list_update xs ys t)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[list_update_def; MEM; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [insert_insert] THEN
  ASM_REWRITE_TAC[]);;

let evaluate_LoadRegs = prove
 (`!save_regs vals (t1:(A,C,FFI)wl_state).
     word_bignumProof_state_rel (s1:(A)word_bignumProof_state) t1 cs2 t0 frame /\
     ALL (\n. n < 25) save_regs /\ ALL_DISTINCT save_regs /\
     ALL2 (\n v. FLOOKUP (word_bignumProof_state_regs s1) n = SOME v) save_regs vals ==>
     wl_evaluate (LoadRegs save_regs p,t1) =
     wl_evaluate (p,wl_state_locals_fupd
                      (K (list_update (MAP (\n. n + 2) save_regs) (MAP wl_Word vals)
                            (wl_state_locals t1))) t1)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LoadRegs_def; list_update_def; ALL2; MAP; ALL; ALL_DISTINCT] THENL
   [REPEAT STRIP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[wl_state_component_equality; wl_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  X_GEN_TAC `t1:(A,C,FFI)wl_state` THEN STRIP_TAC THEN
  REWRITE_TAC[WBIGPAUX_ev_Seq; WBIGPAUX_ev_Get; wl_get_store_def] THEN
  SUBGOAL_THEN `FLOOKUP (wl_state_store (t1:(A,C,FFI)wl_state)) (Temp (word h)) =
                SOME (wl_Word h')` SUBST1_TAC THENL
   [UNDISCH_TAC `word_bignumProof_state_rel (s1:(A)word_bignumProof_state)
                   (t1:(A,C,FFI)wl_state) cs2 t0 frame` THEN
    REWRITE_TAC[word_bignumProof_state_rel_def] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t':(A word)list`;
    `wl_set_var (h + 2) (wl_Word h') (t1:(A,C,FFI)wl_state)`]) THEN
  ASM_REWRITE_TAC[WBIGPAUX_set_var_locals; WBIGPAUX_state_rel_locals] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[wl_state_INFO.ri_fupdfupds; wl_state_INFO.ri_accfupds; K_o_THM] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[K_THM] THEN MATCH_MP_TAC WBIGPAUX_list_update_insert THEN
  REWRITE_TAC[MEM_MAP; ARITH_RULE `h + 2 = x + 2 <=> x = h`] THEN
  ASM_MESON_TAC[]);;

let domain_list_update = prove
 (`!xs (ys:A list) x t. x IN domain (list_update xs ys t) <=> MEM x xs \/ x IN domain t`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_update_def; MEM; domain_insert; IN_INSERT] THEN MESON_TAC[]);;


let list_store_def = cake_def
  `(list_store [] (ys:((A)word_loc)list) (s:(store_name,(A)word_loc)fmap) = s) /\
   (list_store (CONS x xs) ys s = list_store xs (TL ys) s |+ (Temp (word x),HD ys))`;;

(* registers below 25 are different Temp store names, different from      *)
(* TempIn1, TempIn2 and TempOut                                            *)

let WBIGPAUX_Temp_11 = prove
 (`!x y. x < 25 /\ y < 25 ==> (Temp (word x) = Temp (word y) <=> x = y)`,
  REWRITE_TAC[injectivity "store_name"; GSYM VAL_EQ; VAL_WORD; DIMINDEX_CONV `dimindex(:5)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT; ARITH_RULE `x < 25 ==> x < 32`]);;

let WBIGPAUX_Temp_TempIn = prove
 (`!x. x < 25 ==> ~(Temp (word x) = TempIn1) /\ ~(Temp (word x) = TempIn2) /\
                  ~(Temp (word x) = TempOut)`,
  REWRITE_TAC[TempIn1_def; TempIn2_def; TempOut_def; injectivity "store_name";
              GSYM VAL_EQ; VAL_WORD; DIMINDEX_CONV `dimindex(:5)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT; ARITH_RULE `x < 25 ==> x < 32`] THEN
  ARITH_TAC);;

let list_store_FUPDATE = prove
 (`!save_regs st ys.
     ~MEM h save_regs /\ h < 25 /\ ALL (\n. n < 25) save_regs ==>
     list_store save_regs ys (st |+ (Temp (word h),wl_Word (v:A word))) =
     list_store save_regs ys st |+ (Temp (word h),wl_Word v)`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[list_store_def; MEM; ALL; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FUPDATE_COMMUTES THEN
  ASM_SIMP_TAC[WBIGPAUX_Temp_11]);;

let evaluate_SaveRegs = prove
 (`!save_regs (t7:(A,C,FFI)wl_state) vals.
     ALL2 (\n v. lookup (n + 2) (wl_state_locals t7) = SOME (wl_Word v)) save_regs vals /\
     ALL_DISTINCT save_regs /\ ALL (\n. n < 25) save_regs ==>
     wl_evaluate (SaveRegs save_regs,t7) =
     (NONE,wl_state_store_fupd
             (K (list_store save_regs (MAP wl_Word vals) (wl_state_store t7))) t7)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[list_store_def; SaveRegs_def; WBIGPAUX_ev_Skip] THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[PAIR_EQ; wl_state_component_equality;
                                      wl_state_INFO.ri_accfupds; K_THM];
    ALL_TAC] THEN
  X_GEN_TAC `t7:(A,C,FFI)wl_state` THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; ALL_DISTINCT; ALL; MAP; HD; TL] THEN STRIP_TAC THEN
  REWRITE_TAC[WBIGPAUX_ev_Seq; WBIGPAUX_ev_Set; distinctness "store_name";
              wl_word_exp_def; wl_get_var_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`wl_set_store (Temp (word h)) (wl_Word h')
                                   (t7:(A,C,FFI)wl_state)`; `t':(A word)list`]) THEN
  ASM_REWRITE_TAC[wl_set_store_def; wl_state_INFO.ri_accfupds] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[PAIR_EQ; wl_state_INFO.ri_fupdfupds; K_o_THM; K_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC list_store_FUPDATE THEN ASM_REWRITE_TAC[]);;

let FLOOKUP_list_store_ignore = prove
 (`!save_regs (vals:((A)word_loc)list) st.
     ALL (\n. n < 25) save_regs ==>
     FLOOKUP (list_store save_regs vals st) TempIn1 = FLOOKUP st TempIn1 /\
     FLOOKUP (list_store save_regs vals st) TempIn2 = FLOOKUP st TempIn2 /\
     FLOOKUP (list_store save_regs vals st) TempOut = FLOOKUP st TempOut /\
     !n. (!r. ~(n = Temp r)) ==>
         FLOOKUP (list_store save_regs vals st) n = FLOOKUP st n`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[list_store_def; ALL; FLOOKUP_UPDATE] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`TL (vals:((A)word_loc)list)`;
                                `st:(store_name,(A)word_loc)fmap`]) THEN
  ASM_SIMP_TAC[WBIGPAUX_Temp_TempIn] THEN MESON_TAC[]);;


let copy_vars_const = prove
 (`!save_regs s2 s3.
     word_bignumProof_copy_vars save_regs
       (word_bignumProof_state_regs (s1:(A)word_bignumProof_state)) s2 = SOME s3 ==>
     word_bignumProof_state_clock s3 = word_bignumProof_state_clock s2 /\
     word_bignumProof_state_arrays s3 = word_bignumProof_state_arrays s2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[word_bignumProof_copy_vars_def; option_INJ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `FLOOKUP (word_bignumProof_state_regs (s1:(A)word_bignumProof_state)) h`
    (cases "option")) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REWRITE_TAC[WBIGPAUX_reg_write_simp]);;

let lookup_list_update_ADD_2 = prove
 (`!save_regs (ws:A list).
     lookup 0 (list_update (MAP (\n. n + 2) save_regs) ws l) = lookup 0 l`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; list_update_def; lookup_insert; ARITH_RULE `~(0 = h + 2)`]);;

let copy_vars_ignore = prove
 (`!save_regs regs (s2:(A)word_bignumProof_state) s3.
     word_bignumProof_copy_vars save_regs regs s2 = SOME s3 /\
     ~MEM a save_regs /\ a < 25 /\ ALL (\n. n < 25) save_regs ==>
     FAPPLY (word_bignumProof_state_regs s3) a =
     FAPPLY (word_bignumProof_state_regs s2) a`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[word_bignumProof_copy_vars_def; option_INJ; MEM; ALL;
                                   DE_MORGAN_THM] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `FLOOKUP (regs:(num,A word)fmap) h` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[option_DISTINCT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`regs:(num,A word)fmap`;
    `reg_write h (SOME a') (s2:(A)word_bignumProof_state)`;
    `s3:(A)word_bignumProof_state`]) THEN
  ASM_REWRITE_TAC[WBIGPAUX_reg_write_simp; FAPPLY_FUPDATE_THM] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[]);;

let copy_vars_IMP = prove
 (`!save_regs s2 s3.
     word_bignumProof_copy_vars save_regs
       (word_bignumProof_state_regs (s1:(A)word_bignumProof_state)) s2 = SOME s3 ==>
     ?vals. ALL2 (\n v. FLOOKUP (word_bignumProof_state_regs s1) n = SOME v)
              save_regs vals`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[word_bignumProof_copy_vars_def] THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `[]:(A word)list` THEN REWRITE_TAC[ALL2];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `FLOOKUP (word_bignumProof_state_regs (s1:(A)word_bignumProof_state)) h`
    (cases "option")) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_DISTINCT] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  STRIP_TAC THEN EXISTS_TAC `CONS (a:A word) vals` THEN ASM_REWRITE_TAC[ALL2]);;

let LIST_REL_lemma = prove
 (`!xs (ys:B list).
     (!x y. MEM x xs /\ MEM y ys ==> (P:A->B->bool) x y ==> Q x y) ==>
     ALL2 P xs ys ==> ALL2 Q xs ys`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; MEM] THEN
  REPEAT STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t':B list`) THEN ASM_MESON_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* compile_thm: one lemma per rule of Eval (the cases of eval_ind for the    *)
(* statement below)                                                          *)
(* ------------------------------------------------------------------------- *)

let WBIGPAUX_compile_thm_stmt = CASE_TERM
 `!rec (s1:(A)word_bignumProof_state) prog s2.
     word_bignumProof_Eval rec s1 prog s2 ==>
     !n l i cs p1 l1 i1 cs1 cs2 (t1:(A,C,FFI)wl_state) (ret_val:(A)word_loc) p9.
       word_bignum_compile n l i cs prog = (p1,l1,i1,cs1) /\
       word_bignumProof_state_rel s1 t1 cs2 (t0:(A,C,FFI)wl_state)
         (frame:((A word#(A)word_loc)->bool)->bool) /\ 0 < i /\
       word_bignumProof_syntax_ok prog /\ code_subset cs1 cs2 /\
       (!body. rec = SOME body ==>
               ?l i cs p1 l1 i1 cs1.
                 word_bignum_compile n l i cs body = (p1,l1,i1,cs1) /\
                 0 < i /\ syntax_ok_aux body /\ code_subset cs1 cs2 /\
                 lookup n (wl_state_code t1) = SOME (1,wl_Seq p1 (wl_Return 0 [0]))) /\
       (!body. prog = LoopBody body ==>
               p9 = wl_Return 0 [0] /\
               lookup n (wl_state_code t1) = SOME (1,wl_Seq p1 (wl_Return 0 [0]))) /\
       wl_get_var 0 t1 = SOME ret_val /\ good_dimindex (:A) ==>
       ?t2 res.
         wl_evaluate (wl_Seq p1 p9,t1) = res /\
         (match s2 with
            INR s -> res = wl_evaluate (p9,t2) /\ 0 < i1 /\
                     wl_state_stack t2 = wl_state_stack t1 /\
                     wl_get_var 0 t2 = SOME ret_val /\
                     word_bignumProof_state_rel s t2 cs2 t0 frame /\
                     wl_state_code t2 = wl_state_code t1
          | INL s -> res = wl_evaluate (wl_Call NONE (SOME n) [0] NONE,t2) /\ 0 < i1 /\
                     wl_state_stack t2 = wl_state_stack t1 /\
                     wl_get_var 0 t2 = SOME ret_val /\
                     word_bignumProof_state_rel s t2 cs2 t0 frame /\
                     wl_state_code t2 = wl_state_code t1)`;;

let WBIGPAUX_compile_P =
  let vs,bod = strip_forall WBIGPAUX_compile_thm_stmt in
  list_mk_abs(vs,rand bod);;

let WBIGPAUX_compile_ind = BETA_RULE (ISPEC WBIGPAUX_compile_P eval_ind);;

let WBIGPAUX_compile_cases = conjuncts (lhand (concl WBIGPAUX_compile_ind));;

(* the equations p1 = .. l1 = .. of the compiled code, substituted *)

let WBIGPAUX_CSUBST_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    let c = concl th in is_eq c && is_var (rhs c) && not (lhs c = rhs c) &&
    not (vfree_in (rhs c) (lhs c)))));;

let WBIGPAUX_is_compile_eq th =
  try fst (dest_const (fst (strip_comb (lhs (concl th))))) = "word_bignum_compile"
  with Failure _ -> false;;

let WBIGPAUX_CPRE_TAC : tactic =
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check WBIGPAUX_is_compile_eq) THEN
  REWRITE_TAC[word_bignum_compile_def; PAIR_EQ] THEN STRIP_TAC THEN
  WBIGPAUX_CSUBST_TAC THEN CASE_REWRITE_TAC[];;

let WBIGPAUX_ev_Seq_not_NONE = prove
 (`!c p (s:(A,C,FFI)wl_state).
     ~(FST (wl_evaluate (c,s)) = NONE) ==>
     wl_evaluate (wl_Seq c p,s) = wl_evaluate (c,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WBIGPAUX_ev_Seq] THEN
  MP_TAC(ISPEC `wl_evaluate (c:(A)wl_prog,s:(A,C,FFI)wl_state)` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  SIMP_TAC[]);;

let WBIGPAUX_ev_Call_tail_not_NONE = prove
 (`!dest args (s:(A,C,FFI)wl_state).
     ~(FST (wl_evaluate (wl_Call NONE dest args NONE,s)) = NONE)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WBIGPAUX_ev_Call] THEN
  EVERY_CASE_TAC THEN REWRITE_TAC[FST; option_DISTINCT] THEN
  ASM_MESON_TAC[wl_bad_fun_return_def]);;

let WBIGPAUX_compile_Skip = prove
 (el 0 WBIGPAUX_compile_cases,
  WBIGPAUX_CPRE_TAC THEN EXISTS_TAC `t1:(A,C,FFI)wl_state` THEN
  REWRITE_TAC[UNWIND_THM1; WBIGPAUX_ev_Seq; WBIGPAUX_ev_Skip] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let WBIGPAUX_compile_Continue = prove
 (el 1 WBIGPAUX_compile_cases,
  WBIGPAUX_CPRE_TAC THEN EXISTS_TAC `t1:(A,C,FFI)wl_state` THEN
  REWRITE_TAC[UNWIND_THM1] THEN
  ASM_SIMP_TAC[WBIGPAUX_ev_Seq_not_NONE; WBIGPAUX_ev_Call_tail_not_NONE]);;

let WBIGPAUX_compile_Delete = prove
 (el 2 WBIGPAUX_compile_cases,
  WBIGPAUX_CPRE_TAC THEN EXISTS_TAC `t1:(A,C,FFI)wl_state` THEN
  REWRITE_TAC[UNWIND_THM1; WBIGPAUX_ev_Seq; WBIGPAUX_ev_Skip] THEN
  CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[state_rel_delete_vars]);;


let WBIGPAUX_state_rel_reg_write = prove
 (`!s (t:(A,C,FFI)wl_state) cs t0 frame n v.
     word_bignumProof_state_rel s t cs t0 frame /\ n < 25 ==>
     word_bignumProof_state_rel (reg_write n (SOME v) s)
       (wl_set_store (Temp (word n)) (wl_Word v) t) cs t0 frame`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_bignumProof_state_rel_def; WBIGPAUX_reg_write_simp; wl_set_store_def;
              wl_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WBIGPAUX_Temp_TempIn th]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN ASM_CASES_TAC `n = a:num` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[option_INJ] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN RES_TAC THEN
      ASM_SIMP_TAC[WBIGPAUX_Temp_11]];
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(Temp (word n) = n')` (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM_MESON_TAC[]]);;

let WBIGPAUX_get_var_set_var = prove
 (`!i j x (s:(A,C,FFI)wl_state).
     wl_get_var i (wl_set_var j x s) = if i = j then SOME x else wl_get_var i s`,
  REWRITE_TAC[wl_get_var_def; wl_set_var_def; wl_state_INFO.ri_accfupds; K_THM;
              lookup_insert]);;

let WBIGPAUX_set_var_simps = prove
 (`(!i x (s:(A,C,FFI)wl_state).
      wl_state_stack (wl_set_var i x s) = wl_state_stack s /\
      wl_state_code (wl_set_var i x s) = wl_state_code s /\
      wl_state_store (wl_set_var i x s) = wl_state_store s /\
      wl_state_clock (wl_set_var i x s) = wl_state_clock s) /\
   (!v x (s:(A,C,FFI)wl_state).
      wl_state_stack (wl_set_store v x s) = wl_state_stack s /\
      wl_state_code (wl_set_store v x s) = wl_state_code s /\
      wl_state_locals (wl_set_store v x s) = wl_state_locals s /\
      wl_state_clock (wl_set_store v x s) = wl_state_clock s) /\
   (!i v x (s:(A,C,FFI)wl_state).
      wl_get_var i (wl_set_store v x s) = wl_get_var i s)`,
  REWRITE_TAC[wl_set_var_def; wl_set_store_def; wl_get_var_def;
              wl_state_INFO.ri_accfupds; K_THM]);;

let WBIGPAUX_state_rel_set_var = prove
 (`!i x s (t:(A,C,FFI)wl_state) cs t0 frame.
     word_bignumProof_state_rel s (wl_set_var i x t) cs t0 frame <=>
     word_bignumProof_state_rel s t cs t0 frame`,
  REWRITE_TAC[wl_set_var_def; WBIGPAUX_state_rel_locals]);;

let WBIGPAUX_compile_Assign = prove
 (el 3 WBIGPAUX_compile_cases,
  WBIGPAUX_CPRE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_bignumProof_syntax_ok_def; syntax_ok_aux_def]) THEN
  MP_TAC(INST [`s:(A)word_bignumProof_state`,`s1:(A)word_bignumProof_state`]
    word_bignumProof_compile_exp_thm) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `wl_set_store (Temp (word n)) (wl_Word (eval_exp s x))
                (wl_set_var i (wl_Word (eval_exp s x)) (t1:(A,C,FFI)wl_state))` THEN
  REWRITE_TAC[UNWIND_THM1; WBIGPAUX_ev_Seq; WBIGPAUX_ev_Assign; WBIGPAUX_ev_Set] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "store_name"; wl_word_exp_def; WBIGPAUX_get_var_set_var] THEN
  CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[WBIGPAUX_set_var_simps; WBIGPAUX_get_var_set_var;
               ARITH_RULE `0 < i ==> ~(0 = i) /\ 0 < i + 1`] THEN
  MATCH_MP_TAC WBIGPAUX_state_rel_reg_write THEN
  ASM_REWRITE_TAC[WBIGPAUX_state_rel_set_var]);;


(* the compiled code of Seq, If and Loop, with named intermediate results *)

let WBIGPAUX_compile_Seq_eq = prove
 (`!n l i cs (p1:(A)mini) p2 q l1 i1 cs1.
     word_bignum_compile n l i cs (word_bignum_Seq p1 p2) = (q,l1,i1,cs1) <=>
     ?wq1 wla wia wcsa wq2.
       word_bignum_compile n l i cs p1 = (wq1,wla,wia,wcsa) /\
       word_bignum_compile n wla wia wcsa p2 = (wq2,l1,i1,cs1) /\
       q = wl_Seq wq1 wq2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_bignum_compile_def] THEN
  REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  EQ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN ASM_MESON_TAC[PAIR_EQ]);;

let WBIGPAUX_syntax_ok_aux_IMP = prove
 (`!p:(A)mini. syntax_ok_aux p ==>
               word_bignumProof_syntax_ok p /\ !b. ~(p = LoopBody b)`,
  MATCH_MP_TAC mini_INDUCT THEN
  REWRITE_TAC[syntax_ok_aux_def; word_bignumProof_syntax_ok_def;
              distinctness "mini"]);;

let WBIGPAUX_PROGSUBST_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> let c = concl th in
    is_eq c && is_var (lhs c) && type_of (lhs c) = `:(A)wl_prog`));;

let WBIGPAUX_compile_Seq = prove
 (el 4 WBIGPAUX_compile_cases,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[WBIGPAUX_compile_Seq_eq] THEN STRIP_TAC THEN
  WBIGPAUX_PROGSUBST_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_bignumProof_syntax_ok_def; syntax_ok_aux_def;
                              distinctness "mini"]) THEN
  REWRITE_TAC[GSYM evaluate_Seq_Seq] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN (STRIP_ASSUME_TAC o MATCH_MP WBIGPAUX_syntax_ok_aux_IMP)) THEN
  SUBGOAL_THEN `code_subset (wcsa:num#((A)mini#num#(A)wl_prog)list)
                 (cs2:num#((A)mini#num#(A)wl_prog)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[compile_IMP_code_subset; WBIGPAUX_code_subset_trans]; ALL_TAC] THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`n:num`; `l:num`; `i:num`;
     `cs:num#((A)mini#num#(A)wl_prog)list`;
     `wq1:(A)wl_prog`; `wla:num`; `wia:num`; `wcsa:num#((A)mini#num#(A)wl_prog)list`;
     `cs2:num#((A)mini#num#(A)wl_prog)list`; `t1:(A,C,FFI)wl_state`; `ret_val:(A)word_loc`;
     `wl_Seq wq2 p9:(A)wl_prog`]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u2:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "ih2" (MP_TAC o SPECL [`n:num`; `wla:num`; `wia:num`;
     `wcsa:num#((A)mini#num#(A)wl_prog)list`;
     `wq2:(A)wl_prog`; `l1:num`; `i1:num`; `cs1:num#((A)mini#num#(A)wl_prog)list`;
     `cs2:num#((A)mini#num#(A)wl_prog)list`; `u2:(A,C,FFI)wl_state`; `ret_val:(A)word_loc`;
     `p9:(A)wl_prog`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u3:(A,C,FFI)wl_state` (X_CHOOSE_THEN
    `res2:((A)wl_result)option#(A,C,FFI)wl_state` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `u3:(A,C,FFI)wl_state` THEN
  DISJ_CASES_THEN (X_CHOOSE_THEN `v3:(A)word_bignumProof_state` SUBST_ALL_TAC)
    (ISPEC `s3:(A)word_bignumProof_state+(A)word_bignumProof_state` (cases "sum")) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN CASE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let WBIGPAUX_word_cmp_Word = prove
 (`!c (a:A word) b. wl_word_cmp c (wl_Word a) (wl_Word b) = SOME (asm_word_cmp c a b)`,
  MATCH_MP_TAC cmp_INDUCT THEN REWRITE_TAC[wl_word_cmp_def; asm_word_cmp_def]);;
let WBIGPAUX_ev_If_Word = prove
 (`!c r1 ri c1 c2 (s:(A,C,FFI)wl_state) a b.
     wl_get_var r1 s = SOME (wl_Word a) /\ wl_get_var_imm ri s = SOME (wl_Word b) ==>
     wl_evaluate (wl_If c r1 ri c1 c2,s) =
     wl_evaluate ((if asm_word_cmp c a b then c1 else c2),s)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WBIGPAUX_ev_If] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[WBIGPAUX_word_cmp_Word] THEN CASE_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let WBIGPAUX_ev_SeqTemp_Seq = prove
 (`!i r p p9 (t:(A,C,FFI)wl_state).
     Temp (word r) IN FDOM (wl_state_store t) ==>
     wl_evaluate (wl_Seq (SeqTemp i r p) p9,t) =
     wl_evaluate (wl_Seq p p9,wl_set_var i (FAPPLY (wl_state_store t) (Temp (word r))) t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SeqTemp_def; GSYM evaluate_Seq_Seq] THEN
  REWRITE_TAC[GSYM SeqTemp_def] THEN
  GEN_REWRITE_TAC LAND_CONV [evaluate_SeqTemp] THEN ASM_REWRITE_TAC[]);;

let WBIGPAUX_compile_If_eq = prove
 (CASE_TERM
  `!n l i cs c r (ri:(A)reg_imm) p1 p2 q l1 i1 cs1.
     word_bignum_compile n l i cs (word_bignum_If c r ri p1 p2) = (q,l1,i1,cs1) ==>
     ?wq1 wla wia wcsa wq2 wib.
       word_bignum_compile n l i cs p1 = (wq1,wla,wia,wcsa) /\
       word_bignum_compile n wla wia wcsa p2 = (wq2,l1,wib,cs1) /\
       (match ri with
          Reg r2 -> q = SeqTemp wib r (SeqTemp (wib + 1) r2
                          (wl_If c wib (Reg (wib + 1)) wq1 wq2)) /\ i1 = wib + 2
        | Imm im -> q = SeqTemp wib r (wl_If c wib ri wq1 wq2) /\ i1 = wib + 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_bignum_compile_def] THEN
  REPEAT PAIRARG_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`p1:(A)wl_prog`; `l':num`; `i':num`;
      `cs':num#((A)mini#num#(A)wl_prog)list`; `p2:(A)wl_prog`; `i'':num`] THEN
  ASM_REWRITE_TAC[PAIR_EQ]);;

let WBIGPAUX_compile_If = prove
 (el 5 WBIGPAUX_compile_cases,
  (REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ih"))) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP WBIGPAUX_compile_If_eq)
    STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_bignumProof_syntax_ok_def; syntax_ok_aux_def;
                              distinctness "mini"]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN (STRIP_ASSUME_TAC o MATCH_MP WBIGPAUX_syntax_ok_aux_IMP)))) THEN
  MP_TAC state_rel_IN_FDOM THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC) THEN
  (SUBGOAL_THEN `0 < wia /\ 0 < wib` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[compile_IMP_code_subset; LTE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `code_subset (wcsa:num#((A)mini#num#(A)wl_prog)list)
                 (cs2:num#((A)mini#num#(A)wl_prog)list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[compile_IMP_code_subset; WBIGPAUX_code_subset_trans]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?u:(A,C,FFI)wl_state.
      wl_evaluate (wl_Seq p1' p9,t1) =
      wl_evaluate (wl_Seq (if asm_word_cmp c (eval_exp s1 (wl_Var r)) (eval_ri s1 ri)
                           then wq1 else wq2) p9,u) /\
      wl_state_stack u = wl_state_stack t1 /\ wl_state_code u = wl_state_code t1 /\
      wl_get_var 0 u = wl_get_var 0 t1 /\
      word_bignumProof_state_rel s1 u cs2 t0 frame`
   STRIP_ASSUME_TAC THENL
   [DISJ_CASES_THEN2 (X_CHOOSE_THEN `r2:num` SUBST_ALL_TAC)
      (X_CHOOSE_THEN `im:A word` SUBST_ALL_TAC)
      (ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN
    RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC o check (fun th ->
      is_conj (concl th) && is_eq (lhand (concl th)) &&
      type_of (lhand (lhand (concl th))) = `:(A)wl_prog`)) THEN
    ASM_SIMP_TAC[WBIGPAUX_ev_SeqTemp_Seq] THENL
     [(SUBGOAL_THEN `r2 IN FDOM (word_bignumProof_state_regs (s1:(A)word_bignumProof_state))`
    ASSUME_TAC THENL
   [UNDISCH_TAC `eval_ri_pre (s1:(A)word_bignumProof_state) (Reg r2)` THEN
    REWRITE_TAC[eval_ri_pre_def; eval_exp_pre_def]; ALL_TAC] THEN
  MP_TAC(INST [`r2:num`,`r:num`] state_rel_IN_FDOM) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[WBIGPAUX_ev_SeqTemp_Seq; WBIGPAUX_set_var_simps] THEN
  EXISTS_TAC `wl_set_var (wib + 1) (wl_Word (FAPPLY (word_bignumProof_state_regs s1) r2))
    (wl_set_var wib (wl_Word (FAPPLY (word_bignumProof_state_regs s1) r))
       (t1:(A,C,FFI)wl_state))` THEN
  ASM_REWRITE_TAC[WBIGPAUX_set_var_simps; WBIGPAUX_get_var_set_var;
                  WBIGPAUX_state_rel_set_var] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < w ==> ~(0 = w + 1) /\ ~(0 = w)`] THEN
  REWRITE_TAC[WBIGPAUX_ev_Seq] THEN
  MP_TAC(ISPECL [`c:cmp`; `wib:num`; `Reg (wib + 1):(A)reg_imm`; `wq1:(A)wl_prog`;
    `wq2:(A)wl_prog`;
    `wl_set_var (wib + 1) (wl_Word (FAPPLY (word_bignumProof_state_regs s1) r2))
       (wl_set_var wib (wl_Word (FAPPLY (word_bignumProof_state_regs s1) r))
          (t1:(A,C,FFI)wl_state))`;
    `FAPPLY (word_bignumProof_state_regs (s1:(A)word_bignumProof_state)) r`;
    `FAPPLY (word_bignumProof_state_regs (s1:(A)word_bignumProof_state)) r2`]
    WBIGPAUX_ev_If_Word) THEN
  REWRITE_TAC[wl_get_var_imm_def; WBIGPAUX_get_var_set_var;
              ARITH_RULE `~(w = w + 1)`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[eval_exp_def; eval_ri_def]);
      (EXISTS_TAC `wl_set_var wib (wl_Word (FAPPLY (word_bignumProof_state_regs s1) r))
       (t1:(A,C,FFI)wl_state)` THEN
  ASM_REWRITE_TAC[WBIGPAUX_set_var_simps; WBIGPAUX_get_var_set_var;
                  WBIGPAUX_state_rel_set_var] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < w ==> ~(0 = w)`] THEN
  REWRITE_TAC[WBIGPAUX_ev_Seq] THEN
  MP_TAC(ISPECL [`c:cmp`; `wib:num`; `Imm im:(A)reg_imm`; `wq1:(A)wl_prog`;
    `wq2:(A)wl_prog`;
    `wl_set_var wib (wl_Word (FAPPLY (word_bignumProof_state_regs s1) r))
          (t1:(A,C,FFI)wl_state)`;
    `FAPPLY (word_bignumProof_state_regs (s1:(A)word_bignumProof_state)) r`;
    `im:A word`] WBIGPAUX_ev_If_Word) THEN
  REWRITE_TAC[wl_get_var_imm_def; WBIGPAUX_get_var_set_var] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[eval_exp_def; eval_ri_def])];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `0 < i1` ASSUME_TAC THENL
   [UNDISCH_TAC `0 < wib` THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> t = `i1:num`)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "reg_imm_CASE"
                               with _ -> false)) (concl th))) THEN
    STRUCT_CASES_TAC (ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN
    CASE_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `asm_word_cmp c (eval_exp (s1:(A)word_bignumProof_state) (wl_Var r))
                   (eval_ri s1 ri)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
   [REMOVE_THEN "ih" (MP_TAC o SPECL [`n:num`; `l:num`; `i:num`;
      `cs:num#((A)mini#num#(A)wl_prog)list`;
      `wq1:(A)wl_prog`; `wla:num`; `wia:num`; `wcsa:num#((A)mini#num#(A)wl_prog)list`;
      `cs2:num#((A)mini#num#(A)wl_prog)list`; `u:(A,C,FFI)wl_state`; `ret_val:(A)word_loc`;
      `p9:(A)wl_prog`]);
    REMOVE_THEN "ih" (MP_TAC o SPECL [`n:num`; `wla:num`; `wia:num`;
      `wcsa:num#((A)mini#num#(A)wl_prog)list`;
      `wq2:(A)wl_prog`; `l1:num`; `wib:num`; `cs1:num#((A)mini#num#(A)wl_prog)list`;
      `cs2:num#((A)mini#num#(A)wl_prog)list`; `u:(A,C,FFI)wl_state`; `ret_val:(A)word_loc`;
      `p9:(A)wl_prog`])] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u3:(A,C,FFI)wl_state` (X_CHOOSE_THEN
    `res2:((A)wl_result)option#(A,C,FFI)wl_state` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `u3:(A,C,FFI)wl_state` THEN
  DISJ_CASES_THEN (X_CHOOSE_THEN `v3:(A)word_bignumProof_state` SUBST_ALL_TAC)
    (ISPEC `s2:(A)word_bignumProof_state+(A)word_bignumProof_state` (cases "sum")) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN CASE_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]));;


(* reading and writing an element of an array in memory *)

let WBIGPAUX_STAR_AC = prove
 (`(!p q:(A->bool)->bool. p STAR q = q STAR p) /\
   (!p q r:(A->bool)->bool. (p STAR q) STAR r = p STAR (q STAR r)) /\
   (!p q r:(A->bool)->bool. p STAR (q STAR r) = q STAR (p STAR r))`,
  MESON_TAC[STAR_COMM; STAR_ASSOC]);;

let WBIGPAUX_word_list_read = prove
 (`!(a:A word) ys (z:A word) zs rest m dm.
     (misc_word_list a (MAP wl_Word (APPEND ys (CONS z zs))) STAR rest)
       (fun2set (m,dm)) ==>
     m (word_add a (word_mul (word (LENGTH ys)) bytes_in_word)) = wl_Word z /\
     word_add a (word_mul (word (LENGTH ys)) bytes_in_word) IN dm`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MAP_APPEND; MAP; word_bignumProof_word_list_APPEND; misc_word_list_def;
              LENGTH_MAP] THEN
  ONCE_REWRITE_TAC[AC WBIGPAUX_STAR_AC
    `((p:(A word#(A)word_loc->bool)->bool) STAR (q STAR r)) STAR u =
     q STAR (p STAR r STAR u)`] THEN
  MATCH_ACCEPT_TAC read_fun2set);;

let WBIGPAUX_word_list_write = prove
 (`!(a:A word) ys (z:A word) zs rest m dm w.
     (misc_word_list a (MAP wl_Word (APPEND ys (CONS z zs))) STAR rest)
       (fun2set (m,dm)) ==>
     (misc_word_list a (MAP wl_Word (APPEND ys (CONS w zs))) STAR rest)
       (fun2set ((word_add a (word_mul (word (LENGTH ys)) bytes_in_word) =+ wl_Word w) m,
                 dm))`,
  let l1 = AC WBIGPAUX_STAR_AC
    `((p:(A word#(A)word_loc->bool)->bool) STAR (q STAR r)) STAR u =
     q STAR ((p STAR r) STAR u)`
  in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MAP_APPEND; MAP; word_bignumProof_word_list_APPEND; misc_word_list_def;
              LENGTH_MAP] THEN
  REWRITE_TAC[l1] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ISPEC `wl_Word (w:A word)` write_fun2set)) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[STAR_COMM] THEN ACCEPT_TAC th));;

let WBIGPAUX_ev_SeqIndex_Seq = prove
 (CASE_TERM
  `!i r arr p p9 (t:(A,C,FFI)wl_state) base w.
     good_dimindex (:A) /\
     FLOOKUP (wl_state_store t)
       (match arr with Out -> TempOut | In2 -> TempIn2 | In1 -> TempIn1) =
       SOME (wl_Word base) /\
     FLOOKUP (wl_state_store t) (Temp (word r)) = SOME (wl_Word w) ==>
     wl_evaluate (wl_Seq (SeqIndex i r arr p) p9,t) =
     wl_evaluate (wl_Seq p p9,
       wl_set_var i (wl_Word (word_add base (word_mul w bytes_in_word))) t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SeqIndex_def; LET_DEF; LET_END_DEF; GSYM evaluate_Seq_Seq] THEN
  GEN_REWRITE_TAC LAND_CONV [WBIGPAUX_ev_Seq] THEN
  REWRITE_TAC[WBIGPAUX_ev_Assign; wl_word_exp_def; MAP; wl_get_store_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[word_sh_def; the_words_def] THEN
  SUBGOAL_THEN `~(val (word (backend_common_word_shift (:A)):A word) >= dimindex(:A))`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[VAL_WORD; NOT_LE; GE] THEN MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `backend_common_word_shift (:A)` THEN REWRITE_TAC[MOD_LE] THEN
    UNDISCH_TAC `good_dimindex (:A)` THEN
    REWRITE_TAC[good_dimindex_def; backend_common_word_shift_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[OPTION_MAP_DEF] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[word_op_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[ITLIST; WORD_ADD_0; OPTION_MAP_DEF; VAL_WORD; GSYM dimword_def] THEN
  CASE_REWRITE_TAC[] THEN ASM_SIMP_TAC[shift_eq_bytes_in_word]);;

let WBIGPAUX_array_rel_read = prove
 (CASE_TERM
  `!(arr:address->(A word)list) st m dm frame a.
     array_rel arr (FLOOKUP st TempIn1) (FLOOKUP st TempIn2) (FLOOKUP st TempOut)
       m dm frame ==>
     ?base R. FLOOKUP st (match a with Out -> TempOut | In2 -> TempIn2 | In1 -> TempIn1) =
              SOME (wl_Word base) /\
              (misc_word_list base (MAP wl_Word (arr a)) STAR R) (fun2set (m,dm))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[array_rel_def] THEN STRIP_TAC THEN
  STRUCT_CASES_TAC (ISPEC `a:address` (cases "address")) THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[option_INJ; injectivity "word_loc"] THENL
   [EXISTS_TAC `a1:A word`; EXISTS_TAC `a2:A word`; EXISTS_TAC `a3:A word`] THEN
  REWRITE_TAC[] THEN ASM_MESON_TAC[STAR_ASSOC]);;

let WBIGPAUX_set_var_simps2 = prove
 (`(!i x (s:(A,C,FFI)wl_state).
      wl_state_memory (wl_set_var i x s) = wl_state_memory s /\
      wl_state_mdomain (wl_set_var i x s) = wl_state_mdomain s /\
      wl_state_termdep (wl_set_var i x s) = wl_state_termdep s /\
      wl_state_permute (wl_set_var i x s) = wl_state_permute s /\
      wl_state_stack_size (wl_set_var i x s) = wl_state_stack_size s) /\
   (!v x (s:(A,C,FFI)wl_state).
      wl_state_memory (wl_set_store v x s) = wl_state_memory s /\
      wl_state_mdomain (wl_set_store v x s) = wl_state_mdomain s /\
      wl_state_termdep (wl_set_store v x s) = wl_state_termdep s /\
      wl_state_permute (wl_set_store v x s) = wl_state_permute s /\
      wl_state_stack_size (wl_set_store v x s) = wl_state_stack_size s)`,
  REWRITE_TAC[wl_set_var_def; wl_set_store_def; wl_state_INFO.ri_accfupds; K_THM]);;

let WBIGPAUX_compile_Load = prove
 (el 6 WBIGPAUX_compile_cases,
  (WBIGPAUX_CPRE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_bignumProof_syntax_ok_def; syntax_ok_aux_def])) THEN
  (SUBGOAL_THEN `FLOOKUP (wl_state_store (t1:(A,C,FFI)wl_state)) (Temp (word i)) =
                SOME (wl_Word w) /\ i < 25`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `word_bignumProof_state_rel (s:(A)word_bignumProof_state)
                   (t1:(A,C,FFI)wl_state) cs2 t0 frame` THEN
    REWRITE_TAC[word_bignumProof_state_rel_def] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`word_bignumProof_state_arrays (s:(A)word_bignumProof_state)`;
    `wl_state_store (t1:(A,C,FFI)wl_state)`; `wl_state_memory (t1:(A,C,FFI)wl_state)`;
    `wl_state_mdomain (t1:(A,C,FFI)wl_state)`;
    `frame:((A word#(A)word_loc)->bool)->bool`; `a:address`] WBIGPAUX_array_rel_read) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `word_bignumProof_state_rel (s:(A)word_bignumProof_state)
                   (t1:(A,C,FFI)wl_state) cs2 t0 frame` THEN
    SIMP_TAC[word_bignumProof_state_rel_def];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `base:A word` (X_CHOOSE_THEN
    `R:((A word#(A)word_loc)->bool)->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`word_bignumProof_state_arrays (s:(A)word_bignumProof_state) a`;
                 `val (w:A word)`]
    word_bignumProof_LESS_LENGTH_IMP_APPEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ys:(A word)list` (X_CHOOSE_THEN `z:A word`
    (X_CHOOSE_THEN `zs:(A word)list` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(fun th0 ->
    let th = check (fun th -> is_eq (concl th) &&
                     rand (concl th) = `APPEND (ys:(A word)list) (CONS z zs)`) th0 in
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WBIGPAUX_word_list_read) THEN
  ASM_REWRITE_TAC[WORD_VAL] THEN STRIP_TAC) THEN
  (ASM_SIMP_TAC[WBIGPAUX_ev_SeqIndex_Seq] THEN
  EXISTS_TAC `wl_set_store (Temp (word r)) (wl_Word z)
     (wl_set_var (i' + 1) (wl_Word z)
       (wl_set_var i' (wl_Word (word_add base (word_mul w bytes_in_word)))
         (t1:(A,C,FFI)wl_state)))` THEN
  REWRITE_TAC[UNWIND_THM1; GSYM evaluate_Seq_Seq] THEN
  REWRITE_TAC[WBIGPAUX_ev_Seq; WBIGPAUX_ev_Assign; WBIGPAUX_ev_Set; wl_word_exp_def;
              WBIGPAUX_get_var_set_var; distinctness "store_name"] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_mem_load_def; WBIGPAUX_set_var_simps2] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[WBIGPAUX_get_var_set_var] THEN CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[WBIGPAUX_set_var_simps; WBIGPAUX_get_var_set_var;
               ARITH_RULE `0 < i ==> ~(0 = i) /\ ~(0 = i + 1) /\ 0 < i + 2`] THEN
  SUBGOAL_THEN `EL (val (w:A word)) (APPEND ys (CONS z zs)) = z:A word` SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `LENGTH (ys:(A word)list) = val (w:A word)`)) THEN
    REWRITE_TAC[LBIGAUX_EL_LENGTH_CONS]; ALL_TAC] THEN
  MATCH_MP_TAC WBIGPAUX_state_rel_reg_write THEN
  ASM_REWRITE_TAC[WBIGPAUX_state_rel_set_var]));;


let WBIGPAUX_array_rel_write_Out = prove
 (`!(arr:address->(A word)list) v1 v2 a3 m dm frame ys z zs w.
     array_rel arr v1 v2 (SOME (wl_Word a3)) m dm frame /\
     arr Out = APPEND ys (CONS z zs) ==>
     array_rel ((Out =+ APPEND ys (CONS w zs)) arr) v1 v2 (SOME (wl_Word a3))
       ((word_add a3 (word_mul (word (LENGTH ys)) bytes_in_word) =+ wl_Word w) m) dm
       frame`,
  let l1 = AC WBIGPAUX_STAR_AC
    `((p:(A word#(A)word_loc->bool)->bool) STAR q) STAR r = q STAR (p STAR r)` in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[array_rel_def; APPLY_UPDATE_THM; distinctness "address";
              option_INJ; injectivity "word_loc"] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq (concl th) &&
    is_var (lhs (concl th)) && is_var (rhs (concl th)))) THEN
  MAP_EVERY EXISTS_TAC
    [`a1:A word`; `a2:A word`; `a3:A word`; `rest1:((A word#(A)word_loc)->bool)->bool`;
     `rest2:((A word#(A)word_loc)->bool)->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[l1]) THEN REWRITE_TAC[l1] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC WBIGPAUX_word_list_write THEN
  EXISTS_TAC `z:A word` THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_REWRITE_TAC[]);;

let WBIGPAUX_state_rel_mem_write = prove
 (`!s (t:(A,C,FFI)wl_state) cs t0 frame a3 ys z zs w.
     word_bignumProof_state_rel s t cs t0 frame /\
     FLOOKUP (wl_state_store t) TempOut = SOME (wl_Word a3) /\
     word_bignumProof_state_arrays s Out = APPEND ys (CONS z zs) ==>
     word_bignumProof_state_rel (array_write Out (APPEND ys (CONS w zs)) s)
       (wl_state_memory_fupd
          (K ((word_add a3 (word_mul (word (LENGTH ys)) bytes_in_word) =+ wl_Word w)
                (wl_state_memory t))) t) cs t0 frame`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_bignumProof_state_rel_def; WBIGPAUX_array_write_simp;
              wl_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[check (fun th -> concl th =
    `FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) TempOut = SOME (wl_Word a3)`) th]) THEN
  MATCH_MP_TAC WBIGPAUX_array_rel_write_Out THEN
  EXISTS_TAC `z:A word` THEN ASM_MESON_TAC[]);;


let WBIGPAUX_compile_Store = prove
 (el 7 WBIGPAUX_compile_cases,
  (WBIGPAUX_CPRE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_bignumProof_syntax_ok_def; syntax_ok_aux_def])) THEN
  (SUBGOAL_THEN `FLOOKUP (wl_state_store (t1:(A,C,FFI)wl_state)) (Temp (word i)) =
                SOME (wl_Word w) /\
                FLOOKUP (wl_state_store (t1:(A,C,FFI)wl_state)) (Temp (word r)) =
                SOME (wl_Word wr)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `word_bignumProof_state_rel (s:(A)word_bignumProof_state)
                   (t1:(A,C,FFI)wl_state) cs2 t0 frame` THEN
    REWRITE_TAC[word_bignumProof_state_rel_def] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`word_bignumProof_state_arrays (s:(A)word_bignumProof_state)`;
    `wl_state_store (t1:(A,C,FFI)wl_state)`; `wl_state_memory (t1:(A,C,FFI)wl_state)`;
    `wl_state_mdomain (t1:(A,C,FFI)wl_state)`;
    `frame:((A word#(A)word_loc)->bool)->bool`; `Out`] WBIGPAUX_array_rel_read) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `word_bignumProof_state_rel (s:(A)word_bignumProof_state)
                   (t1:(A,C,FFI)wl_state) cs2 t0 frame` THEN
    SIMP_TAC[word_bignumProof_state_rel_def];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `base:A word` (X_CHOOSE_THEN
    `R:((A word#(A)word_loc)->bool)->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`word_bignumProof_state_arrays (s:(A)word_bignumProof_state) Out`;
                 `val (w:A word)`] word_bignumProof_LESS_LENGTH_IMP_APPEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ys:(A word)list` (X_CHOOSE_THEN `z:A word`
    (X_CHOOSE_THEN `zs:(A word)list` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(fun th0 ->
    let th = check (fun th -> is_eq (concl th) &&
                     rand (concl th) = `APPEND (ys:(A word)list) (CONS z zs)`) th0 in
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WBIGPAUX_word_list_read) THEN
  ASM_REWRITE_TAC[WORD_VAL] THEN STRIP_TAC) THEN
  (SUBGOAL_THEN `Temp (word r) IN FDOM (wl_state_store (t1:(A,C,FFI)wl_state)) /\
                FAPPLY (wl_state_store t1) (Temp (word r)) = wl_Word wr`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `FLOOKUP (wl_state_store (t1:(A,C,FFI)wl_state)) (Temp (word r)) =
                 SOME (wl_Word wr)` THEN
    REWRITE_TAC[FLOOKUP_DEF] THEN COND_CASES_TAC THEN
    REWRITE_TAC[option_DISTINCT; option_INJ]; ALL_TAC] THEN
  ASM_SIMP_TAC[WBIGPAUX_ev_SeqTemp_Seq] THEN
  MP_TAC(ISPECL [`i' + 1`; `i:num`; `Out`; `wl_Store (wl_Var (i' + 1)) i':(A)wl_prog`;
    `p9:(A)wl_prog`; `wl_set_var i' (wl_Word wr) (t1:(A,C,FFI)wl_state)`;
    `base:A word`; `w:A word`] WBIGPAUX_ev_SeqIndex_Seq) THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[WBIGPAUX_set_var_simps] THEN
  DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `u = wl_set_var (i' + 1) (wl_Word (word_add base (word_mul w bytes_in_word)))
                    (wl_set_var i' (wl_Word wr) (t1:(A,C,FFI)wl_state))` THEN
  EXISTS_TAC `wl_state_memory_fupd
    (K ((word_add base (word_mul w bytes_in_word) =+ wl_Word wr) (wl_state_memory u)))
    (u:(A,C,FFI)wl_state)` THEN
  REWRITE_TAC[UNWIND_THM1; WBIGPAUX_ev_Seq; WBIGPAUX_ev_Store; wl_word_exp_def] THEN
  EXPAND_TAC "u" THEN
  REWRITE_TAC[WBIGPAUX_get_var_set_var; ARITH_RULE `~(i' = i' + 1)`] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_mem_store_def; WBIGPAUX_set_var_simps2] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; WBIGPAUX_set_var_simps; wl_get_var_def] THEN
  REWRITE_TAC[GSYM wl_get_var_def; WBIGPAUX_get_var_set_var] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < i ==> ~(0 = i) /\ ~(0 = i + 1) /\ 0 < i + 2`]) THEN
  (EXPAND_TAC "u" THEN
  REWRITE_TAC[WBIGPAUX_set_var_simps; WBIGPAUX_get_var_set_var] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < i ==> ~(0 = i) /\ ~(0 = i + 1)`] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM (check (fun th -> concl th =
    `LENGTH (ys:(A word)list) = val (w:A word)`) th)]) THEN
  REWRITE_TAC[LUPDATE_LENGTH] THEN
  MP_TAC(ISPECL [`s:(A)word_bignumProof_state`;
    `wl_set_var (i' + 1) (wl_Word (word_add base (word_mul w bytes_in_word)))
       (wl_set_var i' (wl_Word wr) (t1:(A,C,FFI)wl_state))`;
    `cs2:num#((A)mini#num#(A)wl_prog)list`; `t0:(A,C,FFI)wl_state`;
    `frame:((A word#(A)word_loc)->bool)->bool`; `base:A word`; `ys:(A word)list`;
    `z:A word`; `zs:(A word)list`; `wr:A word`] WBIGPAUX_state_rel_mem_write) THEN
  ASM_REWRITE_TAC[WBIGPAUX_state_rel_set_var; WBIGPAUX_set_var_simps;
                  WBIGPAUX_set_var_simps2; WORD_VAL]));;


let WBIGPAUX_TempIn_distinct = prove
 (`~(TempIn1 = TempIn2) /\ ~(TempIn1 = TempOut) /\ ~(TempIn2 = TempOut) /\
   ~(TempIn2 = TempIn1) /\ ~(TempOut = TempIn1) /\ ~(TempOut = TempIn2) /\
   ~(TempIn1 = Handler) /\ ~(TempIn1 = BitmapBase) /\
   ~(TempIn2 = Handler) /\ ~(TempIn2 = BitmapBase)`,
  REWRITE_TAC[TempIn1_def; TempIn2_def; TempOut_def; injectivity "store_name";
              distinctness "store_name"; GSYM VAL_EQ; VAL_WORD;
              DIMINDEX_CONV `dimindex(:5)`] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let WBIGPAUX_state_rel_swap = prove
 (`!s (t:(A,C,FFI)wl_state) cs t0 frame a1 a2.
     word_bignumProof_state_rel s t cs t0 frame /\
     FLOOKUP (wl_state_store t) TempIn1 = SOME (wl_Word a1) /\
     FLOOKUP (wl_state_store t) TempIn2 = SOME (wl_Word a2) ==>
     word_bignumProof_state_rel
       (array_write In1 (word_bignumProof_state_arrays s In2)
          (array_write In2 (word_bignumProof_state_arrays s In1) s))
       (wl_set_store TempIn2 (wl_Word a1) (wl_set_store TempIn1 (wl_Word a2) t))
       cs t0 frame`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_bignumProof_state_rel_def; WBIGPAUX_array_write_simp; wl_set_store_def;
              wl_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE; APPLY_UPDATE_THM;
              WBIGPAUX_TempIn_distinct; distinctness "address"] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `array_rel (word_bignumProof_state_arrays (s:(A)word_bignumProof_state))
       (FLOOKUP (wl_state_store (t:(A,C,FFI)wl_state)) TempIn1)
       (FLOOKUP (wl_state_store t) TempIn2) (FLOOKUP (wl_state_store t) TempOut)
       (wl_state_memory t) (wl_state_mdomain t) frame` THEN
    ASM_REWRITE_TAC[array_rel_def; APPLY_UPDATE_THM; distinctness "address";
                    option_INJ; injectivity "word_loc"] THEN
    MESON_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN RES_TAC THEN
    ASM_SIMP_TAC[WBIGPAUX_Temp_TempIn];
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(TempIn2 = n) /\ ~(TempIn1 = n)` (fun th -> ASM_SIMP_TAC[th]) THEN
    REWRITE_TAC[TempIn1_def; TempIn2_def] THEN ASM_MESON_TAC[]]);;


(* the carry instruction computes single_add_word *)

let WBIGPAUX_word_add_carry = prove
 (`!l r (c:A word). word_add_carry l r c = single_add_word l r c`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_add_carry_def; single_add_word_thm; single_add_def;
              LET_DEF; LET_END_DEF; multiword_b2w_def; PAIR_EQ] THEN
  ASM_CASES_TAC `c = word 0:A word` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; GSYM ADD_ASSOC] THEN
  REWRITE_TAC[WORD_ADD; WORD_VAL; WORD_ADD_0] THEN
  REPEAT CONJ_TAC THEN
  (CONV_TAC WORD_RULE ORELSE (COND_CASES_TAC THEN REWRITE_TAC[BITVAL_CLAUSES])));;

let WBIGPAUX_single_sub_word = prove
 (`!l r (c:A word). single_sub_word l r c = single_add_word l (word_not r) c`,
  REWRITE_TAC[single_sub_word_thm; single_add_word_thm; single_sub_def]);;

(* the value of a register or immediate in the compiled code *)

let WBIGPAUX_ri_value = prove
 (CASE_TERM
  `!s (t:(A,C,FFI)wl_state) cs t0 frame ri.
     word_bignumProof_state_rel s t cs t0 frame /\ eval_ri_pre s ri ==>
     (!r. ri = Reg r ==> Temp (word r) IN FDOM (wl_state_store t)) /\
     (match ri with Imm w -> wl_Word w
      | Reg r -> FAPPLY (wl_state_store t) (Temp (word r))) =
     wl_Word (eval_ri s ri) /\
     (match ri with Imm w -> wl_Word (word_not w)
      | Reg r -> (match FAPPLY (wl_state_store t) (Temp (word r))
                  with wl_Word w -> wl_Word (word_not w))) =
     wl_Word (word_not (eval_ri s ri)) /\
     (!r. ri = Reg r ==> Temp (word r) IN FDOM (wl_state_store t) /\
          ?w. FAPPLY (wl_state_store t) (Temp (word r)) = wl_Word w)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN
  REWRITE_TAC[eval_ri_pre_def; eval_exp_pre_def; eval_ri_def; eval_exp_def;
              injectivity "reg_imm"; distinctness "reg_imm";
              FORALL_UNWIND_THM1; FORALL_UNWIND_THM2] THEN
  CASE_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(INST [`s:(A)word_bignumProof_state`,`s1:(A)word_bignumProof_state`;
               `t:(A,C,FFI)wl_state`,`t1:(A,C,FFI)wl_state`;
               `cs:num#((A)mini#num#(A)wl_prog)list`,
               `cs2:num#((A)mini#num#(A)wl_prog)list`;
               `a:num`,`r:num`] state_rel_IN_FDOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

let WBIGPAUX_ev_SeqTempImm_Seq = prove
 (CASE_TERM
  `!i ri p p9 (t:(A,C,FFI)wl_state).
     (!r. ri = Reg r ==> Temp (word r) IN FDOM (wl_state_store t)) ==>
     wl_evaluate (wl_Seq (SeqTempImm i ri p) p9,t) =
     wl_evaluate (wl_Seq p p9,
       wl_set_var i (match ri with Imm w -> wl_Word w
                     | Reg r -> FAPPLY (wl_state_store t) (Temp (word r))) t)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN
  REWRITE_TAC[injectivity "reg_imm"; distinctness "reg_imm";
              FORALL_UNWIND_THM1; FORALL_UNWIND_THM2] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[SeqTempImm_def] THEN
  SIMP_TAC[WBIGPAUX_ev_SeqTemp_Seq] THEN
  REWRITE_TAC[GSYM evaluate_Seq_Seq] THEN
  GEN_REWRITE_TAC LAND_CONV [WBIGPAUX_ev_Seq] THEN
  REWRITE_TAC[WBIGPAUX_ev_Assign; wl_word_exp_def] THEN CASE_REWRITE_TAC[]);;

let WBIGPAUX_ev_Seq_cong = prove
 (`!c p q (t:(A,C,FFI)wl_state).
     (!s:(A,C,FFI)wl_state. wl_evaluate (p,s) = wl_evaluate (q,s)) ==>
     wl_evaluate (wl_Seq c p,t) = wl_evaluate (wl_Seq c q,t)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WBIGPAUX_ev_Seq]);;

let WBIGPAUX_ev_SeqTempImmNot_Seq = prove
 (CASE_TERM
  `!i ri p p9 (t:(A,C,FFI)wl_state).
     (!r. ri = Reg r ==> Temp (word r) IN FDOM (wl_state_store t) /\
          ?w. FAPPLY (wl_state_store t) (Temp (word r)) = wl_Word w) ==>
     wl_evaluate (wl_Seq (SeqTempImmNot i ri p) p9,t) =
     wl_evaluate (wl_Seq p p9,
       wl_set_var i (match ri with Imm w -> wl_Word (word_not w)
                     | Reg r -> (match FAPPLY (wl_state_store t) (Temp (word r))
                                 with wl_Word w -> wl_Word (word_not w))) t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `wl_evaluate (wl_Seq (SeqTempImmNot i ri p) p9,(t:(A,C,FFI)wl_state)) =
                wl_evaluate (SeqTempImmNot i ri (wl_Seq p p9),t)` SUBST1_TAC THENL
   [STRUCT_CASES_TAC (ISPEC `ri:(A)reg_imm` (cases "reg_imm")) THEN
    REWRITE_TAC[SeqTempImmNot_def; SeqTemp_def; GSYM evaluate_Seq_Seq] THEN
    MATCH_MP_TAC WBIGPAUX_ev_Seq_cong THEN REWRITE_TAC[GSYM evaluate_Seq_Seq];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [evaluate_SeqTempImmNot] THEN ASM_REWRITE_TAC[]);;


let WBIGPAUX_compile_Swap = prove
 (el 8 WBIGPAUX_compile_cases,
  WBIGPAUX_CPRE_TAC THEN
  SUBGOAL_THEN `?a1 a2. FLOOKUP (wl_state_store (t1:(A,C,FFI)wl_state)) TempIn1 =
                        SOME (wl_Word a1) /\
                        FLOOKUP (wl_state_store t1) TempIn2 = SOME (wl_Word (a2:A word))`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `word_bignumProof_state_rel (s:(A)word_bignumProof_state)
                   (t1:(A,C,FFI)wl_state) cs2 t0 frame` THEN
    REWRITE_TAC[word_bignumProof_state_rel_def; array_rel_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `wl_set_store TempIn2 (wl_Word a1)
     (wl_set_store TempIn1 (wl_Word a2)
       (wl_set_var i (wl_Word a1) (t1:(A,C,FFI)wl_state)))` THEN
  REWRITE_TAC[UNWIND_THM1; GSYM evaluate_Seq_Seq] THEN
  REWRITE_TAC[WBIGPAUX_ev_Seq; WBIGPAUX_ev_Assign; WBIGPAUX_ev_Set; wl_word_exp_def;
              wl_get_store_def; WBIGPAUX_TempIn_distinct] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[WBIGPAUX_set_var_simps; WBIGPAUX_get_var_set_var] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[WBIGPAUX_set_var_simps; WBIGPAUX_get_var_set_var;
               ARITH_RULE `0 < i ==> ~(0 = i) /\ 0 < i + 1`] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC WBIGPAUX_state_rel_swap THEN
  ASM_REWRITE_TAC[WBIGPAUX_state_rel_set_var; WBIGPAUX_set_var_simps]);;

let WBIGPAUX_reg_write_comm = prove
 (`!n1 n2 v1 v2 (s:(A)word_bignumProof_state).
     ~(n1 = n2) ==>
     reg_write n1 (SOME v1) (reg_write n2 (SOME v2) s) =
     reg_write n2 (SOME v2) (reg_write n1 (SOME v1) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[reg_write_def; word_bignumProof_state_component_equality;
    word_bignumProof_state_INFO.ri_accfupds; K_THM] THEN
  MATCH_MP_TAC FUPDATE_COMMUTES THEN ASM_MESON_TAC[]);;

let WBIGPAUX_compile_Add = prove
 (el 9 WBIGPAUX_compile_cases,
  (WBIGPAUX_CPRE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_bignumProof_syntax_ok_def; syntax_ok_aux_def])) THEN
  (MP_TAC(ISPECL [`s:(A)word_bignumProof_state`; `t1:(A,C,FFI)wl_state`;
    `cs2:num#((A)mini#num#(A)wl_prog)list`; `t0:(A,C,FFI)wl_state`;
    `frame:((A word#(A)word_loc)->bool)->bool`; `n5:(A)reg_imm`] WBIGPAUX_ri_value) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(A)word_bignumProof_state`; `t1:(A,C,FFI)wl_state`;
    `cs2:num#((A)mini#num#(A)wl_prog)list`; `t0:(A,C,FFI)wl_state`;
    `frame:((A word#(A)word_loc)->bool)->bool`; `n4:(A)reg_imm`] WBIGPAUX_ri_value) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(INST [`s:(A)word_bignumProof_state`,`s1:(A)word_bignumProof_state`;
               `n3:num`,`r:num`] state_rel_IN_FDOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[WBIGPAUX_ev_SeqTempImm_Seq] THEN
  ASM_SIMP_TAC[WBIGPAUX_ev_SeqTempImm_Seq; WBIGPAUX_set_var_simps] THEN
  ASM_SIMP_TAC[WBIGPAUX_ev_SeqTemp_Seq; WBIGPAUX_set_var_simps]) THEN
  (ABBREV_TAC `u = wl_set_var (i + 2)
      (wl_Word (FAPPLY (word_bignumProof_state_regs s) n3))
      (wl_set_var (i + 3) (wl_Word (eval_ri s n4))
      (wl_set_var (i + 4) (wl_Word (eval_ri s n5)) (t1:(A,C,FFI)wl_state)))` THEN
  EXISTS_TAC `wl_set_store (Temp (word n2)) (wl_Word r2)
     (wl_set_store (Temp (word n1)) (wl_Word r1)
       (wl_set_var (i + 4) (wl_Word r2) (wl_set_var (i + 1) (wl_Word r1)
          (u:(A,C,FFI)wl_state))))` THEN
  REWRITE_TAC[UNWIND_THM1; GSYM evaluate_Seq_Seq] THEN
  REWRITE_TAC[WBIGPAUX_ev_Seq; WBIGPAUX_ev_Inst; wl_inst_def] THEN
  CASE_REWRITE_TAC[] THEN
  EXPAND_TAC "u" THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; wl_get_vars_def; WBIGPAUX_get_var_set_var;
              EQ_ADD_LCANCEL; EQ_ADD_LCANCEL_0; ARITH_EQ] THEN
  CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[WBIGPAUX_word_add_carry] THEN CASE_REWRITE_TAC[]) THEN
  (REWRITE_TAC[WBIGPAUX_ev_Set; distinctness "store_name"; wl_word_exp_def;
              WBIGPAUX_get_var_set_var; EQ_ADD_LCANCEL; EQ_ADD_LCANCEL_0; ARITH_EQ] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[WBIGPAUX_set_var_simps; WBIGPAUX_get_var_set_var; EQ_ADD_LCANCEL;
              EQ_ADD_LCANCEL_0; ARITH_EQ] THEN
  CASE_REWRITE_TAC[] THEN
  EXPAND_TAC "u" THEN
  ASM_SIMP_TAC[WBIGPAUX_set_var_simps; WBIGPAUX_get_var_set_var;
               ARITH_RULE `0 < i ==> ~(0 = i + 1) /\ ~(0 = i + 2) /\ ~(0 = i + 3) /\
                                     ~(0 = i + 4) /\ 0 < i + 5`] THEN
  REWRITE_TAC[MATCH_MP WBIGPAUX_reg_write_comm (ASSUME `~(n1 = n2:num)`)] THEN
  MATCH_MP_TAC WBIGPAUX_state_rel_reg_write THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC WBIGPAUX_state_rel_reg_write THEN
  ASM_REWRITE_TAC[WBIGPAUX_state_rel_set_var] THEN
  EXPAND_TAC "u" THEN ASM_REWRITE_TAC[WBIGPAUX_state_rel_set_var]));;

let WBIGPAUX_compile_Sub = prove
 (el 10 WBIGPAUX_compile_cases,
  (WBIGPAUX_CPRE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_bignumProof_syntax_ok_def; syntax_ok_aux_def])) THEN
  (MP_TAC(ISPECL [`s:(A)word_bignumProof_state`; `t1:(A,C,FFI)wl_state`;
    `cs2:num#((A)mini#num#(A)wl_prog)list`; `t0:(A,C,FFI)wl_state`;
    `frame:((A word#(A)word_loc)->bool)->bool`; `n5:(A)reg_imm`] WBIGPAUX_ri_value) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(A)word_bignumProof_state`; `t1:(A,C,FFI)wl_state`;
    `cs2:num#((A)mini#num#(A)wl_prog)list`; `t0:(A,C,FFI)wl_state`;
    `frame:((A word#(A)word_loc)->bool)->bool`; `n4:(A)reg_imm`] WBIGPAUX_ri_value) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(INST [`s:(A)word_bignumProof_state`,`s1:(A)word_bignumProof_state`;
               `n3:num`,`r:num`] state_rel_IN_FDOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[WBIGPAUX_ev_SeqTempImm_Seq] THEN
  ASM_SIMP_TAC[WBIGPAUX_ev_SeqTempImmNot_Seq; WBIGPAUX_set_var_simps] THEN
  ASM_SIMP_TAC[WBIGPAUX_ev_SeqTemp_Seq; WBIGPAUX_set_var_simps]) THEN
  (ABBREV_TAC `u = wl_set_var (i + 2)
      (wl_Word (FAPPLY (word_bignumProof_state_regs s) n3))
      (wl_set_var (i + 3) (wl_Word (word_not (eval_ri s n4)))
      (wl_set_var (i + 4) (wl_Word (eval_ri s n5)) (t1:(A,C,FFI)wl_state)))` THEN
  EXISTS_TAC `wl_set_store (Temp (word n2)) (wl_Word r2)
     (wl_set_store (Temp (word n1)) (wl_Word r1)
       (wl_set_var (i + 4) (wl_Word r2) (wl_set_var (i + 1) (wl_Word r1)
          (u:(A,C,FFI)wl_state))))` THEN
  REWRITE_TAC[UNWIND_THM1; GSYM evaluate_Seq_Seq] THEN
  REWRITE_TAC[WBIGPAUX_ev_Seq; WBIGPAUX_ev_Inst; wl_inst_def] THEN
  CASE_REWRITE_TAC[] THEN
  EXPAND_TAC "u" THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; wl_get_vars_def; WBIGPAUX_get_var_set_var;
              EQ_ADD_LCANCEL; EQ_ADD_LCANCEL_0; ARITH_EQ] THEN
  CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WBIGPAUX_single_sub_word]) THEN
  ASM_REWRITE_TAC[WBIGPAUX_word_add_carry] THEN CASE_REWRITE_TAC[]) THEN
  (REWRITE_TAC[WBIGPAUX_ev_Set; distinctness "store_name"; wl_word_exp_def;
              WBIGPAUX_get_var_set_var; EQ_ADD_LCANCEL; EQ_ADD_LCANCEL_0; ARITH_EQ] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[WBIGPAUX_set_var_simps; WBIGPAUX_get_var_set_var; EQ_ADD_LCANCEL;
              EQ_ADD_LCANCEL_0; ARITH_EQ] THEN
  CASE_REWRITE_TAC[] THEN
  EXPAND_TAC "u" THEN
  ASM_SIMP_TAC[WBIGPAUX_set_var_simps; WBIGPAUX_get_var_set_var;
               ARITH_RULE `0 < i ==> ~(0 = i + 1) /\ ~(0 = i + 2) /\ ~(0 = i + 3) /\
                                     ~(0 = i + 4) /\ 0 < i + 5`] THEN
  REWRITE_TAC[MATCH_MP WBIGPAUX_reg_write_comm (ASSUME `~(n1 = n2:num)`)] THEN
  MATCH_MP_TAC WBIGPAUX_state_rel_reg_write THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC WBIGPAUX_state_rel_reg_write THEN
  ASM_REWRITE_TAC[WBIGPAUX_state_rel_set_var] THEN
  EXPAND_TAC "u" THEN ASM_REWRITE_TAC[WBIGPAUX_state_rel_set_var]));;


let WBIGPAUX_Temp28 = prove
 (`~(Temp (word 28) = TempIn1) /\ ~(Temp (word 28) = TempIn2) /\
   ~(Temp (word 28) = TempOut) /\
   (!a. a < 25 ==> ~(Temp (word 28) = Temp (word a)))`,
  REWRITE_TAC[TempIn1_def; TempIn2_def; TempOut_def; injectivity "store_name";
              GSYM VAL_EQ; VAL_WORD; DIMINDEX_CONV `dimindex(:5)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT; ARITH_RULE `a < 25 ==> a < 32`] THEN
  ARITH_TAC);;

let WBIGPAUX_state_rel_div_state = prove
 (`!s (t:(A,C,FFI)wl_state) cs t0 frame f g h x.
     word_bignumProof_state_rel s t cs t0 frame ==>
     word_bignumProof_state_rel s
       (wl_set_store (Temp (word 28)) x
         (wl_state_permute_fupd f (wl_state_locals_fupd g (wl_state_stack_max_fupd h t))))
       cs t0 frame`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_bignumProof_state_rel_def; wl_set_store_def;
              wl_state_INFO.ri_accfupds; K_THM; FLOOKUP_UPDATE; WBIGPAUX_Temp28] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN RES_TAC THEN ASM_SIMP_TAC[WBIGPAUX_Temp28];
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(Temp (word 28) = n)` (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM_MESON_TAC[]]);;


let WBIGPAUX_ADD_EQ_SELF = prove
 (`!m n. (m = m + n <=> n = 0) /\ (m + n = m <=> n = 0)`,
  ARITH_TAC);;

let WBIGPAUX_compile_Mul = prove
 (el 11 WBIGPAUX_compile_cases,
  (WBIGPAUX_CPRE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_bignumProof_syntax_ok_def; syntax_ok_aux_def]) THEN
  MP_TAC(INST [`s:(A)word_bignumProof_state`,`s1:(A)word_bignumProof_state`;
               `n3:num`,`r:num`] state_rel_IN_FDOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(INST [`s:(A)word_bignumProof_state`,`s1:(A)word_bignumProof_state`;
               `n4:num`,`r:num`] state_rel_IN_FDOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[WBIGPAUX_ev_SeqTemp_Seq] THEN
  ASM_SIMP_TAC[WBIGPAUX_ev_SeqTemp_Seq; WBIGPAUX_set_var_simps] THEN
  ABBREV_TAC `u = wl_set_var (i + 2)
      (wl_Word (FAPPLY (word_bignumProof_state_regs s) n3))
      (wl_set_var (i + 3) (wl_Word (FAPPLY (word_bignumProof_state_regs s) n4))
         (t1:(A,C,FFI)wl_state))` THEN
  ABBREV_TAC `a = FAPPLY (word_bignumProof_state_regs (s:(A)word_bignumProof_state)) n3` THEN
  ABBREV_TAC `b = FAPPLY (word_bignumProof_state_regs (s:(A)word_bignumProof_state)) n4` THEN
  REWRITE_TAC[single_mul_def; WORD_ADD_0; VAL_WORD_0; ADD_CLAUSES] THEN
  EXISTS_TAC `wl_set_store (Temp (word n1)) (wl_Word (word_mul (a:A word) b))
     (wl_set_store (Temp (word n2)) (wl_Word (word ((val a * val b) DIV dimword(:A))))
       (wl_set_var (i + 1) (wl_Word (word_mul a b))
         (wl_set_var (i + 0) (wl_Word (word ((val a * val b) DIV dimword(:A))))
          (u:(A,C,FFI)wl_state))))` THEN
  REWRITE_TAC[UNWIND_THM1; GSYM evaluate_Seq_Seq] THEN
  REWRITE_TAC[WBIGPAUX_ev_Seq; WBIGPAUX_ev_Inst; wl_inst_def] THEN
  CASE_REWRITE_TAC[] THEN
  EXPAND_TAC "u" THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; wl_get_vars_def; WBIGPAUX_get_var_set_var;
              EQ_ADD_LCANCEL; EQ_ADD_LCANCEL_0; ARITH_EQ] THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_MUL; WORD_VAL] THEN
  REWRITE_TAC[WBIGPAUX_ev_Set; distinctness "store_name"; wl_word_exp_def;
              WBIGPAUX_get_var_set_var; EQ_ADD_LCANCEL; EQ_ADD_LCANCEL_0;
              WBIGPAUX_ADD_EQ_SELF; ARITH_EQ;
              ADD_CLAUSES] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[WBIGPAUX_set_var_simps; WBIGPAUX_get_var_set_var; EQ_ADD_LCANCEL;
              EQ_ADD_LCANCEL_0; WBIGPAUX_ADD_EQ_SELF; ARITH_EQ; ADD_CLAUSES] THEN
  CASE_REWRITE_TAC[] THEN
  EXPAND_TAC "u" THEN
  ASM_SIMP_TAC[WBIGPAUX_set_var_simps; WBIGPAUX_get_var_set_var;
               ARITH_RULE `0 < i ==> ~(0 = i + 1) /\ ~(0 = i + 2) /\ ~(0 = i + 3) /\
                                     ~(0 = i) /\ 0 < i + 4`] THEN
  MATCH_MP_TAC WBIGPAUX_state_rel_reg_write THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC WBIGPAUX_state_rel_reg_write THEN
  ASM_REWRITE_TAC[WBIGPAUX_state_rel_set_var] THEN
  EXPAND_TAC "u" THEN ASM_REWRITE_TAC[WBIGPAUX_state_rel_set_var]));;

let WBIGPAUX_compile_Div = prove
 (el 12 WBIGPAUX_compile_cases,
  (WBIGPAUX_CPRE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_bignumProof_syntax_ok_def; syntax_ok_aux_def]) THEN
  MP_TAC(INST [`s:(A)word_bignumProof_state`,`s1:(A)word_bignumProof_state`;
               `n3:num`,`r:num`] state_rel_IN_FDOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(INST [`s:(A)word_bignumProof_state`,`s1:(A)word_bignumProof_state`;
               `n4:num`,`r:num`] state_rel_IN_FDOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(INST [`s:(A)word_bignumProof_state`,`s1:(A)word_bignumProof_state`;
               `n5:num`,`r:num`] state_rel_IN_FDOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[WBIGPAUX_ev_SeqTemp_Seq] THEN
  ASM_SIMP_TAC[WBIGPAUX_ev_SeqTemp_Seq; WBIGPAUX_set_var_simps] THEN
  ASM_SIMP_TAC[WBIGPAUX_ev_SeqTemp_Seq; WBIGPAUX_set_var_simps] THEN
  ABBREV_TAC `a = FAPPLY (word_bignumProof_state_regs (s:(A)word_bignumProof_state)) n3` THEN
  ABBREV_TAC `b = FAPPLY (word_bignumProof_state_regs (s:(A)word_bignumProof_state)) n4` THEN
  ABBREV_TAC `c = FAPPLY (word_bignumProof_state_regs (s:(A)word_bignumProof_state)) n5`) THEN
  (SUBGOAL_THEN `div_code_assum (:FFI) (:C) (wl_state_code (t1:(A,C,FFI)wl_state)) /\
                ~(wl_state_termdep t1 = 0)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `word_bignumProof_state_rel (s:(A)word_bignumProof_state)
                   (t1:(A,C,FFI)wl_state) cs2 t0 frame` THEN
    SIMP_TAC[word_bignumProof_state_rel_def]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
    try fst(dest_const t) = "div_code_assum" with _ -> false)) (concl th))) THEN
  REWRITE_TAC[div_code_assum_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`t1:(A,C,FFI)wl_state`; `n:num`; `l:num`; `i + 0`; `i + 1`;
    `i + 2`; `i + 3`; `i + 4`; `a:A word`; `b:A word`; `c:A word`; `ret_val:(A)word_loc`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ALL_DISTINCT; MEM; EQ_ADD_LCANCEL; EQ_ADD_LCANCEL_0;
                    WBIGPAUX_ADD_EQ_SELF; ARITH_EQ] THEN
    UNDISCH_TAC `0 < i` THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mx:num option` MP_TAC) THEN
  SUBGOAL_THEN
   `wl_set_var (i + 2) (wl_Word a)
      (wl_set_var (i + 3) (wl_Word b) (wl_set_var (i + 4) (wl_Word c) (t1:(A,C,FFI)wl_state))) =
    wl_state_locals_fupd (K (insert (i + 2) (wl_Word a) (insert (i + 3) (wl_Word b)
      (insert (i + 4) (wl_Word c) (wl_state_locals t1))))) t1`
   SUBST1_TAC THENL
   [REWRITE_TAC[wl_set_var_def; wl_state_INFO.ri_fupdfupds; wl_state_INFO.ri_accfupds;
                K_o_THM; K_THM]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `single_div (a:A word) b c` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:A word`; `rm:A word`] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th; FST; SND] THEN
                       ASSUME_TAC th) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN
  ASM_REWRITE_TAC[FST; SND; o_THM] THEN
  REWRITE_TAC[GSYM evaluate_Seq_Seq] THEN
  GEN_REWRITE_TAC (BINDER_CONV o BINDER_CONV o LAND_CONV o LAND_CONV) [WBIGPAUX_ev_Seq] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) THEN
  (REWRITE_TAC[o_THM] THEN
  EXISTS_TAC `wl_set_store (Temp (word n2)) (wl_Word rm)
     (wl_set_store (Temp (word n1)) (wl_Word q)
      (wl_set_var 0 ret_val (wl_set_var (i + 1) (wl_Word rm)
       (wl_set_var (i + 0) (wl_Word q) (wl_set_store (Temp (word 28)) (wl_Word rm)
        (wl_state_permute_fupd (K (\n. wl_state_permute (t1:(A,C,FFI)wl_state) (n + 1)))
         (wl_state_locals_fupd (K LN) (wl_state_stack_max_fupd (K mx) t1))))))))` THEN
  REWRITE_TAC[UNWIND_THM1] THEN
  REWRITE_TAC[WBIGPAUX_ev_Seq; WBIGPAUX_ev_Set; distinctness "store_name"; wl_word_exp_def;
              WBIGPAUX_set_var_simps] THEN
  ASM_SIMP_TAC[WBIGPAUX_get_var_set_var; EQ_ADD_LCANCEL; EQ_ADD_LCANCEL_0;
               WBIGPAUX_ADD_EQ_SELF; ARITH_EQ; ADD_CLAUSES;
               ARITH_RULE `0 < i ==> ~(i = 0) /\ ~(i + 1 = 0)`] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[WBIGPAUX_set_var_simps; WBIGPAUX_get_var_set_var] THEN
  ASM_SIMP_TAC[WBIGPAUX_get_var_set_var; EQ_ADD_LCANCEL; EQ_ADD_LCANCEL_0;
               WBIGPAUX_ADD_EQ_SELF; ARITH_EQ; ADD_CLAUSES;
               ARITH_RULE `0 < i ==> ~(i = 0) /\ ~(i + 1 = 0)`] THEN
  CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[WBIGPAUX_set_var_simps; WBIGPAUX_get_var_set_var;
               ARITH_RULE `0 < i ==> ~(0 = i + 1) /\ ~(0 = i) /\ 0 < i + 5`] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; WBIGPAUX_set_var_simps] THEN
  REWRITE_TAC[MATCH_MP WBIGPAUX_reg_write_comm (ASSUME `~(n1 = n2:num)`)] THEN
  MATCH_MP_TAC WBIGPAUX_state_rel_reg_write THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC WBIGPAUX_state_rel_reg_write THEN
  ASM_REWRITE_TAC[WBIGPAUX_state_rel_set_var] THEN
  MATCH_MP_TAC WBIGPAUX_state_rel_div_state THEN ASM_REWRITE_TAC[]));;



let WBIGPAUX_lookup_fromList2_1 = prove
 (`!x:A. lookup 0 (fromList2 [x]) = SOME x`,
  REWRITE_TAC[fromList2_def; FOLDL] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[SND; lookup_insert]);;

let WBIGPAUX_ev_tail_call = prove
 (`!n (t:(A,C,FFI)wl_state) ret_val p.
     wl_get_var 0 t = SOME ret_val /\ lookup n (wl_state_code t) = SOME (1,p) /\
     ~(wl_state_clock t = 0) ==>
     wl_evaluate (wl_Call NONE (SOME n) [0] NONE,t) =
     pair_CASE (wl_evaluate (p,wl_call_env [ret_val] (lookup n (wl_state_stack_size t))
                                (wl_dec_clock t)))
       (\res s. if wl_bad_fun_return res then (SOME wl_Error,s) else (res,s))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WBIGPAUX_ev_Call; wl_get_vars_def] THEN ASM_REWRITE_TAC[] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bad_dest_args_def; option_DISTINCT; add_ret_loc_def; wl_find_code_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `SUC 0 = 1`] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[]);;

let WBIGPAUX_state_rel_call_env = prove
 (`!s (t:(A,C,FFI)wl_state) cs t0 frame args ss.
     word_bignumProof_state_rel s t cs t0 frame ==>
     word_bignumProof_state_rel (word_bignumProof_dec_clock s)
       (wl_call_env args ss (wl_dec_clock t)) cs t0 frame`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[word_bignumProof_state_rel_def; wl_call_env_def; wl_dec_clock_def;
              wl_state_INFO.ri_accfupds; K_THM; WBIGPAUX_dec_clock_write_simp] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let WBIGPAUX_ev_Return_ok = prove
 (`!(t:(A,C,FFI)wl_state).
     pair_CASE (wl_evaluate (wl_Return 0 [0],t))
       (\res s. if wl_bad_fun_return res then (SOME wl_Error,s) else (res,s)) =
     wl_evaluate (wl_Return 0 [0],t)`,
  GEN_TAC THEN REWRITE_TAC[WBIGPAUX_ev_Return; wl_get_vars_def] THEN
  EVERY_CASE_TAC THEN CASE_REWRITE_TAC[] THEN REWRITE_TAC[wl_bad_fun_return_def] THEN
  CASE_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[wl_bad_fun_return_def]);;

let WBIGPAUX_call_env_simps = prove
 (`!args ss (t:(A,C,FFI)wl_state).
     wl_state_stack (wl_call_env args ss (wl_dec_clock t)) = wl_state_stack t /\
     wl_state_code (wl_call_env args ss (wl_dec_clock t)) = wl_state_code t /\
     wl_state_clock (wl_call_env args ss (wl_dec_clock t)) = wl_state_clock t - 1 /\
     wl_get_var 0 (wl_call_env [x] ss (wl_dec_clock t)) = SOME x`,
  REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM;
              wl_get_var_def; WBIGPAUX_lookup_fromList2_1]);;

let WBIGPAUX_compile_LoopBody1 = prove
 (el 15 WBIGPAUX_compile_cases,
  (REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[word_bignum_compile_def; word_bignumProof_syntax_ok_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WBIGPAUX_syntax_ok_aux_IMP) THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`n:num`; `l:num`; `i:num`;
     `cs:num#((A)mini#num#(A)wl_prog)list`;
     `p1:(A)wl_prog`; `l1:num`; `i1:num`; `cs1:num#((A)mini#num#(A)wl_prog)list`;
     `cs2:num#((A)mini#num#(A)wl_prog)list`; `t1:(A,C,FFI)wl_state`; `ret_val:(A)word_loc`;
     `p9:(A)wl_prog`]) THEN
  ASM_REWRITE_TAC[]));;

let WBIGPAUX_compile_LoopBody2 = prove
 (el 16 WBIGPAUX_compile_cases,
  (REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ih2"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o check WBIGPAUX_is_compile_eq) THEN
  REWRITE_TAC[word_bignum_compile_def] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_bignumProof_syntax_ok_def; injectivity "mini"]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WBIGPAUX_syntax_ok_aux_IMP o
    check (fun th -> try fst(dest_const(rator(concl th))) = "syntax_ok_aux" with _ -> false)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:(A)mini` o check (fun th -> is_forall (concl th) &&
    can (find_term (fun t -> t = `wl_Return 0 [0]:(A)wl_prog`)) (concl th) &&
    not (can (find_term (fun t -> try fst(dest_const t) = "word_bignum_compile"
                                  with _ -> false)) (concl th)))) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> try lhs (concl th) = `p9:(A)wl_prog`
                                                 with Failure _ -> false)) THEN
  CASE_REWRITE_TAC[]) THEN
  (REMOVE_THEN "ih1" (MP_TAC o SPECL [`n:num`; `l:num`; `i:num`;
     `cs:num#((A)mini#num#(A)wl_prog)list`;
     `p1:(A)wl_prog`; `l1:num`; `i1:num`; `cs1:num#((A)mini#num#(A)wl_prog)list`;
     `cs2:num#((A)mini#num#(A)wl_prog)list`; `t1:(A,C,FFI)wl_state`; `ret_val:(A)word_loc`;
     `wl_Return 0 [0]:(A)wl_prog`]) THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u2:(A,C,FFI)wl_state` (X_CHOOSE_THEN
    `res1:((A)wl_result)option#(A,C,FFI)wl_state` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(wl_state_clock (u2:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `word_bignumProof_state_rel (s2:(A)word_bignumProof_state)
                   (u2:(A,C,FFI)wl_state) cs2 t0 frame` THEN
    REWRITE_TAC[word_bignumProof_state_rel_def] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `u2:(A,C,FFI)wl_state`; `ret_val:(A)word_loc`;
                 `wl_Seq p1 (wl_Return 0 [0]):(A)wl_prog`] WBIGPAUX_ev_tail_call) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REMOVE_THEN "ih2" (MP_TAC o SPECL [`n:num`; `l:num`; `i:num`;
     `cs:num#((A)mini#num#(A)wl_prog)list`;
     `p1:(A)wl_prog`; `l1:num`; `i1:num`; `cs1:num#((A)mini#num#(A)wl_prog)list`;
     `cs2:num#((A)mini#num#(A)wl_prog)list`;
     `wl_call_env [ret_val] (lookup n (wl_state_stack_size u2))
        (wl_dec_clock (u2:(A,C,FFI)wl_state))`; `ret_val:(A)word_loc`;
     `wl_Return 0 [0]:(A)wl_prog`]) THEN
  REWRITE_TAC[WBIGPAUX_call_env_simps] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[check (fun th -> concl th =
    `wl_state_code (u2:(A,C,FFI)wl_state) = wl_state_code (t1:(A,C,FFI)wl_state)`) th]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           MATCH_MP_TAC WBIGPAUX_state_rel_call_env THEN ASM_REWRITE_TAC[];
           ASM_REWRITE_TAC[word_bignumProof_syntax_ok_def; injectivity "mini"] THEN
           NO_TAC;
           ASM_MESON_TAC[injectivity "mini"]];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u3:(A,C,FFI)wl_state` (X_CHOOSE_THEN
    `res2:((A)wl_result)option#(A,C,FFI)wl_state` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `u3:(A,C,FFI)wl_state` THEN
  ASM_REWRITE_TAC[WBIGPAUX_ev_Return_ok; WBIGPAUX_call_env_simps] THEN MESON_TAC[]));;


let WBIGPAUX_cut_envs_ret = prove
 (`!env (v:A). lookup 0 env = SOME v ==>
     cut_envs (LS one,LN) env = SOME (insert 0 v LN,LN)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cut_envs_def; cut_names_def; domain_def] THEN
  REWRITE_TAC[EMPTY_SUBSET; SING_SUBSET; domain_lookup; inter_LN] THEN
  SUBGOAL_THEN `?v':A. lookup 0 env = SOME v'` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[option_INJ; PAIR_EQ] THEN
  SIMP_TAC[spt_eq_thm; wf_inter; wf_insert; wf_def] THEN
  REWRITE_TAC[lookup_inter_alt; lookup_insert; domain_def; IN_SING] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[lookup_def]);;

let WBIGPAUX_env_to_list_LN = prove
 (`!p. env_to_list (LN:((A)word_loc)spt) p = ([],(\n. p (n + 1)))`,
  REWRITE_TAC[env_to_list_def; LET_DEF; LET_END_DEF; toAList_def; foldi_def;
              sort_thm; mergesort_tail_def; LENGTH; CONJUNCT1 mergesortN_tail_def;
              list_rearrange_def] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[list_of_seq]);;

let WBIGPAUX_toAList_insert_0_LN = prove
 (`!v:A. toAList (insert 0 v LN) = [0,v]`,
  ONCE_REWRITE_TAC[insert_def] THEN REWRITE_TAC[toAList_def; foldi_def]);;

let WBIGPAUX_state_rel_fupds = prove
 (`(!f s (t:(A,C,FFI)wl_state) cs t0 frame.
     word_bignumProof_state_rel s (wl_state_stack_fupd f t) cs t0 frame <=>
     word_bignumProof_state_rel s t cs t0 frame) /\
   (!f s (t:(A,C,FFI)wl_state) cs t0 frame.
     word_bignumProof_state_rel s (wl_state_locals_size_fupd f t) cs t0 frame <=>
     word_bignumProof_state_rel s t cs t0 frame) /\
   (!f s (t:(A,C,FFI)wl_state) cs t0 frame.
     word_bignumProof_state_rel s (wl_state_permute_fupd f t) cs t0 frame <=>
     word_bignumProof_state_rel s t cs t0 frame) /\
   (!f s (t:(A,C,FFI)wl_state) cs t0 frame.
     word_bignumProof_state_rel s (wl_state_stack_max_fupd f t) cs t0 frame <=>
     word_bignumProof_state_rel s t cs t0 frame)`,
  REWRITE_TAC[word_bignumProof_state_rel_def; wl_state_INFO.ri_accfupds]);;

let WBIGPAUX_ev_call_ret = prove
 (`!(t:(A,C,FFI)wl_state) x n l i ret_val q u.
     lookup x (wl_state_code t) = SOME (1,wl_Seq q (wl_Return 0 [0])) /\
     wl_get_var 0 t = SOME ret_val /\ ~(wl_state_clock t = 0) /\ 0 < i /\
     wl_evaluate (wl_Seq q (wl_Return 0 [0]),
       wl_call_env [wl_Loc n l] (lookup x (wl_state_stack_size t))
         (wl_push_env (insert 0 ret_val LN,LN) NONE (wl_dec_clock t))) =
     wl_evaluate (wl_Return 0 [0],u) /\
     wl_state_stack u =
       CONS (StackFrame (wl_state_locals_size t) [0,ret_val] [] NONE) (wl_state_stack t) /\
     wl_get_var 0 u = SOME (wl_Loc n l) ==>
     ?t2. wl_evaluate (wl_Call (SOME ([i],(LS one,LN),wl_Skip,n,l)) (SOME x) [] NONE,t) =
          (NONE,t2) /\
          wl_state_stack t2 = wl_state_stack t /\ wl_get_var 0 t2 = SOME ret_val /\
          wl_state_code t2 = wl_state_code u /\
          (!s cs t0 frame. word_bignumProof_state_rel s u cs t0 frame ==>
                           word_bignumProof_state_rel s t2 cs t0 frame)`,
  (REPEAT STRIP_TAC THEN
  REWRITE_TAC[WBIGPAUX_ev_Call; wl_get_vars_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bad_dest_args_def; option_DISTINCT; add_ret_loc_def; wl_find_code_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `SUC 0 = 1`; domain_def; NOT_INSERT_EMPTY;
              ALL_DISTINCT; MEM] THEN
  CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP WBIGPAUX_cut_envs_ret
    (check (fun th -> concl th = `lookup 0 (wl_state_locals (t:(A,C,FFI)wl_state)) =
                                  SOME (ret_val:(A)word_loc)`) th)]) THEN
  CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[]) THEN
  (REWRITE_TAC[WBIGPAUX_ev_Return; wl_get_vars_def; wl_get_var_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `SUC 0 = 1`] THEN
  REWRITE_TAC[wl_pop_env_def; wl_flush_state_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; fromAList_def; union_LN;
              domain_insert; domain_def; UNION_EMPTY] THEN
  REWRITE_TAC[WBIGPAUX_ev_Skip; PAIR_EQ; LEFT_EXISTS_AND_THM; EXISTS_REFL; UNWIND_THM1]) THEN
  (REWRITE_TAC[wl_set_vars_def; wl_state_INFO.ri_accfupds; K_THM; alist_insert_def;
              lookup_insert; WBIGPAUX_state_rel_locals; WBIGPAUX_state_rel_fupds] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < i ==> ~(0 = i)`] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds]));;



let WBIGPAUX_call_push = prove
 (`!(t:(A,C,FFI)wl_state) v x ss.
     wl_get_var 0 (wl_call_env [x] ss
       (wl_push_env (insert 0 v LN,LN) NONE (wl_dec_clock t))) = SOME x /\
     wl_state_stack (wl_call_env [x] ss
       (wl_push_env (insert 0 v LN,LN) NONE (wl_dec_clock t))) =
       CONS (StackFrame (wl_state_locals_size t) [0,v] [] NONE) (wl_state_stack t) /\
     wl_state_code (wl_call_env [x] ss
       (wl_push_env (insert 0 v LN,LN) NONE (wl_dec_clock t))) = wl_state_code t /\
     (!s cs t0 frame.
        word_bignumProof_state_rel s t cs t0 frame ==>
        word_bignumProof_state_rel (word_bignumProof_dec_clock s)
          (wl_call_env [x] ss (wl_push_env (insert 0 v LN,LN) NONE (wl_dec_clock t)))
          cs t0 frame)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wl_call_env_def; wl_push_env_def; LET_DEF; LET_END_DEF;
              WBIGPAUX_env_to_list_LN; WBIGPAUX_toAList_insert_0_LN] THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; wl_get_var_def;
              WBIGPAUX_lookup_fromList2_1; WBIGPAUX_state_rel_locals;
              WBIGPAUX_state_rel_fupds] THEN
  REWRITE_TAC[wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(A)word_bignumProof_state`; `t:(A,C,FFI)wl_state`;
    `cs:num#((A)mini#num#(A)wl_prog)list`; `t0:(A,C,FFI)wl_state`;
    `frame:((A word#(A)word_loc)->bool)->bool`; `[x:(A)word_loc]`; `ss:num option`]
    WBIGPAUX_state_rel_call_env) THEN
  ASM_REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; WBIGPAUX_state_rel_locals;
                  WBIGPAUX_state_rel_fupds]);;

let WBIGPAUX_compile_Loop_eq = prove
 (`!n l i cs rc vs (p:(A)mini) q l1 i1 cs1.
     word_bignum_compile n l i cs (word_bignum_Loop rc vs p) = (q,l1,i1,cs1) ==>
     ?x. q = wl_Call (SOME ([i],(LS one,LN),wl_Skip,n,l)) (SOME x) [] NONE /\
         l1 = l + 1 /\ i1 = i + 1 /\ has_compiled p cs1 = INL x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_bignum_compile_def] THEN
  MP_TAC(ISPEC `has_compiled (p:(A)mini) (cs:num#((A)mini#num#(A)wl_prog)list)`
    (cases "sum")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [STRIP_TAC THEN EXISTS_TAC `a:num` THEN ASM_MESON_TAC[];
    REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    EXISTS_TAC `a:num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> try
      fst(dest_const(fst(strip_comb(lhs(concl th))))) = "install" with _ -> false)) THEN
    MAP_EVERY (fun t -> SPEC_TAC(t,t))
      [`cs':num#((A)mini#num#(A)wl_prog)list`] THEN
    REWRITE_TAC[FORALL_PAIR_THM; install_def; has_compiled_def; ALOOKUP_THM] THEN
    CASE_REWRITE_TAC[]]);;

let WBIGPAUX_compile_Loop = prove
 (el 13 WBIGPAUX_compile_cases,
  (REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP WBIGPAUX_compile_Loop_eq o check WBIGPAUX_is_compile_eq) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_bignumProof_syntax_ok_def; syntax_ok_aux_def]) THEN
  MP_TAC(ISPECL [`s1:(A)word_bignumProof_state`; `t1:(A,C,FFI)wl_state`;
    `cs2:num#((A)mini#num#(A)wl_prog)list`; `t0:(A,C,FFI)wl_state`;
    `frame:((A word#(A)word_loc)->bool)->bool`; `p:(A)mini`;
    `cs1:num#((A)mini#num#(A)wl_prog)list`; `x:num`]
    (GENL [`s1:(A)word_bignumProof_state`; `t1:(A,C,FFI)wl_state`;
      `cs2:num#((A)mini#num#(A)wl_prog)list`; `t0:(A,C,FFI)wl_state`;
      `frame:((A word#(A)word_loc)->bool)->bool`; `p:(A)mini`;
      `cs:num#((A)mini#num#(A)wl_prog)list`; `x:num`] has_compiled_lemma)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(A)wl_prog` (X_CHOOSE_THEN `lq:num` (X_CHOOSE_THEN `iq:num`
    (X_CHOOSE_THEN `csq:num#((A)mini#num#(A)wl_prog)list`
    (X_CHOOSE_THEN `csq1:num#((A)mini#num#(A)wl_prog)list` STRIP_ASSUME_TAC)))))) THEN
  (MP_TAC(ISPECL [`t1:(A,C,FFI)wl_state`; `ret_val:(A)word_loc`; `wl_Loc n l:(A)word_loc`;
    `lookup x (wl_state_stack_size (t1:(A,C,FFI)wl_state))`] WBIGPAUX_call_push) THEN
  ABBREV_TAC `cst = wl_call_env [wl_Loc n l] (lookup x (wl_state_stack_size t1))
     (wl_push_env (insert 0 ret_val LN,LN) NONE (wl_dec_clock (t1:(A,C,FFI)wl_state)))` THEN
  STRIP_TAC THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`x:num`; `2`; `1`;
     `csq:num#((A)mini#num#(A)wl_prog)list`;
     `q:(A)wl_prog`; `lq:num`; `iq:num`; `csq1:num#((A)mini#num#(A)wl_prog)list`;
     `cs2:num#((A)mini#num#(A)wl_prog)list`; `cst:(A,C,FFI)wl_state`;
     `wl_Loc n l:(A)word_loc`; `wl_Return 0 [0]:(A)wl_prog`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[word_bignum_compile_def; word_bignumProof_syntax_ok_def;
                    injectivity "mini"; ARITH_RULE `0 < 1`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC state_rel_delete_vars THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    BOOL_CASES_TAC `rec:bool` THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
    GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`2`; `1`; `csq:num#((A)mini#num#(A)wl_prog)list`;
      `q:(A)wl_prog`; `lq:num`; `iq:num`; `csq1:num#((A)mini#num#(A)wl_prog)list`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `0 < 1`];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:(A,C,FFI)wl_state` (X_CHOOSE_THEN
    `res1:((A)wl_result)option#(A,C,FFI)wl_state` STRIP_ASSUME_TAC))) THEN
  (SUBGOAL_THEN `~(wl_state_clock (t1:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `word_bignumProof_state_rel (s1:(A)word_bignumProof_state)
                   (t1:(A,C,FFI)wl_state) cs2 t0 frame` THEN
    REWRITE_TAC[word_bignumProof_state_rel_def] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t1:(A,C,FFI)wl_state`; `x:num`; `n:num`; `l:num`; `i:num`;
    `ret_val:(A)word_loc`; `q:(A)wl_prog`; `u:(A,C,FFI)wl_state`] WBIGPAUX_ev_call_ret) THEN
  ASM_REWRITE_TAC[] THEN
  TRY(ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `tt:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `tt:(A,C,FFI)wl_state` THEN
  ASM_REWRITE_TAC[WBIGPAUX_ev_Seq; ARITH_RULE `0 < i + 1`] THEN CASE_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[] THEN MESON_TAC[]));;

(* the Rec case: environments of the call *)

(* MEM over list_rearrange (wordProps: mem_list_rearrange) *)
let WBIGPAUX_mem_list_rearrange = prove
 (`!ls (x:A) f. MEM x (list_rearrange f ls) <=> MEM x ls`,
  REPEAT GEN_TAC THEN REWRITE_TAC[list_rearrange_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[MEM_GENLIST] THEN
  REWRITE_TAC[MEM_EXISTS_EL] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[BIJ_IFF_INV; count_DEF; IN_ELIM_THM]) THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `(f:num->num) m` THEN ASM_SIMP_TAC[];
    EXISTS_TAC `(g:num->num) m` THEN ASM_SIMP_TAC[]]);;

(* first half of wordProps' env_to_list_lookup_equiv *)
let WBIGPAUX_ALOOKUP_env_to_list = prove
 (`!(y:((A)word_loc)spt) f n. ALOOKUP (FST (env_to_list y f)) n = lookup n y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[env_to_list_def] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[FST] THEN
  ABBREV_TAC `L = list_rearrange (f 0)
                    (sort key_val_compare (toAList (y:((A)word_loc)spt)))` THEN
  SUBGOAL_THEN `!k v. MEM (k,v) L <=> lookup k (y:((A)word_loc)spt) = SOME v`
  ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[WBIGPAUX_mem_list_rearrange; sort_MEM; MEM_toAList];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(num#(A)word_loc)list`; `n:num`] ALOOKUP_NONE) THEN
  MP_TAC(ISPECL [`L:(num#(A)word_loc)list`; `n:num`] ALOOKUP_MEM) THEN
  ASM_REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; FST] THEN
  MP_TAC(ISPEC `ALOOKUP (L:(num#(A)word_loc)list) n` (cases "option")) THEN
  MP_TAC(ISPEC `lookup n (y:((A)word_loc)spt)` (cases "option")) THEN
  MESON_TAC[option_DISTINCT; option_INJ]);;

let WBIGPAUX_domain_pop = prove
 (`!(e1:((A)word_loc)spt) e2 p.
     domain (union (fromAList (FST (env_to_list e2 p))) (fromAList (toAList e1))) =
     domain e1 UNION domain e2`,
  REWRITE_TAC[EXTENSION; IN_UNION; domain_union] THEN
  REWRITE_TAC[domain_lookup; lookup_fromAList; WBIGPAUX_ALOOKUP_env_to_list;
              ALOOKUP_toAList] THEN
  MESON_TAC[]);;

let WBIGPAUX_cut_envs_rec = prove
 (`!(env:((A)word_loc)spt) v save_regs (vals:(A word)list).
     lookup 0 env = SOME v /\
     ALL2 (\n w. lookup (n + 2) env = SOME (wl_Word w)) save_regs vals ==>
     cut_envs (LS one,list_insert (MAP (\k. k + 2) save_regs) LN) env =
     SOME (inter env (LS one),inter env (list_insert (MAP (\k. k + 2) save_regs) LN))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cut_envs_def; cut_names_def] THEN
  SUBGOAL_THEN `domain (LS one) SUBSET domain (env:((A)word_loc)spt)`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[domain_def; SING_SUBSET; domain_lookup] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  CASE_REWRITE_TAC[] THEN
  SUBGOAL_THEN `domain (list_insert (MAP (\k. k + 2) save_regs) LN) SUBSET
                domain (env:((A)word_loc)spt)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[SUBSET; domain_list_insert; domain_def; NOT_IN_EMPTY; MEM_MAP] THEN
    X_GEN_TAC `m:num` THEN DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[domain_lookup] THEN
    MP_TAC(ISPECL [`save_regs:num list`; `vals:(A word)list`;
      `\n w. lookup (n + 2) (env:((A)word_loc)spt) = SOME (wl_Word (w:A word))`; `k:num`]
      LIST_REL_MEM_IMP) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  CASE_REWRITE_TAC[]);;

let WBIGPAUX_lookup_list_update = prove
 (`!save_regs (vals:(A word)list) tr.
     ALL_DISTINCT save_regs /\ LENGTH save_regs = LENGTH vals ==>
     ALL2 (\n v. lookup (n + 2)
                   (list_update (MAP (\k. k + 2) save_regs) (MAP wl_Word vals) tr) =
                 SOME (wl_Word v)) save_regs vals`,
  LIST_INDUCT_TAC THENL
   [GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `vals:(A word)list` list_CASES) THEN
    REWRITE_TAC[ALL2; LENGTH; GSYM NOT_SUC];
    ALL_TAC] THEN
  X_GEN_TAC `vals:(A word)list` THEN
  MP_TAC(ISPEC `vals:(A word)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `v0:A word` (X_CHOOSE_THEN `vs:(A word)list` SUBST1_TAC))) THEN
  REWRITE_TAC[ALL2; LENGTH; NOT_SUC; MAP; list_update_def; ALL_DISTINCT; SUC_INJ] THEN
  X_GEN_TAC `tr:((A)word_loc)spt` THEN STRIP_TAC THEN
  REWRITE_TAC[lookup_insert] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`vs:(A word)list`; `tr:((A)word_loc)spt`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LIST_REL_lemma THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `w:A word`] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(m + 2 = h + 2)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[EQ_ADD_RCANCEL]; ASM_REWRITE_TAC[]]);;

let WBIGPAUX_rec_lookups = prove
 (`!(L0:((A)word_loc)spt) save_regs (vals:(A word)list) p xv.
     ALL2 (\n v. lookup (n + 2) L0 = SOME (wl_Word v)) save_regs vals ==>
     ALL2 (\n v. lookup (n + 2)
        (insert 1 xv (union (fromAList (FST (env_to_list
            (inter L0 (list_insert (MAP (\k. k + 2) save_regs) LN)) p)))
          (fromAList (toAList (inter L0 (LS one)))))) = SOME (wl_Word v)) save_regs vals`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC LIST_REL_lemma THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `w:A word`] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[lookup_insert; ARITH_RULE `~(m + 2 = 1)`; lookup_union; lookup_fromAList;
              WBIGPAUX_ALOOKUP_env_to_list; lookup_inter_alt; domain_list_insert;
              domain_def; NOT_IN_EMPTY] THEN
  SUBGOAL_THEN `MEM (m + 2) (MAP (\k. k + 2) save_regs)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* the Rec case: copying the saved registers back *)

let WBIGPAUX_copy_vars_regs = prove
 (`!save_regs (vals:(A word)list) (s2:(A)word_bignumProof_state) s3 st.
     word_bignumProof_copy_vars save_regs (word_bignumProof_state_regs s1) s2 = SOME s3 /\
     ALL2 (\n v. FLOOKUP (word_bignumProof_state_regs s1) n = SOME v) save_regs vals /\
     ALL_DISTINCT save_regs /\ ALL (\n. n < 25) save_regs /\
     (!a v. FLOOKUP (word_bignumProof_state_regs s2) a = SOME v ==>
            a < 25 /\ FLOOKUP st (Temp (word a)) = SOME (wl_Word v)) ==>
     (!a v. FLOOKUP (word_bignumProof_state_regs s3) a = SOME v ==>
            a < 25 /\
            FLOOKUP (list_store save_regs (MAP wl_Word vals) st) (Temp (word a)) =
            SOME (wl_Word v))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[word_bignumProof_copy_vars_def; option_INJ; list_store_def] THEN
    MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `vals:(A word)list` THEN
  MP_TAC(ISPEC `vals:(A word)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `v0:A word` (X_CHOOSE_THEN `vs:(A word)list` SUBST1_TAC))) THEN
  REWRITE_TAC[ALL2] THEN
  MAP_EVERY X_GEN_TAC [`s2:(A)word_bignumProof_state`; `s3:(A)word_bignumProof_state`;
                       `st:(store_name,(A)word_loc)fmap`] THEN
  REWRITE_TAC[ALL_DISTINCT; ALL] THEN STRIP_TAC THEN
  UNDISCH_TAC `word_bignumProof_copy_vars (CONS h t)
     (word_bignumProof_state_regs (s1:(A)word_bignumProof_state)) s2 = SOME s3` THEN
  ASM_REWRITE_TAC[word_bignumProof_copy_vars_def] THEN CASE_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[MAP; list_store_def; TL; HD] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`vs:(A word)list`;
     `reg_write h (SOME v0) (s2:(A)word_bignumProof_state)`; `s3:(A)word_bignumProof_state`;
     `st |+ (Temp (word h),wl_Word (v0:A word))`]) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[WBIGPAUX_reg_write_simp; FLOOKUP_UPDATE] THEN
    MAP_EVERY X_GEN_TAC [`a:num`; `w:A word`] THEN
    ASM_CASES_TAC `h:num = a` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `h:num = a`)) THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a:num`; `w:A word`] o check (fun th ->
        try fst(dest_var(fst(dest_forall(concl th)))) = "a" with _ -> false)) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[WBIGPAUX_Temp_11]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[list_store_FUPDATE] THEN MESON_TAC[]);;

let WBIGPAUX_state_rel_copy_vars = prove
 (`!save_regs (vals:(A word)list) (s2:(A)word_bignumProof_state) s3
    (u:(A,C,FFI)wl_state) cs t0 frame.
     word_bignumProof_copy_vars save_regs (word_bignumProof_state_regs s1) s2 = SOME s3 /\
     ALL2 (\n v. FLOOKUP (word_bignumProof_state_regs s1) n = SOME v) save_regs vals /\
     ALL_DISTINCT save_regs /\ ALL (\n. n < 25) save_regs /\
     word_bignumProof_state_rel s2 u cs t0 frame ==>
     word_bignumProof_state_rel s3
       (wl_state_store_fupd (K (list_store save_regs (MAP wl_Word vals) (wl_state_store u))) u)
       cs t0 frame`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP copy_vars_const) THEN
  MP_TAC(ISPECL [`save_regs:num list`; `MAP wl_Word (vals:(A word)list)`;
                 `wl_state_store (u:(A,C,FFI)wl_state)`] FLOOKUP_list_store_ignore) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`save_regs:num list`; `vals:(A word)list`; `s2:(A)word_bignumProof_state`;
                 `s3:(A)word_bignumProof_state`; `wl_state_store (u:(A,C,FFI)wl_state)`]
    WBIGPAUX_copy_vars_regs) THEN
  UNDISCH_TAC `word_bignumProof_state_rel (s2:(A)word_bignumProof_state)
                 (u:(A,C,FFI)wl_state) cs t0 frame` THEN
  REWRITE_TAC[word_bignumProof_state_rel_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[]);;

let WBIGPAUX_call_push_gen = prove
 (`!(t:(A,C,FFI)wl_state) e1 e2 x ss.
     wl_get_var 0 (wl_call_env [x] ss (wl_push_env (e1,e2) NONE (wl_dec_clock t))) =
       SOME x /\
     wl_state_stack (wl_call_env [x] ss (wl_push_env (e1,e2) NONE (wl_dec_clock t))) =
       CONS (StackFrame (wl_state_locals_size t) (toAList e1)
               (FST (env_to_list e2 (wl_state_permute t))) NONE) (wl_state_stack t) /\
     wl_state_code (wl_call_env [x] ss (wl_push_env (e1,e2) NONE (wl_dec_clock t))) =
       wl_state_code t /\
     (!s cs t0 frame.
        word_bignumProof_state_rel s t cs t0 frame ==>
        word_bignumProof_state_rel (word_bignumProof_dec_clock s)
          (wl_call_env [x] ss (wl_push_env (e1,e2) NONE (wl_dec_clock t))) cs t0 frame)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wl_call_env_def; wl_push_env_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPEC `env_to_list (e2:((A)word_loc)spt) (wl_state_permute (wl_dec_clock
    (t:(A,C,FFI)wl_state)))` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:(num#(A)word_loc)list` (X_CHOOSE_THEN `pm:num->num->num`
    (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th))) THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; wl_get_var_def;
              WBIGPAUX_lookup_fromList2_1; WBIGPAUX_state_rel_locals;
              WBIGPAUX_state_rel_fupds] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[wl_dec_clock_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(A)word_bignumProof_state`; `t:(A,C,FFI)wl_state`;
    `cs:num#((A)mini#num#(A)wl_prog)list`; `t0:(A,C,FFI)wl_state`;
    `frame:((A word#(A)word_loc)->bool)->bool`; `[x:(A)word_loc]`; `ss:num option`]
    WBIGPAUX_state_rel_call_env) THEN
  ASM_REWRITE_TAC[wl_call_env_def; wl_dec_clock_def; WBIGPAUX_state_rel_locals;
                  WBIGPAUX_state_rel_fupds]);;

let WBIGPAUX_state_rel_cong = prove
 (`!s (t:(A,C,FFI)wl_state) t' cs t0 frame.
     wl_state_clock t' = wl_state_clock t /\ wl_state_store t' = wl_state_store t /\
     wl_state_memory t' = wl_state_memory t /\ wl_state_mdomain t' = wl_state_mdomain t /\
     wl_state_code t' = wl_state_code t /\ wl_state_termdep t' = wl_state_termdep t /\
     wl_state_gc_fun t' = wl_state_gc_fun t /\ wl_state_handler t' = wl_state_handler t /\
     wl_state_be t' = wl_state_be t /\ wl_state_ffi t' = wl_state_ffi t /\
     wl_state_compile t' = wl_state_compile t /\
     wl_state_compile_oracle t' = wl_state_compile_oracle t /\
     wl_state_code_buffer t' = wl_state_code_buffer t /\
     wl_state_data_buffer t' = wl_state_data_buffer t /\
     wl_state_stack_limit t' = wl_state_stack_limit t /\
     wl_state_stack_size t' = wl_state_stack_size t ==>
     (word_bignumProof_state_rel s t' cs t0 frame <=>
      word_bignumProof_state_rel s t cs t0 frame)`,
  REWRITE_TAC[word_bignumProof_state_rel_def] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let WBIGPAUX_rec_lookup0 = prove
 (`!(L0:((A)word_loc)spt) save_regs p xv.
     lookup 0 (insert 1 xv (union (fromAList (FST (env_to_list
        (inter L0 (list_insert (MAP (\k. k + 2) save_regs) LN)) p)))
        (fromAList (toAList (inter L0 (LS one)))))) = lookup 0 L0`,
  REWRITE_TAC[lookup_insert; ARITH_RULE `~(0 = 1)`; lookup_union; lookup_fromAList;
              WBIGPAUX_ALOOKUP_env_to_list; ALOOKUP_toAList; lookup_inter_alt;
              domain_list_insert; domain_def; NOT_IN_EMPTY; IN_SING; MEM_MAP;
              ARITH_RULE `!k. ~(0 = k + 2)`] THEN
  CASE_REWRITE_TAC[]);;

let WBIGPAUX_ev_call_rec = prove
 (`!(t:(A,C,FFI)wl_state) n l save_regs (vals:(A word)list) ret_val q u.
     lookup n (wl_state_code t) = SOME (1,wl_Seq q (wl_Return 0 [0])) /\
     lookup 0 (wl_state_locals t) = SOME ret_val /\ ~(wl_state_clock t = 0) /\
     ALL2 (\r v. lookup (r + 2) (wl_state_locals t) = SOME (wl_Word v)) save_regs vals /\
     ALL_DISTINCT save_regs /\ ALL (\r. r < 25) save_regs /\
     wl_evaluate (wl_Seq q (wl_Return 0 [0]),
       wl_call_env [wl_Loc n l] (lookup n (wl_state_stack_size t))
         (wl_push_env (inter (wl_state_locals t) (LS one),
            inter (wl_state_locals t) (list_insert (MAP (\k. k + 2) save_regs) LN))
            NONE (wl_dec_clock t))) =
     wl_evaluate (wl_Return 0 [0],u) /\
     wl_state_stack u =
       CONS (StackFrame (wl_state_locals_size t)
               (toAList (inter (wl_state_locals t) (LS one)))
               (FST (env_to_list (inter (wl_state_locals t)
                  (list_insert (MAP (\k. k + 2) save_regs) LN)) (wl_state_permute t))) NONE)
            (wl_state_stack t) /\
     wl_get_var 0 u = SOME (wl_Loc n l) ==>
     ?t2. wl_evaluate (wl_Call (SOME ([1],(LS one,list_insert (MAP (\k. k + 2) save_regs) LN),
                                      SaveRegs save_regs,n,l)) (SOME n) [] NONE,t) =
          (NONE,t2) /\
          wl_state_stack t2 = wl_state_stack t /\ wl_get_var 0 t2 = SOME ret_val /\
          wl_state_code t2 = wl_state_code u /\
          (!s cs t0 frame.
             word_bignumProof_state_rel s
               (wl_state_store_fupd
                  (K (list_store save_regs (MAP wl_Word vals) (wl_state_store u))) u)
               cs t0 frame ==>
             word_bignumProof_state_rel s t2 cs t0 frame)`,
  (REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN
  REWRITE_TAC[WBIGPAUX_ev_Call; wl_get_vars_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[bad_dest_args_def; option_DISTINCT; add_ret_loc_def; wl_find_code_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `SUC 0 = 1`; domain_def; NOT_INSERT_EMPTY; ALL_DISTINCT;
              MEM] THEN
  CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`wl_state_locals (t:(A,C,FFI)wl_state)`; `ret_val:(A)word_loc`;
                 `save_regs:num list`; `vals:(A word)list`] WBIGPAUX_cut_envs_rec) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[]) THEN
  (REWRITE_TAC[WBIGPAUX_ev_Return; wl_get_vars_def; wl_get_var_def] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `SUC 0 = 1`] THEN
  REWRITE_TAC[wl_pop_env_def; wl_flush_state_def; wl_state_INFO.ri_accfupds; K_THM] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; WBIGPAUX_domain_pop]) THEN
  (W(fun (asl,w) ->
     let ev = lhand(lhand(snd(dest_exists w))) in
     let t7 = rand(rand ev) in
     MP_TAC(ISPECL [`save_regs:num list`; t7; `vals:(A word)list`] evaluate_SaveRegs)) THEN
  MP_TAC(ISPECL [`wl_state_locals (t:(A,C,FFI)wl_state)`; `save_regs:num list`;
    `vals:(A word)list`; `wl_state_permute (t:(A,C,FFI)wl_state)`; `wl_Loc n l:(A)word_loc`]
    WBIGPAUX_rec_lookups) THEN
  ASM_REWRITE_TAC[wl_set_vars_def; wl_state_INFO.ri_accfupds; K_THM; alist_insert_def] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[PAIR_EQ; UNWIND_THM1; UNWIND_THM2] THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; WBIGPAUX_rec_lookup0] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN
  MATCH_MP_TAC WBIGPAUX_state_rel_cong THEN
  REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM]));;

let WBIGPAUX_compile_Rec = prove
 (el 14 WBIGPAUX_compile_cases,
  (REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check WBIGPAUX_is_compile_eq) THEN
  REWRITE_TAC[word_bignum_compile_def; PAIR_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[word_bignumProof_syntax_ok_def; syntax_ok_aux_def])) THEN
  (FIRST_ASSUM(MP_TAC o SPEC `p:(A)mini` o check (fun th ->
    try let v,bd = dest_forall(concl th) in
        fst(dest_var v) = "body" && is_imp bd &&
        fst(dest_const(fst(strip_comb(lhs(lhand bd))))) = "SOME"
    with _ -> false)) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lb:num` (X_CHOOSE_THEN `ib:num`
    (X_CHOOSE_THEN `csb:num#((A)mini#num#(A)wl_prog)list` (X_CHOOSE_THEN `pb:(A)wl_prog`
    (X_CHOOSE_THEN `lb1:num` (X_CHOOSE_THEN `ib1:num`
    (X_CHOOSE_THEN `csb1:num#((A)mini#num#(A)wl_prog)list` STRIP_ASSUME_TAC))))))) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `vals:(A word)list` o MATCH_MP copy_vars_IMP)) THEN
  (REWRITE_TAC[WBIGPAUX_ev_Seq] THEN
  MP_TAC(GEN `pp:(A)wl_prog` (INST [`pp:(A)wl_prog`,`p:(A)wl_prog`]
    (SPECL [`save_regs:num list`; `vals:(A word)list`; `t1:(A,C,FFI)wl_state`]
       evaluate_LoadRegs))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th])) THEN
  (ABBREV_TAC `t1' = wl_state_locals_fupd (K (list_update (MAP (\n. n + 2) save_regs)
      (MAP wl_Word vals) (wl_state_locals t1))) (t1:(A,C,FFI)wl_state)`) THEN
  (SUBGOAL_THEN `~(wl_state_clock (t1:(A,C,FFI)wl_state) = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `word_bignumProof_state_rel (s1:(A)word_bignumProof_state)
                   (t1:(A,C,FFI)wl_state) cs2 t0 frame` THEN
    REWRITE_TAC[word_bignumProof_state_rel_def] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
      `word_bignumProof_state_clock (s1:(A)word_bignumProof_state) =
       wl_state_clock (t1:(A,C,FFI)wl_state)`)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `word_bignumProof_state_rel (s1:(A)word_bignumProof_state)
                  (t1':(A,C,FFI)wl_state) cs2 t0 frame /\
                lookup n (wl_state_code t1') = SOME (1,wl_Seq pb (wl_Return 0 [0])) /\
                lookup 0 (wl_state_locals t1') = SOME ret_val /\
                ~(wl_state_clock t1' = 0) /\
                ALL2 (\r v. lookup (r + 2) (wl_state_locals t1') = SOME (wl_Word v))
                  save_regs vals`
  STRIP_ASSUME_TAC THENL
   [(EXPAND_TAC "t1'" THEN
    REWRITE_TAC[wl_state_INFO.ri_accfupds; K_THM; WBIGPAUX_state_rel_locals;
                lookup_list_update_ADD_2]) THEN
    (RULE_ASSUM_TAC(REWRITE_RULE[wl_get_var_def]) THEN ASM_REWRITE_TAC[]) THEN
    (MATCH_MP_TAC WBIGPAUX_lookup_list_update THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP LIST_REL_LENGTH));
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`t1':(A,C,FFI)wl_state`;
     `inter (wl_state_locals (t1':(A,C,FFI)wl_state)) (LS one)`;
     `inter (wl_state_locals (t1':(A,C,FFI)wl_state))
        (list_insert (MAP (\k. k + 2) save_regs) LN)`;
     `wl_Loc n l:(A)word_loc`; `lookup n (wl_state_stack_size (t1':(A,C,FFI)wl_state))`]
     WBIGPAUX_call_push_gen) THEN
  ABBREV_TAC `cst = wl_call_env [wl_Loc n l] (lookup n (wl_state_stack_size t1'))
     (wl_push_env (inter (wl_state_locals t1') (LS one),
                   inter (wl_state_locals t1') (list_insert (MAP (\k. k + 2) save_regs) LN))
        NONE (wl_dec_clock (t1':(A,C,FFI)wl_state)))` THEN
  STRIP_TAC THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`n:num`; `lb:num`; `ib:num`;
     `csb:num#((A)mini#num#(A)wl_prog)list`;
     `pb:(A)wl_prog`; `lb1:num`; `ib1:num`; `csb1:num#((A)mini#num#(A)wl_prog)list`;
     `cs2:num#((A)mini#num#(A)wl_prog)list`; `cst:(A,C,FFI)wl_state`;
     `wl_Loc n l:(A)word_loc`; `wl_Return 0 [0]:(A)wl_prog`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[word_bignum_compile_def; word_bignumProof_syntax_ok_def;
                    injectivity "mini"] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC state_rel_delete_vars THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[option_INJ] THEN GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`lb:num`; `ib:num`; `csb:num#((A)mini#num#(A)wl_prog)list`;
      `pb:(A)wl_prog`; `lb1:num`; `ib1:num`; `csb1:num#((A)mini#num#(A)wl_prog)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (CASE_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:(A,C,FFI)wl_state` (X_CHOOSE_THEN
    `res1:((A)wl_result)option#(A,C,FFI)wl_state` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t1':(A,C,FFI)wl_state`; `n:num`; `l:num`; `save_regs:num list`;
    `vals:(A word)list`; `ret_val:(A)word_loc`; `pb:(A)wl_prog`; `u:(A,C,FFI)wl_state`]
    WBIGPAUX_ev_call_rec) THEN
  ASM_REWRITE_TAC[]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `tt:(A,C,FFI)wl_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `tt:(A,C,FFI)wl_state` THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THEN
  EXISTS_TAC `wl_evaluate (p9:(A)wl_prog,tt:(A,C,FFI)wl_state)` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `wl_state_stack (t1':(A,C,FFI)wl_state) =
                wl_state_stack (t1:(A,C,FFI)wl_state) /\
                wl_state_code t1' = wl_state_code t1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t1'" THEN REWRITE_TAC[wl_state_INFO.ri_accfupds]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC(ISPECL [`save_regs:num list`; `vals:(A word)list`;
    `s2:(A)word_bignumProof_state`] WBIGPAUX_state_rel_copy_vars) THEN
  ASM_REWRITE_TAC[]));;

let word_bignumProof_compile_thm = prove
 (WBIGPAUX_compile_thm_stmt,
  MATCH_MP_TAC WBIGPAUX_compile_ind THEN REPEAT CONJ_TAC THEN
  FIRST (map MATCH_ACCEPT_TAC
    [WBIGPAUX_compile_Skip; WBIGPAUX_compile_Continue; WBIGPAUX_compile_Delete;
     WBIGPAUX_compile_Assign; WBIGPAUX_compile_Seq; WBIGPAUX_compile_If;
     WBIGPAUX_compile_Load; WBIGPAUX_compile_Store; WBIGPAUX_compile_Swap;
     WBIGPAUX_compile_Add; WBIGPAUX_compile_Sub; WBIGPAUX_compile_Mul;
     WBIGPAUX_compile_Div; WBIGPAUX_compile_Loop; WBIGPAUX_compile_Rec;
     WBIGPAUX_compile_LoopBody1; WBIGPAUX_compile_LoopBody2]));;

let word_bignumProof_good_code_def = cake_def
  `word_bignumProof_good_code (cs3:num#((A)mini#num#(A)wl_prog)list) <=>
     !prog n p2.
       MEM (prog,n,p2) (SND cs3) ==>
       ?cs1 l2' i2 cs2.
         word_bignum_compile n 2 1 cs1 prog = (p2,l2',i2,cs2) /\ code_subset cs2 cs3`;;

let WBIGPAUX_compile_Loop_cs = prove
 (`!n l i cs rc vs (body:(A)mini) q l1 i1 cs1.
     word_bignum_compile n l i cs (word_bignum_Loop rc vs body) = (q,l1,i1,cs1) ==>
     (?x. has_compiled body cs = INL x /\ cs1 = cs) \/
     (?ni nc a b cs'. has_compiled body cs = INR ni /\
        word_bignum_compile ni 2 1 (code_acc_next cs) body = (nc,a,b,cs') /\
        cs1 = install (body,ni,nc) cs')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[word_bignum_compile_def] THEN
  MP_TAC(ISPEC `has_compiled (body:(A)mini) (cs:num#((A)mini#num#(A)wl_prog)list)`
    (cases "sum")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[] THENL
   [REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    ASM_MESON_TAC[]]);;

let WBIGPAUX_SND_install = prove
 (`!(c:A) (cs:B#(A)list). SND (install c cs) = CONS c (SND cs)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; install_def]);;

let WBIGPAUX_SND_code_acc_next = prove
 (`!(cs:num#A). SND (code_acc_next cs) = SND cs`,
  REWRITE_TAC[FORALL_PAIR_THM; code_acc_next_def]);;

let WBIGPAUX_T0 = REWRITE_TAC[word_bignum_compile_def; PAIR_EQ] THEN MESON_TAC[];;

let WBIGPAUX_TSEQ getwit =
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN getwit THEN
  X_GEN_TAC `y:(A)mini#num#(A)wl_prog` THEN STRIP_TAC THEN
  ASM_CASES_TAC `MEM (y:(A)mini#num#(A)wl_prog)
                   (SND (csa:num#((A)mini#num#(A)wl_prog)list))` THENL
   [REMOVE_THEN "ih1" (MP_TAC o SPECL [`q1:(A)wl_prog`; `la:num`; `ia:num`;
       `csa:num#((A)mini#num#(A)wl_prog)list`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:(A)mini#num#(A)wl_prog`) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`q1:(A)wl_prog`; `la:num`; `ia:num`;
       `csa:num#((A)mini#num#(A)wl_prog)list`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`q2:(A)wl_prog`; `xx2:num`; `ib:num`;
       `xx5:num#((A)mini#num#(A)wl_prog)list`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:(A)mini#num#(A)wl_prog`) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC];;

let compile_LESS_mini_size = prove
 (`!k l1 l2 (yy5:num#((A)mini#num#(A)wl_prog)list) code xx1 xx2 xx3 xx5.
     word_bignum_compile k l1 l2 yy5 code = (xx1,xx2,xx3,xx5) ==>
     !x. MEM x (SND xx5) /\ ~MEM x (SND yy5) ==>
         mini_size (K 0) (FST x) < mini_size (K 0) code`,
  MATCH_MP_TAC word_bignum_compile_ind THEN
  REWRITE_TAC[type_size_def "mini"] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [WBIGPAUX_T0; WBIGPAUX_T0; WBIGPAUX_T0;
    (* Loop *)
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC o MATCH_MP WBIGPAUX_compile_Loop_cs) THENL
     [ASM_MESON_TAC[];
      X_GEN_TAC `y:(A)mini#num#(A)wl_prog` THEN
      ASM_REWRITE_TAC[WBIGPAUX_SND_install; MEM] THEN STRIP_TAC THENL
       [ASM_REWRITE_TAC[FST] THEN ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o SPEC `ni:num`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPECL [`nc:(A)wl_prog`; `a:num`; `b:num`;
          `cs':num#((A)mini#num#(A)wl_prog)list`]) THEN
        ASM_REWRITE_TAC[WBIGPAUX_SND_code_acc_next] THEN
        DISCH_THEN(MP_TAC o SPEC `y:(A)mini#num#(A)wl_prog`) THEN ASM_REWRITE_TAC[] THEN
        ARITH_TAC]];
    (* LoopBody *)
    REWRITE_TAC[word_bignum_compile_def] THEN MESON_TAC[ARITH_RULE `a < b ==> a < 1 + b`];
    (* Seq *)
    WBIGPAUX_TSEQ (REWRITE_TAC[WBIGPAUX_compile_Seq_eq] THEN
      DISCH_THEN(X_CHOOSE_THEN `q1:(A)wl_prog` (X_CHOOSE_THEN `la:num`
        (X_CHOOSE_THEN `ia:num` (X_CHOOSE_THEN `csa:num#((A)mini#num#(A)wl_prog)list`
        (X_CHOOSE_THEN `q2:(A)wl_prog` STRIP_ASSUME_TAC))))) THEN
      ABBREV_TAC `ib = xx3:num`);
    (* If *)
    WBIGPAUX_TSEQ (DISCH_THEN(MP_TAC o MATCH_MP WBIGPAUX_compile_If_eq) THEN
      DISCH_THEN(X_CHOOSE_THEN `q1:(A)wl_prog` (X_CHOOSE_THEN `la:num`
        (X_CHOOSE_THEN `ia:num` (X_CHOOSE_THEN `csa:num#((A)mini#num#(A)wl_prog)list`
        (X_CHOOSE_THEN `q2:(A)wl_prog` (X_CHOOSE_THEN `ib:num` STRIP_ASSUME_TAC)))))));
    WBIGPAUX_T0; WBIGPAUX_T0; WBIGPAUX_T0; WBIGPAUX_T0; WBIGPAUX_T0;
    WBIGPAUX_T0; WBIGPAUX_T0; WBIGPAUX_T0; WBIGPAUX_T0]);;

let WBIGPAUX_code_subset_SND = prove
 (`!(c1:A#(B#C)list) (c2:D#(B#C)list).
     code_subset c1 c2 <=>
     !n v. ALOOKUP (SND c1) n = SOME v ==> ALOOKUP (SND c2) n = SOME v`,
  REWRITE_TAC[FORALL_PAIR_THM; code_subset_def]);;

let WBIGPAUX_good_code_code_acc_next = prove
 (`!cs:num#((A)mini#num#(A)wl_prog)list.
     word_bignumProof_good_code (code_acc_next cs) <=> word_bignumProof_good_code cs`,
  REWRITE_TAC[word_bignumProof_good_code_def; WBIGPAUX_code_subset_SND;
              WBIGPAUX_SND_code_acc_next]);;

let WBIGPAUX_has_compiled_INR_NONE = prove
 (`!(body:A) (cs:num#(A#num#B)list) ni.
     has_compiled body cs = INR ni ==> ALOOKUP (SND cs) body = NONE`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; has_compiled_def] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `cl:(A#num#B)list`; `ni:num`] THEN
  MP_TAC(ISPEC `ALOOKUP (cl:(A#num#B)list) body` (cases "option")) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[SND] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "sum"] THEN
  SPEC_TAC(`a:num#B`,`a:num#B`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[distinctness "sum"]);;

let WBIGPAUX_TSEQ2 getwit =
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN getwit THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`q1:(A)wl_prog`; `la:num`; `ia:num`;
    `csa:num#((A)mini#num#(A)wl_prog)list`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REMOVE_THEN "ih2" (MP_TAC o SPECL [`q1:(A)wl_prog`; `la:num`; `ia:num`;
    `csa:num#((A)mini#num#(A)wl_prog)list`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`q2:(A)wl_prog`; `xx2:num`; `ib:num`;
    `xx5:num#((A)mini#num#(A)wl_prog)list`]) THEN
  ASM_REWRITE_TAC[];;

let MEM_compile = prove
 (`!k l1 l2 (yy5:num#((A)mini#num#(A)wl_prog)list) code xx1 xx2 xx3 xx5.
     word_bignumProof_good_code yy5 /\
     word_bignum_compile k l1 l2 yy5 code = (xx1,xx2,xx3,xx5) ==>
     word_bignumProof_good_code xx5`,
  MATCH_MP_TAC word_bignum_compile_ind THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [WBIGPAUX_T0; WBIGPAUX_T0; WBIGPAUX_T0;
    (* Loop *)
    DISCH_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (DISJ_CASES_THEN STRIP_ASSUME_TAC o MATCH_MP WBIGPAUX_compile_Loop_cs)) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ni:num` o check (fun th -> is_forall (concl th))) THEN
    ASM_REWRITE_TAC[WBIGPAUX_good_code_code_acc_next] THEN
    DISCH_THEN(MP_TAC o SPECL [`nc:(A)wl_prog`; `a:num`; `b:num`;
      `cs':num#((A)mini#num#(A)wl_prog)list`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `ALOOKUP (SND (cs':num#((A)mini#num#(A)wl_prog)list)) body = NONE`
    ASSUME_TAC THENL
     [REWRITE_TAC[ALOOKUP_NONE; MEM_MAP; EXISTS_PAIR_THM; FST; NOT_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`b0:(A)mini`; `v0:num`; `w0:(A)wl_prog`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`ni:num`; `2`; `1`;
        `code_acc_next (cs:num#((A)mini#num#(A)wl_prog)list)`; `body:(A)mini`;
        `nc:(A)wl_prog`; `a:num`; `b:num`; `cs':num#((A)mini#num#(A)wl_prog)list`]
        compile_LESS_mini_size) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `(b0:(A)mini),(v0:num),(w0:(A)wl_prog)`) THEN
      ASM_REWRITE_TAC[WBIGPAUX_SND_code_acc_next; FST; LT_REFL] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP WBIGPAUX_has_compiled_INR_NONE) THEN
      REWRITE_TAC[ALOOKUP_NONE; MEM_MAP; EXISTS_PAIR_THM; FST] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!c2:num#((A)mini#num#(A)wl_prog)list.
                    code_subset c2 (cs':num#((A)mini#num#(A)wl_prog)list) ==>
                    code_subset c2 (install ((body:(A)mini),(ni:num),(nc:(A)wl_prog)) cs')`
    ASSUME_TAC THENL
     [REWRITE_TAC[WBIGPAUX_code_subset_SND; WBIGPAUX_SND_install; ALOOKUP_THM] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
       [ASM_MESON_TAC[option_DISTINCT]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[word_bignumProof_good_code_def; WBIGPAUX_SND_install; MEM; PAIR_EQ] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`code_acc_next (cs:num#((A)mini#num#(A)wl_prog)list)`;
        `a:num`; `b:num`; `cs':num#((A)mini#num#(A)wl_prog)list`] THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[code_subset_refl];
      UNDISCH_TAC `word_bignumProof_good_code
                     (cs':num#((A)mini#num#(A)wl_prog)list)` THEN
      REWRITE_TAC[word_bignumProof_good_code_def] THEN ASM_MESON_TAC[]];
    (* LoopBody *)
    REWRITE_TAC[word_bignum_compile_def] THEN MESON_TAC[];
    (* Seq *)
    WBIGPAUX_TSEQ2 (REWRITE_TAC[WBIGPAUX_compile_Seq_eq] THEN
      DISCH_THEN(X_CHOOSE_THEN `q1:(A)wl_prog` (X_CHOOSE_THEN `la:num`
        (X_CHOOSE_THEN `ia:num` (X_CHOOSE_THEN `csa:num#((A)mini#num#(A)wl_prog)list`
        (X_CHOOSE_THEN `q2:(A)wl_prog` STRIP_ASSUME_TAC))))) THEN
      ABBREV_TAC `ib = xx3:num`);
    (* If *)
    WBIGPAUX_TSEQ2 (DISCH_THEN(MP_TAC o MATCH_MP WBIGPAUX_compile_If_eq) THEN
      DISCH_THEN(X_CHOOSE_THEN `q1:(A)wl_prog` (X_CHOOSE_THEN `la:num`
        (X_CHOOSE_THEN `ia:num` (X_CHOOSE_THEN `csa:num#((A)mini#num#(A)wl_prog)list`
        (X_CHOOSE_THEN `q2:(A)wl_prog` (X_CHOOSE_THEN `ib:num` STRIP_ASSUME_TAC)))))));
    WBIGPAUX_T0; WBIGPAUX_T0; WBIGPAUX_T0; WBIGPAUX_T0; WBIGPAUX_T0;
    WBIGPAUX_T0; WBIGPAUX_T0; WBIGPAUX_T0; WBIGPAUX_T0]);;

let compile_NIL_IMP = prove
 (`!k l1 l2 l (code:(A)mini) xx1 xx2 xx3 xx5.
     word_bignum_compile k l1 l2 (l,[]) code = (xx1,xx2,xx3,xx5) ==>
     !prog n p2.
       MEM (prog,n,p2) (SND xx5) ==>
       ?cs1 l2' i2 cs2.
         word_bignum_compile n 2 1 cs1 prog = (p2,l2',i2,cs2) /\ code_subset cs2 xx5`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:num`; `l1:num`; `l2:num`; `(l:num),([]:((A)mini#num#(A)wl_prog)list)`;
    `code:(A)mini`; `xx1:(A)wl_prog`; `xx2:num`; `xx3:num`;
    `xx5:num#((A)mini#num#(A)wl_prog)list`] MEM_compile) THEN
  ASM_REWRITE_TAC[word_bignumProof_good_code_def; MEM; SND]);;


(* ------------------------------------------------------------------------- *)
(* correctness judgement                                                     *)
(* ------------------------------------------------------------------------- *)

(* HOL4: val all_corrs = ref (tl [TRUTH]) is WBIGPAUX_all_corrs below *)

let word_bignumProof_Corr_def = new_definition
  `Corr prog (s:(A)word_bignumProof_state) s1 p <=>
     (p ==> word_bignumProof_Eval NONE s prog s1)`;;

let Corr_Skip = prove
 (`Corr word_bignum_Skip (s:(A)word_bignumProof_state) (INR s) T`,
  REWRITE_TAC[word_bignumProof_Corr_def; WBIGPAUX_eval_cases]);;

let Corr_Seq = prove
 (`Corr p2 s1 s2 q2 ==>
   Corr p1 (s:(A)word_bignumProof_state) (INR s1) q1 ==>
   Corr (word_bignum_Seq p1 p2) s s2 (q1 /\ q2)`,
  REWRITE_TAC[word_bignumProof_Corr_def; WBIGPAUX_eval_cases] THEN MESON_TAC[]);;

let Corr_Seq_alt = prove
 (`(b ==> Corr p2 s1 s2 q2) ==>
   Corr p1 (s:(A)word_bignumProof_state) (INR s1) q1 ==>
   b ==> Corr (word_bignum_Seq p1 p2) s s2 (q1 /\ q2)`,
  REWRITE_TAC[word_bignumProof_Corr_def; WBIGPAUX_eval_cases] THEN MESON_TAC[]);;

let Corr_Continue = prove
 (`Corr word_bignum_Continue (s:(A)word_bignumProof_state) (INL s) T`,
  REWRITE_TAC[word_bignumProof_Corr_def; WBIGPAUX_eval_cases]);;

let Corr_Assign = prove
 (`Corr (word_bignum_Assign n x) (s:(A)word_bignumProof_state)
      (INR (reg_write n (SOME (eval_exp s x)) s))
      (eval_exp_pre s x)`,
  REWRITE_TAC[word_bignumProof_Corr_def; WBIGPAUX_eval_cases]);;

let Corr_Delete = prove
 (`Corr (Delete vs) (s:(A)word_bignumProof_state) (INR (delete_vars vs s)) T`,
  REWRITE_TAC[word_bignumProof_Corr_def; WBIGPAUX_eval_cases; FLOOKUP_DEF]);;

let Corr_Load = prove
 (`Corr (word_bignum_Load r i a) (s:(A)word_bignumProof_state)
      (INR (reg_write r (SOME (EL (val (FAPPLY (word_bignumProof_state_regs s) i))
                                  (word_bignumProof_state_arrays s a))) s))
      (i IN FDOM (word_bignumProof_state_regs s) /\
       val (FAPPLY (word_bignumProof_state_regs s) i) <
       LENGTH (word_bignumProof_state_arrays s a))`,
  REWRITE_TAC[word_bignumProof_Corr_def; WBIGPAUX_eval_cases; FLOOKUP_DEF] THEN
  MESON_TAC[]);;

let Corr_Store = prove
 (`Corr (word_bignum_Store r i) (s:(A)word_bignumProof_state)
      (INR (array_write Out
              (LUPDATE (FAPPLY (word_bignumProof_state_regs s) r)
                 (val (FAPPLY (word_bignumProof_state_regs s) i))
                 (word_bignumProof_state_arrays s Out)) s))
      (r IN FDOM (word_bignumProof_state_regs s) /\
       i IN FDOM (word_bignumProof_state_regs s) /\
       val (FAPPLY (word_bignumProof_state_regs s) i) <
       LENGTH (word_bignumProof_state_arrays s Out))`,
  REWRITE_TAC[word_bignumProof_Corr_def; WBIGPAUX_eval_cases; FLOOKUP_DEF] THEN
  MESON_TAC[]);;

let Corr_Swap = prove
 (`Corr Swap (s:(A)word_bignumProof_state)
      (INR (array_write In1 (word_bignumProof_state_arrays s In2)
             (array_write In2 (word_bignumProof_state_arrays s In1) s))) T`,
  REWRITE_TAC[word_bignumProof_Corr_def; WBIGPAUX_eval_cases]);;

let Corr_Add = prove
 (`Corr (word_bignum_Add n1 n2 n3 ri1 ri2) (s:(A)word_bignumProof_state)
      (INR (reg_write n1
              (SOME (FST (single_add_word (FAPPLY (word_bignumProof_state_regs s) n3)
                            (eval_ri s ri1) (eval_ri s ri2))))
            (reg_write n2
              (SOME (SND (single_add_word (FAPPLY (word_bignumProof_state_regs s) n3)
                            (eval_ri s ri1) (eval_ri s ri2)))) s)))
      (n3 IN FDOM (word_bignumProof_state_regs s) /\ eval_ri_pre s ri1 /\
       eval_ri_pre s ri2 /\
       (~(eval_ri s ri2 = word 0) ==> eval_ri s ri2 = word 1) /\ ~(n1 = n2))`,
  REWRITE_TAC[word_bignumProof_Corr_def; WBIGPAUX_eval_cases] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[PAIR]);;

let Corr_Sub = prove
 (`Corr (word_bignum_Sub n1 n2 n3 ri1 ri2) (s:(A)word_bignumProof_state)
      (INR (reg_write n1
              (SOME (FST (single_sub_word (FAPPLY (word_bignumProof_state_regs s) n3)
                            (eval_ri s ri1) (eval_ri s ri2))))
            (reg_write n2
              (SOME (SND (single_sub_word (FAPPLY (word_bignumProof_state_regs s) n3)
                            (eval_ri s ri1) (eval_ri s ri2)))) s)))
      (n3 IN FDOM (word_bignumProof_state_regs s) /\ eval_ri_pre s ri1 /\
       eval_ri_pre s ri2 /\
       (~(eval_ri s ri2 = word 0) ==> eval_ri s ri2 = word 1) /\ ~(n1 = n2))`,
  REWRITE_TAC[word_bignumProof_Corr_def; WBIGPAUX_eval_cases] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[PAIR]);;

let Corr_Mul = prove
 (`Corr (word_bignum_Mul n1 n2 n3 n4) (s:(A)word_bignumProof_state)
      (INR (reg_write n1
              (SOME (FST (single_mul (FAPPLY (word_bignumProof_state_regs s) n3)
                            (FAPPLY (word_bignumProof_state_regs s) n4) (word 0))))
            (reg_write n2
              (SOME (SND (single_mul (FAPPLY (word_bignumProof_state_regs s) n3)
                            (FAPPLY (word_bignumProof_state_regs s) n4) (word 0)))) s)))
      (n3 IN FDOM (word_bignumProof_state_regs s) /\
       n4 IN FDOM (word_bignumProof_state_regs s) /\ ~(n1 = n2))`,
  REWRITE_TAC[word_bignumProof_Corr_def; WBIGPAUX_eval_cases]);;

let Corr_Div = prove
 (`Corr (word_bignum_Div n1 n2 n3 n4 n5) (s:(A)word_bignumProof_state)
      (INR (reg_write n1
              (SOME (FST (single_div (FAPPLY (word_bignumProof_state_regs s) n3)
                            (FAPPLY (word_bignumProof_state_regs s) n4)
                            (FAPPLY (word_bignumProof_state_regs s) n5))))
            (reg_write n2
              (SOME (SND (single_div (FAPPLY (word_bignumProof_state_regs s) n3)
                            (FAPPLY (word_bignumProof_state_regs s) n4)
                            (FAPPLY (word_bignumProof_state_regs s) n5)))) s)))
      (n3 IN FDOM (word_bignumProof_state_regs s) /\
       n4 IN FDOM (word_bignumProof_state_regs s) /\
       n5 IN FDOM (word_bignumProof_state_regs s) /\ ~(n1 = n2) /\
       single_div_pre (FAPPLY (word_bignumProof_state_regs s) n3)
         (FAPPLY (word_bignumProof_state_regs s) n4)
         (FAPPLY (word_bignumProof_state_regs s) n5))`,
  REWRITE_TAC[word_bignumProof_Corr_def; WBIGPAUX_eval_cases]);;

let Corr_If = prove
 (`Corr p1 (s:(A)word_bignumProof_state) f1 q1 /\ Corr p2 s f2 q2 ==>
   Corr (word_bignum_If c r ri p1 p2) s
     (if asm_word_cmp c (eval_exp s (wl_Var r)) (eval_ri s ri) then f1 else f2)
     (r IN FDOM (word_bignumProof_state_regs s) /\ eval_ri_pre s ri /\
      if asm_word_cmp c (eval_exp s (wl_Var r)) (eval_ri s ri) then q1 else q2)`,
  REWRITE_TAC[word_bignumProof_Corr_def; WBIGPAUX_eval_cases] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN MESON_TAC[]);;

let loop_app_def = cake_def
  `loop_app (f:(A)word_bignumProof_state->
                (A)word_bignumProof_state+(A)word_bignumProof_state) g x =
     match f x with
       INL s -> (INL (word_bignumProof_dec_clock s),
                 (g x /\ ~(word_bignumProof_state_clock s = 0)))
     | INR s -> (INR s, g x)`;;

let Corr_LoopBody = prove
 (`(!s. Corr p s ((f:(A)word_bignumProof_state->
                     (A)word_bignumProof_state+(A)word_bignumProof_state) s) (q s)) ==>
   !s. Corr (LoopBody p) s (INR (SHORT_TAILREC (loop_app f q) s))
          (SHORT_TAILREC_PRE (loop_app f q) s)`,
  REWRITE_TAC[word_bignumProof_Corr_def] THEN DISCH_TAC THEN
  MATCH_MP_TAC SHORT_TAILREC_PRE_INDUCT THEN
  X_GEN_TAC `s:(A)word_bignumProof_state` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[SHORT_TAILREC_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[loop_app_def]) THEN REWRITE_TAC[loop_app_def] THEN
  DISJ_CASES_THEN2
    (X_CHOOSE_THEN `s1:(A)word_bignumProof_state`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN
                 ASSUME_TAC th))
    (X_CHOOSE_THEN `s1:(A)word_bignumProof_state`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN
                 ASSUME_TAC th))
    (ISPEC `(f:(A)word_bignumProof_state->
               (A)word_bignumProof_state+(A)word_bignumProof_state) s` (cases "sum")) THEN
  RULE_ASSUM_TAC(CASE_REWRITE_RULE[]) THEN CASE_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ISL; OUTL; OUTR; injectivity "sum";
                              distinctness "sum"; FST; SND]) THEN
  REWRITE_TAC[ISL; OUTL; OUTR; injectivity "sum"; distinctness "sum"] THENL
   [MATCH_MP_TAC WBIGPAUX_eval_LoopBody2 THEN
    EXISTS_TAC `s1:(A)word_bignumProof_state` THEN ASM_MESON_TAC[];
    MATCH_MP_TAC WBIGPAUX_eval_LoopBody1 THEN ASM_MESON_TAC[]]);;

let tick_before_def = cake_def
  `tick_before vs (f:(A)word_bignumProof_state->(A)word_bignumProof_state#bool) s =
     if word_bignumProof_state_clock s = 0 then (s,F)
     else f (delete_vars vs (word_bignumProof_dec_clock s))`;;

let Corr_Loop_lemma = prove
 (`(!s. Corr (LoopBody p) s (INR ((f:(A)word_bignumProof_state->(A)word_bignumProof_state) s))
         (q s)) ==>
   Corr (word_bignum_Loop F vs p) s (INR (f (delete_vars vs (word_bignumProof_dec_clock s))))
     (q (delete_vars vs (word_bignumProof_dec_clock s)) /\
      ~(word_bignumProof_state_clock s = 0))`,
  REWRITE_TAC[word_bignumProof_Corr_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC WBIGPAUX_eval_Loop THEN ASM_SIMP_TAC[]);;

(* HOL4: val Corr_Loop = MATCH_MP Corr_Loop_lemma (Corr_LoopBody |> UNDISCH) *)
(* |> DISCH_ALL                                                            *)

let WBIGPAUX_Corr_Loop = DISCH_ALL (MATCH_MP Corr_Loop_lemma (UNDISCH Corr_LoopBody));;

let Corr_STRENGTHEN_TERM = prove
 (`Corr p (s:(A)word_bignumProof_state) f q ==>
   !f' q'. (q' ==> (f = INR f') /\ q) ==> Corr p s (INR f') q'`,
  REWRITE_TAC[word_bignumProof_Corr_def] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* derive Corr thm from AST                                                  *)
(* ------------------------------------------------------------------------- *)

let dec_clock_thm = prove
 (`word_bignumProof_dec_clock (s:(A)word_bignumProof_state) =
   clock_write (word_bignumProof_state_clock s - 1) s`,
  REWRITE_TAC[word_bignumProof_dec_clock_def; clock_write_def]);;

let array_write_cancel = prove
 (`array_write n (word_bignumProof_state_arrays s n) (s:(A)word_bignumProof_state) = s`,
  REWRITE_TAC[array_write_def; word_bignumProof_state_component_equality;
              word_bignumProof_state_INFO.ri_accfupds; K_THM; FUN_EQ_THM;
              APPLY_UPDATE_THM] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [array_write_cancel];;

let reg_write_cancel = prove
 (`(n IN FDOM (word_bignumProof_state_regs s) ==>
    reg_write n (SOME (FAPPLY (word_bignumProof_state_regs s) n)) s =
    (s:(A)word_bignumProof_state)) /\
   (~(n IN FDOM (word_bignumProof_state_regs s)) ==> reg_write n NONE s = s)`,
  REWRITE_TAC[reg_write_def; word_bignumProof_state_component_equality;
              word_bignumProof_state_INFO.ri_accfupds; K_THM; fmap_eq_flookup;
              FLOOKUP_UPDATE; DOMSUB_FLOOKUP_THM] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[FLOOKUP_DEF] THEN
  ASM_MESON_TAC[]);;
let _ = cake_add_simps [reg_write_cancel];;

let state_eq_lemma = prove
 (`(s0:(A)word_bignumProof_state) = s1 <=>
   word_bignumProof_state_clock s0 = word_bignumProof_state_clock s1 /\
   FDOM (word_bignumProof_state_regs s0) = FDOM (word_bignumProof_state_regs s1) /\
   (!n. n IN FDOM (word_bignumProof_state_regs s0) ==>
        FAPPLY (word_bignumProof_state_regs s0) n =
        FAPPLY (word_bignumProof_state_regs s1) n) /\
   (!n. word_bignumProof_state_arrays s0 n = word_bignumProof_state_arrays s1 n)`,
  REWRITE_TAC[word_bignumProof_state_component_equality; fmap_EXT; FUN_EQ_THM] THEN
  CONV_TAC TAUT);;

let clock_write_simp = prove
 (`word_bignumProof_state_regs (clock_write n (s:(A)word_bignumProof_state)) =
   word_bignumProof_state_regs s /\
   word_bignumProof_state_arrays (clock_write n s) = word_bignumProof_state_arrays s /\
   word_bignumProof_state_clock (clock_write n s) = n`,
  REWRITE_TAC[clock_write_def; word_bignumProof_state_INFO.ri_accfupds; K_THM]);;
let _ = cake_add_simps [clock_write_simp];;

let dec_clock_write_simp = prove
 (`word_bignumProof_state_regs (word_bignumProof_dec_clock (s:(A)word_bignumProof_state)) =
   word_bignumProof_state_regs s /\
   word_bignumProof_state_arrays (word_bignumProof_dec_clock s) =
   word_bignumProof_state_arrays s /\
   word_bignumProof_state_clock (word_bignumProof_dec_clock s) =
   word_bignumProof_state_clock s - 1`,
  REWRITE_TAC[word_bignumProof_dec_clock_def; word_bignumProof_state_INFO.ri_accfupds;
              K_THM]);;
let _ = cake_add_simps [dec_clock_write_simp];;

let reg_write_simp = prove
 (`word_bignumProof_state_regs (reg_write n NONE (s:(A)word_bignumProof_state)) =
   word_bignumProof_state_regs s \\ n /\
   word_bignumProof_state_regs (reg_write n (SOME w) s) =
   word_bignumProof_state_regs s |+ (n,w) /\
   word_bignumProof_state_arrays (reg_write n v s) = word_bignumProof_state_arrays s /\
   word_bignumProof_state_clock (reg_write n v s) = word_bignumProof_state_clock s`,
  STRUCT_CASES_TAC (ISPEC `v:(A word)option` (cases "option")) THEN
  REWRITE_TAC[reg_write_def; word_bignumProof_state_INFO.ri_accfupds; K_THM]);;
let _ = cake_add_simps [reg_write_simp];;

let reg_write_simp_alt = prove
 (`(FAPPLY (word_bignumProof_state_regs (reg_write n NONE (s:(A)word_bignumProof_state))) m =
    if n = m then FAPPLY FEMPTY m else FAPPLY (word_bignumProof_state_regs s) m) /\
   (FAPPLY (word_bignumProof_state_regs (reg_write n (SOME w) s)) m =
    if n = m then w else FAPPLY (word_bignumProof_state_regs s) m) /\
   (FDOM (word_bignumProof_state_regs (reg_write n NONE s)) =
    FDOM (word_bignumProof_state_regs s) DELETE n) /\
   (FDOM (word_bignumProof_state_regs (reg_write n (SOME w) s)) =
    n INSERT FDOM (word_bignumProof_state_regs s))`,
  REWRITE_TAC[reg_write_simp; DOMSUB_FAPPLY_THM; FAPPLY_FUPDATE_THM; FDOM_DOMSUB;
              FDOM_FUPDATE] THEN
  MESON_TAC[]);;

let array_write_simp = prove
 (`word_bignumProof_state_regs (array_write n w (s:(A)word_bignumProof_state)) =
   word_bignumProof_state_regs s /\
   word_bignumProof_state_arrays (array_write n w s) =
   (n =+ w) (word_bignumProof_state_arrays s) /\
   word_bignumProof_state_clock (array_write n w s) = word_bignumProof_state_clock s`,
  REWRITE_TAC[array_write_def; word_bignumProof_state_INFO.ri_accfupds; K_THM]);;
let _ = cake_add_simps [array_write_simp];;

let delete_vars_simp = prove
 (`!vs. word_bignumProof_state_clock (delete_vars vs (s:(A)word_bignumProof_state)) =
        word_bignumProof_state_clock s /\
        word_bignumProof_state_arrays (delete_vars vs s) =
        word_bignumProof_state_arrays s /\
        FLOOKUP (word_bignumProof_state_regs (delete_vars vs s)) n =
        (if MEM n vs then NONE else FLOOKUP (word_bignumProof_state_regs s) n) /\
        (n IN FDOM (word_bignumProof_state_regs (delete_vars vs s)) <=>
         if MEM n vs then F else n IN FDOM (word_bignumProof_state_regs s))`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[delete_vars_def; MEM; reg_write_simp;
    DOMSUB_FLOOKUP_THM; FDOM_DOMSUB; IN_DELETE] THEN
  REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[]);;
let _ = cake_add_simps [delete_vars_simp];;

(* HOL4: val write_simps *)

let WBIGPAUX_write_simps = end_itlist CONJ [array_write_simp; reg_write_simp;
  dec_clock_write_simp; clock_write_simp];;

let FLOOKUP_DOMSUB = prove
 (`FLOOKUP ((f:(A,B)fmap) \\ n) m = if m = n then NONE else FLOOKUP f m`,
  REWRITE_TAC[DOMSUB_FLOOKUP_THM] THEN MESON_TAC[]);;
let _ = cake_add_simps [FLOOKUP_DOMSUB];;


(* HOL4: sort_lemma, sort_thms, sort_writes_conv and remove_write_from_init *)
(* (ML) are replaced by the derivation tools below                          *)

let reg_read_lemma1 = prove
 (`!v n. FLOOKUP (word_bignumProof_state_regs (s:(A)word_bignumProof_state)) n = SOME v
         ==> (n IN FDOM (word_bignumProof_state_regs s) <=> T)`,
  SIMP_TAC[FLOOKUP_DEF] THEN MESON_TAC[option_DISTINCT]);;

let reg_read_lemma2 = prove
 (`!v n. FLOOKUP (word_bignumProof_state_regs (s:(A)word_bignumProof_state)) n = SOME v
         ==> FAPPLY (word_bignumProof_state_regs s) n = v`,
  REWRITE_TAC[FLOOKUP_DEF] THEN MESON_TAC[option_DISTINCT; option_INJ]);;

let array_read_lemma = prove
 (`!v n. word_bignumProof_state_arrays (s:(A)word_bignumProof_state) n = v
         ==> word_bignumProof_state_arrays s n = v`,
  REWRITE_TAC[]);;

let clock_read_lemma = prove
 (`word_bignumProof_state_clock (s:(A)word_bignumProof_state) = l
   ==> word_bignumProof_state_clock s = l`,
  REWRITE_TAC[]);;

let word_bignumProof_Corr_move_pre = prove
 (`(b ==> Corr code (s:(A)word_bignumProof_state) f p) <=> Corr code s f (b /\ p)`,
  REWRITE_TAC[word_bignumProof_Corr_def] THEN MESON_TAC[]);;

let loop_app_EQ = prove
 (`(loop_app (f:(A)word_bignumProof_state->
                 (A)word_bignumProof_state+(A)word_bignumProof_state) g x = (INR t,T) <=>
    f x = INR t /\ g x) /\
   (loop_app f g x = (INL t,T) <=>
    ?x'. f x = INL x' /\ word_bignumProof_dec_clock x' = t /\ g x /\
         ~(word_bignumProof_state_clock x' = 0))`,
  REWRITE_TAC[loop_app_def] THEN
  STRUCT_CASES_TAC (ISPEC `(f:(A)word_bignumProof_state->
                 (A)word_bignumProof_state+(A)word_bignumProof_state) x` (cases "sum")) THEN
  CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[PAIR_EQ; injectivity "sum"; distinctness "sum"] THEN MESON_TAC[]);;

let WBIGPAUX_PAIR_CASE_CONST = prove
 (`!(p:A#B) (c:C). pair_CASE p (\x y. c) = c`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN CASE_REWRITE_TAC[]);;

let true_pres = prove
 (`mc_single_mul_pre ((r0:A word),r1,r2) /\
   mc_mul_by_single2_pre (r6,r7,r8) /\
   mc_cmp3_pre (r1,r2,r3,r9,r10,r11) /\
   mc_cmp_mul2_pre (r6,r7,r8,r9,r10,r11) /\
   mc_cmp2_pre (r0,r2,r10,r11) /\
   mc_adj_cmp_pre (r0,r3,r8) /\
   mc_idiv_mod_header_pre (r6,r11) /\
   mc_iadd1_pre (r1,r2,(xs:(A word)list),ys) /\
   mc_iadd2_pre (r1,r2,r3,r4,xs,ys) /\
   mc_iadd3_pre (r1,xs,ys) /\
   mc_isub_flip_pre (r1,r2) /\
   mc_imul1_pre (r10,r11) /\
   mc_sub1_pre r6 /\ mc_cmp2_pre (r0,r2,r10,r11)`,
  REWRITE_TAC[mc_single_mul_pre_def; mc_cmp3_pre_def; mc_cmp_mul2_pre_def;
              mc_cmp2_pre_def; mc_mul_by_single2_pre_def; mc_adj_cmp_pre_def;
              mc_sub1_pre_def; mc_idiv_mod_header_pre_def; mc_iadd1_pre_def;
              mc_iadd2_pre_def; mc_iadd3_pre_def; mc_imul1_pre_def;
              mc_isub_flip_pre_def; LET_DEF; LET_END_DEF; COND_ID;
              WBIGPAUX_PAIR_CASE_CONST] THEN
  REPEAT (CHANGED_TAC (CASE_REWRITE_TAC[WBIGPAUX_PAIR_CASE_CONST; COND_ID] THEN
                       REWRITE_TAC[mc_single_mul_pre_def; LET_DEF; LET_END_DEF])));;

let single_add_word_imp_0_1 = prove
 (`single_add_word x1 x2 x3 = ((y1:A word),y2) ==> ~(y2 = word 0) ==> y2 = word 1`,
  REWRITE_TAC[single_add_word_thm; PAIR_EQ; multiword_b2w_def] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* the simulation of a tail-recursive function by a loop body: step is    *)
(* the step function of mc_tailrecLib (NAME = SHORT_TAILREC step), inp     *)
(* reads its argument from a state, W writes its result into a state      *)

let WBIGPAUX_LOOP = prove
 (`!(step:X->(X+Y)#bool) (inp:(A)word_bignumProof_state->X)
    (W:Y->(A)word_bignumProof_state->(A)word_bignumProof_state) regs body.
     (!s. regs s /\ SND (step (inp s)) ==>
          ?r. word_bignumProof_Eval NONE s body r /\
              (!y. FST (step (inp s)) = INR y ==> r = INR (W y s)) /\
              (!y. FST (step (inp s)) = INL y ==>
                   ?s2. r = INL s2 /\ ~(word_bignumProof_state_clock s2 = 0) /\
                        regs (word_bignumProof_dec_clock s2) /\
                        inp (word_bignumProof_dec_clock s2) = y /\
                        (!z. W z (word_bignumProof_dec_clock s2) = W z s)))
     ==> !s. regs s /\ SHORT_TAILREC_PRE step (inp s)
             ==> word_bignumProof_Eval NONE s (LoopBody body)
                   (INR (W (SHORT_TAILREC step (inp s)) s))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!x. SHORT_TAILREC_PRE (step:X->(X+Y)#bool) x ==>
        !s. inp s = x /\ regs s ==>
            word_bignumProof_Eval NONE s (LoopBody body)
              (INR ((W:Y->(A)word_bignumProof_state->(A)word_bignumProof_state)
                      (SHORT_TAILREC step x) s))`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC SHORT_TAILREC_PRE_INDUCT THEN
  X_GEN_TAC `x:X` THEN STRIP_TAC THEN
  X_GEN_TAC `s:(A)word_bignumProof_state` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:(A)word_bignumProof_state` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)word_bignumProof_state)+((A)word_bignumProof_state)`
    STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[SHORT_TAILREC_THM] THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `y:X` ASSUME_TAC) (X_CHOOSE_THEN `y:Y` ASSUME_TAC)
    (ISPEC `FST ((step:X->(X+Y)#bool) (inp (s:(A)word_bignumProof_state)))`
       (cases "sum")) THEN
  ASM_REWRITE_TAC[ISL; OUTL; OUTR] THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `y:X`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s2:(A)word_bignumProof_state` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC WBIGPAUX_eval_LoopBody2 THEN
    EXISTS_TAC `s2:(A)word_bignumProof_state` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:X`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WBIGPAUX_eval_LoopBody1 THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:Y`) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[]]);;

(* the same for code that is not a loop: no step continues *)

let WBIGPAUX_NONLOOP = prove
 (`!(step:X->(X+Y)#bool) (inp:(A)word_bignumProof_state->X)
    (W:Y->(A)word_bignumProof_state->(A)word_bignumProof_state) regs code.
     (!s. regs s /\ SND (step (inp s)) ==>
          ?r. word_bignumProof_Eval NONE s code r /\
              (!y. FST (step (inp s)) = INR y ==> r = INR (W y s)) /\
              (!y. ~(FST (step (inp s)) = INL y)))
     ==> !s. regs s /\ SHORT_TAILREC_PRE step (inp s)
             ==> word_bignumProof_Eval NONE s code
                   (INR (W (SHORT_TAILREC step (inp s)) s))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `s:(A)word_bignumProof_state` THEN
  ONCE_REWRITE_TAC[SHORT_TAILREC_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:(A)word_bignumProof_state`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:((A)word_bignumProof_state)+((A)word_bignumProof_state)`
    STRIP_ASSUME_TAC) THEN
  DISJ_CASES_THEN2 (X_CHOOSE_THEN `y:X` ASSUME_TAC) (X_CHOOSE_THEN `y:Y` ASSUME_TAC)
    (ISPEC `FST ((step:X->(X+Y)#bool) (inp (s:(A)word_bignumProof_state)))`
       (cases "sum")) THEN
  ASM_MESON_TAC[ISL; OUTR]);;

(* ------------------------------------------------------------------------- *)
(* reading the components of a state built by writes                         *)
(* ------------------------------------------------------------------------- *)

let WBIGPAUX_address_neqs =
  let ths = CONJUNCTS (distinctness "address") in
  ths @ map GSYM ths;;

(* the words of the deep embedding in the form of mc_multiword: the       *)
(* translation writes word_not x as x xor (0 - 1), shifts by val (word 1) *)

let WBIGPAUX_WORD_XOR_NOT = prove
 (`!x:A word. word_xor x (word_sub (word 0) (word 1)) = word_not x`,
  GEN_TAC THEN REWRITE_TAC[WORD_SUB_LZERO; WORD_NEG_1; WORD_XOR_NOT; WORD_XOR_0]);;

let WBIGPAUX_read_rules =
  [reg_write_simp; clock_write_simp; dec_clock_write_simp; array_write_simp;
   delete_vars_def; FAPPLY_FUPDATE_THM; DOMSUB_FAPPLY_THM; FDOM_FUPDATE;
   FDOM_DOMSUB; IN_INSERT; IN_DELETE; FLOOKUP_UPDATE; DOMSUB_FLOOKUP_THM;
   APPLY_UPDATE_THM; eval_exp_def; eval_exp_pre_def; eval_ri_def; eval_ri_pre_def;
   asm_word_cmp_def; WBIGPAUX_WORD_XOR_NOT; VAL_WORD_1] @ WBIGPAUX_address_neqs;;

let WBIGPAUX_read_net =
  let ths = itlist (mk_rewrites false) WBIGPAUX_read_rules [] in
  let net = itlist (net_of_thm true) ths (basic_net()) in
  net_of_conv `m:num = n` NUM_EQ_CONV (net_of_conv `m < n` NUM_LT_CONV net);;

let WBIGPAUX_READ_CONV = TOP_DEPTH_CONV (REWRITES_CONV WBIGPAUX_read_net);;

(* ------------------------------------------------------------------------- *)
(* The derivation of the Corr theorems (HOL4: derive_corr_thm and its ML     *)
(* helpers find_ret_tuple, get_array_name, add_all_writes, read_conv, ...).  *)
(* For the function NAME (HOL4 tailrec_define: NAME = SHORT_TAILREC step,    *)
(* NAME_pre = SHORT_TAILREC_PRE step) with deep embedding NAME_code, the     *)
(* theorem NAME_corr_thm is HOL4's:                                          *)
(*   Corr NAME_code s                                                        *)
(*     (INR (match NAME inp with out -> delete_vars dels (writes out s)))    *)
(*     (regs_ok s /\ NAME_pre inp)                                          *)
(* where inp reads the arguments from s (rN from register N, xs ys zs from  *)
(* the arrays In1 In2 Out, the num argument from the clock, minus 1 for a   *)
(* loop), writes writes the results back, dels are the registers that the   *)
(* code deletes before it returns, regs_ok says that the argument registers  *)
(* are present; for a loop the precondition is (regs_ok s /\ NAME_pre inp) /\ *)
(* clock <> 0.  The proof is not HOL4's: the code is executed symbolically   *)
(* (WBIGPAUX_EXEC_TAC) along every path of the step function, and the        *)
(* states are compared componentwise (WBIGPAUX_STATE_EQ_TAC); a loop uses    *)
(* WBIGPAUX_LOOP.                                                            *)
(* ------------------------------------------------------------------------- *)

let WBIGPAUX_state_ty = `:(A)word_bignumProof_state`;;

(* the register of a variable rN, the array of xs ys zs *)

let WBIGPAUX_reg_num v = WORDP3AUX_dest_reg v;;

let WBIGPAUX_array_of v =
  let n,_ = dest_var v in
  match WORDP3AUX_base_name n with
    "xs" -> `In1` | "ys" -> `In2` | "zs" -> `Out`
  | _ -> failwith "WBIGPAUX_array_of";;

let WBIGPAUX_tuple_vars tm =
  let rec f t = try let x,y = dest_pair t in x :: f y with Failure _ -> [t] in
  f tm;;

(* the read of the argument v from the state s *)

let WBIGPAUX_read s v =
  if type_of v = `:num` then
    mk_icomb(`word_bignumProof_state_clock:(A)word_bignumProof_state->num`,s) else
  try let n = WBIGPAUX_reg_num v in
      mk_icomb(mk_icomb(`FAPPLY:(num,A word)fmap->num->A word`,
                        mk_icomb(`word_bignumProof_state_regs:
                                    (A)word_bignumProof_state->(num,A word)fmap`,s)),n)
  with Failure _ ->
  mk_icomb(mk_icomb(`word_bignumProof_state_arrays:
                       (A)word_bignumProof_state->address->(A word)list`,s),
           WBIGPAUX_array_of v);;

(* the write of the result v (a variable of the pattern) into the state t *)

let WBIGPAUX_write v t =
  if type_of v = `:num` then
    mk_icomb(mk_icomb(`clock_write:num->(A)word_bignumProof_state->
                                    (A)word_bignumProof_state`,v),t) else
  try let n = WBIGPAUX_reg_num v in
      list_mk_icomb "reg_write" [n; mk_icomb(`SOME:A word->(A word)option`,v); t]
  with Failure _ ->
  list_mk_icomb "array_write" [WBIGPAUX_array_of v; v; t];;

(* pair_CASE e (\a b. ...) for the tuple pattern pat (right nested) *)

let rec WBIGPAUX_mk_pair_case avoid e pat body =
  try let a,rest = dest_pair pat in
      if is_var rest then
        mk_icomb(mk_icomb(mk_const("pair_CASE",[]),e),mk_abs(a,mk_abs(rest,body)))
      else
        let p = variant (avoid @ frees pat @ frees body) (mk_var("p",type_of rest)) in
        mk_icomb(mk_icomb(mk_const("pair_CASE",[]),e),
                 mk_abs(a,mk_abs(p,WBIGPAUX_mk_pair_case (p::avoid) p rest body)))
  with Failure _ -> mk_comb(mk_abs(pat,body),e);;

(* HOL4 find_ret_tuple: the result pattern of an equation NAME_def, read   *)
(* from the equations that the translation uses (WORDP3AUX_defs: their      *)
(* tuple lets are kept, so the names are the source's)                      *)

let rec WBIGPAUX_find_ret_tuple tm =
  if is_var tm || is_pair tm then tm
  else if is_let tm || WORDP3AUX_is_pair_case tm then
    WBIGPAUX_find_ret_tuple (snd (WORDP3AUX_dest_let tm))
  else if is_cond tm then
    let _,(x,y) = dest_cond tm in
    (try WBIGPAUX_find_ret_tuple x with Failure _ -> WBIGPAUX_find_ret_tuple y)
  else failwith "WBIGPAUX_find_ret_tuple";;

let WBIGPAUX_find_ret name =
  let def = assoc (name ^ "_def") (!WORDP3AUX_defs) in
  WBIGPAUX_find_ret_tuple (rhs (concl (SPEC_ALL def)));;

(* the registers deleted before a return *)

let WBIGPAUX_ret_dels deep =
  try let t = find_term (fun t ->
        try let f,args = strip_comb t in
            fst (dest_const f) = "word_bignum_Seq" &&
            (match args with
               [d; k] -> fst (dest_const (rator d)) = "Delete" &&
                         fst (dest_const k) = "word_bignum_Skip"
             | _ -> false)
        with Failure _ -> false) deep in
      rand (rand (rator t))
  with Failure _ -> `[]:num list`;;

(* ------------------------------------------------------------------------- *)
(* comparing two states built by writes from the same state                  *)
(* ------------------------------------------------------------------------- *)

let WBIGPAUX_VALUE_EQ_TAC : tactic =
  REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  (fun (asl,w as g) ->
     if w = `T` then ALL_TAC g else
     try (ASM_REWRITE_TAC[] THEN NO_TAC) g with Failure _ ->
     try (REWRITE_TAC[FLOOKUP_DEF] THEN ASM_REWRITE_TAC[] THEN NO_TAC) g
     with Failure _ ->
       (print_string "WBIGPAUX_VALUE_EQ_TAC: cannot prove\n";
        print_term w; print_newline(); failwith "WBIGPAUX_VALUE_EQ_TAC"));;

let rec WBIGPAUX_KEY_TAC (k:term) : tactic = fun (asl,w as g) ->
  let nums = setify (mapfilter (fun t -> let l,r = dest_eq t in
                         if l = k && is_numeral r then r
                         else if r = k && is_numeral l then l else fail())
                       (find_terms is_eq w)) in
  match nums with
    [] -> WBIGPAUX_VALUE_EQ_TAC g
  | n::_ ->
      (ASM_CASES_TAC (mk_eq(k,n)) THENL
        [POP_ASSUM SUBST1_TAC THEN CONV_TAC WBIGPAUX_READ_CONV THEN
         WBIGPAUX_VALUE_EQ_TAC;
         POP_ASSUM(fun th -> REWRITE_TAC[th; GSYM th]) THEN
         WBIGPAUX_KEY_TAC k]) g;;

let WBIGPAUX_STATE_EQ_TAC : tactic =
  REWRITE_TAC[word_bignumProof_state_component_equality] THEN
  REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC I [fmap_eq_flookup] THEN X_GEN_TAC `wbigp_k:num` THEN
    CONV_TAC WBIGPAUX_READ_CONV THEN WBIGPAUX_KEY_TAC `wbigp_k:num`;
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `wbigp_a:address` THEN
    STRUCT_CASES_TAC (ISPEC `wbigp_a:address` (cases "address")) THEN
    CONV_TAC WBIGPAUX_READ_CONV THEN WBIGPAUX_VALUE_EQ_TAC;
    CONV_TAC WBIGPAUX_READ_CONV THEN WBIGPAUX_VALUE_EQ_TAC];;

(* ------------------------------------------------------------------------- *)
(* symbolic execution                                                        *)
(* ------------------------------------------------------------------------- *)

let WBIGPAUX_FORALL_UNWIND = prove
 (`(!(P:A->bool) a. (!x. a = x ==> P x) <=> P a) /\
   (!(P:A->bool) a. (!x. x = a ==> P x) <=> P a)`,
  MESON_TAC[]);;

let WBIGPAUX_SINGLE_SUB_WORD_0_1 = prove
 (`single_sub_word x1 x2 x3 = ((y1:A word),y2) ==> ~(y2 = word 0) ==> y2 = word 1`,
  REWRITE_TAC[single_sub_word_thm; PAIR_EQ; multiword_b2w_def] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let WBIGPAUX_VAL_WORD_1_LT = prove
 (`val (word 1:A word) < 32`,
  REWRITE_TAC[VAL_WORD_1] THEN ARITH_TAC);;

(* an equation assumption is kept as (a = b) <=> T, so that rewriting with  *)
(* the assumptions does not substitute it                                   *)

let WBIGPAUX_protect th =
  if is_eq (concl th) && type_of (lhand (concl th)) <> bool_ty
  then EQT_INTRO th else th;;

let WBIGPAUX_labelled lab asl =
  map snd (filter (fun (l,_) -> l = lab) asl);;

(* the facts that the assumptions give for the side conditions: the carries *)
(* of single_add_word and single_sub_word are 0 or 1                          *)

let WBIGPAUX_side_facts asl =
  let sp = WBIGPAUX_labelled "wbigp_split" asl in
  mapfilter (fun th -> try MATCH_MP single_add_word_imp_0_1 th with Failure _ ->
                       MATCH_MP WBIGPAUX_SINGLE_SUB_WORD_0_1 th) sp;;

(* HOL4 true_pres: the preconditions that are always true *)

let WBIGPAUX_true_pres = map GEN_ALL (CONJUNCTS true_pres);;

let WBIGPAUX_SIDE_TAC : tactic = fun (asl,w as g) ->
  (CONV_TAC WBIGPAUX_READ_CONV THEN
   REWRITE_TAC(WBIGPAUX_VAL_WORD_1_LT :: WBIGPAUX_true_pres) THEN
   ASM_REWRITE_TAC(WBIGPAUX_side_facts asl) THEN NO_TAC) g;;

let WBIGPAUX_prove_side asl tm =
  try TAC_PROOF((asl,tm),WBIGPAUX_SIDE_TAC) with Failure _ ->
    (print_string "WBIGPAUX: side condition not proved:\n";
     print_term tm; print_newline();
     print_term (rand(concl(WBIGPAUX_READ_CONV tm))); print_newline();
     failwith "WBIGPAUX_prove_side");;

(* normalise a state: compute the values written, apply the splits *)

let WBIGPAUX_VALUE_CONV asl =
  let sp = WBIGPAUX_labelled "wbigp_split" asl in
  WBIGPAUX_READ_CONV THENC
  REWRITE_CONV (sp @ [case_def "prod"; FST; SND]) THENC
  WBIGPAUX_READ_CONV;;

(* the Corr theorems of the instructions *)

let WBIGPAUX_instr_corrs =
  [Corr_Assign; Corr_Delete; Corr_Load; Corr_Store; Corr_Swap; Corr_Add;
   Corr_Sub; Corr_Mul; Corr_Div];;

(* HOL4: val all_corrs; the Corr theorems derived so far *)

let WBIGPAUX_all_corrs = ref ([]:thm list);;

let WBIGPAUX_corr_code th =
  let c = concl (SPEC_ALL th) in
  rand (rator (rator (rator c)));;

(* |- Eval NONE s c1 (INR s1) for the first instruction c1 *)

let WBIGPAUX_STEP asl s c1 =
  let lemma = find (fun th -> can (term_match [] (WBIGPAUX_corr_code th)) c1)
                (WBIGPAUX_instr_corrs @ !WBIGPAUX_all_corrs) in
  let th0 = SPEC_ALL lemma in
  let i = term_match [] (WBIGPAUX_corr_code th0) c1 in
  let th1 = INSTANTIATE i th0 in
  let sv = rand (rator (rator (concl th1))) in
  let th2 = INST [s,sv] th1 in
  let th3 = REWRITE_RULE[word_bignumProof_Corr_def] th2 in
  let th4 = if is_imp (concl th3) then
              MP th3 (WBIGPAUX_prove_side asl (lhand (concl th3)))
            else th3 in
  CONV_RULE (RAND_CONV (RAND_CONV (WBIGPAUX_VALUE_CONV asl))) th4;;

(* decide a guard with the assumptions: |- g <=> T or |- g <=> F *)

let WBIGPAUX_decide asl g =
  let th = WBIGPAUX_READ_CONV g in
  let b = rand (concl th) in
  if b = `T` || b = `F` then th else
  try TRANS th (TAC_PROOF((asl,mk_eq(b,`T`)),ASM_REWRITE_TAC[] THEN NO_TAC))
  with Failure _ ->
  try TRANS th (TAC_PROOF((asl,mk_eq(b,`F`)),ASM_REWRITE_TAC[] THEN NO_TAC))
  with Failure _ ->
    (print_string "WBIGPAUX: guard not decided:\n"; print_term b; print_newline();
     failwith "WBIGPAUX_decide");;

let WBIGPAUX_NONE = `NONE:((A)mini)option`;;

(* |- Eval NONE s code res, along the path that the assumptions decide *)

let rec WBIGPAUX_EXEC asl s code =
  let f,args = strip_comb code in
  match fst (dest_const f),args with
    "word_bignum_Seq",[c1;c2] ->
      let th1 = WBIGPAUX_STEP asl s c1 in
      let s1 = rand (rand (concl th1)) in
      let th2 = WBIGPAUX_EXEC asl s1 c2 in
      MATCH_MP WBIGPAUX_eval_Seq (CONJ th1 th2)
  | "word_bignum_If",[c;r;ri;p1;p2] ->
      let th0 = ISPECL [WBIGPAUX_NONE; s; c; r; ri; p1; p2] WBIGPAUX_eval_If in
      let ant = lhand (concl (SPEC_ALL th0)) in
      let fdom,rest = dest_conj ant in
      let ripre,evif = dest_conj rest in
      let g = rand (rator (rator (rand (rator evif)))) in
      let gth = WBIGPAUX_decide asl g in
      let p = if rand (concl gth) = `T` then p1 else p2 in
      let thp = WBIGPAUX_EXEC asl s p in
      let res = rand (concl thp) in
      let evif' = vsubst [res,rand evif] evif in
      let thif = TAC_PROOF((asl,evif'),REWRITE_TAC[gth] THEN ACCEPT_TAC thp) in
      let th1 = WBIGPAUX_prove_side asl fdom in
      let th2 = WBIGPAUX_prove_side asl ripre in
      MP (SPEC res th0) (CONJ th1 (CONJ th2 thif))
  | "word_bignum_Skip",[] -> ISPECL [WBIGPAUX_NONE; s] WBIGPAUX_eval_Skip
  | "word_bignum_Continue",[] -> ISPECL [WBIGPAUX_NONE; s] WBIGPAUX_eval_Continue
  | _ -> failwith "WBIGPAUX_EXEC: unexpected code";;

(* ------------------------------------------------------------------------- *)
(* the obligations of WBIGPAUX_LOOP and WBIGPAUX_NONLOOP                     *)
(* ------------------------------------------------------------------------- *)

let WBIGPAUX_sum_rws =
  [injectivity "sum"; distinctness "sum"; GSYM (distinctness "sum")];;

(* split the outermost condition or pair case of the step function *)

let WBIGPAUX_SPLIT_TAC : tactic = fun (asl,w as gl) ->
  let fvs = itlist (union o frees o concl o snd) asl (frees w) in
  let avoid = itlist (union o thm_frees o snd) asl (frees w) in
  match lbig_find_split fvs w with
    Some(true,b) ->
      (ASM_CASES_TAC b THENL
        [POP_ASSUM(fun th -> REWRITE_TAC[EQT_INTRO th] THEN
                             LABEL_TAC "wbigp_cond" (WBIGPAUX_protect th));
         POP_ASSUM(fun th -> REWRITE_TAC[EQF_INTRO th] THEN
                             LABEL_TAC "wbigp_cond" th)]) gl
  | Some(false,e) ->
      let pc = find_term (fun t -> WORDP3AUX_is_pair_case t && rand (rator t) = e) w in
      let a,b0 = dest_abs (rand pc) in
      let b,_ = dest_abs b0 in
      let v1 = variant avoid a in
      let v2 = variant (v1::avoid) b in
      (MP_TAC(ISPEC e PAIR_SURJECTIVE) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
       MAP_EVERY X_GEN_TAC [v1;v2] THEN
       DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN
                            (if is_var e then ALL_TAC
                             else LABEL_TAC "wbigp_split" th)) THEN
       CASE_REWRITE_TAC[]) gl
  | None -> failwith "WBIGPAUX_SPLIT_TAC: nothing to split";;

let WBIGPAUX_Q_TAC : tactic =
  REWRITE_TAC(WBIGPAUX_sum_rws @ [UNWIND_THM1; UNWIND_THM2]) THEN
  REPEAT CONJ_TAC THEN
  (fun (asl,w as g) ->
     if is_forall w then
       (REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN CASE_REWRITE_TAC[] THEN
        WBIGPAUX_STATE_EQ_TAC) g
     else if is_eq w && type_of (lhs w) = WBIGPAUX_state_ty then
       WBIGPAUX_STATE_EQ_TAC g
     else (CONV_TAC WBIGPAUX_READ_CONV THEN REWRITE_TAC[PAIR_EQ] THEN
           REWRITE_TAC(WBIGPAUX_VAL_WORD_1_LT :: WBIGPAUX_true_pres) THEN
           ASM_REWRITE_TAC(WBIGPAUX_side_facts asl) THEN NO_TAC) g);;

let WBIGPAUX_LEAF_TAC : tactic =
  REWRITE_TAC([FST; SND; WBIGPAUX_FORALL_UNWIND] @ WBIGPAUX_sum_rws) THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun c -> LABEL_TAC "wbigp_pre" (WBIGPAUX_protect c))
                         (CONJUNCTS th)) THEN
  CASE_REWRITE_TAC[] THEN
  (fun (asl,w as g) ->
     let r,bod = dest_exists w in
     let ev,q = dest_conj bod in
     let _,args = strip_comb ev in
     let s = el 1 args and code = el 2 args in
     let th = WBIGPAUX_EXEC asl s code in
     let res = rand (concl th) in
     (EXISTS_TAC res THEN CONJ_TAC THENL [ACCEPT_TAC th; WBIGPAUX_Q_TAC]) g);;

let WBIGPAUX_H_TAC : tactic =
  X_GEN_TAC `s:(A)word_bignumProof_state` THEN
  CONV_TAC (TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REPEAT WBIGPAUX_SPLIT_TAC THEN
  WBIGPAUX_LEAF_TAC;;

(* ------------------------------------------------------------------------- *)
(* the Corr theorem of a deep embedding                                      *)
(* ------------------------------------------------------------------------- *)

let WBIGPAUX_s = `s:(A)word_bignumProof_state`;;

let WBIGPAUX_find_def c =
  find (fun th -> try fst (dest_const (lhs (concl th))) = c with Failure _ -> false)
       (definitions());;

let WBIGPAUX_mk_tuple l = end_itlist (fun a b -> mk_pair(a,b)) l;;

(* the parts of the derivation for the code definition |- NAME_code = deep *)

let WBIGPAUX_parts code_def =
  let cconst = lhs (concl code_def) and deep = rhs (concl code_def) in
  let cname = fst (dest_const cconst) in
  let name = String.sub cname 0 (String.length cname - 5) in
  let def_thm = INST_TYPE [`:A`,`:N`] (WBIGPAUX_find_def name) in
  let pre_thm = INST_TYPE [`:A`,`:N`] (WBIGPAUX_find_def (name ^ "_pre")) in
  let step = rand (rhs (concl def_thm)) in
  let pat,bod = dest_gabs step in
  let out = WBIGPAUX_find_ret name in
  let is_loop = fst (dest_const (fst (strip_comb deep))) = "word_bignum_Loop" in
  let body = if is_loop then rand deep else deep in
  let dels = WBIGPAUX_ret_dels deep in
  let s = WBIGPAUX_s in
  let ins = WBIGPAUX_tuple_vars pat in
  let base v = let n,ty = dest_var v in mk_var(WORDP3AUX_base_name n,ty) in
  let outs = map base (WBIGPAUX_tuple_vars out) in
  let out = WBIGPAUX_mk_tuple outs in
  let reads = map (WBIGPAUX_read s) ins in
  let inp = mk_abs(s,WBIGPAUX_mk_tuple reads) in
  let reads' = map (fun t -> if type_of t = `:num`
                             then mk_binop `(-):num->num->num` t `1` else t) reads in
  let inp' = mk_abs(s,WBIGPAUX_mk_tuple reads') in
  let writes = itlist WBIGPAUX_write outs s in
  let wbody = list_mk_icomb "delete_vars" [dels; writes] in
  let y = variant (s::outs) (mk_var("y",type_of out)) in
  let w = mk_abs(y,mk_abs(s,WBIGPAUX_mk_pair_case [s] y out wbody)) in
  let regl = mapfilter (fun v -> let n = WBIGPAUX_reg_num v in
               mk_comb(mk_comb(`(IN):num->(num->bool)->bool`,n),
                 mk_icomb(`FDOM:(num,A word)fmap->num->bool`,
                   mk_icomb(`word_bignumProof_state_regs:
                              (A)word_bignumProof_state->(num,A word)fmap`,s)))) ins in
  let regs = mk_abs(s,if regl = [] then `T` else list_mk_conj regl) in
  cconst,code_def,name,def_thm,pre_thm,step,is_loop,deep,body,inp,inp',w,regs,regl;;

(* the statement of NAME_corr_thm *)

let WBIGPAUX_corr_statement code_def =
  let cconst,_,_,def_thm,pre_thm,_,is_loop,_,_,inp,inp',w,_,regl =
    WBIGPAUX_parts code_def in
  let s = WBIGPAUX_s in
  let f = lhs (concl def_thm) and fp = lhs (concl pre_thm) in
  let i = if is_loop then inp' else inp in
  let arg = rand (concl (BETA_CONV (mk_comb(i,s)))) in
  let post = rand (concl ((RATOR_CONV BETA_CONV THENC BETA_CONV)
                            (list_mk_comb(w,[mk_comb(f,arg); s])))) in
  let pre0 = mk_comb(fp,arg) in
  let pre1 = list_mk_conj (regl @ [pre0]) in
  let pre = if is_loop then
              mk_conj(pre1,`~(word_bignumProof_state_clock (s:(A)word_bignumProof_state) = 0)`)
            else pre1 in
  mk_forall(s,list_mk_icomb "Corr"
    [cconst; s; mk_icomb(`INR:(A)word_bignumProof_state->
                              (A)word_bignumProof_state+(A)word_bignumProof_state`,post);
     pre]);;

(* the obligation H of WBIGPAUX_LOOP / WBIGPAUX_NONLOOP and the lemma *)

let WBIGPAUX_obligation code_def =
  let _,_,_,_,_,step,is_loop,_,body,inp,_,w,regs,_ = WBIGPAUX_parts code_def in
  let lemma = ISPECL [step; inp; w; regs; body]
                (if is_loop then WBIGPAUX_LOOP else WBIGPAUX_NONLOOP) in
  lhand (concl lemma),lemma;;

let WBIGPAUX_BETA t = rand (concl (TOP_DEPTH_CONV BETA_CONV t));;

(* HOL4: derive_corr_thm; NAME_corr_thm is also added to WBIGPAUX_all_corrs *)

let WBIGPAUX_derive_corr code_def =
  let cconst,_,name,def_thm,pre_thm,step,is_loop,deep,body,inp,inp',w,regs,regl =
    WBIGPAUX_parts code_def in
  let h,lemma = WBIGPAUX_obligation code_def in
  let hth = prove(h,WBIGPAUX_H_TAC) in
  let lth = MP lemma hth in
  let stmt = WBIGPAUX_corr_statement code_def in
  let s = WBIGPAUX_s in
  let tac =
    if not is_loop then
      GEN_TAC THEN REWRITE_TAC[word_bignumProof_Corr_def; code_def] THEN
      REWRITE_TAC[def_thm; pre_thm] THEN DISCH_TAC THEN
      MP_TAC (SPEC s lth) THEN CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]
    else
      let vs = rand (rator deep) in
      let s1 = list_mk_icomb "delete_vars"
                 [vs; mk_icomb(`word_bignumProof_dec_clock:(A)word_bignumProof_state->
                                (A)word_bignumProof_state`,s)] in
      let inp_eq = prove(mk_eq(WBIGPAUX_BETA (mk_comb(inp,s1)),
                               WBIGPAUX_BETA (mk_comb(inp',s))),
                         CONV_TAC WBIGPAUX_READ_CONV THEN REWRITE_TAC[]) in
      let z = mk_var("z",fst (dest_fun_ty (type_of w))) in
      let w_eq = prove(mk_forall(z,mk_eq(WBIGPAUX_BETA (list_mk_comb(w,[z;s1])),
                                         WBIGPAUX_BETA (list_mk_comb(w,[z;s])))),
                       REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
                       CASE_REWRITE_TAC[] THEN WBIGPAUX_STATE_EQ_TAC) in
      GEN_TAC THEN REWRITE_TAC[word_bignumProof_Corr_def; code_def] THEN
      REWRITE_TAC[def_thm; pre_thm] THEN STRIP_TAC THEN
      MATCH_MP_TAC WBIGPAUX_eval_Loop THEN ASM_REWRITE_TAC[] THEN
      MP_TAC (SPEC s1 lth) THEN CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[inp_eq; w_eq] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC WBIGPAUX_READ_CONV THEN ASM_REWRITE_TAC[] in
  let th = prove(stmt,tac) in
  WBIGPAUX_all_corrs := th :: !WBIGPAUX_all_corrs;
  th;;


(* the Corr theorems of all deep embeddings, in the order of their        *)
(* definitions (HOL4: first (not o can derive_corr_thm) (all_code_defs |>  *)
(* CONJUNCTS |> rev)); the examples mc_fac_X are not derived, as in HOL4  *)

let mc_cmp_corr_thm = WBIGPAUX_derive_corr mc_cmp_code_def;;
let mc_compare_corr_thm = WBIGPAUX_derive_corr mc_compare_code_def;;
let mc_mul_zero_corr_thm = WBIGPAUX_derive_corr mc_mul_zero_code_def;;
let mc_copy_over_corr_thm = WBIGPAUX_derive_corr mc_copy_over_code_def;;
let mc_div0_corr_thm = WBIGPAUX_derive_corr mc_div0_code_def;;
let mc_single_div_corr_thm = WBIGPAUX_derive_corr mc_single_div_code_def;;
let mc_simple_div_corr_thm = WBIGPAUX_derive_corr mc_simple_div_code_def;;
let mc_div1_corr_thm = WBIGPAUX_derive_corr mc_div1_code_def;;
let mc_calc_d_corr_thm = WBIGPAUX_derive_corr mc_calc_d_code_def;;
let mc_single_mul_add_corr_thm = WBIGPAUX_derive_corr mc_single_mul_add_code_def;;
let mc_mul_by_single_corr_thm = WBIGPAUX_derive_corr mc_mul_by_single_code_def;;
let mc_single_mul_corr_thm = WBIGPAUX_derive_corr mc_single_mul_code_def;;
let mc_top_two_corr_thm = WBIGPAUX_derive_corr mc_top_two_code_def;;
let mc_div_r1_corr_thm = WBIGPAUX_derive_corr mc_div_r1_code_def;;
let mc_mul_by_single2_corr_thm = WBIGPAUX_derive_corr mc_mul_by_single2_code_def;;
let mc_cmp3_corr_thm = WBIGPAUX_derive_corr mc_cmp3_code_def;;
let mc_cmp_mul2_corr_thm = WBIGPAUX_derive_corr mc_cmp_mul2_code_def;;
let mc_sub1_corr_thm = WBIGPAUX_derive_corr mc_sub1_code_def;;
let mc_cmp2_corr_thm = WBIGPAUX_derive_corr mc_cmp2_code_def;;
let mc_div_test_corr_thm = WBIGPAUX_derive_corr mc_div_test_code_def;;
let mc_div_guess_corr_thm = WBIGPAUX_derive_corr mc_div_guess_code_def;;
let mc_adj_cmp_corr_thm = WBIGPAUX_derive_corr mc_adj_cmp_code_def;;
let mc_adjust_aux_corr_thm = WBIGPAUX_derive_corr mc_adjust_aux_code_def;;
let mc_div_adjust_corr_thm = WBIGPAUX_derive_corr mc_div_adjust_code_def;;
let mc_div_sub_corr_thm = WBIGPAUX_derive_corr mc_div_sub_code_def;;
let mc_div_sub_loop_corr_thm = WBIGPAUX_derive_corr mc_div_sub_loop_code_def;;
let mc_div_loop_corr_thm = WBIGPAUX_derive_corr mc_div_loop_code_def;;
let mc_simple_div1_corr_thm = WBIGPAUX_derive_corr mc_simple_div1_code_def;;
let mc_fix_corr_thm = WBIGPAUX_derive_corr mc_fix_code_def;;
let mc_copy_down_corr_thm = WBIGPAUX_derive_corr mc_copy_down_code_def;;
let mc_div2_corr_thm = WBIGPAUX_derive_corr mc_div2_code_def;;
let mc_div3_corr_thm = WBIGPAUX_derive_corr mc_div3_code_def;;
let mc_div_corr_thm = WBIGPAUX_derive_corr mc_div_code_def;;
let mc_add1_corr_thm = WBIGPAUX_derive_corr mc_add1_code_def;;
let mc_add1_call_corr_thm = WBIGPAUX_derive_corr mc_add1_call_code_def;;
let mc_div_sub_aux1_corr_thm = WBIGPAUX_derive_corr mc_div_sub_aux1_code_def;;
let mc_div_sub_aux_corr_thm = WBIGPAUX_derive_corr mc_div_sub_aux_code_def;;
let mc_div_sub1_corr_thm = WBIGPAUX_derive_corr mc_div_sub1_code_def;;
let mc_div_sub_call_corr_thm = WBIGPAUX_derive_corr mc_div_sub_call_code_def;;
let mc_idiv_mod_header_corr_thm = WBIGPAUX_derive_corr mc_idiv_mod_header_code_def;;
let mc_idiv0_corr_thm = WBIGPAUX_derive_corr mc_idiv0_code_def;;
let mc_idiv_corr_thm = WBIGPAUX_derive_corr mc_idiv_code_def;;
let mc_iadd1_corr_thm = WBIGPAUX_derive_corr mc_iadd1_code_def;;
let mc_add_loop1_corr_thm = WBIGPAUX_derive_corr mc_add_loop1_code_def;;
let mc_add_loop2_corr_thm = WBIGPAUX_derive_corr mc_add_loop2_code_def;;
let mc_add_loop_corr_thm = WBIGPAUX_derive_corr mc_add_loop_code_def;;
let mc_add_corr_thm = WBIGPAUX_derive_corr mc_add_code_def;;
let mc_iadd3_corr_thm = WBIGPAUX_derive_corr mc_iadd3_code_def;;
let mc_iadd2_corr_thm = WBIGPAUX_derive_corr mc_iadd2_code_def;;
let mc_sub_loop1_corr_thm = WBIGPAUX_derive_corr mc_sub_loop1_code_def;;
let mc_sub_loop2_corr_thm = WBIGPAUX_derive_corr mc_sub_loop2_code_def;;
let mc_sub_loop_corr_thm = WBIGPAUX_derive_corr mc_sub_loop_code_def;;
let mc_sub_corr_thm = WBIGPAUX_derive_corr mc_sub_code_def;;
let mc_iadd_corr_thm = WBIGPAUX_derive_corr mc_iadd_code_def;;
let mc_imul1_corr_thm = WBIGPAUX_derive_corr mc_imul1_code_def;;
let mc_mul_pass_corr_thm = WBIGPAUX_derive_corr mc_mul_pass_code_def;;
let mc_mul_corr_thm = WBIGPAUX_derive_corr mc_mul_code_def;;
let mc_imul_corr_thm = WBIGPAUX_derive_corr mc_imul_code_def;;
let mc_isub_flip_corr_thm = WBIGPAUX_derive_corr mc_isub_flip_code_def;;
let mc_iop_corr_thm = WBIGPAUX_derive_corr mc_iop_code_def;;

(* ------------------------------------------------------------------------- *)
(* connecting all the theorems                                               *)
(* ------------------------------------------------------------------------- *)

let i2mw_NOT_NIL = prove
 (`!i2:int. ~(SND (i2mw i2:bool#(A word)list) = []) <=> ~(i2 = &0)`,
  GEN_TAC THEN REWRITE_TAC[i2mw_def; SND; n2mw_NIL] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS; INT_ABS_ZERO]);;

let mw_ok_SND_i2mw = prove
 (`!fg:int. mw_ok (SND (i2mw fg:bool#(A word)list))`,
  REWRITE_TAC[i2mw_def; SND; mw_ok_n2mw]);;

let code_subset_refl = prove
 (`!cs:A#(B#C)list. code_subset cs cs`,
  REWRITE_TAC[FORALL_PAIR_THM; code_subset_def]);;

(* syntax_ok of the generated code (HOL4: EVAL ``syntax_ok mc_iop_code``):  *)
(* syntax_ok_aux of each code constant, in the order of the definitions     *)

let WBIGPAUX_syntax_ok_thms = ref ([]:thm list);;

let WBIGPAUX_syntax_ok_code def =
  let c = lhs(concl(SPEC_ALL def)) in
  let gl = mk_icomb(`syntax_ok_aux:(A)mini->bool`,c) in
  let th = prove(gl,
    REWRITE_TAC(def :: syntax_ok_aux_def :: !WBIGPAUX_syntax_ok_thms) THEN
    REWRITE_TAC[exp_ok_def] THEN CASE_REWRITE_TAC[] THEN
    REWRITE_TAC[injectivity "reg_imm"; distinctness "reg_imm"; FORALL_UNWIND_THM1;
                FORALL_UNWIND_THM2; ALL; ALL_DISTINCT; MEM] THEN
    CONV_TAC NUM_REDUCE_CONV) in
  WBIGPAUX_syntax_ok_thms := th :: !WBIGPAUX_syntax_ok_thms; th;;

let WBIGPAUX_syntax_ok_codes = map WBIGPAUX_syntax_ok_code
  [mc_cmp_code_def; mc_compare_code_def; mc_mul_zero_code_def;
   mc_copy_over_code_def; mc_div0_code_def; mc_single_div_code_def;
   mc_simple_div_code_def; mc_div1_code_def; mc_calc_d_code_def;
   mc_single_mul_add_code_def; mc_mul_by_single_code_def; mc_single_mul_code_def;
   mc_top_two_code_def; mc_div_r1_code_def; mc_mul_by_single2_code_def;
   mc_cmp3_code_def; mc_cmp_mul2_code_def; mc_sub1_code_def;
   mc_cmp2_code_def; mc_div_test_code_def; mc_div_guess_code_def;
   mc_adj_cmp_code_def; mc_adjust_aux_code_def; mc_div_adjust_code_def;
   mc_div_sub_code_def; mc_div_sub_loop_code_def; mc_div_loop_code_def;
   mc_simple_div1_code_def; mc_fix_code_def; mc_copy_down_code_def;
   mc_div2_code_def; mc_div3_code_def; mc_div_code_def;
   mc_add1_code_def; mc_add1_call_code_def; mc_div_sub_aux1_code_def;
   mc_div_sub_aux_code_def; mc_div_sub1_code_def; mc_div_sub_call_code_def;
   mc_idiv_mod_header_code_def; mc_idiv0_code_def; mc_idiv_code_def;
   mc_iadd1_code_def; mc_add_loop1_code_def; mc_add_loop2_code_def;
   mc_add_loop_code_def; mc_add_code_def; mc_iadd3_code_def;
   mc_iadd2_code_def; mc_sub_loop1_code_def; mc_sub_loop2_code_def;
   mc_sub_loop_code_def; mc_sub_code_def; mc_iadd_code_def;
   mc_imul1_code_def; mc_mul_pass_code_def; mc_mul_code_def;
   mc_imul_code_def; mc_isub_flip_code_def; mc_iop_code_def];;

let WBIGPAUX_syntax_ok_not_LoopBody = prove
 (`!p:(A)mini. (!b. ~(p = LoopBody b)) ==>
               (word_bignumProof_syntax_ok p <=> syntax_ok_aux p)`,
  GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `p:(A)mini` (cases "mini")) THEN
  REWRITE_TAC[word_bignumProof_syntax_ok_def; distinctness "mini"; injectivity "mini"] THEN
  MESON_TAC[]);;

let evaluate_mc_iop = prove
 (`!i1 i2 l' (frame:((A word#(A)word_loc)->bool)->bool) (zs:(A word)list)
    (t:(A,C,FFI)wl_state) ret_val n l iop p1 l1 i' cs.
     word_bignum_compile n l' 1 (n + 1,[]) mc_iop_code = (p1,l1,i',cs) /\
     word_bignumProof_state_rel
       (word_bignumProof_state_REC
          (((FEMPTY |+ (0,mc_header (i2mw i1))) |+ (1,mc_header (i2mw i2))) |+
           (3,int_op_rep iop))
          ((In1 =+ SND (i2mw i1)) ((In2 =+ SND (i2mw i2)) (K zs))) l)
       t cs t frame /\
     wl_get_var 0 t = SOME ret_val /\ good_dimindex (:A) /\ 3 < dimindex (:A) /\
     (mc_header (i2mw i1:bool#(A word)list) = word 0 <=>
      SND (i2mw i1:bool#(A word)list) = []) /\
     (mc_header (i2mw i2:bool#(A word)list) = word 0 <=>
      SND (i2mw i2:bool#(A word)list) = []) /\
     LENGTH (SND (i2mw i1:bool#(A word)list)) +
     LENGTH (SND (i2mw i2:bool#(A word)list)) < LENGTH zs /\
     LENGTH zs < dimword (:A) DIV 2 /\
     ~(iop = multiword_Lt) /\ ~(iop = Eq) /\ ~(iop = multiword_Dec) /\
     (iop = multiword_Div \/ iop = multiword_Mod ==> ~(i2 = &0)) /\
     mc_div_max (SND (i2mw i1)) (SND (i2mw i2)) zs + 2 * LENGTH zs + 2 <= l ==>
     ?zs1 l2 t2.
       mc_iop (l,mc_header (i2mw i1),mc_header (i2mw i2),int_op_rep iop,
               SND (i2mw i1),SND (i2mw i2),zs) =
         (l2,mc_header (i2mw (multiword_int_op iop i1 i2)),SND (i2mw i1),SND (i2mw i2),
          APPEND (SND (i2mw (multiword_int_op iop i1 i2))) zs1) /\
       LENGTH (APPEND (SND (i2mw (multiword_int_op iop i1 i2))) zs1) = LENGTH zs /\
       l <= l2 + mc_div_max (SND (i2mw i1)) (SND (i2mw i2)) zs + 2 * LENGTH zs + 2 /\
       wl_evaluate (wl_Seq p1 (wl_Return 0 [0]),t) = wl_evaluate (wl_Return 0 [0],t2) /\
       0 < i' /\
       wl_state_stack t2 = wl_state_stack t /\
       wl_get_var 0 t2 = SOME ret_val /\
       word_bignumProof_state_rel
         (delete_vars [21; 17; 15; 14; 16; 19; 18; 20; 6; 13; 4; 11; 8; 12; 9; 7; 2; 3; 1; 0]
           (clock_write l2
             (reg_write 10 (SOME (mc_header (i2mw (multiword_int_op iop i1 i2))))
               (array_write In1 (SND (i2mw i1))
                 (array_write In2 (SND (i2mw i2))
                   (array_write Out (APPEND (SND (i2mw (multiword_int_op iop i1 i2))) zs1)
                     (word_bignumProof_state_REC
                        (((FEMPTY |+ (0,mc_header (i2mw i1))) |+
                          (1,mc_header (i2mw i2))) |+ (3,int_op_rep iop))
                        ((In1 =+ SND (i2mw i1)) ((In2 =+ SND (i2mw i2)) (K zs))) l)))))))
         t2 cs t frame /\
       wl_state_code t2 = wl_state_code t`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`SND (i2mw i1:bool#(A word)list)`; `SND (i2mw i2:bool#(A word)list)`;
    `zs:(A word)list`; `FST (i2mw i1:bool#(A word)list)`; `FST (i2mw i2:bool#(A word)list)`;
    `iop:mw_op`; `l:num`] mc_iop_thm) THEN
  REWRITE_TAC[PAIR; mw_ok_SND_i2mw; i2mw_NOT_NIL] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[mwi_op_thm] THEN
  DISCH_THEN(X_CHOOSE_THEN `zs1:(A word)list` (X_CHOOSE_THEN `l2:num` STRIP_ASSUME_TAC))) THEN
  (MP_TAC(ISPEC `word_bignumProof_state_REC
     (((FEMPTY |+ (0,mc_header (i2mw i1:bool#(A word)list))) |+
       (1,mc_header (i2mw i2:bool#(A word)list))) |+ (3,int_op_rep iop))
     ((In1 =+ SND (i2mw i1:bool#(A word)list))
        ((In2 =+ SND (i2mw i2:bool#(A word)list)) (K (zs:(A word)list)))) l`
     mc_iop_corr_thm) THEN
  REWRITE_TAC[word_bignumProof_Corr_def; word_bignumProof_state_INFO.ri_accessors;
              FAPPLY_FUPDATE_THM; APPLY_UPDATE_THM; K_THM; FDOM_FUPDATE; IN_INSERT;
              distinctness "address"; ARITH_EQ] THEN
  ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]) THEN
  (SUBGOAL_THEN `word_bignumProof_syntax_ok (mc_iop_code:(A)mini) /\
                (!body. ~(mc_iop_code = LoopBody body:(A)mini))` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!body. ~(mc_iop_code = LoopBody body:(A)mini)` ASSUME_TAC THENL
     [REWRITE_TAC[mc_iop_code_def; distinctness "mini"]; ALL_TAC] THEN
    ASM_SIMP_TAC[WBIGPAUX_syntax_ok_not_LoopBody] THEN
    REWRITE_TAC(!WBIGPAUX_syntax_ok_thms);
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (INST [`t:(A,C,FFI)wl_state`,`t0:(A,C,FFI)wl_state`]
    word_bignumProof_compile_thm)) THEN
  DISCH_THEN(MP_TAC o SPECL [`n:num`; `l':num`; `1`;
    `(n + 1,[]):num#((A)mini#num#(A)wl_prog)list`; `p1:(A)wl_prog`; `l1:num`; `i':num`;
    `cs:num#((A)mini#num#(A)wl_prog)list`; `cs:num#((A)mini#num#(A)wl_prog)list`;
    `t:(A,C,FFI)wl_state`; `ret_val:(A)word_loc`; `wl_Return 0 [0]:(A)wl_prog`]) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < 1`; code_subset_refl; option_DISTINCT] THEN
  CASE_REWRITE_TAC[]) THEN
  (DISCH_THEN(X_CHOOSE_THEN `t2:(A,C,FFI)wl_state` (X_CHOOSE_THEN
    `res:((A)wl_result)option#(A,C,FFI)wl_state` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`zs1:(A word)list`; `l2:num`; `t2:(A,C,FFI)wl_state`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]));;
