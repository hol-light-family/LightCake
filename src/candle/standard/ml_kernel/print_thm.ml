(* ========================================================================= *)
(* print_thm: port of HOL4 candle/standard/ml_kernel/print_thmScript.sml     *)
(* (CakeML v3479).  Functions for turning a context and a theorem into a    *)
(* string and back.                                                          *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's term and type are holSyntax's hol_term and hol_type             *)
(*   (constructors hol_Var, hol_Const, hol_Comb, hol_Abs, Tyvar, Tyapp), the *)
(*   update constructors are hol_ConstSpec, hol_TypeDefn, hol_NewType,       *)
(*   hol_NewConst, hol_NewAxiom; mlsexp's parse is mlsexp_parse, mlstring's  *)
(*   concat is mlstring_concat, strlit is implode.                           *)
(* - mlstring literals are implode "..."; HOL4's #"\n" is CHR 10; ++ is     *)
(*   APPEND (left associative, as in HOL4); EVERY is ALL.                    *)
(* - HOL4's termination proofs (measure type_size, sexp_size, LENGTH) are   *)
(*   cake_def_wf with the same measures.                                     *)
(* - HOL4's [simp] theorems are added to the kit simp set.                   *)
(* - HOL4 ends with an EVAL of thm_to_string on an example, printed; that   *)
(*   output is not part of the theory and is not reproduced.                 *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/libext.ml";;
needs "basis/pure/mlstring.ml";;
needs "basis/pure/mlint.ml";;
needs "basis/pure/mlsexp.ml";;
needs "candle/standard/monadic/holKernel.ml";;

prioritize_num();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* encoding into v                                                           *)
(* ------------------------------------------------------------------------- *)

let ty_to_v_def = cake_def_wf `MEASURE hol_type_size` TERM_TAC
  `(ty_to_v (Tyvar s) = Expr [Atom (implode "Tyvar"); Atom s]) /\
   (ty_to_v (Tyapp s tys) =
      Expr (CONS (Atom (implode "Tyapp")) (CONS (Atom s) (MAP ty_to_v tys))))`;;

let ty_to_v_ind = cake_ind "ty_to_v";;

let term_to_v_def = cake_def
  `(term_to_v (hol_Var s ty) = Expr [Atom (implode "Var"); Atom s; ty_to_v ty]) /\
   (term_to_v (hol_Const s ty) = Expr [Atom (implode "Const"); Atom s; ty_to_v ty]) /\
   (term_to_v (hol_Comb f x) = Expr [Atom (implode "Comb"); term_to_v f; term_to_v x]) /\
   (term_to_v (hol_Abs f x) = Expr [Atom (implode "Abs"); term_to_v f; term_to_v x])`;;

let thm_to_v_def = cake_def
  `thm_to_v (Sequent ts t) =
     Expr [Atom (implode "Sequent"); Expr (MAP term_to_v ts); term_to_v t]`;;

let update_to_v_def = cake_def
  `(update_to_v (hol_ConstSpec xs t) =
      Expr [Atom (implode "ConstSpec");
            Expr (MAP (\(s,t). Expr [Atom s; term_to_v t]) xs);
            term_to_v t]) /\
   (update_to_v (hol_TypeDefn s1 t s2 s3) =
      Expr [Atom (implode "TypeDefn"); Atom s1; term_to_v t; Atom s2; Atom s3]) /\
   (update_to_v (hol_NewType s n) =
      Expr [Atom (implode "NewType"); Atom s; Atom (num_to_str n)]) /\
   (update_to_v (hol_NewConst s ty) =
      Expr [Atom (implode "NewConst"); Atom s; ty_to_v ty]) /\
   (update_to_v (hol_NewAxiom t) =
      Expr [Atom (implode "NewAxiom"); term_to_v t])`;;

(* ------------------------------------------------------------------------- *)
(* decoding from v                                                           *)
(* ------------------------------------------------------------------------- *)

let MEM_IMP_sexp_size_LESS = prove
 (`!xs a. MEM a xs ==> sexp_size a < list_size sexp_size xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; list_size] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:sexp`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let v_to_str_def = cake_def
  `v_to_str (Atom s) = s`;;
let _ = cake_add_simps [v_to_str_def];;

let PRTHMAUX_MEM_TL_TL = prove
 (`!(xs:A list) y. ~(LENGTH xs < 2) /\ MEM y (TL (TL xs)) ==> MEM y xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; TL; MEM] THEN
  SPEC_TAC(`t:A list`,`t:A list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; TL; MEM] THEN CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[]);;

(* termination of the decoding functions: an element of the list is smaller *)
let PRTHMAUX_SEXP_TERM_TAC =
  REWRITE_TAC[MEASURE; type_size_def "sexp"] THEN REWRITE_TAC(size_aux_eqs "sexp") THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ARITH_RULE `a < b ==> a < 1 + b`) THEN
  MATCH_MP_TAC MEM_IMP_sexp_size_LESS THEN
  TRY(MATCH_MP_TAC MEM_EL THEN ASM_ARITH_TAC) THEN
  ASM_MESON_TAC[PRTHMAUX_MEM_TL_TL];;

let v_to_ty_def = cake_def_wf `MEASURE sexp_size` PRTHMAUX_SEXP_TERM_TAC
  `v_to_ty (Expr xs) =
     if HD xs = Atom (implode "Tyvar") then Tyvar (v_to_str (EL 1 xs))
     else if LENGTH xs < 2 then ARB else
       Tyapp (v_to_str (EL 1 xs)) (MAP v_to_ty (TL (TL xs)))`;;

let v_to_ty_ind = cake_ind "v_to_ty";;

let v_to_term_def = cake_def_wf `MEASURE sexp_size` PRTHMAUX_SEXP_TERM_TAC
  `v_to_term (Expr xs) =
     if LENGTH xs < 3 then ARB
     else if HD xs = Atom (implode "Comb") then
       hol_Comb (v_to_term (EL 1 xs)) (v_to_term (EL 2 xs))
     else if HD xs = Atom (implode "Abs") then
       hol_Abs (v_to_term (EL 1 xs)) (v_to_term (EL 2 xs))
     else if HD xs = Atom (implode "Var") then
       hol_Var (v_to_str (EL 1 xs)) (v_to_ty (EL 2 xs))
     else
       hol_Const (v_to_str (EL 1 xs)) (v_to_ty (EL 2 xs))`;;

let v_to_term_ind = cake_ind "v_to_term";;

let v_to_thm_def = cake_def
  `v_to_thm (Expr xs) =
     Sequent
       (match EL 1 xs with Expr ys -> MAP v_to_term ys)
       (v_to_term (EL 2 xs))`;;

let v_to_update_def = cake_def
  `v_to_update (Expr xs) =
     if HD xs = Atom (implode "ConstSpec") then
       hol_ConstSpec
         (match EL 1 xs with
            Expr ys ->
              MAP (\y. match y with
                         Expr zs -> (v_to_str (EL 0 zs),v_to_term (EL 1 zs))) ys)
         (v_to_term (EL 2 xs))
     else if HD xs = Atom (implode "TypeDefn") then
       hol_TypeDefn (v_to_str (EL 1 xs))
                    (v_to_term (EL 2 xs))
                    (v_to_str (EL 3 xs))
                    (v_to_str (EL 4 xs))
     else if HD xs = Atom (implode "NewType") then
       hol_NewType (v_to_str (EL 1 xs)) (THE (fromNatString (v_to_str (EL 2 xs))))
     else if HD xs = Atom (implode "NewConst") then
       hol_NewConst (v_to_str (EL 1 xs)) (v_to_ty (EL 2 xs))
     else
       hol_NewAxiom (v_to_term (EL 1 xs))`;;

(* the decoders on literal lists: list operations, mlstring and number literals *)
let PRTHMAUX_LIT_TAC =
  REWRITE_TAC[HD; TL; LENGTH; EL_CONS; v_to_str_def; injectivity "sexp";
              injectivity "mlstring"] THEN
  CONV_TAC(DEPTH_CONV STRING_EQ_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[HD; TL; LENGTH; EL_CONS; v_to_str_def] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

let ty_to_v_thm = prove
 (`!ty. v_to_ty (ty_to_v ty) = ty`,
  MATCH_MP_TAC ty_to_v_ind THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[ty_to_v_def] THEN ONCE_REWRITE_TAC[v_to_ty_def] THEN
  PRTHMAUX_LIT_TAC THEN
  REWRITE_TAC[ARITH_RULE `~(SUC (SUC n) < 2)`; injectivity "hol_type"; MAP_MAP_o] THEN
  ASM_REWRITE_TAC[MAP_EQ_ID; o_THM]);;
let _ = cake_add_simps [ty_to_v_thm];;

let term_to_v_thm = prove
 (`!t. v_to_term (term_to_v t) = t`,
  MATCH_MP_TAC hol_term_INDUCT THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[term_to_v_def] THEN ONCE_REWRITE_TAC[v_to_term_def] THEN
  PRTHMAUX_LIT_TAC THEN ASM_REWRITE_TAC[ty_to_v_thm]);;
let _ = cake_add_simps [term_to_v_thm];;

let thm_to_v_thm = prove
 (`!th. v_to_thm (thm_to_v th) = th`,
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `th:thm` (cases "thm")) THEN
  REWRITE_TAC[thm_to_v_def; v_to_thm_def] THEN PRTHMAUX_LIT_TAC THEN
  CASE_REWRITE_TAC[MAP_MAP_o; o_DEF; term_to_v_thm; MAP_ID]);;
let _ = cake_add_simps [thm_to_v_thm];;

let update_to_v_update = prove
 (`!u. v_to_update (update_to_v u) = u`,
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `u:update` (cases "update")) THEN
  REWRITE_TAC[update_to_v_def] THEN ONCE_REWRITE_TAC[v_to_update_def] THEN
  PRTHMAUX_LIT_TAC THEN
  REWRITE_TAC[term_to_v_thm; ty_to_v_thm; fromNatString_toString; THE_DEF] THEN
  CASE_REWRITE_TAC[injectivity "update"; MAP_MAP_o; o_DEF] THEN
  REWRITE_TAC[MAP_EQ_ID; FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  CASE_REWRITE_TAC[] THEN PRTHMAUX_LIT_TAC THEN REWRITE_TAC[term_to_v_thm]);;
let _ = cake_add_simps [update_to_v_update];;

(* ------------------------------------------------------------------------- *)
(* main definition                                                           *)
(* ------------------------------------------------------------------------- *)

let thm_to_string_def = cake_def
  `thm_to_string (ctxt:update list) (th:thm) =
     mlstring_concat
       (APPEND
         (APPEND
           (APPEND [implode "# The following is a theorem of higher-order logic\n\n"]
                   [sexp_to_pretty_string (thm_to_v th)])
           [implode "\n# which is proved in the following context\n"])
         (FLAT (MAP (\def. [implode "\n"; sexp_to_pretty_string (update_to_v def)])
                    ctxt)))`;;

(* it has an inverse: *)

let char_list_to_defs_def = cake_def_wf `MEASURE (LENGTH:string->num)`
  (REWRITE_TAC[MEASURE] THEN MESON_TAC[parse_IMP_LENGTH_LESS])
  `char_list_to_defs input =
     match mlsexp_parse input with
       INL _ -> []
     | INR (x,rest) -> CONS (v_to_update x) (char_list_to_defs rest)`;;

let char_list_to_defs_ind = cake_ind "char_list_to_defs";;

let string_to_thm_def = cake_def
  `string_to_thm s =
     let rest = dropWhile (\c. ~(c = CHR 10)) (explode s) in
     let (th_v,rest) = OUTR (mlsexp_parse rest) in
     let rest = dropWhile (\c. ~(c = CHR 10)) (TL (TL rest)) in
       (char_list_to_defs rest,v_to_thm th_v)`;;

(* HOL4: [local] *)
let to_explode = prove
 (CASE_TERM `!s. (match s with implode t -> t) = explode s`,
  GEN_TAC THEN QCASES_ON "s" THEN CASE_REWRITE_TAC[explode_thm]);;

(* the newline character literal (HOL4 #"\n") and parse_space for it *)
let PRTHMAUX_CHR10 = (REWR_CONV CHR_DEF THENC NUM_REDUCE_CONV) `CHR 10`;;

let PRTHMAUX_parse_space = REWRITE_RULE[PRTHMAUX_CHR10] parse_space;;

let PRTHMAUX_parse_nil = prove
 (`?msg. mlsexp_parse [] = INL (msg,[])`,
  REWRITE_TAC[mlsexp_parse_def; mlsexp_lex_def; mlsexp_lex_aux_def] THEN
  CASE_REWRITE_TAC[parse_aux_def] THEN MESON_TAC[]);;

(* the definitions printed after the theorem are read back *)
let PRTHMAUX_char_list_to_defs = prove
 (`!ctxt. char_list_to_defs
            (CONS (CHR 10)
              (FLAT (MAP explode
                (FLAT (MAP (\def. [implode "\n"; sexp_to_pretty_string (update_to_v def)])
                           ctxt))))) = ctxt`,
  REWRITE_TAC[PRTHMAUX_CHR10] THEN LIST_INDUCT_TAC THEN
  ONCE_REWRITE_TAC[char_list_to_defs_def] THEN
  REWRITE_TAC[MAP; FLAT; MAP_APPEND; FLAT_APPEND; APPEND; APPEND_NIL; explode_thm;
              PRTHMAUX_parse_space] THENL
   [X_CHOOSE_THEN `msg:mlstring` SUBST1_TAC PRTHMAUX_parse_nil THEN CASE_REWRITE_TAC[];
    REWRITE_TAC[parse_sexp_to_pretty_string] THEN
    CASE_REWRITE_TAC[APPEND; update_to_v_update] THEN ASM_REWRITE_TAC[]]);;

let string_to_thm_thm_to_string = prove
 (`!ctxt th. string_to_thm (thm_to_string ctxt th) = (ctxt,th)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[thm_to_string_def; string_to_thm_def; concat_thm; explode_thm] THEN
  REWRITE_TAC[MAP_APPEND; FLAT_APPEND; MAP; FLAT; APPEND_NIL; GSYM APPEND_ASSOC;
              explode_thm] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[APPEND; dropWhile_def; PRTHMAUX_CHR10; injectivity "char"] THEN
  REWRITE_TAC[PRTHMAUX_parse_space; parse_sexp_to_pretty_string; OUTR] THEN
  CASE_REWRITE_TAC[APPEND; TL] THEN
  REWRITE_TAC[dropWhile_def; injectivity "char"] THEN
  REWRITE_TAC[thm_to_v_thm; PAIR_EQ] THEN
  REWRITE_TAC[REWRITE_RULE[PRTHMAUX_CHR10] PRTHMAUX_char_list_to_defs]);;

let thm_to_string_injective = prove
 (`!ctxt1 th1 ctxt2 th2.
     thm_to_string ctxt1 th1 = thm_to_string ctxt2 th2
     ==> ctxt1 = ctxt2 /\ th1 = th2`,
  MESON_TAC[string_to_thm_thm_to_string; PAIR_EQ]);;
