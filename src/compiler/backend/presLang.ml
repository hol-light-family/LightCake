(* ========================================================================= *)
(* presLang: port of HOL4 compiler/backend/presLangScript.sml (CakeML        *)
(* v3479).                                                                   *)
(* Functions for converting various intermediate languages into displayLang *)
(* representations.                                                          *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The constructors of the languages carry their names.tsv prefixes        *)
(*   (displayLang_String, flat_Raise, clos_Var, bvl_Var, wl_Seq, ...); HOL4  *)
(*   toString on num is num_to_str, ^ is strcat, concat is mlstring_concat, *)
(*   FOLDR is ITLIST, w2n is val, and mlstring literals are implode "...".  *)
(* - HOL4's Overloads list_to_display and option_to_display are written out *)
(*   where they are used, as HOL4's parser expands them.                     *)
(* - HOL4 states num_to_hex_eq with words$word_to_hex_string w, which is not *)
(*   in the port; it is stated with its definition                           *)
(*   num_to_hex_string (val w) (= n2s 16 HEX (w2n w), ASCIInumbers).        *)
(* - HOL4's sizes exp1_size ... of the languages are written as list_size / *)
(*   pair_size forms; HOL4's prog_size ARB is stack_prog_size ARB or         *)
(*   wl_prog_size ARB.                                                        *)
(* - h + len - 1 is written (h + len) - 1: in HOL Light - binds tighter      *)
(*   than +.                                                                  *)
(* - The display functions with many clauses or mutual recursion are made   *)
(*   with sem1aux_def_wf and HOL4's measures; variables that HOL4 shadows in *)
(*   case arms are renamed (k1, nset, rs, fop, opw, rto, ...).               *)
(* - The ML values of the HOL4 script (bvl_test, bvi_test, data_test,       *)
(*   lab_test, names_tm, data_prog_tm and the print) are tests, skipped.    *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "basis/pure/mlint.ml";;
needs "basis/pure/mloption.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/displayLang.ml";;
needs "compiler/backend/source_to_flat.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/labLang.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/bvl.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* basics *)

let empty_item_def = cake_def
  `empty_item name = displayLang_String name`;;

let num_to_display_def = cake_def
  `num_to_display (n:num) = displayLang_String (num_to_str n)`;;

let int_to_display_def = cake_def
  `int_to_display (i:int) = displayLang_String (toString i)`;;

let string_imp_def = cake_def
  `string_imp s = displayLang_String s`;;

let item_with_num_def = cake_def
  `item_with_num name n = Item NONE name [num_to_display n]`;;

let item_with_nums_def = cake_def
  `item_with_nums name ns = Item NONE name (MAP num_to_display ns)`;;

let bool_to_display_def = cake_def
  `bool_to_display b =
     empty_item (if b then implode "True" else implode "False")`;;

let num_to_hex_def = cake_def_wf
  `MEASURE (\n:num. n)`
  (REWRITE_TAC WF_REL_THMS THEN REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `~(16 = 0)`] THEN ASM_ARITH_TAC)
  `num_to_hex n =
     APPEND (if n < 16 then [] else num_to_hex (n DIV 16))
            (num_to_hex_digit (n MOD 16))`;;

let separate_lines_def = cake_def
  `separate_lines name xs = displayLang_List (CONS (displayLang_String name) xs)`;;

(* num_to_hex "implements" words$word_to_hex_string in a simple way that the *)
(* translator can handle.  these lemmas check that is true.                   *)

let num_to_hex_digit_eq = prove
 (`!i. i < 16 ==> num_to_hex_digit i = [HEX i]`,
  GEN_TAC THEN REWRITE_TAC[num_to_hex_digit_def; HEX] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[CONS_11] THEN
  TRY (AP_TERM_TAC THEN ASM_ARITH_TAC) THEN ASM_ARITH_TAC);;

(* HOL4 states num_to_hex_eq with words$word_to_hex_string w, which is      *)
(* n2s 16 HEX (w2n w), i.e. num_to_hex_string (val w) (ASCIInumbers)       *)

let num_to_hex_eq = prove
 (`num_to_hex (val (w:N word)) = num_to_hex_string (val w)`,
  SPEC_TAC(`val (w:N word)`,`n:num`) THEN
  REWRITE_TAC[num_to_hex_string_def; n2s_def] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[num_to_hex_def] THEN ONCE_REWRITE_TAC[n2l_def] THEN
  REWRITE_TAC[ARITH_RULE `~(16 < 2)`] THEN
  SIMP_TAC[num_to_hex_digit_eq; MOD_LT_EQ; ARITH_RULE `~(16 = 0)`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP; REVERSE; APPEND] THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `n DIV 16`) THEN
  ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `~(16 = 0)`] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[]);;

let num_to_hex_mlstring_def = cake_def
  `num_to_hex_mlstring n = implode (APPEND "0x" (num_to_hex n))`;;

let word_to_display_def = cake_def
  `word_to_display (w:N word) = empty_item (num_to_hex_mlstring (val w))`;;

let item_with_word_def = cake_def
  `item_with_word name (w:N word) = Item NONE name [word_to_display w]`;;

let lit_to_display_def = cake_def
  `(lit_to_display (IntLit i) =
      Item NONE (implode "IntLit") [empty_item (toString i)]) /\
   (lit_to_display (Char c) =
      Item NONE (implode "Char")
        [empty_item (implode (APPEND (APPEND "#\"" [c]) "\""))]) /\
   (lit_to_display (StrLit s) =
      Item NONE (implode "StrLit") [string_imp s]) /\
   (lit_to_display (Word8 w8) =
      Item NONE (implode "Word8") [word_to_display w8]) /\
   (lit_to_display (Word64 w) =
      Item NONE (implode "Word64") [word_to_display w]) /\
   (lit_to_display (Float64 w) =
      Item NONE (implode "Float64") [word_to_display w])`;;

(* HOL4 Overloads list_to_display f xs = Tuple (MAP f xs) and              *)
(* option_to_display f opt = case opt of NONE => empty_item "none" | SOME  *)
(* opt' => Item NONE "some" [f opt'] are written out where they are used.  *)

(* source *)

let fp_cmp_to_display_def = cake_def
  `fp_cmp_to_display cmp =
     match cmp with
       FP_Less -> empty_item (implode "FP_Less")
     | FP_LessEqual -> empty_item (implode "FP_LessEqual")
     | FP_Greater -> empty_item (implode "FP_Greater")
     | FP_GreaterEqual -> empty_item (implode "FP_GreaterEqual")
     | FP_Equal -> empty_item (implode "FP_Equal")`;;

let fp_uop_to_display_def = cake_def
  `fp_uop_to_display opn =
     match opn with
       FP_Abs -> empty_item (implode "FP_Abs")
     | FP_Neg -> empty_item (implode "FP_Neg")
     | FP_Sqrt -> empty_item (implode "FP_Sqrt")`;;

let fp_bop_to_display_def = cake_def
  `fp_bop_to_display opn =
     match opn with
       FP_Add -> empty_item (implode "FP_Add")
     | FP_Sub -> empty_item (implode "FP_Sub")
     | FP_Mul -> empty_item (implode "FP_Mul")
     | FP_Div -> empty_item (implode "FP_Div")`;;

let fp_top_to_display_def = cake_def
  `fp_top_to_display opn =
     match opn with
       FP_Fma -> empty_item (implode "FP_Fma")`;;

let word_size_to_display_def = cake_def
  `(word_size_to_display W8 = empty_item (implode "W8")) /\
   (word_size_to_display W64 = empty_item (implode "W64"))`;;

let opb_to_display_def = cake_def
  `(opb_to_display Lt = empty_item (implode "Lt")) /\
   (opb_to_display Gt = empty_item (implode "Gt")) /\
   (opb_to_display Leq = empty_item (implode "Leq")) /\
   (opb_to_display Geq = empty_item (implode "Geq"))`;;

let opw_to_display_def = cake_def
  `(opw_to_display Andw = empty_item (implode "Andw")) /\
   (opw_to_display Orw = empty_item (implode "Orw")) /\
   (opw_to_display backend_common_Xor = empty_item (implode "Xor")) /\
   (opw_to_display backend_common_Add = empty_item (implode "Add")) /\
   (opw_to_display backend_common_Sub = empty_item (implode "Sub"))`;;

let shift_to_display_def = cake_def
  `(shift_to_display Lsl = empty_item (implode "Lsl")) /\
   (shift_to_display Lsr = empty_item (implode "Lsr")) /\
   (shift_to_display Asr = empty_item (implode "Asr")) /\
   (shift_to_display Ror = empty_item (implode "Ror"))`;;

let thunk_mode_to_display_def = cake_def
  `(thunk_mode_to_display Evaluated = empty_item (implode "Evaluated")) /\
   (thunk_mode_to_display NotEvaluated = empty_item (implode "NotEvaluated"))`;;

let thunk_op_to_display_def = cake_def
  `(thunk_op_to_display (AllocThunk m) =
      Item NONE (implode "AllocThunk") [thunk_mode_to_display m]) /\
   (thunk_op_to_display (UpdateThunk m) =
      Item NONE (implode "UpdateThunk") [thunk_mode_to_display m]) /\
   (thunk_op_to_display ForceThunk = empty_item (implode "ForceThunk"))`;;

let test_to_display_def = cake_def
  `(test_to_display Equal = empty_item (implode "Equal")) /\
   (test_to_display (Compare cmp) =
      Item NONE (implode "Compare") [opb_to_display cmp]) /\
   (test_to_display (AltCompare cmp) =
      Item NONE (implode "AltCompare") [opb_to_display cmp])`;;

let arith_to_display_def = cake_def
  `(arith_to_display Add = empty_item (implode "Add")) /\
   (arith_to_display Sub = empty_item (implode "Sub")) /\
   (arith_to_display Mul = empty_item (implode "Mul")) /\
   (arith_to_display Div = empty_item (implode "Div")) /\
   (arith_to_display Mod = empty_item (implode "Mod")) /\
   (arith_to_display And = empty_item (implode "And")) /\
   (arith_to_display Xor = empty_item (implode "Xor")) /\
   (arith_to_display Or = empty_item (implode "Or")) /\
   (arith_to_display Neg = empty_item (implode "Neg")) /\
   (arith_to_display Not = empty_item (implode "Not")) /\
   (arith_to_display Abs = empty_item (implode "Abs")) /\
   (arith_to_display Sqrt = empty_item (implode "Sqrt")) /\
   (arith_to_display FMA = empty_item (implode "FMA"))`;;

let prim_type_to_display_def = cake_def
  `(prim_type_to_display BoolT = empty_item (implode "BoolT")) /\
   (prim_type_to_display IntT = empty_item (implode "IntT")) /\
   (prim_type_to_display CharT = empty_item (implode "CharT")) /\
   (prim_type_to_display StrT = empty_item (implode "StrT")) /\
   (prim_type_to_display Float64T = empty_item (implode "Float64T")) /\
   (prim_type_to_display (WordT W8) = empty_item (implode "WordT_W8")) /\
   (prim_type_to_display (WordT W64) = empty_item (implode "WordT_W64"))`;;

let lop_to_display_def = cake_def
  `(lop_to_display Andalso = empty_item (implode "Andalso")) /\
   (lop_to_display Orelse = empty_item (implode "Orelse"))`;;

let op_to_display_def = cake_def
 `op_to_display (p:op) =
  match p with
   Shift ws sh n -> Item NONE (implode "Shift")
                            [word_size_to_display ws;
                             shift_to_display sh;
                             num_to_display n]
  | Arith a ty -> Item NONE (implode "Arith")
                         [arith_to_display a;
                          prim_type_to_display ty]
  | FromTo ty1 ty2 -> Item NONE (implode "FromTo")
                         [prim_type_to_display ty1;
                          prim_type_to_display ty2]
  | Test test ty -> Item NONE (implode "Test")
                         [test_to_display test;
                          prim_type_to_display ty]
  | Equality -> empty_item (implode "Equality")
  | Opapp -> empty_item (implode "Opapp")
  | Opassign -> empty_item (implode "Opassign")
  | Opref -> empty_item (implode "Opref")
  | Opderef -> empty_item (implode "Opderef")
  | Aw8alloc -> empty_item (implode "Aw8alloc")
  | Aw8sub -> empty_item (implode "Aw8sub")
  | Aw8length -> empty_item (implode "Aw8length")
  | Aw8update -> empty_item (implode "Aw8update")
  | CopyStrStr -> empty_item (implode "CopyStrStr")
  | CopyStrAw8 -> empty_item (implode "CopyStrAw8")
  | CopyAw8Str -> empty_item (implode "CopyAw8Str")
  | CopyAw8Aw8 -> empty_item (implode "CopyAw8Aw8")
  | Implode -> empty_item (implode "Implode")
  | Explode -> empty_item (implode "Explode")
  | Strsub -> empty_item (implode "Strsub")
  | Strlen -> empty_item (implode "Strlen")
  | Strcat -> empty_item (implode "Strcat")
  | VfromList -> empty_item (implode "VfromList")
  | Vsub -> empty_item (implode "Vsub")
  | Vsub_unsafe -> empty_item (implode "Vsub_unsafe")
  | Vlength -> empty_item (implode "Vlength")
  | Aalloc -> empty_item (implode "Aalloc")
  | AallocEmpty -> empty_item (implode "AallocEmpty")
  | AallocFixed -> empty_item (implode "AallocFixed")
  | Asub -> empty_item (implode "Asub")
  | Alength -> empty_item (implode "Alength")
  | Aupdate -> empty_item (implode "Aupdate")
  | Asub_unsafe -> empty_item (implode "Asub_unsafe")
  | Aupdate_unsafe -> empty_item (implode "Aupdate_unsafe")
  | Aw8sub_unsafe -> empty_item (implode "Aw8sub_unsafe")
  | Aw8update_unsafe -> empty_item (implode "Aw8update_unsafe")
  | XorAw8Str_unsafe -> empty_item (implode "XorAw8Str_unsafe")
  | ListAppend -> empty_item (implode "ListAppend")
  | ConfigGC -> empty_item (implode "ConfigGC")
  | FFI v35 -> empty_item (implode "FFI v35")
  | Eval -> empty_item (implode "Eval")
  | Env_id -> empty_item (implode "Env_id")
  | ThunkOp t -> thunk_op_to_display t`;;

let id_to_display_def = cake_def
  `(id_to_display (Short n) =
      Item NONE (implode "Short") [displayLang_String n]) /\
   (id_to_display (Long n i) =
      Item NONE (implode "Long") [displayLang_String n; id_to_display i])`;;

let ast_t_to_display_def = sem1aux_def_wf
  `MEASURE (\x:ast_t + ast_t list.
              sum_CASE x (\v. ast_t_size v) (\v. list_size ast_t_size v))`
  SEM1AUX_TC_TAC
  `(ast_t_to_display c =
      match c with
        Atvar n -> Item NONE (implode "Atvar") [displayLang_String n]
      | Atfun t1 t2 ->
          Item NONE (implode "Atfun") [ast_t_to_display t1; ast_t_to_display t2]
      | Attup ts ->
          Item NONE (implode "Attup") [displayLang_Tuple (ast_t_to_display_list ts)]
      | Atapp ts id ->
          Item NONE (implode "Attup")
            [displayLang_Tuple (ast_t_to_display_list ts); id_to_display id]) /\
   (ast_t_to_display_list [] = []) /\
   (ast_t_to_display_list (CONS x xs) =
      CONS (ast_t_to_display x) (ast_t_to_display_list xs))`;;

let ast_t_to_display_ind = cake_ind "ast_t_to_display";;

let pat_to_display_def = sem1aux_def_wf
  `MEASURE (\x:pat + pat list.
              sum_CASE x (\v. ast_pat_size v) (\v. list_size ast_pat_size v))`
  SEM1AUX_TC_TAC
  `(pat_to_display (c:pat) =
      match c with
        Pany -> Item NONE (implode "Pany") []
      | Pvar v -> Item NONE (implode "Pvar") [displayLang_String v]
      | Plit l -> Item NONE (implode "Plit") [lit_to_display l]
      | Pcon opt_id pats ->
          Item NONE (implode "Pcon")
            [(match opt_id with
                NONE -> empty_item (implode "none")
              | SOME opt' -> Item NONE (implode "some") [id_to_display opt']);
             displayLang_Tuple (pat_to_display_list pats)]
      | Pas t v -> Item NONE (implode "Pas") [pat_to_display t; displayLang_String v]
      | Pref t -> Item NONE (implode "Pref") [pat_to_display t]
      | Ptannot x y ->
          Item NONE (implode "Ptannot") [pat_to_display x; ast_t_to_display y]) /\
   (pat_to_display_list [] = []) /\
   (pat_to_display_list (CONS x xs) =
      CONS (pat_to_display x) (pat_to_display_list xs))`;;

let pat_to_display_ind = cake_ind "pat_to_display";;

let exp_to_display_def = sem1aux_def_wf
  `MEASURE (\x:exp + exp list + (pat # exp) list + (varN # varN # exp) list.
     sum_CASE x (\v. exp_size v)
       (\y. sum_CASE y (\v. list_size exp_size v)
              (\z. sum_CASE z (\v. list_size (pair_size ast_pat_size exp_size) v)
                     (\v. list_size (pair_size mlstring_size
                                       (pair_size mlstring_size exp_size)) v))))`
  SEM1AUX_TC_TAC
  `(exp_to_display (c:exp) =
      match c with
        Lit l -> Item NONE (implode "Lit") [lit_to_display l]
      | Raise e -> Item NONE (implode "Raise") [exp_to_display e]
      | Con opt_id es ->
          Item NONE (implode "Con")
            [(match opt_id with
                NONE -> empty_item (implode "none")
              | SOME opt' -> Item NONE (implode "some") [id_to_display opt']);
             displayLang_Tuple (exp_to_display_list es)]
      | Var id -> Item NONE (implode "Var") [id_to_display id]
      | Fun n e -> Item NONE (implode "Fun") [displayLang_String n; exp_to_display e]
      | App opn es ->
          Item NONE (implode "App") (CONS (op_to_display opn) (exp_to_display_list es))
      | Log lop e1 e2 ->
          Item NONE (implode "Log")
            [lop_to_display lop; exp_to_display e1; exp_to_display e2]
      | If e1 e2 e3 ->
          Item NONE (implode "If")
            [exp_to_display e1; exp_to_display e2; exp_to_display e3]
      | Let n_opt e1 e2 ->
          Item NONE (implode "Let")
            [(match n_opt with
                NONE -> empty_item (implode "none")
              | SOME opt' -> Item NONE (implode "some") [displayLang_String opt']);
             exp_to_display e1;
             exp_to_display e2]
      | Mat e pats ->
          Item NONE (implode "Mat")
            [exp_to_display e; displayLang_Tuple (pat_exp_to_display_list pats)]
      | Handle e pats ->
          Item NONE (implode "Handle")
            [exp_to_display e; displayLang_Tuple (pat_exp_to_display_list pats)]
      | Letrec fns e ->
          Item NONE (implode "Letrec")
            [displayLang_Tuple (fun_to_display_list fns); exp_to_display e]
      | Tannot e _ -> Item NONE (implode "Tannot") [exp_to_display e]
      | Lannot e _ -> Item NONE (implode "Lannot") [exp_to_display e]) /\
   (exp_to_display_list [] = []) /\
   (exp_to_display_list (CONS x xs) =
      CONS (exp_to_display x) (exp_to_display_list xs)) /\
   (pat_exp_to_display_list [] = []) /\
   (pat_exp_to_display_list (CONS (p,e) pxs) =
      CONS (displayLang_Tuple [pat_to_display p; exp_to_display e])
           (pat_exp_to_display_list pxs)) /\
   (fun_to_display_list [] = []) /\
   (fun_to_display_list (CONS (m,n,e) fxs) =
      CONS (displayLang_Tuple [displayLang_String m; displayLang_String n;
                               exp_to_display e])
           (fun_to_display_list fxs))`;;

let source_to_display_dec_def = sem1aux_def_wf
  `MEASURE (\x:dec + dec list.
              sum_CASE x (\v. dec_size v) (\v. list_size dec_size v))`
  SEM1AUX_TC_TAC
  `(source_to_display_dec (d:dec) =
      match d with
        Dlet _ pat e ->
          Item NONE (implode "Dlet") [pat_to_display pat; exp_to_display e]
      | Dletrec _ fns ->
          Item NONE (implode "Dletrec")
            (MAP (\(m,n,e). displayLang_Tuple [displayLang_String m;
                                               displayLang_String n;
                                               exp_to_display e]) fns)
      | Dtype _ ts ->
          Item NONE (implode "Dtype")
            (MAP (\(ns,n,z).
                    displayLang_Tuple
                      [displayLang_Tuple (MAP displayLang_String ns);
                       displayLang_String n;
                       displayLang_Tuple
                         (MAP (\(n,tys). displayLang_Tuple
                                [displayLang_String n;
                                 displayLang_Tuple (MAP ast_t_to_display tys)]) z)])
                 ts)
      | Dtabbrev _ ns n ty ->
          Item NONE (implode "Dtabbrev")
            [displayLang_Tuple (MAP displayLang_String ns);
             displayLang_String n;
             ast_t_to_display ty]
      | Dexn _ n tys ->
          Item NONE (implode "Dexn")
            [displayLang_String n; displayLang_Tuple (MAP ast_t_to_display tys)]
      | Dmod n ds ->
          Item NONE (implode "Dmod")
            [displayLang_String n; displayLang_Tuple (source_to_display_dec_list ds)]
      | Dlocal xs ys ->
          Item NONE (implode "Dlocal")
            [displayLang_Tuple (source_to_display_dec_list xs);
             displayLang_Tuple (source_to_display_dec_list ys)]
      | Denv n -> Item NONE (implode "Denv") [displayLang_String n]) /\
   (source_to_display_dec_list [] = []) /\
   (source_to_display_dec_list (CONS x xs) =
      CONS (source_to_display_dec x) (source_to_display_dec_list xs))`;;

let source_to_display_dec_ind = cake_ind "source_to_display_dec";;

(* flat *)

(* HOL4 pat1_size (on flatLang$pat lists) is list_size flat_pat_size *)

let MEM_pat_size = prove
 (`!pats a. MEM a (pats:flat_pat list) ==>
            flat_pat_size a < list_size flat_pat_size pats`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; list_size] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY ARITH_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `a:flat_pat`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let opt_con_to_display_def = cake_def
  `opt_con_to_display (ocon:(num # num option) option) =
     match ocon with
       NONE -> empty_item (implode "ConIdNone")
     | SOME (c, NONE) -> item_with_num (implode "ConIdUntyped") c
     | SOME (c, SOME t) -> item_with_nums (implode "ConIdTyped") [c; t]`;;

let flat_pat_to_display_def = sem1aux_def_wf
  `MEASURE (\x:flat_pat + flat_pat list.
              sum_CASE x (\v. flat_pat_size v) (\v. list_size flat_pat_size v))`
  SEM1AUX_TC_TAC
  `(flat_pat_to_display p =
      match p with
        flat_Pvar nm -> Item NONE (implode "Pvar") [string_imp nm]
      | flat_Pany -> empty_item (implode "Pany")
      | flat_Plit l -> Item NONE (implode "Plit") [lit_to_display l]
      | flat_Pcon id pats ->
          Item NONE (implode "Pcon") (flat_pat_to_display_list pats)
      | flat_Pas pat nm ->
          Item NONE (implode "Pas") [flat_pat_to_display pat; string_imp nm]
      | flat_Pref pat -> Item NONE (implode "Pref") [flat_pat_to_display pat]) /\
   (flat_pat_to_display_list [] = []) /\
   (flat_pat_to_display_list (CONS x xs) =
      CONS (flat_pat_to_display x) (flat_pat_to_display_list xs))`;;

let flat_pat_to_display_ind = cake_ind "flat_pat_to_display";;

let flat_op_to_display_def = cake_def
  `flat_op_to_display opn =
     match opn with
       Src ast_op -> op_to_display ast_op
     | GlobalVarAlloc n -> item_with_num (implode "GlobalVarAlloc") n
     | GlobalVarInit n -> item_with_num (implode "GlobalVarInit") n
     | GlobalVarLookup n -> item_with_num (implode "GlobalVarLookup") n
     | flat_TagLenEq n1 n2 -> item_with_nums (implode "TagLenEq") [n1; n2]
     | flat_LenEq n1 -> item_with_nums (implode "LenEq") [n1]
     | flat_El n -> item_with_num (implode "El") n
     | Id -> empty_item (implode "Id")`;;

(* HOL4 exp1_size, exp6_size, exp3_size (of flatLang) are the list_size    *)
(* forms of flatLang.ml                                                       *)

let MEM_funs_size = prove
 (`!fs v1 v2 e. MEM (v1,v2,e) fs ==>
                flat_exp_size e <
                list_size (pair_size mlstring_size
                             (pair_size mlstring_size flat_exp_size)) fs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; list_size] THEN REPEAT GEN_TAC THEN
  DISCH_THEN (DISJ_CASES_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THENL
   [REWRITE_TAC[pair_size_THM] THEN ARITH_TAC;
    FIRST_X_ASSUM (MP_TAC o SPECL [`v1:mlstring`; `v2:mlstring`; `e:flat_exp`]) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let MEM_exps_size = prove
 (`!exps e. MEM e exps ==> flat_exp_size e < list_size flat_exp_size exps`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; list_size] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY ARITH_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `e:flat_exp`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let MEM_pats_size = prove
 (`!pats p e. MEM (p,e) pats ==>
              flat_exp_size e < list_size (pair_size flat_pat_size flat_exp_size) pats`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; list_size] THEN REPEAT GEN_TAC THEN
  DISCH_THEN (DISJ_CASES_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THENL
   [REWRITE_TAC[pair_size_THM] THEN ARITH_TAC;
    FIRST_X_ASSUM (MP_TAC o SPECL [`p:flat_pat`; `e:flat_exp`]) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let add_name_hint_def = cake_def
  `add_name_hint prefix name_hint =
     mlstring_concat [prefix; implode "<"; name_hint; implode ">"]`;;

let flat_to_display_def = sem1aux_def_wf
  `MEASURE (\x:flat_exp + flat_exp list + (flat_pat # flat_exp) list +
               (varN # varN # flat_exp) list.
     sum_CASE x (\v. flat_exp_size v)
       (\y. sum_CASE y (\v. list_size flat_exp_size v)
              (\z. sum_CASE z (\v. list_size (pair_size flat_pat_size flat_exp_size) v)
                     (\v. list_size (pair_size mlstring_size
                                       (pair_size mlstring_size flat_exp_size)) v))))`
  SEM1AUX_TC_TAC
  `(flat_to_display (flat_Raise tra exp) =
      Item (SOME tra) (implode "raise") [flat_to_display exp]) /\
   (flat_to_display (flat_Handle tra exp pes) =
      Item (SOME tra) (implode "handle")
        (CONS (flat_to_display exp) (pat_flat_to_display_list pes))) /\
   (flat_to_display (flat_Lit tra l) = Item (SOME tra) (implode "lit") []) /\
   (flat_to_display (flat_Con tra id_opt exps) =
      Item (SOME tra) (implode "con")
        (CONS (opt_con_to_display id_opt) (flat_to_display_list exps))) /\
   (flat_to_display (Var_local tra nm) =
      Item (SOME tra) (implode "var_local") [string_imp nm]) /\
   (flat_to_display (flat_Fun name_hint nm exp) =
      Item (SOME backend_common_None) (add_name_hint (implode "fun") name_hint)
        [string_imp nm; flat_to_display exp]) /\
   (flat_to_display (flat_App tra opn exps) =
      Item (SOME tra) (implode "app")
        (CONS (flat_op_to_display opn) (flat_to_display_list exps))) /\
   (flat_to_display (flat_If tra exp1 exp2 exp3) =
      Item (SOME tra) (implode "if")
        [flat_to_display exp1; flat_to_display exp2; flat_to_display exp3]) /\
   (flat_to_display (flat_Mat tra exp pes) =
      Item (SOME tra) (implode "mat")
        (CONS (flat_to_display exp) (pat_flat_to_display_list pes))) /\
   (flat_to_display (flat_Let tra nm_opt exp1 exp2) =
      Item (SOME tra) (implode "let")
        [(match nm_opt with
            NONE -> empty_item (implode "none")
          | SOME opt' -> Item NONE (implode "some") [string_imp opt']);
         flat_to_display exp1; flat_to_display exp2]) /\
   (flat_to_display (flat_Letrec name_hint funs exp) =
      Item (SOME backend_common_None) (add_name_hint (implode "letrec") name_hint)
        [displayLang_Tuple (fun_flat_to_display_list funs); flat_to_display exp]) /\
   (flat_to_display_list [] = []) /\
   (flat_to_display_list (CONS x xs) =
      CONS (flat_to_display x) (flat_to_display_list xs)) /\
   (pat_flat_to_display_list [] = []) /\
   (pat_flat_to_display_list (CONS (pat,exp) pxs) =
      CONS (displayLang_Tuple [flat_pat_to_display pat; flat_to_display exp])
           (pat_flat_to_display_list pxs)) /\
   (fun_flat_to_display_list [] = []) /\
   (fun_flat_to_display_list (CONS (v1,v2,e) fxs) =
      CONS (displayLang_Tuple [string_imp v1; string_imp v2; flat_to_display e])
           (fun_flat_to_display_list fxs))`;;

(* clos *)

let num_to_varn_aux_def = cake_def_wf
  `MEASURE (\n:num. n)`
  (REWRITE_TAC WF_REL_THMS THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC (ARITH_RULE `m <= n DIV 26 /\ n DIV 26 < n ==> m - 1 < n`) THEN
   ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `~(26 = 0)`; LE_REFL] THEN ASM_ARITH_TAC)
  `num_to_varn_aux n =
     if n < 26 then [CHR (97 + n)]
     else APPEND (num_to_varn_aux ((n DIV 26) - 1)) [CHR (97 + (n MOD 26))]`;;

let num_to_varn_aux_ind = cake_ind "num_to_varn_aux";;

let num_to_varn_def = cake_def
  `num_to_varn n = implode (num_to_varn_aux n)`;;

let display_num_as_varn_def = cake_def
  `display_num_as_varn n = string_imp (num_to_varn n)`;;

let num_to_varn_list_def = cake_def
  `num_to_varn_list h n =
     if n = 0 then [] else
     CONS (num_to_varn (h + n)) (num_to_varn_list h (n - 1))`;;

let attach_name_def = cake_def
  `(attach_name (ns:mlstring spt) NONE = implode "none") /\
   (attach_name ns (SOME d) =
      match lookup d ns with
        NONE -> num_to_str d
      | SOME name -> mlstring_concat [name; implode "@"; num_to_str d])`;;

let const_part_to_display_def = cake_def
  `(const_part_to_display (clos_Int i) =
      Item NONE (implode "Int") [int_to_display i]) /\
   (const_part_to_display (clos_Con t vs) =
      Item NONE (implode "Con")
        [num_to_display t; displayLang_Tuple (MAP num_to_display vs)]) /\
   (const_part_to_display (clos_Str s) =
      Item NONE (implode "Str")
        [displayLang_String (mlstring_concat [implode "\""; s; implode "\""])]) /\
   (const_part_to_display (clos_W64 w) =
      Item NONE (implode "W64") [word_to_display w])`;;

let const_to_display_def = sem1aux_def_wf
  `MEASURE (\x:const + const list.
              sum_CASE x (\v. const_size v) (\v. list_size const_size v))`
  SEM1AUX_TC_TAC
  `(const_to_display (ConstInt i) =
      Item NONE (implode "ConstInt") [int_to_display i]) /\
   (const_to_display (ConstCons t vs) =
      Item NONE (implode "ConstCons")
        [num_to_display t; displayLang_Tuple (const_to_display_list vs)]) /\
   (const_to_display (ConstStr s) =
      Item NONE (implode "ConstStr")
        [displayLang_String (mlstring_concat [implode "\""; s; implode "\""])]) /\
   (const_to_display (ConstWord64 w) =
      Item NONE (implode "ConstWord64") [word_to_display w]) /\
   (const_to_display_list [] = []) /\
   (const_to_display_list (CONS x xs) =
      CONS (const_to_display x) (const_to_display_list xs))`;;

let const_to_display_ind = cake_ind "const_to_display";;

let clos_op_to_display_def = cake_def
 `clos_op_to_display ns opn = match opn with
     GlobOp (clos_Global n) -> item_with_num (implode "Global") n
    | GlobOp (SetGlobal n) -> item_with_num (implode "SetGlobal") n
    | GlobOp AllocGlobal -> displayLang_String (implode "AllocGlobal")
    | GlobOp GlobalsPtr -> displayLang_String (implode "GlobalsPtr")
    | GlobOp SetGlobalsPtr -> displayLang_String (implode "SetGlobalsPtr")
    | BlockOp (clos_Cons n) -> item_with_num (implode "Cons") n
    | BlockOp (ElemAt n) -> item_with_num (implode "ElemAt") n
    | BlockOp (clos_TagLenEq n1 n2) -> item_with_nums (implode "TagLenEq") [n1; n2]
    | BlockOp (BoolTest test) -> Item NONE (implode "BoolTest") [test_to_display test]
    | BlockOp BoolNot -> displayLang_String (implode "BoolNot")
    | BlockOp (clos_LenEq n) -> item_with_num (implode "LenEq") n
    | BlockOp (TagEq n) -> item_with_num (implode "TagEq") n
    | BlockOp LengthBlock -> displayLang_String (implode "LengthBlock")
    | BlockOp BoundsCheckBlock -> displayLang_String (implode "BoundsCheckBlock")
    | BlockOp (ConsExtend n) -> item_with_num (implode "ConsExtend") n
    | BlockOp (FromList n) -> item_with_num (implode "FromList") n
    | BlockOp clos_ListAppend -> displayLang_String (implode "ListAppend")
    | BlockOp (Constant c) -> Item NONE (implode "Constant") [const_to_display c]
    | BlockOp clos_Equal -> displayLang_String (implode "Equal")
    | BlockOp (EqualConst c) -> Item NONE (implode "EqualConst") [const_part_to_display c]
    | BlockOp (Build bs) -> Item NONE (implode "Build") (MAP const_part_to_display bs)
    | MemOp clos_Ref -> displayLang_String (implode "Ref")
    | MemOp Update -> displayLang_String (implode "Update")
    | MemOp clos_El -> displayLang_String (implode "El")
    | MemOp Length -> displayLang_String (implode "Length")
    | MemOp LengthByte -> displayLang_String (implode "LengthByte")
    | MemOp (RefByte b) -> Item NONE (implode "RefByte") [bool_to_display b]
    | MemOp RefArray -> displayLang_String (implode "RefArray")
    | MemOp DerefByte -> displayLang_String (implode "DerefByte")
    | MemOp UpdateByte -> displayLang_String (implode "UpdateByte")
    | MemOp ConcatByteVec -> displayLang_String (implode "ConcatByteVec")
    | MemOp (CopyByte b) -> Item NONE (implode "CopyByte") [bool_to_display b]
    | MemOp FromListByte -> displayLang_String (implode "FromListByte")
    | MemOp ToListByte -> displayLang_String (implode "ToListByte")
    | MemOp LengthByteVec -> displayLang_String (implode "LengthByteVec")
    | MemOp DerefByteVec -> displayLang_String (implode "DerefByteVec")
    | MemOp BoundsCheckArray -> displayLang_String (implode "BoundsCheckArray")
    | MemOp (BoundsCheckByte b) -> Item NONE (implode "BoundsCheckByte") [bool_to_display b]
    | MemOp clos_ConfigGC -> displayLang_String (implode "ConfigGC")
    | MemOp (StringCmp b opb) -> Item NONE (implode "StringCmp") [bool_to_display b;
                                                                 opb_to_display opb]
    | MemOp XorByte -> displayLang_String (implode "XorByte")
    | MemOp (MutCons tag i) -> item_with_nums (implode "MutCons") [tag; i]
    | MemOp UpdateCons -> displayLang_String (implode "UpdateCons")
    | MemOp FinaliseCons -> displayLang_String (implode "FinaliseCons")
    | clos_Label n -> Item NONE (implode "Label") [displayLang_String (attach_name ns (SOME n))]
    | clos_FFI s -> Item NONE (implode "FFI") [string_imp s]
    | IntOp (clos_Const i) -> Item NONE (implode "Const") [int_to_display i]
    | IntOp clos_Add -> displayLang_String (implode "Add")
    | IntOp clos_Sub -> displayLang_String (implode "Sub")
    | IntOp Mult -> displayLang_String (implode "Mult")
    | IntOp clos_Div -> displayLang_String (implode "Div")
    | IntOp clos_Mod -> displayLang_String (implode "Mod")
    | IntOp clos_Less -> displayLang_String (implode "Less")
    | IntOp LessEq -> displayLang_String (implode "LessEq")
    | IntOp Greater -> displayLang_String (implode "Greater")
    | IntOp GreaterEq -> displayLang_String (implode "GreaterEq")
    | IntOp (LessConstSmall n) -> item_with_num (implode "LessConstSmall") n
    | WordOp (WordOpw ws opw) -> Item NONE (implode "WordOp")
                                     [word_size_to_display ws;
                                      opw_to_display opw]
    | WordOp (WordShift ws sh n) -> Item NONE (implode "WordShift")
                                           [word_size_to_display ws;
                                            shift_to_display sh;
                                            num_to_display n]
    | WordOp (WordTest ws test) -> Item NONE (implode "WordTest")
                                        [word_size_to_display ws;
                                         test_to_display test]
    | WordOp WordFromInt -> displayLang_String (implode "WordFromInt")
    | WordOp WordToInt -> displayLang_String (implode "WordToInt")
    | WordOp (WordFromWord b) -> Item NONE (implode "WordFromWord") [bool_to_display b]
    | WordOp (FP_cmp cmp) -> fp_cmp_to_display cmp
    | WordOp (FP_uop fop) -> fp_uop_to_display fop
    | WordOp (FP_bop fop) -> fp_bop_to_display fop
    | WordOp (FP_top fop) -> fp_top_to_display fop
    | clos_Install -> displayLang_String (implode "Install")
    | clos_ThunkOp t -> thunk_op_to_display t`;;

(* HOL4 exp3_size (of closLang) is list_size clos_exp_size *)

let MEM_clos_exps_size = prove
 (`!exps e. MEM e exps ==> clos_exp_size e < list_size clos_exp_size exps`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; list_size] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY ARITH_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `e:clos_exp`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let presLang_commas_def = cake_def
  `(presLang_commas [] = implode "") /\
   (presLang_commas [x] = x) /\
   (presLang_commas (CONS x xs) = strcat (strcat x (implode ",")) (presLang_commas xs))`;;

let clos_to_display_def = sem1aux_def_wf
  `MEASURE (\x:(mlstring spt # num # clos_exp) +
               (mlstring spt # num # clos_exp list) +
               (mlstring spt # num # num # clos_exp list) +
               (mlstring spt # num # num # num # (num # clos_exp) list).
     sum_CASE x (\p. clos_exp_size (SND (SND p)))
       (\y. sum_CASE y (\p. list_size clos_exp_size (SND (SND p)))
              (\z. sum_CASE z (\p. list_size clos_exp_size (SND (SND (SND p))))
                     (\p. list_size (pair_size (\x:num. x) clos_exp_size)
                                    (SND (SND (SND (SND p))))))))`
  (SEM1AUX_TC_TAC ORELSE
   (REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    RVEQ_TAC THEN
    REWRITE_TAC(WF_REL_THMS @ [sum_CASE; FST; SND; type_size_def "clos_exp"] @
                size_aux_eqs "clos_exp") THEN
    REWRITE_TAC[list_size_pair_size_MAP_FST_SND] THEN ARITH_TAC))
  `(clos_to_display ns h (clos_Var t n) =
      Item (SOME t) (implode "var") [display_num_as_varn ((h - n) - 1)]) /\
   (clos_to_display ns h (clos_If t x1 x2 x3) =
      Item (SOME t) (implode "if")
        [clos_to_display ns h x1; clos_to_display ns h x2; clos_to_display ns h x3]) /\
   (clos_to_display ns h (clos_Let t xs x) =
      separate_lines (implode "let")
        [displayLang_Tuple (clos_to_display_lets ns h (LENGTH xs - 1) xs);
         clos_to_display ns (h + LENGTH xs) x]) /\
   (clos_to_display ns h (clos_Raise t x) =
      Item (SOME t) (implode "raise") [clos_to_display ns h x]) /\
   (clos_to_display ns h (clos_Tick t x) =
      Item (SOME t) (implode "tick") [clos_to_display ns h x]) /\
   (clos_to_display ns h (clos_Handle t x y) =
      Item (SOME t) (implode "handle")
        [clos_to_display ns h x; display_num_as_varn h;
         clos_to_display ns (h + 1) y]) /\
   (clos_to_display ns h (clos_Call t ticks dest xs) =
      Item (SOME t) (implode "call")
        (APPEND [num_to_display ticks; displayLang_String (attach_name ns (SOME dest))]
                (clos_to_display_list ns h xs))) /\
   (clos_to_display ns h (clos_App t opt_n x xs) =
      Item (SOME t) (implode "app")
        (APPEND [(match opt_n with
                    NONE -> empty_item (implode "none")
                  | SOME opt' -> Item NONE (implode "some") [num_to_display opt']);
                 clos_to_display ns h x]
                (clos_to_display_list ns h xs))) /\
   (clos_to_display ns h (Fn name_hint n1 n2 vn x) =
      Item (SOME backend_common_None) (add_name_hint (implode "fn") name_hint)
        [(match n1 with
            NONE -> empty_item (implode "none")
          | SOME opt' -> Item NONE (implode "some") [num_to_display opt']);
         (match n2 with
            NONE -> empty_item (implode "none")
          | SOME opt' -> Item NONE (implode "some")
                           [displayLang_Tuple (MAP num_to_display opt')]);
         displayLang_Tuple (MAP string_imp (num_to_varn_list h vn));
         clos_to_display ns h x]) /\
   (clos_to_display ns h (clos_Letrec name_hints n1 n2 es e) =
      Item (SOME backend_common_None)
        (add_name_hint (implode "letrec") (presLang_commas name_hints))
        [(match n1 with
            NONE -> empty_item (implode "none")
          | SOME opt' -> Item NONE (implode "some") [num_to_display opt']);
         (match n2 with
            NONE -> empty_item (implode "none")
          | SOME opt' -> Item NONE (implode "some")
                           [displayLang_Tuple (MAP num_to_display opt')]);
         displayLang_Tuple
           (clos_to_display_letrecs ns h (LENGTH es - 1) (LENGTH es) es);
         clos_to_display ns h e]) /\
   (clos_to_display ns h (clos_Op t opn xs) =
      Item (SOME t) (implode "op")
        (CONS (clos_op_to_display LN opn) (clos_to_display_list ns h xs))) /\
   (clos_to_display_list ns h [] = []) /\
   (clos_to_display_list ns h (CONS x xs) =
      CONS (clos_to_display ns h x) (clos_to_display_list ns h xs)) /\
   (clos_to_display_lets ns h i [] = []) /\
   (clos_to_display_lets ns h i (CONS x xs) =
      CONS (displayLang_Tuple [display_num_as_varn (h + i);
                               displayLang_String (implode "<-");
                               clos_to_display ns h x])
           (clos_to_display_lets ns h (i - 1) xs)) /\
   (clos_to_display_letrecs ns h i len [] = []) /\
   (clos_to_display_letrecs ns h i len (CONS (vn,e) es) =
      CONS (displayLang_Tuple
              [display_num_as_varn (h + i);
               displayLang_Tuple (MAP string_imp (num_to_varn_list ((h + len) - 1) vn));
               clos_to_display ns ((h + len) + vn) e])
           (clos_to_display_letrecs ns h (i - 1) len es))`;;

let clos_to_display_ind = cake_ind "clos_to_display";;

let clos_fun_to_display_def = cake_def
  `clos_fun_to_display names (n,argc,body) =
     displayLang_Tuple
       [displayLang_String (implode "func");
        displayLang_String (attach_name names (SOME n));
        displayLang_Tuple (REVERSE (list_of_seq display_num_as_varn argc));
        clos_to_display names argc body]`;;

let clos_dec_to_display_def = cake_def
  `clos_dec_to_display names dec =
     displayLang_Tuple [displayLang_String (implode "dec");
                        clos_to_display names 0 dec]`;;

(* bvl *)

(* HOL4 exp1_size (of bvl) is list_size bvl_exp_size *)

let MEM_bvl_exps_size = prove
 (`!exps e. MEM e exps ==> bvl_exp_size e < list_size bvl_exp_size exps`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; list_size] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY ARITH_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `e:bvl_exp`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let bvl_to_display_def = sem1aux_def_wf
  `MEASURE (\x:(mlstring spt # num # bvl_exp) +
               (mlstring spt # num # bvl_exp list) +
               (mlstring spt # num # num # bvl_exp list).
     sum_CASE x (\p. bvl_exp_size (SND (SND p)))
       (\y. sum_CASE y (\p. list_size bvl_exp_size (SND (SND p)))
              (\p. list_size bvl_exp_size (SND (SND (SND p))))))`
  SEM1AUX_TC_TAC
  `(bvl_to_display ns h (bvl_Var n) =
      Item NONE (implode "var") [display_num_as_varn ((h - n) - 1)]) /\
   (bvl_to_display ns h (bvl_If x1 x2 x3) =
      Item NONE (implode "if")
        [bvl_to_display ns h x1; bvl_to_display ns h x2; bvl_to_display ns h x3]) /\
   (bvl_to_display ns h (bvl_Let xs x) =
      separate_lines (implode "let")
        (APPEND (bvl_to_display_lets ns h (LENGTH xs - 1) xs)
                [bvl_to_display ns (h + LENGTH xs) x])) /\
   (bvl_to_display ns h (bvl_Raise x) =
      Item NONE (implode "raise") [bvl_to_display ns h x]) /\
   (bvl_to_display ns h (bvl_Tick x) =
      Item NONE (implode "tick") [bvl_to_display ns h x]) /\
   (bvl_to_display ns h (bvl_Handle x y) =
      Item NONE (implode "handle")
        [bvl_to_display ns h x; display_num_as_varn h;
         bvl_to_display ns (h + 1) y]) /\
   (bvl_to_display ns h (bvl_Call ticks dest xs) =
      Item NONE (implode "call")
        (CONS (displayLang_String (attach_name ns dest))
              (bvl_to_display_list ns h xs))) /\
   (bvl_to_display ns h (bvl_Force loc n) =
      Item NONE (implode "force")
        [display_num_as_varn ((h - n) - 1);
         displayLang_String (attach_name ns (SOME loc))]) /\
   (bvl_to_display ns h (bvl_Op opn xs) =
      Item NONE (implode "op")
        (CONS (clos_op_to_display ns opn) (bvl_to_display_list ns h xs))) /\
   (bvl_to_display_list ns h [] = []) /\
   (bvl_to_display_list ns h (CONS x xs) =
      CONS (bvl_to_display ns h x) (bvl_to_display_list ns h xs)) /\
   (bvl_to_display_lets ns h i [] = []) /\
   (bvl_to_display_lets ns h i (CONS x xs) =
      CONS (displayLang_Tuple [display_num_as_varn (h + i);
                               displayLang_String (implode "<-");
                               bvl_to_display ns h x])
           (bvl_to_display_lets ns h (i - 1) xs))`;;

let bvl_to_display_ind = cake_ind "bvl_to_display";;

let bvl_fun_to_display_def = cake_def
  `bvl_fun_to_display names (n,argc,body) =
     displayLang_Tuple
       [displayLang_String (implode "func");
        displayLang_String (attach_name names (SOME n));
        displayLang_Tuple (REVERSE (list_of_seq display_num_as_varn argc));
        bvl_to_display names argc body]`;;

(* bvi *)

(* HOL4 exp2_size (of bvi) is list_size bvi_exp_size *)

let MEM_bvi_exps_size = prove
 (`!exps e. MEM e exps ==> bvi_exp_size e < list_size bvi_exp_size exps`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; list_size] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY ARITH_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `e:bvi_exp`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let bvi_to_display_def = sem1aux_def_wf
  `MEASURE (\x:(mlstring spt # num # bvi_exp) +
               (mlstring spt # num # bvi_exp list) +
               (mlstring spt # num # num # bvi_exp list).
     sum_CASE x (\p. bvi_exp_size (SND (SND p)))
       (\y. sum_CASE y (\p. list_size bvi_exp_size (SND (SND p)))
              (\p. list_size bvi_exp_size (SND (SND (SND p))))))`
  SEM1AUX_TC_TAC
  `(bvi_to_display ns h (bvi_Var n) =
      Item NONE (implode "var") [display_num_as_varn ((h - n) - 1)]) /\
   (bvi_to_display ns h (bvi_If x1 x2 x3) =
      Item NONE (implode "if")
        [bvi_to_display ns h x1; bvi_to_display ns h x2; bvi_to_display ns h x3]) /\
   (bvi_to_display ns h (bvi_Let xs x) =
      separate_lines (implode "let")
        (APPEND (bvi_to_display_lets ns h (LENGTH xs - 1) xs)
                [bvi_to_display ns (h + LENGTH xs) x])) /\
   (bvi_to_display ns h (bvi_Raise x) =
      Item NONE (implode "raise") [bvi_to_display ns h x]) /\
   (bvi_to_display ns h (bvi_Tick x) =
      Item NONE (implode "tick") [bvi_to_display ns h x]) /\
   (bvi_to_display ns h (bvi_Call ticks dest xs handler) =
      Item NONE (implode "call")
        (APPEND (CONS (displayLang_String (attach_name ns dest))
                      (bvi_to_display_list ns h xs))
                (match handler with
                   NONE -> []
                 | SOME e -> [Item NONE (implode "handler")
                                [display_num_as_varn h;
                                 empty_item (implode "->");
                                 bvi_to_display ns (h + 1) e]]))) /\
   (bvi_to_display ns h (bvi_Force loc n) =
      Item NONE (implode "force")
        [display_num_as_varn ((h - n) - 1);
         displayLang_String (attach_name ns (SOME loc))]) /\
   (bvi_to_display ns h (bvi_Op opn xs) =
      Item NONE (implode "op")
        (CONS (clos_op_to_display ns opn) (bvi_to_display_list ns h xs))) /\
   (bvi_to_display ns h (bvi_Return xs) =
      Item NONE (implode "return") (bvi_to_display_list ns h xs)) /\
   (bvi_to_display ns h (LetCall rets ticks ldest xs y) =
      separate_lines (implode "letcall")
        [Item NONE (implode "call")
           (CONS (displayLang_String (attach_name ns (SOME ldest)))
                 (bvi_to_display_list ns h xs));
         displayLang_Tuple (REVERSE (list_of_seq (\i. display_num_as_varn (h + i)) rets));
         bvi_to_display ns (h + rets) y]) /\
   (bvi_to_display_list ns h [] = []) /\
   (bvi_to_display_list ns h (CONS x xs) =
      CONS (bvi_to_display ns h x) (bvi_to_display_list ns h xs)) /\
   (bvi_to_display_lets ns h i [] = []) /\
   (bvi_to_display_lets ns h i (CONS x xs) =
      CONS (displayLang_Tuple [display_num_as_varn (h + i);
                               displayLang_String (implode "<-");
                               bvi_to_display ns h x])
           (bvi_to_display_lets ns h (i - 1) xs))`;;

let bvi_to_display_ind = cake_ind "bvi_to_display";;

let bvi_fun_to_display_def = cake_def
  `bvi_fun_to_display names (n,argc,body) =
     displayLang_Tuple
       [displayLang_String (implode "func");
        displayLang_String (attach_name names (SOME n));
        displayLang_Tuple (REVERSE (list_of_seq display_num_as_varn argc));
        bvi_to_display names argc body]`;;

(* data *)

let num_set_to_display_def = cake_def
  `num_set_to_display (ns:num_set) =
     displayLang_String
       (mlstring_concat [implode "{";
                         presLang_commas (MAP num_to_str (MAP FST (toSortedAList ns)));
                         implode "}"])`;;

let data_seqs_def = cake_def
  `data_seqs z =
     match z with
       data_Seq x y -> misc_Append (data_seqs x) (data_seqs y)
     | _ -> misc_List [z]`;;

(* induction over one type of a nested datatype: the other predicates of the *)
(* induction theorem are instantiated with \x. T                              *)

let IL1AUX_NESTED_INDUCT_TAC (ind:thm) : tactic = fun (asl,w as g) ->
  let x,body = dest_forall w in
  let p = mk_abs(x,body) in
  let ps = fst(strip_forall(concl ind)) in
  let ip = inst (type_match (type_of (hd ps)) (type_of p) []) in
  let insts = p :: map (fun v -> let v' = ip v in
                          mk_abs(mk_var("x",fst(dest_fun_ty(type_of v'))),`T`))
                       (tl ps) in
  MATCH_MP_TAC (REWRITE_RULE[] (ISPECL insts ind)) g;;

(* unfold f x = ... (the definition def) only where x is not a variable *)

let IL1AUX_UNFOLD_CONS_CONV (def:thm) : conv =
  let f = fst(strip_comb(lhs(snd(strip_forall(concl def))))) in
  ONCE_DEPTH_CONV (fun t ->
    if is_comb t && rator t = f && not (is_var (rand t)) then REWR_CONV def t
    else failwith "IL1AUX_UNFOLD_CONS_CONV");;

let MEM_append_data_seqs = prove
 (`!x. MEM a (append (data_seqs x)) ==> data_prog_size a <= data_prog_size x`,
  IL1AUX_NESTED_INDUCT_TAC data_prog_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  CONV_TAC (IL1AUX_UNFOLD_CONS_CONV data_seqs_def) THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[append_thm; MEM; MEM_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN
  REWRITE_TAC[type_size_def "data_prog"] THEN RES_TAC THEN ASM_ARITH_TAC);;

let list_size_append_data_seqs = prove
 (`!x. list_size data_prog_size (append (data_seqs x)) = data_prog_size x + 1`,
  IL1AUX_NESTED_INDUCT_TAC data_prog_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  CONV_TAC (IL1AUX_UNFOLD_CONS_CONV data_seqs_def) THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[append_thm; list_size; list_size_append] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[type_size_def "data_prog"] THEN ARITH_TAC);;

let data_prog_to_display_def = sem1aux_def_wf
  `MEASURE (\x:(num # mlstring spt # data_prog) + (num # mlstring spt # data_prog list).
              sum_CASE x (\p. FST p) (\p. FST p))`
  SEM1AUX_TC_TAC
  `(data_prog_to_display 0 ns prog = empty_item (implode "...")) /\
   (data_prog_to_display (SUC k) ns prog =
      match prog with
        data_Skip -> empty_item (implode "skip")
      | data_Move x y ->
          displayLang_Tuple
            [num_to_display x; displayLang_String (implode ":="); num_to_display y]
      | data_Call rets target args NONE ->
          Item NONE (implode "call")
            [(match rets with
                NONE -> empty_item (implode "none")
              | SOME opt' -> Item NONE (implode "some")
                  [(\(x, y). displayLang_Tuple
                       [displayLang_Tuple (MAP num_to_display x);
                        num_set_to_display y]) opt']);
             displayLang_String (attach_name ns target);
             displayLang_Tuple (MAP num_to_display args);
             empty_item (implode "none")]
      | data_Call rets target args (SOME (v, handler)) ->
          Item NONE (implode "call")
            [(match rets with
                NONE -> empty_item (implode "none")
              | SOME opt' -> Item NONE (implode "some")
                  [(\(x, y). displayLang_Tuple
                       [displayLang_Tuple (MAP num_to_display x);
                        num_set_to_display y]) opt']);
             displayLang_String (attach_name ns target);
             displayLang_Tuple (MAP num_to_display args);
             Item NONE (implode "some")
               [displayLang_Tuple [num_to_display v;
                                   data_prog_to_display k ns handler]]]
      | data_Force ret loc src ->
          Item NONE (implode "force")
            [(match ret with
                NONE -> empty_item (implode "none")
              | SOME opt' -> Item NONE (implode "some")
                  [(\(x, y). displayLang_Tuple [num_to_display x; num_set_to_display y])
                     opt']);
             num_to_display loc;
             num_to_display src]
      | data_Assign n opn args n_set ->
          displayLang_Tuple
            [num_to_display n;
             displayLang_String (implode ":=");
             clos_op_to_display ns opn;
             displayLang_Tuple (MAP num_to_display args);
             (match n_set with
                NONE -> empty_item (implode "none")
              | SOME opt' -> Item NONE (implode "some") [num_set_to_display opt'])]
      | data_Seq x y ->
          (let xs = append (misc_Append (data_seqs x) (data_seqs y)) in
           separate_lines (implode "seq") (data_prog_to_display_list k ns xs))
      | data_If n x y ->
          Item NONE (implode "if")
            [num_to_display n; data_prog_to_display k ns x; data_prog_to_display k ns y]
      | MakeSpace n nset ->
          Item NONE (implode "make_space") [num_to_display n; num_set_to_display nset]
      | data_Raise n -> Item NONE (implode "raise") [num_to_display n]
      | data_Return rs ->
          Item NONE (implode "return") [displayLang_Tuple (MAP num_to_display rs)]
      | data_Tick -> empty_item (implode "tick")) /\
   (data_prog_to_display_list k ns [] = []) /\
   (data_prog_to_display_list k ns (CONS x xs) =
      match k with
        0 -> []
      | SUC k1 ->
          CONS (data_prog_to_display k1 ns x) (data_prog_to_display_list k1 ns xs))`;;

let data_prog_to_display_ind = cake_ind "data_prog_to_display";;

let data_fun_to_display_def = cake_def
  `data_fun_to_display names (n,argc,body) =
     displayLang_Tuple
       [displayLang_String (implode "func");
        displayLang_String (attach_name names (SOME n));
        displayLang_Tuple (list_of_seq num_to_display argc);
        data_prog_to_display 1000000000 names body]`;;

(* asm *)

let asm_binop_to_display_def = cake_def
  `asm_binop_to_display opn =
     match opn with
       asm_Add -> empty_item (implode "Add")
     | asm_Sub -> empty_item (implode "Sub")
     | asm_And -> empty_item (implode "And")
     | asm_Or -> empty_item (implode "Or")
     | asm_Xor -> empty_item (implode "Xor")`;;

let asm_reg_imm_to_display_def = cake_def
  `asm_reg_imm_to_display (reg_imm:(A)reg_imm) =
     match reg_imm with
       Reg reg -> item_with_num (implode "Reg") reg
     | Imm imm -> item_with_word (implode "Imm") imm`;;

let asm_arith_to_display_def = cake_def
  `asm_arith_to_display (opn:(A)asm_arith) =
     match opn with
       Binop bop n1 n2 reg_imm ->
         Item NONE (implode "Binop")
           [asm_binop_to_display bop; num_to_display n1; num_to_display n2;
            asm_reg_imm_to_display reg_imm]
     | asm_Shift sh n1 n2 n3 ->
         Item NONE (implode "Shift")
           [shift_to_display sh; num_to_display n1; num_to_display n2;
            asm_reg_imm_to_display n3]
     | asm_Div n1 n2 n3 -> item_with_nums (implode "Div") [n1; n2; n3]
     | LongMul n1 n2 n3 n4 -> item_with_nums (implode "LongMul") [n1; n2; n3; n4]
     | LongDiv n1 n2 n3 n4 n5 ->
         item_with_nums (implode "LongDiv") [n1; n2; n3; n4; n5]
     | asm_AddCarry n1 n2 n3 n4 -> item_with_nums (implode "AddCarry") [n1; n2; n3; n4]
     | AddOverflow n1 n2 n3 n4 ->
         item_with_nums (implode "AddOverflow") [n1; n2; n3; n4]
     | SubOverflow n1 n2 n3 n4 ->
         item_with_nums (implode "SubOverflow") [n1; n2; n3; n4]`;;

let asm_addr_to_display_def = cake_def
  `asm_addr_to_display (addr:(A)addr) =
     match addr with
       Addr reg w -> Item NONE (implode "Addr") [num_to_display reg; word_to_display w]`;;

let asm_memop_to_display_def = cake_def
  `asm_memop_to_display opn =
     match opn with
       asm_Load -> empty_item (implode "Load")
     | Load8 -> empty_item (implode "Load8")
     | Load16 -> empty_item (implode "Load16")
     | asm_Load32 -> empty_item (implode "Load32")
     | asm_Store -> empty_item (implode "Store")
     | Store8 -> empty_item (implode "Store8")
     | Store16 -> empty_item (implode "Store16")
     | asm_Store32 -> empty_item (implode "Store32")`;;

let asm_cmp_to_display_def = cake_def
  `asm_cmp_to_display opn =
     match opn with
       asm_Equal -> empty_item (implode "Equal")
     | Lower -> empty_item (implode "Lower")
     | asm_Less -> empty_item (implode "Less")
     | asm_Test -> empty_item (implode "Test")
     | NotEqual -> empty_item (implode "NotEqual")
     | NotLower -> empty_item (implode "NotLower")
     | NotLess -> empty_item (implode "NotLess")
     | NotTest -> empty_item (implode "NotTest")`;;

let asm_fp_to_display_def = cake_def
  `asm_fp_to_display opn =
     match opn with
       FPLess n1 n2 n3 -> item_with_nums (implode "FPLess") [n1; n2; n3]
     | FPLessEqual n1 n2 n3 -> item_with_nums (implode "FPLessEqual") [n1; n2; n3]
     | FPEqual n1 n2 n3 -> item_with_nums (implode "FPEqual") [n1; n2; n3]
     | FPAbs n1 n2 -> item_with_nums (implode "FPAbs") [n1; n2]
     | FPNeg n1 n2 -> item_with_nums (implode "FPNeg") [n1; n2]
     | FPSqrt n1 n2 -> item_with_nums (implode "FPSqrt") [n1; n2]
     | FPAdd n1 n2 n3 -> item_with_nums (implode "FPAdd") [n1; n2; n3]
     | FPSub n1 n2 n3 -> item_with_nums (implode "FPSub") [n1; n2; n3]
     | FPMul n1 n2 n3 -> item_with_nums (implode "FPMul") [n1; n2; n3]
     | FPDiv n1 n2 n3 -> item_with_nums (implode "FPDiv") [n1; n2; n3]
     | FPFma n1 n2 n3 -> item_with_nums (implode "FPFma") [n1; n2; n3]
     | FPMov n1 n2 -> item_with_nums (implode "FPMov") [n1; n2]
     | FPMovToReg n1 n2 n3 -> item_with_nums (implode "FPMovToReg") [n1; n2; n3]
     | FPMovFromReg n1 n2 n3 -> item_with_nums (implode "FPMovFromReg") [n1; n2; n3]
     | FPToInt n1 n2 -> item_with_nums (implode "FPToInt") [n1; n2]
     | FPFromInt n1 n2 -> item_with_nums (implode "FPFromInt") [n1; n2]`;;

let asm_inst_to_display_def = cake_def
  `asm_inst_to_display (inst:(A)inst) =
     match inst with
       asm_Skip -> empty_item (implode "Skip")
     | asm_Const reg w ->
         Item NONE (implode "Const") [num_to_display reg; word_to_display w]
     | asm_Arith a -> Item NONE (implode "Arith") [asm_arith_to_display a]
     | Mem mop r addr ->
         Item NONE (implode "Mem")
           [asm_memop_to_display mop; num_to_display r; asm_addr_to_display addr]
     | FP fpop -> Item NONE (implode "FP") [asm_fp_to_display fpop]`;;

let asm_asm_to_display_def = cake_def
  `asm_asm_to_display (inst:(A)asm) =
     match inst with
       asm_Inst i -> asm_inst_to_display i
     | asm_Jump w -> item_with_word (implode "Jump") w
     | asm_JumpCmp c r rto w ->
         Item NONE (implode "JumpCmp")
           [asm_cmp_to_display c; num_to_display r; asm_reg_imm_to_display rto;
            word_to_display w]
     | asm_Call w -> item_with_word (implode "Call") w
     | JumpReg r -> item_with_num (implode "JumpReg>") r
     | asm_Loc r w -> Item NONE (implode "Loc") [num_to_display r; word_to_display w]`;;

(* stack *)

let store_name_to_display_def = cake_def
  `store_name_to_display st =
     match st with
       NextFree -> empty_item (implode "NextFree")
     | EndOfHeap -> empty_item (implode "EndOfHeap")
     | TriggerGC -> empty_item (implode "TriggerGC")
     | HeapLength -> empty_item (implode "HeapLength")
     | ProgStart -> empty_item (implode "ProgStart")
     | BitmapBase -> empty_item (implode "BitmapBase")
     | CurrHeap -> empty_item (implode "CurrHeap")
     | OtherHeap -> empty_item (implode "OtherHeap")
     | AllocSize -> empty_item (implode "AllocSize")
     | Globals -> empty_item (implode "Globals")
     | GlobReal -> empty_item (implode "GlobReal")
     | Handler -> empty_item (implode "Handler")
     | GenStart -> empty_item (implode "GenStart")
     | CodeBuffer -> empty_item (implode "CodeBuffer")
     | CodeBufferEnd -> empty_item (implode "CodeBufferEnd")
     | BitmapBuffer -> empty_item (implode "BitmapBuffer")
     | BitmapBufferEnd -> empty_item (implode "BitmapBufferEnd")
     | Temp w -> item_with_word (implode "Temp") w`;;

let stack_seqs_def = cake_def
  `stack_seqs (z:(A)stack_prog) =
     match z with
       stack_Seq x y -> misc_Append (stack_seqs x) (stack_seqs y)
     | _ -> misc_List [z]`;;

let MEM_append_stack_seqs = prove
 (`!x:(A)stack_prog. MEM a (append (stack_seqs x)) ==>
                     stack_prog_size ARB a <= stack_prog_size ARB x`,
  IL1AUX_NESTED_INDUCT_TAC stack_prog_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  CONV_TAC (IL1AUX_UNFOLD_CONS_CONV stack_seqs_def) THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[append_thm; MEM; MEM_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN
  REWRITE_TAC[type_size_def "stack_prog"] THEN RES_TAC THEN ASM_ARITH_TAC);;

let list_size_append_stack_seqs = prove
 (`!x:(A)stack_prog.
     list_size (stack_prog_size ARB) (append (stack_seqs x)) =
     stack_prog_size ARB x + 1`,
  IL1AUX_NESTED_INDUCT_TAC stack_prog_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  CONV_TAC (IL1AUX_UNFOLD_CONS_CONV stack_seqs_def) THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[append_thm; list_size; list_size_append] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[type_size_def "stack_prog"] THEN ARITH_TAC);;

let stack_prog_to_display_def = sem1aux_def_wf
  `MEASURE (\x:(num # mlstring spt # (A)stack_prog) +
               (num # mlstring spt # ((A)stack_prog) list).
              sum_CASE x (\p. FST p) (\p. FST p))`
  SEM1AUX_TC_TAC
  `(stack_prog_to_display 0 ns (prog:(A)stack_prog) = empty_item (implode "...")) /\
   (stack_prog_to_display (SUC k) ns stack_Skip = empty_item (implode "skip")) /\
   (stack_prog_to_display (SUC k) ns (stack_Inst i) = asm_inst_to_display i) /\
   (stack_prog_to_display (SUC k) ns (stack_Get n sn) =
      displayLang_Tuple
        [num_to_display n; displayLang_String (implode "<-"); store_name_to_display sn]) /\
   (stack_prog_to_display (SUC k) ns (stack_Set sn n) =
      displayLang_Tuple
        [store_name_to_display sn; displayLang_String (implode "<-"); num_to_display n]) /\
   (stack_prog_to_display (SUC k) ns (stack_OpCurrHeap b n1 n2) =
      displayLang_Tuple
        [num_to_display n1; displayLang_String (implode ":=");
         displayLang_String (implode "CurrHeap");
         asm_binop_to_display b; num_to_display n2]) /\
   (stack_prog_to_display (SUC k) ns (stack_Call rh tgt eh) =
      Item NONE (implode "call")
        [(match rh with
            NONE -> empty_item (implode "tail")
          | SOME (p,lr,l1,l2) ->
              Item NONE (implode "returning")
                [num_to_display lr;
                 displayLang_String (attach_name ns (SOME l1));
                 num_to_display l2;
                 stack_prog_to_display k ns p]);
         (match tgt with
            INL l -> Item NONE (implode "direct")
                       [displayLang_String (attach_name ns (SOME l))]
          | INR r -> item_with_num (implode "reg") r);
         (match eh with
            NONE -> empty_item (implode "no_handler")
          | SOME (p,l1,l2) ->
              Item NONE (implode "handler")
                [displayLang_String (attach_name ns (SOME l1));
                 num_to_display l2;
                 stack_prog_to_display k ns p])]) /\
   (stack_prog_to_display (SUC k) ns (stack_Seq x y) =
      (let xs = append (misc_Append (stack_seqs x) (stack_seqs y)) in
       separate_lines (implode "seq") (stack_prog_to_display_list k ns xs))) /\
   (stack_prog_to_display (SUC k) ns (stack_If c n rto x y) =
      Item NONE (implode "if")
        [displayLang_Tuple [asm_cmp_to_display c; num_to_display n;
                            asm_reg_imm_to_display rto];
         stack_prog_to_display k ns x;
         stack_prog_to_display k ns y]) /\
   (stack_prog_to_display (SUC k) ns (stack_Loop x) =
      Item NONE (implode "loop") [stack_prog_to_display k ns x]) /\
   (stack_prog_to_display (SUC k) ns (JumpLower n1 n2 n3) =
      item_with_nums (implode "jump_lower") [n1; n2; n3]) /\
   (stack_prog_to_display (SUC k) ns (stack_Alloc n) =
      item_with_num (implode "alloc") n) /\
   (stack_prog_to_display (SUC k) ns (stack_StoreConsts n1 n2 _) =
      item_with_nums (implode "store_consts") [n1; n2]) /\
   (stack_prog_to_display (SUC k) ns (stack_Raise n) =
      item_with_num (implode "raise") n) /\
   (stack_prog_to_display (SUC k) ns (stack_Return n) =
      item_with_num (implode "return") n) /\
   (stack_prog_to_display (SUC k) ns (stack_Break n) =
      item_with_num (implode "break") n) /\
   (stack_prog_to_display (SUC k) ns (stack_Continue n) =
      item_with_num (implode "continue") n) /\
   (stack_prog_to_display (SUC k) ns (stack_FFI nm cp cl ap al ra) =
      Item NONE (implode "ffi")
        (CONS (string_imp nm) (MAP num_to_display [cp; cl; ap; al; ra]))) /\
   (stack_prog_to_display (SUC k) ns stack_Tick = empty_item (implode "tick")) /\
   (stack_prog_to_display (SUC k) ns (stack_LocValue n1 n2 n3) =
      Item NONE (implode "loc_value")
        [num_to_display n1; displayLang_String (attach_name ns (SOME n2));
         num_to_display n3]) /\
   (stack_prog_to_display (SUC k) ns (stack_Install n1 n2 n3 n4 n5) =
      item_with_nums (implode "install") [n1; n2; n3; n4; n5]) /\
   (stack_prog_to_display (SUC k) ns (ShMemOp mop r a) =
      Item NONE (implode "sh_mem")
        [asm_memop_to_display mop; num_to_display r; asm_addr_to_display a]) /\
   (stack_prog_to_display (SUC k) ns (stack_CodeBufferWrite n1 n2) =
      item_with_nums (implode "code_buffer_write") [n1; n2]) /\
   (stack_prog_to_display (SUC k) ns (stack_DataBufferWrite n1 n2) =
      item_with_nums (implode "data_buffer_write") [n1; n2]) /\
   (stack_prog_to_display (SUC k) ns (RawCall n) =
      Item NONE (implode "raw_call") [displayLang_String (attach_name ns (SOME n))]) /\
   (stack_prog_to_display (SUC k) ns (StackAlloc n) =
      item_with_num (implode "stack_alloc") n) /\
   (stack_prog_to_display (SUC k) ns (StackFree n) =
      item_with_num (implode "stack_free") n) /\
   (stack_prog_to_display (SUC k) ns (StackStore n m) =
      displayLang_Tuple
        [displayLang_String
           (strcat (strcat (strcat (implode "stack[") (num_to_hex_mlstring n))
                           (implode "] := ")) (num_to_str m))]) /\
   (stack_prog_to_display (SUC k) ns (StackStoreAny n m) =
      displayLang_Tuple
        [displayLang_String
           (strcat (strcat (strcat (implode "stack[var ") (num_to_str n))
                           (implode "] := ")) (num_to_str m))]) /\
   (stack_prog_to_display (SUC k) ns (StackLoad n m) =
      displayLang_Tuple
        [displayLang_String
           (mlstring_concat [num_to_str n; implode " := stack[";
                             num_to_hex_mlstring m; implode "]"])]) /\
   (stack_prog_to_display (SUC k) ns (StackLoadAny n m) =
      displayLang_Tuple
        [displayLang_String
           (mlstring_concat [num_to_str n; implode " := stack[var ";
                             num_to_str m; implode "]"])]) /\
   (stack_prog_to_display (SUC k) ns (StackGetSize n) =
      item_with_num (implode "stack_get_size") n) /\
   (stack_prog_to_display (SUC k) ns (StackSetSize n) =
      item_with_num (implode "stack_set_size") n) /\
   (stack_prog_to_display (SUC k) ns (BitmapLoad n m) =
      displayLang_Tuple
        [displayLang_String
           (mlstring_concat [num_to_str n; implode " := bitmap[";
                             num_to_hex_mlstring m; implode "]"])]) /\
   (stack_prog_to_display (SUC k) ns (stack_Halt n) =
      item_with_num (implode "halt") n) /\
   (stack_prog_to_display_list k ns [] = []) /\
   (stack_prog_to_display_list k ns (CONS x xs) =
      match k with
        0 -> []
      | SUC k1 ->
          CONS (stack_prog_to_display k1 ns x) (stack_prog_to_display_list k1 ns xs))`;;

let stack_prog_to_display_ind = cake_ind "stack_prog_to_display";;

let stack_fun_to_display_def = cake_def
  `stack_fun_to_display names (n,body:(A)stack_prog) =
     displayLang_Tuple
       [displayLang_String (implode "func");
        displayLang_String (attach_name names (SOME n));
        stack_prog_to_display 1000000000 names body]`;;

(* lab *)

let lab_asm_to_display_def = cake_def
  `lab_asm_to_display ns (la:(A)asm_with_lab) =
     match la with
       lab_Jump (lab_Lab s n) ->
         Item NONE (implode "jump")
           [displayLang_String (attach_name ns (SOME s)); num_to_display n]
     | lab_JumpCmp c r ri (lab_Lab s n) ->
         Item NONE (implode "jump_cmp")
           [displayLang_Tuple [asm_cmp_to_display c; num_to_display r;
                               asm_reg_imm_to_display ri];
            displayLang_String (attach_name ns (SOME s)); num_to_display n]
     | lab_Call (lab_Lab s n) ->
         Item NONE (implode "call")
           [displayLang_String (attach_name ns (SOME s)); num_to_display n]
     | lab_LocValue r (lab_Lab s n) ->
         Item NONE (implode "loc_value")
           [num_to_display r; displayLang_String (attach_name ns (SOME s));
            num_to_display n]
     | CallFFI name -> Item NONE (implode "call_FFI") [string_imp name]
     | lab_Install -> empty_item (implode "install")
     | lab_Halt -> empty_item (implode "halt")`;;

let lab_line_to_display_def = cake_def
  `lab_line_to_display ns (line:(A)line) =
     match line with
       lab_Label s n le ->
         Item NONE (implode "label")
           [displayLang_String (attach_name ns (SOME s)); num_to_display n]
     | Asm aoc enc len ->
         (match aoc with
            Asmi i -> Item NONE (implode "asm") [asm_asm_to_display i]
          | Cbw r1 r2 -> item_with_nums (implode "cbw") [r1; r2]
          | ShareMem mop r a ->
              Item NONE (implode "share_mem")
                [asm_memop_to_display mop; num_to_display r; asm_addr_to_display a])
     | LabAsm la pos enc len -> lab_asm_to_display ns la`;;

let lab_fun_to_display_def = cake_def
  `lab_fun_to_display names (Section n (lines:((A)line)list)) =
     displayLang_List
       (CONS (displayLang_String (attach_name names (SOME n)))
             (MAP (lab_line_to_display names) lines))`;;

(* word *)

let word_seqs_def = cake_def
  `word_seqs (z:(A)wl_prog) =
     match z with
       wl_Seq x y -> misc_Append (word_seqs x) (word_seqs y)
     | _ -> misc_List [z]`;;

let MEM_append_word_seqs = prove
 (`!x:(A)wl_prog. MEM a (append (word_seqs x)) ==>
                  wl_prog_size ARB a <= wl_prog_size ARB x`,
  IL1AUX_NESTED_INDUCT_TAC wl_prog_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  CONV_TAC (IL1AUX_UNFOLD_CONS_CONV word_seqs_def) THEN CAKE_REWRITE_TAC[] THEN
  REWRITE_TAC[append_thm; MEM; MEM_APPEND] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN
  REWRITE_TAC[type_size_def "wl_prog"] THEN RES_TAC THEN ASM_ARITH_TAC);;

(* HOL4: MEM_IMP_exp_size |> Q.GEN `l` |> Q.SPEC `ARB` *)

let MEM_word_exps_size_ARB =
  INST [`ARB:A->num`,`l:A->num`] wl_MEM_IMP_exp_size;;

let word_exp_to_display_def = sem1aux_def_wf
  `MEASURE (\x:(A)wl_exp + ((A)wl_exp) list.
              sum_CASE x (\v. wl_exp_size ARB v) (\v. list_size (wl_exp_size ARB) v))`
  SEM1AUX_TC_TAC
  `(word_exp_to_display (wl_Const (v:A word)) = item_with_word (implode "Const") v) /\
   (word_exp_to_display (wl_Var n) = item_with_num (implode "Var") n) /\
   (word_exp_to_display (Lookup st) =
      Item NONE (implode "Lookup") [store_name_to_display st]) /\
   (word_exp_to_display (wl_Load exp2) =
      Item NONE (implode "MemLoad") [word_exp_to_display exp2]) /\
   (word_exp_to_display (wl_Op bop exs) =
      Item NONE (implode "Op")
        (CONS (asm_binop_to_display bop) (word_exp_to_display_list exs))) /\
   (word_exp_to_display (wl_Shift sh exp exp1) =
      Item NONE (implode "Shift")
        [shift_to_display sh; word_exp_to_display exp; word_exp_to_display exp1]) /\
   (word_exp_to_display_list [] = []) /\
   (word_exp_to_display_list (CONS x xs) =
      CONS (word_exp_to_display x) (word_exp_to_display_list xs))`;;

let word_exp_to_display_ind = cake_ind "word_exp_to_display";;

let ws_to_display_def = cake_def
  `(ws_to_display [] = []) /\
   (ws_to_display (CONS (b,x:A word) xs) =
      CONS (displayLang_Tuple [bool_to_display b; word_to_display x])
           (ws_to_display xs))`;;

let num_sets_to_display_def = cake_def
  `num_sets_to_display (l,r) =
     displayLang_Tuple [num_set_to_display l; num_set_to_display r]`;;

let word_prog_to_display_def = sem1aux_def_wf
  `MEASURE (\x:(num # mlstring spt # (A)wl_prog) +
               (num # mlstring spt # ((A)wl_prog) list) +
               (num # mlstring spt #
                (num list # cutsets # (A)wl_prog # num # num) option) +
               (num # mlstring spt # (num # (A)wl_prog # num # num) option).
     sum_CASE x (\p. FST p)
       (\y. sum_CASE y (\p. FST p) (\z. sum_CASE z (\p. FST p) (\p. FST p))))`
  SEM1AUX_TC_TAC
  `(word_prog_to_display 0 ns (x:(A)wl_prog) = empty_item (implode "...")) /\
   (word_prog_to_display (SUC k) ns wl_Skip = empty_item (implode "skip")) /\
   (word_prog_to_display (SUC k) ns (wl_Move n mvs) =
      Item NONE (implode "move")
        [num_to_display n;
         displayLang_Tuple
           (MAP (\(n1, n2). displayLang_Tuple
                   [num_to_display n1; displayLang_String (implode ":=");
                    num_to_display n2]) mvs)]) /\
   (word_prog_to_display (SUC k) ns (wl_Inst i) =
      Item NONE (implode "inst") [asm_inst_to_display i]) /\
   (word_prog_to_display (SUC k) ns (wl_Assign n exp) =
      displayLang_Tuple
        [num_to_display n; displayLang_String (implode ":=");
         word_exp_to_display exp]) /\
   (word_prog_to_display (SUC k) ns (wl_Get n sn) =
      displayLang_Tuple
        [num_to_display n; displayLang_String (implode "<-");
         store_name_to_display sn]) /\
   (word_prog_to_display (SUC k) ns (wl_Set sn exp) =
      displayLang_Tuple
        [store_name_to_display sn; displayLang_String (implode "<-");
         word_exp_to_display exp]) /\
   (word_prog_to_display (SUC k) ns (wl_Store exp n) =
      displayLang_Tuple
        [displayLang_String (implode "mem"); word_exp_to_display exp;
         displayLang_String (implode ":="); num_to_display n]) /\
   (word_prog_to_display (SUC k) ns (ShareInst mop n exp) =
      displayLang_Tuple
        [displayLang_String (implode "share_mem"); asm_memop_to_display mop;
         num_to_display n; word_exp_to_display exp]) /\
   (word_prog_to_display (SUC k) ns (MustTerminate prog) =
      Item NONE (implode "must_terminate") [word_prog_to_display k ns prog]) /\
   (word_prog_to_display (SUC k) ns (wl_Call ca cb cc cd) =
      Item NONE (implode "call")
        [word_prog_to_display_ret k ns ca;
         (match cb with
            NONE -> empty_item (implode "none")
          | SOME opt' -> Item NONE (implode "some")
                           [displayLang_String (attach_name ns (SOME opt'))]);
         displayLang_Tuple (MAP num_to_display cc);
         word_prog_to_display_handler k ns cd]) /\
   (word_prog_to_display (SUC k) ns (wl_OpCurrHeap bop n1 n2) =
      displayLang_Tuple
        [num_to_display n1; displayLang_String (implode ":=");
         displayLang_String (implode "CurrHeap");
         asm_binop_to_display bop; num_to_display n2]) /\
   (word_prog_to_display (SUC k) ns (wl_Seq prog1 prog2) =
      (let xs = append (misc_Append (word_seqs prog1) (word_seqs prog2)) in
       separate_lines (implode "seq") (word_prog_to_display_list k ns xs))) /\
   (word_prog_to_display (SUC k) ns (wl_If cmp n reg p1 p2) =
      Item NONE (implode "if")
        [displayLang_Tuple [asm_cmp_to_display cmp; num_to_display n;
                            asm_reg_imm_to_display reg];
         word_prog_to_display k ns p1; word_prog_to_display k ns p2]) /\
   (word_prog_to_display (SUC k) ns (wl_Loop ns1 p ns2) =
      Item NONE (implode "Loop")
        [num_set_to_display ns1; word_prog_to_display k ns p;
         num_set_to_display ns2]) /\
   (word_prog_to_display (SUC k) ns (wl_Alloc n ms) =
      Item NONE (implode "alloc") [num_to_display n; num_sets_to_display ms]) /\
   (word_prog_to_display (SUC k) ns (wl_StoreConsts sa sb sc sd ws) =
      Item NONE (implode "store_consts")
        [num_to_display sa; num_to_display sb; num_to_display sc; num_to_display sd;
         displayLang_Tuple (ws_to_display ws)]) /\
   (word_prog_to_display (SUC k) ns (wl_Raise n) = item_with_num (implode "raise") n) /\
   (word_prog_to_display (SUC k) ns (wl_Break n) = item_with_num (implode "break") n) /\
   (word_prog_to_display (SUC k) ns (wl_Continue n) =
      item_with_num (implode "continue") n) /\
   (word_prog_to_display (SUC k) ns (wl_Return n vs) =
      Item NONE (implode "return")
        [num_to_display n; displayLang_Tuple (MAP num_to_display vs)]) /\
   (word_prog_to_display (SUC k) ns wl_Tick = empty_item (implode "tick")) /\
   (word_prog_to_display (SUC k) ns (wl_LocValue n1 n2) =
      Item NONE (implode "loc_value")
        [displayLang_String (attach_name ns (SOME n1)); num_to_display n2]) /\
   (word_prog_to_display (SUC k) ns (wl_Install n1 n2 n3 n4 ms) =
      Item NONE (implode "install")
        (APPEND (MAP num_to_display [n1; n2; n3; n4]) [num_sets_to_display ms])) /\
   (word_prog_to_display (SUC k) ns (wl_CodeBufferWrite n1 n2) =
      item_with_nums (implode "code_buffer_write") [n1; n2]) /\
   (word_prog_to_display (SUC k) ns (wl_DataBufferWrite n1 n2) =
      item_with_nums (implode "data_buffer_write") [n1; n2]) /\
   (word_prog_to_display (SUC k) ns (wl_FFI nm n1 n2 n3 n4 ms) =
      Item NONE (implode "ffi")
        (APPEND (CONS (string_imp nm) (MAP num_to_display [n1; n2; n3; n4]))
                [num_sets_to_display ms])) /\
   (word_prog_to_display_list k ns [] = []) /\
   (word_prog_to_display_list k ns (CONS x xs) =
      match k with
        0 -> []
      | SUC k1 ->
          CONS (word_prog_to_display k1 ns x) (word_prog_to_display_list k1 ns xs)) /\
   (word_prog_to_display_ret k ns NONE = empty_item (implode "tail")) /\
   (word_prog_to_display_ret k ns (SOME (vs, ms, prog, n2, n3)) =
      match k with
        0 -> empty_item (implode "...")
      | SUC k1 ->
          Item NONE (implode "returning")
            [displayLang_Tuple
               [displayLang_Tuple (MAP num_to_display vs); num_sets_to_display ms;
                word_prog_to_display k1 ns prog;
                displayLang_String (attach_name ns (SOME n2));
                num_to_display n3]]) /\
   (word_prog_to_display_handler k ns NONE = empty_item (implode "no_handler")) /\
   (word_prog_to_display_handler k ns (SOME (n1, prog, n2, n3)) =
      match k with
        0 -> empty_item (implode "...")
      | SUC k1 ->
          Item NONE (implode "handler")
            [displayLang_Tuple
               [num_to_display n1; word_prog_to_display k1 ns prog;
                displayLang_String (attach_name ns (SOME n2));
                num_to_display n3]])`;;

let word_prog_to_display_ind = cake_ind "word_prog_to_display";;

let word_fun_to_display_def = cake_def
  `word_fun_to_display names (n,argc,body:(A)wl_prog) =
     displayLang_Tuple
       [displayLang_String (implode "func");
        displayLang_String (attach_name names (SOME n));
        displayLang_Tuple (list_of_seq (\n. num_to_display (2 * n)) argc);
        word_prog_to_display 1000000000 names body]`;;

(* tap configuration *)

let tap_config_INFO = cake_record "tap_config" ["explore_flag","bool"];;

let default_tap_config_def = cake_def
  `default_tap_config = tap_config_REC F`;;

let map_to_append_def = cake_def
  `(map_to_append (f:A->B list) [] = Nil) /\
   (map_to_append f (CONS x xs) = misc_Append (misc_List (f x)) (map_to_append f xs))`;;

let source_to_strs_def = cake_def
  `source_to_strs decs =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    source_to_display_dec) decs`;;

let flat_to_strs_def = cake_def
  `flat_to_strs (decs:flat_exp list) =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    flat_to_display) decs`;;

let clos_to_strs_def = cake_def
  `clos_to_strs (decs,funs) =
     let names = get_src_names (APPEND decs (MAP (SND o SND) funs)) LN in
     misc_Append
       (map_to_append (str_tree_to_strs (implode "\n\n") o
                       display_to_str_tree o
                       clos_dec_to_display names) decs)
       (map_to_append (str_tree_to_strs (implode "\n\n") o
                       display_to_str_tree o
                       clos_fun_to_display names) funs)`;;

let bvl_to_strs_def = cake_def
  `bvl_to_strs names xs =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    bvl_fun_to_display names) xs`;;

let bvi_to_strs_def = cake_def
  `bvi_to_strs names xs =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    bvi_fun_to_display names) xs`;;

let data_to_strs_def = cake_def
  `data_to_strs names xs =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    data_fun_to_display names) xs`;;

let word_to_strs_def = cake_def
  `word_to_strs names (xs:(num # num # (A)wl_prog) list) =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    word_fun_to_display names) xs`;;

let stack_to_strs_def = cake_def
  `stack_to_strs names (xs:(num # (A)stack_prog) list) =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    stack_fun_to_display names) xs`;;

let lab_to_strs_def = cake_def
  `lab_to_strs names (xs:((A)sec) list) =
     map_to_append (str_tree_to_strs (implode "\n\n") o
                    display_to_str_tree o
                    lab_fun_to_display names) xs`;;
