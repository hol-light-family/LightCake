(* ========================================================================= *)
(* flatLang: port of HOL4 compiler/backend/flatLangScript.sml (CakeML v3479).*)
(* The first intermediate language flatLang. It removes modules and resolves *)
(* all global scoping. Each value definition gets allocated a slot in a      *)
(* global variable store, and each type and exception gets a unique global   *)
(* identifier. It removes andalso and orelse and replaces them with if, and  *)
(* removes the AallocEmpty primitive op and replaces it with an alloc call   *)
(* with 0.                                                                   *)
(*                                                                           *)
(* The AST of flatLang differs from the source language by having two       *)
(* variable reference forms, one to reference local bindings (still by      *)
(* name) and one to reference global bindings (by index). At the top level, *)
(* modules and let recs are gone. Top-level lets and letrecs no longer bind *)
(* names (or have patterns). Constructor names are replaced with numbers,   *)
(* and type and exception definitions record the arities of the             *)
(* constructors rather than the types. Type annotations are also gone.      *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's pmatch case expressions (patternMatchesSyntax) are written with *)
(*   match like every other case expression, so SmartIf_PMATCH is SmartIf's *)
(*   definition again.                                                       *)
(* - HOL4's size functions of the nested types of exp are written as their  *)
(*   list_size / pair_size forms (HOL4's exp_size_eq): exp6_size (on exp     *)
(*   list) is list_size flat_exp_size, exp1_size (on (varN # varN # exp)     *)
(*   list) is list_size (pair_size mlstring_size (pair_size mlstring_size    *)
(*   flat_exp_size)), exp2_size its element size, exp3_size (on (pat # exp)  *)
(*   list) is list_size (pair_size flat_pat_size flat_exp_size) and          *)
(*   exp5_size its element size.                                             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "compiler/backend/backend_common.ml";;

type_invention_error := true;;

(* Most ops are inherited from ast$op via the Src wrapper.  GlobalVar ops,  *)
(* TagLenEq, LenEq, El, and Id are flatLang-specific.  GlobalVarAlloc:      *)
(* allocate the given number of new global variables; GlobalVarInit:        *)
(* initialise given global variable; GlobalVarLookup: get the value of the  *)
(* given global variable; flat_TagLenEq, flat_LenEq, flat_El: for pattern   *)
(* match compilation; Id: no-op step for a single value.                    *)

let flat_op_INDUCT,flat_op_RECURSION = cake_type
  "flat_op = Src op
           | GlobalVarAlloc num
           | GlobalVarInit num
           | GlobalVarLookup num
           | flat_TagLenEq num num
           | flat_LenEq num
           | flat_El num
           | Id";;

new_type_abbrev("ctor_id",`:num`);;

(* NONE represents the exception type *)
new_type_abbrev("type_id",`:num option`);;

new_type_abbrev("type_group_id",`:(num # (ctor_id # num) list) option`);;

let flat_pat_INDUCT,flat_pat_RECURSION = cake_type
  "flat_pat = flat_Pany
            | flat_Pvar varN
            | flat_Plit lit
            | flat_Pcon ((ctor_id # type_group_id) option) (flat_pat list)
            | flat_Pas flat_pat varN
            | flat_Pref flat_pat";;

(* HOL4: pat_bindings, pats_bindings *)

let flat_pat_bindings_def = cake_def
  `(flat_pat_bindings flat_Pany = []) /\
   (flat_pat_bindings (flat_Pvar n) = [n]) /\
   (flat_pat_bindings (flat_Plit l) = []) /\
   (flat_pat_bindings (flat_Pcon _ ps) = flat_pats_bindings ps) /\
   (flat_pat_bindings (flat_Pas p i) = APPEND (flat_pat_bindings p) [i]) /\
   (flat_pat_bindings (flat_Pref p) = flat_pat_bindings p) /\
   (flat_pats_bindings [] = []) /\
   (flat_pats_bindings (CONS p ps) =
      APPEND (flat_pats_bindings ps) (flat_pat_bindings p))`;;

let flat_pat_bindings_ind = cake_ind "flat_pat_bindings";;

let flat_exp_INDUCT,flat_exp_RECURSION = cake_type
  "flat_exp = flat_Raise tra flat_exp
            | flat_Handle tra flat_exp ((flat_pat # flat_exp) list)
            | flat_Lit tra lit
            | flat_Con tra ((ctor_id # type_id) option) (flat_exp list)
            | Var_local tra varN
            | flat_Fun varN varN flat_exp
            | flat_App tra flat_op (flat_exp list)
            | flat_If tra flat_exp flat_exp flat_exp
            | flat_Mat tra flat_exp ((flat_pat # flat_exp) list)
            | flat_Let tra (varN option) flat_exp flat_exp
            | flat_Letrec varN ((varN # varN # flat_exp) list) flat_exp";;

(* HOL4: val exp_size_def = definition "exp_size_def": type_size_def          *)
(* "flat_exp" (with size_aux_eqs "flat_exp" for the nested types)            *)

(* HOL4 exp6_size is list_size flat_exp_size *)

let exp6_size_APPEND = prove
 (`!e e2. list_size flat_exp_size (APPEND e e2) =
          list_size flat_exp_size e + list_size flat_exp_size e2`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; list_size] THEN ARITH_TAC);;

let exp6_size_REVERSE = prove
 (`!es. list_size flat_exp_size (REVERSE es) = list_size flat_exp_size es`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REVERSE; exp6_size_APPEND; list_size] THEN ARITH_TAC);;

let _ = cake_add_simps [exp6_size_APPEND; exp6_size_REVERSE];;

let exp6_size = prove
 (`!xs. list_size flat_exp_size xs = LENGTH xs + SUM (MAP flat_exp_size xs)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[list_size; LENGTH; MAP; SUM] THEN
  ARITH_TAC);;

(* HOL4 exp1_size is list_size (pair_size mlstring_size (pair_size           *)
(* mlstring_size flat_exp_size)) and exp2_size its element size              *)

let exp1_size = prove
 (`!xs. list_size (pair_size mlstring_size
                     (pair_size mlstring_size flat_exp_size)) xs =
        LENGTH xs +
        SUM (MAP (pair_size mlstring_size
                    (pair_size mlstring_size flat_exp_size)) xs)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[list_size; LENGTH; MAP; SUM] THEN
  ARITH_TAC);;

(* HOL4 exp3_size is list_size (pair_size flat_pat_size flat_exp_size) and   *)
(* exp5_size its element size                                                *)

let flat_exp3_size = prove
 (`!xs. list_size (pair_size flat_pat_size flat_exp_size) xs =
        LENGTH xs + SUM (MAP (pair_size flat_pat_size flat_exp_size) xs)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[list_size; LENGTH; MAP; SUM] THEN
  ARITH_TAC);;

let exp_size_MAP = prove
 (`(!xs. list_size flat_exp_size (MAP SND xs) <
         list_size (pair_size flat_pat_size flat_exp_size) xs + 1) /\
   (!xs. list_size flat_exp_size (MAP (SND o SND) xs) <
         list_size (pair_size mlstring_size
                      (pair_size mlstring_size flat_exp_size)) xs + 1)`,
  CONJ_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; list_size; pair_size; o_THM] THEN ASM_ARITH_TAC);;

(* HOL4: exp_size_MEM *)

let flat_exp_size_MEM = prove
 (`(!xs x. MEM x xs ==> flat_exp_size x < list_size flat_exp_size xs) /\
   (!xs x. MEM x xs ==>
           flat_exp_size (SND (SND x)) <
           list_size (pair_size mlstring_size
                        (pair_size mlstring_size flat_exp_size)) xs) /\
   (!xs x. MEM x xs ==>
           flat_exp_size (SND x) <
           list_size (pair_size flat_pat_size flat_exp_size) xs)`,
  REPEAT CONJ_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; list_size; pair_size] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN TRY ARITH_TAC THEN RES_TAC THEN ASM_ARITH_TAC);;

let bool_id_def = cake_def
  `bool_id = 0:num`;;

(* HOL4: Bool *)

let flat_Bool_def = cake_def
  `flat_Bool t b = flat_Con t (SOME (bool_to_tag b, SOME bool_id)) []`;;

let SmartIf_def = cake_def
  `SmartIf t e p q =
     match e with
       flat_Con _ (SOME (tag, SOME id)) [] ->
         if id = bool_id then
           if tag = true_tag then p
           else if tag = false_tag then q
           else flat_If t e p q
         else flat_If t e p q
     | _ -> flat_If t e p q`;;

(* HOL4 states this with a pmatch expression (PMATCH_ELIM_CONV): with match *)
(* compiled into case constants it is the definition again                  *)

let SmartIf_PMATCH = prove
 (CASE_TERM
  `!t e p q.
     SmartIf t e p q =
       match e with
         flat_Con _ (SOME (tag, SOME id)) [] ->
           if id = bool_id then
             if tag = true_tag then p
             else if tag = false_tag then q
             else flat_If t e p q
           else flat_If t e p q
       | _ -> flat_If t e p q`,
  REWRITE_TAC[SmartIf_def]);;
