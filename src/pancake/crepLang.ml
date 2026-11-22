(* ========================================================================= *)
(* crepLang: port of HOL4 pancake/crepLangScript.sml (CakeML v3479).         *)
(* Abstract syntax of Crepe language.  Crepe: instructions are similar to    *)
(* that of Pancake, but we flatten locals from struct-layout to word-layout. *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as notes/naming/names.tsv says: crep_exp, crep_prog and the       *)
(*   constructors that clash with other languages (crep_Const, crep_Var,     *)
(*   crep_Seq, ...); LoadGlob, StoreGlob and Crepop keep their names.        *)
(* - HOL4 Type shift = ast$shift, varname = num and funname = mlstring are   *)
(*   the type abbreviations crep_shift, crep_varname and crep_funname        *)
(*   (panLang's varname and funname are mlstring).                           *)
(* - HOL4 exp_size l is crep_exp_size l; exp1_size l (the size of an exp     *)
(*   list) is list_size (crep_exp_size l).                                   *)
(* - 0w is word 0, 1w is word 1, + on words is word_add; ++ is APPEND (left  *)
(*   associative); :: is CONS; $<> n is \x. ~(n = x); MAP2 is HOL Light's    *)
(*   MAP2 (equal lengths: assign_ret's two lists have the same length).     *)
(* - var_cexp: HOL4's last clause is var_cexp TopAddrl = [] with a variable *)
(*   TopAddrl (a typo for TopAddr); after the earlier clauses it matches     *)
(*   only crep_TopAddr, so it is written with crep_TopAddr (the same         *)
(*   completed clauses).                                                     *)
(* - The HOL4 Overload shift = backend_common$word_shift is written out      *)
(*   where used (backend_common_word_shift); no definition here uses it.     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/backend/backend_common.ml";;
needs "pancake/panLang.ml";;

prioritize_num();;
type_invention_error := true;;

new_type_abbrev("crep_shift",`:shift`);;

new_type_abbrev("crep_varname",`:num`);;

new_type_abbrev("crep_funname",`:mlstring`);;

let crepop_INDUCT,crepop_RECURSION = cake_type
  "crepop = crep_Mul";;

let crep_exp_INDUCT,crep_exp_RECURSION = cake_type
  "crep_exp = crep_Const (A word)
            | crep_Var crep_varname
            | crep_Load crep_exp
            | crep_Load32 crep_exp
            | crep_LoadByte crep_exp
            | LoadGlob (5 word)
            | crep_Op binop (crep_exp list)
            | Crepop crepop (crep_exp list)
            | crep_Cmp cmp crep_exp crep_exp
            | crep_Shift crep_shift crep_exp crep_exp
            | crep_BaseAddr
            | crep_TopAddr";;

(* crep_Assign, crep_Store, crep_Store32, crep_StoreByte, StoreGlob: dest,  *)
(* source.  crep_Primitive: since pan_to_crep invents variable names        *)
(* already, variables are used on the right (instead of expressions).      *)
(* crep_Call: NONE is a tail call; SOME (rets, handler) a returning call,  *)
(* the handler (exception id, program) optional.                          *)

let crep_prog_INDUCT,crep_prog_RECURSION = cake_type
  "crep_prog = crep_Skip
             | crep_Dec crep_varname ((A)crep_exp) crep_prog
             | crep_Assign crep_varname ((A)crep_exp)
             | crep_Primitive (crep_varname list) primop (crep_varname list)
             | crep_Store ((A)crep_exp) ((A)crep_exp)
             | crep_Store32 ((A)crep_exp) ((A)crep_exp)
             | crep_StoreByte ((A)crep_exp) ((A)crep_exp)
             | StoreGlob (5 word) ((A)crep_exp)
             | crep_Seq crep_prog crep_prog
             | crep_If ((A)crep_exp) crep_prog crep_prog
             | crep_While ((A)crep_exp) crep_prog
             | crep_Break num
             | crep_Continue num
             | crep_Call (((crep_varname list) #
                           ((A word # crep_prog) option)) option)
                         crep_funname (((A)crep_exp) list)
             | crep_ExtCall crep_funname crep_varname crep_varname
                            crep_varname crep_varname
             | crep_Raise (A word)
             | crep_Return (((A)crep_exp) list)
             | crep_ShMem memop crep_varname ((A)crep_exp)
             | crep_Tick";;

(* HOL4: MEM_IMP_exp_size *)

let crep_MEM_IMP_exp_size = prove
 (`!xs (a:(A)crep_exp).
     MEM a xs ==> crep_exp_size l a < list_size (crep_exp_size l) xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; list_size] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `a:(A)crep_exp`) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC]);;

let load_shape_def = cake_def
  `(load_shape (a:A word) 0 e = []) /\
   (load_shape a (SUC i) e =
      if a = word 0
      then CONS (crep_Load e) (load_shape (word_add a bytes_in_word) i e)
      else CONS (crep_Load (crep_Op asm_Add [e; crep_Const a]))
                (load_shape (word_add a bytes_in_word) i e))`;;

let crep_nested_seq_def = cake_def
  `(crep_nested_seq [] = crep_Skip:(A)crep_prog) /\
   (crep_nested_seq (CONS e es) = crep_Seq e (crep_nested_seq es))`;;

let stores_def = cake_def
  `(stores ad [] (a:A word) = []) /\
   (stores ad (CONS e es) a =
      if a = word 0
      then CONS (crep_Store ad e) (stores ad es (word_add a bytes_in_word))
      else CONS (crep_Store (crep_Op asm_Add [ad; crep_Const a]) e)
                (stores ad es (word_add a bytes_in_word)))`;;

let nested_decs_def = cake_def
  `(nested_decs [] [] (p:(A)crep_prog) = p) /\
   (nested_decs (CONS n ns) (CONS e es) p = crep_Dec n e (nested_decs ns es p)) /\
   (nested_decs [] _ p = crep_Skip) /\
   (nested_decs _ [] p = crep_Skip)`;;

let nested_decs_ind = cake_ind "nested_decs";;

let store_globals_def = cake_def
  `(store_globals (ad:5 word) [] = []:((A)crep_prog)list) /\
   (store_globals ad (CONS e es) =
      CONS (StoreGlob ad e) (store_globals (word_add ad (word 1)) es))`;;

let load_globals_def = cake_def
  `(load_globals (_:5 word) 0 = []:((A)crep_exp)list) /\
   (load_globals ad (SUC n) =
      CONS (LoadGlob ad) (load_globals (word_add ad (word 1)) n))`;;

let assign_ret_def = cake_def
  `assign_ret ns =
     crep_nested_seq
       (MAP2 crep_Assign ns (load_globals (word 0) (LENGTH ns))):(A)crep_prog`;;

let var_cexp_def = cake_def
  `(var_cexp (crep_Const (w:A word)) = []:num list) /\
   (var_cexp (crep_Var v) = [v]) /\
   (var_cexp (crep_Load e) = var_cexp e) /\
   (var_cexp (crep_Load32 e) = var_cexp e) /\
   (var_cexp (crep_LoadByte e) = var_cexp e) /\
   (var_cexp (LoadGlob a) = []) /\
   (var_cexp (crep_Op bop es) = FLAT (MAP var_cexp es)) /\
   (var_cexp (Crepop cop es) = FLAT (MAP var_cexp es)) /\
   (var_cexp (crep_Cmp c e1 e2) = APPEND (var_cexp e1) (var_cexp e2)) /\
   (var_cexp (crep_Shift sh e1 e2) = APPEND (var_cexp e1) (var_cexp e2)) /\
   (var_cexp crep_BaseAddr = []) /\
   (var_cexp crep_TopAddr = [])`;;

let var_cexp_ind = cake_ind "var_cexp";;

(* assigned_free_vars, crep_assigned_vars: the clauses for crep_Call are   *)
(* parsed apart (e is an expression in crep_Dec and a function name in      *)
(* crep_Call; in one quotation a variable has one type)                    *)

let assigned_free_vars_def = cake_def
  (list_mk_conj
   [`(assigned_free_vars (crep_Skip:(A)crep_prog) = []:num list) /\
     (assigned_free_vars (crep_Dec n e p) =
        FILTER (\x. ~(n = x)) (assigned_free_vars p)) /\
     (assigned_free_vars (crep_Assign n e) = [n]) /\
     (assigned_free_vars (crep_Primitive lhss pop rhss) = lhss) /\
     (assigned_free_vars (crep_Seq p p') =
        APPEND (assigned_free_vars p) (assigned_free_vars p')) /\
     (assigned_free_vars (crep_If e p p') =
        APPEND (assigned_free_vars p) (assigned_free_vars p')) /\
     (assigned_free_vars (crep_While e p) = assigned_free_vars p)`;
    `(assigned_free_vars (crep_Call (SOME (rts,SOME (_,p))) e es:(A)crep_prog) =
        APPEND rts (assigned_free_vars p):num list) /\
     (assigned_free_vars (crep_Call (SOME (rts,NONE)) e es) = rts) /\
     (assigned_free_vars (crep_ShMem op r ad) = [r]) /\
     (assigned_free_vars _ = [])`]);;

let crep_assigned_vars_def = cake_def
  (list_mk_conj
   [`(crep_assigned_vars (crep_Skip:(A)crep_prog) = []:num list) /\
     (crep_assigned_vars (crep_Dec n e p) = CONS n (crep_assigned_vars p)) /\
     (crep_assigned_vars (crep_Assign n e) = [n]) /\
     (crep_assigned_vars (crep_Primitive lhss pop rhss) = lhss) /\
     (crep_assigned_vars (crep_Seq p p') =
        APPEND (crep_assigned_vars p) (crep_assigned_vars p')) /\
     (crep_assigned_vars (crep_If e p p') =
        APPEND (crep_assigned_vars p) (crep_assigned_vars p')) /\
     (crep_assigned_vars (crep_While e p) = crep_assigned_vars p)`;
    `(crep_assigned_vars (crep_Call (SOME (rts,SOME (_,p))) e es:(A)crep_prog) =
        APPEND rts (crep_assigned_vars p):num list) /\
     (crep_assigned_vars (crep_Call (SOME (rts,NONE)) e es) = rts) /\
     (crep_assigned_vars (crep_ShMem op r ad) = [r]) /\
     (crep_assigned_vars _ = [])`]);;

let crep_assigned_vars_ind = cake_ind "crep_assigned_vars";;

let crep_exps_def = cake_def
  `(crep_exps (crep_Const (w:A word)) = [crep_Const w]) /\
   (crep_exps (crep_Var v) = [crep_Var v]) /\
   (crep_exps (crep_Load e) = crep_exps e) /\
   (crep_exps (crep_Load32 e) = crep_exps e) /\
   (crep_exps (crep_LoadByte e) = crep_exps e) /\
   (crep_exps (LoadGlob a) = [LoadGlob a]) /\
   (crep_exps (crep_Op bop es) = FLAT (MAP crep_exps es)) /\
   (crep_exps (Crepop pop es) = FLAT (MAP crep_exps es)) /\
   (crep_exps (crep_Cmp c e1 e2) = APPEND (crep_exps e1) (crep_exps e2)) /\
   (crep_exps (crep_Shift sh e1 e2) = APPEND (crep_exps e1) (crep_exps e2)) /\
   (crep_exps crep_BaseAddr = [crep_BaseAddr]) /\
   (crep_exps crep_TopAddr = [crep_TopAddr])`;;

let crep_exps_ind = cake_ind "crep_exps";;
