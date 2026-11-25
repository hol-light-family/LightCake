(* ========================================================================= *)
(* compute_syntax: port of HOL4 candle/prover/compute/compute_syntaxScript   *)
(* .sml (CakeML v3479).  Definitions of compute expressions for the Candle   *)
(* compute primitive.                                                        *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: the types binop and uop are                *)
(*   compute_binop and uop, the constructors compute_Add, ..., compute_Eq,   *)
(*   compute_Fst, compute_Snd, compute_Ispair; the type compute_exp has the  *)
(*   constructors compute_Pair, compute_Num, compute_Var, compute_App,       *)
(*   compute_If, compute_Let, compute_Uop, compute_Binop.  The holSyntax     *)
(*   names are LightCake's: hol_Var, hol_Const, hol_Comb, hol_Abs,           *)
(*   hol_term_ok, ...; mlstring literals are implode "...".                  *)
(* - HOL4 Overloads are notation only (HOL4 stores the expanded terms).      *)
(*   This theory has about sixty (_TRUE, _ADD, _CEXP_NUM, Cexp, ...), used   *)
(*   by every compute file, so they are not written out by hand: a parser    *)
(*   extension (HOL Light's install_parser hook, below) expands them while   *)
(*   the compute files are read, as HOL4's parser does.  An overload with    *)
(*   parameters takes its arguments when it heads an application, and is     *)
(*   the lambda abstraction otherwise (HOL4's beta-reduced overloads):       *)
(*   _ADD x y is hol_Comb (hol_Comb _ADD_TM x) y, MAP _SUC l is MAP (\tm.    *)
(*   hol_Comb _SUC_TM tm) l and bop2term compute_Add = _CEXP_ADD is the      *)
(*   lambda \t1 t2. ...  The stored terms are therefore HOL4's.  The         *)
(*   extension is switched on by compute_overloads_on () after the needs     *)
(*   lines of each compute file and off by compute_overloads_off () at its   *)
(*   end, so other files are read as before.  Besides this theory's          *)
(*   overloads the table has holSyntax's Fun, Bool and Equal.  HOL4's        *)
(*   _CEXP_VAR_TM, _CEXP_VAR, _CEXP_APP_TM and _CEXP_APP (unused; their      *)
(*   HOL4 bodies have a free variable string_ty) are left out.  A lone       *)
(*   overload (a whole quotation, a q-string, an argument of EXISTS_TAC) is  *)
(*   written in parentheses, (_TRUE): HOL Light reads a lone identifier as a *)
(*   variable before the hook is tried.                                      *)
(* - FUNPOW f n x is ITER n f x.  SAFEDIV and SAFEMOD are infixes with the   *)
(*   precedence of DIV and MOD, as in HOL4.                                  *)
(* - compute_syntax needs only holSyntax (HOL4's Ancestors also list         *)
(*   holSyntaxExtra, holSyntaxLib, holKernel and holKernelProof, which it    *)
(*   does not use).                                                          *)
(* ========================================================================= *)

needs "candle/standard/syntax/holSyntax.ml";;

prioritize_num();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The overload table and the parser extension.                              *)
(* ------------------------------------------------------------------------- *)

(* name, (parameters, body as a preterm) *)
let compute_overload_table = ref ([]:(string * (string list * preterm)) list);;

let compute_is_overload (s:string) = can (assoc s) (!compute_overload_table);;

let rec compute_preterm_subst (s:(string*preterm) list) (p:preterm) : preterm =
  match p with
    Varp(v,_) -> (try assoc v s with Failure _ -> p)
  | Combp(f,x) -> Combp(compute_preterm_subst s f,compute_preterm_subst s x)
  | Typing(q,ty) -> Typing(compute_preterm_subst s q,ty)
  | Absp(v,b) ->
      let rec bound q =
        match q with
          Varp(n,_) -> [n]
        | Typing(q',_) -> bound q'
        | Combp(f,x) -> union (bound f) (bound x)
        | _ -> [] in
      let bv = bound v in
      Absp(v,compute_preterm_subst (filter (fun (n,_) -> not (mem n bv)) s) b)
  | Constp _ -> p;;

let rec compute_preterm_names (p:preterm) : string list =
  match p with
    Varp(v,_) -> [v]
  | Combp(f,x) -> union (compute_preterm_names f) (compute_preterm_names x)
  | Typing(q,_) -> compute_preterm_names q
  | Absp(v,b) -> union (compute_preterm_names v) (compute_preterm_names b)
  | Constp _ -> [];;

(* the overload s applied to the first arguments args; the parameters left *)
(* over are abstracted (renamed apart from the names of args)              *)
let compute_overload_expand (s:string) (args:preterm list) : preterm =
  let params,body = assoc s (!compute_overload_table) in
  let given,rest = chop_list (length args) params in
  let avoid = itlist (union o compute_preterm_names) args [] in
  let rec fresh v = if mem v avoid then fresh (v ^ "'") else v in
  let rest' = map fresh rest in
  let sub = zip given args @ zip rest (map (fun v -> Varp(v,dpty)) rest') in
  itlist (fun v b -> Absp(Varp(v,dpty),b)) rest' (compute_preterm_subst sub body);;

(* the tokens of a bracket group (from the opening bracket to the matching *)
(* closing one) and the tokens after it                                    *)
let compute_bracket_group (op:string) (cl:string) (toks:lexcode list) =
  let rec go depth acc l =
    match l with
      [] -> failwith "compute overloads: unbalanced brackets"
    | (Resword r as t)::rest when r = op -> go (depth + 1) (t::acc) rest
    | (Resword r as t)::rest when r = cl ->
        if depth = 1 then rev (t::acc),rest else go (depth - 1) (t::acc) rest
    | t::rest -> go depth (t::acc) rest in
  go 0 [] toks;;

let compute_parse_group (grp:lexcode list) : preterm =
  let p,rest = parse_preterm grp in
  if rest = [] then p else failwith "compute overloads: bad argument";;

let compute_is_stop (s:string) =
  can get_infix_status s || parses_as_binder s || is_prefix s;;

(* one atom of an application: a bracket group or an identifier (an       *)
(* overload is then its lambda abstraction)                                *)
let compute_overload_arg (toks:lexcode list) : (preterm * lexcode list) option =
  match toks with
    Resword "(" :: _ ->
      let g,rest = compute_bracket_group "(" ")" toks in
      Some(compute_parse_group g,rest)
  | Resword "[" :: _ ->
      let g,rest = compute_bracket_group "[" "]" toks in
      Some(compute_parse_group g,rest)
  | Resword "{" :: _ ->
      let g,rest = compute_bracket_group "{" "}" toks in
      Some(compute_parse_group g,rest)
  | Ident s :: rest ->
      if compute_is_stop s then None
      else if compute_is_overload s then Some(compute_overload_expand s [],rest)
      else Some(compute_parse_group [Ident s],rest)
  | _ -> None;;

(* does an overload occur among the atoms of the application starting here *)
let rec compute_seq_has_overload (toks:lexcode list) : bool =
  let skip op cl =
    try compute_seq_has_overload (snd (compute_bracket_group op cl toks))
    with Failure _ -> false in
  match toks with
    Resword "(" :: Ident s :: Resword ")" :: _ when compute_is_overload s -> true
  | Resword "(" :: _ -> skip "(" ")"
  | Resword "[" :: _ -> skip "[" "]"
  | Resword "{" :: _ -> skip "{" "}"
  | Ident s :: rest ->
      not (compute_is_stop s) &&
      (compute_is_overload s || compute_seq_has_overload rest)
  | _ -> false;;

(* the parser extension: an application whose atoms include an overload;  *)
(* an overload at its head takes its arguments.  HOL Light reads a lone     *)
(* identifier, and one in parentheses, as a variable before this hook is    *)
(* tried; ( overload ) is caught here, so a lone overload is written in     *)
(* parentheses: QEXISTS_TAC "(_TRUE)".                                      *)
let compute_overload_parser (toks:lexcode list) : preterm * lexcode list =
  if not (compute_seq_has_overload toks) then raise Noparse else
  let head,rest =
    match toks with
      Resword "(" :: Ident s :: Resword ")" :: rest when compute_is_overload s ->
        compute_overload_expand s [],rest
    | Ident s :: rest when compute_is_overload s ->
        let params,_ = assoc s (!compute_overload_table) in
        let rec take k l acc =
          if k = 0 then rev acc,l else
          match compute_overload_arg l with
            Some(a,l') -> take (k - 1) l' (a::acc)
          | None -> rev acc,l in
        let args,rest' = take (length params) rest [] in
        compute_overload_expand s args,rest'
    | _ ->
        (match compute_overload_arg toks with
           Some(a,l) -> a,l
         | None -> raise Noparse) in
  let rec more acc l =
    match compute_overload_arg l with
      Some(a,l') -> more (Combp(acc,a)) l'
    | None -> acc,l in
  more head rest;;

let compute_overloads_on () =
  delete_parser "compute_overloads";
  install_parser ("compute_overloads",compute_overload_parser);;

let compute_overloads_off () = delete_parser "compute_overloads";;

(* the body is read with the overloads already in the table *)
let compute_add_overload (name:string) (params:string list) (body:string) =
  let p,rest = parse_preterm (lex (explode body)) in
  if rest <> [] then failwith ("compute_add_overload: " ^ name) else
  compute_overload_table := (name,(params,p)) :: !compute_overload_table;;

compute_overloads_on ();;

(* holSyntax *)
compute_add_overload "Fun" ["s"; "t"] "Tyapp (implode \"fun\") [s; t]";;
compute_add_overload "Bool" [] "Tyapp (implode \"bool\") []";;
compute_add_overload "Equal" ["ty"]
  "hol_Const (implode \"=\") (Fun ty (Fun ty Bool))";;

(* Numbers, bools *)
compute_add_overload "Num" [] "Tyapp (implode \"num\") []";;
compute_add_overload "_X" [] "hol_Var (implode \"x\") Bool";;
compute_add_overload "_Y" [] "hol_Var (implode \"y\") Bool";;
compute_add_overload "_TRUE" [] "hol_Const (implode \"T\") Bool";;
compute_add_overload "_FALSE" [] "hol_Const (implode \"F\") Bool";;
(* COND on numbers: *)
compute_add_overload "_COND_TM" []
  "hol_Const (implode \"COND\") (Fun Bool (Fun Num (Fun Num Num)))";;
compute_add_overload "_COND" ["t"; "t1"; "t2"]
  "hol_Comb (hol_Comb (hol_Comb _COND_TM t) t1) t2";;
(* COND on booleans: *)
compute_add_overload "_IF_TM" []
  "hol_Const (implode \"COND\") (Fun Bool (Fun Bool (Fun Bool Bool)))";;
compute_add_overload "_IF" ["t"; "t1"; "t2"]
  "hol_Comb (hol_Comb (hol_Comb _IF_TM t) t1) t2";;
compute_add_overload "_0" [] "hol_Const (implode \"_0\") Num";;
compute_add_overload "_SUC_TM" [] "hol_Const (implode \"SUC\") (Fun Num Num)";;
compute_add_overload "_SUC" ["tm"] "hol_Comb _SUC_TM tm";;
compute_add_overload "_BIT0_TM" [] "hol_Const (implode \"BIT0\") (Fun Num Num)";;
compute_add_overload "_BIT0" ["tm"] "hol_Comb _BIT0_TM tm";;
compute_add_overload "_BIT1_TM" [] "hol_Const (implode \"BIT1\") (Fun Num Num)";;
compute_add_overload "_BIT1" ["tm"] "hol_Comb _BIT1_TM tm";;
compute_add_overload "_N" [] "hol_Var (implode \"n\") Num";;
compute_add_overload "_M" [] "hol_Var (implode \"m\") Num";;
compute_add_overload "_ADD_TM" []
  "hol_Const (implode \"+\") (Fun Num (Fun Num Num))";;
compute_add_overload "_ADD" ["t1"; "t2"] "hol_Comb (hol_Comb _ADD_TM t1) t2";;
compute_add_overload "_SUB_TM" []
  "hol_Const (implode \"-\") (Fun Num (Fun Num Num))";;
compute_add_overload "_SUB" ["t1"; "t2"] "hol_Comb (hol_Comb _SUB_TM t1) t2";;
compute_add_overload "_MUL_TM" []
  "hol_Const (implode \"*\") (Fun Num (Fun Num Num))";;
compute_add_overload "_MUL" ["t1"; "t2"] "hol_Comb (hol_Comb _MUL_TM t1) t2";;
compute_add_overload "_MOD_TM" []
  "hol_Const (implode \"MOD\") (Fun Num (Fun Num Num))";;
compute_add_overload "_MOD" ["t1"; "t2"] "hol_Comb (hol_Comb _MOD_TM t1) t2";;
compute_add_overload "_DIV_TM" []
  "hol_Const (implode \"DIV\") (Fun Num (Fun Num Num))";;
compute_add_overload "_DIV" ["t1"; "t2"] "hol_Comb (hol_Comb _DIV_TM t1) t2";;
compute_add_overload "_LESS_TM" []
  "hol_Const (implode \"<\") (Fun Num (Fun Num Bool))";;
compute_add_overload "_LESS" ["t1"; "t2"] "hol_Comb (hol_Comb _LESS_TM t1) t2";;
compute_add_overload "_NUMERAL_TM" []
  "hol_Const (implode \"NUMERAL\") (Fun Num Num)";;
compute_add_overload "_NUMERAL" ["tm"] "hol_Comb _NUMERAL_TM tm";;

(* Compute expressions *)
compute_add_overload "Cexp" [] "Tyapp (implode \"cval\") []";;
compute_add_overload "Cexp_list" [] "Tyapp (implode \"list\") [Cexp]";;
compute_add_overload "_P1" [] "hol_Var (implode \"p1\") Cexp";;
compute_add_overload "_P2" [] "hol_Var (implode \"p2\") Cexp";;
compute_add_overload "_Q1" [] "hol_Var (implode \"q1\") Cexp";;
compute_add_overload "_Q2" [] "hol_Var (implode \"q2\") Cexp";;
compute_add_overload "_CS" [] "hol_Var (implode \"cs\") Cexp_list";;
compute_add_overload "_CEXP_NUM_TM" []
  "hol_Const (implode \"Cexp_num\") (Fun Num Cexp)";;
compute_add_overload "_CEXP_NUM" ["tm"] "hol_Comb _CEXP_NUM_TM tm";;
compute_add_overload "_CEXP_PAIR_TM" []
  "hol_Const (implode \"Cexp_pair\") (Fun Cexp (Fun Cexp Cexp))";;
compute_add_overload "_CEXP_PAIR" ["t1"; "t2"]
  "hol_Comb (hol_Comb _CEXP_PAIR_TM t1) t2";;
compute_add_overload "_CEXP_ADD_TM" []
  "hol_Const (implode \"Cexp_add\") (Fun Cexp (Fun Cexp Cexp))";;
compute_add_overload "_CEXP_ADD" ["t1"; "t2"]
  "hol_Comb (hol_Comb _CEXP_ADD_TM t1) t2";;
compute_add_overload "_CEXP_SUB_TM" []
  "hol_Const (implode \"Cexp_sub\") (Fun Cexp (Fun Cexp Cexp))";;
compute_add_overload "_CEXP_SUB" ["t1"; "t2"]
  "hol_Comb (hol_Comb _CEXP_SUB_TM t1) t2";;
compute_add_overload "_CEXP_MUL_TM" []
  "hol_Const (implode \"Cexp_mul\") (Fun Cexp (Fun Cexp Cexp))";;
compute_add_overload "_CEXP_MUL" ["t1"; "t2"]
  "hol_Comb (hol_Comb _CEXP_MUL_TM t1) t2";;
compute_add_overload "_CEXP_MOD_TM" []
  "hol_Const (implode \"Cexp_mod\") (Fun Cexp (Fun Cexp Cexp))";;
compute_add_overload "_CEXP_MOD" ["t1"; "t2"]
  "hol_Comb (hol_Comb _CEXP_MOD_TM t1) t2";;
compute_add_overload "_CEXP_DIV_TM" []
  "hol_Const (implode \"Cexp_div\") (Fun Cexp (Fun Cexp Cexp))";;
compute_add_overload "_CEXP_DIV" ["t1"; "t2"]
  "hol_Comb (hol_Comb _CEXP_DIV_TM t1) t2";;
compute_add_overload "_CEXP_LESS_TM" []
  "hol_Const (implode \"Cexp_less\") (Fun Cexp (Fun Cexp Cexp))";;
compute_add_overload "_CEXP_LESS" ["t1"; "t2"]
  "hol_Comb (hol_Comb _CEXP_LESS_TM t1) t2";;
compute_add_overload "_CEXP_IF_TM" []
  "hol_Const (implode \"Cexp_if\") (Fun Cexp (Fun Cexp (Fun Cexp Cexp)))";;
compute_add_overload "_CEXP_IF" ["t1"; "t2"; "t3"]
  "hol_Comb (hol_Comb (hol_Comb _CEXP_IF_TM t1) t2) t3";;
compute_add_overload "_CEXP_FST_TM" []
  "hol_Const (implode \"Cexp_fst\") (Fun Cexp Cexp)";;
compute_add_overload "_CEXP_FST" ["tm"] "hol_Comb _CEXP_FST_TM tm";;
compute_add_overload "_CEXP_SND_TM" []
  "hol_Const (implode \"Cexp_snd\") (Fun Cexp Cexp)";;
compute_add_overload "_CEXP_SND" ["tm"] "hol_Comb _CEXP_SND_TM tm";;
compute_add_overload "_CEXP_ISPAIR_TM" []
  "hol_Const (implode \"Cexp_ispair\") (Fun Cexp Cexp)";;
compute_add_overload "_CEXP_ISPAIR" ["tm"] "hol_Comb _CEXP_ISPAIR_TM tm";;
compute_add_overload "_CEXP_EQ_TM" []
  "hol_Const (implode \"Cexp_eq\") (Fun Cexp (Fun Cexp Cexp))";;
compute_add_overload "_CEXP_EQ" ["t1"; "t2"]
  "hol_Comb (hol_Comb _CEXP_EQ_TM t1) t2";;

(* Lets, let a = b in x: *)
compute_add_overload "_F" [] "hol_Var (implode \"f\") (Fun Cexp Cexp)";;
compute_add_overload "_LET_TM" []
  "hol_Const (implode \"LET\") (Fun (Fun Cexp Cexp) (Fun Cexp Cexp))";;
compute_add_overload "_LET" ["t1"; "t2"] "hol_Comb (hol_Comb _LET_TM t1) t2";;

(* ------------------------------------------------------------------------- *)
(* Bools                                                                     *)
(* ------------------------------------------------------------------------- *)

let bool2term_def = cake_def
  `(bool2term F = _FALSE) /\
   (bool2term T = _TRUE)`;;

(* ------------------------------------------------------------------------- *)
(* Natural numbers                                                           *)
(* ------------------------------------------------------------------------- *)

let num2term_def = cake_def
  `(num2term 0 = _0) /\
   (num2term (SUC n) = _SUC (num2term n))`;;

(* HOL4: Termination wf_rel_tac $< *)
let num2bit_def = cake_def_wf `MEASURE (\n:num. n)`
  (REWRITE_TAC[MEASURE] THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC DIV_LESS THEN ASM_ARITH_TAC)
  `num2bit n =
     if n = 0 then _0 else
     hol_Comb (if n MOD 2 = 0 then _BIT0_TM else _BIT1_TM) (num2bit (n DIV 2))`;;

let num2bit_ind = cake_ind "num2bit";;

(* ------------------------------------------------------------------------- *)
(* Compute expressions                                                       *)
(* ------------------------------------------------------------------------- *)

let compute_binop_INDUCT,compute_binop_RECURSION =
  cake_type "compute_binop = compute_Add | compute_Sub | compute_Mul | compute_Div |
                             compute_Mod | compute_Less | compute_Eq";;

let uop_INDUCT,uop_RECURSION =
  cake_type "uop = compute_Fst | compute_Snd | compute_Ispair";;

let compute_exp_INDUCT,compute_exp_RECURSION =
  cake_type "compute_exp = compute_Pair compute_exp compute_exp
                         | compute_Num num
                         | compute_Var mlstring
                         | compute_App mlstring (compute_exp list)
                         | compute_If compute_exp compute_exp compute_exp
                         | compute_Let mlstring compute_exp compute_exp
                         | compute_Uop uop compute_exp
                         | compute_Binop compute_binop compute_exp compute_exp";;

let cexp_value_def = cake_def
  `(cexp_value (compute_Num n) = T) /\
   (cexp_value (compute_Pair p q) = (cexp_value p /\ cexp_value q)) /\
   (cexp_value _ = F)`;;
let _ = cake_add_simps [cexp_value_def];;

let cexp_value_ind = cake_ind "cexp_value";;

let app_type_def = cake_def
  `app_type arity = ITER arity (Fun Cexp) Cexp`;;

let app_type = prove
 (`app_type 0 = Cexp /\
   app_type (SUC n) = Fun Cexp (app_type n)`,
  REWRITE_TAC[app_type_def; ITER]);;

let bop2term_def = cake_def
  `(bop2term compute_Add = _CEXP_ADD) /\
   (bop2term compute_Sub = _CEXP_SUB) /\
   (bop2term compute_Mul = _CEXP_MUL) /\
   (bop2term compute_Div = _CEXP_DIV) /\
   (bop2term compute_Mod = _CEXP_MOD) /\
   (bop2term compute_Less = _CEXP_LESS) /\
   (bop2term compute_Eq = _CEXP_EQ)`;;

let uop2term_def = cake_def
  `(uop2term compute_Fst = _CEXP_FST) /\
   (uop2term compute_Snd = _CEXP_SND) /\
   (uop2term compute_Ispair = _CEXP_ISPAIR)`;;

(* HOL4: Termination wf_rel_tac measure compute_exp_size *)
let cexp2term_def = cake_def
  `(cexp2term (compute_Num n) = _CEXP_NUM (_NUMERAL (num2bit n))) /\
   (cexp2term (compute_Pair p q) = _CEXP_PAIR (cexp2term p) (cexp2term q)) /\
   (cexp2term (compute_Uop uop p) = uop2term uop (cexp2term p)) /\
   (cexp2term (compute_Binop bop p q) = bop2term bop (cexp2term p) (cexp2term q)) /\
   (cexp2term (compute_If p q r) =
      _CEXP_IF (cexp2term p) (cexp2term q) (cexp2term r)) /\
   (cexp2term (compute_Let s x y) =
      _LET (hol_Abs (hol_Var s Cexp) (cexp2term y)) (cexp2term x)) /\
   (cexp2term (compute_Var s) = hol_Var s Cexp) /\
   (cexp2term (compute_App s cs) =
      FOLDL hol_Comb (hol_Const s (app_type (LENGTH cs))) (MAP cexp2term cs))`;;

let cexp2term_ind = cake_ind "cexp2term";;

(* DIV and MOD definitions that are defined for zero (and as in HOL Light). *)

let SAFEDIV_def = cake_def
  `SAFEDIV m n = if n = 0 then 0 else m DIV n`;;

parse_as_infix("SAFEDIV",(22,"left"));;

let SAFEMOD_def = cake_def
  `SAFEMOD m n = if n = 0 then m else m MOD n`;;

parse_as_infix("SAFEMOD",(22,"left"));;

compute_overloads_off ();;
