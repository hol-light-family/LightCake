(* ========================================================================= *)
(* tokenUtils: port of HOL4 semantics/tokenUtilsScript.sml (CakeML v3479).   *)
(* Utility functions over tokens.                                            *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - All definitions are HOL4 [simp]: they are registered with              *)
(*   cake_add_simps.                                                         *)
(* - HOL4 writes them as clauses with a catch-all (isInt (IntT i) = T,      *)
(*   isInt _ = F), which HOL4's TFL completes into one clause per           *)
(*   constructor.  The kit's completion over the 68 constructors of token   *)
(*   takes about 150 s per definition, so each function is defined by the   *)
(*   equivalent match (first match wins, as in HOL4) and NAME_def is the     *)
(*   completed clause form, derived by SEM2AUX_CASE_CLAUSES (the same        *)
(*   theorem as HOL4's NAME_def, clauses in constructor order).             *)
(* - IntT, WordT and CharT are tokens_IntT, tokens_WordT and tokens_CharT    *)
(*   (names.tsv); grammar's Lf and TOK are those of src/hol4/grammar.ml.     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/tokens.ml";;
needs "hol4/grammar.ml";;

type_invention_error := true;;

(* SEM2AUX_CASE_CLAUSES th: th is |- !x1 .. xn. f x1 .. xn = rhs with case   *)
(* constants on the variables x1 .. xn in rhs; the result is the conjunction *)
(* of the clauses f pat = rhs' obtained by splitting each such case on the   *)
(* constructors of its type (outermost first) and reducing it with the      *)
(* kit's case net (a rewrite with case_def "token" itself would build a net *)
(* of 68 equations with 69 variables each, about 8 s per call).             *)

let SEM2AUX_CASE_CLAUSES =
  let fresh avoid v =
    let n0,ty = dest_var v in
    let names = map (fst o dest_var) (!avoid) in
    let rec go n = if mem n names then go (n^"'") else n in
    let v' = mk_var(go n0,ty) in
    avoid := v' :: !avoid; v' in
  let rec take_abs n t acc =
    if n = 0 then rev acc
    else if is_abs t then let v,b = dest_abs t in take_abs (n-1) b (v::acc)
    else failwith "take_abs" in
  let rec split th =
    let l,r = dest_eq(concl th) in
    let pvs = frees l in
    let is_split t =
      is_case_app t &&
      (let _,x,_ = dest_case_app t in is_var x && mem x pvs) in
    match (try Some(find_term is_split r) with Failure _ -> None) with
      None -> [th]
    | Some t ->
        let c,x,fs = dest_case_app t in
        let ci = case_info_of_const c in
        let xty = type_of x in
        flat (map2 (fun (vs,pat) f ->
            let tyi = type_match (type_of pat) xty [] in
            let vs = map (inst tyi) vs and pat = inst tyi pat in
            (* the names of the arm's bound variables, where usable *)
            let pref =
              try map2 (fun v b ->
                          let n = fst(dest_var b) in
                          if String.length n = 0 || String.sub n 0 1 = "_"
                          then v else mk_var(n,type_of v))
                       vs (take_abs (length vs) f [])
              with Failure _ -> vs in
            let avoid = ref (frees (concl th)) in
            let vs' = map (fresh avoid) pref in
            let pat' = vsubst (zip vs' vs) pat in
            let th1 = INST [pat',x] th in
            split (CONV_RULE (RAND_CONV (CAKE_REWRITE_CONV [] THENC
                                         DEPTH_CONV BETA_CONV)) th1))
          ci.ci_pats fs) in
  fun th ->
    let ths = split (SPEC_ALL th) in
    end_itlist CONJ (map (fun th -> GENL (frees (lhs(concl th))) th) ths);;

let isInt_def = SEM2AUX_CASE_CLAUSES (cake_def
  `isInt t <=> match t with tokens_IntT i -> T | _ -> F`);;
let _ = cake_add_simps [isInt_def];;

let isString_def = SEM2AUX_CASE_CLAUSES (cake_def
  `isString t <=> match t with StringT _ -> T | _ -> F`);;
let _ = cake_add_simps [isString_def];;

let isAlphaT_def = SEM2AUX_CASE_CLAUSES (cake_def
  `isAlphaT t <=> match t with AlphaT s -> T | _ -> F`);;
let _ = cake_add_simps [isAlphaT_def];;

let isSymbolT_def = SEM2AUX_CASE_CLAUSES (cake_def
  `isSymbolT t <=> match t with SymbolT s -> T | _ -> F`);;
let _ = cake_add_simps [isSymbolT_def];;

let isAlphaSym_def = SEM2AUX_CASE_CLAUSES (cake_def
  `isAlphaSym t <=> match t with AlphaT _ -> T | SymbolT _ -> T | _ -> F`);;
let _ = cake_add_simps [isAlphaSym_def];;

let isTyvarT_def = SEM2AUX_CASE_CLAUSES (cake_def
  `isTyvarT t <=> match t with TyvarT _ -> T | _ -> F`);;
let _ = cake_add_simps [isTyvarT_def];;

let isWhitespaceT_def = SEM2AUX_CASE_CLAUSES (cake_def
  `isWhitespaceT t <=> match t with WhitespaceT _ -> T | _ -> F`);;
let _ = cake_add_simps [isWhitespaceT_def];;

let isCharT_def = SEM2AUX_CASE_CLAUSES (cake_def
  `isCharT t <=> match t with tokens_CharT _ -> T | _ -> F`);;
let _ = cake_add_simps [isCharT_def];;

let isWordT_def = SEM2AUX_CASE_CLAUSES (cake_def
  `isWordT t <=> match t with tokens_WordT _ -> T | _ -> F`);;
let _ = cake_add_simps [isWordT_def];;

let isLongidT_def = SEM2AUX_CASE_CLAUSES (cake_def
  `isLongidT t <=> match t with LongidT _ _ -> T | _ -> F`);;
let _ = cake_add_simps [isLongidT_def];;

let destLongidT_def = SEM2AUX_CASE_CLAUSES (cake_def
  `destLongidT t = match t with LongidT str s -> SOME (str,s) | _ -> NONE`);;
let _ = cake_add_simps [destLongidT_def];;

let destLongidT_EQ_SOME = prove
 (`!t strs. destLongidT t = SOME strs <=>
            ?str s. t = LongidT str s /\ strs = (str,s)`,
  GEN_TAC THEN CASES_ON `t:token` THEN SIMP[] THEN MESON_TAC[]);;
let _ = cake_add_simps [destLongidT_EQ_SOME];;

let destTyvarPT_def = SEM2AUX_CASE_CLAUSES (cake_def
  `destTyvarPT (p:(token,B,C)parsetree) =
     match p with grammar_Lf (grammar_TOK (TyvarT s),_) -> SOME s | _ -> NONE`);;
let _ = cake_add_simps [destTyvarPT_def];;

let destLf_def = SEM2AUX_CASE_CLAUSES (cake_def
  `destLf (p:(A,B,C)parsetree) = match p with grammar_Lf (x,_) -> SOME x | _ -> NONE`);;
let _ = cake_add_simps [destLf_def];;

let destTOK_def = SEM2AUX_CASE_CLAUSES (cake_def
  `destTOK (sym:(A,B)symbol) = match sym with grammar_TOK t -> SOME t | _ -> NONE`);;
let _ = cake_add_simps [destTOK_def];;

let destAlphaT_def = SEM2AUX_CASE_CLAUSES (cake_def
  `destAlphaT t = match t with AlphaT s -> SOME s | _ -> NONE`);;
let _ = cake_add_simps [destAlphaT_def];;

let destAlphaT_EQ_SOME = prove
 (`!t s. destAlphaT t = SOME s <=> t = AlphaT s`,
  GEN_TAC THEN CASES_ON `t:token` THEN SIMP[]);;
let _ = cake_add_simps [destAlphaT_EQ_SOME];;

let destSymbolT_def = SEM2AUX_CASE_CLAUSES (cake_def
  `destSymbolT t = match t with SymbolT s -> SOME s | _ -> NONE`);;
let _ = cake_add_simps [destSymbolT_def];;

let destSymbolT_EQ_SOME = prove
 (`!t s. destSymbolT t = SOME s <=> t = SymbolT s`,
  GEN_TAC THEN CASES_ON `t:token` THEN SIMP[]);;
let _ = cake_add_simps [destSymbolT_EQ_SOME];;

let destIntT_def = SEM2AUX_CASE_CLAUSES (cake_def
  `destIntT t = match t with tokens_IntT i -> SOME i | _ -> NONE`);;
let _ = cake_add_simps [destIntT_def];;

let destCharT_def = SEM2AUX_CASE_CLAUSES (cake_def
  `destCharT t = match t with tokens_CharT c -> SOME c | _ -> NONE`);;
let _ = cake_add_simps [destCharT_def];;

let destStringT_def = SEM2AUX_CASE_CLAUSES (cake_def
  `destStringT t = match t with StringT s -> SOME s | _ -> NONE`);;
let _ = cake_add_simps [destStringT_def];;

let destWordT_def = SEM2AUX_CASE_CLAUSES (cake_def
  `destWordT t = match t with tokens_WordT w -> SOME w | _ -> NONE`);;
let _ = cake_add_simps [destWordT_def];;

let destFFIT_def = SEM2AUX_CASE_CLAUSES (cake_def
  `destFFIT t = match t with FFIT s -> SOME s | _ -> NONE`);;
let _ = cake_add_simps [destFFIT_def];;

let destREPLIDT_def = SEM2AUX_CASE_CLAUSES (cake_def
  `destREPLIDT t = match t with REPLIDT s -> SOME s | _ -> NONE`);;
let _ = cake_add_simps [destREPLIDT_def];;
