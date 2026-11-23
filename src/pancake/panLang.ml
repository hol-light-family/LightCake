(* ========================================================================= *)
(* panLang: port of HOL4 pancake/panLangScript.sml (CakeML v3479).           *)
(* Abstract syntax for Pancake language.  Pancake is an imperative language  *)
(* with instructions for conditionals, While loop, memory load and store,    *)
(* functions, and foreign function calls.                                    *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: panLang_exp, panLang_prog and the          *)
(*   constructors that clash with other languages (panLang_Const,            *)
(*   panLang_Var, panLang_Seq, ...); asm's memops are asm_Load, Load8, ...   *)
(* - HOL4 Type shift = ast$shift is the type abbreviation panLang_shift; the  *)
(*   other HOL4 Type abbreviations (stcname, fldname, varname, funname, eid, *)
(*   decname = mlstring; index = num) are HOL Light type abbreviations.      *)
(* - HOL4 exp_size l is panLang_exp_size l; exp3_size l (exp list) is        *)
(*   list_size (panLang_exp_size l); exp1_size l ((fldname # exp) list) is   *)
(*   list_size (pair_size mlstring_size (panLang_exp_size l)); shape1_size  *)
(*   is list_size shape_size.                                                *)
(* - strlit s is implode s, s1 ^ s2 is strcat s1 s2, concat is              *)
(*   mlstring_concat; 0w is word 0; ++ is APPEND (left associative); :: is  *)
(*   CONS; EVERY is ALL; $<> vn is \x. ~(vn = x); r.f is RECTYPE_f r.        *)
(* - The HOL4 Overloads TailCall, AssignCall and StandAloneCall are written  *)
(*   out where used (no definition here uses them).                          *)
(* - Definitions by many clauses over exp or prog (exp_ids, var_exp,         *)
(*   global_var_exp, fun_ids, free_var_ids) are made with sem1aux_def(_wf)   *)
(*   (HOL4's TFL completion of catch-all clauses; semantics/sem1aux_tfl.ml). *)
(* - Local helpers that are not HOL4 theorems are PANLAUX_.                  *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/backend/backend_common.ml";;
needs "semantics/sem1aux_tfl.ml";;

prioritize_num();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Local kit workarounds (PANLAUX_, for exp and struct_info only).           *)
(* 1. The kit's cake_type makes no size functions for exp:                   *)
(*    new_recursive_definition cannot tell apart the CONS clauses of its two *)
(*    list types (exp list and (fldname # exp) list), and the kit's fallback *)
(*    skolemizes the size parameter f_A away (SKOLEM_CONV drops a quantifier *)
(*    the clauses do not use: the only A of exp is in A word, of size 0) and *)
(*    then fails.  PANLAUX_size_functions is the kit's fallback route        *)
(*    (datatype.ml, define_size_functions) with a skolemization that keeps   *)
(*    the parameter, so exp gets HOL4's exp_size f (here panLang_exp_size    *)
(*    f_A) and the aux sizes.  PANLAUX_cake_type sizes is cake_type          *)
(*    (datatype.ml, simp.ml, tactics.ml) with it (sizes = true) or with no   *)
(*    size functions (sizes = false).                                        *)
(* 2. cake_record "struct_info" fails: its cake_type defines the size        *)
(*    function struct_info_size, the name of the accessor of the field size. *)
(*    PANLAUX_cake_record is cake_record (record.ml) on PANLAUX_cake_type    *)
(*    false: struct_info has no size function.                               *)
(* ------------------------------------------------------------------------- *)

let PANLAUX_size_functions (names:string list) =
  let main = hd names in
  let _,_,rth = assoc main (!inductive_type_store) in
  let fvs,bod = strip_forall(concl rth) in
  let fns,cls = strip_exists bod in
  let dom fn = fst(dest_fun_ty(type_of fn)) in
  let mainty = dom (find (fun fn -> fst(dest_type(dom fn)) = main) fns) in
  let tvs = tyvars mainty in
  if length tvs <> 1 then failwith "PANLAUX_size_functions: one type variable" else
  let params = map (fun tv -> mk_var("f_"^dest_vartype tv,mk_fun_ty tv `:num`))
                   tvs in
  let tvsizes = zip tvs params in
  let naux = ref 0 in
  let fname fn =
    let n = fst(dest_type(dom fn)) in
    if mem n names then n^"_size"
    else (incr naux; main^"_size_aux"^string_of_int !naux) in
  let fnames = map fname fns in
  let rthn = INST_TYPE (map (fun fn -> `:num`,snd(dest_fun_ty(type_of fn))) fns)
                       rth in
  let fvs',bod' = strip_forall(concl rthn) in
  let fns',cls' = strip_exists bod' in
  let comp' a =
    let ty = type_of a in
    try let fn' = find (fun f -> dom f = ty) fns' in mk_comb(fn',a)
    with Failure _ ->
      let t = mk_comb(size_of_type tvsizes ty,a) in
      try rhs(concl(BETA_CONV t)) with Failure _ -> t in
  let inst_of cl =
    let _,eq = strip_forall cl in
    let l,r = dest_eq eq in
    let pat = rand l in
    let args = if is_pair pat then [fst(dest_pair pat);snd(dest_pair pat)]
               else snd(strip_comb pat) in
    let fi,rargs = strip_comb r in
    let body = if args = [] then `0:num`
               else list_mk_binop `(+):num->num->num` (`1` :: map comp' args) in
    let rvs = map (fun t -> if is_var t then t else genvar(type_of t)) rargs in
    let body' = subst (filter (fun (v,t) -> v <> t) (zip rvs rargs)) body in
    fi,list_mk_abs(rvs,body') in
  let insts = map inst_of (conjuncts cls') in
  let th1 = CONV_RULE (DEPTH_CONV BETA_CONV)
              (ISPECL (map (fun f -> assoc f insts) fvs') rthn) in
  (* !f_A. ?g1 .. gn. P  to  ?g1 .. gn. !f_A. P[g1 f_A, ..], also when P   *)
  (* does not mention f_A                                                  *)
  let rec skolem tm =
    ((GEN_REWRITE_CONV I [SKOLEM_THM] THENC BINDER_CONV skolem) ORELSEC
     ALL_CONV) tm in
  let th2 = CONV_RULE skolem (GENL params th1) in
  let sp = new_specification fnames th2 in
  let cs = CONJUNCTS (SPECL params sp) in
  let def = end_itlist CONJ
              (map (fun c -> let vs = fst(strip_forall(concl c)) in
                             GENL (vs @ params) (SPECL vs c)) cs) in
  let consts = map (fun nm -> mk_const(nm,[])) fnames in
  List.iter2 (fun nm c ->
      let base = String.sub nm 0 (String.length nm - 5) in
      if mem base names then
        the_size_fns := (base,(c,tvs)) :: !the_size_fns) fnames consts;
  the_size_defs := def :: !the_size_defs;
  (* the auxiliary functions as list_size / pair_size forms *)
  let csz fn = list_mk_comb(assoc fn (zip fns consts),params) in
  let aux_eq fn =
    let d = dom fn in
    let k,targs = dest_type d in
    if mem k names || not (mem k ["list";"option";"prod"]) then failwith "" else
    let arg_size ty =
      try csz (find (fun f -> dom f = ty) fns)
      with Failure _ -> size_of_type tvsizes ty in
    let gc,gtvs = assoc k (!the_size_fns) in
    let gdom = fst(dest_fun_ty(funpow (length gtvs)
                                 (fun t -> snd(dest_fun_ty t)) (type_of gc))) in
    let tyi = type_match gdom d [] in
    let rhs_ = list_mk_comb(inst tyi gc,map arg_size targs) in
    let x = mk_var("x",d) in
    let tm = list_mk_forall(params,mk_eq(csz fn,rhs_)) in
    prove(tm,
      REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
      (if k = "list" then LIST_INDUCT_TAC
       else X_GEN_TAC x THEN
            STRUCT_CASES_TAC (ISPEC x (case_info_of_tyname k).ci_nchotomy)) THEN
      ASM_REWRITE_TAC[def; list_size; option_size; pair_size_THM]) in
  let eqs = mapfilter aux_eq fns in
  if eqs <> [] then
    the_size_aux_eqs := (main,eqs) :: !the_size_aux_eqs;
  def;;

let PANLAUX_cake_type (sizes:bool) s =
  let spec = parse_inductive_type_specification s in
  let names = map (fun (ty,_) -> try dest_vartype ty
                                 with Failure _ -> fst(dest_type ty)) spec in
  let res = define_type s in
  cake_last_types := names;
  do_list (fun n -> ignore(define_case_constant n (n^"_CASE"))) names;
  (if sizes then ignore(PANLAUX_size_functions names));
  do_list cake_register_type_simps names;
  cake_update_case_net();
  res;;

let PANLAUX_cake_record (name:string) (fields:(string * string) list) =
  let cname = name^"_REC" in
  let spec = name^" = "^cname^" "^
             String.concat " " (map (fun (_,ty) -> "("^ty^")") fields) in
  let _ = PANLAUX_cake_type false spec in
  let _,_,rth = assoc name (!inductive_type_store) in
  let nch = (case_info_of_tyname name).ci_nchotomy in
  let x0,bod = dest_forall(concl nch) in
  let rty = type_of x0 in
  let vs,eq = strip_exists bod in
  let pat = rand eq in
  let n = length fields in
  if length vs <> n then failwith "PANLAUX_cake_record: field count" else
  let fnames = map fst fields in
  let xs = map2 (fun (f,_) v -> mk_var(f,type_of v)) fields vs in
  let pat_x = vsubst (zip xs vs) pat in
  let acc_vars = map2 (fun f v -> mk_var(name^"_"^f,mk_fun_ty rty (type_of v)))
                      fnames xs in
  let acc_cls = map2 (fun a x -> list_mk_forall(xs,mk_eq(mk_comb(a,pat_x),x)))
                     acc_vars xs in
  let accessors = end_itlist CONJ (map (new_recursive_definition rth) acc_cls) in
  let accs = map (fun a -> mk_const(fst(dest_var a),[])) acc_vars in
  let accs = map2 (fun c v -> inst (type_match (type_of c) (type_of v) []) c)
                  accs acc_vars in
  let r = mk_var("r",rty) in
  let upd_defs = map2 (fun (f,_) (a,i) ->
      let fty = type_of(mk_comb(a,r)) in
      let g = mk_var("g",mk_fun_ty fty fty) in
      let args = map2 (fun a' j -> if j = i then mk_comb(g,mk_comb(a',r))
                                   else mk_comb(a',r))
                      accs (0--(n-1)) in
      let con = fst(strip_comb pat) in
      let rhs_ = list_mk_comb(con,args) in
      let uv = mk_var(name^"_"^f^"_fupd",
                      mk_fun_ty (type_of g) (mk_fun_ty rty rty)) in
      new_definition (mk_eq(list_mk_comb(uv,[g;r]),rhs_)))
    fields (zip accs (0--(n-1))) in
  let upds = map (fun th -> fst(strip_comb(lhs(snd(strip_forall(concl th))))))
                 upd_defs in
  let rcases = STRUCT_CASES_TAC (SPEC r nch) in
  let gs = map (fun a -> let fty = snd(dest_fun_ty(type_of a)) in
                         mk_var("g",mk_fun_ty fty fty)) accs in
  let hs = map (fun a -> let fty = snd(dest_fun_ty(type_of a)) in
                         mk_var("h",mk_fun_ty fty fty)) accs in
  let fupds_tms = map2 (fun (u,g) i ->
      let args = map2 (fun x j -> if j = i then mk_comb(g,x) else x)
                      xs (0--(n-1)) in
      list_mk_forall(g::xs,
        mk_eq(list_mk_comb(u,[g;pat_x]),list_mk_comb(fst(strip_comb pat),args))))
    (zip upds gs) (0--(n-1)) in
  let fupds = prove(list_mk_conj fupds_tms,
                    REWRITE_TAC(accessors::upd_defs)) in
  let accfupd_tms = flat (map2 (fun a i ->
      map2 (fun (u,g) j ->
             let l = mk_comb(a,list_mk_comb(u,[g;r])) in
             let rr = if i = j then mk_comb(g,mk_comb(a,r)) else mk_comb(a,r) in
             list_mk_forall([g;r],mk_eq(l,rr)))
           (zip upds gs) (0--(n-1)))
    accs (0--(n-1))) in
  let accfupds = prove(list_mk_conj accfupd_tms,
                       REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN rcases THEN
                       REWRITE_TAC(fupds :: [accessors])) in
  let ff_tms = map2 (fun u (g,h) ->
      let t = fst(dest_fun_ty(type_of g)) in
      let oc = mk_const("o",[t,aty; t,bty; t,`:C`]) in
      list_mk_forall([g;h;r],
        mk_eq(list_mk_comb(u,[g;list_mk_comb(u,[h;r])]),
              list_mk_comb(u,[mk_binop oc g h; r]))))
    upds (zip gs hs) in
  let fupdfupds = prove(list_mk_conj ff_tms,
                        REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN rcases THEN
                        REWRITE_TAC[fupds; o_THM]) in
  let canon_tms = flat (map (fun i ->
      map (fun j ->
             let ui,gi = el i upds,el i gs and uj,gj = el j upds,el j hs in
             list_mk_forall([gi;gj;r],
               mk_eq(list_mk_comb(uj,[gj;list_mk_comb(ui,[gi;r])]),
                     list_mk_comb(ui,[gi;list_mk_comb(uj,[gj;r])]))))
          ((i+1)--(n-1)))
    (0--(n-1))) in
  let fupdcanon =
    if canon_tms = [] then TRUTH else
    prove(list_mk_conj canon_tms,
          REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN rcases THEN
          REWRITE_TAC[fupds]) in
  let r1 = mk_var("r1",rty) and r2 = mk_var("r2",rty) in
  let ce_tm = list_mk_forall([r1;r2],
    mk_eq(mk_eq(r1,r2),
          list_mk_conj(map (fun a -> mk_eq(mk_comb(a,r1),mk_comb(a,r2))) accs))) in
  let component_equality = prove(ce_tm,
    REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC (SPEC r1 nch) THEN STRUCT_CASES_TAC (SPEC r2 nch) THEN
    REWRITE_TAC[accessors; injectivity name]) in
  let ri = { ri_name = name;
             ri_fields = map2 (fun f (a,u) -> f,a,u) fnames (zip accs upds);
             ri_accessors = accessors; ri_fupds = fupds; ri_accfupds = accfupds;
             ri_fupdfupds = fupdfupds; ri_fupdcanon = fupdcanon;
             ri_component_equality = component_equality } in
  the_records := (name,ri) :: !the_records;
  cake_add_global_simps ([accessors; fupds; accfupds; fupdfupds; K_o_THM;
                          KLAM_o_THM] @
                         (if fupdcanon = TRUTH then [] else [fupdcanon]));
  ri;;

(* ------------------------------------------------------------------------- *)
(* The syntax.                                                               *)
(* ------------------------------------------------------------------------- *)

(* for overloading the shift operation *)

new_type_abbrev("panLang_shift",`:shift`);;

new_type_abbrev("stcname",`:mlstring`);;

new_type_abbrev("fldname",`:mlstring`);;

new_type_abbrev("varname",`:mlstring`);;

new_type_abbrev("funname",`:mlstring`);;

new_type_abbrev("eid",`:mlstring`);;

new_type_abbrev("decname",`:mlstring`);;

new_type_abbrev("index",`:num`);;

let shape_INDUCT,shape_RECURSION = cake_type
  "shape = One
         | Comb (shape list)
         | Named stcname";;

let panop_INDUCT,panop_RECURSION = cake_type
  "panop = panLang_Mul";;

let varkind_INDUCT,varkind_RECURSION = cake_type
  "varkind = panLang_Local | panLang_Global";;

(* panLang_Load: the expression is the start address of a value of the     *)
(* given shape                                                              *)

let panLang_exp_INDUCT,panLang_exp_RECURSION = PANLAUX_cake_type true
  "panLang_exp = panLang_Const (A word)
               | panLang_Var varkind varname
               | RStruct (panLang_exp list)
               | RField index panLang_exp
               | NStruct stcname ((fldname # panLang_exp) list)
               | NField fldname panLang_exp
               | panLang_Load shape panLang_exp
               | panLang_Load32 panLang_exp
               | LoadByte panLang_exp
               | panLang_Op binop (panLang_exp list)
               | Panop panop (panLang_exp list)
               | Cmp cmp panLang_exp panLang_exp
               | panLang_Shift panLang_shift panLang_exp panLang_exp
               | BaseAddr
               | TopAddr
               | BytesInWord";;

let opsize_INDUCT,opsize_RECURSION = cake_type
  "opsize = Op8 | OpW | Op32 | Op16";;

let primop_INDUCT,primop_RECURSION = cake_type
  "primop = panLang_AddCarry";;

(* panLang_Assign, panLang_Store, panLang_Store32, StoreByte: destination,   *)
(* source.  Primitive: primitives directly target constructs in wordLang.   *)
(* panLang_ExtCall: FFI name, conf_ptr, conf_len, array_ptr, array_len.     *)

let panLang_prog_INDUCT,panLang_prog_RECURSION = cake_type
  "panLang_prog = panLang_Skip
                | Dec varname shape ((A)panLang_exp) panLang_prog
                | panLang_Assign varkind varname ((A)panLang_exp)
                | Primitive varname primop (((A)panLang_exp) list)
                | panLang_Store ((A)panLang_exp) ((A)panLang_exp)
                | panLang_Store32 ((A)panLang_exp) ((A)panLang_exp)
                | StoreByte ((A)panLang_exp) ((A)panLang_exp)
                | panLang_Seq panLang_prog panLang_prog
                | panLang_If ((A)panLang_exp) panLang_prog panLang_prog
                | While ((A)panLang_exp) panLang_prog
                | panLang_Break
                | panLang_Continue
                | panLang_Call
                    ((((varkind # varname) option #
                       ((eid # varname # panLang_prog) option)) option))
                    funname (((A)panLang_exp) list)
                | DecCall varname shape funname (((A)panLang_exp) list)
                          panLang_prog
                | panLang_ExtCall funname ((A)panLang_exp) ((A)panLang_exp)
                                  ((A)panLang_exp) ((A)panLang_exp)
                | panLang_Raise eid ((A)panLang_exp)
                | panLang_Return ((A)panLang_exp)
                | ShMemLoad opsize varkind varname ((A)panLang_exp)
                | ShMemStore opsize ((A)panLang_exp) ((A)panLang_exp)
                | panLang_Tick
                | Annot mlstring mlstring";;

let fun_decl_INFO = cake_record "fun_decl"
  ["name","mlstring";
   "inline","bool";
   "export","bool";
   "params","(varname#shape)list";
   "body","(A)panLang_prog";
   "return","shape"];;

let fun_decl_component_equality =
  (record_info "fun_decl").ri_component_equality;;

let decl_INDUCT,decl_RECURSION = cake_type
  "decl = Function ((A)fun_decl)
        | Decl shape mlstring ((A)panLang_exp)
        | ExnDecl eid shape
        | Name stcname ((fldname # shape) list)";;

(* HOL4 struct_info: no size function (kit workaround 2 above) *)

let struct_info_INFO = PANLAUX_cake_record "struct_info"
  ["fields","(fldname#shape)list";
   "size","num"];;

let struct_info_component_equality =
  (record_info "struct_info").ri_component_equality;;

(* ------------------------------------------------------------------------- *)
(* Functions on the syntax.                                                  *)
(* ------------------------------------------------------------------------- *)

(* HOL4: Overload TailCall = Call NONE; Overload AssignCall = \s h. Call    *)
(* (SOME (SOME s, h)); Overload StandAloneCall = \h. Call (SOME (NONE, h)) *)
(* (written out where used: panLang_Call NONE, ...)                         *)

(* HOL4 shape1_size (the size of a shape list) is list_size shape_size *)

let MEM_IMP_shape_size = prove
 (`!shapes a. MEM a shapes ==> shape_size a < 1 + list_size shape_size shapes`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; list_size] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `a:shape`) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC]);;

let is_wf_shape_def = cake_def
  `(is_wf_shape (ctxt:(mlstring#A)list) One <=> T) /\
   (is_wf_shape ctxt (Comb shs) <=> ALL (is_wf_shape ctxt) shs) /\
   (is_wf_shape ctxt (Named nm) <=>
      match ALOOKUP ctxt nm with
        SOME flds -> T
      | NONE -> F)`;;

let is_wf_flds_def = cake_def
  `(is_wf_flds (ctxt:(mlstring#A)list) [] <=> T) /\
   (is_wf_flds ctxt (CONS ((fld:B),sh) flds) <=>
      is_wf_shape ctxt sh /\ is_wf_flds ctxt flds)`;;

let is_wf_ctxt_def = cake_def
  `(is_wf_ctxt [] <=> T) /\
   (is_wf_ctxt (CONS (nm,info) ctxt') <=>
      ALOOKUP ctxt' nm = NONE /\
      is_wf_flds ctxt' (struct_info_fields info) /\
      is_wf_ctxt ctxt')`;;

(* For passes with Nameds *)

let size_of_sh_with_ctxt_def = cake_def
  `(size_of_sh_with_ctxt (ctxt:(mlstring#struct_info)list) One = 1) /\
   (size_of_sh_with_ctxt ctxt (Comb shapes) =
      SUM (MAP (size_of_sh_with_ctxt ctxt) shapes)) /\
   (size_of_sh_with_ctxt ctxt (Named name) =
      match ALOOKUP ctxt name with
        SOME info -> struct_info_size info
      | NONE -> 1)`;;

(* For passes after Nameds are compiled away, e.g. pan_to_crep *)

let size_of_shape_def = cake_def
  `(size_of_shape One = 1) /\
   (size_of_shape (Comb shapes) = SUM (MAP size_of_shape shapes)) /\
   (size_of_shape (Named name) = 1)`;;

let shape_to_str_def = cake_def
  `(shape_to_str One = implode "1") /\
   (shape_to_str (Comb []) = implode "{}") /\
   (shape_to_str (Comb (CONS x xs)) =
      mlstring_concat
        (APPEND (CONS (implode "{")
                   (CONS (shape_to_str x)
                      (MAP (\x. strcat (implode ",") x) (MAP shape_to_str xs))))
                [implode "}"])) /\
   (shape_to_str (Named nm) = nm)`;;

let shape_val_def = cake_def
  `(shape_val One = panLang_Const (word 0):(A)panLang_exp) /\
   (shape_val (Comb shapes) = RStruct (shape_vals shapes)) /\
   (shape_val (Named nm) = panLang_Const (word 0)) /\
   (shape_vals [] = []) /\
   (shape_vals (CONS sh shs) = CONS (shape_val sh) (shape_vals shs))`;;

(* HOL4 exp3_size (the size of an exp list) is list_size (panLang_exp_size  *)
(* l), exp1_size (of a (fldname # exp) list) is                            *)
(* list_size (pair_size mlstring_size (panLang_exp_size l))                *)

let panLang_MEM_IMP_exp_size = prove
 (`(!xs (a:(A)panLang_exp).
      MEM a xs ==> panLang_exp_size l a < list_size (panLang_exp_size l) xs) /\
   (!xs (a:mlstring#(A)panLang_exp).
      MEM a xs ==>
      panLang_exp_size l (SND a) <
      list_size (pair_size mlstring_size (panLang_exp_size l)) xs)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC MEM_LIST_SIZE THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`pair_size mlstring_size (panLang_exp_size (l:A->num))`;
                   `xs:(mlstring#(A)panLang_exp)list`;
                   `a:mlstring#(A)panLang_exp`] MEM_LIST_SIZE) THEN
    ASM_REWRITE_TAC[pair_size] THEN ARITH_TAC]);;

let nested_seq_def = cake_def
  `(nested_seq [] = panLang_Skip:(A)panLang_prog) /\
   (nested_seq (CONS e es) = panLang_Seq e (nested_seq es))`;;

let with_shape_def = cake_def
  `(with_shape [] (_:A list) = []) /\
   (with_shape (CONS sh shs) e =
      CONS (TAKE (size_of_shape sh) e)
           (with_shape shs (DROP (size_of_shape sh) e)))`;;

let exp_ids_def = sem1aux_def
  `(exp_ids (panLang_Skip:(A)panLang_prog) = []:mlstring list) /\
   (exp_ids (panLang_Raise e _) = [e]) /\
   (exp_ids (Dec _ _ _ p) = exp_ids p) /\
   (exp_ids (panLang_Seq p q) = APPEND (exp_ids p) (exp_ids q)) /\
   (exp_ids (panLang_If _ p q) = APPEND (exp_ids p) (exp_ids q)) /\
   (exp_ids (While _ p) = exp_ids p) /\
   (exp_ids (panLang_Call (SOME (_,SOME (e,_,ep))) _ _) = CONS e (exp_ids ep)) /\
   (exp_ids (DecCall _ _ _ _ p) = exp_ids p) /\
   (exp_ids _ = [])`;;

let is_decl_def = cake_def
  `(is_decl (Decl sh v e:(A)decl) <=> T) /\
   (is_decl _ <=> F)`;;

let is_exn_decl_def = cake_def
  `(is_exn_decl (ExnDecl eid sh:(A)decl) <=> T) /\
   (is_exn_decl _ <=> F)`;;

let is_name_def = cake_def
  `(is_name (Name _ _:(A)decl) <=> T) /\
   (is_name _ <=> F)`;;

let size_of_eids_def = cake_def
  `size_of_eids (prog:((A)decl)list) = LENGTH (FILTER is_exn_decl prog)`;;

(* the termination tactic of var_exp and global_var_exp (HOL4: simp[MEM_MAP, *)
(* EXISTS_PROD] or imp_res_tac MEM_IMP_exp_size, then arithmetic): a call  *)
(* on an element of MAP SND fes is on SND x for some MEM x fes, whose size *)
(* panLang_MEM_IMP_exp_size bounds; then the kit's TERM_TAC.  The clause   *)
(* for panLang_Shift is parsed separately: sh is a shape in panLang_Load and *)
(* a shift there, and in one quotation a variable has one type.             *)

let PANLAUX_EXP_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[MEM_MAP]) THEN
  REPEAT(FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC)) THEN RVEQ_TAC THEN
  (fun (asl,w as g) ->
     let th0 = INST [`ARB:A->num`,`l:A->num`]
                    (CONJUNCT2 panLang_MEM_IMP_exp_size) in
     MAP_EVERY ASSUME_TAC (mapfilter (fun (_,th) -> MATCH_MP th0 th) asl) g) THEN
  TERM_TAC;;

let var_exp_def = sem1aux_def_wf
  `MEASURE (\e:(A)panLang_exp. panLang_exp_size ARB e)`
  PANLAUX_EXP_TC_TAC
  (list_mk_conj
   [`(var_exp (panLang_Const (w:A word)) = []:mlstring list) /\
     (var_exp (panLang_Var panLang_Local v) = [v]) /\
     (var_exp (panLang_Var panLang_Global v) = []) /\
     (var_exp (RStruct es) = FLAT (MAP var_exp es)) /\
     (var_exp (RField i e) = var_exp e) /\
     (var_exp (NStruct sn fes) = FLAT (MAP var_exp (MAP SND fes))) /\
     (var_exp (NField fld e) = var_exp e) /\
     (var_exp (panLang_Load sh e) = var_exp e) /\
     (var_exp (panLang_Load32 e) = var_exp e) /\
     (var_exp (LoadByte e) = var_exp e) /\
     (var_exp (panLang_Op bop es) = FLAT (MAP var_exp es)) /\
     (var_exp (Panop op es) = FLAT (MAP var_exp es)) /\
     (var_exp (Cmp c e1 e2) = APPEND (var_exp e1) (var_exp e2))`;
    `(var_exp (panLang_Shift sh e1 e2:(A)panLang_exp) =
        APPEND (var_exp e1) (var_exp e2):mlstring list) /\
     (var_exp BaseAddr = []) /\
     (var_exp TopAddr = []) /\
     (var_exp BytesInWord = [])`]);;

let var_exp_ind = cake_ind "var_exp";;

(* global_var_exp: HOL4 MAP (global_var_exp o SND) fes; the kit's          *)
(* recursion analysis does not see the call under o (its termination        *)
(* condition has no argument), so the function is defined with              *)
(* \x. global_var_exp (SND x) (PANLAUX_global_var_exp_def) and HOL4's     *)
(* clauses are proved from it; no clauses for panLang_Load32, BaseAddr,      *)
(* TopAddr, BytesInWord (as in HOL4)                                         *)

let PANLAUX_global_var_exp_def = sem1aux_def_wf
  `MEASURE (\e:(A)panLang_exp. panLang_exp_size ARB e)`
  PANLAUX_EXP_TC_TAC
  (list_mk_conj
   [`(global_var_exp (panLang_Const (w:A word)) = []:mlstring list) /\
     (global_var_exp (panLang_Var panLang_Local v) = []) /\
     (global_var_exp (panLang_Var panLang_Global v) = [v]) /\
     (global_var_exp (RStruct es) = FLAT (MAP global_var_exp es)) /\
     (global_var_exp (RField i e) = global_var_exp e) /\
     (global_var_exp (NStruct sn fes) =
        FLAT (MAP (\x. global_var_exp (SND x)) fes)) /\
     (global_var_exp (NField fld e) = global_var_exp e) /\
     (global_var_exp (panLang_Load sh e) = global_var_exp e) /\
     (global_var_exp (LoadByte e) = global_var_exp e) /\
     (global_var_exp (panLang_Op bop es) = FLAT (MAP global_var_exp es)) /\
     (global_var_exp (Panop op es) = FLAT (MAP global_var_exp es)) /\
     (global_var_exp (Cmp c e1 e2) =
        APPEND (global_var_exp e1) (global_var_exp e2))`;
    `global_var_exp (panLang_Shift sh e1 e2:(A)panLang_exp) =
       APPEND (global_var_exp e1) (global_var_exp e2):mlstring list`]);;

let global_var_exp_ind = cake_ind "global_var_exp";;

let global_var_exp_def = prove
 (`(!w. global_var_exp (panLang_Const (w:A word)) = []:mlstring list) /\
   (!v. global_var_exp (panLang_Var panLang_Local v:(A)panLang_exp) = []) /\
   (!v. global_var_exp (panLang_Var panLang_Global v:(A)panLang_exp) = [v]) /\
   (!es. global_var_exp (RStruct es:(A)panLang_exp) =
           FLAT (MAP global_var_exp es)) /\
   (!i e. global_var_exp (RField i e:(A)panLang_exp) = global_var_exp e) /\
   (!sn fes. global_var_exp (NStruct sn fes:(A)panLang_exp) =
               FLAT (MAP (global_var_exp o SND) fes)) /\
   (!fld e. global_var_exp (NField fld e:(A)panLang_exp) = global_var_exp e) /\
   (!sh e. global_var_exp (panLang_Load sh e:(A)panLang_exp) =
             global_var_exp e) /\
   (!e. global_var_exp (LoadByte e:(A)panLang_exp) = global_var_exp e) /\
   (!bop es. global_var_exp (panLang_Op bop es:(A)panLang_exp) =
               FLAT (MAP global_var_exp es)) /\
   (!op es. global_var_exp (Panop op es:(A)panLang_exp) =
              FLAT (MAP global_var_exp es)) /\
   (!c e1 e2. global_var_exp (Cmp c e1 e2:(A)panLang_exp) =
                APPEND (global_var_exp e1) (global_var_exp e2)) /\
   (!sh e1 e2. global_var_exp (panLang_Shift sh e1 e2:(A)panLang_exp) =
                 APPEND (global_var_exp e1) (global_var_exp e2))`,
  REWRITE_TAC[o_DEF; PANLAUX_global_var_exp_def]);;

let load_op_def = cake_def
  `(load_op Op8 = Load8) /\
   (load_op Op16 = Load16) /\
   (load_op OpW = asm_Load) /\
   (load_op Op32 = asm_Load32)`;;

let store_op_def = cake_def
  `(store_op Op8 = Store8) /\
   (store_op Op16 = Store16) /\
   (store_op OpW = asm_Store) /\
   (store_op Op32 = asm_Store32)`;;

let is_function_def = cake_def
  `(is_function (Function _:(A)decl) <=> T) /\
   (is_function _ <=> F)`;;

let functions_def = cake_def
  `(functions ([]:((A)decl)list) = []) /\
   (functions (CONS (Function fi) fs) =
      CONS (fun_decl_name fi,fun_decl_params fi,fun_decl_body fi,
            fun_decl_return fi)
           (functions fs)) /\
   (functions (CONS (Decl _ _ _) fs) = functions fs) /\
   (functions (CONS (ExnDecl _ _) fs) = functions fs) /\
   (functions (CONS (Name _ _) fs) = functions fs)`;;

let exceptions_def = cake_def
  `(exceptions ([]:((A)decl)list) = []) /\
   (exceptions (CONS (Function fi) fs) = exceptions fs) /\
   (exceptions (CONS (Decl _ _ _) fs) = exceptions fs) /\
   (exceptions (CONS (ExnDecl eid sh) fs) = CONS (eid,sh) (exceptions fs)) /\
   (exceptions (CONS (Name _ _) fs) = exceptions fs)`;;

let fun_ids_def = sem1aux_def
  `(fun_ids (Dec _ _ _ p:(A)panLang_prog) = fun_ids p) /\
   (fun_ids (panLang_Seq p q) = APPEND (fun_ids p) (fun_ids q)) /\
   (fun_ids (panLang_If _ p q) = APPEND (fun_ids p) (fun_ids q)) /\
   (fun_ids (While _ p) = fun_ids p) /\
   (fun_ids (panLang_Call (SOME (_,SOME (_,_,ep))) nm _) =
      CONS nm (fun_ids ep)) /\
   (fun_ids (panLang_Call _ nm _) = [nm]) /\
   (fun_ids (DecCall _ _ nm _ p) = CONS nm (fun_ids p)) /\
   (fun_ids _ = [])`;;

let free_var_ids_def = sem1aux_def
  `(free_var_ids (Dec vn sh e p:(A)panLang_prog) =
      APPEND (var_exp e) (FILTER (\x. ~(vn = x)) (free_var_ids p))) /\
   (free_var_ids (panLang_Seq p q) =
      APPEND (free_var_ids p) (free_var_ids q)) /\
   (free_var_ids (panLang_If g p q) =
      APPEND (APPEND (var_exp g) (free_var_ids p)) (free_var_ids q)) /\
   (free_var_ids (While g p) = APPEND (var_exp g) (free_var_ids p)) /\
   (free_var_ids (panLang_Assign vk v e) =
      if vk = panLang_Local then CONS v (var_exp e) else var_exp e) /\
   (free_var_ids (Primitive v pop es) = CONS v (FLAT (MAP var_exp es))) /\
   (free_var_ids (panLang_Store e1 e2) = APPEND (var_exp e1) (var_exp e2)) /\
   (free_var_ids (panLang_Store32 e1 e2) = APPEND (var_exp e1) (var_exp e2)) /\
   (free_var_ids (StoreByte e1 e2) = APPEND (var_exp e1) (var_exp e2)) /\
   (free_var_ids (panLang_Raise eid e) = var_exp e) /\
   (free_var_ids (panLang_Return e) = var_exp e) /\
   (free_var_ids (panLang_ExtCall fn e1 e2 e3 e4) =
      APPEND (APPEND (APPEND (var_exp e1) (var_exp e2)) (var_exp e3))
             (var_exp e4)) /\
   (free_var_ids (ShMemLoad os vk v e) =
      if vk = panLang_Local then CONS v (var_exp e) else var_exp e) /\
   (free_var_ids (ShMemStore os e1 e2) = APPEND (var_exp e1) (var_exp e2)) /\
   (free_var_ids (panLang_Call (SOME (NONE,SOME (_,vn,ep))) _ args) =
      APPEND (CONS vn (free_var_ids ep)) (FLAT (MAP var_exp args))) /\
   (free_var_ids (panLang_Call (SOME (SOME (vk,vn),SOME (_,en,ep))) _ args) =
      APPEND (APPEND (if vk = panLang_Local then [vn] else [])
                     (CONS en (free_var_ids ep)))
             (FLAT (MAP var_exp args))) /\
   (free_var_ids (panLang_Call (SOME (SOME (vk,vn),NONE)) _ args) =
      APPEND (if vk = panLang_Local then [vn] else [])
             (FLAT (MAP var_exp args))) /\
   (free_var_ids (panLang_Call (SOME (NONE,NONE)) _ args) =
      FLAT (MAP var_exp args)) /\
   (free_var_ids (panLang_Call NONE _ args) = FLAT (MAP var_exp args)) /\
   (free_var_ids (DecCall vn _ _ args p) =
      APPEND (CONS vn (free_var_ids p)) (FLAT (MAP var_exp args))) /\
   (free_var_ids _ = [])`;;

let inlinable_def = cake_def
  `(inlinable (Function fi:(A)decl) <=> fun_decl_inline fi) /\
   (inlinable _ <=> F)`;;
