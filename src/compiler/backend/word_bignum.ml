(* ========================================================================= *)
(* word_bignum: port of HOL4 compiler/backend/word_bignumScript.sml         *)
(* (CakeML v3479).                                                           *)
(* The bignum library used by the CakeML compiler. Note that the             *)
(* implementation is automatically generated from a shallow embedding that   *)
(* is part of the HOL distribution in mc_multiwordTheory.                    *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "hol4/mc_multiword.ml";;
needs "compiler/backend/wordLang.ml";;

prioritize_num();;
type_invention_error := true;;

(* syntax of a little language *)

let address_INDUCT,address_RECURSION = cake_type
  "address = In1 | In2 | Out";;

(* LoopBody is only used by the semantics *)

let mini_INDUCT,mini_RECURSION = cake_type
  "mini = word_bignum_Skip
        | word_bignum_Assign num ((A)wl_exp)
        | Delete (num list)
        | word_bignum_Seq mini mini
        | word_bignum_Load num num address
        | word_bignum_Store num num
        | word_bignum_If cmp num ((A)reg_imm) mini mini
        | Swap
        | word_bignum_Add num num num ((A)reg_imm) ((A)reg_imm)
        | word_bignum_Sub num num num ((A)reg_imm) ((A)reg_imm)
        | word_bignum_Mul num num num num
        | word_bignum_Div num num num num num
        | word_bignum_Loop bool (num list) mini
        | word_bignum_Continue
        | Rec (num list) (num list)
        | LoopBody mini";;

(* ------------------------------------------------------------------------- *)
(* generate deep embeddings                                                  *)
(* ------------------------------------------------------------------------- *)

(* HOL4's list functions with HOL4's orders: find_terms lists the matching  *)
(* subterms in reverse preorder (with repetitions); op_mk_set keeps the     *)
(* last occurrence of each element; free_vars lists the free variables in  *)
(* reverse order of first occurrence                                        *)

let WORDP3AUX_find_terms (p:term->bool) tm =
  let acc = ref [] in
  let rec f t =
    (if p t then acc := t :: !acc);
    if is_abs t then f (body t)
    else if is_comb t then (f (rator t); f (rand t)) in
  f tm; !acc;;

let WORDP3AUX_mk_set l =
  itlist (fun a s -> if exists (aconv a) s then s else a :: s) l [];;

let WORDP3AUX_set_diff s1 s2 =
  filter (fun x -> not (exists (aconv x) s2)) s1;;

let WORDP3AUX_free_vars tm =
  let rec fv bnd t acc =
    if is_var t then
      (if mem t bnd || mem t acc then acc else t :: acc)
    else if is_comb t then fv bnd (rand t) (fv bnd (rator t) acc)
    else if is_abs t then
      let v,b = dest_abs t in fv (v::bnd) b acc
    else acc in
  fv [] tm [];;

(* the port's equations bind the components of a tuple with pair_CASE and  *)
(* rename a bound variable that would shadow a free one (r1 becomes r1');  *)
(* the translation reads them as HOL4's tuple lets, a variable as its name *)
(* without the primes                                                      *)

let WORDP3AUX_base_name s =
  let rec go k = if k > 0 && s.[k-1] = '\'' then go (k-1) else k in
  String.sub s 0 (go (String.length s));;

let WORDP3AUX_is_pair_case tm =
  is_comb tm && is_comb (rator tm) && is_const (rator (rator tm)) &&
  fst (dest_const (rator (rator tm))) = "pair_CASE" &&
  is_abs (rand tm) && is_abs (body (rand tm));;

(* v bound by a pair_CASE whose body t is pair_CASE v (\a b. t'): the      *)
(* tuple pattern of v and the remaining body                               *)

let rec WORDP3AUX_refine_pat v t =
  if WORDP3AUX_is_pair_case t && rand (rator t) = v then
    let a,t1 = dest_abs (rand t) in
    let b,t2 = dest_abs t1 in
    if vfree_in v t2 then v,t else
    let pa,t3 = WORDP3AUX_refine_pat a t2 in
    let pb,t4 = WORDP3AUX_refine_pat b t3 in
    mk_pair(pa,pb),t4
  else v,t;;

(* HOL4's dest_anylet with one binding: ((pattern,value),body)             *)

let WORDP3AUX_dest_let tm =
  if is_let tm then
    (match dest_let tm with
       [v,e],t -> (v,e),t
     | _ -> failwith "WORDP3AUX_dest_let")
  else if WORDP3AUX_is_pair_case tm then
    let e = rand (rator tm) in
    let a,t1 = dest_abs (rand tm) in
    let b,t2 = dest_abs t1 in
    let pa,t3 = WORDP3AUX_refine_pat a t2 in
    let pb,t4 = WORDP3AUX_refine_pat b t3 in
    (mk_pair(pa,pb),e),t4
  else failwith "WORDP3AUX_dest_let";;

(* HOL4's dest_let: a let with a variable                                   *)

let WORDP3AUX_dest_var_let tm =
  match WORDP3AUX_dest_let tm with
    (v,e),t when is_var v -> (v,e),t
  | _ -> failwith "WORDP3AUX_dest_var_let";;

(* the constructors of the little language                                 *)

let WORDP3AUX_Skip = `word_bignum_Skip:(A)mini`;;
let WORDP3AUX_Swap = `Swap:(A)mini`;;
let WORDP3AUX_Continue = `word_bignum_Continue:(A)mini`;;

let WORDP3AUX_mk c args = list_mk_icomb c args;;

let WORDP3AUX_is_Rec tm =
  try fst (dest_const (fst (strip_comb tm))) = "Rec"
  with Failure _ -> false;;

(* a register: a variable rN (the primes ignored) of type :A word          *)

let WORDP3AUX_dest_reg v =
  let n,ty = try dest_var v with Failure _ -> failwith "dest_reg" in
  if ty <> `:A word` then failwith "dest_reg" else
  let s = WORDP3AUX_base_name n in
  let k = try int_of_string (String.sub s 1 (String.length s - 1))
          with _ -> failwith "dest_reg" in
  mk_small_numeral k;;

let WORDP3AUX_dest_binop c tm =
  let f,args = strip_comb tm in
  if is_const f && fst (dest_const f) = c && length args = 2
  then hd args,hd (tl args) else failwith "dest_binop";;

let WORDP3AUX_is_word tm =
  try fst (dest_const (rator tm)) = "word" with Failure _ -> false;;

let WORDP3AUX_binops =
  ["word_add","asm_Add"; "word_sub","asm_Sub"; "word_and","asm_And";
   "word_xor","asm_Xor"; "word_or","asm_Or"];;

let WORDP3AUX_shifts =
  ["word_ushr","Lsr"; "word_shl","Lsl"; "word_ishr","Asr"];;

let rec WORDP3AUX_get_exp x =
  (* Var *)
  try WORDP3AUX_mk "wl_Var" [WORDP3AUX_dest_reg x] with Failure _ ->
  (* Const *)
  try if WORDP3AUX_is_word x then WORDP3AUX_mk "wl_Const" [x]
      else failwith "Const" with Failure _ ->
  (* Op *)
  try let c,name = find (fun (c,_) -> can (WORDP3AUX_dest_binop c) x)
                     WORDP3AUX_binops in
      let a,b = WORDP3AUX_dest_binop c x in
      let x1 = WORDP3AUX_get_exp a in
      let x2 = WORDP3AUX_get_exp b in
      WORDP3AUX_mk "wl_Op" [mk_const(name,[]); mk_list([x1;x2],type_of x1)]
  with Failure _ ->
  (* Shift *)
  try let c,name = find (fun (c,_) -> can (WORDP3AUX_dest_binop c) x)
                     WORDP3AUX_shifts in
      let a,n = WORDP3AUX_dest_binop c x in
      let x1 = WORDP3AUX_get_exp a in
      WORDP3AUX_mk "wl_Shift"
        [mk_const(name,[]); x1;
         WORDP3AUX_mk "wl_Const" [mk_comb(`word:num->A word`,n)]]
  with Failure _ ->
  (* ~ *)
  let f,r = dest_comb x in
  if fst (dest_const f) <> "word_not" then failwith "get_exp" else
  WORDP3AUX_get_exp (vsubst [r,`r:A word`]
    `word_xor (r:A word) (word_sub (word 0) (word 1))`);;

let WORDP3AUX_dest_reg_imm ri =
  try WORDP3AUX_mk "Reg" [WORDP3AUX_dest_reg ri] with Failure _ ->
  if WORDP3AUX_is_word ri then WORDP3AUX_mk "Imm" [ri]
  else failwith "dest_reg_imm";;

let WORDP3AUX_get_guard b =
  try
    let name =
      if can (WORDP3AUX_dest_binop "word_ult") b then `Lower` else
      if can (WORDP3AUX_dest_binop "word_ilt") b then `asm_Less` else
      if is_eq b && (try fst (dest_type (type_of (lhs b))) = "word"
                      with Failure _ -> false) then `asm_Equal`
      else failwith "get_guard" in
    let x1 = WORDP3AUX_dest_reg (rand (rator b)) in
    let x2 = WORDP3AUX_dest_reg_imm (rand b) in
    name,x1,x2
  with Failure _ ->
    let l,r = dest_eq b in
    let w,n = WORDP3AUX_dest_binop "word_and" l in
    if not (WORDP3AUX_is_word n && r = mk_comb(`word:num->A word`,`0`))
    then failwith "get_guard" else
    `asm_Test`,WORDP3AUX_dest_reg w,WORDP3AUX_dest_reg_imm n;;

(* the lets that are single instructions of the little language            *)

let WORDP3AUX_dest_lupdate_let tm =
  let (v,r),body = WORDP3AUX_dest_var_let tm in
  let f,args = strip_comb r in
  if not (is_const f && fst (dest_const f) = "LUPDATE" && length args = 3)
  then failwith "dest_lupdate_let" else
  let a = el 0 args and i = el 1 args and zs = el 2 args in
  let vn,vty = dest_var v and zn,zty = dest_var zs in
  if not (WORDP3AUX_base_name vn = WORDP3AUX_base_name zn && vty = zty)
  then failwith "dest_lupdate_let" else
  let vf,r0 = dest_comb i in
  if fst (dest_const vf) <> "val" then failwith "dest_lupdate_let" else
  a,r0,body;;

let WORDP3AUX_dest_el_let tm =
  let (v,r),body = WORDP3AUX_dest_var_let tm in
  let f,args = strip_comb r in
  if not (is_const f && fst (dest_const f) = "EL" && length args = 2)
  then failwith "dest_el_let" else
  let i = el 0 args and arr = el 1 args in
  let vf,y = dest_comb i in
  if fst (dest_const vf) <> "val" then failwith "dest_el_let" else
  let a = WORDP3AUX_base_name (fst (dest_var arr)) in
  let a = if a = "xs" then `In1` else if a = "ys" then `In2` else
          if a = "zs" then `Out` else failwith "dest_el_let" in
  v,y,a,body;;

(* let (a1,a2) = c x1 x2 x3 in body, for c = single_add_word, ...         *)

let WORDP3AUX_dest_single_let c tm =
  let (v,r),body = WORDP3AUX_dest_let tm in
  let f,args = strip_comb r in
  if not (is_const f && fst (dest_const f) = c && length args = 3)
  then failwith "dest_single_let" else
  let a1,a2 = dest_pair v in
  WORDP3AUX_dest_reg a1,WORDP3AUX_dest_reg a2,args,body;;

let WORDP3AUX_get_let tm =
  (* Load *)
  try let r,i,a,rest = WORDP3AUX_dest_el_let tm in
      WORDP3AUX_mk "word_bignum_Load"
        [WORDP3AUX_dest_reg r; WORDP3AUX_dest_reg i; a],rest
  with Failure _ ->
  (* Store *)
  try let r,i,rest = WORDP3AUX_dest_lupdate_let tm in
      WORDP3AUX_mk "word_bignum_Store"
        [WORDP3AUX_dest_reg r; WORDP3AUX_dest_reg i],rest
  with Failure _ ->
  (* Assign *)
  try let (v,x),rest = WORDP3AUX_dest_let tm in
      let n = WORDP3AUX_dest_reg v in
      let e = WORDP3AUX_get_exp x in
      WORDP3AUX_mk "word_bignum_Assign" [n; e],rest
  with Failure _ ->
  (* Swap *)
  try let (v,x),rest = WORDP3AUX_dest_let tm in
      if not (is_pair x) then failwith "Swap" else
      let xs = filter (fun c -> fst (dest_const c) <> ",")
                 (WORDP3AUX_find_terms is_const x) in
      if xs <> [] then failwith "Swap" else WORDP3AUX_Swap,rest
  with Failure _ ->
  (* Add *)
  try let a1,a2,args,rest =
        WORDP3AUX_dest_single_let "single_add_word" tm in
      let r1 = WORDP3AUX_dest_reg (el 0 args) in
      let r2 = WORDP3AUX_dest_reg_imm (el 1 args) in
      let r3 = WORDP3AUX_dest_reg_imm (el 2 args) in
      WORDP3AUX_mk "word_bignum_Add" [a1; a2; r1; r2; r3],rest
  with Failure _ ->
  (* Sub *)
  try let a1,a2,args,rest =
        WORDP3AUX_dest_single_let "single_sub_word" tm in
      let r1 = WORDP3AUX_dest_reg (el 0 args) in
      let r2 = WORDP3AUX_dest_reg_imm (el 1 args) in
      let r3 = WORDP3AUX_dest_reg_imm (el 2 args) in
      WORDP3AUX_mk "word_bignum_Sub" [a1; a2; r1; r2; r3],rest
  with Failure _ ->
  (* Mul *)
  try let a1,a2,args,rest =
        WORDP3AUX_dest_single_let "single_mul" tm in
      if el 2 args <> `word 0:A word` then failwith "Mul" else
      let r1 = WORDP3AUX_dest_reg (el 0 args) in
      let r2 = WORDP3AUX_dest_reg (el 1 args) in
      WORDP3AUX_mk "word_bignum_Mul" [a1; a2; r1; r2],rest
  with Failure _ ->
  (* Div *)
  let a1,a2,args,rest = WORDP3AUX_dest_single_let "single_div" tm in
  let r1 = WORDP3AUX_dest_reg (el 0 args) in
  let r2 = WORDP3AUX_dest_reg (el 1 args) in
  let r3 = WORDP3AUX_dest_reg (el 2 args) in
  WORDP3AUX_mk "word_bignum_Div" [a1; a2; r1; r2; r3],rest;;

(* the definitions made so far (HOL4's !code_defs, the latest first) and  *)
(* the functions translated so far with their code constants              *)

let WORDP3AUX_code_defs = ref ([]:thm list);;
let WORDP3AUX_prev_trans = ref ([]:(term * term) list);;

exception Wordp3aux_unable of string;;

let WORDP3AUX_dest_tuple tm =
  let rec f t = try let x,y = dest_pair t in f x @ f y with Failure _ -> [t] in
  f tm;;

let WORDP3AUX_mk_Seq(p1,p2) = WORDP3AUX_mk "word_bignum_Seq" [p1; p2];;

let WORDP3AUX_get_full_prog inp tm =
  let immediate_deps = ref ([]:term list) in
  let ret_tm = ref WORDP3AUX_Skip in
  let cont_tm = ref WORDP3AUX_Continue in
  let ret_vars = ref ([]:term list) in
  let cont_vars = ref ([]:term list) in
  (* helpers *)
  let dest_num_let tm =
    let (v,e),t = WORDP3AUX_dest_var_let tm in
    if type_of e = `:num` then t else failwith "dest_num_let" in
  let dest_num_if tm =
    let x,(y,z) = dest_cond tm in
    let l,r = dest_eq x in
    if type_of l = `:num` then z else failwith "dest_num_if" in
  let dest_num_let_or_if tm =
    try dest_num_if tm with Failure _ -> dest_num_let tm in
  let dest_rec_let tm =
    let (_,y),rest = WORDP3AUX_dest_let tm in
    let saves,call = dest_pair y in
    saves,call,rest in
  (* main function *)
  let rec get_prog tm =
    (* return *)
    if is_var tm || is_pair tm
    then (ret_vars := WORDP3AUX_free_vars tm; !ret_tm)
    else
    (* let *)
    try let x,rest = WORDP3AUX_get_let tm in
        let p = get_prog rest in WORDP3AUX_mk_Seq(x,p)
    with Failure _ ->
    (* previous translation *)
    try let (v,x),rest = WORDP3AUX_dest_let tm in
        let f = repeat rator x in
        let _,code = find (fun (c,_) -> is_const f &&
                             fst (dest_const c) = fst (dest_const f))
                       (!WORDP3AUX_prev_trans) in
        immediate_deps := code :: (!immediate_deps);
        let p = get_prog rest in WORDP3AUX_mk_Seq(code,p)
    with Failure _ ->
    (* recursive let *)
    try let saves,call,rest = dest_rec_let tm in
        let saves = map WORDP3AUX_dest_reg (WORDP3AUX_dest_tuple saves) in
        let saves = mk_list(saves,`:num`) in
        let dels = mk_list([],`:num`) in
        cont_vars := WORDP3AUX_free_vars call;
        let p = get_prog rest in
        WORDP3AUX_mk_Seq(WORDP3AUX_mk "Rec" [saves; dels],p)
    with Failure _ ->
    (* If *)
    try let b,(t1,t2) = dest_cond tm in
        let x1,x2,x3 = WORDP3AUX_get_guard b in
        let p1 = get_prog t1 in
        let p2 = get_prog t2 in
        WORDP3AUX_mk "word_bignum_If" [x1; x2; x3; p1; p2]
    with Failure _ ->
    if is_comb tm && is_const (rator tm) &&
       (is_var (rand tm) || is_pair (rand tm))
    then (cont_vars := WORDP3AUX_free_vars tm; !cont_tm) else
    if can dest_num_let_or_if tm then get_prog (dest_num_let_or_if tm) else
    let str = try let (v,x),rest = WORDP3AUX_dest_let tm in
                  fst (dest_const (repeat rator x))
              with Failure _ ->
                (Format.print_string "Unable to translate\n\n";
                 print_term tm; Format.print_string "\n\n";
                 Format.print_flush();
                 failwith "WORDP3AUX_get_full_prog: unable to translate") in
    raise (Wordp3aux_unable str) in
  (* compute deps *)
  let init_prog = get_prog tm in
  (* compute what vars are deleted or assigned *)
  let deps = filter (fun th -> mem (lhs (concl th)) (!immediate_deps))
                    (!WORDP3AUX_code_defs) in
  let x = list_mk_conj (mk_eq(init_prog,init_prog) ::
                        map concl deps @ [`T`]) in
  let is_delete tm =
    let f,args = strip_comb tm in
    is_const f && fst (dest_const f) = "Delete" && length args = 1 in
  let is_assign tm =
    let f,args = strip_comb tm in
    is_const f &&
    (let n = fst (dest_const f) and k = length args in
     (n = "word_bignum_Assign" || n = "word_bignum_Load") && k = 1 ||
     mem n ["word_bignum_Add"; "word_bignum_Sub"; "word_bignum_Mul";
            "word_bignum_Div"] && (k = 1 || k = 2)) in
  let f tm = try WORDP3AUX_dest_reg tm with Failure _ -> tm in
  let ds = WORDP3AUX_mk_set
             (map rand (WORDP3AUX_find_terms is_assign x) @
              flat (map (fun t -> dest_list (rand t))
                        (WORDP3AUX_find_terms is_delete x)) @
              filter (fun t -> not (is_var t))
                     (map f (WORDP3AUX_free_vars inp))) in
  let add_dels vs tm =
    if vs = [] then tm else
    WORDP3AUX_mk_Seq(WORDP3AUX_mk "Delete" [mk_list(vs,type_of (hd vs))],tm) in
  ret_tm := add_dels (WORDP3AUX_set_diff ds (map f (!ret_vars)))
                     WORDP3AUX_Skip;
  let cont_dels = WORDP3AUX_set_diff ds (map f (!cont_vars)) in
  cont_tm := add_dels cont_dels WORDP3AUX_Continue;
  let dels = mk_list(cont_dels,`:num`) in
  dels,get_prog tm;;

(* the equations of the functions that the translation may need (HOL4     *)
(* finds NAME_def in the theory database), at the word type :A            *)

let WORDP3AUX_defs = ref ([]:(string * thm) list);;

let rec WORDP3AUX_to_deep def =
  (* produce deep embedding *)
  let c = concl (SPEC_ALL def) in
  let f = repeat rator (lhs c) in
  let tm = rhs c in
  let inp = rand (lhs c) in
  let is_rec = can (find_term (fun t -> is_const t &&
                     fst (dest_const t) = fst (dest_const f))) tm in
  let rec loop () =
    try WORDP3AUX_get_full_prog inp tm
    with Wordp3aux_unable str ->
      (ignore (WORDP3AUX_to_deep (assoc (str ^ "_def") (!WORDP3AUX_defs)));
       loop ()) in
  let dels,deep = loop () in
  let rec_flag = if can (find_term WORDP3AUX_is_Rec) deep then `T` else `F` in
  let deep = if is_rec then WORDP3AUX_mk "word_bignum_Loop" [rec_flag; dels; deep]
             else deep in
  (* store deep embedding *)
  let name = fst (dest_const f) ^ "_code" in
  let code_def = new_definition (mk_eq(mk_var(name,type_of deep),deep)) in
  let code_const = lhs (concl code_def) in
  WORDP3AUX_code_defs := code_def :: (!WORDP3AUX_code_defs);
  WORDP3AUX_prev_trans := (f,code_const) :: (!WORDP3AUX_prev_trans);
  code_def;;

let WORDP3AUX_A th = INST_TYPE [`:A`,`:N`] th;;

let WORDP3AUX_mc_iadd1_def = prove
 (`!r1 r2 xs ys.
     mc_iadd1 (r1:A word,r2,xs,ys) =
     (let r0 = word 0 in
      if word_ult r1 r2 then
        (let (xs,ys) = (ys,xs) in
         let r0 = word 1 in
           (r1,r2,r0,xs,ys))
      else
        (let r8 = r1 in
         let r1 = r2 in
         let r2 = r8 in
           (r1,r2,r0,xs,ys)))`,
  REWRITE_TAC[mc_iadd1_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let WORDP3AUX_mc_iadd2_def = prove
 (`!r1 r2 r10 r12 xs ys.
     mc_iadd2 (r1:A word,r2,r10,r12,xs,ys) =
     (let r0 = word 0 in
      if r10 = word 1 then
        (let (xs,ys) = (ys,xs) in
         let r12 = word_xor r12 (word 1) in
         let r0 = word 1 in
           (r1,r2,r0,r12,xs,ys))
      else
        (let r8 = r1 in
         let r1 = r2 in
         let r2 = r8 in
           (r1,r2,r0,r12,xs,ys)))`,
  REWRITE_TAC[mc_iadd2_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let WORDP3AUX_mc_iadd3_def = prove
 (`!r0 xs ys.
     mc_iadd3 (r0:A word,xs,ys) =
     if r0 = word 0 then (xs,ys) else (let (xs,ys) = (ys,xs) in (xs,ys))`,
  REWRITE_TAC[mc_iadd3_def; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let WORDP3AUX_mc_fac_def = prove
 (`!l r1.
     mc_fac (l,r1:A word) =
     (let l0 = l in
      pair_CASE (mc_fac_init (l,r1)) (\l y1. pair_CASE y1 (\r0 y2.
        pair_CASE y2 (\r1 y3. pair_CASE y3 (\r2 r3.
      let l = MIN l l0 in
        if r0 = word 0 then (l,r1) else
          let r1 = r2 in
          if l = 0 then (l,r1) else
          pair_CASE ((r2,r3),mc_fac (l - 1,r1)) (\p q.
            pair_CASE p (\r2 r3. pair_CASE q (\l r1.
          let l = MIN l l0 in
          let r2 = r1 in
          let r1 = r3 in
          if l = 0 then (l,r1) else
          pair_CASE (r2,mc_fac (l - 1,r1)) (\r2 q. pair_CASE q (\l r1.
          pair_CASE (mc_fac_final (l,r1,r2)) (\l r1.
            (l,r1))))))))))))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [mc_fac_def] THEN
  CASE_REWRITE_TAC[] THEN REWRITE_TAC[]);;

WORDP3AUX_defs :=
  ["mc_cmp_def",WORDP3AUX_A mc_cmp_def;
   "mc_compare_def",WORDP3AUX_A mc_compare_def;
   "mc_icompare_def",WORDP3AUX_A mc_icompare_def;
   "mc_add_loop2_def",WORDP3AUX_A mc_add_loop2_def;
   "mc_add_loop1_def",WORDP3AUX_A mc_add_loop1_def;
   "mc_add_loop_def",WORDP3AUX_A mc_add_loop_def;
   "mc_add_def",WORDP3AUX_A mc_add_def;
   "mc_sub_loop2_def",WORDP3AUX_A mc_sub_loop2_def;
   "mc_sub_loop1_def",WORDP3AUX_A mc_sub_loop1_def;
   "mc_sub_loop_def",WORDP3AUX_A mc_sub_loop_def;
   "mc_fix_def",WORDP3AUX_A mc_fix_def;
   "mc_sub_def",WORDP3AUX_A mc_sub_def;
   "mc_iadd1_def",WORDP3AUX_mc_iadd1_def;
   "mc_iadd2_def",WORDP3AUX_mc_iadd2_def;
   "mc_iadd3_def",WORDP3AUX_mc_iadd3_def;
   "mc_iadd_def",WORDP3AUX_A mc_iadd_def;
   "mc_single_mul_add_def",WORDP3AUX_A mc_single_mul_add_def;
   "mc_mul_pass_def",WORDP3AUX_A mc_mul_pass_def;
   "mc_mul_def",WORDP3AUX_A mc_mul_def;
   "mc_mul_zero_def",WORDP3AUX_A mc_mul_zero_def;
   "mc_imul1_def",WORDP3AUX_A mc_imul1_def;
   "mc_imul_def",WORDP3AUX_A mc_imul_def;
   "mc_single_div_def",WORDP3AUX_A mc_single_div_def;
   "mc_simple_div_def",WORDP3AUX_A mc_simple_div_def;
   "mc_simple_div1_def",WORDP3AUX_A mc_simple_div1_def;
   "mc_calc_d_def",WORDP3AUX_A mc_calc_d_def;
   "mc_single_mul_def",WORDP3AUX_A mc_single_mul_def;
   "mc_mul_by_single2_def",WORDP3AUX_A mc_mul_by_single2_def;
   "mc_cmp3_def",WORDP3AUX_A mc_cmp3_def;
   "mc_cmp_mul2_def",WORDP3AUX_A mc_cmp_mul2_def;
   "mc_sub1_def",WORDP3AUX_A mc_sub1_def;
   "mc_cmp2_def",WORDP3AUX_A mc_cmp2_def;
   "mc_div_test_def",WORDP3AUX_A mc_div_test_def;
   "mc_div_r1_def",WORDP3AUX_A mc_div_r1_def;
   "mc_div_guess_def",WORDP3AUX_A mc_div_guess_def;
   "mc_adj_cmp_def",WORDP3AUX_A mc_adj_cmp_def;
   "mc_adjust_aux_def",WORDP3AUX_A mc_adjust_aux_def;
   "mc_div_adjust_def",WORDP3AUX_A mc_div_adjust_def;
   "mc_div_sub_def",WORDP3AUX_A mc_div_sub_def;
   "mc_div_sub_loop_def",WORDP3AUX_A mc_div_sub_loop_def;
   "mc_div_loop_def",WORDP3AUX_A mc_div_loop_def;
   "mc_mul_by_single_def",WORDP3AUX_A mc_mul_by_single_def;
   "mc_top_two_def",WORDP3AUX_A mc_top_two_def;
   "mc_copy_down_def",WORDP3AUX_A mc_copy_down_def;
   "mc_copy_over_def",WORDP3AUX_A mc_copy_over_def;
   "mc_div0_def",WORDP3AUX_A mc_div0_def;
   "mc_div1_def",WORDP3AUX_A mc_div1_def;
   "mc_div2_def",WORDP3AUX_A mc_div2_def;
   "mc_div3_def",WORDP3AUX_A mc_div3_def;
   "mc_div_def",WORDP3AUX_A mc_div_def;
   "mc_add1_def",WORDP3AUX_A mc_add1_def;
   "mc_add1_call_def",WORDP3AUX_A mc_add1_call_def;
   "mc_div_sub_aux1_def",WORDP3AUX_A mc_div_sub_aux1_def;
   "mc_div_sub_aux_def",WORDP3AUX_A mc_div_sub_aux_def;
   "mc_div_sub1_def",WORDP3AUX_A mc_div_sub1_def;
   "mc_div_sub_call_def",WORDP3AUX_A mc_div_sub_call_def;
   "mc_idiv_mod_header_def",WORDP3AUX_A mc_idiv_mod_header_def;
   "mc_idiv0_def",WORDP3AUX_A mc_idiv0_def;
   "mc_idiv_def",WORDP3AUX_A mc_idiv_def;
   "mc_isub_flip_def",WORDP3AUX_A mc_isub_flip_def;
   "mc_iop_def",WORDP3AUX_A mc_iop_def;
   "mc_fac_init_def",WORDP3AUX_A mc_fac_init_def;
   "mc_fac_final_def",WORDP3AUX_A mc_fac_final_def;
   "mc_fac_def",WORDP3AUX_mc_fac_def;
   "mc_use_fac_def",WORDP3AUX_A mc_use_fac_def];;


(* the translations of the script: each to_deep defines NAME_code for the  *)
(* function NAME and for the functions it calls that are not translated   *)
(* yet (HOL4's code_defs and prev_trans)                                   *)

let mc_cmp_code_def = WORDP3AUX_to_deep (WORDP3AUX_A mc_cmp_def);;
let mc_compare_code_def = WORDP3AUX_to_deep (WORDP3AUX_A mc_compare_def);;
let mc_idiv_code_def = WORDP3AUX_to_deep (WORDP3AUX_A mc_idiv_def);;
let mc_iadd_code_def = WORDP3AUX_to_deep (WORDP3AUX_A mc_iadd_def);;
let mc_imul_code_def = WORDP3AUX_to_deep (WORDP3AUX_A mc_imul_def);;
let mc_iop_code_def = WORDP3AUX_to_deep (WORDP3AUX_A mc_iop_def);;

(* HOL4 stores every definition NAME_code_def in the theory *)

let WORDP3AUX_code_def name =
  find (fun th -> fst (dest_const (lhs (concl th))) = name)
       (!WORDP3AUX_code_defs);;

let mc_mul_zero_code_def = WORDP3AUX_code_def "mc_mul_zero_code";;
let mc_copy_over_code_def = WORDP3AUX_code_def "mc_copy_over_code";;
let mc_div0_code_def = WORDP3AUX_code_def "mc_div0_code";;
let mc_single_div_code_def = WORDP3AUX_code_def "mc_single_div_code";;
let mc_simple_div_code_def = WORDP3AUX_code_def "mc_simple_div_code";;
let mc_div1_code_def = WORDP3AUX_code_def "mc_div1_code";;
let mc_calc_d_code_def = WORDP3AUX_code_def "mc_calc_d_code";;
let mc_single_mul_add_code_def = WORDP3AUX_code_def "mc_single_mul_add_code";;
let mc_mul_by_single_code_def = WORDP3AUX_code_def "mc_mul_by_single_code";;
let mc_single_mul_code_def = WORDP3AUX_code_def "mc_single_mul_code";;
let mc_top_two_code_def = WORDP3AUX_code_def "mc_top_two_code";;
let mc_div_r1_code_def = WORDP3AUX_code_def "mc_div_r1_code";;
let mc_mul_by_single2_code_def = WORDP3AUX_code_def "mc_mul_by_single2_code";;
let mc_cmp3_code_def = WORDP3AUX_code_def "mc_cmp3_code";;
let mc_cmp_mul2_code_def = WORDP3AUX_code_def "mc_cmp_mul2_code";;
let mc_sub1_code_def = WORDP3AUX_code_def "mc_sub1_code";;
let mc_cmp2_code_def = WORDP3AUX_code_def "mc_cmp2_code";;
let mc_div_test_code_def = WORDP3AUX_code_def "mc_div_test_code";;
let mc_div_guess_code_def = WORDP3AUX_code_def "mc_div_guess_code";;
let mc_adj_cmp_code_def = WORDP3AUX_code_def "mc_adj_cmp_code";;
let mc_adjust_aux_code_def = WORDP3AUX_code_def "mc_adjust_aux_code";;
let mc_div_adjust_code_def = WORDP3AUX_code_def "mc_div_adjust_code";;
let mc_div_sub_code_def = WORDP3AUX_code_def "mc_div_sub_code";;
let mc_div_sub_loop_code_def = WORDP3AUX_code_def "mc_div_sub_loop_code";;
let mc_div_loop_code_def = WORDP3AUX_code_def "mc_div_loop_code";;
let mc_simple_div1_code_def = WORDP3AUX_code_def "mc_simple_div1_code";;
let mc_fix_code_def = WORDP3AUX_code_def "mc_fix_code";;
let mc_copy_down_code_def = WORDP3AUX_code_def "mc_copy_down_code";;
let mc_div2_code_def = WORDP3AUX_code_def "mc_div2_code";;
let mc_div3_code_def = WORDP3AUX_code_def "mc_div3_code";;
let mc_div_code_def = WORDP3AUX_code_def "mc_div_code";;
let mc_add1_code_def = WORDP3AUX_code_def "mc_add1_code";;
let mc_add1_call_code_def = WORDP3AUX_code_def "mc_add1_call_code";;
let mc_div_sub_aux1_code_def = WORDP3AUX_code_def "mc_div_sub_aux1_code";;
let mc_div_sub_aux_code_def = WORDP3AUX_code_def "mc_div_sub_aux_code";;
let mc_div_sub1_code_def = WORDP3AUX_code_def "mc_div_sub1_code";;
let mc_div_sub_call_code_def = WORDP3AUX_code_def "mc_div_sub_call_code";;
let mc_idiv_mod_header_code_def = WORDP3AUX_code_def "mc_idiv_mod_header_code";;
let mc_idiv0_code_def = WORDP3AUX_code_def "mc_idiv0_code";;
let mc_iadd1_code_def = WORDP3AUX_code_def "mc_iadd1_code";;
let mc_add_loop1_code_def = WORDP3AUX_code_def "mc_add_loop1_code";;
let mc_add_loop2_code_def = WORDP3AUX_code_def "mc_add_loop2_code";;
let mc_add_loop_code_def = WORDP3AUX_code_def "mc_add_loop_code";;
let mc_add_code_def = WORDP3AUX_code_def "mc_add_code";;
let mc_iadd3_code_def = WORDP3AUX_code_def "mc_iadd3_code";;
let mc_iadd2_code_def = WORDP3AUX_code_def "mc_iadd2_code";;
let mc_sub_loop1_code_def = WORDP3AUX_code_def "mc_sub_loop1_code";;
let mc_sub_loop2_code_def = WORDP3AUX_code_def "mc_sub_loop2_code";;
let mc_sub_loop_code_def = WORDP3AUX_code_def "mc_sub_loop_code";;
let mc_sub_code_def = WORDP3AUX_code_def "mc_sub_code";;
let mc_imul1_code_def = WORDP3AUX_code_def "mc_imul1_code";;
let mc_mul_pass_code_def = WORDP3AUX_code_def "mc_mul_pass_code";;
let mc_mul_code_def = WORDP3AUX_code_def "mc_mul_code";;
let mc_isub_flip_code_def = WORDP3AUX_code_def "mc_isub_flip_code";;

(* all definitions made so far, the latest first *)

let all_code_defs = end_itlist CONJ (!WORDP3AUX_code_defs);;

(* an example that produces Rec *)

let mc_fac_init_code_def = WORDP3AUX_to_deep (WORDP3AUX_A mc_fac_init_def);;
let mc_fac_final_code_def = WORDP3AUX_to_deep (WORDP3AUX_A mc_fac_final_def);;
let mc_fac_code_def = WORDP3AUX_to_deep WORDP3AUX_mc_fac_def;;
let mc_use_fac_code_def = WORDP3AUX_to_deep (WORDP3AUX_A mc_use_fac_def);;

(* compiler into wordLang *)

let has_compiled_def = cake_def
  `has_compiled (code:A) (n,code_list:(A#num#B)list) =
     match ALOOKUP code_list code with
       NONE -> INR (n:num)
     | SOME (index,word_code) -> INL (index:num)`;;

let code_acc_next_def = cake_def
  `code_acc_next (n,code_list:A) = (n + 1,code_list)`;;

let install_def = cake_def
  `install (c:A) (n:B,code_list) = (n,CONS c code_list)`;;

let word_bignum_compile_exp_def = cake_def
  `(word_bignum_compile_exp (wl_Op b [x1;x2]) =
      wl_Op b [word_bignum_compile_exp x1; word_bignum_compile_exp x2]) /\
   (word_bignum_compile_exp (wl_Var n) = Lookup (Temp (word n)):(A)wl_exp) /\
   (word_bignum_compile_exp (wl_Const w) = wl_Const w) /\
   (word_bignum_compile_exp (wl_Shift sh x y) =
      wl_Shift sh (word_bignum_compile_exp x) (word_bignum_compile_exp y)) /\
   (word_bignum_compile_exp _ = wl_Const (word 0))`;;

let word_bignum_compile_exp_ind = cake_ind "word_bignum_compile_exp";;

let TempIn1_def = cake_def
  `TempIn1 = Temp (word 31)`;;

let TempIn2_def = cake_def
  `TempIn2 = Temp (word 30)`;;

let TempOut_def = cake_def
  `TempOut = Temp (word 29)`;;

let SeqTemp_def = cake_def
  `SeqTemp i r (p:(A)wl_prog) = wl_Seq (wl_Assign i (Lookup (Temp (word r)))) p`;;

let SeqTempImm_def = cake_def
  `(SeqTempImm i (Reg r) (p:(A)wl_prog) = SeqTemp i r p) /\
   (SeqTempImm i (Imm w) p = wl_Seq (wl_Assign i (wl_Const w)) p)`;;

let SeqTempImmNot_def = cake_def
  `(SeqTempImmNot i (Reg r) (p:(A)wl_prog) =
      SeqTemp i r (wl_Seq (wl_Assign i (wl_Op asm_Xor [wl_Var i;
                                                       wl_Const (word_not (word 0))])) p)) /\
   (SeqTempImmNot i (Imm w) p = wl_Seq (wl_Assign i (wl_Const (word_not w))) p)`;;

let SeqIndex_def = cake_def
  `SeqIndex i r arr (p:(A)wl_prog) =
     let t = (match arr with Out -> TempOut | In2 -> TempIn2 | In1 -> TempIn1) in
       wl_Seq (wl_Assign i (wl_Op asm_Add
         [Lookup t;
          wl_Shift Lsl (Lookup (Temp (word r)))
                   (wl_Const (word (backend_common_word_shift (:A))))])) p`;;

let div_location_def = cake_def
  `div_location = 23`;;

let DivCode_def = cake_def
  `DivCode l1 l2 n1 n2 n3 n4 n5 =
     MustTerminate
       (wl_Seq (wl_Call (SOME ([n1],(LS one,LN),wl_Skip,l1,l2)) (SOME div_location)
                        [n3;n4;n5] NONE)
               (wl_Assign n2 (Lookup (Temp (word 28))))):(A)wl_prog`;;

let LoadRegs_def = cake_def
  `(LoadRegs [] (p:(A)wl_prog) = p) /\
   (LoadRegs (CONS n ns) p = wl_Seq (wl_Get (n + 2) (Temp (word n))) (LoadRegs ns p))`;;

let SaveRegs_def = cake_def
  `(SaveRegs [] = wl_Skip:(A)wl_prog) /\
   (SaveRegs (CONS n ns) = wl_Seq (wl_Set (Temp (word n)) (wl_Var (n + 2))) (SaveRegs ns))`;;

new_type_abbrev("WORDP3AUX_cty",
  `:num->num->num->num#((A)mini#num#(A)wl_prog)list->(A)mini->
    (A)wl_prog#num#num#num#((A)mini#num#(A)wl_prog)list`);;

let word_bignum_compile_def = sem1aux_def (list_mk_conj
  [`((word_bignum_compile:WORDP3AUX_cty) n l i cs word_bignum_Skip =
      (wl_Skip:(A)wl_prog,l,i,cs))`;
   `((word_bignum_compile:WORDP3AUX_cty) n l i cs word_bignum_Continue =
      (wl_Call NONE (SOME n) [0] NONE,l,i,cs))`;
   `((word_bignum_compile:WORDP3AUX_cty) n l i cs (Rec save_regs names) =
      (LoadRegs save_regs
        (wl_Call (SOME ([1],(LS one,list_insert (MAP (\n. n + 2) save_regs) LN),
                        SaveRegs save_regs,n,l)) (SOME n) [] NONE),l + 1,i,cs))`;
   `((word_bignum_compile:WORDP3AUX_cty) n l i cs (word_bignum_Loop rec_calls vs body) =
      match has_compiled body cs with
        INL existing_index ->
          (wl_Call (SOME ([i],(LS one,LN),wl_Skip,n,l)) (SOME existing_index) [] NONE,
           l + 1,i + 1,cs)
      | INR new_index ->
          let (new_code,a,b,cs) =
            word_bignum_compile new_index 2 1 (code_acc_next cs) body in
          (wl_Call (SOME ([i],(LS one,LN),wl_Skip,n,l)) (SOME new_index) [] NONE,
           l + 1,i + 1,install (body,new_index,new_code) cs))`;
   `((word_bignum_compile:WORDP3AUX_cty) n l i cs (LoopBody b) = word_bignum_compile n l i cs b)`;
   `((word_bignum_compile:WORDP3AUX_cty) n l i cs (word_bignum_Seq p1 p2) =
      let (p1,l,i,cs) = word_bignum_compile n l i cs p1 in
      let (p2,l,i,cs) = word_bignum_compile n l i cs p2 in
        (wl_Seq p1 p2,l,i,cs))`;
   `((word_bignum_compile:WORDP3AUX_cty) n l i cs (word_bignum_If t r ri p1 p2) =
      let (p1,l,i,cs) = word_bignum_compile n l i cs p1 in
      let (p2,l,i,cs) = word_bignum_compile n l i cs p2 in
        match ri with
          Reg r2 -> (SeqTemp i r (SeqTemp (i + 1) r2 (wl_If t i (Reg (i + 1)) p1 p2)),
                     l,i + 2,cs)
        | Imm im -> (SeqTemp i r (wl_If t i ri p1 p2),l,i + 1,cs))`;
   `((word_bignum_compile:WORDP3AUX_cty) n l i cs (word_bignum_Assign j e) =
      (wl_Seq (wl_Assign i (word_bignum_compile_exp e)) (wl_Set (Temp (word j)) (wl_Var i)),
       l,i + 1,cs))`;
   `((word_bignum_compile:WORDP3AUX_cty) n l i cs (Delete _) = (wl_Skip:(A)wl_prog,l,i,cs))`;
   `((word_bignum_compile:WORDP3AUX_cty) n l i cs Swap =
      (wl_Seq (wl_Assign i (Lookup TempIn1))
       (wl_Seq (wl_Set TempIn1 (Lookup TempIn2))
               (wl_Set TempIn2 (wl_Var i))),l,i + 1,cs))`;
   `((word_bignum_compile:WORDP3AUX_cty) n l i cs (word_bignum_Store r1 r2) =
      (SeqTemp i r1
       (SeqIndex (i + 1) r2 Out
          (wl_Store (wl_Var (i + 1)) i)),l,i + 2,cs))`;
   `((word_bignum_compile:WORDP3AUX_cty) n l i cs (word_bignum_Load r1 r2 arr) =
      (SeqIndex i r2 arr
       (wl_Seq (wl_Assign (i + 1) (wl_Load (wl_Var i)))
               (wl_Set (Temp (word r1)) (wl_Var (i + 1)))),l,i + 2,cs))`;
   `((word_bignum_compile:WORDP3AUX_cty) n l i cs (word_bignum_Add r0 r1 r2 r3 r4) =
      (SeqTempImm (i + 4) r4 (SeqTempImm (i + 3) r3 (SeqTemp (i + 2) r2
       (wl_Seq (wl_Inst (asm_Arith (asm_AddCarry (i + 1) (i + 2) (i + 3) (i + 4))))
       (wl_Seq (wl_Set (Temp (word r0)) (wl_Var (i + 1)))
               (wl_Set (Temp (word r1)) (wl_Var (i + 4))))))),l,i + 5,cs))`;
   `((word_bignum_compile:WORDP3AUX_cty) n l i cs (word_bignum_Sub r0 r1 r2 r3 r4) =
      (SeqTempImm (i + 4) r4 (SeqTempImmNot (i + 3) r3 (SeqTemp (i + 2) r2
       (wl_Seq (wl_Inst (asm_Arith (asm_AddCarry (i + 1) (i + 2) (i + 3) (i + 4))))
       (wl_Seq (wl_Set (Temp (word r0)) (wl_Var (i + 1)))
               (wl_Set (Temp (word r1)) (wl_Var (i + 4))))))),l,i + 5,cs))`;
   `((word_bignum_compile:WORDP3AUX_cty) n l i cs (word_bignum_Mul r0 r1 r2 r3) =
      (SeqTemp (i + 3) r3 (SeqTemp (i + 2) r2
       (wl_Seq (wl_Inst (asm_Arith (LongMul (i + 0) (i + 1) (i + 2) (i + 3))))
       (wl_Seq (wl_Set (Temp (word r1)) (wl_Var (i + 0)))
               (wl_Set (Temp (word r0)) (wl_Var (i + 1)))))),l,i + 4,cs))`;
   `((word_bignum_compile:WORDP3AUX_cty) n l i cs (word_bignum_Div r0 r1 r2 r3 r4) =
      (SeqTemp (i + 4) r4 (SeqTemp (i + 3) r3 (SeqTemp (i + 2) r2
       (wl_Seq (DivCode n l (i + 0) (i + 1) (i + 2) (i + 3) (i + 4))
       (wl_Seq (wl_Set (Temp (word r0)) (wl_Var (i + 0)))
               (wl_Set (Temp (word r1)) (wl_Var (i + 1))))))),l + 1,i + 5,cs))`;
   `((word_bignum_compile:WORDP3AUX_cty) n l i cs _ = (wl_Skip,l,i,cs))`]);;

remove_type_abbrev "WORDP3AUX_cty";;

let word_bignum_compile_ind = cake_ind "word_bignum_compile";;

let generated_bignum_stubs_def = cake_def
  `generated_bignum_stubs n =
     let (x1,l1,i1,(n1,cs)) =
       word_bignum_compile n 2 1 (n + 1,[]) (mc_iop_code:(A)mini) in
       CONS (n,1,wl_Seq x1 (wl_Return 0 [0]))
            (MAP (\p. match p with (x,y,z) -> (y,1,wl_Seq z (wl_Return 0 [0]))) cs)`;;

(* HOL4: EVAL ``generated_bignum_stubs n`` |> SIMP_RULE std_ss              *)
(* [GSYM ADD_ASSOC].  The evaluation below is HOL Light's call-by-value     *)
(* Compute (HOL4's computeLib) with the definitions used by                 *)
(* generated_bignum_stubs, numeral arithmetic, and an equality test for the *)
(* ground terms of the datatypes (distinctness and injectivity, as HOL4's   *)
(* EVAL); backend_common_word_shift (:A) is not unfolded.  The result lists *)
(* the 23 stubs n, n + 22, ..., n + 1 with their code.                      *)

let WORDP3AUX_eq_convs = (Hashtbl.create 20 : (string,conv) Hashtbl.t);;

let WORDP3AUX_type_eq_conv tyname =
  try Hashtbl.find WORDP3AUX_eq_convs tyname with Not_found ->
  let dths = try CONJUNCTS (distinctness tyname) with Failure _ -> [] in
  let dths = map (EQF_INTRO o SPEC_ALL) dths @
             map (EQF_INTRO o SPEC_ALL o GSYM) dths in
  let iths = try CONJUNCTS (injectivity tyname) with Failure _ -> [] in
  let iths = if tyname = "prod" then [PAIR_EQ] else iths in
  let conv = GEN_REWRITE_CONV I (dths @ iths) in
  Hashtbl.add WORDP3AUX_eq_convs tyname conv; conv;;

let WORDP3AUX_EQ_CONV tm =
  let l,r = dest_eq tm in
  if l = r then EQT_INTRO (REFL l) else
  let tyname = try fst (dest_type (type_of l)) with Failure _ ->
                 failwith "WORDP3AUX_EQ_CONV" in
  if tyname = "num" then NUM_EQ_CONV tm else
  WORDP3AUX_type_eq_conv tyname tm;;

let WORDP3AUX_stubs_cs =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  num_compute_add_convs cs;
  Compute.add_conv (`(=):A->A->bool`,2,WORDP3AUX_EQ_CONV) cs;
  Compute.add_thms
    ([generated_bignum_stubs_def; word_bignum_compile_def; has_compiled_def;
      ALOOKUP_THM; code_acc_next_def; install_def; word_bignum_compile_exp_def;
      TempIn1_def; TempIn2_def; TempOut_def; SeqTemp_def; SeqTempImm_def;
      SeqTempImmNot_def; SeqIndex_def; div_location_def; DivCode_def;
      LoadRegs_def; SaveRegs_def; list_insert_def; insert_def; MAP;
      LET_END_DEF; case_def "option"; case_def "prod"; case_def "sum";
      case_def "reg_imm"; case_def "address"] @ !WORDP3AUX_code_defs) cs;
  cs;;

let generated_bignum_stubs_eq =
  CONV_RULE (RAND_CONV (REWRITE_CONV[GSYM ADD_ASSOC] THENC NUM_REDUCE_CONV))
    (Compute.CBV_CONV WORDP3AUX_stubs_cs
       `generated_bignum_stubs n:(num#num#(A)wl_prog)list`);;
