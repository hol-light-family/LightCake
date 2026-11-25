(* ========================================================================= *)
(* alist_treeLib: port of HOL4 src/finite_maps/alist_treeLib.sml (the HOL4   *)
(* library of CakeML v3479's ml_progLib).  Partial functions of type         *)
(* A -> B option are represented by association lists sorted by an          *)
(* irreflexive transitive relation R and kept as balanced count_append trees *)
(* (theory hol4/alist_tree.ml); applications f x of represented functions    *)
(* are then evaluated with O(log n) inference steps and at most two proofs   *)
(* of R between concrete keys.                                               *)
(*                                                                           *)
(* The algorithm is HOL4's, step by step (build_insert, balance, mk_repr,    *)
(* add_alist_repr, build_lookup, reprs_conv).  Differences, all forced by    *)
(* HOL Light: OCaml names take the prefix alist_tree_ (one OCaml name space  *)
(* for the whole build); the dictionary of a repr set is a hash table on     *)
(* terms; the comparison of keys is an OCaml function returning an int;    *)
(* library theorems are instantiated by the names of their variables         *)
(* (alist_tree_ISPECL_NAMED), so that the order of their quantifiers does    *)
(* not matter; conversions return a reflexivity theorem where HOL4 raises    *)
(* UNCHANGED.                                                                *)
(* ========================================================================= *)

needs "hol4/alist_tree.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Syntax                                                                    *)
(* ------------------------------------------------------------------------- *)

let alist_tree_is_const_named s tm = is_const tm && fst (dest_const tm) = s;;

let alist_tree_alookup_tm = mk_const ("ALOOKUP",[]);;
let alist_tree_option_choice_tm = mk_const ("option_choice_f",[]);;
let alist_tree_repr_tm = mk_const ("sorted_alist_repr",[]);;

let alist_tree_is_nil tm = alist_tree_is_const_named "NIL" tm;;

(* parsed once: a quotation inside a function is parsed at every call *)
let alist_tree_T_tm = `T`;;

(* SPEC_ALL, then instantiation of the variables with the given names (and  *)
(* the type instantiation that this needs)                                  *)
let alist_tree_ISPECL_NAMED (l:(string * term) list) th =
  let th = SPEC_ALL th in
  let vs = frees (concl th) in
  let pick (n,t) =
    let v = try find (fun v -> fst (dest_var v) = n) vs
            with Failure _ -> failwith ("alist_tree_ISPECL_NAMED: no variable " ^ n) in
    v,t in
  let prs = map pick l in
  let tyin = itlist (fun (v,t) i -> type_match (type_of v) (type_of t) i) prs [] in
  let th = INST_TYPE tyin th in
  INST (map (fun (v,t) -> (t, inst tyin v)) prs) th;;

(* the same, with the theorem stripped and type-instantiated once per list  *)
(* of names and argument types (the steps below instantiate the same few     *)
(* lemmas at the same types many times)                                       *)
let alist_tree_inst_cache =
  (Hashtbl.create 100 : (string * string list * hol_type list, thm * term list) Hashtbl.t);;

let alist_tree_fast_inst lname th (l:(string * term) list) =
  let ns = map fst l and ts = map snd l in
  let key = (lname, ns, map type_of ts) in
  let sth,vars =
    try Hashtbl.find alist_tree_inst_cache key with Not_found ->
      let th' = SPEC_ALL th in
      let vs = frees (concl th') in
      let pick n = try find (fun v -> fst (dest_var v) = n) vs
                   with Failure _ -> failwith ("alist_tree_fast_inst: no variable " ^ n) in
      let prs = map (fun (n,t) -> pick n, t) l in
      let tyin = itlist (fun (v,t) i -> type_match (type_of v) (type_of t) i) prs [] in
      let r = INST_TYPE tyin th', map (fun (v,_) -> inst tyin v) prs in
      Hashtbl.add alist_tree_inst_cache key r; r in
  INST (map2 (fun v t -> (t,v)) vars ts) sth;;

(* the arguments of the conclusion of th, a constant of the given name and   *)
(* arity applied to them                                                      *)
let alist_tree_concl_args name n th =
  let f,xs = strip_comb (concl th) in
  if alist_tree_is_const_named name f && length xs = n then xs
  else failwith ("alist_tree_concl_args: " ^ name);;

(* ------------------------------------------------------------------------- *)
(* The repr set object                                                       *)
(* ------------------------------------------------------------------------- *)

(* a hash table on terms: the hash looks at the names of the constants and  *)
(* variables near the root only, equality is alpha-equivalence              *)
let alist_tree_term_hash tm =
  let rec go d tm acc =
    if d = 0 then acc else
    match tm with
      Var(s,_) -> Hashtbl.hash (acc,1,s)
    | Const(s,_) -> Hashtbl.hash (acc,2,s)
    | Comb(f,x) -> go (d - 1) x (go (d - 1) f (acc + 3))
    | Abs(_,b) -> go (d - 1) b (acc + 5) in
  go 8 tm 0;;

module Alist_tree_termtab = Hashtbl.Make (struct
  type t = term
  let equal s t = aconv s t
  let hash = alist_tree_term_hash
end);;

type 'a alist_reprs =
  { alr_R_thm : thm;                (* |- irreflexive R /\ transitive R *)
    alr_conv : conv;                (* proves R x y (and x = x) as  = T  *)
    alr_dest : term -> 'a;          (* keys as OCaml values *)
    alr_cmp : 'a -> 'a -> int;      (* their order, consistent with R *)
    alr_dict : thm Alist_tree_termtab.t };;

let alist_tree_mk_alist_reprs r_thm conv dest cmp =
  { alr_R_thm = r_thm; alr_conv = conv; alr_dest = dest; alr_cmp = cmp;
    alr_dict = Alist_tree_termtab.create 1000 };;

let alist_tree_peek_functions_in_rs rs =
  Alist_tree_termtab.fold (fun k _ acc -> k :: acc) rs.alr_dict [];;

let alist_tree_peek_repr rs tm =
  try Some (Alist_tree_termtab.find rs.alr_dict tm) with Not_found -> None;;

(* ------------------------------------------------------------------------- *)
(* Constructing is_insert theorems                                           *)
(* ------------------------------------------------------------------------- *)

let rec alist_tree_find_key_rec is_last ts =
  match ts with
    [] -> failwith "alist_tree_find_key_rec: empty"
  | t::ts ->
      if alist_tree_is_nil t then alist_tree_find_key_rec is_last ts else
      let f,xs = strip_comb t in
      if alist_tree_is_const_named "count_append" f then
        let ys = tl xs in
        alist_tree_find_key_rec is_last ((if is_last then rev ys else ys) @ ts)
      else
        let l = dest_list t in
        if is_last then last l else hd l;;

let alist_tree_hd_key t = fst (dest_pair (alist_tree_find_key_rec false [t]));;
let alist_tree_last_key t = fst (dest_pair (alist_tree_find_key_rec true [t]));;

let alist_tree_simp_count_append =
  REWRITE_CONV [count_append_HD_LAST; FST];;

let rec alist_tree_assume_prems th =
  if not (is_imp (concl th)) then th else
  let th = CONV_RULE (LAND_CONV alist_tree_simp_count_append) th in
  let l_asm = fst (dest_imp (concl th)) in
  let prem = if l_asm = alist_tree_T_tm then TRUTH else ASSUME l_asm in
  alist_tree_assume_prems (MP th prem);;

(* HOL4 do_inst_mp: match the antecedent of mp_thm against arg_thm, also   *)
(* instantiating the variables of insts (given at the matched types)       *)
let alist_tree_do_inst_mp (insts:(string * term) list) mp_thm arg_thm =
  let prem = fst (dest_imp (concl mp_thm)) in
  let _,tminst,tyinst =
    try term_match [] prem (concl arg_thm)
    with Failure s -> failwith ("alist_tree_do_inst_mp: match: " ^ s) in
  let ith = INST_TYPE tyinst mp_thm in
  let fvs = frees (concl ith) in
  let more = map (fun (n,t) ->
      let v = try find (fun v -> fst (dest_var v) = n) fvs
              with Failure _ -> failwith ("alist_tree_do_inst_mp: no variable " ^ n) in
      (t,v)) insts in
  let ith = INST (tminst @ more) ith in
  try MP ith arg_thm with Failure s -> failwith ("alist_tree_do_inst_mp: MP: " ^ s);;

let alist_tree_build_insert dest cmp r k x =
  let dest_k = dest k in
  let chk th =
    if alist_tree_is_const_named "is_insert" (fst (strip_comb (concl th))) then th
    else failwith "alist_tree_build_insert: check" in
  let pp th = chk (alist_tree_assume_prems th) in
  let rec build t =
    if alist_tree_is_nil t then
      pp (alist_tree_fast_inst "is_insert_to_empty" is_insert_to_empty ["R",r; "k",k; "x",x])
    else if is_cons t then
      let xs = dest_list t in
      let _ = length xs = 1 || failwith "alist_tree_build_insert: malformed" in
      let v = hd xs in
      let c = cmp dest_k (dest (fst (dest_pair v))) in
      if c = 0 then
        pp (alist_tree_fast_inst "is_insert_overwrite" is_insert_overwrite
              ["R",r; "k",k; "x",x; "v",v])
      else if c > 0 then
        pp (alist_tree_fast_inst "is_insert_far_right" is_insert_far_right
              ["R",r; "k",k; "x",x; "xs",t])
      else
        pp (alist_tree_fast_inst "is_insert_far_left" is_insert_far_left
              ["R",r; "k",k; "x",x; "xs",t])
    else
      let f,xs = strip_comb t in
      let _ = alist_tree_is_const_named "count_append" f ||
              failwith "alist_tree_build_insert: unknown" in
      let n,l,rr = match xs with [n;l;rr] -> n,l,rr
                   | _ -> failwith "alist_tree_build_insert: num args" in
      if not (cmp dest_k (dest (alist_tree_hd_key rr)) < 0) then
        (* is_insert T fr R k x r r' ==> ... *)
        let sub = build rr in
        let a = alist_tree_concl_args "is_insert" 7 sub in
        MP (alist_tree_fast_inst "is_insert_r" is_insert_r
              ["n",n; "fr",el 1 a; "R",el 2 a; "k",el 3 a; "x",el 4 a; "l",l;
               "r",el 5 a; "r'",el 6 a]) sub
      else if cmp dest_k (dest (alist_tree_last_key l)) > 0 then
        pp (alist_tree_fast_inst "is_insert_centre" is_insert_centre
              ["R",r; "n",n; "k",k; "x",x; "l",l; "r",rr])
      else
        (* is_insert fl T R k x l l' ==> ... *)
        let sub = build l in
        let a = alist_tree_concl_args "is_insert" 7 sub in
        MP (alist_tree_fast_inst "is_insert_l" is_insert_l
              ["n",n; "fl",el 0 a; "R",el 2 a; "k",el 3 a; "x",el 4 a; "l",el 5 a;
               "l'",el 6 a; "r",rr]) sub in
  build;;

let alist_tree_prove_assum_by_conv conv th =
  let x,_ = dest_imp (concl th) in
  let eq = conv x in
  try MP th (EQT_ELIM eq) with Failure _ ->
    failwith ("alist_tree_prove_assum_by_conv: " ^ string_of_term x ^
              " reduced only to " ^ string_of_term (rand (concl eq)));;

(* ------------------------------------------------------------------------- *)
(* Balancing count_append trees                                              *)
(* ------------------------------------------------------------------------- *)

let alist_tree_get_depth tm =
  let f,xs = strip_comb tm in
  if alist_tree_is_const_named "count_append" f then dest_small_numeral (hd xs)
  else if is_cons tm then 1
  else failwith "alist_tree_get_depth: unknown";;

let alist_tree_is_arb tm = alist_tree_is_const_named "ARB" tm;;

(* count_append i (count_append j xs ys) zs = count_append ARB xs (...) *)
let alist_tree_balance_r_conv tm =
  match strip_comb tm with
    _,[i;l;zs] ->
      (match strip_comb l with
         _,[j;xs;ys] -> alist_tree_fast_inst "balance_r" balance_r
                          ["i",i; "j",j; "xs",xs; "ys",ys; "zs",zs]
       | _ -> failwith "alist_tree_balance_r_conv")
  | _ -> failwith "alist_tree_balance_r_conv";;

let alist_tree_balance_l_conv tm =
  match strip_comb tm with
    _,[i;xs;r] ->
      (match strip_comb r with
         _,[j;ys;zs] -> alist_tree_fast_inst "balance_l" balance_l
                          ["i",i; "j",j; "xs",xs; "ys",ys; "zs",zs]
       | _ -> failwith "alist_tree_balance_l_conv")
  | _ -> failwith "alist_tree_balance_l_conv";;

let alist_tree_set_count_conv sz tm =
  match strip_comb tm with
    _,[i;xs;ys] -> alist_tree_fast_inst "set_count" set_count
                     ["i",i; "xs",xs; "ys",ys; "j",sz]
  | _ -> failwith "alist_tree_set_count_conv";;

let rec alist_tree_balance iter bias tm =
  if iter > 1000 then failwith "alist_tree_balance: looping" else
  let f,xs = strip_comb tm in
  if not (alist_tree_is_const_named "count_append" f) then REFL tm else
  if not (alist_tree_is_arb (hd xs)) && bias = "N" then REFL tm else
  let step_conv = RAND_CONV (alist_tree_balance 0 "N") THENC
                  RATOR_CONV (RAND_CONV (alist_tree_balance 0 "N")) in
  let th = step_conv tm in
  let tm = rhs (concl th) in
  let l_sz = alist_tree_get_depth (rand (rator tm))
  and r_sz = alist_tree_get_depth (rand tm) in
  let reb = if l_sz > r_sz + 1 || (bias = "R" && l_sz > r_sz) then "R"
            else if r_sz > l_sz + 1 || (bias = "L" && r_sz > l_sz) then "L"
            else "N" in
  let conv1 = if reb = "R" then RATOR_CONV (RAND_CONV (alist_tree_balance 0 "L"))
              else if reb = "L" then RAND_CONV (alist_tree_balance 0 "R")
              else ALL_CONV in
  let conv2 = if reb = "R" then alist_tree_balance_r_conv
              else if reb = "L" then alist_tree_balance_l_conv else ALL_CONV in
  let th = CONV_RULE (RAND_CONV (conv1 THENC conv2 THENC step_conv)) th in
  let tm = rhs (concl th) in
  let l_sz = alist_tree_get_depth (rand (rator tm))
  and r_sz = alist_tree_get_depth (rand tm) in
  let sz = mk_small_numeral (1 + max l_sz r_sz) in
  let set = alist_tree_set_count_conv sz in
  let final = if abs (l_sz - r_sz) < 2 then set
              else alist_tree_balance (iter + 1) "N" in
  CONV_RULE (RAND_CONV final) th;;

let alist_tree_prove_insert r conv dest cmp k x al =
  let th = alist_tree_build_insert dest cmp r k x al in
  let rec prove th =
    if not (is_imp (concl th)) then th
    else prove (alist_tree_prove_assum_by_conv conv th) in
  CONV_RULE (RAND_CONV (alist_tree_balance 0 "N")) (prove (DISCH_ALL th));;

(* ------------------------------------------------------------------------- *)
(* Making repr theorems                                                      *)
(* ------------------------------------------------------------------------- *)

let alist_tree_mk_insert_repr rs prev_repr k_x =
  let k,x = dest_pair k_x in
  let r,al = match snd (strip_comb (concl prev_repr)) with
               [r;al;_] -> r,al
             | _ -> failwith "alist_tree_mk_insert_repr: unexpected" in
  let ins = alist_tree_prove_insert r rs.alr_conv rs.alr_dest rs.alr_cmp k x al in
  (* sorted_alist_repr R al f /\ is_insert fl fr R k x al al' ==> ... *)
  let f = rand (concl prev_repr) in
  let a = alist_tree_concl_args "is_insert" 7 ins in
  MP (alist_tree_fast_inst "repr_insert" repr_insert
        ["R",r; "al",al; "f",f; "fl",el 0 a; "fr",el 1 a; "k",el 3 a; "x",el 4 a;
         "al'",el 6 a])
     (CONJ prev_repr ins);;

(* ALOOKUP [] -> Some None, ALOOKUP [y] -> Some (Some y), else None *)
let alist_tree_dest_alookup_single tm =
  let f,xs = strip_comb tm in
  if not (length xs = 1 && alist_tree_is_const_named "ALOOKUP" f) then None
  else if alist_tree_is_nil (hd xs) then Some None
  else match (try Some (dest_cons (hd xs)) with Failure _ -> None) with
         Some (y,ys) -> if alist_tree_is_nil ys then Some (Some y) else None
       | None -> None;;

let alist_tree_sorted_conv = REWRITE_CONV [SORTED_DEF; MAP; FST];;

let alist_tree_merge_conv =
  CHANGED_CONV (REWRITE_CONV [alookup_to_option_choice; option_choice_f_assoc;
                              alookup_empty_option_choice_f; count_append_def;
                              alookup_append_option_choice_f; empty_is_ALOOKUP]);;

let rec alist_tree_mk_repr_step rs tm =
  let f,xs = strip_comb tm in
  let is_short = not (alist_tree_dest_alookup_single tm = None) in
  let is_merge = alist_tree_is_const_named "option_choice_f" f && length xs = 2 in
  let is_repr_merge = is_merge && alist_tree_peek_repr rs (hd xs) <> None in
  let is_insert,insert_tm =
    if not is_merge then false,alist_tree_T_tm else
    match alist_tree_dest_alookup_single (hd xs) with
      Some (Some t) -> true,t
    | _ -> false,alist_tree_T_tm in
  if is_short then
    let r = rand (rand (rator (concl rs.alr_R_thm))) in
    let th = MP (alist_tree_fast_inst "alist_repr_refl" alist_repr_refl ["al",hd xs; "R",r])
                rs.alr_R_thm in
    alist_tree_prove_assum_by_conv alist_tree_sorted_conv th
  else if is_insert then
    alist_tree_mk_insert_repr rs (alist_tree_mk_repr rs (last xs)) insert_tm
  else if is_repr_merge then
    let l_repr_thm = alist_tree_mk_repr rs (hd xs) in
    let l_repr_al = rand (rator (concl l_repr_thm)) in
    let look = mk_icomb (alist_tree_alookup_tm, l_repr_al) in
    let half_repr = mk_icomb (mk_icomb (alist_tree_option_choice_tm, look), last xs) in
    let next_repr = alist_tree_mk_repr rs half_repr in
    (* sorted_alist_repr R al f /\ sorted_alist_repr R al' (option_choice_f   *)
    (* (ALOOKUP al) g) ==> sorted_alist_repr R al' (option_choice_f f g)       *)
    let a1 = alist_tree_concl_args "sorted_alist_repr" 3 l_repr_thm in
    let a2 = alist_tree_concl_args "sorted_alist_repr" 3 next_repr in
    MP (alist_tree_fast_inst "alist_repr_choice_trans_left" alist_repr_choice_trans_left
          ["R",el 0 a1; "al",el 1 a1; "f",el 2 a1; "al'",el 1 a2; "g",last xs])
       (CONJ l_repr_thm next_repr)
  else
    try alist_tree_merge_conv tm
    with Failure _ -> failwith ("alist_tree_mk_repr_step: no progress: " ^ string_of_term tm)

and alist_tree_mk_repr_known_step rs tm =
  match alist_tree_peek_repr rs tm with
    Some th -> th
  | None -> alist_tree_mk_repr_step rs tm

and alist_tree_mk_repr rs tm =
  let th = alist_tree_mk_repr_known_step rs tm in
  if is_eq (concl th) then
    CONV_RULE (RAND_CONV (REWR_CONV (SYM th))) (alist_tree_mk_repr rs (rhs (concl th)))
  else th;;

(* thm: |- f = rhs, rhs ALOOKUP xs, a function of the repr set, or         *)
(* option_choice_f of two such                                             *)
let alist_tree_add_alist_repr rs th =
  let f,r = dest_eq (concl th) in
  let repr_thm =
    match alist_tree_peek_repr rs r with
      Some rhs_thm -> if is_eq (concl rhs_thm) then TRANS th rhs_thm else th
    | None -> CONV_RULE (RAND_CONV (REWR_CONV (SYM th))) (alist_tree_mk_repr rs r) in
  Alist_tree_termtab.replace rs.alr_dict f repr_thm;;

(* ------------------------------------------------------------------------- *)
(* Proving and using is_lookup theorems                                      *)
(* ------------------------------------------------------------------------- *)

let alist_tree_build_lookup dest cmp r k =
  let dest_k = dest k in
  let chk th =
    if alist_tree_is_const_named "is_lookup" (fst (strip_comb (concl th))) then th
    else failwith "alist_tree_build_lookup: check" in
  let pp th = chk (alist_tree_assume_prems th) in
  let rec build t =
    if alist_tree_is_nil t then
      pp (alist_tree_fast_inst "is_lookup_empty" is_lookup_empty ["R",r; "k",k; "al",t])
    else if is_cons t then
      let xs = dest_list t in
      let _ = length xs = 1 || failwith "alist_tree_build_lookup: malformed" in
      let k',v = dest_pair (hd xs) in
      let c = cmp dest_k (dest k') in
      let ins = ["R",r; "k",k; "k'",k'; "v",v] in
      if c = 0 then pp (alist_tree_fast_inst "is_lookup_hit" is_lookup_hit ins)
      else if c > 0 then pp (alist_tree_fast_inst "is_lookup_far_right" is_lookup_far_right ins)
      else pp (alist_tree_fast_inst "is_lookup_far_left" is_lookup_far_left ins)
    else
      let f,xs = strip_comb t in
      let _ = alist_tree_is_const_named "count_append" f ||
              failwith "alist_tree_build_lookup: unknown" in
      let n,l,rr = match xs with [n;l;rr] -> n,l,rr
                   | _ -> failwith "alist_tree_build_lookup: num args" in
      if not (cmp dest_k (dest (alist_tree_hd_key rr)) < 0) then
        (* is_lookup T fr R r x res ==> is_lookup T fr R (count_append n l r) x res *)
        let sub = build rr in
        let a = alist_tree_concl_args "is_lookup" 6 sub in
        MP (alist_tree_fast_inst "is_lookup_r" is_lookup_r
              ["n",n; "fr",el 1 a; "R",el 2 a; "l",l; "r",el 3 a; "x",el 4 a;
               "res",el 5 a]) sub
      else if cmp dest_k (dest (alist_tree_last_key l)) > 0 then
        pp (alist_tree_fast_inst "is_lookup_centre" is_lookup_centre
              ["R",r; "n",n; "l",l; "r",rr; "k",k])
      else
        (* is_lookup fl T R l x res ==> is_lookup fl T R (count_append n l r) x res *)
        let sub = build l in
        let a = alist_tree_concl_args "is_lookup" 6 sub in
        MP (alist_tree_fast_inst "is_lookup_l" is_lookup_l
              ["n",n; "fl",el 0 a; "R",el 2 a; "l",el 3 a; "r",rr; "x",el 4 a;
               "res",el 5 a]) sub in
  build;;

let alist_tree_prove_lookup r conv dest cmp k al =
  let th = alist_tree_build_lookup dest cmp r k al in
  let rec prove th =
    if not (is_imp (concl th)) then th
    else prove (alist_tree_prove_assum_by_conv conv th) in
  prove (DISCH_ALL th);;

let alist_tree_repr_prove_lookup conv dest cmp repr_thm k =
  let f,xs = strip_comb (concl repr_thm) in
  let _ = alist_tree_is_const_named "sorted_alist_repr" f ||
          failwith "alist_tree_repr_prove_lookup: unexpected" in
  let r,al = match xs with [r;al;_] -> r,al
             | _ -> failwith "alist_tree_repr_prove_lookup: num args" in
  let look = alist_tree_prove_lookup r conv dest cmp k al in
  (* sorted_alist_repr R al f /\ is_lookup fl fr R al x r ==> f x = r *)
  let a = alist_tree_concl_args "is_lookup" 6 look in
  MP (alist_tree_fast_inst "lookup_repr" lookup_repr
        ["R",r; "al",al; "f",last xs; "fl",el 0 a; "fr",el 1 a; "x",el 4 a; "r",el 5 a])
     (CONJ repr_thm look);;

(* f x  -->  SOME y / NONE, for f in the repr set *)
let rec alist_tree_reprs_conv rs tm =
  let f,x = try dest_comb tm with Failure _ -> failwith "alist_tree_reprs_conv" in
  match alist_tree_peek_repr rs f with
    None -> failwith "alist_tree_reprs_conv: not in the repr set"
  | Some th ->
      if is_eq (concl th) then
        (RATOR_CONV (REWR_CONV th) THENC alist_tree_reprs_conv rs) tm
      else alist_tree_repr_prove_lookup rs.alr_conv rs.alr_dest rs.alr_cmp th x;;
