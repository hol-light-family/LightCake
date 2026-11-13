(* ========================================================================= *)
(* CakeML kit: records (HOL4 Datatype ... = <| f1 : ty1; ... |>).            *)
(*                                                                           *)
(*   cake_record "rec" ["f1","ty1"; "f2","ty2"; ...]                         *)
(*                                                                           *)
(* defines the type rec with the constructor rec_REC (fields in order, the   *)
(* HOL4 record literal <| f1 := v1; ... |> is rec_REC v1 v2 ...), the        *)
(* accessors rec_f (HOL4 r.f), the updates rec_f_fupd (HOL4 r with f         *)
(* updated_by g; r with f := v is rec_f_fupd (K v) r), and the theorems      *)
(*   rec_accessors   rec_fi (rec_REC x1 .. xn) = xi                          *)
(*   rec_fupds       rec_fi_fupd g (rec_REC x1 .. xn) = rec_REC .. (g xi) .. *)
(*   rec_accfupds    rec_fi (rec_fj_fupd g r) = rec_fi r  (i <> j)           *)
(*                   rec_fi (rec_fi_fupd g r) = g (rec_fi r)                 *)
(*   rec_fupdfupds   rec_fi_fupd g (rec_fi_fupd h r) = rec_fi_fupd (g o h) r *)
(*   rec_fupdcanon   rec_fj_fupd g (rec_fi_fupd h r)                         *)
(*                     = rec_fi_fupd h (rec_fj_fupd g r)   (i < j)           *)
(*   rec_component_equality   r1 = r2 <=> rec_f1 r1 = rec_f1 r2 /\ ...       *)
(* all but the last registered in the project simpset (HOL4's srw_ss does    *)
(* the same).                                                                *)
(* ========================================================================= *)

type record_info =
  { ri_name : string;
    ri_fields : (string * term * term) list;  (* field, accessor, update *)
    ri_accessors : thm; ri_fupds : thm; ri_accfupds : thm;
    ri_fupdfupds : thm; ri_fupdcanon : thm; ri_component_equality : thm };;

let the_records = ref ([] : (string * record_info) list);;

let record_info name = assoc name (!the_records);;

(* HOL4's K_o_THM *)
let K_o_THM = prove
 (`(!(f:C->B) (v:A). K v o f = K v) /\ (!(f:A->B) (v:A). f o K v = K (f v):C->B)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; K_THM]);;

let KLAM_o_THM = prove
 (`!(x:A) (f:C->B). (\y. x) o f = (\y. x)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM]);;

let cake_record (name:string) (fields:(string * string) list) =
  let cname = name^"_REC" in
  let spec = name^" = "^cname^" "^
             String.concat " " (map (fun (_,ty) -> "("^ty^")") fields) in
  let _ = cake_type spec in
  let _,_,rth = assoc name (!inductive_type_store) in
  let nch = (case_info_of_tyname name).ci_nchotomy in
  let x0,bod = dest_forall(concl nch) in
  let rty = type_of x0 in
  let vs,eq = strip_exists bod in
  let pat = rand eq in                  (* rec_REC a1 .. an *)
  let n = length fields in
  if length vs <> n then failwith "cake_record: field count" else
  let fnames = map fst fields in
  let xs = map2 (fun (f,_) v -> mk_var(f,type_of v)) fields vs in
  let pat_x = vsubst (zip xs vs) pat in
  (* accessors *)
  let acc_vars = map2 (fun f v -> mk_var(name^"_"^f,mk_fun_ty rty (type_of v)))
                      fnames xs in
  let acc_cls = map2 (fun a x -> list_mk_forall(xs,mk_eq(mk_comb(a,pat_x),x)))
                     acc_vars xs in
  let accessors = end_itlist CONJ (map (new_recursive_definition rth) acc_cls) in
  let accs = map (fun a -> mk_const(fst(dest_var a),[])) acc_vars in
  let accs = map2 (fun c v -> inst (type_match (type_of c) (type_of v) []) c)
                  accs acc_vars in
  let r = mk_var("r",rty) in
  (* updates: rec_f_fupd g r = rec_REC (acc1 r) .. (g (acci r)) .. *)
  let upd_defs = map2 (fun (f,_) (a,i) ->
      let fty = type_of(mk_comb(a,r)) in
      let g = mk_var("g",mk_fun_ty fty fty) in
      let args = map2 (fun a' j -> if j = i then mk_comb(g,mk_comb(a',r))
                                   else mk_comb(a',r))
                      accs (0--(n-1)) in
      let con = fst(strip_comb pat) in
      let rhs_ = list_mk_comb(con,args) in
      let uv = mk_var(name^"_"^f^"_fupd",mk_fun_ty (type_of g) (mk_fun_ty rty rty)) in
      new_definition (mk_eq(list_mk_comb(uv,[g;r]),rhs_)))
    fields (zip accs (0--(n-1))) in
  let upds = map (fun th -> fst(strip_comb(lhs(snd(strip_forall(concl th))))))
                 upd_defs in
  let rcases = STRUCT_CASES_TAC (SPEC r nch) in
  let gs = map (fun a -> let fty = snd(dest_fun_ty(type_of a)) in
                         mk_var("g",mk_fun_ty fty fty)) accs in
  let hs = map (fun a -> let fty = snd(dest_fun_ty(type_of a)) in
                         mk_var("h",mk_fun_ty fty fty)) accs in
  (* rec_fupds: on the constructor *)
  let fupds_tms = map2 (fun (u,g) i ->
      let args = map2 (fun x j -> if j = i then mk_comb(g,x) else x)
                      xs (0--(n-1)) in
      list_mk_forall(g::xs,
        mk_eq(list_mk_comb(u,[g;pat_x]),list_mk_comb(fst(strip_comb pat),args))))
    (zip upds gs) (0--(n-1)) in
  let fupds = prove(list_mk_conj fupds_tms,
                    REWRITE_TAC(accessors::upd_defs)) in
  (* rec_accfupds *)
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
  (* rec_fupdfupds *)
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
  (* rec_fupdcanon: a later field's update moves inside an earlier one's *)
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
  (* component equality *)
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
  cake_add_global_simps ([accessors; fupds; accfupds; fupdfupds; K_o_THM; KLAM_o_THM] @
                  (if fupdcanon = TRUTH then [] else [fupdcanon]));
  ri;;
