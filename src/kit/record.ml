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
(*   rec_fupdselfid  rec_fi_fupd (K (rec_fi r)) r = r  (HOL4 r with fi :=    *)
(*                   r.fi = r; record_fupdselfid "rec"; since 2026-11-20)    *)
(* all but the last two registered in the project simpset (HOL4's srw_ss    *)
(* has all but the component equality; the selfid rules are used with the   *)
(* marker RECORD_SELFID_ss: existing proofs rely on their absence).  At the *)
(* end: SAME_RUN_TAC thl and SAME_RUN_SUFF_TAC, for the same run of a        *)
(* function from states proved equal (simulation proofs).                    *)
(* ========================================================================= *)

type record_info =
  { ri_name : string;
    ri_fields : (string * term * term) list;  (* field, accessor, update *)
    ri_accessors : thm; ri_fupds : thm; ri_accfupds : thm;
    ri_fupdfupds : thm; ri_fupdcanon : thm; ri_component_equality : thm };;

let the_records = ref ([] : (string * record_info) list);;



let record_info name = assoc name (!the_records);;

(* the rec_fupdselfid theorem of each record (kept apart from record_info,  *)
(* whose type files of the port also build: pancake/panLang), proved when   *)
(* first used (record_fupdselfid, RECORD_SELFID_ss): a record of n fields   *)
(* takes n small proofs, about a second for the big states                 *)
let the_record_selfids = ref ([] : (string * thm Lazy.t) list);;

let record_fupdselfid name = Lazy.force (assoc name (!the_record_selfids));;

(* HOL4's K_o_THM *)
let K_o_THM = prove
 (`(!(f:C->B) (v:A). K v o f = K v) /\ (!(f:A->B) (v:A). f o K v = K (f v):C->B)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; K_THM]);;

let KLAM_o_THM = prove
 (`!(x:A) (f:C->B). (\y. x) o f = (\y. x)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM]);;

(* parsed once (a quotation in the function body is parsed at every call) *)
let kit_tyvar_C = `:C`;;

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
  let accessors = end_itlist CONJ (map (kit_new_recursive_definition rth) acc_cls) in
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
  (* these three by rewriting with the definitions of the updates: a case  *)
  (* split on r per conjunct cost n CHOOSEs for each of the n^2 conjuncts   *)
  let accfupds = prove(list_mk_conj accfupd_tms,
                       REWRITE_TAC(accessors :: upd_defs)) in
  (* rec_fupdfupds *)
  let ff_tms = map2 (fun u (g,h) ->
      let t = fst(dest_fun_ty(type_of g)) in
      let oc = mk_const("o",[t,aty; t,bty; t,kit_tyvar_C]) in
      list_mk_forall([g;h;r],
        mk_eq(list_mk_comb(u,[g;list_mk_comb(u,[h;r])]),
              list_mk_comb(u,[mk_binop oc g h; r]))))
    upds (zip gs hs) in
  let fupdfupds = prove(list_mk_conj ff_tms,
                        REWRITE_TAC(accfupds :: o_THM :: upd_defs)) in
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
          REWRITE_TAC(accfupds :: upd_defs)) in
  (* component equality *)
  let r1 = mk_var("r1",rty) and r2 = mk_var("r2",rty) in
  let ce_tm = list_mk_forall([r1;r2],
    mk_eq(mk_eq(r1,r2),
          list_mk_conj(map (fun a -> mk_eq(mk_comb(a,r1),mk_comb(a,r2))) accs))) in
  let component_equality = prove(ce_tm,
    REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC (SPEC r1 nch) THEN STRUCT_CASES_TAC (SPEC r2 nch) THEN
    REWRITE_TAC[accessors; injectivity name]) in
  (* rec_fupdselfid (HOL4): r with fi := r.fi = r *)
  let selfid_tms = map2 (fun u a ->
      let fty = snd(dest_fun_ty(type_of a)) in
      let kc = mk_const("K",[fty,aty; fty,bty]) in
      mk_forall(r,mk_eq(list_mk_comb(u,[mk_comb(kc,mk_comb(a,r)); r]),r)))
    upds accs in
  let fupdselfid = lazy (prove(list_mk_conj selfid_tms,
    REPEAT CONJ_TAC THEN GEN_TAC THEN STRUCT_CASES_TAC (SPEC r nch) THEN
    REWRITE_TAC(accessors :: K_THM :: upd_defs))) in
  let ri = { ri_name = name;
             ri_fields = map2 (fun f (a,u) -> f,a,u) fnames (zip accs upds);
             ri_accessors = accessors; ri_fupds = fupds; ri_accfupds = accfupds;
             ri_fupdfupds = fupdfupds; ri_fupdcanon = fupdcanon;
             ri_component_equality = component_equality } in
  the_records := (name,ri) :: !the_records;
  cake_add_global_simps ([accessors; fupds; accfupds; fupdfupds; K_o_THM; KLAM_o_THM] @
                  (if fupdcanon = TRUTH then [] else [fupdcanon]));
  (* the selfid rule: for the RECORD_SELFID_ss marker (simp.ml), not in the *)
  (* project simpset: existing proofs rely on its absence                    *)
  kit_record_selfids := !kit_record_selfids @ [fupdselfid];
  the_record_selfids := (name,fupdselfid) :: !the_record_selfids;
  ri;;

(* ------------------------------------------------------------------------- *)
(* SAME_RUN_TAC thl: the goal mentions a run f (p, s1, ...) (an application  *)
(* of a constant; its arguments split at the pairs) and an assumption or    *)
(* the goal another run f (p, s2, ...) of the same function on the same     *)
(* first argument p.  The different arguments are proved equal (records by  *)
(* their component equality, then SIMP thl, then DECIDE_TAC), the run of    *)
(* the goal is replaced by the other one, and an assumption f (p, s2) = v   *)
(* is used to rewrite it.  The candidates are tried in this order: runs of   *)
(* assumptions f (...) = v (newest first), runs inside assumptions, runs    *)
(* of the goal; the first one whose arguments are proved equal is taken (at *)
(* most kit_same_run_max of them are tried).  A run differs from the other  *)
(* in at least one argument of a record type (cake_record): the state.      *)
(* SAME_RUN_SUFF_TAC: the same with the first candidate, leaving the        *)
(* equality of the arguments as a second goal (HOL4 qsuff_tac `pat1 =      *)
(* pat2` after qpat_abbrev_tac).  Both close the goal when it is then an     *)
(* assumption or a reflexive equation.                                       *)
(* ------------------------------------------------------------------------- *)

(* applications of constants (not constructors or pairs) in tm that contain *)
(* no variable bound in tm                                                   *)
let kit_free_apps (tm:term) : term list =
  let acc = ref [] in
  let rec go bvs t =
    match t with
      Comb(f,x) ->
        let h,args = strip_comb t in
        (if is_const h && args <> [] && not (is_constructor_app t) &&
            not (fst(dest_const h) = ",") && not (exists (fun v -> vfree_in v t) bvs)
         then acc := t :: !acc);
        go bvs f; go bvs x
    | Abs(v,b) -> go (v::bvs) b
    | _ -> () in
  go [] tm; rev !acc;;

let rec kit_flat_pair t = if is_pair t then let a,b = dest_pair t in a :: kit_flat_pair b else [t];;

let kit_run_args t = let _,args = strip_comb t in flat (map kit_flat_pair args);;

(* t1 and t2 are runs of the same function on the same first argument, and *)
(* they differ in an argument of a record type (a state)                    *)
let kit_is_record_ty ty =
  try let n,_ = dest_type ty in can record_info n with Failure _ -> false;;

let kit_same_run t1 t2 =
  not (t1 = t2) &&
  let h1,a1 = strip_comb t1 and h2,a2 = strip_comb t2 in
  h1 = h2 && length a1 = length a2 &&
  let c1 = kit_run_args t1 and c2 = kit_run_args t2 in
  length c1 = length c2 && length c1 >= 2 && aconv (hd c1) (hd c2) &&
  forall2 (fun x y -> type_of x = type_of y) c1 c2 &&
  List.exists2 (fun x y -> not (aconv x y) && kit_is_record_ty (type_of x)) c1 c2;;

(* |- t1 = t2 from the equations of the different components *)
let rec kit_cong_of (eqs:thm list) (t1:term) (t2:term) : thm =
  if aconv t1 t2 then ALPHA t1 t2 else
  try find (fun th -> let l,r = dest_eq(concl th) in aconv l t1 && aconv r t2) eqs
  with Failure _ ->
    match t1,t2 with
      Comb(f1,x1),Comb(f2,x2) -> MK_COMB(kit_cong_of eqs f1 f2,kit_cong_of eqs x1 x2)
    | _ -> failwith "kit_cong_of";;

(* the component-equality theorem of a record type, if there is one *)
let kit_component_equality (ty:hol_type) =
  try (record_info (fst(dest_type ty))).ri_component_equality
  with Failure _ -> failwith "no record";;

let SAME_ARGS_TAC thl : tactic = fun (asl,w as g) ->
  let l,_ = dest_eq w in
  ((try GEN_REWRITE_TAC I [kit_component_equality (type_of l)] with Failure _ -> ALL_TAC) THEN
   SIMP thl THEN REPEAT CONJ_TAC THEN DECIDE_TAC) g;;

(* the candidate pairs (goal run, other run, the assumption equation if any) *)
let kit_run_candidates ((asl,w):goal) =
  let gruns = kit_free_apps w in
  let asms = map snd asl in
  let eq_runs = mapfilter (fun th ->
      let l,_ = dest_eq (concl th) in
      if is_comb l && is_const (fst(strip_comb l)) then (l,Some th) else failwith "") asms in
  let in_asms = flat (map (fun th -> map (fun t -> t,None) (kit_free_apps (concl th))) asms) in
  let in_goal = map (fun t -> t,None) gruns in
  let others = eq_runs @ in_asms @ in_goal in
  flat (map (fun (t2,eo) ->
      mapfilter (fun t1 -> if kit_same_run t1 t2 then (t1,t2,eo) else failwith "") gruns)
    others);;

let kit_same_run_finish (t1,t2,eo) (eqth:thm) : tactic =
  SUBST1_TAC eqth THEN
  (match eo with
     Some th -> GEN_REWRITE_TAC ONCE_DEPTH_CONV [th]
   | None -> ALL_TAC) THEN
  TRY (FIRST_ASSUM ACCEPT_TAC ORELSE REFL_TAC);;

let kit_same_run_max = ref 20;;

let SAME_RUN_TAC thl : tactic = fun (asl,w as g) ->
  let cands = kit_run_candidates g in
  let cands = if length cands > !kit_same_run_max
              then fst (chop_list (!kit_same_run_max) cands) else cands in
  let try_cand (t1,t2,eo as c) =
    let c1 = kit_run_args t1 and c2 = kit_run_args t2 in
    let diffs = filter (fun (x,y) -> not (aconv x y)) (zip c1 c2) in
    let eqs = map (fun (x,y) -> TAC_PROOF((asl,mk_eq(x,y)),SAME_ARGS_TAC thl)) diffs in
    let eqth = kit_cong_of eqs t1 t2 in
    kit_same_run_finish c eqth g in
  try tryfind try_cand cands
  with Failure _ -> failwith "SAME_RUN_TAC: no run with provably equal arguments";;

let SAME_RUN_SUFF_TAC : tactic = fun (asl,w as g) ->
  match kit_run_candidates g with
    [] -> failwith "SAME_RUN_SUFF_TAC: no run"
  | (t1,t2,eo as c)::_ ->
      let c1 = kit_run_args t1 and c2 = kit_run_args t2 in
      let diffs = filter (fun (x,y) -> not (aconv x y)) (zip c1 c2) in
      let eqtm = list_mk_conj (map mk_eq diffs) in
      (SUFF_TAC eqtm THENL
        [DISCH_THEN (fun th -> kit_same_run_finish c (kit_cong_of (CONJUNCTS th) t1 t2));
         ALL_TAC]) g;;
