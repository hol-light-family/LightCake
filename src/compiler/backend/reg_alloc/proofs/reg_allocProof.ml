(* ========================================================================= *)
(* reg_allocProof: port of HOL4 compiler/backend/reg_alloc/proofs/          *)
(* reg_allocProofScript.sml (CakeML v3479).  Proves correctness of the       *)
(* graph-colouring register allocator.                                      *)
(*                                                                           *)
(* Notes:                                                                    *)
(* - The monadic code is rendered as in reg_alloc.ml (st_ex_bind,            *)
(*   st_ex_ignore_bind, st_ex_return; HOL4 () is one).  Most proofs run the  *)
(*   monadic steps one at a time with RAPROOFAUX_BIND_TAC and the success    *)
(*   lemmas of the earlier steps.                                            *)
(* - The HOL4 ML lists msimps, get_eqns, set_eqns, add_eqns and all_eqns are *)
(*   the OCaml theorem lists RAPROOFAUX_msimps and so on; the ML values      *)
(*   list_remap_bij, mk_bij_aux_bij and st_ex_MAP_deg_or_inf are theorems    *)
(*   with the prefix RAPROOFAUX_.  Other helpers also use that prefix.       *)
(* - Changes of a HOL4 statement are noted at the theorem (HOL4: ...).       *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mllist.ml";;
needs "hol4/state_transformer.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "hol4/sorting.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

type_invention_error := true;;

(* Edge from node x to node y, in terms of an adjacency list *)
let has_edge_def = cake_def
  `has_edge (adjls:(num list)list) x y <=>
     x < LENGTH adjls /\
     y < LENGTH adjls /\
     MEM y (EL x adjls)`;;

let undirected_def = cake_def
  `undirected adjls <=>
     !x y. has_edge adjls x y ==> has_edge adjls y x`;;

(* ---
  some well-formedness properties on the state.
  this basically says that all of the arrays have the right dimensions,
  and that the worklists always contain legal nodes
  --- *)

let good_ra_state_def = cake_def
  `good_ra_state s <=>
     LENGTH (ra_state_adj_ls s) = ra_state_dim s /\
     LENGTH (ra_state_node_tag s) = ra_state_dim s /\
     LENGTH (ra_state_degrees s) = ra_state_dim s /\
     LENGTH (ra_state_coalesced s) = ra_state_dim s /\
     LENGTH (ra_state_move_related s) = ra_state_dim s /\
     ALL (\v. v < ra_state_dim s) (ra_state_coalesced s) /\
     ALL (\ls. ALL (\v. v < ra_state_dim s) ls) (ra_state_adj_ls s) /\
     ALL (\ls. SORTED (>) ls) (ra_state_adj_ls s) /\
     ALL (\v. v < ra_state_dim s) (ra_state_simp_wl s) /\
     ALL (\v. v < ra_state_dim s) (ra_state_spill_wl s) /\
     ALL (\v. v < ra_state_dim s) (ra_state_freeze_wl s) /\
     ALL (\m. match m with (p:num,x,y) -> x < ra_state_dim s /\ y < ra_state_dim s)
       (ra_state_avail_moves_wl s) /\
     ALL (\m. match m with (p:num,x,y) -> x < ra_state_dim s /\ y < ra_state_dim s)
       (ra_state_unavail_moves_wl s) /\
     undirected (ra_state_adj_ls s)`;;

(* --- invariant: no two adjacent nodes have the same colour --- *)
let no_clash_def = cake_def
  `no_clash adj_ls (node_tag:reg_alloc_tag list) <=>
     !x y. has_edge adj_ls x y ==>
       match (EL x node_tag,EL y node_tag) with
         (Fixed n,Fixed m) -> (n = m ==> x = y)
       | _ -> T`;;

(*
  Good preference oracle may only inspect, but not touch the state
  Moreover, it must always select a member of the input list
*)
let good_pref_def = cake_def
  `good_pref (pref:num->num list->ra_state->(num option,E)exc#ra_state) <=>
     !n ks s.
       good_ra_state s ==>
       ?res. pref n ks s = (M_success res,s) /\
             match res with NONE -> T | SOME k -> MEM k ks`;;

(* HOL4 ML lists of rewrites (msimps, get_eqns, set_eqns, add_eqns, all_eqns) *)
let RAPROOFAUX_msimps = [st_ex_bind_def; st_ex_ignore_bind_def; st_ex_return_def];;

let RAPROOFAUX_get_eqns =
  [get_dim_def; get_unavail_moves_wl_def; get_avail_moves_wl_def; get_simp_wl_def;
   get_spill_wl_def; set_spill_wl_def; get_freeze_wl_def; reg_alloc_get_stack_def];;

let RAPROOFAUX_set_eqns =
  [set_dim_def; set_unavail_moves_wl_def; set_avail_moves_wl_def; set_simp_wl_def;
   set_spill_wl_def; set_freeze_wl_def; set_stack_def];;

let RAPROOFAUX_add_eqns =
  [add_freeze_wl_def; add_unavail_moves_wl_def; add_spill_wl_def];;

let RAPROOFAUX_all_eqns =
  RAPROOFAUX_get_eqns @ RAPROOFAUX_set_eqns @ RAPROOFAUX_add_eqns @ RAPROOFAUX_msimps;;

(* M_success conditions *)
(* HOL4: case_eq_thms *)
let reg_allocProof_case_eq_thms = end_itlist CONJ
  [pair_case_eq; case_eq "exc"; case_eq "reg_alloc_tag"; list_case_eq; option_case_eq];;

let tag_case_st = prove
 (`!t (a:num->A->B) (b:A->B) c f.
     reg_alloc_tag_CASE t a b c f = reg_alloc_tag_CASE t (\n. a n f) (b f) (c f)`,
  GEN_TAC THEN CASES_ON `t:reg_alloc_tag` THEN SIMP[]);;

let list_case_st = prove
 (`!t (a:A->B) (b:C->C list->A->B) f.
     list_CASE t a b f = list_CASE t (a f) (\x y. b x y f)`,
  GEN_TAC THEN CASES_ON `t:C list` THEN SIMP[]);;

(* ---
  TODO: These lemmas should be automatically generated for each array used!

  Note that they can be stated independently of the precise state invariants
  (as shown below)

  The array components we have are:
    adj_ls, node_tag, degrees, coalesced, move_related
  ---*)

(* Rewriting lemmas for array "sub" *)
(* HOL4: Msub_eqn (the unused variable v of the HOL4 statement is dropped) *)
let reg_allocProof_Msub_eqn = prove
 (`!(e:E) n (ls:A list).
     Msub e n ls = if n < LENGTH ls then M_success (EL n ls) else M_failure e`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[ml_monadBase_Msub_eq] THEN
  MATCH_MP_TAC ml_monadBase_Msub_exn_eq THEN ASM_ARITH_TAC);;
let _ = cake_add_simps [reg_allocProof_Msub_eqn];;

let adj_ls_sub_eqn = prove
 (`!n s.
     adj_ls_sub n s =
     if n < LENGTH (ra_state_adj_ls s) then
       (M_success (EL n (ra_state_adj_ls s)),s)
     else (M_failure Subscript,s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[adj_ls_sub_def; ml_monadBase_Marray_sub_def; reg_allocProof_Msub_eqn] THEN
  COND_CASES_TAC THEN SIMP[]);;
let _ = cake_add_simps [adj_ls_sub_eqn];;

let node_tag_sub_eqn = prove
 (`!n s.
     node_tag_sub n s =
     if n < LENGTH (ra_state_node_tag s) then
       (M_success (EL n (ra_state_node_tag s)),s)
     else (M_failure Subscript,s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[node_tag_sub_def; ml_monadBase_Marray_sub_def; reg_allocProof_Msub_eqn] THEN
  COND_CASES_TAC THEN SIMP[]);;
let _ = cake_add_simps [node_tag_sub_eqn];;

let degrees_sub_eqn = prove
 (`!n s.
     degrees_sub n s =
     if n < LENGTH (ra_state_degrees s) then
       (M_success (EL n (ra_state_degrees s)),s)
     else (M_failure Subscript,s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[degrees_sub_def; ml_monadBase_Marray_sub_def; reg_allocProof_Msub_eqn] THEN
  COND_CASES_TAC THEN SIMP[]);;
let _ = cake_add_simps [degrees_sub_eqn];;

let coalesced_sub = prove
 (`!n s.
     coalesced_sub n s =
     if n < LENGTH (ra_state_coalesced s) then
       (M_success (EL n (ra_state_coalesced s)),s)
     else (M_failure Subscript,s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[coalesced_sub_def; ml_monadBase_Marray_sub_def; reg_allocProof_Msub_eqn] THEN
  COND_CASES_TAC THEN SIMP[]);;
let _ = cake_add_simps [coalesced_sub];;

let move_related_sub = prove
 (`!n s.
     move_related_sub n s =
     if n < LENGTH (ra_state_move_related s) then
       (M_success (EL n (ra_state_move_related s)),s)
     else (M_failure Subscript,s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[move_related_sub_def; ml_monadBase_Marray_sub_def; reg_allocProof_Msub_eqn] THEN
  COND_CASES_TAC THEN SIMP[]);;
let _ = cake_add_simps [move_related_sub];;

(* Rewriting lemmas for array "update" *)
(* HOL4: Mupdate_eqn *)
let reg_allocProof_Mupdate_eqn = prove
 (`!(e:E) (x:A) n ls.
     Mupdate e x n ls =
     if n < LENGTH ls then M_success (LUPDATE x n ls) else M_failure e`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[ml_monadBase_Mupdate_eq] THEN
  MATCH_MP_TAC ml_monadBase_Mupdate_exn_eq THEN ASM_ARITH_TAC);;
let _ = cake_add_simps [reg_allocProof_Mupdate_eqn];;

let update_adj_ls_eqn = prove
 (`!n t s.
     update_adj_ls n t s =
     if n < LENGTH (ra_state_adj_ls s) then
       (M_success one,ra_state_adj_ls_fupd (K (LUPDATE t n (ra_state_adj_ls s))) s)
     else (M_failure Subscript,s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[update_adj_ls_def; ml_monadBase_Marray_update_def; reg_allocProof_Mupdate_eqn] THEN
  COND_CASES_TAC THEN SIMP[]);;
let _ = cake_add_simps [update_adj_ls_eqn];;

let update_node_tag_eqn = prove
 (`!n t s.
     update_node_tag n t s =
     if n < LENGTH (ra_state_node_tag s) then
       (M_success one,ra_state_node_tag_fupd (K (LUPDATE t n (ra_state_node_tag s))) s)
     else (M_failure Subscript,s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[update_node_tag_def; ml_monadBase_Marray_update_def; reg_allocProof_Mupdate_eqn] THEN
  COND_CASES_TAC THEN SIMP[]);;
let _ = cake_add_simps [update_node_tag_eqn];;

let update_degrees_eqn = prove
 (`!n t s.
     update_degrees n t s =
     if n < LENGTH (ra_state_degrees s) then
       (M_success one,ra_state_degrees_fupd (K (LUPDATE t n (ra_state_degrees s))) s)
     else (M_failure Subscript,s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[update_degrees_def; ml_monadBase_Marray_update_def; reg_allocProof_Mupdate_eqn] THEN
  COND_CASES_TAC THEN SIMP[]);;
let _ = cake_add_simps [update_degrees_eqn];;

let update_coalesced_eqn = prove
 (`!n t s.
     update_coalesced n t s =
     if n < LENGTH (ra_state_coalesced s) then
       (M_success one,ra_state_coalesced_fupd (K (LUPDATE t n (ra_state_coalesced s))) s)
     else (M_failure Subscript,s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[update_coalesced_def; ml_monadBase_Marray_update_def; reg_allocProof_Mupdate_eqn] THEN
  COND_CASES_TAC THEN SIMP[]);;
let _ = cake_add_simps [update_coalesced_eqn];;

let update_move_related_eqn = prove
 (`!n t s.
     update_move_related n t s =
     if n < LENGTH (ra_state_move_related s) then
       (M_success one,
        ra_state_move_related_fupd (K (LUPDATE t n (ra_state_move_related s))) s)
     else (M_failure Subscript,s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[update_move_related_def; ml_monadBase_Marray_update_def;
              reg_allocProof_Mupdate_eqn] THEN
  COND_CASES_TAC THEN SIMP[]);;
let _ = cake_add_simps [update_move_related_eqn];;

(* --- *)

(* The following are also routine theorems, but slightly more complicated.
  TODO: can they be stated generically? *)

(* This asserts, e.g. that the monadic map of (\i.node_tag_sub i) returns
   success if the input list were all within range *)
let st_ex_MAP_node_tag_sub = prove
 (`!ls s.
     ALL (\v. v < LENGTH (ra_state_node_tag s)) ls ==>
     st_ex_MAP node_tag_sub ls s =
     (M_success (MAP (\i. EL i (ra_state_node_tag s)) ls),s)`,
  LIST_INDUCT_TAC THEN FS(st_ex_MAP_def :: RAPROOFAUX_msimps));;

let st_ex_MAP_adj_ls_sub = prove
 (`!ls s.
     ALL (\v. v < LENGTH (ra_state_adj_ls s)) ls ==>
     st_ex_MAP adj_ls_sub ls s =
     (M_success (MAP (\i. EL i (ra_state_adj_ls s)) ls),s)`,
  LIST_INDUCT_TAC THEN FS(st_ex_MAP_def :: RAPROOFAUX_msimps));;

let st_ex_MAP_degrees_sub = prove
 (`!ls s.
     ALL (\v. v < LENGTH (ra_state_degrees s)) ls ==>
     st_ex_MAP degrees_sub ls s =
     (M_success (MAP (\i. EL i (ra_state_degrees s)) ls),s)`,
  LIST_INDUCT_TAC THEN FS(st_ex_MAP_def :: RAPROOFAUX_msimps));;

(* Local helpers (RAPROOFAUX_): the monad laws used below, a frame         *)
(* characterisation of record updates of ra_state, and constant cases.     *)

let RAPROOFAUX_bind_return = prove
 (`!(m:S->(A,E)exc#S) s. st_ex_bind m (\r. st_ex_return r) s = m s`,
  REPEAT GEN_TAC THEN SIMP RAPROOFAUX_msimps THEN
  CASES_ON `(m:S->(A,E)exc#S) s` THEN SIMP[] THEN
  CASES_ON `x:(A,E)exc` THEN SIMP[]);;

(* (the unusual type variable names avoid clashes in MATCH_MP with goals *)
(* that have type variables of their own)                                 *)
let RAPROOFAUX_bind_ok = prove
 (`!(m:RAS->(RAA,RAE)exc#RAS) (f:RAA->RAS->(RAB,RAE)exc#RAS) s x s1.
     m s = (M_success x,s1) ==> st_ex_bind m f s = f x s1`,
  SIMP RAPROOFAUX_msimps);;

let RAPROOFAUX_ignore_bind_ok = prove
 (`!(m:RAS->(RAA,RAE)exc#RAS) (f:RAS->(RAB,RAE)exc#RAS) s x s1.
     m s = (M_success x,s1) ==> st_ex_ignore_bind m f s = f s1`,
  SIMP RAPROOFAUX_msimps);;

let RAPROOFAUX_ra_fields =
  ["adj_ls"; "node_tag"; "degrees"; "dim"; "simp_wl"; "spill_wl"; "freeze_wl";
   "avail_moves_wl"; "unavail_moves_wl"; "coalesced"; "move_related"; "stack"];;

(* RAPROOFAUX_frame [f1; ..]:                                               *)
(*   s' = s with <| f1 := s'.f1; .. |>  <=>  the other fields agree         *)
let RAPROOFAUX_frame (flds:string list) =
  let upd = itlist (fun f t -> "ra_state_"^f^"_fupd (K (ra_state_"^f^" s')) ("^t^")")
              flds "s" in
  let others = filter (fun f -> not (mem f flds)) RAPROOFAUX_ra_fields in
  let rhs = end_itlist (fun a b -> a^" /\\ "^b)
    (map (fun f -> "ra_state_"^f^" s' = ra_state_"^f^" s") others) in
  prove(parse_term ("!s s':ra_state. s' = "^upd^" <=> "^rhs),
        REPEAT GEN_TAC THEN SIMP[ra_state_component_equality] THEN MESON_TAC[]);;

let RAPROOFAUX_frame_node_tag = RAPROOFAUX_frame ["node_tag"];;

let RAPROOFAUX_tag_CASE_const = prove
 (`!t (x:A). reg_alloc_tag_CASE t (\c. x) x x = x`,
  GEN_TAC THEN CASES_ON `t:reg_alloc_tag` THEN SIMP[]);;

(* --- the main (core) correctness proofs start here --- *)

(* RAPROOFAUX_remove_colours_CONS: one step of remove_colours *)
let RAPROOFAUX_remove_colours_CONS = prove
 (CASE_TERM `!x xs ks s.
     remove_colours (CONS x xs) ks s =
     if ks = [] then (M_success [],s)
     else if x < LENGTH (ra_state_node_tag s) then
       remove_colours xs
         (match EL x (ra_state_node_tag s) with
            Fixed c -> FILTER (\x. ~(x = c)) ks
          | _ -> ks) s
     else (M_failure Subscript,s)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[remove_colours_def; st_ex_return_def]; ALL_TAC] THEN
  REWRITE_TAC[remove_colours_def; NOT_CONS_NIL] THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [st_ex_bind_def] THEN
  REWRITE_TAC[node_tag_sub_eqn] THEN COND_CASES_TAC THEN SIMP[] THEN
  CASES_ON `EL x (ra_state_node_tag s)` THEN SIMP[RAPROOFAUX_bind_return]);;

let remove_colours_frame = prove
 (`!adjs ks s (res:(num list,state_exn)exc) s'.
     remove_colours adjs ks s = (res,s') ==> s = s'`,
  MATCH_MP_TAC remove_colours_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  SIMP(remove_colours_def :: RAPROOFAUX_msimps) THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN SIMP[] THEN
  CASES_ON `EL x (ra_state_node_tag s)` THEN SIMP[reg_allocProof_case_eq_thms] THEN
  STRIP_TAC THEN ASM_MESON_TAC[]);;

let remove_colours_success = prove
 (CASE_TERM `!adjs ks s ls s'.
   remove_colours adjs ks s = (M_success ls,s') ==>
   Abbrev(set_of_list ls SUBSET set_of_list ks /\
     (!n. MEM n adjs /\ n < LENGTH (ra_state_node_tag s') ==>
        match EL n (ra_state_node_tag s) with Fixed c -> ~MEM c ls | _ -> T))`,
  REWRITE_TAC[marker_Abbrev_def] THEN LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN
    SIMP[remove_colours_def; st_ex_return_def; MEM] THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[RAPROOFAUX_remove_colours_CONS] THEN
  COND_CASES_TAC THENL
   [SIMP[] THEN STRIP_TAC THEN
    GVS[EMPTY_SUBSET; set_of_list; MEM; RAPROOFAUX_tag_CASE_const];
    ALL_TAC] THEN
  COND_CASES_TAC THENL [ALL_TAC; SIMP[]] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP remove_colours_frame) THEN
  FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(MP_TAC o MATCH_MP ih)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  CASES_ON `EL h (ra_state_node_tag s)` THEN
  SIMP[SUBSET; IN_SET_OF_LIST; MEM_FILTER; MEM] THEN STRIP_TAC THEN
  REPEAT STRIP_TAC THEN SIMP[] THEN ASM_MESON_TAC[]);;

let no_clash_LUPDATE_Stemp = prove
 (`!adjls tags n. no_clash adjls tags ==> no_clash adjls (LUPDATE Stemp n tags)`,
  REWRITE_TAC[no_clash_def; EL_LUPDATE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `y:num`]) THEN ASM_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN SIMP[RAPROOFAUX_tag_CASE_const]);;

let no_clash_LUPDATE_Fixed = prove
 (`!adjls tags n x.
     undirected adjls /\
     ALL (\ls. ALL (\v. v < LENGTH tags) ls) adjls /\
     n < LENGTH adjls /\
     (!m. MEM m (EL n adjls) /\ m < LENGTH tags ==> ~(EL m tags = Fixed x)) /\
     no_clash adjls tags
     ==> no_clash adjls (LUPDATE (Fixed x) n tags)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a b. has_edge adjls a b ==> b < LENGTH (tags:reg_alloc_tag list)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\ls. ALL (\v. v < LENGTH (tags:reg_alloc_tag list)) ls) adjls` THEN
    REWRITE_TAC[GSYM ALL_MEM; has_edge_def] THEN MESON_TAC[MEM_EL];
    ALL_TAC] THEN
  REWRITE_TAC[no_clash_def; EL_LUPDATE] THEN
  X_GEN_TAC `a:num` THEN X_GEN_TAC `b:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `has_edge adjls b a` ASSUME_TAC THENL
   [ASM_MESON_TAC[undirected_def]; ALL_TAC] THEN
  UNDISCH_TAC `no_clash adjls tags` THEN REWRITE_TAC[no_clash_def] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:num`; `b:num`]) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n < LENGTH (tags:reg_alloc_tag list)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `a:num = n` THEN ASM_CASES_TAC `b:num = n` THEN ASM_REWRITE_TAC[] THEN
  SIMP[] THENL
   [SUBGOAL_THEN `~(EL b tags = Fixed x)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[has_edge_def]; ALL_TAC] THEN
    CASES_ON `EL b (tags:reg_alloc_tag list)` THEN SIMP[] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `~(EL a tags = Fixed x)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[has_edge_def]; ALL_TAC] THEN
    CASES_ON `EL a (tags:reg_alloc_tag list)` THEN SIMP[RAPROOFAUX_tag_CASE_const] THEN
    ASM_MESON_TAC[]]);;

(* HOL4 quantifies s twice (!adj ks s s.); the outer one is vacuous *)
let remove_colours_succeeds = prove
 (`!adj ks s. ALL (\v. v < LENGTH (ra_state_node_tag s)) adj ==>
     ?ls. remove_colours adj ks s = (M_success ls,s)`,
  LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN SIMP[remove_colours_def; st_ex_return_def]; ALL_TAC] THEN
  REWRITE_TAC[ALL; RAPROOFAUX_remove_colours_CONS] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THENL [MESON_TAC[]; ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let assign_Atemp_tag_correct = prove
 (`!s pref n ks.
     good_ra_state s /\
     no_clash (ra_state_adj_ls s) (ra_state_node_tag s) /\
     good_pref pref /\
     n < ra_state_dim s
     ==> ?s'. assign_Atemp_tag ks pref n s = (M_success one,s') /\
              (!m. if n = m /\ EL n (ra_state_node_tag s) = Atemp
                   then ~(EL n (ra_state_node_tag s') = Atemp)
                   else EL m (ra_state_node_tag s') = EL m (ra_state_node_tag s)) /\
              no_clash (ra_state_adj_ls s') (ra_state_node_tag s') /\
              good_ra_state s' /\
              s' = ra_state_node_tag_fupd (K (ra_state_node_tag s')) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[assign_Atemp_tag_def] THEN
  SUBGOAL_THEN `n < LENGTH (ra_state_node_tag s) /\ n < LENGTH (ra_state_adj_ls s)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[good_ra_state_def]; ALL_TAC] THEN
  SIMP RAPROOFAUX_msimps THEN
  CASES_ON `EL n (ra_state_node_tag s)` THEN SIMP[] THEN
  TRY(SIMP[ra_state_component_equality] THEN NO_TAC) THEN
  SUBGOAL_THEN `ALL (\v. v < LENGTH (ra_state_node_tag s)) (EL n (ra_state_adj_ls s))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `good_ra_state s` THEN REWRITE_TAC[good_ra_state_def; GSYM ALL_MEM] THEN
    ASM_MESON_TAC[MEM_EL];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `ls:num list` o SPEC `ks:num list` o
    MATCH_MP remove_colours_succeeds) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP remove_colours_success) THEN
  ASM_REWRITE_TAC[marker_Abbrev_def] THEN STRIP_TAC THEN SIMP[] THEN
  SUBGOAL_THEN
   `!t. (t = Stemp \/
         ?c. t = Fixed c /\
             (!m. MEM m (EL n (ra_state_adj_ls s)) /\ m < LENGTH (ra_state_node_tag s)
                  ==> ~(EL m (ra_state_node_tag s) = Fixed c))) ==>
        (!m. if n = m then ~(EL m (LUPDATE t m (ra_state_node_tag s)) = Atemp)
             else EL m (LUPDATE t n (ra_state_node_tag s)) = EL m (ra_state_node_tag s)) /\
        no_clash (ra_state_adj_ls s) (LUPDATE t n (ra_state_node_tag s)) /\
        good_ra_state (ra_state_node_tag_fupd (K (LUPDATE t n (ra_state_node_tag s))) s)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THENL
       [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[EL_LUPDATE] THEN
        ASM_MESON_TAC[distinctness "reg_alloc_tag"];
        ASM_SIMP_TAC[EL_LUPDATE]];
      FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC[no_clash_LUPDATE_Stemp] THEN
      MATCH_MP_TAC no_clash_LUPDATE_Fixed THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `good_ra_state s` THEN SIMP[good_ra_state_def];
      UNDISCH_TAC `good_ra_state s` THEN SIMP[good_ra_state_def; LENGTH_LUPDATE]];
    ALL_TAC] THEN
  CASES_ON `ls:num list` THEN SIMP[] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `CONS (a0:num) a1`; `s:ra_state`] o
    REWRITE_RULE[good_pref_def]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
  POP_ASSUM MP_TAC THEN CASES_ON `res:num option` THEN SIMP[] THEN TRY DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[distinctness "reg_alloc_tag"; injectivity "reg_alloc_tag"; UNWIND_THM1] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
  SIMP[MEM] THEN ASM_MESON_TAC[]);;

let assign_Atemps_FOREACH_lem = prove
 (`!ls s ks prefs.
     good_ra_state s /\
     no_clash (ra_state_adj_ls s) (ra_state_node_tag s) /\
     good_pref prefs /\
     ALL (\v. v < ra_state_dim s) ls
     ==> ?s'. st_ex_FOREACH ls (assign_Atemp_tag ks prefs) s = (M_success one,s') /\
              no_clash (ra_state_adj_ls s') (ra_state_node_tag s') /\
              good_ra_state s' /\
              s' = ra_state_node_tag_fupd (K (ra_state_node_tag s')) s /\
              (!m. if MEM m ls /\ EL m (ra_state_node_tag s) = Atemp
                   then ~(EL m (ra_state_node_tag s') = Atemp)
                   else EL m (ra_state_node_tag s') = EL m (ra_state_node_tag s))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[st_ex_FOREACH_def; st_ex_return_def; MEM] THEN
    SIMP[] THEN SIMP[ra_state_component_equality];
    ALL_TAC] THEN
  REWRITE_TAC[ALL; MEM; st_ex_FOREACH_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:ra_state`;
    `prefs:num->num list->ra_state->(num option,state_exn)exc#ra_state`;
    `h:num`; `ks:num list`] assign_Atemp_tag_correct) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:ra_state` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_ignore_bind_ok th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_node_tag]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s1:ra_state`; `ks:num list`;
    `prefs:num->num list->ra_state->(num option,state_exn)exc#ra_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:ra_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s2:ra_state` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_node_tag]) THEN
  ASM_REWRITE_TAC[RAPROOFAUX_frame_node_tag] THEN
  X_GEN_TAC `m:num` THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (is_forall o concl))) THEN
  ASM_CASES_TAC `m:num = h` THEN ASM_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let assign_Atemps_correct = prove
 (`!k ls prefs s.
     good_ra_state s /\ good_pref prefs /\
     no_clash (ra_state_adj_ls s) (ra_state_node_tag s)
     ==> ?s'. assign_Atemps k ls prefs s = (M_success one,s') /\
              no_clash (ra_state_adj_ls s') (ra_state_node_tag s') /\
              good_ra_state s' /\
              s' = ra_state_node_tag_fupd (K (ra_state_node_tag s')) s /\
              ALL (\n. ~(n = Atemp)) (ra_state_node_tag s') /\
              (!m. m < LENGTH (ra_state_node_tag s) /\ ~(EL m (ra_state_node_tag s) = Atemp)
                   ==> EL m (ra_state_node_tag s') = EL m (ra_state_node_tag s))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[assign_Atemps_def; get_dim_def] THEN
  SIMP RAPROOFAUX_msimps THEN
  MP_TAC(ISPECL [`FILTER (\n. n < ra_state_dim s) ls`; `s:ra_state`;
    `list_of_seq (\x:num. x) k`;
    `prefs:num->num list->ra_state->(num option,state_exn)exc#ra_state`]
    assign_Atemps_FOREACH_lem) THEN
  ASM_SIMP_TAC[EVERY_FILTER; ALL_T] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:ra_state` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_node_tag]) THEN
  MP_TAC(ISPECL [`list_of_seq (\x:num. x) (ra_state_dim s)`; `s1:ra_state`;
    `list_of_seq (\x:num. x) k`;
    `prefs:num->num list->ra_state->(num option,state_exn)exc#ra_state`]
    assign_Atemps_FOREACH_lem) THEN
  ASM_SIMP_TAC[EVERY_GENLIST] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:ra_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s2:ra_state` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_node_tag]) THEN
  ASM_REWRITE_TAC[RAPROOFAUX_frame_node_tag] THEN
  SUBGOAL_THEN `LENGTH (ra_state_node_tag s) = ra_state_dim s /\
                LENGTH (ra_state_node_tag s2) = ra_state_dim s`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[good_ra_state_def]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM ALL_EL] THEN X_GEN_TAC `m:num` THEN DISCH_TAC;
    X_GEN_TAC `m:num` THEN STRIP_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (is_forall o concl))) THEN
  ASM_REWRITE_TAC[MEM_GENLIST; MEM_FILTER] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let SORTED_HEAD_LT = prove
 (`!ls (col:num) h. col < h /\ SORTED (\x y. x <= y) (CONS h ls) ==> ~MEM col ls`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `transitive (\x y:num. x <= y)` ASSUME_TAC THENL
   [REWRITE_TAC[transitive_def] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SORTED_EQ] THEN MESON_TAC[NOT_LE]);;

(* Correctness for the second step *)
let unbound_colour_correct = prove
 (`!ls k (k':num). SORTED (\x y. x <= y) ls ==>
     k <= unbound_colour k ls /\ ~MEM (unbound_colour k ls) ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[unbound_colour_def; MEM; LE_REFL] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SORTED_TL) THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[LE_REFL; DE_MORGAN_THM] THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_MESON_TAC[SORTED_HEAD_LT]];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`k + 1`; `k':num`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `k':num`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(*
  Good negated preference oracle may only inspect, but not touch the state
  Moreover, it must always select an element >= k not in the input list
*)
let good_neg_pref_def = cake_def
  `good_neg_pref (k:num) (pref:num->num list->ra_state->(num option,E)exc#ra_state) <=>
     !n bads s.
       good_ra_state s ==>
       ?res. pref n bads s = (M_success res,s) /\
             match res with NONE -> T | SOME c -> ~MEM c bads /\ k <= c`;;

let assign_Stemp_tag_correct = prove
 (`!s n k prefs.
     good_ra_state s /\
     no_clash (ra_state_adj_ls s) (ra_state_node_tag s) /\
     n < ra_state_dim s /\
     good_neg_pref k prefs
     ==> ?s'. assign_Stemp_tag k prefs n s = (M_success one,s') /\
              (!m. if n = m /\ EL n (ra_state_node_tag s) = Stemp
                   then ?k'. EL n (ra_state_node_tag s') = Fixed k' /\ k <= k'
                   else EL m (ra_state_node_tag s') = EL m (ra_state_node_tag s)) /\
              no_clash (ra_state_adj_ls s') (ra_state_node_tag s') /\
              good_ra_state s' /\
              s' = ra_state_node_tag_fupd (K (ra_state_node_tag s')) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[assign_Stemp_tag_def] THEN
  SUBGOAL_THEN `n < LENGTH (ra_state_node_tag s) /\ n < LENGTH (ra_state_adj_ls s)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[good_ra_state_def]; ALL_TAC] THEN
  SIMP RAPROOFAUX_msimps THEN
  CASES_ON `EL n (ra_state_node_tag s)` THEN SIMP[] THEN
  TRY(SIMP[ra_state_component_equality] THEN NO_TAC) THEN
  SUBGOAL_THEN `ALL (\v. v < LENGTH (ra_state_node_tag s)) (EL n (ra_state_adj_ls s))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `good_ra_state s` THEN REWRITE_TAC[good_ra_state_def; GSYM ALL_MEM] THEN
    ASM_MESON_TAC[MEM_EL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[st_ex_MAP_node_tag_sub] THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  SIMP[] THEN
  SUBGOAL_THEN
   `!c. k <= c /\ ~MEM c (sort (\x y. x <= y) (MAP tag_col
          (MAP (\i. EL i (ra_state_node_tag s)) (EL n (ra_state_adj_ls s))))) ==>
     ?s'. update_node_tag n (Fixed c) s = (M_success one,s') /\
     (!m. if n = m then ?k'. EL m (ra_state_node_tag s') = Fixed k' /\ k <= k'
          else EL m (ra_state_node_tag s') = EL m (ra_state_node_tag s)) /\
     no_clash (ra_state_adj_ls s') (ra_state_node_tag s') /\
     good_ra_state s' /\
     s' = ra_state_node_tag_fupd (K (ra_state_node_tag s')) s`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[update_node_tag_eqn] THEN SIMP[] THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THENL
       [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[EL_LUPDATE] THEN
        ASM_MESON_TAC[];
        ASM_SIMP_TAC[EL_LUPDATE]];
      MATCH_MP_TAC no_clash_LUPDATE_Fixed THEN ASM_REWRITE_TAC[CONJ_ASSOC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `good_ra_state s` THEN SIMP[good_ra_state_def];
        X_GEN_TAC `m:num` THEN STRIP_TAC THEN DISCH_TAC THEN
        UNDISCH_TAC `~MEM (c:num) (sort (\x y. x <= y) (MAP tag_col
          (MAP (\i. EL i (ra_state_node_tag s)) (EL n (ra_state_adj_ls s)))))` THEN
        REWRITE_TAC[sort_MEM; MAP_MAP_o; MEM_MAP; o_THM] THEN
        EXISTS_TAC `EL m (ra_state_node_tag s)` THEN
        ASM_REWRITE_TAC[tag_col_def] THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]];
      UNDISCH_TAC `good_ra_state s` THEN SIMP[good_ra_state_def; LENGTH_LUPDATE]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `sort (\x y. x <= y) (MAP tag_col
        (MAP (\i. EL i (ra_state_node_tag s)) (EL n (ra_state_adj_ls s))))`;
        `s:ra_state`] o REWRITE_RULE[good_neg_pref_def]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[case_def "exc"; case_def "prod"] THEN
  POP_ASSUM MP_TAC THEN CASES_ON `res:num option` THEN
  REWRITE_TAC[case_def "option"] THEN TRY DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC unbound_colour_correct THEN
  MATCH_MP_TAC sort_SORTED THEN REWRITE_TAC[transitive_def; total_def] THEN ARITH_TAC);;

(* Almost exactly the same as the FOREACH for Atemps *)
let assign_Stemps_FOREACH_lem = prove
 (`!ls s k prefs.
     good_ra_state s /\
     no_clash (ra_state_adj_ls s) (ra_state_node_tag s) /\
     ALL (\v. v < ra_state_dim s) ls /\
     good_neg_pref k prefs
     ==> ?s'. st_ex_FOREACH ls (assign_Stemp_tag k prefs) s = (M_success one,s') /\
              no_clash (ra_state_adj_ls s') (ra_state_node_tag s') /\
              good_ra_state s' /\
              (!m. if MEM m ls /\ EL m (ra_state_node_tag s) = Stemp
                   then ?k'. EL m (ra_state_node_tag s') = Fixed k' /\ k <= k'
                   else EL m (ra_state_node_tag s') = EL m (ra_state_node_tag s)) /\
              s' = ra_state_node_tag_fupd (K (ra_state_node_tag s')) s`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[st_ex_FOREACH_def; st_ex_return_def; MEM] THEN
    SIMP[] THEN SIMP[ra_state_component_equality];
    ALL_TAC] THEN
  REWRITE_TAC[ALL; MEM; st_ex_FOREACH_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:ra_state`; `h:num`; `k:num`;
    `prefs:num->num list->ra_state->(num option,state_exn)exc#ra_state`]
    assign_Stemp_tag_correct) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:ra_state` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_ignore_bind_ok th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_node_tag]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s1:ra_state`; `k:num`;
    `prefs:num->num list->ra_state->(num option,state_exn)exc#ra_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:ra_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s2:ra_state` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_node_tag]) THEN
  ASM_REWRITE_TAC[RAPROOFAUX_frame_node_tag] THEN
  X_GEN_TAC `m:num` THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (is_forall o concl))) THEN
  ASM_CASES_TAC `m:num = h` THEN ASM_REWRITE_TAC[] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[distinctness "reg_alloc_tag"]);;

let assign_Stemps_correct = prove
 (`!s k prefs.
     good_ra_state s /\
     no_clash (ra_state_adj_ls s) (ra_state_node_tag s) /\
     good_neg_pref k prefs
     ==> ?s'. assign_Stemps k prefs s = (M_success one,s') /\
              no_clash (ra_state_adj_ls s') (ra_state_node_tag s') /\
              good_ra_state s' /\
              s' = ra_state_node_tag_fupd (K (ra_state_node_tag s')) s /\
              (!m. m < LENGTH (ra_state_node_tag s) ==>
                   if EL m (ra_state_node_tag s) = Stemp
                   then ?k'. EL m (ra_state_node_tag s') = Fixed k' /\ k <= k'
                   else EL m (ra_state_node_tag s') = EL m (ra_state_node_tag s))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[assign_Stemps_def; get_dim_def] THEN
  SIMP RAPROOFAUX_msimps THEN
  MP_TAC(ISPECL [`list_of_seq (\x:num. x) (ra_state_dim s)`; `s:ra_state`; `k:num`;
    `prefs:num->num list->ra_state->(num option,state_exn)exc#ra_state`]
    assign_Stemps_FOREACH_lem) THEN
  ASM_SIMP_TAC[EVERY_GENLIST] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:ra_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s1:ra_state` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_node_tag]) THEN
  ASM_REWRITE_TAC[RAPROOFAUX_frame_node_tag] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (is_forall o concl)) THEN
  SUBGOAL_THEN `m < ra_state_dim s` ASSUME_TAC THENL
   [ASM_MESON_TAC[good_ra_state_def]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MEM_GENLIST] THEN
  MATCH_MP_TAC(TAUT `p ==> ((if p /\ c then a else b) ==> (if c then a else b))`) THEN
  ASM_MESON_TAC[]);;

(* --  Random sanity checks that will be needed at some point -- *)

(* Checking that biased_pref satisfies good_pref *)
let first_match_col_correct = prove
 (CASE_TERM `!x ks s. ?res. first_match_col ks x s = (res,s) /\
     match res with
       M_failure v -> v = Subscript
     | M_success (SOME k) -> MEM k ks
     | _ -> T`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[first_match_col_def] THEN SIMP RAPROOFAUX_msimps THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN SIMP[] THEN
  CASES_ON `EL h (ra_state_node_tag s)` THEN SIMP[] THEN TRY COND_CASES_TAC THEN SIMP[]);;

let coalesce_root_success = prove
 (`!n s. good_ra_state s /\ n < ra_state_dim s ==>
         ?v. coalesce_root n s = (M_success v,s)`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s:ra_state` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[coalesce_root_def] THEN
  SUBGOAL_THEN `n < LENGTH (ra_state_coalesced s) /\
                EL n (ra_state_coalesced s) < ra_state_dim s /\
                EL n (ra_state_coalesced s) < LENGTH (ra_state_node_tag s)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `good_ra_state s` THEN REWRITE_TAC[good_ra_state_def; GSYM ALL_MEM] THEN
    ASM_MESON_TAC[MEM_EL];
    ALL_TAC] THEN
  SIMP(is_Fixed_def :: RAPROOFAUX_msimps) THEN
  REPEAT(COND_CASES_TAC THEN SIMP[]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `EL n (ra_state_coalesced s)`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:ra_state`) THEN ASM_REWRITE_TAC[]);;

let good_pref_biased_pref = prove
 (`!t. good_pref (biased_pref t)`,
  REWRITE_TAC[good_pref_def; biased_pref_def; get_dim_def] THEN SIMP RAPROOFAUX_msimps THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN SIMP[] THEN
  MP_TAC(SPECL [`n:num`; `s:ra_state`] coalesce_root_success) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP[LET_DEF; LET_END_DEF; reg_alloc_handle_Subscript_def] THEN
  MP_TAC(ISPECL [CASE_TERM `CONS (v:num) (match lookup n (t:(num list)spt) with
                                              NONE -> [] | SOME vs -> vs)`;
                 `ks:num list`; `s:ra_state`] first_match_col_correct) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
  CASES_ON `res:(num option,state_exn)exc` THEN SIMP[] THEN
  TRY(CASES_ON `a:num option`) THEN SIMP[]);;
(* Checking that the bijection produced is correct *)

let in_clash_tree_def = cake_def
  `(in_clash_tree (Delta w r) x <=> MEM x w \/ MEM x r) /\
   (in_clash_tree (reg_alloc_Set names) x <=> x IN domain names) /\
   (in_clash_tree (reg_alloc_Branch name_opt t1 t2) x <=>
      in_clash_tree t1 x \/ in_clash_tree t2 x \/
      (match name_opt with SOME names -> x IN domain names | NONE -> F)) /\
   (in_clash_tree (reg_alloc_Seq t t') x <=> in_clash_tree t x \/ in_clash_tree t' x)`;;

(*g inverts f as an sptree *)
let sp_inverts_def = cake_def
  `sp_inverts (f:num spt) (g:num spt) <=>
     !m fm. lookup m f = SOME fm ==> lookup fm g = SOME m`;;

let sp_inverts_insert = prove
 (`!f g x y. sp_inverts f g /\ ~(x IN domain f) /\ ~(y IN domain g)
     ==> sp_inverts (insert x y f) (insert y x g)`,
  REWRITE_TAC[sp_inverts_def; lookup_insert; domain_lookup] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_INJ] THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[];
    DISCH_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]]);;

(* RAPROOFAUX_TRIPLE_TAC: name the components of a triple *)

let RAPROOFAUX_TRIPLE_TAC (tm:term) (a:term) (b:term) (c:term) : tactic =
  X_CHOOSE_THEN a (X_CHOOSE_THEN b (X_CHOOSE_THEN c ASSUME_TAC))
    (ISPEC tm BASICAUX_TUPLE3);;

let list_remap_domain = prove
 (`!ls (ta:num spt) (fa:num spt) n ta' fa' n'.
     list_remap ls (ta,fa,n) = (ta',fa',n') ==>
     domain ta' = domain ta UNION set_of_list ls`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[list_remap_def; set_of_list; UNION_EMPTY; PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN CASES_ON `lookup h (ta:num spt)` THEN SIMP[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun ih -> FIRST_ASSUM(MP_TAC o MATCH_MP ih)) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[domain_insert; EXTENSION; IN_UNION; IN_INSERT] THEN
  ASM_MESON_TAC[domain_lookup]);;

(* HOL4: val list_remap_bij (an ML value of the script) *)
let RAPROOFAUX_list_remap_bij = prove
 (`!ls (ta:num spt) (fa:num spt) n ta' fa' n'.
     list_remap ls (ta,fa,n) = (ta',fa',n') /\
     sp_inverts ta fa /\
     sp_inverts fa ta /\
     domain fa = count n ==>
     sp_inverts ta' fa' /\
     sp_inverts fa' ta' /\
     domain fa' = count n'`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[list_remap_def; PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN CASES_ON `lookup h (ta:num spt)` THEN SIMP[] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`insert h n (ta:num spt)`; `insert n h (fa:num spt)`;
      `n + 1`; `ta':num spt`; `fa':num spt`; `n':num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `~(h IN domain (ta:num spt)) /\ ~(n IN domain (fa:num spt))`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_COUNT; LT_REFL] THEN
      REWRITE_TAC[domain_lookup] THEN ASM_REWRITE_TAC[option_DISTINCT];
      ALL_TAC] THEN
    ASM_SIMP_TAC[sp_inverts_insert; domain_insert] THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; IN_COUNT] THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`ta:num spt`; `fa:num spt`;
      `n:num`; `ta':num spt`; `fa':num spt`; `n':num`]) THEN
    ASM_REWRITE_TAC[]]);;

let mk_bij_aux_domain = prove
 (`!ct (ta:num spt) (fa:num spt) n ta' fa' n'.
     mk_bij_aux ct (ta,fa,n) = (ta',fa',n') ==>
     domain ta' = domain ta UNION {x | in_clash_tree ct x}`,
  MATCH_MP_TAC clash_tree_INDUCT THEN REWRITE_TAC[mk_bij_aux_def; in_clash_tree_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [RAPROOFAUX_TRIPLE_TAC `list_remap a1 (ta:num spt,fa:num spt,n:num)`
      `ta1:num spt` `fa1:num spt` `n1:num` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    IMP_RES_TAC list_remap_domain THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; IN_SET_OF_LIST] THEN MESON_TAC[];
    DISCH_TAC THEN IMP_RES_TAC list_remap_domain THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; IN_SET_OF_LIST; toAList_domain];
    STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    RAPROOFAUX_TRIPLE_TAC `mk_bij_aux a1 (ta:num spt,fa:num spt,n:num)`
      `ta1:num spt` `fa1:num spt` `n1:num` THEN
    RAPROOFAUX_TRIPLE_TAC `mk_bij_aux a2 (ta1:num spt,fa1:num spt,n1:num)`
      `ta2:num spt` `fa2:num spt` `n2:num` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun ih -> MP_TAC(MATCH_MP ih (ASSUME
      `mk_bij_aux a2 (ta1,fa1,n1) = (ta2:num spt,fa2:num spt,n2:num)`))) THEN
    FIRST_X_ASSUM(fun ih -> MP_TAC(MATCH_MP ih (ASSUME
      `mk_bij_aux a1 (ta,fa,n) = (ta1:num spt,fa1:num spt,n1:num)`))) THEN
    DISCH_TAC THEN DISCH_TAC THEN
    CASES_ON `a0:(1 spt)option` THEN REWRITE_TAC[case_def "option"] THENL
     [REWRITE_TAC[PAIR_EQ] THEN
      DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; DISJ_ACI];
      DISCH_THEN(ASSUME_TAC o MATCH_MP list_remap_domain) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; IN_SET_OF_LIST; toAList_domain;
                  DISJ_ACI]];
    STRIP_TAC THEN REPEAT GEN_TAC THEN
    RAPROOFAUX_TRIPLE_TAC `mk_bij_aux a1 (ta:num spt,fa:num spt,n:num)`
      `ta1:num spt` `fa1:num spt` `n1:num` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun ih -> MP_TAC(MATCH_MP ih (ASSUME
      `mk_bij_aux a1 (ta,fa,n) = (ta1:num spt,fa1:num spt,n1:num)`))) THEN
    FIRST_X_ASSUM(fun ih -> MP_TAC(MATCH_MP ih (ASSUME
      `mk_bij_aux a0 (ta1,fa1,n1) = (ta':num spt,fa':num spt,n':num)`))) THEN
    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; DISJ_ACI]]);;

(* RAPROOFAUX_mk_bij_aux_inv: an invariant of the triples that list_remap  *)
(* preserves is preserved by mk_bij_aux                                    *)
let RAPROOFAUX_mk_bij_aux_inv = prove
 (`!P. (!ls tfn. P tfn ==> P (list_remap ls tfn)) ==>
       !ct (tfn:num spt#num spt#num). P tfn ==> P (mk_bij_aux ct tfn)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC clash_tree_INDUCT THEN
  REWRITE_TAC[mk_bij_aux_def; LET_DEF; LET_END_DEF] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN
  CASES_ON `a0:(1 spt)option` THEN REWRITE_TAC[case_def "option"] THEN
  ASM_SIMP_TAC[]);;

(* HOL4: val mk_bij_aux_bij (an ML value of the script) *)
let RAPROOFAUX_mk_bij_aux_bij = prove
 (`!ct (ta:num spt) (fa:num spt) n ta' fa' n'.
     mk_bij_aux ct (ta,fa,n) = (ta',fa',n') /\
     sp_inverts ta fa /\
     sp_inverts fa ta /\
     domain fa = count n ==>
     sp_inverts ta' fa' /\
     sp_inverts fa' ta' /\
     domain fa' = count n'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\tfn:num spt#num spt#num. sp_inverts (FST tfn) (FST (SND tfn)) /\
                  sp_inverts (FST (SND tfn)) (FST tfn) /\
                  domain (FST (SND tfn)) = count (SND (SND tfn))`
    RAPROOFAUX_mk_bij_aux_inv) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`ls:num list`; `a:num spt`; `b:num spt`; `c:num`] THEN
    RAPROOFAUX_TRIPLE_TAC `list_remap ls (a:num spt,b:num spt,c:num)`
      `a1:num spt` `b1:num spt` `c1:num` THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC RAPROOFAUX_list_remap_bij THEN
    MAP_EVERY EXISTS_TAC [`ls:num list`; `a:num spt`; `b:num spt`; `c:num`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPECL [`ct:clash_tree`; `ta:num spt`; `fa:num spt`; `n:num`]) THEN
    ASM_REWRITE_TAC[]]);;

let list_remap_wf = prove
 (`!l (ta:num spt) (fa:num spt) n ta' fa' n'.
     list_remap l (ta,fa,n) = (ta',fa',n') /\ wf ta /\ wf fa ==>
     wf ta' /\ wf fa'`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[list_remap_def; PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN CASES_ON `lookup h (ta:num spt)` THEN
  ASM_REWRITE_TAC[case_def "option"] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`insert h n (ta:num spt)`; `insert n h (fa:num spt)`; `n + 1`;
                        `n':num`] THEN
  ASM_MESON_TAC[wf_insert]);;

let mk_bij_aux_wf = prove
 (`!ct (ta:num spt) (fa:num spt) n ta' fa' n'.
     mk_bij_aux ct (ta,fa,n) = (ta',fa',n') /\
     wf ta /\ wf fa ==>
     Abbrev(wf ta' /\ wf fa')`,
  REWRITE_TAC[marker_Abbrev_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\tfn:num spt#num spt#num. wf (FST tfn) /\ wf (FST (SND tfn))`
    RAPROOFAUX_mk_bij_aux_inv) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`ls:num list`; `a:num spt`; `b:num spt`; `c:num`] THEN
    RAPROOFAUX_TRIPLE_TAC `list_remap ls (a:num spt,b:num spt,c:num)`
      `a1:num spt` `b1:num spt` `c1:num` THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC list_remap_wf THEN
    MAP_EVERY EXISTS_TAC [`ls:num list`; `a:num spt`; `b:num spt`; `c:num`; `c1:num`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPECL [`ct:clash_tree`; `ta:num spt`; `fa:num spt`; `n:num`]) THEN
    ASM_REWRITE_TAC[]]);;


(* Properties of the graph manipulating functions
   All of these simultaneously prove success
   together with the correctness properties.

   One could also imagine proving the success separately from
   the correctness
*)
(* the list represents a clique *)
let is_clique_def = cake_def
  `is_clique ls adjls <=>
     !x y. MEM x ls /\ MEM y ls /\ ~(x = y) ==> has_edge adjls x y`;;

let is_subgraph_def = cake_def
  `is_subgraph g h <=> !x y. has_edge g x y ==> has_edge h x y`;;

let is_subgraph_refl = prove
 (`!s. is_subgraph s s`,
  REWRITE_TAC[is_subgraph_def]);;

let is_subgraph_trans = prove
 (`!s s' s''. is_subgraph s s' /\ is_subgraph s' s'' ==> is_subgraph s s''`,
  REWRITE_TAC[is_subgraph_def] THEN MESON_TAC[]);;

(* TODO quick sanity check: move to proof file when done *)
(* HOL4: hide *)
let reg_allocProof_hide_def = cake_def
  `reg_allocProof_hide (x:A) = x`;;

let GT_TRANS = prove
 (`!a b c. a:num > b /\ b > c ==> a > c`,
  ARITH_TAC);;

let RAPROOFAUX_transitive_GT = prove
 (`transitive ((>):num->num->bool)`,
  REWRITE_TAC[transitive_def] THEN ARITH_TAC);;

let GT_sorted_eq = prove
 (`!x L. SORTED (>) (CONS (x:num) L) <=> SORTED (>) L /\ !y. MEM y L ==> x > y`,
  SIMP_TAC[SORTED_EQ; RAPROOFAUX_transitive_GT]);;
let sorted_insert_correct_lem = prove
 (`!ls acc x.
     SORTED (>) ls /\
     SORTED (>) (REVERSE acc) /\
     SORTED (>) (APPEND (REVERSE acc) ls) /\
     ALL (\y. y > x) acc ==>
     reg_allocProof_hide
      (SORTED (>) (sorted_insert x acc ls) /\
       !z. MEM z (sorted_insert x acc ls) <=> x = z \/ MEM z ls \/ MEM z acc)`,
  REWRITE_TAC[reg_allocProof_hide_def] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[sorted_insert_def] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[REVERSE; MEM_APPEND; MEM_REVERSE; MEM] THEN
    ASM_SIMP_TAC[SORTED_APPEND; RAPROOFAUX_transitive_GT; SORTED_DEF; MEM_REVERSE; MEM] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `ALL (\y. y > x) (acc:num list)` THEN REWRITE_TAC[GSYM ALL_MEM] THEN
      MESON_TAC[];
      MESON_TAC[]];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[MEM_APPEND; MEM_REVERSE; MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [UNDISCH_TAC `SORTED (>) (APPEND (REVERSE acc) (CONS h t))` THEN
    ASM_SIMP_TAC[SORTED_APPEND; RAPROOFAUX_transitive_GT; MEM_APPEND; MEM_REVERSE; MEM;
                 SORTED_DEF] THEN
    UNDISCH_TAC `ALL (\y. y > x) (acc:num list)` THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (h:num) acc`; `x:num`]) THEN ANTS_TAC THENL
   [UNDISCH_TAC `SORTED (>) (APPEND (REVERSE acc) (CONS h t))` THEN
    UNDISCH_TAC `SORTED (>) (CONS (h:num) t)` THEN
    ASM_SIMP_TAC[REVERSE; GSYM APPEND_ASSOC; APPEND; SORTED_APPEND; RAPROOFAUX_transitive_GT;
                 MEM_APPEND; MEM_REVERSE; MEM; SORTED_DEF; ALL; GT_sorted_eq] THEN
    REPEAT DISCH_TAC THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_MESON_TAC[]; ASM_ARITH_TAC];
    REWRITE_TAC[MEM] THEN MESON_TAC[]]);;

let sorted_insert_correct = prove
 (`!ls x.
     SORTED (>) ls ==>
     SORTED (>) (sorted_insert x [] ls) /\
     !z. MEM z (sorted_insert x [] ls) <=> x = z \/ MEM z ls`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`ls:num list`; `[]:num list`; `x:num`] sorted_insert_correct_lem) THEN
  ASM_REWRITE_TAC[reg_allocProof_hide_def; REVERSE; APPEND; SORTED_DEF; ALL; MEM]);;

let sorted_mem_correct = prove
 (`!ls x. SORTED (>) ls ==> (sorted_mem x ls <=> MEM x ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[sorted_mem_def; MEM; GT_sorted_eq] THEN
  REPEAT STRIP_TAC THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[ARITH_RULE `~(x:num > y /\ y > x)`]);;
let insert_edge_succeeds = prove
 (`!s x y.
     good_ra_state s /\ y < ra_state_dim s /\ x < ra_state_dim s ==>
     ?s'. insert_edge x y s = (M_success one,s') /\
          good_ra_state s' /\
          s' = ra_state_adj_ls_fupd (K (ra_state_adj_ls s')) s /\
          !a b. has_edge (ra_state_adj_ls s') a b <=>
                (a = x /\ b = y) \/ (a = y /\ b = x) \/ has_edge (ra_state_adj_ls s) a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `x < LENGTH (ra_state_adj_ls s) /\ y < LENGTH (ra_state_adj_ls s)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[good_ra_state_def]; ALL_TAC] THEN
  REWRITE_TAC[insert_edge_def] THEN SIMP RAPROOFAUX_msimps THEN
  SUBGOAL_THEN `!i. i < LENGTH (ra_state_adj_ls s) ==>
     SORTED (>) (EL i (ra_state_adj_ls s)) /\
     ALL (\v. v < ra_state_dim s) (EL i (ra_state_adj_ls s))` ASSUME_TAC THENL
   [UNDISCH_TAC `good_ra_state s` THEN REWRITE_TAC[good_ra_state_def; GSYM ALL_EL] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[has_edge_def; LENGTH_LUPDATE; EL_LUPDATE] THEN
    ASM_REWRITE_TAC[LENGTH_LUPDATE] THEN
    REPEAT GEN_TAC THEN ASM_CASES_TAC `a:num = y` THEN ASM_REWRITE_TAC[] THENL
     [ASM_SIMP_TAC[sorted_insert_correct] THEN ASM_MESON_TAC[];
      ASM_CASES_TAC `a:num = x` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[sorted_insert_correct] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN UNDISCH_TAC `good_ra_state s` THEN REWRITE_TAC[good_ra_state_def] THEN
  SIMP[LENGTH_LUPDATE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC IMP_EVERY_LUPDATE THEN CONJ_TAC) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN ASM_SIMP_TAC[sorted_insert_correct] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN ASM_MESON_TAC[];
    REPEAT(MATCH_MP_TAC IMP_EVERY_LUPDATE THEN CONJ_TAC) THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[sorted_insert_correct];
    REWRITE_TAC[undirected_def] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[undirected_def]]);;
let RAPROOFAUX_frame_adj_ls = RAPROOFAUX_frame ["adj_ls"];;

let list_insert_edge_succeeds = prove
 (`!ys x s.
     good_ra_state s /\ x < ra_state_dim s /\ ALL (\y. y < ra_state_dim s) ys ==>
     ?s'. list_insert_edge x ys s = (M_success one,s') /\
          good_ra_state s' /\
          s' = ra_state_adj_ls_fupd (K (ra_state_adj_ls s')) s /\
          !a b. has_edge (ra_state_adj_ls s') a b <=>
                (a = x /\ MEM b ys) \/ (b = x /\ MEM a ys) \/
                has_edge (ra_state_adj_ls s) a b`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[list_insert_edge_def; st_ex_return_def; MEM] THEN
    SIMP[] THEN SIMP[ra_state_component_equality];
    ALL_TAC] THEN
  REWRITE_TAC[ALL; MEM; list_insert_edge_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:ra_state`; `x:num`; `h:num`] insert_edge_succeeds) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:ra_state` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_ignore_bind_ok th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `s1:ra_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:ra_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s2:ra_state` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  ASM_REWRITE_TAC[RAPROOFAUX_frame_adj_ls] THEN MESON_TAC[]);;
(* From here onwards we stop characterizing s'.adj_ls exactly
   although it could be done
 *)
let clique_insert_edge_succeeds = prove
 (`!ls s.
     good_ra_state s /\ ALL (\y. y < ra_state_dim s) ls ==>
     ?s'. clique_insert_edge ls s = (M_success one,s') /\
          good_ra_state s' /\
          s' = ra_state_adj_ls_fupd (K (ra_state_adj_ls s')) s /\
          is_clique ls (ra_state_adj_ls s') /\
          is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s')`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[clique_insert_edge_def; st_ex_return_def] THEN
    SIMP[] THEN SIMP[ra_state_component_equality; is_clique_def; is_subgraph_def; MEM];
    ALL_TAC] THEN
  REWRITE_TAC[ALL; clique_insert_edge_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`t:num list`; `h:num`; `s:ra_state`] list_insert_edge_succeeds) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:ra_state` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_ignore_bind_ok th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s1:ra_state`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:ra_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s2:ra_state` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  ASM_REWRITE_TAC[RAPROOFAUX_frame_adj_ls] THEN
  UNDISCH_TAC `is_subgraph (ra_state_adj_ls s1) (ra_state_adj_ls s2)` THEN
  UNDISCH_TAC `is_clique t (ra_state_adj_ls s2)` THEN
  REWRITE_TAC[is_clique_def; is_subgraph_def; MEM] THEN ASM_MESON_TAC[]);;
let extend_clique_succeeds = prove
 (`!ls cli s.
     good_ra_state s /\
     is_clique cli (ra_state_adj_ls s) /\
     ALL (\y. y < ra_state_dim s) ls /\
     ALL_DISTINCT cli /\
     ALL (\y. y < ra_state_dim s) cli ==>
     ?cli' s'. extend_clique ls cli s = (M_success cli',s') /\
               good_ra_state s' /\
               ALL_DISTINCT cli' /\
               s' = ra_state_adj_ls_fupd (K (ra_state_adj_ls s')) s /\
               set_of_list cli' = set_of_list (APPEND cli ls) /\
               is_clique cli' (ra_state_adj_ls s') /\
               is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s')`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[extend_clique_def; st_ex_return_def; APPEND_NIL] THEN
    SIMP[] THEN SIMP[ra_state_component_equality; is_subgraph_def];
    ALL_TAC] THEN
  REWRITE_TAC[ALL; extend_clique_def] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`cli:num list`; `s:ra_state`]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_APPEND; MEM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cli:num list`; `h:num`; `s:ra_state`] list_insert_edge_succeeds) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:ra_state` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_ignore_bind_ok th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (h:num) cli`; `s1:ra_state`]) THEN
  ASM_REWRITE_TAC[ALL; ALL_DISTINCT] THEN ANTS_TAC THENL
   [UNDISCH_TAC `is_clique cli (ra_state_adj_ls s)` THEN
    REWRITE_TAC[is_clique_def; MEM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cli1:num list` (X_CHOOSE_THEN `s2:ra_state` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`cli1:num list`; `s2:ra_state`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  ASM_REWRITE_TAC[RAPROOFAUX_frame_adj_ls] THEN CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_APPEND; MEM] THEN MESON_TAC[];
    UNDISCH_TAC `is_subgraph (ra_state_adj_ls s1) (ra_state_adj_ls s2)` THEN
    REWRITE_TAC[is_subgraph_def] THEN ASM_MESON_TAC[]]);;

(* The col needed to get colouring satisfactory can be generated
   from the node tags
   The correctness should be a consequence of no_clash *)
let colouring_satisfactory_def = cake_def
  `colouring_satisfactory (col:num->C) (adjls:(num list)list) <=>
     !x. x < LENGTH adjls ==>
         (!y. y < LENGTH adjls /\ MEM y (EL x adjls) ==> col x = col y ==> x = y)`;;

(*TODO: this is in word_allocProof*)
(* HOL4: INJ_less *)
let reg_allocProof_INJ_less = prove
 (`!(f:A->B) s' t s. INJ f s' t /\ s SUBSET s' ==> INJ f s t`,
  REWRITE_TAC[INJ; SUBSET] THEN MESON_TAC[]);;

let check_partial_col_success = prove
 (`!ls live flive (col:num->num).
     domain flive = IMAGE col (domain live) /\
     INJ col (set_of_list ls UNION domain live) UNIV
     ==> ?livein flivein.
           check_partial_col col ls live flive = SOME (livein,flivein) /\
           domain flivein = IMAGE col (domain livein)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[check_partial_col_def; option_INJ; PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CASES_ON `lookup h (live:1 spt)` THEN REWRITE_TAC[case_def "option"] THENL
   [CASES_ON `lookup ((col:num->num) h) (flive:1 spt)` THEN
    REWRITE_TAC[case_def "option"] THENL
     [ALL_TAC;
      SUBGOAL_THEN `(col:num->num) h IN domain (flive:1 spt)` MP_TAC THENL
       [REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x':num` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `INJ (col:num->num) (set_of_list (CONS h t) UNION domain (live:1 spt)) UNIV` THEN
      REWRITE_TAC[INJ; IN_UNION; IN_SET_OF_LIST; MEM] THEN
      DISCH_THEN(MP_TAC o SPECL [`h:num`; `x':num`] o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_MESON_TAC[domain_lookup; option_DISTINCT]] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[domain_insert; IMAGE_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC reg_allocProof_INJ_less THEN
    EXISTS_TAC `set_of_list (CONS (h:num) t) UNION domain (live:1 spt)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[set_of_list] THEN SET_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC reg_allocProof_INJ_less THEN
    EXISTS_TAC `set_of_list (CONS (h:num) t) UNION domain (live:1 spt)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[set_of_list] THEN SET_TAC[]]);;
let INJ_COMPOSE_IMAGE = prove
 (`!a b u (f:A->B) (g:B->C). INJ f a b /\ INJ g (IMAGE f a) u ==> INJ (g o f) a u`,
  REWRITE_TAC[INJ; IN_IMAGE; o_THM] THEN MESON_TAC[]);;

let colouring_satisfactory_cliques = prove
 (`!ls g (f:num->num).
     ALL_DISTINCT ls /\
     ALL (\x. x < LENGTH g) ls /\
     colouring_satisfactory f g /\ is_clique ls g
     ==> ALL_DISTINCT (MAP f ls)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL_DISTINCT; MAP; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[MEM_MAP] THEN DISCH_THEN(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `has_edge g h y` MP_TAC THENL
     [UNDISCH_TAC `is_clique (CONS h t) g` THEN REWRITE_TAC[is_clique_def; MEM] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[has_edge_def] THEN STRIP_TAC THEN
    UNDISCH_TAC `colouring_satisfactory (f:num->num) g` THEN
    REWRITE_TAC[colouring_satisfactory_def] THEN
    DISCH_THEN(MP_TAC o SPEC `h:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `y:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `g:(num list)list` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `is_clique (CONS h t) g` THEN REWRITE_TAC[is_clique_def; MEM] THEN
    MESON_TAC[]]);;

let domain_eq_IMAGE = prove
 (`!s:A spt. domain s = IMAGE FST (set_of_list (toAList s))`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SET_OF_LIST; EXISTS_PAIR_THM; MEM_toAList;
              domain_lookup] THEN
  MESON_TAC[]);;

let is_clique_FILTER = prove
 (`!ls G P. is_clique ls G ==> is_clique (FILTER P ls) G`,
  REWRITE_TAC[is_clique_def; MEM_FILTER] THEN MESON_TAC[]);;

let is_clique_subgraph = prove
 (`!ls s s'. is_clique ls s /\ is_subgraph s s' ==> is_clique ls s'`,
  REWRITE_TAC[is_clique_def; is_subgraph_def] THEN MESON_TAC[]);;

(* HOL4: domain_numset_list_delete *)
let reg_allocProof_domain_numset_list_delete = prove
 (`!l (live:A spt). domain (numset_list_delete l live) = domain live DIFF set_of_list l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[numset_list_delete_def; set_of_list; DIFF_EMPTY;
    domain_delete] THEN SET_TAC[]);;

(* RAPROOFAUX_mk_graph_P ct: the statement of mk_graph_succeeds for the     *)
(* clash tree ct (a term string), used for the cases of its induction      *)
let RAPROOFAUX_mk_graph_P (ct:string) =
  "!(ta:num->num) liveout s.
     good_ra_state s /\\
     (!x. in_clash_tree ("^ct^") x ==> ta x < ra_state_dim s) /\\
     INJ ta {x | in_clash_tree ("^ct^") x} (count (LENGTH (ra_state_adj_ls s))) /\\
     is_clique liveout (ra_state_adj_ls s) /\\
     ALL_DISTINCT liveout /\\
     ALL (\\y. y < ra_state_dim s) liveout
     ==> ?livein s'. mk_graph ta ("^ct^") liveout s = (M_success livein,s') /\\
           good_ra_state s' /\\
           is_clique livein (ra_state_adj_ls s') /\\
           s' = ra_state_adj_ls_fupd (K (ra_state_adj_ls s')) s /\\
           ALL (\\y. y < ra_state_dim s) livein /\\
           ALL_DISTINCT livein /\\
           set_of_list livein SUBSET
             set_of_list liveout UNION IMAGE ta {x | in_clash_tree ("^ct^") x} /\\
           is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s')";;

let RAPROOFAUX_mk_graph_Delta = prove
 (parse_term ("!w r. "^RAPROOFAUX_mk_graph_P "Delta w r"),
  REPEAT GEN_TAC THEN REWRITE_TAC[mk_graph_def; in_clash_tree_def] THEN STRIP_TAC THEN
  SIMP RAPROOFAUX_msimps THEN
  MP_TAC(SPECL [`MAP (ta:num->num) w`; `liveout:num list`; `s:ra_state`]
    extend_clique_succeeds) THEN
  ASM_SIMP_TAC[ALL_MAP; o_DEF] THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `live1:num list` (X_CHOOSE_THEN `s1:ra_state`
    STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  SUBGOAL_THEN `!z. MEM z live1 <=> MEM z liveout \/ MEM z (MAP (ta:num->num) w)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `set_of_list live1 = set_of_list (APPEND liveout (MAP (ta:num->num) w))` THEN
    REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_APPEND]; ALL_TAC] THEN
  MP_TAC(SPECL [`MAP (ta:num->num) r`; `FILTER (\x. ~MEM x (MAP (ta:num->num) w)) live1`;
    `s1:ra_state`] extend_clique_succeeds) THEN
  ASM_SIMP_TAC[ALL_MAP; o_DEF; is_clique_FILTER; FILTER_ALL_DISTINCT; EVERY_FILTER] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `ALL (\y. y < ra_state_dim s) liveout` THEN
    UNDISCH_TAC `!x. MEM x w \/ MEM x r ==> (ta:num->num) x < ra_state_dim s` THEN
    UNDISCH_TAC `!z. MEM z live1 <=> MEM z liveout \/ MEM z (MAP (ta:num->num) w)` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `livein:num list` (X_CHOOSE_THEN `s2:ra_state`
    STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  ASM_REWRITE_TAC[RAPROOFAUX_frame_adj_ls] THEN
  SUBGOAL_THEN `!z. MEM z livein ==>
                    MEM z liveout \/ ?x. z = (ta:num->num) x /\ (MEM x w \/ MEM x r)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `set_of_list livein = set_of_list (APPEND (FILTER (\x. ~MEM x
       (MAP (ta:num->num) w)) live1) (MAP ta r))` THEN
    UNDISCH_TAC `!z. MEM z live1 <=> MEM z liveout \/ MEM z (MAP (ta:num->num) w)` THEN
    REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_APPEND; MEM_FILTER; MEM_MAP] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `z:num` THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    UNDISCH_TAC `ALL (\y. y < ra_state_dim s) liveout` THEN
    UNDISCH_TAC `!x. MEM x w \/ MEM x r ==> (ta:num->num) x < ra_state_dim s` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
    REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_FILTER; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
    UNDISCH_TAC `!z. MEM z live1 <=> MEM z liveout \/ MEM z (MAP (ta:num->num) w)` THEN
    REWRITE_TAC[MEM_MAP] THEN MESON_TAC[];
    REWRITE_TAC[SUBSET; IN_SET_OF_LIST; IN_UNION; IN_IMAGE; IN_ELIM_THM; MEM_MAP] THEN
    MESON_TAC[];
    ASM_MESON_TAC[is_subgraph_trans]]);;

let RAPROOFAUX_mk_graph_Set = prove
 (parse_term ("!t. "^RAPROOFAUX_mk_graph_P "reg_alloc_Set t"),
  REPEAT GEN_TAC THEN REWRITE_TAC[mk_graph_def; in_clash_tree_def] THEN STRIP_TAC THEN
  SIMP RAPROOFAUX_msimps THEN
  SUBGOAL_THEN `ALL (\y. y < ra_state_dim s) (MAP (ta:num->num) (MAP FST (toAList (t:1 spt))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[toAList_domain; MEM_MAP];
    ALL_TAC] THEN
  MP_TAC(SPECL [`MAP (ta:num->num) (MAP FST (toAList (t:1 spt)))`; `s:ra_state`]
    clique_insert_edge_succeeds) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:ra_state` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_ignore_bind_ok th]) THEN
  SIMP RAPROOFAUX_msimps THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  ASM_REWRITE_TAC[RAPROOFAUX_frame_adj_ls] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList] THEN
    UNDISCH_TAC `INJ (ta:num->num) {x | x IN domain (t:1 spt)}
                   (count (LENGTH (ra_state_adj_ls s)))` THEN
    REWRITE_TAC[INJ; IN_ELIM_THM; toAList_domain] THEN MESON_TAC[];
    REWRITE_TAC[SUBSET; IN_SET_OF_LIST] THEN ONCE_REWRITE_TAC[MEM_MAP] THEN
    REWRITE_TAC[toAList_domain; IN_UNION; IN_IMAGE; IN_ELIM_THM; IN_SET_OF_LIST] THEN
    MESON_TAC[]]);;

let RAPROOFAUX_mk_graph_Branch = prove
 (parse_term ("!topt t1 t2. ("^RAPROOFAUX_mk_graph_P "t1"^") /\\ ("^
    RAPROOFAUX_mk_graph_P "t2"^") ==> "^RAPROOFAUX_mk_graph_P "reg_alloc_Branch topt t1 t2"),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[mk_graph_def; in_clash_tree_def] THEN STRIP_TAC THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`ta:num->num`; `liveout:num list`; `s:ra_state`]) THEN
  ASM_SIMP_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC reg_allocProof_INJ_less THEN
    EXISTS_TAC (CASE_TERM `{x | in_clash_tree t1 x \/ in_clash_tree t2 x \/
                     (match topt with NONE -> F | SOME names -> x IN domain (names:1 spt))}`) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `live1:num list` (X_CHOOSE_THEN `s1:ra_state` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_bind_ok th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  SUBGOAL_THEN `LENGTH (ra_state_adj_ls s1) = LENGTH (ra_state_adj_ls s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[good_ra_state_def]; ALL_TAC] THEN
  REMOVE_THEN "ih2" (MP_TAC o SPECL [`ta:num->num`; `liveout:num list`; `s1:ra_state`]) THEN
  ASM_SIMP_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC reg_allocProof_INJ_less THEN
      EXISTS_TAC (CASE_TERM `{x | in_clash_tree t1 x \/ in_clash_tree t2 x \/
                     (match topt with NONE -> F | SOME names -> x IN domain (names:1 spt))}`) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ASM_MESON_TAC[is_clique_subgraph]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `live2:num list` (X_CHOOSE_THEN `s2:ra_state` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_bind_ok th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  CASES_ON `topt:(1 spt)option` THEN RULE_ASSUM_TAC(REWRITE_RULE[case_def "option"]) THEN
  REWRITE_TAC[case_def "option"] THENL
  [(MP_TAC(SPECL [`live1:num list`; `live2:num list`; `s2:ra_state`] extend_clique_succeeds) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `livein:num list` (X_CHOOSE_THEN `s3:ra_state` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_bind_ok th]) THEN
  SIMP RAPROOFAUX_msimps THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  ASM_REWRITE_TAC[RAPROOFAUX_frame_adj_ls]) THEN
   (REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `set_of_list (livein:num list) = set_of_list (APPEND live2 live1)` THEN
    UNDISCH_TAC `ALL (\y. y < ra_state_dim s) live1` THEN
    UNDISCH_TAC `ALL (\y. y < ra_state_dim s) live2` THEN
    REWRITE_TAC[GSYM ALL_MEM; EXTENSION; IN_SET_OF_LIST; MEM_APPEND] THEN MESON_TAC[];
    UNDISCH_TAC `set_of_list live2 SUBSET
      set_of_list liveout UNION IMAGE (ta:num->num) {x | in_clash_tree t2 x}` THEN
    SET_TAC[];
    UNDISCH_TAC `set_of_list live1 SUBSET
      set_of_list liveout UNION IMAGE (ta:num->num) {x | in_clash_tree t1 x}` THEN
    SET_TAC[];
    ASM_MESON_TAC[is_subgraph_trans]]);
   SIMP RAPROOFAUX_msimps THEN
  SUBGOAL_THEN `ALL (\y. y < ra_state_dim s) (MAP (ta:num->num) (MAP FST (toAList (a:1 spt))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[toAList_domain; MEM_MAP];
    ALL_TAC] THEN
  MP_TAC(SPECL [`MAP (ta:num->num) (MAP FST (toAList (a:1 spt)))`; `s2:ra_state`]
    clique_insert_edge_succeeds) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:ra_state` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_ignore_bind_ok th]) THEN
  SIMP RAPROOFAUX_msimps THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  ASM_REWRITE_TAC[RAPROOFAUX_frame_adj_ls] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList] THEN
    UNDISCH_TAC `INJ (ta:num->num) {x | in_clash_tree t1 x \/ in_clash_tree t2 x \/
                    x IN domain (a:1 spt)} (count (LENGTH (ra_state_adj_ls s)))` THEN
    REWRITE_TAC[INJ; IN_ELIM_THM; toAList_domain] THEN MESON_TAC[];
    REWRITE_TAC[SUBSET; IN_SET_OF_LIST] THEN ONCE_REWRITE_TAC[MEM_MAP] THEN
    REWRITE_TAC[toAList_domain; IN_UNION; IN_IMAGE; IN_ELIM_THM; IN_SET_OF_LIST] THEN
    MESON_TAC[];
    ASM_MESON_TAC[is_subgraph_trans]]]);;

let RAPROOFAUX_mk_graph_Seq = prove
 (parse_term ("!t1 t2. ("^RAPROOFAUX_mk_graph_P "t1"^") /\\ ("^
              RAPROOFAUX_mk_graph_P "t2"^") ==> "^
              RAPROOFAUX_mk_graph_P "reg_alloc_Seq t1 t2"),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[mk_graph_def; in_clash_tree_def] THEN STRIP_TAC THEN
  REMOVE_THEN "ih2" (MP_TAC o SPECL [`ta:num->num`; `liveout:num list`; `s:ra_state`]) THEN
  ASM_SIMP_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC reg_allocProof_INJ_less THEN
    EXISTS_TAC `{x | in_clash_tree t1 x \/ in_clash_tree t2 x}` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `live1:num list` (X_CHOOSE_THEN `s1:ra_state` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_bind_ok th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  SUBGOAL_THEN `LENGTH (ra_state_adj_ls s1) = LENGTH (ra_state_adj_ls s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[good_ra_state_def]; ALL_TAC] THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`ta:num->num`; `live1:num list`; `s1:ra_state`]) THEN
  ASM_SIMP_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC reg_allocProof_INJ_less THEN
    EXISTS_TAC `{x | in_clash_tree t1 x \/ in_clash_tree t2 x}` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `livein:num list` (X_CHOOSE_THEN `s2:ra_state` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`livein:num list`; `s2:ra_state`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  ASM_REWRITE_TAC[RAPROOFAUX_frame_adj_ls] THEN CONJ_TAC THENL
   [UNDISCH_TAC `set_of_list (livein:num list) SUBSET
      set_of_list live1 UNION IMAGE (ta:num->num) {x | in_clash_tree t1 x}` THEN
    UNDISCH_TAC `set_of_list (live1:num list) SUBSET
      set_of_list liveout UNION IMAGE (ta:num->num) {x | in_clash_tree t2 x}` THEN
    SET_TAC[];
    ASM_MESON_TAC[is_subgraph_trans]]);;

(* The success theorem is separated here *)
let mk_graph_succeeds = prove
 (`!ct (ta:num->num) liveout s.
     good_ra_state s /\
     (!x. in_clash_tree ct x ==> ta x < ra_state_dim s) /\
     INJ ta {x | in_clash_tree ct x} (count (LENGTH (ra_state_adj_ls s))) /\
     is_clique liveout (ra_state_adj_ls s) /\
     ALL_DISTINCT liveout /\
     ALL (\y. y < ra_state_dim s) liveout
     ==> ?livein s'. mk_graph ta ct liveout s = (M_success livein,s') /\
           good_ra_state s' /\
           is_clique livein (ra_state_adj_ls s') /\
           s' = ra_state_adj_ls_fupd (K (ra_state_adj_ls s')) s /\
           ALL (\y. y < ra_state_dim s) livein /\
           ALL_DISTINCT livein /\
           set_of_list livein SUBSET
             set_of_list liveout UNION IMAGE ta {x | in_clash_tree ct x} /\
           is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s')`,
  MATCH_MP_TAC clash_tree_INDUCT THEN
  REWRITE_TAC[RAPROOFAUX_mk_graph_Delta; RAPROOFAUX_mk_graph_Set;
              RAPROOFAUX_mk_graph_Branch; RAPROOFAUX_mk_graph_Seq]);;

let colouring_satisfactory_subgraph = prove
 (`!f g h. colouring_satisfactory (f:num->C) h /\ is_subgraph g h
           ==> colouring_satisfactory f g`,
  REWRITE_TAC[colouring_satisfactory_def; is_subgraph_def; has_edge_def] THEN
  MESON_TAC[]);;

let ALL_DISTINCT_set_INJ = prove
 (`!ls (col:A->B). ALL_DISTINCT (MAP col ls) ==> INJ col (set_of_list ls) UNIV`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[INJ; IN_SET_OF_LIST; IN_UNIV; MAP; ALL_DISTINCT; MEM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `col:A->B`) THEN
  ASM_REWRITE_TAC[INJ; IN_SET_OF_LIST; IN_UNIV] THEN
  UNDISCH_TAC `~MEM ((col:A->B) h) (MAP col t)` THEN REWRITE_TAC[MEM_MAP] THEN
  MESON_TAC[]);;

(* HOL4: IMAGE_DIFF *)
let reg_allocProof_IMAGE_DIFF = prove
 (`!(f:A->B) s t. INJ f (s UNION t) UNIV ==>
     IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t`,
  REWRITE_TAC[EXTENSION; INJ; IN_IMAGE; IN_DIFF; IN_UNION; IN_UNIV] THEN MESON_TAC[]);;

let set_FILTER = prove
 (`!P (live:A list). set_of_list (FILTER P live) = set_of_list live DIFF (\x. ~P x)`,
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; MEM_FILTER; IN_DIFF] THEN
  REWRITE_TAC[IN] THEN MESON_TAC[]);;

let MEM_MAP_IMAGE = prove
 (`!(f:A->B) l. (\x. MEM x (MAP f l)) = IMAGE f (set_of_list l)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SET_OF_LIST; MEM_MAP] THEN REWRITE_TAC[IN] THEN
  MESON_TAC[]);;

(* HOL4 [local] domain_difference: the same statement as sptree's          *)
(* domain_difference, which is used                                         *)

let UNION_DIFF_3 = prove
 (`!(s:A->bool) t. s DIFF t UNION t = s UNION t`,
  SET_TAC[]);;

let check_partial_col_domain = prove
 (`!ls (f:num->num) live flive v.
     check_partial_col f ls live flive = SOME v ==>
     domain (FST v) = set_of_list ls UNION domain live`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[check_partial_col_def; option_INJ] THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[set_of_list; UNION_EMPTY];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN CASES_ON `lookup h (live:1 spt)` THEN
  REWRITE_TAC[case_def "option"] THENL
   [CASES_ON `lookup ((f:num->num) h) (flive:1 spt)` THEN
    REWRITE_TAC[case_def "option"; option_DISTINCT] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[domain_insert; set_of_list] THEN SET_TAC[];
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[set_of_list] THEN
    SUBGOAL_THEN `(h:num) IN domain (live:1 spt)` MP_TAC THENL
     [ASM_REWRITE_TAC[domain_lookup] THEN MESON_TAC[]; SET_TAC[]]]);;

let check_clash_tree_domain = prove
 (`!ct (f:num->num) live flive live' flive'.
     check_clash_tree f ct live flive = SOME (live',flive') ==>
     domain live' SUBSET domain live UNION {x | in_clash_tree ct x}`,
  MATCH_MP_TAC clash_tree_INDUCT THEN
  REWRITE_TAC[check_clash_tree_def; in_clash_tree_def; check_col_def; LET_DEF; LET_END_DEF] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[option_case_eq; option_DISTINCT] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP check_partial_col_domain) THEN
    REWRITE_TAC[reg_allocProof_domain_numset_list_delete] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_DIFF; IN_SET_OF_LIST; IN_ELIM_THM] THEN MESON_TAC[];
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[option_case_eq; pair_case_eq; option_DISTINCT] THEN STRIP_TAC THEN
    RVEQ_TAC THEN REWRITE_TAC[case_def "option"] THENL
     [USE_THEN "ih1" (MP_TAC o C MATCH_MP (ASSUME
        `check_clash_tree (f:num->num) a1 live flive = SOME (x,y)`)) THEN
      USE_THEN "ih2" (MP_TAC o C MATCH_MP (ASSUME
        `check_clash_tree (f:num->num) a2 live flive = SOME (x',y')`)) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP check_partial_col_domain) THEN
      REWRITE_TAC[FST] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[SUBSET; IN_UNION; IN_SET_OF_LIST; toAList_domain; domain_difference;
                  IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[];
      POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[option_case_eq; pair_case_eq; option_DISTINCT] THEN STRIP_TAC THEN
    RVEQ_TAC THEN
    USE_THEN "ih2" (MP_TAC o C MATCH_MP (ASSUME
      `check_clash_tree (f:num->num) a1 live flive = SOME (x,y)`)) THEN
    USE_THEN "ih1" (MP_TAC o C MATCH_MP (ASSUME
      `check_clash_tree (f:num->num) a0 x y = SOME (live',flive')`)) THEN
    SET_TAC[]]);;

let RAPROOFAUX_good_lengths = prove
 (`!s. good_ra_state s ==>
       LENGTH (ra_state_adj_ls s) = ra_state_dim s /\
       LENGTH (ra_state_node_tag s) = ra_state_dim s /\
       LENGTH (ra_state_degrees s) = ra_state_dim s /\
       LENGTH (ra_state_coalesced s) = ra_state_dim s /\
       LENGTH (ra_state_move_related s) = ra_state_dim s`,
  SIMP_TAC[good_ra_state_def]);;

(* RAPROOFAUX_..._props: the facts of the _succeeds theorems, for a given result *)
let RAPROOFAUX_extend_clique_props = prove
 (`!ls cli s cli' s'.
     extend_clique ls cli s = (M_success cli',s') /\
     good_ra_state s /\
     is_clique cli (ra_state_adj_ls s) /\
     ALL (\y. y < ra_state_dim s) ls /\
     ALL_DISTINCT cli /\
     ALL (\y. y < ra_state_dim s) cli ==>
     good_ra_state s' /\
     ALL_DISTINCT cli' /\
     s' = ra_state_adj_ls_fupd (K (ra_state_adj_ls s')) s /\
     set_of_list cli' = set_of_list (APPEND cli ls) /\
     is_clique cli' (ra_state_adj_ls s') /\
     is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ls:num list`; `cli:num list`; `s:ra_state`] extend_clique_succeeds) THEN
  ASM_REWRITE_TAC[PAIR_EQ; injectivity "exc"] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num list` (X_CHOOSE_THEN `t:ra_state` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let RAPROOFAUX_clique_insert_edge_props = prove
 (`!ls s u s'.
     clique_insert_edge ls s = (M_success u,s') /\
     good_ra_state s /\ ALL (\y. y < ra_state_dim s) ls ==>
     good_ra_state s' /\
     s' = ra_state_adj_ls_fupd (K (ra_state_adj_ls s')) s /\
     is_clique ls (ra_state_adj_ls s') /\
     is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ls:num list`; `s:ra_state`] clique_insert_edge_succeeds) THEN
  ASM_REWRITE_TAC[PAIR_EQ; injectivity "exc"] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:ra_state` STRIP_ASSUME_TAC) THEN
  RVEQ_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let RAPROOFAUX_mk_graph_props = prove
 (`!ct (ta:num->num) liveout s livein s'.
     mk_graph ta ct liveout s = (M_success livein,s') /\
     good_ra_state s /\
     (!x. in_clash_tree ct x ==> ta x < ra_state_dim s) /\
     INJ ta {x | in_clash_tree ct x} (count (LENGTH (ra_state_adj_ls s))) /\
     is_clique liveout (ra_state_adj_ls s) /\
     ALL_DISTINCT liveout /\
     ALL (\y. y < ra_state_dim s) liveout
     ==> good_ra_state s' /\
         is_clique livein (ra_state_adj_ls s') /\
         s' = ra_state_adj_ls_fupd (K (ra_state_adj_ls s')) s /\
         ALL (\y. y < ra_state_dim s) livein /\
         ALL_DISTINCT livein /\
         set_of_list livein SUBSET
           set_of_list liveout UNION IMAGE ta {x | in_clash_tree ct x} /\
         is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ct:clash_tree`; `ta:num->num`; `liveout:num list`; `s:ra_state`]
    mk_graph_succeeds) THEN
  ASM_REWRITE_TAC[PAIR_EQ; injectivity "exc"] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num list` (X_CHOOSE_THEN `t:ra_state` STRIP_ASSUME_TAC)) THEN
  RVEQ_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* RAPROOFAUX_mk_graph_check_P ct: the statement of mk_graph_check_clash_tree *)
(* for the clash tree ct (a term string), used for the cases of its induction *)
let RAPROOFAUX_mk_graph_check_P (ct:string) =
  "!(ta:num->num) livelist s livelist' s' (col:num->num) live flive.
     mk_graph ta ("^ct^") livelist s = (M_success livelist',s') /\\
     colouring_satisfactory col (ra_state_adj_ls s') /\\
     INJ ta ({x | in_clash_tree ("^ct^") x} UNION domain live)
       (count (LENGTH (ra_state_adj_ls s))) /\\
     IMAGE ta (domain live) = set_of_list livelist /\\
     ALL_DISTINCT livelist /\\
     ALL (\\y. y < ra_state_dim s) livelist /\\
     is_clique livelist (ra_state_adj_ls s) /\\
     good_ra_state s /\\
     domain flive = IMAGE (col o ta) (domain (live:1 spt)) ==>
     ?livein flivein.
       check_clash_tree (col o ta) ("^ct^") live flive = SOME (livein,flivein) /\\
       IMAGE ta (domain livein) = set_of_list livelist' /\\
       domain flivein = IMAGE (col o ta) (domain livein)";;

let RAPROOFAUX_mk_graph_check_Delta = prove
 (parse_term ("!w r. "^RAPROOFAUX_mk_graph_check_P "Delta w r"),
  REPEAT GEN_TAC THEN REWRITE_TAC[mk_graph_def; in_clash_tree_def; check_clash_tree_def;
    LET_DEF; LET_END_DEF] THEN
  SIMP RAPROOFAUX_msimps THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o REWRITE_RULE[reg_allocProof_case_eq_thms]) STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; injectivity "exc"; distinctness "exc"]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN TRY(FIRST_X_ASSUM CONTR_TAC) THEN
  SUBGOAL_THEN `!x. MEM x w \/ MEM x r ==> (ta:num->num) x < ra_state_dim s` ASSUME_TAC THENL
   [UNDISCH_TAC `INJ (ta:num->num) ({x | MEM x w \/ MEM x r} UNION domain (live:1 spt))
      (count (LENGTH (ra_state_adj_ls s)))` THEN
    SUBGOAL_THEN `LENGTH (ra_state_adj_ls s) = ra_state_dim s` SUBST1_TAC THENL
     [ASM_MESON_TAC[good_ra_state_def]; ALL_TAC] THEN
    REWRITE_TAC[INJ; IN_UNION; IN_ELIM_THM; IN_COUNT] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\y. y < ra_state_dim s) (MAP (ta:num->num) w) /\
                ALL (\y. y < ra_state_dim s) (MAP (ta:num->num) r)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`MAP (ta:num->num) w`; `livelist:num list`; `s:ra_state`; `a:num list`;
    `y:ra_state`] RAPROOFAUX_extend_clique_props) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  MP_TAC(SPECL [`MAP (ta:num->num) r`; `FILTER (\x. ~MEM x (MAP (ta:num->num) w)) a`;
    `y:ra_state`; `livelist':num list`; `s':ra_state`] RAPROOFAUX_extend_clique_props) THEN
  ASM_SIMP_TAC[is_clique_FILTER; FILTER_ALL_DISTINCT; EVERY_FILTER] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `set_of_list (a:num list) =
                 set_of_list (APPEND livelist (MAP (ta:num->num) w))` THEN
    UNDISCH_TAC `ALL (\y. y < ra_state_dim s) livelist` THEN
    UNDISCH_TAC `ALL (\y. y < ra_state_dim s) (MAP (ta:num->num) w)` THEN
    REWRITE_TAC[GSYM ALL_MEM; EXTENSION; IN_SET_OF_LIST; MEM_APPEND] THEN MESON_TAC[];
    STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  SUBGOAL_THEN `ALL (\y. y < ra_state_dim s) a /\ ALL (\y. y < ra_state_dim s) livelist'`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `set_of_list (livelist':num list) =
      set_of_list (APPEND (FILTER (\x. ~MEM x (MAP (ta:num->num) w)) a) (MAP ta r))` THEN
    UNDISCH_TAC `set_of_list (a:num list) =
                 set_of_list (APPEND livelist (MAP (ta:num->num) w))` THEN
    UNDISCH_TAC `ALL (\y. y < ra_state_dim s) livelist` THEN
    UNDISCH_TAC `ALL (\y. y < ra_state_dim s) (MAP (ta:num->num) w)` THEN
    UNDISCH_TAC `ALL (\y. y < ra_state_dim s) (MAP (ta:num->num) r)` THEN
    REWRITE_TAC[GSYM ALL_MEM; EXTENSION; IN_SET_OF_LIST; MEM_APPEND; MEM_FILTER] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (ra_state_adj_ls s') = ra_state_dim s` ASSUME_TAC THENL
   [ASM_MESON_TAC[good_ra_state_def]; ALL_TAC] THEN
  SUBGOAL_THEN `INJ (col:num->num) (set_of_list a) UNIV /\
                INJ col (set_of_list livelist') UNIV` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ALL_DISTINCT_set_INJ THEN
    MATCH_MP_TAC colouring_satisfactory_cliques THEN
    EXISTS_TAC `ra_state_adj_ls s'` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[is_clique_subgraph];
    ALL_TAC] THEN
  SUBGOAL_THEN `INJ (ta:num->num) (set_of_list w UNION set_of_list r UNION domain (live:1 spt))
                  (count (LENGTH (ra_state_adj_ls s)))` ASSUME_TAC THENL
   [MATCH_MP_TAC reg_allocProof_INJ_less THEN
    EXISTS_TAC `{x | MEM x w \/ MEM x r} UNION domain (live:1 spt)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_UNION; IN_SET_OF_LIST; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (ta:num->num) (set_of_list w UNION domain (live:1 spt)) = set_of_list a`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_UNION; GSYM LIST_TO_SET_MAP; LIST_TO_SET_APPEND] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (ta:num->num) (set_of_list r UNION (domain (live:1 spt) DIFF set_of_list w)) =
                set_of_list livelist'` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LIST_TO_SET_APPEND; set_FILTER; IMAGE_UNION; LIST_TO_SET_MAP] THEN
    UNDISCH_TAC `INJ (ta:num->num) (set_of_list w UNION set_of_list r UNION domain (live:1 spt))
                  (count (LENGTH (ra_state_adj_ls s)))` THEN
    UNDISCH_TAC `IMAGE (ta:num->num) (domain (live:1 spt)) = set_of_list livelist` THEN
    REWRITE_TAC[EXTENSION; INJ; IN_UNION; IN_DIFF; IN_IMAGE; IN_SET_OF_LIST; MEM_APPEND;
                MEM_MAP] THEN
    REWRITE_TAC[IN] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `INJ ((col:num->num) o (ta:num->num))
                  (set_of_list w UNION domain (live:1 spt)) UNIV` ASSUME_TAC THENL
   [MATCH_MP_TAC INJ_COMPOSE_IMAGE THEN
    EXISTS_TAC `count (LENGTH (ra_state_adj_ls s))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC reg_allocProof_INJ_less THEN
      EXISTS_TAC `set_of_list w UNION set_of_list r UNION domain (live:1 spt)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[ASSUME `IMAGE (ta:num->num) (set_of_list w UNION domain (live:1 spt)) =
                          set_of_list a`] THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`w:num list`; `live:1 spt`; `flive:1 spt`; `(col:num->num) o (ta:num->num)`]
    check_partial_col_success) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lw:1 spt` (X_CHOOSE_THEN `flw:1 spt` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[case_def "option"] THEN
  MP_TAC(SPECL [`r:num list`; `numset_list_delete w (live:1 spt)`;
    `numset_list_delete (MAP ((col:num->num) o (ta:num->num)) w) (flive:1 spt)`;
    `(col:num->num) o (ta:num->num)`] check_partial_col_success) THEN
  REWRITE_TAC[reg_allocProof_domain_numset_list_delete] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[LIST_TO_SET_MAP] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC reg_allocProof_IMAGE_DIFF THEN
      ONCE_REWRITE_TAC[UNION_COMM] THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC INJ_COMPOSE_IMAGE THEN
      EXISTS_TAC `count (LENGTH (ra_state_adj_ls s))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC reg_allocProof_INJ_less THEN
        EXISTS_TAC `set_of_list w UNION set_of_list r UNION domain (live:1 spt)` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        REWRITE_TAC[ASSUME `IMAGE (ta:num->num)
          (set_of_list r UNION (domain (live:1 spt) DIFF set_of_list w)) =
          set_of_list livelist'`] THEN
        FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `livein:1 spt` (X_CHOOSE_THEN `flivein:1 spt` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`livein:1 spt`; `flivein:1 spt`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP check_partial_col_domain) THEN
  REWRITE_TAC[FST; reg_allocProof_domain_numset_list_delete] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM(ASSUME `set_of_list (livelist':num list) =
      set_of_list (APPEND (FILTER (\x. ~MEM x (MAP (ta:num->num) w)) a) (MAP ta r))`)] THEN
  FIRST_ASSUM ACCEPT_TAC);;
let RAPROOFAUX_mk_graph_check_Set = prove
 (parse_term ("!t. "^RAPROOFAUX_mk_graph_check_P "reg_alloc_Set t"),
  REPEAT GEN_TAC THEN REWRITE_TAC[mk_graph_def; in_clash_tree_def; check_clash_tree_def;
    check_col_def; LET_DEF; LET_END_DEF] THEN
  SIMP RAPROOFAUX_msimps THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o REWRITE_RULE[reg_allocProof_case_eq_thms]) STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; injectivity "exc"; distinctness "exc"]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN TRY(FIRST_X_ASSUM CONTR_TAC) THEN
  SUBGOAL_THEN `LENGTH (ra_state_adj_ls s) = ra_state_dim s` ASSUME_TAC THENL
   [ASM_MESON_TAC[good_ra_state_def]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\y. y < ra_state_dim s) (MAP (ta:num->num) (MAP FST (toAList (t:1 spt))))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `INJ (ta:num->num) ({x | x IN domain (t:1 spt)} UNION domain (live:1 spt))
      (count (LENGTH (ra_state_adj_ls s)))` THEN
    ASM_REWRITE_TAC[INJ; IN_UNION; IN_ELIM_THM; IN_COUNT; GSYM ALL_MEM] THEN
    ONCE_REWRITE_TAC[MEM_MAP] THEN REWRITE_TAC[toAList_domain] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`MAP (ta:num->num) (MAP FST (toAList (t:1 spt)))`; `s:ra_state`; `a:1`;
    `s':ra_state`] RAPROOFAUX_clique_insert_edge_props) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP (ta:num->num) (MAP FST (toAList (t:1 spt))))` ASSUME_TAC THENL
   [MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList] THEN
    UNDISCH_TAC `INJ (ta:num->num) ({x | x IN domain (t:1 spt)} UNION domain (live:1 spt))
      (count (LENGTH (ra_state_adj_ls s)))` THEN
    REWRITE_TAC[INJ; IN_ELIM_THM; IN_UNION; toAList_domain] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM MAP_MAP_o] THEN MATCH_MP_TAC colouring_satisfactory_cliques THEN
    EXISTS_TAC `ra_state_adj_ls s'` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `LENGTH (ra_state_adj_ls s') = ra_state_dim s` SUBST1_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
      ASM_MESON_TAC[good_ra_state_def];
      FIRST_ASSUM ACCEPT_TAC];
    REWRITE_TAC[LIST_TO_SET_MAP; GSYM domain_eq_IMAGE];
    REWRITE_TAC[domain_fromAList; MAP_MAP_o; LIST_TO_SET_MAP; domain_eq_IMAGE;
                GSYM IMAGE_o] THEN
    REWRITE_TAC[o_DEF]]);;
let RAPROOFAUX_mk_graph_check_Branch_NONE = prove
 (parse_term ("!t1 t2. ("^RAPROOFAUX_mk_graph_check_P "t1"^") /\\ ("^
    RAPROOFAUX_mk_graph_check_P "t2"^") ==> "^
    RAPROOFAUX_mk_graph_check_P "reg_alloc_Branch NONE t1 t2"),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[mk_graph_def; in_clash_tree_def; check_clash_tree_def;
    case_def "option"] THEN
  SIMP RAPROOFAUX_msimps THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o REWRITE_RULE[reg_allocProof_case_eq_thms]) STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; injectivity "exc"; distinctness "exc"]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN TRY(FIRST_X_ASSUM CONTR_TAC) THEN
  SUBGOAL_THEN `!x. in_clash_tree t1 x \/ in_clash_tree t2 x ==> (ta:num->num) x < ra_state_dim s`
  ASSUME_TAC THENL
   [UNDISCH_TAC `INJ (ta:num->num) ({x | in_clash_tree t1 x \/ in_clash_tree t2 x} UNION
      domain (live:1 spt)) (count (LENGTH (ra_state_adj_ls s)))` THEN
    REWRITE_TAC[CONJUNCT1(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`))] THEN
    REWRITE_TAC[INJ; IN_UNION; IN_ELIM_THM; IN_COUNT] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`t1:clash_tree`; `ta:num->num`; `livelist:num list`; `s:ra_state`;
    `a:num list`; `y:ra_state`] RAPROOFAUX_mk_graph_props) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC reg_allocProof_INJ_less THEN
    EXISTS_TAC `{x | in_clash_tree t1 x \/ in_clash_tree t2 x} UNION domain (live:1 spt)` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  SUBGOAL_THEN `LENGTH (ra_state_adj_ls y) = LENGTH (ra_state_adj_ls s)` ASSUME_TAC THENL
   [REWRITE_TAC[CONJUNCT1(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`));
                CONJUNCT1(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state y`))] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`t2:clash_tree`; `ta:num->num`; `livelist:num list`; `y:ra_state`;
    `a':num list`; `y':ra_state`] RAPROOFAUX_mk_graph_props) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MATCH_MP_TAC reg_allocProof_INJ_less THEN
      EXISTS_TAC `{x | in_clash_tree t1 x \/ in_clash_tree t2 x} UNION domain (live:1 spt)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC is_clique_subgraph THEN EXISTS_TAC `ra_state_adj_ls s` THEN
      ASM_REWRITE_TAC[]];
    STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  MP_TAC(SPECL [`a:num list`; `a':num list`; `y':ra_state`; `livelist':num list`;
    `s':ra_state`] RAPROOFAUX_extend_clique_props) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  SUBGOAL_THEN `is_subgraph (ra_state_adj_ls y) (ra_state_adj_ls s')` ASSUME_TAC THENL
   [ASM_MESON_TAC[is_subgraph_trans]; ALL_TAC] THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`ta:num->num`; `livelist:num list`; `s:ra_state`;
    `a:num list`; `y:ra_state`; `col:num->num`; `live:1 spt`; `flive:1 spt`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC colouring_satisfactory_subgraph THEN
      EXISTS_TAC `ra_state_adj_ls s'` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC reg_allocProof_INJ_less THEN
      EXISTS_TAC `{x | in_clash_tree t1 x \/ in_clash_tree t2 x} UNION domain (live:1 spt)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:1 spt` (X_CHOOSE_THEN `fl1:1 spt` STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "ih2" (MP_TAC o SPECL [`ta:num->num`; `livelist:num list`; `y:ra_state`;
    `a':num list`; `y':ra_state`; `col:num->num`; `live:1 spt`; `flive:1 spt`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC colouring_satisfactory_subgraph THEN
      EXISTS_TAC `ra_state_adj_ls s'` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC reg_allocProof_INJ_less THEN
      EXISTS_TAC `{x | in_clash_tree t1 x \/ in_clash_tree t2 x} UNION domain (live:1 spt)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC is_clique_subgraph THEN EXISTS_TAC `ra_state_adj_ls s` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l2:1 spt` (X_CHOOSE_THEN `fl2:1 spt` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[case_def "option"; case_def "prod"] THEN
  SUBGOAL_THEN `set_of_list (MAP FST (toAList (difference (l2:1 spt) (l1:1 spt)))) UNION domain l1 =
                domain l2 UNION domain l1` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_SET_OF_LIST; toAList_domain; domain_difference;
                IN_DIFF] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (ta:num->num) (domain (l2:1 spt) UNION domain (l1:1 spt)) =
                set_of_list (APPEND a' a)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_UNION; LIST_TO_SET_APPEND]; ALL_TAC] THEN
  SUBGOAL_THEN `INJ (col:num->num) (set_of_list (APPEND a' a)) UNIV` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `set_of_list (livelist':num list) = set_of_list (APPEND a' a)`)] THEN
    MATCH_MP_TAC ALL_DISTINCT_set_INJ THEN
    MATCH_MP_TAC colouring_satisfactory_cliques THEN
    EXISTS_TAC `ra_state_adj_ls s'` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONJUNCT1(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s'`))] THEN
    UNDISCH_TAC `set_of_list (livelist':num list) = set_of_list (APPEND a' a)` THEN
    UNDISCH_TAC `ALL (\y. y < ra_state_dim s) a` THEN
    UNDISCH_TAC `ALL (\y. y < ra_state_dim s) a'` THEN
    ASM_REWRITE_TAC[GSYM ALL_MEM; EXTENSION; IN_SET_OF_LIST; MEM_APPEND] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `INJ (ta:num->num) (domain (l2:1 spt) UNION domain (l1:1 spt))
                  (count (LENGTH (ra_state_adj_ls s)))` ASSUME_TAC THENL
   [MATCH_MP_TAC reg_allocProof_INJ_less THEN
    EXISTS_TAC `{x | in_clash_tree t1 x \/ in_clash_tree t2 x} UNION domain (live:1 spt)` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP check_clash_tree_domain o check (fun th ->
      concl th = `check_clash_tree ((col:num->num) o (ta:num->num)) t1 live flive =
                  SOME (l1,fl1)`)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP check_clash_tree_domain o check (fun th ->
      concl th = `check_clash_tree ((col:num->num) o (ta:num->num)) t2 live flive =
                  SOME (l2,fl2)`)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`MAP FST (toAList (difference (l2:1 spt) (l1:1 spt)))`; `l1:1 spt`; `fl1:1 spt`;
    `(col:num->num) o (ta:num->num)`] check_partial_col_success) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INJ_COMPOSE_IMAGE THEN
    EXISTS_TAC `count (LENGTH (ra_state_adj_ls s))` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `livein:1 spt` (X_CHOOSE_THEN `flivein:1 spt` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`livein:1 spt`; `flivein:1 spt`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP check_partial_col_domain) THEN
  ASM_REWRITE_TAC[FST] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;
let RAPROOFAUX_mk_graph_check_Branch_SOME = prove
 (parse_term ("!t t1 t2. ("^RAPROOFAUX_mk_graph_check_P "t1"^") /\\ ("^
    RAPROOFAUX_mk_graph_check_P "t2"^") ==> "^
    RAPROOFAUX_mk_graph_check_P "reg_alloc_Branch (SOME t) t1 t2"),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[mk_graph_def; in_clash_tree_def; check_clash_tree_def;
    case_def "option"; check_col_def; LET_DEF; LET_END_DEF] THEN
  SIMP RAPROOFAUX_msimps THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o REWRITE_RULE[reg_allocProof_case_eq_thms]) STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; injectivity "exc"; distinctness "exc"]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN TRY(FIRST_X_ASSUM CONTR_TAC) THEN
  SUBGOAL_THEN `!x. in_clash_tree t1 x \/ in_clash_tree t2 x ==> (ta:num->num) x < ra_state_dim s`
  ASSUME_TAC THENL
   [UNDISCH_TAC `INJ (ta:num->num)
      ({x | in_clash_tree t1 x \/ in_clash_tree t2 x \/ x IN domain (t:1 spt)} UNION
      domain (live:1 spt)) (count (LENGTH (ra_state_adj_ls s)))` THEN
    REWRITE_TAC[CONJUNCT1(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`))] THEN
    REWRITE_TAC[INJ; IN_UNION; IN_ELIM_THM; IN_COUNT] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`t1:clash_tree`; `ta:num->num`; `livelist:num list`; `s:ra_state`;
    `a:num list`; `y:ra_state`] RAPROOFAUX_mk_graph_props) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC reg_allocProof_INJ_less THEN
    EXISTS_TAC `{x | in_clash_tree t1 x \/ in_clash_tree t2 x \/ x IN domain (t:1 spt)} UNION
                domain (live:1 spt)` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  SUBGOAL_THEN `LENGTH (ra_state_adj_ls y) = LENGTH (ra_state_adj_ls s)` ASSUME_TAC THENL
   [REWRITE_TAC[CONJUNCT1(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`));
                CONJUNCT1(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state y`))] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`t2:clash_tree`; `ta:num->num`; `livelist:num list`; `y:ra_state`;
    `a':num list`; `y':ra_state`] RAPROOFAUX_mk_graph_props) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MATCH_MP_TAC reg_allocProof_INJ_less THEN
      EXISTS_TAC `{x | in_clash_tree t1 x \/ in_clash_tree t2 x \/ x IN domain (t:1 spt)} UNION
                domain (live:1 spt)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC is_clique_subgraph THEN EXISTS_TAC `ra_state_adj_ls s` THEN
      ASM_REWRITE_TAC[]];
    STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  SUBGOAL_THEN `ALL (\y. y < ra_state_dim s) (MAP (ta:num->num) (MAP FST (toAList (t:1 spt))))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `INJ (ta:num->num) ({x | in_clash_tree t1 x \/ in_clash_tree t2 x \/
      x IN domain (t:1 spt)} UNION domain (live:1 spt)) (count (LENGTH (ra_state_adj_ls s)))` THEN
    REWRITE_TAC[CONJUNCT1(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`))] THEN
    REWRITE_TAC[INJ; IN_UNION; IN_ELIM_THM; IN_COUNT; GSYM ALL_MEM] THEN
    ONCE_REWRITE_TAC[MEM_MAP] THEN REWRITE_TAC[toAList_domain] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`MAP (ta:num->num) (MAP FST (toAList (t:1 spt)))`; `y':ra_state`; `a'':1`;
    `s':ra_state`] RAPROOFAUX_clique_insert_edge_props) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  SUBGOAL_THEN `is_subgraph (ra_state_adj_ls y) (ra_state_adj_ls s')` ASSUME_TAC THENL
   [ASM_MESON_TAC[is_subgraph_trans]; ALL_TAC] THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`ta:num->num`; `livelist:num list`; `s:ra_state`;
    `a:num list`; `y:ra_state`; `col:num->num`; `live:1 spt`; `flive:1 spt`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC colouring_satisfactory_subgraph THEN
      EXISTS_TAC `ra_state_adj_ls s'` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC reg_allocProof_INJ_less THEN
      EXISTS_TAC `{x | in_clash_tree t1 x \/ in_clash_tree t2 x \/ x IN domain (t:1 spt)} UNION
                domain (live:1 spt)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:1 spt` (X_CHOOSE_THEN `fl1:1 spt` STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "ih2" (MP_TAC o SPECL [`ta:num->num`; `livelist:num list`; `y:ra_state`;
    `a':num list`; `y':ra_state`; `col:num->num`; `live:1 spt`; `flive:1 spt`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC colouring_satisfactory_subgraph THEN
      EXISTS_TAC `ra_state_adj_ls s'` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC reg_allocProof_INJ_less THEN
      EXISTS_TAC `{x | in_clash_tree t1 x \/ in_clash_tree t2 x \/ x IN domain (t:1 spt)} UNION
                domain (live:1 spt)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC is_clique_subgraph THEN EXISTS_TAC `ra_state_adj_ls s` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l2:1 spt` (X_CHOOSE_THEN `fl2:1 spt` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[case_def "option"; case_def "prod"] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP (ta:num->num) (MAP FST (toAList (t:1 spt))))` ASSUME_TAC THENL
   [MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList] THEN
    UNDISCH_TAC `INJ (ta:num->num) ({x | in_clash_tree t1 x \/ in_clash_tree t2 x \/
      x IN domain (t:1 spt)} UNION domain (live:1 spt)) (count (LENGTH (ra_state_adj_ls s)))` THEN
    REWRITE_TAC[INJ; IN_ELIM_THM; IN_UNION; toAList_domain] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP ((col:num->num) o (ta:num->num) o FST) (toAList (t:1 spt)))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM MAP_MAP_o] THEN MATCH_MP_TAC colouring_satisfactory_cliques THEN
    EXISTS_TAC `ra_state_adj_ls s'` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONJUNCT1(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s'`))] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`t:1 spt`; `fromAList (MAP (\x. x,one)
    (MAP ((col:num->num) o (ta:num->num) o FST) (toAList (t:1 spt))))`] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[LIST_TO_SET_MAP; GSYM domain_eq_IMAGE];
    REWRITE_TAC[domain_fromAList; MAP_MAP_o; LIST_TO_SET_MAP; domain_eq_IMAGE;
                GSYM IMAGE_o] THEN
    REWRITE_TAC[o_DEF]]);;
let RAPROOFAUX_mk_graph_check_Seq = prove
 (parse_term ("!t1 t2. ("^RAPROOFAUX_mk_graph_check_P "t1"^") /\\ ("^
    RAPROOFAUX_mk_graph_check_P "t2"^") ==> "^
    RAPROOFAUX_mk_graph_check_P "reg_alloc_Seq t1 t2"),
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[mk_graph_def; in_clash_tree_def; check_clash_tree_def] THEN
  SIMP RAPROOFAUX_msimps THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o REWRITE_RULE[reg_allocProof_case_eq_thms]) STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ; injectivity "exc"; distinctness "exc"]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  RVEQ_TAC THEN TRY(FIRST_X_ASSUM CONTR_TAC) THEN
  SUBGOAL_THEN `!x. in_clash_tree t1 x \/ in_clash_tree t2 x ==> (ta:num->num) x < ra_state_dim s`
  ASSUME_TAC THENL
   [UNDISCH_TAC `INJ (ta:num->num) ({x | in_clash_tree t1 x \/ in_clash_tree t2 x} UNION
      domain (live:1 spt)) (count (LENGTH (ra_state_adj_ls s)))` THEN
    REWRITE_TAC[CONJUNCT1(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`))] THEN
    REWRITE_TAC[INJ; IN_UNION; IN_ELIM_THM; IN_COUNT] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`t2:clash_tree`; `ta:num->num`; `livelist:num list`; `s:ra_state`;
    `a:num list`; `y:ra_state`] RAPROOFAUX_mk_graph_props) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC reg_allocProof_INJ_less THEN
    EXISTS_TAC `{x | in_clash_tree t1 x \/ in_clash_tree t2 x} UNION domain (live:1 spt)` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  SUBGOAL_THEN `LENGTH (ra_state_adj_ls y) = LENGTH (ra_state_adj_ls s)` ASSUME_TAC THENL
   [REWRITE_TAC[CONJUNCT1(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`));
                CONJUNCT1(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state y`))] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`t1:clash_tree`; `ta:num->num`; `a:num list`; `y:ra_state`;
    `livelist':num list`; `s':ra_state`] RAPROOFAUX_mk_graph_props) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MATCH_MP_TAC reg_allocProof_INJ_less THEN
      EXISTS_TAC `{x | in_clash_tree t1 x \/ in_clash_tree t2 x} UNION domain (live:1 spt)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  REMOVE_THEN "ih2" (MP_TAC o SPECL [`ta:num->num`; `livelist:num list`; `s:ra_state`;
    `a:num list`; `y:ra_state`; `col:num->num`; `live:1 spt`; `flive:1 spt`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC colouring_satisfactory_subgraph THEN
      EXISTS_TAC `ra_state_adj_ls s'` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC reg_allocProof_INJ_less THEN
      EXISTS_TAC `{x | in_clash_tree t1 x \/ in_clash_tree t2 x} UNION domain (live:1 spt)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l2:1 spt` (X_CHOOSE_THEN `fl2:1 spt` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[case_def "option"; case_def "prod"] THEN
  REMOVE_THEN "ih1" (MP_TAC o SPECL [`ta:num->num`; `a:num list`; `y:ra_state`;
    `livelist':num list`; `s':ra_state`; `col:num->num`; `l2:1 spt`; `fl2:1 spt`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC reg_allocProof_INJ_less THEN
    EXISTS_TAC `{x | in_clash_tree t1 x \/ in_clash_tree t2 x} UNION domain (live:1 spt)` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP check_clash_tree_domain o check (fun th ->
      concl th = `check_clash_tree ((col:num->num) o (ta:num->num)) t2 live flive =
                  SOME (l2,fl2)`)) THEN
    SET_TAC[];
    REWRITE_TAC[]]);;

(* the correctness theorem for mk_graph *)
let mk_graph_check_clash_tree = prove
 (`!ct (ta:num->num) livelist s livelist' s' (col:num->num) live flive.
     mk_graph ta ct livelist s = (M_success livelist',s') /\
     colouring_satisfactory col (ra_state_adj_ls s') /\
     INJ ta ({x | in_clash_tree ct x} UNION domain live)
       (count (LENGTH (ra_state_adj_ls s))) /\
     IMAGE ta (domain live) = set_of_list livelist /\
     ALL_DISTINCT livelist /\
     ALL (\y. y < ra_state_dim s) livelist /\
     is_clique livelist (ra_state_adj_ls s) /\
     good_ra_state s /\
     domain flive = IMAGE (col o ta) (domain (live:1 spt)) ==>
     ?livein flivein.
       check_clash_tree (col o ta) ct live flive = SOME (livein,flivein) /\
       IMAGE ta (domain livein) = set_of_list livelist' /\
       domain flivein = IMAGE (col o ta) (domain livein)`,
  MATCH_MP_TAC clash_tree_INDUCT THEN
  REWRITE_TAC[RAPROOFAUX_mk_graph_check_Delta; RAPROOFAUX_mk_graph_check_Set;
              RAPROOFAUX_mk_graph_check_Seq] THEN
  X_GEN_TAC `topt:(1 spt)option` THEN
  STRUCT_CASES_TAC(ISPEC `topt:(1 spt)option` (cases "option")) THEN
  REWRITE_TAC[RAPROOFAUX_mk_graph_check_Branch_NONE; RAPROOFAUX_mk_graph_check_Branch_SOME]);;

(* This precise characterization is needed to show that the forced edges
   correctly force any two to be distinct *)
let extend_graph_succeeds = prove
 (CASE_TERM `!(forced:(num#num)list) (f:num->num) s.
     good_ra_state s /\
     ALL (\p. match p with (x,y) -> f x < ra_state_dim s /\ f y < ra_state_dim s) forced ==>
     ?s'. extend_graph f forced s = (M_success one,s') /\
          good_ra_state s' /\
          s' = ra_state_adj_ls_fupd (K (ra_state_adj_ls s')) s /\
          !a b. has_edge (ra_state_adj_ls s') a b <=>
                (?x y. f x = a /\ f y = b /\ MEM (y,x) forced) \/
                (?x y. f x = a /\ f y = b /\ MEM (x,y) forced) \/
                has_edge (ra_state_adj_ls s) a b`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[extend_graph_def; st_ex_return_def; MEM] THEN
    SIMP[] THEN SIMP[ra_state_component_equality];
    ALL_TAC] THEN
  MP_TAC(ISPEC `h:num#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `q:num` SUBST1_TAC)) THEN
  REWRITE_TAC[ALL; extend_graph_def] THEN SIMP[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:ra_state`; `(f:num->num) p`; `(f:num->num) q`] insert_edge_succeeds) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:ra_state` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_ignore_bind_ok th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`f:num->num`; `s1:ra_state`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:ra_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s2:ra_state` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  ASM_REWRITE_TAC[RAPROOFAUX_frame_adj_ls; MEM; PAIR_EQ] THEN MESON_TAC[]);;

(* RAPROOFAUX_var_conv: the three kinds of variables, by their remainder mod 4 *)
let RAPROOFAUX_var_conv = prove
 (`!v. (v MOD 4 = 1 ==> ~is_phy_var v /\ ~is_stack_var v) /\
       (v MOD 4 = 3 ==> ~is_phy_var v /\ is_stack_var v) /\
       (~(v MOD 4 = 1) /\ ~(v MOD 4 = 3) ==> is_phy_var v)`,
  GEN_TAC THEN REWRITE_TAC[is_stack_var_def] THEN
  MP_TAC(SPEC `v:num` convention_partitions) THEN
  REWRITE_TAC[is_stack_var_def; is_alloc_var_def] THEN MESON_TAC[]);;

(* Again, this characterization is only needed for the conventions,
   but not for the correctness theorem *)
let mk_tags_st_ex_FOREACH_lem = prove
 (CASE_TERM `!ls s (fa:num->num) (fs:1 spt).
     good_ra_state s /\ ALL (\v. v < ra_state_dim s) ls ==>
     ?s'. st_ex_FOREACH ls
            (\i. if fa i MOD 4 = 1 then
                   (match lookup (fa i) fs with
                      NONE -> update_node_tag i Atemp
                    | SOME (_:1) -> update_node_tag i Stemp)
                 else if fa i MOD 4 = 3 then update_node_tag i Stemp
                 else update_node_tag i (Fixed (fa i DIV 2))) s = (M_success one,s') /\
          good_ra_state s' /\
          s' = ra_state_node_tag_fupd (K (ra_state_node_tag s')) s /\
          (!x. x < ra_state_dim s ==>
               if MEM x ls then
                 (if is_phy_var (fa x) then EL x (ra_state_node_tag s') = Fixed (fa x DIV 2)
                  else if is_stack_var (fa x) then EL x (ra_state_node_tag s') = Stemp
                  else EL x (ra_state_node_tag s') = Atemp \/
                       EL x (ra_state_node_tag s') = Stemp)
               else EL x (ra_state_node_tag s') = EL x (ra_state_node_tag s))`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[st_ex_FOREACH_def; st_ex_return_def; MEM] THEN
    SIMP[] THEN SIMP[ra_state_component_equality];
    ALL_TAC] THEN
  REWRITE_TAC[ALL; MEM; st_ex_FOREACH_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN (CASE_TERM `?tg. (if fa h MOD 4 = 1 then
                   (match lookup (fa h) fs with
                      NONE -> update_node_tag h Atemp
                    | SOME (_:1) -> update_node_tag h Stemp)
                 else if fa h MOD 4 = 3 then update_node_tag h Stemp
                 else update_node_tag h (Fixed (fa h DIV 2))) = update_node_tag h tg /\
              (if is_phy_var (fa h) then tg = Fixed (fa h DIV 2)
               else if is_stack_var (fa h) then tg = Stemp
               else tg = Atemp \/ tg = Stemp)`) STRIP_ASSUME_TAC THENL
  [
   MP_TAC(SPEC `(fa:num->num) h` RAPROOFAUX_var_conv) THEN
  ASM_CASES_TAC `(fa:num->num) h MOD 4 = 1` THEN ASM_REWRITE_TAC[] THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CASES_ON `lookup ((fa:num->num) h) (fs:1 spt)` THEN
    REWRITE_TAC[case_def "option"] THEN MESON_TAC[];
    ASM_CASES_TAC `(fa:num->num) h MOD 4 = 3` THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]];
   FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_cond(lhs(concl th))
                           then REWRITE_TAC[th] else failwith "no") THEN
  SUBGOAL_THEN `h < LENGTH (ra_state_node_tag s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RAPROOFAUX_good_lengths]; ALL_TAC] THEN
  SIMP RAPROOFAUX_msimps THEN
   FIRST_X_ASSUM(MP_TAC o SPECL
    [`ra_state_node_tag_fupd (K (LUPDATE tg h (ra_state_node_tag s))) s`;
     `fa:num->num`; `fs:1 spt`]) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `good_ra_state s` THEN SIMP[good_ra_state_def; LENGTH_LUPDATE] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:ra_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s2:ra_state` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_node_tag]) THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE []) THEN
  ASM_REWRITE_TAC[RAPROOFAUX_frame_node_tag] THEN
   X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[EL_LUPDATE] THEN
  ASM_CASES_TAC `MEM (x:num) t` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `x:num = h` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `x:num = h`)) THEN
  ASM_REWRITE_TAC[]]);;
let mk_tags_succeeds = prove
 (`!s n (fs:1 spt) (fa:num->num).
     good_ra_state s /\ n = ra_state_dim s ==>
     ?s'. mk_tags n fs fa s = (M_success one,s') /\
          good_ra_state s' /\
          s' = ra_state_node_tag_fupd (K (ra_state_node_tag s')) s /\
          !x y. x < n /\ y = fa x ==>
                if is_phy_var y then EL x (ra_state_node_tag s') = Fixed (y DIV 2)
                else if is_stack_var y then EL x (ra_state_node_tag s') = Stemp
                else EL x (ra_state_node_tag s') = Atemp \/
                     EL x (ra_state_node_tag s') = Stemp`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mk_tags_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC RAPROOFAUX_msimps THEN REWRITE_TAC[case_def "prod"; case_def "exc"] THEN
  MP_TAC(SPECL [`list_of_seq (\x:num. x) n`; `s:ra_state`; `fa:num->num`; `fs:1 spt`]
    mk_tags_st_ex_FOREACH_lem) THEN
  ASM_REWRITE_TAC[EVERY_GENLIST] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:ra_state` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s1:ra_state` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_node_tag]) THEN
  ASM_REWRITE_TAC[RAPROOFAUX_frame_node_tag] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `MEM (x:num) (list_of_seq (\x. x) (ra_state_dim s))`
    (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[MEM_GENLIST] THEN ASM_MESON_TAC[]);;

(* copied from word-to-stack proof*)
(* HOL4: TWOxDIV2; the HOL4 statement parses as (2 times x) DIV 2 = x *)
let reg_allocProof_TWOxDIV2 = prove
 (`!x. (2 * x) DIV 2 = x`,
  GEN_TAC THEN MATCH_MP_TAC DIV_MULT THEN ARITH_TAC);;


let RAPROOFAUX_bind_return_left = prove
 (`!(x:A) (f:A->S->(B,E)exc#S). st_ex_bind (st_ex_return x) f = f x`,
  REWRITE_TAC[FUN_EQ_THM] THEN SIMP RAPROOFAUX_msimps);;

let extract_color_st_ex_MAP_lem = prove
 (CASE_TERM `!ls s.
     ALL (\kv. match kv with (k:num,v) -> v < LENGTH (ra_state_node_tag s)) ls ==>
     st_ex_MAP (\kv. match kv with
                       (k,v) -> st_ex_bind (node_tag_sub v)
                                  (\t. st_ex_return (k,extract_tag t))) ls s =
     (M_success (MAP (\kv. match kv with
                             (k,v) -> (k,extract_tag (EL v (ra_state_node_tag s)))) ls),s)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[st_ex_MAP_def; ALL; MAP] THENL
   [REWRITE_TAC[st_ex_return_def]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `h:num#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `q:num` SUBST1_TAC)) THEN
  REWRITE_TAC[case_def "prod"] THEN STRIP_TAC THEN
  FS RAPROOFAUX_msimps);;

let extract_color_succeeds = prove
 (`!s (ta:num spt).
     good_ra_state s /\
     (!x y. lookup x ta = SOME y ==> y < ra_state_dim s) /\
     wf ta ==>
     extract_color ta s =
     (M_success (map (\v. extract_tag (EL v (ra_state_node_tag s))) ta),s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[extract_color_def; RAPROOFAUX_bind_return_left] THEN
  MP_TAC(SPECL [`toAList (ta:num spt)`; `s:ra_state`] extract_color_st_ex_MAP_lem) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; case_def "prod"; MEM_toAList] THEN
    REWRITE_TAC[CONJUNCT1(CONJUNCT2(MATCH_MP RAPROOFAUX_good_lengths
      (ASSUME `good_ra_state s`)))] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_bind_ok th]) THEN
  REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [GSYM(MATCH_MP fromAList_toAList th)]) THEN
  REWRITE_TAC[map_fromAList] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; case_def "prod"]);;

(* Here are the proofs about the "heuristic steps" *)

(* st_ex_PARTITION is similar to st_ex_MAP in that there ought to be
   some generic way to state the following lemmas
*)

(* is_not_coalesced succeeds and preserves state *)
let is_not_coalesced_succeeds = prove
 (`!s n. good_ra_state s /\ n < ra_state_dim s ==>
         ?b. is_not_coalesced n s = (M_success b,s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[is_not_coalesced_def] THEN
  SIMP(RAPROOFAUX_good_lengths :: RAPROOFAUX_msimps));;
(* RAPROOFAUX_split_degree_ok: split_degree reads the state only *)
let RAPROOFAUX_split_degree_ok = prove
 (`!s k h. good_ra_state s ==> ?b. split_degree (ra_state_dim s) k h s = (M_success b,s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[split_degree_def; is_not_coalesced_def] THEN
  COND_CASES_TAC THEN SIMP(RAPROOFAUX_good_lengths :: RAPROOFAUX_msimps) THEN MESON_TAC[]);;

(* As an example, we don't bother fully characterizing
   st_ex_PARTITION, but merely that show it succeeds *)
let st_ex_PARTITION_split_degree = prove
 (`!atemps k lss lss' s.
     good_ra_state s ==>
     ?ts fs. st_ex_PARTITION (split_degree (ra_state_dim s) k) atemps lss lss' s =
               (M_success (ts,fs),s) /\
             ALL (\x. MEM x lss \/ MEM x atemps) ts /\
             ALL (\x. MEM x lss' \/ MEM x atemps) fs`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[st_ex_PARTITION_def; st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
    REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`lss:num list`; `lss':num list`] THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[st_ex_PARTITION_def] THEN
  MP_TAC(SPECL [`s:ra_state`; `k:num`; `h:num`] RAPROOFAUX_split_degree_ok) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `b:bool`) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_bind_ok th]) THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `CONS (h:num) lss`; `lss':num list`; `s:ra_state`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `lss:num list`; `CONS (h:num) lss'`; `s:ra_state`])] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM] THEN MESON_TAC[]);;

let st_ex_PARTITION_move_related_sub = prove
 (`!atemps lss lss' s.
     ALL (\x. x < LENGTH (ra_state_move_related s)) atemps ==>
     ?ts fs. st_ex_PARTITION move_related_sub atemps lss lss' s =
               (M_success (ts,fs),s) /\
             ALL (\x. MEM x lss \/ MEM x atemps) ts /\
             ALL (\x. MEM x lss' \/ MEM x atemps) fs`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[st_ex_PARTITION_def; st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
    REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`lss:num list`; `lss':num list`] THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ALL] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[st_ex_PARTITION_def] THEN
  SUBGOAL_THEN `move_related_sub h s = (M_success (EL h (ra_state_move_related s)),s)`
  (fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_bind_ok th]) THENL
   [ASM_REWRITE_TAC[move_related_sub]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (h:num) lss`; `lss':num list`; `s:ra_state`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`lss:num list`; `CONS (h:num) lss'`; `s:ra_state`])] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM] THEN MESON_TAC[]);;
(* RAPROOFAUX_good_..._fupd: good_ra_state after an update of one field *)
let RAPROOFAUX_good_degrees_fupd = prove
 (`!s d. good_ra_state s /\ LENGTH d = LENGTH (ra_state_degrees s) ==>
         good_ra_state (ra_state_degrees_fupd (K d) s)`,
  REWRITE_TAC[good_ra_state_def] THEN SIMP[]);;

let RAPROOFAUX_good_move_related_fupd = prove
 (`!s d. good_ra_state s /\ LENGTH d = LENGTH (ra_state_move_related s) ==>
         good_ra_state (ra_state_move_related_fupd (K d) s)`,
  REWRITE_TAC[good_ra_state_def] THEN SIMP[]);;

let RAPROOFAUX_good_stack_fupd = prove
 (`!s d. good_ra_state s ==> good_ra_state (ra_state_stack_fupd (K d) s)`,
  REWRITE_TAC[good_ra_state_def] THEN SIMP[]);;

(* This is currently more general than necessary because it doesn't
   do any coalescing (yet) *)
let dec_deg_success = prove
 (`!ls s. ALL (\v. v < ra_state_dim s) ls /\ good_ra_state s ==>
          ?d. st_ex_FOREACH ls dec_deg s = (M_success one,ra_state_degrees_fupd (K d) s) /\
              LENGTH d = LENGTH (ra_state_degrees s)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[st_ex_FOREACH_def; st_ex_return_def] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `ra_state_degrees s` THEN SIMP[ra_state_component_equality];
    ALL_TAC] THEN
  REWRITE_TAC[ALL; st_ex_FOREACH_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `h < LENGTH (ra_state_degrees s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RAPROOFAUX_good_lengths]; ALL_TAC] THEN
  SUBGOAL_THEN `dec_deg h s = (M_success one,
     ra_state_degrees_fupd (K (LUPDATE (EL h (ra_state_degrees s) - 1) h
       (ra_state_degrees s))) s)` (fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_ignore_bind_ok th])
  THENL [REWRITE_TAC[dec_deg_def] THEN SIMP RAPROOFAUX_msimps; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ra_state_degrees_fupd (K (LUPDATE (EL h (ra_state_degrees s) - 1) h
       (ra_state_degrees s))) s`) THEN
  ANTS_TAC THENL
   [SIMP[] THEN MATCH_MP_TAC RAPROOFAUX_good_degrees_fupd THEN
    ASM_REWRITE_TAC[LENGTH_LUPDATE];
    ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `d:num list` THEN ASM_REWRITE_TAC[] THEN
  SIMP[LENGTH_LUPDATE] THEN SIMP[ra_state_component_equality]);;
let dec_degree_success = prove
 (`!ls s. good_ra_state s ==>
          ?d. st_ex_FOREACH ls dec_degree s =
                (M_success one,ra_state_degrees_fupd (K d) s) /\
              LENGTH d = LENGTH (ra_state_degrees s)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[st_ex_FOREACH_def; st_ex_return_def] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `ra_state_degrees s` THEN SIMP[ra_state_component_equality];
    ALL_TAC] THEN
  REWRITE_TAC[st_ex_FOREACH_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?d. dec_degree h s = (M_success one,ra_state_degrees_fupd (K d) s) /\
                    LENGTH d = LENGTH (ra_state_degrees s)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[dec_degree_def; get_dim_def] THEN SIMP RAPROOFAUX_msimps THEN
    COND_CASES_TAC THENL
     [ALL_TAC;
      SIMP[] THEN EXISTS_TAC `ra_state_degrees s` THEN SIMP[ra_state_component_equality]] THEN
    SUBGOAL_THEN `h < LENGTH (ra_state_adj_ls s)` ASSUME_TAC THENL
     [ASM_MESON_TAC[RAPROOFAUX_good_lengths]; ALL_TAC] THEN
    SIMP[] THEN MATCH_MP_TAC dec_deg_success THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `good_ra_state s` THEN REWRITE_TAC[good_ra_state_def; GSYM ALL_EL] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_ignore_bind_ok th]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ra_state_degrees_fupd (K d) s`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC RAPROOFAUX_good_degrees_fupd THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:num list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d2:num list` THEN ASM_REWRITE_TAC[] THEN
  SIMP[] THEN SIMP[ra_state_component_equality]);;

let MEM_smerge = prove
 (`!xs ys (x:num#A). MEM x (smerge xs ys) <=> MEM x xs \/ MEM x ys`,
  MATCH_MP_TAC smerge_ind THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[smerge_def; MEM] THEN STRIP_TAC THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[MEM] THEN MESON_TAC[]);;
let RAPROOFAUX_frame_moves = RAPROOFAUX_frame ["avail_moves_wl"; "unavail_moves_wl"];;

(* RAPROOFAUX_PAIR_TAC p a b: name the components of the first pair subterm *)
(* of the goal that satisfies p                                             *)
let RAPROOFAUX_PAIR_TAC (p:term->bool) (a:term) (b:term) : tactic =
  fun (asl,w as g) ->
    let tm = find_term p w in
    (MP_TAC(ISPEC tm PAIR_SURJECTIVE) THEN
     DISCH_THEN(X_CHOOSE_THEN a (X_CHOOSE_THEN b ASSUME_TAC))) g;;
let revive_moves_success = prove
 (`!ls s.
     ALL (\x. x < LENGTH (ra_state_adj_ls s)) ls ==>
     ?s'. revive_moves ls s = (M_success one,s') /\
          s' = ra_state_avail_moves_wl_fupd (K (ra_state_avail_moves_wl s'))
                 (ra_state_unavail_moves_wl_fupd (K (ra_state_unavail_moves_wl s')) s) /\
          ALL (\x. MEM x (APPEND (ra_state_avail_moves_wl s) (ra_state_unavail_moves_wl s)))
            (ra_state_avail_moves_wl s') /\
          ALL (\x. MEM x (APPEND (ra_state_avail_moves_wl s) (ra_state_unavail_moves_wl s)))
            (ra_state_unavail_moves_wl s')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[revive_moves_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_bind_ok
    (MATCH_MP st_ex_MAP_adj_ls_sub th)]) THEN
  REWRITE_TAC[get_unavail_moves_wl_def; get_avail_moves_wl_def] THEN
  SIMP RAPROOFAUX_msimps THEN
  RAPROOFAUX_PAIR_TAC (fun t -> is_comb t && is_comb(rator t) &&
     rator(rator t) = `PARTITION:(num#num#num->bool)->(num#num#num)list->
                        (num#num#num)list#(num#num#num)list`)
    `rev:(num#num#num)list` `unavail:(num#num#num)list` THEN
  ASM_REWRITE_TAC[case_def "prod"; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[set_avail_moves_wl_def; set_unavail_moves_wl_def] THEN SIMP[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PART_MEM o SYM o REWRITE_RULE[PARTITION_DEF] o
    check (fun th -> can (find_term ((=) `PARTITION:(num#num#num->bool)->(num#num#num)list->
                        (num#num#num)list#(num#num#num)list`)) (concl th))) THEN
  REWRITE_TAC[APPEND_NIL; MEM_APPEND; GSYM ALL_MEM; MEM_smerge; reg_alloc_sort_moves_def;
              sort_MEM; MEM] THEN
  MESON_TAC[]);;
(* HOL4 quantifies an unused b (here of type bool) *)
let unspill_success = prove
 (`!k s.
     good_ra_state s ==>
     ?s' (b:bool). unspill k s = (M_success one,s') /\
            good_ra_state s' /\
            is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s') /\
            ra_state_dim s = ra_state_dim s' /\
            ra_state_node_tag s = ra_state_node_tag s'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ra_state_spill_wl s`; `k:num`; `[]:num list`; `[]:num list`; `s:ra_state`]
    st_ex_PARTITION_split_degree) THEN
  ASM_REWRITE_TAC[MEM] THEN
  DISCH_THEN(X_CHOOSE_THEN `ts:num list` (X_CHOOSE_THEN `fs:num list` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `ALL (\v. v < ra_state_dim s) ts /\ ALL (\v. v < ra_state_dim s) fs`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `good_ra_state s` THEN REWRITE_TAC[good_ra_state_def] THEN STRIP_TAC THEN
    UNDISCH_TAC `ALL (\v. v < ra_state_dim s) (ra_state_spill_wl s)` THEN
    UNDISCH_TAC `ALL (\x. MEM x (ra_state_spill_wl s)) ts` THEN
    UNDISCH_TAC `ALL (\x. MEM x (ra_state_spill_wl s)) fs` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`ts:num list`; `s:ra_state`] revive_moves_success) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[RAPROOFAUX_good_lengths]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:ra_state` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_moves]) THEN
  MP_TAC(SPECL [`ts:num list`; `[]:num list`; `[]:num list`; `s1:ra_state`]
    st_ex_PARTITION_move_related_sub) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[RAPROOFAUX_good_lengths]; ALL_TAC] THEN
  REWRITE_TAC[MEM] THEN
  DISCH_THEN(X_CHOOSE_THEN `tf:num list` (X_CHOOSE_THEN `tsimp:num list` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[unspill_def; get_dim_def; get_spill_wl_def; set_spill_wl_def; add_simp_wl_def;
    add_freeze_wl_def; get_simp_wl_def; get_freeze_wl_def; set_simp_wl_def; set_freeze_wl_def] THEN
  SIMP RAPROOFAUX_msimps THEN
  REWRITE_TAC[is_subgraph_refl] THEN
  UNDISCH_TAC `good_ra_state s` THEN REWRITE_TAC[good_ra_state_def] THEN SIMP[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ALL_APPEND] THEN
  UNDISCH_TAC `ALL (\x. MEM x (APPEND (ra_state_avail_moves_wl s) (ra_state_unavail_moves_wl s)))
      (ra_state_avail_moves_wl s1)` THEN
  UNDISCH_TAC `ALL (\x. MEM x (APPEND (ra_state_avail_moves_wl s) (ra_state_unavail_moves_wl s)))
      (ra_state_unavail_moves_wl s1)` THEN
  UNDISCH_TAC `ALL (\x. MEM x (ts:num list)) tf` THEN
  UNDISCH_TAC `ALL (\x. MEM x (ts:num list)) tsimp` THEN
  UNDISCH_TAC `ALL (\v. v < ra_state_dim s) ts` THEN
  UNDISCH_TAC (CASE_TERM `ALL (\m. match m with (p:num,x,y) ->
      x < ra_state_dim s /\ y < ra_state_dim s) (ra_state_avail_moves_wl s)`) THEN
  UNDISCH_TAC (CASE_TERM `ALL (\m. match m with (p:num,x,y) ->
      x < ra_state_dim s /\ y < ra_state_dim s) (ra_state_unavail_moves_wl s)`) THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_APPEND] THEN MESON_TAC[]);;
let push_stack_success = prove
 (`!ls s.
     ALL (\x. x < ra_state_dim s) ls /\ good_ra_state s ==>
     ?d mr st. st_ex_FOREACH ls push_stack s =
                 (M_success one,
                  ra_state_degrees_fupd (K d) (ra_state_move_related_fupd (K mr)
                    (ra_state_stack_fupd (K st) s))) /\
               LENGTH d = LENGTH (ra_state_degrees s) /\
               LENGTH mr = LENGTH (ra_state_move_related s)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[st_ex_FOREACH_def; st_ex_return_def] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ra_state_degrees s`; `ra_state_move_related s`;
      `ra_state_stack s`] THEN
    SIMP[ra_state_component_equality];
    ALL_TAC] THEN
  REWRITE_TAC[ALL; st_ex_FOREACH_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `h < LENGTH (ra_state_degrees s) /\ h < LENGTH (ra_state_move_related s)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[RAPROOFAUX_good_lengths]; ALL_TAC] THEN
  SUBGOAL_THEN `push_stack h s = (M_success one,
     ra_state_degrees_fupd (K (LUPDATE 0 h (ra_state_degrees s)))
       (ra_state_move_related_fupd (K (LUPDATE F h (ra_state_move_related s)))
         (ra_state_stack_fupd (K (CONS h (ra_state_stack s))) s)))`
    (fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_ignore_bind_ok th]) THENL
   [REWRITE_TAC[push_stack_def; reg_alloc_get_stack_def; set_stack_def] THEN
    SIMP RAPROOFAUX_msimps;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ra_state_degrees_fupd (K (LUPDATE 0 h (ra_state_degrees s)))
       (ra_state_move_related_fupd (K (LUPDATE F h (ra_state_move_related s)))
         (ra_state_stack_fupd (K (CONS h (ra_state_stack s))) s))`) THEN
  ANTS_TAC THENL
   [SIMP[] THEN UNDISCH_TAC `good_ra_state s` THEN
    REWRITE_TAC[good_ra_state_def] THEN SIMP[LENGTH_LUPDATE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num list` (X_CHOOSE_THEN `mr:bool list`
    (X_CHOOSE_THEN `st:num list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`d:num list`; `mr:bool list`; `st:num list`] THEN
  ASM_REWRITE_TAC[] THEN SIMP[LENGTH_LUPDATE] THEN SIMP[ra_state_component_equality]);;
(* RAPROOFAUX_BIND_TAC th: th is m s = (M_success x,s1); rewrite             *)
(* st_ex_bind m f s and st_ex_ignore_bind m f s in the goal                  *)
let RAPROOFAUX_BIND_TAC (th:thm) : tactic =
  REWRITE_TAC[MATCH_MP RAPROOFAUX_bind_ok th; MATCH_MP RAPROOFAUX_ignore_bind_ok th];;

let RAPROOFAUX_get_simp_wl_ok = prove
 (`!s. (get_simp_wl:ra_state->(num list,state_exn)exc#ra_state) s =
       (M_success (ra_state_simp_wl s),s)`,
  REWRITE_TAC[get_simp_wl_def]);;

let do_simplify_success = prove
 (`!k s.
     good_ra_state s ==>
     ?s' b. do_simplify k s = (M_success b,s') /\
            good_ra_state s' /\
            is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s') /\
            ra_state_dim s = ra_state_dim s' /\
            ra_state_node_tag s = ra_state_node_tag s'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[do_simplify_def] THEN
  RAPROOFAUX_BIND_TAC(SPEC `s:ra_state` RAPROOFAUX_get_simp_wl_ok) THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[st_ex_return_def] THEN MAP_EVERY EXISTS_TAC [`s:ra_state`; `F`] THEN
    ASM_REWRITE_TAC[is_subgraph_refl];
    ALL_TAC] THEN
  MP_TAC(SPECL [`ra_state_simp_wl s`; `s:ra_state`] dec_degree_success) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:num list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  MP_TAC(SPECL [`ra_state_simp_wl s`; `ra_state_degrees_fupd (K d) s`] push_stack_success) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `good_ra_state s` THEN SIMP[good_ra_state_def];
      MATCH_MP_TAC RAPROOFAUX_good_degrees_fupd THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:num list` (X_CHOOSE_THEN `mr:bool list`
    (X_CHOOSE_THEN `st:num list` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  REWRITE_TAC[set_simp_wl_def] THEN SIMP RAPROOFAUX_msimps THEN
  MP_TAC(SPECL [`k:num`; `ra_state_degrees_fupd (K d2) (ra_state_simp_wl_fupd (K [])
     (ra_state_move_related_fupd (K mr) (ra_state_stack_fupd (K st) s)))`] unspill_success) THEN
  ANTS_TAC THENL
  [UNDISCH_TAC `good_ra_state s` THEN REWRITE_TAC[good_ra_state_def] THEN SIMP[];
   REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `s4:ra_state` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[case_def "prod"; case_def "exc"] THEN
  MAP_EVERY EXISTS_TAC [`s4:ra_state`; `T`] THEN
  UNDISCH_TAC `ra_state_dim (ra_state_degrees_fupd (K d2) (ra_state_simp_wl_fupd (K [])
     (ra_state_move_related_fupd (K mr) (ra_state_stack_fupd (K st) s)))) = ra_state_dim s4` THEN
  UNDISCH_TAC `ra_state_node_tag (ra_state_degrees_fupd (K d2) (ra_state_simp_wl_fupd (K [])
     (ra_state_move_related_fupd (K mr) (ra_state_stack_fupd (K st) s)))) =
     ra_state_node_tag s4` THEN
  UNDISCH_TAC `is_subgraph (ra_state_adj_ls (ra_state_degrees_fupd (K d2)
     (ra_state_simp_wl_fupd (K [])
     (ra_state_move_related_fupd (K mr) (ra_state_stack_fupd (K st) s)))))
     (ra_state_adj_ls s4)` THEN
  SIMP[]]);;
(* RAPROOFAUX_FILTER_ok, RAPROOFAUX_MAP_ok: st_ex_FILTER and st_ex_MAP of     *)
(* functions that only read the state                                       *)
let RAPROOFAUX_FILTER_ok = prove
 (`!(P:A->S->(bool,E)exc#S) ls acc s.
     (!x. MEM x ls ==> ?b. P x s = (M_success b,s)) ==>
     ?ts. st_ex_FILTER P ls acc s = (M_success ts,s) /\
          !z. MEM z ts ==> MEM z ls \/ MEM z acc`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[st_ex_FILTER_def; MEM] THENL
   [REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
    REPEAT GEN_TAC THEN EXISTS_TAC `acc:A list` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `h:A`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:bool` ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (h:A) acc`; `s:S`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`acc:A list`; `s:S`])] THEN
  (ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[MEM] THEN
  GEN_TAC THEN MATCH_MP_TAC(TAUT `(b ==> c) ==> a /\ b ==> a /\ c`) THEN MESON_TAC[]);;

let RAPROOFAUX_MAP_ok = prove
 (`!(f:A->S->(B,E)exc#S) ls s.
     (!x. MEM x ls ==> ?y. f x s = (M_success y,s)) ==>
     ?ys. st_ex_MAP f ls s = (M_success ys,s)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[st_ex_MAP_def; MEM] THENL
   [REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
    REPEAT GEN_TAC THEN EXISTS_TAC `[]:B list` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `h:A`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:B` ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:S`) THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ys:B list` ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
  EXISTS_TAC `CONS (y:B) ys` THEN REWRITE_TAC[]);;

(* This basically says nothing at the moment *)
(* HOL4: the unused fs is given the type num list *)
let st_ex_FILTER_is_not_coalesced = prove
 (`!ls acc s.
     ALL (\x. x < LENGTH (ra_state_coalesced s)) ls /\
     ALL (\x. x < LENGTH (ra_state_coalesced s)) acc ==>
     ?ts (fs:num list). st_ex_FILTER is_not_coalesced ls acc s = (M_success ts,s) /\
             ALL (\x. x < LENGTH (ra_state_coalesced s)) ts`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`is_not_coalesced`; `ls:num list`; `acc:num list`; `s:ra_state`]
    RAPROOFAUX_FILTER_ok) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN REPEAT STRIP_TAC THEN
    SIMP(is_not_coalesced_def :: RAPROOFAUX_msimps);
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[]);;
let consistency_ok_success = prove
 (`!x y s.
     good_ra_state s /\ x < ra_state_dim s /\ y < ra_state_dim s ==>
     ?b. consistency_ok x y s = (M_success b,s) /\
         (b ==> x < ra_state_dim s /\ y < ra_state_dim s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[consistency_ok_def] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
   [EXISTS_TAC `F` THEN REWRITE_TAC[st_ex_return_def];
    SIMP(COND_RATOR :: is_Fixed_def :: RAPROOFAUX_good_lengths :: RAPROOFAUX_msimps) THEN
    COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ; injectivity "exc"] THEN MESON_TAC[]]);;
let st_ex_FILTER_consistency_ok = prove
 (CASE_TERM `!ls acc s.
     good_ra_state s /\
     ALL (\m. match m with (p:num,x,y) -> x < ra_state_dim s /\ y < ra_state_dim s) ls ==>
     ?ts. st_ex_FILTER (\m. match m with (_,(x,y)) -> consistency_ok x y) ls acc s =
            (M_success ts,s) /\
          ALL (\m. match m with
                     (p,(x,y)) -> (x < ra_state_dim s /\ y < ra_state_dim s) \/
                                  MEM (p,(x,y)) acc) ts`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [CASE_TERM `\m. match m with (_:num,(x,y)) -> consistency_ok x y`;
                 `ls:(num#num#num)list`; `acc:(num#num#num)list`; `s:ra_state`]
    RAPROOFAUX_FILTER_ok) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC (CASE_TERM `ALL (\m. match m with (p:num,x,y) ->
      x < ra_state_dim s /\ y < ra_state_dim s) ls`) THEN
    REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; case_def "prod"] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`p1':num`; `p2:num`; `s:ra_state`] consistency_ok_success) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC(TAUT `(b ==> c) ==> a /\ b ==> a /\ c`) THEN
  UNDISCH_TAC (CASE_TERM `ALL (\m. match m with (p:num,x,y) ->
      x < ra_state_dim s /\ y < ra_state_dim s) ls`) THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; case_def "prod"] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`p1:num`; `p1':num`; `p2:num`]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
(* do_coalesce *)
let RAPROOFAUX_considered_var_ok = prove
 (`!k x s. x < LENGTH (ra_state_node_tag s) ==>
           ?b. considered_var k x s = (M_success b,s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[considered_var_def; is_Atemp_def; is_Fixed_k_def] THEN
  SIMP RAPROOFAUX_msimps THEN MESON_TAC[]);;

(* HOL4: the unused fs is given the type num list; k (free in HOL4) is *)
(* quantified                                                          *)
let st_ex_FILTER_considered_var = prove
 (`!k ls acc s.
     ALL (\x. x < LENGTH (ra_state_node_tag s)) ls /\
     ALL (\x. x < LENGTH (ra_state_node_tag s)) acc ==>
     ?ts (fs:num list). st_ex_FILTER (considered_var k) ls acc s = (M_success ts,s) /\
             ALL (\x. x < LENGTH (ra_state_node_tag s)) ts`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`considered_var k`; `ls:num list`; `acc:num list`; `s:ra_state`]
    RAPROOFAUX_FILTER_ok) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RAPROOFAUX_considered_var_ok THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN REWRITE_TAC[EXISTS_SIMP] THEN
  MATCH_MP_TAC(TAUT `(b ==> c) ==> a /\ b ==> a /\ c`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[]);;

let RAPROOFAUX_deg_or_inf_ok = prove
 (`!k x s. good_ra_state s /\ x < ra_state_dim s ==>
           ?d. deg_or_inf k x s = (M_success d,s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[deg_or_inf_def; is_Fixed_k_def] THEN
  SIMP(COND_RATOR :: RAPROOFAUX_good_lengths :: RAPROOFAUX_msimps) THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ; injectivity "exc"] THEN MESON_TAC[]);;

(* HOL4: val st_ex_MAP_deg_or_inf (an ML value of the script) *)
let RAPROOFAUX_st_ex_MAP_deg_or_inf = prove
 (`!k ls s.
     good_ra_state s /\ ALL (\x. x < ra_state_dim s) ls ==>
     ?degs. st_ex_MAP (deg_or_inf k) ls s = (M_success degs,s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RAPROOFAUX_MAP_ok THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ALL_MEM]) THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RAPROOFAUX_deg_or_inf_ok THEN ASM_SIMP_TAC[]);;
let bg_ok_success = prove
 ((CASE_TERM `!k x y s.
     good_ra_state s /\ x < ra_state_dim s /\ y < ra_state_dim s ==>
     ?opt. bg_ok k x y s = (M_success opt,s) /\
           match opt with
             NONE -> T
           | SOME (case1,case2) ->
               ALL (\v. v < ra_state_dim s) case1 /\ ALL (\v. v < ra_state_dim s) case2`),
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bg_ok_def; LET_DEF; LET_END_DEF; RAPROOFAUX_bind_return_left] THEN
  MP_TAC(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. z < ra_state_dim s ==>
     adj_ls_sub z s = (M_success (EL z (ra_state_adj_ls s)),s) /\
     ALL (\v. v < ra_state_dim s) (EL z (ra_state_adj_ls s))` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[adj_ls_sub_eqn] THEN
    UNDISCH_TAC `good_ra_state s` THEN REWRITE_TAC[good_ra_state_def; GSYM ALL_EL] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    RAPROOFAUX_BIND_TAC(CONJUNCT1(MATCH_MP th (ASSUME `x < ra_state_dim s`)))) THEN
  FIRST_ASSUM(fun th ->
    RAPROOFAUX_BIND_TAC(CONJUNCT1(MATCH_MP th (ASSUME `y < ra_state_dim s`)))) THEN
  RAPROOFAUX_PAIR_TAC (fun t -> is_comb t && is_comb(rator t) &&
     rator(rator t) = `PARTITION:(num->bool)->num list->num list#num list`)
    `c1:num list` `c2:num list` THEN
  ASM_REWRITE_TAC[case_def "prod"] THEN
  SUBGOAL_THEN `ALL (\v. v < ra_state_dim s) c1 /\ ALL (\v. v < ra_state_dim s) c2`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PART_MEM o SYM o REWRITE_RULE[PARTITION_DEF] o
      check (fun th -> can (find_term ((=) `PARTITION:(num->bool)->num list->num list#num list`))
                       (concl th))) THEN
    MP_TAC(CONJUNCT2(MATCH_MP (ASSUME `!z. z < ra_state_dim s ==>
       adj_ls_sub z s = (M_success (EL z (ra_state_adj_ls s)),s) /\
       ALL (\v. v < ra_state_dim s) (EL z (ra_state_adj_ls s))`)
       (ASSUME `y < ra_state_dim s`))) THEN
    REWRITE_TAC[GSYM ALL_MEM; APPEND_NIL; MEM_APPEND; MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `c1:num list`; `[]:num list`; `s:ra_state`]
    st_ex_FILTER_considered_var) THEN
  ASM_REWRITE_TAC[ALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:num list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  MP_TAC(SPECL [`k:num`; `c2:num list`; `[]:num list`; `s:ra_state`]
    st_ex_FILTER_considered_var) THEN
  ASM_REWRITE_TAC[ALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:num list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  MP_TAC(SPECL [`k:num`; `t2:num list`; `s:ra_state`] RAPROOFAUX_st_ex_MAP_deg_or_inf) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dg2:num list` ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN COND_CASES_TAC THENL
   [REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1; case_def "option"; case_def "prod"] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`;
                `FILTER (\v. ~sorted_mem v (EL y (ra_state_adj_ls s))) (EL x (ra_state_adj_ls s))`;
                `[]:num list`; `s:ra_state`] st_ex_FILTER_considered_var) THEN
  ASM_REWRITE_TAC[ALL; EVERY_FILTER] THEN ANTS_TAC THENL
   [MP_TAC(CONJUNCT2(MATCH_MP (ASSUME `!z. z < ra_state_dim s ==>
       adj_ls_sub z s = (M_success (EL z (ra_state_adj_ls s)),s) /\
       ALL (\v. v < ra_state_dim s) (EL z (ra_state_adj_ls s))`)
       (ASSUME `x < ra_state_dim s`))) THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:num list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  MP_TAC(SPECL [`k + 1`; `t1:num list`; `s:ra_state`] RAPROOFAUX_st_ex_MAP_deg_or_inf) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dg1:num list` ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  MP_TAC(SPECL [`k:num`; `t3:num list`; `s:ra_state`] RAPROOFAUX_st_ex_MAP_deg_or_inf) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dg3:num list` ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1; case_def "option"; case_def "prod"] THEN
  ASM_REWRITE_TAC[]);;

let RAPROOFAUX_good_coalesced_fupd = prove
 (`!s c. good_ra_state s /\ LENGTH c = LENGTH (ra_state_coalesced s) /\
         ALL (\v. v < ra_state_dim s) c ==>
         good_ra_state (ra_state_coalesced_fupd (K c) s)`,
  REWRITE_TAC[good_ra_state_def] THEN SIMP[]);;

let RAPROOFAUX_is_Fixed_ok = prove
 (CASE_TERM `!x s. x < LENGTH (ra_state_node_tag s) ==>
     is_Fixed x s = (M_success (match EL x (ra_state_node_tag s) with Fixed n -> T | _ -> F),s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[is_Fixed_def] THEN SIMP RAPROOFAUX_msimps);;

let coalesce_parent_success = prove
 (`!x s. x < ra_state_dim s /\ good_ra_state s ==>
         ?y s' coal. coalesce_parent x s = (M_success y,s') /\
                     y < ra_state_dim s /\ good_ra_state s' /\
                     s' = ra_state_coalesced_fupd (K coal) s`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s:ra_state` THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `EL x (ra_state_coalesced s) < ra_state_dim s` ASSUME_TAC THENL
   [UNDISCH_TAC `good_ra_state s` THEN REWRITE_TAC[good_ra_state_def; GSYM ALL_EL] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[coalesce_parent_def] THEN
  SUBGOAL_THEN `coalesced_sub x s = (M_success (EL x (ra_state_coalesced s)),s)`
    RAPROOFAUX_BIND_TAC THENL [ASM_REWRITE_TAC[coalesced_sub]; ALL_TAC] THEN
  SUBGOAL_THEN `EL x (ra_state_coalesced s) < LENGTH (ra_state_node_tag s)`
    (fun th -> RAPROOFAUX_BIND_TAC(MATCH_MP RAPROOFAUX_is_Fixed_ok th)) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
    MAP_EVERY EXISTS_TAC [`EL x (ra_state_coalesced s)`; `s:ra_state`;
      `ra_state_coalesced s`] THEN
    ASM_REWRITE_TAC[] THEN SIMP[ra_state_component_equality];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
    MAP_EVERY EXISTS_TAC [`x:num`; `s:ra_state`; `ra_state_coalesced s`] THEN
    ASM_REWRITE_TAC[] THEN SIMP[ra_state_component_equality];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `EL x (ra_state_coalesced s)`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:ra_state`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num` (X_CHOOSE_THEN `s1:ra_state`
    (X_CHOOSE_THEN `c1:num list` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `s1:ra_state`)) THEN
  SUBGOAL_THEN `LENGTH (c1:num list) = ra_state_dim s /\
                ALL (\v. v < ra_state_dim s) c1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `good_ra_state (ra_state_coalesced_fupd (K (c1:num list)) s)` THEN
    REWRITE_TAC[good_ra_state_def] THEN SIMP[];
    ALL_TAC] THEN
  SUBGOAL_THEN `update_coalesced x y (ra_state_coalesced_fupd (K (c1:num list)) s) = (M_success one,
     ra_state_coalesced_fupd (K (LUPDATE y x c1)) s)`
    RAPROOFAUX_BIND_TAC THENL [SIMP[update_coalesced_eqn]; ALL_TAC] THEN
  REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
  MAP_EVERY EXISTS_TAC [`y:num`; `ra_state_coalesced_fupd (K (LUPDATE y x (c1:num list))) s`;
    `LUPDATE y x (c1:num list)`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RAPROOFAUX_good_coalesced_fupd THEN
  ASM_REWRITE_TAC[LENGTH_LUPDATE] THEN
  MATCH_MP_TAC IMP_EVERY_LUPDATE THEN ASM_REWRITE_TAC[]);;
let canonize_move_success = prove
 (`!x y s.
     x < ra_state_dim s /\ y < ra_state_dim s /\ good_ra_state s ==>
     ?x2 y2. canonize_move x y s = (M_success (x2,y2),s) /\
             x2 < ra_state_dim s /\ y2 < ra_state_dim s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`)) THEN STRIP_TAC THEN
  REWRITE_TAC[canonize_move_def] THEN
  SUBGOAL_THEN `x < LENGTH (ra_state_node_tag s)`
    (fun th -> RAPROOFAUX_BIND_TAC(MATCH_MP RAPROOFAUX_is_Fixed_ok th)) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `y < LENGTH (ra_state_node_tag s)`
    (fun th -> RAPROOFAUX_BIND_TAC(MATCH_MP RAPROOFAUX_is_Fixed_ok th)) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN ASM_MESON_TAC[]);;
let st_ex_FIRST_consistency_ok_bg_ok = prove
 ((CASE_TERM `!k ls acc s.
  good_ra_state s /\
  ALL (\m. match m with (p:num,x,y) -> x < ra_state_dim s /\ y < ra_state_dim s) ls /\
  ALL (\m. match m with (p:num,x,y) -> x < ra_state_dim s /\ y < ra_state_dim s) acc ==>
  ?ores ys s' coal.
    st_ex_FIRST consistency_ok (bg_ok k) ls acc s = (M_success (ores,ys),s') /\
    good_ra_state s' /\
    s' = ra_state_coalesced_fupd (K coal) s /\
    ALL (\m. match m with (p:num,x,y) -> x < ra_state_dim s /\ y < ra_state_dim s) ys /\
    match ores with
      SOME ((x,y),(case1,case2),rest) ->
        x < ra_state_dim s /\ y < ra_state_dim s /\
        ALL (\v. v < ra_state_dim s) case1 /\ ALL (\v. v < ra_state_dim s) case2 /\
        ALL (\m. match m with (p:num,x,y) -> x < ra_state_dim s /\ y < ra_state_dim s) rest
    | _ -> T`),
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[st_ex_FIRST_def; st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
    REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`NONE:((num#num)#(num list#num list)#(num#num#num)list)option`;
      `acc:(num#num#num)list`; `s:ra_state`; `ra_state_coalesced s`] THEN
    ASM_REWRITE_TAC[case_def "option"] THEN SIMP[ra_state_component_equality];
    ALL_TAC] THEN
  MP_TAC(ISPEC `h:num#num#num` BASICAUX_TUPLE3) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `x:num` (X_CHOOSE_THEN `y:num` SUBST1_TAC))) THEN
  REWRITE_TAC[ALL; st_ex_FIRST_def; case_def "prod"] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:num`; `s:ra_state`] coalesce_parent_success) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:num` (X_CHOOSE_THEN `s1:ra_state`
    (X_CHOOSE_THEN `c1:num list` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `s1:ra_state`)) THEN
  MP_TAC(SPECL [`y:num`; `ra_state_coalesced_fupd (K (c1:num list)) s`]
    coalesce_parent_success) THEN
  SIMP[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:num` (X_CHOOSE_THEN `c2:num list` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  MP_TAC(SPECL [`x1:num`; `y1:num`; `ra_state_coalesced_fupd (K (c2:num list)) s`]
    consistency_ok_success) THEN
  SIMP[] THEN DISCH_THEN(X_CHOOSE_THEN `b1:bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`acc:(num#num#num)list`;
      `ra_state_coalesced_fupd (K (c2:num list)) s`]) THEN
    SIMP[] THEN DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`x1:num`; `y1:num`; `ra_state_coalesced_fupd (K (c2:num list)) s`]
    canonize_move_success) THEN
  SIMP[] THEN DISCH_THEN(X_CHOOSE_THEN `x2:num` (X_CHOOSE_THEN `y2:num` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN REWRITE_TAC[case_def "prod"] THEN
  MP_TAC(SPECL [`k:num`; `x2:num`; `y2:num`; `ra_state_coalesced_fupd (K (c2:num list)) s`]
    bg_ok_success) THEN
  SIMP[] THEN DISCH_THEN(X_CHOOSE_THEN `opt:(num list#num list)option` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  POP_ASSUM MP_TAC THEN CASES_ON `opt:(num list#num list)option` THEN
  REWRITE_TAC[case_def "option"] THENL
   [TRY DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (p:num,x2:num,y2:num) acc`;
      `ra_state_coalesced_fupd (K (c2:num list)) s`]) THEN
    SIMP[ALL; case_def "prod"] THEN DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `a:num list#num list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs1:num list` (X_CHOOSE_THEN `cs2:num list` SUBST1_TAC)) THEN
  REWRITE_TAC[case_def "prod"; st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`SOME ((x2:num,y2:num),(cs1:num list,cs2:num list),t:(num#num#num)list)`;
    `acc:(num#num#num)list`; `c2:num list`] THEN
  ASM_REWRITE_TAC[case_def "option"; case_def "prod"] THEN
  UNDISCH_TAC `x2 < ra_state_dim (ra_state_coalesced_fupd (K (c2:num list)) s)` THEN
  UNDISCH_TAC `y2 < ra_state_dim (ra_state_coalesced_fupd (K (c2:num list)) s)` THEN
  SIMP[]);;
(* RAPROOFAUX_push_stack_ok, RAPROOFAUX_inc_deg_ok: single steps *)
let RAPROOFAUX_push_stack_ok = prove
 (`!y s. y < LENGTH (ra_state_degrees s) /\ y < LENGTH (ra_state_move_related s) ==>
         push_stack y s =
         (M_success one,
          ra_state_degrees_fupd (K (LUPDATE 0 y (ra_state_degrees s)))
            (ra_state_move_related_fupd (K (LUPDATE F y (ra_state_move_related s)))
              (ra_state_stack_fupd (K (CONS y (ra_state_stack s))) s)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[push_stack_def; reg_alloc_get_stack_def; set_stack_def] THEN
  SIMP RAPROOFAUX_msimps);;

let RAPROOFAUX_inc_deg_ok = prove
 (`!x n s. x < LENGTH (ra_state_degrees s) ==>
           inc_deg x n s =
           (M_success one,
            ra_state_degrees_fupd
              (K (LUPDATE (EL x (ra_state_degrees s) + n) x (ra_state_degrees s))) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inc_deg_def] THEN SIMP RAPROOFAUX_msimps);;

let do_coalesce_real_success = prove
 (`!x y case1 case2 s.
     y < ra_state_dim s /\ x < ra_state_dim s /\
     ALL (\v. v < ra_state_dim s) case1 /\ ALL (\v. v < ra_state_dim s) case2 /\
     good_ra_state s ==>
     ?s'. do_coalesce_real x y case1 case2 s = (M_success one,s') /\
          good_ra_state s' /\
          is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s') /\
          ra_state_dim s = ra_state_dim s' /\
          ra_state_node_tag s = ra_state_node_tag s'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`)) THEN STRIP_TAC THEN
  REWRITE_TAC[do_coalesce_real_def] THEN
  SUBGOAL_THEN `update_coalesced y x s = (M_success one,
     ra_state_coalesced_fupd (K (LUPDATE x y (ra_state_coalesced s))) s)`
    RAPROOFAUX_BIND_TAC THENL [ASM_REWRITE_TAC[update_coalesced_eqn]; ALL_TAC] THEN
  SUBGOAL_THEN `good_ra_state (ra_state_coalesced_fupd (K (LUPDATE x y (ra_state_coalesced s))) s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RAPROOFAUX_good_coalesced_fupd THEN
    ASM_REWRITE_TAC[LENGTH_LUPDATE] THEN MATCH_MP_TAC IMP_EVERY_LUPDATE THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `good_ra_state s` THEN SIMP[good_ra_state_def];
    ALL_TAC] THEN
  SUBGOAL_THEN `x < LENGTH (ra_state_node_tag
      (ra_state_coalesced_fupd (K (LUPDATE x y (ra_state_coalesced s))) s))`
    (fun th -> RAPROOFAUX_BIND_TAC(MATCH_MP RAPROOFAUX_is_Fixed_ok th)) THENL
   [SIMP[]; ALL_TAC] THEN
  ALL_TAC THEN
  SUBGOAL_THEN (CASE_TERM `?d2. (if (match EL x (ra_state_node_tag
               (ra_state_coalesced_fupd (K (LUPDATE x y (ra_state_coalesced s))) s)) with
                  Fixed n -> T | _ -> F)
      then st_ex_return one else inc_deg x (LENGTH (case2:num list)))
      (ra_state_coalesced_fupd (K (LUPDATE x y (ra_state_coalesced s))) s) =
      (M_success one, ra_state_degrees_fupd (K d2)
         (ra_state_coalesced_fupd (K (LUPDATE x y (ra_state_coalesced s))) s)) /\
      LENGTH d2 = LENGTH (ra_state_degrees s)`) STRIP_ASSUME_TAC THENL
   [COND_CASES_TAC THENL
     [EXISTS_TAC `ra_state_degrees s` THEN REWRITE_TAC[st_ex_return_def] THEN
      SIMP[ra_state_component_equality];
      SIMP[RAPROOFAUX_inc_deg_ok] THEN
      EXISTS_TAC `LUPDATE (EL x (ra_state_degrees s) + LENGTH (case2:num list)) x
                    (ra_state_degrees s)` THEN
      SIMP[LENGTH_LUPDATE]];
    ALL_TAC] THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  MP_TAC(SPECL [`case2:num list`; `x:num`; `ra_state_degrees_fupd (K (d2:num list))
     (ra_state_coalesced_fupd (K (LUPDATE x y (ra_state_coalesced s))) s)`]
     list_insert_edge_succeeds) THEN
  ANTS_TAC THENL
   [SIMP[] THEN MATCH_MP_TAC RAPROOFAUX_good_degrees_fupd THEN SIMP[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:ra_state` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE []) THEN
  MP_TAC(SPECL [`case1:num list`; `s3:ra_state`] dec_deg_success) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d4:num list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  SUBGOAL_THEN `y < LENGTH (ra_state_degrees (ra_state_degrees_fupd (K d4) s3)) /\
                y < LENGTH (ra_state_move_related (ra_state_degrees_fupd (K d4) s3))`
    (fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_push_stack_ok th]) THENL
   [SIMP[]; ALL_TAC] THEN
  EXISTS_TAC `ra_state_degrees_fupd
               (K (LUPDATE 0 y (ra_state_degrees (ra_state_degrees_fupd (K d4) s3))))
            (ra_state_move_related_fupd
               (K (LUPDATE F y (ra_state_move_related (ra_state_degrees_fupd (K d4) s3))))
              (ra_state_stack_fupd (K (CONS y (ra_state_stack (ra_state_degrees_fupd (K d4) s3))))
                (ra_state_degrees_fupd (K d4) s3)))` THEN
  SIMP[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `good_ra_state s3` THEN REWRITE_TAC[good_ra_state_def] THEN
    SIMP[LENGTH_LUPDATE];
    ASM_REWRITE_TAC[is_subgraph_def] THEN MESON_TAC[]]);;
let RAPROOFAUX_respill_ok = prove
 (`!k x s. good_ra_state s /\ x < ra_state_dim s ==>
           ?s'. respill k x s = (M_success one,s') /\ good_ra_state s' /\
                ra_state_adj_ls s' = ra_state_adj_ls s /\
                ra_state_dim s' = ra_state_dim s /\
                ra_state_node_tag s' = ra_state_node_tag s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`)) THEN STRIP_TAC THEN
  REWRITE_TAC[respill_def] THEN
  SUBGOAL_THEN `degrees_sub x s = (M_success (EL x (ra_state_degrees s)),s)`
    RAPROOFAUX_BIND_TAC THENL [ASM_REWRITE_TAC[degrees_sub_eqn]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[st_ex_return_def] THEN EXISTS_TAC `s:ra_state` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[get_freeze_wl_def; add_spill_wl_def; get_spill_wl_def; set_spill_wl_def;
              set_freeze_wl_def] THEN
  SIMP(COND_RATOR :: RAPROOFAUX_msimps) THEN COND_CASES_TAC THEN SIMP[] THEN
  UNDISCH_TAC `good_ra_state s` THEN REWRITE_TAC[good_ra_state_def] THEN SIMP[ALL] THEN
  REWRITE_TAC[ALL_FILTER] THEN SIMP[GSYM ALL_MEM] THEN MESON_TAC[]);;
let do_coalesce_success = prove
 (`!k s.
     good_ra_state s ==>
     ?s' b. do_coalesce k s = (M_success b,s') /\
            good_ra_state s' /\
            is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s') /\
            ra_state_dim s = ra_state_dim s' /\
            ra_state_node_tag s = ra_state_node_tag s'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[do_coalesce_def] THEN
  SUBGOAL_THEN `(get_avail_moves_wl:ra_state->((num#num#num)list,state_exn)exc#ra_state) s =
                (M_success (ra_state_avail_moves_wl s),s)` RAPROOFAUX_BIND_TAC THENL
   [REWRITE_TAC[get_avail_moves_wl_def]; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `ra_state_avail_moves_wl s`; `[]:(num#num#num)list`; `s:ra_state`]
    st_ex_FIRST_consistency_ok_bg_ok) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `good_ra_state s` THEN SIMP[good_ra_state_def; ALL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ores:((num#num)#(num list#num list)#(num#num#num)list)option`
    (X_CHOOSE_THEN `ys:(num#num#num)list` (X_CHOOSE_THEN `s1:ra_state`
    (X_CHOOSE_THEN `c1:num list` STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN REWRITE_TAC[case_def "prod"] THEN
  SUBGOAL_THEN `(add_unavail_moves_wl ys:ra_state->(1,state_exn)exc#ra_state) s1 = (M_success one,
     ra_state_unavail_moves_wl_fupd (K (APPEND ys (ra_state_unavail_moves_wl s1))) s1)`
    RAPROOFAUX_BIND_TAC THENL
   [REWRITE_TAC[add_unavail_moves_wl_def; get_unavail_moves_wl_def;
                set_unavail_moves_wl_def] THEN SIMP RAPROOFAUX_msimps;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o
    check (fun th -> is_eq(concl th) && lhs(concl th) = `s1:ra_state`)) THEN
  SUBGOAL_THEN `good_ra_state (ra_state_unavail_moves_wl_fupd (K (APPEND ys
     (ra_state_unavail_moves_wl (ra_state_coalesced_fupd (K c1) s))))
     (ra_state_coalesced_fupd (K c1) s))` ASSUME_TAC THENL
   [UNDISCH_TAC `good_ra_state (ra_state_coalesced_fupd (K (c1:num list)) s)` THEN
    REWRITE_TAC[good_ra_state_def] THEN SIMP[ALL_APPEND] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `good_ra_state s` THEN SIMP[good_ra_state_def];
    ALL_TAC] THEN
  CASES_ON `ores:((num#num)#(num list#num list)#(num#num#num)list)option` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "option"]) THEN REWRITE_TAC[case_def "option"] THENL
  [(REWRITE_TAC[set_avail_moves_wl_def] THEN SIMP RAPROOFAUX_msimps THEN
  REWRITE_TAC[is_subgraph_refl] THEN
  UNDISCH_TAC `good_ra_state (ra_state_unavail_moves_wl_fupd (K (APPEND ys
     (ra_state_unavail_moves_wl (ra_state_coalesced_fupd (K (c1:num list)) s))))
     (ra_state_coalesced_fupd (K c1) s))` THEN
  REWRITE_TAC[good_ra_state_def] THEN SIMP[ALL] THEN
  DISCH_THEN(K ALL_TAC) THEN EXISTS_TAC `F` THEN REWRITE_TAC[]);
   (SUBGOAL_THEN `?x y cs1 cs2 ms. (a:(num#num)#(num list#num list)#(num#num#num)list) =
                 ((x,y),(cs1,cs2),ms)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "prod"]) THEN REWRITE_TAC[case_def "prod"] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
   (SUBGOAL_THEN `(set_avail_moves_wl ms:ra_state->(1,state_exn)exc#ra_state)
     (ra_state_unavail_moves_wl_fupd (K (APPEND ys
      (ra_state_unavail_moves_wl (ra_state_coalesced_fupd (K (c1:num list)) s))))
     (ra_state_coalesced_fupd (K c1) s)) =
     (M_success one,
      ra_state_avail_moves_wl_fupd (K ms) (ra_state_unavail_moves_wl_fupd (K (APPEND ys
      (ra_state_unavail_moves_wl (ra_state_coalesced_fupd (K c1) s))))
     (ra_state_coalesced_fupd (K c1) s)))` RAPROOFAUX_BIND_TAC THENL
   [REWRITE_TAC[set_avail_moves_wl_def]; ALL_TAC] THEN
  MP_TAC(SPECL [`x:num`; `y:num`; `cs1:num list`; `cs2:num list`;
    `ra_state_avail_moves_wl_fupd (K ms) (ra_state_unavail_moves_wl_fupd (K (APPEND ys
      (ra_state_unavail_moves_wl (ra_state_coalesced_fupd (K (c1:num list)) s))))
     (ra_state_coalesced_fupd (K c1) s))`] do_coalesce_real_success) THEN
  ANTS_TAC THENL
   [SIMP[] THEN
    UNDISCH_TAC `good_ra_state (ra_state_unavail_moves_wl_fupd (K (APPEND ys
     (ra_state_unavail_moves_wl (ra_state_coalesced_fupd (K (c1:num list)) s))))
     (ra_state_coalesced_fupd (K c1) s))` THEN
    REWRITE_TAC[good_ra_state_def] THEN SIMP[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s4:ra_state` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  MP_TAC(SPECL [`k:num`; `s4:ra_state`] unspill_success) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s5:ra_state` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  MP_TAC(SPECL [`k:num`; `x:num`; `s5:ra_state`] RAPROOFAUX_respill_ok) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> lhs(concl th) = `ra_state_dim s4`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `ra_state_dim s4`)) THEN
    SIMP[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s6:ra_state` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
  MAP_EVERY EXISTS_TAC [`s6:ra_state`; `T`] THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[is_subgraph_trans]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]])]);;

let st_ex_FOREACH_update_move_related = prove
 (`!ls s b.
     ALL (\v. v < LENGTH (ra_state_move_related s)) ls ==>
     ?lss. st_ex_FOREACH ls (\x. update_move_related x b) s =
             (M_success one,ra_state_move_related_fupd (K lss) s) /\
           LENGTH lss = LENGTH (ra_state_move_related s)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[st_ex_FOREACH_def; st_ex_return_def] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `ra_state_move_related s` THEN SIMP[ra_state_component_equality];
    ALL_TAC] THEN
  REWRITE_TAC[ALL; st_ex_FOREACH_def] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `update_move_related h b s = (M_success one,
     ra_state_move_related_fupd (K (LUPDATE b h (ra_state_move_related s))) s)`
    RAPROOFAUX_BIND_TAC THENL [ASM_REWRITE_TAC[update_move_related_eqn]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`ra_state_move_related_fupd (K (LUPDATE b h (ra_state_move_related s))) s`; `b:bool`]) THEN
  SIMP[LENGTH_LUPDATE] THEN
  DISCH_THEN(X_CHOOSE_THEN `l2:bool list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `l2:bool list` THEN ASM_REWRITE_TAC[] THEN SIMP[ra_state_component_equality]);;
(* RAPROOFAUX_reset_move_related_loop: the second loop of reset_move_related *)
let RAPROOFAUX_reset_move_related_loop = prove
 ((CASE_TERM `!(ls:(A#num#num)list) s.
     good_ra_state s /\
     ALL (\m. match m with (p:A,x,y) -> x < ra_state_dim s /\ y < ra_state_dim s) ls ==>
     ?mv. st_ex_FOREACH ls
            (\m. match m with
                   (_,(x,y)) ->
                     st_ex_bind (is_Fixed x) (\bx.
                     st_ex_bind (is_Fixed y) (\by.
                     st_ex_ignore_bind (update_move_related x (~bx))
                                       (update_move_related y (~by))))) s =
            (M_success one,ra_state_move_related_fupd (K mv) s) /\
          LENGTH mv = LENGTH (ra_state_move_related s)`),
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[st_ex_FOREACH_def; st_ex_return_def] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `ra_state_move_related s` THEN SIMP[ra_state_component_equality];
    ALL_TAC] THEN
  MP_TAC(ISPEC `h:A#num#num` BASICAUX_TUPLE3) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:A` (X_CHOOSE_THEN `x:num` (X_CHOOSE_THEN `y:num` SUBST1_TAC))) THEN
  REWRITE_TAC[ALL; st_ex_FOREACH_def; case_def "prod"] THEN REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `?mv1. st_ex_bind (is_Fixed x) (\bx.
          st_ex_bind (is_Fixed y) (\by.
               st_ex_ignore_bind (update_move_related x (~bx))
               (update_move_related y (~by)))) s =
     (M_success one,ra_state_move_related_fupd (K mv1) s) /\
     LENGTH mv1 = LENGTH (ra_state_move_related s)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `x < LENGTH (ra_state_node_tag s)`
      (fun th -> RAPROOFAUX_BIND_TAC(MATCH_MP RAPROOFAUX_is_Fixed_ok th)) THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `y < LENGTH (ra_state_node_tag s)`
      (fun th -> RAPROOFAUX_BIND_TAC(MATCH_MP RAPROOFAUX_is_Fixed_ok th)) THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SIMP(update_move_related_eqn :: RAPROOFAUX_msimps) THEN
    EXISTS_TAC (CASE_TERM `LUPDATE (~(match EL y (ra_state_node_tag s) with
        Fixed n -> T | _ -> F)) y (LUPDATE (~(match EL x (ra_state_node_tag s) with
        Fixed n -> T | _ -> F)) x (ra_state_move_related s))`) THEN
    SIMP[LENGTH_LUPDATE];
    ALL_TAC] THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ra_state_move_related_fupd (K (mv1:bool list)) s`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC RAPROOFAUX_good_move_related_fupd THEN ASM_REWRITE_TAC[];
      SIMP[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mv2:bool list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `mv2:bool list` THEN ASM_REWRITE_TAC[] THEN
  SIMP[ra_state_component_equality]);;
let reset_move_related_success = prove
 (CASE_TERM `!(ls:(A#num#num)list) s.
     good_ra_state s /\
     ALL (\m. match m with (p,(x,y)) -> x < ra_state_dim s /\ y < ra_state_dim s) ls ==>
     ?mv. reset_move_related ls s = (M_success one,ra_state_move_related_fupd (K mv) s) /\
          LENGTH mv = ra_state_dim s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`)) THEN STRIP_TAC THEN
  REWRITE_TAC[reset_move_related_def] THEN
  SUBGOAL_THEN `(get_dim:ra_state->(num,state_exn)exc#ra_state) s =
                (M_success (ra_state_dim s),s)` RAPROOFAUX_BIND_TAC THENL
   [REWRITE_TAC[get_dim_def]; ALL_TAC] THEN
  MP_TAC(SPECL [`COUNT_LIST (ra_state_dim s)`; `s:ra_state`; `F`]
    st_ex_FOREACH_update_move_related) THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM; MEM_COUNT_LIST] THEN
  DISCH_THEN(X_CHOOSE_THEN `lss:bool list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  MP_TAC(ISPECL [`ls:(A#num#num)list`; `ra_state_move_related_fupd (K (lss:bool list)) s`]
    RAPROOFAUX_reset_move_related_loop) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC RAPROOFAUX_good_move_related_fupd THEN ASM_REWRITE_TAC[];
      SIMP[] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mv:bool list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `mv:bool list` THEN ASM_REWRITE_TAC[] THEN
  SIMP[ra_state_component_equality]);;
(* RAPROOFAUX_STEP_TAC thl: evaluate the first st_ex_bind m f st or         *)
(* st_ex_ignore_bind m f st of the goal whose m st the simplifier (with thl  *)
(* and the assumptions) computes to (M_success x,st'), and rewrite it        *)
let RAPROOFAUX_STEP_TAC (thl:thm list) : tactic = fun (asl,w as g) ->
  let isbind t =
    is_comb t && is_comb(rator t) && is_comb(rator(rator t)) &&
    (let c = rator(rator(rator t)) in
     is_const c && mem (fst(dest_const c)) ["st_ex_bind"; "st_ex_ignore_bind"]) in
  let t = find_term isbind w in
  let m = rand(rator(rator t)) and st = rand t in
  let th = CAKE_SIMP_CONV (thl @ RAPROOFAUX_msimps @ map snd asl) (mk_comb(m,st)) in
  RAPROOFAUX_BIND_TAC th g;;

let do_prefreeze_success = prove
 (`!k s.
     good_ra_state s ==>
     ?s' b. do_prefreeze k s = (M_success b,s') /\
            good_ra_state s' /\
            is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s') /\
            ra_state_dim s = ra_state_dim s' /\
            ra_state_node_tag s = ra_state_node_tag s'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`)) THEN STRIP_TAC THEN
  REWRITE_TAC[do_prefreeze_def] THEN
  RAPROOFAUX_STEP_TAC[get_freeze_wl_def] THEN
  MP_TAC(SPECL [`ra_state_freeze_wl s`; `[]:num list`; `s:ra_state`]
    st_ex_FILTER_is_not_coalesced) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ALL] THEN UNDISCH_TAC `good_ra_state s` THEN SIMP[good_ra_state_def];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_SIMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `fwl:num list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  RAPROOFAUX_STEP_TAC[get_spill_wl_def] THEN
  MP_TAC(SPECL [`ra_state_spill_wl s`; `[]:num list`; `s:ra_state`]
    st_ex_FILTER_is_not_coalesced) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ALL] THEN UNDISCH_TAC `good_ra_state s` THEN SIMP[good_ra_state_def];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_SIMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `swl:num list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  RAPROOFAUX_STEP_TAC[set_spill_wl_def] THEN
  RAPROOFAUX_STEP_TAC[get_unavail_moves_wl_def] THEN
  SUBGOAL_THEN `good_ra_state (ra_state_spill_wl_fupd (K swl) s)` ASSUME_TAC THENL
   [UNDISCH_TAC `good_ra_state s` THEN REWRITE_TAC[good_ra_state_def] THEN SIMP[] THEN
    UNDISCH_TAC `ALL (\x. x < LENGTH (ra_state_coalesced s)) swl` THEN SIMP[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ra_state_unavail_moves_wl s`; `[]:(num#num#num)list`;
    `ra_state_spill_wl_fupd (K (swl:num list)) s`] st_ex_FILTER_consistency_ok) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `good_ra_state s` THEN SIMP[good_ra_state_def];
    ALL_TAC] THEN
  REWRITE_TAC[MEM] THEN
  DISCH_THEN(X_CHOOSE_THEN `uam:(num#num#num)list` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  MP_TAC(ISPECL [`uam:(num#num#num)list`; `ra_state_spill_wl_fupd (K (swl:num list)) s`]
    reset_move_related_success) THEN
  SIMP[] THEN
  DISCH_THEN(X_CHOOSE_THEN `mv:bool list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  RAPROOFAUX_STEP_TAC[set_unavail_moves_wl_def] THEN
  MP_TAC(ISPECL [`fwl:num list`; `[]:num list`; `[]:num list`;
    `ra_state_spill_wl_fupd (K (swl:num list)) (ra_state_unavail_moves_wl_fupd (K uam)
       (ra_state_move_related_fupd (K (mv:bool list)) s))`] st_ex_PARTITION_move_related_sub) THEN
  ANTS_TAC THENL
   [SIMP[] THEN UNDISCH_TAC `ALL (\x. x < LENGTH (ra_state_coalesced s)) fwl` THEN SIMP[];
    ALL_TAC] THEN
  REWRITE_TAC[MEM] THEN
  DISCH_THEN(X_CHOOSE_THEN `tf:num list` (X_CHOOSE_THEN `tsimp:num list` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN REWRITE_TAC[case_def "prod"] THEN
  RAPROOFAUX_STEP_TAC[add_simp_wl_def; get_simp_wl_def; set_simp_wl_def] THEN
  RAPROOFAUX_STEP_TAC[set_freeze_wl_def] THEN
  MP_TAC(SPECL [`k:num`; `ra_state_simp_wl_fupd (K (APPEND tsimp (ra_state_simp_wl s)))
     (ra_state_spill_wl_fupd (K swl)
     (ra_state_freeze_wl_fupd (K tf)
     (ra_state_unavail_moves_wl_fupd (K (uam:(num#num#num)list))
     (ra_state_move_related_fupd (K (mv:bool list)) s))))`] do_simplify_success) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `good_ra_state s` THEN REWRITE_TAC[good_ra_state_def] THEN SIMP[ALL_APPEND] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ALL (\x. MEM x (fwl:num list)) tf` THEN
    UNDISCH_TAC `ALL (\x. MEM x (fwl:num list)) tsimp` THEN
    UNDISCH_TAC `ALL (\x. x < LENGTH (ra_state_coalesced s)) fwl` THEN
    UNDISCH_TAC `ALL (\x. x < LENGTH (ra_state_coalesced s)) swl` THEN
    ASM_REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SIMP[] THEN DISCH_THEN ACCEPT_TAC);;
let RAPROOFAUX_dec_degree_ok = prove
 (`!h s. good_ra_state s ==>
         ?d. dec_degree h s = (M_success one,ra_state_degrees_fupd (K d) s) /\
             LENGTH d = LENGTH (ra_state_degrees s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[dec_degree_def; get_dim_def] THEN SIMP RAPROOFAUX_msimps THEN
  COND_CASES_TAC THENL
   [ALL_TAC;
    SIMP[] THEN EXISTS_TAC `ra_state_degrees s` THEN SIMP[ra_state_component_equality]] THEN
  SUBGOAL_THEN `h < LENGTH (ra_state_adj_ls s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RAPROOFAUX_good_lengths]; ALL_TAC] THEN
  SIMP[] THEN MATCH_MP_TAC dec_deg_success THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `good_ra_state s` THEN REWRITE_TAC[good_ra_state_def; GSYM ALL_EL] THEN
  ASM_MESON_TAC[]);;
(* do freeze *)
let do_freeze_success = prove
 (`!k s.
     good_ra_state s ==>
     ?s' b. do_freeze k s = (M_success b,s') /\
            good_ra_state s' /\
            is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s') /\
            ra_state_dim s = ra_state_dim s' /\
            ra_state_node_tag s = ra_state_node_tag s'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`)) THEN STRIP_TAC THEN
  REWRITE_TAC[do_freeze_def] THEN RAPROOFAUX_STEP_TAC[get_freeze_wl_def] THEN
  SUBGOAL_THEN `ALL (\v. v < ra_state_dim s) (ra_state_freeze_wl s)` MP_TAC THENL
   [UNDISCH_TAC `good_ra_state s` THEN SIMP[good_ra_state_def]; ALL_TAC] THEN
  CASES_ON `ra_state_freeze_wl s` THEN REWRITE_TAC[case_def "list"; ALL] THENL
   [TRY DISCH_TAC THEN REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
    MAP_EVERY EXISTS_TAC [`s:ra_state`; `F`] THEN ASM_REWRITE_TAC[is_subgraph_refl];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`a0:num`; `s:ra_state`] RAPROOFAUX_dec_degree_ok) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  SUBGOAL_THEN `a0 < LENGTH (ra_state_degrees (ra_state_degrees_fupd (K d) s)) /\
                a0 < LENGTH (ra_state_move_related (ra_state_degrees_fupd (K d) s))`
    (fun th -> RAPROOFAUX_BIND_TAC(MATCH_MP RAPROOFAUX_push_stack_ok th)) THENL
   [SIMP[]; ALL_TAC] THEN
  RAPROOFAUX_STEP_TAC[set_freeze_wl_def] THEN
  MP_TAC(SPECL [`k:num`; `ra_state_degrees_fupd (K (LUPDATE 0 a0 d))
     (ra_state_freeze_wl_fupd (K a1)
     (ra_state_move_related_fupd
      (K (LUPDATE F a0 (ra_state_move_related s)))
     (ra_state_stack_fupd (K (CONS a0 (ra_state_stack s))) s)))`] unspill_success) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `good_ra_state s` THEN REWRITE_TAC[good_ra_state_def] THEN
    SIMP[LENGTH_LUPDATE];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_SIMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `s4:ra_state` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
  MAP_EVERY EXISTS_TAC [`s4:ra_state`; `T`] THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN ASM_REWRITE_TAC[]);;
(* do spill *)
let st_ex_list_MIN_cost_success = prove
 (`!ls s k v acc (scost:num spt).
     good_ra_state s /\ ALL (\v. v < ra_state_dim s) acc /\ k < ra_state_dim s ==>
     ?x y. st_ex_list_MIN_cost scost ls (ra_state_dim s) k v acc s = (M_success (x,y),s) /\
           x < ra_state_dim s /\ ALL (\v. v < ra_state_dim s) y`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[st_ex_list_MIN_cost_def] THENL
   [REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`)) THEN STRIP_TAC THEN
  COND_CASES_TAC THENL
   [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `degrees_sub h s = (M_success (EL h (ra_state_degrees s)),s)`
    RAPROOFAUX_BIND_TAC THENL [ASM_REWRITE_TAC[degrees_sub_eqn]; ALL_TAC] THEN
  REWRITE_TAC[RAPROOFAUX_bind_return_left] THEN
  COND_CASES_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ALL]);;

let st_ex_list_MAX_deg_success = prove
 (`!ls s k v acc.
     good_ra_state s /\ ALL (\v. v < ra_state_dim s) acc /\ k < ra_state_dim s ==>
     ?x y. st_ex_list_MAX_deg ls (ra_state_dim s) k v acc s = (M_success (x,y),s) /\
           x < ra_state_dim s /\ ALL (\v. v < ra_state_dim s) y`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[st_ex_list_MAX_deg_def] THENL
   [REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`)) THEN STRIP_TAC THEN
  COND_CASES_TAC THENL
   [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `degrees_sub h s = (M_success (EL h (ra_state_degrees s)),s)`
    RAPROOFAUX_BIND_TAC THENL [ASM_REWRITE_TAC[degrees_sub_eqn]; ALL_TAC] THEN
  COND_CASES_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ALL]);;
let do_spill_success = prove
 (`!scost k s.
     good_ra_state s ==>
     ?s' b. do_spill scost k s = (M_success b,s') /\
            good_ra_state s' /\
            is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s') /\
            ra_state_dim s = ra_state_dim s' /\
            ra_state_node_tag s = ra_state_node_tag s'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`)) THEN STRIP_TAC THEN
  REWRITE_TAC[do_spill_def] THEN RAPROOFAUX_STEP_TAC[get_spill_wl_def] THEN
  RAPROOFAUX_STEP_TAC[get_dim_def] THEN
  SUBGOAL_THEN `ALL (\v. v < ra_state_dim s) (ra_state_spill_wl s)` MP_TAC THENL
   [UNDISCH_TAC `good_ra_state s` THEN SIMP[good_ra_state_def]; ALL_TAC] THEN
  CASES_ON `ra_state_spill_wl s` THEN REWRITE_TAC[case_def "list"; ALL] THENL
   [TRY DISCH_TAC THEN REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
    MAP_EVERY EXISTS_TAC [`s:ra_state`; `F`] THEN ASM_REWRITE_TAC[is_subgraph_refl];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `degrees_sub a0 s = (M_success (EL a0 (ra_state_degrees s)),s)`
    RAPROOFAUX_BIND_TAC THENL [ASM_REWRITE_TAC[degrees_sub_eqn]; ALL_TAC] THEN
  SUBGOAL_THEN (CASE_TERM `?y ys. (match scost with
       NONE -> st_ex_list_MAX_deg a1 (ra_state_dim s) a0 (EL a0 (ra_state_degrees s)) []
     | SOME scost -> st_ex_list_MIN_cost scost a1 (ra_state_dim s) a0
         (safe_div (lookup_any a0 scost 0) (EL a0 (ra_state_degrees s))) []) s =
     (M_success (y,ys),s) /\ y < ra_state_dim s /\ ALL (\v. v < ra_state_dim s) ys`)
    STRIP_ASSUME_TAC THENL
   [CASES_ON `scost:(num spt)option` THEN REWRITE_TAC[case_def "option"] THENL
     [MATCH_MP_TAC st_ex_list_MAX_deg_success; MATCH_MP_TAC st_ex_list_MIN_cost_success] THEN
    ASM_REWRITE_TAC[ALL];
    ALL_TAC] THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN REWRITE_TAC[case_def "prod"] THEN
  MP_TAC(SPECL [`y:num`; `s:ra_state`] RAPROOFAUX_dec_degree_ok) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  SUBGOAL_THEN `y < LENGTH (ra_state_degrees (ra_state_degrees_fupd (K d) s)) /\
                y < LENGTH (ra_state_move_related (ra_state_degrees_fupd (K d) s))`
    (fun th -> RAPROOFAUX_BIND_TAC(MATCH_MP RAPROOFAUX_push_stack_ok th)) THENL
   [SIMP[]; ALL_TAC] THEN
  RAPROOFAUX_STEP_TAC[set_spill_wl_def] THEN
  MP_TAC(SPECL [`k:num`; `ra_state_degrees_fupd (K (LUPDATE 0 y d))
     (ra_state_spill_wl_fupd (K ys)
     (ra_state_move_related_fupd
      (K (LUPDATE F y (ra_state_move_related s)))
     (ra_state_stack_fupd (K (CONS y (ra_state_stack s))) s)))`] unspill_success) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `good_ra_state s` THEN REWRITE_TAC[good_ra_state_def] THEN
    SIMP[LENGTH_LUPDATE];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_SIMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `s4:ra_state` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
  MAP_EVERY EXISTS_TAC [`s4:ra_state`; `T`] THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CAKE_SIMP_RULE[]) THEN ASM_REWRITE_TAC[]);;
let do_step_success = prove
 (`!scost k s.
     good_ra_state s ==>
     ?b s'. do_step scost k s = (M_success b,s') /\
            good_ra_state s' /\
            is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s') /\
            ra_state_dim s = ra_state_dim s' /\
            ra_state_node_tag s = ra_state_node_tag s'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[do_step_def] THEN
  MP_TAC(SPECL [`k:num`; `s:ra_state`] do_simplify_success) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:ra_state` (X_CHOOSE_THEN `b1:bool` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN COND_CASES_TAC THENL
   [(REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
    MAP_EVERY EXISTS_TAC [`b1:bool`; `s1:ra_state`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[is_subgraph_trans]); ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `s1:ra_state`] do_coalesce_success) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:ra_state` (X_CHOOSE_THEN `b2:bool` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN COND_CASES_TAC THENL
   [(REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
    MAP_EVERY EXISTS_TAC [`b2:bool`; `s2:ra_state`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[is_subgraph_trans]); ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `s2:ra_state`] do_prefreeze_success) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:ra_state` (X_CHOOSE_THEN `b3:bool` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN COND_CASES_TAC THENL
   [(REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
    MAP_EVERY EXISTS_TAC [`b3:bool`; `s3:ra_state`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[is_subgraph_trans]); ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `s3:ra_state`] do_freeze_success) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s4:ra_state` (X_CHOOSE_THEN `b4:bool` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN COND_CASES_TAC THENL
   [(REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
    MAP_EVERY EXISTS_TAC [`b4:bool`; `s4:ra_state`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[is_subgraph_trans]); ALL_TAC] THEN
  MP_TAC(SPECL [`scost:(num spt)option`; `k:num`; `s4:ra_state`] do_spill_success) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s5:ra_state` (X_CHOOSE_THEN `b5:bool` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  (REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
    MAP_EVERY EXISTS_TAC [`b5:bool`; `s5:ra_state`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[is_subgraph_trans]));;
(* HOL4 quantifies an unused sc (here of type num) *)
let rpt_do_step_success = prove
 (`!n s k (sc:num) scost.
     good_ra_state s ==>
     ?s'. rpt_do_step scost k n s = (M_success one,s') /\
          good_ra_state s' /\
          is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s') /\
          ra_state_dim s = ra_state_dim s' /\
          ra_state_node_tag s = ra_state_node_tag s'`,
  INDUCT_TAC THEN REWRITE_TAC[rpt_do_step_def] THENL
   [REWRITE_TAC[st_ex_return_def; PAIR_EQ] THEN MESON_TAC[is_subgraph_refl]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`scost:(num spt)option`; `k:num`; `s:ra_state`] do_step_success) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:bool` (X_CHOOSE_THEN `s1:ra_state` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`s1:ra_state`; `k:num`; `sc:num`;
      `scost:(num spt)option`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s2:ra_state` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s2:ra_state` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[is_subgraph_trans];
    REWRITE_TAC[st_ex_return_def; PAIR_EQ] THEN EXISTS_TAC `s1:ra_state` THEN
    ASM_REWRITE_TAC[]]);;
let full_consistency_ok_success = prove
 (`!k x y s.
     good_ra_state s ==>
     ?b. full_consistency_ok k x y s = (M_success b,s) /\
         (b ==> x < ra_state_dim s /\ y < ra_state_dim s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`)) THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[full_consistency_ok_def] THEN COND_CASES_TAC THENL
   [EXISTS_TAC `F` THEN REWRITE_TAC[st_ex_return_def]; ALL_TAC] THEN
  RAPROOFAUX_STEP_TAC[get_dim_def] THEN COND_CASES_TAC THENL
   [EXISTS_TAC `F` THEN REWRITE_TAC[st_ex_return_def]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LE; GE]) THEN
  SIMP(COND_RATOR :: is_Fixed_k_def :: is_Atemp_def :: RAPROOFAUX_msimps) THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ; injectivity "exc"] THEN
  ASM_MESON_TAC[]);;
(* RAPROOFAUX_FILTER_ok2: as RAPROOFAUX_FILTER_ok, with the elements kept   *)
let RAPROOFAUX_FILTER_ok2 = prove
 (`!(P:A->S->(bool,E)exc#S) ls acc s.
     (!x. MEM x ls ==> ?b. P x s = (M_success b,s)) ==>
     ?ts. st_ex_FILTER P ls acc s = (M_success ts,s) /\
          !z. MEM z ts ==> MEM z acc \/ (MEM z ls /\ P z s = (M_success T,s))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[st_ex_FILTER_def; MEM] THENL
   [REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
    REPEAT GEN_TAC THEN EXISTS_TAC `acc:A list` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `h:A`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:bool` ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`CONS (h:A) acc`; `s:S`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`acc:A list`; `s:S`])] THEN
  (ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[MEM] THEN
  GEN_TAC THEN MATCH_MP_TAC(TAUT `(b ==> c) ==> a /\ b ==> a /\ c`) THEN
  UNDISCH_TAC `(P:A->S->(bool,E)exc#S) h s = (M_success b,s)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let st_ex_FILTER_full_consistency_ok = prove
 (CASE_TERM `!k (ls:(A#num#num)list) acc s.
     good_ra_state s ==>
     ?ts. st_ex_FILTER (\m. match m with (_,(x,y)) -> full_consistency_ok k x y) ls acc s =
            (M_success ts,s) /\
          ALL (\m. match m with
                     (p,(x,y)) -> (x < ra_state_dim s /\ y < ra_state_dim s) \/
                                  MEM (p,(x,y)) acc) ts`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [CASE_TERM `\m. match m with (_:A,(x,y)) -> full_consistency_ok k x y`;
                 `ls:(A#num#num)list`; `acc:(A#num#num)list`; `s:ra_state`]
    RAPROOFAUX_FILTER_ok2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; case_def "prod"] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`k:num`; `p1':num`; `p2:num`; `s:ra_state`] full_consistency_ok_success) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `b:bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC(TAUT `(b ==> c) ==> a /\ b ==> a /\ c`) THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; case_def "prod"] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`p1:A`; `p1':num`; `p2:num`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`k:num`; `p1':num`; `p2:num`; `s:ra_state`] full_consistency_ok_success) THEN
  ASM_REWRITE_TAC[PAIR_EQ; injectivity "exc"] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* RAPROOFAUX_init_degrees_loop, RAPROOFAUX_init_coalesced_loop: the two     *)
(* initialisation loops of init_alloc1_heu                                  *)
let RAPROOFAUX_init_degrees_loop = prove
 (`!k ls s.
     good_ra_state s /\ ALL (\v. v < ra_state_dim s) ls ==>
     ?d. st_ex_FOREACH ls
           (\i. st_ex_bind (adj_ls_sub i) (\adjls.
                st_ex_bind (st_ex_FILTER (\v. considered_var k v) adjls []) (\fills.
                update_degrees i (LENGTH fills)))) s =
         (M_success one,ra_state_degrees_fupd (K d) s) /\
         LENGTH d = LENGTH (ra_state_degrees s)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[st_ex_FOREACH_def; st_ex_return_def] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `ra_state_degrees s` THEN SIMP[ra_state_component_equality];
    ALL_TAC] THEN
  REWRITE_TAC[ALL; st_ex_FOREACH_def; ETA_AX] THEN REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `?d1. st_ex_bind (adj_ls_sub h) (\adjls.
                st_ex_bind (st_ex_FILTER (considered_var k) adjls []) (\fills.
                update_degrees h (LENGTH fills))) s =
                (M_success one,ra_state_degrees_fupd (K d1) s) /\
                LENGTH d1 = LENGTH (ra_state_degrees s)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `adj_ls_sub h s = (M_success (EL h (ra_state_adj_ls s)),s)`
      RAPROOFAUX_BIND_TAC THENL [ASM_REWRITE_TAC[adj_ls_sub_eqn]; ALL_TAC] THEN
    MP_TAC(SPECL [`k:num`; `EL h (ra_state_adj_ls s)`; `[]:num list`; `s:ra_state`]
      st_ex_FILTER_considered_var) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ALL] THEN UNDISCH_TAC `good_ra_state s` THEN
      REWRITE_TAC[good_ra_state_def; GSYM ALL_EL] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[EXISTS_SIMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `fl:num list` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
    ASM_REWRITE_TAC[update_degrees_eqn] THEN
    EXISTS_TAC `LUPDATE (LENGTH (fl:num list)) h (ra_state_degrees s)` THEN
    ASM_REWRITE_TAC[LENGTH_LUPDATE];
    ALL_TAC] THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ra_state_degrees_fupd (K (d1:num list)) s`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC RAPROOFAUX_good_degrees_fupd THEN ASM_REWRITE_TAC[]; SIMP[]];
    ALL_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:num list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d2:num list` THEN ASM_REWRITE_TAC[] THEN SIMP[ra_state_component_equality]);;
let RAPROOFAUX_init_coalesced_loop = prove
 (`!ls s.
     good_ra_state s /\ ALL (\v. v < ra_state_dim s) ls ==>
     ?c. st_ex_FOREACH ls do_upd_coalesce s =
           (M_success one,ra_state_coalesced_fupd (K c) s) /\
         good_ra_state (ra_state_coalesced_fupd (K c) s)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[st_ex_FOREACH_def; st_ex_return_def] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `ra_state_coalesced s` THEN
    SUBGOAL_THEN `ra_state_coalesced_fupd (K (ra_state_coalesced s)) s = s` SUBST1_TAC THENL
     [SIMP[ra_state_component_equality]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[ALL; st_ex_FOREACH_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `do_upd_coalesce h s = (M_success one,
     ra_state_coalesced_fupd (K (LUPDATE h h (ra_state_coalesced s))) s)`
    RAPROOFAUX_BIND_TAC THENL
   [ASM_REWRITE_TAC[do_upd_coalesce_def; update_coalesced_eqn; ADD_CLAUSES]; ALL_TAC] THEN
  SUBGOAL_THEN `good_ra_state (ra_state_coalesced_fupd (K (LUPDATE h h (ra_state_coalesced s))) s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RAPROOFAUX_good_coalesced_fupd THEN ASM_REWRITE_TAC[LENGTH_LUPDATE] THEN
    MATCH_MP_TAC IMP_EVERY_LUPDATE THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `good_ra_state s` THEN SIMP[good_ra_state_def];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `ra_state_coalesced_fupd (K (LUPDATE h h (ra_state_coalesced s))) s`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMP[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:num list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c2:num list` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [SIMP[ra_state_component_equality]; ALL_TAC] THEN
  UNDISCH_TAC `good_ra_state (ra_state_coalesced_fupd (K (c2:num list))
     (ra_state_coalesced_fupd (K (LUPDATE h h (ra_state_coalesced s))) s))` THEN
  SIMP[]);;
let RAPROOFAUX_is_Atemp_ok = prove
 (`!x s. x < LENGTH (ra_state_node_tag s) ==>
         ?b. is_Atemp x s = (M_success b,s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[is_Atemp_def] THEN SIMP RAPROOFAUX_msimps THEN MESON_TAC[]);;
(* RAPROOFAUX_init_alloc1_heu_ok: the initialisation of do_alloc1 *)
let RAPROOFAUX_init_alloc1_heu_ok = prove
 ((CASE_TERM `!s moves k.
     good_ra_state s /\
     ALL (\m. match m with (p:num,x,y) -> x < ra_state_dim s /\ y < ra_state_dim s) moves ==>
     ?l s'. init_alloc1_heu moves (ra_state_dim s) k s = (M_success l,s') /\
            good_ra_state s' /\
            ra_state_adj_ls s' = ra_state_adj_ls s /\
            ra_state_dim s' = ra_state_dim s /\
            ra_state_node_tag s' = ra_state_node_tag s`),
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s`)) THEN STRIP_TAC THEN
  REWRITE_TAC[init_alloc1_heu_def; RAPROOFAUX_bind_return_left] THEN
  MP_TAC(ISPECL [`is_Atemp`; `COUNT_LIST (ra_state_dim s)`; `[]:num list`; `s:ra_state`]
    RAPROOFAUX_FILTER_ok) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MEM_COUNT_LIST] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RAPROOFAUX_is_Atemp_ok THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MEM_COUNT_LIST; MEM] THEN
  DISCH_THEN(X_CHOOSE_THEN `atemps:num list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  MP_TAC(SPECL [`k:num`; `COUNT_LIST (ra_state_dim s)`; `s:ra_state`]
    RAPROOFAUX_init_degrees_loop) THEN
  ASM_REWRITE_TAC[GSYM ALL_MEM; MEM_COUNT_LIST] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:num list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  MP_TAC(SPECL [`COUNT_LIST (ra_state_dim s)`; `ra_state_degrees_fupd (K (d1:num list)) s`]
    RAPROOFAUX_init_coalesced_loop) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC RAPROOFAUX_good_degrees_fupd THEN ASM_REWRITE_TAC[];
      SIMP[GSYM ALL_MEM; MEM_COUNT_LIST]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:num list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  RAPROOFAUX_STEP_TAC[set_avail_moves_wl_def] THEN
  SUBGOAL_THEN `good_ra_state (ra_state_degrees_fupd (K (d1:num list))
     (ra_state_avail_moves_wl_fupd (K (reg_alloc_sort_moves (moves:(num#num#num)list)))
     (ra_state_coalesced_fupd (K (c1:num list)) s)))` ASSUME_TAC THENL
   [UNDISCH_TAC `good_ra_state (ra_state_coalesced_fupd (K (c1:num list))
       (ra_state_degrees_fupd (K (d1:num list)) s))` THEN
    REWRITE_TAC[good_ra_state_def] THEN SIMP[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC (CASE_TERM `ALL (\m. match m with (p:num,x,y) ->
      x < ra_state_dim s /\ y < ra_state_dim s) moves`) THEN
    REWRITE_TAC[GSYM ALL_MEM; reg_alloc_sort_moves_def; sort_MEM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moves:(num#num#num)list`; `ra_state_degrees_fupd (K (d1:num list))
     (ra_state_avail_moves_wl_fupd (K (reg_alloc_sort_moves (moves:(num#num#num)list)))
     (ra_state_coalesced_fupd (K (c1:num list)) s))`] reset_move_related_success) THEN
  SIMP[] THEN
  DISCH_THEN(X_CHOOSE_THEN `mv:bool list` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  SUBGOAL_THEN `good_ra_state (ra_state_degrees_fupd (K (d1:num list))
     (ra_state_avail_moves_wl_fupd (K (reg_alloc_sort_moves (moves:(num#num#num)list)))
     (ra_state_coalesced_fupd (K (c1:num list))
       (ra_state_move_related_fupd (K (mv:bool list)) s))))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `good_ra_state (ra_state_degrees_fupd (K (d1:num list))
     (ra_state_avail_moves_wl_fupd (K (reg_alloc_sort_moves (moves:(num#num#num)list)))
     (ra_state_coalesced_fupd (K (c1:num list)) s)))` THEN
    REWRITE_TAC[good_ra_state_def] THEN SIMP[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`atemps:num list`; `k:num`; `[]:num list`; `[]:num list`;
    `ra_state_degrees_fupd (K (d1:num list))
     (ra_state_avail_moves_wl_fupd (K (reg_alloc_sort_moves (moves:(num#num#num)list)))
     (ra_state_coalesced_fupd (K (c1:num list))
       (ra_state_move_related_fupd (K (mv:bool list)) s)))`]
    st_ex_PARTITION_split_degree) THEN
  ASM_REWRITE_TAC[MEM] THEN SIMP[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ltk:num list` (X_CHOOSE_THEN `gtk:num list` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN REWRITE_TAC[case_def "prod"] THEN
  MP_TAC(SPECL [`ltk:num list`; `[]:num list`; `[]:num list`;
    `ra_state_degrees_fupd (K (d1:num list))
     (ra_state_avail_moves_wl_fupd (K (reg_alloc_sort_moves (moves:(num#num#num)list)))
     (ra_state_coalesced_fupd (K (c1:num list))
       (ra_state_move_related_fupd (K (mv:bool list)) s)))`]
    st_ex_PARTITION_move_related_sub) THEN
  ANTS_TAC THENL
   [SIMP[] THEN UNDISCH_TAC `ALL (\x. MEM x (atemps:num list)) ltk` THEN
    UNDISCH_TAC `!z. MEM z (atemps:num list) ==> z < ra_state_dim s` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MEM] THEN
  DISCH_THEN(X_CHOOSE_THEN `tf:num list` (X_CHOOSE_THEN `tsimp:num list` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN REWRITE_TAC[case_def "prod"] THEN
  RAPROOFAUX_STEP_TAC[set_spill_wl_def] THEN RAPROOFAUX_STEP_TAC[set_simp_wl_def] THEN
  RAPROOFAUX_STEP_TAC[set_freeze_wl_def] THEN
  REWRITE_TAC[st_ex_return_def; PAIR_EQ; injectivity "exc"] THEN
  SIMP[] THEN
  UNDISCH_TAC `good_ra_state (ra_state_degrees_fupd (K (d1:num list))
     (ra_state_avail_moves_wl_fupd (K (reg_alloc_sort_moves (moves:(num#num#num)list)))
     (ra_state_coalesced_fupd (K (c1:num list))
       (ra_state_move_related_fupd (K (mv:bool list)) s))))` THEN
  REWRITE_TAC[good_ra_state_def] THEN SIMP[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ALL (\x. MEM x (atemps:num list)) ltk` THEN
  UNDISCH_TAC `ALL (\x. MEM x (atemps:num list)) gtk` THEN
  UNDISCH_TAC `ALL (\x. MEM x (ltk:num list)) tf` THEN
  UNDISCH_TAC `ALL (\x. MEM x (ltk:num list)) tsimp` THEN
  UNDISCH_TAC `!z. MEM z (atemps:num list) ==> z < ra_state_dim s` THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[]);;
let do_alloc1_success = prove
 (CASE_TERM `!s moves scost k.
     good_ra_state s /\
     ALL (\m. match m with (p:num,x,y) -> x < ra_state_dim s /\ y < ra_state_dim s) moves ==>
     ?ls s'. do_alloc1 moves scost k s = (M_success ls,s') /\
             good_ra_state s' /\
             is_subgraph (ra_state_adj_ls s) (ra_state_adj_ls s') /\
             ra_state_dim s' = ra_state_dim s /\
             ra_state_node_tag s' = ra_state_node_tag s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[do_alloc1_def] THEN RAPROOFAUX_STEP_TAC[get_dim_def] THEN
  MP_TAC(SPECL [`s:ra_state`; `moves:(num#num#num)list`; `k:num`]
    RAPROOFAUX_init_alloc1_heu_ok) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` (X_CHOOSE_THEN `s1:ra_state` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  MP_TAC(SPECL [`l:num`; `s1:ra_state`; `k:num`; `0`; `scost:(num spt)option`]
    rpt_do_step_success) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:ra_state` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN
  REWRITE_TAC[reg_alloc_get_stack_def] THEN SIMP RAPROOFAUX_msimps THEN
  ASM_MESON_TAC[]);;

let no_clash_colouring_satisfactory = prove
 (`!adjls node_tag.
     no_clash adjls node_tag /\ LENGTH adjls = LENGTH node_tag /\
     ALL (\n. ~(n = Stemp) /\ ~(n = Atemp)) node_tag ==>
     colouring_satisfactory
       (\f. if f < LENGTH node_tag then extract_tag (EL f node_tag) else 0) adjls`,
  REWRITE_TAC[no_clash_def; colouring_satisfactory_def; has_edge_def; GSYM ALL_EL] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `y:num`] o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:num`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:num`) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) && is_cond(lhs(concl th)))) THEN
  SUBGOAL_THEN `x < LENGTH (node_tag:reg_alloc_tag list) /\ y < LENGTH node_tag`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `EL x (node_tag:reg_alloc_tag list)` THEN
  CASES_ON `EL y (node_tag:reg_alloc_tag list)` THEN
  REWRITE_TAC[extract_tag_def; case_def "reg_alloc_tag"; distinctness "reg_alloc_tag"] THEN
  MESON_TAC[]);;

let check_partial_col_same_dom = prove
 (`!ls f g (t:1 spt) (ft:1 spt).
     (!x. MEM x ls ==> f x = g x) ==>
     check_partial_col f ls t ft = check_partial_col g ls t ft`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[check_partial_col_def; MEM] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:num->num) h = g h` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!(u:1 spt) (fu:1 spt). check_partial_col f t u fu = check_partial_col g t u fu`
    (fun th -> REWRITE_TAC[th]) THEN
  REPEAT GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;
let check_clash_tree_same_dom = prove
 (`!ct f g (live:1 spt) (flive:1 spt).
     (!x. in_clash_tree ct x \/ x IN domain live ==> f x = g x) ==>
     check_clash_tree f ct live flive = check_clash_tree g ct live flive`,
  MATCH_MP_TAC clash_tree_INDUCT THEN
  REWRITE_TAC[in_clash_tree_def; check_clash_tree_def] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `check_partial_col f a0 live flive = check_partial_col g a0 live flive /\
                  MAP (f:num->num) a0 = MAP g a0 /\
                  (!u fu. check_partial_col f a1 u fu = check_partial_col g a1 u fu)`
      STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC check_partial_col_same_dom THEN ASM_MESON_TAC[];
        REWRITE_TAC[MAP_EQ_f] THEN ASM_MESON_TAC[];
        REPEAT GEN_TAC THEN MATCH_MP_TAC check_partial_col_same_dom THEN ASM_MESON_TAC[]];
      ASM_REWRITE_TAC[]];
    DISCH_TAC THEN REWRITE_TAC[check_col_def; LET_DEF; LET_END_DEF] THEN
    SUBGOAL_THEN `MAP ((f:num->num) o FST) (toAList (a:1 spt)) = MAP (g o FST) (toAList a)`
      (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[MAP_EQ_f; FORALL_PAIR_THM; o_THM; MEM_toAList] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[];
    (DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `check_clash_tree f a1 live flive = check_clash_tree g a1 live flive /\
                check_clash_tree f a2 live flive = check_clash_tree g a2 live flive`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL [USE_THEN "ih1" MATCH_MP_TAC; USE_THEN "ih2" MATCH_MP_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  CASES_ON `check_clash_tree g a1 live flive` THEN REWRITE_TAC[case_def "option"] THEN
  CASES_ON `check_clash_tree g a2 live flive` THEN REWRITE_TAC[case_def "option"] THEN
  MP_TAC(ISPEC `a:1 spt#1 spt` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:1 spt` (X_CHOOSE_THEN `fl1:1 spt` SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `a':1 spt#1 spt` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l2:1 spt` (X_CHOOSE_THEN `fl2:1 spt` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[case_def "prod"] THEN
  CASES_ON `a0:(1 spt)option` THEN REWRITE_TAC[case_def "option"] THENL
   [MATCH_MP_TAC check_partial_col_same_dom THEN
    REWRITE_TAC[toAList_domain; domain_difference; IN_DIFF] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP check_clash_tree_domain o check (fun th ->
      concl th = `check_clash_tree g a2 live flive = SOME (l2:1 spt,fl2:1 spt)`)) THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[check_col_def; LET_DEF; LET_END_DEF] THEN
    SUBGOAL_THEN `MAP ((f:num->num) o FST) (toAList (a'':1 spt)) = MAP (g o FST) (toAList a'')`
      (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[MAP_EQ_f; FORALL_PAIR_THM; o_THM; MEM_toAList] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[domain_lookup; case_def "option"] THEN ASM_MESON_TAC[]]);
    (DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `check_clash_tree f a1 live flive = check_clash_tree g a1 live flive`
    SUBST1_TAC THENL
   [USE_THEN "ih2" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `check_clash_tree g a1 live flive` THEN REWRITE_TAC[case_def "option"] THEN
  MP_TAC(ISPEC `a:1 spt#1 spt` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l2:1 spt` (X_CHOOSE_THEN `fl2:1 spt` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[case_def "prod"] THEN USE_THEN "ih1" MATCH_MP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP check_clash_tree_domain o check (fun th ->
    concl th = `check_clash_tree g a1 live flive = SOME (l2:1 spt,fl2:1 spt)`)) THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN ASM_MESON_TAC[])]);;
let opt_split = prove
 (`!a:1 option. ~(a = NONE) <=> a = SOME one`,
  GEN_TAC THEN CASES_ON `a:1 option` THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  ONCE_REWRITE_TAC[one] THEN REWRITE_TAC[]);;

let INJ_IMG_lookup = prove
 (`!x (g:num->num) (gt:1 spt) (ft:1 spt).
     INJ g UNIV UNIV /\ domain gt = IMAGE g (domain ft) ==>
     lookup (g x) gt = lookup x ft`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INJ; IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:num->num) x IN domain (gt:1 spt) <=> x IN domain (ft:1 spt)` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[domain_lookup] THEN
  CASES_ON `lookup ((g:num->num) x) (gt:1 spt)` THEN
  CASES_ON `lookup (x:num) (ft:1 spt)` THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  ONCE_REWRITE_TAC[one] THEN MESON_TAC[]);;
(* HOL4: check_partial_col_INJ (f and g free in HOL4) *)
let reg_allocProof_check_partial_col_INJ = prove
 ((CASE_TERM `!ls (t:1 spt) (ft:1 spt) (gt:1 spt) (f:num->num) (g:num->num).
     INJ g UNIV UNIV /\ domain gt = IMAGE g (domain ft) ==>
     match check_partial_col f ls t ft with
       NONE -> check_partial_col (g o f) ls t gt = NONE
     | SOME (tt,ftt) -> ?gtt. check_partial_col (g o f) ls t gt = SOME (tt,gtt) /\
                              domain gtt = IMAGE g (domain ftt)`),
  LIST_INDUCT_TAC THEN REWRITE_TAC[check_partial_col_def; case_def "option"; case_def "prod"] THENL
  [(REPEAT STRIP_TAC THEN EXISTS_TAC `gt:1 spt` THEN ASM_REWRITE_TAC[]);
   (REPEAT STRIP_TAC THEN
  CASES_ON `lookup (h:num) (t':1 spt)` THEN REWRITE_TAC[case_def "option"]) THENL
   [(REWRITE_TAC[o_THM] THEN
  MP_TAC(SPECL [`(f:num->num) h`; `g:num->num`; `gt:1 spt`; `ft:1 spt`] INJ_IMG_lookup) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CASES_ON `lookup ((f:num->num) h) (ft:1 spt)` THEN REWRITE_TAC[case_def "option"] THEN

  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[domain_insert; IMAGE_CLAUSES; o_THM]);
    (FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[])]]);;
(* HOL4: check_col_INJ *)
let reg_allocProof_check_col_INJ = prove
 (CASE_TERM `!(f:num->num) (g:num->num) (s:1 spt).
     INJ g UNIV UNIV ==>
     match check_col f s with
       NONE -> check_col (g o f) s = NONE
     | SOME (t,ft) -> ?gt. check_col (g o f) s = SOME (t,gt) /\
                           domain gt = IMAGE g (domain ft)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[check_col_def; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP (((g:num->num) o f) o FST) (toAList (s:1 spt))) <=>
                ALL_DISTINCT (MAP (f o FST) (toAList s))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM o_ASSOC; GSYM MAP_MAP_o] THEN EQ_TAC THENL
     [MESON_TAC[ALL_DISTINCT_MAP];
      DISCH_TAC THEN MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `INJ (g:num->num) UNIV UNIV` THEN REWRITE_TAC[INJ; IN_UNIV] THEN MESON_TAC[]];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[case_def "option"; case_def "prod"] THEN
  TRY(EXISTS_TAC
        `fromAList (MAP (\x. x,one) (MAP (((g:num->num) o f) o FST) (toAList (s:1 spt))))`) THEN
  REWRITE_TAC[domain_fromAList; MAP_MAP_o; LIST_TO_SET_MAP; GSYM IMAGE_o] THEN
  REWRITE_TAC[o_DEF]);;
(* RAPROOFAUX_IH_TAC lab args: add the instance of the labelled induction  *)
(* hypothesis whose two antecedents are assumptions                        *)
let RAPROOFAUX_IH_TAC (lab:string) (args:term list) : tactic =
  USE_THEN lab (fun ih -> FIRST_ASSUM(fun inj -> FIRST_ASSUM(fun dom ->
    ASSUME_TAC(MATCH_MP (SPECL args ih) (CONJ inj dom)))));;
(* HOL4: check_clash_tree_INJ (f and g are free in HOL4) *)
let check_clash_tree_INJ = prove
 ((CASE_TERM `!ct (f:num->num) (g:num->num) (live:1 spt) (flive:1 spt) (glive:1 spt).
     INJ g UNIV UNIV /\ domain glive = IMAGE g (domain flive) ==>
     match check_clash_tree f ct live flive with
       NONE -> check_clash_tree (g o f) ct live glive = NONE
     | SOME (liveout,fliveout) ->
         ?gliveout. check_clash_tree (g o f) ct live glive = SOME (liveout,gliveout) /\
                    domain gliveout = IMAGE g (domain fliveout)`),
  MATCH_MP_TAC clash_tree_INDUCT THEN REWRITE_TAC[check_clash_tree_def] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(SPECL [`a0:num list`; `live:1 spt`; `flive:1 spt`; `glive:1 spt`; `f:num->num`;
      `g:num->num`] reg_allocProof_check_partial_col_INJ) THEN ASM_REWRITE_TAC[] THEN
    CASES_ON `check_partial_col f a0 live flive` THEN REWRITE_TAC[case_def "option"] THENL
     [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[case_def "option"]; ALL_TAC] THEN
    MP_TAC(ISPEC `a:1 spt#1 spt` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `tt:1 spt` (X_CHOOSE_THEN `ftt:1 spt` SUBST1_TAC)) THEN
    REWRITE_TAC[case_def "prod"] THEN
    DISCH_THEN(X_CHOOSE_THEN `gtt:1 spt` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[case_def "option"; LET_DEF; LET_END_DEF] THEN
    MATCH_MP_TAC reg_allocProof_check_partial_col_INJ THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[reg_allocProof_domain_numset_list_delete; LIST_TO_SET_MAP; IMAGE_o] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC reg_allocProof_IMAGE_DIFF THEN
    UNDISCH_TAC `INJ (g:num->num) UNIV UNIV` THEN REWRITE_TAC[INJ; IN_UNIV] THEN MESON_TAC[];
    STRIP_TAC THEN MATCH_MP_TAC reg_allocProof_check_col_INJ THEN ASM_REWRITE_TAC[];
    (DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RAPROOFAUX_IH_TAC "ih1" [`f:num->num`; `g:num->num`; `live:1 spt`; `flive:1 spt`;
    `glive:1 spt`] THEN
  RAPROOFAUX_IH_TAC "ih2" [`f:num->num`; `g:num->num`; `live:1 spt`; `flive:1 spt`;
    `glive:1 spt`] THEN
  CASES_ON `check_clash_tree f a1 live flive` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "option"]) THEN ASM_REWRITE_TAC[case_def "option"] THEN
     MP_TAC(ISPEC `a:1 spt#1 spt` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t1o:1 spt` (X_CHOOSE_THEN `ft1o:1 spt` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "prod"]) THEN REWRITE_TAC[case_def "prod"] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `gt1:1 spt` STRIP_ASSUME_TAC o check (is_exists o concl)) THEN
  ASM_REWRITE_TAC[case_def "option"; case_def "prod"] THEN
  CASES_ON `check_clash_tree f a2 live flive` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "option"]) THEN ASM_REWRITE_TAC[case_def "option"] THEN
  MP_TAC(ISPEC `a':1 spt#1 spt` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t2o:1 spt` (X_CHOOSE_THEN `ft2o:1 spt` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "prod"]) THEN REWRITE_TAC[case_def "prod"] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `gt2:1 spt` STRIP_ASSUME_TAC o check (is_exists o concl)) THEN
  ASM_REWRITE_TAC[case_def "option"; case_def "prod"] THEN
  CASES_ON `a0:(1 spt)option` THEN REWRITE_TAC[case_def "option"] THENL
   [MATCH_MP_TAC reg_allocProof_check_partial_col_INJ THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC reg_allocProof_check_col_INJ THEN ASM_REWRITE_TAC[]]);
    (DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RAPROOFAUX_IH_TAC "ih2" [`f:num->num`; `g:num->num`; `live:1 spt`; `flive:1 spt`;
    `glive:1 spt`] THEN
  CASES_ON `check_clash_tree f a1 live flive` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "option"]) THEN ASM_REWRITE_TAC[case_def "option"] THEN
  MP_TAC(ISPEC `a:1 spt#1 spt` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t2o:1 spt` (X_CHOOSE_THEN `ft2o:1 spt` SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[case_def "prod"]) THEN REWRITE_TAC[case_def "prod"] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `gt2:1 spt` STRIP_ASSUME_TAC o check (is_exists o concl)) THEN
  ASM_REWRITE_TAC[case_def "option"; case_def "prod"] THEN
  USE_THEN "ih1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[])]);;

let neg_first_match_col_correct = prove
 (CASE_TERM `!x k ks s. ?res. neg_first_match_col k ks x s = (res,s) /\
     match res with
       M_failure v -> v = Subscript
     | M_success (SOME c) -> ~MEM c ks /\ k <= c
     | _ -> T`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[neg_first_match_col_def] THEN SIMP RAPROOFAUX_msimps THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN SIMP[] THEN
  CASES_ON `EL h (ra_state_node_tag s)` THEN SIMP[] THEN TRY COND_CASES_TAC THEN SIMP[] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[DE_MORGAN_THM; NOT_LT] THEN SIMP_TAC[]);;
let good_neg_pref_neg_biased_pref = prove
 (`!k t. good_neg_pref k (neg_biased_pref k t)`,
  REWRITE_TAC[good_neg_pref_def; neg_biased_pref_def; get_dim_def] THEN
  SIMP RAPROOFAUX_msimps THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN SIMP[] THEN
  SIMP[LET_DEF; LET_END_DEF; reg_alloc_handle_Subscript_def] THEN
  MP_TAC(ISPECL [CASE_TERM `match lookup n (t:(num list)spt) with NONE -> [] | SOME vs -> vs`;
                 `k:num`; `bads:num list`; `s:ra_state`] neg_first_match_col_correct) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
  CASES_ON `res:(num option,state_exn)exc` THEN SIMP[] THEN
  TRY(CASES_ON `a:num option`) THEN SIMP[]);;
let RAPROOFAUX_mk_bij_props = prove
 (`!ct ta fa n.
     mk_bij ct = (ta,fa,n) ==>
     mk_bij_aux ct (LN,LN,0) = (ta,fa,n) /\
     domain ta = {x | in_clash_tree ct x} /\ sp_inverts ta fa /\ sp_inverts fa ta /\
     domain fa = count n /\ wf ta /\ wf fa`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mk_bij_def] THEN
  RAPROOFAUX_TRIPLE_TAC `mk_bij_aux ct (LN,LN,0)` `ta1:num spt` `fa1:num spt` `n1:num` THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP mk_bij_aux_domain) THEN
  REWRITE_TAC[domain_def; UNION_EMPTY] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ct:clash_tree`; `LN:num spt`; `LN:num spt`; `0`;
                 `ta:num spt`; `fa:num spt`; `n:num`] RAPROOFAUX_mk_bij_aux_bij) THEN
  MP_TAC(ISPECL [`ct:clash_tree`; `LN:num spt`; `LN:num spt`; `0`;
                 `ta:num spt`; `fa:num spt`; `n:num`] mk_bij_aux_wf) THEN
  ASM_REWRITE_TAC[marker_Abbrev_def; wf_def; sp_inverts_def; lookup_def; domain_def;
                  COUNT_ZERO] THEN
  SIMP[]);;
let RAPROOFAUX_mk_tags_no_clash = prove
 (CASE_TERM `!adjls tags (fa:num spt) (ta:num spt) n.
     LENGTH (adjls:(num list)list) = n /\ sp_inverts fa ta /\ domain fa = count n /\
     (!x y. x < n /\ y = sp_default fa x ==>
        (if is_phy_var y then EL x tags = Fixed (y DIV 2)
         else if is_stack_var y then EL x tags = Stemp
         else EL x tags = Atemp \/ EL x tags = Stemp)) ==>
     no_clash adjls tags`,
  REWRITE_TAC[no_clash_def; has_edge_def] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl)) THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?u. lookup x (fa:num spt) = SOME u` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM domain_lookup] THEN ASM_REWRITE_TAC[IN_COUNT]; ALL_TAC] THEN
  SUBGOAL_THEN `?v. lookup y (fa:num spt) = SOME v` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM domain_lookup] THEN ASM_REWRITE_TAC[IN_COUNT]; ALL_TAC] THEN
  SUBGOAL_THEN `sp_default fa x = u /\ sp_default fa y = v` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[sp_default_def] THEN SIMP[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:num`; `u:num`] o check (is_forall o concl)) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`y:num`; `v:num`] o check (is_forall o concl)) THEN
  REWRITE_TAC[ASSUME `x < LENGTH (adjls:(num list)list)`;
              ASSUME `y < LENGTH (adjls:(num list)list)`;
              ASSUME `sp_default fa x = u`; ASSUME `sp_default fa y = v`] THEN
  ASM_CASES_TAC `is_phy_var u` THEN ASM_CASES_TAC `is_phy_var v` THEN ASM_REWRITE_TAC[] THENL
   [REPEAT(DISCH_THEN SUBST1_TAC) THEN SIMP[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `u:num = v` SUBST_ALL_TAC THENL
     [MP_TAC(SPECL [`u:num`; `2`] (CONJUNCT2 DIVISION_SIMP)) THEN
      MP_TAC(SPECL [`v:num`; `2`] (CONJUNCT2 DIVISION_SIMP)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[is_phy_var_def]) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `sp_inverts fa ta` THEN REWRITE_TAC[sp_inverts_def] THEN
    DISCH_THEN(fun th -> MP_TAC(MATCH_MP th (ASSUME `lookup x (fa:num spt) = SOME v`)) THEN
                         MP_TAC(MATCH_MP th (ASSUME `lookup y (fa:num spt) = SOME v`))) THEN
    DISCH_THEN SUBST1_TAC THEN SIMP[];
    ALL_TAC; ALL_TAC; ALL_TAC] THEN
  REPEAT COND_CASES_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[]);;

let do_reg_alloc_correct = prove
 (CASE_TERM `!alg scost k moves ct forced fs st ta fa n.
     mk_bij ct = (ta,fa,n) ==>
     ra_state_adj_ls st = REPLICATE n [] ==>
     ra_state_node_tag st = REPLICATE n Atemp ==>
     ra_state_degrees st = REPLICATE n 0 ==>
     ra_state_dim st = n ==>
     ra_state_simp_wl st = [] ==>
     ra_state_spill_wl st = [] ==>
     ra_state_freeze_wl st = [] ==>
     ra_state_avail_moves_wl st = [] ==>
     ra_state_unavail_moves_wl st = [] ==>
     ra_state_coalesced st = REPLICATE n 0 ==>
     ra_state_move_related st = REPLICATE n F ==>
     ALL (\p. match p with (x,y) -> in_clash_tree ct x /\ in_clash_tree ct y) forced ==>
     ?spcol st' livein flivein.
       do_reg_alloc alg scost k moves ct forced fs (ta,fa,n) st = (M_success spcol,st') /\
       check_clash_tree (sp_default spcol) ct LN LN = SOME(livein,flivein) /\
       (!x. in_clash_tree ct x ==>
            x IN domain spcol /\
            (if is_phy_var x then sp_default spcol x = x DIV 2
             else if is_stack_var x then k <= sp_default spcol x
             else T)) /\
       (!x. x IN domain spcol ==> in_clash_tree ct x) /\
       ALL (\p. match p with (x,y) -> sp_default spcol x = sp_default spcol y ==> x = y)
         forced`,
  (REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP RAPROOFAUX_mk_bij_props) THEN
  STRIP_TAC THEN REPEAT DISCH_TAC) THEN
  (* the bijection ta, fa between the clash tree variables and count n *)
  (SUBGOAL_THEN `!x. in_clash_tree ct x ==>
       ?y. lookup x (ta:num spt) = SOME y /\ lookup y (fa:num spt) = SOME x /\ y < n`
     (LABEL_TAC "A1") THENL
   [X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?y. lookup x (ta:num spt) = SOME y` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM domain_lookup] THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    EXISTS_TAC `y:num` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `lookup y (fa:num spt) = SOME x` ASSUME_TAC THENL
     [ASM_MESON_TAC[sp_inverts_def]; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM IN_COUNT] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `count n`)) THEN
    REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
  (* the initial state is good *)
  (SUBGOAL_THEN `good_ra_state st` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[good_ra_state_def; LENGTH_REPLICATE; ALL; undirected_def; has_edge_def] THEN
    REWRITE_TAC[GSYM ALL_EL; LENGTH_REPLICATE] THEN
    SIMP[EL_REPLICATE; MEM; SORTED_DEF; ALL] THEN REPEAT CONJ_TAC THENL
     [ARITH_TAC; ARITH_TAC;
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      UNDISCH_TAC `MEM (y:num) (EL x (REPLICATE n ([]:num list)))` THEN
      ASM_SIMP_TAC[EL_REPLICATE; MEM]]; ALL_TAC]) THEN
  (SUBGOAL_THEN `!x y. in_clash_tree ct x /\ in_clash_tree ct y /\
                       sp_default ta x = sp_default ta y ==> x = y`
     (LABEL_TAC "INJ1") THENL
   [MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
    USE_THEN "A1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `in_clash_tree ct x`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "A1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `in_clash_tree ct y`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `sp_default ta x = sp_default ta y` THEN
    REWRITE_TAC[sp_default_def] THEN ASM_REWRITE_TAC[] THEN SIMP[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `lookup v (fa:num spt) = SOME x` THEN ASM_REWRITE_TAC[] THEN
    SIMP[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. in_clash_tree ct x ==> sp_default ta x < n` (LABEL_TAC "BND") THENL
   [X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    USE_THEN "A1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `in_clash_tree ct x`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[sp_default_def] THEN SIMP[] THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (* init_ra_state: mk_graph, extend_graph, mk_tags *)
  (MP_TAC(ISPECL [`ct:clash_tree`; `sp_default ta`; `[]:num list`; `st:ra_state`]
     mk_graph_succeeds) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[is_clique_def; MEM; ALL_DISTINCT; ALL; LENGTH_REPLICATE] THEN
    ASM_REWRITE_TAC[INJ; IN_ELIM_THM; IN_COUNT] THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `gl:num list` (X_CHOOSE_THEN `s1:ra_state` STRIP_ASSUME_TAC))] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls])) THEN
  (MP_TAC(ISPECL [`forced:(num#num)list`; `sp_default ta`; `s1:ra_state`]
     extend_graph_succeeds) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC (CASE_TERM `ALL (\p. match p with (x,y) -> in_clash_tree ct x /\ in_clash_tree ct y)
      (forced:(num#num)list)`) THEN
    MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN SIMP[] THEN
    ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `s2:ra_state` STRIP_ASSUME_TAC)] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_adj_ls]) THEN
  FIRST_X_ASSUM(LABEL_TAC "EG" o
    check (fun th -> is_forall (concl th) && free_in `s2:ra_state` (concl th)))) THEN
  (MP_TAC(ISPECL [`s2:ra_state`; `n:num`; `fs:1 spt`; `sp_default fa`] mk_tags_succeeds) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `s3:ra_state` STRIP_ASSUME_TAC)] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_node_tag]) THEN
  FIRST_X_ASSUM(LABEL_TAC "MT" o
    check (fun th -> is_forall (concl th) && free_in `s3:ra_state` (concl th)))) THEN
  (SUBGOAL_THEN `init_ra_state ct forced fs (ta,fa,n) st = (M_success one,s3)` ASSUME_TAC THENL
   [REWRITE_TAC[init_ra_state_def] THEN
    RAPROOFAUX_BIND_TAC (ASSUME `mk_graph (sp_default ta) ct [] st = (M_success gl,s1)`) THEN
    RAPROOFAUX_BIND_TAC
      (ASSUME `extend_graph (sp_default ta) forced s1 = (M_success one,s2)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (* the steps of do_reg_alloc *)
  (REWRITE_TAC[do_reg_alloc_def] THEN
   RAPROOFAUX_BIND_TAC
     (ASSUME `init_ra_state ct forced fs (ta,fa,n) st = (M_success one,s3)`) THEN
   REWRITE_TAC[RAPROOFAUX_bind_return_left]) THEN
  (MP_TAC(ISPECL [`k:num`; `MAP (update_move (sp_default ta)) (moves:(num#num#num)list)`;
                  `[]:(num#num#num)list`; `s3:ra_state`] st_ex_FILTER_full_consistency_ok) THEN
   ASM_REWRITE_TAC[MEM] THEN
   DISCH_THEN(X_CHOOSE_THEN `ts:(num#num#num)list` STRIP_ASSUME_TAC) THEN
   FIRST_ASSUM RAPROOFAUX_BIND_TAC) THEN
  (MP_TAC(ISPECL [`s3:ra_state`;
                  `if alg = reg_alloc_Simple then [] else ts:(num#num#num)list`;
                  `scost:(num spt)option`; `k:num`] do_alloc1_success) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ALL];
    DISCH_THEN(X_CHOOSE_THEN `ls:num list` (X_CHOOSE_THEN `s4:ra_state` STRIP_ASSUME_TAC))] THEN
   FIRST_ASSUM RAPROOFAUX_BIND_TAC) THEN
  (* the precoloured tags of mk_tags do not clash *)
  (SUBGOAL_THEN `no_clash (ra_state_adj_ls s4) (ra_state_node_tag s4)` ASSUME_TAC THENL
   [MATCH_MP_TAC RAPROOFAUX_mk_tags_no_clash THEN
    MAP_EVERY EXISTS_TAC [`fa:num spt`; `ta:num spt`; `n:num`] THEN
    MP_TAC(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s4`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (fun (asl,w as g) ->
     let t = find_term (fun t -> is_comb t && rator t = `biased_pref`) w in
     (MP_TAC(ISPECL [`k:num`; `ls:num list`; t; `s4:ra_state`] assign_Atemps_correct) THEN
      ANTS_TAC THENL
      [ASM_REWRITE_TAC[good_pref_biased_pref];
       DISCH_THEN(X_CHOOSE_THEN `s5:ra_state` STRIP_ASSUME_TAC)]) g) THEN
  (FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_node_tag]) THEN
   FIRST_X_ASSUM(LABEL_TAC "AT" o
     check (fun th -> is_forall (concl th) && free_in `s5:ra_state` (concl th)))) THEN
  (fun (asl,w as g) ->
     let t = find_term (fun t -> is_comb t && is_comb (rator t) &&
                                 rator(rator t) = `neg_biased_pref`) w in
     (MP_TAC(ISPECL [`s5:ra_state`; `k:num`; t] assign_Stemps_correct) THEN
      ANTS_TAC THENL
      [ASM_REWRITE_TAC[good_neg_pref_neg_biased_pref];
       DISCH_THEN(X_CHOOSE_THEN `s6:ra_state` STRIP_ASSUME_TAC)]) g) THEN
  (FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[RAPROOFAUX_frame_node_tag]) THEN
   FIRST_X_ASSUM(LABEL_TAC "ST" o
     check (fun th -> is_forall (concl th) && free_in `s6:ra_state` (concl th)))) THEN
  (MP_TAC(ISPECL [`s6:ra_state`; `ta:num spt`] extract_color_succeeds) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `lookup y (fa:num spt) = SOME x` ASSUME_TAC THENL
     [ASM_MESON_TAC[sp_inverts_def]; ALL_TAC] THEN
    REWRITE_TAC[GSYM IN_COUNT] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> rhs(concl th) = `count n`)) THEN
    REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[];
    DISCH_TAC] THEN
   FIRST_ASSUM RAPROOFAUX_BIND_TAC THEN REWRITE_TAC[st_ex_return_def]) THEN
  (SUBGOAL_THEN `LENGTH (ra_state_node_tag s6) = n /\ LENGTH (ra_state_adj_ls s6) = n /\
                 LENGTH (ra_state_node_tag s5) = n /\ LENGTH (ra_state_node_tag s4) = n`
     STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s6`)) THEN
    MP_TAC(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s5`)) THEN
    MP_TAC(MATCH_MP RAPROOFAUX_good_lengths (ASSUME `good_ra_state s4`)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  (* the colouring spcol and the evolution of the tags *)
  (EXISTS_TAC `map (\v. extract_tag (EL v (ra_state_node_tag s6))) (ta:num spt)` THEN
   EXISTS_TAC `s6:ra_state` THEN REWRITE_TAC[] THEN
   SUBGOAL_THEN `!x y. lookup x ta = SOME y ==>
       sp_default (map (\v. extract_tag (EL v (ra_state_node_tag s6))) ta) x =
       extract_tag (EL y (ra_state_node_tag s6))` (LABEL_TAC "SP") THENL
    [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[sp_default_def; lookup_map] THEN SIMP[];
     ALL_TAC] THEN
   SUBGOAL_THEN `domain (map (\v. extract_tag (EL v (ra_state_node_tag s6))) ta) =
                 {x | in_clash_tree ct x}` (LABEL_TAC "DOM") THENL
    [ASM_REWRITE_TAC[domain_map]; ALL_TAC]) THEN
  (SUBGOAL_THEN `!y. y < n ==> ~(EL y (ra_state_node_tag s6) = Atemp) /\
                               ~(EL y (ra_state_node_tag s6) = Stemp)` (LABEL_TAC "T1") THENL
   [X_GEN_TAC `y:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(EL y (ra_state_node_tag s5) = Atemp)` ASSUME_TAC THENL
     [UNDISCH_TAC `ALL (\n. ~(n = Atemp)) (ra_state_node_tag s5)` THEN
      REWRITE_TAC[GSYM ALL_EL] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "ST" (MP_TAC o SPEC `y:num`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP[]; ALL_TAC]) THEN
  (SUBGOAL_THEN `!y c. y < n /\ EL y (ra_state_node_tag s3) = Fixed c ==>
                       EL y (ra_state_node_tag s6) = Fixed c` (LABEL_TAC "E1") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `EL y (ra_state_node_tag s5) = Fixed c` ASSUME_TAC THENL
     [USE_THEN "AT" (MP_TAC o SPEC `y:num`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN SIMP[]; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    USE_THEN "ST" (MP_TAC o SPEC `y:num`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN SIMP[]]; ALL_TAC]) THEN
  (SUBGOAL_THEN `!y. y < n /\ EL y (ra_state_node_tag s3) = Stemp ==>
                     ?k'. EL y (ra_state_node_tag s6) = Fixed k' /\ k <= k'`
     (LABEL_TAC "E2") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `EL y (ra_state_node_tag s5) = Stemp` ASSUME_TAC THENL
     [USE_THEN "AT" (MP_TAC o SPEC `y:num`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN SIMP[]; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    USE_THEN "ST" (MP_TAC o SPEC `y:num`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]; ALL_TAC]) THEN
  (SUBGOAL_THEN `!x y. in_clash_tree ct x /\ lookup x ta = SOME y ==>
       y < n /\
       (if is_phy_var x then EL y (ra_state_node_tag s6) = Fixed (x DIV 2)
        else if is_stack_var x then ?k'. EL y (ra_state_node_tag s6) = Fixed k' /\ k <= k'
        else T)` (LABEL_TAC "T2") THENL
   [MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
    USE_THEN "A1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `in_clash_tree ct x`))) THEN
    ASM_REWRITE_TAC[] THEN SIMP[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "MT" (MP_TAC o SPECL [`y:num`; `x:num`]) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[sp_default_def] THEN SIMP[]; ALL_TAC] THEN
    ASM_CASES_TAC `is_phy_var x` THEN ASM_REWRITE_TAC[] THENL
     [DISCH_TAC THEN USE_THEN "E1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_CASES_TAC `is_stack_var x` THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN USE_THEN "E2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC]) THEN
  (* the conclusions *)
  (SUBGOAL_THEN `is_subgraph (ra_state_adj_ls s2) (ra_state_adj_ls s6)` (LABEL_TAC "SG2") THENL
   [UNDISCH_TAC `is_subgraph (ra_state_adj_ls s3) (ra_state_adj_ls s4)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `is_subgraph (ra_state_adj_ls s1) (ra_state_adj_ls s6)` (LABEL_TAC "SG1") THENL
   [MATCH_MP_TAC is_subgraph_trans THEN EXISTS_TAC `ra_state_adj_ls s2` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[is_subgraph_def] THEN
    USE_THEN "EG" (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[];
    ALL_TAC]) THEN
  (SUBGOAL_THEN `colouring_satisfactory
     (\f. if f < LENGTH (ra_state_node_tag s6)
          then extract_tag (EL f (ra_state_node_tag s6)) else 0)
     (ra_state_adj_ls s1)` ASSUME_TAC THENL
   [MATCH_MP_TAC colouring_satisfactory_subgraph THEN
    EXISTS_TAC `ra_state_adj_ls s6` THEN CONJ_TAC THENL
     [MATCH_MP_TAC no_clash_colouring_satisfactory THEN
      ASM_REWRITE_TAC[GSYM ALL_EL] THEN ASM_MESON_TAC[];
      USE_THEN "SG1" ACCEPT_TAC];
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`ct:clash_tree`; `sp_default ta`; `[]:num list`; `st:ra_state`;
       `gl:num list`; `s1:ra_state`;
       `\f. if f < LENGTH (ra_state_node_tag s6)
            then extract_tag (EL f (ra_state_node_tag s6)) else 0`;
       `LN:1 spt`; `LN:1 spt`] mk_graph_check_clash_tree) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[domain_def; UNION_EMPTY; IMAGE_CLAUSES; set_of_list; ALL_DISTINCT; ALL;
                    is_clique_def; MEM; INJ; IN_ELIM_THM; IN_COUNT; LENGTH_REPLICATE] THEN
    ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `livein:1 spt` (X_CHOOSE_THEN `flivein:1 spt` STRIP_ASSUME_TAC))]) THEN
  (EXISTS_TAC `livein:1 spt` THEN EXISTS_TAC `flivein:1 spt` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_eq (concl th) && rhs (concl th) = `SOME (livein:1 spt,flivein:1 spt)`
      then GEN_REWRITE_TAC RAND_CONV [SYM th] else failwith "") THEN
    MATCH_MP_TAC check_clash_tree_same_dom THEN REWRITE_TAC[domain_def; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    USE_THEN "A1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `in_clash_tree ct x`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "SP" (fun th ->
      REWRITE_TAC[MATCH_MP th (ASSUME `lookup x (ta:num spt) = SOME y`)]) THEN
    ASM_REWRITE_TAC[o_THM; sp_default_def] THEN SIMP[] THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (CONJ_TAC THENL
   [X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    USE_THEN "DOM" (fun th -> REWRITE_TAC[th; IN_ELIM_THM]) THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "A1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `in_clash_tree ct x`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "SP" (fun th ->
      REWRITE_TAC[MATCH_MP th (ASSUME `lookup x (ta:num spt) = SOME y`)]) THEN
    USE_THEN "T2" (MP_TAC o SPECL [`x:num`; `y:num`]) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `is_phy_var x` THEN ASM_REWRITE_TAC[] THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[extract_tag_def] THEN SIMP[];
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[extract_tag_def] THEN SIMP[] THEN ASM_REWRITE_TAC[]];
    ALL_TAC]) THEN
  (CONJ_TAC THENL
   [USE_THEN "DOM" (fun th -> REWRITE_TAC[th; IN_ELIM_THM]); ALL_TAC]) THEN
  (MP_TAC(ASSUME (CASE_TERM
     `ALL (\p. match p with (x,y) -> in_clash_tree ct x /\ in_clash_tree ct y)
        (forced:(num#num)list)`)) THEN
   REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM] THEN SIMP[]) THEN
  (DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN DISCH_TAC THEN
   SUBGOAL_THEN `in_clash_tree ct x /\ in_clash_tree ct y` STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
   USE_THEN "A1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `in_clash_tree ct x`))) THEN
   DISCH_THEN(X_CHOOSE_THEN `u:num` STRIP_ASSUME_TAC) THEN
   USE_THEN "A1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `in_clash_tree ct y`))) THEN
   DISCH_THEN(X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) THEN
   USE_THEN "SP" (fun th ->
     REWRITE_TAC[MATCH_MP th (ASSUME `lookup x (ta:num spt) = SOME u`);
                 MATCH_MP th (ASSUME `lookup y (ta:num spt) = SOME v`)]) THEN
   SUBGOAL_THEN `sp_default ta x = u /\ sp_default ta y = v` STRIP_ASSUME_TAC THENL
    [ASM_REWRITE_TAC[sp_default_def] THEN SIMP[]; ALL_TAC] THEN
   SUBGOAL_THEN `has_edge (ra_state_adj_ls s6) u v` ASSUME_TAC THENL
    [USE_THEN "SG2" (MATCH_MP_TAC o REWRITE_RULE[is_subgraph_def]) THEN
     USE_THEN "EG" (fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `?a b. EL u (ra_state_node_tag s6) = Fixed a /\
                       EL v (ra_state_node_tag s6) = Fixed b` STRIP_ASSUME_TAC THENL
    [USE_THEN "T1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `u < n`)) THEN
                              MP_TAC(MATCH_MP th (ASSUME `v < n`))) THEN
     MESON_TAC[cases "reg_alloc_tag"]; ALL_TAC] THEN
   UNDISCH_TAC `no_clash (ra_state_adj_ls s6) (ra_state_node_tag s6)` THEN
   REWRITE_TAC[no_clash_def] THEN DISCH_THEN(MP_TAC o SPECL [`u:num`; `v:num`]) THEN
   ASM_REWRITE_TAC[extract_tag_def] THEN SIMP[]) THEN
  (REPEAT STRIP_TAC THEN USE_THEN "INJ1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[]));;

(* The top-most correctness theorem (HOL4's ML helper first_prove_imp is not needed) *)
let reg_alloc_correct = prove
 (CASE_TERM `!alg scost k moves ct forced fs.
     ALL (\p. match p with (x,y) -> in_clash_tree ct x /\ in_clash_tree ct y) forced ==>
     ?spcol livein flivein.
       reg_alloc alg scost k moves ct forced fs = M_success spcol /\
       check_clash_tree (sp_default spcol) ct LN LN = SOME(livein,flivein) /\
       (!x. in_clash_tree ct x ==>
            x IN domain spcol /\
            (if is_phy_var x then sp_default spcol x = x DIV 2
             else if is_stack_var x then k <= sp_default spcol x
             else T)) /\
       (!x. x IN domain spcol ==> in_clash_tree ct x) /\
       ALL (\p. match p with (x,y) -> sp_default spcol x = sp_default spcol y ==> x = y)
         forced`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[reg_alloc_def] THEN
  RAPROOFAUX_TRIPLE_TAC `mk_bij ct` `ta:num spt` `fa:num spt` `n:num` THEN
  ASM_REWRITE_TAC[reg_alloc_aux_def; run_ira_state_def; ml_monadBase_run_def] THEN
  (fun (asl,w as g) ->
     let t = find_term (fun t ->
       let f,args = strip_comb t in
       is_const f && fst(dest_const f) = "do_reg_alloc" && length args = 9) w in
     MP_TAC(ISPECL [`alg:algorithm`; `scost:(num spt)option`; `k:num`;
                    `moves:(num#num#num)list`; `ct:clash_tree`; `forced:(num#num)list`;
                    `fs:1 spt`; rand t; `ta:num spt`; `fa:num spt`; `n:num`]
       do_reg_alloc_correct) g) THEN
  ASM_REWRITE_TAC[] THEN SIMP[] THEN
  DISCH_THEN(X_CHOOSE_THEN `spcol:num spt` (X_CHOOSE_THEN `st':ra_state`
    (X_CHOOSE_THEN `livein:1 spt` (X_CHOOSE_THEN `flivein:1 spt` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`spcol:num spt`; `livein:1 spt`; `flivein:1 spt`] THEN
  ASM_REWRITE_TAC[FST]);;
