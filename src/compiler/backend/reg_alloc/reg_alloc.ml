(* ========================================================================= *)
(* reg_alloc: port of HOL4 compiler/backend/reg_alloc/reg_allocScript.sml    *)
(* (CakeML v3479).  A monadic graph-coloring register allocator.             *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's do-notation for the monad st_ex is written with its constants   *)
(*   (translator/monadic/monad_base/ml_monadBase.ml): do x <- m; r od is     *)
(*   st_ex_bind m (\x. r), do m; r od is st_ex_ignore_bind m r, return is    *)
(*   st_ex_return, and a pattern bind (x,y) <- m is st_ex_bind m (\p. match  *)
(*   p with (x,y) -> r).  HOL4 () is one.                                    *)
(* - The constants that HOL4 makes with ML automation (ml_monadBaseLib) are *)
(*   defined here with HOL4's names and equations:                           *)
(*   define_monad_access_funs: get_f = \state. (M_success state.f,state)    *)
(*     and set_f x = \state. (M_success (),state with f := x) for every      *)
(*     field f of ra_state (get_stack is reg_alloc_get_stack);               *)
(*   define_monad_exception_functions: raise_E and handle_E for the          *)
(*     constructors E of state_exn (reg_alloc_raise_Fail, ...);              *)
(*   define_MFarray_manip_funs: f_length = Marray_length (\state. state.f), *)
(*     f_sub = Marray_sub (\state. state.f) Subscript and update_f =         *)
(*     Marray_update (\state. state.f) (\x state. state with f := x)         *)
(*     Subscript for the array fields;                                       *)
(*   define_run: the record ira_state (the array fields of ra_state         *)
(*     replaced by pairs (length, initial element)) and run_ira_state.      *)
(*   The exception type of the get_, set_ and _length functions is a type   *)
(*   variable, as in HOL4.                                                   *)
(* - HOL4 GENLIST f n is list_of_seq f n, EXISTS is EX; num_set is 1 spt.    *)
(* - HOL4's paired lambdas (\(p,x). t) are (\px. match px with (p,x) -> t);  *)
(*   a pattern SOME () is SOME (_:1).                                        *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mllist.ml";;
needs "hol4/state_transformer.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;
needs "hol4/sorting.ml";;

type_invention_error := true;;

(*
  The graph-coloring register allocator

  It currently uses several secret invariants that are important for
  performance but are not verified.

  This is an attempt at listing them:

  1) In ra_state.coalesced, coalesced[x] = x iff x is not coalesced.
     For non-Fixed pairs, coalesces happen downwards (smaller index
     survives). For Fixed-Atemp pairs, the Fixed node survives regardless
     of index, so coalesce_parent checks is_Fixed before the <= test.

  2) adjacency lists are ALWAYS sorted
*)

(*
  The tag datatype representing the state of nodes:

  Fixed n : means it is fixed to color n
  Atemp   : means that the node is allowed to be allocated to any register or stack pos
  Stemp   : only allowed to be mapped to k, k+1, ... (stack positions)
*)

(* HOL4: tag *)
let reg_alloc_tag_INDUCT,reg_alloc_tag_RECURSION = cake_type
  "reg_alloc_tag = Fixed num | Atemp | Stemp";;

(*
  Inputs are tagged with Fixed, Atemp , Stemp

  At all times, maintain invariant that adjacent nodes cannot be both Fixed
  to the same number

  First pass changes all Atemps to either Fixed or Stemp
  - Proofs: Fixed/Stemp stays unchanged

  Second pass changes all Stemps to Fixed with argument >= k
  - Proof: No remaining Stemp, every input node is mapped to Fixed
*)

(* Coloring state
  - Invariant: all the arrays have dimension = dim
  adj_ls: adjacency list (array of lists); node_tag: tags for each node
  (array); degrees: degrees for each node (array); dim: number of vertices
  in the graph; simp_wl: simplify worklist (non-move related, deg < k);
  spill_wl: spill worklist (deg >= k); freeze_wl: freeze worklist (move
  related, deg < k); avail_moves_wl: active moves (sorted by priority);
  unavail_moves_wl: inactive moves; coalesced: coalesce target of each node
  (array); move_related: whether a node is still move related (array);
  stack.
*)

let ra_state_INFO = cake_record "ra_state"
  ["adj_ls","(num list)list";
   "node_tag","(reg_alloc_tag)list";
   "degrees","num list";
   "dim","num";
   "simp_wl","num list";
   "spill_wl","num list";
   "freeze_wl","num list";
   "avail_moves_wl","(num#num#num)list";
   "unavail_moves_wl","(num#num#num)list";
   "coalesced","num list";
   "move_related","bool list";
   "stack","num list"];;

let ra_state_component_equality = ra_state_INFO.ri_component_equality;;

(* HOL4 define_monad_access_funs: get_f and set_f for every field f *)
let get_adj_ls_def = cake_def
  `(get_adj_ls:ra_state->((num list)list,C)exc#ra_state) =
     \state. (M_success (ra_state_adj_ls state),state)`;;

let get_node_tag_def = cake_def
  `(get_node_tag:ra_state->(reg_alloc_tag list,C)exc#ra_state) =
     \state. (M_success (ra_state_node_tag state),state)`;;

let get_degrees_def = cake_def
  `(get_degrees:ra_state->(num list,C)exc#ra_state) =
     \state. (M_success (ra_state_degrees state),state)`;;

let get_dim_def = cake_def
  `(get_dim:ra_state->(num,C)exc#ra_state) =
     \state. (M_success (ra_state_dim state),state)`;;

let get_simp_wl_def = cake_def
  `(get_simp_wl:ra_state->(num list,C)exc#ra_state) =
     \state. (M_success (ra_state_simp_wl state),state)`;;

let get_spill_wl_def = cake_def
  `(get_spill_wl:ra_state->(num list,C)exc#ra_state) =
     \state. (M_success (ra_state_spill_wl state),state)`;;

let get_freeze_wl_def = cake_def
  `(get_freeze_wl:ra_state->(num list,C)exc#ra_state) =
     \state. (M_success (ra_state_freeze_wl state),state)`;;

let get_avail_moves_wl_def = cake_def
  `(get_avail_moves_wl:ra_state->((num#num#num)list,C)exc#ra_state) =
     \state. (M_success (ra_state_avail_moves_wl state),state)`;;

let get_unavail_moves_wl_def = cake_def
  `(get_unavail_moves_wl:ra_state->((num#num#num)list,C)exc#ra_state) =
     \state. (M_success (ra_state_unavail_moves_wl state),state)`;;

let get_coalesced_def = cake_def
  `(get_coalesced:ra_state->(num list,C)exc#ra_state) =
     \state. (M_success (ra_state_coalesced state),state)`;;

let get_move_related_def = cake_def
  `(get_move_related:ra_state->(bool list,C)exc#ra_state) =
     \state. (M_success (ra_state_move_related state),state)`;;

let reg_alloc_get_stack_def = cake_def
  `(reg_alloc_get_stack:ra_state->(num list,C)exc#ra_state) =
     \state. (M_success (ra_state_stack state),state)`;;

let set_adj_ls_def = cake_def
  `(set_adj_ls:(num list)list->ra_state->(1,C)exc#ra_state) x =
     \state. (M_success one,ra_state_adj_ls_fupd (combin_K x) state)`;;

let set_node_tag_def = cake_def
  `(set_node_tag:reg_alloc_tag list->ra_state->(1,C)exc#ra_state) x =
     \state. (M_success one,ra_state_node_tag_fupd (combin_K x) state)`;;

let set_degrees_def = cake_def
  `(set_degrees:num list->ra_state->(1,C)exc#ra_state) x =
     \state. (M_success one,ra_state_degrees_fupd (combin_K x) state)`;;

let set_dim_def = cake_def
  `(set_dim:num->ra_state->(1,C)exc#ra_state) x =
     \state. (M_success one,ra_state_dim_fupd (combin_K x) state)`;;

let set_simp_wl_def = cake_def
  `(set_simp_wl:num list->ra_state->(1,C)exc#ra_state) x =
     \state. (M_success one,ra_state_simp_wl_fupd (combin_K x) state)`;;

let set_spill_wl_def = cake_def
  `(set_spill_wl:num list->ra_state->(1,C)exc#ra_state) x =
     \state. (M_success one,ra_state_spill_wl_fupd (combin_K x) state)`;;

let set_freeze_wl_def = cake_def
  `(set_freeze_wl:num list->ra_state->(1,C)exc#ra_state) x =
     \state. (M_success one,ra_state_freeze_wl_fupd (combin_K x) state)`;;

let set_avail_moves_wl_def = cake_def
  `(set_avail_moves_wl:(num#num#num)list->ra_state->(1,C)exc#ra_state) x =
     \state. (M_success one,ra_state_avail_moves_wl_fupd (combin_K x) state)`;;

let set_unavail_moves_wl_def = cake_def
  `(set_unavail_moves_wl:(num#num#num)list->ra_state->(1,C)exc#ra_state) x =
     \state. (M_success one,ra_state_unavail_moves_wl_fupd (combin_K x) state)`;;

let set_coalesced_def = cake_def
  `(set_coalesced:num list->ra_state->(1,C)exc#ra_state) x =
     \state. (M_success one,ra_state_coalesced_fupd (combin_K x) state)`;;

let set_move_related_def = cake_def
  `(set_move_related:bool list->ra_state->(1,C)exc#ra_state) x =
     \state. (M_success one,ra_state_move_related_fupd (combin_K x) state)`;;

let set_stack_def = cake_def
  `(set_stack:num list->ra_state->(1,C)exc#ra_state) x =
     \state. (M_success one,ra_state_stack_fupd (combin_K x) state)`;;

(* Data type for the exceptions *)
let state_exn_INDUCT,state_exn_RECURSION = cake_type
  "state_exn = reg_alloc_Fail string | Subscript";;

(* Monadic functions to handle the exceptions (HOL4                          *)
(* define_monad_exception_functions; HOL4 also overloads failwith for       *)
(* raise_Fail, locally)                                                      *)

let reg_alloc_raise_Fail_def = cake_def
  `reg_alloc_raise_Fail (e1:string) =
     \state:ra_state. (M_failure (reg_alloc_Fail e1):(A,state_exn)exc,state)`;;

let reg_alloc_raise_Subscript_def = cake_def
  `reg_alloc_raise_Subscript =
     \state:ra_state. (M_failure Subscript:(A,state_exn)exc,state)`;;

let reg_alloc_handle_Fail_def = cake_def
  `reg_alloc_handle_Fail (x:ra_state->(A,state_exn)exc#ra_state)
                         (f:string->ra_state->(A,state_exn)exc#ra_state) =
     \state. match x state with
               (res,state) ->
                 (match res with
                    M_success y -> (M_success y,state)
                  | M_failure e ->
                      (match e with
                         reg_alloc_Fail e1 -> f e1 state
                       | Subscript -> (M_failure Subscript,state)))`;;

let reg_alloc_handle_Subscript_def = cake_def
  `reg_alloc_handle_Subscript (x:ra_state->(A,state_exn)exc#ra_state)
                              (f:ra_state->(A,state_exn)exc#ra_state) =
     \state. match x state with
               (res,state) ->
                 (match res with
                    M_success y -> (M_success y,state)
                  | M_failure e ->
                      (match e with
                         reg_alloc_Fail e1 -> (M_failure (reg_alloc_Fail e1),state)
                       | Subscript -> f state))`;;

(* HOL4 define_MFarray_manip_funs: f_length, f_sub and update_f for the  *)
(* array fields, with the exception Subscript                               *)

let adj_ls_length_def = cake_def
  `(adj_ls_length:ra_state->(num,C)exc#ra_state) =
     Marray_length (\state. ra_state_adj_ls state)`;;

let adj_ls_sub_def = cake_def
  `adj_ls_sub =
     Marray_sub (\state:ra_state. ra_state_adj_ls state) Subscript`;;

let update_adj_ls_def = cake_def
  `update_adj_ls =
     Marray_update (\state:ra_state. ra_state_adj_ls state)
       (\x state. ra_state_adj_ls_fupd (combin_K x) state) Subscript`;;

let node_tag_length_def = cake_def
  `(node_tag_length:ra_state->(num,C)exc#ra_state) =
     Marray_length (\state. ra_state_node_tag state)`;;

let node_tag_sub_def = cake_def
  `node_tag_sub =
     Marray_sub (\state:ra_state. ra_state_node_tag state) Subscript`;;

let update_node_tag_def = cake_def
  `update_node_tag =
     Marray_update (\state:ra_state. ra_state_node_tag state)
       (\x state. ra_state_node_tag_fupd (combin_K x) state) Subscript`;;

let degrees_length_def = cake_def
  `(degrees_length:ra_state->(num,C)exc#ra_state) =
     Marray_length (\state. ra_state_degrees state)`;;

let degrees_sub_def = cake_def
  `degrees_sub =
     Marray_sub (\state:ra_state. ra_state_degrees state) Subscript`;;

let update_degrees_def = cake_def
  `update_degrees =
     Marray_update (\state:ra_state. ra_state_degrees state)
       (\x state. ra_state_degrees_fupd (combin_K x) state) Subscript`;;

let coalesced_length_def = cake_def
  `(coalesced_length:ra_state->(num,C)exc#ra_state) =
     Marray_length (\state. ra_state_coalesced state)`;;

let coalesced_sub_def = cake_def
  `coalesced_sub =
     Marray_sub (\state:ra_state. ra_state_coalesced state) Subscript`;;

let update_coalesced_def = cake_def
  `update_coalesced =
     Marray_update (\state:ra_state. ra_state_coalesced state)
       (\x state. ra_state_coalesced_fupd (combin_K x) state) Subscript`;;

let move_related_length_def = cake_def
  `(move_related_length:ra_state->(num,C)exc#ra_state) =
     Marray_length (\state. ra_state_move_related state)`;;

let move_related_sub_def = cake_def
  `move_related_sub =
     Marray_sub (\state:ra_state. ra_state_move_related state) Subscript`;;

let update_move_related_def = cake_def
  `update_move_related =
     Marray_update (\state:ra_state. ra_state_move_related state)
       (\x state. ra_state_move_related_fupd (combin_K x) state) Subscript`;;

let adj_ls_accessor = end_itlist CONJ
  [get_adj_ls_def; set_adj_ls_def;
   adj_ls_length_def; adj_ls_sub_def; update_adj_ls_def];;

let node_tag_accessor = end_itlist CONJ
  [get_node_tag_def; set_node_tag_def;
   node_tag_length_def; node_tag_sub_def; update_node_tag_def];;

let degrees_accessor = end_itlist CONJ
  [get_degrees_def; set_degrees_def;
   degrees_length_def; degrees_sub_def; update_degrees_def];;

let coalesced_accessor = end_itlist CONJ
  [get_coalesced_def; set_coalesced_def;
   coalesced_length_def; coalesced_sub_def; update_coalesced_def];;

let move_related_accessor = end_itlist CONJ
  [get_move_related_def; set_move_related_def;
   move_related_length_def; move_related_sub_def; update_move_related_def];;

(* Helper functions for defining the allocator *)

(* Monadic list functions -- doesn't care about order *)
let st_ex_FOREACH_def = cake_def
  `(st_ex_FOREACH [] (a:X->S->(B,E)exc#S) = st_ex_return one) /\
   (st_ex_FOREACH (CONS x xs) a = st_ex_ignore_bind (a x) (st_ex_FOREACH xs a))`;;

let st_ex_MAP_def = cake_def
  `(st_ex_MAP (f:X->S->(Y,E)exc#S) [] = st_ex_return []) /\
   (st_ex_MAP f (CONS x xs) =
      st_ex_bind (f x) (\fx.
      st_ex_bind (st_ex_MAP f xs) (\fxs.
      st_ex_return (CONS fx fxs))))`;;

let st_ex_PARTITION_def = cake_def
  `(st_ex_PARTITION (P:X->S->(bool,E)exc#S) [] tt ff = st_ex_return (tt,ff)) /\
   (st_ex_PARTITION P (CONS x xs) tt ff =
      st_ex_bind (P x) (\Px.
      if Px then st_ex_PARTITION P xs (CONS x tt) ff
      else st_ex_PARTITION P xs tt (CONS x ff)))`;;

let st_ex_FILTER_def = cake_def
  `(st_ex_FILTER (P:X->S->(bool,E)exc#S) [] acc = st_ex_return acc) /\
   (st_ex_FILTER P (CONS x xs) acc =
      st_ex_bind (P x) (\Px.
      if Px then st_ex_FILTER P xs (CONS x acc)
      else st_ex_FILTER P xs acc))`;;

(* Keep adjacency lists sorted by > *)

(* Insert an undirect edge into the adj list representation *)
let sorted_insert_def = cake_def
  `(sorted_insert (x:num) acc [] = REVERSE (CONS x acc)) /\
   (sorted_insert x acc (CONS y ys) =
      if x = y then APPEND (REVERSE acc) (CONS y ys)
      else if x > y then APPEND (REVERSE acc) (CONS x (CONS y ys))
      else sorted_insert x (CONS y acc) ys)`;;

let sorted_mem_def = cake_def
  `(sorted_mem (x:num) [] <=> F) /\
   (sorted_mem x (CONS y ys) <=>
      if x = y then T
      else if x > y then F
      else sorted_mem x ys)`;;

let insert_edge_def = cake_def
  `insert_edge x y =
     st_ex_bind (adj_ls_sub x) (\adjx.
     st_ex_bind (adj_ls_sub y) (\adjy.
     st_ex_ignore_bind (update_adj_ls x (sorted_insert y [] adjx))
                       (update_adj_ls y (sorted_insert x [] adjy))))`;;

(* insert a list of edges all adjacent to one node *)
let list_insert_edge_def = cake_def
  `(list_insert_edge x [] = st_ex_return one) /\
   (list_insert_edge x (CONS y ys) =
      st_ex_ignore_bind (insert_edge x y) (list_insert_edge x ys))`;;

let clique_insert_edge_def = cake_def
  `(clique_insert_edge [] = st_ex_return one) /\
   (clique_insert_edge (CONS x xs) =
      st_ex_ignore_bind (list_insert_edge x xs) (clique_insert_edge xs))`;;

(* assuming vertices in cli already forms a clique,
   extend it with new members
*)
let extend_clique_def = cake_def
  `(extend_clique [] cli = st_ex_return cli) /\
   (extend_clique (CONS x xs) cli =
      if MEM x cli then extend_clique xs cli
      else st_ex_ignore_bind (list_insert_edge x cli)
                             (extend_clique xs (CONS x cli)))`;;

(* The allocator heuristics, designed to minimize proof at the
   cost of some extra computation *)

(* (Safely) decrement the degree of all vertices adjacent to n by 1 *)
let dec_deg_def = cake_def
  `dec_deg n =
     st_ex_bind (degrees_sub n) (\cd. update_degrees n (cd - 1))`;;

let dec_degree_def = cake_def
  `dec_degree n =
     st_ex_bind get_dim (\d.
     if n < d then
       st_ex_bind (adj_ls_sub n) (\adjs. st_ex_FOREACH adjs dec_deg)
     else st_ex_return one)`;;

let add_simp_wl_def = cake_def
  `(add_simp_wl ls:ra_state->(1,E)exc#ra_state) =
     st_ex_bind get_simp_wl (\swl. set_simp_wl (APPEND ls swl))`;;

let add_spill_wl_def = cake_def
  `(add_spill_wl ls:ra_state->(1,E)exc#ra_state) =
     st_ex_bind get_spill_wl (\swl. set_spill_wl (APPEND ls swl))`;;

let add_freeze_wl_def = cake_def
  `(add_freeze_wl ls:ra_state->(1,E)exc#ra_state) =
     st_ex_bind get_freeze_wl (\fwl. set_freeze_wl (APPEND ls fwl))`;;

(* push x onto the stack, deleting it from existence *)
let push_stack_def = cake_def
  `push_stack x =
     st_ex_bind reg_alloc_get_stack (\swl.
     st_ex_ignore_bind (update_degrees x 0)
     (st_ex_ignore_bind (update_move_related x F)
     (set_stack (CONS x swl))))`;;

let add_unavail_moves_wl_def = cake_def
  `(add_unavail_moves_wl ls:ra_state->(1,E)exc#ra_state) =
     st_ex_bind get_unavail_moves_wl (\swl.
     set_unavail_moves_wl (APPEND ls swl))`;;

(* unspill:
   Move any vertices in the spill list that has
   degree < k into the simplify or freeze worklist
   Revive all neighboring moves of these nodes
*)
let is_not_coalesced_def = cake_def
  `is_not_coalesced d =
     st_ex_bind (coalesced_sub d) (\dt. st_ex_return (d = dt))`;;

let split_degree_def = cake_def
  `split_degree d k v =
     if v < d then
       st_ex_bind (degrees_sub v) (\vd.
       st_ex_bind (is_not_coalesced v) (\b.
       st_ex_return (vd < k /\ b)))
     else st_ex_return T`;;

(* sort moves by priority *)
(* HOL4: sort_moves *)
let reg_alloc_sort_moves_def = cake_def
  `reg_alloc_sort_moves (ls:(num#A)list) =
     sort (\px px'. match px with
                      (p,x) -> (match px' with (p',x') -> p > p')) ls`;;

(* merge two sorted lists *)
let smerge_def = cake_def
  `(smerge [] (ys:(num#A)list) = ys) /\
   (smerge xs [] = xs) /\
   (smerge (CONS (p,m) xs) (CONS (p',m') ys) =
      if p >= p' then CONS (p,m) (smerge xs (CONS (p',m') ys))
      else CONS (p',m') (smerge (CONS (p,m) xs) ys))`;;

let smerge_ind = cake_ind "smerge";;

(*
  revive the unavailable moves that touch each neighbor
*)
let revive_moves_def = cake_def
  `revive_moves vs =
     st_ex_bind (st_ex_MAP adj_ls_sub vs) (\nbs.
     st_ex_bind get_unavail_moves_wl (\uam.
     st_ex_bind get_avail_moves_wl (\am.
     let (rev,unavail) =
       PARTITION (\m. match m with
                        (_,(x,y)) -> EX (sorted_mem x) nbs \/ EX (sorted_mem y) nbs)
                 uam in
     let sorted = smerge (reg_alloc_sort_moves rev) am in
     st_ex_ignore_bind (set_avail_moves_wl sorted)
                       (set_unavail_moves_wl unavail))))`;;

(* (after the partition, the nodes in ltk have turned into low degree nodes) *)
let unspill_def = cake_def
  `unspill (k:num) =
     st_ex_bind get_dim (\d.
     st_ex_bind get_spill_wl (\swl.
     st_ex_bind (st_ex_PARTITION (split_degree d k) swl [] []) (\p.
     match p with (ltk,gtk) ->
     st_ex_ignore_bind (revive_moves ltk)
     (st_ex_bind (st_ex_PARTITION move_related_sub ltk [] []) (\p.
      match p with (ltkfreeze,ltksimp) ->
      st_ex_ignore_bind (set_spill_wl gtk)
      (st_ex_ignore_bind (add_simp_wl ltksimp)
      (add_freeze_wl ltkfreeze)))))))`;;

(* simplify:
  Directly simplifies the entire list
  instead of doing it 1-by-1
  T = successful simplification
  F = no simplification
*)
let do_simplify_def = cake_def
  `do_simplify k =
     st_ex_bind get_simp_wl (\simps.
     if NULL simps then st_ex_return F
     else
       st_ex_ignore_bind (st_ex_FOREACH simps dec_degree)
       (st_ex_ignore_bind (st_ex_FOREACH simps push_stack)
       (st_ex_ignore_bind (set_simp_wl [])
       (st_ex_ignore_bind (unspill k)
       (st_ex_return T)))))`;;

(* increment degree of n by d *)
let inc_deg_def = cake_def
  `inc_deg n d =
     st_ex_bind (degrees_sub n) (\cd. update_degrees n (cd + d))`;;

(*
  Within the allocator, we will assume that all moves
  have the form:

  1) x:=y where x is Fixed (<k) or Atemp, and y is Atemp
  2) x < y
*)

(*
  do coalesce for real :
  perform a coalesce of (x,y) by merging y into x
  - this assumes y is Atemp
  - we only pretend to delete y from the graph
  Case 1:
  x -> v <- y, then the degree of v is reduced by 1
  Case 2:
  x -/-> v <- y, then the degree of x is increased by 1
  Case 3:
  x -> v <-/- y, no change
  In both cases, we leave the v-y edge dangling
*)

(* An actual register *)
let is_Fixed_def = cake_def
  `is_Fixed x =
     st_ex_bind (node_tag_sub x) (\xt.
     st_ex_return (match xt with Fixed n -> T | _ -> F))`;;

let do_coalesce_real_def = cake_def
  `do_coalesce_real x y case1 case2 =
     st_ex_ignore_bind (update_coalesced y x)
     (st_ex_bind (is_Fixed x) (\bx.
      st_ex_ignore_bind
        (if bx then st_ex_return one else inc_deg x (LENGTH case2))
      (st_ex_ignore_bind (list_insert_edge x case2)
      (st_ex_ignore_bind (st_ex_FOREACH case1 dec_deg)
      (push_stack y)))))`;;

(* The coalesceable criterion, Briggs and George *)

(*
  Briggs:
  the result of combining x,y should have fewer than k neighbors
  of significant degree (i.e. degree >= k)

  George:
  assume that x is a high degree node (typically a Fixed node)
  then coalescing y into x is allowed if every neighbor of y not already
  a neighbor of x (i.e. case 2) has degree < k

  TODO: The implementation here isn't super great,
  because the George check is only
  really efficient if one has a true adjacency matrix representation
*)
let is_Atemp_def = cake_def
  `is_Atemp d =
     st_ex_bind (node_tag_sub d) (\dt. st_ex_return (dt = Atemp))`;;

let is_Fixed_k_def = cake_def
  `is_Fixed_k k x =
     st_ex_bind (node_tag_sub x) (\xt.
     st_ex_return (match xt with Fixed n -> n < k | _ -> F))`;;

let considered_var_def = cake_def
  `considered_var k x =
     st_ex_bind (is_Atemp x) (\bx.
     st_ex_bind (is_Fixed_k k x) (\fx.
     st_ex_return (bx \/ fx)))`;;

(* Fixed vars are treated as having infinite degree *)
let deg_or_inf_def = cake_def
  `deg_or_inf k x =
     st_ex_bind (is_Fixed_k k x) (\bx.
     if bx then st_ex_return k else degrees_sub x)`;;

(* see do_coalesce_real for the cases; c2len = 0 is the George criterion; *)
(* in case1degs, k+1 is infinity                                          *)
let bg_ok_def = cake_def
  `bg_ok k x y =
     st_ex_bind (adj_ls_sub x) (\adjx.
     st_ex_bind (adj_ls_sub y) (\adjy.
     let (case1,case2) = PARTITION (\v. sorted_mem v adjx) adjy in
     st_ex_bind (st_ex_FILTER (considered_var k) case1 []) (\case1.
     st_ex_bind (st_ex_FILTER (considered_var k) case2 []) (\case2.
     st_ex_bind (st_ex_MAP (deg_or_inf k) case2) (\case2degs.
     let c2len = LENGTH (FILTER (\x. x >= k) case2degs) in
     if c2len = 0 then st_ex_return (SOME (case1,case2))
     else
       let case3 = FILTER (\v. ~sorted_mem v adjy) adjx in
       st_ex_bind (st_ex_FILTER (considered_var k) case3 []) (\case3.
       st_ex_bind (st_ex_MAP (deg_or_inf (k + 1)) case1) (\case1degs.
       st_ex_bind (st_ex_MAP (deg_or_inf k) case3) (\case3degs.
       st_ex_bind (st_ex_return (LENGTH (FILTER (\x. x - 1 >= k) case1degs)))
         (\c1len.
       st_ex_bind (st_ex_return (LENGTH (FILTER (\x. x >= k) case3degs)))
         (\c3len.
       if (c1len + c2len) + c3len < k then st_ex_return (SOME (case1,case2))
       else st_ex_return NONE))))))))))`;;

(*
  Consistency check for moves
  Any moves failing this check can be directly discarded
  1) x <> y
  2) x,y must not already clash

  3) x,y either fixed or atemps and not both fixed
*)

let consistency_ok_def = cake_def
  `consistency_ok x y =
     if x = y then st_ex_return F
     else
       st_ex_bind (adj_ls_sub y) (\adjy.
       if sorted_mem x adjy then st_ex_return F
       else
         st_ex_bind (is_Fixed x) (\bx.
         st_ex_bind (is_Fixed y) (\by.
         st_ex_bind (move_related_sub x) (\movrelx.
         st_ex_bind (move_related_sub y) (\movrely.
         st_ex_return ((bx \/ movrelx) /\ (by \/ movrely) /\ ~(bx /\ by)))))))`;;

(*
  find the ancestor
  and collapse along the way
  (special case: x is coalesced to a fixed color already)
*)
let coalesce_parent_def = cake_def_wf `MEASURE (\x:num. x)` TERM_TAC
  `coalesce_parent x =
     st_ex_bind (coalesced_sub x) (\xt.
     st_ex_bind (is_Fixed xt) (\bx.
     if bx then st_ex_return xt
     else if x <= xt then st_ex_return x
     else
       st_ex_bind (coalesce_parent xt) (\anc.
       st_ex_ignore_bind (update_coalesced x anc) (st_ex_return anc))))`;;

(* HOL4's coalesce_parent_ind, with HOL4's names for the variables of the  *)
(* continuations (the kit's version has the variable name of the rule        *)
(* MONADAUX_ADMISSIBLE_st_ex_bind)                                          *)
let coalesce_parent_ind = prove
 (`!P. (!x. (!bx xt. ~bx /\ ~(x <= xt) ==> P xt) ==> P x) ==> !x. P x`,
  MATCH_ACCEPT_TAC (cake_ind "coalesce_parent"));;

let canonize_move_def = cake_def
  `canonize_move x y =
     st_ex_bind (is_Fixed x) (\bx.
     st_ex_bind (is_Fixed y) (\by.
     if by then st_ex_return (y,x)
     else if bx then st_ex_return (x,y)
     else if x < y then st_ex_return (x,y)
     else st_ex_return (y,x)))`;;

(*
  Picks apart the available moves worklist
  1) If we find any inconsistent ones -> throw them away
  not necessary? -- 2) canonize the move to put fixed register in front
  3) returns the first bg_ok move that is also consistent
*)
let st_ex_FIRST_def = cake_def
  `(st_ex_FIRST P (Q:num->num->ra_state->(B option,state_exn)exc#ra_state)
                [] (unavail:(A#num#num)list) = st_ex_return (NONE,unavail)) /\
   (st_ex_FIRST P Q (CONS m ms) unavail =
      let (p,(x,y)) = m in
      st_ex_bind (coalesce_parent x) (\x.
      st_ex_bind (coalesce_parent y) (\y.
      st_ex_bind (P x y) (\b1.
      if ~b1 then st_ex_FIRST P Q ms unavail
      else
        st_ex_bind (canonize_move x y) (\xy.
        match xy with (x,y) ->
        st_ex_bind (Q x y) (\optb2.
        match optb2 with
          NONE -> st_ex_FIRST P Q ms (CONS (p,(x,y)) unavail)
        | SOME pr -> st_ex_return (SOME ((x,y),pr,ms),unavail)))))))`;;

let respill_def = cake_def
  `respill k x =
     st_ex_bind (degrees_sub x) (\xd.
     if xd < k then st_ex_return one
     else
       st_ex_bind get_freeze_wl (\freeze.
       if MEM x freeze then
         st_ex_ignore_bind (add_spill_wl [x])
                           (set_freeze_wl (FILTER (\y. ~(y = x)) freeze))
       else st_ex_return one))`;;

(* the move (x,y) is coalesced: y into x *)
let do_coalesce_def = cake_def
  `do_coalesce k =
     st_ex_bind get_avail_moves_wl (\am.
     st_ex_bind (st_ex_FIRST consistency_ok (bg_ok k) am []) (\p.
     match p with (ores,unavail) ->
     st_ex_ignore_bind (add_unavail_moves_wl unavail)
     (match ores with
        NONE -> st_ex_ignore_bind (set_avail_moves_wl []) (st_ex_return F)
      | SOME ((x,y),(case1,case2),ms) ->
          st_ex_ignore_bind (set_avail_moves_wl ms)
          (st_ex_ignore_bind (do_coalesce_real x y case1 case2)
          (st_ex_ignore_bind (unspill k)
          (st_ex_ignore_bind (respill k x)
          (st_ex_return T)))))))`;;

(*
  prefreeze: make the freeze and spill worklists consistent.

  If this makes a node simplifiable, then we skip freezing

  If we got here, it means coalescing failed, i.e. everything is
  an unavailable move now

  Here, we cleanup any potential mess in the coalescing phase
  1) Filter out all nodes y that have been coalesced
  2) delete any moves in the unavailable list, that are actually invalid
  3) mark only nodes involved in the remaining moves as move related
  4) simplify any resulting non-move-related nodes

*)

(* zero out move_related, then reset to correct values (make sure fixed  *)
(* are kept as NOT move_related)                                          *)
let reset_move_related_def = cake_def
  `reset_move_related (ls:(A#num#num)list) =
     st_ex_bind get_dim (\d.
     st_ex_ignore_bind (st_ex_FOREACH (COUNT_LIST d) (\x. update_move_related x F))
     (st_ex_FOREACH ls (\m.
        match m with (_,(x,y)) ->
        st_ex_bind (is_Fixed x) (\bx.
        st_ex_bind (is_Fixed y) (\by.
        st_ex_ignore_bind (update_move_related x (~bx))
                          (update_move_related y (~by)))))))`;;

let do_prefreeze_def = cake_def
  `do_prefreeze k =
     st_ex_bind get_freeze_wl (\fwl_pre.
     st_ex_bind (st_ex_FILTER is_not_coalesced fwl_pre []) (\fwl.
     st_ex_bind get_spill_wl (\swl_pre.
     st_ex_bind (st_ex_FILTER is_not_coalesced swl_pre []) (\swl.
     st_ex_ignore_bind (set_spill_wl swl)
     (st_ex_bind get_unavail_moves_wl (\uam_pre.
      st_ex_bind (st_ex_FILTER (\m. match m with (_,(x,y)) -> consistency_ok x y)
                               uam_pre []) (\uam.
      st_ex_ignore_bind (reset_move_related uam)
      (st_ex_bind (set_unavail_moves_wl uam) (\uam.
       st_ex_bind (st_ex_PARTITION move_related_sub fwl [] []) (\p.
       match p with (ltkfreeze,ltksimp) ->
       st_ex_ignore_bind (add_simp_wl ltksimp)
       (st_ex_ignore_bind (set_freeze_wl ltkfreeze)
       (do_simplify k))))))))))))`;;

(* if prefreeze failed, then just freeze *)

let do_freeze_def = cake_def
  `do_freeze k =
     st_ex_bind get_freeze_wl (\freeze.
     match freeze with
       [] -> st_ex_return F
     | CONS x xs ->
         st_ex_ignore_bind (dec_degree x)
         (st_ex_ignore_bind (push_stack x)
         (st_ex_ignore_bind (set_freeze_wl xs)
         (st_ex_ignore_bind (unspill k)
         (st_ex_return T)))))`;;

(* spill:
  If given a spill cost,
    picks the cheapest node in the spill worklist,
    based on spill cost / degree
  Otherwise,
    picks highest degree node
*)
let safe_div_def = cake_def
  `safe_div x v = if v = 0 then 0 else x DIV v`;;

(* MONADAUX_LEN_TAC: termination by the length of a list argument (the kit's *)
(* automatic search takes minutes for these definitions with many arguments) *)
let MONADAUX_LEN_TAC : tactic =
  REWRITE_TAC[measure_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC;;

let st_ex_list_MIN_cost_def = cake_def_wf
  `MEASURE (\(scost:num spt,l:num list,d:num,k:num,v:num,acc:num list). LENGTH l)`
  MONADAUX_LEN_TAC
  `(st_ex_list_MIN_cost (scost:num spt) [] d k v acc = st_ex_return (k,acc)) /\
   (st_ex_list_MIN_cost scost (CONS x xs) d k v acc =
      if x < d then
        st_ex_bind (degrees_sub x) (\xv.
        st_ex_bind (st_ex_return (safe_div (lookup_any x scost 0) xv)) (\cost.
        if v > cost then st_ex_list_MIN_cost scost xs d x cost (CONS k acc)
        else st_ex_list_MIN_cost scost xs d k v (CONS x acc)))
      else st_ex_list_MIN_cost scost xs d k v acc)`;;

let st_ex_list_MAX_deg_def = cake_def_wf
  `MEASURE (\(l:num list,d:num,k:num,v:num,acc:num list). LENGTH l)`
  MONADAUX_LEN_TAC
  `(st_ex_list_MAX_deg [] d (k:num) (v:num) acc = st_ex_return (k,acc)) /\
   (st_ex_list_MAX_deg (CONS x xs) d k v acc =
      if x < d then
        st_ex_bind (degrees_sub x) (\xv.
        if v < xv then st_ex_list_MAX_deg xs d x xv (CONS k acc)
        else st_ex_list_MAX_deg xs d k v (CONS x acc))
      else st_ex_list_MAX_deg xs d k v acc)`;;

let do_spill_def = cake_def
  `do_spill scostopt k =
     st_ex_bind get_spill_wl (\spills.
     st_ex_bind get_dim (\d.
     match spills with
       [] -> st_ex_return F
     | CONS x xs ->
         st_ex_bind (degrees_sub x) (\xv.
         st_ex_bind
           (match scostopt with
              NONE -> st_ex_list_MAX_deg xs d x xv []
            | SOME scost ->
                st_ex_list_MIN_cost scost xs d x
                  (safe_div (lookup_any x scost 0) xv) []) (\yys.
         match yys with (y,ys) ->
         st_ex_ignore_bind (dec_degree y)
         (st_ex_ignore_bind (push_stack y)
         (st_ex_ignore_bind (set_spill_wl ys)
         (st_ex_ignore_bind (unspill k)
         (st_ex_return T))))))))`;;

let do_step_def = cake_def
  `do_step scost k =
     st_ex_bind (do_simplify k) (\b.
     if b then st_ex_return b
     else
       st_ex_bind (do_coalesce k) (\b.
       if b then st_ex_return b
       else
         st_ex_bind (do_prefreeze k) (\b.
         if b then st_ex_return b
         else
           st_ex_bind (do_freeze k) (\b.
           if b then st_ex_return b
           else st_ex_bind (do_spill scost k) (\b. st_ex_return b)))))`;;

let rpt_do_step_def = cake_def
  `(rpt_do_step scost k 0 = st_ex_return one) /\
   (rpt_do_step scost k (SUC c) =
      st_ex_bind (do_step scost k) (\b.
      if b then rpt_do_step scost k c else st_ex_return one))`;;

(*
  The coloring functions
*)

(* Removing adjacent colours from ks: no more available colours; some     *)
(* available colour after checking; do the check for vertex x             *)
let remove_colours_def = cake_def
  `(remove_colours (ls:num list) [] = st_ex_return []) /\
   (remove_colours [] (ks:num list) = st_ex_return ks) /\
   (remove_colours (CONS x xs) ks =
      st_ex_bind (node_tag_sub x) (\cx.
      st_ex_bind
        (match cx with
           Fixed c -> remove_colours xs (FILTER (\x. ~(x = c)) ks)
         | _ -> remove_colours xs ks) (\r.
      st_ex_return r)))`;;

let remove_colours_ind = cake_ind "remove_colours";;

(* First colouring -- turns all Atemps into Fixeds or Stemps drawing from colors in ks *)
(* Assign a tag to an Atemp node, skipping if it is not actually an Atemp *)
(* (prefs n ks applies the monadic preference oracle)                     *)

let assign_Atemp_tag_def = cake_def
  `assign_Atemp_tag ks
     (prefs:num->num list->ra_state->(num option,state_exn)exc#ra_state) n =
     st_ex_bind (node_tag_sub n) (\ntag.
     match ntag with
       Atemp ->
         st_ex_bind (adj_ls_sub n) (\adjs.
         st_ex_bind (remove_colours adjs ks) (\ks.
         match ks with
           [] -> update_node_tag n Stemp
         | CONS x _ ->
             st_ex_bind (prefs n ks) (\c.
             match c with
               NONE -> update_node_tag n (Fixed x)
             | SOME y -> update_node_tag n (Fixed y))))
     | _ -> st_ex_return one)`;;

(* The first allocation step *)
(* k = num registers, ls = heuristic list, prefs = coloring preference *)
(* Assign all the ones that the ls tells us to; assign_Atemp_tag already  *)
(* filters for Atemps, so it is then given all the nodes                  *)
let assign_Atemps_def = cake_def
  `assign_Atemps k ls prefs =
     st_ex_bind get_dim (\d.
     st_ex_bind (st_ex_return (FILTER (\n. n < d) ls)) (\ls.
     st_ex_bind (st_ex_return (list_of_seq (\x. x) k)) (\ks.
     st_ex_bind (st_ex_return (list_of_seq (\x. x) d)) (\cs.
     st_ex_ignore_bind (st_ex_FOREACH ls (assign_Atemp_tag ks prefs))
                       (st_ex_FOREACH cs (assign_Atemp_tag ks prefs))))))`;;

(* Default makes it easier to translate, doesn't matter for our purposes what
   the default is *)
let tag_col_def = cake_def
  `(tag_col (Fixed n) = n) /\
   (tag_col _ = 0)`;;

(* Find the first available in k,k+1,...
   assuming input is sorted
*)
let unbound_colour_def = cake_def
  `(unbound_colour col [] = col) /\
   (unbound_colour col (CONS (x:num) xs) =
      if col < x then col
      else if x = col then unbound_colour (col + 1) xs
      else unbound_colour col xs)`;;

(* Second colouring -- turns all Stemps into Fixed >= k *)
let assign_Stemp_tag_def = cake_def
  `assign_Stemp_tag k
     (prefs:num->num list->ra_state->(num option,state_exn)exc#ra_state) n =
     st_ex_bind (node_tag_sub n) (\ntag.
     match ntag with
       Stemp ->
         st_ex_bind (adj_ls_sub n) (\adjs.
         st_ex_bind (st_ex_MAP node_tag_sub adjs) (\tags.
         let bads = sort (\x y. x <= y) (MAP tag_col tags) in
         st_ex_bind (prefs n bads) (\c.
         match c with
           NONE -> update_node_tag n (Fixed (unbound_colour k bads))
         | SOME y -> update_node_tag n (Fixed y))))
     | _ -> st_ex_return one)`;;

(* The second allocation step *)
let assign_Stemps_def = cake_def
  `assign_Stemps k prefs =
     st_ex_bind get_dim (\d.
     st_ex_bind (st_ex_return (list_of_seq (\x. x) d)) (\cs.
     st_ex_FOREACH cs (assign_Stemp_tag k prefs)))`;;

(* Monadic biased selection oracle, finds the first matching color *)
let first_match_col_def = cake_def
  `(first_match_col ks [] = st_ex_return NONE) /\
   (first_match_col ks (CONS x xs) =
      st_ex_bind (node_tag_sub x) (\c.
      match c with
        Fixed m -> if MEM m ks then st_ex_return (SOME m)
                   else first_match_col ks xs
      | _ -> first_match_col ks xs))`;;

(* Clash tree representation of a program -- this is designed as an interface:
  wordLang program -> clash tree -> reg alloc

  It only represents wordLang programs, which do not have back-edges
  The allocator itself is more general, and supports arbitrary graphs
  It serves two purposes:
  1) slightly more efficient checking of coloring oracles
  2) it gets compiled in to the clash graphs for the allocator

  TODO: probably want to move the clash tree representation up and separate it
  from the allocator

  Delta (writes list) (reads list); Set: a fixed set; Branch: a binary
  branch, with an optional liveset at the head; Seq.
*)

let clash_tree_INDUCT,clash_tree_RECURSION = cake_type
  "clash_tree = Delta (num list) (num list)
              | reg_alloc_Set (1 spt)
              | reg_alloc_Branch ((1 spt)option) clash_tree clash_tree
              | reg_alloc_Seq clash_tree clash_tree";;

(* --- clash_tree oracle checks --- *)
let numset_list_delete_def = cake_def
  `(numset_list_delete [] (t:A spt) = t) /\
   (numset_list_delete (CONS x xs) t = numset_list_delete xs (delete x t))`;;

(*Check that a numset is injective over the clash sets in an interpreted tree*)
let check_col_def = cake_def
  `check_col f (t:A spt) =
     let names = MAP (f o FST) (toAList t) in
     if ALL_DISTINCT names then SOME (t,fromAList (MAP (\x. (x,one)) names))
     else NONE`;;

let check_partial_col_def = cake_def
  `(check_partial_col f [] (t:1 spt) (ft:1 spt) = SOME (t,ft)) /\
   (check_partial_col f (CONS x xs) t ft =
      match lookup x t with
        SOME (_:1) -> check_partial_col f xs t ft
      | NONE ->
          (match lookup (f x) ft with
             NONE -> check_partial_col f xs (insert x one t) (insert (f x) one ft)
           | SOME (_:1) -> NONE))`;;

(* The checking function, used by oracle, and also used as part of the correctness proof *)
(* live = the liveset, flive = the liveset with f applied over it *)
(* (in the Branch case without a liveset, the check can be done in either direction) *)
let check_clash_tree_def = cake_def
  `(check_clash_tree f (Delta w r) live flive =
      match check_partial_col f w live flive with
        NONE -> NONE
      | SOME _ ->
          let del_w = numset_list_delete w live in
          let fdel_w = numset_list_delete (MAP f w) flive in
          check_partial_col f r del_w fdel_w) /\
   (check_clash_tree f (reg_alloc_Set t) live flive = check_col f t) /\
   (check_clash_tree f (reg_alloc_Branch topt t1 t2) live flive =
      match check_clash_tree f t1 live flive with
        NONE -> NONE
      | SOME (t1_out,ft1_out) ->
          (match check_clash_tree f t2 live flive with
             NONE -> NONE
           | SOME (t2_out,ft2_out) ->
               (match topt with
                  NONE ->
                    check_partial_col f (MAP FST (toAList (difference t2_out t1_out)))
                      t1_out ft1_out
                | SOME t -> check_col f t))) /\
   (check_clash_tree f (reg_alloc_Seq t1 t2) live flive =
      match check_clash_tree f t2 live flive with
        NONE -> NONE
      | SOME (t2_out,ft2_out) -> check_clash_tree f t1 t2_out ft2_out)`;;

(* --
compile clash_trees into a register allocator state
This produces two sptrees that re-map clash_tree variables
into the register allocator state, and vice versa
The second remap is probably not necessary?
-- *)

(* Map clash tree variables into allocator nodes, also computes the
  size of the array required
  ta = to allocator
  fa = from allocator
  nv = next fresh name
*)
let list_remap_def = cake_def
  `(list_remap [] (ta,fa,nv) = (ta,fa,nv)) /\
   (list_remap (CONS x xs) (ta:num spt,fa:num spt,nv:num) =
      match lookup x ta with
        SOME v -> list_remap xs (ta,fa,nv)
      | NONE -> list_remap xs (insert x nv ta,insert nv x fa,nv + 1))`;;

let mk_bij_aux_def = cake_def
  `(mk_bij_aux (Delta writes reads) tfn =
      list_remap writes (list_remap reads tfn)) /\
   (mk_bij_aux (reg_alloc_Set t) tfn =
      list_remap (MAP FST (toAList t)) tfn) /\
   (mk_bij_aux (reg_alloc_Branch topt t1 t2) tfn =
      let tfn' = mk_bij_aux t2 (mk_bij_aux t1 tfn) in
      match topt with
        NONE -> tfn'
      | SOME ts -> list_remap (MAP FST (toAList ts)) tfn') /\
   (mk_bij_aux (reg_alloc_Seq t1 t2) tfn =
      mk_bij_aux t1 (mk_bij_aux t2 tfn))`;;

(* HOL4 comment: hide the sptree implementation,                          *)
(* ((\i. lookup_any i ta 0),(\i. lookup_any i fa 0), n)                   *)
let mk_bij_def = cake_def
  `mk_bij t =
     let (ta,fa,n) = mk_bij_aux t (LN,LN,0) in
     (ta,fa,n)`;;

(*Distinguish 3 kinds of variables:
  Evens are physical registers
  4n+1 are allocatable registers
  4n+3 are stack registers*)

let is_stack_var_def = cake_def
  `is_stack_var (n:num) <=> n MOD 4 = 3`;;

let is_phy_var_def = cake_def
  `is_phy_var (n:num) <=> n MOD 2 = 0`;;

let is_alloc_var_def = cake_def
  `is_alloc_var (n:num) <=> n MOD 4 = 1`;;

let convention_partitions = prove
 (`!n. (is_stack_var n <=> ~is_phy_var n /\ ~is_alloc_var n) /\
       (is_phy_var n <=> ~is_stack_var n /\ ~is_alloc_var n) /\
       (is_alloc_var n <=> ~is_phy_var n /\ ~is_stack_var n)`,
  GEN_TAC THEN REWRITE_TAC[is_stack_var_def; is_phy_var_def; is_alloc_var_def] THEN
  SUBGOAL_THEN `n MOD 2 = (n MOD 4) MOD 2` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; MOD_MOD]; ALL_TAC] THEN
  SUBGOAL_THEN `n MOD 4 < 4` MP_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`n MOD 4`,`m:num`) THEN
  REWRITE_TAC[ARITH_RULE `m < 4 <=> m = 0 \/ m = 1 \/ m = 2 \/ m = 3`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Set the tags according to wordLang conventions *)
let mk_tags_def = cake_def
  `mk_tags n (fs:1 spt) fa =
     st_ex_bind (st_ex_return (list_of_seq (\x. x) n)) (\inds.
     st_ex_FOREACH inds
       (\i.
          let v = fa i in
          let remainder = v MOD 4 in
          if remainder = 1 then
            (match lookup v fs with
               NONE -> update_node_tag i Atemp
             | SOME (_:1) -> update_node_tag i Stemp)
          else if remainder = 3 then update_node_tag i Stemp
          else update_node_tag i (Fixed (v DIV 2))))`;;

(* Initializes the clash_graph using a clash_tree and a remapping bijection *)
let mk_graph_def = cake_def
  `(mk_graph ta (Delta w r) liveout =
      st_ex_bind (st_ex_return (MAP ta w)) (\wta.
      st_ex_bind (st_ex_return (MAP ta r)) (\rta.
      st_ex_bind (extend_clique wta liveout) (\live.
      st_ex_bind (st_ex_return (FILTER (\x. ~MEM x wta) live)) (\live.
      st_ex_bind (extend_clique rta live) (\livein.
      st_ex_return livein)))))) /\
   (mk_graph ta (reg_alloc_Set t) liveout =
      st_ex_bind (st_ex_return (MAP ta (MAP FST (toAList t)))) (\live.
      st_ex_ignore_bind (clique_insert_edge live) (st_ex_return live))) /\
   (mk_graph ta (reg_alloc_Branch topt t1 t2) liveout =
      st_ex_bind (mk_graph ta t1 liveout) (\t1_live.
      st_ex_bind (mk_graph ta t2 liveout) (\t2_live.
      match topt with
        NONE ->
          st_ex_bind (extend_clique t1_live t2_live) (\livein.
          st_ex_return livein)
      | SOME t ->
          st_ex_bind (st_ex_return (MAP ta (MAP FST (toAList t)))) (\clashes.
          st_ex_ignore_bind (clique_insert_edge clashes)
                            (st_ex_return clashes))))) /\
   (mk_graph ta (reg_alloc_Seq t1 t2) liveout =
      st_ex_bind (mk_graph ta t2 liveout) (\live.
      mk_graph ta t1 live))`;;

let sp_default_def = cake_def
  `sp_default t i =
     match lookup i t with
       NONE -> if is_phy_var i then i DIV 2 else 0
     | SOME x -> x`;;

let extend_graph_def = cake_def
  `(extend_graph (ta:A->num) [] = st_ex_return one) /\
   (extend_graph ta (CONS (x,y) xs) =
      st_ex_ignore_bind (insert_edge (ta x) (ta y)) (extend_graph ta xs))`;;

(* sets up the register allocator init state with the clash_tree input
  TODO: should the sptrees be hidden right away?
  It might be easier to transfer an sptree directly for the oracle register
  allocator

  ct = clash_tree
  forced = forced edges -- will need new proof that all forced edges are in the tree
  (mk_graph puts in the usual edges)
*)
let init_ra_state_def = cake_def
  `init_ra_state ct forced fs (ta,fa,n) =
     st_ex_ignore_bind (mk_graph (sp_default ta) ct [])
     (st_ex_ignore_bind (extend_graph (sp_default ta) forced)
     (mk_tags n fs (sp_default fa)))`;;

(* work around translator bug *)
let do_upd_coalesce_def = cake_def
  `do_upd_coalesce i = update_coalesced i (0 + i)`;;

(* Initializer for the first allocation step: make sure move_related is  *)
(* correct, only allocate Atemps, set the degree of each node             *)
let init_alloc1_heu_def = cake_def
  `init_alloc1_heu moves d k =
     st_ex_bind (st_ex_return (COUNT_LIST d)) (\ds.
     st_ex_bind (st_ex_FILTER is_Atemp ds []) (\allocs.
     st_ex_ignore_bind
       (st_ex_FOREACH ds
          (\i.
             st_ex_bind (adj_ls_sub i) (\adjls.
             st_ex_bind (st_ex_FILTER (\v. considered_var k v) adjls []) (\fills.
             update_degrees i (LENGTH fills)))))
     (st_ex_ignore_bind (st_ex_FOREACH ds do_upd_coalesce)
     (st_ex_ignore_bind (set_avail_moves_wl (reg_alloc_sort_moves moves))
     (st_ex_ignore_bind (reset_move_related moves)
     (st_ex_bind (st_ex_PARTITION (split_degree d k) allocs [] []) (\p.
      match p with (ltk,gtk) ->
      st_ex_bind (st_ex_PARTITION move_related_sub ltk [] []) (\p.
      match p with (ltkfreeze,ltksimp) ->
      st_ex_ignore_bind (set_spill_wl gtk)
      (st_ex_ignore_bind (set_simp_wl ltksimp)
      (st_ex_ignore_bind (set_freeze_wl ltkfreeze)
      (st_ex_return (LENGTH allocs))))))))))))`;;

let do_alloc1_def = cake_def
  `do_alloc1 moves scost k =
     st_ex_bind get_dim (\d.
     st_ex_bind (init_alloc1_heu moves d k) (\l.
     st_ex_ignore_bind (rpt_do_step scost k l)
     (st_ex_bind reg_alloc_get_stack (\st.
      st_ex_return st))))`;;

(* never happens *)
let extract_tag_def = cake_def
  `extract_tag t = match t with Fixed m -> m | _ -> 0`;;

(* return the final coloring as an sptree (can make the sptree directly) *)
let extract_color_def = cake_def
  `extract_color ta =
     st_ex_bind (st_ex_return (toAList ta)) (\taa.
     st_ex_bind
       (st_ex_MAP (\kv. match kv with
                          (k,v) -> st_ex_bind (node_tag_sub v) (\t.
                                   st_ex_return (k,extract_tag t))) taa) (\itags.
     st_ex_return (fromAList itags)))`;;

let pri_move_insert_def = cake_def
  `pri_move_insert (p:A) x (y:B) acc =
     match lookup x acc with
       NONE -> insert x [(p,y)] acc
     | SOME ls -> insert x (CONS (p,y) ls) acc`;;

let undir_move_insert_def = cake_def
  `undir_move_insert (p:A) x y acc =
     pri_move_insert p x y (pri_move_insert p y x acc)`;;

let moves_to_sp_def = cake_def
  `(moves_to_sp [] (acc:((A#num)list)spt) = acc) /\
   (moves_to_sp (CONS move xs) acc =
      let (p,x,y) = move in
      moves_to_sp xs (undir_move_insert p x y acc))`;;

(*Do a consistency sort after setting up the sptree of moves*)
let resort_moves_def = cake_def
  `resort_moves (acc:((num#A)list)spt) =
     sptree_map (\ls. MAP SND (reg_alloc_sort_moves ls)) acc`;;

let algorithm_INDUCT,algorithm_RECURSION = cake_type
  "algorithm = reg_alloc_Simple | IRC";;

(* Read-only version of coalesce_parent: follows the coalesce chain
   to the root without path compression. Safe for use in biased_pref
   where state must not be modified. *)
let coalesce_root_def = cake_def_wf `MEASURE (\x:num. x)` TERM_TAC
  `coalesce_root x =
     st_ex_bind (coalesced_sub x) (\xt.
     st_ex_bind (is_Fixed xt) (\bx.
     if bx then st_ex_return xt
     else if x <= xt then st_ex_return x
     else coalesce_root xt))`;;

(* mtable is an sptree lookup for the moves *)
let biased_pref_def = cake_def
  `biased_pref mtable n ks =
     st_ex_bind get_dim (\d.
     if n < d then
       st_ex_bind (coalesce_root n) (\v.
       let vs = (match lookup n mtable with NONE -> [] | SOME vs -> vs) in
       reg_alloc_handle_Subscript (first_match_col ks (CONS v vs))
                                  (st_ex_return NONE))
     else st_ex_return NONE)`;;

(* very similar to consistency_ok, but for initializing *)
let full_consistency_ok_def = cake_def
  `full_consistency_ok k x y =
     if x = y then st_ex_return F
     else
       st_ex_bind get_dim (\d.
       if x >= d \/ y >= d then st_ex_return F
       else
         st_ex_bind (adj_ls_sub y) (\adjy.
         if sorted_mem x adjy then st_ex_return F
         else
           st_ex_bind (is_Fixed_k k x) (\bx.
           st_ex_bind (is_Fixed_k k y) (\by.
           st_ex_bind (is_Atemp x) (\ax.
           st_ex_bind (is_Atemp y) (\ay.
           st_ex_return ((bx \/ ax) /\ (by \/ ay) /\ ~(bx /\ by))))))))`;;

let update_move_def = cake_def
  `update_move spta (p:num,(x:num,y:num)) =
     let spx:num = spta x in
     let spy:num = spta y in
     if spx <= spy then (p,(spx,spy)) else (p,(spy,spx))`;;

(* These behave in reverse to their other versions *)
let neg_first_match_col_def = cake_def
  `(neg_first_match_col k bads [] = st_ex_return NONE) /\
   (neg_first_match_col k bads (CONS x xs) =
      st_ex_bind (node_tag_sub x) (\c.
      match c with
        Fixed m -> if MEM m bads \/ m < k then neg_first_match_col k bads xs
                   else st_ex_return (SOME m)
      | _ -> neg_first_match_col k bads xs))`;;

let neg_biased_pref_def = cake_def
  `neg_biased_pref k mtable n bads =
     st_ex_bind get_dim (\d.
     if n < d then
       let vs = (match lookup n mtable with NONE -> [] | SOME vs -> vs) in
       reg_alloc_handle_Subscript (neg_first_match_col k bads vs)
                                  (st_ex_return NONE)
     else st_ex_return NONE)`;;

(* Putting everything together in one call; returns the composed map from *)
(* wordLang into the graph and the allocation                             *)
let do_reg_alloc_def = cake_def
  `do_reg_alloc alg scost k moves ct forced fs (ta,fa,n) =
     st_ex_ignore_bind (init_ra_state ct forced fs (ta,fa,n))
     (st_ex_bind (st_ex_return (MAP (update_move (sp_default ta)) moves)) (\moves0.
      st_ex_bind (st_ex_FILTER (\m. match m with (_,(x,y)) -> full_consistency_ok k x y)
                               moves0 []) (\moves.
      st_ex_bind (do_alloc1 (if alg = reg_alloc_Simple then [] else moves) scost k)
        (\ls.
      st_ex_bind (st_ex_return (resort_moves (moves_to_sp moves0 LN))) (\mvs.
      st_ex_ignore_bind (assign_Atemps k ls (biased_pref mvs))
      (st_ex_ignore_bind (assign_Stemps k (neg_biased_pref k mvs))
      (st_ex_bind (extract_color ta) (\spcol.
       st_ex_return spcol))))))))`;;

(* As we are using fixed-size array, we need to define a different record *)
(* type for the initialization (HOL4 define_run with the array fields     *)
(* adj_ls, node_tag, degrees, coalesced, move_related: each becomes a     *)
(* pair (size, initial element))                                          *)

let ira_state_INFO = cake_record "ira_state"
  ["adj_ls","num#(num list)";
   "node_tag","num#reg_alloc_tag";
   "degrees","num#num";
   "dim","num";
   "simp_wl","num list";
   "spill_wl","num list";
   "freeze_wl","num list";
   "avail_moves_wl","(num#num#num)list";
   "unavail_moves_wl","(num#num#num)list";
   "coalesced","num#num";
   "move_related","num#bool";
   "stack","num list"];;

let ira_state_component_equality = ira_state_INFO.ri_component_equality;;

let run_ira_state_def = cake_def
  `run_ira_state (x:ra_state->(B,C)exc#ra_state) state =
     ml_monadBase_run x
       (ra_state_REC
          (REPLICATE (FST (ira_state_adj_ls state)) (SND (ira_state_adj_ls state)))
          (REPLICATE (FST (ira_state_node_tag state)) (SND (ira_state_node_tag state)))
          (REPLICATE (FST (ira_state_degrees state)) (SND (ira_state_degrees state)))
          (ira_state_dim state)
          (ira_state_simp_wl state)
          (ira_state_spill_wl state)
          (ira_state_freeze_wl state)
          (ira_state_avail_moves_wl state)
          (ira_state_unavail_moves_wl state)
          (REPLICATE (FST (ira_state_coalesced state)) (SND (ira_state_coalesced state)))
          (REPLICATE (FST (ira_state_move_related state))
                     (SND (ira_state_move_related state)))
          (ira_state_stack state))`;;

(* The top-level (non-monadic) reg_alloc call which should be modified to fit
   the translator's requirements *)

let reg_alloc_aux_def = cake_def
  `reg_alloc_aux alg scost k moves ct forced fs (ta,fa,n) =
     run_ira_state (do_reg_alloc alg scost k moves ct forced fs (ta,fa,n))
       (ira_state_REC (n,[]) (n,Atemp) (n,0) n [] [] [] [] [] (n,0) (n,F) [])`;;

let reg_alloc_def = cake_def
  `reg_alloc alg scost k moves ct forced fs =
     reg_alloc_aux alg scost k moves ct forced fs (mk_bij ct)`;;
