(* ========================================================================= *)
(* linear_scan: port of HOL4 compiler/backend/reg_alloc/linear_scanScript.sml *)
(* (CakeML v3479).  A linear-scan register allocator.                        *)
(*                                                                           *)
(* Notes on the rendering (see also the header of reg_alloc.ml):             *)
(* - HOL4's do-notation is written with st_ex_bind, st_ex_ignore_bind and    *)
(*   st_ex_return; HOL4 () is one; HOL4 int literals n are &n.               *)
(* - The ML automation of ml_monadBaseLib (define_monad_access_funs,         *)
(*   define_monad_exception_functions, define_MFarray_manip_funs,            *)
(*   define_run) is replaced by the definitions it makes, for the state      *)
(*   linear_scan_hidden_state and reg_alloc's exception type state_exn:      *)
(*   get_f, set_f, f_length, f_sub, update_f for the fields f, the           *)
(*   exception functions linear_scan_raise_Fail, linear_scan_handle_Fail,    *)
(*   linear_scan_raise_Subscript, linear_scan_handle_Subscript (HOL4         *)
(*   raise_Fail, ...: separate constants from reg_alloc's), the record       *)
(*   i_linear_scan_hidden_state and run_i_linear_scan_hidden_state.          *)
(* - Record literals are rec_REC with the values in field order; an update   *)
(*   r with <| f1 := v1; f2 updated_by g |> is                               *)
(*   rec_f1_fupd (K v1) (rec_f2_fupd g r), as HOL4 parses it.                *)
(* - HOL4 ($+1) is ((+) 1) and ($<> col) is (\x. ~(col = x)); set is         *)
(*   set_of_list; paired lambdas are lambdas over a match.                   *)
(* - The HOL4 variable abs (an interface name in HOL Light) is abs'.         *)
(* - The Termination relations of HOL4 are given to cake_def_wf; a few      *)
(*   definitions with many arguments get an explicit measure as well (the   *)
(*   kit's automatic search is slow for them).                               *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mllist.ml";;
needs "hol4/sptree.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "hol4/state_transformer.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

type_invention_error := true;;

let live_tree_INDUCT,live_tree_RECURSION = cake_type
  "live_tree = Writes (num list)
             | Reads (num list)
             | linear_scan_Branch live_tree live_tree
             | linear_scan_Seq live_tree live_tree";;

(* HOL4: numset_list_insert *)
let linear_scan_numset_list_insert_def = cake_def
  `(linear_scan_numset_list_insert [] (t:1 spt) = t) /\
   (linear_scan_numset_list_insert (CONS x xs) t =
      linear_scan_numset_list_insert xs (insert x one t))`;;

let numset_list_insert_nottailrec_def = cake_def
  `(numset_list_insert_nottailrec [] (t:1 spt) = t) /\
   (numset_list_insert_nottailrec (CONS x xs) t =
      insert x one (numset_list_insert_nottailrec xs t))`;;

let get_live_tree_def = cake_def
  `(get_live_tree (Delta wr rd) = linear_scan_Seq (Reads rd) (Writes wr)) /\
   (get_live_tree (reg_alloc_Set cutset) =
      let cutlist = MAP FST (toAList cutset) in
      Reads cutlist) /\
   (get_live_tree (reg_alloc_Branch optcutset ct1 ct2) =
      let lt1 = get_live_tree ct1 in
      let lt2 = get_live_tree ct2 in
      match optcutset with
        SOME cutset ->
          let cutlist = MAP FST (toAList cutset) in
          linear_scan_Seq (Reads cutlist) (linear_scan_Branch lt1 lt2)
      | NONE -> linear_scan_Branch lt1 lt2) /\
   (get_live_tree (reg_alloc_Seq ct1 ct2) =
      let lt2 = get_live_tree ct2 in
      let lt1 = get_live_tree ct1 in
      linear_scan_Seq lt1 lt2)`;;

let check_live_tree_def = cake_def
  `(check_live_tree f (Writes l) live flive =
      match check_partial_col f l live flive with
        NONE -> NONE
      | SOME _ ->
          let livein = numset_list_delete l live in
          let flivein = numset_list_delete (MAP f l) flive in
          SOME (livein,flivein)) /\
   (check_live_tree f (Reads l) live flive = check_partial_col f l live flive) /\
   (check_live_tree f (linear_scan_Branch lt1 lt2) live flive =
      match check_live_tree f lt1 live flive with
        NONE -> NONE
      | SOME (livein1,flivein1) ->
          (match check_live_tree f lt2 live flive with
             NONE -> NONE
           | SOME (livein2,flivein2) ->
               check_partial_col f (MAP FST (toAList (difference livein2 livein1)))
                 livein1 flivein1)) /\
   (check_live_tree f (linear_scan_Seq lt1 lt2) live flive =
      match check_live_tree f lt2 live flive with
        NONE -> NONE
      | SOME (livein2,flivein2) -> check_live_tree f lt1 livein2 flivein2)`;;

let get_live_backward_def = cake_def
  `(get_live_backward (Writes l) live = numset_list_delete l live) /\
   (get_live_backward (Reads l) live = linear_scan_numset_list_insert l live) /\
   (get_live_backward (linear_scan_Branch lt1 lt2) live =
      let live1 = get_live_backward lt1 live in
      let live2 = get_live_backward lt2 live in
      linear_scan_numset_list_insert (MAP FST (toAList (difference live2 live1))) live1) /\
   (get_live_backward (linear_scan_Seq lt1 lt2) live =
      get_live_backward lt1 (get_live_backward lt2 live))`;;

let fix_domination_def = cake_def
  `fix_domination lt =
     let live = get_live_backward lt LN in
     if live = LN then lt
     else linear_scan_Seq (Writes (MAP FST (toAList live))) lt`;;

let numset_list_add_if_def = cake_def
  `(numset_list_add_if [] (v:int) s P = s) /\
   (numset_list_add_if (CONS x xs) v s P =
      match lookup x s with
        SOME v' ->
          if P v v' then numset_list_add_if xs v (insert x v s) P
          else numset_list_add_if xs v s P
      | NONE -> numset_list_add_if xs v (insert x v s) P)`;;

let numset_list_add_if_lt_def = cake_def
  `numset_list_add_if_lt l (v:int) s = numset_list_add_if l v s (<=)`;;

let numset_list_add_if_gt_def = cake_def
  `numset_list_add_if_gt l (v:int) s = numset_list_add_if l v s (\a b. b <= a)`;;

let size_of_live_tree_def = cake_def
  `(size_of_live_tree (Writes l) = &1:int) /\
   (size_of_live_tree (Reads l) = &1) /\
   (size_of_live_tree (linear_scan_Branch lt1 lt2) =
      size_of_live_tree lt1 + size_of_live_tree lt2) /\
   (size_of_live_tree (linear_scan_Seq lt1 lt2) =
      size_of_live_tree lt1 + size_of_live_tree lt2)`;;

let get_intervals_def = cake_def
  `(get_intervals (Writes l) (n:int) int_beg int_end =
      (n - &1,numset_list_add_if_lt l n int_beg,numset_list_add_if_gt l n int_end)) /\
   (get_intervals (Reads l) n int_beg int_end =
      (n - &1,int_beg,numset_list_add_if_gt l n int_end)) /\
   (get_intervals (linear_scan_Branch lt1 lt2) n int_beg int_end =
      let (n2,int_beg2,int_end2) = get_intervals lt2 n int_beg int_end in
      get_intervals lt1 n2 int_beg2 int_end2) /\
   (get_intervals (linear_scan_Seq lt1 lt2) n int_beg int_end =
      let (n2,int_beg2,int_end2) = get_intervals lt2 n int_beg int_end in
      get_intervals lt1 n2 int_beg2 int_end2)`;;

(* computes the same thing as get_intervals (as says the                    *)
(* get_intervals_withlive_beg_eq_get_intervals_beg theorem), but has the    *)
(* following invariant: !r. r IN domain live ==> r NOTIN domain beg_in (as  *)
(* stated by the get_intervals_withlive_live_intbeg theorem)                *)
let get_intervals_withlive_def = cake_def
  `(get_intervals_withlive (Writes l) (n:int) int_beg int_end (live:1 spt) =
      (n - &1,numset_list_add_if_lt l n int_beg,numset_list_add_if_gt l n int_end)) /\
   (get_intervals_withlive (Reads l) n int_beg int_end live =
      (n - &1,numset_list_delete l int_beg,numset_list_add_if_gt l n int_end)) /\
   (get_intervals_withlive (linear_scan_Branch lt1 lt2) n int_beg int_end live =
      let (n2,int_beg2,int_end2) =
        get_intervals_withlive lt2 n int_beg int_end live in
      let (n1,int_beg1,int_end1) =
        get_intervals_withlive lt1 n2 (difference int_beg2 live) int_end2 live in
      (n1,difference int_beg1 (sptree_union (get_live_backward lt1 live)
                                     (get_live_backward lt2 live)),int_end1)) /\
   (get_intervals_withlive (linear_scan_Seq lt1 lt2) n int_beg int_end live =
      let (n2,int_beg2,int_end2) =
        get_intervals_withlive lt2 n int_beg int_end live in
      let (n1,int_beg1,int_end1) =
        get_intervals_withlive lt1 n2 int_beg2 int_end2 (get_live_backward lt2 live) in
      (n1,int_beg1,int_end1))`;;

let check_number_property_def = cake_def
  `(check_number_property (P:int->1 spt->bool) (Writes l) n live =
      let n_out = n - &1 in
      let live_out = numset_list_delete l live in
      P n_out live_out) /\
   (check_number_property P (Reads l) n live =
      let n_out = n - &1 in
      let live_out = linear_scan_numset_list_insert l live in
      P n_out live_out) /\
   (check_number_property P (linear_scan_Branch lt1 lt2) n live =
      let r2 = check_number_property P lt2 n live in
      let r1 = check_number_property P lt1 (n - size_of_live_tree lt2) live in
      r1 /\ r2) /\
   (check_number_property P (linear_scan_Seq lt1 lt2) n live =
      let r2 = check_number_property P lt2 n live in
      let r1 = check_number_property P lt1 (n - size_of_live_tree lt2)
                 (get_live_backward lt2 live) in
      r1 /\ r2)`;;

let check_number_property_strong_def = cake_def
  `(check_number_property_strong (P:int->1 spt->bool) (Writes l) n live =
      let n_out = n - &1 in
      let live_out = numset_list_delete l live in
      P n_out live_out) /\
   (check_number_property_strong P (Reads l) n live =
      let n_out = n - &1 in
      let live_out = linear_scan_numset_list_insert l live in
      P n_out live_out) /\
   (check_number_property_strong P (linear_scan_Branch lt1 lt2) n live =
      let r2 = check_number_property_strong P lt2 n live in
      let r1 = check_number_property_strong P lt1 (n - size_of_live_tree lt2) live in
      r1 /\ r2 /\
      P (n - size_of_live_tree (linear_scan_Branch lt1 lt2))
        (get_live_backward (linear_scan_Branch lt1 lt2) live)) /\
   (check_number_property_strong P (linear_scan_Seq lt1 lt2) n live =
      let r2 = check_number_property_strong P lt2 n live in
      let r1 = check_number_property_strong P lt1 (n - size_of_live_tree lt2)
                 (get_live_backward lt2 live) in
      r1 /\ r2)`;;

let check_startlive_prop_def = cake_def
  `(check_startlive_prop (Writes l) (n:int) beg end (ndef:int) <=>
      !r. MEM r l ==> (option_CASE (lookup r beg) ndef (\x. x) <= n /\
                       (?v. lookup r end = SOME v /\ n <= v))) /\
   (check_startlive_prop (Reads l) n beg end ndef <=> T) /\
   (check_startlive_prop (linear_scan_Branch lt1 lt2) n beg end ndef <=>
      let r2 = check_startlive_prop lt2 n beg end ndef in
      let r1 = check_startlive_prop lt1 (n - size_of_live_tree lt2) beg end ndef in
      r1 /\ r2) /\
   (check_startlive_prop (linear_scan_Seq lt1 lt2) n beg end ndef <=>
      let r2 = check_startlive_prop lt2 n beg end ndef in
      let r1 = check_startlive_prop lt1 (n - size_of_live_tree lt2) beg end ndef in
      r1 /\ r2)`;;

let live_tree_registers_def = cake_def
  `(live_tree_registers (Writes l) = set_of_list l) /\
   (live_tree_registers (Reads l) = set_of_list l) /\
   (live_tree_registers (linear_scan_Branch lt1 lt2) =
      live_tree_registers lt1 UNION live_tree_registers lt2) /\
   (live_tree_registers (linear_scan_Seq lt1 lt2) =
      live_tree_registers lt1 UNION live_tree_registers lt2)`;;

let interval_intersect_def = cake_def
  `interval_intersect (l1:int,r1:int) (l2,r2) <=> l1 <= r2 /\ l2 <= r1`;;

let point_inside_interval_def = cake_def
  `point_inside_interval (l:int,r:int) n <=> l <= n /\ n <= r`;;

let check_intervals_def = cake_def
  `check_intervals (f:num->A) (int_beg:int spt) (int_end:int spt) <=>
     !r1 r2.
       r1 IN domain int_beg /\ r2 IN domain int_beg /\
       interval_intersect (THE (lookup r1 int_beg),THE (lookup r1 int_end))
                          (THE (lookup r2 int_beg),THE (lookup r2 int_end)) /\
       f r1 = f r2
       ==> r1 = r2`;;

let get_intervals_ct_aux_def = cake_def
  `(get_intervals_ct_aux (Delta wr rd) (n:int) int_beg int_end live =
      (n - &2,numset_list_add_if_lt wr n int_beg,
       numset_list_add_if_gt rd (n - &1) (numset_list_add_if_gt wr n int_end),
       linear_scan_numset_list_insert rd (numset_list_delete wr live))) /\
   (get_intervals_ct_aux (reg_alloc_Set cutset) n int_beg int_end live =
      (n - &1,int_beg,numset_list_add_if_gt (MAP FST (toAList cutset)) n int_end,
       sptree_union cutset live)) /\
   (get_intervals_ct_aux (reg_alloc_Branch optcutset ct1 ct2) n int_beg int_end live =
      let (n2,int_beg2,int_end2,live2) =
        get_intervals_ct_aux ct2 n int_beg int_end live in
      let (n1,int_beg1,int_end1,live1) =
        get_intervals_ct_aux ct1 n2 int_beg2 int_end2 live in
      match optcutset with
        NONE -> (n1,int_beg1,int_end1,sptree_union live1 live2)
      | SOME cutset ->
          (n1 - &1,int_beg1,
           numset_list_add_if_gt (MAP FST (toAList cutset)) n1 int_end1,
           sptree_union cutset (sptree_union live1 live2))) /\
   (get_intervals_ct_aux (reg_alloc_Seq ct1 ct2) n int_beg int_end live =
      let (n2,int_beg2,int_end2,live2) =
        get_intervals_ct_aux ct2 n int_beg int_end live in
      get_intervals_ct_aux ct1 n2 int_beg2 int_end2 live2)`;;

let get_intervals_ct_def = cake_def
  `get_intervals_ct ct =
     let (n,int_beg,int_end,live) = get_intervals_ct_aux ct (&0) LN LN LN in
     let listlive = MAP FST (toAList live) in
     (n - &1,numset_list_add_if_lt listlive n int_beg,
      numset_list_add_if_gt listlive n int_end)`;;

(* active: interval end # reg *)
let linear_scan_state_INFO = cake_record "linear_scan_state"
  ["active","(int#num)list";
   "colorpool","num list";
   "phyregs","1 spt";
   "colornum","num";
   "colormax","num";
   "stacknum","num"];;

let linear_scan_state_component_equality =
  linear_scan_state_INFO.ri_component_equality;;

let linear_scan_hidden_state_INFO = cake_record "linear_scan_hidden_state"
  ["colors","num list";
   "int_beg","int list";
   "int_end","int list";
   "sorted_regs","num list";
   "sorted_moves","(num#num#num)list"];;

let linear_scan_hidden_state_component_equality =
  linear_scan_hidden_state_INFO.ri_component_equality;;

(* HOL4 define_monad_access_funs: get_f and set_f for every field f *)
let get_colors_def = cake_def
  `(get_colors:linear_scan_hidden_state->(num list,C)exc#linear_scan_hidden_state) =
     \state. (M_success (linear_scan_hidden_state_colors state),state)`;;

let get_int_beg_def = cake_def
  `(get_int_beg:linear_scan_hidden_state->(int list,C)exc#linear_scan_hidden_state) =
     \state. (M_success (linear_scan_hidden_state_int_beg state),state)`;;

let get_int_end_def = cake_def
  `(get_int_end:linear_scan_hidden_state->(int list,C)exc#linear_scan_hidden_state) =
     \state. (M_success (linear_scan_hidden_state_int_end state),state)`;;

let get_sorted_regs_def = cake_def
  `(get_sorted_regs:linear_scan_hidden_state->(num list,C)exc#linear_scan_hidden_state) =
     \state. (M_success (linear_scan_hidden_state_sorted_regs state),state)`;;

let get_sorted_moves_def = cake_def
  `(get_sorted_moves:linear_scan_hidden_state->((num#num#num)list,C)exc#linear_scan_hidden_state) =
     \state. (M_success (linear_scan_hidden_state_sorted_moves state),state)`;;

let set_colors_def = cake_def
  `(set_colors:num list->linear_scan_hidden_state->(1,C)exc#linear_scan_hidden_state) x =
     \state. (M_success one,linear_scan_hidden_state_colors_fupd (combin_K x) state)`;;

let set_int_beg_def = cake_def
  `(set_int_beg:int list->linear_scan_hidden_state->(1,C)exc#linear_scan_hidden_state) x =
     \state. (M_success one,linear_scan_hidden_state_int_beg_fupd (combin_K x) state)`;;

let set_int_end_def = cake_def
  `(set_int_end:int list->linear_scan_hidden_state->(1,C)exc#linear_scan_hidden_state) x =
     \state. (M_success one,linear_scan_hidden_state_int_end_fupd (combin_K x) state)`;;

let set_sorted_regs_def = cake_def
  `(set_sorted_regs:num list->linear_scan_hidden_state->(1,C)exc#linear_scan_hidden_state) x =
     \state. (M_success one,linear_scan_hidden_state_sorted_regs_fupd (combin_K x) state)`;;

let set_sorted_moves_def = cake_def
  `(set_sorted_moves:
      (num#num#num)list->linear_scan_hidden_state->(1,C)exc#linear_scan_hidden_state) x =
     \state. (M_success one,linear_scan_hidden_state_sorted_moves_fupd (combin_K x) state)`;;


(* HOL4 reuses reg_alloc's Datatype state_exn = Fail string | Subscript *)

(* Monadic functions to handle the exceptions (HOL4                          *)
(* define_monad_exception_functions; HOL4 also overloads failwith for        *)
(* raise_Fail)                                                               *)

let linear_scan_raise_Fail_def = cake_def
  `linear_scan_raise_Fail (e1:string) =
     \state:linear_scan_hidden_state.
       (M_failure (reg_alloc_Fail e1):(A,state_exn)exc,state)`;;

let linear_scan_raise_Subscript_def = cake_def
  `linear_scan_raise_Subscript =
     \state:linear_scan_hidden_state. (M_failure Subscript:(A,state_exn)exc,state)`;;

let linear_scan_handle_Fail_def = cake_def
  `linear_scan_handle_Fail
     (x:linear_scan_hidden_state->(A,state_exn)exc#linear_scan_hidden_state)
     (f:string->linear_scan_hidden_state->(A,state_exn)exc#linear_scan_hidden_state) =
     \state. match x state with
               (res,state) ->
                 (match res with
                    M_success y -> (M_success y,state)
                  | M_failure e ->
                      (match e with
                         reg_alloc_Fail e1 -> f e1 state
                       | Subscript -> (M_failure Subscript,state)))`;;

let linear_scan_handle_Subscript_def = cake_def
  `linear_scan_handle_Subscript
     (x:linear_scan_hidden_state->(A,state_exn)exc#linear_scan_hidden_state)
     (f:linear_scan_hidden_state->(A,state_exn)exc#linear_scan_hidden_state) =
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

let colors_length_def = cake_def
  `(colors_length:linear_scan_hidden_state->(num,C)exc#linear_scan_hidden_state) =
     Marray_length (\state. linear_scan_hidden_state_colors state)`;;

let colors_sub_def = cake_def
  `colors_sub =
     Marray_sub (\state:linear_scan_hidden_state. linear_scan_hidden_state_colors state)
       Subscript`;;

let update_colors_def = cake_def
  `update_colors =
     Marray_update (\state:linear_scan_hidden_state. linear_scan_hidden_state_colors state)
       (\x state. linear_scan_hidden_state_colors_fupd (combin_K x) state) Subscript`;;

let int_beg_length_def = cake_def
  `(int_beg_length:linear_scan_hidden_state->(num,C)exc#linear_scan_hidden_state) =
     Marray_length (\state. linear_scan_hidden_state_int_beg state)`;;

let int_beg_sub_def = cake_def
  `int_beg_sub =
     Marray_sub (\state:linear_scan_hidden_state. linear_scan_hidden_state_int_beg state)
       Subscript`;;

let update_int_beg_def = cake_def
  `update_int_beg =
     Marray_update (\state:linear_scan_hidden_state. linear_scan_hidden_state_int_beg state)
       (\x state. linear_scan_hidden_state_int_beg_fupd (combin_K x) state) Subscript`;;

let int_end_length_def = cake_def
  `(int_end_length:linear_scan_hidden_state->(num,C)exc#linear_scan_hidden_state) =
     Marray_length (\state. linear_scan_hidden_state_int_end state)`;;

let int_end_sub_def = cake_def
  `int_end_sub =
     Marray_sub (\state:linear_scan_hidden_state. linear_scan_hidden_state_int_end state)
       Subscript`;;

let update_int_end_def = cake_def
  `update_int_end =
     Marray_update (\state:linear_scan_hidden_state. linear_scan_hidden_state_int_end state)
       (\x state. linear_scan_hidden_state_int_end_fupd (combin_K x) state) Subscript`;;

let sorted_regs_length_def = cake_def
  `(sorted_regs_length:linear_scan_hidden_state->(num,C)exc#linear_scan_hidden_state) =
     Marray_length (\state. linear_scan_hidden_state_sorted_regs state)`;;

let sorted_regs_sub_def = cake_def
  `sorted_regs_sub =
     Marray_sub (\state:linear_scan_hidden_state. linear_scan_hidden_state_sorted_regs state)
       Subscript`;;

let update_sorted_regs_def = cake_def
  `update_sorted_regs =
     Marray_update (\state:linear_scan_hidden_state. linear_scan_hidden_state_sorted_regs state)
       (\x state. linear_scan_hidden_state_sorted_regs_fupd (combin_K x) state) Subscript`;;

let sorted_moves_length_def = cake_def
  `(sorted_moves_length:linear_scan_hidden_state->(num,C)exc#linear_scan_hidden_state) =
     Marray_length (\state. linear_scan_hidden_state_sorted_moves state)`;;

let sorted_moves_sub_def = cake_def
  `sorted_moves_sub =
     Marray_sub (\state:linear_scan_hidden_state. linear_scan_hidden_state_sorted_moves state)
       Subscript`;;

let update_sorted_moves_def = cake_def
  `update_sorted_moves =
     Marray_update (\state:linear_scan_hidden_state. linear_scan_hidden_state_sorted_moves state)
       (\x state. linear_scan_hidden_state_sorted_moves_fupd (combin_K x) state) Subscript`;;

let colors_accessor = end_itlist CONJ
  [get_colors_def; set_colors_def;
   colors_length_def; colors_sub_def; update_colors_def];;

let int_beg_accessor = end_itlist CONJ
  [get_int_beg_def; set_int_beg_def;
   int_beg_length_def; int_beg_sub_def; update_int_beg_def];;

let int_end_accessor = end_itlist CONJ
  [get_int_end_def; set_int_end_def;
   int_end_length_def; int_end_sub_def; update_int_end_def];;

let sorted_regs_accessor = end_itlist CONJ
  [get_sorted_regs_def; set_sorted_regs_def;
   sorted_regs_length_def; sorted_regs_sub_def; update_sorted_regs_def];;

let sorted_moves_accessor = end_itlist CONJ
  [get_sorted_moves_def; set_sorted_moves_def;
   sorted_moves_length_def; sorted_moves_sub_def; update_sorted_moves_def];;


let numset_list_add_if_lt_monad_def = cake_def
  `(numset_list_add_if_lt_monad [] (v:int) = st_ex_return one) /\
   (numset_list_add_if_lt_monad (CONS r rs) v =
      st_ex_bind (int_beg_sub r) (\begr.
      if &0 < begr then
        st_ex_ignore_bind (update_int_beg r v) (numset_list_add_if_lt_monad rs v)
      else if v <= begr then
        st_ex_ignore_bind (update_int_beg r v) (numset_list_add_if_lt_monad rs v)
      else numset_list_add_if_lt_monad rs v))`;;

let numset_list_add_if_gt_monad_def = cake_def
  `(numset_list_add_if_gt_monad [] (v:int) = st_ex_return one) /\
   (numset_list_add_if_gt_monad (CONS r rs) v =
      st_ex_bind (int_end_sub r) (\begr.
      if &0 < begr then
        st_ex_ignore_bind (update_int_end r v) (numset_list_add_if_gt_monad rs v)
      else if begr <= v then
        st_ex_ignore_bind (update_int_end r v) (numset_list_add_if_gt_monad rs v)
      else numset_list_add_if_gt_monad rs v))`;;

let get_intervals_ct_monad_aux_def = cake_def
  `(get_intervals_ct_monad_aux (Delta wr rd) (n:int) live =
      st_ex_ignore_bind (numset_list_add_if_lt_monad wr n)
      (st_ex_ignore_bind (numset_list_add_if_gt_monad wr n)
      (st_ex_ignore_bind (numset_list_add_if_gt_monad rd (n - &1))
      (st_ex_return
         (n - &2,linear_scan_numset_list_insert rd (numset_list_delete wr live)))))) /\
   (get_intervals_ct_monad_aux (reg_alloc_Set cutset) n live =
      st_ex_ignore_bind (numset_list_add_if_gt_monad (MAP FST (toAList cutset)) n)
      (st_ex_return (n - &1,sptree_union cutset live))) /\
   (get_intervals_ct_monad_aux (reg_alloc_Branch optcutset ct1 ct2) n live =
      st_ex_bind (get_intervals_ct_monad_aux ct2 n live) (\p.
      match p with (n2,live2) ->
      st_ex_bind (get_intervals_ct_monad_aux ct1 n2 live) (\p.
      match p with (n1,live1) ->
      match optcutset with
        NONE -> st_ex_return (n1,sptree_union live1 live2)
      | SOME cutset ->
          st_ex_ignore_bind
            (numset_list_add_if_gt_monad (MAP FST (toAList cutset)) n1)
            (st_ex_return (n1 - &1,sptree_union cutset (sptree_union live1 live2)))))) /\
   (get_intervals_ct_monad_aux (reg_alloc_Seq ct1 ct2) n live =
      st_ex_bind (get_intervals_ct_monad_aux ct2 n live) (\p.
      match p with (n2,live2) ->
      get_intervals_ct_monad_aux ct1 n2 live2))`;;

let get_intervals_ct_monad_def = cake_def
  `get_intervals_ct_monad ct =
     st_ex_bind (get_intervals_ct_monad_aux ct (&0) LN) (\p.
     match p with (n,live) ->
     st_ex_ignore_bind (numset_list_add_if_lt_monad (MAP FST (toAList live)) n)
     (st_ex_ignore_bind (numset_list_add_if_gt_monad (MAP FST (toAList live)) n)
     (st_ex_return (n - &1))))`;;

(* HOL4 Termination: WF_REL_TAC measure (\(_,st). LENGTH st.active) >> rw [] *)
let remove_inactive_intervals_def = cake_def_wf
  `MEASURE (\(beg:int,st:linear_scan_state). LENGTH (linear_scan_state_active st))`
  (REWRITE_TAC[measure_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   RW[LENGTH])
  `remove_inactive_intervals beg st =
     match linear_scan_state_active st with
       [] -> st_ex_return st
     | CONS (e,r) activetail ->
         if e < beg then
           st_ex_bind (colors_sub r) (\col.
           let st' = linear_scan_state_active_fupd (combin_K activetail)
                       (linear_scan_state_colorpool_fupd (\l. CONS col l) st) in
           remove_inactive_intervals beg st')
         else st_ex_return st`;;

(* The induction theorems of this file are the kit's (cake_ind), restated *)
(* with names for the variables of the continuations (the kit's version has *)
(* the variable name y of the rule MONADAUX_ADMISSIBLE_st_ex_bind)         *)
let remove_inactive_intervals_ind = prove
 (`!P. (!beg st.
          (!r e activetail col.
             linear_scan_state_active st = CONS (e,r) activetail /\ e < beg
             ==> P beg (linear_scan_state_active_fupd (combin_K activetail)
                          (linear_scan_state_colorpool_fupd (\l. CONS col l) st)))
          ==> P beg st)
       ==> !beg st. P beg st`,
  MATCH_ACCEPT_TAC (cake_ind "remove_inactive_intervals"));;

let add_active_interval_def = cake_def
  `(add_active_interval v [] = [v]) /\
   (add_active_interval (v1:int#num) (CONS v2 tail) =
      if FST v1 <= FST v2 then CONS v1 (CONS v2 tail)
      else CONS v2 (add_active_interval v1 tail))`;;

let find_color_in_list_def = cake_def
  `(find_color_in_list [] (forbidden:1 spt) = NONE) /\
   (find_color_in_list (CONS r rs) forbidden =
      if lookup r forbidden = NONE then SOME (r,rs)
      else
        match find_color_in_list rs forbidden with
          NONE -> NONE
        | SOME (col,rest) -> SOME (col,CONS r rest))`;;

let find_color_in_colornum_def = cake_def
  `find_color_in_colornum st (forbidden:1 spt) =
     if linear_scan_state_colormax st <= linear_scan_state_colornum st then (st,NONE)
     else (linear_scan_state_colornum_fupd ((+) 1) st,
           SOME (linear_scan_state_colornum st))`;;

let find_color_def = cake_def
  `find_color st (forbidden:1 spt) =
     match find_color_in_list (linear_scan_state_colorpool st) forbidden with
       SOME (col,rest) -> (linear_scan_state_colorpool_fupd (combin_K rest) st,SOME col)
     | NONE -> find_color_in_colornum st forbidden`;;

let spill_register_def = cake_def
  `spill_register st reg =
     st_ex_ignore_bind (update_colors reg (linear_scan_state_stacknum st))
       (st_ex_return (linear_scan_state_stacknum_fupd ((+) 1) st))`;;

let color_register_def = cake_def
  `color_register st reg col (rend:int) =
     st_ex_ignore_bind (update_colors reg col)
       (if is_phy_var reg then
          st_ex_return
            (linear_scan_state_active_fupd (add_active_interval (rend,reg))
               (linear_scan_state_phyregs_fupd (insert col one) st))
        else
          st_ex_return (linear_scan_state_active_fupd (add_active_interval (rend,reg)) st))`;;

let find_last_stealable_def = cake_def
  `(find_last_stealable [] (forbidden:1 spt) = st_ex_return NONE) /\
   (find_last_stealable (CONS (x:int#num) xs) forbidden =
      st_ex_bind (find_last_stealable xs forbidden) (\recursion.
      match recursion with
        SOME (steal,rest) -> st_ex_return (SOME (steal,CONS x rest))
      | NONE ->
          st_ex_bind (colors_sub (SND x)) (\xcol.
          if ~(is_phy_var (SND x)) /\ lookup xcol forbidden = NONE then
            st_ex_return (SOME (x,xs))
          else st_ex_return NONE)))`;;

let find_spill_def = cake_def
  `find_spill st (forbidden:1 spt) reg rend force =
     st_ex_bind (find_last_stealable (linear_scan_state_active st) forbidden)
       (\stealable.
     match stealable with
       NONE -> spill_register st reg
     | SOME ((stealend,stealreg),newactive) ->
         if force \/ rend < stealend then
           st_ex_bind (colors_sub stealreg) (\stealcolor.
           st_ex_bind (spill_register (linear_scan_state_active_fupd (combin_K newactive) st)
                                      stealreg) (\st'.
           color_register st' reg stealcolor rend))
         else spill_register st reg)`;;

(* HOL4 comment: TODO: this might be slow *)
let linear_reg_alloc_step_aux_def = cake_def
  `linear_reg_alloc_step_aux st (forbidden:1 spt) preferred reg rend force =
     let preferred_filtered =
       FILTER (\c. MEM c (linear_scan_state_colorpool st)) preferred in
     match find_color_in_list preferred_filtered forbidden with
       SOME (col,_) ->
         color_register (linear_scan_state_colorpool_fupd (FILTER (\x. ~(col = x))) st)
           reg col rend
     | NONE ->
         (match find_color st forbidden with
            (st',SOME col) -> color_register st' reg col rend
          | (st',NONE) -> find_spill st' forbidden reg rend force)`;;

let linear_reg_alloc_step_pass1_def = cake_def
  `linear_reg_alloc_step_pass1 forced moves st reg =
     st_ex_bind (int_beg_sub reg) (\rbeg.
     st_ex_bind (int_end_sub reg) (\rend.
     st_ex_bind (remove_inactive_intervals rbeg st) (\st'.
     if is_stack_var reg then spill_register st' reg
     else
       st_ex_bind (st_ex_MAP colors_sub (misc_the [] (lookup reg forced)))
         (\forced_forbidden_list.
       let forced_forbidden = fromAList (MAP (\c. (c,one)) forced_forbidden_list) in
       if is_phy_var reg then
         if reg < 2 * linear_scan_state_colormax st' then
           let forbidden = sptree_union (linear_scan_state_phyregs st') forced_forbidden in
           linear_reg_alloc_step_aux st' forbidden [] reg rend T
         else spill_register st' reg
       else
         st_ex_bind (st_ex_MAP colors_sub (misc_the [] (lookup reg moves)))
           (\moves_preferred.
         linear_reg_alloc_step_aux st' forced_forbidden moves_preferred reg rend F)))))`;;

let linear_reg_alloc_step_pass2_def = cake_def
  `linear_reg_alloc_step_pass2 forced moves st reg =
     st_ex_bind (int_beg_sub reg) (\rbeg.
     st_ex_bind (int_end_sub reg) (\rend.
     st_ex_bind (remove_inactive_intervals rbeg st) (\st'.
     st_ex_bind (st_ex_MAP colors_sub (misc_the [] (lookup reg forced)))
       (\forced_forbidden_list.
     st_ex_bind (st_ex_return (fromAList (MAP (\c. (c,one)) forced_forbidden_list)))
       (\forced_forbidden.
     st_ex_bind (st_ex_MAP colors_sub (misc_the [] (lookup reg moves))) (\moves_preferred.
     if is_phy_var reg then
       let forbidden = sptree_union (linear_scan_state_phyregs st') forced_forbidden in
       linear_reg_alloc_step_aux st' forbidden [] reg rend F
     else
       linear_reg_alloc_step_aux st' forced_forbidden moves_preferred reg rend F))))))`;;

let linear_reg_alloc_pass1_initial_state_def = cake_def
  `linear_reg_alloc_pass1_initial_state k =
     linear_scan_state_REC [] [] LN 0 k k`;;

let linear_reg_alloc_pass2_initial_state_def = cake_def
  `linear_reg_alloc_pass2_initial_state k nreg =
     linear_scan_state_REC [] [] LN k (k + nreg) (k + nreg)`;;

let find_reg_exchange_def = cake_def
  `(find_reg_exchange [] exch invexch = st_ex_return (exch,invexch)) /\
   (find_reg_exchange (CONS r rs) exch invexch =
      st_ex_bind (colors_sub r) (\col1.
      let fcol1 = r DIV 2 in
      let col2 = option_CASE (lookup fcol1 invexch) fcol1 (\x. x) in
      let fcol2 = option_CASE (lookup col1 exch) col1 (\x. x) in
      find_reg_exchange rs (insert col1 fcol1 (insert col2 fcol2 exch))
                           (insert fcol1 col1 (insert fcol2 col2 invexch))))`;;

let MAP_colors_def = cake_def
  `(MAP_colors f 0 = st_ex_return one) /\
   (MAP_colors f (SUC n) =
      st_ex_bind (colors_sub n) (\col.
      st_ex_ignore_bind (update_colors n (f col)) (MAP_colors f n)))`;;

let apply_reg_exchange_def = cake_def
  `apply_reg_exchange phyregs =
     st_ex_bind (find_reg_exchange phyregs LN LN) (\p.
     match p with (exch,invexch) ->
     st_ex_bind colors_length (\col_size.
     MAP_colors (\c. option_CASE (lookup c exch) c (\x. x)) col_size))`;;

let st_ex_FOLDL_def = cake_def
  `(st_ex_FOLDL (f:B->X->S->(B,E)exc#S) e [] = st_ex_return e) /\
   (st_ex_FOLDL f e (CONS x xs) =
      st_ex_bind (f e x) (\e'. st_ex_FOLDL f e' xs))`;;

(* like st_ex_FILTER, but preserve the order *)
let st_ex_FILTER_good_def = cake_def
  `(st_ex_FILTER_good (P:X->S->(bool,E)exc#S) [] = st_ex_return []) /\
   (st_ex_FILTER_good P (CONS x xs) =
      st_ex_bind (P x) (\Px.
      if Px then
        st_ex_bind (st_ex_FILTER_good P xs) (\filter_xs.
        st_ex_return (CONS x filter_xs))
      else st_ex_FILTER_good P xs))`;;

let edges_to_adjlist_def = cake_def
  `(edges_to_adjlist [] acc = st_ex_return acc) /\
   (edges_to_adjlist (CONS (a,b) abs') acc =
      if a = b then edges_to_adjlist abs' acc
      else
        st_ex_bind (int_beg_sub a) (\bega.
        st_ex_bind (int_beg_sub b) (\begb.
        if bega < begb \/ (bega = begb /\ a <= b) then
          edges_to_adjlist abs' (insert b (CONS a (misc_the [] (lookup b acc))) acc)
        else
          edges_to_adjlist abs' (insert a (CONS b (misc_the [] (lookup a acc))) acc))))`;;

let sort_moves_rev_def = cake_def
  `sort_moves_rev (ls:(num#A)list) =
     sort (\px px'. match px with
                      (p,x) -> (match px' with (p',x') -> p < p')) ls`;;

let swap_regs_def = cake_def
  `swap_regs i1 i2 =
     st_ex_bind (sorted_regs_sub i1) (\r1.
     st_ex_bind (sorted_regs_sub i2) (\r2.
     st_ex_ignore_bind (update_sorted_regs i1 r2) (update_sorted_regs i2 r1)))`;;

(* MONADAUX_DIFF_TAC: the termination conditions of the Termination        *)
(* measures r - l of HOL4 below (WF_REL_TAC alone proves them in HOL4)      *)
let MONADAUX_DIFF_TAC : tactic =
  REWRITE_TAC[measure_THM] THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[IMP_CONJ; DE_MORGAN_THM] THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN ASM_ARITH_TAC;;

(* HOL4 Termination: WF_REL_TAC measure (\l,rpiv,begrpiv,r. r-l) *)
let partition_regs_def = cake_def_wf
  `MEASURE (\(l:num,rpiv:num,begrpiv:int,r:num). r - l)` MONADAUX_DIFF_TAC
  `partition_regs l rpiv begrpiv r =
     if r <= l then st_ex_return l
     else
       st_ex_bind (sorted_regs_sub l) (\reg.
       st_ex_bind (int_beg_sub reg) (\begreg.
       if begreg < begrpiv \/ (begreg = begrpiv /\ reg <= rpiv) then
         partition_regs (l + 1) rpiv begrpiv r
       else
         st_ex_ignore_bind (swap_regs l (r - 1))
                           (partition_regs l rpiv begrpiv (r - 1))))`;;

let partition_regs_ind = prove
 (`!P. (!l rpiv (begrpiv:int) r.
          (!begreg reg.
             ~(r <= l) /\ ~(begreg < begrpiv \/ begreg = begrpiv /\ reg <= rpiv)
             ==> P l rpiv begrpiv (r - 1)) /\
          (!begreg reg.
             ~(r <= l) /\ (begreg < begrpiv \/ begreg = begrpiv /\ reg <= rpiv)
             ==> P (l + 1) rpiv begrpiv r)
          ==> P l rpiv begrpiv r)
       ==> !l rpiv begrpiv r. P l rpiv begrpiv r`,
  MATCH_ACCEPT_TAC (cake_ind "partition_regs"));;

(* HOL4 Termination: WF_REL_TAC measure (\l,r. r-l); the test m <= l \/ r < m *)
(* is necessary for the termination argument, but useless in practice       *)
let sort_regs_def = cake_def_wf
  `MEASURE (\(l:num,r:num). r - l)` MONADAUX_DIFF_TAC
  `sort_regs l r =
     if r <= l + 1 then st_ex_return one
     else
       st_ex_bind (sorted_regs_sub l) (\rpiv.
       st_ex_bind (int_beg_sub rpiv) (\begrpiv.
       st_ex_bind (partition_regs (l + 1) rpiv begrpiv r) (\m.
       st_ex_ignore_bind (swap_regs l (m - 1))
       (if m <= l \/ r < m then st_ex_return one
        else st_ex_ignore_bind (sort_regs l (m - 1)) (sort_regs m r)))))`;;

let sort_regs_ind = prove
 (`!P. (!l r. (!m. ~(r <= l + 1) /\ ~(m <= l \/ r < m) ==> P l (m - 1)) /\
              (!m. ~(r <= l + 1) /\ ~(m <= l \/ r < m) ==> P m r)
              ==> P l r)
       ==> !l r. P l r`,
  MATCH_ACCEPT_TAC (cake_ind "sort_regs"));;

let list_to_sorted_regs_def = cake_def
  `(list_to_sorted_regs [] n = st_ex_return one) /\
   (list_to_sorted_regs (CONS r rs) n =
      st_ex_ignore_bind (update_sorted_regs n r) (list_to_sorted_regs rs (n + 1)))`;;

(* HOL4 Termination: WF_REL_TAC measure (\n,last. last-n) *)
let sorted_regs_to_list_def = cake_def_wf
  `MEASURE (\(n:num,last:num). last - n)` MONADAUX_DIFF_TAC
  `sorted_regs_to_list n last =
     if last <= n then st_ex_return []
     else
       st_ex_bind (sorted_regs_sub n) (\r.
       st_ex_bind (sorted_regs_to_list (n + 1) last) (\l.
       st_ex_return (CONS r l)))`;;

let sorted_regs_to_list_ind = cake_ind "sorted_regs_to_list";;

let swap_moves_def = cake_def
  `swap_moves i1 i2 =
     st_ex_bind (sorted_moves_sub i1) (\r1.
     st_ex_bind (sorted_moves_sub i2) (\r2.
     st_ex_ignore_bind (update_sorted_moves i1 r2) (update_sorted_moves i2 r1)))`;;

(* HOL4 Termination: WF_REL_TAC measure (\l,piv,r. r-l) *)
let partition_moves_def = cake_def_wf
  `MEASURE (\(l:num,piv:num,r:num). r - l)` MONADAUX_DIFF_TAC
  `partition_moves l ppiv r =
     if r <= l then st_ex_return l
     else
       st_ex_bind (sorted_moves_sub l) (\move.
       if FST move < ppiv then partition_moves (l + 1) ppiv r
       else
         st_ex_ignore_bind (swap_moves l (r - 1)) (partition_moves l ppiv (r - 1)))`;;

(* (p is FST move: the kit's induction theorem quantifies over it) *)
let partition_moves_ind = prove
 (`!P. (!l ppiv r. (!p. ~(r <= l) /\ ~(p < ppiv) ==> P l ppiv (r - 1)) /\
                   (!p. ~(r <= l) /\ p < ppiv ==> P (l + 1) ppiv r)
                   ==> P l ppiv r)
       ==> !l ppiv r. P l ppiv r`,
  MATCH_ACCEPT_TAC (cake_ind "partition_moves"));;

(* HOL4: sort_moves; Termination: WF_REL_TAC measure (\l,r. r-l) *)
let linear_scan_sort_moves_def = cake_def_wf
  `MEASURE (\(l:num,r:num). r - l)` MONADAUX_DIFF_TAC
  `linear_scan_sort_moves l r =
     if r <= l + 1 then st_ex_return one
     else
       st_ex_bind (sorted_moves_sub l) (\piv.
       st_ex_bind (partition_moves (l + 1) (FST piv) r) (\m.
       st_ex_ignore_bind (swap_moves l (m - 1))
       (if m <= l \/ r < m then st_ex_return one
        else st_ex_ignore_bind (linear_scan_sort_moves l (m - 1))
                               (linear_scan_sort_moves m r))))`;;

let linear_scan_sort_moves_ind = prove
 (`!P. (!l r. (!m. ~(r <= l + 1) /\ ~(m <= l \/ r < m) ==> P l (m - 1)) /\
              (!m. ~(r <= l + 1) /\ ~(m <= l \/ r < m) ==> P m r)
              ==> P l r)
       ==> !l r. P l r`,
  MATCH_ACCEPT_TAC (cake_ind "linear_scan_sort_moves"));;

let list_to_sorted_moves_def = cake_def
  `(list_to_sorted_moves [] n = st_ex_return one) /\
   (list_to_sorted_moves (CONS r rs) n =
      st_ex_ignore_bind (update_sorted_moves n r) (list_to_sorted_moves rs (n + 1)))`;;

(* HOL4 Termination: WF_REL_TAC measure (\n,len. len-n) *)
let sorted_moves_to_list_def = cake_def_wf
  `MEASURE (\(n:num,len:num). len - n)` MONADAUX_DIFF_TAC
  `sorted_moves_to_list n len =
     if len <= n then st_ex_return []
     else
       st_ex_bind (sorted_moves_sub n) (\r.
       st_ex_bind (sorted_moves_to_list (n + 1) len) (\l.
       st_ex_return (CONS r l)))`;;

let sorted_moves_to_list_ind = cake_ind "sorted_moves_to_list";;

let linear_reg_alloc_intervals_def = cake_def
  `linear_reg_alloc_intervals k forced moves reglist_unsorted =
     let lenreg = LENGTH reglist_unsorted in
     let lenmoves = LENGTH moves in
     let st_init_pass1 = linear_reg_alloc_pass1_initial_state k in
     st_ex_ignore_bind (list_to_sorted_regs reglist_unsorted 0)
     (st_ex_ignore_bind (sort_regs 0 lenreg)
     (st_ex_bind (sorted_regs_to_list 0 lenreg) (\reglist.
      st_ex_bind (st_ex_return (FILTER is_phy_var reglist)) (\phyregs.
      st_ex_bind (st_ex_return (FILTER (\r. r < 2 * k) phyregs)) (\phyphyregs.
      st_ex_bind (st_ex_return (FILTER (\r. 2 * k <= r) phyregs)) (\stackphyregs.
      st_ex_ignore_bind (list_to_sorted_moves moves 0)
      (st_ex_ignore_bind (linear_scan_sort_moves 0 lenmoves)
      (st_ex_bind (sorted_moves_to_list 0 lenmoves) (\smoves.
       st_ex_bind (edges_to_adjlist (MAP SND smoves) LN) (\moves_adjlist.
       st_ex_bind (edges_to_adjlist forced LN) (\forced_adjlist.
       st_ex_bind
         (st_ex_FOLDL (linear_reg_alloc_step_pass1 forced_adjlist moves_adjlist)
            st_init_pass1 reglist) (\st_end_pass1.
       st_ex_ignore_bind (apply_reg_exchange phyphyregs)
       (st_ex_bind
          (st_ex_FILTER_good
             (\r. st_ex_bind (colors_sub r) (\col.
                  st_ex_return (is_stack_var r \/ k <= col))) reglist) (\stacklist.
        st_ex_bind
          (st_ex_return (linear_reg_alloc_pass2_initial_state k (LENGTH stacklist)))
          (\st_init_pass2.
        st_ex_bind (st_ex_return (fromAList (MAP (\r. (r,one)) stacklist)))
          (\stackset.
        st_ex_bind
          (st_ex_return (sptree_map (FILTER (\r. ~(lookup r stackset = NONE))) forced_adjlist))
          (\forced_adjlist'.
        st_ex_bind
          (st_ex_return (sptree_map (FILTER (\r. ~(lookup r stackset = NONE))) moves_adjlist))
          (\moves_adjlist'.
        st_ex_bind
          (st_ex_FOLDL (linear_reg_alloc_step_pass2 forced_adjlist' moves_adjlist')
             st_init_pass2 stacklist) (\st_end_pass2.
        apply_reg_exchange stackphyregs)))))))))))))))))))`;;

let extract_coloration_def = cake_def
  `(extract_coloration invbij [] acc = st_ex_return acc) /\
   (extract_coloration invbij (CONS r rs) acc =
      st_ex_bind (colors_sub r) (\col.
      extract_coloration invbij rs (insert (misc_the 0 (lookup r invbij)) col acc)))`;;

let bijection_state_INFO = cake_record "bijection_state"
  ["bij","num spt";
   "invbij","num spt";
   "nmax","num";
   "nstack","num";
   "nalloc","num"];;

let bijection_state_component_equality =
  bijection_state_INFO.ri_component_equality;;

let find_bijection_init_def = cake_def
  `find_bijection_init = bijection_state_REC LN LN 0 3 1`;;

let find_bijection_step_def = cake_def
  `find_bijection_step state r =
     if ~(lookup r (bijection_state_bij state) = NONE) then state
     else if is_phy_var r then
       bijection_state_bij_fupd (combin_K (insert r r (bijection_state_bij state)))
       (bijection_state_invbij_fupd (combin_K (insert r r (bijection_state_invbij state)))
       (bijection_state_nmax_fupd (combin_K (MAX r (bijection_state_nmax state))) state))
     else if is_stack_var r then
       bijection_state_bij_fupd
         (combin_K (insert r (bijection_state_nstack state) (bijection_state_bij state)))
       (bijection_state_invbij_fupd
         (combin_K (insert (bijection_state_nstack state) r (bijection_state_invbij state)))
       (bijection_state_nmax_fupd
         (combin_K (MAX (bijection_state_nstack state) (bijection_state_nmax state)))
       (bijection_state_nstack_fupd (combin_K (bijection_state_nstack state + 4)) state)))
     else
       bijection_state_bij_fupd
         (combin_K (insert r (bijection_state_nalloc state) (bijection_state_bij state)))
       (bijection_state_invbij_fupd
         (combin_K (insert (bijection_state_nalloc state) r (bijection_state_invbij state)))
       (bijection_state_nmax_fupd
         (combin_K (MAX (bijection_state_nalloc state) (bijection_state_nmax state)))
       (bijection_state_nalloc_fupd (combin_K (bijection_state_nalloc state + 4)) state)))`;;

let find_bijection_clash_tree_def = cake_def
  `(find_bijection_clash_tree state (Delta wr rd) =
      FOLDL find_bijection_step (FOLDL find_bijection_step state rd) wr) /\
   (find_bijection_clash_tree state (reg_alloc_Set cutset) =
      foldi (\r v acc. find_bijection_step acc r) 0 state cutset) /\
   (find_bijection_clash_tree state (reg_alloc_Branch optcutset ct1 ct2) =
      let state1 = find_bijection_clash_tree state ct1 in
      let state2 = find_bijection_clash_tree state1 ct2 in
      match optcutset with
        NONE -> state2
      | SOME cutset -> foldi (\r v acc. find_bijection_step acc r) 0 state2 cutset) /\
   (find_bijection_clash_tree state (reg_alloc_Seq ct1 ct2) =
      let state1 = find_bijection_clash_tree state ct1 in
      find_bijection_clash_tree state1 ct2)`;;

let apply_bijection_def = cake_def
  `apply_bijection bij (interval:int spt) =
     foldi (\r i acc. insert (misc_the 0 (lookup r bij)) i acc) 0 LN interval`;;

(* HOL4 define_run with the array fields colors, int_beg, int_end,          *)
(* sorted_regs, sorted_moves: each becomes a pair (size, initial element)   *)
let i_linear_scan_hidden_state_INFO = cake_record "i_linear_scan_hidden_state"
  ["colors","num#num";
   "int_beg","num#int";
   "int_end","num#int";
   "sorted_regs","num#num";
   "sorted_moves","num#num#num#num"];;

let i_linear_scan_hidden_state_component_equality =
  i_linear_scan_hidden_state_INFO.ri_component_equality;;

let run_i_linear_scan_hidden_state_def = cake_def
  `run_i_linear_scan_hidden_state
     (x:linear_scan_hidden_state->(B,C)exc#linear_scan_hidden_state) state =
     ml_monadBase_run x
       (linear_scan_hidden_state_REC
          (REPLICATE (FST (i_linear_scan_hidden_state_colors state))
                     (SND (i_linear_scan_hidden_state_colors state)))
          (REPLICATE (FST (i_linear_scan_hidden_state_int_beg state))
                     (SND (i_linear_scan_hidden_state_int_beg state)))
          (REPLICATE (FST (i_linear_scan_hidden_state_int_end state))
                     (SND (i_linear_scan_hidden_state_int_end state)))
          (REPLICATE (FST (i_linear_scan_hidden_state_sorted_regs state))
                     (SND (i_linear_scan_hidden_state_sorted_regs state)))
          (REPLICATE (FST (i_linear_scan_hidden_state_sorted_moves state))
                     (SND (i_linear_scan_hidden_state_sorted_moves state))))`;;

let linear_reg_alloc_and_extract_coloration_def = cake_def
  `linear_reg_alloc_and_extract_coloration ct k forced moves reglist_unsorted invbij
     (nmax:A) =
     st_ex_ignore_bind (get_intervals_ct_monad ct)
     (st_ex_ignore_bind (linear_reg_alloc_intervals k forced moves reglist_unsorted)
     (extract_coloration invbij reglist_unsorted LN))`;;

let size_of_clash_tree_def = cake_def
  `(size_of_clash_tree (Delta wr rd) = &2:int) /\
   (size_of_clash_tree (reg_alloc_Set cutset) = &1) /\
   (size_of_clash_tree (reg_alloc_Branch optcutset ct1 ct2) =
      ((if IS_SOME optcutset then &1 else &0) + size_of_clash_tree ct1) +
      size_of_clash_tree ct2) /\
   (size_of_clash_tree (reg_alloc_Seq ct1 ct2) =
      size_of_clash_tree ct1 + size_of_clash_tree ct2)`;;

let run_linear_reg_alloc_intervals_def = cake_def
  `run_linear_reg_alloc_intervals ct k forced moves reglist_unsorted invbij nmax =
     run_i_linear_scan_hidden_state
       (linear_reg_alloc_and_extract_coloration ct k forced moves reglist_unsorted
          invbij nmax)
       (i_linear_scan_hidden_state_REC (nmax + 1,0) (nmax + 1,&1) (nmax + 1,&1)
          (nmax + 1,0) (LENGTH moves,(0,(0,0))))`;;

let apply_bij_on_clash_tree_def = cake_def
  `(apply_bij_on_clash_tree (Delta wr rd) bij =
      Delta (MAP (\r. misc_the 0 (lookup r bij)) wr) (MAP (\r. misc_the 0 (lookup r bij)) rd)) /\
   (apply_bij_on_clash_tree (reg_alloc_Set cutset) bij =
      reg_alloc_Set (foldi (\r v acc. insert (misc_the 0 (lookup r bij)) one acc) 0 LN cutset)) /\
   (apply_bij_on_clash_tree (reg_alloc_Branch optcutset ct1 ct2) bij =
      reg_alloc_Branch
        (OPTION_MAP (foldi (\r v acc. insert (misc_the 0 (lookup r bij)) one acc) 0 LN)
           optcutset)
        (apply_bij_on_clash_tree ct1 bij) (apply_bij_on_clash_tree ct2 bij)) /\
   (apply_bij_on_clash_tree (reg_alloc_Seq ct1 ct2) bij =
      reg_alloc_Seq (apply_bij_on_clash_tree ct1 bij) (apply_bij_on_clash_tree ct2 bij))`;;

let linear_scan_reg_alloc_def = cake_def
  `linear_scan_reg_alloc k moves ct forced =
     let bijstate = find_bijection_clash_tree find_bijection_init ct in
     let ct' = apply_bij_on_clash_tree ct (bijection_state_bij bijstate) in
     let forced' =
       MAP (\r12. match r12 with
                    (r1,r2) -> (misc_the 0 (lookup r1 (bijection_state_bij bijstate)),
                                misc_the 0 (lookup r2 (bijection_state_bij bijstate))))
           forced in
     let moves' =
       MAP (\pr12. match pr12 with
                     (p,(r1,r2)) ->
                       (p,(misc_the 0 (lookup r1 (bijection_state_bij bijstate)),
                           misc_the 0 (lookup r2 (bijection_state_bij bijstate)))))
           moves in
     let reglist_unsorted = MAP SND (toAList (bijection_state_bij bijstate)) in
     run_linear_reg_alloc_intervals ct' k forced' moves' reglist_unsorted
       (bijection_state_invbij bijstate) (bijection_state_nmax bijstate)`;;

(* HOL4 comment (not ported: the commented-out monadic translation of the   *)
(* allocator, map_colors_sub and map_colors_sub_eq, for the bootstrap)     *)
