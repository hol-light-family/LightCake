(* ========================================================================= *)
(* spt_closure: HOL4 examples/algorithms/spt_closureScript.sml (HOL4         *)
(* library used by CakeML v3479): the closure of a set of nodes under the    *)
(* edges of a num_set num_map.                                               *)
(*                                                                           *)
(* The whole theory is already ported, with proofs, at the end of            *)
(* hol4/sptree.ml (section spt_closure), under the HOL4 names:               *)
(*   num_set_tree_union_def  domain_spt_fold_union  closure_spt_def          *)
(*   closure_spt_ind  is_adjacent_def  is_reachable_def                      *)
(*   num_set_tree_union_empty  wf_num_set_tree_union                         *)
(*   domain_num_set_tree_union  num_set_tree_union_sym                       *)
(*   lookup_num_set_tree_union  wf_spt_fold_union  wf_closure_spt            *)
(*   adjacent_domain  reachable_domain  reachable_LHS_NOTIN  rtc_is_adjacent *)
(*   is_adjacent_num_set_tree_union  is_reachable_num_set_tree_union         *)
(*   closure_spt_lemma  closure_spt_thm                                      *)
(* (HOL4 isEmpty t is stated as t = LN in num_set_tree_union_empty, as      *)
(* everywhere in sptree.ml).  This file only loads sptree.ml, so that the    *)
(* files of the theories with spt_closure as an ancestor (flat_elim,         *)
(* word_elim and their proofs) can name it, and checks that every theorem    *)
(* of the theory is there.                                                   *)
(* ========================================================================= *)

needs "hol4/sptree.ml";;

type_invention_error := true;;

ignore
 [num_set_tree_union_def; domain_spt_fold_union; closure_spt_def;
  closure_spt_ind; is_adjacent_def; is_reachable_def;
  num_set_tree_union_empty; wf_num_set_tree_union;
  domain_num_set_tree_union; num_set_tree_union_sym;
  lookup_num_set_tree_union; wf_spt_fold_union; wf_closure_spt;
  adjacent_domain; reachable_domain; reachable_LHS_NOTIN; rtc_is_adjacent;
  is_adjacent_num_set_tree_union; is_reachable_num_set_tree_union;
  closure_spt_lemma; closure_spt_thm];;
