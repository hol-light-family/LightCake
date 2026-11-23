(* ========================================================================= *)
(* linear_scanProof: port of HOL4 compiler/backend/reg_alloc/proofs/         *)
(* linear_scanProofScript.sml (CakeML v3479).  Proves correctness of the     *)
(* linear-scan register allocator.                                           *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names of linear_scan.ml and reg_alloc.ml: HOL4 numset_list_insert is    *)
(*   linear_scan_numset_list_insert, the live_tree constructors Branch and   *)
(*   Seq are linear_scan_Branch and linear_scan_Seq, the clash_tree          *)
(*   constructors Set, Branch and Seq are reg_alloc_Set, reg_alloc_Branch    *)
(*   and reg_alloc_Seq, linear_scan's sort_moves is linear_scan_sort_moves.  *)
(* - Records: sth.colors is linear_scan_hidden_state_colors sth, st.active   *)
(*   is linear_scan_state_active st, bijstate.bij is bijection_state_bij     *)
(*   bijstate; r with f := v is rec_f_fupd (K v) r, r with f updated_by g is *)
(*   rec_f_fupd g r, r with <| f1 := v1; f2 := v2 |> is                      *)
(*   rec_f1_fupd (K v1) (rec_f2_fupd (K v2) r).                              *)
(* - HOL4 () is one, num_set is 1 spt, int num_map is int spt; do-notation   *)
(*   is st_ex_bind / st_ex_ignore_bind / st_ex_return; int literals are &n.  *)
(* - Library: EVERY = ALL, set = set_of_list, FOLDR f e l = ITLIST f l e,    *)
(*   GENLIST = list_of_seq, l1 ++ l2 = APPEND l1 l2 (HOL4 ++ is left-        *)
(*   associative), x NOTIN s = ~(x IN s), ($< LEX $<=) is                    *)
(*   ((<):int->int->bool) LEX ((<=):num->num->bool) (the kit's LEX).         *)
(* - HOL4 paired lambdas \(x,y). t are \xy. match xy with (x,y) -> t        *)
(*   (pair_CASE; statements with them go through CASE_TERM).                 *)
(* - Free variables of the HOL4 statements are universally quantified at the *)
(*   front.                                                                  *)
(* - HOL4 id (line 2162) is linear_scanProof_id (a common word, see          *)
(*   doc/CONVENTIONS.md).                                                    *)
(* - HOL4 LENGTH_toAList (line 5922, "TODO: move") is the LENGTH_toAList of  *)
(*   hol4/sptree.ml (the same statement, HOL4's sptree has it too).          *)
(* - LSCANPAUX_ names are local helpers (not HOL4 names).                    *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mllist.ml";;
needs "hol4/sptree.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/reg_alloc/linear_scan.ml";;
needs "compiler/backend/reg_alloc/proofs/reg_allocProof.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

type_invention_error := true;;

(* HOL4 lines 10-19: simpset and parser settings (temp_delsimps,            *)
(* tight equality, monad syntax, hide "state"): nothing to do here          *)

(* HOL4 line 23 *)
let set_MAP_FST_toAList_eq_domain = prove
 (`!s:A spt. set_of_list (MAP FST (toAList s)) = domain s`,
  REWRITE_TAC[set_MAP_FST_toAList_domain]);;

(* HOL4 line 29 *)
let numset_list_insert_FOLDL = prove
 (`!l (live:1 spt).
     linear_scan_numset_list_insert l live = FOLDL (\live x. insert x one live) live l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[linear_scan_numset_list_insert_def; FOLDL]);;

(* HOL4 line 35 *)
let numset_list_insert_nottailrec_FOLDR = prove
 (`!l (live:1 spt).
     numset_list_insert_nottailrec l live = ITLIST (\x live. insert x one live) l live`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[numset_list_insert_nottailrec_def; ITLIST]);;

(* HOL4 line 41 *)
let both_numset_list_insert_equal = prove
 (`!l (live:1 spt).
     linear_scan_numset_list_insert l live = numset_list_insert_nottailrec (REVERSE l) live`,
  REWRITE_TAC[numset_list_insert_FOLDL; numset_list_insert_nottailrec_FOLDR; FOLDR_REVERSE]);;

(* HOL4 line 48: domain_numset_list_insert *)
let linear_scanProof_domain_numset_list_insert = prove
 (`!l (s:1 spt).
     domain (linear_scan_numset_list_insert l s) = set_of_list l UNION domain s`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[linear_scan_numset_list_insert_def; set_of_list; domain_insert] THEN
  SET_TAC[]);;

(* HOL4 line 57 (HOL4 comment: why breaking encapsulation like this? To get *)
(* rid of the assumption wf s) *)
let lookup_insert_id = prove
 (`!x (y:1) (s:1 spt). lookup x s = SOME one ==> s = insert x one s`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC insert_unchanged THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 82 *)
let numset_list_insert_FILTER = prove
 (`!l (live:1 spt).
     linear_scan_numset_list_insert (FILTER (\x. lookup x live = NONE) l) live =
     linear_scan_numset_list_insert l live`,
  SUBGOAL_THEN
   `!x l (live:1 spt). lookup x live = SOME one ==>
                       lookup x (numset_list_insert_nottailrec l live) = SOME one`
  ASSUME_TAC THENL
   [GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_SIMP_TAC[numset_list_insert_nottailrec_def; lookup_insert; COND_ID];
    ALL_TAC] THEN
  REWRITE_TAC[both_numset_list_insert_equal; GSYM FILTER_REVERSE] THEN
  GEN_TAC THEN SPEC_TAC(`REVERSE (l:num list)`,`l:num list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; numset_list_insert_nottailrec_def] THEN
  GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[numset_list_insert_nottailrec_def] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC insert_unchanged THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  POP_ASSUM MP_TAC THEN STRUCT_CASES_TAC(ISPEC `lookup (h:num) (live:1 spt)` (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[one]);;

(* HOL4 line 100: domain_numset_list_delete *)
let linear_scanProof_domain_numset_list_delete = prove
 (`!l (s:A spt). domain (numset_list_delete l s) = domain s DIFF set_of_list l`,
  REWRITE_TAC[reg_allocProof_domain_numset_list_delete]);;

(* HOL4 line 107 *)
let check_partial_col_success_INJ_lemma = prove
 (`!live' flive' l live flive f.
     domain flive = IMAGE f (domain live) /\
     INJ f (domain live) UNIV /\
     check_partial_col f l live flive = SOME (live',flive')
     ==> INJ f (set_of_list l UNION domain live) UNIV`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[set_of_list; UNION_EMPTY] THEN MESON_TAC[]; ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "ih") THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[check_partial_col_def] THEN
  CASES_ON `lookup h (live:1 spt)` THEN REWRITE_TAC[case_def "option"] THENL
   [CASES_ON `lookup ((f:num->num) h) (flive:1 spt)` THEN
    REWRITE_TAC[case_def "option"; option_DISTINCT] THEN STRIP_TAC THEN
    REMOVE_THEN "ih" (MP_TAC o SPECL
      [`insert h one (live:1 spt)`; `insert ((f:num->num) h) one (flive:1 spt)`;
       `f:num->num`]) THEN
    ASM_REWRITE_TAC[domain_insert; IMAGE_CLAUSES; INJ_INSERT; IN_UNIV] THEN
    ANTS_TAC THENL
     [X_GEN_TAC `y:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(f:num->num) h IN domain (flive:1 spt)` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
        ASM_REWRITE_TAC[domain_lookup; option_DISTINCT] THEN MESON_TAC[option_DISTINCT]];
      DISCH_TAC THEN MATCH_MP_TAC reg_allocProof_INJ_less THEN
      EXISTS_TAC `set_of_list t UNION ((h:num) INSERT domain (live:1 spt))` THEN
      ASM_REWRITE_TAC[set_of_list] THEN SET_TAC[]];
    STRIP_TAC THEN
    SUBGOAL_THEN `(h:num) IN domain (live:1 spt)` ASSUME_TAC THENL
     [REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC reg_allocProof_INJ_less THEN
    EXISTS_TAC `set_of_list t UNION domain (live:1 spt)` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[set_of_list] THEN ASM SET_TAC[]]]);;

(* HOL4 line 136 *)
let check_partial_col_success_INJ = prove
 (`!live' flive' l live flive f.
     domain flive = IMAGE f (domain live) /\
     INJ f (domain live) UNIV /\
     check_partial_col f l live flive = SOME (live',flive')
     ==> INJ f (set_of_list l UNION domain live) UNIV /\
         INJ f (domain live') UNIV`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `domain (live':1 spt) = set_of_list l UNION domain (live:1 spt)`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP check_partial_col_domain) THEN REWRITE_TAC[FST];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC check_partial_col_success_INJ_lemma THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 150 *)
let check_partial_col_input_monotone = prove
 (`!f live1 flive1 live2 flive2 l v.
     IMAGE f (domain live1) = domain flive1 /\ IMAGE f (domain live2) = domain flive2 ==>
     domain live1 SUBSET domain live2 ==>
     INJ f (domain live2) UNIV ==>
     check_partial_col f l live2 flive2 = SOME v ==>
     ?livein1 flivein1. check_partial_col f l live1 flive1 = SOME (livein1,flivein1)`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  STRIP_ASSUME_TAC(ISPEC `v:1 spt#1 spt` PAIR_SURJECTIVE) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `INJ (f:num->num) (set_of_list l UNION domain (live2:1 spt)) UNIV`
  ASSUME_TAC THENL [ASM_MESON_TAC[check_partial_col_success_INJ]; ALL_TAC] THEN
  MP_TAC(SPECL [`l:num list`; `live1:1 spt`; `flive1:1 spt`; `f:num->num`]
    check_partial_col_success) THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC reg_allocProof_INJ_less THEN
  EXISTS_TAC `set_of_list l UNION domain (live2:1 spt)` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* HOL4 line 166 *)
let numset_list_delete_IMAGE = prove
 (`!f l live flive v.
     domain flive = IMAGE f (domain live) ==>
     INJ f (domain live) UNIV ==>
     check_partial_col f l live flive = SOME v ==>
     domain (numset_list_delete (MAP f l) flive) =
     IMAGE f (domain (numset_list_delete l live))`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  STRIP_ASSUME_TAC(ISPEC `v:1 spt#1 spt` PAIR_SURJECTIVE) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `INJ (f:num->num) (set_of_list l UNION domain (live:1 spt)) UNIV`
  MP_TAC THENL [ASM_MESON_TAC[check_partial_col_success_INJ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[linear_scanProof_domain_numset_list_delete; SET_OF_LIST_MAP] THEN
  REWRITE_TAC[INJ; IN_UNIV; EXTENSION; IN_IMAGE; IN_DIFF; IN_UNION] THEN
  MESON_TAC[]);;

(* HOL4 line 190 *)
let check_partial_col_IMAGE = prove
 (`!f l live flive live' flive'.
     domain flive = IMAGE f (domain live) ==>
     check_partial_col f l live flive = SOME (live',flive') ==>
     domain flive' = IMAGE f (domain live')`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[check_partial_col_def; option_INJ; PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN CASES_ON `lookup h (live:1 spt)` THEN
  REWRITE_TAC[case_def "option"] THENL
   [CASES_ON `lookup ((f:num->num) h) (flive:1 spt)` THEN
    REWRITE_TAC[case_def "option"; option_DISTINCT] THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[domain_insert; IMAGE_CLAUSES];
    ASM_MESON_TAC[]]);;

(* HOL4 line 205 *)
let branch_domain = prove
 (`!(live1:1 spt) (live2:1 spt).
     set_of_list (MAP FST (toAList (difference live2 live1))) UNION domain live1 =
     domain live1 UNION domain live2`,
  REWRITE_TAC[set_MAP_FST_toAList_domain; domain_difference] THEN SET_TAC[]);;

(* HOL4 line 214 *)
let check_partial_col_branch_domain = prove
 (`!f (live1:1 spt) (live2:1 spt) flive1 liveout fliveout.
     check_partial_col f (MAP FST (toAList (difference live2 live1))) live1 flive1 =
       SOME (liveout,fliveout) ==>
     domain liveout = domain live1 UNION domain live2`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP check_partial_col_domain) THEN
  REWRITE_TAC[FST; branch_domain]);;

(* HOL4 line 223 *)
let check_partial_col_branch_comm = prove
 (`!f live1 flive1 live2 flive2 a b.
     INJ f (domain live1) UNIV ==>
     domain flive1 = IMAGE f (domain live1) /\ domain flive2 = IMAGE f (domain live2) ==>
     check_partial_col f (MAP FST (toAList (difference live2 live1))) live1 flive1 =
       SOME (a,b) ==>
     ?c d. check_partial_col f (MAP FST (toAList (difference live1 live2))) live2 flive2 =
             SOME (c,d)`,
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `INJ (f:num->num) (domain (live1:1 spt) UNION domain (live2:1 spt)) UNIV`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `domain (a:1 spt) = domain (live1:1 spt) UNION domain (live2:1 spt)`
    (SUBST1_TAC o SYM) THENL
     [ASM_MESON_TAC[check_partial_col_branch_domain];
      ASM_MESON_TAC[check_partial_col_success_INJ]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`MAP FST (toAList (difference (live1:1 spt) (live2:1 spt)))`;
                `live2:1 spt`; `flive2:1 spt`; `f:num->num`] check_partial_col_success) THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  ASM_REWRITE_TAC[branch_domain] THEN ONCE_REWRITE_TAC[UNION_COMM] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 237 *)
let check_partial_col_list_monotone = prove
 (`!f live flive (s1:1 spt) (s2:1 spt) a b.
     domain flive = IMAGE f (domain live) ==>
     INJ f (domain live) UNIV ==>
     domain s1 SUBSET domain s2 ==>
     check_partial_col f (MAP FST (toAList s2)) live flive = SOME (a,b) ==>
     ?c d. check_partial_col f (MAP FST (toAList s1)) live flive = SOME (c,d)`,
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `INJ (f:num->num) (domain (s2:1 spt) UNION domain (live:1 spt)) UNIV`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `domain (s2:1 spt) UNION domain (live:1 spt) = domain (a:1 spt)`
    SUBST1_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP check_partial_col_domain) THEN
      REWRITE_TAC[FST; set_MAP_FST_toAList_domain] THEN MESON_TAC[];
      ASM_MESON_TAC[check_partial_col_success_INJ]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`MAP FST (toAList (s1:1 spt))`; `live:1 spt`; `flive:1 spt`;
                `f:num->num`] check_partial_col_success) THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  ASM_REWRITE_TAC[set_MAP_FST_toAList_domain] THEN
  MATCH_MP_TAC reg_allocProof_INJ_less THEN
  EXISTS_TAC `domain (s2:1 spt) UNION domain (live:1 spt)` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;


(* LSCANPAUX_check_live_tree_SOME, LSCANPAUX_check_clash_tree_SOME: the     *)
(* successful runs of check_live_tree and check_clash_tree, one clause per   *)
(* constructor, with named intermediate results                              *)
let LSCANPAUX_check_live_tree_SOME = prove
 (`(!f l live flive lo flo.
      check_live_tree f (Writes l) live flive = SOME (lo,flo) <=>
      (?v. check_partial_col f l live flive = SOME v) /\
      lo = numset_list_delete l live /\ flo = numset_list_delete (MAP f l) flive) /\
   (!f l live flive lo flo.
      check_live_tree f (Reads l) live flive = SOME (lo,flo) <=>
      check_partial_col f l live flive = SOME (lo,flo)) /\
   (!f lt1 lt2 live flive lo flo.
      check_live_tree f (linear_scan_Branch lt1 lt2) live flive = SOME (lo,flo) <=>
      ?livein1 flivein1 livein2 flivein2.
        check_live_tree f lt1 live flive = SOME (livein1,flivein1) /\
        check_live_tree f lt2 live flive = SOME (livein2,flivein2) /\
        check_partial_col f (MAP FST (toAList (difference livein2 livein1)))
          livein1 flivein1 = SOME (lo,flo)) /\
   (!f lt1 lt2 live flive lo flo.
      check_live_tree f (linear_scan_Seq lt1 lt2) live flive = SOME (lo,flo) <=>
      ?lmid flmid.
        check_live_tree f lt2 live flive = SOME (lmid,flmid) /\
        check_live_tree f lt1 lmid flmid = SOME (lo,flo))`,
  REWRITE_TAC[check_live_tree_def; LET_DEF; LET_END_DEF] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[option_case_eq; pair_case_eq; option_DISTINCT; option_INJ; PAIR_EQ] THEN
  REWRITE_TAC[EXISTS_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

let LSCANPAUX_check_clash_tree_SOME = prove
 (`(!f w r live flive lo flo.
      check_clash_tree f (Delta w r) live flive = SOME (lo,flo) <=>
      (?v. check_partial_col f w live flive = SOME v) /\
      check_partial_col f r (numset_list_delete w live)
        (numset_list_delete (MAP f w) flive) = SOME (lo,flo)) /\
   (!f t live flive lo flo.
      check_clash_tree f (reg_alloc_Set t) live flive = SOME (lo,flo) <=>
      check_col f t = SOME (lo,flo)) /\
   (!f t1 t2 live flive lo flo.
      check_clash_tree f (reg_alloc_Branch NONE t1 t2) live flive = SOME (lo,flo) <=>
      ?t1_out ft1_out t2_out ft2_out.
        check_clash_tree f t1 live flive = SOME (t1_out,ft1_out) /\
        check_clash_tree f t2 live flive = SOME (t2_out,ft2_out) /\
        check_partial_col f (MAP FST (toAList (difference t2_out t1_out)))
          t1_out ft1_out = SOME (lo,flo)) /\
   (!f t t1 t2 live flive lo flo.
      check_clash_tree f (reg_alloc_Branch (SOME t) t1 t2) live flive = SOME (lo,flo) <=>
      ?t1_out ft1_out t2_out ft2_out.
        check_clash_tree f t1 live flive = SOME (t1_out,ft1_out) /\
        check_clash_tree f t2 live flive = SOME (t2_out,ft2_out) /\
        check_col f t = SOME (lo,flo)) /\
   (!f t1 t2 live flive lo flo.
      check_clash_tree f (reg_alloc_Seq t1 t2) live flive = SOME (lo,flo) <=>
      ?t2_out ft2_out.
        check_clash_tree f t2 live flive = SOME (t2_out,ft2_out) /\
        check_clash_tree f t1 t2_out ft2_out = SOME (lo,flo))`,
  REWRITE_TAC[check_clash_tree_def; LET_DEF; LET_END_DEF] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[option_case_eq; pair_case_eq; option_DISTINCT; option_INJ; PAIR_EQ;
              case_def "option"] THEN
  REWRITE_TAC[EXISTS_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

(* HOL4 line 254 *)
let check_live_tree_success = prove
 (`!lt live flive live' flive' f.
     domain flive = IMAGE f (domain live) /\
     INJ f (domain live) UNIV /\
     check_live_tree f lt live flive = SOME (live',flive') ==>
     domain flive' = IMAGE f (domain live') /\
     INJ f (domain live') UNIV`,
  MATCH_MP_TAC live_tree_INDUCT THEN REWRITE_TAC[LSCANPAUX_check_live_tree_SOME] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `l:num list` THEN REPEAT GEN_TAC THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `v:1 spt#1 spt`) THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[numset_list_delete_IMAGE];
      MATCH_MP_TAC reg_allocProof_INJ_less THEN EXISTS_TAC `domain (live:1 spt)` THEN
      ASM_REWRITE_TAC[linear_scanProof_domain_numset_list_delete] THEN SET_TAC[]];
    X_GEN_TAC `l:num list` THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_MESON_TAC[check_partial_col_IMAGE; check_partial_col_success_INJ];
    X_GEN_TAC `lt1:live_tree` THEN X_GEN_TAC `lt2:live_tree` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `domain (flivein1:1 spt) = IMAGE (f:num->num) (domain (livein1:1 spt)) /\
                  INJ f (domain livein1) UNIV` STRIP_ASSUME_TAC THENL
     [REMOVE_THEN "ih1" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[check_partial_col_IMAGE; check_partial_col_success_INJ];
    X_GEN_TAC `lt1:live_tree` THEN X_GEN_TAC `lt2:live_tree` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `domain (flmid:1 spt) = IMAGE (f:num->num) (domain (lmid:1 spt)) /\
                  INJ f (domain lmid) UNIV` STRIP_ASSUME_TAC THENL
     [REMOVE_THEN "ih2" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "ih1" MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

(* HOL4 line 305 *)
let ALL_DISTINCT_INJ_MAP = prove
 (`!(f:A->B) l. ALL_DISTINCT (MAP f l) ==> INJ f (set_of_list l) UNIV`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ALL_DISTINCT; set_of_list; INJ_INSERT; IN_UNIV] THENL
   [REWRITE_TAC[INJ; NOT_IN_EMPTY; IN_UNIV];
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_SET_OF_LIST] THEN
    ASM_MESON_TAC[MEM_MAP]]);;

(* HOL4 line 313 *)
let check_col_output = prove
 (`!f (live:A spt) live' flive'.
     check_col f live = SOME (live',flive') ==>
     domain flive' = IMAGE f (domain live') /\
     INJ f (domain live') UNIV`,
  REPEAT GEN_TAC THEN REWRITE_TAC[check_col_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; domain_fromAList; IN_SET_OF_LIST; MEM_MAP; IN_IMAGE;
                GSYM set_MAP_FST_toAList_domain; o_THM; EXISTS_PAIR_THM; PAIR_EQ] THEN
    MESON_TAC[];
    ONCE_REWRITE_TAC[GSYM set_MAP_FST_toAList_domain] THEN
    MATCH_MP_TAC ALL_DISTINCT_INJ_MAP THEN ASM_REWRITE_TAC[GSYM MAP_o]]);;

(* HOL4 line 331 *)
let check_col_success = prove
 (`!f (live:A spt).
     INJ f (domain live) UNIV ==>
     ?flive. check_col f live = SOME (live,flive)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[check_col_def; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP ((f:num->num) o FST) (toAList (live:A spt)))`
    (fun th -> REWRITE_TAC[th; option_INJ; PAIR_EQ] THEN MESON_TAC[]) THEN
  REWRITE_TAC[MAP_o] THEN
  MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList] THEN
  UNDISCH_TAC `INJ (f:num->num) (domain (live:A spt)) UNIV` THEN
  REWRITE_TAC[INJ; GSYM set_MAP_FST_toAList_domain; IN_SET_OF_LIST] THEN
  MESON_TAC[]);;

(* LSCANPAUX_clash_tree_INDUCT: clash_tree induction with the optional cut  *)
(* set of a Branch split into NONE and SOME                                  *)
let LSCANPAUX_clash_tree_INDUCT = prove
 (`!P. (!w r. P (Delta w r)) /\
       (!t. P (reg_alloc_Set t)) /\
       (!t1 t2. P t1 /\ P t2 ==> P (reg_alloc_Branch NONE t1 t2)) /\
       (!t t1 t2. P t1 /\ P t2 ==> P (reg_alloc_Branch (SOME t) t1 t2)) /\
       (!t1 t2. P t1 /\ P t2 ==> P (reg_alloc_Seq t1 t2))
       ==> !ct. P ct`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC clash_tree_INDUCT THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `topt:(1 spt)option` THEN
  STRUCT_CASES_TAC(ISPEC `topt:(1 spt)option` (cases "option")) THEN
  ASM_MESON_TAC[]);;

(* LSCANPAUX_get_live_tree: get_live_tree without lets, Branch split *)
let LSCANPAUX_get_live_tree = prove
 (`(!wr rd. get_live_tree (Delta wr rd) = linear_scan_Seq (Reads rd) (Writes wr)) /\
   (!cutset. get_live_tree (reg_alloc_Set cutset) = Reads (MAP FST (toAList cutset))) /\
   (!ct1 ct2. get_live_tree (reg_alloc_Branch NONE ct1 ct2) =
              linear_scan_Branch (get_live_tree ct1) (get_live_tree ct2)) /\
   (!cutset ct1 ct2.
      get_live_tree (reg_alloc_Branch (SOME cutset) ct1 ct2) =
      linear_scan_Seq (Reads (MAP FST (toAList cutset)))
        (linear_scan_Branch (get_live_tree ct1) (get_live_tree ct2))) /\
   (!ct1 ct2. get_live_tree (reg_alloc_Seq ct1 ct2) =
              linear_scan_Seq (get_live_tree ct1) (get_live_tree ct2))`,
  REWRITE_TAC[get_live_tree_def; LET_DEF; LET_END_DEF; case_def "option"]);;

(* LSCANPAUX_cpc_mono: check_partial_col succeeds on a smaller live set,     *)
(* with a smaller output                                                      *)
let LSCANPAUX_cpc_mono = prove
 (`!f l live1 flive1 live2 flive2 a2 fa2.
     IMAGE f (domain live1) = domain flive1 /\ IMAGE f (domain live2) = domain flive2 /\
     domain live1 SUBSET domain live2 /\ INJ f (domain live2) UNIV /\
     check_partial_col f l live2 flive2 = SOME (a2,fa2) ==>
     ?a1 fa1. check_partial_col f l live1 flive1 = SOME (a1,fa1) /\
              domain a1 SUBSET domain a2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`f:num->num`; `live1:1 spt`; `flive1:1 spt`; `live2:1 spt`; `flive2:1 spt`;
                `l:num list`; `(a2:1 spt,fa2:1 spt)`] check_partial_col_input_monotone) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b1:1 spt` (X_CHOOSE_TAC `fb1:1 spt`)) THEN
  MAP_EVERY EXISTS_TAC [`b1:1 spt`; `fb1:1 spt`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP check_partial_col_domain)) THEN
  REWRITE_TAC[FST] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN ASM SET_TAC[]);;

(* HOL4 line 345 *)
let check_clash_tree_output = prove
 (`!f ct live flive livein flivein.
     domain flive = IMAGE f (domain live) /\
     INJ f (domain live) UNIV /\
     check_clash_tree f ct live flive = SOME (livein,flivein) ==>
     domain flivein = IMAGE f (domain livein) /\
     INJ f (domain livein) UNIV`,
  GEN_TAC THEN MATCH_MP_TAC LSCANPAUX_clash_tree_INDUCT THEN
  REWRITE_TAC[LSCANPAUX_check_clash_tree_SOME] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`w:num list`; `r:num list`] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `domain (numset_list_delete (MAP (f:num->num) w) (flive:1 spt)) =
                  IMAGE f (domain (numset_list_delete w (live:1 spt)))` ASSUME_TAC THENL
     [ASM_MESON_TAC[numset_list_delete_IMAGE]; ALL_TAC] THEN
    SUBGOAL_THEN `INJ (f:num->num) (domain (numset_list_delete w (live:1 spt))) UNIV`
    ASSUME_TAC THENL
     [MATCH_MP_TAC reg_allocProof_INJ_less THEN EXISTS_TAC `domain (live:1 spt)` THEN
      ASM_REWRITE_TAC[linear_scanProof_domain_numset_list_delete] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_MESON_TAC[check_partial_col_IMAGE; check_partial_col_success_INJ];
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[check_col_output];
    MAP_EVERY X_GEN_TAC [`t1:clash_tree`; `t2:clash_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `domain (ft1_out:1 spt) = IMAGE (f:num->num) (domain (t1_out:1 spt)) /\
                  INJ f (domain t1_out) UNIV` STRIP_ASSUME_TAC THENL
     [REMOVE_THEN "ih1" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[check_partial_col_IMAGE; check_partial_col_success_INJ];
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[check_col_output];
    MAP_EVERY X_GEN_TAC [`t1:clash_tree`; `t2:clash_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `domain (ft2_out:1 spt) = IMAGE (f:num->num) (domain (t2_out:1 spt)) /\
                  INJ f (domain t2_out) UNIV` STRIP_ASSUME_TAC THENL
     [REMOVE_THEN "ih2" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "ih1" MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

(* LSCANPAUX_get_live_tree_correct: get_live_tree_correct_lemma with the   *)
(* clash tree quantified first (for the induction)                          *)
let LSCANPAUX_get_live_tree_correct = prove
 (`!ct f live flive live' flive' livein' flivein'.
     IMAGE f (domain live) = domain flive /\ IMAGE f (domain live') = domain flive' ==>
     INJ f (domain live') UNIV ==>
     domain live SUBSET domain live' ==>
     check_live_tree f (get_live_tree ct) live' flive' = SOME (livein',flivein') ==>
     ?livein flivein. check_clash_tree f ct live flive = SOME (livein,flivein) /\
                      domain livein SUBSET domain livein'`,
  MATCH_MP_TAC LSCANPAUX_clash_tree_INDUCT THEN
  REWRITE_TAC[LSCANPAUX_get_live_tree; LSCANPAUX_check_live_tree_SOME;
              LSCANPAUX_check_clash_tree_SOME] THEN
  REPEAT CONJ_TAC THENL
   [(* Delta *)
    MAP_EVERY X_GEN_TAC [`w:num list`; `r:num list`; `f:num->num`; `live:1 spt`;
      `flive:1 spt`; `live':1 spt`; `flive':1 spt`; `livein':1 spt`; `flivein':1 spt`] THEN
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    SUBGOAL_THEN `INJ (f:num->num) (domain (live:1 spt)) UNIV` ASSUME_TAC THENL
     [MATCH_MP_TAC reg_allocProof_INJ_less THEN EXISTS_TAC `domain (live':1 spt)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?v1. check_partial_col f w live flive = SOME (v1:1 spt#1 spt)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[check_partial_col_input_monotone]; ALL_TAC] THEN
    MP_TAC(SPECL [`f:num->num`; `r:num list`; `numset_list_delete w (live:1 spt)`;
      `numset_list_delete (MAP (f:num->num) w) (flive:1 spt)`;
      `numset_list_delete w (live':1 spt)`;
      `numset_list_delete (MAP (f:num->num) w) (flive':1 spt)`;
      `livein':1 spt`; `flivein':1 spt`] LSCANPAUX_cpc_mono) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN ASM_MESON_TAC[numset_list_delete_IMAGE];
        CONV_TAC SYM_CONV THEN ASM_MESON_TAC[numset_list_delete_IMAGE];
        REWRITE_TAC[linear_scanProof_domain_numset_list_delete] THEN ASM SET_TAC[];
        MATCH_MP_TAC reg_allocProof_INJ_less THEN EXISTS_TAC `domain (live':1 spt)` THEN
        ASM_REWRITE_TAC[linear_scanProof_domain_numset_list_delete] THEN SET_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `b1:1 spt` (X_CHOOSE_THEN `fb1:1 spt` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`b1:1 spt`; `fb1:1 spt`] THEN ASM_MESON_TAC[]];
    (* Set *)
    MAP_EVERY X_GEN_TAC [`s:1 spt`; `f:num->num`; `live:1 spt`; `flive:1 spt`;
      `live':1 spt`; `flive':1 spt`; `livein':1 spt`; `flivein':1 spt`] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `INJ (f:num->num) (domain (livein':1 spt)) UNIV /\
                  domain livein' = domain (s:1 spt) UNION domain (live':1 spt)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[check_partial_col_success_INJ];
        FIRST_ASSUM(MP_TAC o MATCH_MP check_partial_col_domain) THEN
        REWRITE_TAC[FST; set_MAP_FST_toAList_domain]];
      ALL_TAC] THEN
    SUBGOAL_THEN `INJ (f:num->num) (domain (s:1 spt)) UNIV` ASSUME_TAC THENL
     [MATCH_MP_TAC reg_allocProof_INJ_less THEN EXISTS_TAC `domain (livein':1 spt)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `fcut:1 spt` o MATCH_MP check_col_success) THEN
    MAP_EVERY EXISTS_TAC [`s:1 spt`; `fcut:1 spt`] THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    (* Branch NONE *)
    MAP_EVERY X_GEN_TAC [`ct1:clash_tree`; `ct2:clash_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    MAP_EVERY X_GEN_TAC [`f:num->num`; `live:1 spt`; `flive:1 spt`; `live':1 spt`;
      `flive':1 spt`; `livein':1 spt`; `flivein':1 spt`] THEN
    REPEAT STRIP_TAC THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`f:num->num`; `live:1 spt`; `flive:1 spt`;
      `live':1 spt`; `flive':1 spt`; `livein1:1 spt`; `flivein1:1 spt`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a1:1 spt` (X_CHOOSE_THEN `fa1:1 spt` STRIP_ASSUME_TAC)) THEN
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`f:num->num`; `live:1 spt`; `flive:1 spt`;
      `live':1 spt`; `flive':1 spt`; `livein2:1 spt`; `flivein2:1 spt`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a2:1 spt` (X_CHOOSE_THEN `fa2:1 spt` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `domain (flivein1:1 spt) = IMAGE (f:num->num) (domain (livein1:1 spt)) /\
                  INJ f (domain livein1) UNIV` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC check_live_tree_success THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `INJ (f:num->num) (domain (livein1:1 spt) UNION domain (livein2:1 spt)) UNIV`
    ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[GSYM branch_domain] THEN
      ASM_MESON_TAC[check_partial_col_success_INJ];
      ALL_TAC] THEN
    SUBGOAL_THEN `INJ (f:num->num) (domain (live:1 spt)) UNIV` ASSUME_TAC THENL
     [MATCH_MP_TAC reg_allocProof_INJ_less THEN EXISTS_TAC `domain (live':1 spt)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `domain (fa1:1 spt) = IMAGE (f:num->num) (domain (a1:1 spt))` ASSUME_TAC THENL
     [ASM_MESON_TAC[check_clash_tree_output]; ALL_TAC] THEN
    MP_TAC(SPECL [`MAP FST (toAList (difference (a2:1 spt) (a1:1 spt)))`; `a1:1 spt`;
                  `fa1:1 spt`; `f:num->num`] check_partial_col_success) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[branch_domain] THEN MATCH_MP_TAC reg_allocProof_INJ_less THEN
      EXISTS_TAC `domain (livein1:1 spt) UNION domain (livein2:1 spt)` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `b:1 spt` (X_CHOOSE_THEN `fb:1 spt` STRIP_ASSUME_TAC))] THEN
    MAP_EVERY EXISTS_TAC [`b:1 spt`; `fb:1 spt`] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `domain (b:1 spt) = domain (a1:1 spt) UNION domain (a2:1 spt) /\
                  domain (livein':1 spt) = domain (livein1:1 spt) UNION domain (livein2:1 spt)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_MESON_TAC[check_partial_col_branch_domain]; ASM SET_TAC[]];
    (* Branch SOME *)
    MAP_EVERY X_GEN_TAC [`cutset:1 spt`; `ct1:clash_tree`; `ct2:clash_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    MAP_EVERY X_GEN_TAC [`f:num->num`; `live:1 spt`; `flive:1 spt`; `live':1 spt`;
      `flive':1 spt`; `livein':1 spt`; `flivein':1 spt`] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `domain (flivein1:1 spt) = IMAGE (f:num->num) (domain (livein1:1 spt)) /\
                  INJ f (domain livein1) UNIV` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC check_live_tree_success THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `domain (flmid:1 spt) = IMAGE (f:num->num) (domain (lmid:1 spt)) /\
                  INJ f (domain lmid) UNIV` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[check_partial_col_IMAGE; check_partial_col_success_INJ]; ALL_TAC] THEN
    SUBGOAL_THEN `INJ (f:num->num) (domain (livein':1 spt)) UNIV /\
                  domain livein' = domain (cutset:1 spt) UNION domain (lmid:1 spt)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[check_partial_col_success_INJ];
        MP_TAC(MATCH_MP check_partial_col_domain (ASSUME
          `check_partial_col f (MAP FST (toAList (cutset:1 spt))) lmid flmid =
           SOME (livein':1 spt,flivein':1 spt)`)) THEN
        REWRITE_TAC[FST; set_MAP_FST_toAList_domain]];
      ALL_TAC] THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`f:num->num`; `live:1 spt`; `flive:1 spt`;
      `live':1 spt`; `flive':1 spt`; `livein1:1 spt`; `flivein1:1 spt`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a1:1 spt` (X_CHOOSE_THEN `fa1:1 spt` STRIP_ASSUME_TAC)) THEN
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`f:num->num`; `live:1 spt`; `flive:1 spt`;
      `live':1 spt`; `flive':1 spt`; `livein2:1 spt`; `flivein2:1 spt`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a2:1 spt` (X_CHOOSE_THEN `fa2:1 spt` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `INJ (f:num->num) (domain (cutset:1 spt)) UNIV` ASSUME_TAC THENL
     [MATCH_MP_TAC reg_allocProof_INJ_less THEN EXISTS_TAC `domain (livein':1 spt)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `fcut:1 spt` o MATCH_MP check_col_success) THEN
    MAP_EVERY EXISTS_TAC [`cutset:1 spt`; `fcut:1 spt`] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN SET_TAC[]];
    (* Seq *)
    MAP_EVERY X_GEN_TAC [`ct1:clash_tree`; `ct2:clash_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    MAP_EVERY X_GEN_TAC [`f:num->num`; `live:1 spt`; `flive:1 spt`; `live':1 spt`;
      `flive':1 spt`; `livein':1 spt`; `flivein':1 spt`] THEN
    REPEAT STRIP_TAC THEN
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`f:num->num`; `live:1 spt`; `flive:1 spt`;
      `live':1 spt`; `flive':1 spt`; `lmid:1 spt`; `flmid:1 spt`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a2:1 spt` (X_CHOOSE_THEN `fa2:1 spt` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `INJ (f:num->num) (domain (live:1 spt)) UNIV` ASSUME_TAC THENL
     [MATCH_MP_TAC reg_allocProof_INJ_less THEN EXISTS_TAC `domain (live':1 spt)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (f:num->num) (domain (a2:1 spt)) = domain (fa2:1 spt)` ASSUME_TAC THENL
     [ASM_MESON_TAC[check_clash_tree_output]; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (f:num->num) (domain (lmid:1 spt)) = domain (flmid:1 spt) /\
                  INJ f (domain lmid) UNIV` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[check_live_tree_success]; ALL_TAC] THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`f:num->num`; `a2:1 spt`; `fa2:1 spt`;
      `lmid:1 spt`; `flmid:1 spt`; `livein':1 spt`; `flivein':1 spt`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* HOL4 line 394 *)
let get_live_tree_correct_lemma = prove
 (`!f live flive live' flive' ct livein' flivein'.
     IMAGE f (domain live) = domain flive /\ IMAGE f (domain live') = domain flive' ==>
     INJ f (domain live') UNIV ==>
     domain live SUBSET domain live' ==>
     check_live_tree f (get_live_tree ct) live' flive' = SOME (livein',flivein') ==>
     ?livein flivein. check_clash_tree f ct live flive = SOME (livein,flivein) /\
                      domain livein SUBSET domain livein'`,
  MESON_TAC[LSCANPAUX_get_live_tree_correct]);;

(* HOL4 line 512 *)
let get_live_tree_correct = prove
 (`!f live flive ct livein flivein.
     IMAGE f (domain live) = domain flive ==>
     INJ f (domain live) UNIV ==>
     check_live_tree f (get_live_tree ct) live flive = SOME (livein,flivein) ==>
     ?livein' flivein'. check_clash_tree f ct live flive = SOME (livein',flivein')`,
  MESON_TAC[get_live_tree_correct_lemma; SUBSET_REFL]);;

(* HOL4 line 522 *)
let get_live_tree_correct_LN = prove
 (`!f ct livein flivein.
     check_live_tree f (get_live_tree ct) LN LN = SOME (livein,flivein) ==>
     ?livein' flivein'. check_clash_tree f ct LN LN = SOME (livein',flivein')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`f:num->num`; `LN:1 spt`; `LN:1 spt`; `ct:clash_tree`; `livein:1 spt`;
                `flivein:1 spt`] get_live_tree_correct) THEN
  ASM_REWRITE_TAC[domain_def; IMAGE_CLAUSES; INJ; NOT_IN_EMPTY]);;

(* HOL4 line 530 *)
let check_partial_col_numset_list_insert = prove
 (`!f l live flive liveout fliveout.
     check_partial_col f l live flive = SOME (liveout,fliveout) ==>
     liveout = linear_scan_numset_list_insert l live`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[check_partial_col_def; linear_scan_numset_list_insert_def; option_INJ;
              PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN CASES_ON `lookup h (live:1 spt)` THEN
  REWRITE_TAC[case_def "option"] THENL
   [CASES_ON `lookup ((f:num->num) h) (flive:1 spt)` THEN
    REWRITE_TAC[case_def "option"; option_DISTINCT] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `insert h one (live:1 spt) = live` SUBST1_TAC THENL
     [MATCH_MP_TAC insert_unchanged THEN ASM_MESON_TAC[one]; ASM_MESON_TAC[]]]);;

(* HOL4 line 548 *)
let check_live_tree_eq_get_live_backward = prove
 (`!f lt live flive liveout fliveout.
     check_live_tree f lt live flive = SOME (liveout,fliveout) ==>
     liveout = get_live_backward lt live`,
  GEN_TAC THEN MATCH_MP_TAC live_tree_INDUCT THEN
  REWRITE_TAC[LSCANPAUX_check_live_tree_SOME; get_live_backward_def; LET_DEF; LET_END_DEF] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    MESON_TAC[check_partial_col_numset_list_insert];
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `livein1 = get_live_backward lt1 (live:1 spt) /\
                  livein2 = get_live_backward lt2 live` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[check_partial_col_numset_list_insert]];
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `lmid = get_live_backward lt2 (live:1 spt)` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]]]);;

(* HOL4 line 577 *)
let fix_domination_fixes_domination = prove
 (`!lt. domain (get_live_backward (fix_domination lt) LN) = {}`,
  GEN_TAC THEN REWRITE_TAC[fix_domination_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[get_live_backward_def; domain_def; linear_scanProof_domain_numset_list_delete;
                  set_MAP_FST_toAList_domain; DIFF_EQ_EMPTY]);;

(* HOL4 line 584 *)
let fix_domination_check_live_tree = prove
 (`!f lt liveout fliveout.
     check_live_tree f (fix_domination lt) LN LN = SOME (liveout,fliveout) ==>
     ?liveout' fliveout'. check_live_tree f lt LN LN = SOME (liveout',fliveout')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fix_domination_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LSCANPAUX_check_live_tree_SOME] THEN MESON_TAC[]);;

(* HOL4 line 594 *)
let size_of_live_tree_positive = prove
 (`!lt. &0 <= size_of_live_tree lt`,
  MATCH_MP_TAC live_tree_INDUCT THEN REWRITE_TAC[size_of_live_tree_def] THEN
  REPEAT STRIP_TAC THEN ASM_INT_ARITH_TAC);;

(* LSCANPAUX_get_intervals_EQ, LSCANPAUX_get_intervals_withlive_EQ,         *)
(* LSCANPAUX_get_intervals_ct_aux_EQ: the recursive equations of the         *)
(* interval functions as relations, with the intermediate results named as  *)
(* in their definitions                                                      *)
let LSCANPAUX_get_intervals_EQ = prove
 (`(!l n b e no bo eo.
      (no,bo,eo) = get_intervals (Writes l) n b e <=>
      no = n - &1 /\ bo = numset_list_add_if_lt l n b /\ eo = numset_list_add_if_gt l n e) /\
   (!l n b e no bo eo.
      (no,bo,eo) = get_intervals (Reads l) n b e <=>
      no = n - &1 /\ bo = b /\ eo = numset_list_add_if_gt l n e) /\
   (!lt1 lt2 n b e no bo eo.
      (no,bo,eo) = get_intervals (linear_scan_Branch lt1 lt2) n b e <=>
      ?n2 int_beg2 int_end2.
        (n2,int_beg2,int_end2) = get_intervals lt2 n b e /\
        (no,bo,eo) = get_intervals lt1 n2 int_beg2 int_end2) /\
   (!lt1 lt2 n b e no bo eo.
      (no,bo,eo) = get_intervals (linear_scan_Seq lt1 lt2) n b e <=>
      ?n2 int_beg2 int_end2.
        (n2,int_beg2,int_end2) = get_intervals lt2 n b e /\
        (no,bo,eo) = get_intervals lt1 n2 int_beg2 int_end2)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[get_intervals_def; LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  REPEAT PAIRARG_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let LSCANPAUX_get_intervals_withlive_EQ = prove
 (`(!l n b e live no bo eo.
      (no,bo,eo) = get_intervals_withlive (Writes l) n b e live <=>
      no = n - &1 /\ bo = numset_list_add_if_lt l n b /\ eo = numset_list_add_if_gt l n e) /\
   (!l n b e live no bo eo.
      (no,bo,eo) = get_intervals_withlive (Reads l) n b e live <=>
      no = n - &1 /\ bo = numset_list_delete l b /\ eo = numset_list_add_if_gt l n e) /\
   (!lt1 lt2 n b e live no bo eo.
      (no,bo,eo) = get_intervals_withlive (linear_scan_Branch lt1 lt2) n b e live <=>
      ?n2 int_beg2 int_end2 int_beg1.
        (n2,int_beg2,int_end2) = get_intervals_withlive lt2 n b e live /\
        (no,int_beg1,eo) =
          get_intervals_withlive lt1 n2 (difference int_beg2 live) int_end2 live /\
        bo = difference int_beg1 (sptree_union (get_live_backward lt1 live)
                                        (get_live_backward lt2 live))) /\
   (!lt1 lt2 n b e live no bo eo.
      (no,bo,eo) = get_intervals_withlive (linear_scan_Seq lt1 lt2) n b e live <=>
      ?n2 int_beg2 int_end2.
        (n2,int_beg2,int_end2) = get_intervals_withlive lt2 n b e live /\
        (no,bo,eo) =
          get_intervals_withlive lt1 n2 int_beg2 int_end2 (get_live_backward lt2 live))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[get_intervals_withlive_def; LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  REPEAT PAIRARG_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1; UNWIND_THM2] THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let LSCANPAUX_get_intervals_ct_aux_EQ = prove
 (`(!wr rd n b e live no bo eo lo.
      (no,bo,eo,lo) = get_intervals_ct_aux (Delta wr rd) n b e live <=>
      no = n - &2 /\ bo = numset_list_add_if_lt wr n b /\
      eo = numset_list_add_if_gt rd (n - &1) (numset_list_add_if_gt wr n e) /\
      lo = linear_scan_numset_list_insert rd (numset_list_delete wr live)) /\
   (!cutset n b e live no bo eo lo.
      (no,bo,eo,lo) = get_intervals_ct_aux (reg_alloc_Set cutset) n b e live <=>
      no = n - &1 /\ bo = b /\ eo = numset_list_add_if_gt (MAP FST (toAList cutset)) n e /\
      lo = sptree_union cutset live) /\
   (!ct1 ct2 n b e live no bo eo lo.
      (no,bo,eo,lo) = get_intervals_ct_aux (reg_alloc_Branch NONE ct1 ct2) n b e live <=>
      ?n2 int_beg2 int_end2 live2 live1.
        (n2,int_beg2,int_end2,live2) = get_intervals_ct_aux ct2 n b e live /\
        (no,bo,eo,live1) = get_intervals_ct_aux ct1 n2 int_beg2 int_end2 live /\
        lo = sptree_union live1 live2) /\
   (!cutset ct1 ct2 n b e live no bo eo lo.
      (no,bo,eo,lo) =
        get_intervals_ct_aux (reg_alloc_Branch (SOME cutset) ct1 ct2) n b e live <=>
      ?n2 int_beg2 int_end2 live2 n1 int_end1 live1.
        (n2,int_beg2,int_end2,live2) = get_intervals_ct_aux ct2 n b e live /\
        (n1,bo,int_end1,live1) = get_intervals_ct_aux ct1 n2 int_beg2 int_end2 live /\
        no = n1 - &1 /\ eo = numset_list_add_if_gt (MAP FST (toAList cutset)) n1 int_end1 /\
        lo = sptree_union cutset (sptree_union live1 live2)) /\
   (!ct1 ct2 n b e live no bo eo lo.
      (no,bo,eo,lo) = get_intervals_ct_aux (reg_alloc_Seq ct1 ct2) n b e live <=>
      ?n2 int_beg2 int_end2 live2.
        (n2,int_beg2,int_end2,live2) = get_intervals_ct_aux ct2 n b e live /\
        (no,bo,eo,lo) = get_intervals_ct_aux ct1 n2 int_beg2 int_end2 live2)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[get_intervals_ct_aux_def; LET_DEF; LET_END_DEF; PAIR_EQ; case_def "option"] THEN
  REPEAT PAIRARG_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1; UNWIND_THM2] THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

(* LSCANPAUX_INT_ARITH_TAC: linear integer arithmetic from the integer     *)
(* facts among the assumptions (the others confuse INT_ARITH)               *)
let LSCANPAUX_is_int_fact =
  let ops = ["int_le"; "int_lt"; "int_ge"; "int_gt"] in
  let rec ok t =
    if is_neg t then ok (rand t)
    else if is_conj t || is_disj t || is_imp t then ok (lhand t) && ok (rand t)
    else if is_eq t then type_of (lhand t) = `:int`
    else is_comb t && is_comb (rator t) &&
         (let op = rator (rator t) in
          is_const op && mem (fst(dest_const op)) ops) in
  ok;;

let LSCANPAUX_INT_ARITH_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (LSCANPAUX_is_int_fact o concl))) THEN
  INT_ARITH_TAC;;

(* HOL4 line 600 *)
let check_number_property_strong_monotone_weak = prove
 (`!P Q lt n (live:1 spt).
     (!n' live'. P n' live' ==> Q n' live') /\
     check_number_property_strong P lt n live ==>
     check_number_property_strong Q lt n live`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC live_tree_INDUCT THEN
  REWRITE_TAC[check_number_property_strong_def; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 612 *)
let check_number_property_strong_monotone = prove
 (`!P Q lt n (live:1 spt).
     (!n' live'. n - size_of_live_tree lt <= n' /\ P n' live' ==> Q n' live') /\
     check_number_property_strong P lt n live ==>
     check_number_property_strong Q lt n live`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC live_tree_INDUCT THEN
  REWRITE_TAC[check_number_property_strong_def; size_of_live_tree_def; LET_DEF;
              LET_END_DEF] THEN
  REPEAT CONJ_TAC THENL [MESON_TAC[INT_LE_REFL]; MESON_TAC[INT_LE_REFL]; ALL_TAC; ALL_TAC] THEN
  (MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:int`; `live:1 spt`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n':int. (n - size_of_live_tree lt2) - size_of_live_tree lt1 <= n' ==>
                         n - (size_of_live_tree lt1 + size_of_live_tree lt2) <= n'`
  ASSUME_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!n':int. n - size_of_live_tree lt2 <= n' ==>
                         n - (size_of_live_tree lt1 + size_of_live_tree lt2) <= n'`
  ASSUME_TAC THENL
   [MP_TAC(SPEC `lt1:live_tree` size_of_live_tree_positive) THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_MESON_TAC[INT_LE_REFL]));;

(* HOL4 line 643 *)
let check_number_property_strong_end = prove
 (`!P lt n (live:1 spt).
     check_number_property_strong P lt n live ==>
     P (n - size_of_live_tree lt) (get_live_backward lt live)`,
  GEN_TAC THEN MATCH_MP_TAC live_tree_INDUCT THEN
  REWRITE_TAC[check_number_property_strong_def; get_live_backward_def;
              size_of_live_tree_def; LET_DEF; LET_END_DEF] THEN
  REPEAT CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n - (size_of_live_tree lt1 + size_of_live_tree lt2) =
                (n - size_of_live_tree lt2) - size_of_live_tree lt1` SUBST1_TAC THENL
   [INT_ARITH_TAC; ASM_MESON_TAC[]]);;

(* HOL4 line 656 *)
let check_number_property_monotone_weak = prove
 (`!P Q lt n (live:1 spt).
     (!n' live'. P n' live' ==> Q n' live') /\
     check_number_property P lt n live ==>
     check_number_property Q lt n live`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC live_tree_INDUCT THEN
  REWRITE_TAC[check_number_property_def; LET_DEF; LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 668 *)
let lookup_numset_list_add_if = prove
 (CASE_TERM
  `!P r l v s.
     lookup r (numset_list_add_if l v s P) =
       if MEM r l then
         (match lookup r s with
            SOME vr -> if P v vr then SOME v else SOME vr
          | NONE -> SOME v)
       else lookup r s`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[numset_list_add_if_def; MEM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `r:num = h` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    CASES_ON `lookup h (s:int spt)` THEN REWRITE_TAC[case_def "option"] THEN
    TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[lookup_insert; case_def "option"; COND_ID];
    CASES_ON `lookup h (s:int spt)` THEN REWRITE_TAC[case_def "option"] THEN
    TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[lookup_insert]]);;

(* HOL4 line 698 *)
let lookup_numset_list_add_if_lt = prove
 (CASE_TERM
  `!r l v s.
     lookup r (numset_list_add_if_lt l v s) =
       if MEM r l then
         (match lookup r s with
            SOME vr -> if v <= vr then SOME v else SOME vr
          | NONE -> SOME v)
       else lookup r s`,
  REWRITE_TAC[numset_list_add_if_lt_def; lookup_numset_list_add_if]);;

(* HOL4 line 715 *)
let lookup_numset_list_add_if_gt = prove
 (CASE_TERM
  `!r l v s.
     lookup r (numset_list_add_if_gt l v s) =
       if MEM r l then
         (match lookup r s with
            SOME vr -> if vr <= v then SOME v else SOME vr
          | NONE -> SOME v)
       else lookup r s`,
  REWRITE_TAC[numset_list_add_if_gt_def; lookup_numset_list_add_if]);;

(* LSCANPAUX_lookup_add_if_lt, LSCANPAUX_lookup_add_if_gt: what a lookup in *)
(* numset_list_add_if_lt / _gt gives                                        *)
let LSCANPAUX_lookup_add_if_lt = prove
 (`!l (n:int) b r.
     (MEM r l ==> ?v. lookup r (numset_list_add_if_lt l n b) = SOME v /\ v <= n) /\
     (~MEM r l ==> lookup r (numset_list_add_if_lt l n b) = lookup r b) /\
     (!v. lookup r b = SOME v ==>
          ?v'. lookup r (numset_list_add_if_lt l n b) = SOME v' /\ v' <= v /\
               (MEM r l ==> v' <= n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_numset_list_add_if_lt] THEN
  ASM_CASES_TAC `MEM (r:num) l` THEN ASM_REWRITE_TAC[INT_LE_REFL] THENL
   [CASES_ON `lookup r (b:int spt)` THEN
    REWRITE_TAC[case_def "option"; option_INJ; option_DISTINCT; UNWIND_THM1;
                FORALL_UNWIND_THM1; INT_LE_REFL] THEN
    TRY COND_CASES_TAC THEN REWRITE_TAC[option_INJ; UNWIND_THM1] THEN
    LSCANPAUX_INT_ARITH_TAC;
    MESON_TAC[INT_LE_REFL]]);;

let LSCANPAUX_lookup_add_if_gt = prove
 (`!l (n:int) e r.
     (MEM r l ==> ?v. lookup r (numset_list_add_if_gt l n e) = SOME v /\ n <= v) /\
     (~MEM r l ==> lookup r (numset_list_add_if_gt l n e) = lookup r e) /\
     (!v. lookup r e = SOME v ==>
          ?v'. lookup r (numset_list_add_if_gt l n e) = SOME v' /\ v <= v' /\
               (MEM r l ==> n <= v'))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_numset_list_add_if_gt] THEN
  ASM_CASES_TAC `MEM (r:num) l` THEN ASM_REWRITE_TAC[INT_LE_REFL] THENL
   [CASES_ON `lookup r (e:int spt)` THEN
    REWRITE_TAC[case_def "option"; option_INJ; option_DISTINCT; UNWIND_THM1;
                FORALL_UNWIND_THM1; INT_LE_REFL] THEN
    TRY COND_CASES_TAC THEN REWRITE_TAC[option_INJ; UNWIND_THM1] THEN
    LSCANPAUX_INT_ARITH_TAC;
    MESON_TAC[INT_LE_REFL]]);;

(* HOL4 line 732 *)
let domain_numset_list_add_if = prove
 (`!l v s P. domain (numset_list_add_if l v s P) = set_of_list l UNION domain s`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[numset_list_add_if_def; set_of_list; UNION_EMPTY] THEN
  REPEAT GEN_TAC THEN CASES_ON `lookup h (s:int spt)` THEN
  REWRITE_TAC[case_def "option"] THEN TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[domain_insert] THEN TRY(SET_TAC[]) THEN
  SUBGOAL_THEN `(h:num) IN domain (s:int spt)` MP_TAC THENL
   [REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[]; SET_TAC[]]);;

(* HOL4 line 749 *)
let domain_numset_list_add_if_lt = prove
 (`!l v s. domain (numset_list_add_if_lt l v s) = set_of_list l UNION domain s`,
  REWRITE_TAC[numset_list_add_if_lt_def; domain_numset_list_add_if]);;

(* HOL4 line 755 *)
let domain_numset_list_add_if_gt = prove
 (`!l v s. domain (numset_list_add_if_gt l v s) = set_of_list l UNION domain s`,
  REWRITE_TAC[numset_list_add_if_gt_def; domain_numset_list_add_if]);;

(* HOL4 line 761 *)
let lookup_numset_list_delete = prove
 (`!l (s:A spt) x.
     lookup x (numset_list_delete l s) = if MEM x l then NONE else lookup x s`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[numset_list_delete_def; MEM; lookup_delete] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `MEM (x:num) t` THEN
  ASM_CASES_TAC `x:num = h` THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 769 *)
let get_intervals_nout = prove
 (`!lt n_in beg_in end_in n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals lt n_in beg_in end_in ==>
     n_out = n_in - size_of_live_tree lt`,
  let tac =
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `n2 = n_in - size_of_live_tree lt2 /\ n_out = n2 - size_of_live_tree lt1`
    MP_TAC THENL [ASM_MESON_TAC[]; INT_ARITH_TAC] in
  MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[LSCANPAUX_get_intervals_EQ; size_of_live_tree_def] THENL
   [MESON_TAC[]; MESON_TAC[]; tac; tac]);;

(* HOL4 line 782 *)
let get_intervals_withlive_nout = prove
 (`!lt n_in beg_in end_in n_out beg_out end_out live.
     (n_out,beg_out,end_out) = get_intervals_withlive lt n_in beg_in end_in live ==>
     n_out = n_in - size_of_live_tree lt`,
  let tac =
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `n2 = n_in - size_of_live_tree lt2 /\ n_out = n2 - size_of_live_tree lt1`
    MP_TAC THENL [ASM_MESON_TAC[]; INT_ARITH_TAC] in
  MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[LSCANPAUX_get_intervals_withlive_EQ; size_of_live_tree_def] THENL
   [MESON_TAC[]; MESON_TAC[]; tac; tac]);;

(* HOL4 line 796 *)
let get_intervals_intend_augment = prove
 (`!lt n_in beg_in end_in n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals lt n_in beg_in end_in ==>
     !r v. lookup r end_in = SOME v ==> (?v'. lookup r end_out = SOME v' /\ v <= v')`,
  let tac =
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`r:num`; `v:int`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `?v1. lookup r (int_end2:int spt) = SOME v1 /\ v <= v1`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?v2. lookup r (end_out:int spt) = SOME v2 /\ v1 <= v2`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `v2:int` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[INT_LE_TRANS] in
  MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[LSCANPAUX_get_intervals_EQ] THENL
   [REPEAT STRIP_TAC THEN ASM_MESON_TAC[LSCANPAUX_lookup_add_if_gt];
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[LSCANPAUX_lookup_add_if_gt];
    tac; tac]);;

(* HOL4 line 819 *)
let check_number_property_intend = prove
 (`!(end_out:int spt) lt n_in live_in.
     check_number_property
       (\n (live:1 spt). !r. r IN domain live ==>
                             ?v. lookup r end_out = SOME v /\ n + &1 <= v)
       lt n_in live_in ==>
     !r. r IN domain (get_live_backward lt live_in) ==>
         ?v. lookup r end_out = SOME v /\ n_in - size_of_live_tree lt <= v`,
  GEN_TAC THEN MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[check_number_property_def; get_live_backward_def; size_of_live_tree_def;
              LET_DEF; LET_END_DEF] THENL
   [MESON_TAC[INT_ARITH `!n v:int. (n - &1) + &1 <= v ==> n - &1 <= v`];
    MESON_TAC[INT_ARITH `!n v:int. (n - &1) + &1 <= v ==> n - &1 <= v`];
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    MAP_EVERY X_GEN_TAC [`n:int`; `live:1 spt`] THEN STRIP_TAC THEN X_GEN_TAC `r:num` THEN
    REWRITE_TAC[linear_scanProof_domain_numset_list_insert; branch_domain; IN_UNION] THEN
    MP_TAC(SPEC `lt1:live_tree` size_of_live_tree_positive) THEN DISCH_TAC THEN
    STRIP_TAC THENL
     [REMOVE_THEN "ih1" (MP_TAC o SPECL [`n - size_of_live_tree lt2`; `live:1 spt`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[INT_ARITH `!n s1 s2 v:int. (n - s2) - s1 <= v ==> n - (s1 + s2) <= v`];
      REMOVE_THEN "ih2" (MP_TAC o SPECL [`n:int`; `live:1 spt`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 <= size_of_live_tree lt1` THEN
      MESON_TAC[INT_ARITH `!n s1 s2 v:int. &0 <= s1 /\ n - s2 <= v ==> n - (s1 + s2) <= v`]];
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    MAP_EVERY X_GEN_TAC [`n:int`; `live:1 spt`] THEN STRIP_TAC THEN X_GEN_TAC `r:num` THEN
    DISCH_TAC THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`n - size_of_live_tree lt2`;
                                        `get_live_backward lt2 live`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[INT_ARITH `!n s1 s2 v:int. (n - s2) - s1 <= v ==> n - (s1 + s2) <= v`]]);;

(* HOL4 line 852 *)
let get_intervals_live_less_end = prove
 (`!lt n_in beg_in end_in (live_in:1 spt) n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals lt n_in beg_in end_in /\
     (!r. r IN domain live_in ==> ?v. lookup r end_in = SOME v /\ n_in <= v) ==>
     check_number_property
       (\n (live:1 spt). !r. r IN domain live ==>
                             ?v. lookup r end_out = SOME v /\ n + &1 <= v)
       lt n_in live_in`,
  MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[LSCANPAUX_get_intervals_EQ; check_number_property_def; LET_DEF;
              LET_END_DEF] THENL
   [(* Writes *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[linear_scanProof_domain_numset_list_delete; IN_DIFF; IN_SET_OF_LIST] THEN
    REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[LSCANPAUX_lookup_add_if_gt; INT_ARITH `!n v:int. n <= v ==> (n - &1) + &1 <= v`];
    (* Reads *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[linear_scanProof_domain_numset_list_insert; IN_UNION; IN_SET_OF_LIST] THEN
    X_GEN_TAC `r:num` THEN ASM_CASES_TAC `MEM (r:num) l` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[LSCANPAUX_lookup_add_if_gt; INT_LE_TRANS;
                  INT_ARITH `!n v:int. n <= v ==> (n - &1) + &1 <= v`];
    (* Branch *)
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `n2 = n_in - size_of_live_tree lt2` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[get_intervals_nout]; ALL_TAC] THEN
    MP_TAC(SPEC `lt2:live_tree` size_of_live_tree_positive) THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [REMOVE_THEN "ih1" (MP_TAC o SPECL [`n_in - size_of_live_tree lt2`; `int_beg2:int spt`;
        `int_end2:int spt`; `live_in:1 spt`; `n_out:int`; `beg_out:int spt`;
        `end_out:int spt`]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?v. lookup r (end_in:int spt) = SOME v /\ n_in <= v` STRIP_ASSUME_TAC
      THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `?v'. lookup r (int_end2:int spt) = SOME v' /\ v <= v'` STRIP_ASSUME_TAC
      THENL [ASM_MESON_TAC[get_intervals_intend_augment]; ALL_TAC] THEN
      EXISTS_TAC `v':int` THEN ASM_REWRITE_TAC[] THEN LSCANPAUX_INT_ARITH_TAC;
      MATCH_MP_TAC check_number_property_monotone_weak THEN
      EXISTS_TAC `\(n:int) (live:1 spt). !r. r IN domain live ==>
                     ?v. lookup r (int_end2:int spt) = SOME v /\ n + &1 <= v` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
        SUBGOAL_THEN `?v. lookup r (int_end2:int spt) = SOME v /\ n' + &1 <= v`
        STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `?v'. lookup r (end_out:int spt) = SOME v' /\ v <= v'`
        STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[get_intervals_intend_augment]; ALL_TAC] THEN
        EXISTS_TAC `v':int` THEN ASM_REWRITE_TAC[] THEN LSCANPAUX_INT_ARITH_TAC;
        REMOVE_THEN "ih2" MATCH_MP_TAC THEN ASM_MESON_TAC[]]];
    (* Seq *)
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `n2 = n_in - size_of_live_tree lt2` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[get_intervals_nout]; ALL_TAC] THEN
    SUBGOAL_THEN
     `check_number_property
        (\n (live:1 spt). !r. r IN domain live ==>
                              ?v. lookup r (int_end2:int spt) = SOME v /\ n + &1 <= v)
        lt2 n_in live_in` ASSUME_TAC THENL
     [REMOVE_THEN "ih2" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REMOVE_THEN "ih1" (MP_TAC o SPECL [`n_in - size_of_live_tree lt2`; `int_beg2:int spt`;
        `int_end2:int spt`; `get_live_backward lt2 live_in`; `n_out:int`;
        `beg_out:int spt`; `end_out:int spt`]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[check_number_property_intend];
      MATCH_MP_TAC check_number_property_monotone_weak THEN
      EXISTS_TAC `\(n:int) (live:1 spt). !r. r IN domain live ==>
                     ?v. lookup r (int_end2:int spt) = SOME v /\ n + &1 <= v` THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `?v. lookup r (int_end2:int spt) = SOME v /\ n' + &1 <= v`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `?v'. lookup r (end_out:int spt) = SOME v' /\ v <= v'`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[get_intervals_intend_augment]; ALL_TAC] THEN
      EXISTS_TAC `v':int` THEN ASM_REWRITE_TAC[] THEN LSCANPAUX_INT_ARITH_TAC]]);;

(* LSCANPAUX_OPT_TAC tms: case split on the option-valued terms tms of the  *)
(* goal (lookups), reduce the cases, conditionals and option equations,     *)
(* and finish with integer arithmetic                                        *)
let LSCANPAUX_OPT_REWRITES =
  [case_def "option"; option_INJ; option_DISTINCT; FORALL_UNWIND_THM1;
   FORALL_UNWIND_THM2; UNWIND_THM1; UNWIND_THM2];;

let LSCANPAUX_OPT_TAC (tms:term list) : tactic =
  MAP_EVERY (fun t -> STRUCT_CASES_TAC (ISPEC t (cases "option"))) tms THEN
  REWRITE_TAC LSCANPAUX_OPT_REWRITES THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC LSCANPAUX_OPT_REWRITES) THEN
  LSCANPAUX_INT_ARITH_TAC;;

(* HOL4 line 909 *)
let get_intervals_withlive_intbeg_reduce = prove
 (`!lt n_in beg_in end_in n_out beg_out end_out live.
     (n_out,beg_out,end_out) = get_intervals_withlive lt n_in beg_in end_in live /\
     (!r v. lookup r beg_in = SOME v ==> n_in <= v) ==>
     (!r. option_CASE (lookup r beg_out) n_out (\x. x) <=
          option_CASE (lookup r beg_in) n_in (\x. x)) /\
     (!r v. lookup r beg_out = SOME v ==> n_out <= v)`,
  MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[LSCANPAUX_get_intervals_withlive_EQ] THENL
   [(* Writes *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[lookup_numset_list_add_if_lt] THEN
    CONJ_TAC THEN X_GEN_TAC `r:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN
    LSCANPAUX_OPT_TAC [`lookup r (beg_in:int spt)`];
    (* Reads *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[lookup_numset_list_delete] THEN
    CONJ_TAC THEN X_GEN_TAC `r:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN
    LSCANPAUX_OPT_TAC [`lookup r (beg_in:int spt)`];
    (* Branch *)
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`n_in:int`; `beg_in:int spt`; `end_in:int spt`;
      `n2:int`; `int_beg2:int spt`; `int_end2:int spt`; `live:1 spt`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`n2:int`; `difference (int_beg2:int spt) (live:1 spt)`;
      `int_end2:int spt`; `n_out:int`; `int_beg1:int spt`; `end_out:int spt`;
      `live:1 spt`]) THEN
    ASM_REWRITE_TAC[lookup_difference] THEN ANTS_TAC THENL
     [REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
      ASM_MESON_TAC[];
      STRIP_TAC] THEN
    SUBGOAL_THEN `n_out <= n2 /\ n2 <= (n_in:int)` STRIP_ASSUME_TAC THENL
     [MP_TAC(SPEC `lt1:live_tree` size_of_live_tree_positive) THEN
      MP_TAC(SPEC `lt2:live_tree` size_of_live_tree_positive) THEN
      SUBGOAL_THEN `n2 = n_in - size_of_live_tree lt2 /\ n_out = n2 - size_of_live_tree lt1`
      MP_TAC THENL [ASM_MESON_TAC[get_intervals_withlive_nout]; INT_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[lookup_difference] THEN CONJ_TAC THEN X_GEN_TAC `r:num` THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (is_forall o concl))) THEN
    LSCANPAUX_OPT_TAC
      [`lookup r (sptree_union (get_live_backward lt1 live) (get_live_backward lt2 live))`;
       `lookup r (live:1 spt)`; `lookup r (int_beg1:int spt)`;
       `lookup r (int_beg2:int spt)`; `lookup r (beg_in:int spt)`];
    (* Seq *)
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`n_in:int`; `beg_in:int spt`; `end_in:int spt`;
      `n2:int`; `int_beg2:int spt`; `int_end2:int spt`; `live:1 spt`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`n2:int`; `int_beg2:int spt`; `int_end2:int spt`;
      `n_out:int`; `beg_out:int spt`; `end_out:int spt`;
      `get_live_backward lt2 live`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:num` THEN ASM_MESON_TAC[INT_LE_TRANS]]);;

(* HOL4 line 993 *)
let get_intervals_withlive_intbeg_nout = prove
 (`!lt n_in beg_in end_in n_out beg_out end_out live.
     (n_out,beg_out,end_out) = get_intervals_withlive lt n_in beg_in end_in live /\
     (!r v. lookup r beg_in = SOME v ==> n_in <= v) ==>
     (!r v. lookup r beg_out = SOME v ==> n_out <= v)`,
  MESON_TAC[get_intervals_withlive_intbeg_reduce]);;

(* HOL4 line 1002 *)
let get_intervals_intbeg_nout = prove
 (`!lt n_in beg_in end_in n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals lt n_in beg_in end_in /\
     (!r v. lookup r beg_in = SOME v ==> n_in <= v) ==>
     (!r v. lookup r beg_out = SOME v ==> n_out <= v)`,
  let tac =
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `!r v. lookup r (int_beg2:int spt) = SOME v ==> n2 <= v` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]] in
  MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[LSCANPAUX_get_intervals_EQ] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[lookup_numset_list_add_if_lt] THEN
    X_GEN_TAC `r:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN
    LSCANPAUX_OPT_TAC [`lookup r (beg_in:int spt)`];
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[INT_ARITH `!n v:int. n <= v ==> n - &1 <= v`];
    tac; tac]);;

(* HOL4 line 1031 *)
let get_intervals_withlive_live_intbeg = prove
 (`!lt n_in beg_in end_in live n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals_withlive lt n_in beg_in end_in live /\
     (!r. r IN domain live ==> ~(r IN domain beg_in)) ==>
     (!r. r IN domain (get_live_backward lt live) ==> ~(r IN domain beg_out))`,
  MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[LSCANPAUX_get_intervals_withlive_EQ; get_live_backward_def; LET_DEF;
              LET_END_DEF] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[linear_scanProof_domain_numset_list_delete;
                    domain_numset_list_add_if_lt] THEN ASM SET_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[linear_scanProof_domain_numset_list_delete;
                    linear_scanProof_domain_numset_list_insert] THEN ASM SET_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[domain_difference; domain_union; linear_scanProof_domain_numset_list_insert;
                    branch_domain] THEN SET_TAC[];
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `!r. r IN domain (get_live_backward lt2 live) ==>
                      ~(r IN domain (int_beg2:int spt))` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]]]);;

(* HOL4 line 1061 *)
let get_intervals_withlive_beg_less_live = prove
 (`!lt n_in beg_in end_in live_in n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals_withlive lt n_in beg_in end_in live_in /\
     (!r v. lookup r beg_in = SOME v ==> n_in <= v) /\
     (!r. r IN domain live_in ==> ~(r IN domain beg_in)) ==>
     check_number_property_strong
       (\n (live:1 spt). !r. r IN domain live ==>
                             option_CASE (lookup r beg_out) n_out (\x. x) <= n)
       lt n_in live_in`,
  MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THENL
   [(* Writes *)
    REWRITE_TAC[LSCANPAUX_get_intervals_withlive_EQ; check_number_property_strong_def;
                LET_DEF; LET_END_DEF] THEN
    X_GEN_TAC `l:num list` THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[linear_scanProof_domain_numset_list_delete; IN_DIFF; IN_SET_OF_LIST;
                    lookup_numset_list_add_if_lt] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `lookup r (beg_in:int spt) = NONE`
      (fun th -> REWRITE_TAC[th; case_def "option"; INT_LE_REFL]) THEN
    ASM_MESON_TAC[lookup_NONE_domain];
    (* Reads *)
    REWRITE_TAC[LSCANPAUX_get_intervals_withlive_EQ; check_number_property_strong_def;
                LET_DEF; LET_END_DEF] THEN
    X_GEN_TAC `l:num list` THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[linear_scanProof_domain_numset_list_insert; IN_UNION; IN_SET_OF_LIST;
                    lookup_numset_list_delete] THEN
    X_GEN_TAC `r:num` THEN ASM_CASES_TAC `MEM (r:num) l` THEN
    ASM_REWRITE_TAC[case_def "option"; INT_LE_REFL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `lookup r (beg_in:int spt) = NONE`
      (fun th -> REWRITE_TAC[th; case_def "option"; INT_LE_REFL]) THEN
    ASM_MESON_TAC[lookup_NONE_domain];
    (* Branch *)
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REWRITE_TAC[LSCANPAUX_get_intervals_withlive_EQ; check_number_property_strong_def;
                LET_DEF; LET_END_DEF] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `n2 = n_in - size_of_live_tree lt2 /\ n_out = n2 - size_of_live_tree lt1`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[get_intervals_withlive_nout]; ALL_TAC] THEN
    MP_TAC(SPEC `lt1:live_tree` size_of_live_tree_positive) THEN
    MP_TAC(SPEC `lt2:live_tree` size_of_live_tree_positive) THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `!r v. lookup r (int_beg2:int spt) = SOME v ==> n2 <= v` ASSUME_TAC THENL
     [ASM_MESON_TAC[get_intervals_withlive_intbeg_nout]; ALL_TAC] THEN
    SUBGOAL_THEN
     `check_number_property_strong
        (\n (live:1 spt). !r. r IN domain live ==>
           option_CASE (lookup r (int_beg2:int spt)) n2 (\x. x) <= n) lt2 n_in live_in`
    ASSUME_TAC THENL [REMOVE_THEN "ih2" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `check_number_property_strong
        (\n (live:1 spt). !r. r IN domain live ==>
           option_CASE (lookup r (int_beg1:int spt)) n_out (\x. x) <= n) lt1 n2 live_in`
    ASSUME_TAC THENL
     [REMOVE_THEN "ih1" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`difference (int_beg2:int spt) (live_in:1 spt)`;
                            `int_end2:int spt`; `end_out:int spt`] THEN
      ASM_REWRITE_TAC[lookup_difference; domain_difference; IN_DIFF] THEN CONJ_TAC THENL
       [REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
        ASM_MESON_TAC[];
        MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!r. option_CASE (lookup r (int_beg1:int spt)) n_out (\x. x) <=
          option_CASE (lookup r (difference (int_beg2:int spt) (live_in:1 spt))) n2 (\x. x)`
    (LABEL_TAC "a1") THENL
     [MP_TAC(ISPECL [`lt1:live_tree`; `n2:int`; `difference (int_beg2:int spt) (live_in:1 spt)`;
        `int_end2:int spt`; `n_out:int`; `int_beg1:int spt`; `end_out:int spt`;
        `live_in:1 spt`] get_intervals_withlive_intbeg_reduce) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[lookup_difference] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
        REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[];
        MESON_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
                                                   lhs (concl th) = `beg_out:int spt`)) THEN
    REPEAT CONJ_TAC THENL
     [(* lt1 *)
      SUBGOAL_THEN `n_in - size_of_live_tree lt2 = n2` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC check_number_property_strong_monotone THEN
      EXISTS_TAC `\(n:int) (live:1 spt). !r. r IN domain live ==>
                    option_CASE (lookup r (int_beg1:int spt)) n_out (\x. x) <= n` THEN
      ASM_REWRITE_TAC[] THEN BETA_TAC THEN REWRITE_TAC[lookup_difference] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o
        check (fun th -> is_forall (concl th) && free_in `live':1 spt` (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      LSCANPAUX_OPT_TAC
        [`lookup r (sptree_union (get_live_backward lt1 live_in) (get_live_backward lt2 live_in))`;
         `lookup r (int_beg1:int spt)`];
      (* lt2 *)
      MATCH_MP_TAC check_number_property_strong_monotone THEN
      EXISTS_TAC `\(n:int) (live:1 spt). !r. r IN domain live ==>
                    option_CASE (lookup r (int_beg2:int spt)) n2 (\x. x) <= n` THEN
      ASM_REWRITE_TAC[] THEN BETA_TAC THEN REWRITE_TAC[lookup_difference] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o
        check (fun th -> is_forall (concl th) && free_in `live':1 spt` (concl th))) THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "a1" (MP_TAC o SPEC `r:num`) THEN
      REWRITE_TAC[lookup_difference] THEN
      LSCANPAUX_OPT_TAC
        [`lookup r (sptree_union (get_live_backward lt1 live_in) (get_live_backward lt2 live_in))`;
         `lookup r (live_in:1 spt)`; `lookup r (int_beg1:int spt)`;
         `lookup r (int_beg2:int spt)`];
      (* the live set of the whole branch *)
      REWRITE_TAC[get_live_backward_def; LET_DEF; LET_END_DEF;
        linear_scanProof_domain_numset_list_insert; branch_domain; lookup_difference] THEN
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(lookup r (sptree_union (get_live_backward lt1 live_in)
                                      (get_live_backward lt2 live_in)) = NONE)`
        (fun th -> REWRITE_TAC[th; case_def "option"]) THENL
       [ASM_REWRITE_TAC[lookup_NONE_domain; domain_union];
        ASM_REWRITE_TAC[size_of_live_tree_def] THEN LSCANPAUX_INT_ARITH_TAC]];
    (* Seq *)
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REWRITE_TAC[LSCANPAUX_get_intervals_withlive_EQ; check_number_property_strong_def;
                LET_DEF; LET_END_DEF] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `n2 = n_in - size_of_live_tree lt2 /\ n_out = n2 - size_of_live_tree lt1`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[get_intervals_withlive_nout]; ALL_TAC] THEN
    SUBGOAL_THEN `!r v. lookup r (int_beg2:int spt) = SOME v ==> n2 <= v` ASSUME_TAC THENL
     [ASM_MESON_TAC[get_intervals_withlive_intbeg_nout]; ALL_TAC] THEN
    SUBGOAL_THEN
     `check_number_property_strong
        (\n (live:1 spt). !r. r IN domain live ==>
           option_CASE (lookup r (int_beg2:int spt)) n2 (\x. x) <= n) lt2 n_in live_in`
    ASSUME_TAC THENL [REMOVE_THEN "ih2" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!r. option_CASE (lookup r (beg_out:int spt)) n_out (\x. x) <=
          option_CASE (lookup r (int_beg2:int spt)) n2 (\x. x)` (LABEL_TAC "a1") THENL
     [ASM_MESON_TAC[get_intervals_withlive_intbeg_reduce]; ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `n_in - size_of_live_tree lt2 = n2` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REMOVE_THEN "ih1" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`int_beg2:int spt`; `int_end2:int spt`; `end_out:int spt`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC get_intervals_withlive_live_intbeg THEN
      MAP_EVERY EXISTS_TAC [`n_in:int`; `beg_in:int spt`; `end_in:int spt`; `n2:int`;
                            `int_end2:int spt`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC check_number_property_strong_monotone THEN
      EXISTS_TAC `\(n:int) (live:1 spt). !r. r IN domain live ==>
                    option_CASE (lookup r (int_beg2:int spt)) n2 (\x. x) <= n` THEN
      ASM_REWRITE_TAC[] THEN BETA_TAC THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o
        check (fun th -> is_forall (concl th) && free_in `live':1 spt` (concl th))) THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "a1" (MP_TAC o SPEC `r:num`) THEN
      LSCANPAUX_OPT_TAC [`lookup r (beg_out:int spt)`; `lookup r (int_beg2:int spt)`]]]);;

(* HOL4 line 1194 *)
let get_intervals_withlive_n_eq_get_intervals_n = prove
 (`!lt n beg end beg' end' n1 beg1 end1 n2 beg2 end2 live.
     (n1,beg1,end1) = get_intervals lt n beg end /\
     (n2,beg2,end2) = get_intervals_withlive lt n beg' end' live ==>
     n1 = n2`,
  MESON_TAC[get_intervals_nout; get_intervals_withlive_nout]);;

(* LSCANPAUX_GI_TAC: open the two intermediate triples of a Branch or Seq   *)
(* case of get_intervals (m2,b2,e2) and get_intervals_withlive              *)
(* (m2',b2',e2', and b1' for the Branch case)                               *)
let LSCANPAUX_GI_BRANCH_TAC : tactic =
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m2':int` (X_CHOOSE_THEN `b2':int spt`
    (X_CHOOSE_THEN `e2':int spt` (X_CHOOSE_THEN `b1':int spt` STRIP_ASSUME_TAC))) o
    check (fun th -> length (fst(strip_exists (concl th))) = 4)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m2:int` (X_CHOOSE_THEN `b2:int spt`
    (X_CHOOSE_THEN `e2:int spt` STRIP_ASSUME_TAC)) o check (is_exists o concl));;

let LSCANPAUX_GI_SEQ_TAC : tactic =
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m2':int` (X_CHOOSE_THEN `b2':int spt`
    (X_CHOOSE_THEN `e2':int spt` STRIP_ASSUME_TAC)) o
    check (fun th -> is_exists (concl th) &&
                     can (find_term (fun t -> is_const t &&
                        fst(dest_const t) = "get_intervals_withlive")) (concl th))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m2:int` (X_CHOOSE_THEN `b2:int spt`
    (X_CHOOSE_THEN `e2:int spt` STRIP_ASSUME_TAC)) o check (is_exists o concl));;

(* HOL4 line 1206 *)
let get_intervals_withlive_end_eq_get_intervals_end = prove
 (`!lt n beg beg' end n1 beg1 end1 n2 beg2 end2 live.
     (n1,beg1,end1) = get_intervals lt n beg end /\
     (n2,beg2,end2) = get_intervals_withlive lt n beg' end live ==>
     end1 = end2`,
  MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[LSCANPAUX_get_intervals_EQ; LSCANPAUX_get_intervals_withlive_EQ] THENL
   [MESON_TAC[]; MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN LSCANPAUX_GI_BRANCH_TAC THEN
    SUBGOAL_THEN `m2':int = m2 /\ e2':int spt = e2` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [ASM_MESON_TAC[get_intervals_withlive_n_eq_get_intervals_n]; ASM_MESON_TAC[]];
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN LSCANPAUX_GI_SEQ_TAC THEN
    SUBGOAL_THEN `m2':int = m2 /\ e2':int spt = e2` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [ASM_MESON_TAC[get_intervals_withlive_n_eq_get_intervals_n]; ASM_MESON_TAC[]]]);;

(* HOL4 line 1219 *)
let get_intervals_withlive_beg_eq_get_intervals_beg_when_some = prove
 (`!lt n beg beg' end n1 beg1 end1 n2 beg2 end2 live.
     (n1,beg1,end1) = get_intervals lt n beg end /\
     (n2,beg2,end2) = get_intervals_withlive lt n beg' end live /\
     (!r v. lookup r beg = SOME v ==> n <= v) /\
     (!r v. lookup r beg' = SOME v ==> n <= v) /\
     (!r v1 v2. lookup r beg = SOME v1 /\ lookup r beg' = SOME v2 ==> v1 = v2)
     ==> !r v1 v2. lookup r beg1 = SOME v1 /\ lookup r beg2 = SOME v2 ==> v1 = v2`,
  MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[LSCANPAUX_get_intervals_EQ; LSCANPAUX_get_intervals_withlive_EQ] THENL
   [(* Writes *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[lookup_numset_list_add_if_lt] THEN
    X_GEN_TAC `r:num` THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (is_forall o concl))) THEN
    LSCANPAUX_OPT_TAC [`lookup r (beg:int spt)`; `lookup r (beg':int spt)`];
    (* Reads *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[lookup_numset_list_delete] THEN
    X_GEN_TAC `r:num` THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (is_forall o concl))) THEN
    LSCANPAUX_OPT_TAC [`lookup r (beg:int spt)`; `lookup r (beg':int spt)`];
    (* Branch *)
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN LSCANPAUX_GI_BRANCH_TAC THEN
    SUBGOAL_THEN `m2':int = m2 /\ e2':int spt = e2` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [ASM_MESON_TAC[get_intervals_withlive_n_eq_get_intervals_n;
                    get_intervals_withlive_end_eq_get_intervals_end];
      ALL_TAC] THEN
    SUBGOAL_THEN `!r v1 v2. lookup r (b2:int spt) = SOME v1 /\ lookup r (b2':int spt) = SOME v2
                            ==> v1 = v2` ASSUME_TAC THENL
     [REMOVE_THEN "ih2" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(!r v. lookup r (b2:int spt) = SOME v ==> m2 <= v) /\
                  (!r v. lookup r (b2':int spt) = SOME v ==> m2 <= v)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[get_intervals_intbeg_nout; get_intervals_withlive_intbeg_nout];
      ALL_TAC] THEN
    SUBGOAL_THEN `!r v1 v2. lookup r (beg1:int spt) = SOME v1 /\
                            lookup r (b1':int spt) = SOME v2 ==> v1 = v2` ASSUME_TAC THENL
     [REMOVE_THEN "ih1" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`m2:int`; `b2:int spt`; `difference (b2':int spt) (live:1 spt)`;
        `e2:int spt`; `n1:int`; `end1:int spt`; `n2:int`; `end2:int spt`; `live:1 spt`] THEN
      ASM_REWRITE_TAC[lookup_difference] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[lookup_difference] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN ASM_MESON_TAC[];
    (* Seq *)
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN LSCANPAUX_GI_SEQ_TAC THEN
    SUBGOAL_THEN `m2':int = m2 /\ e2':int spt = e2` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [ASM_MESON_TAC[get_intervals_withlive_n_eq_get_intervals_n;
                    get_intervals_withlive_end_eq_get_intervals_end];
      ALL_TAC] THEN
    SUBGOAL_THEN `!r v1 v2. lookup r (b2:int spt) = SOME v1 /\ lookup r (b2':int spt) = SOME v2
                            ==> v1 = v2` ASSUME_TAC THENL
     [REMOVE_THEN "ih2" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(!r v. lookup r (b2:int spt) = SOME v ==> m2 <= v) /\
                  (!r v. lookup r (b2':int spt) = SOME v ==> m2 <= v)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[get_intervals_intbeg_nout; get_intervals_withlive_intbeg_nout];
      ALL_TAC] THEN
    REMOVE_THEN "ih1" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`m2:int`; `b2:int spt`; `b2':int spt`;
      `e2:int spt`; `n1:int`; `end1:int spt`; `n2:int`; `end2:int spt`;
      `get_live_backward lt2 live`] THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 1286 *)
let get_intervals_withlive_beg_subset_get_intervals_beg = prove
 (`!lt n beg_in1 beg_in2 end n1 beg_out1 end1 n2 beg_out2 end2 live.
     (n1,beg_out1,end1) = get_intervals_withlive lt n beg_in1 end live /\
     (n2,beg_out2,end2) = get_intervals lt n beg_in2 end /\
     domain beg_in1 SUBSET domain beg_in2 ==>
     domain beg_out1 SUBSET domain beg_out2`,
  MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[LSCANPAUX_get_intervals_EQ; LSCANPAUX_get_intervals_withlive_EQ] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[domain_numset_list_add_if_lt] THEN
    ASM SET_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[linear_scanProof_domain_numset_list_delete] THEN ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN LSCANPAUX_GI_BRANCH_TAC THEN
    SUBGOAL_THEN `m2':int = m2 /\ e2':int spt = e2` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [ASM_MESON_TAC[get_intervals_withlive_n_eq_get_intervals_n;
                    get_intervals_withlive_end_eq_get_intervals_end];
      ALL_TAC] THEN
    SUBGOAL_THEN `domain (b2':int spt) SUBSET domain (b2:int spt)` ASSUME_TAC THENL
     [REMOVE_THEN "ih2" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `domain (b1':int spt) SUBSET domain (beg_out2:int spt)` MP_TAC THENL
     [REMOVE_THEN "ih1" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`m2:int`; `difference (b2':int spt) (live:1 spt)`; `b2:int spt`;
        `e2:int spt`; `n1:int`; `end1:int spt`; `n2:int`; `end2:int spt`; `live:1 spt`] THEN
      ASM_REWRITE_TAC[domain_difference] THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[domain_difference] THEN SET_TAC[]];
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN LSCANPAUX_GI_SEQ_TAC THEN
    SUBGOAL_THEN `m2':int = m2 /\ e2':int spt = e2` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [ASM_MESON_TAC[get_intervals_withlive_n_eq_get_intervals_n;
                    get_intervals_withlive_end_eq_get_intervals_end];
      ALL_TAC] THEN
    SUBGOAL_THEN `domain (b2':int spt) SUBSET domain (b2:int spt)` ASSUME_TAC THENL
     [REMOVE_THEN "ih2" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "ih1" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`m2:int`; `b2':int spt`; `b2:int spt`;
      `e2:int spt`; `n1:int`; `end1:int spt`; `n2:int`; `end2:int spt`;
      `get_live_backward lt2 live`] THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 1326 *)
let get_intervals_beg_subset_registers = prove
 (`!lt n_in beg_in end_in n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals lt n_in beg_in end_in ==>
     domain beg_out SUBSET (domain beg_in UNION live_tree_registers lt)`,
  let tac =
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `domain (int_beg2:int spt) SUBSET domain (beg_in:int spt) UNION
                  live_tree_registers lt2 /\
                  domain (beg_out:int spt) SUBSET domain int_beg2 UNION
                  live_tree_registers lt1` MP_TAC THENL
     [ASM_MESON_TAC[]; SET_TAC[]] in
  MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[LSCANPAUX_get_intervals_EQ; live_tree_registers_def] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[domain_numset_list_add_if_lt] THEN
    SET_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    tac; tac]);;

(* HOL4 line 1343 (HOL4 comment: this theorem looks like lipschitz          *)
(* continuity: it says something like f(x+y) <= f(x)+y) *)
let get_intervals_withlive_beg_lipschitz = prove
 (`!lt n1 beg1 end1 live n2 beg2 end2 (s:int spt) nout1 begout1 endout1 nout2 begout2
    endout2.
     (nout1,begout1,endout1) = get_intervals_withlive lt n1 beg1 end1 live /\
     (nout2,begout2,endout2) = get_intervals_withlive lt n2 beg2 end2 live /\
     domain beg2 SUBSET domain beg1 UNION domain s ==>
     domain begout2 SUBSET domain begout1 UNION domain s`,
  MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[LSCANPAUX_get_intervals_withlive_EQ] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[domain_numset_list_add_if_lt] THEN
    ASM SET_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[linear_scanProof_domain_numset_list_delete] THEN ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `m2':int` (X_CHOOSE_THEN `b2':int spt`
      (X_CHOOSE_THEN `e2':int spt` (X_CHOOSE_THEN `b1':int spt` STRIP_ASSUME_TAC)))) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `m2:int` (X_CHOOSE_THEN `b2:int spt`
      (X_CHOOSE_THEN `e2:int spt` (X_CHOOSE_THEN `b1:int spt` STRIP_ASSUME_TAC))) o
      check (is_exists o concl)) THEN
    SUBGOAL_THEN `domain (b2':int spt) SUBSET domain (b2:int spt) UNION domain (s:int spt)`
    ASSUME_TAC THENL [REMOVE_THEN "ih2" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `domain (b1':int spt) SUBSET domain (b1:int spt) UNION domain (s:int spt)`
    MP_TAC THENL
     [REMOVE_THEN "ih1" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`m2:int`; `difference (b2:int spt) (live:1 spt)`; `e2:int spt`;
        `live:1 spt`; `m2':int`; `difference (b2':int spt) (live:1 spt)`; `e2':int spt`;
        `nout1:int`; `endout1:int spt`; `nout2:int`; `endout2:int spt`] THEN
      ASM_REWRITE_TAC[domain_difference] THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[domain_difference] THEN SET_TAC[]];
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `m2':int` (X_CHOOSE_THEN `b2':int spt`
      (X_CHOOSE_THEN `e2':int spt` STRIP_ASSUME_TAC)) o check (is_exists o concl)) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `m2:int` (X_CHOOSE_THEN `b2:int spt`
      (X_CHOOSE_THEN `e2:int spt` STRIP_ASSUME_TAC)) o check (is_exists o concl)) THEN
    SUBGOAL_THEN `domain (b2':int spt) SUBSET domain (b2:int spt) UNION domain (s:int spt)`
    ASSUME_TAC THENL [REMOVE_THEN "ih2" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "ih1" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`m2:int`; `b2:int spt`; `e2:int spt`; `get_live_backward lt2 live`;
      `m2':int`; `b2':int spt`; `e2':int spt`; `nout1:int`; `endout1:int spt`;
      `nout2:int`; `endout2:int spt`] THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 1379 *)
let get_intervals_withlive_registers_subset_beg = prove
 (`!lt n_in beg_in end_in n_out beg_out end_out live_in.
     domain end_in SUBSET domain beg_in UNION domain live_in /\
     (n_out,beg_out,end_out) = get_intervals_withlive lt n_in beg_in end_in live_in ==>
     domain end_out SUBSET domain beg_out UNION domain (get_live_backward lt live_in)`,
  MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[LSCANPAUX_get_intervals_withlive_EQ] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[get_live_backward_def; domain_numset_list_add_if_lt;
      linear_scanProof_domain_numset_list_delete; domain_numset_list_add_if_gt] THEN
    ASM SET_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[get_live_backward_def; linear_scanProof_domain_numset_list_insert;
      linear_scanProof_domain_numset_list_delete; domain_numset_list_add_if_gt] THEN
    ASM SET_TAC[];
    (* Branch *)
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `domain (int_end2:int spt) SUBSET domain (int_beg2:int spt) UNION
                  domain (get_live_backward lt2 live_in)` ASSUME_TAC THENL
     [REMOVE_THEN "ih2" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `tl = sptree_map (K (&0:int)) (get_live_backward lt2 live_in)` THEN
    SUBGOAL_THEN `domain (tl:int spt) = domain (get_live_backward lt2 live_in)`
    ASSUME_TAC THENL [EXPAND_TAC "tl" THEN REWRITE_TAC[domain_map]; ALL_TAC] THEN
    RAPROOFAUX_TRIPLE_TAC
      `get_intervals_withlive lt1 n2 (sptree_union (difference int_beg2 live_in) tl) int_end2
         live_in` `n1':int` `ib1':int spt` `ie1':int spt` THEN
    RAPROOFAUX_TRIPLE_TAC `get_intervals lt1 n2 LN int_end2` `na:int` `ba:int spt`
      `ea:int spt` THEN
    SUBGOAL_THEN `ie1' = end_out:int spt` SUBST_ALL_TAC THENL
     [MP_TAC(ISPECL [`lt1:live_tree`; `n2:int`; `LN:int spt`;
        `difference (int_beg2:int spt) (live_in:1 spt)`; `int_end2:int spt`; `na:int`;
        `ba:int spt`; `ea:int spt`; `n_out:int`; `int_beg1:int spt`; `end_out:int spt`;
        `live_in:1 spt`] get_intervals_withlive_end_eq_get_intervals_end) THEN
      MP_TAC(ISPECL [`lt1:live_tree`; `n2:int`; `LN:int spt`;
        `sptree_union (difference (int_beg2:int spt) (live_in:1 spt)) tl`; `int_end2:int spt`;
        `na:int`; `ba:int spt`; `ea:int spt`; `n1':int`; `ib1':int spt`; `ie1':int spt`;
        `live_in:1 spt`] get_intervals_withlive_end_eq_get_intervals_end) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `domain (end_out:int spt) SUBSET domain (ib1':int spt) UNION
                  domain (get_live_backward lt1 live_in)` ASSUME_TAC THENL
     [REMOVE_THEN "ih1" (MP_TAC o SPECL [`n2:int`;
        `sptree_union (difference (int_beg2:int spt) (live_in:1 spt)) tl`; `int_end2:int spt`;
        `n1':int`; `ib1':int spt`; `end_out:int spt`; `live_in:1 spt`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[domain_union; domain_difference] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `domain (ib1':int spt) SUBSET domain (int_beg1:int spt) UNION
                  domain (get_live_backward lt2 live_in)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`lt1:live_tree`; `n2:int`; `difference (int_beg2:int spt) (live_in:1 spt)`;
        `int_end2:int spt`; `live_in:1 spt`; `n2:int`;
        `sptree_union (difference (int_beg2:int spt) (live_in:1 spt)) tl`; `int_end2:int spt`;
        `tl:int spt`; `n_out:int`; `int_beg1:int spt`; `end_out:int spt`; `n1':int`;
        `ib1':int spt`; `end_out:int spt`] get_intervals_withlive_beg_lipschitz) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[domain_union; domain_difference] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[get_live_backward_def; LET_DEF; LET_END_DEF;
      linear_scanProof_domain_numset_list_insert; branch_domain; domain_difference;
      domain_union] THEN
    ASM SET_TAC[];
    (* Seq *)
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `domain (int_end2:int spt) SUBSET domain (int_beg2:int spt) UNION
                  domain (get_live_backward lt2 live_in)` ASSUME_TAC THENL
     [REMOVE_THEN "ih2" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[get_live_backward_def] THEN
    REMOVE_THEN "ih1" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`n2:int`; `int_beg2:int spt`; `int_end2:int spt`; `n_out:int`] THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 1440 *)
let get_intervals_withlive_live_tree_registers_subset_endout = prove
 (`!lt n_in beg_in end_in live_in n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals_withlive lt n_in beg_in end_in live_in ==>
     domain end_in UNION live_tree_registers lt SUBSET domain end_out`,
  let tac =
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `domain (end_in:int spt) UNION live_tree_registers lt2 SUBSET
                  domain (int_end2:int spt) /\
                  domain int_end2 UNION live_tree_registers lt1 SUBSET
                  domain (end_out:int spt)` MP_TAC THENL
     [ASM_MESON_TAC[]; SET_TAC[]] in
  MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[LSCANPAUX_get_intervals_withlive_EQ; live_tree_registers_def] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[domain_numset_list_add_if_gt] THEN
    SET_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[domain_numset_list_add_if_gt] THEN
    SET_TAC[];
    tac; tac]);;

(* HOL4 line 1473 *)
let get_intervals_domain_eq_live_tree_registers = prove
 (`!lt n beg end.
     (n,beg,end) = get_intervals (fix_domination lt) (&0) LN LN ==>
     domain beg = live_tree_registers (fix_domination lt) /\
     domain end = live_tree_registers (fix_domination lt)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC `lt:live_tree` fix_domination_fixes_domination) THEN
  SPEC_TAC(`fix_domination lt`,`lt':live_tree`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
  RAPROOFAUX_TRIPLE_TAC `get_intervals_withlive lt' (&0) LN LN LN` `n':int` `beg':int spt`
    `end':int spt` THEN
  SUBGOAL_THEN `end' = end:int spt` SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`lt':live_tree`; `&0:int`; `LN:int spt`; `LN:int spt`; `LN:int spt`;
      `n:int`; `beg:int spt`; `end:int spt`; `n':int`; `beg':int spt`; `end':int spt`;
      `LN:1 spt`] get_intervals_withlive_end_eq_get_intervals_end) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `live_tree_registers lt' SUBSET domain (end:int spt)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`lt':live_tree`; `&0:int`; `LN:int spt`; `LN:int spt`; `LN:1 spt`;
      `n':int`; `beg':int spt`; `end:int spt`]
      get_intervals_withlive_live_tree_registers_subset_endout) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `domain (end:int spt) SUBSET domain (beg':int spt)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`lt':live_tree`; `&0:int`; `LN:int spt`; `LN:int spt`; `n':int`;
      `beg':int spt`; `end:int spt`; `LN:1 spt`]
      get_intervals_withlive_registers_subset_beg) THEN
    ASM_REWRITE_TAC[domain_def; UNION_EMPTY; SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `domain (beg':int spt) SUBSET domain (beg:int spt)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`lt':live_tree`; `&0:int`; `LN:int spt`; `LN:int spt`; `LN:int spt`;
      `n':int`; `beg':int spt`; `end:int spt`; `n:int`; `beg:int spt`; `end:int spt`;
      `LN:1 spt`] get_intervals_withlive_beg_subset_get_intervals_beg) THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `domain (beg:int spt) SUBSET live_tree_registers lt'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`lt':live_tree`; `&0:int`; `LN:int spt`; `LN:int spt`; `n:int`;
      `beg:int spt`; `end:int spt`] get_intervals_beg_subset_registers) THEN
    ASM_REWRITE_TAC[domain_def; UNION_EMPTY];
    ALL_TAC] THEN
  ASM SET_TAC[]);;

(* HOL4 line 1499 *)
let get_intervals_withlive_domain_eq_live_tree_registers = prove
 (`!lt n beg end.
     (n,beg,end) = get_intervals_withlive (fix_domination lt) (&0) LN LN LN ==>
     domain beg = live_tree_registers (fix_domination lt) /\
     domain end = live_tree_registers (fix_domination lt)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC `lt:live_tree` fix_domination_fixes_domination) THEN
  SPEC_TAC(`fix_domination lt`,`lt':live_tree`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
  RAPROOFAUX_TRIPLE_TAC `get_intervals lt' (&0) LN LN` `n':int` `beg':int spt`
    `end':int spt` THEN
  SUBGOAL_THEN `end' = end:int spt` SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`lt':live_tree`; `&0:int`; `LN:int spt`; `LN:int spt`; `LN:int spt`;
      `n':int`; `beg':int spt`; `end':int spt`; `n:int`; `beg:int spt`; `end:int spt`;
      `LN:1 spt`] get_intervals_withlive_end_eq_get_intervals_end) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `live_tree_registers lt' SUBSET domain (end:int spt)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`lt':live_tree`; `&0:int`; `LN:int spt`; `LN:int spt`; `LN:1 spt`;
      `n:int`; `beg:int spt`; `end:int spt`]
      get_intervals_withlive_live_tree_registers_subset_endout) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `domain (end:int spt) SUBSET domain (beg:int spt)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`lt':live_tree`; `&0:int`; `LN:int spt`; `LN:int spt`; `n:int`;
      `beg:int spt`; `end:int spt`; `LN:1 spt`]
      get_intervals_withlive_registers_subset_beg) THEN
    ASM_REWRITE_TAC[domain_def; UNION_EMPTY; SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `domain (beg:int spt) SUBSET domain (beg':int spt)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`lt':live_tree`; `&0:int`; `LN:int spt`; `LN:int spt`; `LN:int spt`;
      `n:int`; `beg:int spt`; `end:int spt`; `n':int`; `beg':int spt`; `end:int spt`;
      `LN:1 spt`] get_intervals_withlive_beg_subset_get_intervals_beg) THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `domain (beg':int spt) SUBSET live_tree_registers lt'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`lt':live_tree`; `&0:int`; `LN:int spt`; `LN:int spt`; `n':int`;
      `beg':int spt`; `end:int spt`] get_intervals_beg_subset_registers) THEN
    ASM_REWRITE_TAC[domain_def; UNION_EMPTY];
    ALL_TAC] THEN
  ASM SET_TAC[]);;

(* HOL4 line 1525 *)
let get_intervals_withlive_beg_eq_get_intervals_beg = prove
 (`!lt n beg end n' beg' end'.
     (n,beg,end) = get_intervals_withlive (fix_domination lt) (&0) LN LN LN /\
     (n',beg',end') = get_intervals (fix_domination lt) (&0) LN LN ==>
     !r:num. lookup r beg = lookup r beg'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `r:num` THEN
  SUBGOAL_THEN `domain (beg:int spt) = domain (beg':int spt)` ASSUME_TAC THENL
   [ASM_MESON_TAC[get_intervals_withlive_domain_eq_live_tree_registers;
                  get_intervals_domain_eq_live_tree_registers];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v1 v2. lookup r (beg':int spt) = SOME v1 /\ lookup r (beg:int spt) = SOME v2
                        ==> v1 = v2` MP_TAC THENL
   [MP_TAC(ISPECL [`fix_domination lt`; `&0:int`; `LN:int spt`; `LN:int spt`; `LN:int spt`;
      `n':int`; `beg':int spt`; `end':int spt`; `n:int`; `beg:int spt`; `end:int spt`;
      `LN:1 spt`] get_intervals_withlive_beg_eq_get_intervals_beg_when_some) THEN
    ASM_REWRITE_TAC[lookup_def; option_DISTINCT] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(?v. lookup r (beg:int spt) = SOME v) <=> (?v. lookup r (beg':int spt) = SOME v)`
  MP_TAC THENL [ASM_REWRITE_TAC[GSYM domain_lookup]; ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `lookup r (beg:int spt)` (cases "option")) THEN
  STRUCT_CASES_TAC(ISPEC `lookup r (beg':int spt)` (cases "option")) THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

(* HOL4 line 1546 *)
let get_intervals_end_increase = prove
 (`!lt n_in beg_in end_in n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals lt n_in beg_in end_in ==>
     domain end_in SUBSET domain end_out`,
  let tac =
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `domain (end_in:int spt) SUBSET domain (int_end2:int spt) /\
                  domain int_end2 SUBSET domain (end_out:int spt)` MP_TAC THENL
     [ASM_MESON_TAC[]; SET_TAC[]] in
  MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[LSCANPAUX_get_intervals_EQ] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[domain_numset_list_add_if_gt] THEN
    SET_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[domain_numset_list_add_if_gt] THEN
    SET_TAC[];
    tac; tac]);;

(* HOL4 line 1565 *)
let check_number_property_subset_endout = prove
 (`!lt n_in beg_in end_in (live_in:1 spt) n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals lt n_in beg_in end_in /\
     domain live_in SUBSET domain end_in ==>
     check_number_property_strong (\n (live:1 spt). domain live SUBSET domain end_out)
       lt n_in live_in`,
  MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LSCANPAUX_get_intervals_EQ; check_number_property_strong_def; LET_DEF;
                LET_END_DEF] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[linear_scanProof_domain_numset_list_delete; domain_numset_list_add_if_gt] THEN
    ASM SET_TAC[];
    REWRITE_TAC[LSCANPAUX_get_intervals_EQ; check_number_property_strong_def; LET_DEF;
                LET_END_DEF] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[linear_scanProof_domain_numset_list_insert; domain_numset_list_add_if_gt] THEN
    ASM SET_TAC[];
    (* Branch *)
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REWRITE_TAC[LSCANPAUX_get_intervals_EQ; check_number_property_strong_def; LET_DEF;
                LET_END_DEF] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `n2 = n_in - size_of_live_tree lt2` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[get_intervals_nout]; ALL_TAC] THEN
    SUBGOAL_THEN `domain (end_in:int spt) SUBSET domain (int_end2:int spt) /\
                  domain int_end2 SUBSET domain (end_out:int spt)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[get_intervals_end_increase]; ALL_TAC] THEN
    SUBGOAL_THEN `check_number_property_strong
                    (\n (live:1 spt). domain live SUBSET domain (end_out:int spt))
                    lt2 n_in live_in` ASSUME_TAC THENL
     [MATCH_MP_TAC check_number_property_strong_monotone_weak THEN
      EXISTS_TAC `\(n:int) (live:1 spt). domain live SUBSET domain (int_end2:int spt)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[] THEN ASM SET_TAC[];
        REMOVE_THEN "ih2" MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET_TRANS]];
      ALL_TAC] THEN
    SUBGOAL_THEN `check_number_property_strong
                    (\n (live:1 spt). domain live SUBSET domain (end_out:int spt))
                    lt1 (n_in - size_of_live_tree lt2) live_in` ASSUME_TAC THENL
     [REMOVE_THEN "ih1" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`int_beg2:int spt`; `int_end2:int spt`; `n_out:int`;
                            `beg_out:int spt`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[get_live_backward_def; LET_DEF; LET_END_DEF;
      linear_scanProof_domain_numset_list_insert; branch_domain; UNION_SUBSET] THEN
    CONJ_TAC THENL
     [MP_TAC(BETA_RULE(MATCH_MP check_number_property_strong_end (ASSUME
        `check_number_property_strong
           (\n (live:1 spt). domain live SUBSET domain (end_out:int spt))
           lt1 (n_in - size_of_live_tree lt2) live_in`))) THEN REWRITE_TAC[];
      MP_TAC(BETA_RULE(MATCH_MP check_number_property_strong_end (ASSUME
        `check_number_property_strong
           (\n (live:1 spt). domain live SUBSET domain (end_out:int spt))
           lt2 n_in live_in`))) THEN REWRITE_TAC[]];
    (* Seq *)
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REWRITE_TAC[LSCANPAUX_get_intervals_EQ; check_number_property_strong_def; LET_DEF;
                LET_END_DEF] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `n2 = n_in - size_of_live_tree lt2` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[get_intervals_nout]; ALL_TAC] THEN
    SUBGOAL_THEN `domain (end_in:int spt) SUBSET domain (int_end2:int spt) /\
                  domain int_end2 SUBSET domain (end_out:int spt)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[get_intervals_end_increase]; ALL_TAC] THEN
    SUBGOAL_THEN `check_number_property_strong
                    (\n (live:1 spt). domain live SUBSET domain (int_end2:int spt))
                    lt2 n_in live_in` ASSUME_TAC THENL
     [REMOVE_THEN "ih2" MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REMOVE_THEN "ih1" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`int_beg2:int spt`; `int_end2:int spt`; `n_out:int`;
                            `beg_out:int spt`] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(BETA_RULE(MATCH_MP check_number_property_strong_end (ASSUME
        `check_number_property_strong
           (\n (live:1 spt). domain live SUBSET domain (int_end2:int spt))
           lt2 n_in live_in`))) THEN REWRITE_TAC[];
      MATCH_MP_TAC check_number_property_strong_monotone_weak THEN
      EXISTS_TAC `\(n:int) (live:1 spt). domain live SUBSET domain (int_end2:int spt)` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]]);;

(* HOL4 line 1622 *)
let get_intervals_beg_less_live = prove
 (`!lt (live_in:1 spt) n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals (fix_domination lt) (&0) LN LN ==>
     check_number_property_strong
       (\n (live:1 spt). !r. r IN domain live ==>
                             option_CASE (lookup r beg_out) n_out (\x. x) <= n)
       (fix_domination lt) (&0) LN`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  RAPROOFAUX_TRIPLE_TAC `get_intervals_withlive (fix_domination lt) (&0) LN LN LN` `n':int`
    `beg':int spt` `end':int spt` THEN
  SUBGOAL_THEN `n':int = n_out` SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`fix_domination lt`; `&0:int`; `LN:int spt`; `LN:int spt`; `LN:int spt`;
      `LN:int spt`; `n_out:int`; `beg_out:int spt`; `end_out:int spt`; `n':int`;
      `beg':int spt`; `end':int spt`; `LN:1 spt`]
      get_intervals_withlive_n_eq_get_intervals_n) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. lookup r (beg':int spt) = lookup r beg_out` ASSUME_TAC THENL
   [MATCH_MP_TAC get_intervals_withlive_beg_eq_get_intervals_beg THEN
    MAP_EVERY EXISTS_TAC [`lt:live_tree`; `n_out:int`; `end':int spt`; `n_out:int`;
                          `end_out:int spt`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`fix_domination lt`; `&0:int`; `LN:int spt`; `LN:int spt`; `LN:1 spt`;
    `n_out:int`; `beg':int spt`; `end':int spt`] get_intervals_withlive_beg_less_live) THEN
  ASM_REWRITE_TAC[lookup_def; option_DISTINCT; domain_def; NOT_IN_EMPTY]);;

(* HOL4 line 1646 *)
let get_intervals_intbeg_reduce = prove
 (`!lt n_in beg_in end_in n_out beg_out end_out (live:1 spt).
     (n_out,beg_out,end_out) = get_intervals lt n_in beg_in end_in /\
     (!r v. lookup r beg_in = SOME v ==> n_in <= v) ==>
     (!r. option_CASE (lookup r beg_out) n_out (\x. x) <=
          option_CASE (lookup r beg_in) n_in (\x. x)) /\
     (!r v. lookup r beg_out = SOME v ==> n_out <= v)`,
  let tac =
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`n_in:int`; `beg_in:int spt`; `end_in:int spt`;
      `n2:int`; `int_beg2:int spt`; `int_end2:int spt`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`n2:int`; `int_beg2:int spt`; `int_end2:int spt`;
      `n_out:int`; `beg_out:int spt`; `end_out:int spt`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:num` THEN ASM_MESON_TAC[INT_LE_TRANS] in
  MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[LSCANPAUX_get_intervals_EQ] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[lookup_numset_list_add_if_lt] THEN
    CONJ_TAC THEN X_GEN_TAC `r:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN
    LSCANPAUX_OPT_TAC [`lookup r (beg_in:int spt)`];
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN X_GEN_TAC `r:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN
    LSCANPAUX_OPT_TAC [`lookup r (beg_in:int spt)`];
    tac; tac]);;

(* HOL4 line 1694 *)
let check_startlive_prop_monotone = prove
 (`!lt beg ndef end beg' ndef' end' n_in.
     (!r. option_CASE (lookup r beg') ndef' (\x. x) <=
          option_CASE (lookup r beg) ndef (\x. x)) /\
     (!r v. lookup r end = SOME v ==> (?v'. lookup r end' = SOME v' /\ v <= v')) /\
     check_startlive_prop lt n_in beg end ndef ==>
     check_startlive_prop lt n_in beg' end' ndef'`,
  MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[check_startlive_prop_def; LET_DEF; LET_END_DEF] THENL
   [REPEAT STRIP_TAC THEN ASM_MESON_TAC[INT_LE_TRANS];
    MESON_TAC[];
    MESON_TAC[]]);;

(* HOL4 line 1711 *)
let check_startlive_prop_augment_ndef = prove
 (`!ndef' lt n_in beg_out end_out ndef.
     check_startlive_prop lt n_in beg_out end_out ndef /\
     ndef <= ndef' /\
     ndef' <= n_in - size_of_live_tree lt ==>
     check_startlive_prop lt n_in beg_out end_out ndef'`,
  let tac =
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPEC `lt1:live_tree` size_of_live_tree_positive) THEN DISCH_TAC THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `ndef:int` THEN
    ASM_REWRITE_TAC[] THEN LSCANPAUX_INT_ARITH_TAC in
  GEN_TAC THEN MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[check_startlive_prop_def; size_of_live_tree_def] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN LSCANPAUX_OPT_TAC [`lookup r (beg_out:int spt)`];
    REWRITE_TAC[check_startlive_prop_def];
    REWRITE_TAC[check_startlive_prop_def; size_of_live_tree_def; LET_DEF; LET_END_DEF] THEN
    tac;
    REWRITE_TAC[check_startlive_prop_def; size_of_live_tree_def; LET_DEF; LET_END_DEF] THEN
    tac]);;

(* HOL4 line 1737 *)
let get_intervals_check_startlive_prop = prove
 (`!lt n_in beg_in end_in n_out beg_out end_out.
     (n_out,beg_out,end_out) = get_intervals lt n_in beg_in end_in /\
     (!r v. lookup r beg_in = SOME v ==> n_in <= v) ==>
     check_startlive_prop lt n_in beg_out end_out n_out`,
  let tac =
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REWRITE_TAC[LSCANPAUX_get_intervals_EQ; check_startlive_prop_def; LET_DEF;
                LET_END_DEF] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `check_startlive_prop lt2 n_in int_beg2 int_end2 n2` ASSUME_TAC THENL
     [REMOVE_THEN "ih2" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `!r v. lookup r (int_beg2:int spt) = SOME v ==> n2 <= v` ASSUME_TAC THENL
     [ASM_MESON_TAC[get_intervals_intbeg_reduce]; ALL_TAC] THEN
    SUBGOAL_THEN `check_startlive_prop lt1 n2 beg_out end_out n_out` ASSUME_TAC THENL
     [REMOVE_THEN "ih1" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `n2 = n_in - size_of_live_tree lt2` (SUBST_ALL_TAC o SYM) THENL
     [ASM_MESON_TAC[get_intervals_nout]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC check_startlive_prop_monotone THEN
    MAP_EVERY EXISTS_TAC [`int_beg2:int spt`; `n2:int`; `int_end2:int spt`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[get_intervals_intbeg_reduce];
      ASM_MESON_TAC[get_intervals_intend_augment]] in
  MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `l:num list` THEN
    REWRITE_TAC[LSCANPAUX_get_intervals_EQ; check_startlive_prop_def] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`l:num list`; `n_in:int`; `beg_in:int spt`; `r:num`]
        LSCANPAUX_lookup_add_if_lt) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[case_def "option"];
      ASM_MESON_TAC[LSCANPAUX_lookup_add_if_gt]];
    REWRITE_TAC[check_startlive_prop_def];
    tac; tac]);;

(* HOL4 line 1767 *)
let exists_point_inside_interval_interval_intersect = prove
 (`!l1 r1 l2 r2 v.
     point_inside_interval (l1,r1) v /\ point_inside_interval (l2,r2) v ==>
     interval_intersect (l1,r1) (l2,r2)`,
  REWRITE_TAC[point_inside_interval_def; interval_intersect_def] THEN INT_ARITH_TAC);;

(* LSCANPAUX_check_intervals_INJ: registers whose intervals all contain one *)
(* point N have different colours under check_intervals                    *)
let LSCANPAUX_check_intervals_INJ = prove
 (`!(f:num->num) beg end s (N:int).
     check_intervals f beg end /\
     (!r. r IN s ==> ?vb ve. lookup r beg = SOME vb /\ lookup r end = SOME ve /\
                             vb <= N /\ N <= ve) ==>
     INJ f s UNIV`,
  REWRITE_TAC[check_intervals_def; INJ; IN_UNIV; interval_intersect_def] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ci") (LABEL_TAC "in")) THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
  USE_THEN "in" (MP_TAC o SPEC `x:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `vbx:int` (X_CHOOSE_THEN `vex:int` STRIP_ASSUME_TAC)) THEN
  USE_THEN "in" (MP_TAC o SPEC `y:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `vby:int` (X_CHOOSE_THEN `vey:int` STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "ci" MATCH_MP_TAC THEN ASM_REWRITE_TAC[THE_DEF] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[domain_lookup]; ASM_MESON_TAC[domain_lookup];
    LSCANPAUX_INT_ARITH_TAC; LSCANPAUX_INT_ARITH_TAC]);;

(* HOL4 line 1776 *)
let check_intervals_check_live_tree_lemma = prove
 (`!n_out lt n_in beg_out end_out f live flive.
     check_startlive_prop lt n_in beg_out end_out (n_in - size_of_live_tree lt) /\
     check_number_property_strong
       (\n (live':1 spt). !r. r IN domain live' ==>
                              option_CASE (lookup r beg_out) n_out (\x. x) <= n)
       lt n_in live /\
     check_number_property
       (\n (live':1 spt). !r. r IN domain live' ==>
                              ?v. lookup r end_out = SOME v /\ n + &1 <= v)
       lt n_in live /\
     check_number_property_strong (\n (live':1 spt). domain live' SUBSET domain end_out)
       lt n_in live /\
     domain beg_out = domain end_out /\
     live_tree_registers lt SUBSET domain end_out /\
     check_intervals f beg_out end_out /\
     domain flive = IMAGE f (domain live) /\
     INJ f (domain live) UNIV ==>
     ?liveout fliveout. check_live_tree f lt live flive = SOME (liveout,fliveout)`,
  let labs =
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "csp") (CONJUNCTS_THEN2 (LABEL_TAC "beg")
      (CONJUNCTS_THEN2 (LABEL_TAC "end") (CONJUNCTS_THEN2 (LABEL_TAC "sub")
      (CONJUNCTS_THEN2 (LABEL_TAC "dom") (CONJUNCTS_THEN2 (LABEL_TAC "ltr")
      (CONJUNCTS_THEN2 (LABEL_TAC "ci") (CONJUNCTS_THEN2 (LABEL_TAC "img")
      (LABEL_TAC "inj"))))))))) in
  let in_beg lab =
    SUBGOAL_THEN `?vb. lookup r (beg_out:int spt) = SOME vb` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM domain_lookup] THEN USE_THEN "dom" SUBST1_TAC THEN
      USE_THEN lab (MP_TAC o REWRITE_RULE[SUBSET; IN_SET_OF_LIST]) THEN ASM_MESON_TAC[];
      ALL_TAC] in
  GEN_TAC THEN MATCH_MP_TAC live_tree_INDUCT THEN REPEAT CONJ_TAC THENL
   [(* Writes *)
    X_GEN_TAC `l:num list` THEN
    REWRITE_TAC[check_startlive_prop_def; check_number_property_strong_def;
      check_number_property_def; live_tree_registers_def; size_of_live_tree_def;
      LSCANPAUX_check_live_tree_SOME; LET_DEF; LET_END_DEF] THEN
    REPEAT GEN_TAC THEN labs THEN
    SUBGOAL_THEN `INJ (f:num->num) (set_of_list l UNION domain (live:1 spt)) UNIV`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LSCANPAUX_check_intervals_INJ THEN
      MAP_EVERY EXISTS_TAC [`beg_out:int spt`; `end_out:int spt`; `n_in:int`] THEN
      ASM_REWRITE_TAC[IN_UNION; IN_SET_OF_LIST] THEN X_GEN_TAC `r:num` THEN
      ASM_CASES_TAC `MEM (r:num) l` THEN ASM_REWRITE_TAC[] THENL
       [USE_THEN "csp" (MP_TAC o SPEC `r:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        in_beg "ltr" THEN ASM_REWRITE_TAC[case_def "option"] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `ve:int` STRIP_ASSUME_TAC)) THEN
        MAP_EVERY EXISTS_TAC [`vb:int`; `ve:int`] THEN ASM_REWRITE_TAC[];
        DISCH_TAC THEN
        SUBGOAL_THEN `r IN domain (numset_list_delete l (live:1 spt))` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[linear_scanProof_domain_numset_list_delete; IN_DIFF;
                          IN_SET_OF_LIST];
          ALL_TAC] THEN
        USE_THEN "beg" (MP_TAC o SPEC `r:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        USE_THEN "end" (MP_TAC o SPEC `r:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        in_beg "sub" THEN ASM_REWRITE_TAC[case_def "option"] THEN
        DISCH_THEN(X_CHOOSE_THEN `ve:int` STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
        MAP_EVERY EXISTS_TAC [`vb:int`; `ve:int`] THEN ASM_REWRITE_TAC[] THEN
        LSCANPAUX_INT_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`l:num list`; `live:1 spt`; `flive:1 spt`; `f:num->num`]
      check_partial_col_success) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    (* Reads *)
    X_GEN_TAC `l:num list` THEN
    REWRITE_TAC[check_startlive_prop_def; check_number_property_strong_def;
      check_number_property_def; live_tree_registers_def; size_of_live_tree_def;
      LSCANPAUX_check_live_tree_SOME; LET_DEF; LET_END_DEF] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "beg")
      (CONJUNCTS_THEN2 (LABEL_TAC "end") (CONJUNCTS_THEN2 (LABEL_TAC "sub")
      (CONJUNCTS_THEN2 (LABEL_TAC "dom") (CONJUNCTS_THEN2 (LABEL_TAC "ltr")
      (CONJUNCTS_THEN2 (LABEL_TAC "ci") (CONJUNCTS_THEN2 (LABEL_TAC "img")
      (LABEL_TAC "inj")))))))) THEN
    SUBGOAL_THEN `INJ (f:num->num) (set_of_list l UNION domain (live:1 spt)) UNIV`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LSCANPAUX_check_intervals_INJ THEN
      MAP_EVERY EXISTS_TAC [`beg_out:int spt`; `end_out:int spt`; `n_in:int`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `r IN domain (linear_scan_numset_list_insert l (live:1 spt))` ASSUME_TAC
      THENL [ASM_REWRITE_TAC[linear_scanProof_domain_numset_list_insert]; ALL_TAC] THEN
      USE_THEN "beg" (MP_TAC o SPEC `r:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "end" (MP_TAC o SPEC `r:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      in_beg "sub" THEN ASM_REWRITE_TAC[case_def "option"] THEN
      DISCH_THEN(X_CHOOSE_THEN `ve:int` STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`vb:int`; `ve:int`] THEN ASM_REWRITE_TAC[] THEN
      LSCANPAUX_INT_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`l:num list`; `live:1 spt`; `flive:1 spt`; `f:num->num`]
      check_partial_col_success) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    (* Branch *)
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REWRITE_TAC[check_startlive_prop_def; check_number_property_strong_def;
      check_number_property_def; live_tree_registers_def; size_of_live_tree_def;
      LSCANPAUX_check_live_tree_SOME; LET_DEF; LET_END_DEF; UNION_SUBSET] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPEC `lt1:live_tree` size_of_live_tree_positive) THEN
    MP_TAC(SPEC `lt2:live_tree` size_of_live_tree_positive) THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `(n_in - size_of_live_tree lt2) - size_of_live_tree lt1 =
                  n_in - (size_of_live_tree lt1 + size_of_live_tree lt2)` ASSUME_TAC THENL
     [INT_ARITH_TAC; ALL_TAC] THEN
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`n_in:int`; `beg_out:int spt`; `end_out:int spt`;
      `f:num->num`; `live:1 spt`; `flive:1 spt`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC check_startlive_prop_augment_ndef THEN
      EXISTS_TAC `n_in - (size_of_live_tree lt1 + size_of_live_tree lt2)` THEN
      ASM_REWRITE_TAC[INT_LE_REFL] THEN LSCANPAUX_INT_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `live2:1 spt` (X_CHOOSE_TAC `flive2:1 spt`))] THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`n_in - size_of_live_tree lt2`; `beg_out:int spt`;
      `end_out:int spt`; `f:num->num`; `live:1 spt`; `flive:1 spt`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `live1:1 spt` (X_CHOOSE_TAC `flive1:1 spt`))] THEN
    SUBGOAL_THEN `live1 = get_live_backward lt1 (live:1 spt) /\
                  live2 = get_live_backward lt2 live` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [ASM_MESON_TAC[check_live_tree_eq_get_live_backward]; ALL_TAC] THEN
    SUBGOAL_THEN `domain (flive1:1 spt) = IMAGE (f:num->num) (domain
                    (get_live_backward lt1 (live:1 spt)))` ASSUME_TAC THENL
     [ASM_MESON_TAC[check_live_tree_success]; ALL_TAC] THEN
    SUBGOAL_THEN `INJ (f:num->num) (domain (get_live_backward lt1 (live:1 spt)) UNION
                                    domain (get_live_backward lt2 live)) UNIV`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LSCANPAUX_check_intervals_INJ THEN
      MAP_EVERY EXISTS_TAC [`beg_out:int spt`; `end_out:int spt`;
        `n_in - (size_of_live_tree lt1 + size_of_live_tree lt2)`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `r IN domain (get_live_backward (linear_scan_Branch lt1 lt2) (live:1 spt))`
      ASSUME_TAC THENL
       [ASM_REWRITE_TAC[get_live_backward_def; LET_DEF; LET_END_DEF;
                        linear_scanProof_domain_numset_list_insert; branch_domain];
        ALL_TAC] THEN
      SUBGOAL_THEN `?vb. lookup r (beg_out:int spt) = SOME vb` STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[GSYM domain_lookup] THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `vb <= n_in - (size_of_live_tree lt1 + size_of_live_tree lt2)`
      ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th -> is_forall (concl th) &&
          free_in `get_live_backward (linear_scan_Branch lt1 lt2) (live:1 spt)` (concl th))) THEN
        ASM_REWRITE_TAC[case_def "option"];
        ALL_TAC] THEN
      SUBGOAL_THEN `?ve. lookup r (end_out:int spt) = SOME ve /\
                         n_in - (size_of_live_tree lt1 + size_of_live_tree lt2) <= ve`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `r IN domain (get_live_backward lt1 (live:1 spt)) UNION
                       domain (get_live_backward lt2 live)` THEN
        REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
         [MP_TAC(ISPECL [`end_out:int spt`; `lt1:live_tree`; `n_in - size_of_live_tree lt2`;
            `live:1 spt`] check_number_property_intend) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[];
          MP_TAC(ISPECL [`end_out:int spt`; `lt2:live_tree`; `n_in:int`;
            `live:1 spt`] check_number_property_intend) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
          DISCH_THEN(X_CHOOSE_THEN `ve:int` STRIP_ASSUME_TAC) THEN
          EXISTS_TAC `ve:int` THEN ASM_REWRITE_TAC[] THEN LSCANPAUX_INT_ARITH_TAC];
        ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`vb:int`; `ve:int`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`MAP FST (toAList (difference (get_live_backward lt2 (live:1 spt))
                                                (get_live_backward lt1 live)))`;
                  `get_live_backward lt1 (live:1 spt)`; `flive1:1 spt`; `f:num->num`]
      check_partial_col_success) THEN
    ASM_REWRITE_TAC[branch_domain] THEN ASM_MESON_TAC[];
    (* Seq *)
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REWRITE_TAC[check_startlive_prop_def; check_number_property_strong_def;
      check_number_property_def; live_tree_registers_def; size_of_live_tree_def;
      LSCANPAUX_check_live_tree_SOME; LET_DEF; LET_END_DEF; UNION_SUBSET] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPEC `lt1:live_tree` size_of_live_tree_positive) THEN
    MP_TAC(SPEC `lt2:live_tree` size_of_live_tree_positive) THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `(n_in - size_of_live_tree lt2) - size_of_live_tree lt1 =
                  n_in - (size_of_live_tree lt1 + size_of_live_tree lt2)` ASSUME_TAC THENL
     [INT_ARITH_TAC; ALL_TAC] THEN
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`n_in:int`; `beg_out:int spt`; `end_out:int spt`;
      `f:num->num`; `live:1 spt`; `flive:1 spt`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC check_startlive_prop_augment_ndef THEN
      EXISTS_TAC `n_in - (size_of_live_tree lt1 + size_of_live_tree lt2)` THEN
      ASM_REWRITE_TAC[INT_LE_REFL] THEN LSCANPAUX_INT_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `live2:1 spt` (X_CHOOSE_TAC `flive2:1 spt`))] THEN
    SUBGOAL_THEN `live2 = get_live_backward lt2 (live:1 spt)` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[check_live_tree_eq_get_live_backward]; ALL_TAC] THEN
    SUBGOAL_THEN `domain (flive2:1 spt) = IMAGE (f:num->num) (domain
                    (get_live_backward lt2 (live:1 spt))) /\
                  INJ f (domain (get_live_backward lt2 live)) UNIV` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[check_live_tree_success]; ALL_TAC] THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`n_in - size_of_live_tree lt2`; `beg_out:int spt`;
      `end_out:int spt`; `f:num->num`; `get_live_backward lt2 (live:1 spt)`;
      `flive2:1 spt`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_MESON_TAC[]]]);;

(* HOL4 line 1930 *)
let check_intervals_check_live_tree = prove
 (`!lt n_out beg_out end_out f.
     (n_out,beg_out,end_out) = get_intervals (fix_domination lt) (&0) LN LN /\
     check_intervals f beg_out end_out ==>
     ?liveout fliveout.
       check_live_tree f (fix_domination lt) LN LN = SOME (liveout,fliveout)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC check_intervals_check_live_tree_lemma THEN
  MAP_EVERY EXISTS_TAC [`n_out:int`; `&0:int`; `beg_out:int spt`; `end_out:int spt`] THEN
  ASM_REWRITE_TAC[domain_def; IMAGE_CLAUSES; INJ; NOT_IN_EMPTY] THEN
  SUBGOAL_THEN `n_out = &0 - size_of_live_tree (fix_domination lt)` (SUBST1_TAC o SYM) THENL
   [ASM_MESON_TAC[get_intervals_nout]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC get_intervals_check_startlive_prop THEN
    MAP_EVERY EXISTS_TAC [`LN:int spt`; `LN:int spt`] THEN
    ASM_REWRITE_TAC[lookup_def; option_DISTINCT];
    MATCH_MP_TAC get_intervals_beg_less_live THEN
    EXISTS_TAC `end_out:int spt` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC get_intervals_live_less_end THEN
    MAP_EVERY EXISTS_TAC [`LN:int spt`; `LN:int spt`; `n_out:int`; `beg_out:int spt`] THEN
    ASM_REWRITE_TAC[domain_def; NOT_IN_EMPTY];
    MATCH_MP_TAC check_number_property_subset_endout THEN
    MAP_EVERY EXISTS_TAC [`LN:int spt`; `LN:int spt`; `n_out:int`; `beg_out:int spt`] THEN
    ASM_REWRITE_TAC[domain_def; EMPTY_SUBSET];
    ASM_MESON_TAC[get_intervals_domain_eq_live_tree_registers];
    ASM_MESON_TAC[get_intervals_domain_eq_live_tree_registers; SUBSET_REFL]]);;

(* HOL4 line 1952 *)
let get_intervals_ct_aux_live = prove
 (`!ct n_in beg_in end_in live_in live_in' n_out beg_out end_out live_out.
     domain live_in = domain live_in' /\
     (n_out,beg_out,end_out,live_out) = get_intervals_ct_aux ct n_in beg_in end_in live_in ==>
     domain live_out = domain (get_live_backward (get_live_tree ct) live_in')`,
  MATCH_MP_TAC LSCANPAUX_clash_tree_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[LSCANPAUX_get_intervals_ct_aux_EQ; LSCANPAUX_get_live_tree;
              get_live_backward_def; LET_DEF; LET_END_DEF] THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[linear_scanProof_domain_numset_list_insert;
                    linear_scanProof_domain_numset_list_delete];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[linear_scanProof_domain_numset_list_insert; domain_union;
                    set_MAP_FST_toAList_domain];
    MAP_EVERY X_GEN_TAC [`ct1:clash_tree`; `ct2:clash_tree`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[linear_scanProof_domain_numset_list_insert; domain_union; branch_domain] THEN
    BINOP_TAC THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`cutset:1 spt`; `ct1:clash_tree`; `ct2:clash_tree`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[linear_scanProof_domain_numset_list_insert; domain_union; branch_domain;
                    set_MAP_FST_toAList_domain] THEN
    AP_TERM_TAC THEN BINOP_TAC THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`ct1:clash_tree`; `ct2:clash_tree`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `domain (live2:1 spt) = domain (get_live_backward (get_live_tree ct2) live_in')`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]]]);;

(* HOL4 line 1979 *)
let get_intervals_ct_aux_int = prove
 (`!ct n_in beg_in end_in live_in n_out beg_out end_out live_out.
     (n_out,beg_out,end_out,live_out) = get_intervals_ct_aux ct n_in beg_in end_in live_in ==>
     (n_out,beg_out,end_out) = get_intervals (get_live_tree ct) n_in beg_in end_in`,
  MATCH_MP_TAC LSCANPAUX_clash_tree_INDUCT THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[LSCANPAUX_get_intervals_ct_aux_EQ; LSCANPAUX_get_live_tree;
              LSCANPAUX_get_intervals_EQ] THENL
   [MAP_EVERY X_GEN_TAC [`wr:num list`; `rd:num list`] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`(n_in:int) - &1`; `numset_list_add_if_lt wr (n_in:int) beg_in`;
                          `numset_list_add_if_gt wr (n_in:int) end_in`] THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`ct1:clash_tree`; `ct2:clash_tree`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`n2:int`; `int_beg2:int spt`; `int_end2:int spt`] THEN
    ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`cutset:1 spt`; `ct1:clash_tree`; `ct2:clash_tree`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`n1:int`; `beg_out:int spt`; `int_end1:int spt`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`n2:int`; `int_beg2:int spt`; `int_end2:int spt`] THEN
    ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`ct1:clash_tree`; `ct2:clash_tree`] THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`n2:int`; `int_beg2:int spt`; `int_end2:int spt`] THEN
    ASM_MESON_TAC[]]);;

(* HOL4 line 2003 *)
let get_intervals_ct_eq = prove
 (`!ct int_beg1 int_beg2 int_end1 int_end2 n1 n2.
     (n1,int_beg1,int_end1) = get_intervals_ct ct /\
     (n2,int_beg2,int_end2) = get_intervals (fix_domination (get_live_tree ct)) (&0) LN LN ==>
     (!r. lookup r int_beg1 = lookup r int_beg2) /\
     (!r. lookup r int_end1 = lookup r int_end2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[get_intervals_ct_def; LET_DEF; LET_END_DEF] THEN
  REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `(n,int_beg,int_end) = get_intervals (get_live_tree ct) (&0) LN LN`
  ASSUME_TAC THENL
   [MATCH_MP_TAC get_intervals_ct_aux_int THEN
    MAP_EVERY EXISTS_TAC [`LN:1 spt`; `live:1 spt`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `domain (live:1 spt) = domain (get_live_backward (get_live_tree ct) LN)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC get_intervals_ct_aux_live THEN
    MAP_EVERY EXISTS_TAC [`&0:int`; `LN:int spt`; `LN:int spt`; `LN:1 spt`; `n:int`;
                          `int_beg:int spt`; `int_end:int spt`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[lookup_numset_list_add_if_lt; lookup_numset_list_add_if_gt] THEN
  REWRITE_TAC[fix_domination_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `int_beg2:int spt = int_beg /\ int_end2:int spt = int_end`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_MESON_TAC[PAIR_EQ]; ALL_TAC] THEN
    SUBGOAL_THEN `!r. ~MEM r (MAP FST (toAList (live:1 spt)))` (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[GSYM IN_SET_OF_LIST; set_MAP_FST_toAList_domain; domain_def;
                    NOT_IN_EMPTY];
    REWRITE_TAC[LSCANPAUX_get_intervals_EQ] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:int` (X_CHOOSE_THEN `b:int spt`
      (X_CHOOSE_THEN `e:int spt` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `m:int = n /\ b:int spt = int_beg /\ e:int spt = int_end`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[PAIR_EQ]; ALL_TAC] THEN
    ASM_REWRITE_TAC[lookup_numset_list_add_if_lt; lookup_numset_list_add_if_gt] THEN
    SUBGOAL_THEN `!r. MEM r (MAP FST (toAList (live:1 spt))) <=>
                      MEM r (MAP FST (toAList (get_live_backward (get_live_tree ct) LN)))`
      (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[GSYM IN_SET_OF_LIST; set_MAP_FST_toAList_domain]]);;

(* HOL4 lines 2020-2128: the [simp] equations of the array accessors *)

(* HOL4 line 2020 *)
let colors_sub_eqn = prove
 (`!n s.
     colors_sub n s =
       if n < LENGTH (linear_scan_hidden_state_colors s)
       then (M_success (EL n (linear_scan_hidden_state_colors s)),s)
       else (M_failure Subscript,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[colors_sub_def; ml_monadBase_Marray_sub_def] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[ml_monadBase_Msub_eq];
    POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ml_monadBase_Msub_exn_eq; GE]]);;

(* HOL4 line 2031 *)
let update_colors_eqn = prove
 (`!n t s.
     update_colors n t s =
       if n < LENGTH (linear_scan_hidden_state_colors s)
       then (M_success one,
             linear_scan_hidden_state_colors_fupd
               (K (LUPDATE t n (linear_scan_hidden_state_colors s))) s)
       else (M_failure Subscript,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[update_colors_def; ml_monadBase_Marray_update_def] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[ml_monadBase_Mupdate_eq; case_def "exc"];
    POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ml_monadBase_Mupdate_exn_eq; GE; case_def "exc"]]);;

(* HOL4 line 2042 *)
let int_beg_sub_eqn = prove
 (`!n s.
     int_beg_sub n s =
       if n < LENGTH (linear_scan_hidden_state_int_beg s)
       then (M_success (EL n (linear_scan_hidden_state_int_beg s)),s)
       else (M_failure Subscript,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_beg_sub_def; ml_monadBase_Marray_sub_def] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[ml_monadBase_Msub_eq];
    POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ml_monadBase_Msub_exn_eq; GE]]);;

(* HOL4 line 2053 *)
let update_int_beg_eqn = prove
 (`!n t s.
     update_int_beg n t s =
       if n < LENGTH (linear_scan_hidden_state_int_beg s)
       then (M_success one,
             linear_scan_hidden_state_int_beg_fupd
               (K (LUPDATE t n (linear_scan_hidden_state_int_beg s))) s)
       else (M_failure Subscript,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[update_int_beg_def; ml_monadBase_Marray_update_def] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[ml_monadBase_Mupdate_eq; case_def "exc"];
    POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ml_monadBase_Mupdate_exn_eq; GE; case_def "exc"]]);;

(* HOL4 line 2064 *)
let int_end_sub_eqn = prove
 (`!n s.
     int_end_sub n s =
       if n < LENGTH (linear_scan_hidden_state_int_end s)
       then (M_success (EL n (linear_scan_hidden_state_int_end s)),s)
       else (M_failure Subscript,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_end_sub_def; ml_monadBase_Marray_sub_def] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[ml_monadBase_Msub_eq];
    POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ml_monadBase_Msub_exn_eq; GE]]);;

(* HOL4 line 2075 *)
let update_int_end_eqn = prove
 (`!n t s.
     update_int_end n t s =
       if n < LENGTH (linear_scan_hidden_state_int_end s)
       then (M_success one,
             linear_scan_hidden_state_int_end_fupd
               (K (LUPDATE t n (linear_scan_hidden_state_int_end s))) s)
       else (M_failure Subscript,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[update_int_end_def; ml_monadBase_Marray_update_def] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[ml_monadBase_Mupdate_eq; case_def "exc"];
    POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ml_monadBase_Mupdate_exn_eq; GE; case_def "exc"]]);;

(* HOL4 line 2086 *)
let sorted_regs_sub_eqn = prove
 (`!n s.
     sorted_regs_sub n s =
       if n < LENGTH (linear_scan_hidden_state_sorted_regs s)
       then (M_success (EL n (linear_scan_hidden_state_sorted_regs s)),s)
       else (M_failure Subscript,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sorted_regs_sub_def; ml_monadBase_Marray_sub_def] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[ml_monadBase_Msub_eq];
    POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ml_monadBase_Msub_exn_eq; GE]]);;

(* HOL4 line 2097 *)
let update_sorted_regs_eqn = prove
 (`!n t s.
     update_sorted_regs n t s =
       if n < LENGTH (linear_scan_hidden_state_sorted_regs s)
       then (M_success one,
             linear_scan_hidden_state_sorted_regs_fupd
               (K (LUPDATE t n (linear_scan_hidden_state_sorted_regs s))) s)
       else (M_failure Subscript,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[update_sorted_regs_def; ml_monadBase_Marray_update_def] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[ml_monadBase_Mupdate_eq; case_def "exc"];
    POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ml_monadBase_Mupdate_exn_eq; GE; case_def "exc"]]);;

(* HOL4 line 2108 *)
let sorted_moves_sub_eqn = prove
 (`!n s.
     sorted_moves_sub n s =
       if n < LENGTH (linear_scan_hidden_state_sorted_moves s)
       then (M_success (EL n (linear_scan_hidden_state_sorted_moves s)),s)
       else (M_failure Subscript,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sorted_moves_sub_def; ml_monadBase_Marray_sub_def] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[ml_monadBase_Msub_eq];
    POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ml_monadBase_Msub_exn_eq; GE]]);;

(* HOL4 line 2119 *)
let update_sorted_moves_eqn = prove
 (`!n t s.
     update_sorted_moves n t s =
       if n < LENGTH (linear_scan_hidden_state_sorted_moves s)
       then (M_success one,
             linear_scan_hidden_state_sorted_moves_fupd
               (K (LUPDATE t n (linear_scan_hidden_state_sorted_moves s))) s)
       else (M_failure Subscript,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[update_sorted_moves_def; ml_monadBase_Marray_update_def] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[ml_monadBase_Mupdate_eq; case_def "exc"];
    POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ml_monadBase_Mupdate_exn_eq; GE; case_def "exc"]]);;

let _ = cake_add_simps
  [colors_sub_eqn; update_colors_eqn; int_beg_sub_eqn; update_int_beg_eqn;
   int_end_sub_eqn; update_int_end_eqn; sorted_regs_sub_eqn; update_sorted_regs_eqn;
   sorted_moves_sub_eqn; update_sorted_moves_eqn];;

(* HOL4 line 2130: the ML list msimps (reg_allocProof's RAPROOFAUX_msimps) *)

(* HOL4 line 2132 *)
let lookup_default_id_def = cake_def
  `lookup_default_id (s:num spt) x = option_CASE (lookup x s) x (\x. x)`;;

(* HOL4 line 2136 *)
let find_reg_exchange_step_def = cake_def
  `find_reg_exchange_step colors r (exch,invexch) =
     let col1 = EL r colors in
     let fcol1 = r DIV 2 in
     let col2 = lookup_default_id invexch fcol1 in
     let fcol2 = lookup_default_id exch col1 in
     (insert col1 fcol1 (insert col2 fcol2 exch),
      insert fcol1 col1 (insert fcol2 col2 invexch))`;;

(* HOL4 line 2145 *)
let find_reg_exchange_FOLDL = prove
 (`!l (colors:num list) exch invexch sth.
     (!r. MEM r l ==> r < LENGTH (linear_scan_hidden_state_colors sth)) ==>
     find_reg_exchange l exch invexch sth =
       (M_success (FOLDL (\a b. find_reg_exchange_step (linear_scan_hidden_state_colors sth) b a)
                         (exch,invexch) l),
        sth)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[find_reg_exchange_def; FOLDL; MEM] THENL
   [REWRITE_TAC[st_ex_return_def]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[st_ex_bind_def; colors_sub_eqn; case_def "prod"; case_def "exc"] THEN
  REWRITE_TAC[find_reg_exchange_step_def; lookup_default_id_def; LET_DEF; LET_END_DEF] THEN
  FIRST_X_ASSUM(fun th -> W(fun (_,w) -> MATCH_MP_TAC th)) THEN ASM_MESON_TAC[]);;

(* HOL4 line 2155 *)
let lookup_default_id_insert = prove
 (`!s k1 k2 v.
     lookup_default_id (insert k2 v s) k1 =
       if k1 = k2 then v else lookup_default_id s k1`,
  REWRITE_TAC[lookup_default_id_def; lookup_insert] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[case_def "option"]);;

(* HOL4 line 2162: id *)
let linear_scanProof_id_def = cake_def
  `linear_scanProof_id (x:A) = x`;;

(* LSCANPAUX_lde_step: one step of find_reg_exchange on the two lookups *)
let LSCANPAUX_lde_step = prove
 (`!colors h exch1 invexch1 exch invexch.
     (exch,invexch) = find_reg_exchange_step colors h (exch1,invexch1) ==>
     (!c. lookup_default_id exch c =
          if c = EL h colors then h DIV 2
          else if c = lookup_default_id invexch1 (h DIV 2)
          then lookup_default_id exch1 (EL h colors)
          else lookup_default_id exch1 c) /\
     (!c. lookup_default_id invexch c =
          if c = h DIV 2 then EL h colors
          else if c = lookup_default_id exch1 (EL h colors)
          then lookup_default_id invexch1 (h DIV 2)
          else lookup_default_id invexch1 c)`,
  REWRITE_TAC[find_reg_exchange_step_def; LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[lookup_default_id_insert]);;

(* LSCANPAUX_phy_div2_inj: two physical registers with the same r DIV 2 *)
let LSCANPAUX_phy_div2_inj = prove
 (`!r h. is_phy_var r /\ is_phy_var h /\ r DIV 2 = h DIV 2 ==> r = h`,
  REWRITE_TAC[is_phy_var_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`r:num`; `2`] DIVISION) THEN MP_TAC(SPECL [`h:num`; `2`] DIVISION) THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(2 = 0)`] THEN ARITH_TAC);;

(* HOL4 line 2166 *)
let find_reg_exchange_FOLDR_correct = prove
 (`!l colors exch invexch k.
     ALL_DISTINCT (MAP (\r. EL r colors) l) /\
     (!r. MEM r l ==> is_phy_var r) /\
     (exch,invexch) = ITLIST (\a b. find_reg_exchange_step colors a b) l (LN,LN) ==>
     (lookup_default_id exch o lookup_default_id invexch = (\x. x) /\
      lookup_default_id invexch o lookup_default_id exch = (\x. x)) /\
     (!r. MEM r l ==> lookup_default_id exch (EL r colors) = r DIV 2) /\
     ((!r. MEM r l ==> (k <= EL r colors <=> k <= r DIV 2)) ==>
      (!c. linear_scanProof_id (k <= c <=> k <= lookup_default_id exch c))) /\
     ((!r. MEM r l ==> r DIV 2 < k) ==>
      (!c. k <= c /\ (!r. MEM r l ==> ~(c = EL r colors)) ==>
           k <= lookup_default_id exch c)) /\
     ((!r. MEM r l ==> k <= EL r colors /\ k <= r DIV 2) ==>
      (!c. c < k ==> lookup_default_id exch c = c))`,
  REWRITE_TAC[linear_scanProof_id_def; FUN_EQ_THM; o_THM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; MEM] THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[lookup_default_id_def; lookup_def; case_def "option"];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`colors:num list`; `exch:num spt`; `invexch:num spt`; `k:num`] THEN
  REWRITE_TAC[MAP; ALL_DISTINCT; MEM_MAP] THEN
  ABBREV_TAC `p = ITLIST (\a b. find_reg_exchange_step colors a b) t (LN,LN)` THEN
  MP_TAC(ISPEC `p:num spt#num spt` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `exch1:num spt` (X_CHOOSE_THEN `invexch1:num spt`
    SUBST_ALL_TAC)) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`colors:num list`; `exch1:num spt`; `invexch1:num spt`;
                                `k:num`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "inv1") (LABEL_TAC "inv2"))
    (CONJUNCTS_THEN2 (LABEL_TAC "p2") (CONJUNCTS_THEN2 (LABEL_TAC "p3")
    (CONJUNCTS_THEN2 (LABEL_TAC "p4") (LABEL_TAC "p5"))))) THEN
  MP_TAC(SPECL [`colors:num list`; `h:num`; `exch1:num spt`; `invexch1:num spt`;
                `exch:num spt`; `invexch:num spt`] LSCANPAUX_lde_step) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "e") (LABEL_TAC "i")) THEN
  REPEAT CONJ_TAC THENL
   [(* inverse 1 *)
    X_GEN_TAC `x:num` THEN REWRITE_TAC[ASSUME
      `!c. lookup_default_id exch c =
           (if c = EL h colors then h DIV 2
            else if c = lookup_default_id invexch1 (h DIV 2)
            then lookup_default_id exch1 (EL h colors)
            else lookup_default_id exch1 c)`] THEN
    REWRITE_TAC[ASSUME
      `!c. lookup_default_id invexch c =
           (if c = h DIV 2 then EL h colors
            else if c = lookup_default_id exch1 (EL h colors)
            then lookup_default_id invexch1 (h DIV 2)
            else lookup_default_id invexch1 c)`] THEN
    REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[];
    (* inverse 2 *)
    X_GEN_TAC `x:num` THEN REWRITE_TAC[ASSUME
      `!c. lookup_default_id exch c =
           (if c = EL h colors then h DIV 2
            else if c = lookup_default_id invexch1 (h DIV 2)
            then lookup_default_id exch1 (EL h colors)
            else lookup_default_id exch1 c)`] THEN
    REWRITE_TAC[ASSUME
      `!c. lookup_default_id invexch c =
           (if c = h DIV 2 then EL h colors
            else if c = lookup_default_id exch1 (EL h colors)
            then lookup_default_id invexch1 (h DIV 2)
            else lookup_default_id invexch1 c)`] THEN
    REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[];
    (* the colours of l *)
    X_GEN_TAC `r:num` THEN USE_THEN "e" (fun th -> REWRITE_TAC[th]) THEN
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[];
      SUBGOAL_THEN `~(EL r colors = EL h (colors:num list))` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
      COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      SUBGOAL_THEN `r DIV 2 = h DIV 2` ASSUME_TAC THENL
       [USE_THEN "p2" (MP_TAC o SPEC `r:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `r = h:num` (fun th -> ASM_MESON_TAC[th]) THEN
      MATCH_MP_TAC LSCANPAUX_phy_div2_inj THEN ASM_MESON_TAC[]];
    (* k <= c *)
    DISCH_TAC THEN X_GEN_TAC `c:num` THEN USE_THEN "e" (fun th -> REWRITE_TAC[th]) THEN
    REMOVE_THEN "p3" (MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(LABEL_TAC "ih3")] THEN
    SUBGOAL_THEN `k <= EL h colors <=> k <= h DIV 2` (LABEL_TAC "hk") THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> lhs(concl th) = `c:num`)) THEN
      USE_THEN "hk" ACCEPT_TAC;
      ALL_TAC] THEN
    COND_CASES_TAC THENL [ALL_TAC; USE_THEN "ih3" MATCH_ACCEPT_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> lhs(concl th) = `c:num`)) THEN
    USE_THEN "ih3" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    USE_THEN "inv1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "hk" (fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
    USE_THEN "ih3" MATCH_ACCEPT_TAC;
    (* k <= c and c not a colour of l *)
    DISCH_TAC THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    USE_THEN "e" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `k <= lookup_default_id exch1 c` ASSUME_TAC THENL
     [REMOVE_THEN "p4" (MP_TAC o check (is_imp o concl)) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(c = EL h (colors:num list))` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `h DIV 2 < k` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `k <= lookup_default_id exch1 c` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    (* c < k *)
    DISCH_TAC THEN X_GEN_TAC `c:num` THEN USE_THEN "e" (fun th -> REWRITE_TAC[th]) THEN
    REMOVE_THEN "p5" (MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
    REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[NOT_LE]]);;

(* HOL4 line 2283 *)
let find_reg_exchange_correct = prove
 (`!l sth k.
     ALL_DISTINCT (MAP (\r. EL r (linear_scan_hidden_state_colors sth)) l) /\
     (!r. MEM r l ==> is_phy_var r) /\
     (!r. MEM r l ==> r < LENGTH (linear_scan_hidden_state_colors sth)) ==>
     ?exch invexch.
       find_reg_exchange l LN LN sth = (M_success (exch,invexch),sth) /\
       (lookup_default_id exch o lookup_default_id invexch = (\x. x) /\
        lookup_default_id invexch o lookup_default_id exch = (\x. x)) /\
       (!r. MEM r l ==>
            lookup_default_id exch (EL r (linear_scan_hidden_state_colors sth)) = r DIV 2) /\
       ((!r. MEM r l ==> (k <= EL r (linear_scan_hidden_state_colors sth) <=> k <= r DIV 2))
        ==> (!c. linear_scanProof_id (k <= c <=> k <= lookup_default_id exch c))) /\
       ((!r. MEM r l ==> r DIV 2 < k) ==>
        (!c. k <= c /\ (!r. MEM r l ==> ~(c = EL r (linear_scan_hidden_state_colors sth)))
             ==> k <= lookup_default_id exch c)) /\
       ((!r. MEM r l ==> k <= EL r (linear_scan_hidden_state_colors sth) /\ k <= r DIV 2)
        ==> (!c. c < k ==> lookup_default_id exch c = c))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[find_reg_exchange_FOLDL] THEN
  MP_TAC(ISPEC `FOLDL (\a b. find_reg_exchange_step (linear_scan_hidden_state_colors sth) b a)
                  (LN,LN) l` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `exch:num spt` (X_CHOOSE_THEN `invexch:num spt` ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`exch:num spt`; `invexch:num spt`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`REVERSE (l:num list)`; `linear_scan_hidden_state_colors sth`;
                `exch:num spt`; `invexch:num spt`; `k:num`]
    find_reg_exchange_FOLDR_correct) THEN
  REWRITE_TAC[MEM_REVERSE; GSYM MAP_REVERSE; ALL_DISTINCT_REVERSE] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `FOLDL (\a b. find_reg_exchange_step (linear_scan_hidden_state_colors sth) b a)
                 (LN,LN) l = exch,invexch` THEN
  REWRITE_TAC[FOLDL_FOLDR_REVERSE] THEN BETA_TAC THEN DISCH_THEN(ACCEPT_TAC o SYM));;

(* the record theorems of linear_scan_hidden_state, for REWRITE_TAC *)
let LSCANPAUX_hs_record =
  let ri = record_info "linear_scan_hidden_state" in
  [ri.ri_accessors; ri.ri_fupds; ri.ri_accfupds; ri.ri_fupdfupds];;

let LSCANPAUX_st_record =
  let ri = record_info "linear_scan_state" in
  [ri.ri_accessors; ri.ri_fupds; ri.ri_accfupds; ri.ri_fupdfupds];;

(* HOL4 line 2313 *)
let MAP_colors_eq_lemma = prove
 (`!sth n f.
     n <= LENGTH (linear_scan_hidden_state_colors sth) ==>
     ?sthout.
       (M_success one,sthout) = MAP_colors f n sth /\
       LENGTH (linear_scan_hidden_state_colors sth) =
         LENGTH (linear_scan_hidden_state_colors sthout) /\
       linear_scan_hidden_state_int_beg sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout = linear_scan_hidden_state_int_end sth /\
       (!n'. n' < n ==>
             EL n' (linear_scan_hidden_state_colors sthout) =
             f (EL n' (linear_scan_hidden_state_colors sth))) /\
       (!n'. n <= n' ==>
             EL n' (linear_scan_hidden_state_colors sthout) =
             EL n' (linear_scan_hidden_state_colors sth))`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN INDUCT_TAC THENL
   [REWRITE_TAC[MAP_colors_def; st_ex_return_def; PAIR_EQ; LT] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n < LENGTH (linear_scan_hidden_state_colors sth)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `sth' = linear_scan_hidden_state_colors_fupd
                       (K (LUPDATE ((f:num->num) (EL n (linear_scan_hidden_state_colors sth))) n
                             (linear_scan_hidden_state_colors sth))) sth` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`sth':linear_scan_hidden_state`; `f:num->num`]) THEN
  EXPAND_TAC "sth'" THEN REWRITE_TAC(K_THM :: LENGTH_LUPDATE :: LSCANPAUX_hs_record) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sthout:linear_scan_hidden_state`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lt") (LABEL_TAC "ge"))))))) THEN
  EXISTS_TAC `sthout:linear_scan_hidden_state` THEN
  ASM_REWRITE_TAC[MAP_colors_def; st_ex_bind_def; st_ex_ignore_bind_def; colors_sub_eqn;
                  update_colors_eqn; case_def "prod"; case_def "exc"] THEN
  CONJ_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THENL
   [ASM_CASES_TAC `m:num = n` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "ge" (MP_TAC o SPEC `n:num`) THEN
      REWRITE_TAC[LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[EL_LUPDATE];
      USE_THEN "lt" (MP_TAC o SPEC `m:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[EL_LUPDATE]];
    USE_THEN "ge" (MP_TAC o SPEC `m:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `~(m:num = n)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_LUPDATE]]);;

(* HOL4 line 2352 *)
let MAP_colors_eq = prove
 (`!sth f.
     ?sthout.
       (M_success one,sthout) =
         MAP_colors f (LENGTH (linear_scan_hidden_state_colors sth)) sth /\
       (!n. n < LENGTH (linear_scan_hidden_state_colors sth) ==>
            EL n (linear_scan_hidden_state_colors sthout) =
            f (EL n (linear_scan_hidden_state_colors sth))) /\
       LENGTH (linear_scan_hidden_state_colors sth) =
         LENGTH (linear_scan_hidden_state_colors sthout) /\
       linear_scan_hidden_state_int_beg sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout = linear_scan_hidden_state_int_end sth`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`sth:linear_scan_hidden_state`;
                `LENGTH (linear_scan_hidden_state_colors sth)`; `f:num->num`]
    MAP_colors_eq_lemma) THEN
  REWRITE_TAC[LE_REFL] THEN MESON_TAC[]);;

(* HOL4 line 2364 *)
let apply_reg_exchange_correct = prove
 (`!l sth k.
     ALL_DISTINCT (MAP (\r. EL r (linear_scan_hidden_state_colors sth)) l) /\
     (!r. MEM r l ==> is_phy_var r) /\
     (!r. MEM r l ==> r < LENGTH (linear_scan_hidden_state_colors sth)) ==>
     ?sthout.
       (M_success one,sthout) = apply_reg_exchange l sth /\
       LENGTH (linear_scan_hidden_state_colors sthout) =
         LENGTH (linear_scan_hidden_state_colors sth) /\
       linear_scan_hidden_state_int_beg sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout = linear_scan_hidden_state_int_end sth /\
       (!r1 r2. r1 < LENGTH (linear_scan_hidden_state_colors sth) /\
                r2 < LENGTH (linear_scan_hidden_state_colors sth) ==>
                EL r1 (linear_scan_hidden_state_colors sthout) =
                EL r2 (linear_scan_hidden_state_colors sthout) ==>
                EL r1 (linear_scan_hidden_state_colors sth) =
                EL r2 (linear_scan_hidden_state_colors sth)) /\
       (!r. MEM r l ==> EL r (linear_scan_hidden_state_colors sthout) = r DIV 2) /\
       ((!r. MEM r l ==> (k <= EL r (linear_scan_hidden_state_colors sth) <=> k <= r DIV 2))
        ==> (!r. r < LENGTH (linear_scan_hidden_state_colors sth) ==>
                 (k <= EL r (linear_scan_hidden_state_colors sth) <=>
                  k <= EL r (linear_scan_hidden_state_colors sthout)))) /\
       ((!r. MEM r l ==> r DIV 2 < k) ==>
        (!r. r < LENGTH (linear_scan_hidden_state_colors sth) /\
             k <= EL r (linear_scan_hidden_state_colors sth) /\
             (!r'. MEM r' l ==>
                   ~(EL r (linear_scan_hidden_state_colors sth) =
                     EL r' (linear_scan_hidden_state_colors sth)))
             ==> k <= EL r (linear_scan_hidden_state_colors sthout))) /\
       ((!r. MEM r l ==> k <= EL r (linear_scan_hidden_state_colors sth) /\ k <= r DIV 2)
        ==> (!r. r < LENGTH (linear_scan_hidden_state_colors sth) /\
                 EL r (linear_scan_hidden_state_colors sth) < k
                 ==> EL r (linear_scan_hidden_state_colors sthout) =
                     EL r (linear_scan_hidden_state_colors sth)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:num list`; `sth:linear_scan_hidden_state`; `k:num`]
    find_reg_exchange_correct) THEN
  ASM_REWRITE_TAC[linear_scanProof_id_def; FUN_EQ_THM; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `exch:num spt` (X_CHOOSE_THEN `invexch:num spt`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "inv1")
      (LABEL_TAC "inv2")) (CONJUNCTS_THEN2 (LABEL_TAC "p2") (CONJUNCTS_THEN2 (LABEL_TAC "p3")
      (CONJUNCTS_THEN2 (LABEL_TAC "p4") (LABEL_TAC "p5")))))))) THEN
  MP_TAC(SPECL [`sth:linear_scan_hidden_state`; `lookup_default_id exch`] MAP_colors_eq) THEN
  DISCH_THEN(X_CHOOSE_THEN `sthout:linear_scan_hidden_state`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "el") STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `sthout:linear_scan_hidden_state` THEN
  ASM_REWRITE_TAC[apply_reg_exchange_def; st_ex_bind_def; colors_length_def;
                  ml_monadBase_Marray_length_def; case_def "prod"; case_def "exc"] THEN
  REWRITE_TAC[GSYM lookup_default_id_def; ETA_AX] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "el" (fun th -> ASM_SIMP_TAC[th]) THEN
    DISCH_THEN(MP_TAC o AP_TERM `lookup_default_id invexch`) THEN
    USE_THEN "inv2" (fun th -> REWRITE_TAC[th]);
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `r < LENGTH (linear_scan_hidden_state_colors sth)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `LENGTH (linear_scan_hidden_state_colors sth)`)) (concl th) &&
        can (find_term ((=) `MEM:num->num list->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "el" (fun th -> ASM_SIMP_TAC[th]) THEN
    USE_THEN "p2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `r < LENGTH (linear_scan_hidden_state_colors sth)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "el" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `r < LENGTH (linear_scan_hidden_state_colors sth)`)]) THEN
    USE_THEN "p3" (MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_ACCEPT_TAC];
    DISCH_TAC THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `r < LENGTH (linear_scan_hidden_state_colors sth)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "el" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `r < LENGTH (linear_scan_hidden_state_colors sth)`)]) THEN
    USE_THEN "p4" (MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `r < LENGTH (linear_scan_hidden_state_colors sth)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "el" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `r < LENGTH (linear_scan_hidden_state_colors sth)`)]) THEN
    USE_THEN "p5" (MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 2404 *)
let less_FST_def = cake_def
  `less_FST (x:int#num) (y:int#num) <=> FST x <= FST y`;;

(* HOL4 line 2408 *)
let transitive_less_FST = prove
 (`transitive less_FST`,
  REWRITE_TAC[transitive_DEF; less_FST_def] THEN INT_ARITH_TAC);;

(* HOL4 line 2415 *)
let good_linear_scan_state_def = cake_def
  `good_linear_scan_state st sth l (pos:int) forced mincol <=>
     LENGTH (linear_scan_hidden_state_int_beg sth) =
       LENGTH (linear_scan_hidden_state_colors sth) /\
     LENGTH (linear_scan_hidden_state_int_end sth) =
       LENGTH (linear_scan_hidden_state_colors sth) /\
     ALL_DISTINCT (APPEND (linear_scan_state_colorpool st)
                     (MAP (\er. match er with
                                  (e,r) -> EL r (linear_scan_hidden_state_colors sth))
                          (linear_scan_state_active st))) /\
     ALL (\r. r < LENGTH (linear_scan_hidden_state_colors sth)) l /\
     ALL (\r. EL r (linear_scan_hidden_state_colors sth) < linear_scan_state_stacknum st) l /\
     domain (linear_scan_state_phyregs st) =
       {EL r (linear_scan_hidden_state_colors sth) | r |
          MEM r l /\ is_phy_var r /\
          EL r (linear_scan_hidden_state_colors sth) < linear_scan_state_colormax st} /\
     ALL_DISTINCT (MAP (\r. EL r (linear_scan_hidden_state_colors sth)) (FILTER is_phy_var l)) /\
     ALL (\c. c < linear_scan_state_colornum st) (linear_scan_state_colorpool st) /\
     ALL (\er. match er with
                 (e,r) -> EL r (linear_scan_hidden_state_colors sth) <
                          linear_scan_state_colornum st)
         (linear_scan_state_active st) /\
     linear_scan_state_colornum st <= linear_scan_state_colormax st /\
     linear_scan_state_colormax st <= linear_scan_state_stacknum st /\
     ALL (\r. EL r (linear_scan_hidden_state_colors sth) < linear_scan_state_colormax st ==>
              EL r (linear_scan_hidden_state_colors sth) < linear_scan_state_colornum st) l /\
     ALL (\r. EL r (linear_scan_hidden_state_int_beg sth) <= pos) l /\
     ALL (\r. pos <= EL r (linear_scan_hidden_state_int_end sth) /\
              EL r (linear_scan_hidden_state_colors sth) < linear_scan_state_colormax st ==>
              MEM (EL r (linear_scan_hidden_state_int_end sth),r)
                  (linear_scan_state_active st)) l /\
     ALL (\r. MEM (EL r (linear_scan_hidden_state_int_end sth),r)
                  (linear_scan_state_active st) ==>
              pos <= &1 + EL r (linear_scan_hidden_state_int_end sth)) l /\
     (!r1 r2. MEM r1 l /\ MEM r2 l /\
              interval_intersect (EL r1 (linear_scan_hidden_state_int_beg sth),
                                  EL r1 (linear_scan_hidden_state_int_end sth))
                                 (EL r2 (linear_scan_hidden_state_int_beg sth),
                                  EL r2 (linear_scan_hidden_state_int_end sth)) /\
              EL r1 (linear_scan_hidden_state_colors sth) =
              EL r2 (linear_scan_hidden_state_colors sth) ==> r1 = r2) /\
     SORTED less_FST (linear_scan_state_active st) /\
     ALL (\er. match er with
                 (e,r) -> e = EL r (linear_scan_hidden_state_int_end sth))
         (linear_scan_state_active st) /\
     ALL (\er. match er with (e,r) -> MEM r l) (linear_scan_state_active st) /\
     ALL (\r12. match r12 with
                  (r1,r2) -> MEM r1 l /\ MEM r2 l /\
                             EL r1 (linear_scan_hidden_state_colors sth) =
                             EL r2 (linear_scan_hidden_state_colors sth) ==> r1 = r2)
         forced /\
     mincol <= linear_scan_state_colornum st /\
     ALL (\c. mincol <= c)
         (APPEND (linear_scan_state_colorpool st)
                 (MAP (\r. EL r (linear_scan_hidden_state_colors sth)) l))`;;

(* HOL4 line 2444: the ML value good_linear_scan_state_def' (the definition *)
(* with the injectivity conjuncts f x = f y ==> x = y as iffs) is not a     *)
(* theorem of the script; the proofs below use the definition               *)

(* LSCANPAUX_LABEL_CONJS p th: the conjuncts of th as assumptions p1, p2, ... *)
let LSCANPAUX_LABEL_CONJS (p:string) : thm_tactic = fun th ->
  let ths = CONJUNCTS th in
  EVERY (map2 (fun i t -> LABEL_TAC (p ^ string_of_int i) t) (1--length ths) ths);;

(* LSCANPAUX_GLS_TAC: unfold a good_linear_scan_state goal into its 22      *)
(* conjuncts, record fields of updated states reduced                       *)
let LSCANPAUX_GLS_TAC : tactic =
  REWRITE_TAC(good_linear_scan_state_def :: K_THM :: LSCANPAUX_st_record) THEN
  REPEAT CONJ_TAC;;

(* HOL4 line 2453 *)
let remove_inactive_intervals_invariants = prove
 (`!beg st sth l pos forced mincol.
     good_linear_scan_state st sth l pos forced mincol /\
     pos <= beg ==>
     ?stout. (M_success stout,sth) = remove_inactive_intervals beg st sth /\
             good_linear_scan_state stout sth l beg forced mincol /\
             linear_scan_state_colormax stout = linear_scan_state_colormax st`,
  MATCH_MP_TAC remove_inactive_intervals_ind THEN
  MAP_EVERY X_GEN_TAC [`beg:int`; `st:linear_scan_state`] THEN DISCH_THEN(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`sth:linear_scan_hidden_state`; `l:num list`; `pos:int`;
    `forced:(num#num)list`; `mincol:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gls") ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[remove_inactive_intervals_def] THEN
  CASES_ON `linear_scan_state_active st` THENL
   [ASM_REWRITE_TAC[case_def "list"; st_ex_return_def; PAIR_EQ] THEN
    EXISTS_TAC `st:linear_scan_state` THEN REWRITE_TAC[] THEN
    USE_THEN "gls" MP_TAC THEN REWRITE_TAC[good_linear_scan_state_def] THEN
    ASM_REWRITE_TAC[MEM; GSYM ALL_MEM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[INT_LE_TRANS];
    ALL_TAC] THEN
  MP_TAC(ISPEC `a0:int#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:int` (X_CHOOSE_THEN `r:num` SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(LABEL_TAC "act" o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `linear_scan_state_active st`)) THEN
  REWRITE_TAC[case_def "list"; pair_CASE] THEN
  USE_THEN "gls" (LSCANPAUX_LABEL_CONJS "h" o REWRITE_RULE[good_linear_scan_state_def]) THEN
  SUBGOAL_THEN `MEM r l /\ e = EL r (linear_scan_hidden_state_int_end sth)` STRIP_ASSUME_TAC
  THENL
   [USE_THEN "h18" MP_TAC THEN USE_THEN "h19" MP_TAC THEN
    USE_THEN "act" (fun th -> REWRITE_TAC[th; ALL; pair_CASE]) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(pos:int) <= &1 + e` ASSUME_TAC THENL
   [USE_THEN "h15" (MP_TAC o SPEC `r:num` o REWRITE_RULE[GSYM ALL_MEM]) THEN
    USE_THEN "act" (fun th -> REWRITE_TAC[th; MEM]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e' (r':num). MEM (e',r') (a1:(int#num)list) ==> e <= e'` ASSUME_TAC THENL
   [USE_THEN "h17" MP_TAC THEN USE_THEN "act" (fun th -> REWRITE_TAC[th]) THEN
    SIMP_TAC[SORTED_EQ; transitive_less_FST] THEN
    REWRITE_TAC[less_FST_def; FORALL_PAIR_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [(* e < beg: the head interval is removed *)
    SUBGOAL_THEN `r < LENGTH (linear_scan_hidden_state_colors sth)` ASSUME_TAC THENL
     [USE_THEN "h4" (MP_TAC o SPEC `r:num` o REWRITE_RULE[GSYM ALL_MEM]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[st_ex_bind_def; colors_sub_eqn; case_def "prod"; case_def "exc";
                    LET_DEF; LET_END_DEF] THEN
    REMOVE_THEN "ih" (MP_TAC o SPECL [`r:num`; `e:int`; `a1:(int#num)list`;
      `EL r (linear_scan_hidden_state_colors sth)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`sth:linear_scan_hidden_state`; `l:num list`; `(e:int) + &1`;
      `forced:(num#num)list`; `mincol:num`]) THEN
    REWRITE_TAC(K_THM :: LSCANPAUX_st_record) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    CONJ_TAC THENL [ALL_TAC; LSCANPAUX_INT_ARITH_TAC] THEN
    LSCANPAUX_GLS_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [(* colorpool and active colours distinct *)
      USE_THEN "h3" MP_TAC THEN USE_THEN "act" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[MAP; pair_CASE; ALL_DISTINCT_APPEND; ALL_DISTINCT; MEM_APPEND; MEM] THEN
      MESON_TAC[];
      (* colorpool below colornum *)
      USE_THEN "h8" MP_TAC THEN USE_THEN "h9" MP_TAC THEN
      USE_THEN "act" (fun th -> REWRITE_TAC[th; ALL; pair_CASE]) THEN MESON_TAC[];
      (* active colours below colornum *)
      USE_THEN "h9" MP_TAC THEN USE_THEN "act" (fun th -> REWRITE_TAC[th; ALL]) THEN
      MESON_TAC[];
      (* int_beg *)
      REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
      USE_THEN "h13" (MP_TAC o SPEC `x:num` o REWRITE_RULE[GSYM ALL_MEM]) THEN
      ASM_REWRITE_TAC[] THEN LSCANPAUX_INT_ARITH_TAC;
      (* pos <= int_end ==> active *)
      REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN STRIP_TAC THEN
      USE_THEN "h14" (MP_TAC o SPEC `x:num` o REWRITE_RULE[GSYM ALL_MEM]) THEN
      USE_THEN "act" (fun th -> REWRITE_TAC[th; MEM; PAIR_EQ]) THEN ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [LSCANPAUX_INT_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(e:int) + &1 <= EL x (linear_scan_hidden_state_int_end sth)` THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      (* active ==> int_end bound *)
      REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `x:num` THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `e <= EL x (linear_scan_hidden_state_int_end sth)` MP_TAC THENL
       [ASM_MESON_TAC[]; INT_ARITH_TAC];
      (* sorted *)
      USE_THEN "h17" MP_TAC THEN USE_THEN "act" (fun th -> REWRITE_TAC[th]) THEN
      MESON_TAC[SORTED_TL];
      (* active ends *)
      USE_THEN "h18" MP_TAC THEN USE_THEN "act" (fun th -> REWRITE_TAC[th; ALL]) THEN
      MESON_TAC[];
      (* active registers in l *)
      USE_THEN "h19" MP_TAC THEN USE_THEN "act" (fun th -> REWRITE_TAC[th; ALL]) THEN
      MESON_TAC[];
      (* mincol *)
      USE_THEN "h22" MP_TAC THEN
      REWRITE_TAC[ALL_APPEND; ALL; GSYM ALL_MEM; MEM_MAP] THEN ASM_MESON_TAC[]];
    (* ~(e < beg): nothing is removed *)
    REWRITE_TAC[st_ex_return_def; PAIR_EQ] THEN EXISTS_TAC `st:linear_scan_state` THEN
    REWRITE_TAC[] THEN LSCANPAUX_GLS_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `x:num` THEN DISCH_TAC THENL
     [USE_THEN "h13" (MP_TAC o SPEC `x:num` o REWRITE_RULE[GSYM ALL_MEM]) THEN
      ASM_REWRITE_TAC[] THEN LSCANPAUX_INT_ARITH_TAC;
      STRIP_TAC THEN
      USE_THEN "h14" (MP_TAC o SPEC `x:num` o REWRITE_RULE[GSYM ALL_MEM]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      LSCANPAUX_INT_ARITH_TAC;
      USE_THEN "act" (fun th -> REWRITE_TAC[th; MEM; PAIR_EQ]) THEN STRIP_TAC THENL
       [ASM_REWRITE_TAC[] THEN LSCANPAUX_INT_ARITH_TAC;
        SUBGOAL_THEN `e <= EL x (linear_scan_hidden_state_int_end sth)` MP_TAC THENL
         [ASM_MESON_TAC[]; LSCANPAUX_INT_ARITH_TAC]]]]);;

(* HOL4 line 2561 *)
let add_active_interval_output = prove
 (`!e r lin (x:A) lout.
     SORTED less_FST lin /\
     lout = add_active_interval (e,r) lin ==>
     SORTED less_FST lout /\
     ?l1 l2. lin = APPEND l1 l2 /\ lout = APPEND l1 (CONS (e,r) l2)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[add_active_interval_def] THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[SORTED_SING] THEN
    MAP_EVERY EXISTS_TAC [`[]:(int#num)list`; `[]:(int#num)list`] THEN REWRITE_TAC[APPEND];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  SUBGOAL_THEN `SORTED less_FST t /\ (!y. MEM y t ==> FST (h:int#num) <= FST y)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `SORTED less_FST (CONS (h:int#num) t)` THEN
    SIMP_TAC[SORTED_EQ; transitive_less_FST; less_FST_def];
    ALL_TAC] THEN
  REWRITE_TAC[FST] THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[SORTED_EQ; transitive_less_FST; less_FST_def; MEM; FST] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[INT_LE_TRANS];
      MAP_EVERY EXISTS_TAC [`[]:(int#num)list`; `CONS (h:int#num) t`] THEN
      REWRITE_TAC[APPEND]];
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `add_active_interval (e,r) t`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `l1:(int#num)list`
      (X_CHOOSE_THEN `l2:(int#num)list` STRIP_ASSUME_TAC))) THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[SORTED_EQ; transitive_less_FST; less_FST_def] THEN
      UNDISCH_TAC `~(e <= FST (h:int#num))` THEN ASM_REWRITE_TAC[MEM_APPEND; MEM] THEN
      REWRITE_TAC[INT_NOT_LE] THEN STRIP_TAC THEN X_GEN_TAC `y:int#num` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[FST] THENL
       [ASM_MESON_TAC[MEM_APPEND];
        ASM_INT_ARITH_TAC;
        ASM_MESON_TAC[MEM_APPEND]];
      MAP_EVERY EXISTS_TAC [`CONS (h:int#num) l1`; `l2:(int#num)list`] THEN
      ASM_REWRITE_TAC[APPEND]]]);;

(* HOL4 line 2594 *)
let find_color_in_list_output = prove
 (`!forbidden col l rest.
     find_color_in_list l forbidden = SOME (col,rest) ==>
     MEM col l /\ ~(col IN domain forbidden) /\
     ?l1 l2. rest = APPEND l1 l2 /\ l = APPEND l1 (CONS col l2)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[find_color_in_list_def; option_DISTINCT] THEN GEN_TAC THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[option_INJ; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) THEN
    ASM_REWRITE_TAC[MEM; GSYM lookup_NONE_domain] THEN
    MAP_EVERY EXISTS_TAC [`[]:num list`; `t:num list`] THEN REWRITE_TAC[APPEND];
    ALL_TAC] THEN
  REWRITE_TAC[option_case_eq; pair_case_eq; option_DISTINCT; option_INJ; PAIR_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num#num list` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `x:num` (X_CHOOSE_THEN `y:num list` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:num list` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `l1:num list` (X_CHOOSE_THEN `l2:num list` STRIP_ASSUME_TAC)))) THEN
  ASM_REWRITE_TAC[MEM] THEN
  MAP_EVERY EXISTS_TAC [`CONS (h:num) l1`; `l2:num list`] THEN
  REWRITE_TAC[APPEND] THEN ASM_MESON_TAC[]);;

(* LSCANPAUX_ALL_DISTINCT_CONS_FRESH: a fresh element at the front *)
let LSCANPAUX_ALL_DISTINCT_CONS_FRESH = prove
 (`!(x:A) l1 l2. ALL_DISTINCT (APPEND l1 l2) /\ ~MEM x l1 /\ ~MEM x l2 ==>
                 ALL_DISTINCT (APPEND (CONS x l1) l2)`,
  REWRITE_TAC[ALL_DISTINCT_APPEND; ALL_DISTINCT; MEM] THEN MESON_TAC[]);;

(* HOL4 line 2623 *)
let find_color_in_colornum_invariants = prove
 (`!stout col st forbidden sth l pos forced mincol.
     good_linear_scan_state st sth l pos forced mincol /\
     domain forbidden SUBSET {EL r (linear_scan_hidden_state_colors sth) | r | MEM r l} /\
     find_color_in_colornum st forbidden = (stout,SOME col) ==>
     good_linear_scan_state (linear_scan_state_colorpool_fupd (\l. CONS col l) stout)
       sth l pos forced mincol /\
     linear_scan_state_colornum st <= col /\ col < linear_scan_state_colornum stout /\
     linear_scan_state_colornum st <= linear_scan_state_colornum stout /\
     ~(col IN domain forbidden) /\
     st = linear_scan_state_colorpool_fupd (K (linear_scan_state_colorpool st))
            (linear_scan_state_colornum_fupd (K (linear_scan_state_colornum st)) stout)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[find_color_in_colornum_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[PAIR_EQ; option_DISTINCT; option_INJ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gls") (CONJUNCTS_THEN2 (LABEL_TAC "forb")
    (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)))) THEN
  USE_THEN "gls" (LSCANPAUX_LABEL_CONJS "h" o REWRITE_RULE[good_linear_scan_state_def]) THEN
  REWRITE_TAC(K_THM :: LSCANPAUX_st_record) THEN
  SUBGOAL_THEN `~(linear_scan_state_colornum st IN domain (forbidden:1 spt))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    USE_THEN "forb" (MP_TAC o SPEC `linear_scan_state_colornum st` o REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "h12" (MP_TAC o SPEC `x:num` o REWRITE_RULE[GSYM ALL_MEM]) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC
      `~(linear_scan_state_colormax st <= linear_scan_state_colornum st)` THEN
    UNDISCH_TAC
      `linear_scan_state_colornum st = EL x (linear_scan_hidden_state_colors sth)` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `n <= 1 + n /\ n < 1 + n`; LE_REFL] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[linear_scan_state_component_equality] THEN
    REWRITE_TAC(K_THM :: o_THM :: LSCANPAUX_st_record)] THEN
  LSCANPAUX_GLS_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [(* colorpool and active colours distinct *)
    MATCH_MP_TAC LSCANPAUX_ALL_DISTINCT_CONS_FRESH THEN
    USE_THEN "h3" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      USE_THEN "h8" (MP_TAC o SPEC `linear_scan_state_colornum st` o
                     REWRITE_RULE[GSYM ALL_MEM]) THEN
      ASM_REWRITE_TAC[LT_REFL];
      REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; pair_CASE] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:int` (X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC)) THEN
      USE_THEN "h9" (MP_TAC o SPEC `(e:int,r:num)` o REWRITE_RULE[GSYM ALL_MEM]) THEN
      ASM_REWRITE_TAC[pair_CASE; LT_REFL]];
    (* colorpool below colornum *)
    USE_THEN "h8" MP_TAC THEN REWRITE_TAC[ALL; GSYM ALL_MEM] THEN
    MESON_TAC[ARITH_RULE `n < 1 + n`; ARITH_RULE `m < n ==> m < 1 + n`];
    (* active below colornum *)
    USE_THEN "h9" MP_TAC THEN REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE] THEN
    MESON_TAC[ARITH_RULE `m < n ==> m < 1 + n`];
    (* colornum below colormax *)
    UNDISCH_TAC `~(linear_scan_state_colormax st <= linear_scan_state_colornum st)` THEN
    ARITH_TAC;
    (* colours below colormax are below colornum *)
    USE_THEN "h12" MP_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    MESON_TAC[ARITH_RULE `m < n ==> m < 1 + n`];
    (* mincol <= colornum *)
    USE_THEN "h21" MP_TAC THEN ARITH_TAC;
    (* mincol below all colours *)
    USE_THEN "h22" MP_TAC THEN USE_THEN "h21" MP_TAC THEN
    REWRITE_TAC[ALL_APPEND; ALL] THEN SIMP_TAC[]]);;

(* HOL4 line 2660 *)
let find_color_invariants = prove
 (`!st forbidden stout col sth l pos forced mincol.
     good_linear_scan_state st sth l pos forced mincol /\
     domain forbidden SUBSET {EL r (linear_scan_hidden_state_colors sth) | r | MEM r l} /\
     find_color st forbidden = (stout,SOME col) ==>
     good_linear_scan_state (linear_scan_state_colorpool_fupd (\l. CONS col l) stout)
       sth l pos forced mincol /\
     col < linear_scan_state_colornum stout /\
     ~(col IN domain forbidden) /\
     st = linear_scan_state_colorpool_fupd (K (linear_scan_state_colorpool st))
            (linear_scan_state_colornum_fupd (K (linear_scan_state_colornum st)) stout)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[find_color_def] THEN
  CASES_ON `find_color_in_list (linear_scan_state_colorpool st) forbidden` THEN
  REWRITE_TAC[case_def "option"] THENL
   [STRIP_TAC THEN
    MP_TAC(SPECL [`stout:linear_scan_state`; `col:num`; `st:linear_scan_state`;
      `forbidden:1 spt`; `sth:linear_scan_hidden_state`; `l:num list`; `pos:int`;
      `forced:(num#num)list`; `mincol:num`] find_color_in_colornum_invariants) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC) THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `a:num#num list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `col':num` (X_CHOOSE_THEN `rest:num list` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[pair_CASE; PAIR_EQ; option_INJ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gls") (CONJUNCTS_THEN2 (LABEL_TAC "forb")
    (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (SUBST_ALL_TAC o SYM)))) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP find_color_in_list_output) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "mem") (CONJUNCTS_THEN2 (LABEL_TAC "notin")
    (X_CHOOSE_THEN `l1:num list` (X_CHOOSE_THEN `l2:num list`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC (LABEL_TAC "cp")))))) THEN
  USE_THEN "gls" (LSCANPAUX_LABEL_CONJS "h" o REWRITE_RULE[good_linear_scan_state_def]) THEN
  REWRITE_TAC(K_THM :: o_THM :: LSCANPAUX_st_record) THEN
  USE_THEN "notin" (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    CONJ_TAC THENL
     [USE_THEN "h8" MP_TAC THEN
      USE_THEN "cp" (fun th -> REWRITE_TAC[th; ALL_APPEND; ALL]) THEN SIMP_TAC[];
      REWRITE_TAC[linear_scan_state_component_equality] THEN
      REWRITE_TAC(K_THM :: o_THM :: LSCANPAUX_st_record)]] THEN
  REWRITE_TAC(o_THM :: good_linear_scan_state_def :: K_THM :: LSCANPAUX_st_record) THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [(* distinct *)
    USE_THEN "h3" MP_TAC THEN USE_THEN "cp" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC ALL_DISTINCT_PERM THEN
    REWRITE_TAC[PERM_APPEND_IFF] THEN ONCE_REWRITE_TAC[PERM_SYM] THEN
    REWRITE_TAC[PERM_CONS_EQ_APPEND] THEN
    MAP_EVERY EXISTS_TAC [`l1:num list`; `l2:num list`] THEN REWRITE_TAC[PERM_REFL];
    (* colorpool below colornum *)
    USE_THEN "h8" MP_TAC THEN
    USE_THEN "cp" (fun th -> REWRITE_TAC[th; ALL_APPEND; ALL]) THEN SIMP_TAC[];
    (* mincol *)
    USE_THEN "h22" MP_TAC THEN
    USE_THEN "cp" (fun th -> REWRITE_TAC[th; ALL_APPEND; ALL]) THEN SIMP_TAC[]]);;

(* HOL4 line 2697 *)
let update_color_active_colors_same = prove
 (CASE_TERM
  `!(e:A) reg (active:(A#num)list) (regcol:B) colors.
     MAP (\er. match er with (e,r) -> EL r (LUPDATE regcol reg colors))
         (FILTER (\er. match er with (e,r) -> ~(r = reg)) active) =
     MAP (\er. match er with (e,r) -> EL r colors)
         (FILTER (\er. match er with (e,r) -> ~(r = reg)) active)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; MAP] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `h:A#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` (X_CHOOSE_THEN `r:num` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[pair_CASE] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[MAP; pair_CASE; EL_LUPDATE; CONS_11]);;

(* HOL4 line 2708 *)
let forced_update_stack_color_lemma = prove
 (`!(colors:num list) (stacknum:num) l r2 r1.
     ALL (\r. EL r colors < stacknum) l /\
     MEM r2 l /\
     r1 < LENGTH colors /\
     EL r1 (LUPDATE stacknum r1 colors) = EL r2 (LUPDATE stacknum r1 colors) ==>
     r1 = r2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN STRIP_TAC THEN
  ASM_CASES_TAC `r2:num = r1` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r2:num`) THEN
  UNDISCH_TAC `EL r1 (LUPDATE stacknum r1 colors) =
               EL r2 (LUPDATE (stacknum:num) r1 colors)` THEN
  ASM_REWRITE_TAC[EL_LUPDATE] THEN ARITH_TAC);;

(* HOL4 line 2727 (HOL4 comment: this should be part of the standard        *)
(* library, but I could not find it) *)
let IS_SPARSE_SUBLIST_def = cake_def
  `(IS_SPARSE_SUBLIST [] (l2:A list) <=> T) /\
   (IS_SPARSE_SUBLIST (CONS x xs) [] <=> F) /\
   (IS_SPARSE_SUBLIST (CONS x xs) (CONS y ys) <=>
      (x = y /\ IS_SPARSE_SUBLIST xs ys) \/ IS_SPARSE_SUBLIST (CONS x xs) ys)`;;

(* HOL4 line 2738 *)
let FILTER_IS_SPARSE_SUBLIST = prove
 (`!(P:A->bool) l. IS_SPARSE_SUBLIST (FILTER P l) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; IS_SPARSE_SUBLIST_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_SPARSE_SUBLIST_def] THEN
  UNDISCH_TAC `IS_SPARSE_SUBLIST (FILTER (P:A->bool) t) t` THEN
  SPEC_TAC(`FILTER (P:A->bool) t`, `k:A list`) THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `k:A list` list_CASES) THEN
  REWRITE_TAC[IS_SPARSE_SUBLIST_def] THEN SIMP_TAC[]);;

(* HOL4 line 2747 *)
let MEM_SPARSE_SUBLIST = prove
 (`!l1 l2 (x:A). IS_SPARSE_SUBLIST l1 l2 /\ MEM x l1 ==> MEM x l2`,
  REWRITE_TAC[IMP_CONJ] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l1:A list` list_CASES) THEN
  REWRITE_TAC[IS_SPARSE_SUBLIST_def; MEM] THEN ASM_MESON_TAC[MEM]);;

(* HOL4 line 2757 *)
let IS_SPARSE_SUBLIST_APPEND_LEFT = prove
 (`!l1 l2 (l:A list).
     IS_SPARSE_SUBLIST l1 l2 ==> IS_SPARSE_SUBLIST (APPEND l l1) (APPEND l l2)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[APPEND; IS_SPARSE_SUBLIST_def]);;

(* LSCANPAUX_ISS_CONS_RIGHT: a sparse sublist of ys is one of y::ys *)
let LSCANPAUX_ISS_CONS_RIGHT = prove
 (`!l1 (y:A) l2. IS_SPARSE_SUBLIST l1 l2 ==> IS_SPARSE_SUBLIST l1 (CONS y l2)`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `l1:A list` list_CASES) THEN
  SIMP_TAC[IS_SPARSE_SUBLIST_def]);;

(* LSCANPAUX_ISS_REFL *)
let LSCANPAUX_ISS_REFL = prove
 (`!l:A list. IS_SPARSE_SUBLIST l l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[IS_SPARSE_SUBLIST_def]);;

(* LSCANPAUX_ISS_APPEND_SUFFIX: l is a sparse sublist of m ++ l *)
let LSCANPAUX_ISS_APPEND_SUFFIX = prove
 (`!m (l:A list). IS_SPARSE_SUBLIST l (APPEND m l)`,
  LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[APPEND; LSCANPAUX_ISS_REFL; LSCANPAUX_ISS_CONS_RIGHT]);;

(* HOL4 line 2764 *)
let IS_SPARSE_SUBLIST_APPEND_RIGHT = prove
 (`!l1 l2 (l:A list).
     IS_SPARSE_SUBLIST l1 l2 ==> IS_SPARSE_SUBLIST (APPEND l1 l) (APPEND l2 l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; LSCANPAUX_ISS_APPEND_SUFFIX] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; IS_SPARSE_SUBLIST_def] THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

(* HOL4 line 2775 *)
let MAP_IS_SPARSE_SUBLIST = prove
 (`!(f:A->B) l1 l2.
     IS_SPARSE_SUBLIST l1 l2 ==> IS_SPARSE_SUBLIST (MAP f l1) (MAP f l2)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l1:A list` list_CASES) THEN
  REWRITE_TAC[IS_SPARSE_SUBLIST_def; MAP] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[GSYM MAP]);;

(* HOL4 line 2784 *)
let ALL_DISTINCT_IS_SPARSE_SUBLIST = prove
 (`!l1 (l2:A list). ALL_DISTINCT l2 /\ IS_SPARSE_SUBLIST l1 l2 ==> ALL_DISTINCT l1`,
  REWRITE_TAC[IMP_CONJ] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `l1:A list` list_CASES) THEN
  REWRITE_TAC[IS_SPARSE_SUBLIST_def; ALL_DISTINCT] THEN
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[MEM_SPARSE_SUBLIST];
    ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `CONS (h':A) t'`) THEN
    ASM_REWRITE_TAC[ALL_DISTINCT] THEN SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `CONS (h':A) t'`) THEN
    ASM_REWRITE_TAC[ALL_DISTINCT] THEN SIMP_TAC[]]);;

(* LSCANPAUX_PAIR_WITNESS_TAC: for a goal ?a b. (M_success a,b) = (M_success x,y) /\ ..., *)
(* the witnesses x and y read off the goal                                 *)
let LSCANPAUX_PAIR_WITNESS_TAC : tactic = fun (asl,w as g) ->
  let _,bd = strip_exists w in
  let eq = if is_conj bd then fst(dest_conj bd) else bd in
  let x,y = dest_pair(rand eq) in
  (EXISTS_TAC (rand x) THEN EXISTS_TAC y) g;;

(* LSCANPAUX_GSPEC_CONG: congruence for set comprehensions over num *)
let LSCANPAUX_GSPEC_CONG = prove
 (`!(f:num->num) g P Q. (!r. P r <=> Q r) /\ (!r. P r ==> f r = g r) ==>
     {f r | r | P r} = {g r | r | Q r}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]);;

(* HOL4 line 2803 *)
let spill_register_FILTER_invariants_hidden = prove
 (CASE_TERM
  `!st sth l pos forced reg mincol.
     linear_scanProof_id (~is_phy_var reg \/ ~MEM reg l) /\
     good_linear_scan_state st sth l pos forced mincol /\
     reg < LENGTH (linear_scan_hidden_state_colors sth) /\
     EL reg (linear_scan_hidden_state_int_beg sth) <= pos ==>
     ?stout sthout.
       (M_success stout,sthout) =
         spill_register
           (linear_scan_state_active_fupd
              (K (FILTER (\er. match er with (e,r) -> ~(r = reg))
                         (linear_scan_state_active st))) st) reg sth /\
       good_linear_scan_state stout sthout (CONS reg l) pos forced mincol /\
       LENGTH (linear_scan_hidden_state_colors sthout) =
         LENGTH (linear_scan_hidden_state_colors sth) /\
       (!r. ~(r = reg) ==>
            EL r (linear_scan_hidden_state_colors sth) =
            EL r (linear_scan_hidden_state_colors sthout)) /\
       linear_scan_state_colormax stout = linear_scan_state_colormax st /\
       linear_scan_hidden_state_int_beg sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout = linear_scan_hidden_state_int_end sth /\
       linear_scan_state_colormax st <= EL reg (linear_scan_hidden_state_colors sthout)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "id") (CONJUNCTS_THEN2 (LABEL_TAC "gls")
    (CONJUNCTS_THEN2 (LABEL_TAC "reglt") (LABEL_TAC "regbeg")))) THEN
  SUBGOAL_THEN `!r. MEM r l /\ is_phy_var r ==> ~(r = reg)` (LABEL_TAC "phy") THENL
   [USE_THEN "id" MP_TAC THEN REWRITE_TAC[linear_scanProof_id_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC(spill_register_def :: update_colors_eqn :: RAPROOFAUX_msimps) THEN
  REWRITE_TAC(K_THM :: LSCANPAUX_st_record) THEN
  USE_THEN "reglt" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
  LSCANPAUX_PAIR_WITNESS_TAC THEN
  REWRITE_TAC(K_THM :: LENGTH_LUPDATE :: LSCANPAUX_st_record @ LSCANPAUX_hs_record) THEN
  USE_THEN "gls" (LSCANPAUX_LABEL_CONJS "h" o REWRITE_RULE[good_linear_scan_state_def]) THEN
  SUBGOAL_THEN `!r. MEM r l ==> EL r (linear_scan_hidden_state_colors sth) <
                                linear_scan_state_stacknum st` (LABEL_TAC "lts") THENL
   [USE_THEN "h5" (ACCEPT_TAC o REWRITE_RULE[GSYM ALL_MEM]); ALL_TAC] THEN
  SUBGOAL_THEN `~(linear_scan_state_stacknum st < linear_scan_state_colormax st)`
    (LABEL_TAC "nSM") THENL [USE_THEN "h11" MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mincol <= linear_scan_state_stacknum st` (LABEL_TAC "mS") THENL
   [USE_THEN "h21" MP_TAC THEN USE_THEN "h10" MP_TAC THEN USE_THEN "h11" MP_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN
  let ELC_TAC = REWRITE_TAC[EL_LUPDATE] THEN USE_THEN "reglt" (fun th -> REWRITE_TAC[th]) in
  let LTS_TAC = STRIP_TAC THEN
    FIRST_ASSUM(fun th -> USE_THEN "lts" (fun lts -> MP_TAC(MATCH_MP lts th))) THEN
    ASM_REWRITE_TAC[LT_REFL] THEN NO_TAC in
  CONJ_TAC THENL [ALL_TAC; ELC_TAC THEN CONJ_TAC THENL
   [SIMP_TAC[]; USE_THEN "h11" ACCEPT_TAC]] THEN
  REWRITE_TAC(good_linear_scan_state_def :: K_THM :: LENGTH_LUPDATE ::
              LSCANPAUX_st_record @ LSCANPAUX_hs_record) THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [(* 3: distinct colours *)
    REWRITE_TAC[update_color_active_colors_same] THEN
    USE_THEN "h3" (fun th -> MATCH_MP_TAC ALL_DISTINCT_IS_SPARSE_SUBLIST THEN
      EXISTS_TAC (rand(concl th)) THEN REWRITE_TAC[th]) THEN
    MATCH_MP_TAC IS_SPARSE_SUBLIST_APPEND_LEFT THEN
    MATCH_MP_TAC MAP_IS_SPARSE_SUBLIST THEN MATCH_ACCEPT_TAC FILTER_IS_SPARSE_SUBLIST;
    (* 4: registers in range *)
    REWRITE_TAC[ALL] THEN USE_THEN "reglt" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "h4" ACCEPT_TAC;
    (* 5: colours below the stack bound *)
    ELC_TAC THEN REWRITE_TAC[ALL; ARITH_RULE `n < 1 + n`] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[ARITH_RULE `n < 1 + n`] THEN
    USE_THEN "lts" (fun th -> MP_TAC(MATCH_MP th (ASSUME `MEM (r:num) l`))) THEN ARITH_TAC;
    (* 6: phyregs *)
    USE_THEN "h6" (fun th -> REWRITE_TAC[th]) THEN ELC_TAC THEN REWRITE_TAC[MEM] THEN
    MATCH_MP_TAC LSCANPAUX_GSPEC_CONG THEN BETA_TAC THEN CONJ_TAC THEN
    X_GEN_TAC `r:num` THENL
     [ASM_CASES_TAC `r:num = reg` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
        USE_THEN "nSM" (fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "phy" (MP_TAC o SPEC `reg:num`) THEN REWRITE_TAC[] THEN MESON_TAC[];
        POP_ASSUM(fun th -> REWRITE_TAC[th])];
      STRIP_TAC THEN SUBGOAL_THEN `~(r:num = reg)` (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "phy" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* 7: physical registers distinct *)
    ELC_TAC THEN
    SUBGOAL_THEN `MAP (\r. if r = reg then linear_scan_state_stacknum st
                           else EL r (linear_scan_hidden_state_colors sth))
                      (FILTER is_phy_var l) =
                  MAP (\r. EL r (linear_scan_hidden_state_colors sth)) (FILTER is_phy_var l)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN
      X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(r:num = reg)` (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "phy" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[FILTER] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP; ALL_DISTINCT] THEN
    REWRITE_TAC[MEM_MAP; MEM_FILTER; NOT_EXISTS_THM] THEN X_GEN_TAC `r:num` THEN
    STRIP_TAC THEN
    USE_THEN "lts" (fun th -> MP_TAC(MATCH_MP th (ASSUME `MEM (r:num) l`))) THEN
    ASM_REWRITE_TAC[LT_REFL];
    (* 9: active colours below colornum *)
    ELC_TAC THEN USE_THEN "h9" MP_TAC THEN
    REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER; FORALL_PAIR_THM; pair_CASE] THEN
    DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`e:int`; `r:num`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPECL [`e:int`; `r:num`]) THEN
    ASM_REWRITE_TAC[];
    (* 11: colormax below the new stacknum *)
    USE_THEN "h11" MP_TAC THEN ARITH_TAC;
    (* 12: colours below colormax are below colornum *)
    ELC_TAC THEN REWRITE_TAC[ALL] THEN USE_THEN "nSM" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "h12" MP_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    DISCH_TAC THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    USE_THEN "nSM" (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[];
    (* 13: int_beg *)
    REWRITE_TAC[ALL] THEN USE_THEN "regbeg" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "h13" ACCEPT_TAC;
    (* 14: live registers are active *)
    ELC_TAC THEN REWRITE_TAC[ALL; MEM_FILTER; pair_CASE] THEN
    USE_THEN "nSM" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "h14" MP_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN DISCH_TAC THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    USE_THEN "nSM" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[];
    (* 15: active registers end late enough *)
    REWRITE_TAC[ALL; MEM_FILTER; pair_CASE] THEN
    USE_THEN "h15" MP_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
    (* 16: interference *)
    ELC_TAC THEN REWRITE_TAC[MEM] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC `r1:num = reg` THEN ASM_CASES_TAC `r2:num = reg` THEN
    ASM_REWRITE_TAC[] THEN LTS_TAC;
    (* 17: sorted *)
    MATCH_MP_TAC SORTED_FILTER THEN REWRITE_TAC[transitive_less_FST] THEN
    USE_THEN "h17" ACCEPT_TAC;
    (* 18: active ends *)
    USE_THEN "h18" MP_TAC THEN REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN MESON_TAC[];
    (* 19: active registers in l *)
    USE_THEN "h19" MP_TAC THEN
    REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER; FORALL_PAIR_THM; pair_CASE; MEM] THEN MESON_TAC[];
    (* 20: forced pairs *)
    ELC_TAC THEN USE_THEN "h20" MP_TAC THEN
    REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE; MEM] THEN
    DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`r1:num`; `r2:num`] THEN DISCH_TAC THEN
    ASM_CASES_TAC `r1:num = reg` THEN ASM_CASES_TAC `r2:num = reg` THEN
    ASM_REWRITE_TAC[] THEN TRY LTS_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`r1:num`; `r2:num`]) THEN ASM_REWRITE_TAC[];
    (* 22: mincol *)
    ELC_TAC THEN USE_THEN "h22" MP_TAC THEN
    REWRITE_TAC[ALL_APPEND; ALL_MAP; MAP; ALL; GSYM ALL_MEM; o_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "m2")) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "m2" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* HOL4 line 2914 *)
let spill_register_FILTER_invariants =
  REWRITE_RULE[linear_scanProof_id_def] spill_register_FILTER_invariants_hidden;;

(* HOL4 line 2918 *)
let FILTER_MEM_active = prove
 (CASE_TERM
  `!(reg:num) l.
     (!e:int. ~MEM (e,reg) l) ==>
     FILTER (\er. match er with (e,r) -> ~(r = reg)) l = l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[FILTER; MEM; DE_MORGAN_THM; FORALL_AND_THM] THEN
  MP_TAC(ISPEC `h:int#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:int` (X_CHOOSE_THEN `r:num` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[pair_CASE; PAIR_EQ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(r:num = reg)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[CONS_11] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 2926 *)
let spill_register_invariants = prove
 (`!st sth l pos forced reg mincol.
     (!e. ~MEM (e,reg) (linear_scan_state_active st)) /\
     (~is_phy_var reg \/ ~MEM reg l) /\
     good_linear_scan_state st sth l pos forced mincol /\
     reg < LENGTH (linear_scan_hidden_state_colors sth) /\
     EL reg (linear_scan_hidden_state_int_beg sth) <= pos ==>
     ?stout sthout.
       (M_success stout,sthout) = spill_register st reg sth /\
       good_linear_scan_state stout sthout (CONS reg l) pos forced mincol /\
       LENGTH (linear_scan_hidden_state_colors sthout) =
         LENGTH (linear_scan_hidden_state_colors sth) /\
       linear_scan_hidden_state_int_beg sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout = linear_scan_hidden_state_int_end sth /\
       (!r. ~(r = reg) ==>
            EL r (linear_scan_hidden_state_colors sth) =
            EL r (linear_scan_hidden_state_colors sthout)) /\
       linear_scan_state_colormax stout = linear_scan_state_colormax st /\
       linear_scan_state_colormax st <= EL reg (linear_scan_hidden_state_colors sthout)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nomem") MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP spill_register_FILTER_invariants) THEN
  USE_THEN "nomem" (fun th -> REWRITE_TAC[MATCH_MP FILTER_MEM_active th]) THEN
  SUBGOAL_THEN `linear_scan_state_active_fupd (K (linear_scan_state_active st)) st = st`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[linear_scan_state_component_equality] THEN
    REWRITE_TAC(K_THM :: LSCANPAUX_st_record);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `stout:linear_scan_state`
    (X_CHOOSE_THEN `sthout:linear_scan_hidden_state` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`stout:linear_scan_state`; `sthout:linear_scan_hidden_state`] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 2947 *)
let edges_to_adjlist_step_def = cake_def
  `edges_to_adjlist_step sth (a,b) (acc:(num list)spt) =
     if a = b then acc
     else if (((<):int->int->bool) LEX ((<=):num->num->bool))
               (EL a (linear_scan_hidden_state_int_beg sth),a)
               (EL b (linear_scan_hidden_state_int_beg sth),b)
     then insert b (CONS a (misc_the [] (lookup b acc))) acc
     else insert a (CONS b (misc_the [] (lookup a acc))) acc`;;
(* HOL4 line 2957 *)
let edges_to_adjlist_FOLDL = prove
 (CASE_TERM
  `!forced sth acc.
     ALL (\r12. match r12 with
                  (r1,r2) -> r1 < LENGTH (linear_scan_hidden_state_int_beg sth) /\
                             r2 < LENGTH (linear_scan_hidden_state_int_beg sth))
         forced ==>
     edges_to_adjlist forced acc sth =
       (M_success (FOLDL (\acc pair. edges_to_adjlist_step sth pair acc) acc forced),sth)`,
    LIST_INDUCT_TAC THENL
   [REWRITE_TAC(edges_to_adjlist_def :: FOLDL :: RAPROOFAUX_msimps); ALL_TAC] THEN
  MP_TAC(ISPEC `h:num#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `b:num` SUBST_ALL_TAC)) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL; pair_CASE] THEN STRIP_TAC THEN
  REWRITE_TAC[FOLDL; edges_to_adjlist_def; edges_to_adjlist_step_def] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_REWRITE_TAC(int_beg_sub_eqn :: case_def "prod" :: case_def "exc" :: LEX_THM ::
                  RAPROOFAUX_msimps) THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

(* HOL4 line 2972 *)
let forbidden_is_from_forced_def = cake_def
  `forbidden_is_from_forced forced (int_beg:int list) reg forbidden <=>
     !reg2. (~(reg = reg2) /\ (MEM (reg2,reg) forced \/ MEM (reg,reg2) forced) /\
             (((<):int->int->bool) LEX ((<=):num->num->bool))
               (EL reg2 int_beg,reg2) (EL reg int_beg,reg)) <=>
            MEM reg2 forbidden`;;
(* HOL4 line 2978 *)
let forbidden_is_from_forced_sublist_def = cake_def
  `forbidden_is_from_forced_sublist l forced (int_beg:int list) reg forbidden <=>
     !reg2. (~(reg = reg2) /\ (MEM (reg2,reg) forced \/ MEM (reg,reg2) forced) /\
             (((<):int->int->bool) LEX ((<=):num->num->bool))
               (EL reg2 int_beg,reg2) (EL reg int_beg,reg)) <=>
            (MEM reg2 forbidden /\ MEM reg l)`;;
(* HOL4 line 2984 *)
let forbidden_is_from_forced_list_def = cake_def
  `forbidden_is_from_forced_list forced l (reg:num) forbidden <=>
     !reg2. MEM reg2 l /\ (MEM (reg2,reg) forced \/ MEM (reg,reg2) forced) ==>
            MEM reg2 forbidden`;;
(* HOL4 line 2991 *)
let forbidden_is_from_map_color_forced_def = cake_def
  `forbidden_is_from_map_color_forced forced l (colors:num list) (reg:num)
     (forbidden:1 spt) <=>
     !reg2. MEM reg2 l /\ (MEM (reg2,reg) forced \/ MEM (reg,reg2) forced) ==>
            EL reg2 colors IN domain forbidden`;;
(* LSCANPAUX_LEX_ANTISYM, LSCANPAUX_LEX_TOTAL: the order used for the     *)
(* forced edges is antisymmetric and total                                  *)
let LSCANPAUX_LEX_ANTISYM = prove
 (`!(x:int) (a:num) y b.
     (((<):int->int->bool) LEX ((<=):num->num->bool)) (x,a) (y,b) /\
     (((<):int->int->bool) LEX ((<=):num->num->bool)) (y,b) (x,a) ==> a = b`,
  REWRITE_TAC[LEX_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `x:int = y` THEN ASM_REWRITE_TAC[INT_LT_REFL] THENL
   [ARITH_TAC; MESON_TAC[INT_LT_ANTISYM]]);;

let LSCANPAUX_LEX_TOTAL = prove
 (`!(x:int) (a:num) y b.
     ~((((<):int->int->bool) LEX ((<=):num->num->bool)) (x,a) (y,b)) ==>
     (((<):int->int->bool) LEX ((<=):num->num->bool)) (y,b) (x,a)`,
  REWRITE_TAC[LEX_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `x:int = y` THEN ASM_REWRITE_TAC[INT_LT_REFL] THENL
   [ARITH_TAC; POP_ASSUM MP_TAC THEN INT_ARITH_TAC]);;


(* HOL4 line 2998 *)
let edges_to_adjlist_FOLDR_output = prove
 (`!forced sth. !reg.
     forbidden_is_from_forced forced (linear_scan_hidden_state_int_beg sth) reg
       (misc_the [] (lookup reg (ITLIST (\pair acc. edges_to_adjlist_step sth pair acc)
                                   forced LN)))`,
    GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC THEN
  REWRITE_TAC[forbidden_is_from_forced_def] THEN
  LIST_INDUCT_TAC THENL [REWRITE_TAC[ITLIST; MEM; lookup_def; misc_the_def]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  MP_TAC(ISPEC `h:num#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `b:num` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[ITLIST] THEN
  SPEC_TAC(`ITLIST (\pair acc. edges_to_adjlist_step sth pair acc) t LN`,
           `adj:(num list)spt`) THEN
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "ih") THEN
  REWRITE_TAC[edges_to_adjlist_step_def; MEM; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`reg:num`; `reg2:num`] THEN
  ASM_CASES_TAC `a:num = b` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
    REMOVE_THEN "ih" (fun th -> REWRITE_TAC[GSYM th]) THEN MESON_TAC[];
    ALL_TAC] THEN
  POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
  ASM_CASES_TAC `(((<):int->int->bool) LEX ((<=):num->num->bool))
                   (EL a (linear_scan_hidden_state_int_beg sth),a)
                   (EL b (linear_scan_hidden_state_int_beg sth),b)` THEN
  POP_ASSUM(fun th -> REWRITE_TAC[th; lookup_insert] THEN ASSUME_TAC th) THENL
   [ASM_CASES_TAC `reg:num = b` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[misc_the_def; MEM] THEN
      REMOVE_THEN "ih" (fun th -> REWRITE_TAC[GSYM th]) THEN
      ASM_CASES_TAC `reg2:num = a` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
      REMOVE_THEN "ih" (fun th -> REWRITE_TAC[GSYM th]) THEN
      ASM_MESON_TAC[LSCANPAUX_LEX_ANTISYM]];
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP LSCANPAUX_LEX_TOTAL) THEN
    ASM_CASES_TAC `reg:num = a` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[misc_the_def; MEM] THEN
      REMOVE_THEN "ih" (fun th -> REWRITE_TAC[GSYM th]) THEN
      ASM_CASES_TAC `reg2:num = b` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
      REMOVE_THEN "ih" (fun th -> REWRITE_TAC[GSYM th]) THEN
      ASM_MESON_TAC[]]]);;

(* HOL4 line 3062 *)
let edges_to_adjlist_output = prove
 (CASE_TERM
  `!forced sth.
     ALL (\r12. match r12 with
                  (r1,r2) -> r1 < LENGTH (linear_scan_hidden_state_int_beg sth) /\
                             r2 < LENGTH (linear_scan_hidden_state_int_beg sth))
         forced ==>
     ?adjlist. edges_to_adjlist forced LN sth = (M_success adjlist,sth) /\
               !reg. forbidden_is_from_forced forced (linear_scan_hidden_state_int_beg sth)
                       reg (misc_the [] (lookup reg adjlist))`,
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[edges_to_adjlist_FOLDL] THEN
  (fun (asl,w as g) ->
     let eq = fst(dest_conj(snd(dest_exists w))) in
     EXISTS_TAC (rand(fst(dest_pair(lhs eq)))) g) THEN
  REWRITE_TAC[] THEN X_GEN_TAC `reg:num` THEN
  MP_TAC(SPECL [`REVERSE forced:(num#num)list`; `sth:linear_scan_hidden_state`; `reg:num`]
    edges_to_adjlist_FOLDR_output) THEN
  REWRITE_TAC[forbidden_is_from_forced_def; MEM_REVERSE; FOLDL_FOLDR_REVERSE]);;

(* HOL4 line 3073 *)
let state_invariants_remove_head = prove
 (`!st sth reg l pos forced mincol.
     MEM reg l /\
     good_linear_scan_state st sth (CONS reg l) pos forced mincol ==>
     good_linear_scan_state st sth l pos forced mincol`,
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `!r:num. MEM r (CONS reg l) <=> MEM r l` (LABEL_TAC "memeq") THENL
   [REWRITE_TAC[MEM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[good_linear_scan_state_def] THEN
  SUBGOAL_THEN
   `ALL_DISTINCT (MAP (\r. EL r (linear_scan_hidden_state_colors sth))
                      (FILTER is_phy_var (CONS reg l))) ==>
    ALL_DISTINCT (MAP (\r. EL r (linear_scan_hidden_state_colors sth))
                      (FILTER is_phy_var l))` MP_TAC THENL
   [REWRITE_TAC[FILTER] THEN COND_CASES_TAC THEN REWRITE_TAC[MAP; ALL_DISTINCT] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM ALL_MEM; ALL_APPEND; MEM_MAP] THEN
  USE_THEN "memeq" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* HOL4 line 3086 *)
let find_last_stealable_success = prove
 (CASE_TERM
  `!forbidden sth active.
     ALL (\er. match er with (e,r) -> r < LENGTH (linear_scan_hidden_state_colors sth))
         active ==>
     ?optout. find_last_stealable active forbidden sth = (M_success optout,sth)`,
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC(find_last_stealable_def :: RAPROOFAUX_msimps) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `h:int#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:int` (X_CHOOSE_THEN `r:num` SUBST_ALL_TAC)) THEN
  REWRITE_TAC[ALL; pair_CASE; SND] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `opt:((int#num)#(int#num)list)option` SUBST1_TAC) THEN
  REWRITE_TAC[case_def "prod"; case_def "exc"] THEN
  CASES_ON `opt:((int#num)#(int#num)list)option` THEN
  REWRITE_TAC[case_def "option"] THENL
   [ASM_REWRITE_TAC(colors_sub_eqn :: case_def "prod" :: case_def "exc" :: RAPROOFAUX_msimps) THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN MESON_TAC[];
    MP_TAC(ISPEC `a:(int#num)#(int#num)list` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `steal:int#num` (X_CHOOSE_THEN `rest:(int#num)list`
      SUBST1_TAC)) THEN
    REWRITE_TAC(pair_CASE :: RAPROOFAUX_msimps) THEN MESON_TAC[]]);;


(* HOL4 line 3100 *)
let find_last_stealable_output = prove
 (`!forbidden sth active steal rest.
     find_last_stealable active forbidden sth = (M_success (SOME (steal,rest)),sth) ==>
     ~is_phy_var (SND steal) /\
     lookup (EL (SND steal) (linear_scan_hidden_state_colors sth)) forbidden = NONE /\
     ?l1 l2. rest = APPEND l1 l2 /\ active = APPEND l1 (CONS steal l2)`,
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC(find_last_stealable_def :: RAPROOFAUX_msimps) THEN
  REWRITE_TAC[PAIR_EQ; injectivity "exc"; option_DISTINCT] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `find_last_stealable t forbidden sth` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `res:(((int#num)#(int#num)list)option,state_exn)exc`
    (X_CHOOSE_THEN `s1:linear_scan_hidden_state` (LABEL_TAC "rec"))) THEN
  USE_THEN "rec" (fun th -> REWRITE_TAC[th; case_def "prod"]) THEN
  DISJ_CASES_THEN2
    (X_CHOOSE_THEN `v:((int#num)#(int#num)list)option` SUBST_ALL_TAC)
    (X_CHOOSE_THEN `err:state_exn` SUBST_ALL_TAC)
    (ISPEC `res:(((int#num)#(int#num)list)option,state_exn)exc` (cases "exc")) THEN
  REWRITE_TAC[case_def "exc"; PAIR_EQ; distinctness "exc"] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `p:(int#num)#(int#num)list` SUBST_ALL_TAC)
    (ISPEC `v:((int#num)#(int#num)list)option` (cases "option")) THEN
  REWRITE_TAC[case_def "option"] THENL
   [REWRITE_TAC(colors_sub_eqn :: case_def "prod" :: case_def "exc" :: RAPROOFAUX_msimps) THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[case_def "prod"; case_def "exc"; PAIR_EQ; distinctness "exc"] THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[PAIR_EQ; injectivity "exc"; option_DISTINCT; option_INJ] THEN
    STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`[]:(int#num)list`; `t:(int#num)list`] THEN REWRITE_TAC[APPEND];
    MP_TAC(ISPEC `p:(int#num)#(int#num)list` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `steal':int#num` (X_CHOOSE_THEN `rest':(int#num)list`
      SUBST_ALL_TAC)) THEN
    REWRITE_TAC(pair_CASE :: RAPROOFAUX_msimps) THEN
    REWRITE_TAC[PAIR_EQ; injectivity "exc"; option_INJ] THEN
    STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_eq(concl th) && is_var(rhs(concl th))))) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`steal':int#num`; `rest':(int#num)list`]) THEN
    USE_THEN "rec" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `l1:(int#num)list` (X_CHOOSE_THEN `l2:(int#num)list`
        STRIP_ASSUME_TAC)))) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`CONS (h:int#num) l1`; `l2:(int#num)list`] THEN
    REWRITE_TAC[APPEND]]);;

(* HOL4 line 3132 *)
let good_linear_scan_state_active_length_colors = prove
 (CASE_TERM
  `!st sth l pos forced mincol.
     good_linear_scan_state st sth l pos forced mincol ==>
     ALL (\er. match er with (e,r) -> r < LENGTH (linear_scan_hidden_state_colors sth))
         (linear_scan_state_active st)`,
    REPEAT GEN_TAC THEN
  DISCH_THEN(LSCANPAUX_LABEL_CONJS "h" o REWRITE_RULE[good_linear_scan_state_def]) THEN
  USE_THEN "h4" MP_TAC THEN USE_THEN "h19" MP_TAC THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE] THEN MESON_TAC[]);;

(* HOL4 line 3142 *)
let color_register_eq = prove
 (`!st reg col rend.
     color_register st reg col rend =
       st_ex_ignore_bind (update_colors reg col)
         (st_ex_return
            (linear_scan_state_active_fupd (add_active_interval (rend,reg))
               (linear_scan_state_phyregs_fupd
                  (K (if is_phy_var reg then insert col one (linear_scan_state_phyregs st)
                      else linear_scan_state_phyregs st)) st)))`,
    REPEAT GEN_TAC THEN REWRITE_TAC[color_register_def] THEN COND_CASES_TAC THEN
  REPEAT AP_TERM_TAC THEN REWRITE_TAC[linear_scan_state_component_equality] THEN
  REWRITE_TAC(K_THM :: LSCANPAUX_st_record));;


(* LSCANPAUX_ALL_DISTINCT_MIDDLE: an element inserted in the middle *)
let LSCANPAUX_ALL_DISTINCT_MIDDLE = prove
 (`!(x:A) l1 l2. ALL_DISTINCT (APPEND l1 (CONS x l2)) <=>
                 ~MEM x (APPEND l1 l2) /\ ALL_DISTINCT (APPEND l1 l2)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`APPEND l1 (CONS (x:A) l2)`; `CONS (x:A) (APPEND l1 l2)`]
    ALL_DISTINCT_PERM) THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[PERM_SYM] THEN REWRITE_TAC[PERM_CONS_EQ_APPEND] THEN
    MAP_EVERY EXISTS_TAC [`l1:A list`; `l2:A list`] THEN REWRITE_TAC[PERM_REFL];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ALL_DISTINCT]]);;

(* LSCANPAUX_MAP_PAIR_LUPDATE: updating a colour not used by the intervals *)
let LSCANPAUX_MAP_PAIR_LUPDATE = prove
 (CASE_TERM
  `!(k:(int#num)list) col reg (C:num list).
     (!e r. MEM (e,r) k ==> ~(r = reg)) ==>
     MAP (\er. match er with (e,r) -> EL r (LUPDATE col reg C)) k =
     MAP (\er. match er with (e,r) -> EL r C) k`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[EL_LUPDATE] THEN
  SUBGOAL_THEN `~(p2:num = reg)` (fun th -> REWRITE_TAC[th]) THEN ASM_MESON_TAC[]);;

(* HOL4 line 3161 *)
let color_register_invariants = prove
 (CASE_TERM
  `!st sth l pos forced reg col forbidden mincol.
     good_linear_scan_state st sth l pos forced mincol /\
     forbidden_is_from_map_color_forced forced l (linear_scan_hidden_state_colors sth) reg
       forbidden /\
     ~(col IN domain forbidden) /\
     (is_phy_var reg ==> domain (linear_scan_state_phyregs st) SUBSET domain forbidden) /\
     ~MEM col (APPEND (linear_scan_state_colorpool st)
                 (MAP (\er. match er with
                              (e,r) -> EL r (linear_scan_hidden_state_colors sth))
                      (linear_scan_state_active st))) /\
     EL reg (linear_scan_hidden_state_int_beg sth) = pos /\
     EL reg (linear_scan_hidden_state_int_beg sth) <=
       EL reg (linear_scan_hidden_state_int_end sth) /\
     col < linear_scan_state_colornum st /\
     mincol <= col /\
     reg < LENGTH (linear_scan_hidden_state_colors sth) /\
     ~MEM reg l
     ==> ?stout sthout.
           (M_success stout,sthout) =
             color_register st reg col (EL reg (linear_scan_hidden_state_int_end sth)) sth /\
           good_linear_scan_state stout sthout (CONS reg l) pos forced mincol /\
           LENGTH (linear_scan_hidden_state_colors sthout) =
             LENGTH (linear_scan_hidden_state_colors sth) /\
           linear_scan_hidden_state_int_beg sthout = linear_scan_hidden_state_int_beg sth /\
           linear_scan_hidden_state_int_end sthout = linear_scan_hidden_state_int_end sth /\
           (!r. ~(r = reg) ==>
                EL r (linear_scan_hidden_state_colors sth) =
                EL r (linear_scan_hidden_state_colors sthout)) /\
           linear_scan_state_colormax stout = linear_scan_state_colormax st`,
    REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gls") (CONJUNCTS_THEN2 (LABEL_TAC "fmc")
    (CONJUNCTS_THEN2 (LABEL_TAC "colnf") (CONJUNCTS_THEN2 (LABEL_TAC "phyf")
    (CONJUNCTS_THEN2 (LABEL_TAC "colnm") (CONJUNCTS_THEN2 (LABEL_TAC "begpos")
    (CONJUNCTS_THEN2 (LABEL_TAC "begend") (CONJUNCTS_THEN2 (LABEL_TAC "colN")
    (CONJUNCTS_THEN2 (LABEL_TAC "mincol") (CONJUNCTS_THEN2 (LABEL_TAC "reglt")
    (LABEL_TAC "regnl"))))))))))) THEN
  USE_THEN "gls" (LSCANPAUX_LABEL_CONJS "h" o REWRITE_RULE[good_linear_scan_state_def]) THEN
  SUBGOAL_THEN `!r:num. MEM r l ==> ~(r = reg)` (LABEL_TAC "nl") THENL
   [USE_THEN "regnl" MP_TAC THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!(e:int) (r:num). MEM (e,r) (linear_scan_state_active st) ==> ~(r = reg)`
    (LABEL_TAC "nreg") THENL
   [USE_THEN "h19" MP_TAC THEN USE_THEN "nl" MP_TAC THEN
    REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `col < linear_scan_state_colormax st` (LABEL_TAC "colM") THENL
   [USE_THEN "colN" MP_TAC THEN USE_THEN "h10" MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`EL reg (linear_scan_hidden_state_int_end sth)`; `reg:num`;
    `linear_scan_state_active st`; `0`;
    `add_active_interval (EL reg (linear_scan_hidden_state_int_end sth),reg)
       (linear_scan_state_active st)`] add_active_interval_output) THEN
  USE_THEN "h17" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sortA") (X_CHOOSE_THEN `l1:(int#num)list`
    (X_CHOOSE_THEN `l2:(int#num)list` (CONJUNCTS_THEN2 (LABEL_TAC "Aeq")
      (LABEL_TAC "A'eq"))))) THEN
  SUBGOAL_THEN `!x. MEM x (add_active_interval (EL reg (linear_scan_hidden_state_int_end sth),reg)
                     (linear_scan_state_active st)) <=>
                    x = (EL reg (linear_scan_hidden_state_int_end sth),reg) \/
                    MEM x (linear_scan_state_active st)` (LABEL_TAC "memA") THENL
   [USE_THEN "A'eq" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "Aeq" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[MEM_APPEND; MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. MEM r l /\ pos <= EL r (linear_scan_hidden_state_int_end sth) ==>
                  ~(EL r (linear_scan_hidden_state_colors sth) = col)` (LABEL_TAC "cf") THENL
   [X_GEN_TAC `r:num` THEN STRIP_TAC THEN DISCH_TAC THEN
    USE_THEN "h14" (MP_TAC o SPEC `r:num` o REWRITE_RULE[GSYM ALL_MEM]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "colnm" MP_TAC THEN REWRITE_TAC[MEM_APPEND; MEM_MAP; EXISTS_PAIR_THM; pair_CASE] THEN
    DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`EL r (linear_scan_hidden_state_int_end sth)`; `r:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN (CASE_TERM
   `ALL_DISTINCT (APPEND (linear_scan_state_colorpool st)
      (MAP (\er. match er with
                   (e,r) -> EL r (LUPDATE col reg (linear_scan_hidden_state_colors sth)))
           (add_active_interval (EL reg (linear_scan_hidden_state_int_end sth),reg)
              (linear_scan_state_active st))))`) (LABEL_TAC "g3") THENL
   [SUBGOAL_THEN `(!(e:int) r. MEM (e,r) (l1:(int#num)list) ==> ~(r = reg)) /\
                  (!(e:int) r. MEM (e,r) (l2:(int#num)list) ==> ~(r = reg))`
      (CONJUNCTS_THEN2 (LABEL_TAC "nr1") (LABEL_TAC "nr2")) THENL
     [USE_THEN "nreg" MP_TAC THEN USE_THEN "Aeq" (fun th -> REWRITE_TAC[th; MEM_APPEND]) THEN
      MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "A'eq" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[MAP_APPEND; MAP; pair_CASE] THEN
    USE_THEN "nr1" (fun th -> REWRITE_TAC[MATCH_MP LSCANPAUX_MAP_PAIR_LUPDATE th]) THEN
    USE_THEN "nr2" (fun th -> REWRITE_TAC[MATCH_MP LSCANPAUX_MAP_PAIR_LUPDATE th]) THEN
    REWRITE_TAC[EL_LUPDATE] THEN USE_THEN "reglt" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[APPEND_ASSOC] THEN REWRITE_TAC[LSCANPAUX_ALL_DISTINCT_MIDDLE] THEN
    USE_THEN "h3" MP_TAC THEN USE_THEN "colnm" MP_TAC THEN
    USE_THEN "Aeq" (fun th -> REWRITE_TAC[th; MAP_APPEND; APPEND_ASSOC]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "Aeq" (K ALL_TAC) THEN REMOVE_THEN "A'eq" (K ALL_TAC) THEN
  REWRITE_TAC[color_register_eq] THEN
  REWRITE_TAC(update_colors_eqn :: RAPROOFAUX_msimps) THEN
  USE_THEN "reglt" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
  LSCANPAUX_PAIR_WITNESS_TAC THEN
  REWRITE_TAC(K_THM :: LENGTH_LUPDATE :: LSCANPAUX_st_record @ LSCANPAUX_hs_record) THEN
  let ELC_TAC = REWRITE_TAC[EL_LUPDATE] THEN USE_THEN "reglt" (fun th -> REWRITE_TAC[th]) in
  let NL_TAC = USE_THEN "nl" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `MEM (r:num) l`)]) in
  CONJ_TAC THENL [ALL_TAC; ELC_TAC THEN SIMP_TAC[]] THEN
  REWRITE_TAC(good_linear_scan_state_def :: K_THM :: LENGTH_LUPDATE ::
              LSCANPAUX_st_record @ LSCANPAUX_hs_record) THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [(* 4: registers in range *)
    REWRITE_TAC[ALL] THEN USE_THEN "reglt" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "h4" ACCEPT_TAC;
    (* 5: colours below stacknum *)
    ELC_TAC THEN REWRITE_TAC[ALL] THEN CONJ_TAC THENL
     [USE_THEN "colM" MP_TAC THEN USE_THEN "h11" MP_TAC THEN ARITH_TAC;
      USE_THEN "h5" MP_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN
      DISCH_TAC THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN NL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[]];
    (* 6: phyregs *)
    COND_CASES_TAC THENL
     [REWRITE_TAC[domain_insert] THEN USE_THEN "h6" (fun th -> REWRITE_TAC[th]) THEN
      ELC_TAC THEN REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM; MEM] THEN
      X_GEN_TAC `x:num` THEN EQ_TAC THENL
       [STRIP_TAC THENL
         [EXISTS_TAC `reg:num` THEN ASM_REWRITE_TAC[];
          EXISTS_TAC `r:num` THEN NL_TAC THEN ASM_REWRITE_TAC[]];
        DISCH_THEN(X_CHOOSE_THEN `r:num` MP_TAC) THEN ASM_CASES_TAC `r:num = reg` THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        DISJ2_TAC THEN EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[]];
      USE_THEN "h6" (fun th -> REWRITE_TAC[th]) THEN ELC_TAC THEN REWRITE_TAC[MEM] THEN
      MATCH_MP_TAC LSCANPAUX_GSPEC_CONG THEN BETA_TAC THEN CONJ_TAC THEN
      X_GEN_TAC `r:num` THENL
       [ASM_CASES_TAC `r:num = reg` THEN ASM_REWRITE_TAC[];
        STRIP_TAC THEN NL_TAC]];
    (* 7: physical registers distinct *)
    ELC_TAC THEN
    SUBGOAL_THEN `MAP (\r. if r = reg then col else EL r (linear_scan_hidden_state_colors sth))
                      (FILTER is_phy_var l) =
                  MAP (\r. EL r (linear_scan_hidden_state_colors sth)) (FILTER is_phy_var l)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN
      X_GEN_TAC `r:num` THEN STRIP_TAC THEN NL_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[FILTER] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP; ALL_DISTINCT] THEN
    REWRITE_TAC[MEM_MAP; MEM_FILTER; NOT_EXISTS_THM] THEN X_GEN_TAC `r:num` THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `col:num`)) THEN
    USE_THEN "colnf" MP_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "phyf" (fun th -> MP_TAC(MATCH_MP th (ASSUME `is_phy_var reg`))) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "h6" (fun th -> REWRITE_TAC[th; IN_ELIM_THM]) THEN
    EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[];
    (* 9: active colours below colornum *)
    ELC_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN USE_THEN "memA" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; pair_CASE] THEN
    MAP_EVERY X_GEN_TAC [`e:int`; `r:num`] THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "nreg" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `MEM (e:int,r:num) (linear_scan_state_active st)`)]) THEN
      USE_THEN "h9" (MP_TAC o SPEC `(e:int,r:num)` o REWRITE_RULE[GSYM ALL_MEM]) THEN
      ASM_REWRITE_TAC[pair_CASE]];
    (* 12: colours below colormax are below colornum *)
    ELC_TAC THEN REWRITE_TAC[ALL] THEN USE_THEN "colN" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "h12" MP_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    DISCH_TAC THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN NL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[];
    (* 13: int_beg *)
    REWRITE_TAC[ALL] THEN USE_THEN "begpos" (fun th -> REWRITE_TAC[th; INT_LE_REFL]) THEN
    USE_THEN "h13" ACCEPT_TAC;
    (* 14: live registers are active *)
    ELC_TAC THEN USE_THEN "memA" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[ALL] THEN
    USE_THEN "h14" MP_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    DISCH_TAC THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN NL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    (* 15: active intervals end late enough *)
    USE_THEN "memA" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[ALL] THEN CONJ_TAC THENL
     [USE_THEN "begpos" (SUBST1_TAC o SYM) THEN USE_THEN "begend" MP_TAC THEN INT_ARITH_TAC;
      USE_THEN "h15" MP_TAC THEN REWRITE_TAC[GSYM ALL_MEM; PAIR_EQ] THEN
      DISCH_TAC THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN NL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[]];
    (* 16: interference *)
    ELC_TAC THEN REWRITE_TAC[MEM] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC `r1:num = reg` THEN ASM_CASES_TAC `r2:num = reg` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[interval_intersect_def] THEN STRIP_TAC THENL
     [REMOVE_THEN "cf" (MP_TAC o SPEC `r2:num`) THEN ASM_REWRITE_TAC[];
      REMOVE_THEN "cf" (MP_TAC o SPEC `r1:num`) THEN ASM_REWRITE_TAC[]];
    (* 18: active ends *)
    REWRITE_TAC[GSYM ALL_MEM] THEN USE_THEN "memA" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; pair_CASE] THEN
    MAP_EVERY X_GEN_TAC [`e:int`; `r:num`] THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "h18" (MP_TAC o SPEC `(e:int,r:num)` o REWRITE_RULE[GSYM ALL_MEM]) THEN
      ASM_REWRITE_TAC[pair_CASE]];
    (* 19: active registers in CONS reg l *)
    REWRITE_TAC[GSYM ALL_MEM] THEN USE_THEN "memA" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; pair_CASE; MEM] THEN
    MAP_EVERY X_GEN_TAC [`e:int`; `r:num`] THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[];
      DISJ2_TAC THEN
      USE_THEN "h19" (MP_TAC o SPEC `(e:int,r:num)` o REWRITE_RULE[GSYM ALL_MEM]) THEN
      ASM_REWRITE_TAC[pair_CASE]];
    (* 20: forced pairs *)
    ELC_TAC THEN REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE; MEM] THEN
    MAP_EVERY X_GEN_TAC [`r1:num`; `r2:num`] THEN DISCH_TAC THEN
    ASM_CASES_TAC `r1:num = reg` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_CASES_TAC `r2:num = reg` THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN USE_THEN "colnf" MP_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `col:num`)) THEN
      USE_THEN "fmc" (MATCH_MP_TAC o REWRITE_RULE[forbidden_is_from_map_color_forced_def]) THEN
      ASM_REWRITE_TAC[];
      ASM_CASES_TAC `r2:num = reg` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
        STRIP_TAC THEN USE_THEN "colnf" MP_TAC THEN REWRITE_TAC[] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o
          check (fun th -> is_eq(concl th) && rhs(concl th) = `col:num`)) THEN
        USE_THEN "fmc" (MATCH_MP_TAC o REWRITE_RULE[forbidden_is_from_map_color_forced_def]) THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN
        USE_THEN "h20" (MP_TAC o SPEC `(r1:num,r2:num)` o REWRITE_RULE[GSYM ALL_MEM]) THEN
        ASM_REWRITE_TAC[pair_CASE]]];
    (* 22: mincol *)
    ELC_TAC THEN USE_THEN "h22" MP_TAC THEN
    REWRITE_TAC[ALL_APPEND; ALL_MAP; MAP; ALL; GSYM ALL_MEM; o_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "m2")) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN NL_TAC THEN
    USE_THEN "m2" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;


(* LSCANPAUX_gls_nomem: registers outside l have no active interval *)
let LSCANPAUX_gls_nomem = prove
 (`!st sth l pos forced mincol reg.
     good_linear_scan_state st sth l pos forced mincol /\ ~MEM reg l ==>
     !e. ~MEM (e,reg) (linear_scan_state_active st)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (LSCANPAUX_LABEL_CONJS "h" o REWRITE_RULE[good_linear_scan_state_def]) MP_TAC) THEN
  USE_THEN "h19" MP_TAC THEN REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE] THEN
  MESON_TAC[]);;

(* LSCANPAUX_find_spill_fallback: the spilling branches of find_spill *)
let LSCANPAUX_find_spill_fallback = prove
 (`!st sth l forced reg mincol.
     ~MEM reg l /\
     good_linear_scan_state st sth l (EL reg (linear_scan_hidden_state_int_beg sth)) forced
       mincol /\
     reg < LENGTH (linear_scan_hidden_state_colors sth) ==>
     ?stout sthout.
       (M_success stout,sthout) = spill_register st reg sth /\
       good_linear_scan_state stout sthout (CONS reg l)
         (EL reg (linear_scan_hidden_state_int_beg sth)) forced mincol /\
       LENGTH (linear_scan_hidden_state_colors sthout) =
         LENGTH (linear_scan_hidden_state_colors sth) /\
       linear_scan_hidden_state_int_beg sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout = linear_scan_hidden_state_int_end sth /\
       (!r. ~MEM r (CONS reg l) ==>
            EL r (linear_scan_hidden_state_colors sthout) =
            EL r (linear_scan_hidden_state_colors sth)) /\
       (!r. MEM r l /\ is_phy_var r ==>
            EL r (linear_scan_hidden_state_colors sthout) =
            EL r (linear_scan_hidden_state_colors sth)) /\
       linear_scan_state_colormax stout = linear_scan_state_colormax st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st:linear_scan_state`; `sth:linear_scan_hidden_state`; `l:num list`;
    `EL reg (linear_scan_hidden_state_int_beg sth)`; `forced:(num#num)list`; `reg:num`;
    `mincol:num`] spill_register_invariants) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INT_LE_REFL] THEN
    MP_TAC(SPECL [`st:linear_scan_state`; `sth:linear_scan_hidden_state`; `l:num list`;
      `EL reg (linear_scan_hidden_state_int_beg sth)`; `forced:(num#num)list`; `mincol:num`;
      `reg:num`] LSCANPAUX_gls_nomem) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `stout:linear_scan_state`
    (X_CHOOSE_THEN `sthout:linear_scan_hidden_state` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`stout:linear_scan_state`; `sthout:linear_scan_hidden_state`] THEN
  ASM_REWRITE_TAC[MEM; DE_MORGAN_THM] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* LSCANPAUX_steal_unique: the stolen register has no other active interval *)
let LSCANPAUX_steal_unique = prove
 (CASE_TERM
  `!(C:num list) cp l1 l2 (se:int) sr.
     ALL_DISTINCT (APPEND cp (MAP (\er. match er with (e,r) -> EL r C)
                                  (APPEND l1 (CONS (se,sr) l2)))) ==>
     (!e. ~MEM (e,sr) l1) /\ (!e. ~MEM (e,sr) l2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MAP_APPEND; MAP; pair_CASE; ALL_DISTINCT_APPEND; ALL_DISTINCT; MEM_APPEND;
              MEM] THEN
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; pair_CASE] THEN MESON_TAC[]);;


(* HOL4 line 3362 *)
let find_spill_invariants = prove
 (`!st sth l forbidden forced reg force mincol.
     ~MEM reg l /\
     good_linear_scan_state st sth l (EL reg (linear_scan_hidden_state_int_beg sth)) forced
       mincol /\
     reg < LENGTH (linear_scan_hidden_state_colors sth) /\
     forbidden_is_from_map_color_forced forced l (linear_scan_hidden_state_colors sth) reg
       forbidden /\
     (is_phy_var reg ==> domain (linear_scan_state_phyregs st) SUBSET domain forbidden) /\
     EL reg (linear_scan_hidden_state_int_beg sth) <=
       EL reg (linear_scan_hidden_state_int_end sth) ==>
     ?stout sthout.
       (M_success stout,sthout) =
         find_spill st forbidden reg (EL reg (linear_scan_hidden_state_int_end sth)) force
           sth /\
       good_linear_scan_state stout sthout (CONS reg l)
         (EL reg (linear_scan_hidden_state_int_beg sth)) forced mincol /\
       LENGTH (linear_scan_hidden_state_colors sthout) =
         LENGTH (linear_scan_hidden_state_colors sth) /\
       linear_scan_hidden_state_int_beg sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout = linear_scan_hidden_state_int_end sth /\
       (!r. ~MEM r (CONS reg l) ==>
            EL r (linear_scan_hidden_state_colors sthout) =
            EL r (linear_scan_hidden_state_colors sth)) /\
       (!r. MEM r l /\ is_phy_var r ==>
            EL r (linear_scan_hidden_state_colors sthout) =
            EL r (linear_scan_hidden_state_colors sth)) /\
       linear_scan_state_colormax stout = linear_scan_state_colormax st`,
    REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "regnl") (CONJUNCTS_THEN2 (LABEL_TAC "gls")
    (CONJUNCTS_THEN2 (LABEL_TAC "reglt") (CONJUNCTS_THEN2 (LABEL_TAC "fmc")
    (CONJUNCTS_THEN2 (LABEL_TAC "phyf") (LABEL_TAC "begend")))))) THEN
  MP_TAC(SPECL [`st:linear_scan_state`; `sth:linear_scan_hidden_state`; `l:num list`;
    `forced:(num#num)list`; `reg:num`; `mincol:num`] LSCANPAUX_find_spill_fallback) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "fb")] THEN
  USE_THEN "gls" (LABEL_TAC "alc" o MATCH_MP good_linear_scan_state_active_length_colors) THEN
  MP_TAC(SPECL [`forbidden:1 spt`; `sth:linear_scan_hidden_state`;
    `linear_scan_state_active st`] find_last_stealable_success) THEN
  USE_THEN "alc" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `opt:((int#num)#(int#num)list)option` (LABEL_TAC "fls")) THEN
  REWRITE_TAC(find_spill_def :: RAPROOFAUX_msimps) THEN
  USE_THEN "fls" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `p:(int#num)#(int#num)list` SUBST_ALL_TAC)
    (ISPEC `opt:((int#num)#(int#num)list)option` (cases "option")) THEN
  REWRITE_TAC[case_def "option"] THENL [USE_THEN "fb" ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `p:(int#num)#(int#num)list` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:int#num` (X_CHOOSE_THEN `newactive:(int#num)list`
    SUBST_ALL_TAC)) THEN
  MP_TAC(ISPEC `q:int#num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `stealend:int` (X_CHOOSE_THEN `stealreg:num`
    SUBST_ALL_TAC)) THEN
  REWRITE_TAC[pair_CASE] THEN COND_CASES_TAC THENL [ALL_TAC; USE_THEN "fb" ACCEPT_TAC] THEN
  USE_THEN "fls" (MP_TAC o MATCH_MP find_last_stealable_output) THEN REWRITE_TAC[SND] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nphy") (CONJUNCTS_THEN2 (LABEL_TAC "nforb")
    (X_CHOOSE_THEN `l1:(int#num)list` (X_CHOOSE_THEN `l2:(int#num)list`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC (LABEL_TAC "Aeq")))))) THEN
  USE_THEN "gls" (LSCANPAUX_LABEL_CONJS "h" o REWRITE_RULE[good_linear_scan_state_def]) THEN
  SUBGOAL_THEN `MEM (stealend:int,stealreg:num) (linear_scan_state_active st)`
    (LABEL_TAC "memst") THENL
   [USE_THEN "Aeq" (fun th -> REWRITE_TAC[th; MEM_APPEND; MEM]); ALL_TAC] THEN
  SUBGOAL_THEN `MEM (stealreg:num) l` (LABEL_TAC "stl") THENL
   [USE_THEN "h19" (MP_TAC o SPEC `(stealend:int,stealreg:num)` o REWRITE_RULE[GSYM ALL_MEM]) THEN
    USE_THEN "memst" (fun th -> REWRITE_TAC[th; pair_CASE]);
    ALL_TAC] THEN
  SUBGOAL_THEN `stealreg < LENGTH (linear_scan_hidden_state_colors sth)` (LABEL_TAC "stlt") THENL
   [USE_THEN "h4" (MP_TAC o SPEC `stealreg:num` o REWRITE_RULE[GSYM ALL_MEM]) THEN
    USE_THEN "stl" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  USE_THEN "h3" (fun h3 -> USE_THEN "Aeq" (fun aeq ->
    LABEL_TAC "uniq" (MATCH_MP LSCANPAUX_steal_unique (REWRITE_RULE[aeq] h3)))) THEN
  MP_TAC(SPECL [`st:linear_scan_state`; `sth:linear_scan_hidden_state`; `l:num list`;
    `EL reg (linear_scan_hidden_state_int_beg sth)`; `forced:(num#num)list`; `stealreg:num`;
    `mincol:num`] spill_register_FILTER_invariants) THEN
  ANTS_TAC THENL
   [USE_THEN "nphy" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "gls" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "stlt" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "h13" (MP_TAC o SPEC `stealreg:num` o REWRITE_RULE[GSYM ALL_MEM]) THEN
    USE_THEN "stl" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  USE_THEN "Aeq" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FILTER_APPEND; FILTER; pair_CASE] THEN
  USE_THEN "uniq" (fun th -> REWRITE_TAC[MATCH_MP FILTER_MEM_active (CONJUNCT1 th);
                                         MATCH_MP FILTER_MEM_active (CONJUNCT2 th)]) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:linear_scan_state` (X_CHOOSE_THEN `t1:linear_scan_hidden_state`
    (CONJUNCTS_THEN2 (LABEL_TAC "speq") (CONJUNCTS_THEN2 (LABEL_TAC "gls1")
      (CONJUNCTS_THEN2 (LABEL_TAC "t1len") (CONJUNCTS_THEN2 (LABEL_TAC "t1el")
        (CONJUNCTS_THEN2 (LABEL_TAC "s1max") (CONJUNCTS_THEN2 (LABEL_TAC "t1beg")
          (CONJUNCTS_THEN2 (LABEL_TAC "t1end") (K ALL_TAC)))))))))) THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC[colors_sub_eqn] THEN
  USE_THEN "stlt" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
  USE_THEN "speq" (fun th -> REWRITE_TAC[GSYM th; case_def "prod"; case_def "exc"]) THEN
  USE_THEN "speq" (MP_TAC o REWRITE_RULE(spill_register_def :: update_colors_eqn :: K_THM ::
    RAPROOFAUX_msimps @ LSCANPAUX_st_record)) THEN
  USE_THEN "stlt" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"; PAIR_EQ;
                                         injectivity "exc"]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "s1eq") (LABEL_TAC "t1eq")) THEN
  USE_THEN "gls1" (fun g1 -> USE_THEN "stl" (fun stl ->
    LABEL_TAC "gls2" (MATCH_MP state_invariants_remove_head (CONJ stl g1)))) THEN
  MP_TAC(SPECL [`s1:linear_scan_state`; `t1:linear_scan_hidden_state`; `l:num list`;
    `EL reg (linear_scan_hidden_state_int_beg sth)`; `forced:(num#num)list`; `reg:num`;
    `EL stealreg (linear_scan_hidden_state_colors sth)`; `forbidden:1 spt`; `mincol:num`]
    color_register_invariants) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [USE_THEN "gls2" ACCEPT_TAC; ALL_TAC] THEN
    USE_THEN "s1eq" (fun a -> USE_THEN "t1eq" (fun b -> REWRITE_TAC[a; b])) THEN
    REWRITE_TAC(K_THM :: LENGTH_LUPDATE :: LSCANPAUX_st_record @ LSCANPAUX_hs_record) THEN
    USE_THEN "reglt" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "regnl" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "begend" (fun th -> REWRITE_TAC[th]) THEN
    REPEAT CONJ_TAC THENL
     [(* forced neighbours are forbidden *)
      REWRITE_TAC[forbidden_is_from_map_color_forced_def; EL_LUPDATE] THEN
      USE_THEN "stlt" (fun th -> REWRITE_TAC[th]) THEN
      X_GEN_TAC `reg2:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        USE_THEN "nforb" (MP_TAC o REWRITE_RULE[lookup_NONE_domain]) THEN
        USE_THEN "fmc" (MP_TAC o SPEC `stealreg:num` o
          REWRITE_RULE[forbidden_is_from_map_color_forced_def]) THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[];
        USE_THEN "fmc" (MP_TAC o SPEC `reg2:num` o
          REWRITE_RULE[forbidden_is_from_map_color_forced_def]) THEN
        ASM_REWRITE_TAC[]];
      (* the stolen colour is not forbidden *)
      USE_THEN "nforb" (ACCEPT_TAC o REWRITE_RULE[lookup_NONE_domain]);
      (* phyregs *)
      USE_THEN "phyf" ACCEPT_TAC;
      (* the stolen colour is free *)
      SUBGOAL_THEN `(!(e:int) r. MEM (e,r) (l1:(int#num)list) ==> ~(r = stealreg)) /\
                    (!(e:int) r. MEM (e,r) (l2:(int#num)list) ==> ~(r = stealreg))`
        (CONJUNCTS_THEN2 (LABEL_TAC "nr1") (LABEL_TAC "nr2")) THENL
       [USE_THEN "uniq" MP_TAC THEN MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[MAP_APPEND] THEN
      USE_THEN "nr1" (fun th -> REWRITE_TAC[MATCH_MP LSCANPAUX_MAP_PAIR_LUPDATE th]) THEN
      USE_THEN "nr2" (fun th -> REWRITE_TAC[MATCH_MP LSCANPAUX_MAP_PAIR_LUPDATE th]) THEN
      USE_THEN "h3" MP_TAC THEN USE_THEN "Aeq" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[MAP_APPEND; MAP; pair_CASE; APPEND_ASSOC; LSCANPAUX_ALL_DISTINCT_MIDDLE] THEN
      SIMP_TAC[];
      (* the stolen colour is below colornum *)
      USE_THEN "h9" (MP_TAC o SPEC `(stealend:int,stealreg:num)` o
        REWRITE_RULE[GSYM ALL_MEM]) THEN
      USE_THEN "memst" (fun th -> REWRITE_TAC[th; pair_CASE]);
      (* mincol *)
      USE_THEN "h22" (MP_TAC o CONJUNCT2 o REWRITE_RULE[ALL_APPEND]) THEN
      REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; o_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `stealreg:num`) THEN
      USE_THEN "stl" (fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `stout:linear_scan_state`
    (X_CHOOSE_THEN `sthout:linear_scan_hidden_state`
      (CONJUNCTS_THEN2 (LABEL_TAC "creq") (CONJUNCTS_THEN2 (LABEL_TAC "glsout")
        (CONJUNCTS_THEN2 (LABEL_TAC "lenout") (CONJUNCTS_THEN2 (LABEL_TAC "begout")
          (CONJUNCTS_THEN2 (LABEL_TAC "endout") (CONJUNCTS_THEN2 (LABEL_TAC "elout")
            (LABEL_TAC "maxout"))))))))) THEN
  MAP_EVERY EXISTS_TAC [`stout:linear_scan_state`; `sthout:linear_scan_hidden_state`] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "creq" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "t1end" (fun th -> REWRITE_TAC[th]);
    USE_THEN "glsout" ACCEPT_TAC;
    USE_THEN "lenout" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "t1len" ACCEPT_TAC;
    USE_THEN "begout" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "t1beg" ACCEPT_TAC;
    USE_THEN "endout" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "t1end" ACCEPT_TAC;
    X_GEN_TAC `r:num` THEN REWRITE_TAC[MEM; DE_MORGAN_THM] THEN STRIP_TAC THEN
    USE_THEN "elout" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `~(r:num = reg)`))]) THEN
    CONV_TAC SYM_CONV THEN USE_THEN "t1el" MATCH_MP_TAC THEN
    DISCH_TAC THEN UNDISCH_TAC `~MEM (r:num) l` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(r:num = reg)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `MEM (r:num) l` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "elout" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `~(r:num = reg)`))]) THEN
    CONV_TAC SYM_CONV THEN USE_THEN "t1el" MATCH_MP_TAC THEN
    DISCH_TAC THEN UNDISCH_TAC `is_phy_var r` THEN ASM_REWRITE_TAC[];
    USE_THEN "maxout" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "s1max" ACCEPT_TAC]);;


(* LSCANPAUX_gls_colorpool_filter: removing colours from the pool *)
let LSCANPAUX_gls_colorpool_filter = prove
 (`!st sth l pos forced mincol.
     good_linear_scan_state st sth l pos forced mincol ==>
     !Q. good_linear_scan_state (linear_scan_state_colorpool_fupd (FILTER Q) st)
           sth l pos forced mincol`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(LSCANPAUX_LABEL_CONJS "h" o REWRITE_RULE[good_linear_scan_state_def]) THEN
  GEN_TAC THEN LSCANPAUX_GLS_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [USE_THEN "h3" (fun th -> MATCH_MP_TAC ALL_DISTINCT_IS_SPARSE_SUBLIST THEN
      EXISTS_TAC (rand(concl th)) THEN REWRITE_TAC[th]) THEN
    MATCH_MP_TAC IS_SPARSE_SUBLIST_APPEND_RIGHT THEN MATCH_ACCEPT_TAC FILTER_IS_SPARSE_SUBLIST;
    USE_THEN "h8" MP_TAC THEN REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN MESON_TAC[];
    USE_THEN "h22" MP_TAC THEN REWRITE_TAC[ALL_APPEND; GSYM ALL_MEM; MEM_FILTER] THEN
    MESON_TAC[]]);;

(* LSCANPAUX_gls_colorpool_cons: a state whose pool has an extra colour *)
let LSCANPAUX_gls_colorpool_cons = prove
 (CASE_TERM
  `!col st sth l pos forced mincol.
     good_linear_scan_state (linear_scan_state_colorpool_fupd (\cp. CONS col cp) st)
       sth l pos forced mincol ==>
     good_linear_scan_state st sth l pos forced mincol /\
     ~MEM col (APPEND (linear_scan_state_colorpool st)
                 (MAP (\er. match er with
                              (e,r) -> EL r (linear_scan_hidden_state_colors sth))
                      (linear_scan_state_active st))) /\
     mincol <= col`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(LSCANPAUX_LABEL_CONJS "h" o
    REWRITE_RULE(good_linear_scan_state_def :: K_THM :: LSCANPAUX_st_record)) THEN
  CONJ_TAC THENL
   [LSCANPAUX_GLS_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [USE_THEN "h3" MP_TAC THEN REWRITE_TAC[APPEND; ALL_DISTINCT] THEN SIMP_TAC[];
      USE_THEN "h8" MP_TAC THEN REWRITE_TAC[ALL] THEN SIMP_TAC[];
      USE_THEN "h22" MP_TAC THEN REWRITE_TAC[APPEND; ALL] THEN SIMP_TAC[]];
    CONJ_TAC THENL
     [USE_THEN "h3" MP_TAC THEN REWRITE_TAC[APPEND; ALL_DISTINCT] THEN SIMP_TAC[];
      USE_THEN "h22" MP_TAC THEN REWRITE_TAC[APPEND; ALL] THEN SIMP_TAC[]]]);;

(* HOL4 line 3478 *)
let linear_reg_alloc_step_aux_invariants = prove
 (`!st sth l preferred (forbidden:1 spt) forced reg force mincol.
     ~MEM reg l /\
     good_linear_scan_state st sth l (EL reg (linear_scan_hidden_state_int_beg sth)) forced
       mincol /\
     reg < LENGTH (linear_scan_hidden_state_colors sth) /\
     forbidden_is_from_map_color_forced forced l (linear_scan_hidden_state_colors sth) reg
       forbidden /\
     (is_phy_var reg ==> domain (linear_scan_state_phyregs st) SUBSET domain forbidden) /\
     domain forbidden SUBSET {EL r (linear_scan_hidden_state_colors sth) | r | MEM r l} /\
     EL reg (linear_scan_hidden_state_int_beg sth) <=
       EL reg (linear_scan_hidden_state_int_end sth) ==>
     ?stout sthout.
       (M_success stout,sthout) =
         linear_reg_alloc_step_aux st forbidden preferred reg
           (EL reg (linear_scan_hidden_state_int_end sth)) force sth /\
       good_linear_scan_state stout sthout (CONS reg l)
         (EL reg (linear_scan_hidden_state_int_beg sth)) forced mincol /\
       LENGTH (linear_scan_hidden_state_colors sthout) =
         LENGTH (linear_scan_hidden_state_colors sth) /\
       linear_scan_hidden_state_int_beg sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout = linear_scan_hidden_state_int_end sth /\
       (!r. ~MEM r (CONS reg l) ==>
            EL r (linear_scan_hidden_state_colors sthout) =
            EL r (linear_scan_hidden_state_colors sth)) /\
       (!r. MEM r l /\ is_phy_var r ==>
            EL r (linear_scan_hidden_state_colors sthout) =
            EL r (linear_scan_hidden_state_colors sth)) /\
       linear_scan_state_colormax stout = linear_scan_state_colormax st`,
    REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "regnl") (CONJUNCTS_THEN2 (LABEL_TAC "gls")
    (CONJUNCTS_THEN2 (LABEL_TAC "reglt") (CONJUNCTS_THEN2 (LABEL_TAC "fmc")
    (CONJUNCTS_THEN2 (LABEL_TAC "phyf") (CONJUNCTS_THEN2 (LABEL_TAC "forbsub")
      (LABEL_TAC "begend"))))))) THEN
  REWRITE_TAC[linear_reg_alloc_step_aux_def; LET_DEF; LET_END_DEF] THEN
  CASES_ON `find_color_in_list (FILTER (\c. MEM c (linear_scan_state_colorpool st)) preferred)
              forbidden` THEN
  REWRITE_TAC[case_def "option"] THENL
   [(* no preferred colour: find_color *)
    MP_TAC(ISPEC `find_color st forbidden` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `st1:linear_scan_state` (X_CHOOSE_THEN `oc:num option`
      (LABEL_TAC "fc"))) THEN
    USE_THEN "fc" (fun th -> REWRITE_TAC[th; pair_CASE]) THEN
    DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `col:num` SUBST_ALL_TAC)
      (ISPEC `oc:num option` (cases "option")) THEN
    REWRITE_TAC[case_def "option"] THENL
     [(* no colour: spill *)
      SUBGOAL_THEN `st1:linear_scan_state = st` SUBST_ALL_TAC THENL
       [USE_THEN "fc" MP_TAC THEN REWRITE_TAC[find_color_def] THEN
        CASES_ON `find_color_in_list (linear_scan_state_colorpool st) forbidden` THEN
        REWRITE_TAC[case_def "option"] THENL
         [REWRITE_TAC[find_color_in_colornum_def] THEN COND_CASES_TAC THEN
          REWRITE_TAC[PAIR_EQ; option_DISTINCT] THEN MESON_TAC[];
          MP_TAC(ISPEC `a:num#num list` PAIR_SURJECTIVE) THEN
          DISCH_THEN(X_CHOOSE_THEN `c:num` (X_CHOOSE_THEN `rest:num list` SUBST1_TAC)) THEN
          REWRITE_TAC[pair_CASE; PAIR_EQ; option_DISTINCT]];
        ALL_TAC] THEN
      MP_TAC(SPECL [`st:linear_scan_state`; `sth:linear_scan_hidden_state`; `l:num list`;
        `forbidden:1 spt`; `forced:(num#num)list`; `reg:num`; `force:bool`; `mincol:num`]
        find_spill_invariants) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
      (* a free colour *)
      MP_TAC(SPECL [`st:linear_scan_state`; `forbidden:1 spt`; `st1:linear_scan_state`;
        `col:num`; `sth:linear_scan_hidden_state`; `l:num list`;
        `EL reg (linear_scan_hidden_state_int_beg sth)`; `forced:(num#num)list`;
        `mincol:num`] find_color_invariants) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "g1") (CONJUNCTS_THEN2 (LABEL_TAC "c1")
        (CONJUNCTS_THEN2 (LABEL_TAC "c2") (LABEL_TAC "steq")))) THEN
      USE_THEN "g1" (fun th -> MP_TAC(MATCH_MP LSCANPAUX_gls_colorpool_cons th)) THEN
      DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "g2") (CONJUNCTS_THEN2 (LABEL_TAC "nm")
        (LABEL_TAC "mc"))) THEN
      USE_THEN "steq" (fun th -> LABEL_TAC "phy1" (REWRITE_RULE(K_THM :: LSCANPAUX_st_record)
        (AP_TERM `linear_scan_state_phyregs` th))) THEN
      USE_THEN "steq" (fun th -> LABEL_TAC "max1" (REWRITE_RULE(K_THM :: LSCANPAUX_st_record)
        (AP_TERM `linear_scan_state_colormax` th))) THEN
      REMOVE_THEN "steq" (K ALL_TAC) THEN
      MP_TAC(SPECL [`st1:linear_scan_state`; `sth:linear_scan_hidden_state`; `l:num list`;
        `EL reg (linear_scan_hidden_state_int_beg sth)`; `forced:(num#num)list`; `reg:num`;
        `col:num`; `forbidden:1 spt`; `mincol:num`] color_register_invariants) THEN
      ANTS_TAC THENL
       [USE_THEN "phy1" (fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `stout:linear_scan_state`
        (X_CHOOSE_THEN `sthout:linear_scan_hidden_state` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`stout:linear_scan_state`; `sthout:linear_scan_hidden_state`] THEN
      ASM_REWRITE_TAC[MEM; DE_MORGAN_THM] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]];
    (* a preferred colour *)
    MP_TAC(ISPEC `a:num#num list` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `col:num` (X_CHOOSE_THEN `rest:num list` SUBST_ALL_TAC)) THEN
    REWRITE_TAC[pair_CASE] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP find_color_in_list_output) THEN
    REWRITE_TAC[MEM_FILTER] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "colcp") (K ALL_TAC))
      (CONJUNCTS_THEN2 (LABEL_TAC "colnf") (K ALL_TAC))) THEN
    USE_THEN "gls" (LABEL_TAC "g2" o ISPEC `\x:num. ~(col = x)` o
      MATCH_MP LSCANPAUX_gls_colorpool_filter) THEN
    USE_THEN "gls" (LSCANPAUX_LABEL_CONJS "h" o REWRITE_RULE[good_linear_scan_state_def]) THEN
    MP_TAC(SPECL [`linear_scan_state_colorpool_fupd (FILTER (\x:num. ~(col = x))) st`;
      `sth:linear_scan_hidden_state`; `l:num list`;
      `EL reg (linear_scan_hidden_state_int_beg sth)`; `forced:(num#num)list`; `reg:num`;
      `col:num`; `forbidden:1 spt`; `mincol:num`] color_register_invariants) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [USE_THEN "g2" ACCEPT_TAC; ALL_TAC] THEN
      REWRITE_TAC(K_THM :: LSCANPAUX_st_record) THEN
      USE_THEN "fmc" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "colnf" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "phyf" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "begend" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "reglt" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "regnl" (fun th -> REWRITE_TAC[th]) THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "h3" MP_TAC THEN
        REWRITE_TAC[MEM_APPEND; MEM_FILTER; ALL_DISTINCT_APPEND] THEN
        USE_THEN "colcp" MP_TAC THEN MESON_TAC[];
        USE_THEN "h8" (MP_TAC o SPEC `col:num` o REWRITE_RULE[GSYM ALL_MEM]) THEN
        USE_THEN "colcp" (fun th -> REWRITE_TAC[th]);
        USE_THEN "h22" (MP_TAC o SPEC `col:num` o REWRITE_RULE[GSYM ALL_MEM]) THEN
        USE_THEN "colcp" (fun th -> REWRITE_TAC[th; MEM_APPEND])];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `stout:linear_scan_state`
      (X_CHOOSE_THEN `sthout:linear_scan_hidden_state` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`stout:linear_scan_state`; `sthout:linear_scan_hidden_state`] THEN
    ASM_REWRITE_TAC[MEM; DE_MORGAN_THM] THEN
    REWRITE_TAC(K_THM :: LSCANPAUX_st_record) THEN
    CONJ_TAC THEN REPEAT STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;


(* HOL4 line 3542 *)
let st_ex_MAP_colors_sub = prove
 (`!l sth.
     ALL (\r. r < LENGTH (linear_scan_hidden_state_colors sth)) l ==>
     st_ex_MAP colors_sub l sth =
       (M_success (MAP (\r. EL r (linear_scan_hidden_state_colors sth)) l),sth)`,
    LIST_INDUCT_TAC THEN REWRITE_TAC(st_ex_MAP_def :: MAP :: ALL :: RAPROOFAUX_msimps) THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC(colors_sub_eqn :: case_def "prod" :: case_def "exc" :: RAPROOFAUX_msimps));;

(* HOL4 line 3550 *)
let phystack_on_stack_def = cake_def
  `phystack_on_stack l st sth <=>
     !r. MEM r l /\ is_phy_var r /\ 2 * linear_scan_state_colormax st <= r ==>
         linear_scan_state_colormax st <= EL r (linear_scan_hidden_state_colors sth)`;;
(* LSCANPAUX_phystack_step: phystack_on_stack after one allocation step *)
let LSCANPAUX_phystack_step = prove
 (`!st sth l stout sthout reg.
     phystack_on_stack l st sth /\
     linear_scan_state_colormax stout = linear_scan_state_colormax st /\
     (!r. MEM r l /\ is_phy_var r ==>
          EL r (linear_scan_hidden_state_colors sthout) =
          EL r (linear_scan_hidden_state_colors sth)) /\
     (is_phy_var reg /\ 2 * linear_scan_state_colormax st <= reg ==>
      linear_scan_state_colormax st <= EL reg (linear_scan_hidden_state_colors sthout)) ==>
     phystack_on_stack (CONS reg l) stout sthout`,
  REPEAT GEN_TAC THEN REWRITE_TAC[phystack_on_stack_def; MEM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:num` THEN
  ASM_CASES_TAC `r:num = reg` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `EL r (linear_scan_hidden_state_colors sthout) =
                EL r (linear_scan_hidden_state_colors sth)` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `sthout:linear_scan_hidden_state`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `2 * linear_scan_state_colormax st`)) (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

(* LSCANPAUX_pass1_spill: the spilling branches of the first pass *)
let LSCANPAUX_pass1_spill = prove
 (`!st st1 sth l forced reg mincol.
     ~MEM reg l /\
     good_linear_scan_state st1 sth l (EL reg (linear_scan_hidden_state_int_beg sth)) forced
       mincol /\
     linear_scan_state_colormax st1 = linear_scan_state_colormax st /\
     reg < LENGTH (linear_scan_hidden_state_colors sth) /\
     (is_phy_var reg ==> 2 * linear_scan_state_colormax st <= reg) ==>
     ?stout sthout.
       (M_success stout,sthout) = spill_register st1 reg sth /\
       good_linear_scan_state stout sthout (CONS reg l)
         (EL reg (linear_scan_hidden_state_int_beg sth)) forced mincol /\
       LENGTH (linear_scan_hidden_state_colors sthout) =
         LENGTH (linear_scan_hidden_state_colors sth) /\
       linear_scan_hidden_state_int_beg sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout = linear_scan_hidden_state_int_end sth /\
       (!r. ~MEM r (CONS reg l) ==>
            EL r (linear_scan_hidden_state_colors sthout) =
            EL r (linear_scan_hidden_state_colors sth)) /\
       (!r. MEM r l /\ is_phy_var r ==>
            EL r (linear_scan_hidden_state_colors sthout) =
            EL r (linear_scan_hidden_state_colors sth)) /\
       (phystack_on_stack l st sth ==> phystack_on_stack (CONS reg l) stout sthout) /\
       linear_scan_state_colormax stout = linear_scan_state_colormax st`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`st1:linear_scan_state`; `sth:linear_scan_hidden_state`; `l:num list`;
    `EL reg (linear_scan_hidden_state_int_beg sth)`; `forced:(num#num)list`; `reg:num`;
    `mincol:num`] spill_register_invariants) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INT_LE_REFL] THEN
    MP_TAC(SPECL [`st1:linear_scan_state`; `sth:linear_scan_hidden_state`; `l:num list`;
      `EL reg (linear_scan_hidden_state_int_beg sth)`; `forced:(num#num)list`; `mincol:num`;
      `reg:num`] LSCANPAUX_gls_nomem) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `stout:linear_scan_state`
    (X_CHOOSE_THEN `sthout:linear_scan_hidden_state` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`stout:linear_scan_state`; `sthout:linear_scan_hidden_state`] THEN
  SUBGOAL_THEN `!r. ~(r = reg) ==>
                  EL r (linear_scan_hidden_state_colors sthout) =
                  EL r (linear_scan_hidden_state_colors sth)` (LABEL_TAC "ne") THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!r:num. MEM r l ==> ~(r = reg)` (LABEL_TAC "nl") THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MEM; DE_MORGAN_THM] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "ne" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "ne" MATCH_MP_TAC THEN
    USE_THEN "nl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    MATCH_MP_TAC(SPECL [`st:linear_scan_state`; `sth:linear_scan_hidden_state`]
      LSCANPAUX_phystack_step) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "ne" MATCH_MP_TAC THEN
      USE_THEN "nl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]]]);;

(* LSCANPAUX_forced_forbidden: the forbidden set computed from the forced edges *)
let LSCANPAUX_forced_forbidden = prove
 (`!forced l reg fa (C:num list).
     forbidden_is_from_forced_list forced l reg fa /\ ALL (\r. MEM r l) fa ==>
     forbidden_is_from_map_color_forced forced l C reg
       (fromAList (MAP (\c. (c,one)) (MAP (\r. EL r C) fa))) /\
     domain (fromAList (MAP (\c. (c,one)) (MAP (\r. EL r C) fa))) SUBSET
       {EL r C | r | MEM r l}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[forbidden_is_from_map_color_forced_def; forbidden_is_from_forced_list_def;
              domain_fromAList] THEN
  SUBGOAL_THEN `!m. MAP FST (MAP (\c:num. (c,one)) m) = m` (fun th -> REWRITE_TAC[th]) THENL
   [LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP]; ALL_TAC] THEN
  REWRITE_TAC[IN_SET_OF_LIST; MEM_MAP; SUBSET; IN_ELIM_THM; GSYM ALL_MEM] THEN MESON_TAC[]);;

(* HOL4 line 3555 *)
let linear_reg_alloc_step_pass1_invariants = prove
 (`!st sth l moves forced_adj forced reg pos mincol.
     ~MEM reg l /\
     good_linear_scan_state st sth l pos forced mincol /\
     pos <= EL reg (linear_scan_hidden_state_int_beg sth) /\
     reg < LENGTH (linear_scan_hidden_state_colors sth) /\
     forbidden_is_from_forced_list forced l reg (misc_the [] (lookup reg forced_adj)) /\
     ALL (\r. MEM r l) (misc_the [] (lookup reg forced_adj)) /\
     ALL (\r. r < LENGTH (linear_scan_hidden_state_colors sth)) (misc_the [] (lookup reg forced_adj)) /\
     ALL (\r. r < LENGTH (linear_scan_hidden_state_colors sth)) (misc_the [] (lookup reg moves)) /\
     EL reg (linear_scan_hidden_state_int_beg sth) <=
       EL reg (linear_scan_hidden_state_int_end sth) ==>
     ?stout sthout.
       (M_success stout,sthout) = linear_reg_alloc_step_pass1 forced_adj moves st reg sth /\
       good_linear_scan_state stout sthout (CONS reg l)
         (EL reg (linear_scan_hidden_state_int_beg sth)) forced mincol /\
       LENGTH (linear_scan_hidden_state_colors sthout) =
         LENGTH (linear_scan_hidden_state_colors sth) /\
       linear_scan_hidden_state_int_beg sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout = linear_scan_hidden_state_int_end sth /\
       (!r. ~MEM r (CONS reg l) ==>
            EL r (linear_scan_hidden_state_colors sthout) =
            EL r (linear_scan_hidden_state_colors sth)) /\
       (!r. MEM r l /\ is_phy_var r ==>
            EL r (linear_scan_hidden_state_colors sthout) =
            EL r (linear_scan_hidden_state_colors sth)) /\
       (phystack_on_stack l st sth ==> phystack_on_stack (CONS reg l) stout sthout) /\
       linear_scan_state_colormax stout = linear_scan_state_colormax st`,
    REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "regnl") (CONJUNCTS_THEN2 (LABEL_TAC "gls")
    (CONJUNCTS_THEN2 (LABEL_TAC "posle") (CONJUNCTS_THEN2 (LABEL_TAC "reglt")
    (CONJUNCTS_THEN2 (LABEL_TAC "ffl") (CONJUNCTS_THEN2 (LABEL_TAC "fadjl")
    (CONJUNCTS_THEN2 (LABEL_TAC "fadjlt") (CONJUNCTS_THEN2 (LABEL_TAC "movlt")
      (LABEL_TAC "begend"))))))))) THEN
  USE_THEN "gls" (LSCANPAUX_LABEL_CONJS "h" o REWRITE_RULE[good_linear_scan_state_def]) THEN
  SUBGOAL_THEN `reg < LENGTH (linear_scan_hidden_state_int_beg sth) /\
                reg < LENGTH (linear_scan_hidden_state_int_end sth)`
    (CONJUNCTS_THEN2 (LABEL_TAC "rb") (LABEL_TAC "re")) THENL
   [USE_THEN "h1" (fun a -> USE_THEN "h2" (fun b -> REWRITE_TAC[a; b])) THEN
    USE_THEN "reglt" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(SPECL [`EL reg (linear_scan_hidden_state_int_beg sth)`; `st:linear_scan_state`;
    `sth:linear_scan_hidden_state`; `l:num list`; `pos:int`; `forced:(num#num)list`;
    `mincol:num`] remove_inactive_intervals_invariants) THEN
  ANTS_TAC THENL
   [USE_THEN "gls" (fun a -> USE_THEN "posle" (fun b -> REWRITE_TAC[a; b])); ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `st1:linear_scan_state` (CONJUNCTS_THEN2 (LABEL_TAC "rii")
    (CONJUNCTS_THEN2 (LABEL_TAC "gls1") (LABEL_TAC "max1")))) THEN
  REWRITE_TAC(linear_reg_alloc_step_pass1_def :: RAPROOFAUX_msimps) THEN
  REWRITE_TAC[int_beg_sub_eqn; int_end_sub_eqn] THEN
  USE_THEN "rb" (fun a -> USE_THEN "re" (fun b ->
    REWRITE_TAC[a; b; case_def "prod"; case_def "exc"])) THEN
  REMOVE_THEN "rii" (fun th -> REWRITE_TAC[GSYM th; case_def "prod"; case_def "exc"]) THEN
  ASM_CASES_TAC `is_stack_var reg` THENL
   [POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
    MATCH_MP_TAC LSCANPAUX_pass1_spill THEN
    USE_THEN "regnl" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "gls1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "max1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "reglt" (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `is_stack_var reg` THEN
    MP_TAC(SPEC `reg:num` convention_partitions) THEN MESON_TAC[];
    ALL_TAC] THEN
  POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
  USE_THEN "fadjlt" (fun th -> REWRITE_TAC[MATCH_MP st_ex_MAP_colors_sub th]) THEN
  REWRITE_TAC[case_def "prod"; case_def "exc"; LET_DEF; LET_END_DEF] THEN
  MP_TAC(SPECL [`forced:(num#num)list`; `l:num list`; `reg:num`;
    `misc_the [] (lookup reg forced_adj):num list`; `linear_scan_hidden_state_colors sth`]
    LSCANPAUX_forced_forbidden) THEN
  ANTS_TAC THENL
   [USE_THEN "ffl" (fun a -> USE_THEN "fadjl" (fun b -> REWRITE_TAC[a; b])); ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ffm") (LABEL_TAC "ffsub")) THEN
  USE_THEN "gls1" (LSCANPAUX_LABEL_CONJS "g" o REWRITE_RULE[good_linear_scan_state_def]) THEN
  ASM_CASES_TAC `is_phy_var reg` THENL
   [POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
    ASM_CASES_TAC `reg < 2 * linear_scan_state_colormax st1` THENL
     [POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
      MP_TAC(SPECL [`st1:linear_scan_state`; `sth:linear_scan_hidden_state`; `l:num list`;
        `[]:num list`;
        `sptree_union (linear_scan_state_phyregs st1)
           (fromAList (MAP (\c. (c,one)) (MAP (\r. EL r (linear_scan_hidden_state_colors sth))
              (misc_the [] (lookup reg forced_adj)))))`;
        `forced:(num#num)list`; `reg:num`; `T`; `mincol:num`]
        linear_reg_alloc_step_aux_invariants) THEN
      ANTS_TAC THENL
       [USE_THEN "regnl" (fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "gls1" (fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "reglt" (fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "begend" (fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[domain_union] THEN REPEAT CONJ_TAC THENL
         [USE_THEN "ffm" MP_TAC THEN
          REWRITE_TAC[forbidden_is_from_map_color_forced_def; domain_union; IN_UNION] THEN
          MESON_TAC[];
          SET_TAC[];
          REWRITE_TAC[UNION_SUBSET] THEN USE_THEN "ffsub" (fun th -> REWRITE_TAC[th]) THEN
          USE_THEN "g6" (fun th -> REWRITE_TAC[th]) THEN
          REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `stout:linear_scan_state`
        (X_CHOOSE_THEN `sthout:linear_scan_hidden_state` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`stout:linear_scan_state`; `sthout:linear_scan_hidden_state`] THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MATCH_MP_TAC(SPECL [`st:linear_scan_state`; `sth:linear_scan_hidden_state`]
        LSCANPAUX_phystack_step) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `reg < 2 * linear_scan_state_colormax st1` THEN
      USE_THEN "max1" (fun th -> REWRITE_TAC[th]) THEN ARITH_TAC;
      POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
      MATCH_MP_TAC LSCANPAUX_pass1_spill THEN
      USE_THEN "regnl" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "gls1" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "max1" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "reglt" (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `~(reg < 2 * linear_scan_state_colormax st1)` THEN
      USE_THEN "max1" (fun th -> REWRITE_TAC[th]) THEN ARITH_TAC];
    POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
    USE_THEN "movlt" (fun th -> REWRITE_TAC[MATCH_MP st_ex_MAP_colors_sub th]) THEN
    REWRITE_TAC[case_def "prod"; case_def "exc"] THEN
    MP_TAC(SPECL [`st1:linear_scan_state`; `sth:linear_scan_hidden_state`; `l:num list`;
      `MAP (\r. EL r (linear_scan_hidden_state_colors sth)) (misc_the [] (lookup reg moves))`;
      `fromAList (MAP (\c. (c,one)) (MAP (\r. EL r (linear_scan_hidden_state_colors sth))
         (misc_the [] (lookup reg forced_adj))))`;
      `forced:(num#num)list`; `reg:num`; `F`; `mincol:num`]
      linear_reg_alloc_step_aux_invariants) THEN
    ANTS_TAC THENL
     [USE_THEN "regnl" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "gls1" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "reglt" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "begend" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "ffm" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "ffsub" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `stout:linear_scan_state`
      (X_CHOOSE_THEN `sthout:linear_scan_hidden_state` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`stout:linear_scan_state`; `sthout:linear_scan_hidden_state`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC(SPECL [`st:linear_scan_state`; `sth:linear_scan_hidden_state`]
      LSCANPAUX_phystack_step) THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 3636 *)
let linear_reg_alloc_step_pass2_invariants = prove
 (`!st sth l moves forced_adj forced reg pos mincol.
     ~MEM reg l /\
     good_linear_scan_state st sth l pos forced mincol /\
     pos <= EL reg (linear_scan_hidden_state_int_beg sth) /\
     reg < LENGTH (linear_scan_hidden_state_colors sth) /\
     forbidden_is_from_forced_list forced l reg (misc_the [] (lookup reg forced_adj)) /\
     ALL (\r. MEM r l) (misc_the [] (lookup reg forced_adj)) /\
     ALL (\r. r < LENGTH (linear_scan_hidden_state_colors sth)) (misc_the [] (lookup reg forced_adj)) /\
     ALL (\r. r < LENGTH (linear_scan_hidden_state_colors sth)) (misc_the [] (lookup reg moves)) /\
     EL reg (linear_scan_hidden_state_int_beg sth) <=
       EL reg (linear_scan_hidden_state_int_end sth) ==>
     ?stout sthout.
       (M_success stout,sthout) = linear_reg_alloc_step_pass2 forced_adj moves st reg sth /\
       good_linear_scan_state stout sthout (CONS reg l)
         (EL reg (linear_scan_hidden_state_int_beg sth)) forced mincol /\
       LENGTH (linear_scan_hidden_state_colors sthout) =
         LENGTH (linear_scan_hidden_state_colors sth) /\
       linear_scan_hidden_state_int_beg sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout = linear_scan_hidden_state_int_end sth /\
       (!r. ~MEM r (CONS reg l) ==>
            EL r (linear_scan_hidden_state_colors sthout) =
            EL r (linear_scan_hidden_state_colors sth)) /\
       (!r. MEM r l /\ is_phy_var r ==>
            EL r (linear_scan_hidden_state_colors sthout) =
            EL r (linear_scan_hidden_state_colors sth)) /\
       linear_scan_state_colormax stout = linear_scan_state_colormax st`,
    REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "regnl") (CONJUNCTS_THEN2 (LABEL_TAC "gls")
    (CONJUNCTS_THEN2 (LABEL_TAC "posle") (CONJUNCTS_THEN2 (LABEL_TAC "reglt")
    (CONJUNCTS_THEN2 (LABEL_TAC "ffl") (CONJUNCTS_THEN2 (LABEL_TAC "fadjl")
    (CONJUNCTS_THEN2 (LABEL_TAC "fadjlt") (CONJUNCTS_THEN2 (LABEL_TAC "movlt")
      (LABEL_TAC "begend"))))))))) THEN
  USE_THEN "gls" (LSCANPAUX_LABEL_CONJS "h" o REWRITE_RULE[good_linear_scan_state_def]) THEN
  SUBGOAL_THEN `reg < LENGTH (linear_scan_hidden_state_int_beg sth) /\
                reg < LENGTH (linear_scan_hidden_state_int_end sth)`
    (CONJUNCTS_THEN2 (LABEL_TAC "rb") (LABEL_TAC "re")) THENL
   [USE_THEN "h1" (fun a -> USE_THEN "h2" (fun b -> REWRITE_TAC[a; b])) THEN
    USE_THEN "reglt" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(SPECL [`EL reg (linear_scan_hidden_state_int_beg sth)`; `st:linear_scan_state`;
    `sth:linear_scan_hidden_state`; `l:num list`; `pos:int`; `forced:(num#num)list`;
    `mincol:num`] remove_inactive_intervals_invariants) THEN
  ANTS_TAC THENL
   [USE_THEN "gls" (fun a -> USE_THEN "posle" (fun b -> REWRITE_TAC[a; b])); ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `st1:linear_scan_state` (CONJUNCTS_THEN2 (LABEL_TAC "rii")
    (CONJUNCTS_THEN2 (LABEL_TAC "gls1") (LABEL_TAC "max1")))) THEN
  REWRITE_TAC(linear_reg_alloc_step_pass2_def :: RAPROOFAUX_msimps) THEN
  REWRITE_TAC[int_beg_sub_eqn; int_end_sub_eqn] THEN
  USE_THEN "rb" (fun a -> USE_THEN "re" (fun b ->
    REWRITE_TAC[a; b; case_def "prod"; case_def "exc"])) THEN
  REMOVE_THEN "rii" (fun th -> REWRITE_TAC[GSYM th; case_def "prod"; case_def "exc"]) THEN
  USE_THEN "fadjlt" (fun th -> REWRITE_TAC[MATCH_MP st_ex_MAP_colors_sub th]) THEN
  REWRITE_TAC[case_def "prod"; case_def "exc"] THEN
  USE_THEN "movlt" (fun th -> REWRITE_TAC[MATCH_MP st_ex_MAP_colors_sub th]) THEN
  REWRITE_TAC[case_def "prod"; case_def "exc"; LET_DEF; LET_END_DEF] THEN
  MP_TAC(SPECL [`forced:(num#num)list`; `l:num list`; `reg:num`;
    `misc_the [] (lookup reg forced_adj):num list`; `linear_scan_hidden_state_colors sth`]
    LSCANPAUX_forced_forbidden) THEN
  ANTS_TAC THENL
   [USE_THEN "ffl" (fun a -> USE_THEN "fadjl" (fun b -> REWRITE_TAC[a; b])); ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ffm") (LABEL_TAC "ffsub")) THEN
  USE_THEN "gls1" (LSCANPAUX_LABEL_CONJS "g" o REWRITE_RULE[good_linear_scan_state_def]) THEN
  ASM_CASES_TAC `is_phy_var reg` THEN POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th)
  THENL
   [MP_TAC(SPECL [`st1:linear_scan_state`; `sth:linear_scan_hidden_state`; `l:num list`;
      `[]:num list`;
      `sptree_union (linear_scan_state_phyregs st1)
         (fromAList (MAP (\c. (c,one)) (MAP (\r. EL r (linear_scan_hidden_state_colors sth))
            (misc_the [] (lookup reg forced_adj)))))`;
      `forced:(num#num)list`; `reg:num`; `F`; `mincol:num`]
      linear_reg_alloc_step_aux_invariants) THEN
    ANTS_TAC THENL
     [USE_THEN "regnl" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "gls1" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "reglt" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "begend" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[domain_union] THEN REPEAT CONJ_TAC THENL
       [USE_THEN "ffm" MP_TAC THEN
        REWRITE_TAC[forbidden_is_from_map_color_forced_def; domain_union; IN_UNION] THEN
        MESON_TAC[];
        SET_TAC[];
        REWRITE_TAC[UNION_SUBSET] THEN USE_THEN "ffsub" (fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "g6" (fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
      ALL_TAC];
    MP_TAC(SPECL [`st1:linear_scan_state`; `sth:linear_scan_hidden_state`; `l:num list`;
      `MAP (\r. EL r (linear_scan_hidden_state_colors sth)) (misc_the [] (lookup reg moves))`;
      `fromAList (MAP (\c. (c,one)) (MAP (\r. EL r (linear_scan_hidden_state_colors sth))
         (misc_the [] (lookup reg forced_adj))))`;
      `forced:(num#num)list`; `reg:num`; `F`; `mincol:num`]
      linear_reg_alloc_step_aux_invariants) THEN
    ANTS_TAC THENL
     [USE_THEN "regnl" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "gls1" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "reglt" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "begend" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "ffm" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "ffsub" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC]] THEN
  DISCH_THEN(X_CHOOSE_THEN `stout:linear_scan_state`
    (X_CHOOSE_THEN `sthout:linear_scan_hidden_state` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`stout:linear_scan_state`; `sthout:linear_scan_hidden_state`] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 3692 (HOL4 comment: TODO: move) *)
let intbeg_less_def = cake_def
  `intbeg_less (int_beg:int list) r1 r2 <=>
     (((<):int->int->bool) LEX ((<=):num->num->bool))
       (EL r1 int_beg,r1) (EL r2 int_beg,r2)`;;
(* HOL4 line 3696 *)
let intbeg_less_transitive = prove
 (`!int_beg. transitive (intbeg_less int_beg)`,
    REWRITE_TAC[transitive_DEF; intbeg_less_def; LEX_THM] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `EL x int_beg = (EL y int_beg:int)` THEN
  ASM_CASES_TAC `EL y int_beg = (EL z int_beg:int)` THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  MAP_EVERY (fun t -> SPEC_TAC(t, genvar(type_of t)))
    [`EL x int_beg:int`; `EL y int_beg:int`; `EL z int_beg:int`] THEN
  REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

(* HOL4 line 3703 *)
let intbeg_less_total = prove
 (`!int_beg. total (intbeg_less int_beg)`,
    REWRITE_TAC[total_DEF; intbeg_less_def] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(((<):int->int->bool) LEX ((<=):num->num->bool))
                   (EL x int_beg,x) (EL y int_beg,y)` THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM(ACCEPT_TAC o MATCH_MP LSCANPAUX_LEX_TOTAL));;


(* LSCANPAUX_passn_forced: the forced neighbours of the next register are    *)
(* already allocated                                                         *)
let LSCANPAUX_passn_forced = prove
 (CASE_TERM
  `!(B:int list) l h regl forced fa.
     SORTED (intbeg_less B) (CONS h regl) /\
     (!r1 r2. MEM r1 l /\ MEM r2 (CONS h regl) ==> intbeg_less B r1 r2) /\
     ALL_DISTINCT (CONS h regl) /\ ~MEM h l /\
     forbidden_is_from_forced_sublist (APPEND l (CONS h regl)) forced B h fa /\
     ALL (\r12. match r12 with
                  (r1,r2) -> MEM r1 (APPEND l (CONS h regl)) /\
                             MEM r2 (APPEND l (CONS h regl))) forced ==>
     forbidden_is_from_forced_list forced l h fa /\ ALL (\r. MEM r l) fa`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sorted") (CONJUNCTS_THEN2 (LABEL_TAC "less")
    (CONJUNCTS_THEN2 (LABEL_TAC "dist") (CONJUNCTS_THEN2 (LABEL_TAC "hnl")
    (CONJUNCTS_THEN2 (LABEL_TAC "fsub") (LABEL_TAC "fmem")))))) THEN
  USE_THEN "fsub" (LABEL_TAC "fs" o REWRITE_RULE[forbidden_is_from_forced_sublist_def;
    GSYM intbeg_less_def; MEM_APPEND; MEM]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[forbidden_is_from_forced_list_def] THEN X_GEN_TAC `reg2:num` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "m") (LABEL_TAC "adj")) THEN
    USE_THEN "fs" (fun th -> REWRITE_TAC[GSYM th]) THEN
    USE_THEN "adj" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~MEM (reg2:num) l` THEN
      USE_THEN "m" (fun th -> REWRITE_TAC[th]);
      USE_THEN "less" MATCH_MP_TAC THEN USE_THEN "m" (fun th -> REWRITE_TAC[th; MEM])];
    REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `r:num` THEN
    USE_THEN "fs" (fun th -> REWRITE_TAC[GSYM th]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rneq") (CONJUNCTS_THEN2 (LABEL_TAC "adj")
      (LABEL_TAC "rless"))) THEN
    SUBGOAL_THEN `MEM (r:num) (APPEND l (CONS h regl))` MP_TAC THENL
     [USE_THEN "fmem" (MP_TAC o REWRITE_RULE[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE]) THEN
      USE_THEN "adj" MP_TAC THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[MEM_APPEND; MEM] THEN USE_THEN "rneq" (fun th -> REWRITE_TAC[th]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "sorted" (MP_TAC o REWRITE_RULE[MATCH_MP SORTED_EQ
      (SPEC `B:int list` intbeg_less_transitive)]) THEN
    DISCH_THEN(MP_TAC o SPEC `r:num` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
    USE_THEN "rneq" MP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC LSCANPAUX_LEX_ANTISYM THEN
    MAP_EVERY EXISTS_TAC [`EL h (B:int list)`; `EL r (B:int list)`] THEN
    ASM_REWRITE_TAC[GSYM intbeg_less_def]]);;

(* LSCANPAUX_ffsublist_cong: forbidden_is_from_forced_sublist only depends on *)
(* the members of its list argument                                         *)
let LSCANPAUX_ffsublist_cong = prove
 (`!L1 L2. (!x:num. MEM x L1 <=> MEM x L2) ==>
           !forced (B:int list) r fa.
             (forbidden_is_from_forced_sublist L1 forced B r fa <=>
              forbidden_is_from_forced_sublist L2 forced B r fa)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[forbidden_is_from_forced_sublist_def]);;

(* HOL4 line 3710 *)
let st_ex_FOLDL_linear_reg_alloc_step_passn_invariants_lemma = prove
 (CASE_TERM
  `!regl st sth l pos b moves forced_adj forced mincol.
     SORTED (intbeg_less (linear_scan_hidden_state_int_beg sth)) regl /\
     (!r1 r2. MEM r1 l /\ MEM r2 regl ==>
              intbeg_less (linear_scan_hidden_state_int_beg sth) r1 r2) /\
     ALL_DISTINCT regl /\
     ALL (\r. ~MEM r regl) l /\
     good_linear_scan_state st sth l pos forced mincol /\
     ALL (\r. pos <= EL r (linear_scan_hidden_state_int_beg sth)) regl /\
     ALL (\r. r < LENGTH (linear_scan_hidden_state_colors sth)) regl /\
     (!r. forbidden_is_from_forced_sublist (APPEND l regl) forced
            (linear_scan_hidden_state_int_beg sth) r (misc_the [] (lookup r forced_adj))) /\
     ALL (\r12. match r12 with
                  (r1,r2) -> MEM r1 (APPEND l regl) /\ MEM r2 (APPEND l regl)) forced /\
     (!r1. ALL (\r2. r2 < LENGTH (linear_scan_hidden_state_colors sth))
               (misc_the [] (lookup r1 forced_adj))) /\
     (!r1. ALL (\r2. r2 < LENGTH (linear_scan_hidden_state_colors sth))
               (misc_the [] (lookup r1 moves))) /\
     ALL (\r. EL r (linear_scan_hidden_state_int_beg sth) <=
              EL r (linear_scan_hidden_state_int_end sth)) regl ==>
     ?stout sthout posout.
       (M_success stout,sthout) =
         st_ex_FOLDL ((if b then linear_reg_alloc_step_pass1 else linear_reg_alloc_step_pass2)
                        forced_adj moves) st regl sth /\
       good_linear_scan_state stout sthout (APPEND (REVERSE regl) l) posout forced mincol /\
       LENGTH (linear_scan_hidden_state_colors sthout) =
         LENGTH (linear_scan_hidden_state_colors sth) /\
       linear_scan_hidden_state_int_beg sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout = linear_scan_hidden_state_int_end sth /\
       (!r. ~MEM r (APPEND l regl) ==>
            EL r (linear_scan_hidden_state_colors sthout) =
            EL r (linear_scan_hidden_state_colors sth)) /\
       (b ==> (phystack_on_stack l st sth ==>
               phystack_on_stack (APPEND (REVERSE regl) l) stout sthout)) /\
       linear_scan_state_colormax stout = linear_scan_state_colormax st`,
    LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC(st_ex_FOLDL_def :: RAPROOFAUX_msimps) THEN
    MAP_EVERY EXISTS_TAC [`st:linear_scan_state`; `sth:linear_scan_hidden_state`; `pos:int`] THEN
    ASM_REWRITE_TAC[REVERSE; APPEND; APPEND_NIL] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sorted") (CONJUNCTS_THEN2 (LABEL_TAC "less")
    (CONJUNCTS_THEN2 (LABEL_TAC "dist") (CONJUNCTS_THEN2 (LABEL_TAC "disj")
    (CONJUNCTS_THEN2 (LABEL_TAC "gls") (CONJUNCTS_THEN2 (LABEL_TAC "posle")
    (CONJUNCTS_THEN2 (LABEL_TAC "lt") (CONJUNCTS_THEN2 (LABEL_TAC "fsub")
    (CONJUNCTS_THEN2 (LABEL_TAC "fmem") (CONJUNCTS_THEN2 (LABEL_TAC "fadjlt")
    (CONJUNCTS_THEN2 (LABEL_TAC "movlt") (LABEL_TAC "begend")))))))))))) THEN
  USE_THEN "posle" (CONJUNCTS_THEN2 (LABEL_TAC "posh") (LABEL_TAC "post") o
    REWRITE_RULE[ALL]) THEN
  USE_THEN "lt" (CONJUNCTS_THEN2 (LABEL_TAC "lth") (LABEL_TAC "ltt") o REWRITE_RULE[ALL]) THEN
  USE_THEN "begend" (CONJUNCTS_THEN2 (LABEL_TAC "beh") (LABEL_TAC "bet") o
    REWRITE_RULE[ALL]) THEN
  USE_THEN "dist" (CONJUNCTS_THEN2 (LABEL_TAC "hnt") (LABEL_TAC "distt") o
    REWRITE_RULE[ALL_DISTINCT]) THEN
  SUBGOAL_THEN `~MEM (h:num) l` (LABEL_TAC "hnl") THENL
   [USE_THEN "disj" MP_TAC THEN REWRITE_TAC[GSYM ALL_MEM; MEM] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`linear_scan_hidden_state_int_beg sth`; `l:num list`; `h:num`; `t:num list`;
    `forced:(num#num)list`; `misc_the [] (lookup h forced_adj):num list`] LSCANPAUX_passn_forced) THEN
  ANTS_TAC THENL
   [USE_THEN "sorted" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "less" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "dist" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "hnl" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "fsub" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "fmem" (fun th -> REWRITE_TAC[th]);
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ffl") (LABEL_TAC "fadjl"))] THEN
  SUBGOAL_THEN
   `?stmid sthmid.
      (if b then linear_reg_alloc_step_pass1 else linear_reg_alloc_step_pass2)
        forced_adj moves st h sth = (M_success stmid,sthmid) /\
      good_linear_scan_state stmid sthmid (CONS h l)
        (EL h (linear_scan_hidden_state_int_beg sth)) forced mincol /\
      LENGTH (linear_scan_hidden_state_colors sthmid) =
        LENGTH (linear_scan_hidden_state_colors sth) /\
      linear_scan_hidden_state_int_beg sthmid = linear_scan_hidden_state_int_beg sth /\
      linear_scan_hidden_state_int_end sthmid = linear_scan_hidden_state_int_end sth /\
      (!r. ~MEM r (CONS h l) ==>
           EL r (linear_scan_hidden_state_colors sthmid) =
           EL r (linear_scan_hidden_state_colors sth)) /\
      (b ==> (phystack_on_stack l st sth ==> phystack_on_stack (CONS h l) stmid sthmid)) /\
      linear_scan_state_colormax stmid = linear_scan_state_colormax st`
    MP_TAC THENL
   [ASM_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[] THENL
     [MP_TAC(SPECL [`st:linear_scan_state`; `sth:linear_scan_hidden_state`; `l:num list`;
        `moves:(num list)spt`; `forced_adj:(num list)spt`; `forced:(num#num)list`; `h:num`;
        `pos:int`; `mincol:num`] linear_reg_alloc_step_pass1_invariants);
      MP_TAC(SPECL [`st:linear_scan_state`; `sth:linear_scan_hidden_state`; `l:num list`;
        `moves:(num list)spt`; `forced_adj:(num list)spt`; `forced:(num#num)list`; `h:num`;
        `pos:int`; `mincol:num`] linear_reg_alloc_step_pass2_invariants)] THEN
    ANTS_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `stmid:linear_scan_state`
      (X_CHOOSE_THEN `sthmid:linear_scan_hidden_state` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`stmid:linear_scan_state`; `sthmid:linear_scan_hidden_state`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `stmid:linear_scan_state` (X_CHOOSE_THEN
    `sthmid:linear_scan_hidden_state`
    (CONJUNCTS_THEN2 (LABEL_TAC "midq") (CONJUNCTS_THEN2 (LABEL_TAC "glsm")
    (CONJUNCTS_THEN2 (LABEL_TAC "lenm") (CONJUNCTS_THEN2 (LABEL_TAC "begm")
    (CONJUNCTS_THEN2 (LABEL_TAC "endm") (CONJUNCTS_THEN2 (LABEL_TAC "elm")
    (CONJUNCTS_THEN2 (LABEL_TAC "phym") (LABEL_TAC "maxm")))))))))) THEN
  REWRITE_TAC(st_ex_FOLDL_def :: RAPROOFAUX_msimps) THEN
  USE_THEN "midq" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`stmid:linear_scan_state`; `sthmid:linear_scan_hidden_state`;
    `CONS (h:num) l`; `EL h (linear_scan_hidden_state_int_beg sth)`; `b:bool`;
    `moves:(num list)spt`; `forced_adj:(num list)spt`; `forced:(num#num)list`;
    `mincol:num`]) THEN
  USE_THEN "begm" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "endm" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "lenm" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `!r. MEM r (APPEND (CONS h l) t) <=> MEM (r:num) (APPEND l (CONS h t))`
    (LABEL_TAC "memeq") THENL
   [REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "memeq" (fun th -> REWRITE_TAC[th; MATCH_MP LSCANPAUX_ffsublist_cong th]) THEN
  USE_THEN "sorted" (LABEL_TAC "sortedq" o REWRITE_RULE[MATCH_MP SORTED_EQ
    (SPEC `linear_scan_hidden_state_int_beg sth` intbeg_less_transitive)]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "sortedq" (ACCEPT_TAC o CONJUNCT1);
      REWRITE_TAC[MEM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [USE_THEN "sortedq" (MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
        USE_THEN "less" MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM]];
      USE_THEN "distt" ACCEPT_TAC;
      REWRITE_TAC[ALL] THEN USE_THEN "hnt" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "disj" MP_TAC THEN REWRITE_TAC[GSYM ALL_MEM; MEM] THEN MESON_TAC[];
      USE_THEN "glsm" ACCEPT_TAC;
      REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      REMOVE_THEN "sortedq" (MP_TAC o SPEC `r:num` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[intbeg_less_def; LEX_THM] THEN INT_ARITH_TAC;
      USE_THEN "ltt" ACCEPT_TAC;
      USE_THEN "fsub" ACCEPT_TAC;
      USE_THEN "fmem" ACCEPT_TAC;
      USE_THEN "fadjlt" ACCEPT_TAC;
      USE_THEN "movlt" ACCEPT_TAC;
      USE_THEN "bet" ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `stout:linear_scan_state` (X_CHOOSE_THEN
    `sthout:linear_scan_hidden_state` (X_CHOOSE_THEN `posout:int`
    (CONJUNCTS_THEN2 (LABEL_TAC "outq") (CONJUNCTS_THEN2 (LABEL_TAC "glso")
    (CONJUNCTS_THEN2 (LABEL_TAC "leno") (CONJUNCTS_THEN2 (LABEL_TAC "bego")
    (CONJUNCTS_THEN2 (LABEL_TAC "endo") (CONJUNCTS_THEN2 (LABEL_TAC "elo")
    (CONJUNCTS_THEN2 (LABEL_TAC "phyo") (LABEL_TAC "maxo"))))))))))) THEN
  MAP_EVERY EXISTS_TAC [`stout:linear_scan_state`; `sthout:linear_scan_hidden_state`;
    `posout:int`] THEN
  REWRITE_TAC[REVERSE; GSYM APPEND_ASSOC; APPEND] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "outq" ACCEPT_TAC;
    USE_THEN "glso" ACCEPT_TAC;
    USE_THEN "leno" ACCEPT_TAC;
    USE_THEN "bego" ACCEPT_TAC;
    USE_THEN "endo" ACCEPT_TAC;
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    USE_THEN "elo" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `~MEM (r:num) (APPEND l (CONS h t))`)]) THEN
    USE_THEN "elm" MATCH_MP_TAC THEN
    UNDISCH_TAC `~MEM (r:num) (APPEND l (CONS h t))` THEN
    REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[];
    USE_THEN "phym" MP_TAC THEN USE_THEN "phyo" MP_TAC THEN MESON_TAC[];
    USE_THEN "maxo" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "maxm" ACCEPT_TAC]);;


(* HOL4 line 3795 *)
let st_ex_FOLDL_linear_reg_alloc_step_passn_invariants = prove
 (CASE_TERM
  `!regl st sth pos b moves forced_adj forced mincol.
     SORTED (intbeg_less (linear_scan_hidden_state_int_beg sth)) regl /\
     ALL_DISTINCT regl /\
     good_linear_scan_state st sth [] pos forced mincol /\
     ALL (\r. pos <= EL r (linear_scan_hidden_state_int_beg sth)) regl /\
     ALL (\r. r < LENGTH (linear_scan_hidden_state_colors sth)) regl /\
     (!r. forbidden_is_from_forced_sublist regl forced
            (linear_scan_hidden_state_int_beg sth) r (misc_the [] (lookup r forced_adj))) /\
     ALL (\r12. match r12 with (r1,r2) -> MEM r1 regl /\ MEM r2 regl) forced /\
     (!r1. ALL (\r2. r2 < LENGTH (linear_scan_hidden_state_colors sth))
               (misc_the [] (lookup r1 forced_adj))) /\
     (!r1. ALL (\r2. r2 < LENGTH (linear_scan_hidden_state_colors sth))
               (misc_the [] (lookup r1 moves))) /\
     ALL (\r. EL r (linear_scan_hidden_state_int_beg sth) <=
              EL r (linear_scan_hidden_state_int_end sth)) regl ==>
     ?stout sthout posout.
       (M_success stout,sthout) =
         st_ex_FOLDL ((if b then linear_reg_alloc_step_pass1 else linear_reg_alloc_step_pass2)
                        forced_adj moves) st regl sth /\
       good_linear_scan_state stout sthout (REVERSE regl) posout forced mincol /\
       LENGTH (linear_scan_hidden_state_colors sthout) =
         LENGTH (linear_scan_hidden_state_colors sth) /\
       linear_scan_hidden_state_int_beg sthout = linear_scan_hidden_state_int_beg sth /\
       linear_scan_hidden_state_int_end sthout = linear_scan_hidden_state_int_end sth /\
       (!r. ~MEM r regl ==>
            EL r (linear_scan_hidden_state_colors sthout) =
            EL r (linear_scan_hidden_state_colors sth)) /\
       (b ==> phystack_on_stack (REVERSE regl) stout sthout) /\
       linear_scan_state_colormax stout = linear_scan_state_colormax st`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`regl:num list`; `st:linear_scan_state`; `sth:linear_scan_hidden_state`;
    `[]:num list`; `pos:int`; `b:bool`; `moves:(num list)spt`; `forced_adj:(num list)spt`;
    `forced:(num#num)list`; `mincol:num`]
    st_ex_FOLDL_linear_reg_alloc_step_passn_invariants_lemma) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[APPEND; MEM; ALL]; ALL_TAC] THEN
  REWRITE_TAC[APPEND; APPEND_NIL] THEN
  SUBGOAL_THEN `phystack_on_stack [] st sth` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[phystack_on_stack_def; MEM]);;

(* HOL4 line 3821 *)
let swap_regs_eq = prove
 (`!sth i1 i2.
     i1 < LENGTH (linear_scan_hidden_state_sorted_regs sth) /\
     i2 < LENGTH (linear_scan_hidden_state_sorted_regs sth) ==>
     ?sthout.
       swap_regs i1 i2 sth = (M_success one,sthout) /\
       sthout =
         linear_scan_hidden_state_sorted_regs_fupd
           (K (LUPDATE (EL i1 (linear_scan_hidden_state_sorted_regs sth)) i2
                 (LUPDATE (EL i2 (linear_scan_hidden_state_sorted_regs sth)) i1
                    (linear_scan_hidden_state_sorted_regs sth)))) sth`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC(swap_regs_def :: sorted_regs_sub_eqn :: update_sorted_regs_eqn ::
              RAPROOFAUX_msimps) THEN
  ASM_REWRITE_TAC(case_def "prod" :: case_def "exc" :: K_THM :: LENGTH_LUPDATE ::
                  LSCANPAUX_hs_record) THEN
  REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN
  REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
  REWRITE_TAC(K_THM :: o_THM :: LSCANPAUX_hs_record));;

(* HOL4 line 3831 (HOL4 comment: TODO: move) *)
let if_thm = prove
 (`!b (x:A) y z. (if b then x else y) = z <=> (b /\ x = z) \/ (~b /\ y = z)`,
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* HOL4 line 3837 *)
let split_at_indice_sing = prove
 (`!(l:A list) i.
     i < LENGTH l ==> ?l1 x l2. l = APPEND (APPEND l1 [x]) l2 /\ LENGTH l1 = i`,
    LIST_INDUCT_TAC THENL [REWRITE_TAC[LENGTH; LT]; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[LENGTH; LT_SUC] THEN DISCH_TAC THENL
   [MAP_EVERY EXISTS_TAC [`[]:A list`; `h:A`; `t:A list`] THEN REWRITE_TAC[APPEND; LENGTH];
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l1:A list` (X_CHOOSE_THEN `x:A` (X_CHOOSE_THEN `l2:A list`
      STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`CONS (h:A) l1`; `x:A`; `l2:A list`] THEN
    ASM_REWRITE_TAC[APPEND; LENGTH]]);;

(* HOL4 line 3859 *)
let split_at_indice = prove
 (`!(l:A list) i. i <= LENGTH l ==> ?l1 l2. l = APPEND l1 l2 /\ LENGTH l1 = i`,
    LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LENGTH; LE] THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXISTS_TAC [`[]:A list`; `[]:A list`] THEN REWRITE_TAC[APPEND; LENGTH];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[LENGTH; LE_SUC] THEN DISCH_TAC THENL
   [MAP_EVERY EXISTS_TAC [`[]:A list`; `CONS (h:A) t`] THEN REWRITE_TAC[APPEND; LENGTH];
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l1:A list` (X_CHOOSE_THEN `l2:A list` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`CONS (h:A) l1`; `l2:A list`] THEN
    ASM_REWRITE_TAC[APPEND; LENGTH]]);;

(* LSCANPAUX_swap_perm_lt: swap_perm_lemma when i1 < i2 *)
let LSCANPAUX_swap_perm_lt = prove
 (`!(l:A list) i1 i2.
     i1 < i2 /\ i2 < LENGTH l ==>
     PERM l (LUPDATE (EL i1 l) i2 (LUPDATE (EL i2 l) i1 l))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:A list`; `i2:num`] split_at_indice_sing) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:A list` (X_CHOOSE_THEN `y:A` (X_CHOOSE_THEN `l2:A list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`l1:A list`; `i1:num`] split_at_indice_sing) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l11:A list` (X_CHOOSE_THEN `x:A` (X_CHOOSE_THEN `l12:A list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && is_var(rhs(concl th))))) THEN
  SUBGOAL_THEN
   `APPEND (APPEND (APPEND (APPEND l11 [x]) l12) [y]) l2 =
    APPEND (APPEND l11 [x:A]) (APPEND l12 (APPEND [y] l2))` (LABEL_TAC "re") THENL
   [REWRITE_TAC[APPEND_ASSOC]; ALL_TAC] THEN
  SUBGOAL_THEN `EL (LENGTH (l11:A list)) (APPEND (APPEND (APPEND (APPEND l11 [x]) l12) [y]) l2) = x`
    SUBST1_TAC THENL [USE_THEN "re" (fun th -> REWRITE_TAC[th; el_append3]); ALL_TAC] THEN
  REWRITE_TAC[el_append3] THEN
  SUBGOAL_THEN
   `LUPDATE (y:A) (LENGTH (l11:A list)) (APPEND (APPEND (APPEND (APPEND l11 [x]) l12) [y]) l2) =
    APPEND (APPEND (APPEND (APPEND l11 [y]) l12) [y]) l2` SUBST1_TAC THENL
   [USE_THEN "re" (fun th -> REWRITE_TAC[th; lupdate_append2]) THEN REWRITE_TAC[APPEND_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (APPEND (APPEND l11 [x]) l12) =
                LENGTH (APPEND (APPEND l11 [y:A]) l12)` SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH]; ALL_TAC] THEN
  REWRITE_TAC[lupdate_append2] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN REWRITE_TAC[PERM_APPEND_IFF] THEN
  REWRITE_TAC[PERM_CONS_EQ_APPEND] THEN
  MAP_EVERY EXISTS_TAC [`CONS (y:A) l12`; `l2:A list`] THEN
  REWRITE_TAC[APPEND] THEN ONCE_REWRITE_TAC[PERM_SYM] THEN
  REWRITE_TAC[PERM_CONS_EQ_APPEND] THEN
  MAP_EVERY EXISTS_TAC [`l12:A list`; `l2:A list`] THEN REWRITE_TAC[PERM_REFL]);;

(* HOL4 line 3879 *)
let swap_perm_lemma = prove
 (`!(l:A list) i1 i2.
     i1 < LENGTH l /\ i2 < LENGTH l ==>
     PERM l (LUPDATE (EL i1 l) i2 (LUPDATE (EL i2 l) i1 l))`,
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `i1:num = i2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[LUPDATE_SAME; PERM_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `i1 < i2 \/ i2 < (i1:num)` MP_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN DISJ_CASES_TAC] THENL
   [MATCH_MP_TAC LSCANPAUX_swap_perm_lt THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `LUPDATE (EL i1 l) i2 (LUPDATE (EL i2 l) i1 l) =
                  LUPDATE (EL i2 l) i1 (LUPDATE (EL i1 (l:A list)) i2 l)` SUBST1_TAC THENL
     [MATCH_MP_TAC LUPDATE_commutes THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LSCANPAUX_swap_perm_lt THEN ASM_REWRITE_TAC[]]]);;

(* HOL4 line 3914 *)
let LUPDATE_TAKE = prove
 (`!n x (y:A) l.
     x < n /\ n <= LENGTH l ==> TAKE n (LUPDATE y x l) = LUPDATE y x (TAKE n l)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ_REWRITE] THEN
  SUBGOAL_THEN `x < LENGTH (l:A list)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LENGTH_TAKE; LENGTH_LUPDATE] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_TAKE; EL_LUPDATE; LENGTH_TAKE] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[EL_TAKE]);;

(* HOL4 line 3924 *)
let swap_regs_perm = prove
 (`!sth i1 i2 sthout.
     swap_regs i1 i2 sth = (M_success one,sthout) ==>
     (!n. i1 < n /\ i2 < n /\ n <= LENGTH (linear_scan_hidden_state_sorted_regs sth) ==>
          PERM (TAKE n (linear_scan_hidden_state_sorted_regs sth))
               (TAKE n (linear_scan_hidden_state_sorted_regs sthout)))`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`sth:linear_scan_hidden_state`; `i1:num`; `i2:num`] swap_regs_eq) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:linear_scan_hidden_state` (CONJUNCTS_THEN2 ASSUME_TAC
    SUBST_ALL_TAC)) THEN
  UNDISCH_TAC `swap_regs i1 i2 sth = (M_success one,sthout)` THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC(K_THM :: LSCANPAUX_hs_record) THEN
  ASM_SIMP_TAC[LUPDATE_TAKE; LENGTH_LUPDATE] THEN
  SUBGOAL_THEN
   `EL i1 (linear_scan_hidden_state_sorted_regs sth) =
    EL i1 (TAKE n (linear_scan_hidden_state_sorted_regs sth)) /\
    EL i2 (linear_scan_hidden_state_sorted_regs sth) =
    EL i2 (TAKE n (linear_scan_hidden_state_sorted_regs sth))`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_SIMP_TAC[EL_TAKE]; ALL_TAC] THEN
  MATCH_MP_TAC swap_perm_lemma THEN ASM_SIMP_TAC[LENGTH_TAKE]);;


(* HOL4 line 3937 *)
let partition_regs_correct = prove
 (`!l rpiv begrpiv r sth.
     (!i. l <= i /\ i < r ==>
          EL i (linear_scan_hidden_state_sorted_regs sth) <
          LENGTH (linear_scan_hidden_state_int_beg sth)) /\
     l <= LENGTH (linear_scan_hidden_state_sorted_regs sth) /\
     r <= LENGTH (linear_scan_hidden_state_sorted_regs sth) ==>
     ?mid sthout.
       partition_regs l rpiv begrpiv r sth = (M_success mid,sthout) /\
       sthout = linear_scan_hidden_state_sorted_regs_fupd
                  (K (linear_scan_hidden_state_sorted_regs sthout)) sth /\
       LENGTH (linear_scan_hidden_state_sorted_regs sthout) =
         LENGTH (linear_scan_hidden_state_sorted_regs sth) /\
       (l <= r ==> l <= mid /\ mid <= r) /\
       (!n. l <= n /\ r <= n /\ n <= LENGTH (linear_scan_hidden_state_sorted_regs sth) ==>
            PERM (TAKE n (linear_scan_hidden_state_sorted_regs sth))
                 (TAKE n (linear_scan_hidden_state_sorted_regs sthout))) /\
       (!ind. ind < l \/ r <= ind ==>
              EL ind (linear_scan_hidden_state_sorted_regs sthout) =
              EL ind (linear_scan_hidden_state_sorted_regs sth)) /\
       (!ind. l <= ind /\ ind < mid ==>
              let reg = EL ind (linear_scan_hidden_state_sorted_regs sthout) in
              (((<):int->int->bool) LEX ((<=):num->num->bool))
                (EL reg (linear_scan_hidden_state_int_beg sth),reg) (begrpiv,rpiv)) /\
       (!ind. mid <= ind /\ ind < r ==>
              let reg = EL ind (linear_scan_hidden_state_sorted_regs sthout) in
              (((<):int->int->bool) LEX ((<=):num->num->bool))
                (begrpiv,rpiv) (EL reg (linear_scan_hidden_state_int_beg sth),reg))`,
    MATCH_MP_TAC partition_regs_ind THEN
  MAP_EVERY X_GEN_TAC [`l:num`; `rpiv:num`; `begrpiv:int`; `r:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihswap") (LABEL_TAC "ihnext")) THEN
  X_GEN_TAC `sth:linear_scan_hidden_state` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inb") (CONJUNCTS_THEN2 (LABEL_TAC "lle")
    (LABEL_TAC "rle"))) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ONCE_REWRITE_TAC[partition_regs_def] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC RAPROOFAUX_msimps THEN
    MAP_EVERY EXISTS_TAC [`l:num`; `sth:linear_scan_hidden_state`] THEN
    REWRITE_TAC[PERM_REFL; LE_REFL] THEN CONJ_TAC THENL
     [REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
      REWRITE_TAC(K_THM :: LSCANPAUX_hs_record);
      CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "rl") THEN
  SUBGOAL_THEN `l < LENGTH (linear_scan_hidden_state_sorted_regs sth)` (LABEL_TAC "llt") THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `EL l (linear_scan_hidden_state_sorted_regs sth) <
                LENGTH (linear_scan_hidden_state_int_beg sth)` (LABEL_TAC "reglt") THENL
   [USE_THEN "inb" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC(sorted_regs_sub_eqn :: int_beg_sub_eqn :: RAPROOFAUX_msimps) THEN
  USE_THEN "llt" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
  USE_THEN "reglt" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
  ASM_CASES_TAC
   `EL (EL l (linear_scan_hidden_state_sorted_regs sth)) (linear_scan_hidden_state_int_beg sth)
      < begrpiv \/
    EL (EL l (linear_scan_hidden_state_sorted_regs sth)) (linear_scan_hidden_state_int_beg sth)
      = begrpiv /\ EL l (linear_scan_hidden_state_sorted_regs sth) <= rpiv` THEN
  POP_ASSUM(fun th -> REWRITE_TAC[th] THEN LABEL_TAC "cond" th) THENL
   [(* the register stays on the left *)
    REMOVE_THEN "ihnext" (MP_TAC o SPECL
      [`EL (EL l (linear_scan_hidden_state_sorted_regs sth))
           (linear_scan_hidden_state_int_beg sth)`;
       `EL l (linear_scan_hidden_state_sorted_regs sth)`]) THEN
    USE_THEN "rl" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "cond" (fun th -> REWRITE_TAC[th; LET_DEF; LET_END_DEF]) THEN
    DISCH_THEN(MP_TAC o SPEC `sth:linear_scan_hidden_state`) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN USE_THEN "inb" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC;
        USE_THEN "rle" ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `mid:num` (X_CHOOSE_THEN `sthout:linear_scan_hidden_state`
      (CONJUNCTS_THEN2 (LABEL_TAC "eq") (CONJUNCTS_THEN2 (LABEL_TAC "rec")
      (CONJUNCTS_THEN2 (LABEL_TAC "len") (CONJUNCTS_THEN2 (LABEL_TAC "mr")
      (CONJUNCTS_THEN2 (LABEL_TAC "perm") (CONJUNCTS_THEN2 (LABEL_TAC "elsame")
      (CONJUNCTS_THEN2 (LABEL_TAC "lo") (LABEL_TAC "hi")))))))))) THEN
    MAP_EVERY EXISTS_TAC [`mid:num`; `sthout:linear_scan_hidden_state`] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "eq" ACCEPT_TAC;
      USE_THEN "rec" ACCEPT_TAC;
      USE_THEN "len" ACCEPT_TAC;
      DISCH_TAC THEN USE_THEN "mr" MP_TAC THEN ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "perm" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "elsame" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      X_GEN_TAC `ind:num` THEN STRIP_TAC THEN ASM_CASES_TAC `ind:num = l` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        USE_THEN "elsame" (fun th -> REWRITE_TAC[MATCH_MP th
          (ARITH_RULE `l < l + 1 \/ r <= l`)]) THEN
        REWRITE_TAC[LEX_THM] THEN USE_THEN "cond" ACCEPT_TAC;
        USE_THEN "lo" MATCH_MP_TAC THEN ASM_ARITH_TAC];
      USE_THEN "hi" ACCEPT_TAC];
    (* the register is swapped to the right *)
    MP_TAC(SPECL [`sth:linear_scan_hidden_state`; `l:num`; `r - 1`] swap_regs_eq) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `sth1:linear_scan_hidden_state`
      (CONJUNCTS_THEN2 (LABEL_TAC "sw") SUBST_ALL_TAC)) THEN
    USE_THEN "sw" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
    REMOVE_THEN "ihswap" (MP_TAC o SPECL
      [`EL (EL l (linear_scan_hidden_state_sorted_regs sth))
           (linear_scan_hidden_state_int_beg sth)`;
       `EL l (linear_scan_hidden_state_sorted_regs sth)`]) THEN
    USE_THEN "rl" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "cond" (fun th -> REWRITE_TAC[th; LET_DEF; LET_END_DEF]) THEN
    DISCH_THEN(MP_TAC o SPEC
     `linear_scan_hidden_state_sorted_regs_fupd
        (K (LUPDATE (EL l (linear_scan_hidden_state_sorted_regs sth)) (r - 1)
              (LUPDATE (EL (r - 1) (linear_scan_hidden_state_sorted_regs sth)) l
                 (linear_scan_hidden_state_sorted_regs sth)))) sth`) THEN
    REWRITE_TAC(K_THM :: LENGTH_LUPDATE :: LSCANPAUX_hs_record) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[EL_LUPDATE; LENGTH_LUPDATE] THEN
        COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        COND_CASES_TAC THEN USE_THEN "inb" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        USE_THEN "lle" ACCEPT_TAC;
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `mid:num` (X_CHOOSE_THEN `sthout:linear_scan_hidden_state`
      (CONJUNCTS_THEN2 (LABEL_TAC "eq") (CONJUNCTS_THEN2 (LABEL_TAC "rec")
      (CONJUNCTS_THEN2 (LABEL_TAC "len") (CONJUNCTS_THEN2 (LABEL_TAC "mr")
      (CONJUNCTS_THEN2 (LABEL_TAC "perm") (CONJUNCTS_THEN2 (LABEL_TAC "elsame")
      (CONJUNCTS_THEN2 (LABEL_TAC "lo") (LABEL_TAC "hi")))))))))) THEN
    MAP_EVERY EXISTS_TAC [`mid:num`; `sthout:linear_scan_hidden_state`] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[] THEN USE_THEN "eq" ACCEPT_TAC;
      USE_THEN "rec" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
      REWRITE_TAC(K_THM :: o_THM :: LSCANPAUX_hs_record);
      USE_THEN "len" ACCEPT_TAC;
      DISCH_TAC THEN USE_THEN "mr" MP_TAC THEN ASM_ARITH_TAC;
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN MATCH_MP_TAC PERM_TRANS THEN
      EXISTS_TAC `TAKE n (LUPDATE (EL l (linear_scan_hidden_state_sorted_regs sth)) (r - 1)
              (LUPDATE (EL (r - 1) (linear_scan_hidden_state_sorted_regs sth)) l
                 (linear_scan_hidden_state_sorted_regs sth)))` THEN
      CONJ_TAC THENL
       [USE_THEN "sw" (MP_TAC o SPEC `n:num` o MATCH_MP swap_regs_perm) THEN
        REWRITE_TAC(K_THM :: LSCANPAUX_hs_record) THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_ARITH_TAC;
        USE_THEN "perm" MATCH_MP_TAC THEN ASM_ARITH_TAC];
      X_GEN_TAC `ind:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `ind < l \/ r - 1 <= ind` (fun th ->
        USE_THEN "elsame" (fun el -> REWRITE_TAC[MATCH_MP el th])) THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[EL_LUPDATE; LENGTH_LUPDATE] THEN
      SUBGOAL_THEN `~(ind = r - 1) /\ ~(ind:num = l)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC;
      USE_THEN "lo" ACCEPT_TAC;
      X_GEN_TAC `ind:num` THEN STRIP_TAC THEN ASM_CASES_TAC `ind = r - 1` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        USE_THEN "elsame" (fun th -> REWRITE_TAC[MATCH_MP th
          (ARITH_RULE `r - 1 < l \/ r - 1 <= r - 1`)]) THEN
        REWRITE_TAC[EL_LUPDATE; LENGTH_LUPDATE] THEN
        SUBGOAL_THEN `r - 1 < LENGTH (linear_scan_hidden_state_sorted_regs sth)`
          (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC LSCANPAUX_LEX_TOTAL THEN REWRITE_TAC[LEX_THM] THEN
        USE_THEN "cond" ACCEPT_TAC;
        USE_THEN "hi" MATCH_MP_TAC THEN ASM_ARITH_TAC]]]);;


(* HOL4 line 4016 *)
let PERM_EVERY_EQ = prove
 (`!(P:A->bool) l1 l2. PERM l1 l2 ==> (ALL P l1 <=> ALL P l2)`,
    MATCH_ACCEPT_TAC PERM_EVERY);;

(* LSCANPAUX_EL_APPEND3_L/M/R: indexing into APPEND (APPEND a b) c *)
let LSCANPAUX_EL_APPEND3_L = prove
 (`!(a:B list) b c x. x < LENGTH a ==> EL x (APPEND (APPEND a b) c) = EL x a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x < LENGTH (a:B list) + LENGTH (b:B list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[EL_APPEND_EQN; LENGTH_APPEND]);;

let LSCANPAUX_EL_APPEND3_M = prove
 (`!(a:B list) b c x. LENGTH a <= x /\ x < LENGTH a + LENGTH b ==>
                      EL x (APPEND (APPEND a b) c) = EL (x - LENGTH a) b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(x < LENGTH (a:B list))` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[EL_APPEND_EQN; LENGTH_APPEND]);;

let LSCANPAUX_EL_APPEND3_R = prove
 (`!(a:B list) b c x. LENGTH a + LENGTH b <= x ==>
                      EL x (APPEND (APPEND a b) c) = EL (x - (LENGTH a + LENGTH b)) c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(x < LENGTH (a:B list) + LENGTH (b:B list))` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[EL_APPEND_EQN; LENGTH_APPEND]);;

(* HOL4 line 4027 *)
let sort_regs_prop_lemma = prove
 (`!(P:num->bool) l1 l2 l r.
     l <= LENGTH l1 /\
     r <= LENGTH l1 /\
     (!ind. ind < l \/ r <= ind ==> EL ind l2 = EL ind l1) /\
     (!ind. l <= ind /\ ind < r ==> P (EL ind l1)) /\
     PERM l1 l2 ==>
     (!ind. l <= ind /\ ind < r ==> P (EL ind l2))`,
    REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ll") (CONJUNCTS_THEN2 (LABEL_TAC "rl")
    (CONJUNCTS_THEN2 (LABEL_TAC "out") (CONJUNCTS_THEN2 (LABEL_TAC "pin")
      (LABEL_TAC "perm"))))) THEN
  USE_THEN "perm" (LABEL_TAC "len" o MATCH_MP PERM_LENGTH) THEN
  ASM_CASES_TAC `l <= r:num` THENL [ALL_TAC; REPEAT STRIP_TAC THEN ASM_ARITH_TAC] THEN
  MP_TAC(ISPECL [`l1:num list`; `r:num`] split_at_indice) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a12:num list` (X_CHOOSE_THEN `a3:num list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`a12:num list`; `l:num`] split_at_indice) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:num list` (X_CHOOSE_THEN `a2:num list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`l2:num list`; `r:num`] split_at_indice) THEN
  ANTS_TAC THENL [USE_THEN "len" (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b12:num list` (X_CHOOSE_THEN `b3:num list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`b12:num list`; `l:num`] split_at_indice) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b1:num list` (X_CHOOSE_THEN `b2:num list`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND]) THEN
  SUBGOAL_THEN `LENGTH (a2:num list) = r - l /\ LENGTH (b2:num list) = r - l /\
                LENGTH (b3:num list) = LENGTH (a3:num list)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `b1:num list = a1` SUBST_ALL_TAC THENL
   [REWRITE_TAC[LIST_EQ_REWRITE] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    USE_THEN "out" (MP_TAC o SPEC `x:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `x < LENGTH (a1:num list)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LSCANPAUX_EL_APPEND3_L];
    ALL_TAC] THEN
  SUBGOAL_THEN `b3:num list = a3` SUBST_ALL_TAC THENL
   [REWRITE_TAC[LIST_EQ_REWRITE] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    USE_THEN "out" (MP_TAC o SPEC `x + r:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`a1:num list`; `a2:num list`; `a3:num list`; `x + r:num`]
      LSCANPAUX_EL_APPEND3_R) THEN
    MP_TAC(ISPECL [`a1:num list`; `b2:num list`; `b3:num list`; `x + r:num`]
      LSCANPAUX_EL_APPEND3_R) THEN
    ASM_REWRITE_TAC[ARITH_RULE `r <= x + r:num`; ADD_SUB] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `PERM (a2:num list) b2` (LABEL_TAC "p2") THENL
   [USE_THEN "perm" MP_TAC THEN REWRITE_TAC[PERM_APPEND_IFF]; ALL_TAC] THEN
  SUBGOAL_THEN `ALL (P:num->bool) a2` MP_TAC THENL
   [REWRITE_TAC[EVERY_EL] THEN X_GEN_TAC `y:num` THEN DISCH_TAC THEN
    USE_THEN "pin" (MP_TAC o SPEC `y + LENGTH (a1:num list)`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`a1:num list`; `a2:num list`; `a3:num list`;
      `y + LENGTH (a1:num list)`] LSCANPAUX_EL_APPEND3_M) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ADD_SUB];
    ALL_TAC] THEN
  USE_THEN "p2" (fun th -> REWRITE_TAC[MATCH_MP PERM_EVERY th]) THEN
  REWRITE_TAC[EVERY_EL] THEN DISCH_TAC THEN X_GEN_TAC `ind:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a1:num list`; `b2:num list`; `a3:num list`; `ind:num`]
    LSCANPAUX_EL_APPEND3_M) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;


(* LSCANPAUX_qsort_combine: the two sorted halves and the pivot of a        *)
(* quicksort step give a sorted segment                                      *)
let LSCANPAUX_qsort_combine = prove
 (`!(R:A->A->bool) L l m r p.
     transitive R /\ (!x. R x x) /\
     l <= m /\ m < r /\ EL m L = p /\
     (!i. l <= i /\ i < m ==> R (EL i L) p) /\
     (!i. m < i /\ i < r ==> R p (EL i L)) /\
     (!i1 i2. l <= i1 /\ i1 <= i2 /\ i2 < m ==> R (EL i1 L) (EL i2 L)) /\
     (!i1 i2. m < i1 /\ i1 <= i2 /\ i2 < r ==> R (EL i1 L) (EL i2 L)) ==>
     !i1 i2. l <= i1 /\ i1 <= i2 /\ i2 < r ==> R (EL i1 L) (EL i2 L)`,
  REWRITE_TAC[transitive_DEF] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tr") (CONJUNCTS_THEN2 (LABEL_TAC "rf")
    (CONJUNCTS_THEN2 (LABEL_TAC "lm") (CONJUNCTS_THEN2 (LABEL_TAC "mr")
    (CONJUNCTS_THEN2 (LABEL_TAC "piv") (CONJUNCTS_THEN2 (LABEL_TAC "lo")
    (CONJUNCTS_THEN2 (LABEL_TAC "hi") (CONJUNCTS_THEN2 (LABEL_TAC "sl")
      (LABEL_TAC "sr"))))))))) THEN
  MAP_EVERY X_GEN_TAC [`i1:num`; `i2:num`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `i2 < m:num` THENL
   [USE_THEN "sl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `m < i1:num` THENL
   [USE_THEN "sr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `R (EL i1 L) (p:A) /\ R p (EL i2 (L:A list))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_CASES_TAC `i1:num = m` THENL
       [USE_THEN "piv" (fun th -> ASM_REWRITE_TAC[th]);
        USE_THEN "lo" MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ASM_CASES_TAC `i2:num = m` THENL
       [USE_THEN "piv" (fun th -> ASM_REWRITE_TAC[th]);
        USE_THEN "hi" MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  USE_THEN "tr" MATCH_MP_TAC THEN EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[]);;

(* LSCANPAUX_intbeg_less_refl *)
let LSCANPAUX_intbeg_less_refl = prove
 (`!(B:int list) x. intbeg_less B x x`,
  REWRITE_TAC[intbeg_less_def; LEX_THM; LE_REFL]);;

(* LSCANPAUX_PERM_TAKE_ALL: PERM of all prefixes gives PERM of the lists *)
let LSCANPAUX_PERM_TAKE_ALL = prove
 (`!(l1:A list) l2.
     LENGTH l2 = LENGTH l1 /\ PERM (TAKE (LENGTH l1) l1) (TAKE (LENGTH l1) l2) ==>
     PERM l1 l2`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [ASSUME `LENGTH (l1:A list) = LENGTH (l2:A list)`] THEN
  REWRITE_TAC[TAKE_LENGTH_ID]);;


(* HOL4 line 4071 *)
let sort_regs_correct = prove
 (`!l r sth.
     (!i. l <= i /\ i < r ==>
          EL i (linear_scan_hidden_state_sorted_regs sth) <
          LENGTH (linear_scan_hidden_state_int_beg sth)) /\
     l <= LENGTH (linear_scan_hidden_state_sorted_regs sth) /\
     r <= LENGTH (linear_scan_hidden_state_sorted_regs sth) ==>
     ?sthout.
       sort_regs l r sth = (M_success one,sthout) /\
       sthout = linear_scan_hidden_state_sorted_regs_fupd
                  (K (linear_scan_hidden_state_sorted_regs sthout)) sth /\
       LENGTH (linear_scan_hidden_state_sorted_regs sthout) =
         LENGTH (linear_scan_hidden_state_sorted_regs sth) /\
       (!n. l <= n /\ r <= n /\ n <= LENGTH (linear_scan_hidden_state_sorted_regs sth) ==>
            PERM (TAKE n (linear_scan_hidden_state_sorted_regs sth))
                 (TAKE n (linear_scan_hidden_state_sorted_regs sthout))) /\
       (!ind. ind < l \/ r <= ind ==>
              EL ind (linear_scan_hidden_state_sorted_regs sthout) =
              EL ind (linear_scan_hidden_state_sorted_regs sth)) /\
       (!i1 i2. l <= i1 /\ i1 <= i2 /\ i2 < r ==>
                let reg1 = EL i1 (linear_scan_hidden_state_sorted_regs sthout) in
                let reg2 = EL i2 (linear_scan_hidden_state_sorted_regs sthout) in
                (((<):int->int->bool) LEX ((<=):num->num->bool))
                  (EL reg1 (linear_scan_hidden_state_int_beg sth),reg1)
                  (EL reg2 (linear_scan_hidden_state_int_beg sth),reg2))`,
    MATCH_MP_TAC sort_regs_ind THEN MAP_EVERY X_GEN_TAC [`l:num`; `r:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihl") (LABEL_TAC "ihr")) THEN
  X_GEN_TAC `sth:linear_scan_hidden_state` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inb") (CONJUNCTS_THEN2 (LABEL_TAC "lle")
    (LABEL_TAC "rle"))) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ONCE_REWRITE_TAC[sort_regs_def] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC RAPROOFAUX_msimps THEN EXISTS_TAC `sth:linear_scan_hidden_state` THEN
    REWRITE_TAC[PERM_REFL] THEN CONJ_TAC THENL
     [REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
      REWRITE_TAC(K_THM :: LSCANPAUX_hs_record);
      REPEAT STRIP_TAC THEN SUBGOAL_THEN `i1:num = i2` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[LEX_THM; LE_REFL]]];
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "rl") THEN
  SUBGOAL_THEN `l < LENGTH (linear_scan_hidden_state_sorted_regs sth)` (LABEL_TAC "llt") THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `EL l (linear_scan_hidden_state_sorted_regs sth) <
                LENGTH (linear_scan_hidden_state_int_beg sth)` (LABEL_TAC "pivlt") THENL
   [USE_THEN "inb" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC(sorted_regs_sub_eqn :: int_beg_sub_eqn :: RAPROOFAUX_msimps) THEN
  USE_THEN "llt" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
  USE_THEN "pivlt" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
  MP_TAC(SPECL [`l + 1`; `EL l (linear_scan_hidden_state_sorted_regs sth)`;
    `EL (EL l (linear_scan_hidden_state_sorted_regs sth)) (linear_scan_hidden_state_int_beg sth)`;
    `r:num`; `sth:linear_scan_hidden_state`] partition_regs_correct) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "inb" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC;
      USE_THEN "rle" ACCEPT_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; GSYM intbeg_less_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `mid:num` (X_CHOOSE_THEN `sp:linear_scan_hidden_state`
    (CONJUNCTS_THEN2 (LABEL_TAC "peq") (CONJUNCTS_THEN2 (LABEL_TAC "prec")
    (CONJUNCTS_THEN2 (LABEL_TAC "plen") (CONJUNCTS_THEN2 (LABEL_TAC "pmr")
    (CONJUNCTS_THEN2 (LABEL_TAC "pperm") (CONJUNCTS_THEN2 (LABEL_TAC "pel")
    (CONJUNCTS_THEN2 (LABEL_TAC "plo") (LABEL_TAC "phi")))))))))) THEN
  USE_THEN "peq" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
  USE_THEN "prec" (fun th -> LABEL_TAC "pbeg" (REWRITE_RULE(K_THM :: LSCANPAUX_hs_record)
    (AP_TERM `linear_scan_hidden_state_int_beg` th))) THEN
  SUBGOAL_THEN `l + 1 <= mid /\ mid <= r` (LABEL_TAC "midb") THENL
   [USE_THEN "pmr" MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `EL l (linear_scan_hidden_state_sorted_regs sp) =
                EL l (linear_scan_hidden_state_sorted_regs sth)` (LABEL_TAC "pivp") THENL
   [USE_THEN "pel" MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`sp:linear_scan_hidden_state`; `l:num`; `mid - 1`] swap_regs_eq) THEN
  ANTS_TAC THENL [USE_THEN "plen" (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ss:linear_scan_hidden_state` (CONJUNCTS_THEN2 (LABEL_TAC "seq")
    (LABEL_TAC "srec"))) THEN
  USE_THEN "srec" (fun th -> LABEL_TAC "sreg" (REWRITE_RULE(K_THM :: LSCANPAUX_hs_record)
    (AP_TERM `linear_scan_hidden_state_sorted_regs` th))) THEN
  USE_THEN "srec" (fun th -> LABEL_TAC "sbeg0" (REWRITE_RULE(K_THM :: LSCANPAUX_hs_record)
    (AP_TERM `linear_scan_hidden_state_int_beg` th))) THEN
  USE_THEN "seq" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
  SUBGOAL_THEN `~(mid <= l \/ r < mid)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC RAPROOFAUX_msimps THEN
  SUBGOAL_THEN `PERM (linear_scan_hidden_state_sorted_regs sth) (linear_scan_hidden_state_sorted_regs sp)` (LABEL_TAC "pP") THENL
   [MATCH_MP_TAC LSCANPAUX_PERM_TAKE_ALL THEN USE_THEN "plen" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "pperm" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. l <= i /\ i < r ==> EL i (linear_scan_hidden_state_sorted_regs sp) < LENGTH (linear_scan_hidden_state_int_beg sth)` (LABEL_TAC "pbound") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_CASES_TAC `i:num = l` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN USE_THEN "pivp" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "pivlt" ACCEPT_TAC;
      MP_TAC(ISPECL [`\x:num. x < LENGTH (linear_scan_hidden_state_int_beg sth)`; `linear_scan_hidden_state_sorted_regs sth`; `linear_scan_hidden_state_sorted_regs sp`; `l + 1`; `r:num`]
        sort_regs_prop_lemma) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_ARITH_TAC; USE_THEN "rle" ACCEPT_TAC; USE_THEN "pel" ACCEPT_TAC;
          REPEAT STRIP_TAC THEN USE_THEN "inb" MATCH_MP_TAC THEN ASM_ARITH_TAC;
          USE_THEN "pP" ACCEPT_TAC];
        DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `l < LENGTH (linear_scan_hidden_state_sorted_regs sp) /\ mid - 1 < LENGTH (linear_scan_hidden_state_sorted_regs sp)` STRIP_ASSUME_TAC THENL
   [USE_THEN "plen" (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!i. l <= i /\ i < r ==> EL i (linear_scan_hidden_state_sorted_regs ss) < LENGTH (linear_scan_hidden_state_int_beg sth)` (LABEL_TAC "sbound") THENL
   [USE_THEN "sreg" (fun th -> REWRITE_TAC[th]) THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[EL_LUPDATE; LENGTH_LUPDATE] THEN
    REPEAT COND_CASES_TAC THEN USE_THEN "pbound" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH (linear_scan_hidden_state_sorted_regs ss) = LENGTH (linear_scan_hidden_state_sorted_regs sth)` (LABEL_TAC "slen") THENL
   [USE_THEN "sreg" (fun th -> REWRITE_TAC[th; LENGTH_LUPDATE]) THEN
    USE_THEN "plen" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `PERM (linear_scan_hidden_state_sorted_regs sp) (linear_scan_hidden_state_sorted_regs ss)` (LABEL_TAC "sP") THENL
   [MATCH_MP_TAC LSCANPAUX_PERM_TAKE_ALL THEN
    USE_THEN "slen" (fun a -> USE_THEN "plen" (fun b -> REWRITE_TAC[a; b])) THEN
    USE_THEN "seq" (MP_TAC o SPEC `LENGTH (linear_scan_hidden_state_sorted_regs sth)` o MATCH_MP swap_regs_perm) THEN
    USE_THEN "plen" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "sbeg0" (fun a -> USE_THEN "pbeg" (fun b ->
    LABEL_TAC "sbeg" (TRANS a b))) THEN
  (* the left recursive call *)
  REMOVE_THEN "ihl" (MP_TAC o SPEC `mid:num`) THEN
  USE_THEN "rl" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `~(mid <= l \/ r < mid)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `ss:linear_scan_hidden_state`) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; GSYM intbeg_less_def] THEN
  USE_THEN "sbeg" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "slen" (fun th -> REWRITE_TAC[th]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "sbound" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sq:linear_scan_hidden_state`
    (CONJUNCTS_THEN2 (LABEL_TAC "qeq") (CONJUNCTS_THEN2 (LABEL_TAC "qrec")
    (CONJUNCTS_THEN2 (LABEL_TAC "qlen") (CONJUNCTS_THEN2 (LABEL_TAC "qperm")
    (CONJUNCTS_THEN2 (LABEL_TAC "qel") (LABEL_TAC "qsorted"))))))) THEN
  USE_THEN "qrec" (fun th -> USE_THEN "sbeg" (fun b -> LABEL_TAC "qbeg"
    (TRANS (REWRITE_RULE(K_THM :: LSCANPAUX_hs_record)
      (AP_TERM `linear_scan_hidden_state_int_beg` th)) b))) THEN
  SUBGOAL_THEN `PERM (linear_scan_hidden_state_sorted_regs ss) (linear_scan_hidden_state_sorted_regs sq)` (LABEL_TAC "qP") THENL
   [MATCH_MP_TAC LSCANPAUX_PERM_TAKE_ALL THEN
    USE_THEN "qlen" (fun a -> USE_THEN "slen" (fun b -> REWRITE_TAC[a; b])) THEN
    USE_THEN "slen" (fun th -> REWRITE_TAC[GSYM th]) THEN
    USE_THEN "qperm" MATCH_MP_TAC THEN USE_THEN "slen" (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* the right recursive call *)
  REMOVE_THEN "ihr" (MP_TAC o SPEC `mid:num`) THEN
  USE_THEN "rl" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `~(mid <= l \/ r < mid)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `sq:linear_scan_hidden_state`) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; GSYM intbeg_less_def] THEN
  USE_THEN "qbeg" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "qlen" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "slen" (fun th -> REWRITE_TAC[th]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `EL i (linear_scan_hidden_state_sorted_regs sq) = EL i (linear_scan_hidden_state_sorted_regs ss)` SUBST1_TAC THENL
       [USE_THEN "qel" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "sbound" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sthout:linear_scan_hidden_state`
    (CONJUNCTS_THEN2 (LABEL_TAC "req") (CONJUNCTS_THEN2 (LABEL_TAC "rrec")
    (CONJUNCTS_THEN2 (LABEL_TAC "rlen") (CONJUNCTS_THEN2 (LABEL_TAC "rperm")
    (CONJUNCTS_THEN2 (LABEL_TAC "rel") (LABEL_TAC "rsorted"))))))) THEN
  SUBGOAL_THEN `PERM (linear_scan_hidden_state_sorted_regs sq) (linear_scan_hidden_state_sorted_regs sthout)` (LABEL_TAC "rP") THENL
   [MATCH_MP_TAC LSCANPAUX_PERM_TAKE_ALL THEN
    USE_THEN "rlen" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "qlen" (fun a -> USE_THEN "slen" (fun b -> REWRITE_TAC[a; b])) THEN
    USE_THEN "rperm" MATCH_MP_TAC THEN
    USE_THEN "qlen" (fun a -> USE_THEN "slen" (fun b -> REWRITE_TAC[a; b])) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "qeq" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
  EXISTS_TAC `sthout:linear_scan_hidden_state` THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "req" ACCEPT_TAC;
    USE_THEN "rrec" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    USE_THEN "qrec" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    USE_THEN "srec" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
    USE_THEN "prec" (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
    REWRITE_TAC(K_THM :: o_THM :: LSCANPAUX_hs_record);
    USE_THEN "rlen" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "qlen" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "slen" ACCEPT_TAC;
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC PERM_TRANS THEN EXISTS_TAC `TAKE n (linear_scan_hidden_state_sorted_regs sp)` THEN CONJ_TAC THENL
     [USE_THEN "pperm" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC PERM_TRANS THEN EXISTS_TAC `TAKE n (linear_scan_hidden_state_sorted_regs ss)` THEN CONJ_TAC THENL
     [USE_THEN "seq" (MP_TAC o SPEC `n:num` o MATCH_MP swap_regs_perm) THEN
      DISCH_THEN MATCH_MP_TAC THEN USE_THEN "plen" (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC PERM_TRANS THEN EXISTS_TAC `TAKE n (linear_scan_hidden_state_sorted_regs sq)` THEN CONJ_TAC THENL
     [USE_THEN "qperm" MATCH_MP_TAC THEN USE_THEN "slen" (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC;
      USE_THEN "rperm" MATCH_MP_TAC THEN
      USE_THEN "qlen" (fun a -> USE_THEN "slen" (fun b -> REWRITE_TAC[a; b])) THEN
      ASM_ARITH_TAC];
    X_GEN_TAC `ind:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `EL ind (linear_scan_hidden_state_sorted_regs sthout) = EL ind (linear_scan_hidden_state_sorted_regs sq) /\ EL ind (linear_scan_hidden_state_sorted_regs sq) = EL ind (linear_scan_hidden_state_sorted_regs ss) /\
                  EL ind (linear_scan_hidden_state_sorted_regs ss) = EL ind (linear_scan_hidden_state_sorted_regs sp) /\ EL ind (linear_scan_hidden_state_sorted_regs sp) = EL ind (linear_scan_hidden_state_sorted_regs sth)`
      (fun th -> REWRITE_TAC[th]) THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "rel" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      USE_THEN "qel" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      USE_THEN "sreg" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[EL_LUPDATE] THEN
      SUBGOAL_THEN `~(ind = mid - 1) /\ ~(ind:num = l)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC;
      USE_THEN "pel" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    MATCH_MP_TAC(ISPECL [`intbeg_less (linear_scan_hidden_state_int_beg sth)`; `linear_scan_hidden_state_sorted_regs sthout`; `l:num`; `mid - 1`; `r:num`;
      `EL l (linear_scan_hidden_state_sorted_regs sth)`] LSCANPAUX_qsort_combine) THEN
    REWRITE_TAC[intbeg_less_transitive; LSCANPAUX_intbeg_less_refl] THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      ASM_ARITH_TAC;
      SUBGOAL_THEN `EL (mid - 1) (linear_scan_hidden_state_sorted_regs sthout) = EL (mid - 1) (linear_scan_hidden_state_sorted_regs sq) /\
                    EL (mid - 1) (linear_scan_hidden_state_sorted_regs sq) = EL (mid - 1) (linear_scan_hidden_state_sorted_regs ss)` (fun th -> REWRITE_TAC[th]) THENL
       [CONJ_TAC THENL
         [USE_THEN "rel" MATCH_MP_TAC THEN ASM_ARITH_TAC;
          USE_THEN "qel" MATCH_MP_TAC THEN ARITH_TAC];
        ALL_TAC] THEN
      USE_THEN "sreg" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[EL_LUPDATE; LENGTH_LUPDATE] THEN
      REWRITE_TAC[ASSUME `mid - 1 < LENGTH (linear_scan_hidden_state_sorted_regs sp)`] THEN
      USE_THEN "pivp" ACCEPT_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `EL i (linear_scan_hidden_state_sorted_regs sthout) = EL i (linear_scan_hidden_state_sorted_regs sq)` SUBST1_TAC THENL
       [USE_THEN "rel" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`\x:num. intbeg_less (linear_scan_hidden_state_int_beg sth) x (EL l (linear_scan_hidden_state_sorted_regs sth))`; `linear_scan_hidden_state_sorted_regs ss`; `linear_scan_hidden_state_sorted_regs sq`; `l:num`;
        `mid - 1`] sort_regs_prop_lemma) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [USE_THEN "slen" (fun th -> REWRITE_TAC[th]) THEN REPEAT CONJ_TAC THENL
         [ASM_ARITH_TAC; ASM_ARITH_TAC; USE_THEN "qel" ACCEPT_TAC;
          X_GEN_TAC `ind:num` THEN STRIP_TAC THEN
          USE_THEN "sreg" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[EL_LUPDATE] THEN
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `~(ind = mid - 1)` (fun th -> REWRITE_TAC[th]) THENL
           [ASM_ARITH_TAC; ALL_TAC] THEN
          COND_CASES_TAC THEN USE_THEN "plo" MATCH_MP_TAC THEN ASM_ARITH_TAC;
          USE_THEN "qP" ACCEPT_TAC];
        DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`\x:num. intbeg_less (linear_scan_hidden_state_int_beg sth) (EL l (linear_scan_hidden_state_sorted_regs sth)) x`; `linear_scan_hidden_state_sorted_regs sq`; `linear_scan_hidden_state_sorted_regs sthout`; `mid:num`;
        `r:num`] sort_regs_prop_lemma) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [USE_THEN "qlen" (fun a -> USE_THEN "slen" (fun b -> REWRITE_TAC[a; b])) THEN
        REPEAT CONJ_TAC THENL
         [ASM_ARITH_TAC; ASM_ARITH_TAC; USE_THEN "rel" ACCEPT_TAC;
          X_GEN_TAC `ind:num` THEN STRIP_TAC THEN
          SUBGOAL_THEN `EL ind (linear_scan_hidden_state_sorted_regs sq) = EL ind (linear_scan_hidden_state_sorted_regs ss)` SUBST1_TAC THENL
           [USE_THEN "qel" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
          USE_THEN "sreg" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[EL_LUPDATE] THEN
          SUBGOAL_THEN `~(ind = mid - 1) /\ ~(ind:num = l)` (fun th -> REWRITE_TAC[th]) THENL
           [ASM_ARITH_TAC; ALL_TAC] THEN
          USE_THEN "phi" MATCH_MP_TAC THEN ASM_ARITH_TAC;
          USE_THEN "rP" ACCEPT_TAC];
        DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `EL i1 (linear_scan_hidden_state_sorted_regs sthout) = EL i1 (linear_scan_hidden_state_sorted_regs sq) /\ EL i2 (linear_scan_hidden_state_sorted_regs sthout) = EL i2 (linear_scan_hidden_state_sorted_regs sq)`
        (fun th -> REWRITE_TAC[th]) THENL
       [CONJ_TAC THEN USE_THEN "rel" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "qsorted" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "rsorted" MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;


(* HOL4 line 4241 *)
let swap_moves_eq = prove
 (`!sth i1 i2.
     i1 < LENGTH (linear_scan_hidden_state_sorted_moves sth) /\
     i2 < LENGTH (linear_scan_hidden_state_sorted_moves sth) ==>
     ?sthout.
       swap_moves i1 i2 sth = (M_success one,sthout) /\
       sthout =
         linear_scan_hidden_state_sorted_moves_fupd
           (K (LUPDATE (EL i1 (linear_scan_hidden_state_sorted_moves sth)) i2
                 (LUPDATE (EL i2 (linear_scan_hidden_state_sorted_moves sth)) i1
                    (linear_scan_hidden_state_sorted_moves sth)))) sth`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC(swap_moves_def :: sorted_moves_sub_eqn :: update_sorted_moves_eqn ::
              RAPROOFAUX_msimps) THEN
  ASM_REWRITE_TAC(case_def "prod" :: case_def "exc" :: K_THM :: LENGTH_LUPDATE ::
                  LSCANPAUX_hs_record) THEN
  REWRITE_TAC[PAIR_EQ; UNWIND_THM1] THEN
  REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
  REWRITE_TAC(K_THM :: o_THM :: LSCANPAUX_hs_record));;

(* HOL4 line 4250 *)
let swap_moves_correct = prove
 (`!sth i1 i2.
     i1 < LENGTH (linear_scan_hidden_state_sorted_moves sth) /\
     i2 < LENGTH (linear_scan_hidden_state_sorted_moves sth) ==>
     ?sthout.
       swap_moves i1 i2 sth = (M_success one,sthout) /\
       sthout = linear_scan_hidden_state_sorted_moves_fupd
                  (K (linear_scan_hidden_state_sorted_moves sthout)) sth /\
       LENGTH (linear_scan_hidden_state_sorted_moves sthout) =
         LENGTH (linear_scan_hidden_state_sorted_moves sth) /\
       (!n. i1 < n /\ i2 < n /\ n <= LENGTH (linear_scan_hidden_state_sorted_moves sth) ==>
            PERM (TAKE n (linear_scan_hidden_state_sorted_moves sth))
                 (TAKE n (linear_scan_hidden_state_sorted_moves sthout)))`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`sth:linear_scan_hidden_state`; `i1:num`; `i2:num`] swap_moves_eq) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:linear_scan_hidden_state` (CONJUNCTS_THEN2 ASSUME_TAC
    SUBST_ALL_TAC)) THEN
  (fun (asl,w as g) ->
     let eq = concl(snd(find (fun (_,th) -> is_eq(concl th) &&
                is_comb(lhs(concl th)) &&
                can (find_term ((=) `swap_moves`)) (lhs(concl th))) asl)) in
     EXISTS_TAC (snd(dest_pair(rhs eq))) g) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC(K_THM :: LENGTH_LUPDATE :: LSCANPAUX_hs_record) THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LUPDATE_TAKE; LENGTH_LUPDATE] THEN
  SUBGOAL_THEN
   `EL i1 (linear_scan_hidden_state_sorted_moves sth) =
    EL i1 (TAKE n (linear_scan_hidden_state_sorted_moves sth)) /\
    EL i2 (linear_scan_hidden_state_sorted_moves sth) =
    EL i2 (TAKE n (linear_scan_hidden_state_sorted_moves sth))`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_SIMP_TAC[EL_TAKE]; ALL_TAC] THEN
  MATCH_MP_TAC swap_perm_lemma THEN ASM_SIMP_TAC[LENGTH_TAKE]);;

(* HOL4 line 4264 *)
let partition_moves_correct = prove
 (`!l ppiv r sth.
     l <= LENGTH (linear_scan_hidden_state_sorted_moves sth) /\
     r <= LENGTH (linear_scan_hidden_state_sorted_moves sth) ==>
     ?mid sthout.
       partition_moves l ppiv r sth = (M_success mid,sthout) /\
       (l <= r ==> l <= mid /\ mid <= r) /\
       sthout = linear_scan_hidden_state_sorted_moves_fupd
                  (K (linear_scan_hidden_state_sorted_moves sthout)) sth /\
       LENGTH (linear_scan_hidden_state_sorted_moves sthout) =
         LENGTH (linear_scan_hidden_state_sorted_moves sth) /\
       (!n. l <= n /\ r <= n /\ n <= LENGTH (linear_scan_hidden_state_sorted_moves sth) ==>
            PERM (TAKE n (linear_scan_hidden_state_sorted_moves sth))
                 (TAKE n (linear_scan_hidden_state_sorted_moves sthout)))`,
    MATCH_MP_TAC partition_moves_ind THEN
  MAP_EVERY X_GEN_TAC [`l:num`; `ppiv:num`; `r:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihswap") (LABEL_TAC "ihnext")) THEN
  X_GEN_TAC `sth:linear_scan_hidden_state` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lle") (LABEL_TAC "rle")) THEN
  ONCE_REWRITE_TAC[partition_moves_def] THEN COND_CASES_TAC THENL
   [REWRITE_TAC RAPROOFAUX_msimps THEN
    MAP_EVERY EXISTS_TAC [`l:num`; `sth:linear_scan_hidden_state`] THEN
    REWRITE_TAC[PERM_REFL; LE_REFL] THEN
    REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
    REWRITE_TAC(K_THM :: LSCANPAUX_hs_record);
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "rl") THEN
  SUBGOAL_THEN `l < LENGTH (linear_scan_hidden_state_sorted_moves sth)` (LABEL_TAC "llt") THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC(sorted_moves_sub_eqn :: RAPROOFAUX_msimps) THEN
  USE_THEN "llt" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
  ASM_CASES_TAC `FST (EL l (linear_scan_hidden_state_sorted_moves sth)) < ppiv` THEN
  POP_ASSUM(fun th -> REWRITE_TAC[th] THEN LABEL_TAC "cond" th) THENL
   [REMOVE_THEN "ihnext" (MP_TAC o SPEC
      `FST (EL l (linear_scan_hidden_state_sorted_moves sth))`) THEN
    USE_THEN "rl" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "cond" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(MP_TAC o SPEC `sth:linear_scan_hidden_state`) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [ASM_ARITH_TAC; USE_THEN "rle" ACCEPT_TAC]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `mid:num` (X_CHOOSE_THEN `sthout:linear_scan_hidden_state`
      (CONJUNCTS_THEN2 (LABEL_TAC "eq") (CONJUNCTS_THEN2 (LABEL_TAC "mr")
      (CONJUNCTS_THEN2 (LABEL_TAC "rec") (CONJUNCTS_THEN2 (LABEL_TAC "len")
        (LABEL_TAC "perm"))))))) THEN
    MAP_EVERY EXISTS_TAC [`mid:num`; `sthout:linear_scan_hidden_state`] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "eq" ACCEPT_TAC;
      DISCH_TAC THEN USE_THEN "mr" MP_TAC THEN ASM_ARITH_TAC;
      USE_THEN "rec" ACCEPT_TAC;
      USE_THEN "len" ACCEPT_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "perm" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    MP_TAC(SPECL [`sth:linear_scan_hidden_state`; `l:num`; `r - 1`] swap_moves_correct) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:linear_scan_hidden_state`
      (CONJUNCTS_THEN2 (LABEL_TAC "seq") (CONJUNCTS_THEN2 (LABEL_TAC "srec")
      (CONJUNCTS_THEN2 (LABEL_TAC "slen") (LABEL_TAC "sperm"))))) THEN
    USE_THEN "seq" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
    REMOVE_THEN "ihswap" (MP_TAC o SPEC
      `FST (EL l (linear_scan_hidden_state_sorted_moves sth))`) THEN
    USE_THEN "rl" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "cond" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(MP_TAC o SPEC `s1:linear_scan_hidden_state`) THEN
    USE_THEN "slen" (fun th -> REWRITE_TAC[th]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `mid:num` (X_CHOOSE_THEN `sthout:linear_scan_hidden_state`
      (CONJUNCTS_THEN2 (LABEL_TAC "eq") (CONJUNCTS_THEN2 (LABEL_TAC "mr")
      (CONJUNCTS_THEN2 (LABEL_TAC "rec") (CONJUNCTS_THEN2 (LABEL_TAC "len")
        (LABEL_TAC "perm"))))))) THEN
    MAP_EVERY EXISTS_TAC [`mid:num`; `sthout:linear_scan_hidden_state`] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[] THEN USE_THEN "eq" ACCEPT_TAC;
      DISCH_TAC THEN USE_THEN "mr" MP_TAC THEN ASM_ARITH_TAC;
      USE_THEN "rec" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      USE_THEN "srec" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
      REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
      REWRITE_TAC(K_THM :: o_THM :: LSCANPAUX_hs_record);
      USE_THEN "len" ACCEPT_TAC;
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN MATCH_MP_TAC PERM_TRANS THEN
      EXISTS_TAC `TAKE n (linear_scan_hidden_state_sorted_moves s1)` THEN CONJ_TAC THENL
       [USE_THEN "sperm" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        USE_THEN "perm" MATCH_MP_TAC THEN ASM_ARITH_TAC]]]);;

(* HOL4 line 4297 (sort_moves is linear_scan_sort_moves) *)
let sort_moves_correct = prove
 (`!l r sth.
     l <= LENGTH (linear_scan_hidden_state_sorted_moves sth) /\
     r <= LENGTH (linear_scan_hidden_state_sorted_moves sth) ==>
     ?sthout.
       linear_scan_sort_moves l r sth = (M_success one,sthout) /\
       sthout = linear_scan_hidden_state_sorted_moves_fupd
                  (K (linear_scan_hidden_state_sorted_moves sthout)) sth /\
       LENGTH (linear_scan_hidden_state_sorted_moves sthout) =
         LENGTH (linear_scan_hidden_state_sorted_moves sth) /\
       (!n. l <= n /\ r <= n /\ n <= LENGTH (linear_scan_hidden_state_sorted_moves sth) ==>
            PERM (TAKE n (linear_scan_hidden_state_sorted_moves sth))
                 (TAKE n (linear_scan_hidden_state_sorted_moves sthout)))`,
    MATCH_MP_TAC linear_scan_sort_moves_ind THEN MAP_EVERY X_GEN_TAC [`l:num`; `r:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ihl") (LABEL_TAC "ihr")) THEN
  X_GEN_TAC `sth:linear_scan_hidden_state` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lle") (LABEL_TAC "rle")) THEN
  ONCE_REWRITE_TAC[linear_scan_sort_moves_def] THEN COND_CASES_TAC THENL
   [REWRITE_TAC RAPROOFAUX_msimps THEN EXISTS_TAC `sth:linear_scan_hidden_state` THEN
    REWRITE_TAC[PERM_REFL] THEN
    REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
    REWRITE_TAC(K_THM :: LSCANPAUX_hs_record);
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "rl") THEN
  SUBGOAL_THEN `l < LENGTH (linear_scan_hidden_state_sorted_moves sth)` (LABEL_TAC "llt") THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC(sorted_moves_sub_eqn :: RAPROOFAUX_msimps) THEN
  USE_THEN "llt" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
  MP_TAC(SPECL [`l + 1`; `FST (EL l (linear_scan_hidden_state_sorted_moves sth))`; `r:num`;
    `sth:linear_scan_hidden_state`] partition_moves_correct) THEN
  ANTS_TAC THENL [CONJ_TAC THENL [ASM_ARITH_TAC; USE_THEN "rle" ACCEPT_TAC]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mid:num` (X_CHOOSE_THEN `sp:linear_scan_hidden_state`
    (CONJUNCTS_THEN2 (LABEL_TAC "peq") (CONJUNCTS_THEN2 (LABEL_TAC "pmr")
    (CONJUNCTS_THEN2 (LABEL_TAC "prec") (CONJUNCTS_THEN2 (LABEL_TAC "plen")
      (LABEL_TAC "pperm"))))))) THEN
  USE_THEN "peq" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
  SUBGOAL_THEN `l + 1 <= mid /\ mid <= r` (LABEL_TAC "midb") THENL
   [USE_THEN "pmr" MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`sp:linear_scan_hidden_state`; `l:num`; `mid - 1`] swap_moves_correct) THEN
  ANTS_TAC THENL [USE_THEN "plen" (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ss:linear_scan_hidden_state`
    (CONJUNCTS_THEN2 (LABEL_TAC "seq") (CONJUNCTS_THEN2 (LABEL_TAC "srec")
    (CONJUNCTS_THEN2 (LABEL_TAC "slen") (LABEL_TAC "sperm"))))) THEN
  USE_THEN "seq" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
  SUBGOAL_THEN `~(mid <= l \/ r < mid)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC RAPROOFAUX_msimps THEN
  REMOVE_THEN "ihl" (MP_TAC o SPEC `mid:num`) THEN
  USE_THEN "rl" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `~(mid <= l \/ r < mid)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `ss:linear_scan_hidden_state`) THEN
  USE_THEN "slen" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "plen" (fun th -> REWRITE_TAC[th]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sq:linear_scan_hidden_state`
    (CONJUNCTS_THEN2 (LABEL_TAC "qeq") (CONJUNCTS_THEN2 (LABEL_TAC "qrec")
    (CONJUNCTS_THEN2 (LABEL_TAC "qlen") (LABEL_TAC "qperm"))))) THEN
  USE_THEN "qeq" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
  REMOVE_THEN "ihr" (MP_TAC o SPEC `mid:num`) THEN
  USE_THEN "rl" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `~(mid <= l \/ r < mid)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `sq:linear_scan_hidden_state`) THEN
  USE_THEN "qlen" (fun th -> REWRITE_TAC[th]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sthout:linear_scan_hidden_state`
    (CONJUNCTS_THEN2 (LABEL_TAC "req") (CONJUNCTS_THEN2 (LABEL_TAC "rrec")
    (CONJUNCTS_THEN2 (LABEL_TAC "rlen") (LABEL_TAC "rperm"))))) THEN
  EXISTS_TAC `sthout:linear_scan_hidden_state` THEN REPEAT CONJ_TAC THENL
   [USE_THEN "req" ACCEPT_TAC;
    USE_THEN "rrec" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    USE_THEN "qrec" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    USE_THEN "srec" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
    USE_THEN "prec" (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
    REWRITE_TAC(K_THM :: o_THM :: LSCANPAUX_hs_record);
    USE_THEN "rlen" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "qlen" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "slen" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "plen" ACCEPT_TAC;
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC PERM_TRANS THEN
    EXISTS_TAC `TAKE n (linear_scan_hidden_state_sorted_moves sp)` THEN CONJ_TAC THENL
     [USE_THEN "pperm" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC PERM_TRANS THEN
    EXISTS_TAC `TAKE n (linear_scan_hidden_state_sorted_moves ss)` THEN CONJ_TAC THENL
     [USE_THEN "sperm" MATCH_MP_TAC THEN USE_THEN "plen" (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC PERM_TRANS THEN
    EXISTS_TAC `TAKE n (linear_scan_hidden_state_sorted_moves sq)` THEN CONJ_TAC THENL
     [USE_THEN "qperm" MATCH_MP_TAC THEN
      USE_THEN "slen" (fun a -> USE_THEN "plen" (fun b -> REWRITE_TAC[a; b])) THEN
      ASM_ARITH_TAC;
      USE_THEN "rperm" MATCH_MP_TAC THEN
      USE_THEN "qlen" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "slen" (fun a -> USE_THEN "plen" (fun b -> REWRITE_TAC[a; b])) THEN
      ASM_ARITH_TAC]]);;

(* HOL4 line 4332 *)
let list_minimum = prove
 (`!(f:num->int) (l:num list). ?x:int. ALL (\y. x <= f y) l`,
    GEN_TAC THEN LIST_INDUCT_TAC THENL [EXISTS_TAC `&0:int` THEN REWRITE_TAC[ALL]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x:int`) THEN
  ASM_CASES_TAC `x <= (f:num->int) h` THENL
   [EXISTS_TAC `x:int` THEN ASM_REWRITE_TAC[ALL];
    EXISTS_TAC `(f:num->int) h` THEN REWRITE_TAC[ALL; INT_LE_REFL] THEN
    UNDISCH_TAC `ALL (\y. x <= (f:num->int) y) t` THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    POP_ASSUM MP_TAC THEN MESON_TAC[INT_LE_TRANS; INT_NOT_LE; INT_LT_IMP_LE]]);;


(* HOL4 line 4350 *)
let linear_reg_alloc_pass1_initial_state_invariants = prove
 (`!sth (reglist:num list) forced k (st:linear_scan_state).
     LENGTH (linear_scan_hidden_state_int_beg sth) =
       LENGTH (linear_scan_hidden_state_colors sth) /\
     LENGTH (linear_scan_hidden_state_int_end sth) =
       LENGTH (linear_scan_hidden_state_colors sth) ==>
     ?pos.
       good_linear_scan_state (linear_reg_alloc_pass1_initial_state k) sth [] pos forced 0 /\
       ALL (\r. pos <= EL r (linear_scan_hidden_state_int_beg sth)) reglist`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\r. EL r (linear_scan_hidden_state_int_beg sth)`; `reglist:num list`]
    list_minimum) THEN
  DISCH_THEN(X_CHOOSE_TAC `pos:int`) THEN EXISTS_TAC `pos:int` THEN
  POP_ASSUM(fun th -> REWRITE_TAC[REWRITE_RULE[] th]) THEN
  REWRITE_TAC(good_linear_scan_state_def :: linear_reg_alloc_pass1_initial_state_def ::
              LSCANPAUX_st_record) THEN
  ASM_REWRITE_TAC[MEM; ALL; APPEND; MAP; FILTER; ALL_DISTINCT; SORTED_DEF; LE_0; LE_REFL;
                  domain_def] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; GSYM ALL_MEM; FORALL_PAIR_THM;
              pair_CASE]);;

(* HOL4 line 4365 *)
let linear_reg_alloc_pass2_initial_state_invariants = prove
 (`!sth (reglist:num list) forced k nreg (st:linear_scan_state).
     LENGTH (linear_scan_hidden_state_int_beg sth) =
       LENGTH (linear_scan_hidden_state_colors sth) /\
     LENGTH (linear_scan_hidden_state_int_end sth) =
       LENGTH (linear_scan_hidden_state_colors sth) ==>
     ?pos.
       good_linear_scan_state (linear_reg_alloc_pass2_initial_state k nreg) sth [] pos
         forced k /\
       ALL (\r. pos <= EL r (linear_scan_hidden_state_int_beg sth)) reglist`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\r. EL r (linear_scan_hidden_state_int_beg sth)`; `reglist:num list`]
    list_minimum) THEN
  DISCH_THEN(X_CHOOSE_TAC `pos:int`) THEN EXISTS_TAC `pos:int` THEN
  POP_ASSUM(fun th -> REWRITE_TAC[REWRITE_RULE[] th]) THEN
  REWRITE_TAC(good_linear_scan_state_def :: linear_reg_alloc_pass2_initial_state_def ::
              LSCANPAUX_st_record) THEN
  ASM_REWRITE_TAC[MEM; ALL; APPEND; MAP; FILTER; ALL_DISTINCT; SORTED_DEF; LE_0; LE_REFL;
                  LE_ADD; domain_def] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; GSYM ALL_MEM; FORALL_PAIR_THM;
              pair_CASE]);;

(* LSCANPAUX_FILTER_good: st_ex_FILTER_good with a pure predicate *)
let LSCANPAUX_FILTER_good = prove
 (`!(P:A->S->(bool,E)exc#S) Q l s.
     (!r. MEM r l ==> P r s = (M_success (Q r),s)) ==>
     st_ex_FILTER_good P l s = (M_success (FILTER Q l),s)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC(st_ex_FILTER_good_def :: FILTER :: MEM :: RAPROOFAUX_msimps) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(P:A->S->(bool,E)exc#S) h s = (M_success (Q h),s)` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[case_def "prod"; case_def "exc"] THEN
  SUBGOAL_THEN `st_ex_FILTER_good (P:A->S->(bool,E)exc#S) t s = (M_success (FILTER Q t),s)`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC(case_def "prod" :: case_def "exc" :: RAPROOFAUX_msimps));;

(* HOL4 line 4380 *)
let st_ex_FILTER_good_stack = prove
 (`!reglist sth k.
     ALL (\r. r < LENGTH (linear_scan_hidden_state_colors sth)) reglist ==>
     st_ex_FILTER_good
       (\r. st_ex_bind (colors_sub r) (\col. st_ex_return (is_stack_var r \/ k <= col)))
       reglist sth =
     (M_success (FILTER (\r. is_stack_var r \/ k <= EL r (linear_scan_hidden_state_colors sth))
                  reglist),sth)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LSCANPAUX_FILTER_good THEN
  X_GEN_TAC `r:num` THEN DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `r < LENGTH (linear_scan_hidden_state_colors sth)` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\r. r < LENGTH (linear_scan_hidden_state_colors sth)) reglist` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC(colors_sub_eqn :: case_def "prod" :: case_def "exc" :: RAPROOFAUX_msimps));;

(* HOL4 line 4396 *)
let lookup_fromAList_MAP_not_NONE = prove
 (`!r l. ~(lookup r (fromAList (MAP (\r. (r,one)) l)) = NONE) <=> MEM r l`,
    REWRITE_TAC[lookup_NONE_domain; domain_fromAList; IN_SET_OF_LIST] THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `MAP FST (MAP (\r:num. (r,one)) l) = l` (fun th -> REWRITE_TAC[th]) THEN
  SPEC_TAC(`l:num list`,`l:num list`) THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP]);;

(* HOL4 line 4408: PERM_PARTITION *)
let linear_scanProof_PERM_PARTITION = prove
 (`!(P:A->bool) l. PERM l (APPEND (FILTER (\x. P x) l) (FILTER (\x. ~P x) l))`,
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; APPEND; PERM_REFL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[APPEND; PERM_CONS_IFF] THEN
  REWRITE_TAC[PERM_CONS_EQ_APPEND] THEN
  MAP_EVERY EXISTS_TAC [`FILTER (\x. (P:A->bool) x) t`; `FILTER (\x. ~(P:A->bool) x) t`] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 4418 *)
let forbidden_is_from_forced_take_sublist = prove
 (CASE_TERM
  `!l forced int_beg forced_adj.
     ALL (\r12. match r12 with (r1,r2) -> MEM r1 l /\ MEM r2 l) forced /\
     (!r. forbidden_is_from_forced forced int_beg r (misc_the [] (lookup r forced_adj))) ==>
     (!r. forbidden_is_from_forced_sublist l forced int_beg r
            (misc_the [] (lookup r forced_adj)))`,
    REPEAT GEN_TAC THEN
  REWRITE_TAC[forbidden_is_from_forced_def; forbidden_is_from_forced_sublist_def;
              GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fm") (LABEL_TAC "ff")) THEN
  MAP_EVERY X_GEN_TAC [`r:num`; `reg2:num`] THEN
  USE_THEN "ff" (fun th -> REWRITE_TAC[GSYM(SPECL [`r:num`; `reg2:num`] th)]) THEN
  USE_THEN "fm" MP_TAC THEN MESON_TAC[]);;

(* HOL4 line 4427 *)
let good_linear_scan_state_REVERSE = prove
 (`!st sth l pos forced mincol.
     good_linear_scan_state st sth (REVERSE l) pos forced mincol <=>
     good_linear_scan_state st sth l pos forced mincol`,
    REWRITE_TAC[good_linear_scan_state_def; MEM_REVERSE; EVERY_REVERSE; FILTER_REVERSE;
              GSYM MAP_REVERSE; ALL_DISTINCT_REVERSE; ALL_APPEND]);;

(* HOL4 line 4437 *)
let phystack_on_stack_REVERSE = prove
 (`!l st sth. phystack_on_stack (REVERSE l) st sth <=> phystack_on_stack l st sth`,
    REWRITE_TAC[phystack_on_stack_def; MEM_REVERSE]);;

(* HOL4 line 4443 *)
let FILTER_remove_MEM_l = prove
 (`!(P:A->bool) l. FILTER (\x. P x /\ MEM x l) l = FILTER (\x. P x) l`,
    SUBGOAL_THEN `!(P:A->bool) l1 l2. (!x. MEM x l1 ==> MEM x l2) ==>
                  FILTER (\x. P x /\ MEM x l2) l1 = FILTER (\x. P x) l1`
    (fun th -> MESON_TAC[th]) THEN
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; MEM] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MEM (h:A) l2` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONS_11] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 4452 *)
let le_div_2 = prove
 (`!k r. k <= r DIV 2 <=> 2 * k <= r`,
    SIMP_TAC[LE_RDIV_EQ; ARITH_EQ]);;

(* HOL4 line 4458 *)
let lt_div_2 = prove
 (`!k r. r DIV 2 < k <=> r < 2 * k`,
    SIMP_TAC[RDIV_LT_EQ; ARITH_EQ]);;


(* HOL4 line 4464 *)
let list_to_sorted_regs_correct = prove
 (`!l n sth.
     n + LENGTH l <= LENGTH (linear_scan_hidden_state_sorted_regs sth) ==>
     ?sthout.
       (M_success one,sthout) = list_to_sorted_regs l n sth /\
       LENGTH (linear_scan_hidden_state_sorted_regs sthout) =
         LENGTH (linear_scan_hidden_state_sorted_regs sth) /\
       sthout = linear_scan_hidden_state_sorted_regs_fupd
                  (K (linear_scan_hidden_state_sorted_regs sthout)) sth /\
       TAKE n (linear_scan_hidden_state_sorted_regs sthout) =
         TAKE n (linear_scan_hidden_state_sorted_regs sth) /\
       TAKE (LENGTH l) (DROP n (linear_scan_hidden_state_sorted_regs sthout)) = l`,
    LIST_INDUCT_TAC THENL
   [REWRITE_TAC(list_to_sorted_regs_def :: RAPROOFAUX_msimps) THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `sth:linear_scan_hidden_state` THEN REWRITE_TAC[LENGTH; TAKE_0] THEN
    REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
    REWRITE_TAC(K_THM :: LSCANPAUX_hs_record);
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `n < LENGTH (linear_scan_hidden_state_sorted_regs sth)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC(list_to_sorted_regs_def :: update_sorted_regs_eqn :: RAPROOFAUX_msimps) THEN
  ASM_REWRITE_TAC[case_def "prod"; case_def "exc"] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n + 1`;
    `linear_scan_hidden_state_sorted_regs_fupd (K (LUPDATE h n (linear_scan_hidden_state_sorted_regs sth))) sth`]) THEN
  REWRITE_TAC(K_THM :: LENGTH_LUPDATE :: LSCANPAUX_hs_record) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sthout:linear_scan_hidden_state`
    (CONJUNCTS_THEN2 (LABEL_TAC "eq") (CONJUNCTS_THEN2 (LABEL_TAC "len")
    (CONJUNCTS_THEN2 (LABEL_TAC "rec") (CONJUNCTS_THEN2 (LABEL_TAC "tk")
      (LABEL_TAC "dr")))))) THEN
  EXISTS_TAC `sthout:linear_scan_hidden_state` THEN
  SUBGOAL_THEN `n < LENGTH (linear_scan_hidden_state_sorted_regs sthout)` ASSUME_TAC THENL
   [USE_THEN "len" (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < n + 1 ==> EL i (linear_scan_hidden_state_sorted_regs sthout) = EL i (LUPDATE h n (linear_scan_hidden_state_sorted_regs sth))`
    (LABEL_TAC "elq") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "tk" (MP_TAC o AP_TERM `EL (i:num):num list->num`) THEN ASM_SIMP_TAC[EL_TAKE];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "eq" ACCEPT_TAC;
    USE_THEN "len" ACCEPT_TAC;
    USE_THEN "rec" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
    REWRITE_TAC(K_THM :: o_THM :: LSCANPAUX_hs_record);
    REWRITE_TAC[LIST_EQ_REWRITE] THEN
    ASM_SIMP_TAC[LENGTH_TAKE; LT_IMP_LE] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_TAKE] THEN
    USE_THEN "elq" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[EL_LUPDATE] THEN
    SUBGOAL_THEN `~(i:num = n)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[DROP_EL_CONS] THEN
    REWRITE_TAC[TAKE_def; NOT_SUC; SUC_SUB1; CONS_11] THEN
    USE_THEN "dr" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "elq" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[EL_LUPDATE]]);;

(* HOL4 line 4502 *)
let sorted_regs_to_list_correct = prove
 (`!n last sth.
     last <= LENGTH (linear_scan_hidden_state_sorted_regs sth) ==>
     sorted_regs_to_list n last sth =
       (M_success (TAKE (last - n) (DROP n (linear_scan_hidden_state_sorted_regs sth))),sth)`,
    MATCH_MP_TAC sorted_regs_to_list_ind THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `last:num`] THEN DISCH_THEN(LABEL_TAC "ih") THEN
  X_GEN_TAC `sth:linear_scan_hidden_state` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[sorted_regs_to_list_def] THEN COND_CASES_TAC THENL
   [REWRITE_TAC RAPROOFAUX_msimps THEN
    SUBGOAL_THEN `last - n = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[TAKE_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `n < LENGTH (linear_scan_hidden_state_sorted_regs sth)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC(sorted_regs_sub_eqn :: RAPROOFAUX_msimps) THEN
  ASM_REWRITE_TAC[case_def "prod"; case_def "exc"] THEN
  REMOVE_THEN "ih" (fun ih -> MP_TAC(SPEC `sth:linear_scan_hidden_state`
    (MP ih (ASSUME `~(last <= n:num)`)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[case_def "prod"; case_def "exc"; PAIR_EQ; injectivity "exc"] THEN
  ASM_SIMP_TAC[DROP_EL_CONS] THEN
  SUBGOAL_THEN `last - n = SUC (last - (n + 1))` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[TAKE_def; NOT_SUC; SUC_SUB1]);;

(* HOL4 line 4519 *)
let list_to_sorted_moves_correct = prove
 (`!l n sth.
     n + LENGTH l <= LENGTH (linear_scan_hidden_state_sorted_moves sth) ==>
     ?sthout.
       (M_success one,sthout) = list_to_sorted_moves l n sth /\
       LENGTH (linear_scan_hidden_state_sorted_moves sthout) =
         LENGTH (linear_scan_hidden_state_sorted_moves sth) /\
       sthout = linear_scan_hidden_state_sorted_moves_fupd
                  (K (linear_scan_hidden_state_sorted_moves sthout)) sth /\
       TAKE n (linear_scan_hidden_state_sorted_moves sthout) =
         TAKE n (linear_scan_hidden_state_sorted_moves sth) /\
       TAKE (LENGTH l) (DROP n (linear_scan_hidden_state_sorted_moves sthout)) = l`,
    LIST_INDUCT_TAC THENL
   [REWRITE_TAC(list_to_sorted_moves_def :: RAPROOFAUX_msimps) THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `sth:linear_scan_hidden_state` THEN REWRITE_TAC[LENGTH; TAKE_0] THEN
    REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
    REWRITE_TAC(K_THM :: LSCANPAUX_hs_record);
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `n < LENGTH (linear_scan_hidden_state_sorted_moves sth)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC(list_to_sorted_moves_def :: update_sorted_moves_eqn :: RAPROOFAUX_msimps) THEN
  ASM_REWRITE_TAC[case_def "prod"; case_def "exc"] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n + 1`;
    `linear_scan_hidden_state_sorted_moves_fupd (K (LUPDATE h n (linear_scan_hidden_state_sorted_moves sth))) sth`]) THEN
  REWRITE_TAC(K_THM :: LENGTH_LUPDATE :: LSCANPAUX_hs_record) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sthout:linear_scan_hidden_state`
    (CONJUNCTS_THEN2 (LABEL_TAC "eq") (CONJUNCTS_THEN2 (LABEL_TAC "len")
    (CONJUNCTS_THEN2 (LABEL_TAC "rec") (CONJUNCTS_THEN2 (LABEL_TAC "tk")
      (LABEL_TAC "dr")))))) THEN
  EXISTS_TAC `sthout:linear_scan_hidden_state` THEN
  SUBGOAL_THEN `n < LENGTH (linear_scan_hidden_state_sorted_moves sthout)` ASSUME_TAC THENL
   [USE_THEN "len" (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < n + 1 ==> EL i (linear_scan_hidden_state_sorted_moves sthout) = EL i (LUPDATE h n (linear_scan_hidden_state_sorted_moves sth))`
    (LABEL_TAC "elq") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "tk" (MP_TAC o AP_TERM `EL (i:num):(num#num#num)list->num#num#num`) THEN ASM_SIMP_TAC[EL_TAKE];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "eq" ACCEPT_TAC;
    USE_THEN "len" ACCEPT_TAC;
    USE_THEN "rec" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
    REWRITE_TAC(K_THM :: o_THM :: LSCANPAUX_hs_record);
    REWRITE_TAC[LIST_EQ_REWRITE] THEN
    ASM_SIMP_TAC[LENGTH_TAKE; LT_IMP_LE] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_TAKE] THEN
    USE_THEN "elq" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[EL_LUPDATE] THEN
    SUBGOAL_THEN `~(i:num = n)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[DROP_EL_CONS] THEN
    REWRITE_TAC[TAKE_def; NOT_SUC; SUC_SUB1; CONS_11] THEN
    USE_THEN "dr" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "elq" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[EL_LUPDATE]]);;

(* HOL4 line 4557 *)
let sorted_moves_to_list_correct = prove
 (`!n last sth.
     last <= LENGTH (linear_scan_hidden_state_sorted_moves sth) ==>
     sorted_moves_to_list n last sth =
       (M_success (TAKE (last - n) (DROP n (linear_scan_hidden_state_sorted_moves sth))),
        sth)`,
    MATCH_MP_TAC sorted_moves_to_list_ind THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `last:num`] THEN DISCH_THEN(LABEL_TAC "ih") THEN
  X_GEN_TAC `sth:linear_scan_hidden_state` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[sorted_moves_to_list_def] THEN COND_CASES_TAC THENL
   [REWRITE_TAC RAPROOFAUX_msimps THEN
    SUBGOAL_THEN `last - n = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[TAKE_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `n < LENGTH (linear_scan_hidden_state_sorted_moves sth)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC(sorted_moves_sub_eqn :: RAPROOFAUX_msimps) THEN
  ASM_REWRITE_TAC[case_def "prod"; case_def "exc"] THEN
  REMOVE_THEN "ih" (fun ih -> MP_TAC(SPEC `sth:linear_scan_hidden_state`
    (MP ih (ASSUME `~(last <= n:num)`)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[case_def "prod"; case_def "exc"; PAIR_EQ; injectivity "exc"] THEN
  ASM_SIMP_TAC[DROP_EL_CONS] THEN
  SUBGOAL_THEN `last - n = SUC (last - (n + 1))` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[TAKE_def; NOT_SUC; SUC_SUB1]);;


(* LSCANPAUX_INJ_MAP: ALL_DISTINCT (MAP f l) makes f injective on l *)
let LSCANPAUX_INJ_MAP = prove
 (`!(f:A->B) l x y. ALL_DISTINCT (MAP f l) /\ MEM x l /\ MEM y l /\ f x = f y ==> x = y`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP ALL_DISTINCT_INJ_MAP)
    STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[INJ; IN_SET_OF_LIST] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  ASM_REWRITE_TAC[]);;

(* LSCANPAUX_ivl_c: after the second pass the physical registers have      *)
(* distinct colours                                                          *)
let LSCANPAUX_ivl_c = prove
 (`!k reglist stacklist (C1:num list) C2 C3 n.
     ALL_DISTINCT reglist /\ ALL (\r. r < n) reglist /\
     ALL_DISTINCT (MAP (\r. EL r C1) (FILTER is_phy_var reglist)) /\
     (!r1 r2. r1 < n /\ r2 < n ==> EL r1 C2 = EL r2 C2 ==> EL r1 C1 = EL r2 C1) /\
     stacklist = FILTER (\r. is_stack_var r \/ k <= EL r C2) reglist /\
     ALL (\r. k <= EL r C3) stacklist /\
     ALL_DISTINCT (MAP (\r. EL r C3) (FILTER is_phy_var stacklist)) /\
     (!r. ~MEM r stacklist ==> EL r C3 = EL r C2) ==>
     ALL_DISTINCT (MAP (\r. EL r C3) (FILTER is_phy_var reglist))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dist") (CONJUNCTS_THEN2 (LABEL_TAC "lt")
    (CONJUNCTS_THEN2 (LABEL_TAC "d1") (CONJUNCTS_THEN2 (LABEL_TAC "inj2")
    (CONJUNCTS_THEN2 (LABEL_TAC "sl") (CONJUNCTS_THEN2 (LABEL_TAC "kle")
    (CONJUNCTS_THEN2 (LABEL_TAC "d3") (LABEL_TAC "out")))))))) THEN
  MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN
  USE_THEN "dist" (fun th -> REWRITE_TAC[MATCH_MP FILTER_ALL_DISTINCT th]) THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN REWRITE_TAC[MEM_FILTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. MEM r reglist /\ ~MEM r stacklist ==> EL r C3 < k` (LABEL_TAC "nstk") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "out" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `~MEM (r:num) stacklist`)]) THEN
    UNDISCH_TAC `~MEM (r:num) stacklist` THEN USE_THEN "sl" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[MEM_FILTER] THEN ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "kle" (LABEL_TAC "kle'" o REWRITE_RULE[GSYM ALL_MEM]) THEN
  ASM_CASES_TAC `MEM (x:num) stacklist` THEN ASM_CASES_TAC `MEM (y:num) stacklist` THENL
   [MATCH_MP_TAC(ISPEC `\r:num. EL r (C3:num list)` LSCANPAUX_INJ_MAP) THEN
    EXISTS_TAC `FILTER is_phy_var stacklist` THEN ASM_REWRITE_TAC[MEM_FILTER];
    USE_THEN "kle'" (fun th -> MP_TAC(MATCH_MP th (ASSUME `MEM (x:num) stacklist`))) THEN
    USE_THEN "nstk" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `MEM (y:num) reglist`)
      (ASSUME `~MEM (y:num) stacklist`)))) THEN
    UNDISCH_TAC `EL x (C3:num list) = EL y C3` THEN ARITH_TAC;
    USE_THEN "kle'" (fun th -> MP_TAC(MATCH_MP th (ASSUME `MEM (y:num) stacklist`))) THEN
    USE_THEN "nstk" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `MEM (x:num) reglist`)
      (ASSUME `~MEM (x:num) stacklist`)))) THEN
    UNDISCH_TAC `EL x (C3:num list) = EL y C3` THEN ARITH_TAC;
    MATCH_MP_TAC(ISPEC `\r:num. EL r (C1:num list)` LSCANPAUX_INJ_MAP) THEN
    EXISTS_TAC `FILTER is_phy_var reglist` THEN ASM_REWRITE_TAC[MEM_FILTER] THEN
    USE_THEN "inj2" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
    USE_THEN "lt" (fun th -> ASM_SIMP_TAC[REWRITE_RULE[GSYM ALL_MEM] th]) THEN
    USE_THEN "out" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `~MEM (x:num) stacklist`));
      GSYM(MATCH_MP th (ASSUME `~MEM (y:num) stacklist`))]) THEN
    ASM_REWRITE_TAC[]]);;

(* LSCANPAUX_ivl_final: the colour properties after the second register     *)
(* exchange, from the facts gathered along linear_reg_alloc_intervals       *)
let LSCANPAUX_ivl_final = prove
 (CASE_TERM
  `!k forced reglist stacklist (B:int list) (E:int list) (C1:num list) C2 C3 C4 n.
     ALL (\r. r < n) reglist /\
     ALL (\r12. match r12 with (r1,r2) -> MEM r1 reglist /\ MEM r2 reglist) forced /\
     (!r1 r2. MEM r1 reglist /\ MEM r2 reglist /\
              interval_intersect (EL r1 B,EL r1 E) (EL r2 B,EL r2 E) /\
              EL r1 C1 = EL r2 C1 ==> r1 = r2) /\
     ALL (\r12. match r12 with
                  (r1,r2) -> MEM r1 reglist /\ MEM r2 reglist /\ EL r1 C1 = EL r2 C1 ==>
                             r1 = r2) forced /\
     ALL_DISTINCT (MAP (\r. EL r C1) (FILTER is_phy_var reglist)) /\
     (!r. MEM r reglist /\ is_phy_var r /\ 2 * k <= r ==> k <= EL r C1) /\
     (!r1 r2. r1 < n /\ r2 < n ==> EL r1 C2 = EL r2 C2 ==> EL r1 C1 = EL r2 C1) /\
     (!r. MEM r (FILTER (\r. r < 2 * k) (FILTER is_phy_var reglist)) ==> EL r C2 = r DIV 2) /\
     ((!r. MEM r (FILTER (\r. r < 2 * k) (FILTER is_phy_var reglist)) ==> r DIV 2 < k) ==>
      (!r. r < n /\ k <= EL r C1 /\
           (!r'. MEM r' (FILTER (\r. r < 2 * k) (FILTER is_phy_var reglist)) ==>
                 ~(EL r C1 = EL r' C1))
           ==> k <= EL r C2)) /\
     stacklist = FILTER (\r. is_stack_var r \/ k <= EL r C2) reglist /\
     (!r1 r2. MEM r1 stacklist /\ MEM r2 stacklist /\
              interval_intersect (EL r1 B,EL r1 E) (EL r2 B,EL r2 E) /\
              EL r1 C3 = EL r2 C3 ==> r1 = r2) /\
     ALL (\r12. match r12 with
                  (r1,r2) -> MEM r1 stacklist /\ MEM r2 stacklist /\ EL r1 C3 = EL r2 C3 ==>
                             r1 = r2)
         (FILTER (\r12. match r12 with (r1,r2) -> MEM r1 stacklist /\ MEM r2 stacklist)
                 forced) /\
     ALL (\r. k <= EL r C3) stacklist /\
     (!r. ~MEM r stacklist ==> EL r C3 = EL r C2) /\
     (!r1 r2. r1 < n /\ r2 < n ==> EL r1 C4 = EL r2 C4 ==> EL r1 C3 = EL r2 C3) /\
     (!r. MEM r (FILTER (\r. 2 * k <= r) (FILTER is_phy_var reglist)) ==> EL r C4 = r DIV 2) /\
     ((!r. MEM r (FILTER (\r. 2 * k <= r) (FILTER is_phy_var reglist)) ==>
           (k <= EL r C3 <=> k <= r DIV 2)) ==>
      (!r. r < n ==> (k <= EL r C3 <=> k <= EL r C4))) /\
     ((!r. MEM r (FILTER (\r. 2 * k <= r) (FILTER is_phy_var reglist)) ==>
           k <= EL r C3 /\ k <= r DIV 2) ==>
      (!r. r < n /\ EL r C3 < k ==> EL r C4 = EL r C3)) ==>
     (!r1 r2. MEM r1 reglist /\ MEM r2 reglist /\
              interval_intersect (EL r1 B,EL r1 E) (EL r2 B,EL r2 E) /\
              EL r1 C4 = EL r2 C4 ==> r1 = r2) /\
     ALL (\r. if is_phy_var r then EL r C4 = r DIV 2
              else if is_stack_var r then k <= EL r C4 else T) reglist /\
     ALL (\r12. match r12 with (r1,r2) -> EL r1 C4 = EL r2 C4 ==> r1 = r2) forced`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lt") (CONJUNCTS_THEN2 (LABEL_TAC "fsub")
    (CONJUNCTS_THEN2 (LABEL_TAC "int1") (CONJUNCTS_THEN2 (LABEL_TAC "f1")
    (CONJUNCTS_THEN2 (LABEL_TAC "d1") (CONJUNCTS_THEN2 (LABEL_TAC "ps")
    (CONJUNCTS_THEN2 (LABEL_TAC "inj2") (CONJUNCTS_THEN2 (LABEL_TAC "ex1b")
    (CONJUNCTS_THEN2 (LABEL_TAC "ex1e") (CONJUNCTS_THEN2 (LABEL_TAC "sl")
    (CONJUNCTS_THEN2 (LABEL_TAC "int3") (CONJUNCTS_THEN2 (LABEL_TAC "f3")
    (CONJUNCTS_THEN2 (LABEL_TAC "kle") (CONJUNCTS_THEN2 (LABEL_TAC "out")
    (CONJUNCTS_THEN2 (LABEL_TAC "inj4") (CONJUNCTS_THEN2 (LABEL_TAC "ex2b")
    (CONJUNCTS_THEN2 (LABEL_TAC "ex2c") (LABEL_TAC "ex2d")))))))))))))))))) THEN
  USE_THEN "lt" (LABEL_TAC "ltm" o REWRITE_RULE[GSYM ALL_MEM]) THEN
  USE_THEN "kle" (LABEL_TAC "stk" o REWRITE_RULE[GSYM ALL_MEM]) THEN
  SUBGOAL_THEN `!r. MEM r reglist /\ ~MEM r stacklist ==> EL r (C3:num list) < k`
    (LABEL_TAC "nstk") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "out" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `~MEM (r:num) stacklist`)]) THEN
    UNDISCH_TAC `~MEM (r:num) stacklist` THEN USE_THEN "sl" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[MEM_FILTER] THEN ARITH_TAC;
    ALL_TAC] THEN
  (* the registers spilled to the stack by the first pass are on the stack *)
  SUBGOAL_THEN `!r. MEM r (FILTER (\r. 2 * k <= r) (FILTER is_phy_var reglist)) ==>
                    MEM r stacklist` (LABEL_TAC "sprs") THENL
   [X_GEN_TAC `r:num` THEN REWRITE_TAC[MEM_FILTER] THEN STRIP_TAC THEN
    USE_THEN "sl" (fun th -> REWRITE_TAC[th; MEM_FILTER]) THEN ASM_REWRITE_TAC[] THEN
    DISJ2_TAC THEN
    USE_THEN "ex1e" (MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
     [REWRITE_TAC[MEM_FILTER; lt_div_2] THEN MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [USE_THEN "ltm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "ps" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `r':num` THEN REWRITE_TAC[MEM_FILTER] THEN STRIP_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `r:num = r'` MP_TAC THENL
       [MATCH_MP_TAC(ISPEC `\r:num. EL r (C1:num list)` LSCANPAUX_INJ_MAP) THEN
        EXISTS_TAC `FILTER is_phy_var reglist` THEN ASM_REWRITE_TAC[MEM_FILTER];
        DISCH_THEN SUBST_ALL_TAC THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. MEM r (FILTER (\r. 2 * k <= r) (FILTER is_phy_var reglist)) ==>
                    k <= EL r (C3:num list) /\ k <= r DIV 2` (LABEL_TAC "sprboth") THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [USE_THEN "stk" MATCH_MP_TAC THEN USE_THEN "sprs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `MEM r (FILTER (\r. 2 * k <= r) (FILTER is_phy_var reglist))` THEN
      SIMP_TAC[MEM_FILTER; le_div_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r < n ==> (k <= EL r (C3:num list) <=> k <= EL r (C4:num list))`
    (LABEL_TAC "c34") THENL
   [USE_THEN "ex2c" MATCH_MP_TAC THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    USE_THEN "sprboth" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `MEM r (FILTER (\r. 2 * k <= r) (FILTER is_phy_var reglist))`))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "ex2d" (fun d -> USE_THEN "sprboth" (fun b -> LABEL_TAC "keep" (MP d b))) THEN
  SUBGOAL_THEN `!r1 r2. MEM r1 reglist /\ MEM r2 reglist /\
                        EL r1 (C4:num list) = EL r2 C4 ==> EL r1 (C3:num list) = EL r2 C3`
    (LABEL_TAC "c43") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "inj4" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    USE_THEN "ltm" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r1 r2. MEM r1 reglist /\ MEM r2 reglist /\ EL r1 (C3:num list) = EL r2 C3 ==>
            (MEM r1 stacklist /\ MEM r2 stacklist) \/
            (~MEM r1 stacklist /\ ~MEM r2 stacklist /\ EL r1 (C1:num list) = EL r2 C1)`
    (LABEL_TAC "split") THENL
   [REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `MEM (r1:num) stacklist` THEN ASM_CASES_TAC `MEM (r2:num) stacklist` THEN
    ASM_REWRITE_TAC[] THENL
     [USE_THEN "stk" (fun th -> MP_TAC(MATCH_MP th (ASSUME `MEM (r1:num) stacklist`))) THEN
      USE_THEN "nstk" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `MEM (r2:num) reglist`)
        (ASSUME `~MEM (r2:num) stacklist`)))) THEN
      UNDISCH_TAC `EL r1 (C3:num list) = EL r2 C3` THEN ARITH_TAC;
      USE_THEN "stk" (fun th -> MP_TAC(MATCH_MP th (ASSUME `MEM (r2:num) stacklist`))) THEN
      USE_THEN "nstk" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `MEM (r1:num) reglist`)
        (ASSUME `~MEM (r1:num) stacklist`)))) THEN
      UNDISCH_TAC `EL r1 (C3:num list) = EL r2 C3` THEN ARITH_TAC;
      USE_THEN "inj2" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "ltm" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        USE_THEN "ltm" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        USE_THEN "out" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
          (ASSUME `~MEM (r1:num) stacklist`)); GSYM(MATCH_MP th
          (ASSUME `~MEM (r2:num) stacklist`))]) THEN
        FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* interference *)
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `EL r1 (C3:num list) = EL r2 C3` ASSUME_TAC THENL
     [USE_THEN "c43" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "split" (MP_TAC o SPECL [`r1:num`; `r2:num`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THENL
     [USE_THEN "int3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "int1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* colours *)
    REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(r:num) < n` ASSUME_TAC THENL
     [USE_THEN "ltm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [ASM_CASES_TAC `r < 2 * k` THENL
       [SUBGOAL_THEN `MEM r (FILTER (\r. r < 2 * k) (FILTER is_phy_var reglist))` ASSUME_TAC
        THENL [ASM_REWRITE_TAC[MEM_FILTER]; ALL_TAC] THEN
        SUBGOAL_THEN `EL r (C2:num list) = r DIV 2` ASSUME_TAC THENL
         [USE_THEN "ex1b" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `~MEM (r:num) stacklist` ASSUME_TAC THENL
         [USE_THEN "sl" (fun th -> REWRITE_TAC[th; MEM_FILTER]) THEN
          ASM_REWRITE_TAC[DE_MORGAN_THM; NOT_LE; lt_div_2] THEN
          MP_TAC(SPEC `r:num` convention_partitions) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `EL r (C3:num list) = r DIV 2` ASSUME_TAC THENL
         [USE_THEN "out" (fun th -> REWRITE_TAC[MATCH_MP th
            (ASSUME `~MEM (r:num) stacklist`)]) THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        REMOVE_THEN "keep" (MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[lt_div_2] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
        USE_THEN "ex2b" MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM_FILTER] THEN ASM_ARITH_TAC];
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `MEM (r:num) stacklist` ASSUME_TAC THENL
       [USE_THEN "sl" (fun th -> REWRITE_TAC[th; MEM_FILTER]) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "c34" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `(r:num) < n`))]) THEN
      USE_THEN "stk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* forced pairs *)
    REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE] THEN
    MAP_EVERY X_GEN_TAC [`r1:num`; `r2:num`] THEN DISCH_TAC THEN DISCH_TAC THEN
    USE_THEN "fsub" (fun th -> MP_TAC(MATCH_MP
      (REWRITE_RULE[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE] th)
      (ASSUME `MEM (r1:num,r2:num) forced`))) THEN STRIP_TAC THEN
    SUBGOAL_THEN `EL r1 (C3:num list) = EL r2 C3` ASSUME_TAC THENL
     [USE_THEN "c43" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "split" (MP_TAC o SPECL [`r1:num`; `r2:num`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THENL
     [USE_THEN "f3" (MP_TAC o SPECL [`r1:num`; `r2:num`] o
        REWRITE_RULE[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE; MEM_FILTER]) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "f1" (MP_TAC o SPECL [`r1:num`; `r2:num`] o
        REWRITE_RULE[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE]) THEN
      ASM_REWRITE_TAC[]]]);;

let LSCANPAUX_rbind = prove
 (`!(x:A) (f:A->S->(B,E)exc#S) s. st_ex_bind (st_ex_return x) f s = f x s`,
  REWRITE_TAC(case_def "prod" :: case_def "exc" :: RAPROOFAUX_msimps));;

(* LSCANPAUX_ivl_phaseA: sorting the registers by interval start *)
let LSCANPAUX_ivl_phaseA = prove
 (`!R sth.
     ALL (\r. r < LENGTH (linear_scan_hidden_state_int_beg sth)) R /\
     LENGTH R <= LENGTH (linear_scan_hidden_state_sorted_regs sth) ==>
     ?sth' reglist.
       (!f:num list->linear_scan_hidden_state->(B,state_exn)exc#linear_scan_hidden_state.
          st_ex_ignore_bind (list_to_sorted_regs R 0)
            (st_ex_ignore_bind (sort_regs 0 (LENGTH R))
              (st_ex_bind (sorted_regs_to_list 0 (LENGTH R)) f)) sth = f reglist sth') /\
       sth' = linear_scan_hidden_state_sorted_regs_fupd
                (K (linear_scan_hidden_state_sorted_regs sth')) sth /\
       PERM R reglist /\
       SORTED (intbeg_less (linear_scan_hidden_state_int_beg sth)) reglist`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rb") (LABEL_TAC "rl")) THEN
  MP_TAC(SPECL [`R:num list`; `0`; `sth:linear_scan_hidden_state`]
    list_to_sorted_regs_correct) THEN
  USE_THEN "rl" (fun th -> REWRITE_TAC[th; ADD_CLAUSES]) THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:linear_scan_hidden_state`
    (CONJUNCTS_THEN2 (LABEL_TAC "eq3") (CONJUNCTS_THEN2 (LABEL_TAC "len3")
    (CONJUNCTS_THEN2 (LABEL_TAC "rec3") (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "dr3")))))) THEN
  USE_THEN "rec3" (fun th -> LABEL_TAC "beg3" (REWRITE_RULE(K_THM :: LSCANPAUX_hs_record)
    (AP_TERM `linear_scan_hidden_state_int_beg` th))) THEN
  USE_THEN "dr3" (LABEL_TAC "tk3" o REWRITE_RULE[DROP_0]) THEN
  MP_TAC(SPECL [`0`; `LENGTH (R:num list)`; `s3:linear_scan_hidden_state`] sort_regs_correct) THEN
  ANTS_TAC THENL
   [USE_THEN "len3" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "beg3" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "rl" (fun th -> REWRITE_TAC[th; LE_0]) THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `EL i (linear_scan_hidden_state_sorted_regs s3) = EL i (R:num list)`
      SUBST1_TAC THENL
     [USE_THEN "tk3" (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM th]) THEN
      ASM_SIMP_TAC[EL_TAKE];
      USE_THEN "rb" (MP_TAC o REWRITE_RULE[EVERY_EL]) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; GSYM intbeg_less_def] THEN
  USE_THEN "beg3" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:linear_scan_hidden_state`
    (CONJUNCTS_THEN2 (LABEL_TAC "eq2") (CONJUNCTS_THEN2 (LABEL_TAC "rec2")
    (CONJUNCTS_THEN2 (LABEL_TAC "len2") (CONJUNCTS_THEN2 (LABEL_TAC "perm2")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "sorted2"))))))) THEN
  MP_TAC(SPECL [`0`; `LENGTH (R:num list)`; `s2:linear_scan_hidden_state`]
    sorted_regs_to_list_correct) THEN
  ANTS_TAC THENL
   [USE_THEN "len2" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "len3" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "rl" ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUB_0; DROP_0] THEN DISCH_THEN(LABEL_TAC "eq1") THEN
  MAP_EVERY EXISTS_TAC [`s2:linear_scan_hidden_state`;
    `TAKE (LENGTH (R:num list)) (linear_scan_hidden_state_sorted_regs s2)`] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN
    USE_THEN "eq3" (fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_ignore_bind_ok (SYM th)]) THEN
    USE_THEN "eq2" (fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_ignore_bind_ok th]) THEN
    USE_THEN "eq1" (fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_bind_ok th]);
    USE_THEN "rec2" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    USE_THEN "rec3" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
    REWRITE_TAC(K_THM :: o_THM :: LSCANPAUX_hs_record);
    USE_THEN "tk3" (fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
    USE_THEN "perm2" MATCH_MP_TAC THEN USE_THEN "len3" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "rl" (fun th -> REWRITE_TAC[th; LE_0; LE_REFL]);
    SIMP_TAC[SORTED_EL_LESS; intbeg_less_transitive] THEN
    SUBGOAL_THEN `LENGTH (R:num list) <= LENGTH (linear_scan_hidden_state_sorted_regs s2)`
      ASSUME_TAC THENL
     [USE_THEN "len2" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "len3" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "rl" ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LENGTH_TAKE] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `m < LENGTH (R:num list)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_TAKE] THEN
    USE_THEN "sorted2" MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* LSCANPAUX_ivl_phaseB: sorting the moves by priority *)
let LSCANPAUX_ivl_phaseB = prove
 (`!(moves:(num#num#num)list) sth.
     LENGTH moves <= LENGTH (linear_scan_hidden_state_sorted_moves sth) ==>
     ?sth' smoves.
       (!f:(num#num#num)list->linear_scan_hidden_state->
           (B,state_exn)exc#linear_scan_hidden_state.
          st_ex_ignore_bind (list_to_sorted_moves moves 0)
            (st_ex_ignore_bind (linear_scan_sort_moves 0 (LENGTH moves))
              (st_ex_bind (sorted_moves_to_list 0 (LENGTH moves)) f)) sth = f smoves sth') /\
       sth' = linear_scan_hidden_state_sorted_moves_fupd
                (K (linear_scan_hidden_state_sorted_moves sth')) sth /\
       PERM moves smoves`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "ml") THEN
  MP_TAC(SPECL [`moves:(num#num#num)list`; `0`; `sth:linear_scan_hidden_state`]
    list_to_sorted_moves_correct) THEN
  USE_THEN "ml" (fun th -> REWRITE_TAC[th; ADD_CLAUSES]) THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:linear_scan_hidden_state`
    (CONJUNCTS_THEN2 (LABEL_TAC "eq3") (CONJUNCTS_THEN2 (LABEL_TAC "len3")
    (CONJUNCTS_THEN2 (LABEL_TAC "rec3") (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "dr3")))))) THEN
  USE_THEN "dr3" (LABEL_TAC "tk3" o REWRITE_RULE[DROP_0]) THEN
  MP_TAC(SPECL [`0`; `LENGTH (moves:(num#num#num)list)`; `s3:linear_scan_hidden_state`]
    sort_moves_correct) THEN
  ANTS_TAC THENL
   [USE_THEN "len3" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "ml" (fun th -> REWRITE_TAC[th; LE_0]);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:linear_scan_hidden_state`
    (CONJUNCTS_THEN2 (LABEL_TAC "eq2") (CONJUNCTS_THEN2 (LABEL_TAC "rec2")
    (CONJUNCTS_THEN2 (LABEL_TAC "len2") (LABEL_TAC "perm2"))))) THEN
  MP_TAC(SPECL [`0`; `LENGTH (moves:(num#num#num)list)`; `s2:linear_scan_hidden_state`]
    sorted_moves_to_list_correct) THEN
  ANTS_TAC THENL
   [USE_THEN "len2" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "len3" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "ml" ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUB_0; DROP_0] THEN DISCH_THEN(LABEL_TAC "eq1") THEN
  MAP_EVERY EXISTS_TAC [`s2:linear_scan_hidden_state`;
    `TAKE (LENGTH (moves:(num#num#num)list)) (linear_scan_hidden_state_sorted_moves s2)`] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN
    USE_THEN "eq3" (fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_ignore_bind_ok (SYM th)]) THEN
    USE_THEN "eq2" (fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_ignore_bind_ok th]) THEN
    USE_THEN "eq1" (fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_bind_ok th]);
    USE_THEN "rec2" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    USE_THEN "rec3" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
    REWRITE_TAC(K_THM :: o_THM :: LSCANPAUX_hs_record);
    USE_THEN "tk3" (fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
    USE_THEN "perm2" MATCH_MP_TAC THEN USE_THEN "len3" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "ml" (fun th -> REWRITE_TAC[th; LE_0; LE_REFL])]);;


(* LSCANPAUX_ffs_restrict: restricting the forced edges to a sublist *)
let LSCANPAUX_ffs_restrict = prove
 (CASE_TERM
  `!forced (B:int list) sl fa r.
     forbidden_is_from_forced forced B r fa ==>
     forbidden_is_from_forced_sublist sl
       (FILTER (\r12. match r12 with (r1,r2) -> MEM r1 sl /\ MEM r2 sl) forced) B r
       (FILTER (\r'. MEM r' sl) fa)`,
  REWRITE_TAC[forbidden_is_from_forced_def; forbidden_is_from_forced_sublist_def;
              MEM_FILTER; pair_CASE] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `reg2:num`) THEN MESON_TAC[]);;

(* LSCANPAUX_the_lookup_map_FILTER *)
let LSCANPAUX_the_lookup_map_FILTER = prove
 (`!(P:A->bool) r t. misc_the [] (lookup r (sptree_map (FILTER P) t)) = FILTER P (misc_the [] (lookup r t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lookup_map] THEN MATCH_MP_TAC the_OPTION_MAP THEN
  REWRITE_TAC[FILTER]);;

(* HOL4 line 4574 *)
let linear_reg_alloc_intervals_correct = prove
 (CASE_TERM
  `!k forced moves reglist_unsorted sth.
     ALL (\r12. match r12 with
                  (r1,r2) -> MEM r1 reglist_unsorted /\ MEM r2 reglist_unsorted) forced /\
     ALL (\r12. match r12 with
                  (r1,r2) -> r1 < LENGTH (linear_scan_hidden_state_colors sth) /\
                             r2 < LENGTH (linear_scan_hidden_state_colors sth))
         (MAP SND moves) /\
     ALL (\r. r < LENGTH (linear_scan_hidden_state_colors sth)) reglist_unsorted /\
     ALL (\r. EL r (linear_scan_hidden_state_int_beg sth) <=
              EL r (linear_scan_hidden_state_int_end sth)) reglist_unsorted /\
     ALL_DISTINCT reglist_unsorted /\
     ALL (\r. r < LENGTH (linear_scan_hidden_state_int_beg sth)) reglist_unsorted /\
     LENGTH (linear_scan_hidden_state_colors sth) =
       LENGTH (linear_scan_hidden_state_int_beg sth) /\
     LENGTH (linear_scan_hidden_state_int_end sth) =
       LENGTH (linear_scan_hidden_state_int_beg sth) /\
     LENGTH reglist_unsorted <= LENGTH (linear_scan_hidden_state_sorted_regs sth) /\
     LENGTH moves <= LENGTH (linear_scan_hidden_state_sorted_moves sth) ==>
     ?sthout.
       linear_reg_alloc_intervals k forced moves reglist_unsorted sth =
         (M_success one,sthout) /\
       (!r1 r2. MEM r1 reglist_unsorted /\ MEM r2 reglist_unsorted /\
                interval_intersect (EL r1 (linear_scan_hidden_state_int_beg sth),
                                    EL r1 (linear_scan_hidden_state_int_end sth))
                                   (EL r2 (linear_scan_hidden_state_int_beg sth),
                                    EL r2 (linear_scan_hidden_state_int_end sth)) /\
                EL r1 (linear_scan_hidden_state_colors sthout) =
                EL r2 (linear_scan_hidden_state_colors sthout) ==>
                r1 = r2) /\
       ALL (\r. if is_phy_var r then EL r (linear_scan_hidden_state_colors sthout) = r DIV 2
                else if is_stack_var r then k <= EL r (linear_scan_hidden_state_colors sthout)
                else T) reglist_unsorted /\
       ALL (\r12. match r12 with
                    (r1,r2) -> EL r1 (linear_scan_hidden_state_colors sthout) =
                               EL r2 (linear_scan_hidden_state_colors sthout) ==> r1 = r2)
           forced /\
       LENGTH (linear_scan_hidden_state_colors sthout) =
         LENGTH (linear_scan_hidden_state_colors sth)`,
    REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fR") (CONJUNCTS_THEN2 (LABEL_TAC "mvlt")
    (CONJUNCTS_THEN2 (LABEL_TAC "Rlt") (CONJUNCTS_THEN2 (LABEL_TAC "Rbe")
    (CONJUNCTS_THEN2 (LABEL_TAC "Rd") (CONJUNCTS_THEN2 (LABEL_TAC "Rlb")
    (CONJUNCTS_THEN2 (LABEL_TAC "lcb") (CONJUNCTS_THEN2 (LABEL_TAC "leb")
    (CONJUNCTS_THEN2 (LABEL_TAC "lsr") (LABEL_TAC "lsm")))))))))) THEN
  REWRITE_TAC[linear_reg_alloc_intervals_def; LET_DEF; LET_END_DEF] THEN
  (* phase A: sorting the registers *)
  MP_TAC(INST_TYPE [`:1`,`:B`] (ISPECL [`reglist_unsorted:num list`;
    `sth:linear_scan_hidden_state`] LSCANPAUX_ivl_phaseA)) THEN
  ANTS_TAC THENL [USE_THEN "Rlb" (fun a -> USE_THEN "lsr" (fun b -> REWRITE_TAC[a; b]));
                  ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sA:linear_scan_hidden_state` (X_CHOOSE_THEN `reglist:num list`
    (CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th]) (CONJUNCTS_THEN2 (LABEL_TAC "recA")
    (CONJUNCTS_THEN2 (LABEL_TAC "permA") (LABEL_TAC "sortedA")))))) THEN
  REWRITE_TAC[LSCANPAUX_rbind] THEN
  (* phase B: sorting the moves *)
  MP_TAC(INST_TYPE [`:1`,`:B`] (ISPECL [`moves:(num#num#num)list`;
    `sA:linear_scan_hidden_state`] LSCANPAUX_ivl_phaseB)) THEN
  ANTS_TAC THENL
   [USE_THEN "recA" (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    REWRITE_TAC(K_THM :: LSCANPAUX_hs_record) THEN USE_THEN "lsm" ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:linear_scan_hidden_state` (X_CHOOSE_THEN
    `smoves:(num#num#num)list`
    (CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th]) (CONJUNCTS_THEN2 (LABEL_TAC "recB")
      (LABEL_TAC "permB"))))) THEN
  SUBGOAL_THEN
   `linear_scan_hidden_state_colors s0 = linear_scan_hidden_state_colors sth /\
    linear_scan_hidden_state_int_beg s0 = linear_scan_hidden_state_int_beg sth /\
    linear_scan_hidden_state_int_end s0 = linear_scan_hidden_state_int_end sth`
    (CONJUNCTS_THEN2 (LABEL_TAC "c0") (CONJUNCTS_THEN2 (LABEL_TAC "b0") (LABEL_TAC "e0"))) THENL
   [USE_THEN "recB" (fun th -> ONCE_REWRITE_TAC[th]) THEN
    USE_THEN "recA" (fun th -> ONCE_REWRITE_TAC[th]) THEN
    REWRITE_TAC(K_THM :: LSCANPAUX_hs_record);
    ALL_TAC] THEN
  (* the adjacency lists of the moves and of the forced edges *)
  MP_TAC(SPECL [`MAP SND (smoves:(num#num#num)list)`; `s0:linear_scan_hidden_state`]
    edges_to_adjlist_output) THEN
  ANTS_TAC THENL
   [USE_THEN "b0" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "lcb" (fun th -> REWRITE_TAC[GSYM th]) THEN
    USE_THEN "permB" (fun th -> REWRITE_TAC[GSYM(MATCH_MP PERM_EVERY
      (MATCH_MP (ISPEC `SND:num#num#num->num#num` PERM_MAP) th))]) THEN
    USE_THEN "mvlt" ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `madj:(num list)spt` (CONJUNCTS_THEN2
    (fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_bind_ok th]) (LABEL_TAC "mff"))) THEN
  MP_TAC(SPECL [`forced:(num#num)list`; `s0:linear_scan_hidden_state`]
    edges_to_adjlist_output) THEN
  ANTS_TAC THENL
   [USE_THEN "b0" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "fR" MP_TAC THEN USE_THEN "Rlb" MP_TAC THEN
    REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `fadj:(num list)spt` (CONJUNCTS_THEN2
    (fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_bind_ok th]) (LABEL_TAC "fff"))) THEN
  USE_THEN "b0" (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN LABEL_TAC "b0" th) THEN
  (* facts about the sorted register list *)
  USE_THEN "permA" (LABEL_TAC "memR" o MATCH_MP PERM_MEM_EQ) THEN
  SUBGOAL_THEN `ALL (\r. r < LENGTH (linear_scan_hidden_state_colors sth)) reglist /\
                ALL_DISTINCT reglist /\
                ALL (\r. EL r (linear_scan_hidden_state_int_beg sth) <=
                         EL r (linear_scan_hidden_state_int_end sth)) reglist`
    (CONJUNCTS_THEN2 (LABEL_TAC "rlt") (CONJUNCTS_THEN2 (LABEL_TAC "rd") (LABEL_TAC "rbe")))
  THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "Rlt" MP_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
      USE_THEN "permA" (fun th -> REWRITE_TAC[GSYM(MATCH_MP ALL_DISTINCT_PERM th)]) THEN
      USE_THEN "Rd" ACCEPT_TAC;
      USE_THEN "Rbe" MP_TAC THEN REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN (CASE_TERM
   `ALL (\r12. match r12 with (r1,r2) -> MEM r1 (reglist:num list) /\ MEM r2 reglist)
        (forced:(num#num)list)`)
    (LABEL_TAC "fr") THENL
   [USE_THEN "fR" MP_TAC THEN REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. forbidden_is_from_forced_sublist reglist forced
                      (linear_scan_hidden_state_int_beg sth) r (misc_the [] (lookup r fadj))`
    (LABEL_TAC "fsub") THENL
   [MATCH_MP_TAC forbidden_is_from_forced_take_sublist THEN
    USE_THEN "fr" (fun a -> USE_THEN "fff" (fun b -> REWRITE_TAC[a; b]));
    ALL_TAC] THEN
  SUBGOAL_THEN `!r1. ALL (\r2. r2 < LENGTH (linear_scan_hidden_state_colors sth))
                         (misc_the [] (lookup r1 fadj))` (LABEL_TAC "fadjlt") THENL
   [X_GEN_TAC `r1:num` THEN REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `r2:num` THEN
    USE_THEN "fff" (fun th -> REWRITE_TAC[GSYM(REWRITE_RULE[forbidden_is_from_forced_def]
      (SPEC `r1:num` th))]) THEN
    STRIP_TAC THEN USE_THEN "fr" (MP_TAC o REWRITE_RULE[GSYM ALL_MEM; FORALL_PAIR_THM;
      pair_CASE]) THEN
    USE_THEN "rlt" (MP_TAC o REWRITE_RULE[GSYM ALL_MEM]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r1. ALL (\r2. r2 < LENGTH (linear_scan_hidden_state_colors sth))
                         (misc_the [] (lookup r1 madj))` (LABEL_TAC "madjlt") THENL
   [X_GEN_TAC `r1:num` THEN REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `r2:num` THEN
    USE_THEN "mff" (fun th -> REWRITE_TAC[GSYM(REWRITE_RULE[forbidden_is_from_forced_def]
      (SPEC `r1:num` th))]) THEN
    USE_THEN "permB" (fun th -> REWRITE_TAC[GSYM(MATCH_MP PERM_MEM_EQ
      (MATCH_MP (ISPEC `SND:num#num#num->num#num` PERM_MAP) th))]) THEN
    STRIP_TAC THEN
    USE_THEN "mvlt" (MP_TAC o REWRITE_RULE[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the first pass *)
  MP_TAC(SPECL [`s0:linear_scan_hidden_state`; `reglist:num list`; `forced:(num#num)list`;
    `k:num`; `linear_reg_alloc_pass1_initial_state k`]
    linear_reg_alloc_pass1_initial_state_invariants) THEN
  ANTS_TAC THENL
   [USE_THEN "c0" (fun a -> USE_THEN "b0" (fun b -> USE_THEN "e0" (fun c ->
      REWRITE_TAC[a; b; c]))) THEN
    USE_THEN "lcb" (fun a -> USE_THEN "leb" (fun b -> REWRITE_TAC[a; b]));
    ALL_TAC] THEN
  USE_THEN "b0" (fun b -> DISCH_THEN(X_CHOOSE_THEN `pos1:int`
    (CONJUNCTS_THEN2 (LABEL_TAC "gls0") (LABEL_TAC "pos1" o REWRITE_RULE[b])))) THEN
  MP_TAC(SPECL [`reglist:num list`; `linear_reg_alloc_pass1_initial_state k`;
    `s0:linear_scan_hidden_state`; `pos1:int`; `T`; `madj:(num list)spt`;
    `fadj:(num list)spt`; `forced:(num#num)list`; `0`]
    st_ex_FOLDL_linear_reg_alloc_step_passn_invariants) THEN
  REWRITE_TAC[] THEN
  USE_THEN "c0" (fun a -> USE_THEN "b0" (fun b -> USE_THEN "e0" (fun c ->
    REWRITE_TAC[a; b; c]))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `st1:linear_scan_state` (X_CHOOSE_THEN
    `s1:linear_scan_hidden_state` (X_CHOOSE_THEN `p1:int`
    (CONJUNCTS_THEN2 (LABEL_TAC "eq1") (CONJUNCTS_THEN2 (LABEL_TAC "gls1")
    (CONJUNCTS_THEN2 (LABEL_TAC "len1") (CONJUNCTS_THEN2 (LABEL_TAC "beg1")
    (CONJUNCTS_THEN2 (LABEL_TAC "end1") (CONJUNCTS_THEN2 (LABEL_TAC "out1")
    (CONJUNCTS_THEN2 (LABEL_TAC "ps1") (LABEL_TAC "max1"))))))))))) THEN
  USE_THEN "eq1" (fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_bind_ok (SYM th)]) THEN
  USE_THEN "gls1" (LSCANPAUX_LABEL_CONJS "a" o
    REWRITE_RULE[good_linear_scan_state_REVERSE; good_linear_scan_state_def]) THEN
  USE_THEN "ps1" (LABEL_TAC "ps1'" o REWRITE_RULE[phystack_on_stack_REVERSE;
    phystack_on_stack_def]) THEN
  USE_THEN "max1" (LABEL_TAC "max1'" o
    REWRITE_RULE(linear_reg_alloc_pass1_initial_state_def :: LSCANPAUX_st_record)) THEN
  (* the first register exchange *)
  MP_TAC(SPECL [`FILTER (\r. r < 2 * k) (FILTER is_phy_var reglist)`;
    `s1:linear_scan_hidden_state`; `k:num`] apply_reg_exchange_correct) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ALL_DISTINCT_IS_SPARSE_SUBLIST THEN
      EXISTS_TAC `MAP (\r. EL r (linear_scan_hidden_state_colors s1))
                      (FILTER is_phy_var reglist)` THEN
      CONJ_TAC THENL
       [USE_THEN "a7" ACCEPT_TAC;
        MATCH_MP_TAC MAP_IS_SPARSE_SUBLIST THEN MATCH_ACCEPT_TAC FILTER_IS_SPARSE_SUBLIST];
      REWRITE_TAC[MEM_FILTER] THEN MESON_TAC[];
      USE_THEN "len1" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "c0" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[MEM_FILTER] THEN
      USE_THEN "rlt" (MP_TAC o REWRITE_RULE[GSYM ALL_MEM]) THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:linear_scan_hidden_state`
    (CONJUNCTS_THEN2 (LABEL_TAC "x1eq") (CONJUNCTS_THEN2 (LABEL_TAC "x1len")
    (CONJUNCTS_THEN2 (LABEL_TAC "x1beg") (CONJUNCTS_THEN2 (LABEL_TAC "x1end")
    (CONJUNCTS_THEN2 (LABEL_TAC "x1inj") (CONJUNCTS_THEN2 (LABEL_TAC "x1b")
    (CONJUNCTS_THEN2 (LABEL_TAC "x1c") (CONJUNCTS_THEN2 (LABEL_TAC "x1e")
      (LABEL_TAC "x1d")))))))))) THEN
  USE_THEN "x1eq" (fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_ignore_bind_ok (SYM th)]) THEN
  (* the registers that go to the second pass *)
  MP_TAC(SPECL [`reglist:num list`; `s2:linear_scan_hidden_state`; `k:num`]
    st_ex_FILTER_good_stack) THEN
  ANTS_TAC THENL
   [USE_THEN "x1len" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "len1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "c0" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "rlt" ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_bind_ok th]) THEN
  REWRITE_TAC[LSCANPAUX_rbind] THEN
  ABBREV_TAC `stacklist = FILTER (\r. is_stack_var r \/
                k <= EL r (linear_scan_hidden_state_colors s2)) reglist` THEN
  POP_ASSUM(LABEL_TAC "sl") THEN
  USE_THEN "x1len" (fun a -> USE_THEN "len1" (fun b -> LABEL_TAC "L2" (TRANS a b))) THEN
  USE_THEN "x1beg" (fun a -> USE_THEN "beg1" (fun b -> LABEL_TAC "B2" (TRANS a b))) THEN
  USE_THEN "x1end" (fun a -> USE_THEN "end1" (fun b -> LABEL_TAC "E2" (TRANS a b))) THEN
  (* the second pass *)
  MP_TAC(SPECL [`s2:linear_scan_hidden_state`; `stacklist:num list`;
    CASE_TERM `FILTER (\r12. match r12 with (r1,r2) -> MEM r1 (stacklist:num list) /\
                                                       MEM r2 stacklist)
                 (forced:(num#num)list)`;
    `k:num`; `LENGTH (stacklist:num list)`;
    `linear_reg_alloc_pass2_initial_state k (LENGTH (stacklist:num list))`]
    linear_reg_alloc_pass2_initial_state_invariants) THEN
  USE_THEN "L2" (fun a -> USE_THEN "B2" (fun b -> USE_THEN "E2" (fun c ->
    REWRITE_TAC[a; b; c]))) THEN
  ANTS_TAC THENL
   [USE_THEN "lcb" (fun a -> USE_THEN "leb" (fun b -> REWRITE_TAC[a; b])); ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `pos2:int`
    (CONJUNCTS_THEN2 (LABEL_TAC "gls20") (LABEL_TAC "pos2"))) THEN
  MP_TAC(SPECL [`stacklist:num list`;
    `linear_reg_alloc_pass2_initial_state k (LENGTH (stacklist:num list))`;
    `s2:linear_scan_hidden_state`; `pos2:int`; `F`;
    `sptree_map (FILTER (\r. ~(lookup r (fromAList (MAP (\r. (r,one)) (stacklist:num list))) = NONE)))
         (madj:(num list)spt)`;
    `sptree_map (FILTER (\r. ~(lookup r (fromAList (MAP (\r. (r,one)) (stacklist:num list))) = NONE)))
         (fadj:(num list)spt)`;
    CASE_TERM `FILTER (\r12. match r12 with (r1,r2) -> MEM r1 (stacklist:num list) /\
                                                       MEM r2 stacklist)
                 (forced:(num#num)list)`;
    `k:num`] st_ex_FOLDL_linear_reg_alloc_step_passn_invariants) THEN
  REWRITE_TAC[] THEN
  USE_THEN "L2" (fun a -> USE_THEN "B2" (fun b -> USE_THEN "E2" (fun c ->
    REWRITE_TAC[a; b; c]))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "sl" (fun th -> REWRITE_TAC[GSYM th]) THEN MATCH_MP_TAC SORTED_FILTER THEN
      REWRITE_TAC[intbeg_less_transitive] THEN USE_THEN "sortedA" ACCEPT_TAC;
      USE_THEN "sl" (fun th -> REWRITE_TAC[GSYM th]) THEN MATCH_MP_TAC FILTER_ALL_DISTINCT THEN
      USE_THEN "rd" ACCEPT_TAC;
      USE_THEN "gls20" ACCEPT_TAC;
      USE_THEN "pos2" ACCEPT_TAC;
      USE_THEN "sl" (fun th -> REWRITE_TAC[GSYM th]) THEN
      REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN
      USE_THEN "rlt" (MP_TAC o REWRITE_RULE[GSYM ALL_MEM]) THEN MESON_TAC[];
      X_GEN_TAC `r:num` THEN
      REWRITE_TAC[LSCANPAUX_the_lookup_map_FILTER; lookup_fromAList_MAP_not_NONE] THEN
      MATCH_MP_TAC LSCANPAUX_ffs_restrict THEN USE_THEN "fff" (fun th -> REWRITE_TAC[th]);
      REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER; FORALL_PAIR_THM; pair_CASE] THEN MESON_TAC[];
      X_GEN_TAC `r1:num` THEN
      REWRITE_TAC[LSCANPAUX_the_lookup_map_FILTER; GSYM ALL_MEM; MEM_FILTER] THEN
      USE_THEN "fadjlt" (MP_TAC o SPEC `r1:num`) THEN REWRITE_TAC[GSYM ALL_MEM] THEN
      MESON_TAC[];
      X_GEN_TAC `r1:num` THEN
      REWRITE_TAC[LSCANPAUX_the_lookup_map_FILTER; GSYM ALL_MEM; MEM_FILTER] THEN
      USE_THEN "madjlt" (MP_TAC o SPEC `r1:num`) THEN REWRITE_TAC[GSYM ALL_MEM] THEN
      MESON_TAC[];
      USE_THEN "sl" (fun th -> REWRITE_TAC[GSYM th]) THEN
      REWRITE_TAC[GSYM ALL_MEM; MEM_FILTER] THEN
      USE_THEN "rbe" (MP_TAC o REWRITE_RULE[GSYM ALL_MEM]) THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `st3:linear_scan_state` (X_CHOOSE_THEN
    `s3:linear_scan_hidden_state` (X_CHOOSE_THEN `p3:int`
    (CONJUNCTS_THEN2 (LABEL_TAC "eq3") (CONJUNCTS_THEN2 (LABEL_TAC "gls3")
    (CONJUNCTS_THEN2 (LABEL_TAC "len3") (CONJUNCTS_THEN2 (LABEL_TAC "beg3")
    (CONJUNCTS_THEN2 (LABEL_TAC "end3") (CONJUNCTS_THEN2 (LABEL_TAC "out3")
      (LABEL_TAC "max3")))))))))) THEN
  USE_THEN "eq3" (fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_bind_ok (SYM th)]) THEN
  USE_THEN "gls3" (LSCANPAUX_LABEL_CONJS "b" o
    REWRITE_RULE[good_linear_scan_state_REVERSE; good_linear_scan_state_def]) THEN
  SUBGOAL_THEN `ALL (\r. k <= EL r (linear_scan_hidden_state_colors s3)) stacklist`
    (LABEL_TAC "kle3") THENL
   [USE_THEN "b22" MP_TAC THEN REWRITE_TAC[ALL_APPEND; ALL_MAP; o_DEF] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the second register exchange *)
  MP_TAC(SPECL [`FILTER (\r. 2 * k <= r) (FILTER is_phy_var reglist)`;
    `s3:linear_scan_hidden_state`; `k:num`] apply_reg_exchange_correct) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ALL_DISTINCT_IS_SPARSE_SUBLIST THEN
      EXISTS_TAC `MAP (\r. EL r (linear_scan_hidden_state_colors s3))
                      (FILTER is_phy_var reglist)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LSCANPAUX_ivl_c THEN
        MAP_EVERY EXISTS_TAC [`k:num`; `stacklist:num list`;
          `linear_scan_hidden_state_colors s1`; `linear_scan_hidden_state_colors s2`;
          `LENGTH (linear_scan_hidden_state_colors sth)`] THEN
        USE_THEN "len1" (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
        REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        USE_THEN "sl" (ACCEPT_TAC o SYM);
        MATCH_MP_TAC MAP_IS_SPARSE_SUBLIST THEN MATCH_ACCEPT_TAC FILTER_IS_SPARSE_SUBLIST];
      REWRITE_TAC[MEM_FILTER] THEN MESON_TAC[];
      USE_THEN "len3" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[MEM_FILTER] THEN
      USE_THEN "rlt" (MP_TAC o REWRITE_RULE[GSYM ALL_MEM]) THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s4:linear_scan_hidden_state`
    (CONJUNCTS_THEN2 (LABEL_TAC "x2eq") (CONJUNCTS_THEN2 (LABEL_TAC "x2len")
    (CONJUNCTS_THEN2 (LABEL_TAC "x2beg") (CONJUNCTS_THEN2 (LABEL_TAC "x2end")
    (CONJUNCTS_THEN2 (LABEL_TAC "x2inj") (CONJUNCTS_THEN2 (LABEL_TAC "x2b")
    (CONJUNCTS_THEN2 (LABEL_TAC "x2c") (CONJUNCTS_THEN2 (LABEL_TAC "x2e")
      (LABEL_TAC "x2d")))))))))) THEN
  EXISTS_TAC `s4:linear_scan_hidden_state` THEN
  USE_THEN "x2eq" (fun th -> REWRITE_TAC[GSYM th]) THEN
  MP_TAC(SPECL [`k:num`; `forced:(num#num)list`; `reglist:num list`; `stacklist:num list`;
    `linear_scan_hidden_state_int_beg sth`; `linear_scan_hidden_state_int_end sth`;
    `linear_scan_hidden_state_colors s1`; `linear_scan_hidden_state_colors s2`;
    `linear_scan_hidden_state_colors s3`; `linear_scan_hidden_state_colors s4`;
    `LENGTH (linear_scan_hidden_state_colors sth)`] LSCANPAUX_ivl_final) THEN
  USE_THEN "len1" (fun a -> USE_THEN "len3" (fun b -> USE_THEN "beg1" (fun c ->
    USE_THEN "end1" (fun d -> USE_THEN "beg3" (fun e -> USE_THEN "end3" (fun f ->
    USE_THEN "max1'" (fun g ->
      RULE_ASSUM_TAC(REWRITE_RULE[a; b; c; d; e; f; g])))))))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN USE_THEN "sl" (ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  USE_THEN "memR" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "permA" (fun th -> REWRITE_TAC[MATCH_MP PERM_EVERY th]) THEN
  USE_THEN "x2len" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[]);;


(* the record theorems of bijection_state, for REWRITE_TAC *)
let LSCANPAUX_bs_record =
  let ri = record_info "bijection_state" in
  [ri.ri_accessors; ri.ri_fupds; ri.ri_accfupds; ri.ri_fupdfupds];;

(* HOL4 line 4997 *)
let good_bijection_state_def = cake_def
  `good_bijection_state st regset <=>
     regset = domain (bijection_state_bij st) /\
     (sp_inverts (bijection_state_bij st) (bijection_state_invbij st) /\
      sp_inverts (bijection_state_invbij st) (bijection_state_bij st)) /\
     ((!r. r IN regset ==>
           (is_stack_var r <=> is_stack_var (misc_the 0 (lookup r (bijection_state_bij st))))) /\
      (!r. r IN regset ==>
           (is_alloc_var r <=> is_alloc_var (misc_the 0 (lookup r (bijection_state_bij st))))) /\
      (!r. r IN regset /\ is_phy_var r ==> r = misc_the 0 (lookup r (bijection_state_bij st)))) /\
     (!r. r IN domain (bijection_state_invbij st) /\ is_stack_var r ==>
          r < bijection_state_nstack st) /\
     (!r. r IN domain (bijection_state_invbij st) /\ is_alloc_var r ==>
          r < bijection_state_nalloc st) /\
     (is_stack_var (bijection_state_nstack st) /\ is_alloc_var (bijection_state_nalloc st)) /\
     (!r. misc_the 0 (lookup r (bijection_state_bij st)) <= bijection_state_nmax st)`;;
(* HOL4 line 5018 *)
let convention_partitions_or = prove
 (`!r. (is_phy_var r /\ ~is_stack_var r /\ ~is_alloc_var r) \/
       (~is_phy_var r /\ is_stack_var r /\ ~is_alloc_var r) \/
       (~is_phy_var r /\ ~is_stack_var r /\ is_alloc_var r)`,
    GEN_TAC THEN MP_TAC(SPEC `r:num` convention_partitions) THEN CONV_TAC TAUT);;

(* LSCANPAUX_var_add4: the variable kinds are invariant under adding 4 *)
let LSCANPAUX_var_add4 = prove
 (`!n. (is_stack_var (n + 4) <=> is_stack_var n) /\
       (is_alloc_var (n + 4) <=> is_alloc_var n)`,
  GEN_TAC THEN REWRITE_TAC[is_stack_var_def; is_alloc_var_def] THEN
  SUBGOAL_THEN `n + 4 = n + 4 * 1` SUBST1_TAC THENL [ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD]]);;

(* LSCANPAUX_gbs_insert: adding a fresh pair to a good bijection state *)
let LSCANPAUX_gbs_insert = prove
 (`!st st' regset r x.
     good_bijection_state st regset /\
     ~(r IN domain (bijection_state_bij st)) /\ ~(x IN domain (bijection_state_invbij st)) /\
     (is_stack_var r <=> is_stack_var x) /\ (is_alloc_var r <=> is_alloc_var x) /\
     (is_phy_var r ==> r = x) /\
     bijection_state_bij st' = insert r x (bijection_state_bij st) /\
     bijection_state_invbij st' = insert x r (bijection_state_invbij st) /\
     bijection_state_nmax st' = MAX x (bijection_state_nmax st) /\
     (!y. y IN domain (bijection_state_invbij st') /\ is_stack_var y ==>
          y < bijection_state_nstack st') /\
     (!y. y IN domain (bijection_state_invbij st') /\ is_alloc_var y ==>
          y < bijection_state_nalloc st') /\
     is_stack_var (bijection_state_nstack st') /\ is_alloc_var (bijection_state_nalloc st') ==>
     good_bijection_state st' (r INSERT regset)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[good_bijection_state_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rn") (CONJUNCTS_THEN2 (LABEL_TAC "xn")
    (CONJUNCTS_THEN2 (LABEL_TAC "sk") (CONJUNCTS_THEN2 (LABEL_TAC "ak")
    (CONJUNCTS_THEN2 (LABEL_TAC "pk") (CONJUNCTS_THEN2 (LABEL_TAC "bij'")
    (CONJUNCTS_THEN2 (LABEL_TAC "inv'") (CONJUNCTS_THEN2 (LABEL_TAC "nmax'")
    (CONJUNCTS_THEN2 (LABEL_TAC "g4") (CONJUNCTS_THEN2 (LABEL_TAC "g5")
      (LABEL_TAC "g6"))))))))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `regset = domain (bijection_state_bij st)`)) THEN
  USE_THEN "g4" (fun a -> USE_THEN "g5" (fun b -> USE_THEN "g6" (fun c ->
    REWRITE_TAC[a; b; c]))) THEN
  USE_THEN "bij'" (fun a -> USE_THEN "inv'" (fun b -> USE_THEN "nmax'" (fun c ->
    REWRITE_TAC[a; b; c]))) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[domain_insert];
    MATCH_MP_TAC sp_inverts_insert THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC sp_inverts_insert THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_INSERT; lookup_insert] THEN X_GEN_TAC `y:num` THEN
    ASM_CASES_TAC `y:num = r` THEN ASM_REWRITE_TAC[misc_the_def];
    REWRITE_TAC[IN_INSERT; lookup_insert] THEN X_GEN_TAC `y:num` THEN
    ASM_CASES_TAC `y:num = r` THEN ASM_REWRITE_TAC[misc_the_def];
    REWRITE_TAC[IN_INSERT; lookup_insert] THEN X_GEN_TAC `y:num` THEN
    ASM_CASES_TAC `y:num = r` THEN ASM_REWRITE_TAC[misc_the_def];
    REWRITE_TAC[lookup_insert] THEN X_GEN_TAC `y:num` THEN
    COND_CASES_TAC THEN REWRITE_TAC[misc_the_def] THENL
     [ARITH_TAC;
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `bijection_state_nmax st` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC]]);;

(* HOL4 line 5026 *)
let find_bijection_invariants = prove
 (`!st r regset.
     good_bijection_state st regset ==>
     good_bijection_state (find_bijection_step st r) (r INSERT regset)`,
    REPEAT GEN_TAC THEN REWRITE_TAC[find_bijection_step_def] THEN
  COND_CASES_TAC THENL
   [DISCH_TAC THEN SUBGOAL_THEN `(r:num) INSERT regset = regset` (fun th -> ASM_REWRITE_TAC[th]) THEN
    UNDISCH_TAC `good_bijection_state st regset` THEN REWRITE_TAC[good_bijection_state_def] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[lookup_NONE_domain] THEN SET_TAC[];
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "rn" o REWRITE_RULE[lookup_NONE_domain]) THEN
  DISCH_THEN(fun th -> LABEL_TAC "gbs" th THEN
    LSCANPAUX_LABEL_CONJS "g" (REWRITE_RULE[good_bijection_state_def] th)) THEN
  USE_THEN "g1" SUBST_ALL_TAC THEN
  MP_TAC(SPEC `r:num` convention_partitions_or) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LSCANPAUX_gbs_insert THENL
   [(* a physical register is its own image *)
    EXISTS_TAC `st:bijection_state` THEN EXISTS_TAC `r:num` THEN
    ASM_REWRITE_TAC(K_THM :: LSCANPAUX_bs_record) THEN
    SUBGOAL_THEN `~(r IN domain (bijection_state_invbij st))` ASSUME_TAC THENL
     [REWRITE_TAC[domain_lookup] THEN DISCH_THEN(X_CHOOSE_TAC `fr:num`) THEN
      SUBGOAL_THEN `lookup fr (bijection_state_bij st) = SOME r` ASSUME_TAC THENL
       [USE_THEN "g3" (MP_TAC o REWRITE_RULE[sp_inverts_def]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `fr IN domain (bijection_state_bij st)` ASSUME_TAC THENL
       [REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      MP_TAC(SPEC `fr:num` convention_partitions_or) THEN STRIP_TAC THENL
       [USE_THEN "g6" (fun th -> MP_TAC(MATCH_MP th (CONJ
          (ASSUME `fr IN domain (bijection_state_bij st)`) (ASSUME `is_phy_var fr`)))) THEN
        ASM_REWRITE_TAC[misc_the_def] THEN
        DISCH_THEN SUBST_ALL_TAC THEN USE_THEN "rn" MP_TAC THEN
        REWRITE_TAC[domain_lookup] THEN ASM_MESON_TAC[];
        USE_THEN "g4" (fun th -> MP_TAC(MATCH_MP th
          (ASSUME `fr IN domain (bijection_state_bij st)`))) THEN ASM_REWRITE_TAC[misc_the_def];
        USE_THEN "g5" (fun th -> MP_TAC(MATCH_MP th
          (ASSUME `fr IN domain (bijection_state_bij st)`))) THEN ASM_REWRITE_TAC[misc_the_def]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[domain_insert; IN_INSERT] THEN CONJ_TAC THEN X_GEN_TAC `y:num` THEN
    ASM_CASES_TAC `y:num = r` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    (* a stack variable gets the next stack slot *)
    EXISTS_TAC `st:bijection_state` THEN EXISTS_TAC `bijection_state_nstack st` THEN
    ASM_REWRITE_TAC(K_THM :: LSCANPAUX_var_add4 :: LSCANPAUX_bs_record) THEN
    SUBGOAL_THEN `~(bijection_state_nstack st IN domain (bijection_state_invbij st))`
      ASSUME_TAC THENL
     [DISCH_TAC THEN USE_THEN "g7" (fun th -> MP_TAC(MATCH_MP th (CONJ
        (ASSUME `bijection_state_nstack st IN domain (bijection_state_invbij st)`)
        (ASSUME `is_stack_var (bijection_state_nstack st)`)))) THEN
      REWRITE_TAC[LT_REFL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[domain_insert; IN_INSERT] THEN
    MP_TAC(SPEC `bijection_state_nstack st` convention_partitions) THEN
    MP_TAC(SPEC `r:num` convention_partitions) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `y:num` THEN
    DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC) THENL
     [ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MATCH_MP_TAC(ARITH_RULE `m < n ==> m < n + 4`) THEN
      USE_THEN "g7" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `is_alloc_var y` THEN ASM_REWRITE_TAC[];
      USE_THEN "g8" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* an allocatable variable gets the next allocation slot *)
    EXISTS_TAC `st:bijection_state` THEN EXISTS_TAC `bijection_state_nalloc st` THEN
    ASM_REWRITE_TAC(K_THM :: LSCANPAUX_var_add4 :: LSCANPAUX_bs_record) THEN
    SUBGOAL_THEN `~(bijection_state_nalloc st IN domain (bijection_state_invbij st))`
      ASSUME_TAC THENL
     [DISCH_TAC THEN USE_THEN "g8" (fun th -> MP_TAC(MATCH_MP th (CONJ
        (ASSUME `bijection_state_nalloc st IN domain (bijection_state_invbij st)`)
        (ASSUME `is_alloc_var (bijection_state_nalloc st)`)))) THEN
      REWRITE_TAC[LT_REFL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[domain_insert; IN_INSERT] THEN
    MP_TAC(SPEC `bijection_state_nalloc st` convention_partitions) THEN
    MP_TAC(SPEC `r:num` convention_partitions) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `y:num` THEN
    DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC) THENL
     [UNDISCH_TAC `is_stack_var y` THEN ASM_REWRITE_TAC[];
      USE_THEN "g7" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MATCH_MP_TAC(ARITH_RULE `m < n ==> m < n + 4`) THEN
      USE_THEN "g8" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;


(* HOL4 line 5128 *)
let FOLDL_find_bijection_invariants = prove
 (`!st l regset.
     good_bijection_state st regset ==>
     good_bijection_state (FOLDL find_bijection_step st l) (set_of_list l UNION regset)`,
    GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[FOLDL; set_of_list; UNION_EMPTY] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`find_bijection_step st h`; `(h:num) INSERT regset`]) THEN
  ANTS_TAC THENL [MATCH_MP_TAC find_bijection_invariants THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[]);;

(* LSCANPAUX_ITLIST_bij: find_bijection_step over an association list *)
let LSCANPAUX_ITLIST_bij = prove
 (`!(L:(num#A)list) st regset.
     good_bijection_state st regset ==>
     good_bijection_state (ITLIST (UNCURRY (\r v acc. find_bijection_step acc r)) L st)
       (set_of_list (MAP FST L) UNION regset)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; MAP; set_of_list; UNION_EMPTY] THEN
  MP_TAC(ISPEC `h:num#A` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `b:A` SUBST1_TAC)) THEN
  REWRITE_TAC[UNCURRY_DEF; FST] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a INSERT set_of_list (MAP FST (t:(num#A)list))) UNION regset =
                a INSERT (set_of_list (MAP FST t) UNION regset)` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC find_bijection_invariants THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 5142 *)
let foldi_find_bijection_invariants = prove
 (`!st (s:A spt) regset.
     good_bijection_state st regset ==>
     good_bijection_state (foldi (\r v acc. find_bijection_step acc r) 0 st s)
       (domain s UNION regset)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[foldi_FOLDR_toAList] THEN
  ONCE_REWRITE_TAC[GSYM set_MAP_FST_toAList_eq_domain] THEN
  MATCH_MP_TAC LSCANPAUX_ITLIST_bij THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 5156 *)
let in_clash_tree_set_eq = prove
 (CASE_TERM
  `(!w r. in_clash_tree (Delta w r) = set_of_list w UNION set_of_list r) /\
   (!names. in_clash_tree (reg_alloc_Set names) = domain names) /\
   (!name_opt t1 t2.
      in_clash_tree (reg_alloc_Branch name_opt t1 t2) =
        match name_opt with
          SOME names -> (domain names UNION in_clash_tree t1) UNION in_clash_tree t2
        | NONE -> in_clash_tree t1 UNION in_clash_tree t2) /\
   (!t1 t2. in_clash_tree (reg_alloc_Seq t1 t2) = in_clash_tree t1 UNION in_clash_tree t2)`,
    REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_SET_OF_LIST] THEN REWRITE_TAC[IN; in_clash_tree_def];
    REWRITE_TAC[EXTENSION] THEN REWRITE_TAC[IN; in_clash_tree_def];
    STRUCT_CASES_TAC(ISPEC `name_opt:(1 spt)option` option_CASES) THEN
    REWRITE_TAC[case_def "option"; EXTENSION; IN_UNION] THEN REWRITE_TAC[IN; in_clash_tree_def;
      case_def "option"] THEN MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_UNION] THEN REWRITE_TAC[IN; in_clash_tree_def]]);;

(* HOL4 line 5173 *)
let find_bijection_clash_tree_invariants = prove
 (`!st ct regset.
     good_bijection_state st regset ==>
     good_bijection_state (find_bijection_clash_tree st ct) (in_clash_tree ct UNION regset)`,
    GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN MATCH_MP_TAC clash_tree_INDUCT THEN
  REWRITE_TAC[find_bijection_clash_tree_def; in_clash_tree_set_eq; LET_DEF; LET_END_DEF] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(set_of_list a0 UNION set_of_list a1) UNION regset =
                  set_of_list a0 UNION (set_of_list a1 UNION (regset:num->bool))` SUBST1_TAC
    THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC FOLDL_find_bijection_invariants THEN
    MATCH_MP_TAC FOLDL_find_bijection_invariants THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC foldi_find_bijection_invariants THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `st:bijection_state` THEN
    X_GEN_TAC `regset:num->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `good_bijection_state
                    (find_bijection_clash_tree (find_bijection_clash_tree st a1) a2)
                    ((in_clash_tree a1 UNION in_clash_tree a2) UNION regset)` ASSUME_TAC THENL
     [SUBGOAL_THEN `(in_clash_tree a1 UNION in_clash_tree a2) UNION regset =
                    in_clash_tree a2 UNION (in_clash_tree a1 UNION (regset:num->bool))`
        SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISJ_CASES_THEN2 (X_CHOOSE_THEN `cs:1 spt` SUBST1_TAC) SUBST1_TAC
      (ISPEC `a0:(1 spt)option` option_CASES) THEN
    REWRITE_TAC[case_def "option"] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `((domain cs UNION in_clash_tree a1) UNION in_clash_tree a2) UNION regset =
                  domain (cs:1 spt) UNION ((in_clash_tree a1 UNION in_clash_tree a2) UNION
                  (regset:num->bool))` SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC foldi_find_bijection_invariants THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(in_clash_tree a0 UNION in_clash_tree a1) UNION regset =
                  in_clash_tree a1 UNION (in_clash_tree a0 UNION (regset:num->bool))`
      SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN ASM_MESON_TAC[]]);;

(* HOL4 line 5200 *)
let find_bijection_init_invariants = prove
 (`good_bijection_state find_bijection_init {}`,
    REWRITE_TAC(good_bijection_state_def :: find_bijection_init_def :: LSCANPAUX_bs_record) THEN
  REWRITE_TAC[sp_inverts_def; lookup_def; domain_def; NOT_IN_EMPTY; misc_the_def; LE_REFL;
              option_DISTINCT; is_stack_var_def; is_alloc_var_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;


(* HOL4 line 5206 *)
let sptree_eq_list_def = cake_def
  `sptree_eq_list (s:int spt) l <=>
     !i. i < LENGTH l ==>
         (&0 < EL i l <=> lookup i s = NONE) /\
         (EL i l <= &0 <=> lookup i s = SOME (EL i l))`;;
(* HOL4 line 5213 *)
let numset_list_add_if_lt_monad_correct = prove
 (`!int_beg sth l v.
     v <= &0 /\
     sptree_eq_list int_beg (linear_scan_hidden_state_int_beg sth) /\
     ALL (\r. r < LENGTH (linear_scan_hidden_state_int_beg sth)) l ==>
     ?sthout.
       numset_list_add_if_lt_monad l v sth = (M_success one,sthout) /\
       sptree_eq_list (numset_list_add_if_lt l v int_beg)
         (linear_scan_hidden_state_int_beg sthout) /\
       sthout = linear_scan_hidden_state_int_beg_fupd
                  (K (linear_scan_hidden_state_int_beg sthout)) sth /\
       LENGTH (linear_scan_hidden_state_int_beg sthout) =
         LENGTH (linear_scan_hidden_state_int_beg sth)`,
    REPEAT GEN_TAC THEN
  SPEC_TAC(`int_beg:int spt`,`s:int spt`) THEN SPEC_TAC(`sth:linear_scan_hidden_state`,`sth:linear_scan_hidden_state`) THEN
  SPEC_TAC(`v:int`,`v:int`) THEN SPEC_TAC(`l:num list`,`l:num list`) THEN
  LIST_INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `sth:linear_scan_hidden_state` THEN
    ASM_REWRITE_TAC(numset_list_add_if_lt_monad_def :: numset_list_add_if_lt_def ::
                    numset_list_add_if_def :: RAPROOFAUX_msimps) THEN
    REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
    REWRITE_TAC(K_THM :: LSCANPAUX_hs_record);
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "v0") (CONJUNCTS_THEN2 (LABEL_TAC "eq")
    (CONJUNCTS_THEN2 (LABEL_TAC "hlt") (LABEL_TAC "tlt")))) THEN
  REWRITE_TAC(numset_list_add_if_lt_monad_def :: RAPROOFAUX_msimps) THEN
  USE_THEN "hlt" (fun th -> REWRITE_TAC[int_beg_sub_eqn; th; case_def "prod"; case_def "exc"]) THEN
  REWRITE_TAC[numset_list_add_if_lt_def; numset_list_add_if_def] THEN
  REWRITE_TAC[GSYM numset_list_add_if_lt_def] THEN
  USE_THEN "eq" (MP_TAC o SPEC `h:num` o REWRITE_RULE[sptree_eq_list_def]) THEN
  USE_THEN "hlt" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "e1") (LABEL_TAC "e2")) THEN
  SUBGOAL_THEN
   `!s'. sptree_eq_list s' (linear_scan_hidden_state_int_beg sth) ==>
         sptree_eq_list (insert h v s')
           (LUPDATE v h (linear_scan_hidden_state_int_beg sth))` (LABEL_TAC "upd") THENL
   [GEN_TAC THEN REWRITE_TAC[sptree_eq_list_def; LENGTH_LUPDATE; EL_LUPDATE; lookup_insert] THEN
    DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "hlt" (fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `i:num = h` THEN ASM_SIMP_TAC[option_DISTINCT] THEN
    USE_THEN "v0" MP_TAC THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?sthout.
       numset_list_add_if_lt_monad t v
         (linear_scan_hidden_state_int_beg_fupd
            (K (LUPDATE v h (linear_scan_hidden_state_int_beg sth))) sth) =
         (M_success one,sthout) /\
       sptree_eq_list (numset_list_add_if_lt t v (insert h v s))
         (linear_scan_hidden_state_int_beg sthout) /\
       sthout = linear_scan_hidden_state_int_beg_fupd
                  (K (linear_scan_hidden_state_int_beg sthout)) sth /\
       LENGTH (linear_scan_hidden_state_int_beg sthout) =
         LENGTH (linear_scan_hidden_state_int_beg sth)` (LABEL_TAC "updcase") THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`v:int`;
      `linear_scan_hidden_state_int_beg_fupd
         (K (LUPDATE v h (linear_scan_hidden_state_int_beg sth))) sth`;
      `insert h v (s:int spt)`]) THEN
    REWRITE_TAC(K_THM :: LENGTH_LUPDATE :: LSCANPAUX_hs_record) THEN
    ANTS_TAC THENL
     [USE_THEN "v0" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "tlt" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "upd" MATCH_MP_TAC THEN USE_THEN "eq" ACCEPT_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `sthout:linear_scan_hidden_state` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rec") ASSUME_TAC)))) THEN
    EXISTS_TAC `sthout:linear_scan_hidden_state` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "rec" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
    REWRITE_TAC(K_THM :: o_THM :: LSCANPAUX_hs_record);
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < EL h (linear_scan_hidden_state_int_beg sth)` THENL
   [SUBGOAL_THEN `lookup h (s:int spt) = NONE` (LABEL_TAC "lk") THENL
     [USE_THEN "e1" (fun th -> REWRITE_TAC[GSYM th]) THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    USE_THEN "lk" (fun th -> REWRITE_TAC[th; case_def "option"]) THEN
    REWRITE_TAC[ASSUME `&0 < EL h (linear_scan_hidden_state_int_beg sth)`] THEN
    REWRITE_TAC(update_int_beg_eqn :: RAPROOFAUX_msimps) THEN
    USE_THEN "hlt" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
    USE_THEN "updcase" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lookup h (s:int spt) = SOME (EL h (linear_scan_hidden_state_int_beg sth))` (LABEL_TAC "lk") THENL
   [USE_THEN "e2" (fun th -> REWRITE_TAC[GSYM th]) THEN
    UNDISCH_TAC `~(&0 < EL h (linear_scan_hidden_state_int_beg sth))` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "lk" (fun th -> REWRITE_TAC[th; case_def "option"]) THEN
  REWRITE_TAC[ASSUME `~(&0 < EL h (linear_scan_hidden_state_int_beg sth))`] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC(update_int_beg_eqn :: RAPROOFAUX_msimps) THEN
    USE_THEN "hlt" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
    USE_THEN "updcase" ACCEPT_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`v:int`; `sth:linear_scan_hidden_state`; `s:int spt`]) THEN
    USE_THEN "v0" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "tlt" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "eq" (fun th -> REWRITE_TAC[th])]);;

(* HOL4 line 5234 *)
let numset_list_add_if_gt_monad_correct = prove
 (`!int_end sth l v.
     v <= &0 /\
     sptree_eq_list int_end (linear_scan_hidden_state_int_end sth) /\
     ALL (\r. r < LENGTH (linear_scan_hidden_state_int_end sth)) l ==>
     ?sthout.
       numset_list_add_if_gt_monad l v sth = (M_success one,sthout) /\
       sptree_eq_list (numset_list_add_if_gt l v int_end)
         (linear_scan_hidden_state_int_end sthout) /\
       sthout = linear_scan_hidden_state_int_end_fupd
                  (K (linear_scan_hidden_state_int_end sthout)) sth /\
       LENGTH (linear_scan_hidden_state_int_end sthout) =
         LENGTH (linear_scan_hidden_state_int_end sth)`,
    REPEAT GEN_TAC THEN
  SPEC_TAC(`int_end:int spt`,`s:int spt`) THEN SPEC_TAC(`sth:linear_scan_hidden_state`,`sth:linear_scan_hidden_state`) THEN
  SPEC_TAC(`v:int`,`v:int`) THEN SPEC_TAC(`l:num list`,`l:num list`) THEN
  LIST_INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `sth:linear_scan_hidden_state` THEN
    ASM_REWRITE_TAC(numset_list_add_if_gt_monad_def :: numset_list_add_if_gt_def ::
                    numset_list_add_if_def :: RAPROOFAUX_msimps) THEN
    REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
    REWRITE_TAC(K_THM :: LSCANPAUX_hs_record);
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ALL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "v0") (CONJUNCTS_THEN2 (LABEL_TAC "eq")
    (CONJUNCTS_THEN2 (LABEL_TAC "hlt") (LABEL_TAC "tlt")))) THEN
  REWRITE_TAC(numset_list_add_if_gt_monad_def :: RAPROOFAUX_msimps) THEN
  USE_THEN "hlt" (fun th -> REWRITE_TAC[int_end_sub_eqn; th; case_def "prod"; case_def "exc"]) THEN
  REWRITE_TAC[numset_list_add_if_gt_def; numset_list_add_if_def] THEN
  REWRITE_TAC[GSYM numset_list_add_if_gt_def] THEN
  USE_THEN "eq" (MP_TAC o SPEC `h:num` o REWRITE_RULE[sptree_eq_list_def]) THEN
  USE_THEN "hlt" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "e1") (LABEL_TAC "e2")) THEN
  SUBGOAL_THEN
   `!s'. sptree_eq_list s' (linear_scan_hidden_state_int_end sth) ==>
         sptree_eq_list (insert h v s')
           (LUPDATE v h (linear_scan_hidden_state_int_end sth))` (LABEL_TAC "upd") THENL
   [GEN_TAC THEN REWRITE_TAC[sptree_eq_list_def; LENGTH_LUPDATE; EL_LUPDATE; lookup_insert] THEN
    DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "hlt" (fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `i:num = h` THEN ASM_SIMP_TAC[option_DISTINCT] THEN
    USE_THEN "v0" MP_TAC THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?sthout.
       numset_list_add_if_gt_monad t v
         (linear_scan_hidden_state_int_end_fupd
            (K (LUPDATE v h (linear_scan_hidden_state_int_end sth))) sth) =
         (M_success one,sthout) /\
       sptree_eq_list (numset_list_add_if_gt t v (insert h v s))
         (linear_scan_hidden_state_int_end sthout) /\
       sthout = linear_scan_hidden_state_int_end_fupd
                  (K (linear_scan_hidden_state_int_end sthout)) sth /\
       LENGTH (linear_scan_hidden_state_int_end sthout) =
         LENGTH (linear_scan_hidden_state_int_end sth)` (LABEL_TAC "updcase") THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`v:int`;
      `linear_scan_hidden_state_int_end_fupd
         (K (LUPDATE v h (linear_scan_hidden_state_int_end sth))) sth`;
      `insert h v (s:int spt)`]) THEN
    REWRITE_TAC(K_THM :: LENGTH_LUPDATE :: LSCANPAUX_hs_record) THEN
    ANTS_TAC THENL
     [USE_THEN "v0" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "tlt" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "upd" MATCH_MP_TAC THEN USE_THEN "eq" ACCEPT_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `sthout:linear_scan_hidden_state` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rec") ASSUME_TAC)))) THEN
    EXISTS_TAC `sthout:linear_scan_hidden_state` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "rec" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
    REWRITE_TAC(K_THM :: o_THM :: LSCANPAUX_hs_record);
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < EL h (linear_scan_hidden_state_int_end sth)` THENL
   [SUBGOAL_THEN `lookup h (s:int spt) = NONE` (LABEL_TAC "lk") THENL
     [USE_THEN "e1" (fun th -> REWRITE_TAC[GSYM th]) THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    USE_THEN "lk" (fun th -> REWRITE_TAC[th; case_def "option"]) THEN
    REWRITE_TAC[ASSUME `&0 < EL h (linear_scan_hidden_state_int_end sth)`] THEN
    REWRITE_TAC(update_int_end_eqn :: RAPROOFAUX_msimps) THEN
    USE_THEN "hlt" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
    USE_THEN "updcase" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lookup h (s:int spt) = SOME (EL h (linear_scan_hidden_state_int_end sth))` (LABEL_TAC "lk") THENL
   [USE_THEN "e2" (fun th -> REWRITE_TAC[GSYM th]) THEN
    UNDISCH_TAC `~(&0 < EL h (linear_scan_hidden_state_int_end sth))` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "lk" (fun th -> REWRITE_TAC[th; case_def "option"]) THEN
  REWRITE_TAC[ASSUME `~(&0 < EL h (linear_scan_hidden_state_int_end sth))`] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC(update_int_end_eqn :: RAPROOFAUX_msimps) THEN
    USE_THEN "hlt" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
    USE_THEN "updcase" ACCEPT_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`v:int`; `sth:linear_scan_hidden_state`; `s:int spt`]) THEN
    USE_THEN "v0" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "tlt" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "eq" (fun th -> REWRITE_TAC[th])]);;


(* LSCANPAUX_hs2_eq: the two-field record equation of the interval monad *)
let LSCANPAUX_hs2_trans = prove
 (`!s1 s2 s3.
     s2 = linear_scan_hidden_state_int_beg_fupd (K (linear_scan_hidden_state_int_beg s2))
            (linear_scan_hidden_state_int_end_fupd (K (linear_scan_hidden_state_int_end s2))
               s1) /\
     s3 = linear_scan_hidden_state_int_beg_fupd (K (linear_scan_hidden_state_int_beg s3))
            (linear_scan_hidden_state_int_end_fupd (K (linear_scan_hidden_state_int_end s3))
               s2) ==>
     s3 = linear_scan_hidden_state_int_beg_fupd (K (linear_scan_hidden_state_int_beg s3))
            (linear_scan_hidden_state_int_end_fupd (K (linear_scan_hidden_state_int_end s3))
               s1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th ->
    GEN_REWRITE_TAC LAND_CONV [th])) THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
  REWRITE_TAC(K_THM :: o_THM :: LSCANPAUX_hs_record));;

(* HOL4 line 5255 *)
let get_intervals_ct_monad_aux_correct = prove
 (`!ct sth live n int_beg int_end nout int_begout int_endout liveout.
     n <= &0 /\
     sptree_eq_list int_beg (linear_scan_hidden_state_int_beg sth) /\
     sptree_eq_list int_end (linear_scan_hidden_state_int_end sth) /\
     get_intervals_ct_aux ct n int_beg int_end live = (nout,int_begout,int_endout,liveout) /\
     LENGTH (linear_scan_hidden_state_int_end sth) =
       LENGTH (linear_scan_hidden_state_int_beg sth) /\
     (!r. in_clash_tree ct r ==> r < LENGTH (linear_scan_hidden_state_int_beg sth)) /\
     (!r. r IN domain live ==> r < LENGTH (linear_scan_hidden_state_int_beg sth)) ==>
     ?sthout.
       get_intervals_ct_monad_aux ct n live sth = (M_success (nout,liveout),sthout) /\
       sptree_eq_list int_begout (linear_scan_hidden_state_int_beg sthout) /\
       sptree_eq_list int_endout (linear_scan_hidden_state_int_end sthout) /\
       LENGTH (linear_scan_hidden_state_int_beg sthout) =
         LENGTH (linear_scan_hidden_state_int_beg sth) /\
       LENGTH (linear_scan_hidden_state_int_end sthout) =
         LENGTH (linear_scan_hidden_state_int_end sth) /\
       (!r. r IN domain liveout ==> r < LENGTH (linear_scan_hidden_state_int_beg sth)) /\
       sthout = linear_scan_hidden_state_int_beg_fupd
                  (K (linear_scan_hidden_state_int_beg sthout))
                  (linear_scan_hidden_state_int_end_fupd
                     (K (linear_scan_hidden_state_int_end sthout)) sth) /\
       nout <= &0`,
    MATCH_MP_TAC clash_tree_INDUCT THEN REPEAT CONJ_TAC THENL
   [(* Delta *)
    MAP_EVERY X_GEN_TAC [`wr:num list`; `rd:num list`] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[get_intervals_ct_aux_def; PAIR_EQ; in_clash_tree_def] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "n0") (CONJUNCTS_THEN2 (LABEL_TAC "eb")
      (CONJUNCTS_THEN2 (LABEL_TAC "ee") (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
        (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
          (SUBST1_TAC o SYM))))
      (CONJUNCTS_THEN2 (LABEL_TAC "len") (CONJUNCTS_THEN2 (LABEL_TAC "ct")
        (LABEL_TAC "lv"))))))) THEN
    REWRITE_TAC(get_intervals_ct_monad_aux_def :: RAPROOFAUX_msimps) THEN
    MP_TAC(SPECL [`int_beg:int spt`; `sth:linear_scan_hidden_state`; `wr:num list`; `n:int`]
      numset_list_add_if_lt_monad_correct) THEN
    ANTS_TAC THENL
     [USE_THEN "n0" (fun a -> USE_THEN "eb" (fun b -> REWRITE_TAC[a; b])) THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN USE_THEN "ct" (fun th -> MESON_TAC[th]);
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:linear_scan_hidden_state` (CONJUNCTS_THEN2 (LABEL_TAC "q1")
      (CONJUNCTS_THEN2 (LABEL_TAC "b1") (CONJUNCTS_THEN2 (LABEL_TAC "r1") (LABEL_TAC "l1"))))) THEN
    USE_THEN "q1" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
    USE_THEN "r1" (fun th -> LABEL_TAC "e1" (REWRITE_RULE(K_THM :: LSCANPAUX_hs_record)
      (AP_TERM `linear_scan_hidden_state_int_end` th))) THEN
    MP_TAC(SPECL [`int_end:int spt`; `s1:linear_scan_hidden_state`; `wr:num list`; `n:int`]
      numset_list_add_if_gt_monad_correct) THEN
    ANTS_TAC THENL
     [USE_THEN "e1" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "n0" (fun a -> USE_THEN "ee" (fun b -> REWRITE_TAC[a; b])) THEN
      USE_THEN "len" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN USE_THEN "ct" (fun th -> MESON_TAC[th]);
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s2:linear_scan_hidden_state` (CONJUNCTS_THEN2 (LABEL_TAC "q2")
      (CONJUNCTS_THEN2 (LABEL_TAC "e2") (CONJUNCTS_THEN2 (LABEL_TAC "r2") (LABEL_TAC "l2"))))) THEN
    USE_THEN "q2" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
    USE_THEN "r2" (fun th -> LABEL_TAC "b2" (REWRITE_RULE(K_THM :: LSCANPAUX_hs_record)
      (AP_TERM `linear_scan_hidden_state_int_beg` th))) THEN
    MP_TAC(SPECL [`numset_list_add_if_gt wr n int_end`; `s2:linear_scan_hidden_state`;
      `rd:num list`; `(n:int) - &1`] numset_list_add_if_gt_monad_correct) THEN
    ANTS_TAC THENL
     [USE_THEN "e2" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "l2" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "e1" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "len" (fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THENL [USE_THEN "n0" MP_TAC THEN INT_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN USE_THEN "ct" (fun th -> MESON_TAC[th]);
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s3:linear_scan_hidden_state` (CONJUNCTS_THEN2 (LABEL_TAC "q3")
      (CONJUNCTS_THEN2 (LABEL_TAC "e3") (CONJUNCTS_THEN2 (LABEL_TAC "r3") (LABEL_TAC "l3"))))) THEN
    USE_THEN "q3" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
    USE_THEN "r3" (fun th -> LABEL_TAC "b3" (REWRITE_RULE(K_THM :: LSCANPAUX_hs_record)
      (AP_TERM `linear_scan_hidden_state_int_beg` th))) THEN
    EXISTS_TAC `s3:linear_scan_hidden_state` THEN REWRITE_TAC[PAIR_EQ] THEN
    USE_THEN "b3" (fun a -> USE_THEN "b2" (fun b -> REWRITE_TAC[a; b])) THEN
    USE_THEN "b1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "e3" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "l1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "l3" (fun a -> USE_THEN "l2" (fun b -> REWRITE_TAC[a; b])) THEN
    USE_THEN "e1" (fun th -> REWRITE_TAC[th]) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[linear_scanProof_domain_numset_list_insert;
                  linear_scanProof_domain_numset_list_delete; IN_UNION; IN_DIFF;
                  IN_SET_OF_LIST] THEN
      USE_THEN "ct" MP_TAC THEN USE_THEN "lv" MP_TAC THEN MESON_TAC[];
      USE_THEN "r3" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      USE_THEN "r2" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
      USE_THEN "r1" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
      REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
      REWRITE_TAC(K_THM :: o_THM :: LSCANPAUX_hs_record);
      USE_THEN "n0" MP_TAC THEN INT_ARITH_TAC];
    (* Set *)
    X_GEN_TAC `cs:1 spt` THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[get_intervals_ct_aux_def; PAIR_EQ; in_clash_tree_def] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "n0") (CONJUNCTS_THEN2 (LABEL_TAC "eb")
      (CONJUNCTS_THEN2 (LABEL_TAC "ee") (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
        (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
          (SUBST1_TAC o SYM))))
      (CONJUNCTS_THEN2 (LABEL_TAC "len") (CONJUNCTS_THEN2 (LABEL_TAC "ct")
        (LABEL_TAC "lv"))))))) THEN
    REWRITE_TAC(get_intervals_ct_monad_aux_def :: RAPROOFAUX_msimps) THEN
    MP_TAC(SPECL [`int_end:int spt`; `sth:linear_scan_hidden_state`;
      `MAP FST (toAList (cs:1 spt))`; `n:int`] numset_list_add_if_gt_monad_correct) THEN
    ANTS_TAC THENL
     [USE_THEN "n0" (fun a -> USE_THEN "ee" (fun b -> REWRITE_TAC[a; b])) THEN
      USE_THEN "len" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[GSYM ALL_MEM; GSYM IN_SET_OF_LIST; set_MAP_FST_toAList_eq_domain] THEN
      USE_THEN "ct" ACCEPT_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:linear_scan_hidden_state` (CONJUNCTS_THEN2 (LABEL_TAC "q1")
      (CONJUNCTS_THEN2 (LABEL_TAC "e1") (CONJUNCTS_THEN2 (LABEL_TAC "r1") (LABEL_TAC "l1"))))) THEN
    USE_THEN "q1" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
    USE_THEN "r1" (fun th -> LABEL_TAC "b1" (REWRITE_RULE(K_THM :: LSCANPAUX_hs_record)
      (AP_TERM `linear_scan_hidden_state_int_beg` th))) THEN
    EXISTS_TAC `s1:linear_scan_hidden_state` THEN REWRITE_TAC[PAIR_EQ] THEN
    USE_THEN "b1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "e1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "eb" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "l1" (fun th -> REWRITE_TAC[th]) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[domain_union; IN_UNION] THEN
      USE_THEN "ct" MP_TAC THEN USE_THEN "lv" MP_TAC THEN MESON_TAC[];
      USE_THEN "r1" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
      REWRITE_TAC(K_THM :: o_THM :: LSCANPAUX_hs_record);
      USE_THEN "n0" MP_TAC THEN INT_ARITH_TAC];
    (* Branch *)
    MAP_EVERY X_GEN_TAC [`opt:(1 spt)option`; `c1:clash_tree`; `c2:clash_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    MAP_EVERY X_GEN_TAC [`sth:linear_scan_hidden_state`; `live:1 spt`; `n:int`;
      `int_beg:int spt`; `int_end:int spt`; `nout:int`; `int_begout:int spt`;
      `int_endout:int spt`; `liveout:1 spt`] THEN
    REWRITE_TAC[in_clash_tree_def] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "n0") (CONJUNCTS_THEN2 (LABEL_TAC "eb")
      (CONJUNCTS_THEN2 (LABEL_TAC "ee") (CONJUNCTS_THEN2 (LABEL_TAC "aux")
      (CONJUNCTS_THEN2 (LABEL_TAC "len") (CONJUNCTS_THEN2 (LABEL_TAC "ct")
        (LABEL_TAC "lv"))))))) THEN
    MP_TAC(ISPEC `get_intervals_ct_aux c2 n int_beg int_end live` BASICAUX_TUPLE4) THEN
    DISCH_THEN(X_CHOOSE_THEN `n2:int` (X_CHOOSE_THEN `b2:int spt` (X_CHOOSE_THEN `e2:int spt`
      (X_CHOOSE_THEN `lv2:1 spt` (LABEL_TAC "a2"))))) THEN
    MP_TAC(ISPEC `get_intervals_ct_aux c1 n2 b2 e2 live` BASICAUX_TUPLE4) THEN
    DISCH_THEN(X_CHOOSE_THEN `n1:int` (X_CHOOSE_THEN `b1:int spt` (X_CHOOSE_THEN `e1:int spt`
      (X_CHOOSE_THEN `lv1:1 spt` (LABEL_TAC "a1"))))) THEN
    USE_THEN "aux" (MP_TAC o REWRITE_RULE[get_intervals_ct_aux_def]) THEN
    USE_THEN "a2" (fun th -> REWRITE_TAC[th; pair_CASE]) THEN
    USE_THEN "a1" (fun th -> REWRITE_TAC[th; pair_CASE]) THEN
    DISCH_THEN(LABEL_TAC "aux'") THEN
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`sth:linear_scan_hidden_state`; `live:1 spt`; `n:int`;
      `int_beg:int spt`; `int_end:int spt`; `n2:int`; `b2:int spt`; `e2:int spt`;
      `lv2:1 spt`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      REPEAT STRIP_TAC THEN USE_THEN "ct" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s2:linear_scan_hidden_state` (CONJUNCTS_THEN2 (LABEL_TAC "q2")
      (CONJUNCTS_THEN2 (LABEL_TAC "sb2") (CONJUNCTS_THEN2 (LABEL_TAC "se2")
      (CONJUNCTS_THEN2 (LABEL_TAC "lb2") (CONJUNCTS_THEN2 (LABEL_TAC "le2")
      (CONJUNCTS_THEN2 (LABEL_TAC "lvb2") (CONJUNCTS_THEN2 (LABEL_TAC "r2")
        (LABEL_TAC "n2le"))))))))) THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`s2:linear_scan_hidden_state`; `live:1 spt`; `n2:int`;
      `b2:int spt`; `e2:int spt`; `n1:int`; `b1:int spt`; `e1:int spt`; `lv1:1 spt`]) THEN
    USE_THEN "lb2" (fun a -> USE_THEN "le2" (fun b -> REWRITE_TAC[a; b])) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      REPEAT STRIP_TAC THEN USE_THEN "ct" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:linear_scan_hidden_state` (CONJUNCTS_THEN2 (LABEL_TAC "q1")
      (CONJUNCTS_THEN2 (LABEL_TAC "sb1") (CONJUNCTS_THEN2 (LABEL_TAC "se1")
      (CONJUNCTS_THEN2 (LABEL_TAC "lb1") (CONJUNCTS_THEN2 (LABEL_TAC "le1")
      (CONJUNCTS_THEN2 (LABEL_TAC "lvb1") (CONJUNCTS_THEN2 (LABEL_TAC "r1")
        (LABEL_TAC "n1le"))))))))) THEN
    USE_THEN "r2" (fun a -> USE_THEN "r1" (fun b ->
      LABEL_TAC "r12" (MATCH_MP LSCANPAUX_hs2_trans (CONJ a b)))) THEN
    REWRITE_TAC(get_intervals_ct_monad_aux_def :: RAPROOFAUX_msimps) THEN
    USE_THEN "q2" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"; pair_CASE]) THEN
    USE_THEN "q1" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"; pair_CASE]) THEN
    DISJ_CASES_THEN2 (X_CHOOSE_THEN `cs:1 spt` SUBST_ALL_TAC) SUBST_ALL_TAC
      (ISPEC `opt:(1 spt)option` option_CASES) THEN
    REMOVE_THEN "aux'" (MP_TAC o REWRITE_RULE[case_def "option"; PAIR_EQ]) THEN
    REWRITE_TAC[case_def "option"] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
      (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (SUBST1_TAC o SYM)))) THENL
     [(* SOME cs *)
      MP_TAC(SPECL [`e1:int spt`; `s1:linear_scan_hidden_state`;
        `MAP FST (toAList (cs:1 spt))`; `n1:int`] numset_list_add_if_gt_monad_correct) THEN
      ANTS_TAC THENL
       [USE_THEN "n1le" (fun a -> USE_THEN "se1" (fun b -> REWRITE_TAC[a; b])) THEN
        USE_THEN "le1" (fun a -> USE_THEN "le2" (fun b -> USE_THEN "len" (fun c ->
          REWRITE_TAC[a; b; c]))) THEN
        REWRITE_TAC[GSYM ALL_MEM; GSYM IN_SET_OF_LIST; set_MAP_FST_toAList_eq_domain] THEN
        REPEAT STRIP_TAC THEN USE_THEN "ct" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[case_def "option"];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `s0:linear_scan_hidden_state` (CONJUNCTS_THEN2 (LABEL_TAC "q0")
        (CONJUNCTS_THEN2 (LABEL_TAC "se0") (CONJUNCTS_THEN2 (LABEL_TAC "r0")
          (LABEL_TAC "l0"))))) THEN
      USE_THEN "q0" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
      USE_THEN "r0" (fun th -> LABEL_TAC "sb0" (REWRITE_RULE(K_THM :: LSCANPAUX_hs_record)
        (AP_TERM `linear_scan_hidden_state_int_beg` th))) THEN
      EXISTS_TAC `s0:linear_scan_hidden_state` THEN REWRITE_TAC[PAIR_EQ] THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "sb0" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "sb1" ACCEPT_TAC;
        USE_THEN "se0" ACCEPT_TAC;
        USE_THEN "sb0" (fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "lb1" (fun a -> USE_THEN "lb2" (fun b -> REWRITE_TAC[a; b]));
        USE_THEN "l0" (fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "le1" (fun a -> USE_THEN "le2" (fun b -> REWRITE_TAC[a; b]));
        REWRITE_TAC[domain_union; IN_UNION] THEN
        USE_THEN "ct" (MP_TAC o REWRITE_RULE[case_def "option"]) THEN
        USE_THEN "lvb1" MP_TAC THEN USE_THEN "lvb2" MP_TAC THEN
        USE_THEN "lb2" (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[];
        MATCH_MP_TAC LSCANPAUX_hs2_trans THEN EXISTS_TAC `s1:linear_scan_hidden_state` THEN
        CONJ_TAC THENL [USE_THEN "r12" ACCEPT_TAC; ALL_TAC] THEN
        USE_THEN "r0" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
        REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
        REWRITE_TAC(K_THM :: o_THM :: LSCANPAUX_hs_record) THEN
        USE_THEN "sb0" (fun th -> REWRITE_TAC[th]);
        USE_THEN "n1le" MP_TAC THEN INT_ARITH_TAC];
      (* NONE *)
      EXISTS_TAC `s1:linear_scan_hidden_state` THEN
      REWRITE_TAC RAPROOFAUX_msimps THEN REWRITE_TAC[PAIR_EQ] THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "sb1" ACCEPT_TAC;
        USE_THEN "se1" ACCEPT_TAC;
        USE_THEN "lb1" (fun a -> USE_THEN "lb2" (fun b -> REWRITE_TAC[a; b]));
        USE_THEN "le1" (fun a -> USE_THEN "le2" (fun b -> REWRITE_TAC[a; b]));
        REWRITE_TAC[domain_union; IN_UNION] THEN
        USE_THEN "lvb1" MP_TAC THEN USE_THEN "lvb2" MP_TAC THEN
        USE_THEN "lb2" (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[];
        USE_THEN "r12" ACCEPT_TAC;
        USE_THEN "n1le" ACCEPT_TAC]];
    (* Seq *)
    MAP_EVERY X_GEN_TAC [`c1:clash_tree`; `c2:clash_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    MAP_EVERY X_GEN_TAC [`sth:linear_scan_hidden_state`; `live:1 spt`; `n:int`;
      `int_beg:int spt`; `int_end:int spt`; `nout:int`; `int_begout:int spt`;
      `int_endout:int spt`; `liveout:1 spt`] THEN
    REWRITE_TAC[in_clash_tree_def] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "n0") (CONJUNCTS_THEN2 (LABEL_TAC "eb")
      (CONJUNCTS_THEN2 (LABEL_TAC "ee") (CONJUNCTS_THEN2 (LABEL_TAC "aux")
      (CONJUNCTS_THEN2 (LABEL_TAC "len") (CONJUNCTS_THEN2 (LABEL_TAC "ct")
        (LABEL_TAC "lv"))))))) THEN
    MP_TAC(ISPEC `get_intervals_ct_aux c2 n int_beg int_end live` BASICAUX_TUPLE4) THEN
    DISCH_THEN(X_CHOOSE_THEN `n2:int` (X_CHOOSE_THEN `b2:int spt` (X_CHOOSE_THEN `e2:int spt`
      (X_CHOOSE_THEN `lv2:1 spt` (LABEL_TAC "a2"))))) THEN
    USE_THEN "aux" (MP_TAC o REWRITE_RULE[get_intervals_ct_aux_def]) THEN
    USE_THEN "a2" (fun th -> REWRITE_TAC[th; pair_CASE]) THEN
    DISCH_THEN(LABEL_TAC "aux'") THEN
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`sth:linear_scan_hidden_state`; `live:1 spt`; `n:int`;
      `int_beg:int spt`; `int_end:int spt`; `n2:int`; `b2:int spt`; `e2:int spt`;
      `lv2:1 spt`]) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      REPEAT STRIP_TAC THEN USE_THEN "ct" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s2:linear_scan_hidden_state` (CONJUNCTS_THEN2 (LABEL_TAC "q2")
      (CONJUNCTS_THEN2 (LABEL_TAC "sb2") (CONJUNCTS_THEN2 (LABEL_TAC "se2")
      (CONJUNCTS_THEN2 (LABEL_TAC "lb2") (CONJUNCTS_THEN2 (LABEL_TAC "le2")
      (CONJUNCTS_THEN2 (LABEL_TAC "lvb2") (CONJUNCTS_THEN2 (LABEL_TAC "r2")
        (LABEL_TAC "n2le"))))))))) THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`s2:linear_scan_hidden_state`; `lv2:1 spt`; `n2:int`;
      `b2:int spt`; `e2:int spt`; `nout:int`; `int_begout:int spt`; `int_endout:int spt`;
      `liveout:1 spt`]) THEN
    USE_THEN "lb2" (fun a -> USE_THEN "le2" (fun b -> REWRITE_TAC[a; b])) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      REPEAT STRIP_TAC THEN USE_THEN "ct" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:linear_scan_hidden_state` (CONJUNCTS_THEN2 (LABEL_TAC "q1")
      (CONJUNCTS_THEN2 (LABEL_TAC "sb1") (CONJUNCTS_THEN2 (LABEL_TAC "se1")
      (CONJUNCTS_THEN2 (LABEL_TAC "lb1") (CONJUNCTS_THEN2 (LABEL_TAC "le1")
      (CONJUNCTS_THEN2 (LABEL_TAC "lvb1") (CONJUNCTS_THEN2 (LABEL_TAC "r1")
        (LABEL_TAC "n1le"))))))))) THEN
    REWRITE_TAC(get_intervals_ct_monad_aux_def :: RAPROOFAUX_msimps) THEN
    USE_THEN "q2" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"; pair_CASE]) THEN
    EXISTS_TAC `s1:linear_scan_hidden_state` THEN
    USE_THEN "q1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "sb1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "se1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "lb1" (fun a -> USE_THEN "lb2" (fun b -> REWRITE_TAC[a; b])) THEN
    USE_THEN "le1" (fun a -> USE_THEN "le2" (fun b -> REWRITE_TAC[a; b])) THEN
    USE_THEN "n1le" (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THENL
     [USE_THEN "lvb1" MP_TAC THEN USE_THEN "lb2" (fun th -> REWRITE_TAC[th]);
      MATCH_MP_TAC LSCANPAUX_hs2_trans THEN EXISTS_TAC `s2:linear_scan_hidden_state` THEN
      CONJ_TAC THENL [USE_THEN "r2" ACCEPT_TAC; USE_THEN "r1" ACCEPT_TAC]]]);;


(* HOL4 line 5349 *)
let get_intervals_ct_monad_correct = prove
 (`!ct sth n int_beg int_end.
     (!i. i < LENGTH (linear_scan_hidden_state_int_beg sth) ==>
          &0 < EL i (linear_scan_hidden_state_int_beg sth)) /\
     (!i. i < LENGTH (linear_scan_hidden_state_int_end sth) ==>
          &0 < EL i (linear_scan_hidden_state_int_end sth)) /\
     get_intervals_ct ct = (n,int_beg,int_end) /\
     LENGTH (linear_scan_hidden_state_int_end sth) =
       LENGTH (linear_scan_hidden_state_int_beg sth) /\
     (!r. in_clash_tree ct r ==> r < LENGTH (linear_scan_hidden_state_int_beg sth)) ==>
     ?sthout.
       get_intervals_ct_monad ct sth = (M_success n,sthout) /\
       sptree_eq_list int_beg (linear_scan_hidden_state_int_beg sthout) /\
       sptree_eq_list int_end (linear_scan_hidden_state_int_end sthout) /\
       LENGTH (linear_scan_hidden_state_int_beg sthout) =
         LENGTH (linear_scan_hidden_state_int_beg sth) /\
       LENGTH (linear_scan_hidden_state_int_end sthout) =
         LENGTH (linear_scan_hidden_state_int_end sth) /\
       sthout = linear_scan_hidden_state_int_beg_fupd
                  (K (linear_scan_hidden_state_int_beg sthout))
                  (linear_scan_hidden_state_int_end_fupd
                     (K (linear_scan_hidden_state_int_end sthout)) sth)`,
    REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pb") (CONJUNCTS_THEN2 (LABEL_TAC "pe")
    (CONJUNCTS_THEN2 (LABEL_TAC "gi") (CONJUNCTS_THEN2 (LABEL_TAC "len") (LABEL_TAC "ct"))))) THEN
  MP_TAC(ISPEC `get_intervals_ct_aux ct (&0) LN LN LN` BASICAUX_TUPLE4) THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:int` (X_CHOOSE_THEN `b1:int spt` (X_CHOOSE_THEN `e1:int spt`
    (X_CHOOSE_THEN `lv1:1 spt` (LABEL_TAC "a1"))))) THEN
  USE_THEN "gi" (MP_TAC o REWRITE_RULE[get_intervals_ct_def; LET_DEF; LET_END_DEF]) THEN
  USE_THEN "a1" (fun th -> REWRITE_TAC[th; pair_CASE; PAIR_EQ]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (CONJUNCTS_THEN2 (SUBST1_TAC o SYM)
    (SUBST1_TAC o SYM))) THEN
  MP_TAC(SPECL [`ct:clash_tree`; `sth:linear_scan_hidden_state`; `LN:1 spt`; `&0:int`;
    `LN:int spt`; `LN:int spt`; `n1:int`; `b1:int spt`; `e1:int spt`; `lv1:1 spt`]
    get_intervals_ct_monad_aux_correct) THEN
  ANTS_TAC THENL
   [USE_THEN "a1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "len" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "ct" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[domain_def; NOT_IN_EMPTY; INT_LE_REFL; sptree_eq_list_def; lookup_def;
                option_DISTINCT] THEN
    CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THENL
     [REMOVE_THEN "pb" (MP_TAC o SPEC `i:num`); REMOVE_THEN "pe" (MP_TAC o SPEC `i:num`)] THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:linear_scan_hidden_state` (CONJUNCTS_THEN2 (LABEL_TAC "q1")
    (CONJUNCTS_THEN2 (LABEL_TAC "sb1") (CONJUNCTS_THEN2 (LABEL_TAC "se1")
    (CONJUNCTS_THEN2 (LABEL_TAC "lb1") (CONJUNCTS_THEN2 (LABEL_TAC "le1")
    (CONJUNCTS_THEN2 (LABEL_TAC "lvb1") (CONJUNCTS_THEN2 (LABEL_TAC "r1")
      (LABEL_TAC "n1le"))))))))) THEN
  REWRITE_TAC(get_intervals_ct_monad_def :: RAPROOFAUX_msimps) THEN
  USE_THEN "q1" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"; pair_CASE]) THEN
  MP_TAC(SPECL [`b1:int spt`; `s1:linear_scan_hidden_state`; `MAP FST (toAList (lv1:1 spt))`;
    `n1:int`] numset_list_add_if_lt_monad_correct) THEN
  ANTS_TAC THENL
   [USE_THEN "n1le" (fun a -> USE_THEN "sb1" (fun b -> REWRITE_TAC[a; b])) THEN
    USE_THEN "lb1" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM ALL_MEM; GSYM IN_SET_OF_LIST; set_MAP_FST_toAList_eq_domain] THEN
    USE_THEN "lvb1" ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:linear_scan_hidden_state` (CONJUNCTS_THEN2 (LABEL_TAC "q2")
    (CONJUNCTS_THEN2 (LABEL_TAC "sb2") (CONJUNCTS_THEN2 (LABEL_TAC "r2") (LABEL_TAC "l2"))))) THEN
  USE_THEN "q2" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
  USE_THEN "r2" (fun th -> LABEL_TAC "e2" (REWRITE_RULE(K_THM :: LSCANPAUX_hs_record)
    (AP_TERM `linear_scan_hidden_state_int_end` th))) THEN
  MP_TAC(SPECL [`e1:int spt`; `s2:linear_scan_hidden_state`; `MAP FST (toAList (lv1:1 spt))`;
    `n1:int`] numset_list_add_if_gt_monad_correct) THEN
  ANTS_TAC THENL
   [USE_THEN "e2" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "n1le" (fun a -> USE_THEN "se1" (fun b -> REWRITE_TAC[a; b])) THEN
    USE_THEN "le1" (fun a -> USE_THEN "len" (fun b -> REWRITE_TAC[a; b])) THEN
    REWRITE_TAC[GSYM ALL_MEM; GSYM IN_SET_OF_LIST; set_MAP_FST_toAList_eq_domain] THEN
    USE_THEN "lvb1" ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s3:linear_scan_hidden_state` (CONJUNCTS_THEN2 (LABEL_TAC "q3")
    (CONJUNCTS_THEN2 (LABEL_TAC "se3") (CONJUNCTS_THEN2 (LABEL_TAC "r3") (LABEL_TAC "l3"))))) THEN
  USE_THEN "q3" (fun th -> REWRITE_TAC[th; case_def "prod"; case_def "exc"]) THEN
  USE_THEN "r3" (fun th -> LABEL_TAC "b3" (REWRITE_RULE(K_THM :: LSCANPAUX_hs_record)
    (AP_TERM `linear_scan_hidden_state_int_beg` th))) THEN
  EXISTS_TAC `s3:linear_scan_hidden_state` THEN REWRITE_TAC RAPROOFAUX_msimps THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "b3" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "sb2" ACCEPT_TAC;
    USE_THEN "se3" ACCEPT_TAC;
    USE_THEN "b3" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "l2" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "lb1" ACCEPT_TAC;
    USE_THEN "l3" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "e2" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "le1" ACCEPT_TAC;
    MATCH_MP_TAC LSCANPAUX_hs2_trans THEN EXISTS_TAC `s1:linear_scan_hidden_state` THEN
    CONJ_TAC THENL [USE_THEN "r1" ACCEPT_TAC; ALL_TAC] THEN
    USE_THEN "r3" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    USE_THEN "r2" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[linear_scan_hidden_state_component_equality] THEN
    REWRITE_TAC(K_THM :: o_THM :: LSCANPAUX_hs_record) THEN
    USE_THEN "b3" (fun th -> REWRITE_TAC[th])]);;


(* HOL4 line 5386 *)
let in_clash_tree_eq_live_tree_registers = prove
 (`!ct r. in_clash_tree ct r <=> r IN live_tree_registers (get_live_tree ct)`,
    MATCH_MP_TAC clash_tree_INDUCT THEN
  REWRITE_TAC[in_clash_tree_def; get_live_tree_def; LET_DEF; LET_END_DEF;
              live_tree_registers_def; IN_UNION] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_SET_OF_LIST] THEN MESON_TAC[];
    REWRITE_TAC[set_MAP_FST_toAList_eq_domain];
    REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
    DISJ_CASES_THEN2 (X_CHOOSE_THEN `cs:1 spt` SUBST1_TAC) SUBST1_TAC
      (ISPEC `a0:(1 spt)option` option_CASES) THEN
    ASM_REWRITE_TAC[case_def "option"; live_tree_registers_def; IN_UNION;
                    set_MAP_FST_toAList_eq_domain] THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 5400 *)
let get_live_backward_in_live_tree_registers = prove
 (`!lt live.
     domain (get_live_backward lt live) SUBSET domain live UNION live_tree_registers lt`,
    MATCH_MP_TAC live_tree_INDUCT THEN
  REWRITE_TAC[get_live_backward_def; live_tree_registers_def; LET_DEF; LET_END_DEF;
              linear_scanProof_domain_numset_list_delete;
              linear_scanProof_domain_numset_list_insert; branch_domain] THEN
  REPEAT CONJ_TAC THENL
   [SET_TAC[];
    SET_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `live:1 spt` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `live:1 spt`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `live:1 spt`) THEN SET_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `live:1 spt` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `live:1 spt`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `get_live_backward a1 live`) THEN SET_TAC[]]);;

(* HOL4 line 5409 *)
let fix_domination_live_tree_registers = prove
 (`!lt. live_tree_registers (fix_domination lt) = live_tree_registers lt`,
    GEN_TAC THEN REWRITE_TAC[fix_domination_def; LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[live_tree_registers_def; set_MAP_FST_toAList_eq_domain] THEN
  MP_TAC(SPECL [`lt:live_tree`; `LN:1 spt`] get_live_backward_in_live_tree_registers) THEN
  REWRITE_TAC[domain_def; UNION_EMPTY] THEN SET_TAC[]);;

(* HOL4 line 5419 *)
let get_intervals_beg_less_end = prove
 (`!lt n_in beg_in end_in n_out beg_out end_out.
     (!r. r IN domain beg_in ==> misc_the (&0) (lookup r beg_in) <= misc_the (&0) (lookup r end_in)) /\
     domain beg_in SUBSET domain end_in /\
     (n_out,beg_out,end_out) = get_intervals lt n_in beg_in end_in ==>
     (!r. r IN domain beg_out ==>
          misc_the (&0) (lookup r beg_out) <= misc_the (&0) (lookup r end_out)) /\
     domain beg_out SUBSET domain end_out`,
    MATCH_MP_TAC live_tree_INDUCT THEN REWRITE_TAC[get_intervals_def; PAIR_EQ] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `l:num list` THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "le") (CONJUNCTS_THEN2 (LABEL_TAC "sub")
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)))) THEN
    REWRITE_TAC[domain_numset_list_add_if_lt; domain_numset_list_add_if_gt] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `r:num` THEN REWRITE_TAC[IN_UNION; IN_SET_OF_LIST] THEN DISCH_TAC THEN
      REWRITE_TAC[lookup_numset_list_add_if_lt; lookup_numset_list_add_if_gt] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THENL
       [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `n_in:int` THEN CONJ_TAC THENL
         [CASES_ON `lookup r (beg_in:int spt)` THEN
          REWRITE_TAC[case_def "option"] THEN TRY COND_CASES_TAC THEN
          REWRITE_TAC[misc_the_def] THEN ASM_INT_ARITH_TAC;
          CASES_ON `lookup r (end_in:int spt)` THEN
          REWRITE_TAC[case_def "option"] THEN TRY COND_CASES_TAC THEN
          REWRITE_TAC[misc_the_def] THEN ASM_INT_ARITH_TAC];
        USE_THEN "le" MATCH_MP_TAC THEN ASM_MESON_TAC[]];
      USE_THEN "sub" MP_TAC THEN SET_TAC[]];
    X_GEN_TAC `l:num list` THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "le") (CONJUNCTS_THEN2 (LABEL_TAC "sub")
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)))) THEN
    REWRITE_TAC[domain_numset_list_add_if_gt] THEN CONJ_TAC THENL
     [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `r IN domain (end_in:int spt)` MP_TAC THENL
       [USE_THEN "sub" MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[domain_lookup] THEN DISCH_THEN(X_CHOOSE_TAC `ve:int`) THEN
      REMOVE_THEN "le" (MP_TAC o SPEC `r:num`) THEN
      ASM_REWRITE_TAC[lookup_numset_list_add_if_gt; case_def "option"; misc_the_def] THEN
      ASM_CASES_TAC `MEM (r:num) l` THEN ASM_REWRITE_TAC[misc_the_def] THEN
      ASM_CASES_TAC `ve <= n_in:int` THEN ASM_REWRITE_TAC[misc_the_def] THEN
      POP_ASSUM MP_TAC THEN INT_ARITH_TAC;
      USE_THEN "sub" MP_TAC THEN SET_TAC[]];
    MAP_EVERY X_GEN_TAC [`lt1:live_tree`; `lt2:live_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN REPEAT GEN_TAC THEN
    MP_TAC(ISPEC `get_intervals lt2 n_in beg_in end_in` BASICAUX_TUPLE3) THEN
    DISCH_THEN(X_CHOOSE_THEN `n2:int` (X_CHOOSE_THEN `b2:int spt` (X_CHOOSE_THEN `e2:int spt`
      (LABEL_TAC "a2")))) THEN
    USE_THEN "a2" (fun th -> REWRITE_TAC[th; LET_DEF; LET_END_DEF; pair_CASE]) THEN
    STRIP_TAC THEN USE_THEN "ih1" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`n2:int`; `b2:int spt`; `e2:int spt`; `n_out:int`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "ih2" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`n_in:int`; `beg_in:int spt`; `end_in:int spt`; `n2:int`] THEN
    ASM_REWRITE_TAC[]]);;


(* HOL4 line 5471 *)
let linear_reg_alloc_without_renaming_correct = prove
 (CASE_TERM
  `!sth reglist_unsorted k moves ct forced.
     (!i. i < LENGTH (linear_scan_hidden_state_int_beg sth) ==>
          &0 < EL i (linear_scan_hidden_state_int_beg sth)) /\
     (!i. i < LENGTH (linear_scan_hidden_state_int_end sth) ==>
          &0 < EL i (linear_scan_hidden_state_int_end sth)) /\
     LENGTH (linear_scan_hidden_state_int_end sth) =
       LENGTH (linear_scan_hidden_state_int_beg sth) /\
     (!r. MEM r reglist_unsorted <=> in_clash_tree ct r) /\
     (!r. in_clash_tree ct r ==> r < LENGTH (linear_scan_hidden_state_int_beg sth)) /\
     ALL (\r12. match r12 with (r1,r2) -> in_clash_tree ct r1 /\ in_clash_tree ct r2)
         forced /\
     ALL (\r12. match r12 with
                  (r1,r2) -> r1 < LENGTH (linear_scan_hidden_state_colors sth) /\
                             r2 < LENGTH (linear_scan_hidden_state_colors sth))
         (MAP SND moves) /\
     LENGTH reglist_unsorted <= LENGTH (linear_scan_hidden_state_sorted_regs sth) /\
     LENGTH moves <= LENGTH (linear_scan_hidden_state_sorted_moves sth) /\
     LENGTH (linear_scan_hidden_state_colors sth) =
       LENGTH (linear_scan_hidden_state_int_beg sth) /\
     LENGTH (linear_scan_hidden_state_int_end sth) =
       LENGTH (linear_scan_hidden_state_int_beg sth) /\
     ALL_DISTINCT reglist_unsorted
     ==> ?sthout livein flivein.
           st_ex_ignore_bind (get_intervals_ct_monad ct)
             (linear_reg_alloc_intervals k forced moves reglist_unsorted) sth =
             (M_success one,sthout) /\
           check_clash_tree (\r. EL r (linear_scan_hidden_state_colors sthout)) ct LN LN =
             SOME (livein,flivein) /\
           (!r. in_clash_tree ct r ==>
                (if is_phy_var r then EL r (linear_scan_hidden_state_colors sthout) = r DIV 2
                 else if is_stack_var r
                 then k <= EL r (linear_scan_hidden_state_colors sthout)
                 else T)) /\
           ALL (\r12. match r12 with
                        (r1,r2) -> EL r1 (linear_scan_hidden_state_colors sthout) =
                                   EL r2 (linear_scan_hidden_state_colors sthout) ==>
                                   r1 = r2)
               forced /\
           LENGTH (linear_scan_hidden_state_colors sthout) =
             LENGTH (linear_scan_hidden_state_colors sth)`,
    REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pb") (CONJUNCTS_THEN2 (LABEL_TAC "pe")
    (CONJUNCTS_THEN2 (LABEL_TAC "leb") (CONJUNCTS_THEN2 (LABEL_TAC "memR")
    (CONJUNCTS_THEN2 (LABEL_TAC "ctb") (CONJUNCTS_THEN2 (LABEL_TAC "fct")
    (CONJUNCTS_THEN2 (LABEL_TAC "mvlt") (CONJUNCTS_THEN2 (LABEL_TAC "lsr")
    (CONJUNCTS_THEN2 (LABEL_TAC "lsm") (CONJUNCTS_THEN2 (LABEL_TAC "lcb")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "Rd")))))))))))) THEN
  MP_TAC(ISPEC `get_intervals_ct ct` BASICAUX_TUPLE3) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:int` (X_CHOOSE_THEN `ib:int spt` (X_CHOOSE_THEN `ie:int spt`
    (LABEL_TAC "gi")))) THEN
  MP_TAC(SPECL [`ct:clash_tree`; `sth:linear_scan_hidden_state`; `n:int`; `ib:int spt`;
    `ie:int spt`] get_intervals_ct_monad_correct) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `si:linear_scan_hidden_state` (CONJUNCTS_THEN2 (LABEL_TAC "qi")
    (CONJUNCTS_THEN2 (LABEL_TAC "sbi") (CONJUNCTS_THEN2 (LABEL_TAC "sei")
    (CONJUNCTS_THEN2 (LABEL_TAC "lbi") (CONJUNCTS_THEN2 (LABEL_TAC "lei")
      (LABEL_TAC "ri"))))))) THEN
  SUBGOAL_THEN
   `linear_scan_hidden_state_colors si = linear_scan_hidden_state_colors sth /\
    linear_scan_hidden_state_sorted_regs si = linear_scan_hidden_state_sorted_regs sth /\
    linear_scan_hidden_state_sorted_moves si = linear_scan_hidden_state_sorted_moves sth`
    (CONJUNCTS_THEN2 (LABEL_TAC "ci") (CONJUNCTS_THEN2 (LABEL_TAC "sri") (LABEL_TAC "smi")))
  THENL
   [USE_THEN "ri" (fun th -> ONCE_REWRITE_TAC[th]) THEN
    REWRITE_TAC(K_THM :: LSCANPAUX_hs_record);
    ALL_TAC] THEN
  MP_TAC(ISPEC `get_intervals (fix_domination (get_live_tree ct)) (&0) LN LN`
    BASICAUX_TUPLE3) THEN
  DISCH_THEN(X_CHOOSE_THEN `n':int` (X_CHOOSE_THEN `ib':int spt` (X_CHOOSE_THEN `ie':int spt`
    (LABEL_TAC "gi'")))) THEN
  MP_TAC(SPECL [`ct:clash_tree`; `ib:int spt`; `ib':int spt`; `ie:int spt`; `ie':int spt`;
    `n:int`; `n':int`] get_intervals_ct_eq) THEN
  USE_THEN "gi" (fun a -> USE_THEN "gi'" (fun b -> REWRITE_TAC[a; b])) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lkb") (LABEL_TAC "lke")) THEN
  MP_TAC(SPECL [`fix_domination (get_live_tree ct)`; `&0:int`; `LN:int spt`; `LN:int spt`;
    `n':int`; `ib':int spt`; `ie':int spt`] get_intervals_beg_less_end) THEN
  USE_THEN "gi'" (fun th -> REWRITE_TAC[th; domain_def; NOT_IN_EMPTY; EMPTY_SUBSET]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ble") (K ALL_TAC)) THEN
  MP_TAC(SPECL [`get_live_tree ct`; `n':int`; `ib':int spt`; `ie':int spt`]
    get_intervals_domain_eq_live_tree_registers) THEN
  USE_THEN "gi'" (fun th -> REWRITE_TAC[th; fix_domination_live_tree_registers]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "db") (LABEL_TAC "de")) THEN
  SUBGOAL_THEN `!r. r IN domain (ib':int spt) <=> in_clash_tree ct r` (LABEL_TAC "dib") THENL
   [USE_THEN "db" (fun th -> REWRITE_TAC[th; GSYM in_clash_tree_eq_live_tree_registers]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN domain (ie':int spt) <=> in_clash_tree ct r` (LABEL_TAC "die") THENL
   [USE_THEN "de" (fun th -> REWRITE_TAC[th; GSYM in_clash_tree_eq_live_tree_registers]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. in_clash_tree ct r ==>
        lookup r (ib':int spt) = SOME (EL r (linear_scan_hidden_state_int_beg si)) /\
        lookup r (ie':int spt) = SOME (EL r (linear_scan_hidden_state_int_end si))`
    (LABEL_TAC "lk") THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `r < LENGTH (linear_scan_hidden_state_int_beg si) /\
                  r < LENGTH (linear_scan_hidden_state_int_end si)` STRIP_ASSUME_TAC THENL
     [USE_THEN "lbi" (fun a -> USE_THEN "lei" (fun b -> USE_THEN "leb" (fun c ->
        REWRITE_TAC[a; b; c]))) THEN
      USE_THEN "ctb" (fun th -> ASM_SIMP_TAC[th]);
      ALL_TAC] THEN
    USE_THEN "sbi" (MP_TAC o SPEC `r:num` o REWRITE_RULE[sptree_eq_list_def]) THEN
    USE_THEN "sei" (MP_TAC o SPEC `r:num` o REWRITE_RULE[sptree_eq_list_def]) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "lkb" (fun a -> USE_THEN "lke" (fun b -> REWRITE_TAC[a; b])) THEN
    SUBGOAL_THEN `~(lookup r (ib':int spt) = NONE) /\ ~(lookup r (ie':int spt) = NONE)`
      MP_TAC THENL
     [REWRITE_TAC[lookup_NONE_domain] THEN
      USE_THEN "dib" (fun a -> USE_THEN "die" (fun b -> REWRITE_TAC[a; b])) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM INT_NOT_LT] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `forced:(num#num)list`; `moves:(num#num#num)list`;
    `reglist_unsorted:num list`; `si:linear_scan_hidden_state`]
    linear_reg_alloc_intervals_correct) THEN
  USE_THEN "ci" (fun a -> USE_THEN "sri" (fun b -> USE_THEN "smi" (fun c ->
    REWRITE_TAC[a; b; c]))) THEN
  USE_THEN "lbi" (fun a -> USE_THEN "lei" (fun b -> REWRITE_TAC[a; b])) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "fct" MP_TAC THEN
      REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE] THEN ASM_MESON_TAC[];
      USE_THEN "mvlt" ACCEPT_TAC;
      REWRITE_TAC[GSYM ALL_MEM] THEN USE_THEN "lcb" (fun th -> REWRITE_TAC[th]) THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `r:num` THEN
      USE_THEN "memR" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
      REMOVE_THEN "ble" (MP_TAC o SPEC `r:num`) THEN
      USE_THEN "dib" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "lk" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `in_clash_tree ct r`)]) THEN
      ASM_REWRITE_TAC[misc_the_def];
      USE_THEN "Rd" ACCEPT_TAC;
      REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
      USE_THEN "lcb" ACCEPT_TAC;
      USE_THEN "leb" ACCEPT_TAC;
      USE_THEN "lsr" ACCEPT_TAC;
      USE_THEN "lsm" ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `so:linear_scan_hidden_state` (CONJUNCTS_THEN2 (LABEL_TAC "qo")
    (CONJUNCTS_THEN2 (LABEL_TAC "into") (CONJUNCTS_THEN2 (LABEL_TAC "colo")
    (CONJUNCTS_THEN2 (LABEL_TAC "fo") (LABEL_TAC "leno")))))) THEN
  MP_TAC(SPECL [`get_live_tree ct`; `n':int`; `ib':int spt`; `ie':int spt`;
    `\r. EL r (linear_scan_hidden_state_colors so)`] check_intervals_check_live_tree) THEN
  USE_THEN "gi'" (fun th -> REWRITE_TAC[th]) THEN ANTS_TAC THENL
   [REWRITE_TAC[check_intervals_def] THEN MAP_EVERY X_GEN_TAC [`r1:num`; `r2:num`] THEN
    USE_THEN "dib" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    USE_THEN "into" MATCH_MP_TAC THEN
    USE_THEN "memR" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `interval_intersect (THE (lookup r1 (ib':int spt)),THE (lookup r1 (ie':int spt)))
                   (THE (lookup r2 ib'),THE (lookup r2 ie'))` THEN
    USE_THEN "lk" (fun th -> ASM_SIMP_TAC[th; THE_DEF]);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lo:1 spt` (X_CHOOSE_THEN `flo:1 spt`
    (MP_TAC o MATCH_MP fix_domination_check_live_tree))) THEN
  DISCH_THEN(X_CHOOSE_THEN `lo':1 spt` (X_CHOOSE_THEN `flo':1 spt`
    (MP_TAC o MATCH_MP get_live_tree_correct_LN))) THEN
  DISCH_THEN(X_CHOOSE_THEN `livein:1 spt` (X_CHOOSE_THEN `flivein:1 spt` ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`so:linear_scan_hidden_state`; `livein:1 spt`; `flivein:1 spt`] THEN
  USE_THEN "qi" (fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_ignore_bind_ok th]) THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  USE_THEN "colo" (MP_TAC o SPEC `r:num` o REWRITE_RULE[GSYM ALL_MEM]) THEN
  USE_THEN "memR" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]);;


(* LSCANPAUX_domain_foldi_insert: the keys of a foldi-built set (used at   *)
(* HOL4 lines 5565 and 5676, where the fact is proved inline)              *)
let LSCANPAUX_domain_foldi_insert = prove
 (`!(s:A spt) (g:num->num).
     domain (foldi (\r (v:A) acc. insert (g r) one acc) 0 LN s) = IMAGE g (domain s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[foldi_FOLDR_toAList] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM set_MAP_FST_toAList_eq_domain] THEN
  SPEC_TAC(`toAList (s:A spt)`, `l:(num#A)list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; MAP; set_of_list; IMAGE_CLAUSES; domain_def] THEN
  MP_TAC(ISPEC `h:num#A` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `b:A` SUBST1_TAC)) THEN
  ASM_REWRITE_TAC[UNCURRY_DEF; FST; domain_insert]);;

(* HOL4 line 5565 *)
let check_col_apply_bijection = prove
 (`!bijdom bijcodom appbij appinvbij (cutset:1 spt) livein flivein f.
     (!r. r IN bijdom ==> appbij r IN bijcodom /\ appinvbij (appbij r) = r) /\
     (!r. r IN bijcodom ==> appinvbij r IN bijdom /\ appbij (appinvbij r) = r) /\
     domain cutset SUBSET bijdom /\
     check_col f (foldi (\r v acc. insert (appbij r) one acc) 0 LN cutset) =
       SOME (livein,flivein) ==>
     ?livein' flivein'.
       check_col (\r. f (appbij r)) cutset = SOME (livein',flivein') /\
       domain livein' = IMAGE appinvbij (domain livein)`,
    REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "b1") (CONJUNCTS_THEN2 (LABEL_TAC "b2")
    (CONJUNCTS_THEN2 (LABEL_TAC "sub") MP_TAC))) THEN
  MP_TAC(ISPECL [`cutset:1 spt`; `appbij:num->num`] LSCANPAUX_domain_foldi_insert) THEN
  SPEC_TAC(`foldi (\r (v:1) acc. insert ((appbij:num->num) r) one acc) 0 LN (cutset:1 spt)`,
           `tt:1 spt`) THEN
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "dt") THEN
  REWRITE_TAC[check_col_def; LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `ALL_DISTINCT (MAP ((f:num->num) o FST) (toAList (tt:1 spt)))` THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (K ALL_TAC)) THEN
  SUBGOAL_THEN `domain (cutset:1 spt) = IMAGE appinvbij (domain (tt:1 spt))` (LABEL_TAC "dc")
  THENL
   [USE_THEN "dt" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "sub" MP_TAC THEN USE_THEN "b1" MP_TAC THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (MAP ((\r. (f:num->num) (appbij r)) o FST)
                                  (toAList (cutset:1 spt)))`
    (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `ALL_DISTINCT (MAP ((f:num->num) o FST) (toAList (tt:1 spt)))` THEN
    REWRITE_TAC[MAP_o] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ALL_DISTINCT_INJ_MAP) THEN
    REWRITE_TAC[set_MAP_FST_toAList_eq_domain; INJ; IN_UNIV] THEN DISCH_THEN(LABEL_TAC "inj") THEN
    MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList] THEN
    REWRITE_TAC[GSYM IN_SET_OF_LIST; set_MAP_FST_toAList_eq_domain] THEN
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "xin") (CONJUNCTS_THEN2 (LABEL_TAC "yin")
      (LABEL_TAC "fxy"))) THEN
    SUBGOAL_THEN `(appbij:num->num) x = appbij y` ASSUME_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN
      USE_THEN "dt" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "fxy" (fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:num) IN bijdom /\ (y:num) IN bijdom` STRIP_ASSUME_TAC THENL
     [USE_THEN "sub" MP_TAC THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN(fun th -> CONJ_TAC THEN MATCH_MP_TAC th THEN FIRST_ASSUM ACCEPT_TAC);
      ALL_TAC] THEN
    USE_THEN "b1" (fun th -> MP_TAC(SPEC `x:num` th) THEN MP_TAC(SPEC `y:num` th)) THEN
    REWRITE_TAC[ASSUME `(x:num) IN bijdom`; ASSUME `(y:num) IN bijdom`] THEN
    UNDISCH_TAC `(appbij:num->num) x = appbij y` THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[option_INJ; PAIR_EQ] THEN USE_THEN "dc" MP_TAC THEN MESON_TAC[]);;

(* HOL4 line 5602 *)
let check_partial_col_apply_bijection = prove
 (`!bijdom bijcodom appbij appinvbij f l live flive live' flive' livein flivein.
     (!r. r IN bijdom ==> appbij r IN bijcodom /\ appinvbij (appbij r) = r) /\
     (!r. r IN bijcodom ==> appinvbij r IN bijdom /\ appbij (appinvbij r) = r) /\
     set_of_list l SUBSET bijdom /\
     domain live SUBSET bijcodom /\
     domain flive = IMAGE f (domain live) /\
     domain flive' = IMAGE (f o appbij) (domain live') /\
     domain live' = IMAGE appinvbij (domain live) /\
     INJ f (domain live) UNIV /\
     check_partial_col f (MAP appbij l) live flive = SOME (livein,flivein) ==>
     ?livein' flivein'.
       check_partial_col (\r. f (appbij r)) l live' flive' = SOME (livein',flivein') /\
       domain livein' = IMAGE appinvbij (domain livein)`,
    MAP_EVERY X_GEN_TAC [`bijdom:num->bool`; `bijcodom:num->bool`; `appbij:num->num`;
    `appinvbij:num->num`; `f:num->num`] THEN
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[MAP; check_partial_col_def; option_INJ; PAIR_EQ] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`live':1 spt`; `flive':1 spt`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`live:1 spt`; `flive:1 spt`; `live':1 spt`; `flive':1 spt`;
    `livein:1 spt`; `flivein:1 spt`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "b1") (CONJUNCTS_THEN2 (LABEL_TAC "b2")
    (CONJUNCTS_THEN2 (LABEL_TAC "sl") (CONJUNCTS_THEN2 (LABEL_TAC "slive")
    (CONJUNCTS_THEN2 (LABEL_TAC "dfl") (CONJUNCTS_THEN2 (LABEL_TAC "dfl'")
    (CONJUNCTS_THEN2 (LABEL_TAC "dl'") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
      (LABEL_TAC "cpc"))))))))) THEN
  SUBGOAL_THEN `(h:num) IN bijdom /\ set_of_list t SUBSET bijdom`
    (CONJUNCTS_THEN2 (LABEL_TAC "hb") (LABEL_TAC "tb")) THENL
   [USE_THEN "sl" MP_TAC THEN REWRITE_TAC[set_of_list; INSERT_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:num) IN domain (live':1 spt) <=> (appbij:num->num) h IN domain (live:1 spt)`
    (LABEL_TAC "hl") THENL
   [USE_THEN "dl'" (fun th -> REWRITE_TAC[th; IN_IMAGE]) THEN
    USE_THEN "slive" MP_TAC THEN USE_THEN "b1" MP_TAC THEN USE_THEN "b2" MP_TAC THEN
    USE_THEN "hb" MP_TAC THEN REWRITE_TAC[SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `domain (flive':1 spt) = domain (flive:1 spt)` (LABEL_TAC "dff") THENL
   [USE_THEN "dfl'" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "dl'" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "dfl" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; o_THM] THEN
    USE_THEN "slive" MP_TAC THEN USE_THEN "b2" MP_TAC THEN REWRITE_TAC[SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "cpc" MP_TAC THEN REWRITE_TAC[MAP; check_partial_col_def] THEN
  ASM_CASES_TAC `(appbij:num->num) h IN domain (live:1 spt)` THENL
   [(* the register is already live *)
    SUBGOAL_THEN `(h:num) IN domain (live':1 spt)` MP_TAC THENL
     [USE_THEN "hl" (fun th -> REWRITE_TAC[th]) THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[domain_lookup] THEN DISCH_THEN(X_CHOOSE_THEN `b:1` (LABEL_TAC "lb")) THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[domain_lookup] o check (fun th ->
      concl th = `(appbij:num->num) h IN domain (live:1 spt)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:1` (fun th -> REWRITE_TAC[th; case_def "option"])) THEN
    DISCH_TAC THEN USE_THEN "lb" (fun th -> REWRITE_TAC[th; case_def "option"]) THEN
    REMOVE_THEN "ih" (MP_TAC o SPECL [`live:1 spt`; `flive:1 spt`; `live':1 spt`;
      `flive':1 spt`; `livein:1 spt`; `flivein:1 spt`]) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `li:1 spt` (X_CHOOSE_THEN `fli:1 spt` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`li:1 spt`; `fli:1 spt`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the register is not live *)
  SUBGOAL_THEN `lookup ((appbij:num->num) h) (live:1 spt) = NONE /\
                lookup (h:num) (live':1 spt) = NONE` (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th]))
  THENL
   [REWRITE_TAC[lookup_NONE_domain] THEN USE_THEN "hl" (fun th -> REWRITE_TAC[th]) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[case_def "option"] THEN
  ASM_CASES_TAC `(f:num->num) ((appbij:num->num) h) IN domain (flive:1 spt)` THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[domain_lookup] o check (fun th ->
      concl th = `(f:num->num) ((appbij:num->num) h) IN domain (flive:1 spt)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:1` (fun th -> REWRITE_TAC[th; case_def "option"])) THEN
    REWRITE_TAC[option_DISTINCT];
    ALL_TAC] THEN
  SUBGOAL_THEN `lookup ((f:num->num) ((appbij:num->num) h)) (flive:1 spt) = NONE /\
                lookup ((f:num->num) ((appbij:num->num) h)) (flive':1 spt) = NONE`
    (CONJUNCTS_THEN (fun th -> REWRITE_TAC[th]))
  THENL
   [REWRITE_TAC[lookup_NONE_domain] THEN USE_THEN "dff" (fun th -> REWRITE_TAC[th]) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[case_def "option"] THEN DISCH_TAC THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`insert ((appbij:num->num) h) one (live:1 spt)`;
    `insert ((f:num->num) ((appbij:num->num) h)) one (flive:1 spt)`; `insert (h:num) one (live':1 spt)`;
    `insert ((f:num->num) ((appbij:num->num) h)) one (flive':1 spt)`; `livein:1 spt`; `flivein:1 spt`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[domain_insert] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "b1" ACCEPT_TAC;
      USE_THEN "b2" ACCEPT_TAC;
      USE_THEN "tb" ACCEPT_TAC;
      REWRITE_TAC[INSERT_SUBSET] THEN CONJ_TAC THENL
       [USE_THEN "b1" (MP_TAC o SPEC `h:num`) THEN USE_THEN "hb" (fun th -> SIMP_TAC[th]);
        USE_THEN "slive" ACCEPT_TAC];
      USE_THEN "dfl" (fun th -> REWRITE_TAC[th; IMAGE_CLAUSES]);
      USE_THEN "dfl'" (fun th -> REWRITE_TAC[th; IMAGE_CLAUSES; o_THM]);
      USE_THEN "dl'" (fun th -> REWRITE_TAC[th; IMAGE_CLAUSES]) THEN
      USE_THEN "b1" (MP_TAC o SPEC `h:num`) THEN USE_THEN "hb" (fun th -> SIMP_TAC[th]);
      REWRITE_TAC[INJ_INSERT; IN_UNIV] THEN USE_THEN "inj" (fun th -> REWRITE_TAC[th]) THEN
      X_GEN_TAC `y:num` THEN STRIP_TAC THEN
      UNDISCH_TAC `~((f:num->num) ((appbij:num->num) h) IN domain (flive:1 spt))` THEN
      USE_THEN "dfl" (fun th -> REWRITE_TAC[th; IN_IMAGE]) THEN ASM_MESON_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `li:1 spt` (X_CHOOSE_THEN `fli:1 spt` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`li:1 spt`; `fli:1 spt`] THEN ASM_REWRITE_TAC[]);;

(* HOL4 line 5647 *)
let check_clash_tree_output_subset = prove
 (`!f ct live flive livein flivein.
     check_clash_tree f ct live flive = SOME (livein,flivein) ==>
     domain livein SUBSET domain live UNION in_clash_tree ct`,
    GEN_TAC THEN MATCH_MP_TAC clash_tree_INDUCT THEN REPEAT CONJ_TAC THENL
   [(* Delta *)
    MAP_EVERY X_GEN_TAC [`w:num list`; `r:num list`] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[LSCANPAUX_check_clash_tree_SOME; in_clash_tree_set_eq] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (MP_TAC o MATCH_MP check_partial_col_domain)) THEN
    REWRITE_TAC[FST; linear_scanProof_domain_numset_list_delete] THEN SET_TAC[];
    (* Set *)
    X_GEN_TAC `t:1 spt` THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[LSCANPAUX_check_clash_tree_SOME; in_clash_tree_set_eq; check_col_def;
                LET_DEF; LET_END_DEF] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    (* Branch *)
    X_GEN_TAC `topt:(1 spt)option` THEN MAP_EVERY X_GEN_TAC [`t1:clash_tree`; `t2:clash_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN REPEAT GEN_TAC THEN
    DISJ_CASES_THEN2 (X_CHOOSE_THEN `t:1 spt` SUBST1_TAC) SUBST1_TAC
      (ISPEC `topt:(1 spt)option` option_CASES) THEN
    REWRITE_TAC[LSCANPAUX_check_clash_tree_SOME; in_clash_tree_set_eq; case_def "option"] THENL
     [REWRITE_TAC[check_col_def; LET_DEF; LET_END_DEF] THEN
      DISCH_THEN(X_CHOOSE_THEN `t1_out:1 spt` (X_CHOOSE_THEN `ft1_out:1 spt`
        (X_CHOOSE_THEN `t2_out:1 spt` (X_CHOOSE_THEN `ft2_out:1 spt`
        (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC)))))) THEN
      COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `t1_out:1 spt` (X_CHOOSE_THEN `ft1_out:1 spt`
        (X_CHOOSE_THEN `t2_out:1 spt` (X_CHOOSE_THEN `ft2_out:1 spt`
        (CONJUNCTS_THEN2 (fun th -> USE_THEN "ih1" (MP_TAC o C MATCH_MP th))
          (CONJUNCTS_THEN2 (fun th -> USE_THEN "ih2" (MP_TAC o C MATCH_MP th))
            (MP_TAC o MATCH_MP check_partial_col_branch_domain))))))) THEN
      SET_TAC[]];
    (* Seq *)
    MAP_EVERY X_GEN_TAC [`t1:clash_tree`; `t2:clash_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[LSCANPAUX_check_clash_tree_SOME; in_clash_tree_set_eq] THEN
    DISCH_THEN(X_CHOOSE_THEN `t2_out:1 spt` (X_CHOOSE_THEN `ft2_out:1 spt`
      (CONJUNCTS_THEN2 (fun th -> USE_THEN "ih2" (MP_TAC o C MATCH_MP th))
         (fun th -> USE_THEN "ih1" (MP_TAC o C MATCH_MP th))))) THEN
    SET_TAC[]]);;

(* HOL4 line 5676 *)
let domain_apply_bij_set = prove
 (`!(s:A spt) bij.
     domain (foldi (\r v acc. insert (misc_the 0 (lookup r bij)) one acc) 0 LN s) =
     IMAGE (\r. misc_the 0 (lookup r bij)) (domain s)`,
    REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`s:A spt`; `\r. misc_the 0 (lookup r (bij:num spt))`]
    LSCANPAUX_domain_foldi_insert) THEN
  BETA_TAC THEN DISCH_THEN ACCEPT_TAC);;

(* HOL4 line 5692 *)
let in_clash_tree_apply_bij = prove
 (`!bij ct.
     in_clash_tree ct SUBSET domain bij ==>
     in_clash_tree (apply_bij_on_clash_tree ct bij) =
     IMAGE (\r. misc_the 0 (lookup r bij)) (in_clash_tree ct)`,
    GEN_TAC THEN MATCH_MP_TAC clash_tree_INDUCT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[apply_bij_on_clash_tree_def; in_clash_tree_set_eq; SET_OF_LIST_MAP;
                IMAGE_UNION];
    REWRITE_TAC[apply_bij_on_clash_tree_def; in_clash_tree_set_eq; domain_apply_bij_set];
    X_GEN_TAC `topt:(1 spt)option` THEN MAP_EVERY X_GEN_TAC [`t1:clash_tree`; `t2:clash_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    DISJ_CASES_THEN2 (X_CHOOSE_THEN `s:1 spt` SUBST1_TAC) SUBST1_TAC
      (ISPEC `topt:(1 spt)option` option_CASES) THEN
    REWRITE_TAC[apply_bij_on_clash_tree_def; in_clash_tree_set_eq; OPTION_MAP_DEF;
                case_def "option"; domain_apply_bij_set; IMAGE_UNION; UNION_SUBSET] THEN
    STRIP_TAC THEN
    USE_THEN "ih1" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `in_clash_tree t1 SUBSET domain (bij:num spt)`)]) THEN
    USE_THEN "ih2" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `in_clash_tree t2 SUBSET domain (bij:num spt)`)]);
    MAP_EVERY X_GEN_TAC [`t1:clash_tree`; `t2:clash_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    REWRITE_TAC[apply_bij_on_clash_tree_def; in_clash_tree_set_eq; IMAGE_UNION;
                UNION_SUBSET] THEN
    STRIP_TAC THEN
    USE_THEN "ih1" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `in_clash_tree t1 SUBSET domain (bij:num spt)`)]) THEN
    USE_THEN "ih2" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `in_clash_tree t2 SUBSET domain (bij:num spt)`)])]);;


(* LSCANPAUX_sp_inverts_app: an sptree inverse gives a left inverse on the *)
(* domain (proved inline at HOL4 line 5730)                                *)
let LSCANPAUX_sp_inverts_app = prove
 (`!bij invbij.
     sp_inverts bij invbij ==>
     !r. r IN domain bij ==>
         misc_the 0 (lookup r bij) IN domain invbij /\
         misc_the 0 (lookup (misc_the 0 (lookup r bij)) invbij) = r`,
  REWRITE_TAC[sp_inverts_def; domain_lookup] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `r:num` THEN DISCH_THEN(X_CHOOSE_TAC `v:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`r:num`; `v:num`]) THEN ASM_REWRITE_TAC[misc_the_def] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[misc_the_def; option_INJ] THEN MESON_TAC[]);;

(* LSCANPAUX_INJ_bij: the renamed colouring is injective on the renamed set *)
let LSCANPAUX_INJ_bij = prove
 (`!bijdom bijcodom appbij appinvbij (f:num->num) (live:1 spt) (live':1 spt).
     (!x. x IN bijcodom ==> appinvbij x IN bijdom /\ appbij (appinvbij x) = x) /\
     domain live SUBSET bijcodom /\ domain live' = IMAGE appinvbij (domain live) /\
     INJ f (domain live) UNIV ==>
     INJ (\x. f (appbij x)) (domain live') UNIV`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "b2") (CONJUNCTS_THEN2 (LABEL_TAC "sl")
    (CONJUNCTS_THEN2 (LABEL_TAC "dl") (LABEL_TAC "inj")))) THEN
  USE_THEN "dl" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[INJ; IN_UNIV; IN_IMAGE] THEN BETA_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:num` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
  SUBGOAL_THEN `(u:num) IN bijcodom /\ (v:num) IN bijcodom` STRIP_ASSUME_TAC THENL
   [USE_THEN "sl" (fun th -> CONJ_TAC THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] th) THEN
      FIRST_ASSUM ACCEPT_TAC);
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "b2" (fun th -> REWRITE_TAC[CONJUNCT2(MATCH_MP th (ASSUME `(u:num) IN bijcodom`));
                                       CONJUNCT2(MATCH_MP th (ASSUME `(v:num) IN bijcodom`))]) THEN
  DISCH_TAC THEN AP_TERM_TAC THEN
  USE_THEN "inj" (MATCH_MP_TAC o CONJUNCT2 o REWRITE_RULE[INJ]) THEN ASM_REWRITE_TAC[]);;

(* LSCANPAUX_cct_out_bij: the output live set of a renamed tree stays in   *)
(* the codomain of the bijection                                           *)
let LSCANPAUX_cct_out_bij = prove
 (`!bij invbij f ct (live:1 spt) flive livein flivein.
     sp_inverts bij invbij /\ in_clash_tree ct SUBSET domain bij /\
     domain live SUBSET domain invbij /\
     check_clash_tree f (apply_bij_on_clash_tree ct bij) live flive = SOME (livein,flivein) ==>
     domain livein SUBSET domain invbij`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP LSCANPAUX_sp_inverts_app)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o MATCH_MP check_clash_tree_output_subset)))) THEN
  ASM_SIMP_TAC[in_clash_tree_apply_bij] THEN
  UNDISCH_TAC `in_clash_tree ct SUBSET domain (bij:num spt)` THEN
  UNDISCH_TAC `domain (live:1 spt) SUBSET domain (invbij:num spt)` THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_IMAGE] THEN MESON_TAC[]);;

(* LSCANPAUX_cct_bij_delta: the Delta case of check_clash_tree_apply_     *)
(* bijection (HOL4 line 5745), for abstract bijections                     *)
let LSCANPAUX_cct_bij_delta = prove
 (`!bijdom bijcodom appbij appinvbij f wl rl (live:1 spt) flive live' flive' livein flivein.
     (!x. x IN bijdom ==> appbij x IN bijcodom /\ appinvbij (appbij x) = x) /\
     (!x. x IN bijcodom ==> appinvbij x IN bijdom /\ appbij (appinvbij x) = x) /\
     set_of_list wl SUBSET bijdom /\ set_of_list rl SUBSET bijdom /\
     domain live SUBSET bijcodom /\
     domain flive = IMAGE f (domain live) /\
     domain flive' = IMAGE (f o appbij) (domain live') /\
     domain live' = IMAGE appinvbij (domain live) /\
     INJ f (domain live) UNIV /\
     check_clash_tree f (Delta (MAP appbij wl) (MAP appbij rl)) live flive =
       SOME (livein,flivein) ==>
     ?livein' flivein'.
       check_clash_tree (\x. f (appbij x)) (Delta wl rl) live' flive' =
         SOME (livein',flivein') /\
       domain livein' = IMAGE appinvbij (domain livein)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "b1") (CONJUNCTS_THEN2 (LABEL_TAC "b2")
    (CONJUNCTS_THEN2 (LABEL_TAC "sw") (CONJUNCTS_THEN2 (LABEL_TAC "sr")
    (CONJUNCTS_THEN2 (LABEL_TAC "slive") (CONJUNCTS_THEN2 (LABEL_TAC "dfl")
    (CONJUNCTS_THEN2 (LABEL_TAC "dfl'") (CONJUNCTS_THEN2 (LABEL_TAC "dl'")
    (CONJUNCTS_THEN2 (LABEL_TAC "inj") MP_TAC))))))))) THEN
  REWRITE_TAC[LSCANPAUX_check_clash_tree_SOME] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `v:1 spt#1 spt`) (LABEL_TAC "c2")) THEN
  (* the written registers *)
  MP_TAC(ISPECL [`bijdom:num->bool`; `bijcodom:num->bool`; `appbij:num->num`;
    `appinvbij:num->num`; `f:num->num`; `wl:num list`; `live:1 spt`; `flive:1 spt`;
    `live':1 spt`; `flive':1 spt`; `FST (v:1 spt#1 spt)`; `SND (v:1 spt#1 spt)`]
    check_partial_col_apply_bijection) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[PAIR] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:1 spt` (X_CHOOSE_THEN `v2:1 spt`
    (CONJUNCTS_THEN2 (LABEL_TAC "c1'") (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`FST (v:1 spt#1 spt)`; `SND (v:1 spt#1 spt)`; `MAP (appbij:num->num) wl`;
    `live:1 spt`; `flive:1 spt`; `f:num->num`] check_partial_col_success_INJ_lemma) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[PAIR] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[SET_OF_LIST_MAP] THEN DISCH_THEN(LABEL_TAC "inj2")] THEN
  (* the read registers *)
  MP_TAC(ISPECL [`bijdom:num->bool`; `bijcodom:num->bool`; `appbij:num->num`;
    `appinvbij:num->num`; `f:num->num`; `rl:num list`;
    `numset_list_delete (MAP (appbij:num->num) wl) (live:1 spt)`;
    `numset_list_delete (MAP (f:num->num) (MAP (appbij:num->num) wl)) (flive:1 spt)`;
    `numset_list_delete (wl:num list) (live':1 spt)`;
    `numset_list_delete (MAP (\x. (f:num->num) ((appbij:num->num) x)) wl) (flive':1 spt)`;
    `livein:1 spt`; `flivein:1 spt`] check_partial_col_apply_bijection) THEN
  REWRITE_TAC[linear_scanProof_domain_numset_list_delete] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "b1" ACCEPT_TAC;
      USE_THEN "b2" ACCEPT_TAC;
      USE_THEN "sr" ACCEPT_TAC;
      USE_THEN "slive" MP_TAC THEN SET_TAC[];
      (* the colours of the remaining live registers *)
      USE_THEN "dfl" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[SET_OF_LIST_MAP] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC IMAGE_DIFF_INJ THEN
      USE_THEN "inj2" MP_TAC THEN REWRITE_TAC[INJ; IN_UNION] THEN MESON_TAC[];
      (* the same for the renamed registers *)
      REWRITE_TAC[SET_OF_LIST_MAP] THEN USE_THEN "dfl'" (fun th -> REWRITE_TAC[th; o_DEF]) THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC IMAGE_DIFF_INJ THEN BETA_TAC THEN
      MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
      USE_THEN "dl'" (fun th -> REWRITE_TAC[th; IN_IMAGE; IN_SET_OF_LIST]) THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:num` STRIP_ASSUME_TAC)
        (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `(u:num) IN bijcodom /\ (y:num) IN bijdom` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [USE_THEN "slive" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN FIRST_ASSUM ACCEPT_TAC;
          USE_THEN "sw" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
          ASM_REWRITE_TAC[IN_SET_OF_LIST]];
        ALL_TAC] THEN
      USE_THEN "b2" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(u:num) IN bijcodom`))) THEN
      USE_THEN "b1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:num) IN bijdom`))) THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(u:num) = (appbij:num->num) y` ASSUME_TAC THENL
       [USE_THEN "inj2" (MATCH_MP_TAC o CONJUNCT2 o REWRITE_RULE[INJ]) THEN
        REWRITE_TAC[IN_UNION; IN_IMAGE; IN_SET_OF_LIST] THEN REPEAT CONJ_TAC THENL
         [DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          DISJ1_TAC THEN EXISTS_TAC `y:num` THEN ASM_REWRITE_TAC[];
          UNDISCH_TAC `(f:num->num) (appbij (x:num)) = f (appbij y)` THEN
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`(x:num) = (appinvbij:num->num) u`; `(u:num) = (appbij:num->num) y`;
        `(appinvbij:num->num) (appbij (y:num)) = y`] THEN
      MESON_TAC[];
      (* the renamed live registers *)
      USE_THEN "dl'" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[EXTENSION; IN_DIFF; IN_IMAGE; IN_SET_OF_LIST; MEM_MAP] THEN
      X_GEN_TAC `z:num` THEN EQ_TAC THENL
       [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:num` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
        EXISTS_TAC `u:num` THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `y:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
        SUBGOAL_THEN `(y:num) IN bijdom` ASSUME_TAC THENL
         [USE_THEN "sw" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
          ASM_REWRITE_TAC[IN_SET_OF_LIST];
          ALL_TAC] THEN
        USE_THEN "b1" (fun th -> MP_TAC(CONJUNCT2(MATCH_MP th (ASSUME `(y:num) IN bijdom`)))) THEN
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
        UNDISCH_TAC `~MEM (z:num) wl` THEN ASM_REWRITE_TAC[];
        DISCH_THEN(X_CHOOSE_THEN `u:num` (CONJUNCTS_THEN2 SUBST1_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
        SUBGOAL_THEN `(u:num) IN bijcodom` ASSUME_TAC THENL
         [USE_THEN "slive" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN FIRST_ASSUM ACCEPT_TAC;
          ALL_TAC] THEN
        CONJ_TAC THENL
         [EXISTS_TAC `u:num` THEN ASM_REWRITE_TAC[];
          DISCH_TAC THEN
          UNDISCH_TAC `~(?x. MEM x wl /\ (u:num) = (appbij:num->num) x)` THEN REWRITE_TAC[] THEN
          EXISTS_TAC `(appinvbij:num->num) u` THEN ASM_REWRITE_TAC[] THEN
          USE_THEN "b2" (fun th -> REWRITE_TAC[CONJUNCT2(MATCH_MP th
            (ASSUME `(u:num) IN bijcodom`))])]];
      MATCH_MP_TAC reg_allocProof_INJ_less THEN EXISTS_TAC `domain (live:1 spt)` THEN
      USE_THEN "inj" (fun th -> REWRITE_TAC[th]) THEN SET_TAC[];
      USE_THEN "c2" ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `li:1 spt` (X_CHOOSE_THEN `fli:1 spt`
    (CONJUNCTS_THEN2 (LABEL_TAC "c2'") (LABEL_TAC "dli")))) THEN
  MAP_EVERY EXISTS_TAC [`li:1 spt`; `fli:1 spt`] THEN
  USE_THEN "dli" (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL
   [EXISTS_TAC `(v1:1 spt),(v2:1 spt)` THEN USE_THEN "c1'" ACCEPT_TAC;
    USE_THEN "c2'" ACCEPT_TAC]);;

(* LSCANPAUX_cct_bij_branch: the Branch case without a cut set of        *)
(* check_clash_tree_apply_bijection (HOL4 line 5785), for abstract       *)
(* bijections                                                            *)
let LSCANPAUX_cct_bij_branch = prove
 (`!bijdom bijcodom appbij appinvbij f (t1_out:1 spt) ft1_out (t2_out:1 spt) livein1 flivein1
    (livein2:1 spt) livein flivein.
     (!x. x IN bijdom ==> appbij x IN bijcodom /\ appinvbij (appbij x) = x) /\
     (!x. x IN bijcodom ==> appinvbij x IN bijdom /\ appbij (appinvbij x) = x) /\
     domain t1_out SUBSET bijcodom /\ domain t2_out SUBSET bijcodom /\
     domain ft1_out = IMAGE f (domain t1_out) /\ INJ f (domain t1_out) UNIV /\
     domain flivein1 = IMAGE (f o appbij) (domain livein1) /\
     domain livein1 = IMAGE appinvbij (domain t1_out) /\
     domain livein2 = IMAGE appinvbij (domain t2_out) /\
     check_partial_col f (MAP FST (toAList (difference t2_out t1_out))) t1_out ft1_out =
       SOME (livein,flivein) ==>
     ?li fli.
       check_partial_col (\x. f (appbij x)) (MAP FST (toAList (difference livein2 livein1)))
         livein1 flivein1 = SOME (li,fli) /\
       domain li = IMAGE appinvbij (domain livein)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "b1") (CONJUNCTS_THEN2 (LABEL_TAC "b2")
    (CONJUNCTS_THEN2 (LABEL_TAC "s1") (CONJUNCTS_THEN2 (LABEL_TAC "s2")
    (CONJUNCTS_THEN2 (LABEL_TAC "df1") (CONJUNCTS_THEN2 (LABEL_TAC "inj1")
    (CONJUNCTS_THEN2 (LABEL_TAC "dfl1") (CONJUNCTS_THEN2 (LABEL_TAC "dl1")
    (CONJUNCTS_THEN2 (LABEL_TAC "dl2") (LABEL_TAC "cpc")))))))))) THEN
  ABBREV_TAC `l = MAP FST (toAList (difference (livein2:1 spt) (livein1:1 spt)))` THEN
  (* the renamed new registers are the new registers *)
  SUBGOAL_THEN `set_of_list (MAP (appbij:num->num) l) UNION domain (t1_out:1 spt) =
                domain t1_out UNION domain (t2_out:1 spt)` (LABEL_TAC "seteq") THENL
   [EXPAND_TAC "l" THEN
    REWRITE_TAC[SET_OF_LIST_MAP; set_MAP_FST_toAList_eq_domain; domain_difference] THEN
    USE_THEN "dl1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "dl2" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "s1" MP_TAC THEN USE_THEN "s2" MP_TAC THEN USE_THEN "b2" MP_TAC THEN
    REWRITE_TAC[EXTENSION; SUBSET; IN_UNION; IN_DIFF; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`livein:1 spt`; `flivein:1 spt`;
    `MAP FST (toAList (difference (t2_out:1 spt) (t1_out:1 spt)))`;
    `t1_out:1 spt`; `ft1_out:1 spt`; `f:num->num`] check_partial_col_success_INJ_lemma) THEN
  REWRITE_TAC[branch_domain] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(LABEL_TAC "inj12")] THEN
  (* the renamed check succeeds *)
  MP_TAC(ISPECL [`MAP (appbij:num->num) l`; `t1_out:1 spt`; `ft1_out:1 spt`; `f:num->num`]
    check_partial_col_success) THEN
  ANTS_TAC THENL
   [USE_THEN "seteq" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `br:1 spt` (X_CHOOSE_THEN `fbr:1 spt`
    (CONJUNCTS_THEN2 (LABEL_TAC "cbr") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `domain (br:1 spt) = domain (livein:1 spt)` (LABEL_TAC "dbr") THENL
   [USE_THEN "cbr" (MP_TAC o MATCH_MP check_partial_col_domain) THEN
    USE_THEN "cpc" (MP_TAC o MATCH_MP check_partial_col_domain) THEN
    REWRITE_TAC[FST; branch_domain] THEN
    USE_THEN "seteq" (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`bijdom:num->bool`; `bijcodom:num->bool`; `appbij:num->num`;
    `appinvbij:num->num`; `f:num->num`; `l:num list`; `t1_out:1 spt`; `ft1_out:1 spt`;
    `livein1:1 spt`; `flivein1:1 spt`; `br:1 spt`; `fbr:1 spt`]
    check_partial_col_apply_bijection) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "b1" ACCEPT_TAC;
      USE_THEN "b2" ACCEPT_TAC;
      EXPAND_TAC "l" THEN REWRITE_TAC[set_MAP_FST_toAList_eq_domain; domain_difference] THEN
      USE_THEN "dl2" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "s2" MP_TAC THEN USE_THEN "b2" MP_TAC THEN
      REWRITE_TAC[SUBSET; IN_DIFF; IN_IMAGE] THEN MESON_TAC[];
      USE_THEN "s1" ACCEPT_TAC;
      USE_THEN "df1" ACCEPT_TAC;
      USE_THEN "dfl1" ACCEPT_TAC;
      USE_THEN "dl1" ACCEPT_TAC;
      USE_THEN "inj1" ACCEPT_TAC;
      USE_THEN "cbr" ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `li:1 spt` (X_CHOOSE_THEN `fli:1 spt`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dli")))) THEN
  MAP_EVERY EXISTS_TAC [`li:1 spt`; `fli:1 spt`] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    USE_THEN "dli" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "dbr" (fun th -> REWRITE_TAC[th])]);;

(* HOL4 line 5710 *)
let check_clash_tree_apply_bijection = prove
 (`!bij invbij f ct live flive live' flive' livein flivein.
     sp_inverts bij invbij /\
     sp_inverts invbij bij /\
     in_clash_tree ct SUBSET domain bij /\
     domain live SUBSET domain invbij /\
     domain flive = IMAGE f (domain live) /\
     domain flive' = IMAGE (\r. f (misc_the 0 (lookup r bij))) (domain live') /\
     domain live' = IMAGE (\r. misc_the 0 (lookup r invbij)) (domain live) /\
     INJ f (domain live) UNIV /\
     check_clash_tree f (apply_bij_on_clash_tree ct bij) live flive =
       SOME (livein,flivein) ==>
     ?livein' flivein'.
       check_clash_tree (\r. f (misc_the 0 (lookup r bij))) ct live' flive' =
         SOME (livein',flivein') /\
       domain livein' = IMAGE (\r. misc_the 0 (lookup r invbij)) (domain livein)`,
    MAP_EVERY X_GEN_TAC [`bij:num spt`; `invbij:num spt`; `f:num->num`] THEN
  MATCH_MP_TAC clash_tree_INDUCT THEN REPEAT CONJ_TAC THENL
   [(* Delta *)
    MAP_EVERY X_GEN_TAC [`wl:num list`; `rl:num list`] THEN
    MAP_EVERY X_GEN_TAC [`live:1 spt`; `flive:1 spt`; `live':1 spt`; `flive':1 spt`;
      `livein:1 spt`; `flivein:1 spt`] THEN
    REWRITE_TAC[apply_bij_on_clash_tree_def; in_clash_tree_set_eq; UNION_SUBSET] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`domain (bij:num spt)`; `domain (invbij:num spt)`;
      `\x. misc_the 0 (lookup x (bij:num spt))`; `\x. misc_the 0 (lookup x (invbij:num spt))`;
      `f:num->num`; `wl:num list`; `rl:num list`; `live:1 spt`; `flive:1 spt`;
      `live':1 spt`; `flive':1 spt`; `livein:1 spt`; `flivein:1 spt`]
      LSCANPAUX_cct_bij_delta) THEN
    REWRITE_TAC[o_DEF] THEN BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC LSCANPAUX_sp_inverts_app THEN FIRST_ASSUM ACCEPT_TAC];
    (* Set *)
    X_GEN_TAC `s:1 spt` THEN
    MAP_EVERY X_GEN_TAC [`live:1 spt`; `flive:1 spt`; `live':1 spt`; `flive':1 spt`;
      `livein:1 spt`; `flivein:1 spt`] THEN
    REWRITE_TAC[apply_bij_on_clash_tree_def; in_clash_tree_set_eq;
                LSCANPAUX_check_clash_tree_SOME] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`domain (bij:num spt)`; `domain (invbij:num spt)`;
      `\x. misc_the 0 (lookup x (bij:num spt))`; `\x. misc_the 0 (lookup x (invbij:num spt))`;
      `s:1 spt`; `livein:1 spt`; `flivein:1 spt`; `f:num->num`]
      check_col_apply_bijection) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC LSCANPAUX_sp_inverts_app THEN FIRST_ASSUM ACCEPT_TAC];
    (* Branch *)
    X_GEN_TAC `topt:(1 spt)option` THEN MAP_EVERY X_GEN_TAC [`t1:clash_tree`; `t2:clash_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    DISJ_CASES_THEN2 (X_CHOOSE_THEN `s:1 spt` SUBST1_TAC) SUBST1_TAC
      (ISPEC `topt:(1 spt)option` option_CASES) THEN
    MAP_EVERY X_GEN_TAC [`live:1 spt`; `flive:1 spt`; `live':1 spt`; `flive':1 spt`;
      `livein:1 spt`; `flivein:1 spt`] THEN
    REWRITE_TAC[apply_bij_on_clash_tree_def; OPTION_MAP_DEF; LSCANPAUX_check_clash_tree_SOME;
                in_clash_tree_set_eq; case_def "option"; UNION_SUBSET] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sp1") (CONJUNCTS_THEN2 (LABEL_TAC "sp2")
      (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "slive")
      (CONJUNCTS_THEN2 (LABEL_TAC "dfl") (CONJUNCTS_THEN2 (LABEL_TAC "dfl'")
      (CONJUNCTS_THEN2 (LABEL_TAC "dl'") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
      (X_CHOOSE_THEN `t1_out:1 spt` (X_CHOOSE_THEN `ft1_out:1 spt`
      (X_CHOOSE_THEN `t2_out:1 spt` (X_CHOOSE_THEN `ft2_out:1 spt`
      (CONJUNCTS_THEN2 (LABEL_TAC "c1") (CONJUNCTS_THEN2 (LABEL_TAC "c2")
        (LABEL_TAC "c3"))))))))))))))) THEN
    (SUBGOAL_THEN `!x. x IN domain (bij:num spt) ==>
                      misc_the 0 (lookup x bij) IN domain (invbij:num spt) /\
                      misc_the 0 (lookup (misc_the 0 (lookup x bij)) invbij) = x` (LABEL_TAC "B1") THENL
     [MATCH_MP_TAC LSCANPAUX_sp_inverts_app THEN USE_THEN "sp1" ACCEPT_TAC; ALL_TAC]) THEN
    (SUBGOAL_THEN `!x. x IN domain (invbij:num spt) ==>
                      misc_the 0 (lookup x invbij) IN domain (bij:num spt) /\
                      misc_the 0 (lookup (misc_the 0 (lookup x invbij)) bij) = x` (LABEL_TAC "B2") THENL
     [MATCH_MP_TAC LSCANPAUX_sp_inverts_app THEN USE_THEN "sp2" ACCEPT_TAC; ALL_TAC]) THEN
    USE_THEN "ih1" (MP_TAC o SPECL [`live:1 spt`; `flive:1 spt`; `live':1 spt`; `flive':1 spt`;
      `t1_out:1 spt`; `ft1_out:1 spt`]) THEN
    (ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `livein1:1 spt` (X_CHOOSE_THEN `flivein1:1 spt`
      (CONJUNCTS_THEN2 (LABEL_TAC "d1") (LABEL_TAC "e1")))) THEN
    USE_THEN "ih2" (MP_TAC o SPECL [`live:1 spt`; `flive:1 spt`; `live':1 spt`; `flive':1 spt`;
      `t2_out:1 spt`; `ft2_out:1 spt`]) THEN
    (ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `livein2:1 spt` (X_CHOOSE_THEN `flivein2:1 spt`
      (CONJUNCTS_THEN2 (LABEL_TAC "d2") (LABEL_TAC "e2")))) THENL
     [(* a cut set *)
      MP_TAC(ISPECL [`domain (bij:num spt)`; `domain (invbij:num spt)`;
        `\x. misc_the 0 (lookup x (bij:num spt))`; `\x. misc_the 0 (lookup x (invbij:num spt))`;
        `s:1 spt`; `livein:1 spt`; `flivein:1 spt`; `f:num->num`]
        check_col_apply_bijection) THEN
      BETA_TAC THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `li:1 spt` (X_CHOOSE_THEN `fli:1 spt` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`li:1 spt`; `fli:1 spt`] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`livein1:1 spt`; `flivein1:1 spt`; `livein2:1 spt`;
        `flivein2:1 spt`] THEN
      ASM_REWRITE_TAC[];
      (* no cut set *)
      SUBGOAL_THEN `INJ (\x. (f:num->num) (misc_the 0 (lookup x (bij:num spt)))) (domain (live':1 spt))
                      UNIV` (LABEL_TAC "inj'") THENL
       [MP_TAC(ISPECL [`domain (bij:num spt)`; `domain (invbij:num spt)`;
          `\x. misc_the 0 (lookup x (bij:num spt))`; `\x. misc_the 0 (lookup x (invbij:num spt))`;
          `f:num->num`; `live:1 spt`; `live':1 spt`] LSCANPAUX_INJ_bij) THEN
        BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `domain (t1_out:1 spt) SUBSET domain (invbij:num spt)` (LABEL_TAC "s1") THENL
       [MP_TAC(ISPECL [`bij:num spt`; `invbij:num spt`; `f:num->num`; `t1:clash_tree`;
          `live:1 spt`; `flive:1 spt`; `t1_out:1 spt`; `ft1_out:1 spt`] LSCANPAUX_cct_out_bij) THEN
        DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `domain (t2_out:1 spt) SUBSET domain (invbij:num spt)` (LABEL_TAC "s2") THENL
       [MP_TAC(ISPECL [`bij:num spt`; `invbij:num spt`; `f:num->num`; `t2:clash_tree`;
          `live:1 spt`; `flive:1 spt`; `t2_out:1 spt`; `ft2_out:1 spt`] LSCANPAUX_cct_out_bij) THEN
        DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`f:num->num`; `apply_bij_on_clash_tree t1 bij`; `live:1 spt`;
        `flive:1 spt`; `t1_out:1 spt`; `ft1_out:1 spt`] check_clash_tree_output) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "df1") (LABEL_TAC "inj1")) THEN
      MP_TAC(ISPECL [`\x. (f:num->num) (misc_the 0 (lookup x (bij:num spt)))`; `t1:clash_tree`;
        `live':1 spt`; `flive':1 spt`; `livein1:1 spt`; `flivein1:1 spt`]
        check_clash_tree_output) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dfl1") (K ALL_TAC)) THEN
      MP_TAC(ISPECL [`domain (bij:num spt)`; `domain (invbij:num spt)`;
        `\x. misc_the 0 (lookup x (bij:num spt))`; `\x. misc_the 0 (lookup x (invbij:num spt))`;
        `f:num->num`; `t1_out:1 spt`; `ft1_out:1 spt`; `t2_out:1 spt`; `livein1:1 spt`;
        `flivein1:1 spt`; `livein2:1 spt`; `livein:1 spt`; `flivein:1 spt`]
        LSCANPAUX_cct_bij_branch) THEN
      REWRITE_TAC[o_DEF] THEN BETA_TAC THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `li:1 spt` (X_CHOOSE_THEN `fli:1 spt` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`li:1 spt`; `fli:1 spt`] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`livein1:1 spt`; `flivein1:1 spt`; `livein2:1 spt`;
        `flivein2:1 spt`] THEN
      ASM_REWRITE_TAC[]];
    (* Seq *)
    MAP_EVERY X_GEN_TAC [`t1:clash_tree`; `t2:clash_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    MAP_EVERY X_GEN_TAC [`live:1 spt`; `flive:1 spt`; `live':1 spt`; `flive':1 spt`;
      `livein:1 spt`; `flivein:1 spt`] THEN
    REWRITE_TAC[apply_bij_on_clash_tree_def; LSCANPAUX_check_clash_tree_SOME;
                in_clash_tree_set_eq; UNION_SUBSET] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sp1") (CONJUNCTS_THEN2 (LABEL_TAC "sp2")
      (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "slive")
      (CONJUNCTS_THEN2 (LABEL_TAC "dfl") (CONJUNCTS_THEN2 (LABEL_TAC "dfl'")
      (CONJUNCTS_THEN2 (LABEL_TAC "dl'") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
      (X_CHOOSE_THEN `t2_out:1 spt` (X_CHOOSE_THEN `ft2_out:1 spt`
      (CONJUNCTS_THEN2 (LABEL_TAC "c2") (LABEL_TAC "c1")))))))))))) THEN
    USE_THEN "ih2" (MP_TAC o SPECL [`live:1 spt`; `flive:1 spt`; `live':1 spt`; `flive':1 spt`;
      `t2_out:1 spt`; `ft2_out:1 spt`]) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `livein2:1 spt` (X_CHOOSE_THEN `flivein2:1 spt`
      (CONJUNCTS_THEN2 (LABEL_TAC "d2") (LABEL_TAC "e2")))) THEN
    SUBGOAL_THEN `INJ (\x. (f:num->num) (misc_the 0 (lookup x (bij:num spt)))) (domain (live':1 spt))
                    UNIV` (LABEL_TAC "inj'") THENL
     [MP_TAC(ISPECL [`domain (bij:num spt)`; `domain (invbij:num spt)`;
        `\x. misc_the 0 (lookup x (bij:num spt))`; `\x. misc_the 0 (lookup x (invbij:num spt))`;
        `f:num->num`; `live:1 spt`; `live':1 spt`] LSCANPAUX_INJ_bij) THEN
      BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
      FIRST [FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC LSCANPAUX_sp_inverts_app THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `domain (t2_out:1 spt) SUBSET domain (invbij:num spt)` (LABEL_TAC "s2") THENL
     [MP_TAC(ISPECL [`bij:num spt`; `invbij:num spt`; `f:num->num`; `t2:clash_tree`;
        `live:1 spt`; `flive:1 spt`; `t2_out:1 spt`; `ft2_out:1 spt`] LSCANPAUX_cct_out_bij) THEN
      DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:num->num`; `apply_bij_on_clash_tree t2 bij`; `live:1 spt`;
      `flive:1 spt`; `t2_out:1 spt`; `ft2_out:1 spt`] check_clash_tree_output) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "df2") (LABEL_TAC "inj2")) THEN
    MP_TAC(ISPECL [`\x. (f:num->num) (misc_the 0 (lookup x (bij:num spt)))`; `t2:clash_tree`;
      `live':1 spt`; `flive':1 spt`; `livein2:1 spt`; `flivein2:1 spt`]
      check_clash_tree_output) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dfl2") (K ALL_TAC)) THEN
    USE_THEN "ih1" (MP_TAC o SPECL [`t2_out:1 spt`; `ft2_out:1 spt`; `livein2:1 spt`;
      `flivein2:1 spt`; `livein:1 spt`; `flivein:1 spt`]) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `li:1 spt` (X_CHOOSE_THEN `fli:1 spt` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`li:1 spt`; `fli:1 spt`] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`livein2:1 spt`; `flivein2:1 spt`] THEN ASM_REWRITE_TAC[]]);;


(* HOL4 line 5867 *)
let extract_coloration_output = prove
 (`!bij invbij sth l acc.
     sp_inverts bij invbij /\
     sp_inverts invbij bij /\
     ALL (\r. r IN domain invbij) l /\
     ALL (\r. r < LENGTH (linear_scan_hidden_state_colors sth)) l ==>
     ?col.
       extract_coloration invbij l acc sth = (M_success col,sth) /\
       (!r. r IN domain bij ==>
            (if MEM (misc_the 0 (lookup r bij)) l
             then lookup r col =
                  SOME (EL (misc_the 0 (lookup r bij)) (linear_scan_hidden_state_colors sth))
             else lookup r col = lookup r acc)) /\
       domain col SUBSET domain bij UNION domain acc`,
    MAP_EVERY X_GEN_TAC [`bij:num spt`; `invbij:num spt`; `sth:linear_scan_hidden_state`] THEN
  LIST_INDUCT_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `acc:num spt` THEN
    REWRITE_TAC[extract_coloration_def; st_ex_return_def; MEM] THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `acc:num spt` THEN REWRITE_TAC[ALL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sp1") (CONJUNCTS_THEN2 (LABEL_TAC "sp2")
    (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "hdom") (LABEL_TAC "tdom"))
      (CONJUNCTS_THEN2 (LABEL_TAC "hlt") (LABEL_TAC "tlt"))))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `insert (misc_the 0 (lookup h (invbij:num spt)))
    (EL h (linear_scan_hidden_state_colors sth)) (acc:num spt)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `col:num spt` (CONJUNCTS_THEN2 (LABEL_TAC "ex")
    (CONJUNCTS_THEN2 (LABEL_TAC "lk") (LABEL_TAC "dc")))) THEN
  EXISTS_TAC `col:num spt` THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `colors_sub h sth =
                  (M_success (EL h (linear_scan_hidden_state_colors sth)),sth)` ASSUME_TAC THENL
     [REWRITE_TAC[colors_sub_eqn] THEN USE_THEN "hlt" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    REWRITE_TAC[extract_coloration_def] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RAPROOFAUX_bind_ok th]) THEN BETA_TAC THEN
    USE_THEN "ex" ACCEPT_TAC;
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    REMOVE_THEN "lk" (MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[MEM] THEN
    ASM_CASES_TAC `MEM (misc_the 0 (lookup r (bij:num spt))) t` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[lookup_insert] THEN
    SUBGOAL_THEN `(r = misc_the 0 (lookup h (invbij:num spt))) <=> (misc_the 0 (lookup r (bij:num spt)) = h)`
      (fun th -> REWRITE_TAC[th]) THENL
     [USE_THEN "sp1" (MP_TAC o REWRITE_RULE[sp_inverts_def]) THEN
      USE_THEN "sp2" (MP_TAC o REWRITE_RULE[sp_inverts_def]) THEN
      UNDISCH_TAC `(r:num) IN domain (bij:num spt)` THEN USE_THEN "hdom" MP_TAC THEN
      REWRITE_TAC[domain_lookup] THEN
      DISCH_THEN(X_CHOOSE_TAC `y:num`) THEN DISCH_THEN(X_CHOOSE_TAC `x:num`) THEN
      ASM_REWRITE_TAC[misc_the_def] THEN ASM_MESON_TAC[option_INJ];
      ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "dc" MP_TAC THEN REWRITE_TAC[domain_insert] THEN
    SUBGOAL_THEN `misc_the 0 (lookup h (invbij:num spt)) IN domain (bij:num spt)` MP_TAC THENL
     [USE_THEN "hdom" (MP_TAC o REWRITE_RULE[domain_lookup]) THEN
      DISCH_THEN(X_CHOOSE_TAC `y:num`) THEN ASM_REWRITE_TAC[misc_the_def; domain_lookup] THEN
      USE_THEN "sp2" (MP_TAC o REWRITE_RULE[sp_inverts_def]) THEN ASM_MESON_TAC[];
      SET_TAC[]]]);;

(* HOL4 line 5932 *)
let check_col_equal_col = prove
 (`!(s:A spt) f1 f2.
     (!r. r IN domain s ==> f1 r = f2 r) ==> check_col f1 s = check_col f2 s`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[check_col_def; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `MAP ((f1:num->num) o FST) (toAList (s:A spt)) = MAP (f2 o FST) (toAList s)`
    (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  REWRITE_TAC[GSYM IN_SET_OF_LIST; set_MAP_FST_toAList_eq_domain] THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* HOL4 line 5944 *)
let check_partial_col_equal_col = prove
 (`!l live flive f1 f2.
     (!r. MEM r l ==> f1 r = f2 r) ==>
     check_partial_col f1 l live flive = check_partial_col f2 l live flive`,
    LIST_INDUCT_TAC THENL [REWRITE_TAC[check_partial_col_def]; ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "ih") THEN
  MAP_EVERY X_GEN_TAC [`live:1 spt`; `flive:1 spt`; `f1:num->num`; `f2:num->num`] THEN
  REWRITE_TAC[MEM] THEN DISCH_THEN(LABEL_TAC "eq") THEN
  SUBGOAL_THEN `!lv flv. check_partial_col (f1:num->num) t lv flv = check_partial_col f2 t lv flv`
    (LABEL_TAC "ihi") THENL
   [REPEAT GEN_TAC THEN USE_THEN "ih" MATCH_MP_TAC THEN USE_THEN "eq" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(f1:num->num) h = f2 h` ASSUME_TAC THENL
   [USE_THEN "eq" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  ASM_REWRITE_TAC[check_partial_col_def]);;

(* HOL4 line 5954 *)
let check_clash_tree_equal_col = prove
 (`!f1 f2 ct live flive.
     (!r. r IN in_clash_tree ct ==> f1 r = f2 r) /\
     (!r. r IN domain live ==> f1 r = f2 r) ==>
     check_clash_tree f1 ct live flive = check_clash_tree f2 ct live flive`,
    MAP_EVERY X_GEN_TAC [`f1:num->num`; `f2:num->num`] THEN
  MATCH_MP_TAC clash_tree_INDUCT THEN REPEAT CONJ_TAC THENL
   [(* Delta *)
    MAP_EVERY X_GEN_TAC [`wl:num list`; `rl:num list`; `live:1 spt`; `flive:1 spt`] THEN
    REWRITE_TAC[in_clash_tree_set_eq; IN_UNION; IN_SET_OF_LIST] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "e1") (LABEL_TAC "e2")) THEN
    REWRITE_TAC[check_clash_tree_def; LET_DEF; LET_END_DEF] THEN
    SUBGOAL_THEN `!lv flv. check_partial_col (f1:num->num) wl lv flv =
                           check_partial_col f2 wl lv flv` (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC check_partial_col_equal_col THEN
      USE_THEN "e1" (fun th -> MESON_TAC[th]);
      ALL_TAC] THEN
    SUBGOAL_THEN `!lv flv. check_partial_col (f1:num->num) rl lv flv =
                           check_partial_col f2 rl lv flv` (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC check_partial_col_equal_col THEN
      USE_THEN "e1" (fun th -> MESON_TAC[th]);
      ALL_TAC] THEN
    SUBGOAL_THEN `MAP (f1:num->num) wl = MAP f2 wl` (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    USE_THEN "e1" (fun th -> MESON_TAC[th]);
    (* Set *)
    X_GEN_TAC `s:1 spt` THEN MAP_EVERY X_GEN_TAC [`live:1 spt`; `flive:1 spt`] THEN
    REWRITE_TAC[in_clash_tree_set_eq; check_clash_tree_def] THEN STRIP_TAC THEN
    MATCH_MP_TAC check_col_equal_col THEN FIRST_ASSUM ACCEPT_TAC;
    (* Branch *)
    X_GEN_TAC `topt:(1 spt)option` THEN MAP_EVERY X_GEN_TAC [`t1:clash_tree`; `t2:clash_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    DISJ_CASES_THEN2 (X_CHOOSE_THEN `s:1 spt` SUBST1_TAC) SUBST1_TAC
      (ISPEC `topt:(1 spt)option` option_CASES) THEN
    MAP_EVERY X_GEN_TAC [`live:1 spt`; `flive:1 spt`] THEN
    REWRITE_TAC[in_clash_tree_set_eq; case_def "option"; IN_UNION] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "e1") (LABEL_TAC "e2")) THEN
    (SUBGOAL_THEN `!r. r IN in_clash_tree t1 ==> (f1:num->num) r = f2 r` (LABEL_TAC "et1") THENL
      [USE_THEN "e1" (fun th -> MESON_TAC[th]); ALL_TAC]) THEN
    (SUBGOAL_THEN `!r. r IN in_clash_tree t2 ==> (f1:num->num) r = f2 r` (LABEL_TAC "et2") THENL
      [USE_THEN "e1" (fun th -> MESON_TAC[th]); ALL_TAC]) THEN
    USE_THEN "ih1" (MP_TAC o SPECL [`live:1 spt`; `flive:1 spt`]) THEN
    (ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN DISCH_TAC THEN
    USE_THEN "ih2" (MP_TAC o SPECL [`live:1 spt`; `flive:1 spt`]) THEN
    (ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN DISCH_TAC THEN
    REWRITE_TAC[check_clash_tree_def; case_def "option"] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `check_clash_tree f2 t1 live flive` option_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `p1:1 spt#1 spt` SUBST1_TAC) SUBST1_TAC) THEN
    REWRITE_TAC[case_def "option"] THEN
    MP_TAC(ISPEC `p1:1 spt#1 spt` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `t1_out:1 spt` (X_CHOOSE_THEN `ft1_out:1 spt` SUBST1_TAC)) THEN
    REWRITE_TAC[case_def "prod"] THEN
    MP_TAC(ISPEC `check_clash_tree f2 t2 live flive` option_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `p2:1 spt#1 spt`
      (fun th -> SUBST1_TAC th THEN ASSUME_TAC th)) SUBST1_TAC) THEN
    REWRITE_TAC[case_def "option"] THEN
    MP_TAC(ISPEC `p2:1 spt#1 spt` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `t2_out:1 spt` (X_CHOOSE_THEN `ft2_out:1 spt` SUBST_ALL_TAC)) THEN
    REWRITE_TAC[case_def "prod"] THENL
     [MATCH_MP_TAC check_col_equal_col THEN USE_THEN "e1" (fun th -> MESON_TAC[th]);
      MATCH_MP_TAC check_partial_col_equal_col THEN
      REWRITE_TAC[GSYM IN_SET_OF_LIST; set_MAP_FST_toAList_eq_domain; domain_difference;
                  IN_DIFF] THEN
      X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      UNDISCH_TAC `check_clash_tree f2 t2 live flive = SOME (t2_out,ft2_out)` THEN
      DISCH_THEN(MP_TAC o MATCH_MP check_clash_tree_output_subset) THEN
      REWRITE_TAC[SUBSET; IN_UNION] THEN DISCH_THEN(MP_TAC o SPEC `r:num`) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "e2" (fun a -> USE_THEN "et2" (fun b -> MESON_TAC[a; b]))];
    (* Seq *)
    MAP_EVERY X_GEN_TAC [`t1:clash_tree`; `t2:clash_tree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    MAP_EVERY X_GEN_TAC [`live:1 spt`; `flive:1 spt`] THEN
    REWRITE_TAC[in_clash_tree_set_eq; IN_UNION] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "e1") (LABEL_TAC "e2")) THEN
    USE_THEN "ih2" (MP_TAC o SPECL [`live:1 spt`; `flive:1 spt`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [USE_THEN "e1" (fun th -> MESON_TAC[th]); USE_THEN "e2" ACCEPT_TAC];
      DISCH_TAC] THEN
    REWRITE_TAC[check_clash_tree_def] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `check_clash_tree f2 t2 live flive` option_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `p2:1 spt#1 spt`
      (fun th -> SUBST1_TAC th THEN ASSUME_TAC th)) SUBST1_TAC) THEN
    REWRITE_TAC[case_def "option"] THEN
    MP_TAC(ISPEC `p2:1 spt#1 spt` PAIR_SURJECTIVE) THEN
    DISCH_THEN(X_CHOOSE_THEN `t2_out:1 spt` (X_CHOOSE_THEN `ft2_out:1 spt` SUBST_ALL_TAC)) THEN
    REWRITE_TAC[case_def "prod"] THEN
    USE_THEN "ih1" MATCH_MP_TAC THEN CONJ_TAC THENL
     [USE_THEN "e1" (fun th -> MESON_TAC[th]);
      UNDISCH_TAC `check_clash_tree f2 t2 live flive = SOME (t2_out,ft2_out)` THEN
      DISCH_THEN(MP_TAC o MATCH_MP check_clash_tree_output_subset) THEN
      REWRITE_TAC[SUBSET; IN_UNION] THEN
      USE_THEN "e1" (fun a -> USE_THEN "e2" (fun b -> MESON_TAC[a; b]))]]);;


(* LSCANPAUX_ibind_assoc: a successful prefix of two ignore-binds *)
let LSCANPAUX_ibind_assoc = prove
 (`!(m:S->(A,E)exc#S) (g:S->(B,E)exc#S) (h:S->(C,E)exc#S) s a s'.
     st_ex_ignore_bind m g s = (M_success a,s') ==>
     st_ex_ignore_bind m (st_ex_ignore_bind g h) s = h s'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[st_ex_ignore_bind_def] THEN BETA_TAC THEN
  MP_TAC(ISPEC `(m:S->(A,E)exc#S) s` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(A,E)exc` (X_CHOOSE_THEN `s1:S` SUBST1_TAC)) THEN
  REWRITE_TAC[case_def "prod"] THEN
  CASES_ON `r:(A,E)exc` THEN REWRITE_TAC[case_def "exc"; PAIR_EQ; distinctness "exc"] THEN
  MP_TAC(ISPEC `(g:S->(B,E)exc#S) s1` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:(B,E)exc` (X_CHOOSE_THEN `s2:S` SUBST1_TAC)) THEN
  REWRITE_TAC[case_def "prod"] THEN
  CASES_ON `r2:(B,E)exc` THEN REWRITE_TAC[case_def "exc"; PAIR_EQ; distinctness "exc"] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* LSCANPAUX_MEM_MAP_SND_toAList: the values of an sptree *)
let LSCANPAUX_MEM_MAP_SND_toAList = prove
 (`!(bij:num spt) x.
     MEM x (MAP SND (toAList bij)) <=> ?r. r IN domain bij /\ x = misc_the 0 (lookup r bij)`,
  REWRITE_TAC[MEM_MAP; EXISTS_PAIR_THM; MEM_toAList; domain_lookup; SND] THEN
  MESON_TAC[misc_the_def]);;

(* LSCANPAUX_ALL_DISTINCT_MAP_SND_toAList: an invertible sptree has distinct values *)
let LSCANPAUX_ALL_DISTINCT_MAP_SND_toAList = prove
 (`!(bij:num spt) invbij. sp_inverts bij invbij ==> ALL_DISTINCT (MAP SND (toAList bij))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ALL_DISTINCT_MAP_INJ THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; MEM_toAList; PAIR_EQ; SND] THEN
    UNDISCH_TAC `sp_inverts (bij:num spt) invbij` THEN REWRITE_TAC[sp_inverts_def] THEN
    MESON_TAC[option_INJ];
    MATCH_MP_TAC(ISPEC `FST:num#num->num` ALL_DISTINCT_MAP) THEN
    REWRITE_TAC[ALL_DISTINCT_MAP_FST_toAList]]);;

(* LSCANPAUX_ABBREV_ARG_TAC c i v: abbreviate as v the argument i of the *)
(* first application of the constant c in the goal                       *)
let LSCANPAUX_ABBREV_ARG_TAC (cname:string) (i:int) (v:string) : tactic = fun (asl,w as g) ->
  let tm = find_term (fun t -> let h,args = strip_comb t in
                        is_const h && fst(dest_const h) = cname && List.length args > i) w in
  let arg = List.nth (snd(strip_comb tm)) i in
  ABBREV_TAC (mk_eq(mk_var(v,type_of arg),arg)) g;;

(* HOL4 line 6008 *)
let linear_scan_reg_alloc_correct = prove
 (CASE_TERM
  `!k moves ct forced.
     ALL (\r12. match r12 with (r1,r2) -> in_clash_tree ct r1 /\ in_clash_tree ct r2)
         forced
     ==> ?col livein flivein.
           linear_scan_reg_alloc k moves ct forced = M_success col /\
           check_clash_tree (sp_default col) ct LN LN = SOME (livein,flivein) /\
           (!r. in_clash_tree ct r
                ==> r IN domain col /\
                    (if is_phy_var r then sp_default col r = r DIV 2
                     else if is_stack_var r then k <= sp_default col r
                     else T)) /\
           (!r. r IN domain col ==> in_clash_tree ct r) /\
           ALL (\r12. match r12 with
                        (r1,r2) -> sp_default col r1 = sp_default col r2 ==> r1 = r2)
               forced`,
    REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "fct") THEN
  REWRITE_TAC[linear_scan_reg_alloc_def; run_linear_reg_alloc_intervals_def;
              run_i_linear_scan_hidden_state_def; ml_monadBase_run_def;
              linear_reg_alloc_and_extract_coloration_def; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[(record_info "i_linear_scan_hidden_state").ri_accessors; FST; SND] THEN
  ABBREV_TAC `bs = find_bijection_clash_tree find_bijection_init ct` THEN
  MP_TAC(ISPECL [`find_bijection_init`; `ct:clash_tree`; `{}:num->bool`]
    find_bijection_clash_tree_invariants) THEN
  ASM_REWRITE_TAC[find_bijection_init_invariants; UNION_EMPTY] THEN
  REWRITE_TAC[good_bijection_state_def] THEN
  ABBREV_TAC `bij = bijection_state_bij bs` THEN
  ABBREV_TAC `invbij = bijection_state_invbij bs` THEN
  ABBREV_TAC `nmax = bijection_state_nmax bs` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dom") (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "sp1") (LABEL_TAC "sp2")) (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "stk") (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "phy")))
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (LABEL_TAC "nmax"))))))) THEN
  LSCANPAUX_ABBREV_ARG_TAC "linear_reg_alloc_intervals" 1 "forced'" THEN
  LSCANPAUX_ABBREV_ARG_TAC "linear_reg_alloc_intervals" 2 "moves'" THEN
  LSCANPAUX_ABBREV_ARG_TAC "linear_reg_alloc_intervals" 3 "rl" THEN
  LSCANPAUX_ABBREV_ARG_TAC "get_intervals_ct_monad" 0 "ct'" THEN
  LSCANPAUX_ABBREV_ARG_TAC "st_ex_ignore_bind" 2 "sth" THEN
  (* facts about the bijection *)
  SUBGOAL_THEN `!r. in_clash_tree ct r <=> r IN domain (bij:num spt)` (LABEL_TAC "domr") THENL
   [GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [IN] THEN USE_THEN "dom" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  USE_THEN "sp1" (LABEL_TAC "bin" o MATCH_MP LSCANPAUX_sp_inverts_app) THEN
  SUBGOAL_THEN `!x. in_clash_tree ct' x <=>
                    ?r. r IN domain (bij:num spt) /\ x = misc_the 0 (lookup r bij)` (LABEL_TAC "ict'")
  THENL
   [X_GEN_TAC `x:num` THEN
    MP_TAC(ISPECL [`bij:num spt`; `ct:clash_tree`] in_clash_tree_apply_bij) THEN
    USE_THEN "dom" (fun th -> REWRITE_TAC[th; SUBSET_REFL]) THEN
    REWRITE_TAC[ASSUME `apply_bij_on_clash_tree ct bij = ct'`] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM IN] THEN REWRITE_TAC[th; IN_IMAGE]) THEN
    BETA_TAC THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. MEM x rl <=> ?r. r IN domain (bij:num spt) /\ x = misc_the 0 (lookup r bij)`
    (LABEL_TAC "memrl") THENL
   [REWRITE_TAC[GSYM(ASSUME `MAP SND (toAList (bij:num spt)) = rl`);
                LSCANPAUX_MEM_MAP_SND_toAList];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL_DISTINCT (rl:num list)` (LABEL_TAC "rld") THENL
   [REWRITE_TAC[GSYM(ASSUME `MAP SND (toAList (bij:num spt)) = rl`)] THEN
    MATCH_MP_TAC LSCANPAUX_ALL_DISTINCT_MAP_SND_toAList THEN
    EXISTS_TAC `invbij:num spt` THEN USE_THEN "sp1" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear_scan_hidden_state_colors sth = REPLICATE (nmax + 1) 0 /\
    linear_scan_hidden_state_int_beg sth = REPLICATE (nmax + 1) (&1) /\
    linear_scan_hidden_state_int_end sth = REPLICATE (nmax + 1) (&1) /\
    linear_scan_hidden_state_sorted_regs sth = REPLICATE (nmax + 1) 0 /\
    linear_scan_hidden_state_sorted_moves sth =
      REPLICATE (LENGTH (moves':(num#num#num)list)) (0,0,0)` (LABEL_TAC "sthc") THENL
   [EXPAND_TAC "sth" THEN REWRITE_TAC[(record_info "linear_scan_hidden_state").ri_accessors];
    ALL_TAC] THEN
  (* the allocation without renaming *)
  MP_TAC(SPECL [`sth:linear_scan_hidden_state`; `rl:num list`; `k:num`;
    `moves':(num#num#num)list`; `ct':clash_tree`; `forced':(num#num)list`]
    linear_reg_alloc_without_renaming_correct) THEN
  ANTS_TAC THENL
   [USE_THEN "sthc" (fun th -> REWRITE_TAC[th; LENGTH_REPLICATE]) THEN
    REPEAT CONJ_TAC THENL
     [SIMP_TAC[EL_REPLICATE; INT_LT_01];
      SIMP_TAC[EL_REPLICATE; INT_LT_01];
      USE_THEN "memrl" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "ict'" (fun th -> REWRITE_TAC[th]);
      USE_THEN "ict'" (fun th -> REWRITE_TAC[th]) THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "nmax" (MP_TAC o SPEC `r':num`) THEN ARITH_TAC;
      EXPAND_TAC "forced'" THEN USE_THEN "fct" MP_TAC THEN
      REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM; case_def "prod"] THEN
      USE_THEN "ict'" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "domr" (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[];
      EXPAND_TAC "moves'" THEN
      REWRITE_TAC[GSYM MAP_o; ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM; case_def "prod"] THEN
      USE_THEN "nmax" (fun th -> REWRITE_TAC[ARITH_RULE `a < n + 1 <=> a <= n`; th]);
      MP_TAC(ISPEC `rl:num list` ALL_DISTINCT_CARD_LIST_TO_SET) THEN
      USE_THEN "rld" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD (0..nmax)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CARD_SUBSET THEN
        REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_SET_OF_LIST] THEN
        USE_THEN "memrl" (fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "nmax" (fun th -> MESON_TAC[th; LE_0]);
        REWRITE_TAC[CARD_NUMSEG] THEN ARITH_TAC];
      REWRITE_TAC[LE_REFL];
      USE_THEN "rld" ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sthout:linear_scan_hidden_state` (X_CHOOSE_THEN `livein:1 spt`
    (X_CHOOSE_THEN `flivein:1 spt` (CONJUNCTS_THEN2 (LABEL_TAC "qo")
    (CONJUNCTS_THEN2 (LABEL_TAC "cct") (CONJUNCTS_THEN2 (LABEL_TAC "colo")
    (CONJUNCTS_THEN2 (LABEL_TAC "fo") (LABEL_TAC "leno")))))))) THEN
  (* the extraction of the colouring *)
  MP_TAC(SPECL [`bij:num spt`; `invbij:num spt`; `sthout:linear_scan_hidden_state`;
    `rl:num list`; `LN:num spt`] extract_coloration_output) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "sp1" ACCEPT_TAC;
      USE_THEN "sp2" ACCEPT_TAC;
      REWRITE_TAC[GSYM ALL_MEM] THEN USE_THEN "memrl" (fun th -> REWRITE_TAC[th]) THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN USE_THEN "bin" (fun th -> ASM_SIMP_TAC[th]);
      REWRITE_TAC[GSYM ALL_MEM] THEN USE_THEN "memrl" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "leno" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "sthc" (fun th -> REWRITE_TAC[th; LENGTH_REPLICATE]) THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN USE_THEN "nmax" (MP_TAC o SPEC `r:num`) THEN
      ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `col:num spt` (CONJUNCTS_THEN2 (LABEL_TAC "ex")
    (CONJUNCTS_THEN2 (LABEL_TAC "lk") (LABEL_TAC "dc")))) THEN
  SUBGOAL_THEN
   `st_ex_ignore_bind (get_intervals_ct_monad ct')
      (st_ex_ignore_bind (linear_reg_alloc_intervals k forced' moves' rl)
         (extract_coloration invbij rl LN)) sth = (M_success col,sthout)` (LABEL_TAC "run")
  THENL
   [USE_THEN "qo" (fun th -> REWRITE_TAC[MATCH_MP LSCANPAUX_ibind_assoc th]) THEN
    USE_THEN "ex" ACCEPT_TAC;
    ALL_TAC] THEN
  (* the check on the original tree *)
  MP_TAC(ISPECL [`bij:num spt`; `invbij:num spt`;
    `\r. EL r (linear_scan_hidden_state_colors sthout)`; `ct:clash_tree`; `LN:1 spt`;
    `LN:1 spt`; `LN:1 spt`; `LN:1 spt`; `livein:1 spt`; `flivein:1 spt`]
    check_clash_tree_apply_bijection) THEN
  REWRITE_TAC[domain_def; IMAGE_CLAUSES; EMPTY_SUBSET; INJ; NOT_IN_EMPTY] THEN BETA_TAC THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ASSUME `apply_bij_on_clash_tree ct bij = ct'`] THEN
    USE_THEN "dom" (fun th -> REWRITE_TAC[th; SUBSET_REFL]) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `li:1 spt` (X_CHOOSE_THEN `fli:1 spt`
    (CONJUNCTS_THEN2 (LABEL_TAC "cct2") (K ALL_TAC)))) THEN
  SUBGOAL_THEN
   `!r. in_clash_tree ct r ==>
        lookup r col =
        SOME (EL (misc_the 0 (lookup r (bij:num spt))) (linear_scan_hidden_state_colors sthout))`
    (LABEL_TAC "lkc") THENL
   [X_GEN_TAC `r:num` THEN USE_THEN "domr" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
    USE_THEN "lk" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(r:num) IN domain (bij:num spt)`))) THEN
    SUBGOAL_THEN `MEM (misc_the 0 (lookup r (bij:num spt))) rl`
      (fun th -> REWRITE_TAC[th] THEN DISCH_THEN ACCEPT_TAC) THEN
    USE_THEN "memrl" (fun th -> REWRITE_TAC[th]) THEN EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. in_clash_tree ct r ==>
        sp_default col r =
        EL (misc_the 0 (lookup r (bij:num spt))) (linear_scan_hidden_state_colors sthout)`
    (LABEL_TAC "spd") THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    USE_THEN "lkc" (fun th -> REWRITE_TAC[sp_default_def; MATCH_MP th
      (ASSUME `in_clash_tree ct r`); case_def "option"]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sp_default col`;
    `\r. EL (misc_the 0 (lookup r (bij:num spt))) (linear_scan_hidden_state_colors sthout)`;
    `ct:clash_tree`; `LN:1 spt`; `LN:1 spt`] check_clash_tree_equal_col) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[domain_def; NOT_IN_EMPTY] THEN BETA_TAC THEN REWRITE_TAC[IN] THEN
    USE_THEN "spd" ACCEPT_TAC;
    DISCH_THEN(LABEL_TAC "eqc")] THEN
  MAP_EVERY EXISTS_TAC [`col:num spt`; `li:1 spt`; `fli:1 spt`] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "run" (fun th -> REWRITE_TAC[th; FST]);
    USE_THEN "eqc" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "cct2" ACCEPT_TAC;
    (* the colours *)
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(r:num) IN domain (bij:num spt)` ASSUME_TAC THENL
     [USE_THEN "domr" (fun th -> REWRITE_TAC[GSYM th]) THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[domain_lookup] THEN EXISTS_TAC
        `EL (misc_the 0 (lookup r (bij:num spt))) (linear_scan_hidden_state_colors sthout)` THEN
      USE_THEN "lkc" (fun th -> MATCH_MP_TAC th) THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    USE_THEN "spd" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `in_clash_tree ct r`)]) THEN
    SUBGOAL_THEN `in_clash_tree ct' (misc_the 0 (lookup r (bij:num spt)))` ASSUME_TAC THENL
     [USE_THEN "ict'" (fun th -> REWRITE_TAC[th]) THEN EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "colo" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `in_clash_tree ct' (misc_the 0 (lookup r (bij:num spt)))`))) THEN
    SUBGOAL_THEN `(is_stack_var r <=> is_stack_var (misc_the 0 (lookup r (bij:num spt))))`
      ASSUME_TAC THENL
     [USE_THEN "stk" MATCH_MP_TAC THEN USE_THEN "dom" (fun th -> REWRITE_TAC[th]) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `is_phy_var r` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `misc_the 0 (lookup r (bij:num spt)) = r` (fun th -> REWRITE_TAC[th]) THENL
       [CONV_TAC SYM_CONV THEN USE_THEN "phy" MATCH_MP_TAC THEN
        USE_THEN "dom" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      ASM_CASES_TAC `is_stack_var (misc_the 0 (lookup r (bij:num spt)))` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~is_phy_var (misc_the 0 (lookup r (bij:num spt)))` (fun th -> REWRITE_TAC[th]) THEN
      ASM_MESON_TAC[convention_partitions]];
    (* the domain of the colouring *)
    USE_THEN "dc" MP_TAC THEN REWRITE_TAC[domain_def; UNION_EMPTY; SUBSET] THEN
    USE_THEN "domr" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN MATCH_ACCEPT_TAC;
    (* the forced pairs *)
    USE_THEN "fo" MP_TAC THEN EXPAND_TAC "forced'" THEN USE_THEN "fct" MP_TAC THEN
    REWRITE_TAC[ALL_MAP; GSYM ALL_MEM; FORALL_PAIR_THM; o_THM; case_def "prod"] THEN
    DISCH_THEN(LABEL_TAC "fct2") THEN DISCH_THEN(LABEL_TAC "fo2") THEN
    MAP_EVERY X_GEN_TAC [`r1:num`; `r2:num`] THEN DISCH_TAC THEN
    USE_THEN "fct2" (fun th -> MP_TAC(MATCH_MP th (ASSUME `MEM (r1:num,r2:num) forced`))) THEN
    STRIP_TAC THEN
    USE_THEN "spd" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `in_clash_tree ct r1`);
                                          MATCH_MP th (ASSUME `in_clash_tree ct r2`)]) THEN
    DISCH_TAC THEN
    USE_THEN "fo2" (fun th -> MP_TAC(MATCH_MP th (ASSUME `MEM (r1:num,r2:num) forced`))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(r1:num) IN domain (bij:num spt) /\ (r2:num) IN domain (bij:num spt)`
      STRIP_ASSUME_TAC THENL
     [USE_THEN "domr" (fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "bin" (fun th ->
      MP_TAC(CONJUNCT2(MATCH_MP th (ASSUME `(r1:num) IN domain (bij:num spt)`))) THEN
      MP_TAC(CONJUNCT2(MATCH_MP th (ASSUME `(r2:num) IN domain (bij:num spt)`)))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;
