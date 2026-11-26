(* ========================================================================= *)
(* ListProg: port of HOL4 basis/ListProgScript.sml (CakeML v3479), the code  *)
(* part (decision D2): module about the built-in list type, and the Alist    *)
(* module of finite maps as association lists.  The CF specifications        *)
(* tabulate_aux_inv_spec and tabulate_inv_spec are ListProg_part2.ml (M10).  *)
(*                                                                           *)
(* HOL4 library functions are translated from theorems with HOL4's shape     *)
(* (hol4/list.ml, hol4/basic.ml, mllist.ml).  Differences of the library:    *)
(* HOL4's FOLDR f e l is ITLIST f l e (foldr takes the list before the       *)
(* initial value), TL [] and the uncurried truncating ZIP of HOL4 have no    *)
(* counterpart in HOL Light (TL [] and ZIP (CONS x l) [] are unspecified):   *)
(* the CakeML functions tl and zip have preconditions instead (zip is        *)
(* curried).  HOL4's GENLIST_AUX (listTheory) and REVERSE_REV are not in    *)
(* the library layer: GENLIST_AUX is defined here, REVERSE_REV is            *)
(* BAS1AUX_REVERSE_REV.                                                      *)
(* ========================================================================= *)

needs "hol4/mergesort.ml";;
needs "translator/std_prelude.ml";;
needs "basis/pure/mllist.ml";;
needs "translator/ml_translator.ml";;
needs "basis/OptionProg.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

translation_extends "OptionProg";;

ml_prog_update (ml_prog_open_module "List");;

(* HOL4 generate_sigs := true: module signatures are not generated (HOL4's  *)
(* generate_sig_thms makes TRUTH)                                            *)

ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [implode "'a"] (implode "list")
     (Atapp [Atvar (implode "'a")] (Short (implode "list")))` I);;

let _ = translate NULL;;

ml_prog_update ml_prog_open_local_block;;
let _ = translate LENGTH_AUX_def;;
ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["length"];;
let _ = translate LENGTH_AUX_THM;;

(* HOL4 listTheory REVERSE_REV *)
let BAS1AUX_REVERSE_REV = prove
 (`REVERSE (L:A list) = REV L []`,
  REWRITE_TAC[REV_REVERSE_LEM; APPEND_NIL]);;

ml_prog_update ml_prog_open_local_block;;
let _ = translate REV_DEF;;
let _ = translate map_rev'_def;;
let _ = translate filter_rev'_def;;
let _ = translate flat_rev'_def;;
ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["rev"];;
let _ = translate BAS1AUX_REVERSE_REV;;
next_ml_names := ["mapRev"];;
let _ = translate map_rev_def;;
next_ml_names := ["filterRev"];;
let _ = translate filter_rev_def;;
next_ml_names := ["flatRev"];;
let _ = translate flat_rev_def;;

(* New list-append translation *)
let append_v_thm = trans "@" `APPEND:A list->A list->A list`;;
let ListProg_List_append_def = tr_fetch "List_append_def";;

let _ = translate HD;;
let hd_side_def = update_precondition (prove
 (`!xs:A list. hd_side xs <=> ~(xs = [])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[tr_fetch "hd_side_def"; NOT_CONS_NIL] THEN
  MESON_TAC[]));;

let _ = translate TL;;

let _ = translate LAST_DEF;;

next_ml_names := ["getItem"];;
let _ = translate getItem_def;;

let nth_thm = prove
 (`nth (l:A list) 0 = HD l /\
   nth l (SUC n) = nth (TL l) n`,
  REWRITE_TAC[nth_def; EL]);;

let _ = translate nth_thm;;
let nth_side_def = tr_fetch "nth_side_def";;

let _ = translate (REWRITE_RULE [GSYM take_def] TAKE_def);;
let _ = translate (REWRITE_RULE [GSYM mllist_drop_def] DROP_def);;

next_ml_names := ["takeUntil"; "dropUntil"];;
let _ = translate takeUntil_def;;
let _ = translate dropUntil_def;;

next_ml_names := ["cmp"];;
let _ = translate list_compare_def;;

next_ml_names := ["concat"];;
let _ = translate FLAT;;

next_ml_names := ["intersperse"];;
let _ = translate intersperse_def;;

(* the let is introduced to produce slight better code (smaller stack frames) *)
let MAP_let = prove
 (CASE_TERM
  `MAP (f:A->B) xs =
     match xs with
       [] -> []
     | CONS y ys -> let z = f y in CONS z (MAP f ys)`,
  STRUCT_CASES_TAC (ISPEC `xs:A list` list_CASES) THEN
  REWRITE_TAC[MAP; list_CASE; LET_DEF; LET_END_DEF]);;

let MAP_ind = prove
 (`!P. (!(f:A->B) xs. (!y ys z. xs = CONS y ys /\ z = f y ==> P f ys) ==> P f xs) ==>
       !f xs. P f xs`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 add_preferred_thy "-": the translator finds MAP_ind above *)
add_ind_thm "MAP" MAP_ind;;

next_ml_names := ["map"];;
let _ = translate MAP_let;;

ml_prog_update ml_prog_open_local_block;;
let _ = translate mllist_mapi_def;;
ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["mapi"; "mapPartial"];;
let _ = translate MAPI_thm;;
let _ = translate mllist_mapPartial_def;;

add_cakeml_at (122,18) {|
  fun app f ls = case ls of [] => ()
    | (x::xs) => (f x; app f xs)
|};;

let _ = translate FIND_thm;;

let _ = translate FILTER;;

ml_prog_update ml_prog_open_local_block;;
let _ = translate partition_aux_def;;
ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["partition"];;
let _ = translate partition_def;;

let _ = translate mllist_foldl_def;;

ml_prog_update ml_prog_open_local_block;;
let _ = translate mllist_foldli_aux_def;;
ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["foldli"];;
let _ = translate mllist_foldli_def;;

let _ = translate FOLDR;;
next_ml_names := ["foldri"];;
let _ = translate (REWRITE_RULE [o_DEF] FOLDRi_def);;

let _ = translate EX;;

next_ml_names := ["all"];;
let _ = translate EVERY_DEF;;

let _ = translate SNOC;;

(* HOL4 listTheory GENLIST_AUX and GENLIST_GENLIST_AUX *)
let GENLIST_AUX = new_recursive_definition num_RECURSION
  `(GENLIST_AUX (f:num->A) 0 l = l) /\
   (GENLIST_AUX f (SUC n) l = GENLIST_AUX f n (CONS (f n) l))`;;

let GENLIST_GENLIST_AUX = prove
 (`!n. list_of_seq (f:num->A) n = GENLIST_AUX f n []`,
  SUBGOAL_THEN `!n (l1:A list) l2. APPEND (GENLIST_AUX (f:num->A) n l1) l2 =
                                   GENLIST_AUX f n (APPEND l1 l2)`
   ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[GENLIST_AUX; APPEND]; ALL_TAC] THEN
  INDUCT_TAC THEN REWRITE_TAC[list_of_seq; GENLIST_AUX] THEN
  ONCE_REWRITE_TAC[MESON[APPEND] `CONS (x:A) [] = APPEND [] [x]`] THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND]);;

ml_prog_update ml_prog_open_local_block;;

let _ = translate GENLIST_AUX;;

ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["genlist"];;
let _ = translate GENLIST_GENLIST_AUX;;

next_ml_names := ["tabulate"];;
let _ = translate tabulate_aux_def;;

(* tabulate_aux_inv_spec: CF specification, ListProg_part2.ml (M10) *)

next_ml_names := ["tabulate"];;
let _ = translate mllist_tabulate_def;;

(* tabulate_inv_spec: CF specification, ListProg_part2.ml (M10) *)

let _ = translate mllist_collate_def;;

(* HOL4's ZIP is uncurried and truncates; HOL Light's ZIP (CONS x l) [] is *)
(* unspecified: ZIP_ind and ZIP_eq are stated for the curried ZIP, and the  *)
(* translation of ZIP_eq has the precondition that the second list is not  *)
(* shorter than the first one (DEVIATIONS)                                  *)
let ZIP_ind = prove
 (`!P. (!(v1:A list) (v2:B list).
          (!x4 x3 x2 x1. v1 = CONS x4 x3 /\ v2 = CONS x2 x1 ==> P x3 x1) ==> P v1 v2) ==>
       !v1 v2. P v1 v2`,
  GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN
  ASM_MESON_TAC[]);;

let ZIP_eq = CONJUNCT2 ZIP_def;;

add_ind_thm "ZIP" ZIP_ind;;

let _ = translate ZIP_def;;

let _ = translate MEMBER_def;;

let _ = translate SUM;;

let UNZIP_eq = prove
 (CASE_TERM
  `!xs:(A#B)list.
     UNZIP xs =
       match xs with
         [] -> ([], [])
       | CONS (y,z) xs -> let (ys,zs) = UNZIP xs in (CONS y ys, CONS z zs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[UNZIP_DEF; MAP; list_CASE] THEN
  PAIR_CASES_ON `h:A#B` THEN REWRITE_TAC[pair_CASE; MAP; FST; SND] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CAKE_REWRITE_TAC[]);;

let UNZIP_ind = prove
 (`!P. (!v:(A#B)list. (!x4 x3. v = CONS x4 x3 ==> !x2 x1. x4 = (x2,x1) ==> P x3) ==> P v) ==>
       !v. P v`,
  GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[NOT_CONS_NIL; CONS_11] THEN
  ASM_MESON_TAC[]);;

add_ind_thm "UNZIP" UNZIP_ind;;

let _ = translate UNZIP_eq;;

let _ = translate (REWRITE_RULE [GSYM sub_check_def] PAD_RIGHT);;
let _ = translate (REWRITE_RULE [GSYM sub_check_def] PAD_LEFT);;
let _ = translate (REWRITE_RULE [MEMBER_INTRO] ALL_DISTINCT);;
next_ml_names := ["isPrefix"];;
let _ = translate isPREFIX;;
let _ = translate FRONT_DEF;;

next_ml_names := ["splitAtPki"];;
let _ = translate (REWRITE_RULE [SUC_LEMMA] splitAtPki_def);;

let SPLITP_alt = prove
 (CASE_TERM
  `SPLITP (P:A->bool) [] = ([],[]) /\
   SPLITP P (CONS x l) =
   if P x then ([],CONS x l) else
     let (l',l'') = SPLITP P l in
       (CONS x l',l'')`,
  REWRITE_TAC[SPLITP] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MP_TAC (ISPEC `SPLITP (P:A->bool) l` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[FST; SND] THEN CAKE_REWRITE_TAC[]);;
next_ml_names := ["split"];;
let _ = translate SPLITP_alt;;

let last_side_def = update_precondition (prove
 (`!xs:A list. last_side xs <=> ~(xs = [])`,
  LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC [tr_fetch "last_side_def"] THEN
  REWRITE_TAC[ml_CONTAINER_def; NOT_CONS_NIL; GSYM NOT_CONS_NIL; CONS_11] THEN
  ASM_MESON_TAC[]));;

let nth_side_def = update_precondition (prove
 (`!n xs:A list. nth_side xs n <=> n < LENGTH xs`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ONCE_REWRITE_TAC [tr_fetch "nth_side_def"] THEN
  REWRITE_TAC[ml_CONTAINER_def; LENGTH; LT_SUC; LT_0; NOT_SUC; NOT_CONS_NIL;
              GSYM NOT_CONS_NIL; TL; tr_fetch "tl_side_def"; CONS_11; SUC_SUB1;
              SUC_INJ; LT_REFL; LT; ARITH_RULE `1 <= SUC x`] THEN
  ASM_MESON_TAC[]));;

let LUPDATE_ind = prove
 (`!P. (!(e:A) (n:num). P e n ([]:A list)) /\
       (!e n x xs. (!e n. P e n xs) ==> P e n (CONS (x:A) xs)) ==>
       !e n xs. P e n xs`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!(xs:A list) (e:A) (n:num). P e n xs` (fun th -> REWRITE_TAC[th]) THEN
  LIST_INDUCT_TAC THEN ASM_MESON_TAC[]);;

let LUPDATE_eq = prove
 (CASE_TERM
  `LUPDATE (e:A) n xs =
     match xs with
       [] -> []
     | CONS y ys -> if n = 0 then CONS e ys else CONS y (LUPDATE e (n - 1) ys)`,
  STRUCT_CASES_TAC (ISPEC `xs:A list` list_CASES) THEN
  REWRITE_TAC[LUPDATE_DEF; list_CASE]);;

add_ind_thm "LUPDATE" LUPDATE_ind;;

next_ml_names := ["update"];;
let _ = translate LUPDATE_eq;;

next_ml_names := ["compare"];;
let _ = translate list_compare_def;;

ml_prog_update ml_prog_open_local_block;;

let _ = translate sort2_tail_def;;
let _ = translate sort3_tail_def;;
let _ = translate REV_DEF;;
let _ = translate merge_tail_def;;
let _ = translate DIV2_def;;
let _ = translate DROP_def;;
let _ = translate_no_ind LSORTAUX_mergesortN_tail_eqn;;

(* HOL4 fetch "-" "mergesortn_tail_ind_def": the definition of the induction *)
(* goal the translator left open (HOL4 hide_ind_goal_rule)                   *)
let mergesortn_tail_ind_def =
  try tr_fetch "mergesortn_tail_ind_def" with Failure _ ->
  find (fun th -> try fst (dest_const (lhs (concl th))) = "mergesortn_tail_ind"
                  with Failure _ -> false) (definitions ());;

let mergesortn_tail_ind = prove
 (`mergesortn_tail_ind (UNIV:A->bool)`,
  REWRITE_TAC[mergesortn_tail_ind_def] THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (latest_ind ()) THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th -> is_var (lhs (concl th)))) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[NOT_SUC]);;

let _ = update_precondition mergesortn_tail_ind;;

let mergesortn_tail_side = prove
 (`!w x y (z:A list). mergesortn_tail_side w x y z`,
  SUBGOAL_THEN `!y w x (z:A list). mergesortn_tail_side w x y z` (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `y:num` THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[tr_fetch "mergesortn_tail_side_def"] THEN X_GEN_TAC `x1:num` THEN
  DISCH_THEN SUBST_ALL_TAC THEN REPEAT DISCH_TAC THEN REWRITE_TAC[DIV2_def] THEN
  SUBGOAL_THEN `0 < SUC x1 DIV 2 /\ SUC x1 DIV 2 < SUC x1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `0 < n <=> 1 <= n`] THEN SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC DIV_LESS THEN ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM (MATCH_MP_TAC o REWRITE_RULE[RIGHT_IMP_FORALL_THM]) THEN ASM_ARITH_TAC;
    FIRST_ASSUM (MATCH_MP_TAC o REWRITE_RULE[RIGHT_IMP_FORALL_THM]) THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let _ = update_precondition mergesortn_tail_side;;
let _ = translate mergesort_tail_def;;

ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["sort"];;

let _ = translate sort_def;;

ml_prog_update ml_prog_close_local_blocks;;
ml_prog_update (ml_prog_close_module None);;

(* finite maps -- depend on lists *)

ml_prog_update (ml_prog_open_module "Alist");;

(* HOL4: FMAP_EQ_ALIST *)
let ListProg_FMAP_EQ_ALIST_def = new_definition
  `ListProg_FMAP_EQ_ALIST (f:(A,B)fmap) l <=> (ALOOKUP l = FLOOKUP f)`;;

(* HOL4: FMAP_TYPE *)
let ListProg_FMAP_TYPE_def = new_definition
  `ListProg_FMAP_TYPE (a:A->v->bool) (b:B->v->bool) (f:(A,B)fmap) =
     \v. ?l. LIST_TYPE (PAIR_TYPE a b) l v /\ ListProg_FMAP_EQ_ALIST f l`;;

add_type_inv `ListProg_FMAP_TYPE (a:A->v->bool) (b:B->v->bool)` `:(A#B)list`;;

next_ml_names := ["lookup"];;
let ALOOKUP_eval = translate ALOOKUP_def;;

let Eval_FLOOKUP = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. ((LIST_TYPE (PAIR_TYPE (b:B->v->bool) (a:A->v->bool)) -->
         b --> OPTION_TYPE a) ALOOKUP) v ==>
       ((ListProg_FMAP_TYPE b a --> b --> OPTION_TYPE a) FLOOKUP) v`,
  REWRITE_TAC[ml_Arrow_def; ml_AppReturns_def; ListProg_FMAP_TYPE_def;
              ListProg_FMAP_EQ_ALIST_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN MESON_TAC[])) ALOOKUP_eval);;

next_ml_names := ["update"];;
let AUPDATE_def = cake_def
  `AUPDATE l (x:A,y:B) = CONS (x,y) l`;;
let AUPDATE_eval = translate AUPDATE_def;;

let FMAP_EQ_ALIST_UPDATE = prove
 (`ListProg_FMAP_EQ_ALIST (f:(A,B)fmap) l ==>
   ListProg_FMAP_EQ_ALIST (f |+ (x,y)) (AUPDATE l (x,y))`,
  REWRITE_TAC[ListProg_FMAP_EQ_ALIST_def; AUPDATE_def; ALOOKUP_def; FUN_EQ_THM;
              FLOOKUP_UPDATE] THEN
  MESON_TAC[]);;

let Eval_FUPDATE = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. ((LIST_TYPE (PAIR_TYPE a b) -->
         PAIR_TYPE (a:A->v->bool) (b:B->v->bool) -->
         LIST_TYPE (PAIR_TYPE a b)) AUPDATE) v ==>
       ((ListProg_FMAP_TYPE a b --> PAIR_TYPE a b --> ListProg_FMAP_TYPE a b) FUPDATE) v`,
  REWRITE_TAC[ml_Arrow_def; ml_AppReturns_def; ListProg_FMAP_TYPE_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  MP_TAC (prove
   (`!(f:(A,B)fmap) l p. ListProg_FMAP_EQ_ALIST f l ==>
                        ListProg_FMAP_EQ_ALIST (f |+ p) (AUPDATE l p)`,
    REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[FMAP_EQ_ALIST_UPDATE])) THEN
  MESON_TAC[])) AUPDATE_eval);;

let NIL_eval = hol2deep `[]:(A#B)list`;;

(* HOL Light's matching instantiates Q of Eval_WEAKEN eta-expanded: ETA_CONV *)
let Eval_FEMPTY = add_eval_thm (CONV_RULE (RAND_CONV ETA_CONV)
 (MATCH_MP (MATCH_MP Eval_WEAKEN NIL_eval) (prove
 (`!v. (LIST_TYPE (PAIR_TYPE (a:A->v->bool) (b:B->v->bool)) []) v ==>
       ((ListProg_FMAP_TYPE a b) FEMPTY) v`,
  REWRITE_TAC[ListProg_FMAP_TYPE_def; ListProg_FMAP_EQ_ALIST_def] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `[]:(A#B)list` THEN
  ASM_REWRITE_TAC[ALOOKUP_def; FUN_EQ_THM; FLOOKUP_EMPTY]))));;

let AEVERY_AUX_def = cake_def
  `(AEVERY_AUX aux (P:A#B->bool) [] <=> T) /\
   (AEVERY_AUX aux P (CONS (x:A,y:B) xs) <=>
      if MEMBER x aux then AEVERY_AUX aux P xs else
        P (x,y) /\ AEVERY_AUX (CONS x aux) P xs)`;;
let AEVERY_def = new_definition
  `AEVERY = (AEVERY_AUX ([]:A list) :(A#B->bool)->(A#B)list->bool)`;;
next_ml_names := ["every"; "every"];;
let _ = translate AEVERY_AUX_def;;
let AEVERY_eval = translate AEVERY_def;;

let AEVERY_AUX_THM = prove
 (`!l aux (P:A#B->bool). AEVERY_AUX aux P l <=>
                         !x y. (ALOOKUP l x = SOME y) /\ ~(MEM x aux) ==> P (x,y)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[AEVERY_AUX_def; ALOOKUP_def; distinctness "option"] THEN
  PAIR_CASES_ON `h:A#B` THEN
  ASM_REWRITE_TAC[AEVERY_AUX_def; ALOOKUP_def; GSYM MEMBER_INTRO; MEM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN
  REPEAT (FIRST_X_ASSUM (MP_TAC o check (is_cond o lhs o concl))) THEN
  ASM_MESON_TAC[injectivity "option"]);;

let AEVERY_THM = prove
 (`AEVERY (P:A#B->bool) l <=> !x y. (ALOOKUP l x = SOME y) ==> P (x,y)`,
  REWRITE_TAC[AEVERY_def; AEVERY_AUX_THM; MEM]);;

let AEVERY_EQ_FEVERY = prove
 (`ListProg_FMAP_EQ_ALIST (f:(A,B)fmap) l ==> (AEVERY P l <=> FEVERY P f)`,
  REWRITE_TAC[ListProg_FMAP_EQ_ALIST_def; FEVERY_DEF; AEVERY_THM] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FLOOKUP_DEF] THEN
  MESON_TAC[injectivity "option"; distinctness "option"]);;

let Eval_FEVERY = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (((PAIR_TYPE (a:A->v->bool) (b:B->v->bool) --> ml_BOOL) -->
         LIST_TYPE (PAIR_TYPE a b) --> ml_BOOL) AEVERY) v ==>
       (((PAIR_TYPE (a:A->v->bool) (b:B->v->bool) --> ml_BOOL) -->
         ListProg_FMAP_TYPE a b --> ml_BOOL) FEVERY) v`,
  REWRITE_TAC[ml_Arrow_def; ml_AppReturns_def; ListProg_FMAP_TYPE_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (fun th -> FIRST_X_ASSUM (fun th2 ->
    STRIP_ASSUME_TAC (SPEC_ALL (MATCH_MP th th2)))) THEN
  MP_TAC (prove
   (`!P (f:(A,B)fmap) l u. ListProg_FMAP_EQ_ALIST f l ==>
       (ml_BOOL (AEVERY P l) u <=> ml_BOOL (FEVERY P f) u)`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM (fun th -> REWRITE_TAC[MATCH_MP AEVERY_EQ_FEVERY th]))) THEN
  ASM_MESON_TAC[])) AEVERY_eval);;

next_ml_names := ["map"];;
let AMAP_def = cake_def
  `(AMAP (f:B->C) [] = []) /\
   (AMAP f (CONS (x:A,y:B) xs) = CONS (x,f y) (AMAP f xs))`;;
let AMAP_eval = translate AMAP_def;;

let ALOOKUP_AMAP = prove
 (CASE_TERM
  `!l. ALOOKUP (AMAP (f:B->C) l) (a:A) =
       match ALOOKUP l a with NONE -> NONE | SOME x -> SOME (f x)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[AMAP_def; ALOOKUP_def; option_CASE] THEN
  PAIR_CASES_ON `h:A#B` THEN ASM_REWRITE_TAC[AMAP_def; ALOOKUP_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_CASE]);;

let FMAP_EQ_ALIST_o_f = prove
 (`ListProg_FMAP_EQ_ALIST (m:(A,B)fmap) l ==>
   ListProg_FMAP_EQ_ALIST ((x:B->C) o_f m) (AMAP x l)`,
  REWRITE_TAC[ListProg_FMAP_EQ_ALIST_def; FUN_EQ_THM; ALOOKUP_AMAP; FLOOKUP_o_f] THEN
  MESON_TAC[]);;

let ListProg_Eval_o_f = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (((b --> c) --> LIST_TYPE (PAIR_TYPE (a:A->v->bool) (b:B->v->bool)) -->
          LIST_TYPE (PAIR_TYPE a (c:C->v->bool))) AMAP) v ==>
       (((b --> c) --> ListProg_FMAP_TYPE a b --> ListProg_FMAP_TYPE a c) (o_f)) v`,
  REWRITE_TAC[ml_Arrow_def; ml_AppReturns_def; ListProg_FMAP_TYPE_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (fun th -> FIRST_X_ASSUM (fun th2 ->
    STRIP_ASSUME_TAC (SPEC_ALL (MATCH_MP th th2)))) THEN
  ASM_MESON_TAC[FMAP_EQ_ALIST_o_f])) AMAP_eval);;

(* TODO: quick fix on account of hol2deep not accepting APPEND (HOL4) *)
let append_eval =
  INST [`PAIR_TYPE (a:A->v->bool) (b:B->v->bool)`, `a:A#B->v->bool`]
       (INST_TYPE [`:A#B`,`:A`] append_v_thm);;

let Eval_FUNION = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. (LIST_TYPE (PAIR_TYPE a b) --> LIST_TYPE (PAIR_TYPE a b) -->
        LIST_TYPE (PAIR_TYPE (a:A->v->bool) (b:B->v->bool))) APPEND v ==>
       (ListProg_FMAP_TYPE a b --> ListProg_FMAP_TYPE a b --> ListProg_FMAP_TYPE a b)
         FUNION v`,
  REWRITE_TAC[ml_Arrow_def; ml_AppReturns_def; ListProg_FMAP_TYPE_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  MP_TAC (prove
   (`!(f1:(A,B)fmap) f2 l1 l2.
       ListProg_FMAP_EQ_ALIST f1 l1 /\ ListProg_FMAP_EQ_ALIST f2 l2 ==>
       ListProg_FMAP_EQ_ALIST (FUNION f1 f2) (APPEND l1 l2)`,
    REWRITE_TAC[ListProg_FMAP_EQ_ALIST_def; FUN_EQ_THM; ALOOKUP_APPEND;
                FLOOKUP_FUNION] THEN
    MESON_TAC[])) THEN
  MESON_TAC[])) append_eval);;

next_ml_names := ["delete"];;
let ADEL_def = cake_def
  `(ADEL [] (z:A) = ([]:(A#B)list)) /\
   (ADEL (CONS (x:A,y:B) xs) z = if x = z then ADEL xs z else CONS (x,y) (ADEL xs z))`;;
let ADEL_eval = translate ADEL_def;;

let ALOOKUP_ADEL = prove
 (`!l (a:A) x. ALOOKUP (ADEL l a) x = if x = a then NONE else ALOOKUP (l:(A#B)list) x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_def; ADEL_def; COND_ID] THEN
  PAIR_CASES_ON `h:A#B` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ALOOKUP_def; ADEL_def] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[ALOOKUP_def] THEN ASM_MESON_TAC[]);;

let FMAP_EQ_ALIST_ADEL = prove
 (`!x l. ListProg_FMAP_EQ_ALIST (x:(A,B)fmap) l ==>
         ListProg_FMAP_EQ_ALIST (x \\ a) (ADEL l a)`,
  REWRITE_TAC[ListProg_FMAP_EQ_ALIST_def; FUN_EQ_THM; ALOOKUP_ADEL;
              DOMSUB_FLOOKUP_THM] THEN
  MESON_TAC[]);;

let ListProg_Eval_fmap_domsub = add_user_proved_v_thm (MATCH_MP (prove
 (`!v. ((LIST_TYPE (PAIR_TYPE a b) --> a -->
         LIST_TYPE (PAIR_TYPE (a:A->v->bool) (b:B->v->bool))) ADEL) v ==>
       ((ListProg_FMAP_TYPE a b --> a --> ListProg_FMAP_TYPE a b) fdomsub) v`,
  REWRITE_TAC[ml_Arrow_def; ml_AppReturns_def; ListProg_FMAP_TYPE_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  MESON_TAC[FMAP_EQ_ALIST_ADEL])) ADEL_eval);;

ml_prog_update (ml_prog_close_module None);;

finalise_translation ();;
