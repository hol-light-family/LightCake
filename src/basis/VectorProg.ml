(* ========================================================================= *)
(* VectorProg: port of HOL4 basis/VectorProgScript.sml (CakeML v3479).       *)
(* Module about the built-in 'a vector.                                      *)
(* ========================================================================= *)

needs "hol4/regexp_compiler.ml";;
needs "translator/ml_translator.ml";;
needs "basis/ListProg.ml";;
needs "basis/pure/mlvector.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

(* HOL4's proofs Induct_on len, then rw with Once NAME_aux_side_def, of    *)
(* the side conditions of the index-recursive vector and string functions;  *)
(* the collate variant splits the conditional of its statement              *)
let BAS1AUX_SIDE_LEMMAS_TAC v side_def thl =
  HOL4_INDUCT_ON v THEN ONCE_REWRITE_TAC[side_def] THEN
  REWRITE_TAC[GSYM NOT_SUC; SUC_INJ; SUC_SUB1; ARITH_RULE `1 <= SUC x`] THEN
  REPEAT STRIP_TAC THEN
  TRY (FIRST_X_ASSUM (SUBST_ALL_TAC o SYM o check (fun th -> is_var (rhs (concl th))))) THEN
  TRY (FIRST_X_ASSUM MATCH_MP_TAC ORELSE MAP_FIRST MATCH_MP_TAC thl) THEN ASM_ARITH_TAC;;

let BAS1AUX_SIDE_TAC v side_def = BAS1AUX_SIDE_LEMMAS_TAC v side_def [];;

let BAS1AUX_COLLATE_SIDE_TAC v side_def =
  HOL4_INDUCT_ON v THEN ONCE_REWRITE_TAC[side_def] THEN
  REWRITE_TAC[GSYM NOT_SUC; SUC_INJ; SUC_SUB1; ARITH_RULE `1 <= SUC x`] THEN
  REPEAT STRIP_TAC THEN
  TRY (FIRST_X_ASSUM (SUBST_ALL_TAC o SYM o check (fun th -> is_var (rhs (concl th))))) THEN
  TRY (FIRST_X_ASSUM MATCH_MP_TAC) THEN
  REPEAT (FIRST_X_ASSUM (K ALL_TAC o check (is_forall o concl))) THEN
  REPEAT (POP_ASSUM MP_TAC) THEN COND_CASES_TAC THEN ASM_ARITH_TAC;;

translation_extends "ListProg";;

ml_prog_update (ml_prog_open_module "Vector");;

(* HOL4 generate_sigs := true: no signatures (see ListProg.ml) *)

ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [implode "'a"] (implode "vector")
     (Atapp [Atvar (implode "'a")] (Short (implode "vector")))` I);;

let _ = trans "fromList" `Vector:A list->A vector`;;
let Vector_fromList_def = tr_fetch "Vector_fromList_def";;
let _ = trans "length" `regexp_compiler_length:A vector->num`;;
let VectorProg_Vector_length_def = tr_fetch "Vector_length_def";;
let _ = trans "sub" `regexp_compiler_sub:A vector->num->A`;;
let VectorProg_Vector_sub_def = tr_fetch "Vector_sub_def";;

next_ml_names := ["tabulate"];;
let _ = translate mlvector_tabulate_def;;

ml_prog_update ml_prog_open_local_block;;
let _ = translate toList_aux_def;;
ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["toList"];;
let _ = translate mlvector_toList_def;;

next_ml_names := ["update"];;
let _ = translate update_def;;

next_ml_names := ["concat"];;
let _ = translate mlvector_concat_def;;

next_ml_names := ["map"];;
let _ = translate mlvector_map_def;;
next_ml_names := ["mapi"];;
let _ = translate mlvector_mapi_def;;

ml_prog_update ml_prog_open_local_block;;
let _ = translate mlvector_foldli_aux_def;;
let foldli_aux_side_def = tr_fetch "foldli_aux_side_def";;
ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["foldli"];;
let _ = translate mlvector_foldli_def;;
let foldli_side_def = tr_fetch "foldli_1_side_def";;

let foldli_aux_side_thm = prove
 (`!(f:num->A->B->B) e vec n len.
     n + len = regexp_compiler_length vec ==> foldli_aux_side f e vec n len`,
  BAS1AUX_SIDE_TAC "len" foldli_aux_side_def);;

let foldli_side_thm = update_precondition (prove
 (`!f e vec:A vector. foldli_1_side (f:num->A->B->B) e vec`,
  REWRITE_TAC[foldli_side_def] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC foldli_aux_side_thm THEN ARITH_TAC));;

ml_prog_update ml_prog_open_local_block;;
let _ = translate foldl_aux_def;;
let foldl_aux_side_def = tr_fetch "foldl_aux_side_def";;
ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["foldl"];;
let _ = translate mlvector_foldl_def;;
let foldl_side_def = tr_fetch "foldl_1_side_def";;

let foldl_aux_side_thm = prove
 (`!(f:B->A->B) e vec n len.
     n + len = regexp_compiler_length vec ==> foldl_aux_side f e vec n len`,
  BAS1AUX_SIDE_TAC "len" foldl_aux_side_def);;

let foldl_side_thm = update_precondition (prove
 (`!f e vec:A vector. foldl_1_side (f:B->A->B) e vec`,
  REWRITE_TAC[foldl_side_def] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC foldl_aux_side_thm THEN ARITH_TAC));;

ml_prog_update ml_prog_open_local_block;;
let _ = translate foldri_aux_def;;
let foldri_aux_side_def = tr_fetch "foldri_aux_side_def";;
ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["foldri"];;
let _ = translate foldri_def;;
let foldri_side_def = tr_fetch "foldri_1_side_def";;

let foldri_aux_side_thm = prove
 (`!(f:num->A->B->B) e vec len.
     len <= regexp_compiler_length vec ==> foldri_aux_side f e vec len`,
  BAS1AUX_SIDE_TAC "len" foldri_aux_side_def);;

let foldri_side_thm = update_precondition (prove
 (`!f e vec:A vector. foldri_1_side (f:num->A->B->B) e vec`,
  REWRITE_TAC[foldri_side_def] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC foldri_aux_side_thm THEN ARITH_TAC));;

ml_prog_update ml_prog_open_local_block;;
let _ = translate foldr_aux_def;;
let foldr_aux_side_def = tr_fetch "foldr_aux_side_def";;
ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["foldr"];;
let _ = translate foldr_def;;
let foldr_side_def = tr_fetch "foldr_1_side_def";;

let foldr_aux_side_thm = prove
 (`!(f:A->B->B) e vec len.
     len <= regexp_compiler_length vec ==> foldr_aux_side f e vec len`,
  BAS1AUX_SIDE_TAC "len" foldr_aux_side_def);;

let foldr_side_thm = update_precondition (prove
 (`!f e vec:A vector. foldr_1_side (f:A->B->B) e vec`,
  REWRITE_TAC[foldr_side_def] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC foldr_aux_side_thm THEN ARITH_TAC));;

ml_prog_update ml_prog_open_local_block;;
let _ = translate findi_aux_def;;
let findi_aux_side_def = tr_fetch "findi_aux_side_def";;
ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["findi"];;
let _ = translate mlvector_findi_def;;
let findi_side_def = tr_fetch "findi_side_def";;

let findi_aux_side_thm = prove
 (`!(f:num->A->bool) vec n len.
     n + len = regexp_compiler_length vec ==> findi_aux_side f vec n len`,
  BAS1AUX_SIDE_TAC "len" findi_aux_side_def);;

let findi_side_thm = update_precondition (prove
 (`!f vec:A vector. findi_side (f:num->A->bool) vec`,
  REWRITE_TAC[findi_side_def] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC findi_aux_side_thm THEN ARITH_TAC));;

ml_prog_update ml_prog_open_local_block;;
let _ = translate find_aux_def;;
let find_aux_side_def = tr_fetch "find_aux_side_def";;
ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["find"];;
let _ = translate find_def;;
let find_side_def = tr_fetch "find_1_side_def";;

let find_aux_side_thm = prove
 (`!(f:A->bool) vec n len.
     n + len = regexp_compiler_length vec ==> find_aux_side f vec n len`,
  BAS1AUX_SIDE_TAC "len" find_aux_side_def);;

let find_side_thm = update_precondition (prove
 (`!f vec:A vector. find_1_side (f:A->bool) vec`,
  REWRITE_TAC[find_side_def] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC find_aux_side_thm THEN ARITH_TAC));;

ml_prog_update ml_prog_open_local_block;;
let _ = translate exists_aux_def;;
let exists_aux_side_def = tr_fetch "exists_aux_side_def";;
ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["exists"];;
let _ = translate mlvector_exists_def;;
let exists_side_def = tr_fetch "exists_1_side_def";;

let exists_aux_side_thm = prove
 (`!(f:A->bool) vec n len.
     n + len = regexp_compiler_length vec ==> exists_aux_side f vec n len`,
  BAS1AUX_SIDE_TAC "len" exists_aux_side_def);;

let exists_side_thm = update_precondition (prove
 (`!f vec:A vector. exists_1_side (f:A->bool) vec`,
  REWRITE_TAC[exists_side_def] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC exists_aux_side_thm THEN ARITH_TAC));;

ml_prog_update ml_prog_open_local_block;;
let _ = translate all_aux_def;;
let all_aux_side_def = tr_fetch "all_aux_side_def";;
ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["all"];;
let _ = translate mlvector_all_def;;
let all_side_def = tr_fetch "all_1_side_def";;

let all_aux_side_thm = prove
 (`!(f:A->bool) vec n len.
     n + len = regexp_compiler_length vec ==> all_aux_side f vec n len`,
  BAS1AUX_SIDE_TAC "len" all_aux_side_def);;

let all_side_thm = update_precondition (prove
 (`!f vec:A vector. all_1_side (f:A->bool) vec`,
  REWRITE_TAC[all_side_def] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC all_aux_side_thm THEN ARITH_TAC));;

ml_prog_update ml_prog_open_local_block;;
let _ = translate mlvector_collate_aux_def;;
let collate_aux_side_def = tr_fetch "collate_aux_side_def";;
ml_prog_update ml_prog_open_local_in_block;;

next_ml_names := ["collate"];;
let _ = translate mlvector_collate_def;;
let collate_side_def = tr_fetch "collate_1_side_def";;

let VectorProg_collate_aux_side_thm = prove
 (`!(f:A->B->ordering) vec1 vec2 n ord len.
     n + len = (if regexp_compiler_length vec1 < regexp_compiler_length vec2
                then regexp_compiler_length vec1 else regexp_compiler_length vec2) ==>
     collate_aux_side f vec1 vec2 n ord len`,
  BAS1AUX_COLLATE_SIDE_TAC "len" collate_aux_side_def);;

let collate_side_thm = update_precondition (prove
 (`!f vec1 vec2. collate_1_side (f:A->B->ordering) vec1 vec2`,
  REWRITE_TAC[collate_side_def] THEN REPEAT GEN_TAC THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC VectorProg_collate_aux_side_thm THEN ASM_ARITH_TAC));;

ml_prog_update ml_prog_close_local_blocks;;
ml_prog_update (ml_prog_close_module None);;

finalise_translation ();;
