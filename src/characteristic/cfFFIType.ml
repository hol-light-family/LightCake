(* ========================================================================= *)
(* cfFFIType: port of HOL4 characteristic/cfFFITypeScript.sml (CakeML v3479).*)
(* Defines a type that can be used for embedding different FFI models for   *)
(* parts of the FFI state.                                                   *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;
needs "hol4/llist.ml";;

type_invention_error := true;;

(* This file defines a type that behaves like the following one:            *)
(*                                                                           *)
(*   ffi = Str mlstring                                                      *)
(*       | Num num                                                           *)
(*       | Cons ffi ffi                                                      *)
(*       | List (ffi list)                                                   *)
(*       | Stream (num llist)                                                *)
(*       | Fun (ffi_inner -> ffi)                                            *)
(*       | Inner ffi_inner                                                   *)
(*                                                                           *)
(*   ffi_inner = iStr mlstring                                               *)
(*             | iNum num                                                    *)
(*             | iCons ffi_inner ffi_inner                                   *)
(*             | iList (ffi_inner list)                                      *)
(*             | iStream (num llist)                                         *)
(*                                                                           *)
(* The ffi type is missing an nchotomy thm and an induction thm, but the     *)
(* important injectivity (suffix: "_11") are here.                           *)
(*                                                                           *)
(* Names (doc/names.tsv): the ffi value functions Num, Str, Cons,            *)
(* List, Stream, Fun and Inner are cf_Num, cf_Str, cf_Cons, cf_List,         *)
(* cf_Stream, cf_Fun and cf_Inner, their theorems cf_Num_def, cf_Num_11, ... *)
(* HOL4 deletes ffi_app, ffi_app_def and the definitions Num_def, ... at the *)
(* end of the script; HOL Light cannot delete them, so they stay.            *)
(* HOL4's ffi_distinct (restated below with HOL4's name) has no kit-derived  *)
(* counterpart: ffi has one constructor, so neither the kit nor HOL Light    *)
(* makes a distinctness theorem for it.                                      *)

let ffi_inner_INDUCT,ffi_inner_RECURSION = cake_type
  "ffi_inner = iStr mlstring
             | iNum num
             | iCons ffi_inner ffi_inner
             | iList (ffi_inner list)
             | iStream (num llist)";;

let ffi_INDUCT,ffi_RECURSION = cake_type
  "ffi = FFI_TYPE (ffi_inner -> ffi_inner)";;

let ffi_app_def = cake_def
  `ffi_app x (n:ffi_inner) = match x with FFI_TYPE f -> f n`;;

(* constructors *)

let cf_Num_def = cake_def
  `cf_Num i = FFI_TYPE (\n. if n = iNum 0 then iNum 0 else iNum i)`;;

let cf_Str_def = cake_def
  `cf_Str i = FFI_TYPE (\n. if n = iNum 0 then iNum 1 else iStr i)`;;

let cf_Cons_def = cake_def
  `cf_Cons (x:ffi) (y:ffi) =
     FFI_TYPE (\n. if n = iNum 0 then iNum 2 else
                     match n with
                       iCons (iNum 0) m -> ffi_app x m
                     | iCons (iNum 1) m -> ffi_app y m
                     | _ -> iNum 0)`;;

let cf_List_def = cake_def
  `cf_List (xs:ffi list) =
     FFI_TYPE (\n. if n = iNum 0 then iNum 3 else
                   if n = iNum 1 then iNum (LENGTH xs) else
                     match n with
                       iCons (iNum k) m -> ffi_app (EL k xs) m
                     | _ -> iNum 0)`;;

let cf_Stream_def = cake_def
  `cf_Stream i = FFI_TYPE (\n. if n = iNum 0 then iNum 4 else iStream i)`;;

let cf_Fun_def = cake_def
  `cf_Fun (f:ffi_inner -> ffi) =
     FFI_TYPE (\n. if n = iNum 0 then iNum 5 else
                     match n with
                       iCons x y -> ffi_app (f x) y
                     | _ -> iNum 0)`;;

let cf_Inner_def = cake_def
  `cf_Inner i = FFI_TYPE (\n. if n = iNum 0 then iNum 6 else i)`;;

(* injectivity *)

(* helper: an ffi value is determined by its ffi_app function *)
let CF1AUX_ffi_app_ext = prove
 (`!x y. (!m. ffi_app x m = ffi_app y m) ==> x = y`,
  REPEAT GEN_TAC THEN QCASES_ON "x" THEN QCASES_ON "y" THEN
  SIMP[ffi_app_def; FUN_EQ_THM]);;

let cf_Num_11 = prove
 (`!n1 n2. cf_Num n1 = cf_Num n2 <=> n1 = n2`,
  FS[cf_Num_def; FUN_EQ_THM] THEN RW[] THEN EQ_TAC THEN RW[] THEN
  POP_ASSUM (QSPEC_THEN "iNum 1" MP_TAC) THEN FS[]);;
let _ = cake_add_simps [cf_Num_11];;

let cf_Str_11 = prove
 (`!n1 n2. cf_Str n1 = cf_Str n2 <=> n1 = n2`,
  FS[cf_Str_def; FUN_EQ_THM] THEN RW[] THEN EQ_TAC THEN RW[] THEN
  POP_ASSUM (QSPEC_THEN "iNum 1" MP_TAC) THEN FS[]);;
let _ = cake_add_simps [cf_Str_11];;

let cf_Cons_11 = prove
 (`!x1 x2 y1 y2. cf_Cons x1 x2 = cf_Cons y1 y2 <=> x1 = y1 /\ x2 = y2`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP[] THEN
  SIMP[cf_Cons_def; FUN_EQ_THM] THEN DISCH_TAC THEN
  CONJ_TAC THEN MATCH_MP_TAC CF1AUX_ffi_app_ext THEN X_GEN_TAC `m:ffi_inner` THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `iCons (iNum 0) m`);
    FIRST_X_ASSUM (MP_TAC o SPEC `iCons (iNum 1) m`)] THEN
  SIMP[]);;
let _ = cake_add_simps [cf_Cons_11];;

let cf_List_11 = prove
 (`!xs ys. cf_List xs = cf_List ys <=> xs = ys`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP[] THEN
  SIMP[cf_List_def; FUN_EQ_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[LIST_EQ] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `iNum 1`) THEN SIMP[];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN MATCH_MP_TAC CF1AUX_ffi_app_ext THEN
    X_GEN_TAC `m:ffi_inner` THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `iCons (iNum k) m`) THEN SIMP[]]);;
let _ = cake_add_simps [cf_List_11];;

let cf_Stream_11 = prove
 (`!n1 n2. cf_Stream n1 = cf_Stream n2 <=> n1 = n2`,
  FS[cf_Stream_def; FUN_EQ_THM] THEN RW[] THEN EQ_TAC THEN RW[] THEN
  POP_ASSUM (QSPEC_THEN "iNum 1" MP_TAC) THEN FS[]);;
let _ = cake_add_simps [cf_Stream_11];;

let cf_Fun_11 = prove
 (`cf_Fun f1 = cf_Fun f2 <=> f1 = f2`,
  EQ_TAC THEN SIMP[] THEN SIMP[cf_Fun_def; FUN_EQ_THM] THEN DISCH_TAC THEN
  X_GEN_TAC `x:ffi_inner` THEN MATCH_MP_TAC CF1AUX_ffi_app_ext THEN
  X_GEN_TAC `y:ffi_inner` THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `iCons x y`) THEN SIMP[]);;
let _ = cake_add_simps [cf_Fun_11];;

let cf_Inner_11 = prove
 (`!n1 n2. cf_Inner n1 = cf_Inner n2 <=> n1 = n2`,
  FS[cf_Inner_def; FUN_EQ_THM] THEN RW[] THEN EQ_TAC THEN RW[] THEN
  POP_ASSUM (QSPEC_THEN "iNum 1" MP_TAC) THEN FS[]);;
let _ = cake_add_simps [cf_Inner_11];;

(* distinctness *)

(* helper: the tag of each kind of ffi value *)
let CF1AUX_ffi_tags = prove
 (`(!n. ffi_app (cf_Num n) (iNum 0) = iNum 0) /\
   (!s. ffi_app (cf_Str s) (iNum 0) = iNum 1) /\
   (!x y. ffi_app (cf_Cons x y) (iNum 0) = iNum 2) /\
   (!l. ffi_app (cf_List l) (iNum 0) = iNum 3) /\
   (!ll. ffi_app (cf_Stream ll) (iNum 0) = iNum 4) /\
   (!f. ffi_app (cf_Fun f) (iNum 0) = iNum 5) /\
   (!i. ffi_app (cf_Inner i) (iNum 0) = iNum 6)`,
  SIMP[ffi_app_def; cf_Num_def; cf_Str_def; cf_Cons_def; cf_List_def;
       cf_Stream_def; cf_Fun_def; cf_Inner_def]);;

(* HOL4: ALL_DISTINCT [Num n; Str s; Cons x y; List l; Stream ll; Fun f;     *)
(* Inner i] simplified with ALL_DISTINCT, MEM, GSYM CONJ_ASSOC and GEN_ALL'd *)
let ffi_distinct = prove
 (`!n s x y l ll f i.
     ~(cf_Num n = cf_Str s) /\ ~(cf_Num n = cf_Cons x y) /\
     ~(cf_Num n = cf_List l) /\ ~(cf_Num n = cf_Stream ll) /\
     ~(cf_Num n = cf_Fun f) /\ ~(cf_Num n = cf_Inner i) /\
     ~(cf_Str s = cf_Cons x y) /\ ~(cf_Str s = cf_List l) /\
     ~(cf_Str s = cf_Stream ll) /\ ~(cf_Str s = cf_Fun f) /\
     ~(cf_Str s = cf_Inner i) /\ ~(cf_Cons x y = cf_List l) /\
     ~(cf_Cons x y = cf_Stream ll) /\ ~(cf_Cons x y = cf_Fun f) /\
     ~(cf_Cons x y = cf_Inner i) /\ ~(cf_List l = cf_Stream ll) /\
     ~(cf_List l = cf_Fun f) /\ ~(cf_List l = cf_Inner i) /\
     ~(cf_Stream ll = cf_Fun f) /\ ~(cf_Stream ll = cf_Inner i) /\
     ~(cf_Fun f = cf_Inner i)`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN
  DISCH_THEN(MP_TAC o C AP_THM `iNum 0` o AP_TERM `ffi_app`) THEN
  SIMP[CF1AUX_ffi_tags]);;
let _ = cake_add_simps [ffi_distinct];;

(* destructors *)

(* helper: the pair with given components *)
let CF1AUX_FST_SND_EQ = prove
 (`!(n:A#B) x y. FST n = x /\ SND n = y <=> n = (x,y)`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ]);;

let CF1AUX_DEST_TAC =
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN BETA_TAC THEN
  SIMP[CF1AUX_ffi_tags; cf_Num_11; cf_Str_11; cf_Cons_11; cf_List_11;
       cf_Stream_11; cf_Fun_11; cf_Inner_11; CF1AUX_FST_SND_EQ; SELECT_REFL];;

let destNum_exists = prove
 (`?destNum.
     (!n. destNum (cf_Num n) = SOME n) /\
     (!s. destNum (cf_Str s) = NONE) /\
     (!x y. destNum (cf_Cons x y) = NONE) /\
     (!l. destNum (cf_List l) = NONE) /\
     (!ll. destNum (cf_Stream ll) = NONE) /\
     (!f. destNum (cf_Fun f) = NONE) /\
     (!i. destNum (cf_Inner i) = NONE)`,
  EXISTS_TAC `\f. if ffi_app f (iNum 0) = iNum 0
                  then SOME (@n. cf_Num n = f) else NONE` THEN
  CF1AUX_DEST_TAC);;

let destNum_def = new_specification ["destNum"] destNum_exists;;
let _ = cake_add_simps [destNum_def];;

let destStr_exists = prove
 (`?destStr.
     (!n. destStr (cf_Num n) = NONE) /\
     (!s. destStr (cf_Str s) = SOME s) /\
     (!x y. destStr (cf_Cons x y) = NONE) /\
     (!l. destStr (cf_List l) = NONE) /\
     (!ll. destStr (cf_Stream ll) = NONE) /\
     (!f. destStr (cf_Fun f) = NONE) /\
     (!i. destStr (cf_Inner i) = NONE)`,
  EXISTS_TAC `\f. if ffi_app f (iNum 0) = iNum 1
                  then SOME (@n. cf_Str n = f) else NONE` THEN
  CF1AUX_DEST_TAC);;

let destStr_def = new_specification ["destStr"] destStr_exists;;
let _ = cake_add_simps [destStr_def];;

let destStr_o_Str = prove
 (`destStr o cf_Str = SOME`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; destStr_def]);;
let _ = cake_add_simps [destStr_o_Str];;

let destCons_exists = prove
 (`?destCons.
     (!n. destCons (cf_Num n) = NONE) /\
     (!s. destCons (cf_Str s) = NONE) /\
     (!x y. destCons (cf_Cons x y) = SOME (x,y)) /\
     (!l. destCons (cf_List l) = NONE) /\
     (!ll. destCons (cf_Stream ll) = NONE) /\
     (!f. destCons (cf_Fun f) = NONE) /\
     (!i. destCons (cf_Inner i) = NONE)`,
  EXISTS_TAC `\f. if ffi_app f (iNum 0) = iNum 2
                  then SOME (@n. cf_Cons (FST n) (SND n) = f) else NONE` THEN
  CF1AUX_DEST_TAC);;

let destCons_def = new_specification ["destCons"] destCons_exists;;
let _ = cake_add_simps [destCons_def];;

let destList_exists = prove
 (`?destList.
     (!n. destList (cf_Num n) = NONE) /\
     (!s. destList (cf_Str s) = NONE) /\
     (!x y. destList (cf_Cons x y) = NONE) /\
     (!l. destList (cf_List l) = SOME l) /\
     (!ll. destList (cf_Stream ll) = NONE) /\
     (!f. destList (cf_Fun f) = NONE) /\
     (!i. destList (cf_Inner i) = NONE)`,
  EXISTS_TAC `\f. if ffi_app f (iNum 0) = iNum 3
                  then SOME (@n. cf_List n = f) else NONE` THEN
  CF1AUX_DEST_TAC);;

let destList_def = new_specification ["destList"] destList_exists;;
let _ = cake_add_simps [destList_def];;

let destStream_exists = prove
 (`?destStream.
     (!n. destStream (cf_Num n) = NONE) /\
     (!s. destStream (cf_Str s) = NONE) /\
     (!x y. destStream (cf_Cons x y) = NONE) /\
     (!l. destStream (cf_List l) = NONE) /\
     (!ll. destStream (cf_Stream ll) = SOME ll) /\
     (!f. destStream (cf_Fun f) = NONE) /\
     (!i. destStream (cf_Inner i) = NONE)`,
  EXISTS_TAC `\f. if ffi_app f (iNum 0) = iNum 4
                  then SOME (@n. cf_Stream n = f) else NONE` THEN
  CF1AUX_DEST_TAC);;

let destStream_def = new_specification ["destStream"] destStream_exists;;
let _ = cake_add_simps [destStream_def];;

let destFun_exists = prove
 (`?destFun.
     (!n. destFun (cf_Num n) = NONE) /\
     (!s. destFun (cf_Str s) = NONE) /\
     (!x y. destFun (cf_Cons x y) = NONE) /\
     (!l. destFun (cf_List l) = NONE) /\
     (!ll. destFun (cf_Stream ll) = NONE) /\
     (!f. destFun (cf_Fun f) = SOME f) /\
     (!i. destFun (cf_Inner i) = NONE)`,
  EXISTS_TAC `\f. if ffi_app f (iNum 0) = iNum 5
                  then SOME (@n. cf_Fun n = f) else NONE` THEN
  CF1AUX_DEST_TAC);;

let destFun_def = new_specification ["destFun"] destFun_exists;;
let _ = cake_add_simps [destFun_def];;

let destInner_exists = prove
 (`?destInner.
     (!n. destInner (cf_Num n) = NONE) /\
     (!s. destInner (cf_Str s) = NONE) /\
     (!x y. destInner (cf_Cons x y) = NONE) /\
     (!l. destInner (cf_List l) = NONE) /\
     (!ll. destInner (cf_Stream ll) = NONE) /\
     (!f. destInner (cf_Fun f) = NONE) /\
     (!i. destInner (cf_Inner i) = SOME i)`,
  EXISTS_TAC `\f. if ffi_app f (iNum 0) = iNum 6
                  then SOME (@n. cf_Inner n = f) else NONE` THEN
  CF1AUX_DEST_TAC);;

let destInner_def = new_specification ["destInner"] destInner_exists;;
let _ = cake_add_simps [destInner_def];;

(* HOL4: a partial definition (the other constructors give ARB) *)
let dest_iStr_def = cake_def
  `dest_iStr (iStr s) = s`;;
let _ = cake_add_simps [dest_iStr_def];;
