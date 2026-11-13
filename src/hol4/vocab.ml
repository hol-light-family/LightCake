(* ========================================================================= *)
(* The HOL4 library vocabulary that CakeML uses and HOL Light lacks:         *)
(* definitions only (the theorems are in the other files of src/hol4/).      *)
(*                                                                           *)
(* Where HOL Light already has a constant with the same meaning, the port   *)
(* uses HOL Light's (notes/survey/hol4lib_refs.tsv, column hol_light):       *)
(*   EVERY = ALL   EXISTS = EX   LIST_REL = EVERY2 = ALL2   FRONT = BUTLAST  *)
(*   set = LIST_TO_SET = set_of_list   BIGUNION = UNIONS   LEAST = minimal   *)
(*   GENLIST f n = list_of_seq f n   FUNPOW f n x = ITER n f x               *)
(*   FOLDR f e l = ITLIST f l e   ZIP (l1,l2) = ZIP l1 l2 (curried; equal    *)
(*   lengths)   x NOTIN s = ~(x IN s)   flip = C of HOL4 combin.            *)
(* ========================================================================= *)

needs "kit/kit.ml";;

(* ------------------------------------------------------------------------- *)
(* combin                                                                    *)
(* ------------------------------------------------------------------------- *)

let flip_DEF = new_definition
  `flip (f:A->B->C) x y = f y x`;;

parse_as_infix("=+",(14,"right"));;

let UPDATE_DEF = new_definition
  `((a:A) =+ (b:B)) = \f c. if a = c then b else f c`;;

let APPLY_UPDATE_THM = prove
 (`!(a:A) (b:B) f c. (a =+ b) f c = if a = c then b else f c`,
  REWRITE_TAC[UPDATE_DEF]);;

(* ------------------------------------------------------------------------- *)
(* option                                                                    *)
(* ------------------------------------------------------------------------- *)

let THE_DEF = new_recursive_definition option_RECURSION
  `THE (SOME (x:A)) = x`;;

let IS_SOME_DEF = new_recursive_definition option_RECURSION
  `(IS_SOME (NONE:A option) <=> F) /\ (IS_SOME (SOME (x:A)) <=> T)`;;

let IS_NONE_DEF = new_recursive_definition option_RECURSION
  `(IS_NONE (NONE:A option) <=> T) /\ (IS_NONE (SOME (x:A)) <=> F)`;;

let OPTION_MAP_DEF = new_recursive_definition option_RECURSION
  `(OPTION_MAP (f:A->B) NONE = NONE) /\
   (OPTION_MAP f (SOME x) = SOME (f x))`;;

let OPTION_BIND_DEF = new_recursive_definition option_RECURSION
  `(OPTION_BIND (NONE:A option) (f:A->B option) = NONE) /\
   (OPTION_BIND (SOME x) f = f x)`;;

let OPTION_IGNORE_BIND_DEF = new_definition
  `OPTION_IGNORE_BIND (m1:A option) (m2:B option) = OPTION_BIND m1 (\x. m2)`;;

let OPTION_GUARD_DEF = new_definition
  `OPTION_GUARD b = if b then SOME one else NONE`;;

let OPTION_MAP2_DEF = new_definition
  `OPTION_MAP2 (f:A->B->C) x y =
     if IS_SOME x /\ IS_SOME y then SOME (f (THE x) (THE y)) else NONE`;;

let OPTION_JOIN_DEF = new_recursive_definition option_RECURSION
  `(OPTION_JOIN (NONE:(A option) option) = NONE) /\
   (OPTION_JOIN (SOME x) = x)`;;

let OPTION_CHOICE_DEF = new_recursive_definition option_RECURSION
  `(OPTION_CHOICE (NONE:A option) y = y) /\
   (OPTION_CHOICE (SOME x) y = SOME x)`;;

let OPTION_APPLY_DEF = new_recursive_definition option_RECURSION
  `(OPTION_APPLY (NONE:(A->B) option) x = NONE) /\
   (OPTION_APPLY (SOME f) x = OPTION_MAP f x)`;;

let OPTREL_DEF = new_definition
  `OPTREL (R:A->B->bool) x y <=>
     (x = NONE /\ y = NONE) \/ (?x0 y0. x = SOME x0 /\ y = SOME y0 /\ R x0 y0)`;;

(* HOL4's binder some: some x. P x *)

let some_DEF = new_definition
  `some (P:A->bool) = if ?x. P x then SOME (@x. P x) else NONE`;;

parse_as_binder "some";;

let lift2_DEF = new_definition
  `lift2 (f:A->B->C) x y =
     option_CASE x NONE (\a. option_CASE y NONE (\b. SOME (f a b)))`;;

(* ------------------------------------------------------------------------- *)
(* pair                                                                      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("##",(20,"right"));;

let PAIR_MAP_DEF = new_definition
  `((f:A->C) ## (g:B->D)) = \p. (f (FST p), g (SND p))`;;

let PAIR_MAP_THM = prove
 (`!(f:A->C) (g:B->D) x y. (f ## g) (x,y) = (f x, g y)`,
  REWRITE_TAC[PAIR_MAP_DEF]);;

(* ------------------------------------------------------------------------- *)
(* list and rich_list                                                        *)
(* ------------------------------------------------------------------------- *)

let TAKE_DEF = new_recursive_definition list_RECURSION
  `(TAKE n ([]:A list) = []) /\
   (TAKE n (CONS (x:A) xs) = if n = 0 then [] else CONS x (TAKE (n - 1) xs))`;;

let DROP_DEF = new_recursive_definition list_RECURSION
  `(DROP n ([]:A list) = []) /\
   (DROP n (CONS (x:A) xs) = if n = 0 then CONS x xs else DROP (n - 1) xs)`;;

let LUPDATE_DEF = new_recursive_definition list_RECURSION
  `(LUPDATE (e:A) n [] = []) /\
   (LUPDATE e n (CONS x l) =
      if n = 0 then CONS e l else CONS x (LUPDATE e (n - 1) l))`;;

let ALL_DISTINCT = new_recursive_definition list_RECURSION
  `(ALL_DISTINCT ([]:A list) <=> T) /\
   (ALL_DISTINCT (CONS (h:A) t) <=> ~MEM h t /\ ALL_DISTINCT t)`;;

let SUM = new_recursive_definition list_RECURSION
  `(SUM [] = 0) /\ (SUM (CONS h t) = h + SUM t)`;;

let FLAT = new_recursive_definition list_RECURSION
  `(FLAT ([]:(A list) list) = []) /\ (FLAT (CONS h t) = APPEND h (FLAT t))`;;

let SNOC = new_recursive_definition list_RECURSION
  `(SNOC (x:A) [] = [x]) /\ (SNOC x (CONS h t) = CONS h (SNOC x t))`;;

let FOLDL = new_recursive_definition list_RECURSION
  `(FOLDL (f:B->A->B) e [] = e) /\
   (FOLDL f e (CONS x l) = FOLDL f (f e x) l)`;;

let oEL_DEF = new_recursive_definition list_RECURSION
  `(oEL n ([]:A list) = NONE) /\
   (oEL n (CONS x xs) = if n = 0 then SOME x else oEL (n - 1) xs)`;;

let oHD_DEF = new_recursive_definition list_RECURSION
  `(oHD ([]:A list) = NONE) /\ (oHD (CONS (h:A) t) = SOME h)`;;

let isPREFIX = new_recursive_definition list_RECURSION
  `(isPREFIX ([]:A list) l <=> T) /\
   (isPREFIX (CONS h t) l <=>
      list_CASE l F (\h' t'. h = h' /\ isPREFIX t t'))`;;

parse_as_infix("<<=",(12,"right"));;
override_interface("<<=",`isPREFIX:A list->A list->bool`);;

let IS_PREFIX_DEF = new_definition
  `IS_PREFIX (l1:A list) l2 <=> isPREFIX l2 l1`;;

let IS_SUFFIX_DEF = new_definition
  `IS_SUFFIX (l1:A list) l2 <=> isPREFIX (REVERSE l2) (REVERSE l1)`;;

let IS_SUBLIST_DEF = new_definition
  `IS_SUBLIST (l1:A list) l2 <=> ?l l'. l1 = APPEND l (APPEND l2 l')`;;

let nub_DEF = new_recursive_definition list_RECURSION
  `(nub ([]:A list) = []) /\
   (nub (CONS x l) = if MEM x l then nub l else CONS x (nub l))`;;

let LIST_BIND_DEF = new_definition
  `LIST_BIND (l:A list) (f:A->B list) = FLAT (MAP f l)`;;

let MAPi_DEF = new_recursive_definition list_RECURSION
  `(MAPi (f:num->A->B) [] = []) /\
   (MAPi f (CONS h t) = CONS (f 0 h) (MAPi (f o SUC) t))`;;

let COUNT_LIST_DEF = new_recursive_definition num_RECURSION
  `(COUNT_LIST 0 = []) /\
   (COUNT_LIST (SUC n) = CONS 0 (MAP SUC (COUNT_LIST n)))`;;

let LASTN_DEF = new_definition
  `LASTN n (l:A list) = REVERSE (TAKE n (REVERSE l))`;;

let BUTLASTN_DEF = new_definition
  `BUTLASTN n (l:A list) = REVERSE (DROP n (REVERSE l))`;;

let SEG_DEF = new_definition
  `SEG m k (l:A list) = TAKE m (DROP k l)`;;

let MAX_LIST = new_recursive_definition list_RECURSION
  `(MAX_LIST [] = 0) /\ (MAX_LIST (CONS h t) = MAX h (MAX_LIST t))`;;

let LIST_ELEM_COUNT_DEF = new_definition
  `LIST_ELEM_COUNT (e:A) l = LENGTH (FILTER (\x. x = e) l)`;;

let OPT_MMAP_DEF = new_recursive_definition list_RECURSION
  `(OPT_MMAP (f:A->B option) [] = SOME []) /\
   (OPT_MMAP f (CONS h t) =
      OPTION_BIND (f h) (\h'. OPTION_BIND (OPT_MMAP f t) (\t'. SOME (CONS h' t'))))`;;

let UNZIP_DEF = new_definition
  `UNZIP (l:(A#B) list) = (MAP FST l, MAP SND l)`;;

let INDEX_FIND_DEF = new_recursive_definition list_RECURSION
  `(INDEX_FIND i (P:A->bool) [] = NONE) /\
   (INDEX_FIND i P (CONS h t) =
      if P h then SOME (i,h) else INDEX_FIND (SUC i) P t)`;;

let FIND_DEF = new_definition
  `FIND (P:A->bool) l = OPTION_MAP SND (INDEX_FIND 0 P l)`;;

let SPLITP_DEF = new_recursive_definition list_RECURSION
  `(SPLITP (P:A->bool) [] = ([],[])) /\
   (SPLITP P (CONS h t) =
      if P h then ([], CONS h t)
      else (CONS h (FST (SPLITP P t)), SND (SPLITP P t)))`;;

(* ------------------------------------------------------------------------- *)
(* alist                                                                     *)
(* ------------------------------------------------------------------------- *)

let ALOOKUP_DEF = new_recursive_definition list_RECURSION
  `(ALOOKUP ([]:(A#B) list) q = NONE) /\
   (ALOOKUP (CONS h t) q = if FST h = q then SOME (SND h) else ALOOKUP t q)`;;

let ALOOKUP_THM = prove
 (`(!q. ALOOKUP ([]:(A#B) list) q = NONE) /\
   (!x y t q. ALOOKUP (CONS ((x:A),(y:B)) t) q =
              if x = q then SOME y else ALOOKUP t q)`,
  REWRITE_TAC[ALOOKUP_DEF]);;

(* ------------------------------------------------------------------------- *)
(* arithmetic                                                                *)
(* ------------------------------------------------------------------------- *)

let DIV2_DEF = new_definition
  `DIV2 n = n DIV 2`;;

let NRC = new_recursive_definition num_RECURSION
  `(NRC (R:A->A->bool) 0 x y <=> x = y) /\
   (NRC R (SUC n) x y <=> ?z. R x z /\ NRC R n z y)`;;

(* ------------------------------------------------------------------------- *)
(* pred_set                                                                  *)
(* ------------------------------------------------------------------------- *)

let count_DEF = new_definition
  `count n = {m | m < n}`;;

let COMPL_DEF = new_definition
  `COMPL (s:A->bool) = UNIV DIFF s`;;

let PREIMAGE_DEF = new_definition
  `PREIMAGE (f:A->B) s = {x | f x IN s}`;;

let SUM_IMAGE_DEF = new_definition
  `SUM_IMAGE (f:A->num) s = nsum s f`;;

let SUM_SET_DEF = new_definition
  `SUM_SET s = nsum s (\x:num. x)`;;

let MAX_SET_DEF = new_definition
  `MAX_SET s = if s = {} then 0 else @m. m IN s /\ !n:num. n IN s ==> n <= m`;;

(* ------------------------------------------------------------------------- *)
(* relation                                                                  *)
(* ------------------------------------------------------------------------- *)

let transitive_DEF = new_definition
  `transitive (R:A->A->bool) <=> !x y z. R x y /\ R y z ==> R x z`;;

let reflexive_DEF = new_definition
  `reflexive (R:A->A->bool) <=> !x. R x x`;;

let symmetric_DEF = new_definition
  `symmetric (R:A->A->bool) <=> !x y. R x y <=> R y x`;;

let irreflexive_DEF = new_definition
  `irreflexive (R:A->A->bool) <=> !x. ~R x x`;;

let antisymmetric_DEF = new_definition
  `antisymmetric (R:A->A->bool) <=> !x y. R x y /\ R y x ==> x = y`;;

let total_DEF = new_definition
  `total (R:A->A->bool) <=> !x y. R x y \/ R y x`;;

let trichotomous_DEF = new_definition
  `trichotomous (R:A->A->bool) <=> !a b. R a b \/ R b a \/ a = b`;;

let RSUBSET_DEF = new_definition
  `RSUBSET (R1:A->B->bool) R2 <=> !x y. R1 x y ==> R2 x y`;;

(* ------------------------------------------------------------------------- *)
(* While                                                                     *)
(* ------------------------------------------------------------------------- *)

let OWHILE_DEF = new_definition
  `OWHILE (G:A->bool) f s =
     if ?n. ~G (ITER n f s)
     then SOME (ITER (minimal n. ~G (ITER n f s)) f s) else NONE`;;

let WHILE_DEF = new_definition
  `WHILE (G:A->bool) f s =
     if ?n. ~G (ITER n f s)
     then ITER (minimal n. ~G (ITER n f s)) f s else @x. F`;;

let OLEAST_DEF = new_definition
  `OLEAST (P:num->bool) = if ?n. P n then SOME (minimal n. P n) else NONE`;;

parse_as_binder "OLEAST";;
