(* ========================================================================= *)
(* cfHeapsBase: port of HOL4 characteristic/cfHeapsBaseScript.sml (CakeML    *)
(* v3479).  Defines the heap type that the separation logic used by CF uses. *)
(* Also defines POSTv etc.                                                   *)
(*                                                                           *)
(* Notation.  As in hol4/set_sep.ml, HOL4's star (multiplication symbol)     *)
(* on heap predicates is the infix STAR, HOL4's cond (overloaded ampersand)  *)
(* is set_sep_cond, emp is set_sep_emp and one is set_sep_one.  HOL4's       *)
(* infix overloads of line 274 of the script are infixes here too, with the  *)
(* same symbols: star-plus for STARPOST (precedence 18, left; HOL4 580),     *)
(* ==>> for SEP_IMP and ==+> for SEP_IMPPOST (13, right; HOL4 469), ~~>> for *)
(* cf_cell and ~~> for cf_REF (23, right; HOL4 690), so that, as in HOL4,    *)
(* ~~> binds tighter than STAR, STAR tighter than star-plus, and star-plus   *)
(* tighter than ==>> and ==+>, which bind tighter than = and /\.            *)
(* HOL4's ==v>, ==e>, ==f>, ==d>, =~v> and =~e> mix letters and symbols,     *)
(* which HOL Light's lexer splits: they are written with their constants     *)
(* SEP_IMPPOSTv, SEP_IMPPOSTe, SEP_IMPPOSTf, SEP_IMPPOSTd, SEP_IMPPOSTv_inv   *)
(* and SEP_IMPPOSTe_inv.  POSTv, POSTe, POSTf and POSTd are binders, as in   *)
(* HOL4 (POSTv v. Q v); the bare constants are (POSTv), ... (HOL4 $POSTv).   *)
(* Names (doc/names.tsv): GC, cell, REF, ARRAY, W8ARRAY, IO and IOx *)
(* are cf_GC, cf_cell, cf_REF, cf_ARRAY, cf_W8ARRAY, cf_IO and cf_IOx; the   *)
(* constructors Mem, FFI_split, FFI_part, FFI_full of heap_part and Val,     *)
(* Exn, FFIDiv, Div of res have the prefix cf_ as well; the types loc and    *)
(* ffi_result are cf_loc and cf_ffi_result.  HOL4's Num (int to num) is      *)
(* num_of_int and ABS is abs; word8 is byte; the empty mlstring literal is   *)
(* implode "".                                                               *)
(* Type abbreviations: HOL Light's cannot have type parameters, so HOL4's    *)
(* ffi_proj, the pair of a projection of the ffi state FFI to a finite map   *)
(* from mlstring to ffi and of a list of (port names, ffi_next) parts, is    *)
(* written out where it is used, as the type                                 *)
(*   (FFI->(mlstring,ffi)fmap)#(((mlstring)list#ffi_next)list)               *)
(* Helper lemmas that are not HOL4 theorems are CF1AUX_.                     *)
(* ========================================================================= *)

needs "characteristic/cfFFIType.ml";;
needs "hol4/alist.ml";;
needs "hol4/llist.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "hol4/set_sep.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Heaps                                                                     *)
(* ------------------------------------------------------------------------- *)

let encode_pair_def = cake_def
  `encode_pair (e1:A->ffi) (e2:B->ffi) (x,y) = cf_Cons (e1 x) (e2 y)`;;

let encode_list_def = cake_def
  `encode_list (e:A->ffi) l = cf_List (MAP e l)`;;

let encode_list_11 = prove
 (`!xs ys.
     encode_list (f:A->ffi) xs = encode_list f ys /\
     (!x y. f x = f y <=> x = y) ==>
     xs = ys`,
  REWRITE_TAC[encode_list_def; cf_List_11] THEN MESON_TAC[INJECTIVE_MAP]);;

let encode_option_def = cake_def
  `(encode_option (e:A->ffi) NONE = cf_List []) /\
   (encode_option e (SOME x) = cf_List [e x])`;;

let encode_option_11 = prove
 (`!x y. encode_option (f:A->ffi) x = encode_option f y /\
         (!x y. f x = f y <=> x = y) ==> x = y`,
  REPEAT GEN_TAC THEN QCASES_ON "x" THEN QCASES_ON "y" THEN
  SIMP[encode_option_def; cf_List_11; CONS_11; NOT_CONS_NIL] THEN MESON_TAC[]);;

let encode_bool_def = cake_def
  `(encode_bool F = cf_Num 0) /\
   (encode_bool T = cf_Num 1)`;;

let encode_bool_11 = prove
 (`!x y. encode_bool x = encode_bool y <=> x = y`,
  REPEAT GEN_TAC THEN QCASES_ON "x" THEN QCASES_ON "y" THEN
  SIMP[encode_bool_def; cf_Num_11]);;
let _ = cake_add_simps [encode_bool_11];;

let encode_int_def = cake_def
  `encode_int i = cf_Cons (encode_bool (&0 <= i)) (cf_Num (num_of_int (abs i)))`;;

let encode_int_11 = prove
 (`!x y. encode_int x = encode_int y <=> x = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[encode_int_def; cf_Cons_11; encode_bool_11; cf_Num_11] THEN
  EQ_TAC THEN SIMP[] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN SIMP[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN
  INT_ARITH_TAC);;
let _ = cake_add_simps [encode_int_11];;

let cf_ffi_result_INDUCT,cf_ffi_result_RECURSION = cake_type
  "cf_ffi_result = FFIreturn (byte list) FFI | FFIdiverge";;

(* make an ffi_next function from base functions and encode/decode; the     *)
(* type is HOL4's most general one                                           *)
let mk_ffi_next_def = cake_def
  `mk_ffi_next (encode:A->E,decode:S->(B)option,
                ls:(K#(C->D->B->((A)cf_ffi_result)option))list)
               (name:K) (conf:C) (bytes:D) (s:S) =
     OPTION_BIND (ALOOKUP ls name) (\f.
     OPTION_BIND (decode s) (\s.
     OPTION_BIND (f conf bytes s) (\r.
       match r with
         FFIreturn bytes s -> SOME (FFIreturn bytes (encode s))
       | FFIdiverge -> SOME FFIdiverge)))`;;

new_type_abbrev("cf_loc",`:num`);;

new_type_abbrev("ffi_next",
  `:mlstring->(byte)list->(byte)list->ffi->((ffi)cf_ffi_result)option`);;

let heap_part_INDUCT,heap_part_RECURSION = cake_type
  "heap_part = cf_Mem cf_loc (v store_v)
             | cf_FFI_split
             | cf_FFI_part ffi ffi_next (mlstring list) (io_event list)
             | cf_FFI_full (io_event list)";;

new_type_abbrev("heap",`:heap_part->bool`);;
new_type_abbrev("hprop",`:heap->bool`);;

let res_INDUCT,res_RECURSION = cake_type
  "res = cf_Val v
       | cf_Exn v
       | cf_FFIDiv mlstring (byte list) (byte list)
       | cf_Div (io_event llist)";;

(* HOL4: Type ffi_proj = (see the header) *)

let SPLIT3_def = cake_def
  `SPLIT3 (s:A->bool) (u,v,w) <=>
     ((u UNION v) UNION w = s) /\
     DISJOINT u v /\ DISJOINT v w /\ DISJOINT u w`;;

(* ------------------------------------------------------------------------- *)
(* Heap predicates                                                           *)
(* ------------------------------------------------------------------------- *)

(* in set_sep: emp, one, STAR, SEP_IMP, SEP_EXISTS, cond *)

(* STAR for post-conditions *)
let STARPOST_def = cake_def
  `STARPOST (Q:res->hprop) (H:hprop) = \r. Q r STAR H`;;

(* SEP_IMP lifted to post-conditions *)
let SEP_IMPPOST_def = cake_def
  `SEP_IMPPOST (Q1:res->hprop) (Q2:res->hprop) <=> !r. SEP_IMP (Q1 r) (Q2 r)`;;

let SEP_IMPPOSTv_def = cake_def
  `SEP_IMPPOSTv (Q1:res->hprop) (Q2:res->hprop) <=>
     !v. SEP_IMP (Q1 (cf_Val v)) (Q2 (cf_Val v))`;;

let SEP_IMPPOSTe_def = cake_def
  `SEP_IMPPOSTe (Q1:res->hprop) (Q2:res->hprop) <=>
     !e. SEP_IMP (Q1 (cf_Exn e)) (Q2 (cf_Exn e))`;;

let SEP_IMPPOSTf_def = cake_def
  `SEP_IMPPOSTf (Q1:res->hprop) (Q2:res->hprop) <=>
     !name conf bytes.
       SEP_IMP (Q1 (cf_FFIDiv name conf bytes)) (Q2 (cf_FFIDiv name conf bytes))`;;

let SEP_IMPPOSTd_def = cake_def
  `SEP_IMPPOSTd (Q1:res->hprop) (Q2:res->hprop) <=>
     !io. SEP_IMP (Q1 (cf_Div io)) (Q2 (cf_Div io))`;;

let SEP_IMPPOSTv_inv_def = cake_def
  `SEP_IMPPOSTv_inv (Q1:res->hprop) (Q2:res->hprop) <=>
     (SEP_IMPPOSTe Q1 Q2 /\ SEP_IMPPOSTf Q1 Q2 /\ SEP_IMPPOSTd Q1 Q2)`;;

let SEP_IMPPOSTe_inv_def = cake_def
  `SEP_IMPPOSTe_inv (Q1:res->hprop) (Q2:res->hprop) <=>
     (SEP_IMPPOSTv Q1 Q2 /\ SEP_IMPPOSTf Q1 Q2 /\ SEP_IMPPOSTd Q1 Q2)`;;

(* Garbage collection predicate *)
let cf_GC_def = cake_def
  `cf_GC = (SEP_EXISTS (H:hprop). H)`;;

(* Injections for post-conditions *)
let POST_def = cake_def
  `POST (Qv:v->hprop) (Qe:v->hprop) (Qf:mlstring->byte list->byte list->hprop)
        (Qd:io_event llist->bool) =
     \r. match r with
           cf_Val v -> Qv v
         | cf_Exn e -> Qe e
         | cf_FFIDiv name conf bytes -> Qf name conf bytes
         | cf_Div io -> set_sep_cond (Qd io)`;;

let POSTv_def = cake_def
  `POSTv (Qv:v->hprop) =
     POST Qv (\e. set_sep_cond F) (\name conf bytes. set_sep_cond F) (\io. F)`;;
parse_as_binder "POSTv";;

let POSTe_def = cake_def
  `POSTe (Qe:v->hprop) =
     POST (\v. set_sep_cond F) Qe (\name conf bytes. set_sep_cond F) (\io. F)`;;
parse_as_binder "POSTe";;

let POSTf_def = cake_def
  `POSTf (Qf:mlstring->byte list->byte list->hprop) =
     POST (\v. set_sep_cond F) (\e. set_sep_cond F) Qf (\io. F)`;;
parse_as_binder "POSTf";;

let POSTd_def = cake_def
  `POSTd (Qd:io_event llist->bool) =
     POST (\v. set_sep_cond F) (\e. set_sep_cond F) (\name conf bytes. set_sep_cond F) Qd`;;
parse_as_binder "POSTd";;

let POSTve_def = cake_def
  `POSTve (Qv:v->hprop) (Qe:v->hprop) =
     POST Qv Qe (\name conf bytes. set_sep_cond F) (\io. F)`;;

let POSTvd_def = cake_def
  `POSTvd (Qv:v->hprop) (Qd:io_event llist->bool) =
     POST Qv (\e. set_sep_cond F) (\name conf bytes. set_sep_cond F) Qd`;;

let POSTed_def = cake_def
  `POSTed (Qe:v->hprop) (Qd:io_event llist->bool) =
     POST (\v. set_sep_cond F) Qe (\name conf bytes. set_sep_cond F) Qd`;;

let POST_F_def = cake_def
  `POST_F (r:res) = (set_sep_cond F:hprop)`;;

(* cond specialized to equality to some value; as a post-condition *)
let cond_eq_def = cake_def
  `cond_eq (v:A) = \x. (set_sep_cond (x = v):(B->bool)->bool)`;;

(* A single memory cell. *)
let cf_cell_def = cake_def
  `cf_cell (l:cf_loc) (v:v store_v) = set_sep_one (cf_Mem l v)`;;

(* A reference cell, as a convenience wrapper over cell and Refv *)
let cf_REF_def = cake_def
  `cf_REF rv xv =
     SEP_EXISTS loc. set_sep_cond (rv = Loc T loc) STAR cf_cell loc (Refv xv)`;;

(* An array cell, as a wrapper over cell and Varray *)
let cf_ARRAY_def = cake_def
  `cf_ARRAY av vl =
     SEP_EXISTS loc. set_sep_cond (av = Loc T loc) STAR cf_cell loc (Varray vl)`;;

(* A bytearray cell, as a wrapper over cell and W8array *)
let cf_W8ARRAY_def = cake_def
  `cf_W8ARRAY av wl =
     SEP_EXISTS loc. set_sep_cond (av = Loc T loc) STAR cf_cell loc (W8array wl)`;;

let cf_IO_def = cake_def
  `cf_IO s u ns =
     SEP_EXISTS events.
       set_sep_one (cf_FFI_part s u ns events) STAR set_sep_cond (~MEM (implode "") ns)`;;

let cf_IOx_def = cake_def
  `cf_IOx (encode:A->ffi,decode:ffi->(B)option,ls) (s:A) =
     cf_IO (encode s) (mk_ffi_next (encode,decode,ls)) (MAP FST ls)`;;

let mk_proj1_def = cake_def
  `mk_proj1 (encode:A->B,decode:C,ls:(D#E)list) (s:A) =
     MAP (\x. (x, encode s)) (MAP FST ls)`;;

let mk_proj2_def = cake_def
  `mk_proj2 (encode:A->E,decode:S->(B)option,
             ls:(K#(C->D->B->((A)cf_ffi_result)option))list) =
     (MAP FST ls, mk_ffi_next (encode,decode,ls))`;;

(* ------------------------------------------------------------------------- *)
(* Notations for heap predicates (see the header)                           *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("*+",(18,"left"));;
override_interface("*+",`STARPOST`);;

parse_as_infix("==>>",(13,"right"));;
override_interface("==>>",`SEP_IMP:((A->bool)->bool)->((A->bool)->bool)->bool`);;

parse_as_infix("==+>",(13,"right"));;
override_interface("==+>",`SEP_IMPPOST`);;

parse_as_infix("~~>>",(23,"right"));;
override_interface("~~>>",`cf_cell`);;

parse_as_infix("~~>",(23,"right"));;
override_interface("~~>",`cf_REF`);;

(* ------------------------------------------------------------------------- *)
(* Low level lemmas about SPLIT and SPLIT3                                   *)
(* ------------------------------------------------------------------------- *)

(* HOL4: SPLIT_TAC *)
let CF1AUX_SPLIT_TAC = REWRITE_TAC[SPLIT_def; SPLIT3_def] THEN SET_TAC[];;

let SPLIT3_of_SPLIT_emp3 = prove
 (`!h h1 h2:A->bool. SPLIT h (h1, h2) ==> SPLIT3 h (h1, h2, {})`,
  CF1AUX_SPLIT_TAC);;

let SPLIT3_of_SPLIT_emp2 = prove
 (`!h h1 h3:A->bool. SPLIT h (h1, h3) ==> SPLIT3 h (h1, {}, h3)`,
  CF1AUX_SPLIT_TAC);;

let SPLIT3_swap23 = prove
 (`!h h1 h2 h3:A->bool. SPLIT3 h (h1, h2, h3) ==> SPLIT3 h (h1, h3, h2)`,
  CF1AUX_SPLIT_TAC);;

let SPLIT_emp1 = prove
 (`!h h':A->bool. SPLIT h ({}, h') <=> (h' = h)`,
  CF1AUX_SPLIT_TAC);;

let SPLIT_emp2 = prove
 (`!h h':A->bool. SPLIT h (h', {}) <=> (h' = h)`,
  CF1AUX_SPLIT_TAC);;

let SPLIT3_emp1 = prove
 (`!h h1 h2:A->bool. SPLIT3 h ({}, h1, h2) <=> SPLIT h (h1, h2)`,
  CF1AUX_SPLIT_TAC);;

let SPLIT3_emp3 = prove
 (`!h h1 h2:A->bool. SPLIT3 h (h1,h2,{}) <=> SPLIT h (h1,h2)`,
  CF1AUX_SPLIT_TAC);;

let SPLIT_of_SPLIT3_2u3 = prove
 (`!h h1 h2 h3:A->bool. SPLIT3 h (h1, h2, h3) ==> SPLIT h (h1, h2 UNION h3)`,
  CF1AUX_SPLIT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Additionnal properties of STAR                                            *)
(* ------------------------------------------------------------------------- *)

let STARPOST_emp = prove
 (`!Q. Q *+ set_sep_emp = Q`,
  REWRITE_TAC[STARPOST_def; SEP_CLAUSES; ETA_AX]);;

let SEP_IMP_frame_single_l = prove
 (`!(H':(A->bool)->bool) R.
     (set_sep_emp ==>> H') ==>
     (R ==>> H' STAR R)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `R:(A->bool)->bool` o MATCH_MP SEP_IMP_FRAME) THEN
  REWRITE_TAC[SEP_CLAUSES]);;

let SEP_IMP_frame_single_r = prove
 (`!(H:(A->bool)->bool) R.
     (H ==>> set_sep_emp) ==>
     (H STAR R ==>> R)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `R:(A->bool)->bool` o MATCH_MP SEP_IMP_FRAME) THEN
  REWRITE_TAC[SEP_CLAUSES]);;

(* the four shapes of frame lemmas below: a frame H ==>> H' around one       *)
(* assertion, or the frame emp ==>> H' on the left, H ==>> emp on the right, *)
(* or none                                                                   *)
let CF1AUX_FRAME_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST [MATCH_MP_TAC SEP_IMP_STAR THEN ASM_REWRITE_TAC[SEP_IMP_REFL];
         MATCH_MP_TAC SEP_IMP_frame_single_l THEN ASM_REWRITE_TAC[];
         MATCH_MP_TAC SEP_IMP_frame_single_r THEN ASM_REWRITE_TAC[];
         REWRITE_TAC[SEP_IMP_REFL]];;

let SEP_IMP_cell_frame = prove
 (`!H H' l v v'.
     (v = v') /\ (H ==>> H') ==>
     (H STAR l ~~>> v ==>> H' STAR l ~~>> v')`,
  CF1AUX_FRAME_TAC);;

let SEP_IMP_cell_frame_single_l = prove
 (`!H' l v v'.
     (v = v') /\ (set_sep_emp ==>> H') ==>
     (l ~~>> v ==>> H' STAR l ~~>> v')`,
  CF1AUX_FRAME_TAC);;

let SEP_IMP_cell_frame_single_r = prove
 (`!H l v v'.
     (v = v') /\ (H ==>> set_sep_emp) ==>
     (H STAR l ~~>> v ==>> l ~~>> v')`,
  CF1AUX_FRAME_TAC);;

(* HOL4: H is a vacuous variable and emp has any type *)
let SEP_IMP_cell_frame_single = prove
 (`!(H:A) l v v'.
     (v = v') /\ ((set_sep_emp:(B->bool)->bool) ==>> set_sep_emp) ==>
     (l ~~>> v ==>> l ~~>> v')`,
  CF1AUX_FRAME_TAC);;

let SEP_IMP_REF_frame = prove
 (`!H H' r v v'.
     (v = v') /\ (H ==>> H') ==>
     (H STAR r ~~> v ==>> H' STAR r ~~> v')`,
  CF1AUX_FRAME_TAC);;

let SEP_IMP_REF_frame_single_l = prove
 (`!H' r v v'.
     (v = v') /\ (set_sep_emp ==>> H') ==>
     (r ~~> v ==>> H' STAR r ~~> v')`,
  CF1AUX_FRAME_TAC);;

let SEP_IMP_REF_frame_single_r = prove
 (`!H r v v'.
     (v = v') /\ (H ==>> set_sep_emp) ==>
     (H STAR r ~~> v ==>> r ~~> v')`,
  CF1AUX_FRAME_TAC);;

let SEP_IMP_REF_frame_single = prove
 (`!(H:A) r v v'.
     (v = v') /\ ((set_sep_emp:(B->bool)->bool) ==>> set_sep_emp) ==>
     (r ~~> v ==>> r ~~> v')`,
  CF1AUX_FRAME_TAC);;

let SEP_IMP_ARRAY_frame = prove
 (`!H H' a vl vl'.
     (vl = vl') /\ (H ==>> H') ==>
     (H STAR cf_ARRAY a vl ==>> H' STAR cf_ARRAY a vl')`,
  CF1AUX_FRAME_TAC);;

let SEP_IMP_ARRAY_frame_single_l = prove
 (`!H' a vl vl'.
     (vl = vl') /\ (set_sep_emp ==>> H') ==>
     (cf_ARRAY a vl ==>> H' STAR cf_ARRAY a vl')`,
  CF1AUX_FRAME_TAC);;

let SEP_IMP_ARRAY_frame_single_r = prove
 (`!H a vl vl'.
     (vl = vl') /\ (H ==>> set_sep_emp) ==>
     (H STAR cf_ARRAY a vl ==>> cf_ARRAY a vl')`,
  CF1AUX_FRAME_TAC);;

let SEP_IMP_ARRAY_frame_single = prove
 (`!(H:A) a vl vl'.
     (vl = vl') /\ ((set_sep_emp:(B->bool)->bool) ==>> set_sep_emp) ==>
     (cf_ARRAY a vl ==>> cf_ARRAY a vl')`,
  CF1AUX_FRAME_TAC);;

let SEP_IMP_W8ARRAY_frame = prove
 (`!H H' a wl wl'.
     (wl = wl') /\ (H ==>> H') ==>
     (H STAR cf_W8ARRAY a wl ==>> H' STAR cf_W8ARRAY a wl')`,
  CF1AUX_FRAME_TAC);;

let SEP_IMP_W8ARRAY_frame_single_l = prove
 (`!H' a wl wl'.
     (wl = wl') /\ (set_sep_emp ==>> H') ==>
     (cf_W8ARRAY a wl ==>> H' STAR cf_W8ARRAY a wl')`,
  CF1AUX_FRAME_TAC);;

let SEP_IMP_W8ARRAY_frame_single_r = prove
 (`!H a wl wl'.
     (wl = wl') /\ (H ==>> set_sep_emp) ==>
     (H STAR cf_W8ARRAY a wl ==>> cf_W8ARRAY a wl')`,
  CF1AUX_FRAME_TAC);;

let SEP_IMP_W8ARRAY_frame_single = prove
 (`!(H:A) a wl wl'.
     (wl = wl') /\ ((set_sep_emp:(B->bool)->bool) ==>> set_sep_emp) ==>
     (cf_W8ARRAY a wl ==>> cf_W8ARRAY a wl')`,
  CF1AUX_FRAME_TAC);;

let SEP_IMP_IO_frame = prove
 (`!H H' idx st u st' u'.
     (st = st' /\ u = u') /\ (H ==>> H') ==>
     (H STAR cf_IO st u idx ==>> H' STAR cf_IO st' u' idx)`,
  CF1AUX_FRAME_TAC);;

let SEP_IMP_IO_frame_single_l = prove
 (`!H' idx st u st' u'.
     (st = st' /\ u = u') /\ (set_sep_emp ==>> H') ==>
     (cf_IO st u idx ==>> H' STAR cf_IO st' u' idx)`,
  CF1AUX_FRAME_TAC);;

let SEP_IMP_IO_frame_single_r = prove
 (`!H idx st u st' u'.
     (st = st' /\ u = u') /\ (H ==>> set_sep_emp) ==>
     (H STAR cf_IO st u idx ==>> cf_IO st' u' idx)`,
  CF1AUX_FRAME_TAC);;

let SEP_IMP_IO_frame_single = prove
 (`!idx st u st' u'.
     (st = st' /\ u = u') /\ ((set_sep_emp:(A->bool)->bool) ==>> set_sep_emp) ==>
     (cf_IO st u idx ==>> cf_IO st' u' idx)`,
  CF1AUX_FRAME_TAC);;

(* ------------------------------------------------------------------------- *)
(* Normalization of STAR                                                     *)
(* ------------------------------------------------------------------------- *)

(* HOL4's rew_heap_thms and rew_heap (full_simp_tac bool_ss with AC STAR,    *)
(* SEP_CLAUSES, STARPOST_emp and the definitions of SEP_IMPPOST,             *)
(* SEP_IMPPOSTv, SEP_IMPPOSTe, STARPOST and cond_eq) are SML values for the  *)
(* proofs of this theory and of cfHeaps, not theorems.                      *)

(* Workaround because of SEP_CLAUSES turning set_sep_cond F into SEP_F *)

let SEP_F_to_cond = prove
 (`(SEP_F:(A->bool)->bool) = set_sep_cond F`,
  REWRITE_TAC[FUN_EQ_THM; SEP_F_def; set_sep_cond_def]);;

(* ------------------------------------------------------------------------- *)
(* Properties of GC                                                          *)
(* ------------------------------------------------------------------------- *)

let GC_STAR_GC = prove
 (`cf_GC STAR cf_GC = cf_GC`,
  REWRITE_TAC[FUN_EQ_THM; cf_GC_def; SEP_EXISTS_THM; STAR_def] THEN
  X_GEN_TAC `h:heap` THEN EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `\h:heap. T` THEN REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`h:heap`; `{}:heap`] THEN
    REWRITE_TAC[SPLIT_def; UNION_EMPTY; DISJOINT_EMPTY] THEN
    CONJ_TAC THEN EXISTS_TAC `\h:heap. T` THEN REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Unfolding + case split lemma for SEP_IMPPOST                              *)
(* ------------------------------------------------------------------------- *)

let SEP_IMPPOST_unfold = prove
 (`!Q1 Q2.
     (Q1 ==+> Q2) <=>
     (!v. Q1 (cf_Val v) ==>> Q2 (cf_Val v)) /\
     (!v. Q1 (cf_Exn v) ==>> Q2 (cf_Exn v)) /\
     (!name conf bytes.
        Q1 (cf_FFIDiv name conf bytes) ==>> Q2 (cf_FFIDiv name conf bytes)) /\
     (!io. Q1 (cf_Div io) ==>> Q2 (cf_Div io))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SEP_IMPPOST_def] THEN EQ_TAC THEN
  SIMP[] THEN STRIP_TAC THEN X_GEN_TAC `r:res` THEN QCASES_ON "r" THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Extraction from H1 in H1 ==>> H2                                          *)
(* ------------------------------------------------------------------------- *)

let hpull_prop = prove
 (`!(H:(A->bool)->bool) H' P.
     (P ==> H ==>> H') ==>
     (H STAR set_sep_cond P ==>> H')`,
  REWRITE_TAC[SEP_IMP_def; cond_STAR] THEN MESON_TAC[]);;

let hpull_prop_single = prove
 (`!(H':(A->bool)->bool) P.
     (P ==> set_sep_emp ==>> H') ==>
     (set_sep_cond P ==>> H')`,
  REWRITE_TAC[SEP_IMP_def; set_sep_cond_def; set_sep_emp_def] THEN MESON_TAC[]);;

(* HOL4: A is a vacuous variable *)
let hpull_exists_single = prove
 (`!(A:C) (H':(A->bool)->bool) (J:B->(A->bool)->bool).
     (!x. (J x) ==>> H') ==>
     ((SEP_EXISTS) J ==>> H')`,
  REWRITE_TAC[SEP_IMP_def; SEP_EXISTS] THEN MESON_TAC[]);;

let SEP_IMP_rew = prove
 (`!(H1:(A->bool)->bool) H2 H1' H2'.
     (H1 = H2) ==> (H1' = H2') ==> ((H1 ==>> H1') <=> (H2 ==>> H2'))`,
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Simplification in H2 on H1 ==>> H2                                        *)
(* ------------------------------------------------------------------------- *)

let hsimpl_prop = prove
 (`!(H':(A->bool)->bool) H P.
     P /\ (H' ==>> H) ==>
     (H' ==>> H STAR set_sep_cond P)`,
  REWRITE_TAC[SEP_IMP_def; cond_STAR] THEN MESON_TAC[]);;

let hsimpl_prop_single = prove
 (`!(H':(A->bool)->bool) P.
     P /\ (H' ==>> set_sep_emp) ==>
     (H' ==>> set_sep_cond P)`,
  REWRITE_TAC[SEP_IMP_def; set_sep_cond_def; set_sep_emp_def] THEN MESON_TAC[]);;

let hsimpl_exists_single = prove
 (`!(x:B) (H':(A->bool)->bool) (J:B->(A->bool)->bool).
     (H' ==>> J x) ==>
     (H' ==>> (SEP_EXISTS) J)`,
  REWRITE_TAC[SEP_IMP_def; SEP_EXISTS] THEN MESON_TAC[]);;

let hsimpl_gc = prove
 (`!H. H ==>> cf_GC`,
  REWRITE_TAC[cf_GC_def; SEP_IMP_def; SEP_EXISTS_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Automatic rewrites for post-condition injections                          *)
(* ------------------------------------------------------------------------- *)

let POST_Val = prove
 (`!Qv Qe Qf Qd v. POST Qv Qe Qf Qd (cf_Val v) = Qv v`,
  SIMP[POST_def]);;

let POST_Exn = prove
 (`!Qv Qe Qf Qd v. POST Qv Qe Qf Qd (cf_Exn v) = Qe v`,
  SIMP[POST_def]);;

let POST_FFIDiv = prove
 (`!Qv Qe Qf Qd name conf bytes.
     POST Qv Qe Qf Qd (cf_FFIDiv name conf bytes) = Qf name conf bytes`,
  SIMP[POST_def]);;

let POST_Div = prove
 (`!Qv Qe Qf Qd io. POST Qv Qe Qf Qd (cf_Div io) = set_sep_cond (Qd io)`,
  SIMP[POST_def]);;
let _ = cake_add_simps [POST_Val; POST_Exn; POST_FFIDiv; POST_Div];;

let POSTv_Val = prove
 (`!Qv v. (POSTv) Qv (cf_Val v) = Qv v`,
  SIMP[POSTv_def]);;

let POSTv_Exn = prove
 (`!Qv v. (POSTv) Qv (cf_Exn v) = set_sep_cond F`,
  SIMP[POSTv_def]);;

let POSTv_FFIDiv = prove
 (`!Qv name conf bytes. (POSTv) Qv (cf_FFIDiv name conf bytes) = set_sep_cond F`,
  SIMP[POSTv_def]);;

let POSTv_Div = prove
 (`!Qv io. (POSTv) Qv (cf_Div io) = set_sep_cond F`,
  SIMP[POSTv_def]);;
let _ = cake_add_simps [POSTv_Val; POSTv_Exn; POSTv_FFIDiv; POSTv_Div];;

let POSTe_Val = prove
 (`!Qe v. (POSTe) Qe (cf_Val v) = set_sep_cond F`,
  SIMP[POSTe_def]);;

let POSTe_Exn = prove
 (`!Qe v. (POSTe) Qe (cf_Exn v) = Qe v`,
  SIMP[POSTe_def]);;

let POSTe_FFIDiv = prove
 (`!Qe name conf bytes. (POSTe) Qe (cf_FFIDiv name conf bytes) = set_sep_cond F`,
  SIMP[POSTe_def]);;

let POSTe_Div = prove
 (`!Qe io. (POSTe) Qe (cf_Div io) = set_sep_cond F`,
  SIMP[POSTe_def]);;
let _ = cake_add_simps [POSTe_Val; POSTe_Exn; POSTe_FFIDiv; POSTe_Div];;

let POSTf_Val = prove
 (`!Qf v. (POSTf) Qf (cf_Val v) = set_sep_cond F`,
  SIMP[POSTf_def]);;

let POSTf_Exn = prove
 (`!Qf v. (POSTf) Qf (cf_Exn v) = set_sep_cond F`,
  SIMP[POSTf_def]);;

let POSTf_FFIDiv = prove
 (`!Qf name conf bytes. (POSTf) Qf (cf_FFIDiv name conf bytes) = Qf name conf bytes`,
  SIMP[POSTf_def]);;

let POSTf_Div = prove
 (`!Qf io. (POSTf) Qf (cf_Div io) = set_sep_cond F`,
  SIMP[POSTf_def]);;
let _ = cake_add_simps [POSTf_Val; POSTf_Exn; POSTf_FFIDiv; POSTf_Div];;

let POSTd_Val = prove
 (`!Qd v. (POSTd) Qd (cf_Val v) = set_sep_cond F`,
  SIMP[POSTd_def]);;

let POSTd_Exn = prove
 (`!Qd v. (POSTd) Qd (cf_Exn v) = set_sep_cond F`,
  SIMP[POSTd_def]);;

let POSTd_FFIDiv = prove
 (`!Qd name conf bytes. (POSTd) Qd (cf_FFIDiv name conf bytes) = set_sep_cond F`,
  SIMP[POSTd_def]);;

let POSTd_Div = prove
 (`!Qd io. (POSTd) Qd (cf_Div io) = set_sep_cond (Qd io)`,
  SIMP[POSTd_def]);;
let _ = cake_add_simps [POSTd_Val; POSTd_Exn; POSTd_FFIDiv; POSTd_Div];;

let POSTve_Val = prove
 (`!Qv Qe v. POSTve Qv Qe (cf_Val v) = Qv v`,
  SIMP[POSTve_def]);;

let POSTve_Exn = prove
 (`!Qv Qe v. POSTve Qv Qe (cf_Exn v) = Qe v`,
  SIMP[POSTve_def]);;

let POSTve_FFIDiv = prove
 (`!Qv Qe name conf bytes. POSTve Qv Qe (cf_FFIDiv name conf bytes) = set_sep_cond F`,
  SIMP[POSTve_def]);;

let POSTve_Div = prove
 (`!Qv Qe io. POSTve Qv Qe (cf_Div io) = set_sep_cond F`,
  SIMP[POSTve_def]);;
let _ = cake_add_simps [POSTve_Val; POSTve_Exn; POSTve_FFIDiv; POSTve_Div];;

let POSTvd_Val = prove
 (`!Qv Qd v. POSTvd Qv Qd (cf_Val v) = Qv v`,
  SIMP[POSTvd_def]);;

let POSTvd_Exn = prove
 (`!Qv Qd v. POSTvd Qv Qd (cf_Exn v) = set_sep_cond F`,
  SIMP[POSTvd_def]);;

let POSTvd_FFIDiv = prove
 (`!Qv Qd name conf bytes. POSTvd Qv Qd (cf_FFIDiv name conf bytes) = set_sep_cond F`,
  SIMP[POSTvd_def]);;

let POSTvd_Div = prove
 (`!Qv Qd io. POSTvd Qv Qd (cf_Div io) = set_sep_cond (Qd io)`,
  SIMP[POSTvd_def]);;
let _ = cake_add_simps [POSTvd_Val; POSTvd_Exn; POSTvd_FFIDiv; POSTvd_Div];;

let POSTed_Val = prove
 (`!Qe Qd v. POSTed Qe Qd (cf_Val v) = set_sep_cond F`,
  SIMP[POSTed_def]);;

let POSTed_Exn = prove
 (`!Qe Qd v. POSTed Qe Qd (cf_Exn v) = Qe v`,
  SIMP[POSTed_def]);;

let POSTed_FFIDiv = prove
 (`!Qe Qd name conf bytes. POSTed Qe Qd (cf_FFIDiv name conf bytes) = set_sep_cond F`,
  SIMP[POSTed_def]);;

let POSTed_Div = prove
 (`!Qe Qd io. POSTed Qe Qd (cf_Div io) = set_sep_cond (Qd io)`,
  SIMP[POSTed_def]);;
let _ = cake_add_simps [POSTed_Val; POSTed_Exn; POSTed_FFIDiv; POSTed_Div];;

(* other lemmas about POSTv *)

let POSTv_ignore = prove
 (`(POSTv v. (P:hprop)) r h <=> ?v. r = cf_Val v /\ P h`,
  QCASES_ON "r" THEN SIMP[set_sep_cond_def]);;

(* ------------------------------------------------------------------------- *)
(* Lemmas for SEP_IMPPOSTv, SEP_IMPPOSTe, SEP_IMPPOSTf, SEP_IMPPOSTd,         *)
(* SEP_IMPPOSTv_inv, SEP_IMPPOSTe_inv (HOL4 ==v> ==e> ==f> ==d> =~v> =~e>)   *)
(* ------------------------------------------------------------------------- *)

let CF1AUX_POST_LEFT_TAC =
  SIMP[POSTv_def; POSTe_def; POSTf_def; POSTd_def; POSTve_def; POSTvd_def;
       POSTed_def; SEP_IMPPOSTv_inv_def; SEP_IMPPOSTe_inv_def;
       SEP_IMPPOSTv_def; SEP_IMPPOSTe_def; SEP_IMPPOSTf_def; SEP_IMPPOSTd_def;
       SEP_IMP_def; set_sep_cond_def];;

let SEP_IMPPOSTv_POSTe_left = prove
 (`!Qe Q. SEP_IMPPOSTv ((POSTe) Qe) Q`,
  CF1AUX_POST_LEFT_TAC);;

let SEP_IMPPOSTv_POSTf_left = prove
 (`!Qf Q. SEP_IMPPOSTv ((POSTf) Qf) Q`,
  CF1AUX_POST_LEFT_TAC);;

let SEP_IMPPOSTv_POSTd_left = prove
 (`!Qd Q. SEP_IMPPOSTv ((POSTd) Qd) Q`,
  CF1AUX_POST_LEFT_TAC);;

let SEP_IMPPOSTv_POSTed_left = prove
 (`!Qe Qd Q. SEP_IMPPOSTv (POSTed Qe Qd) Q`,
  CF1AUX_POST_LEFT_TAC);;

let SEP_IMPPOSTe_POSTv_left = prove
 (`!Qv Q. SEP_IMPPOSTe ((POSTv) Qv) Q`,
  CF1AUX_POST_LEFT_TAC);;

let SEP_IMPPOSTe_POSTf_left = prove
 (`!Qf Q. SEP_IMPPOSTe ((POSTf) Qf) Q`,
  CF1AUX_POST_LEFT_TAC);;

let SEP_IMPPOSTe_POSTd_left = prove
 (`!Qd Q. SEP_IMPPOSTe ((POSTd) Qd) Q`,
  CF1AUX_POST_LEFT_TAC);;

let SEP_IMPPOSTe_POSTvd_left = prove
 (`!Qv Qd Q. SEP_IMPPOSTe (POSTvd Qv Qd) Q`,
  CF1AUX_POST_LEFT_TAC);;

let SEP_IMPPOSTf_POSTv_left = prove
 (`!Qv Q. SEP_IMPPOSTf ((POSTv) Qv) Q`,
  CF1AUX_POST_LEFT_TAC);;

let SEP_IMPPOSTf_POSTe_left = prove
 (`!Qe Q. SEP_IMPPOSTf ((POSTe) Qe) Q`,
  CF1AUX_POST_LEFT_TAC);;

let SEP_IMPPOSTf_POSTd_left = prove
 (`!Qd Q. SEP_IMPPOSTf ((POSTd) Qd) Q`,
  CF1AUX_POST_LEFT_TAC);;

let SEP_IMPPOSTf_POSTve_left = prove
 (`!Qv Qe Q. SEP_IMPPOSTf (POSTve Qv Qe) Q`,
  CF1AUX_POST_LEFT_TAC);;

let SEP_IMPPOSTf_POSTvd_left = prove
 (`!Qv Qd Q. SEP_IMPPOSTf (POSTvd Qv Qd) Q`,
  CF1AUX_POST_LEFT_TAC);;

let SEP_IMPPOSTf_POSTed_left = prove
 (`!Qe Qd Q. SEP_IMPPOSTf (POSTed Qe Qd) Q`,
  CF1AUX_POST_LEFT_TAC);;

let SEP_IMPPOSTd_POSTv_left = prove
 (`!Qv Q. SEP_IMPPOSTd ((POSTv) Qv) Q`,
  CF1AUX_POST_LEFT_TAC);;

let SEP_IMPPOSTd_POSTe_left = prove
 (`!Qe Q. SEP_IMPPOSTd ((POSTe) Qe) Q`,
  CF1AUX_POST_LEFT_TAC);;

let SEP_IMPPOSTd_POSTf_left = prove
 (`!Qf Q. SEP_IMPPOSTd ((POSTf) Qf) Q`,
  CF1AUX_POST_LEFT_TAC);;

let SEP_IMPPOSTd_POSTve_left = prove
 (`!Qv Qe Q. SEP_IMPPOSTd (POSTve Qv Qe) Q`,
  CF1AUX_POST_LEFT_TAC);;

let SEP_IMPPOSTv_inv_POSTv_left = prove
 (`!Qv Q. SEP_IMPPOSTv_inv ((POSTv) Qv) Q`,
  CF1AUX_POST_LEFT_TAC);;

let SEP_IMPPOSTe_inv_POSTe_left = prove
 (`!Qe Q. SEP_IMPPOSTe_inv ((POSTe) Qe) Q`,
  CF1AUX_POST_LEFT_TAC);;
