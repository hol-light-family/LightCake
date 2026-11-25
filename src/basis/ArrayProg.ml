(* ========================================================================= *)
(* ArrayProg: port of HOL4 basis/ArrayProgScript.sml (CakeML v3479).         *)
(* A module about Arrays for the CakeML standard basis library.              *)
(* The CakeML text of the Quote add_cakeml blocks is HOL4's, verbatim, at  *)
(* HOL4's source positions (add_cakeml_at).                                  *)
(* ========================================================================= *)

needs "basis/Word8ArrayProg.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

translation_extends "Word8ArrayProg";;

ml_prog_update (ml_prog_open_module "Array");;

ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [implode "'a"] (implode "array")
     (Atapp [Atvar (implode "'a")] (Short (implode "array")))` I);;

append_decs
  `[mlbasicsProg_mk_binop (implode "array") Aalloc;
    mlbasicsProg_mk_unop (implode "arrayEmpty") AallocEmpty;
    mlbasicsProg_mk_binop (implode "sub") Asub;
    mlbasicsProg_mk_unop (implode "length") Alength;
    Dlet unknown_loc (Pvar (implode "update"))
     (Fun (implode "x") (Fun (implode "y") (Fun (implode "z")
       (App Aupdate [Var (Short (implode "x")); Var (Short (implode "y"));
                     Var (Short (implode "z"))]))))]`;;


add_cakeml_at (26,18) {|
  fun fromList l =
    let fun f arr l i =
       case l of
          [] => arr
        | (h::t) => (update arr i h; f arr t (i + 1))
    in
      case l of
        [] => arrayEmpty ()
      | h::t => f (array (List.length l) h) t 1
    end
|};;

add_cakeml_at (39,18) {|
  fun tabulate n f =
    let fun u arr x =
        if x = n then arr
        else (update arr x (f x); u arr (x + 1))
    in
      if n = 0 then
        arrayEmpty ()
      else
        u (array n (f 0)) 1
    end
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (54,18) {|
  fun copy_aux src dst di max n =
    if n = max
      then ()
    else (update dst di (sub src n); copy_aux src dst (di + 1) max (n + 1))
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (63,18) {|
  fun copy src dst di =
    copy_aux src dst di (length src) 0
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (70,18) {|
  fun copyVec_aux src dst di max n =
    if n = max
        then ()
    else (update dst (di + n) (Vector.sub src n); copyVec_aux src dst di max (n + 1))
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (79,18) {|
  fun copyVec src dst di =
    copyVec_aux src dst di (Vector.length src) 0
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (86,18) {|
  fun app_aux f arr max n =
    if n = max
      then ()
    else (f (sub arr n); app_aux f arr max (n + 1))
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (95,18) {|
  fun app f arr =
    app_aux f arr (length arr) 0
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (102,18) {|
  fun appi_aux f arr max n =
    if n = max
      then ()
    else (f n (sub arr n): unit;
          appi_aux f arr max (n + 1))
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (112,18) {|
  fun appi f arr =
    appi_aux f arr (length arr) 0
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (119,18) {|
  fun modify_aux f arr max n =
    if n = max
      then ()
    else (update arr n (f (sub arr n)); modify_aux f arr max (n + 1))
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (128,18) {|
  fun modify f arr =
    modify_aux f arr (length arr) 0
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (135,18) {|
  fun modifyi_aux f arr max n =
    if n = max
      then ()
    else (update arr n (f n (sub arr n)); modifyi_aux f arr max (n + 1))
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (144,18) {|
  fun modifyi f arr =
    modifyi_aux f arr (length arr) 0
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (151,18) {|
  fun foldli_aux f init arr max n =
    if n = max
      then init
    else foldli_aux f (f n (sub arr n) init ) arr max (n + 1)
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (160,18) {|
  fun foldli f init arr =
    foldli_aux f init arr (length arr) 0
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (167,18) {|
  fun foldl_aux f init arr max n =
    if n = max
      then init
    else foldl_aux f (f (sub arr n) init ) arr max (n + 1)
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (176,18) {|
  fun foldl f init arr =
    foldl_aux f init arr (length arr) 0
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (183,18) {|
  fun foldri_aux f init arr n =
    if n = 0
      then init
    else foldri_aux f (f (n - 1) (sub arr (n - 1)) init) arr (n - 1)
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (192,18) {|
  fun foldri f init arr =
    foldri_aux f init arr (length arr)
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (199,18) {|
  fun foldr_aux f init arr n =
    if n = 0
      then init
    else foldr_aux f (f (sub arr (n - 1)) init) arr (n - 1)
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (208,18) {|
  fun foldr f init arr =
    foldr_aux f init arr (length arr)
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (215,18) {|
  fun find_aux f arr max n =
    if n = max
      then None
    else (if f (sub arr n)
        then Some(sub arr n)
      else find_aux f arr max (n + 1))
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (226,18) {|
  fun find f arr =
    find_aux f arr (length arr) 0
|};;

ml_prog_update ml_prog_open_local_block;;

(* Parser bug, see Issue #25 (HOL4 comment): findi_aux as an AST *)
let array_findi_aux =
 `[(Dletrec unknown_loc
[(implode "findi_aux",implode "f",
 Fun (implode "arr")
   (Fun (implode "max")
      (Fun (implode "n")
         (Let (SOME (implode "a"))
            (App Opapp
               [App Opapp [Var (Short (implode "=")); Var (Short (implode "n"))];
                Var (Short (implode "max"))])
            (If (Var (Short (implode "a"))) (Con (SOME (Short (implode "None"))) [])
               (Let (SOME (implode "b"))
                  (App Opapp
                     [App Opapp
                        [Var (Short (implode "sub")); Var (Short (implode "arr"))];
                      Var (Short (implode "n"))])
                  (Let (SOME (implode "c"))
                     (App Opapp
                        [App Opapp
                           [Var (Short (implode "f")); Var (Short (implode "n"))];
                         Var (Short (implode "b"))])
                     (If (Var (Short (implode "c")))
                        (Let (SOME (implode "d"))
                           (App Opapp
                              [App Opapp
                                 [Var (Short (implode "sub"));
                                  Var (Short (implode "arr"))];
                               Var (Short (implode "n"))])
                           (Con (SOME (Short (implode "Some")))
                              [Con NONE [Var (Short (implode "n"));
                               Var (Short (implode "d"))]]))
                        (Let (SOME (implode "e"))
                           (App Opapp
                              [App Opapp
                                 [Var (Short (implode "+"));
                                  Var (Short (implode "n"))];
                               Lit (IntLit (&1))])
                           (App Opapp
                              [App Opapp
                                 [App Opapp
                                    [App Opapp
                                       [Var (Short (implode "findi_aux"));
                                        Var (Short (implode "f"))];
                                     Var (Short (implode "arr"))];
                                  Var (Short (implode "max"))];
                               Var (Short (implode "e"))]))))))))))])]`;;

append_prog array_findi_aux;;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (285,18) {|
  fun findi f arr =
    findi_aux f arr (length arr) 0
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (292,18) {|
  fun exists_aux f arr max n =
    if n = max
      then False
    else (if f (sub arr n)
      then True
    else exists_aux f arr max (n + 1))
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (303,18) {|
  fun exists f arr =
    exists_aux f arr (length arr) 0
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (310,18) {|
  fun all_aux f arr max n =
    if n = max
      then True
    else (if f (sub arr n)
      then all_aux f arr max (n + 1)
    else False)
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (321,18) {|
  fun all f arr =
    all_aux f arr (length arr) 0
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (328,18) {|
  fun collate_aux f a1 a2 max ord n =
    if n = max
      then ord
    else (if f (sub a1 n) (sub a2 n) = Equal
        then collate_aux f a1 a2 max ord (n + 1)
      else f (sub a1 n) (sub a2 n))
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (339,18) {|
  fun collate f a1 a2 =
    if (length a1) < (length a2)
      then collate_aux f a1 a2 (length a1) Less 0
    else if (length a2) < (length a1)
      then collate_aux f a1 a2 (length a2) Greater 0
    else collate_aux f a1 a2 (length a2) Equal 0
|};;

add_cakeml_at (348,18) {|
  val lookup = fn arr => fn default => fn n =>
    sub arr n handle _ => default
|};;

add_cakeml_at (353,18) {|
  val updateResize = fn arr => fn default => fn n => fn v =>
    (update arr n v; arr) handle _ =>
    let
      val arr' = array (2*n+1) default
    in
      (copy arr arr' 0;
       update arr' n v;
       arr')
    end
|};;

ml_prog_update ml_prog_close_local_blocks;;

ml_prog_update (ml_prog_close_module None);;

finalise_translation ();;
