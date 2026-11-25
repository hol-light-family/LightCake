(* ========================================================================= *)
(* addPrettyPrintersLib: port of HOL4 basis/addPrettyPrintersLib.sml         *)
(* (CakeML v3479).  Library code for applying the type-dec to pp-dec        *)
(* functions (typeDecToPP) to the ml_progLib state.  Used in the basis to    *)
(* install default pretty-printers for some of the basis types.             *)
(*                                                                           *)
(* HOL4's EVAL of pps_for_dec over the program is ml_parseLib's evaluation   *)
(* with the compset of the dependency closure of the term (mlp_eval with     *)
(* mlp_closure_compset).                                                     *)
(* ========================================================================= *)

needs "compiler/printing/typeDecToPP.ml";;
needs "translator/ml_progLib.ml";;
needs "translator/ml_parseLib.ml";;

type_invention_error := true;;

let addpp_empty_local = `Dlocal ([]:dec list) []`;;

let addpp_is_app name n t =
  let f,xs = strip_comb t in
  is_const f && fst (dest_const f) = name && length xs = n;;

(* HOL4 dec_global_only: modules and local blocks become empty local blocks *)
let rec dec_global_only t =
  if addpp_is_app "Dmod" 2 t || addpp_is_app "Dlocal" 2 t then addpp_empty_local
  else let f,xs = strip_comb t in list_mk_comb (f, map dec_global_only xs);;

let addpp_pps_for_dec_empty =
  `pps_for_dec (nsEmpty:(mlstring,mlstring,((mlstring,mlstring)id)option)namespace)`;;

let addpp_MAP_tm = `MAP:(dec->(dec)list)->(dec)list->((dec)list)list`;;
let addpp_FLAT_tm = `FLAT:((dec)list)list->(dec)list`;;

(* num_of_int has no equations: num_of_int (&n) = n on numerals *)
let addpp_num_of_int_conv tm =
  match tm with
    Comb(_, Comb(i, n)) when is_numeral n && is_const i &&
                             fst (dest_const i) = "int_of_num" ->
      SPEC n NUM_OF_INT_OF_NUM
  | _ -> failwith "addpp_num_of_int_conv";;

(* HOL4 pps_of_global_tys: the pretty-printer declarations of the global    *)
(* types of a program (a CONS list of declarations)                         *)
let pps_of_global_tys prog =
  let gl = dec_global_only prog in
  let app = mk_comb (addpp_FLAT_tm, list_mk_comb (addpp_MAP_tm, [addpp_pps_for_dec_empty; gl])) in
  let cs = mlp_closure_compset ~allowed:["num_of_int"] [app] in
  Mlp_compute.add_conv (`num_of_int`, 1, addpp_num_of_int_conv) cs;
  let th = mlp_eval cs app in
  dest_list (rhs (concl th));;

(* HOL4 add_pps *)
let add_pps pps prog_st =
  List.fold_left (fun prog_st pp -> ml_prog_add_dec pp I prog_st) prog_st pps;;
