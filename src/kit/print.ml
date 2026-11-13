(* ========================================================================= *)
(* CakeML kit: printing case constants as HOL4 case expressions.             *)
(*                                                                           *)
(*   ty_CASE x (\a. e1) (\b c. e2)   prints as                               *)
(*   (case x of C1 a => e1 | C2 b c => e2)                                   *)
(* (print only: terms are never parsed back in this syntax; write match in  *)
(* quotations).  delete_user_printer "cake_case" turns it off.               *)
(* ========================================================================= *)

let print_case_term fmt tm =
  if not (is_case_app tm) then failwith "print_case_term" else
  let c,x,fs = dest_case_app tm in
  let ci = case_info_of_const c in
  let xty = type_of x in
  let arms = map2 (fun (vs,pat) f ->
      let tyi = type_match (type_of pat) xty [] in
      let vs = map (inst tyi) vs and pat = inst tyi pat in
      let k = length vs in
      let rec take_abs n t acc =
        if n = 0 then Some(rev acc,t)
        else if is_abs t then let v,b = dest_abs t in take_abs (n-1) b (v::acc)
        else None in
      match take_abs k f [] with
        Some(vs',body) -> vsubst (zip vs' vs) pat,body
      | None -> pat,list_mk_comb(f,vs))
    ci.ci_pats fs in
  pp_open_hvbox fmt 1;
  pp_print_string fmt "(case ";
  pp_print_term fmt x;
  pp_print_string fmt " of";
  let first = ref true in
  do_list (fun (p,b) ->
      (if !first then (pp_print_break fmt 1 2; first := false)
       else (pp_print_space fmt (); pp_print_string fmt "| "));
      pp_open_hvbox fmt 2;
      pp_print_term fmt p;
      pp_print_string fmt " =>";
      pp_print_space fmt ();
      pp_print_term fmt b;
      pp_close_box fmt ()) arms;
  pp_print_string fmt ")";
  pp_close_box fmt ();;

install_user_printer("cake_case",print_case_term);;
