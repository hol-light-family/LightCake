(* Load the whole port and check it: loadt "check.ml";; prints CHECK_OK if every *)
(* file of make.ml loaded and HOL Light's three axioms are the only axioms.      *)

loadt "make.ml";;

let check_files = ["vocab.ml"; "list.ml"; "rich_list.ml"; "basic.ml"; "finite_map.ml"; "alist.ml"; "sptree.ml"; "words4.ml"; "ternaryComparisons.ml"; "toto.ml"; "comparison.ml"; "binary_ieee.ml"; "machine_ieee.ml"; "string4.ml"; "numposrep.ml"; "ASCIInumbers.ml"; "bitstring.ml"; "namespace.ml"; "namespaceProps.ml"; "pattern_common.ml"];;

let check_missing = filter (fun f -> not (exists (fun (g,_) -> g = f) (!loaded_files))) check_files;;
List.iter (fun f -> print_string ("NOT LOADED " ^ f ^ "\n")) check_missing;;
Printf.printf "AXIOMS_COUNT %d\n%!" (List.length (axioms()));;
List.iter (fun th -> print_string ("AXIOM " ^ string_of_term (concl th) ^ "\n")) (axioms());;
print_string (if check_missing = [] && List.length (axioms()) = 3
              then "CHECK_OK\n" else "CHECK_FAILED\n");;
