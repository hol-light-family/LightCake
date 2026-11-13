(* Load the whole port: start HOL Light in this directory, then loadt "make.ml";; *)

use_file_raise_failure := true;;

loadt "src/prelude.ml";;

needs "hol4/vocab.ml";;
needs "hol4/list.ml";;
needs "hol4/rich_list.ml";;
needs "hol4/basic.ml";;
needs "hol4/finite_map.ml";;
needs "hol4/alist.ml";;
needs "hol4/sptree.ml";;
needs "hol4/words4.ml";;
needs "hol4/ternaryComparisons.ml";;
needs "hol4/toto.ml";;
needs "hol4/comparison.ml";;
needs "hol4/binary_ieee.ml";;
needs "hol4/machine_ieee.ml";;
needs "hol4/string4.ml";;
needs "hol4/numposrep.ml";;
needs "hol4/ASCIInumbers.ml";;
needs "hol4/bitstring.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "compiler/backend/pattern_matching/pattern_common.ml";;
