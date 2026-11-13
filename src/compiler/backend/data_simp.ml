(* ========================================================================= *)
(* data_simp: port of HOL4 compiler/backend/data_simpScript.sml             *)
(* (CakeML v3479).                                                           *)
(* This simple compiler phase cleans up dataLang programs.  The simp         *)
(* optimisation removes Skips and deletes some dead code created by Raise    *)
(* and Return.  Example:                                                     *)
(*   Seq (Seq Skip (Raise n)) anything_here                                  *)
(* translates into                                                           *)
(*   Raise n                                                                 *)
(* It also right-associates Seq, e.g.                                        *)
(*   Seq (Seq x1 x2) x3 --> Seq x1 (Seq x2 x3)                               *)
(*                                                                           *)
(* Notes on the rendering: simp (a catch-all clause completed into one       *)
(* clause per remaining constructor, as HOL4's TFL does) is defined with     *)
(* sem1aux_def (semantics/sem1aux_tfl.ml).                                   *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/dataLang.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

let pSeq_def = cake_def
  `pSeq c1 c2 = if c2 = data_Skip then c1 else data_Seq c1 c2`;;

let simp_def = sem1aux_def (list_mk_conj
  [`(simp:data_prog->data_prog->data_prog) data_Skip c = c`;
   `(simp:data_prog->data_prog->data_prog) (data_Return n) c = data_Return n`;
   `(simp:data_prog->data_prog->data_prog) (data_Raise n) c = data_Raise n`;
   `(simp:data_prog->data_prog->data_prog) (data_Seq c1 c2) c = simp c1 (simp c2 c)`;
   `(simp:data_prog->data_prog->data_prog) (data_If n c2 c3) c =
      pSeq (data_If n (simp c2 data_Skip) (simp c3 data_Skip)) c`;
   `(simp:data_prog->data_prog->data_prog) (data_Call ret dest args (SOME (v,handler))) c =
      pSeq (data_Call ret dest args (SOME (v,simp handler data_Skip))) c`;
   `(simp:data_prog->data_prog->data_prog) c1 c2 = pSeq c1 c2`]);;

let simp_ind = cake_ind "simp";;
