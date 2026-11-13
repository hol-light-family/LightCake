(* ========================================================================= *)
(* labLang: port of HOL4 compiler/backend/labLangScript.sml (CakeML v3479).  *)
(* The labLang intermediate language is a target-neutral assembly language  *)
(* at the bottom end of the compiler backend.                                *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 Type reg = num is the HOL Light type abbreviation lab_reg; HOL4    *)
(*   Type prog = ('a sec) list is written out where used ((A)sec list).      *)
(* - The constructors that clash with other ILs carry the prefix lab_        *)
(*   (lab_Lab, lab_Jump, lab_Call, lab_Label, ...), as names.tsv says.        *)
(* - word8 is byte.                                                          *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/encoders/asm/asm.ml";;

prioritize_num();;
type_invention_error := true;;

new_type_abbrev("lab_reg",`:num`);;

(* A label refers to either a section name or a local label definition      *)
(* within the current section.                                              *)

let lab_INDUCT,lab_RECURSION = cake_type
  "lab = lab_Lab num num";;

(* Each line of a section consists of either a label, an assembly           *)
(* instruction (without a label) or some labelled asm instruction.          *)
(* CallFFI, Install and Halt have no label, but have similar semantics.     *)

let asm_with_lab_INDUCT,asm_with_lab_RECURSION = cake_type
  "asm_with_lab = lab_Jump lab
                | lab_JumpCmp cmp lab_reg ((A)reg_imm) lab
                | lab_Call lab
                | lab_LocValue lab_reg lab
                | CallFFI mlstring
                | lab_Install
                | lab_Halt";;

(* Either an asm inst/jumpreg or code-buffer-write *)

let asm_or_cbw_INDUCT,asm_or_cbw_RECURSION = cake_type
  "asm_or_cbw = Asmi ((A)asm) | Cbw lab_reg lab_reg
              | ShareMem memop lab_reg ((A)addr)";;

(* lab_Label: section number, label number, length; Asm: instruction,       *)
(* encoded instruction, length; LabAsm: position, encoded instruction,      *)
(* length.                                                                   *)

let line_INDUCT,line_RECURSION = cake_type
  "line = lab_Label num num num
        | Asm ((A)asm_or_cbw) (byte list) num
        | LabAsm ((A)asm_with_lab) (A word) (byte list) num";;

(* A section consists a name (num) and a list of assembly lines. *)

let sec_INDUCT,sec_RECURSION = cake_type
  "sec = Section num (((A)line)list)";;

(* HOL4: Section_num_def *)

let lab_Section_num_def = cake_def
  `Section_num (Section k (_:((A)line)list)) = k`;;

let _ = cake_add_simps [lab_Section_num_def];;

(* HOL4: Section_lines_def *)

let lab_Section_lines_def = cake_def
  `Section_lines (Section _ lines:(A)sec) = lines`;;

let _ = cake_add_simps [lab_Section_lines_def];;

(* A full assembly program consists of a list of sections.                  *)
(* HOL4: Type prog = ``:('a sec) list``  (written out where used)            *)
