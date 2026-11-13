(* ========================================================================= *)
(* export_mips: port of HOL4                                                 *)
(* compiler/backend/mips/export_mipsScript.sml (CakeML v3479).               *)
(* Define the format of the compiler-generated .S file for MIPS.             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/export.ml";;

type_invention_error := true;;

(* Notation as in export.ml: the mlstring literal syntax is implode "...";   *)
(* misc$List is misc_List; word64 is int64.  Names                           *)
(* (notes/naming/names.tsv): startup, ffi_asm, export_func and               *)
(* export_funcs are export_mips_startup, export_mips_ffi_asm,                *)
(* export_mips_export_func and export_mips_export_funcs.  The HOL4 script    *)
(* builds parts of mips_export_def in ML: the values ffi_code and            *)
(* entry_point_code are terms computed with EVAL and spliced in by           *)
(* antiquotation.  They are computed the same way here (export_mips_EVAL,    *)
(* the HOL Light counterpart of EVAL on these terms: beta reduction, then    *)
(* MAP, APPEND and conditionals on literals) and substituted for the         *)
(* variables ffi_code and entry_point_code of the quotation of               *)
(* mips_export_def.                                                          *)

(*
CakeML expects 4 arguments in order:

a0 - entry address i.e., the address of cake_main
a1 - first address of heap
a2 - first address of stack
a3 - first address past the stack

In addition, the first address on the heap should store the address of
cake_bitmaps

Note: this set up does NOT account for restoring clobbered registers
*)

(* HOL4: startup_def *)

let export_mips_startup_def = cake_def
  `export_mips_startup ret pk =
    SmartAppend (misc_List
      [implode "\n";
       implode "#### Start up code\n";
       implode "     .text\n";
       implode "     .p2align 3\n";
       implode "     .globl  cdecl(cml_main)\n";
       implode "     .globl  cdecl(cml_heap)\n";
       implode "     .globl  cdecl(cml_stack)\n";
       implode "     .globl  cdecl(cml_stackend)\n";
       implode "     .type   cml_main, function\n";
       implode "cdecl(cml_main):\n";
       implode "     dla     $a0,cake_main           # arg1: entry address\n";
       implode "     ld      $a1,cdecl(cml_heap)     # arg2: first address of heap\n"])
    (SmartAppend (misc_List
      (if ~pk then
        [implode "     dla     $t0,cake_bitmaps\n";
         implode "     sd      $t0, 0($a1)             # store bitmap pointer\n"]
      else []))
    (SmartAppend (misc_List
      [implode "     ld      $a2,cdecl(cml_stack)    # arg3: first address of stack\n";
       implode "     ld      $a3,cdecl(cml_stackend) # arg4: first address past the stack\n"])
    (SmartAppend (misc_List
      (if ret then
        [implode "     j       cml_enter\n"]
      else
        [implode "     j       cake_main\n"]))
    (misc_List
      [implode "     nop\n";
       implode "\n"]))))`;;

(* HOL4: ffi_asm_def *)

let export_mips_ffi_asm_def = cake_def
  `(export_mips_ffi_asm [] = Nil) /\
  (export_mips_ffi_asm (CONS ffi ffis) =
      SmartAppend (misc_List [
       implode "cake_ffi"; ffi; implode ":\n";
       implode "     dla    $t9,cdecl(ffi"; ffi; implode ")\n";
       implode "     jr     $t9\n";
       implode "     .p2align 4\n";
       implode "\n"]) (export_mips_ffi_asm ffis))`;;

(* the HOL4 EVAL of the ML values below *)

let export_mips_EVAL tm =
  rhs(concl((TRY_CONV BETA_CONV THENC REWRITE_CONV[MAP; APPEND]) tm));;

let export_mips_ffi_code' =
  `\ret. SmartAppend
    (misc_List (MAP (\n. implode (APPEND n "\n"))
     ["#### CakeML FFI interface (each block is 16 bytes long)";
       "";
       "     .p2align 4";
       ""]))
    (SmartAppend
     (export_mips_ffi_asm (REVERSE (ffi_names:mlstring list)))
     (misc_List (MAP (\n. implode (APPEND n "\n"))
      (APPEND (APPEND
       ["cake_clear:";
       "     dla   $t9,cdecl(cml_exit)";
       "     jr    $t9";
       "     .p2align 4";
       "";
       "cake_exit:"]
       (if ret then
         ["     j    cml_return"]
       else
        ["     dla   $t9,cdecl(cml_exit)";
         "     jr    $t9"]))
       ["     .p2align 4";
       "";
       "cake_main:";
       "";
       "#### Generated machine code follows";
       ""]))))`;;

let export_mips_ffi_code_true = export_mips_EVAL (mk_comb(export_mips_ffi_code',`T`))
and export_mips_ffi_code_false = export_mips_EVAL (mk_comb(export_mips_ffi_code',`F`));;

let export_mips_ffi_code =
  mk_abs(`ret:bool`,
         mk_cond(`ret:bool`,export_mips_ffi_code_true,export_mips_ffi_code_false));;

let export_mips_entry_point_code = export_mips_EVAL
  `(misc_List (MAP (\n. implode (APPEND n "\n"))
    [""; "";
     "cml_enter:";
     "     daddiu  $sp, $sp, -72";
     "     sd      $ra, 0($sp)";
     "     sd      $s7, 8($sp)";
     "     sd      $s6, 16($sp)";
     "     sd      $s5, 24($sp)";
     "     sd      $s4, 32($sp)";
     "     sd      $s3, 40($sp)";
     "     sd      $s2, 48($sp)";
     "     sd      $s1, 56($sp)";
     "     sd      $s0, 64($sp)";
     "     j       cake_main";
     "     .p2align 4";
     ""; "";
     "cake_enter:";
     "     daddiu  $sp, $sp, -72";
     "     sd      $ra, 0($sp)";
     "     sd      $s7, 8($sp)";
     "     sd      $s6, 16($sp)";
     "     sd      $s5, 24($sp)";
     "     sd      $s4, 32($sp)";
     "     sd      $s3, 40($sp)";
     "     sd      $s2, 48($sp)";
     "     sd      $s1, 56($sp)";
     "     sd      $s0, 64($sp)";
     "     dla     $t1, can_enter";
     "     ld      $t2, 0($t1)";
     "     beq     $t2, $zero, cake_err3";
     "     sd      $zero, 0($t1)";
     "     dla     $t1, ret_base";
     "     ld      $s7, 0($t1)";
     "     dla     $t1, ret_stack";
     "     ld      $s5, 0($t1)";
     "     dla     $t1, ret_stackend";
     "     ld      $s6, 0($t1)";
     "     dla     $ra, cake_return";
     "     jr      $t0";
     "     .p2align 4";
     ""; "";
     "cml_return:";
     "     dla     $t1, ret_base";
     "     sd      $s7, 0($t1)";
     "     dla     $t1, ret_stack";
     "     sd      $s5, 0($t1)";
     "     dla     $t1, ret_stackend";
     "     sd      $s6, 0($t1)";
     "";
     "cake_return:";
     "     dla     $t1, can_enter";
     "     li      $t2, 1";
     "     sd      $t2, 0($t1)";
     "     move    $v0, $a0";
     "     ld      $s0, 64($sp)";
     "     ld      $s1, 56($sp)";
     "     ld      $s2, 48($sp)";
     "     ld      $s3, 40($sp)";
     "     ld      $s4, 32($sp)";
     "     ld      $s5, 24($sp)";
     "     ld      $s6, 16($sp)";
     "     ld      $s7, 8($sp)";
     "     ld      $ra, 0($sp)";
     "     daddiu  $sp, $sp, 72";
     "     jr      $ra";
     "     .p2align 4";
     ""; "";
     "cake_err3:";
     "     li      $a0, 3";
     "     dla     $t9,cdecl(cml_err)";
     "     jr      $t9";
     "     .p2align 4";
     ""]))`;;

(* HOL4: export_func_def *)

let export_mips_export_func_def = cake_def
  `export_mips_export_func appl (name,label,start:A,len:B) =
    SmartAppend appl (misc_List
    [implode "\n     .globl  cdecl("; name; implode ")\n";
     implode "     .type   "; name; implode ", function\n";
     implode "cdecl("; name; implode "):\n";
     implode "     dla     $t0, "; name; implode "_jmp\n";
     implode "     j       cake_enter\n";
            name; implode "_jmp:\n";
     implode "     j       "; label; implode "\n"
    ])`;;

(* HOL4: export_funcs_def *)

let export_mips_export_funcs_def = cake_def
  `export_mips_export_funcs (lsyms:(mlstring#mlstring#A#B)list) exp =
    FOLDL export_mips_export_func Nil (FILTER ((flip MEM exp) o FST) lsyms)`;;

let mips_export_def = cake_def (vsubst
  [export_mips_ffi_code,`ffi_code:bool->mlstring app_list`;
   export_mips_entry_point_code,`entry_point_code:mlstring app_list`]
  `mips_export (ffi_names:mlstring list) bytes (data:int64 list) syms exp ret pk =
    let lsyms = get_sym_labels syms in
    SmartAppend
      (SmartAppend (misc_List preamble)
      (SmartAppend (misc_List (data_section ".quad" ret))
      (SmartAppend (split16 (words_line (implode "\t.quad ") word_to_string) data)
      (SmartAppend (misc_List data_buffer)
      (SmartAppend (export_mips_startup ret pk) (ffi_code ret))))))
      (SmartAppend (split16 (words_line (implode "\t.byte ") byte_to_string) bytes)
      (SmartAppend (misc_List code_buffer)
      (SmartAppend (emit_symbols lsyms)
      (if ret then
        (SmartAppend entry_point_code (export_mips_export_funcs lsyms exp))
      else misc_List []))))`);;
