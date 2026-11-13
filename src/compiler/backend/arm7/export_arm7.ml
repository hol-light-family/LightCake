(* ========================================================================= *)
(* export_arm7: port of HOL4                                                 *)
(* compiler/backend/arm7/export_arm7Script.sml (CakeML v3479).               *)
(* Define the format of the compiler-generated .S file for ARMv7.            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/export.ml";;

type_invention_error := true;;

(* Notation as in export.ml: the mlstring literal syntax is implode "...";   *)
(* misc$List is misc_List; word32 is int32.  Names                           *)
(* (notes/naming/names.tsv): startup, ffi_asm, export_func and               *)
(* export_funcs are export_arm7_startup, export_arm7_ffi_asm,                *)
(* export_arm7_export_func and export_arm7_export_funcs.  The HOL4 script    *)
(* builds parts of arm7_export_def in ML: the values ffi_code and            *)
(* entry_point_code are terms computed with EVAL and spliced in by           *)
(* antiquotation.  They are computed the same way here (export_arm7_EVAL,    *)
(* the HOL Light counterpart of EVAL on these terms: beta reduction, then    *)
(* MAP, APPEND and conditionals on literals) and substituted for the         *)
(* variables ffi_code and entry_point_code of the quotation of               *)
(* arm7_export_def.                                                          *)

(*
CakeML expects 4 arguments in order:

r0 - entry address i.e., the address of cake_main
r1 - first address of heap
r2 - first address of stack
r3 - first address past the stack

In addition, the first address on the heap should store the address of
cake_bitmaps

Note: this set up does NOT account for restoring clobbered registers
*)

(* HOL4: startup_def *)

let export_arm7_startup_def = cake_def
  `export_arm7_startup ret pk =
    SmartAppend (misc_List
      [implode "\n";
       implode "/* Start up code */\n";
       implode "\n";
       implode "     .text\n";
       implode "     .p2align 3\n";
       implode "     .globl  cdecl(cml_main)\n";
       implode "     .globl  cdecl(cml_heap)\n";
       implode "     .globl  cdecl(cml_stack)\n";
       implode "     .globl  cdecl(cml_stackend)\n";
       implode "     .type   cml_main, function\n";
       implode "cdecl(cml_main):\n";
       implode "     ldr    r0,=cake_main            /* arg1: entry address */\n";
       implode "     ldr    r1,=cdecl(cml_heap)      /* arg2: first address of heap */\n";
       implode "     ldr    r1,[r1]\n"])
    (SmartAppend (misc_List
      (if ~pk then
        [implode "     ldr    r2,=cake_bitmaps\n";
         implode "     str    r2,[r1]                  /* store bitmap pointer */\n"]
      else []))
    (SmartAppend (misc_List
      [implode "     ldr    r2,=cdecl(cml_stack)     /* arg3: first address of stack */\n";
       implode "     ldr    r2,[r2]\n";
       implode "     ldr    r3,=cdecl(cml_stackend)  /* arg4: first address past the stack */\n";
       implode "     ldr    r3,[r3]\n"])
    (SmartAppend (misc_List
      (if ret then
        [implode "     b      cml_enter\n"]
      else
        [implode "     b      cake_main\n"]))
    (misc_List
      [implode "     .ltorg\n";
       implode "\n"]))))`;;

(* HOL4: ffi_asm_def *)

let export_arm7_ffi_asm_def = cake_def
  `(export_arm7_ffi_asm [] = Nil) /\
  (export_arm7_ffi_asm (CONS ffi ffis) =
      SmartAppend (misc_List [
       implode "cake_ffi"; ffi; implode ":\n";
       implode "     b     cdecl(ffi"; ffi; implode ")\n";
       implode "     .p2align 4\n";
       implode "\n"]) (export_arm7_ffi_asm ffis))`;;

(* the HOL4 EVAL of the ML values below *)

let export_arm7_EVAL tm =
  rhs(concl((TRY_CONV BETA_CONV THENC REWRITE_CONV[MAP; APPEND]) tm));;

let export_arm7_ffi_code' =
  `\ret. SmartAppend
    (misc_List (MAP (\n. implode (APPEND n "\n"))
     ["/* CakeML FFI interface (each block is 16 bytes long) */";
       "";
       "     .p2align 4";
       ""]))
    (SmartAppend
     (export_arm7_ffi_asm (REVERSE (ffi_names:mlstring list)))
     (misc_List (MAP (\n. implode (APPEND n "\n"))
      (APPEND (APPEND
       ["cake_clear:";
       "     b   cdecl(cml_exit)";
       "     .p2align 4";
       "";
       "cake_exit:"]
       (if ret then
         ["     b   cml_return"]
       else
         ["     b   cdecl(cml_exit)"]))
      ["     .p2align 4";
       "";
       "cake_main:";
       "";
       "/* Generated machine code follows */";
       ""]))))`;;

let export_arm7_ffi_code_true = export_arm7_EVAL (mk_comb(export_arm7_ffi_code',`T`))
and export_arm7_ffi_code_false = export_arm7_EVAL (mk_comb(export_arm7_ffi_code',`F`));;

let export_arm7_ffi_code =
  mk_abs(`ret:bool`,
         mk_cond(`ret:bool`,export_arm7_ffi_code_true,export_arm7_ffi_code_false));;

let export_arm7_entry_point_code = export_arm7_EVAL
  `(misc_List (MAP (\n. implode (APPEND n "\n"))
    [""; "";
     "cml_enter:";
     "     push   {r5,r6,r8,r10,r11,lr}";
     "     b      cake_main";
     "     .p2align 4";
     ""; "";
     "cake_enter:";
     "     push   {r5,r6,r8,r10,r11,lr}";
     "     ldr    r5,=can_enter";
     "     ldr    r6, [r5]";
     "     cmp    r6, #0";
     "     beq    cake_err3";
     "     mov    r6, #0";
     "     str    r6, [r5]";
     "     ldr    r5,=ret_base";
     "     ldr    r10, [r5]";
     "     ldr    r5,=ret_stack";
     "     ldr    r11, [r5]";
     "     ldr    r5,=ret_stackend";
     "     ldr    r8, [r5]";
     "     ldr    lr,=cake_return";
     "     bx     r4";
     "     .p2align 4";
     ""; "";
     "cml_return:";
     "     ldr    r5,=ret_base";
     "     str    r10, [r5]";
     "     ldr    r5,=ret_stack";
     "     str    r11, [r5]";
     "     ldr    r5,=ret_stackend";
     "     str    r8, [r5]";
     "";
     "cake_return:";
     "     ldr    r5,=can_enter";
     "     mov    r6, #1";
     "     str    r6, [r5]";
     "     pop    {r5,r6,r8,r10,r11,lr}";
     "     pop    {r4}";
     "     bx     lr";
     "     .p2align 4";
     ""; "";
     "cake_err3:";
     "     mov    r0, #3";
     "     b      cdecl(cml_err)";
     "     .p2align 4";
     ""]))`;;

(* HOL4: export_func_def *)

let export_arm7_export_func_def = cake_def
  `export_arm7_export_func appl (name,label,start:A,len:B) =
    SmartAppend appl (misc_List
    [implode "\n     .globl  cdecl("; name; implode ")\n";
     implode "     .type   "; name; implode ", function\n";
     implode "cdecl("; name; implode "):\n";
     implode "     push   {r4}\n";
     implode "     ldr    r4,="; name; implode "_jmp\n";
     implode "     b       cake_enter\n";
            name; implode "_jmp:\n";
     implode "     b       "; label; implode "\n"
    ])`;;

(* HOL4: export_funcs_def *)

let export_arm7_export_funcs_def = cake_def
  `export_arm7_export_funcs (lsyms:(mlstring#mlstring#A#B)list) exp =
    FOLDL export_arm7_export_func Nil (FILTER ((flip MEM exp) o FST) lsyms)`;;

let arm7_export_def = cake_def (vsubst
  [export_arm7_ffi_code,`ffi_code:bool->mlstring app_list`;
   export_arm7_entry_point_code,`entry_point_code:mlstring app_list`]
  `arm7_export (ffi_names:mlstring list) bytes (data:int32 list) syms exp ret pk =
    let lsyms = get_sym_labels syms in
    SmartAppend
      (SmartAppend (misc_List preamble)
      (SmartAppend (misc_List (data_section ".long" ret))
      (SmartAppend (split16 (words_line (implode "\t.long ") word_to_string) data)
      (SmartAppend (misc_List data_buffer)
      (SmartAppend (export_arm7_startup ret pk) (ffi_code ret))))))
      (SmartAppend (split16 (words_line (implode "\t.byte ") byte_to_string) bytes)
      (SmartAppend (misc_List code_buffer)
      (SmartAppend (emit_symbols lsyms)
      (if ret then
        (SmartAppend entry_point_code (export_arm7_export_funcs lsyms exp))
      else misc_List []))))`);;
