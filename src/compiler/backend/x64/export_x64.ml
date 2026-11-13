(* ========================================================================= *)
(* export_x64: port of HOL4 compiler/backend/x64/export_x64Script.sml        *)
(* (CakeML v3479).  Define the format of the compiler-generated .S file for *)
(* x64.                                                                      *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/export.ml";;

type_invention_error := true;;

(* Notation as in export.ml: the mlstring literal syntax is implode "...";  *)
(* misc$List is misc_List; word64 is int64.  Names (notes/naming/names.tsv): *)
(* startup, ffi_asm, export_func and export_funcs are export_x64_startup,    *)
(* export_x64_ffi_asm, export_x64_export_func and export_x64_export_funcs.   *)
(* The HOL4 script builds parts of x64_export_def in ML: the values          *)
(* ffi_code, windows_ffi_code and entry_point_code are terms computed with   *)
(* EVAL and spliced in by antiquotation.  They are computed the same way     *)
(* here (export_x64_EVAL, the HOL Light counterpart of EVAL on these terms:  *)
(* beta reduction, then MAP, APPEND and conditionals on literals) and        *)
(* substituted for the variables ffi_code, windows_ffi_code and              *)
(* entry_point_code of the quotation of x64_export_def.                      *)

(*
CakeML expects 4 arguments in order:

RDI - entry address i.e., the address of cake_main
RSI - first address of heap
RDX - first address of stack
RCX - first address past the stack

In addition, the first address on the heap should store the address of
cake_bitmaps

Note: this set up does NOT account for restoring clobbered registers
*)

(* HOL4: startup_def *)

let export_x64_startup_def = cake_def
  `export_x64_startup ret pk =
    SmartAppend (misc_List
      [implode "\n";
       implode "/* Start up code */\n";
       implode "\n";
       implode "     .text\n";
       implode "     .p2align 12\n";
       implode "     .globl  cdecl(cake_text_begin)\n";
       implode "cdecl(cake_text_begin):\n";
       implode "     .globl  cdecl(cml_main)\n";
       implode "     .globl  cdecl(cml_heap)\n";
       implode "     .globl  cdecl(cml_stack)\n";
       implode "     .globl  cdecl(cml_stackend)\n";
       implode "#if defined(__APPLE__)\n";
       implode "\n";
       implode "#elif defined(__WIN32)\n";
       implode "     .func   cml_main\n";
       implode "#else\n";
       implode "     .type   cml_main, function\n";
       implode "#endif\n";
       implode "cdecl(cml_main):\n";
       implode "     pushq   %rbp                            # push base pointer\n";
       implode "     movq    %rsp, %rbp                      # save stack pointer\n";
       implode "     leaq    cake_main(%rip), %rdi           # arg1: entry address\n";
       implode "     movq    cdecl(cml_heap)(%rip), %rsi     # arg2: first address of heap\n"])
    (SmartAppend (misc_List
      (if ~pk then
        [implode "     leaq    cake_bitmaps(%rip), %rax\n";
         implode "     movq    %rax, 0(%rsi)                   # store bitmap pointer\n";
         implode "     leaq    cdecl(cake_bitmaps_buffer_begin)(%rip), %rax\n";
         implode "     movq    %rax, 8(%rsi)                   # store bitmap mutable start pointer\n";
         implode "     leaq    cdecl(cake_bitmaps_buffer_end)(%rip), %rax\n";
         implode "     movq    %rax, 16(%rsi)                  # store bitmap mutable end pointer\n";
         implode "     leaq    cdecl(cake_codebuffer_begin)(%rip), %rax\n";
         implode "     movq    %rax, 24(%rsi)                  # store code mutable start pointer\n";
         implode "     leaq    cdecl(cake_codebuffer_end)(%rip), %rax\n";
         implode "     movq    %rax, 32(%rsi)                  # store code mutable end pointer\n"]
      else []))
    (SmartAppend (misc_List
      [implode "     movq    cdecl(cml_stack)(%rip), %rdx    # arg3: first address of stack\n";
       implode "     movq    cdecl(cml_stackend)(%rip), %rcx # arg4: first address past the stack\n"])
    (SmartAppend (misc_List
      (if ret then
        [implode "     jmp     cml_enter\n"]
      else
        [implode "     jmp     cake_main\n"]))
    (misc_List
      [implode "\n";
       implode "#if defined(__WIN32)\n";
       implode "     .endfunc\n";
       implode "#endif\n"]))))`;;

(* HOL4: ffi_asm_def *)

let export_x64_ffi_asm_def = cake_def
  `(export_x64_ffi_asm [] = Nil) /\
   (export_x64_ffi_asm (CONS ffi ffis) =
      SmartAppend (misc_List [
       implode "cake_ffi"; ffi; implode ":\n";
       implode "     pushq   %rax\n";
       implode "     jmp     wcdecl(ffi"; ffi; implode ")\n";
       implode "     .p2align 4\n";
       implode "\n"]) (export_x64_ffi_asm ffis))`;;

(* the HOL4 EVAL of the ML values below *)

let export_x64_EVAL tm =
  rhs(concl((TRY_CONV BETA_CONV THENC REWRITE_CONV[MAP; APPEND]) tm));;

let export_x64_ffi_code' =
  `\ret. SmartAppend
    (misc_List (MAP (\n. implode (APPEND n "\n"))
     ["/* CakeML FFI interface (each block is 16 bytes long) */";
       "";
       "     .p2align 4";
       ""]))
    (SmartAppend
     (export_x64_ffi_asm (REVERSE (ffi_names:mlstring list)))
     (misc_List (MAP (\n. implode (APPEND n "\n"))
      (APPEND (APPEND
      ["cake_clear:";
       "     pushq   %rax";
       "     pushq   %rdi";
       "     callq   wcdecl(cml_clear)";
       "     popq    %rdi";
       "     ret";
       "     .p2align 4";
       "";
       "cake_exit:"]
       (if ret then
         ["     jmp     cml_return"]
       else
         ["     callq   cdecl(cml_exit)"]))
       ["     .p2align 4";
       "";
       "cake_main:";
       "";
       "/* Generated machine code follows */";
       ""]))))`;;

let export_x64_ffi_code_true = export_x64_EVAL (mk_comb(export_x64_ffi_code',`T`))
and export_x64_ffi_code_false = export_x64_EVAL (mk_comb(export_x64_ffi_code',`F`));;

let export_x64_ffi_code =
  mk_abs(`ret:bool`,
         mk_cond(`ret:bool`,export_x64_ffi_code_true,export_x64_ffi_code_false));;

let windows_ffi_asm_def = cake_def
  `(windows_ffi_asm [] = Nil) /\
   (windows_ffi_asm (CONS ffi ffis) =
      SmartAppend (misc_List [
       implode "windows_ffi"; ffi; implode ":\n";
       implode "     movq    %rcx, %r9\n";
       implode "     movq    %rdx, %r8\n";
       implode "     movq    %rsi, %rdx\n";
       implode "     movq    %rdi, %rcx\n";
       implode "     jmp     cdecl(ffi"; ffi; implode ")\n";
       implode "\n"]) (windows_ffi_asm ffis))`;;

(* if ret: no need to treat cake_exit as a function *)

let export_x64_windows_ffi_code' =
  `\ret. SmartAppend
    (
     misc_List [implode "\n/* Windows Compatibility for CakeML FFI interface */\n\n"]
    )
    (
    SmartAppend
     (windows_ffi_asm (REVERSE (ffi_names:mlstring list)))
     (misc_List (MAP (\n. implode (APPEND n "\n"))
      (APPEND
       ["windows_cml_clear:";
        "     movq    %rcx, %r9";
        "     movq    %rdx, %r8";
        "     movq    %rsi, %rdx";
        "     movq    %rdi, %rcx";
        "     jmp     cdecl(cml_clear)"]
       (if ret then
         []
       else
         ["windows_cml_exit:";
         "     movq    %rcx, %r9";
         "     movq    %rdx, %r8";
         "     movq    %rsi, %rdx";
         "     movq    %rdi, %rcx";
         "     callq   cdecl(cml_exit)"])))))`;;

let export_x64_windows_ffi_code_true =
  export_x64_EVAL (mk_comb(export_x64_windows_ffi_code',`T`))
and export_x64_windows_ffi_code_false =
  export_x64_EVAL (mk_comb(export_x64_windows_ffi_code',`F`));;

let export_x64_windows_ffi_code =
  mk_abs(`ret:bool`,
         mk_cond(`ret:bool`,export_x64_windows_ffi_code_true,
                 export_x64_windows_ffi_code_false));;

let export_x64_entry_point_code = export_x64_EVAL
  `(misc_List (MAP (\n. implode (APPEND n "\n"))
    ["cml_enter:";
     "     sub     $0x30, %rsp";
     "     movq    %r12, -0x8(%rbp)";
     "     movq    %r13, -0x10(%rbp)";
     "     movq    %r14, -0x18(%rbp)";
     "     movq    %r15, -0x20(%rbp)";
     "     movq    %rbx, -0x28(%rbp)";
     "     jmp     cake_main";
     "";
     "windows_cake_enter:";
     "     movq    %rcx, %rdi";
     "     movq    %rdx, %rsi";
     "     movq    %r8, %rdx";
     "     movq    %r9, %rcx";
     "";
     "cake_enter:";
     "     pushq   %rbp";
     "     movq    %rsp, %rbp";
     "     sub     $0x30, %rsp";
     "     movq    %r12, -0x8(%rbp)";
     "     movq    %r13, -0x10(%rbp)";
     "     movq    %r14, -0x18(%rbp)";
     "     movq    %r15, -0x20(%rbp)";
     "     movq    %rbx, -0x28(%rbp)";
     "     movq    can_enter(%rip), %r11";
     "     cmp     $0, %r11";
     "     je      cake_err3";
     "     movq    $0, can_enter(%rip)";
     "     movq    ret_base(%rip), %r14";
     "     movq    ret_stack(%rip), %r12";
     "     movq    ret_stackend(%rip), %r13";
     "     lea     cake_return(%rip), %rax";
     "     jmp     *%r10";
     "     .p2align 4";
     "";
     "cml_return:";
     "     movq    %r14, ret_base(%rip)";
     "     movq    %r12, ret_stack(%rip)";
     "     movq    %r13, ret_stackend(%rip)";
     "";
     "cake_return:";
     "     movq    $1, can_enter(%rip)";
     "     mov     %edi, %eax";
     "     movq    -0x28(%rbp),%rbx";
     "     movq    -0x20(%rbp),%r15";
     "     movq    -0x18(%rbp),%r14";
     "     movq    -0x10(%rbp),%r13";
     "     movq    -0x8(%rbp),%r12";
     "     leave";
     "     ret";
     "     .p2align 4";
     "";
     "cake_err3:";
     "     pushq   %rax";
     "     movq    $3, %rdi";
     "     jmp     wcdecl(cml_err)";
     "     .p2align 4";
     "";
     "windows_cml_err:";
     "     movq    %rcx, %r9";
     "     movq    %rdx, %r8";
     "     movq    %rsi, %rdx";
     "     movq    %rdi, %rcx";
     "     jmp     cdecl(cml_err)";
     ""]))`;;

(* HOL4: export_func_def *)

let export_x64_export_func_def = cake_def
  `export_x64_export_func appl (name,label,start:A,len:B) =
    SmartAppend appl (misc_List
    [implode "\n    .globl cdecl("; name; implode ")\n";
     implode "#if defined(__APPLE__)\n";
     implode "\n";
     implode "#elif defined(__WIN32)\n";
     implode "     .func   cdecl("; name; implode ")\n";
     implode "#else\n";
     implode "     .type   cdecl("; name; implode "), function\n";
     implode "#endif\n";
     implode "cdecl("; name; implode "):\n";
     implode "     lea     "; name; implode "_jmp(%rip), %r10\n";
     implode "     jmp     wcml(cake_enter)\n";
            name; implode "_jmp:\n";
     implode "     jmp     "; label; implode "\n";
     implode "#if defined(__WIN32)\n";
     implode "     .endfunc\n";
     implode "#endif\n"
    ])`;;

(* HOL4: export_funcs_def *)

let export_x64_export_funcs_def = cake_def
  `export_x64_export_funcs (lsyms:(mlstring#mlstring#A#B)list) exp =
    FOLDL export_x64_export_func Nil (FILTER ((flip MEM exp) o FST) lsyms)`;;

let x64_export_def = cake_def (vsubst
  [export_x64_ffi_code,`ffi_code:bool->mlstring app_list`;
   export_x64_windows_ffi_code,`windows_ffi_code:bool->mlstring app_list`;
   export_x64_entry_point_code,`entry_point_code:mlstring app_list`]
  `x64_export (ffi_names:mlstring list) bytes (data:int64 list) syms exp ret pk =
    let lsyms = get_sym_labels syms in
    SmartAppend
      (SmartAppend
      (SmartAppend (misc_List preamble)
      (SmartAppend (misc_List (data_section ".quad" ret))
      (SmartAppend (split16 (words_line (implode "\t.quad ") word_to_string) data)
      (SmartAppend (misc_List data_buffer)
      (SmartAppend (export_x64_startup ret pk) (ffi_code ret))))))
      (SmartAppend (split16 (words_line (implode "\t.byte ") byte_to_string) bytes)
      (SmartAppend (misc_List code_buffer)
      (emit_symbols lsyms))))
      (SmartAppend (windows_ffi_code ret)
      (if ret then
        (SmartAppend entry_point_code (export_x64_export_funcs lsyms exp))
      else misc_List []))`);;
