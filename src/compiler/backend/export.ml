(* ========================================================================= *)
(* export: port of HOL4 compiler/backend/exportScript.sml (CakeML v3479).    *)
(* Some common helper functions for writing the final byte list -> string   *)
(* exporter.                                                                 *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;
needs "basis/pure/mlvector.ml";;
needs "basis/pure/mlint.ml";;

type_invention_error := true;;

(* Notation (as in the basis files): HOL4 strlit and the mlstring literal   *)
(* syntax are implode "..."; s1 ^ s2 is strcat s1 s2 (left associative in   *)
(* HOL4); string ++ is APPEND (left associative in HOL4); toString is       *)
(* num_to_str on num and chr_to_str on char; concat is mlstring_concat;     *)
(* misc$List and misc$Append are misc_List and misc_Append; word8 is byte,  *)
(* n2w is word, w2n is val; GENLIST f n is list_of_seq f n.                 *)

let split16_def = cake_def_wf
  `MEASURE (\p:(A list->B app_list)#A list. LENGTH (SND p))`
  (REWRITE_TAC[measure_THM; LENGTH_DROP; LENGTH] THEN ARITH_TAC)
  `(split16 (f:A list->B app_list) [] = Nil) /\
   (split16 f xs =
      let xs1 = TAKE 16 xs in
      let xs2 = DROP 16 xs in
        SmartAppend (f xs1) (split16 f xs2))`;;

let split16_ind = cake_ind "split16";;

(* HOL4 defines preamble as the EVAL result of                              *)
(*   MAP (\n. strlit (n ++ "\n")) [...]                                     *)
(* so the defining equation is the evaluated list                          *)

let preamble_def = cake_def
  `preamble =
   [
    implode "/* Preprocessor to get around Mac OS, Windows, and Linux differences in naming and calling conventions */\n";
    implode "\n";
    implode "#if defined(__APPLE__)\n";
    implode "# define cdecl(s) _##s\n";
    implode "#else\n";
    implode "# define cdecl(s) s\n";
    implode "#endif\n";
    implode "\n";
    implode "#if defined(__APPLE__)\n";
    implode "# define wcdecl(s) _##s\n";
    implode "#elif defined(__WIN32)\n";
    implode "# define wcdecl(s) windows_##s\n";
    implode "#else\n";
    implode "# define wcdecl(s) s\n";
    implode "#endif\n";
    implode "\n";
    implode "#if defined(__APPLE__)\n";
    implode "# define wcml(s) s\n";
    implode "#elif defined(__WIN32)\n";
    implode "# define wcml(s) windows_##s\n";
    implode "#else\n";
    implode "# define wcml(s) s\n";
    implode "#endif\n";
    implode "\n";
    implode "#if defined(__APPLE__)\n";
    implode ".macro _makesym name, base, len\n";
    implode ".set \\name, cake_main+\\base\n";
    implode ".endm\n";
    implode "# define makesym(name,base,len) _makesym name, base, len\n";
    implode "#elif defined(__WIN32)\n";
    implode ".macro _makesym name, base, len\n";
    implode ".set \\name, cake_main+\\base\n";
    implode ".endm\n";
    implode "# define makesym(name,base,len) _makesym name, base, len\n";
    implode "#else\n";
    implode ".macro _makesym name, base, len\n";
    implode ".local \\name\n";
    implode ".set \\name, cake_main+\\base\n";
    implode ".size \\name, \\len\n";
    implode ".type \\name, function\n";
    implode ".endm\n";
    implode "# define makesym(name,base,len) _makesym name, base, len\n";
    implode "#endif\n";
    implode "\n";
    implode "#define DATA_BUFFER_SIZE    65536\n";
    implode "#define CODE_BUFFER_SIZE  5242880\n";
    implode "\n";
    implode "     .file        \"cake.S\"\n";
    implode "\n"
   ]`;;

let data_section_def = cake_def
  `data_section (word_directive:string) ret =
     MAP (\n. implode (APPEND n "\n"))
       (APPEND
         (APPEND
           ["     .data";
            "     .p2align 3";
            APPEND (APPEND "cdecl(cml_heap): " word_directive) " 0";
            APPEND (APPEND "cdecl(cml_stack): " word_directive) " 0";
            APPEND (APPEND "cdecl(cml_stackend): " word_directive) " 0"]
           (if ret then
              [APPEND (APPEND "ret_base: " word_directive) " 0";
               APPEND (APPEND "ret_stack: " word_directive) " 0";
               APPEND (APPEND "ret_stackend: " word_directive) " 0";
               APPEND (APPEND "can_enter: " word_directive) " 0"]
            else []))
         ["     .p2align 3";
          "cake_bitmaps:"])`;;

let data_buffer_def = cake_def
  `data_buffer =
     MAP (\n. implode (APPEND n "\n"))
       ["     .globl cdecl(cake_bitmaps_buffer_begin)";
        "cdecl(cake_bitmaps_buffer_begin):";
        "#if defined(EVAL)";
        "     .space DATA_BUFFER_SIZE";
        "#endif";
        "     .globl cdecl(cake_bitmaps_buffer_end)";
        "cdecl(cake_bitmaps_buffer_end):"]`;;

let code_buffer_def = cake_def
  `code_buffer =
     MAP (\n. implode (APPEND n "\n"))
       ["     .globl cdecl(cake_codebuffer_begin)";
        "cdecl(cake_codebuffer_begin):";
        "#if defined(EVAL)";
        "     .space CODE_BUFFER_SIZE";
        "#endif";
        "     .p2align 12";
        "     .globl cdecl(cake_codebuffer_end)";
        "cdecl(cake_codebuffer_end):";
        "     .space 4096"]`;;

let comm_strlit_def = cake_def
  `comm_strlit = implode ","`;;

let newl_strlit_def = cake_def
  `newl_strlit = implode "\n"`;;

let comma_cat_def = cake_def
  `comma_cat (f:A->mlstring) x =
     match x with
       [] -> [newl_strlit]
     | [x] -> [f x; newl_strlit]
     | CONS x xs -> CONS (f x) (CONS comm_strlit (comma_cat f xs))`;;

let comma_cat_ind = cake_ind "comma_cat";;

let words_line_def = cake_def
  `words_line word_directive (to_string:A->mlstring) ls =
     misc_List (CONS word_directive (comma_cat to_string ls))`;;

let word_to_string_def = cake_def
  `word_to_string (w:N word) = num_to_str (val w)`;;

let byte_to_string_def = cake_def
  `byte_to_string (b:byte) =
     implode (APPEND (APPEND "0x" [EL (val b DIV 16) "0123456789ABCDEF"])
                     [EL (val b MOD 16) "0123456789ABCDEF"])`;;

let all_bytes_def = cake_def
  `all_bytes = Vector (list_of_seq (\n. byte_to_string (word n)) 256)`;;

(* HOL4: Theorem all_bytes_eq = EVAL all_bytes (an EVAL theorem, proved    *)
(* here by conversions)                                                      *)

let all_bytes_eq = prove
 (`all_bytes =
   Vector
    [
     implode "0x00"; implode "0x01"; implode "0x02"; implode "0x03"; implode "0x04"; implode "0x05";
     implode "0x06"; implode "0x07"; implode "0x08"; implode "0x09"; implode "0x0A"; implode "0x0B";
     implode "0x0C"; implode "0x0D"; implode "0x0E"; implode "0x0F"; implode "0x10"; implode "0x11";
     implode "0x12"; implode "0x13"; implode "0x14"; implode "0x15"; implode "0x16"; implode "0x17";
     implode "0x18"; implode "0x19"; implode "0x1A"; implode "0x1B"; implode "0x1C"; implode "0x1D";
     implode "0x1E"; implode "0x1F"; implode "0x20"; implode "0x21"; implode "0x22"; implode "0x23";
     implode "0x24"; implode "0x25"; implode "0x26"; implode "0x27"; implode "0x28"; implode "0x29";
     implode "0x2A"; implode "0x2B"; implode "0x2C"; implode "0x2D"; implode "0x2E"; implode "0x2F";
     implode "0x30"; implode "0x31"; implode "0x32"; implode "0x33"; implode "0x34"; implode "0x35";
     implode "0x36"; implode "0x37"; implode "0x38"; implode "0x39"; implode "0x3A"; implode "0x3B";
     implode "0x3C"; implode "0x3D"; implode "0x3E"; implode "0x3F"; implode "0x40"; implode "0x41";
     implode "0x42"; implode "0x43"; implode "0x44"; implode "0x45"; implode "0x46"; implode "0x47";
     implode "0x48"; implode "0x49"; implode "0x4A"; implode "0x4B"; implode "0x4C"; implode "0x4D";
     implode "0x4E"; implode "0x4F"; implode "0x50"; implode "0x51"; implode "0x52"; implode "0x53";
     implode "0x54"; implode "0x55"; implode "0x56"; implode "0x57"; implode "0x58"; implode "0x59";
     implode "0x5A"; implode "0x5B"; implode "0x5C"; implode "0x5D"; implode "0x5E"; implode "0x5F";
     implode "0x60"; implode "0x61"; implode "0x62"; implode "0x63"; implode "0x64"; implode "0x65";
     implode "0x66"; implode "0x67"; implode "0x68"; implode "0x69"; implode "0x6A"; implode "0x6B";
     implode "0x6C"; implode "0x6D"; implode "0x6E"; implode "0x6F"; implode "0x70"; implode "0x71";
     implode "0x72"; implode "0x73"; implode "0x74"; implode "0x75"; implode "0x76"; implode "0x77";
     implode "0x78"; implode "0x79"; implode "0x7A"; implode "0x7B"; implode "0x7C"; implode "0x7D";
     implode "0x7E"; implode "0x7F"; implode "0x80"; implode "0x81"; implode "0x82"; implode "0x83";
     implode "0x84"; implode "0x85"; implode "0x86"; implode "0x87"; implode "0x88"; implode "0x89";
     implode "0x8A"; implode "0x8B"; implode "0x8C"; implode "0x8D"; implode "0x8E"; implode "0x8F";
     implode "0x90"; implode "0x91"; implode "0x92"; implode "0x93"; implode "0x94"; implode "0x95";
     implode "0x96"; implode "0x97"; implode "0x98"; implode "0x99"; implode "0x9A"; implode "0x9B";
     implode "0x9C"; implode "0x9D"; implode "0x9E"; implode "0x9F"; implode "0xA0"; implode "0xA1";
     implode "0xA2"; implode "0xA3"; implode "0xA4"; implode "0xA5"; implode "0xA6"; implode "0xA7";
     implode "0xA8"; implode "0xA9"; implode "0xAA"; implode "0xAB"; implode "0xAC"; implode "0xAD";
     implode "0xAE"; implode "0xAF"; implode "0xB0"; implode "0xB1"; implode "0xB2"; implode "0xB3";
     implode "0xB4"; implode "0xB5"; implode "0xB6"; implode "0xB7"; implode "0xB8"; implode "0xB9";
     implode "0xBA"; implode "0xBB"; implode "0xBC"; implode "0xBD"; implode "0xBE"; implode "0xBF";
     implode "0xC0"; implode "0xC1"; implode "0xC2"; implode "0xC3"; implode "0xC4"; implode "0xC5";
     implode "0xC6"; implode "0xC7"; implode "0xC8"; implode "0xC9"; implode "0xCA"; implode "0xCB";
     implode "0xCC"; implode "0xCD"; implode "0xCE"; implode "0xCF"; implode "0xD0"; implode "0xD1";
     implode "0xD2"; implode "0xD3"; implode "0xD4"; implode "0xD5"; implode "0xD6"; implode "0xD7";
     implode "0xD8"; implode "0xD9"; implode "0xDA"; implode "0xDB"; implode "0xDC"; implode "0xDD";
     implode "0xDE"; implode "0xDF"; implode "0xE0"; implode "0xE1"; implode "0xE2"; implode "0xE3";
     implode "0xE4"; implode "0xE5"; implode "0xE6"; implode "0xE7"; implode "0xE8"; implode "0xE9";
     implode "0xEA"; implode "0xEB"; implode "0xEC"; implode "0xED"; implode "0xEE"; implode "0xEF";
     implode "0xF0"; implode "0xF1"; implode "0xF2"; implode "0xF3"; implode "0xF4"; implode "0xF5";
     implode "0xF6"; implode "0xF7"; implode "0xF8"; implode "0xF9"; implode "0xFA"; implode "0xFB";
     implode "0xFC"; implode "0xFD"; implode "0xFE"; implode "0xFF"
    ]`,
  REWRITE_TAC[all_bytes_def] THEN
  CONV_TAC(LAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN
  REWRITE_TAC[byte_to_string_def; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[APPEND]);;

let byte_to_string_eq = prove
 (`!b. byte_to_string b = regexp_compiler_sub all_bytes (val b)`,
  GEN_TAC THEN REWRITE_TAC[all_bytes_def; regexp_compiler_sub_def] THEN
  SUBGOAL_THEN `val (b:byte) < 256` ASSUME_TAC THENL
   [MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    ARITH_TAC;
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; WORD_VAL]]);;

(* gas allows 0-9a-zA-Z_$. in labels as long as the first is _A-Za-z *)
(* we prefix labels and reserve $; . is special *)

let escape_sym_char_def = cake_def
  `escape_sym_char ch =
     let code = ORD ch in
     if code >= 0x61 /\ code <= 0x7A \/ code >= 0x41 /\ code <= 0x5A \/
        code >= 0x30 /\ code <= 0x39 \/ code = 0x5F then chr_to_str ch else
     strcat (strcat (implode "$") (num_to_str code)) (implode "_")`;;

let get_sym_label_def = cake_def
  `get_sym_label (ix,appl:(mlstring#mlstring#A#B)list) (name,start:A,len:B) =
     let label =
       strcat (strcat (strcat (implode "cml_")
                              (mlstring_concat
                                 (MAP escape_sym_char (explode name))))
                      (implode "_"))
              (num_to_str ix) in
     (ix + 1, APPEND appl [(name,label,start,len)])`;;

let get_sym_labels_def = cake_def
  `get_sym_labels (syms:(mlstring#A#B)list) =
     SND (FOLDL get_sym_label (0, []) syms)`;;

let emit_symbol_def = cake_def
  `emit_symbol appl (name:A,label,start,len) =
     misc_Append appl (misc_List
       [strcat (strcat (strcat (strcat (strcat (strcat
          (implode "    makesym(") label) (implode ", ")) (num_to_str start))
          (implode ", ")) (num_to_str len)) (implode ")\n")])`;;

let emit_symbols_def = cake_def
  `emit_symbols (lsyms:(A#mlstring#num#num)list) =
     FOLDL emit_symbol Nil lsyms`;;
