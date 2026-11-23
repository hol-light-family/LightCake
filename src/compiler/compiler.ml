(* ========================================================================= *)
(* compiler: port of HOL4 compiler/compilerScript.sml (CakeML v3479).       *)
(* Definition of the CakeML compiler as a function that takes a list of     *)
(* command line arguments and a string corresponding to standard input, and *)
(* produces a pair of output strings for standard error and standard output *)
(* (the latter containing the generated machine code if successful).        *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: compiler_config (fields                   *)
(*   compiler_config_inferencer_config, ...), compiler_compile.              *)
(* - The definitions that need theories outside the port are not here:     *)
(*   parse_target_64 and parse_target_32 (the asm configurations           *)
(*   x64_config, arm8_config, mips_config, riscv_config and arm7_config of *)
(*   the target theories x64_target, ..., which are built on the L3 models *)
(*   of the ISAs; only ag32_target is ported), compile_64 and compile_32   *)
(*   (they need those and basisProg's basis), compile_pancake_64 and       *)
(*   compile_pancake_32 (they need parse_target_64 and parse_target_32),   *)
(*   full_compile_64 and full_compile_32 (they need those and the file     *)
(*   system of the basis library: add_stdout, add_stderr of TextIOProof,   *)
(*   fastForwardFD of fsFFIProps).                                         *)
(* - compile_pancake: HOL4's pattern return () is errorMonad_return _ (the *)
(*   unit type has one value); its paired lambda is HOL Light's            *)
(*   \(msg,loc). t; staterr and its constructors are panStatic's.          *)
(* - The build information (git commit of CakeML and of HOL4, version of     *)
(*   Poly/ML, date of the build) that HOL4 computes in ML when the theory is *)
(*   built is not available: current_build_info_str is the HOL4 expression  *)
(*   with the CakeML version e8eca63, no HOL4 and Poly/ML lines, and no date.*)
(* - help_string is the text of the HOL4 script (from its second line, as   *)
(*   HOL4's drop_until and tl do), built in OCaml since it contains          *)
(*   backquotes.                                                             *)
(* - mlstring literals are implode s; s1 ^ s2 is strcat s1 s2 (left          *)
(*   associative); concat is mlstring_concat; extract is mlstring_extract;    *)
(*   toString on num is num_to_str; a character literal is CHR of its code; *)
(*   EVERY is ALL; ++ is APPEND; STRCAT is APPEND; HOL4 MEMBER (ml_translator,*)
(*   outside the port) is MEM, which it equals (ml_translator MEMBER_INTRO). *)
(* - parse_prog returns a pegresult: Success is peg_Success.                *)
(* - HOL4 conf_ok_check (:'a) c takes the universe (:A) as data_to_word's     *)
(*   conf_ok: conf_ok_check_DEF is the definition, conf_ok_check_def the     *)
(*   HOL4 statement.                                                         *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "basis/pure/mlstring.ml";;
needs "basis/pure/mlint.ml";;
needs "semantics/lexer_fun.ml";;
needs "compiler/parsing/lexer_impl.ml";;
needs "compiler/parsing/cmlParse.ml";;
needs "compiler/inference/infer.ml";;
needs "compiler/parsing/fromSexp.ml";;
needs "hol4/simpleSexpParse.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/backend_passes.ml";;
needs "pancake/parser/panPtreeConversion.ml";;
needs "pancake/panStatic.ml";;
needs "pancake/pan_passes.ml";;

prioritize_num();;
type_invention_error := true;;

let print_option_def = cake_def
  `print_option h x =
     match x with
       NONE -> implode ""
     | SOME y -> strcat (strcat (strcat h (implode " ")) y) (implode "\n")`;;

(* == Build info =========================================================== *)

let current_build_info_str_def = cake_def
  `current_build_info_str =
     let commit = print_option (implode "CakeML:") (SOME (implode "e8eca63")) in
     let hol = print_option (implode "HOL4:  ") NONE in
     let poly = print_option (implode "PolyML:") NONE in
     mlstring_concat
       [implode "The CakeML compiler\n\n";
        implode "Version details:\n";
        implode ""; implode "\n";
        commit; hol; poly]`;;

(* ========================================================================= *)

let compiler_config_INFO = cake_record "compiler_config"
  ["inferencer_config","inf_env";
   "backend_config","backend_config";
   "asm_config","(A)asm_config";
   "input_is_sexp","bool";
   "exclude_prelude","bool";
   "skip_type_inference","bool";
   "only_print_types","bool";
   "only_print_sexp","bool"];;

let compiler_config_component_equality =
  compiler_config_INFO.ri_component_equality;;

let help_string_def =
  new_definition
   (mk_eq(`help_string:mlstring`,
          mk_comb(`implode`,
            mk_string (
   "\n" ^
   "Usage:  cake [OPTIONS] < input_file > output_file\n" ^
   "\n" ^
   "The cake executable is usually invoked as shown above. The different\n" ^
   "OPTIONS are described in the OPTIONS listing below.\n" ^
   "\n" ^
   "One can also run the cake execuable as follows to print a listing of\n" ^
   "the type of each top-level binding (including the bindings made in\n" ^
   "the standard basis library).\n" ^
   "\n" ^
   "Usage:  cake --types < input_file\n" ^
   "\n" ^
   "One can invoke the cake executable to print this help message (--help)\n" ^
   "or version information (--version) without an input_file:\n" ^
   "\n" ^
   "Usage:  cake --version\n" ^
   "Usage:  cake --help\n" ^
   "\n" ^
   "OPTIONS:\n" ^
   "\n" ^
   "  --repl        starts an interactive read-eval-print loop; all other\n" ^
   "                flags are ignored, when the --repl flag is present\n" ^
   "\n" ^
   "  --reg_alg=N   N is a natural number that specifies the register\n" ^
   "                allocation algorithm to use:\n" ^
   "                   0   - simple allocator, no spill heuristics\n" ^
   "                   1   - simple allocator, spill heuristics\n" ^
   "                   2   - IRC allocator, no spill heuristics (default)\n" ^
   "                   3   - IRC allocator, spill heuristics\n" ^
   "                   >=4 - linear scan allocator\n" ^
   "\n" ^
   "  --gc=G        specifies garbage collector type; here G is one of:\n" ^
   "                   none   - no garbage collector is used\n" ^
   "                   simple - a non-generational Cheney (default)\n" ^
   "                   genN   - a generational Cheney garbage collector is\n" ^
   "                            used; the size of the nursery generation is\n" ^
   "                            N machine words (example: --gc=gen5000)\n" ^
   "                This option has no effect under --pancake; the Pancake\n" ^
   "                compiler always uses gc=none.\n" ^
   "\n" ^
   "  --target=T    specifies that compilation should produce code for target\n" ^
   "                T, where T can be one of x64, arm8, mips, riscv for\n" ^
   "                the 64-bit compiler; for the 32-bit compiler T can be\n" ^
   "                one of arm7 and ag32.\n" ^
   "\n" ^
   "  --sexp=B      B can be either true or false; here false means that the\n" ^
   "                input will be parsed as normal CakeML concrete syntax;\n" ^
   "                true means that the input is parsed as an s-expression.\n" ^
   "\n" ^
   "  --print_sexp  causes the cake to print the given program in\n" ^
   "                s-expression format; with this option, the compiler\n" ^
   "                does not generate machine code.\n" ^
   "\n" ^
   "  --exclude_prelude=B   here B can be either true or false; the default\n" ^
   "                is false; setting this to true causes the compiler not\n" ^
   "                to include the standard basis library.\n" ^
   "\n" ^
   "  --skip_type_inference=B   here B can be either true or false; the\n" ^
   "                default is false; true will make the compiler skip\n" ^
   "                type inference. There are no gurantees of safety if\n" ^
   "                the type inferencer is skipped.\n" ^
   "\n" ^
   "  --explore     outputs intermediate forms of the compiled program\n" ^
   "\n" ^
   "  --pancake     takes a pancake program as input\n" ^
   "\n" ^
   "  --no_warn     silences pancake warning output\n" ^
   "\n" ^
   "  --main_return=B   here B can be either true or false; the default is\n" ^
   "                false; setting this to true causes the main function to\n" ^
   "                return to caller instead of exit; this option is\n" ^
   "                required to use multiple entry points with Pancake.\n" ^
   "\n" ^
   "ADDITIONAL OPTIONS:\n" ^
   "\n" ^
   "Optimisations can be configured using the following advanced options.\n" ^
   "\n" ^
   "  --jump=B    true means conditional jumps to be used for out-of-stack checks\n" ^
   "  --multi=B   true means clos_to_bvl phase is to use multi optimisation\n" ^
   "  --known=B   true means clos_to_bvl phase is to use known optimisation\n" ^
   "  --call=B    true means clos_to_bvl phase is to use call optimisation\n" ^
   "  --tmc=B     true means tail-call modulo cons optimisations is used\n" ^
   "  --tailrec=B true means attempts to turn functions into tail-rec form\n" ^
   "  --inline_factor=N  threshold used by for ClosLang inliner in known pass\n" ^
   "  --max_body_size=N  threshold used by for ClosLang inliner in known pass\n" ^
   "  --max_app=N   max number of optimised curried applications in multi pass\n" ^
   "  --inline_size=N  threshold used by for BVL inliner pass\n" ^
   "  --exp_cut=N  threshold for when to cut large expression into subfunctions\n" ^
   "  --split=B  true means main expression will be split at sequencing (;)\n" ^
   "  --tag_bits=N  number of tag bits in every pointer\n" ^
   "  --len_bits=N  number of length bits in every pointer\n" ^
   "  --pad_bits=N  number of zero padding in every pointer\n" ^
   "  --len_size=N  size of length field in heap object header cells\n" ^
   "  --emit_empty_ffi=B  true emits debugging FFI calls for use with DEBUG_FFI\n" ^
   "  --hash_size=N  size of the memoization table used by instruction encoder\n" ^
   "  --perf_callgraph=B  unverified: emit C-stack shadowing so \096perf record\n" ^
   "                --call-graph fp\096 produces correct call graphs (x64 only)\n" ^
   "\n"))));;

let compile_error_INDUCT,compile_error_RECURSION = cake_type
  "compile_error = ParseError mlstring
                 | TypeError mlstring
                 | AssembleError
                 | ConfigError mlstring
                 | StaticError staterr";;

let find_next_newline_def = cake_def_wf
  `MEASURE (\(n:num,s:mlstring). strlen s - n)`
  (REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN REWRITE_TAC WF_REL_THMS THEN
   CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN ARITH_TAC)
  `find_next_newline n s =
     if strlen s <= n then n else
     if strsub s n = CHR 10 then n else
     find_next_newline (n + 1) s`;;

let find_next_newline_ind = cake_ind "find_next_newline";;

let safe_substring_def = cake_def
  `safe_substring s n l =
     let k = strlen s in
     if k <= n then implode "" else
     if n + l <= k then substring s n l
     else substring s n (k - n)`;;

let get_nth_line_def = cake_def
  `get_nth_line k s n =
     if k = 0 then
       let n1 = find_next_newline n s in
       safe_substring s n (n1 - n)
     else
       get_nth_line (k - 1:num) s (find_next_newline n s + 1)`;;

let locs_to_string_def = cake_def
  `(locs_to_string input NONE = implode "unknown location") /\
   (locs_to_string input (SOME (Locs startl endl)) =
      match startl with
        POSN r c ->
          (let line = get_nth_line r input 0 in
           let len = strlen line in
           let stop = (match endl with POSN r1 c1 -> (if r1 = r then c1 else len)
                                     | _ -> len) in
           let underline =
             mlstring_concat (APPEND (REPLICATE c (implode " "))
                                     (REPLICATE ((stop - c) + 1) (implode [CHR 94]))) in
           mlstring_concat [implode "line "; num_to_str (r + 1); implode "\n\n";
                            line; implode "\n";
                            underline; implode "\n"])
      | _ -> implode "unknown location")`;;

(* this is a rather annoying feature of peg_exec requiring locs...         *)
(* HOL4: Overload add_locs = MAP (\c. (c,unknown_loc)) (written out)         *)

let parse_sexp_input_def = cake_def
  `parse_sexp_input input =
     let err = implode "Parsing of sexp syntax failed" in
     match parse_sexp (MAP (\c. (c,unknown_loc)) input) with
       NONE -> INL err
     | SOME x -> (match sexplist sexpdec x with
                    NONE -> INL err
                  | SOME x -> INR x)`;;

let parse_cml_input_def = cake_def
  `parse_cml_input input =
     match parse_prog (lexer_fun input) with
       Failure l _ ->
         INL (strcat (implode "Parsing failed at ")
                     (locs_to_string (implode input) (SOME l)))
     | peg_Success _ x _ -> INR x`;;

let compiler_compile_def = cake_def
  `compiler_compile (c:(A)compiler_config) prelude input =
     let _ = empty_ffi (implode "finished: start up") in
     match (if compiler_config_input_is_sexp c
            then parse_sexp_input input
            else parse_cml_input input) with
       INL msg -> (M_failure (ParseError msg),Nil)
     | INR prog ->
         let _ = empty_ffi (implode "finished: lexing and parsing") in
         let full_prog = if compiler_config_exclude_prelude c then prog
                         else APPEND prelude prog in
         (match (if compiler_config_skip_type_inference c
                 then M_success (compiler_config_inferencer_config c)
                 else infertype_prog (compiler_config_inferencer_config c) full_prog) with
            M_failure (locs,msg) ->
              (M_failure (TypeError (mlstring_concat
                 [msg; implode " at "; locs_to_string (implode input) locs])),Nil)
          | M_success ic ->
              let _ = empty_ffi (implode "finished: type inference") in
              if compiler_config_only_print_types c then
                (M_failure (TypeError (mlstring_concat
                   (APPEND (APPEND [implode "\n"] (inf_env_to_types_string ic))
                           [implode "\n"]))),Nil)
              else if compiler_config_only_print_sexp c then
                (M_failure (TypeError (implode
                   (APPEND "\n" (print_sexp (listsexp (MAP decsexp full_prog)))))),Nil)
              else
                (match compile_tap (compiler_config_asm_config c)
                         (compiler_config_backend_config c) full_prog with
                   (NONE,td) -> (M_failure AssembleError,td)
                 | (SOME (bytes,data,c),td) -> (M_success (bytes,data,c),td)))`;;

let compile_pancake_def = cake_def
  `compile_pancake (asm_conf:(A)asm_config) (c:backend_config) input =
     let _ = empty_ffi (implode "finished: start up") in
     match parse_topdecs_to_ast input with
       INR errs ->
         (M_failure (ParseError (mlstring_concat
            (MAP (\(msg,loc). mlstring_concat
                    [msg; implode " at "; locs_to_string (implode input) (SOME loc);
                     implode "\n"])
                 errs))),Nil,[])
     | INL funs ->
         (match static_check funs with
            (errorMonad_error e,warns) ->
              (M_failure (StaticError e),Nil,MAP StaticError warns)
          | (errorMonad_return _,warns) ->
              let _ = empty_ffi (implode "finished: lexing and parsing") in
              (match pan_compile_tap asm_conf c funs with
                 (NONE,td) -> (M_failure AssembleError,td,MAP StaticError warns)
               | (SOME (bytes,data,c),td) ->
                   (M_success (bytes,data,c),td,MAP StaticError warns)))`;;

(* The top-level compiler *)

(* TypeError: if the first char in the message is a newline char then it   *)
(* isn't an error                                                            *)

let error_to_str_def = cake_def
  `(error_to_str (ParseError s) =
      mlstring_concat [implode "### ERROR: parse error\n"; s; implode "\n"]) /\
   (error_to_str (TypeError s) =
      if (if strlen s = 0 then T else if strsub s 0 = CHR 10 then F else T) then
        mlstring_concat [implode "### ERROR: type error\n"; s; implode "\n"]
      else s) /\
   (error_to_str (ConfigError s) =
      mlstring_concat [implode "### ERROR: config error\n"; s; implode "\n"]) /\
   (error_to_str AssembleError = implode "### ERROR: assembly error\n") /\
   (error_to_str (StaticError e) =
      match e with
        ScopeErr s ->
          mlstring_concat [implode "### ERROR: scope error\n"; s; implode "\n"]
      | WarningErr s ->
          mlstring_concat [implode "# WARNING:\n"; s; implode "\n"]
      | GenErr s ->
          mlstring_concat [implode "### ERROR: static error\n"; s; implode "\n"]
      | ShapeErr s ->
          mlstring_concat [implode "### ERROR: shape error\n"; s; implode "\n"])`;;

let is_error_msg_def = cake_def
  `is_error_msg x = isPrefix (implode "###") x`;;

(* TODO: translator fails inside mlstringLib.mlstring_case_conv when the     *)
(* following definition just matches against (strlit str) directly          *)

let parse_num_def = cake_def
  `parse_num str =
     let str = explode str in
     if ALL isDigit str then SOME (num_from_dec_string_alt str) else NONE`;;

let parse_bool_def = cake_def
  `parse_bool str =
     if str = implode "true" then SOME T
     else if str = implode "false" then SOME F
     else NONE`;;

(* Finds the first occurence of the flag and returns the rest of the string *)
(* after it                                                                  *)

let find_str_def = cake_def
  `(find_str flag [] = NONE) /\
   (find_str flag (CONS x xs) =
      if isPrefix flag x then SOME (mlstring_extract x (strlen flag) NONE)
      else find_str flag xs)`;;

(* Finds all occurences of the flag as a prefix, returning the remainder in *)
(* each occurence.                                                           *)

let find_strs_def = cake_def
  `(find_strs flag [] = []) /\
   (find_strs flag (CONS x xs) =
      if isPrefix flag x then CONS (mlstring_extract x (strlen flag) NONE) (find_strs flag xs)
      else find_strs flag xs)`;;

(* If flag is not present then F, else if it is present then we should not  *)
(* get any config string afterwards                                          *)

let find_bool_def = cake_def
  `find_bool flag ls default =
     match find_str flag ls with
       NONE -> INL default
     | SOME rest ->
         (match parse_bool rest with
            SOME b -> INL b
          | NONE -> INR (mlstring_concat [implode "Unable to parse as bool: "; rest;
                                          implode " for flag: "; flag]))`;;

(* If flag is not present then INL default, else if it is present then the  *)
(* rest of the config string should be a number                              *)

let find_num_def = cake_def
  `find_num flag ls default =
     match find_str flag ls with
       NONE -> INL default
     | SOME rest ->
         (match parse_num rest with
            SOME n -> INL n
          | NONE -> INR (mlstring_concat [implode "Unable to parse as num: "; rest;
                                          implode " for flag: "; flag]))`;;

let get_err_str_def = cake_def
  `(get_err_str (INL (n:A)) = implode "") /\
   (get_err_str (INR s) = mlstring_concat [s; implode "\n"])`;;

(* All the numbers must parse *)

let parse_num_list_def = cake_def
  `(parse_num_list [] = INL []) /\
   (parse_num_list (CONS x xs) =
      match parse_num x with
        NONE -> INR (mlstring_concat [implode "Unable to parse as num: "; x])
      | SOME n ->
          (match parse_num_list xs with
             INR s -> INR s
           | INL ns -> INL (CONS n ns)))`;;

let comma_tokens_def = cake_def
  `(comma_tokens acc xs [] = if NULL xs then acc else APPEND acc [implode xs]) /\
   (comma_tokens acc (xs:string) (CONS c (cs:string)) =
      if c = CHR 44 then
        comma_tokens (APPEND acc (if NULL xs then [] else [implode xs])) [] cs
      else
        comma_tokens acc (APPEND xs [c]) cs)`;;

let parse_nums_def = cake_def
  `parse_nums str = parse_num_list (comma_tokens [] [] (explode str))`;;

(* Each of these is a helper function that extends a conf; it either        *)
(* returns an INL extended_conf or INR error_string                          *)

(* clos_conf *)

let parse_clos_conf_def = cake_def
  `parse_clos_conf ls (clos:clos_to_bvl_config) =
     let multi = find_bool (implode "--multi=") ls (clos_to_bvl_config_do_mti clos) in
     let known = find_bool (implode "--known=") ls
                   (IS_SOME (clos_to_bvl_config_known_conf clos)) in
     let inline_factor = find_num (implode "--inline_factor=") ls default_inline_factor in
     let call = find_bool (implode "--call=") ls (clos_to_bvl_config_do_call clos) in
     let maxapp = find_num (implode "--max_app=") ls (clos_to_bvl_config_max_app clos) in
     match (multi,known,inline_factor,call,maxapp) with
       (INL m,INL k,INL i,INL c,INL n) ->
         if k then
           (let max_body_size = find_num (implode "--max_body_size=") ls
                                  (default_max_body_size n i) in
            match max_body_size with
              INL x ->
                INL (clos_to_bvl_config_do_mti_fupd (K m)
                      (clos_to_bvl_config_known_conf_fupd (K (SOME (mk_config x i)))
                        (clos_to_bvl_config_do_call_fupd (K c)
                          (clos_to_bvl_config_max_app_fupd (K n) clos))))
            | _ -> INR (mlstring_concat [get_err_str max_body_size]))
         else
           INL (clos_to_bvl_config_do_mti_fupd (K m)
                 (clos_to_bvl_config_known_conf_fupd (K NONE)
                   (clos_to_bvl_config_do_call_fupd (K c)
                     (clos_to_bvl_config_max_app_fupd (K n) clos))))
     | _ ->
         INR (mlstring_concat [get_err_str multi;
                               get_err_str known;
                               get_err_str inline_factor;
                               get_err_str call;
                               get_err_str maxapp])`;;

(* bvl *)

let parse_bvl_conf_def = cake_def
  `parse_bvl_conf ls (bvl:bvl_to_bvi_config) =
     let inlinesz = find_num (implode "--inline_size=") ls
                      (bvl_to_bvi_config_inline_size_limit bvl) in
     let expcut = find_num (implode "--exp_cut=") ls (bvl_to_bvi_config_exp_cut bvl) in
     let tmc = find_bool (implode "--tmc=") ls (bvl_to_bvi_config_do_tmc bvl) in
     let tailrec = find_bool (implode "--tailrec=") ls (bvl_to_bvi_config_do_tailrec bvl) in
     let splitmain = find_bool (implode "--split=") ls
                       (bvl_to_bvi_config_split_main_at_seq bvl) in
     match (inlinesz,expcut,splitmain,tmc,tailrec) with
       (INL i,INL e,INL m,INL do_tmc,INL do_tailrec) ->
         INL (bvl_to_bvi_config_inline_size_limit_fupd (K i)
               (bvl_to_bvi_config_exp_cut_fupd (K e)
                 (bvl_to_bvi_config_split_main_at_seq_fupd (K m)
                   (bvl_to_bvi_config_do_tmc_fupd (K do_tmc)
                     (bvl_to_bvi_config_do_tailrec_fupd (K do_tailrec) bvl)))))
     | _ ->
         INR (mlstring_concat [get_err_str inlinesz;
                               get_err_str expcut;
                               get_err_str splitmain;
                               get_err_str tmc;
                               get_err_str tailrec])`;;

(* wtw *)

let parse_wtw_conf_def = cake_def
  `parse_wtw_conf ls (wtw:word_to_word_config) =
     let regalg = find_num (implode "--reg_alg=") ls (word_to_word_config_reg_alg wtw) in
     match regalg with
       INL r -> INL (word_to_word_config_reg_alg_fupd (K r) wtw)
     | INR s -> INR (get_err_str regalg)`;;

let parse_gc_def = cake_def
  `parse_gc ls default =
     match find_str (implode "--gc=") ls with
       NONE -> INL default
     | SOME rest ->
         if rest = implode "none" then INL data_to_word_None
         else if rest = implode "simple" then INL data_to_word_Simple
         else if isPrefix (implode "gen") rest then
           (match parse_nums (mlstring_extract rest (strlen (implode "gen")) NONE) with
              INL ls -> INL (Generational ls)
            | INR s ->
                INR (mlstring_concat [implode "Error parsing GenGC argument: "; s]))
         else INR (mlstring_concat [implode "Unrecognized GC option: "; rest])`;;

(* Copy of conf_ok from data_to_word *)

let conf_ok_check_DEF = new_definition
  `conf_ok_check (s:A->bool) (c:data_to_word_config) <=>
     shift_length c < dimindex(:A) /\
     backend_common_word_shift(:A) <= shift_length c /\
     ~(data_to_word_config_len_size c = 0) /\
     data_to_word_config_len_size c + 7 < dimindex(:A)`;;

let conf_ok_check_def = prove
 (`!c. conf_ok_check (:A) c <=>
     shift_length c < dimindex(:A) /\
     backend_common_word_shift(:A) <= shift_length c /\
     ~(data_to_word_config_len_size c = 0) /\
     data_to_word_config_len_size c + 7 < dimindex(:A)`,
  REWRITE_TAC[conf_ok_check_DEF]);;

(* data *)

let parse_data_conf_def = cake_def
  `parse_data_conf ls (data:data_to_word_config) =
     let tag_bits = find_num (implode "--tag_bits=") ls
                      (data_to_word_config_tag_bits data) in
     let len_bits = find_num (implode "--len_bits=") ls
                      (data_to_word_config_len_bits data) in
     let pad_bits = find_num (implode "--pad_bits=") ls
                      (data_to_word_config_pad_bits data) in
     let len_size = find_num (implode "--len_size=") ls
                      (data_to_word_config_len_size data) in
     let empty_FFI = find_bool (implode "--emit_empty_ffi=") ls
                       (data_to_word_config_call_empty_ffi data) in
     let gc = parse_gc ls (data_to_word_config_gc_kind data) in
     match (tag_bits,len_bits,pad_bits,len_size,gc,empty_FFI) with
       (INL tb,INL lb,INL pb,INL ls,INL gc,INL empty_FFI) ->
         INL (data_to_word_config_tag_bits_fupd (K tb)
               (data_to_word_config_len_bits_fupd (K lb)
                 (data_to_word_config_pad_bits_fupd (K pb)
                   (data_to_word_config_len_size_fupd (K ls)
                     (data_to_word_config_gc_kind_fupd (K gc)
                       (data_to_word_config_call_empty_ffi_fupd (K empty_FFI) data))))))
     | _ ->
         INR (mlstring_concat [get_err_str tag_bits;
                               get_err_str len_bits;
                               get_err_str pad_bits;
                               get_err_str len_size;
                               get_err_str gc;
                               get_err_str empty_FFI])`;;

(* stack *)

let parse_stack_conf_def = cake_def
  `parse_stack_conf ls (stack:stack_to_lab_config) =
     let jump = find_bool (implode "--jump=") ls (stack_to_lab_config_jump stack) in
     let perf = find_bool (implode "--perf_callgraph=") ls
                  (stack_to_lab_config_perf_calls stack) in
     match (jump,perf) with
       (INL j,INL p) -> INL (stack_to_lab_config_jump_fupd (K j)
                              (stack_to_lab_config_perf_calls_fupd (K p) stack))
     | (INR s,_) -> INR s
     | (_,INR s) -> INR s`;;

(* tap *)

let parse_tap_conf_def = cake_def
  `parse_tap_conf ls (stack:B) =
     INL (tap_config_REC (MEM (implode "--explore") ls)):tap_config+C`;;

(* lab *)

let parse_lab_conf_def = cake_def
  `parse_lab_conf ls (lab:lab_to_target_config) =
     let hs = find_num (implode "--hash_size=") ls (lab_to_target_config_hash_size lab) in
     match hs with
       INL r -> INL (lab_to_target_config_hash_size_fupd (K r) lab)
     | INR s -> INR s`;;

let extend_conf_def = cake_def
  `extend_conf ls (conf:backend_config) =
     let clos = parse_clos_conf ls (backend_config_clos_conf conf) in
     let bvl = parse_bvl_conf ls (backend_config_bvl_conf conf) in
     let wtw = parse_wtw_conf ls (backend_config_word_to_word_conf conf) in
     let data = parse_data_conf ls (backend_config_data_conf conf) in
     let stack = parse_stack_conf ls (backend_config_stack_conf conf) in
     let tap = parse_tap_conf ls (backend_config_tap_conf conf) in
     let lab = parse_lab_conf ls (backend_config_lab_conf conf) in
     match (clos,bvl,wtw,data,stack,tap,lab) with
       (INL clos,INL bvl,INL wtw,INL data,INL stack,INL tap,INL lab) ->
         INL (backend_config_clos_conf_fupd (K clos)
               (backend_config_bvl_conf_fupd (K bvl)
                 (backend_config_word_to_word_conf_fupd (K wtw)
                   (backend_config_data_conf_fupd (K data)
                     (backend_config_stack_conf_fupd (K stack)
                       (backend_config_tap_conf_fupd (K tap)
                         (backend_config_lab_conf_fupd (K lab) conf)))))))
     | _ ->
         INR (mlstring_concat [get_err_str clos;
                               get_err_str bvl;
                               get_err_str wtw;
                               get_err_str data;
                               get_err_str stack;
                               get_err_str tap;
                               get_err_str lab])`;;

let parse_top_config_def = cake_def
  `parse_top_config ls =
     let sexp = find_bool (implode "--sexp=") ls F in
     let prelude = find_bool (implode "--exclude_prelude=") ls F in
     let typeinference = find_bool (implode "--skip_type_inference=") ls F in
     let sexpprint = MEM (implode "--print_sexp") ls in
     let onlyprinttypes = MEM (implode "--types") ls in
     let nowarnings = MEM (implode "--no_warn") ls in
     let mainreturn = find_bool (implode "--main_return=") ls F in
     match (sexp,prelude,typeinference,mainreturn) with
       (INL sexp,INL prelude,INL typeinference,INL mainreturn) ->
         INL (sexp,prelude,typeinference,onlyprinttypes,sexpprint,mainreturn,nowarnings)
     | _ -> INR (mlstring_concat [get_err_str sexp;
                                  get_err_str prelude;
                                  get_err_str typeinference;
                                  get_err_str mainreturn])`;;

(* Check for version flag *)

let has_version_flag_def = cake_def
  `has_version_flag ls <=> MEM (implode "--version") ls`;;

(* Check for version help *)

let has_help_flag_def = cake_def
  `has_help_flag ls <=> MEM (implode "--help") ls`;;

(* Check for pancake flag *)

let has_pancake_flag_def = cake_def
  `has_pancake_flag ls <=> MEM (implode "--pancake") ls`;;

let format_compiler_result_def = cake_def
  `(format_compiler_result
      (bytes_export:ffiname list->byte list->(A word)list->(mlstring)app_list)
      (M_failure err) =
      (misc_List []:(mlstring)app_list,error_to_str err)) /\
   (format_compiler_result bytes_export
      (M_success (bytes:byte list,data:(A word)list,c:backend_config)) =
      (bytes_export (misc_the [] (lab_to_target_config_ffi_names (backend_config_lab_conf c)))
         bytes data,implode ""))`;;

(* FIXME TODO: this is an awful workaround to avoid implementing a file      *)
(* writer right now.                                                         *)

let add_tap_output_def = cake_def
  `add_tap_output td out = if td = Nil then out else td:(mlstring)app_list`;;

let pancake_backend_conf_def = cake_def
  `pancake_backend_conf (c:backend_config) =
     backend_config_data_conf_fupd
       (K (data_to_word_config_gc_kind_fupd (K data_to_word_None)
             (backend_config_data_conf c))) c`;;
