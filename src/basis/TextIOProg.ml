(* ========================================================================= *)
(* TextIOProg: port of HOL4 basis/TextIOProgScript.sml (CakeML v3479), the   *)
(* code part.  Module for text-based I/O with the underlying file system.   *)
(* The CakeML text of the Quote add_cakeml blocks is HOL4's, verbatim, at  *)
(* HOL4's source positions (add_cakeml_at; the comments between the blocks  *)
(* are left out).  HOL4's EVAL of the                                       *)
(* allocation of iobuff is DoubleProg's BAS1AUX_W8ALLOC_evaluate; its        *)
(* SIMP_RULE of the stream names with n2w8_def is BAS1AUX_STREAM_NAME_CONV  *)
(* (the names as string literals, as HOL4's simplifier leaves them).         *)
(* TextIOProof is M10.                                                       *)
(* ========================================================================= *)

needs "basis/MarshallingProg.ml";;
needs "basis/Marshalling.ml";;
needs "translator/ml_translator.ml";;
needs "basis/basisFunctionsLib.ml";;

type_invention_error := true;;

translation_extends "MarshallingProg";;

ml_prog_update (ml_prog_open_module "TextIO");;

ml_prog_update ml_prog_open_local_block;;

let instream_INDUCT,instream_RECURSION = cake_type "instream = Instream mlstring";;

let outstream_INDUCT,outstream_RECURSION = cake_type "outstream = Outstream mlstring";;

let get_out_def = cake_def
  `get_out (Outstream s) = s`;;

let get_in_def = cake_def
  `get_in (Instream s) = s`;;

use_full_type_names := false;;
register_type `:instream`;;
register_type `:outstream`;;
use_full_type_names := true;;

add_cakeml_at (38,18) {|
  datatype instreambuffered =
  InstreamBuffered
    instream     (* stream name *)
    (int ref)    (* read index *)
    (int ref)    (* write index *)
    byte_array
|};;

let cur_env = ml_prog_get_env (get_ml_prog_state ());;
let TextIOProg_stamp_eval = ml_prog_lookup_eq_conv
  (vsubst [cur_env, `e:v sem_env`]
     `nsLookup (sem_env_c (e:v sem_env)) (Short (implode "InstreamBuffered"))`);;
let instreambuffered_con_stamp = rhs (concl TextIOProg_stamp_eval);;

(* HOL4 [simp] *)
let instreambuffered_con_stamp_def = new_definition
  (mk_eq (`instreambuffered_con_stamp:stamp option`,
          mk_comb (`OPTION_MAP (SND:num#stamp->stamp)`, instreambuffered_con_stamp)));;
let _ = cake_add_simps [instreambuffered_con_stamp_def];;

next_ml_names := ["get_out"];;
let _ = translate get_out_def;;
next_ml_names := ["get_in"];;
let _ = translate get_in_def;;

ml_prog_update ml_prog_open_local_in_block;;

ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [] (implode "raw_instream") (Atapp [] (Short (implode "instream")))` I);;
ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [] (implode "outstream") (Atapp [] (Short (implode "outstream")))` I);;
ml_prog_update (ml_prog_add_dec
  `Dtabbrev unknown_loc [] (implode "instream") (Atapp [] (Short (implode "instreambuffered")))` I);;

add_cakeml_at (69,18) {|
  exception BadFileName;
  exception InvalidFD;
  exception EndOfFile;
  exception IllegalArgument
|};;

ml_prog_update ml_prog_open_local_block;;

let TextIOProg_BadFileName = get_exn_conv `implode "BadFileName"`;;
let TextIOProg_InvalidFD = get_exn_conv `implode "InvalidFD"`;;
let TextIOProg_EndOfFile = get_exn_conv `implode "EndOfFile"`;;
let TextIOProg_IllegalArgument = get_exn_conv `implode "IllegalArgument"`;;

let BadFileName_exn_def = new_definition (vsubst [TextIOProg_BadFileName, `s:stamp`]
  `BadFileName_exn (v:v) <=> v = Conv (SOME (s:stamp)) []`);;

let InvalidFD_exn_def = new_definition (vsubst [TextIOProg_InvalidFD, `s:stamp`]
  `InvalidFD_exn (v:v) <=> v = Conv (SOME (s:stamp)) []`);;

let EndOfFile_exn_def = new_definition (vsubst [TextIOProg_EndOfFile, `s:stamp`]
  `EndOfFile_exn (v:v) <=> v = Conv (SOME (s:stamp)) []`);;

let IllegalArgument_exn_def = new_definition (vsubst [TextIOProg_IllegalArgument, `s:stamp`]
  `IllegalArgument_exn (v:v) <=> v = Conv (SOME (s:stamp)) []`);;

let TextIOProg_iobuff_eval_thm =
  let env = ml_prog_get_env (get_ml_prog_state ())
  and st = ml_prog_get_state (get_ml_prog_state ()) in
  let th = ISPECL [env; st; `2052`; `word 0:byte`] BAS1AUX_W8ALLOC_evaluate in
  let len = rand (rand (concl th)) in
  let len_eq = (ML_PROG_EVAL_CONV THENC REWRITE_CONV [LENGTH_APPEND; LENGTH] THENC
                NUM_REDUCE_CONV) len in
  let th = CONV_RULE (RAND_CONV (RAND_CONV (K len_eq))) th in
  let v_def = ml_prog_define_abbrev false "iobuff_loc" (rand (concl th)) in
  PURE_REWRITE_RULE [GSYM v_def] th;;

ml_prog_update (ml_prog_add_Dlet TextIOProg_iobuff_eval_thm "iobuff");;

ml_prog_update ml_prog_open_local_in_block;;

(* stdout, stderr *)

let stdOut_def = new_definition
  `stdOut = Outstream (implode (MAP (CHR o val) (n2w8 1)))`;;

let stdErr_def = new_definition
  `stdErr = Outstream (implode (MAP (CHR o val) (n2w8 2)))`;;

next_ml_names := ["stdOut"; "stdErr"];;

(* HOL4: SIMP_RULE (srw_ss()) [n2w8_def]; HOL4's simplifier leaves the     *)
(* name as a string literal (its characters CHR n are HOL4's literals): here *)
(* the characters are made literals (the translator's tr_CHR_literal_conv)   *)
(* so that the name is a string literal too                                  *)
let BAS1AUX_STREAM_NAME_CONV =
  REWRITE_CONV [n2w8_def; MAP; o_THM] THENC NUM_REDUCE_CONV THENC
  REWRITE_CONV [VAL_WORD; DIMINDEX_8] THENC NUM_REDUCE_CONV THENC
  DEPTH_CONV tr_CHR_literal_conv;;

let _ = translate (CONV_RULE (RAND_CONV BAS1AUX_STREAM_NAME_CONV) stdOut_def);;

let _ = translate (CONV_RULE (RAND_CONV BAS1AUX_STREAM_NAME_CONV) stdErr_def);;

ml_prog_update ml_prog_open_local_block;;

(* Note how we are in a local block: declarations are not exported. This is *)
(* because we want to only expose the more efficient, buffered input to     *)
(* users. (HOL4 comment)                                                     *)

let raw_stdIn_def = new_definition
  `raw_stdIn = Instream (implode (MAP (CHR o val) (n2w8 0)))`;;

next_ml_names := ["raw_stdIn"];;

let _ = translate (CONV_RULE (RAND_CONV BAS1AUX_STREAM_NAME_CONV) raw_stdIn_def);;
add_cakeml_at (155,18) {|
  fun raw_openIn fname =
    let val b = Word8Array.array 9 (Word8.fromInt 0)
        val a = #(open_in) (fname ^ (String.str (Char.chr 0))) b in
          if Word8Array.sub b 0 = Word8.fromInt 0
          then Instream (Word8Array.substring b 1 8)
          else raise BadFileName
    end
|};;

add_cakeml_at (165,18) {|
  fun raw_closeIn fd =
    let val a = #(close) (get_in fd) iobuff in
          if Word8Array.sub iobuff 0 = Word8.fromInt 0
          then () else raise InvalidFD
    end
|};;

add_cakeml_at (178,18) {|
  fun writei fd n i =
    let val a = Marshalling.n2w2 n iobuff 0
        val a = Marshalling.n2w2 i iobuff 2
        val a = #(write) fd iobuff in
        if Word8Array.sub iobuff 0 = Word8.fromInt 1
        then raise InvalidFD
        else
          let val nw = Marshalling.w22n iobuff 1 in
            if nw = 0 then writei fd n i
            else nw
          end
    end
    fun write fd n i =
      if n = 0 then () else
        let val nw = writei fd n i in
          if nw < n then write fd (n-nw) (i+nw) else () end
|};;

add_cakeml_at (197,18) {|
  fun output_aux fd s i z =
  if z <= i then () else let
    val left = z - i
    val n = if left <= 2048 then left else 2048
    val _ = Word8Array.copyVec s i n iobuff 4
    val _ = write (get_out fd) n 0
  in output_aux fd s (i + n) z end
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (210,18) {|
  fun output1 fd c =
    (Word8Array.update iobuff 4 (Word8.fromInt(Char.ord c)); write (get_out fd) 1 0; ())
|};;

add_cakeml_at (216,18) {|
  fun output fd s = output_aux fd s 0 (String.size s)
  fun print s = output stdOut s
  fun print_err s = output stdErr s
|};;

add_cakeml_at (222,18) {|
  fun print_list ls =
    case ls of [] => () | (x::xs) => (print x; print_list xs)
|};;

add_cakeml_at (227,18) {|
  fun openOut fname =
    let val b = Word8Array.array 9 (Word8.fromInt 0)
        val a = #(open_out) (fname ^ (String.str (Char.chr 0))) b in
          if Word8Array.sub b 0 = Word8.fromInt 0
          then Outstream (Word8Array.substring b 1 8)
          else raise BadFileName
    end
|};;

add_cakeml_at (237,18) {|
  fun closeOut fd =
    let val a = #(close) (get_out fd) iobuff in
          if Word8Array.sub iobuff 0 = Word8.fromInt 0
          then () else raise InvalidFD
    end
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (248,18) {|
  fun read fd n =
    let val a = Marshalling.n2w2 n iobuff 0 in
          (#(read) fd iobuff;
          if Word8.toInt (Word8Array.sub iobuff 0) <> 1
          then Marshalling.w22n iobuff 1
          else raise InvalidFD)
    end
|};;

add_cakeml_at (262,18) {|
  fun raw_input fd buff off len =
  let fun input0 off len count =
      let val nread = read (get_in fd) (min len 2048) in
          if nread = 0 then count else
            (Word8Array.copy iobuff 4 nread buff off;
             input0 (off + nread) (len - nread) (count + nread))
      end
  in input0 off len 0 end
|};;

add_cakeml_at (276,18) {|
  fun extend_array arr =
    let
      val len = Word8Array.length arr
      val arr' = Word8Array.array (2*len) (Word8.fromInt 0)
    in (Word8Array.copy arr 0 len arr' 0; arr') end
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (290,18) {|
  fun openStdInSetBufferSize bsize =
      InstreamBuffered raw_stdIn (Ref 4) (Ref 4)
        (Word8Array.array (min 65535 (max (bsize+4) 1028))
          (Word8.fromInt 48))
|};;

add_cakeml_at (297,18) {|
  fun openStdIn () = openStdInSetBufferSize 4096
|};;

add_cakeml_at (303,18) {|
  fun openInSetBufferSize fname bsize =
    let
      val is = raw_openIn fname
    in
        InstreamBuffered is (Ref 4) (Ref 4)
          (Word8Array.array (min 65535 (max (bsize+4) 1028))
            (Word8.fromInt 48))
    end
|};;

add_cakeml_at (314,18) {|
  fun openIn fname = openInSetBufferSize fname 4096
|};;

add_cakeml_at (318,18) {|
  fun closeIn is =
    case is of InstreamBuffered fd rref wref surplus =>
      raw_closeIn fd
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (327,18) {|
  fun input_aux is buff off len =
    case is of InstreamBuffered fd rref wref surplus =>
      let
        val readat = (!rref)
      in
        Word8Array.copy surplus readat len buff off;
        rref := readat + len;
        len
      end
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (341,18) {|
 fun input is buff off len =
   case is of InstreamBuffered fd rref wref surplus =>
     let
       val nBuffered = (!wref) - (!rref)
     in
       if Word8Array.length buff < len + off then raise IllegalArgument
       else
         if (Word8Array.length surplus - 4) < len then
           (input_aux is buff off nBuffered;
           raw_input fd buff (off+nBuffered) (len - nBuffered) + nBuffered)
         else
           (*If there arent enough bytes in the buffer: copy all of the bytes
           in the buffer and then refill it, and copy the remaining bytes *)
           if len > nBuffered then
             (input_aux is buff off nBuffered;
             wref := 4 + raw_input fd surplus 4 ((Word8Array.length surplus)-4);
             rref := 4;
             (input_aux is buff (off+nBuffered) (min ((!wref) - 4) (len-nBuffered))) + nBuffered)
           (*If there are enough bytes in the buffer, just copy them*)
           else
             input_aux is buff off len
     end
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (369,18) {|
  fun read_into fd buff n =
    let val a = Marshalling.n2w2 n buff 0 in
          (#(read) fd buff;
          if Word8.toInt (Word8Array.sub buff 0) <> 1
          then Marshalling.w22n buff 1
          else raise InvalidFD)
    end
|};;

add_cakeml_at (379,18) {|
 fun refillBuffer_with_read is =
   case is of InstreamBuffered fd rref wref surplus =>
       (wref := 4 + (read_into (get_in fd) surplus ((Word8Array.length surplus)-4));
       rref := 4;
       (!wref) - 4)
|};;

add_cakeml_at (387,18) {|
 fun peekChar_aux is =
   case is of InstreamBuffered fd rref wref surplus =>
          if (!wref) = (!rref) then None
          else
            let val readat = (!rref) in
              Char.some (Char.fromByte (Word8Array.sub surplus readat))
            end
|};;

add_cakeml_at (397,18) {|
 fun input1_aux is =
   case is of InstreamBuffered fd rref wref surplus =>
          let val readat = (!rref) in
            if (!wref) = readat then None
            else
              (rref := readat + 1;
              Char.some (Char.fromByte (Word8Array.sub surplus readat)))
          end
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (410,18) {|
  fun peekChar is =
    case is of InstreamBuffered fd rref wref surplus =>
        if (!wref) = (!rref)
        then (refillBuffer_with_read is; peekChar_aux is)
        else peekChar_aux is
|};;

add_cakeml_at (418,18) {|
  fun input1 is =
    case is of InstreamBuffered fd rref wref surplus =>
        if (!wref) = (!rref)
        then (refillBuffer_with_read is; input1_aux is)
        else input1_aux is
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (428,18) {|
  fun find_surplus c surplus readat writeat =
  if readat = writeat then None
  else
    if Char.fromByte (Word8Array.sub surplus readat) = c
    then Some (readat)
    else find_surplus c surplus (readat + 1) writeat;
|};;

add_cakeml_at (437,18) {|
  fun inputUntil_1 is chr =
  case is of InstreamBuffered fd rref wref surplus =>
  let
    val readat = (!rref)
    val writeat = (!wref)
  in
    case find_surplus chr surplus readat writeat of
      None =>
      (rref := writeat;
        Inl (Word8Array.substring surplus readat (writeat-readat)))
    | Some i =>
      (rref := i+1;
        Inr (Word8Array.substring surplus readat (i+1-readat)))
  end;
|};;

add_cakeml_at (454,18) {|
  fun refillBuffer_with_read_guard is =
    (refillBuffer_with_read is;
     case is of InstreamBuffered fd rref wref surplus =>
     (!wref) = (!rref));
|};;

add_cakeml_at (461,18) {|
  fun inputUntil_2 is chr acc =
  case inputUntil_1 is chr of
    Inr s => Some (case acc of [] => s | _ => String.concat (List.rev (s :: acc)))
  | Inl s =>
      if refillBuffer_with_read_guard is
      then
        let
          val res = String.concat (List.rev (String.str chr :: s :: acc))
        in if String.size res = 1 then None else Some res end
      else
        inputUntil_2 is chr (s :: acc);
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (477,18) {|
  fun inputLineWith c0 is = inputUntil_2 is c0 []
|};;

add_cakeml_at (481,18) {|
  fun inputLine is = inputLineWith #"\n" is
|};;

add_cakeml_at (485,18) {|
  fun inputLineTokens c0 is tokP mp =
    case inputLineWith c0 is of
      None => None
    | Some l =>
      Some (List.map mp (String.tokens tokP l))
|};;

ml_prog_update ml_prog_open_local_block;;

add_cakeml_at (495,18) {|
  fun inputLines_aux c0 is acc =
     case inputLineWith c0 is of
       None => List.rev acc
     | Some l => inputLines_aux c0 is (l::acc)
|};;

add_cakeml_at (502,18) {|
  fun inputAllTokens_aux c0 is f g acc =
     case inputLineTokens c0 is f g of
       None => List.rev acc
     | Some l => inputAllTokens_aux c0 is f g (l::acc)
|};;

add_cakeml_at (509,18) {|
  fun consume_rest is =
    case input1 is of
      None => ()
    | Some c => consume_rest is;
|};;

add_cakeml_at (516,18) {|
  fun open_option stdin_or_fname =
    case stdin_or_fname of
      None (* stdin *) =>
                    (let
                       val is = openStdIn ()
                     in Some (is, (fn () => consume_rest is)) end)
    | Some fname => (let
                       val is = openIn fname
                     in Some (is, (fn () => closeIn is)) end
                     handle BadFileName => None)
|};;

add_cakeml_at (529,18) {|
  fun fold_chars_loop f is y =
    case input1 is of
      None => y
    | Some c => fold_chars_loop f is (f c y);
  fun fold_lines_loop c0 f is y =
    case inputLineWith c0 is of
      None => y
    | Some c => fold_lines_loop c0 f is (f c y);
  fun fold_tokens_loop c0 tokP mp fld is y =
    case inputLineTokens c0 is tokP mp of
      None => y
    | Some c => fold_tokens_loop c0 tokP mp fld is (fld c y);
|};;

add_cakeml_at (544,18) {|
  fun inputBuff is =
    case is of InstreamBuffered fd rref wref surplus =>
    let
      val r = (!rref)
      val w = (!wref)
      val u = (rref := w)
    in
      Word8Array.substring surplus r (w - r)
    end
|};;

add_cakeml_at (556,18) {|
  fun inputAll_aux is acc =
    let
      val new_acc = inputBuff is :: acc
    in
      if refillBuffer_with_read_guard is then
        String.concat (List.rev new_acc)
      else
        inputAll_aux is new_acc
    end
|};;

ml_prog_update ml_prog_open_local_in_block;;

add_cakeml_at (570,18) {|
  fun inputLines c0 is =
    inputLines_aux c0 is []
|};;

add_cakeml_at (575,18) {|
  fun inputLinesFile c0 fname =
    let
      val is = openIn fname
      val lines = inputLines c0 is
    in
      closeIn is; Some lines
    end handle BadFileName => None
|};;

add_cakeml_at (585,18) {|
  fun inputLinesStdIn c0 =
    let
      val is = openStdIn ()
    in
      inputLines c0 is
    end
|};;

add_cakeml_at (594,18) {|
  fun inputAll is = inputAll_aux is []
|};;

add_cakeml_at (598,18) {|
  fun inputAllFrom stdin_or_fname =
    case open_option stdin_or_fname of
      None => None
    | Some (is,close) => let
        val content = inputAll is
      in close (); Some content end
      handle e => (close (); raise e)
|};;

add_cakeml_at (608,18) {|
  fun inputAllTokens c0 is f g =
    inputAllTokens_aux c0 is f g []
|};;

add_cakeml_at (614,18) {|
  fun inputAllTokensFile c0 fname f g =
    let
      val is = openIn fname
      val lines = inputAllTokens c0 is f g
    in
      closeIn is; Some lines
    end handle BadFileName => None
|};;

add_cakeml_at (624,18) {|
  fun inputAllTokensFrom c0 stdin_or_fname f g =
    case open_option stdin_or_fname of
      None => None
    | Some (is,close) => let
        val lines = inputAllTokens c0 is f g
      in close (); Some lines end
      handle e => (close (); raise e)
|};;

add_cakeml_at (634,18) {|
  fun foldChars f x stdin_or_fname =
    case open_option stdin_or_fname of
      None => None
    | Some (is,close) =>
      (let
         val res = fold_chars_loop f is x
         val _ = close ()
       in Some res end
       handle e => (close (); raise e))
|};;

add_cakeml_at (646,18) {|
  fun foldLines c0 f x stdin_or_fname =
    case open_option stdin_or_fname of
      None => None
    | Some (is,close) =>
      (let
         val res = fold_lines_loop c0 f is x
         val _ = close ()
       in Some res end
       handle e => (close (); raise e))
|};;

add_cakeml_at (658,18) {|
  fun foldTokens c0 tokP mp fld x stdin_or_fname =
    case open_option stdin_or_fname of
      None => None
    | Some (is,close) =>
      (let
         val res = fold_tokens_loop c0 tokP mp fld is x
         val _ = close ()
       in Some res end
       handle e => (close (); raise e))
|};;

ml_prog_update ml_prog_close_local_blocks;;

ml_prog_update (ml_prog_close_module None);;

finalise_translation ();;
