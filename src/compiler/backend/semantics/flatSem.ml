(* ========================================================================= *)
(* flatSem: port of HOL4 compiler/backend/semantics/flatSemScript.sml        *)
(* (CakeML v3479).  The formal semantics of flatLang.                        *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's type variables 'c 'ffi are C FFI; word8 is byte, word64 int64;   *)
(*   n2w is word, w2n is val, Num (ABS n) is num_of_int (abs n), int_of_num  *)
(*   is &; FOLDR f e l is ITLIST f l e; the mlstring literal of x is         *)
(*   implode "x", s1 ^ s2 is strcat s1 s2; HOL4's trace None is              *)
(*   backend_common_None.                                                    *)
(* - Record fields: env.v is flat_environment_v env, s.clock is              *)
(*   flat_state_clock s, ...; r with f := x is rec_f_fupd (K x) r, r with f  *)
(*   updated_by g is rec_f_fupd g r; a literal <| ... |> is rec_REC.         *)
(* - In the Arith and FromTo cases of do_app, check_type, do_arith and       *)
(*   do_conversion are semanticPrimitives' (on source values), as HOL4's     *)
(*   overloading resolves them.                                              *)
(* - The semantics is defined with fix_clock (as in HOL4) so that the        *)
(*   termination conditions are provable; HOL4 then rebinds evaluate_def and *)
(*   evaluate_ind to the versions without fix_clock.  Here the definition    *)
(*   with fix_clock and its induction theorem are FLATSEMAUX_evaluate_fix_def*)
(*   and FLATSEMAUX_evaluate_fix_ind (HOL4's first evaluate_def and          *)
(*   evaluate_ind); flat_evaluate_def and flat_evaluate_ind are HOL4's final *)
(*   theorems.  In the Eval case HOL4's let s = s with eval_config := c in t *)
(*   is t with the updated state written out (the recursion package gives a  *)
(*   let no context).                                                        *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/lprefix_lub.ml";;
needs "compiler/backend/flatLang.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/evaluate.ml";;

type_invention_error := true;;

(* The values of flatLang differ from source semantic values in that the    *)
(* closures do not carry environments for global definitions.               *)
(*                                                                           *)
(* The semantics of flatLang differ from source in that there is no module  *)
(* environment menv, nor are top-level bindings added to the normal env,    *)
(* thus when a closure is created, only locals bindings are put into it.    *)
(* There is a global environment genv, which is just a list of the          *)
(* top-level bindings seen so far, with the older bindings nearer the head. *)
(* Global variable reference expressions simply index into global           *)
(* environment.  Top-level let rec declarations evaluate to closures,       *)
(* rather than to recursive closures, since the recursion can be handled    *)
(* through the genv.  The expressions bound to top-level lets must evaluate *)
(* to a tuple with exactly as many things in it as the number of bindings   *)
(* that the let will bind.                                                   *)

(* HOL4: environment (a record with one field v) *)

let flat_environment_INFO = cake_record "flat_environment"
  ["v","(varN#V) list"];;

let flat_environment_component_equality =
  flat_environment_INFO.ri_component_equality;;

(* HOL4: v *)

let flat_v_INDUCT,flat_v_RECURSION = cake_type
  "flat_v = flat_Litv lit
          | flat_Conv ((ctor_id # type_id) option) (flat_v list)
          | flat_Closure ((flat_v)flat_environment) varN flat_exp
          | flat_Recclosure ((flat_v)flat_environment)
                            ((varN # varN # flat_exp) list) varN
          | flat_Loc bool num
          | flat_Vectorv (flat_v list)";;

let install_config_INFO = cake_record "install_config"
  ["compile","C->flat_exp list->(byte list#int64 list#C)option";
   "compile_oracle","num->C#flat_exp list"];;

let install_config_component_equality =
  install_config_INFO.ri_component_equality;;

(* HOL4: state; eval_config: eval or install mode *)

let flat_state_INFO = cake_record "flat_state"
  ["clock","num";
   "refs","(flat_v store_v) list";
   "ffi","(FFI)ffi_state";
   "globals","(flat_v option) list";
   "eval_config","(C)install_config"];;

let flat_state_component_equality = flat_state_INFO.ri_component_equality;;

let list_id_def = cake_def
  `list_id = 1`;;

(* HOL4: Boolv_def *)
let flat_Boolv_def = cake_def
  `flat_Boolv b =
     flat_Conv (SOME ((if b then true_tag else false_tag),SOME bool_id)) []`;;

(* HOL4: Unitv_def *)
let flat_Unitv_def = cake_def
  `Unitv = flat_Conv NONE []`;;

(* HOL4: bind_exn_v_def, chr_exn_v_def, div_exn_v_def *)
let flat_bind_exn_v_def = cake_def
  `flat_bind_exn_v = flat_Conv (SOME (bind_tag,NONE)) []`;;

let flat_chr_exn_v_def = cake_def
  `flat_chr_exn_v = flat_Conv (SOME (chr_tag,NONE)) []`;;

let flat_div_exn_v_def = cake_def
  `flat_div_exn_v = flat_Conv (SOME (div_tag,NONE)) []`;;

let subscript_exn_v_def = cake_def
  `subscript_exn_v = flat_Conv (SOME (subscript_tag,NONE)) []`;;

(* HOL4: build_rec_env_def *)
let flat_build_rec_env_def = cake_def
  `flat_build_rec_env (funs:(varN#varN#flat_exp) list) cl_env add_to_env =
     ITLIST (\fxe env'. match fxe with
                          (f,x,e) -> CONS (f,flat_Recclosure cl_env funs f) env')
            funs add_to_env`;;

(* HOL4: ctor_same_type_def (polymorphic, as in HOL4) *)
let flat_ctor_same_type_def = cake_def
  `(flat_ctor_same_type (SOME ((_:A),(t:B))) (SOME ((_:C),t')) <=> t = t') /\
   (flat_ctor_same_type (NONE:(A#B)option) (NONE:(C#B)option) <=> T) /\
   (flat_ctor_same_type _ _ <=> F)`;;

(* HOL4: do_eq_def; HOL4's Loc b1 l1 / Loc b2 l2 are Loc b1 n1 / Loc b2 n2 *)
(* here (l1 and l2 are the literals of the first clause)                    *)

let flat_do_eq_def = sem1aux_def_wf
  `inv_image (<)
     (\x:(flat_v # flat_v) + (flat_v list # flat_v list).
        sum_CASE x (\t. flat_v_size (FST t))
                   (\t. list_size flat_v_size (FST t)))`
  SEM1AUX_TC_TAC
  `(flat_do_eq (flat_Litv l1) (flat_Litv l2) =
      if lit_same_type l1 l2 then Eq_val (l1 = l2) else Eq_type_error) /\
   (flat_do_eq (flat_Loc b1 n1) (flat_Loc b2 n2) =
      if b1 /\ b2 then Eq_val (n1 = n2) else Eq_type_error) /\
   (flat_do_eq (flat_Conv cn1 vs1) (flat_Conv cn2 vs2) =
      if cn1 = cn2 /\ LENGTH vs1 = LENGTH vs2 then flat_do_eq_list vs1 vs2
      else if flat_ctor_same_type cn1 cn2 then Eq_val F
      else Eq_type_error) /\
   (flat_do_eq (flat_Vectorv vs1) (flat_Vectorv vs2) =
      if LENGTH vs1 = LENGTH vs2 then flat_do_eq_list vs1 vs2
      else Eq_val F) /\
   (flat_do_eq (flat_Closure _ _ _) (flat_Closure _ _ _) = Eq_val T) /\
   (flat_do_eq (flat_Closure _ _ _) (flat_Recclosure _ _ _) = Eq_val T) /\
   (flat_do_eq (flat_Recclosure _ _ _) (flat_Closure _ _ _) = Eq_val T) /\
   (flat_do_eq (flat_Recclosure _ _ _) (flat_Recclosure _ _ _) = Eq_val T) /\
   (flat_do_eq _ _ = Eq_type_error) /\
   (flat_do_eq_list [] [] = Eq_val T) /\
   (flat_do_eq_list (CONS v1 vs1) (CONS v2 vs2) =
      match flat_do_eq v1 v2 with
        Eq_type_error -> Eq_type_error
      | Eq_val r -> if r then flat_do_eq_list vs1 vs2 else Eq_val F) /\
   (flat_do_eq_list _ _ = Eq_val F)`;;

let flat_do_eq_ind = cake_ind "flat_do_eq";;

(* Do an application *)

let flat_do_opapp_def = cake_def
  `flat_do_opapp vs =
     match vs with
       [flat_Closure env n e; v] ->
         SOME (flat_environment_v_fupd (\env. CONS (n,v) env) env,e)
     | [flat_Recclosure env funs n; v] ->
         if ALL_DISTINCT (MAP FST funs) then
           (match find_recfun n funs with
              SOME (n,e) ->
                SOME (flat_environment_v_fupd
                        (K (CONS (n,v)
                              (flat_build_rec_env funs env
                                 (flat_environment_v env)))) env,e)
            | NONE -> NONE)
         else NONE
     | _ -> NONE`;;

let flat_v_to_list_def = sem1aux_def
  `(flat_v_to_list (flat_Conv (SOME (cid,tid)) []) =
      if cid = nil_tag /\ tid = SOME list_id then SOME [] else NONE) /\
   (flat_v_to_list (flat_Conv (SOME (cid,tid)) [v1; v2]) =
      if cid = cons_tag /\ tid = SOME list_id then
        (match flat_v_to_list v2 with
           SOME vs -> SOME (CONS v1 vs)
         | NONE -> NONE)
      else NONE) /\
   (flat_v_to_list _ = NONE)`;;

let flat_v_to_list_ind = cake_ind "flat_v_to_list";;

let flat_list_to_v_def = cake_def
  `(flat_list_to_v [] = flat_Conv (SOME (nil_tag,SOME list_id)) []) /\
   (flat_list_to_v (CONS x xs) =
      flat_Conv (SOME (cons_tag,SOME list_id)) [x; flat_list_to_v xs])`;;

let flat_v_to_char_list_def = sem1aux_def
  `(flat_v_to_char_list (flat_Conv (SOME (cid,tid)) []) =
      if cid = nil_tag /\ tid = SOME list_id then SOME [] else NONE) /\
   (flat_v_to_char_list (flat_Conv (SOME (cid,tid)) [flat_Litv (Char c); v]) =
      if cid = cons_tag /\ tid = SOME list_id then
        (match flat_v_to_char_list v with
           SOME cs -> SOME (CONS c cs)
         | NONE -> NONE)
      else NONE) /\
   (flat_v_to_char_list _ = NONE)`;;

let flat_v_to_char_list_ind = cake_ind "flat_v_to_char_list";;

let flat_vs_to_string_def = sem1aux_def
  `(flat_vs_to_string [] = SOME (implode "")) /\
   (flat_vs_to_string (CONS (flat_Litv (StrLit s1)) vs) =
      match flat_vs_to_string vs with
        SOME s2 -> SOME (strcat s1 s2)
      | _ -> NONE) /\
   (flat_vs_to_string _ = NONE)`;;

let flat_vs_to_string_ind = cake_ind "flat_vs_to_string";;

let flat_v_to_bytes_def = cake_def
  `flat_v_to_bytes lv =
     some ns. flat_v_to_list lv = SOME (MAP (flat_Litv o Word8) ns)`;;

let flat_v_to_words_def = cake_def
  `flat_v_to_words lv =
     some ns. flat_v_to_list lv = SOME (MAP (flat_Litv o Word64) ns)`;;

let flat_check_type_def = sem1aux_def
  `(flat_check_type BoolT v <=> v = flat_Boolv T \/ v = flat_Boolv F) /\
   (flat_check_type IntT v <=> ?i. v = flat_Litv (IntLit i)) /\
   (flat_check_type CharT v <=> ?c. v = flat_Litv (Char c)) /\
   (flat_check_type StrT v <=> ?s. v = flat_Litv (StrLit s)) /\
   (flat_check_type (WordT W8) v <=> ?w. v = flat_Litv (Word8 w)) /\
   (flat_check_type (WordT W64) v <=> ?w. v = flat_Litv (Word64 w)) /\
   (flat_check_type Float64T v <=> ?w. v = flat_Litv (Float64 w))`;;

let flat_dest_Litv_def = sem1aux_def
  `(flat_dest_Litv (flat_Litv v) = SOME v) /\
   (flat_dest_Litv _ = NONE)`;;

let flat_the_Litv_Float64_def = cake_def
  `flat_the_Litv_Float64 (flat_Litv (Float64 w)) = w`;;

let flat_do_test_def = sem1aux_def
  `(flat_do_test Equal ty v1 v2 =
      if flat_check_type ty v1 /\ flat_check_type ty v2 then
        (if ty = Float64T
         then Eq_val (fp64_equal (flat_the_Litv_Float64 v1)
                                 (flat_the_Litv_Float64 v2))
         else flat_do_eq v1 v2)
      else Eq_type_error) /\
   (flat_do_test (Compare cmp) ty v1 v2 =
      match (ty,flat_dest_Litv v1,flat_dest_Litv v2) with
        (IntT,SOME (IntLit i),SOME (IntLit j)) -> Eq_val (int_cmp cmp i j)
      | (CharT,SOME (Char c),SOME (Char d)) ->
          Eq_val (num_cmp cmp (ORD c) (ORD d))
      | (WordT W8,SOME (Word8 w),SOME (Word8 v)) ->
          Eq_val (num_cmp cmp (val w) (val v))
      | (Float64T,SOME (Float64 w),SOME (Float64 v)) -> Eq_val (fp_cmp cmp w v)
      | (StrT,SOME (StrLit s),SOME (StrLit t)) -> Eq_val (str_cmp F cmp s t)
      | _ -> Eq_type_error) /\
   (flat_do_test (AltCompare cmp) ty v1 v2 =
      match (ty,flat_dest_Litv v1,flat_dest_Litv v2) with
        (StrT,SOME (StrLit s),SOME (StrLit t)) -> Eq_val (str_cmp T cmp s t)
      | _ -> Eq_type_error)`;;

let v_to_flat_def = cake_def
  `(v_to_flat (Litv v) = flat_Litv v) /\
   (v_to_flat (Conv x y) =
      if Conv x y = Boolv T then flat_Boolv T else
      if Conv x y = Boolv F then flat_Boolv F else flat_Vectorv []) /\
   (v_to_flat _ = flat_Vectorv [])`;;

let flat_to_v_def = cake_def
  `(flat_to_v (flat_Litv v) = Litv v) /\
   (flat_to_v (flat_Conv x y) =
      if flat_Conv x y = flat_Boolv T then Boolv T else
      if flat_Conv x y = flat_Boolv F then Boolv F else Vectorv []) /\
   (flat_to_v _ = Vectorv [])`;;

(* HOL4: dest_thunk_ret *)

let flat_dest_thunk_ret_INDUCT,flat_dest_thunk_ret_RECURSION = cake_type
  "flat_dest_thunk_ret = flat_BadRef
                       | flat_NotThunk
                       | flat_IsThunk thunk_mode flat_v";;

let flat_dest_thunk_def = sem1aux_def
  `(flat_dest_thunk [flat_Loc b n] (st:(flat_v store_v) list) =
      match store_lookup n st with
        NONE -> flat_BadRef
      | SOME (Thunk Evaluated v) ->
          if b then flat_BadRef else flat_IsThunk Evaluated v
      | SOME (Thunk NotEvaluated v) ->
          if b then flat_BadRef else flat_IsThunk NotEvaluated v
      | SOME _ -> flat_NotThunk) /\
   (flat_dest_thunk vs st = flat_NotThunk)`;;

(* HOL4's first clause has the pattern Loc F n, so that its completion has  *)
(* a clause for Loc T n; here Loc b n with if b then NONE (the kit does not *)
(* complete clauses with literal patterns)                                   *)

let flat_update_thunk_def = sem1aux_def
  `(flat_update_thunk [flat_Loc b n] (st:(flat_v store_v) list) [v] =
      if b then NONE else
      match flat_dest_thunk [v] st with
        flat_NotThunk -> store_assign n (Thunk Evaluated v) st
      | _ -> NONE) /\
   (flat_update_thunk _ st _ = NONE)`;;

let flat_bad_thunk_update_def = cake_def
  `flat_bad_thunk_update m v (refs:(flat_v store_v) list) <=>
     m = Evaluated /\ ~(flat_dest_thunk [v] refs = flat_NotThunk)`;;

(* HOL4: do_app_def.  Num (ABS n) is num_of_int (abs n); int_of_num is &;    *)
(* n2w is word; s with refs := r is flat_state_refs_fupd (K r) s.            *)

let flat_do_app_def = sem1aux_def
  `flat_do_app (s:(C,FFI)flat_state) op (vs:flat_v list) =
     match (op,vs) with
       (Src (Shift wz sh n),[flat_Litv w]) ->
         (match do_shift sh n wz w with
            NONE -> NONE
          | SOME w -> SOME (s,Rval (flat_Litv w)))
     | (Src Equality,[v1; v2]) ->
         (match flat_do_eq v1 v2 with
            Eq_type_error -> NONE
          | Eq_val b -> SOME (s,Rval (flat_Boolv b)))
     | (Src (Test test test_ty),[v1; v2]) ->
         (match flat_do_test test test_ty v1 v2 with
            Eq_type_error -> NONE
          | Eq_val b -> SOME (s,Rval (flat_Boolv b)))
     | (Src (Arith a ty),vs) ->
         (let vs = MAP flat_to_v vs in
          if ALL (check_type ty) vs then
            (match do_arith a ty vs with
               SOME (INR res) -> SOME (s,Rval (v_to_flat res))
             | SOME (INL exn) -> SOME (s,Rerr (Rraise flat_div_exn_v))
             | NONE -> NONE)
          else NONE)
     | (Src (FromTo ty1 ty2),[v]) ->
         (let v = flat_to_v v in
          if check_type ty1 v then
            (match do_conversion v ty1 ty2 with
               SOME (INR res) -> SOME (s,Rval (v_to_flat res))
             | SOME (INL exn) -> SOME (s,Rerr (Rraise flat_chr_exn_v))
             | NONE -> NONE)
          else NONE)
     | (Src Opassign,[flat_Loc _ lnum; v]) ->
         (match store_assign lnum (Refv v) (flat_state_refs s) with
            SOME s' -> SOME (flat_state_refs_fupd (K s') s,Rval Unitv)
          | NONE -> NONE)
     | (Src Opref,[v]) ->
         let (s',n) = store_alloc (Refv v) (flat_state_refs s) in
         SOME (flat_state_refs_fupd (K s') s,Rval (flat_Loc T n))
     | (Src Aw8alloc,[flat_Litv (IntLit n); flat_Litv (Word8 w)]) ->
         if n < &0 then
           SOME (s,Rerr (Rraise subscript_exn_v))
         else
           let (s',lnum) =
             store_alloc (W8array (REPLICATE (num_of_int (abs n)) w))
               (flat_state_refs s) in
           SOME (flat_state_refs_fupd (K s') s,Rval (flat_Loc T lnum))
     | (Src Aw8sub,[flat_Loc _ lnum; flat_Litv (IntLit i)]) ->
         (match store_lookup lnum (flat_state_refs s) with
            SOME (W8array ws) ->
              if i < &0 then
                SOME (s,Rerr (Rraise subscript_exn_v))
              else
                let n = num_of_int (abs i) in
                if n >= LENGTH ws then
                  SOME (s,Rerr (Rraise subscript_exn_v))
                else
                  SOME (s,Rval (flat_Litv (Word8 (EL n ws))))
          | _ -> NONE)
     | (Src Aw8sub_unsafe,[flat_Loc _ lnum; flat_Litv (IntLit i)]) ->
         (match store_lookup lnum (flat_state_refs s) with
            SOME (W8array ws) ->
              if i < &0 then
                NONE
              else
                let n = num_of_int (abs i) in
                if n >= LENGTH ws then
                  NONE
                else
                  SOME (s,Rval (flat_Litv (Word8 (EL n ws))))
          | _ -> NONE)
     | (Src Aw8length,[flat_Loc _ n]) ->
         (match store_lookup n (flat_state_refs s) with
            SOME (W8array ws) ->
              SOME (s,Rval (flat_Litv (IntLit (&(LENGTH ws)))))
          | _ -> NONE)
     | (Src Aw8update,[flat_Loc _ lnum; flat_Litv (IntLit i);
                       flat_Litv (Word8 w)]) ->
         (match store_lookup lnum (flat_state_refs s) with
            SOME (W8array ws) ->
              if i < &0 then
                SOME (s,Rerr (Rraise subscript_exn_v))
              else
                let n = num_of_int (abs i) in
                if n >= LENGTH ws then
                  SOME (s,Rerr (Rraise subscript_exn_v))
                else
                  (match store_assign lnum (W8array (LUPDATE w n ws))
                           (flat_state_refs s) with
                     NONE -> NONE
                   | SOME s' -> SOME (flat_state_refs_fupd (K s') s,Rval Unitv))
          | _ -> NONE)
     | (Src Aw8update_unsafe,[flat_Loc _ lnum; flat_Litv (IntLit i);
                              flat_Litv (Word8 w)]) ->
         (match store_lookup lnum (flat_state_refs s) with
            SOME (W8array ws) ->
              if i < &0 then
                NONE
              else
                let n = num_of_int (abs i) in
                if n >= LENGTH ws then
                  NONE
                else
                  (match store_assign lnum (W8array (LUPDATE w n ws))
                           (flat_state_refs s) with
                     NONE -> NONE
                   | SOME s' -> SOME (flat_state_refs_fupd (K s') s,Rval Unitv))
          | _ -> NONE)
     | (Src CopyStrStr,[flat_Litv (StrLit str); flat_Litv (IntLit off);
                        flat_Litv (IntLit len)]) ->
         SOME (s,
               (match copy_array (explode str,off) len NONE with
                  NONE -> Rerr (Rraise subscript_exn_v)
                | SOME cs -> Rval (flat_Litv (StrLit (implode cs)))))
     | (Src CopyStrAw8,[flat_Litv (StrLit str); flat_Litv (IntLit off);
                        flat_Litv (IntLit len); flat_Loc _ dst;
                        flat_Litv (IntLit dstoff)]) ->
         (match store_lookup dst (flat_state_refs s) with
            SOME (W8array ws) ->
              (match copy_array (explode str,off) len
                       (SOME (ws_to_chars ws,dstoff)) with
                 NONE -> SOME (s,Rerr (Rraise subscript_exn_v))
               | SOME cs ->
                   (match store_assign dst (W8array (chars_to_ws cs))
                            (flat_state_refs s) with
                      SOME s' -> SOME (flat_state_refs_fupd (K s') s,Rval Unitv)
                    | _ -> NONE))
          | _ -> NONE)
     | (Src CopyAw8Str,[flat_Loc _ src; flat_Litv (IntLit off);
                        flat_Litv (IntLit len)]) ->
         (match store_lookup src (flat_state_refs s) with
            SOME (W8array ws) ->
              SOME (s,
                    (match copy_array (ws,off) len NONE with
                       NONE -> Rerr (Rraise subscript_exn_v)
                     | SOME ws ->
                         Rval (flat_Litv (StrLit (implode (ws_to_chars ws))))))
          | _ -> NONE)
     | (Src CopyAw8Aw8,[flat_Loc _ src; flat_Litv (IntLit off);
                        flat_Litv (IntLit len); flat_Loc _ dst;
                        flat_Litv (IntLit dstoff)]) ->
         (match (store_lookup src (flat_state_refs s),
                 store_lookup dst (flat_state_refs s)) with
            (SOME (W8array ws),SOME (W8array ds)) ->
              (match copy_array (ws,off) len (SOME (ds,dstoff)) with
                 NONE -> SOME (s,Rerr (Rraise subscript_exn_v))
               | SOME ws ->
                   (match store_assign dst (W8array ws) (flat_state_refs s) with
                      SOME s' -> SOME (flat_state_refs_fupd (K s') s,Rval Unitv)
                    | _ -> NONE))
          | _ -> NONE)
     | (Src XorAw8Str_unsafe,[flat_Loc _ dst; flat_Litv (StrLit str_arg)]) ->
         (match store_lookup dst (flat_state_refs s) with
            SOME (W8array ds) ->
              (match xor_bytes (MAP (word o ORD) (explode str_arg)) ds with
                 NONE -> NONE
               | SOME new_bs ->
                   (match store_assign dst (W8array new_bs) (flat_state_refs s) with
                      NONE -> NONE
                    | SOME s' -> SOME (flat_state_refs_fupd (K s') s,Rval Unitv)))
          | _ -> NONE)
     | (Src Implode,[v]) ->
         (match flat_v_to_char_list v with
            SOME ls -> SOME (s,Rval (flat_Litv (StrLit (implode ls))))
          | NONE -> NONE)
     | (Src Explode,[flat_Litv (StrLit str)]) ->
         SOME (s,Rval (flat_list_to_v (MAP (\c. flat_Litv (Char c)) (explode str))))
     | (Src Strsub,[flat_Litv (StrLit str); flat_Litv (IntLit i)]) ->
         if i < &0 then
           SOME (s,Rerr (Rraise subscript_exn_v))
         else
           let n = num_of_int (abs i) in
           if n >= strlen str then
             SOME (s,Rerr (Rraise subscript_exn_v))
           else
             SOME (s,Rval (flat_Litv (Char (strsub str n))))
     | (Src Strlen,[flat_Litv (StrLit str)]) ->
         SOME (s,Rval (flat_Litv (IntLit (&(strlen str)))))
     | (Src Strcat,[v]) ->
         (match flat_v_to_list v with
            SOME vs ->
              (match flat_vs_to_string vs with
                 SOME str -> SOME (s,Rval (flat_Litv (StrLit str)))
               | _ -> NONE)
          | _ -> NONE)
     | (Src VfromList,[v]) ->
         (match flat_v_to_list v with
            SOME vs -> SOME (s,Rval (flat_Vectorv vs))
          | NONE -> NONE)
     | (Src Vsub,[flat_Vectorv vs; flat_Litv (IntLit i)]) ->
         if i < &0 then
           SOME (s,Rerr (Rraise subscript_exn_v))
         else
           let n = num_of_int (abs i) in
           if n >= LENGTH vs then
             SOME (s,Rerr (Rraise subscript_exn_v))
           else
             SOME (s,Rval (EL n vs))
     | (Src Vsub_unsafe,[flat_Vectorv vs; flat_Litv (IntLit i)]) ->
         if &0 <= i /\ num_of_int i < LENGTH vs then
           SOME (s,Rval (EL (num_of_int i) vs))
         else
           NONE
     | (Src Vlength,[flat_Vectorv vs]) ->
         SOME (s,Rval (flat_Litv (IntLit (&(LENGTH vs)))))
     | (Src Aalloc,[flat_Litv (IntLit n); v]) ->
         if n < &0 then
           SOME (s,Rerr (Rraise subscript_exn_v))
         else
           let (s',lnum) =
             store_alloc (Varray (REPLICATE (num_of_int (abs n)) v))
               (flat_state_refs s) in
           SOME (flat_state_refs_fupd (K s') s,Rval (flat_Loc T lnum))
     | (Src AallocFixed,vs) ->
         let (s',lnum) = store_alloc (Varray vs) (flat_state_refs s) in
         SOME (flat_state_refs_fupd (K s') s,Rval (flat_Loc T lnum))
     | (Src Asub,[flat_Loc _ lnum; flat_Litv (IntLit i)]) ->
         (match store_lookup lnum (flat_state_refs s) with
            SOME (Varray vs) ->
              if i < &0 then
                SOME (s,Rerr (Rraise subscript_exn_v))
              else
                let n = num_of_int (abs i) in
                if n >= LENGTH vs then
                  SOME (s,Rerr (Rraise subscript_exn_v))
                else
                  SOME (s,Rval (EL n vs))
          | _ -> NONE)
     | (Src Asub_unsafe,[flat_Loc _ lnum; flat_Litv (IntLit i)]) ->
         (match store_lookup lnum (flat_state_refs s) with
            SOME (Varray vs) ->
              if i < &0 then
                NONE
              else
                let n = num_of_int (abs i) in
                if n >= LENGTH vs then
                  NONE
                else
                  SOME (s,Rval (EL n vs))
          | _ -> NONE)
     | (Src Alength,[flat_Loc _ n]) ->
         (match store_lookup n (flat_state_refs s) with
            SOME (Varray ws) ->
              SOME (s,Rval (flat_Litv (IntLit (&(LENGTH ws)))))
          | _ -> NONE)
     | (Src Aupdate,[flat_Loc _ lnum; flat_Litv (IntLit i); v]) ->
         (match store_lookup lnum (flat_state_refs s) with
            SOME (Varray vs) ->
              if i < &0 then
                SOME (s,Rerr (Rraise subscript_exn_v))
              else
                let n = num_of_int (abs i) in
                if n >= LENGTH vs then
                  SOME (s,Rerr (Rraise subscript_exn_v))
                else
                  (match store_assign lnum (Varray (LUPDATE v n vs))
                           (flat_state_refs s) with
                     NONE -> NONE
                   | SOME s' -> SOME (flat_state_refs_fupd (K s') s,Rval Unitv))
          | _ -> NONE)
     | (Src Aupdate_unsafe,[flat_Loc _ lnum; flat_Litv (IntLit i); v]) ->
         (match store_lookup lnum (flat_state_refs s) with
            SOME (Varray vs) ->
              if i < &0 then
                NONE
              else
                let n = num_of_int (abs i) in
                if n >= LENGTH vs then
                  NONE
                else
                  (match store_assign lnum (Varray (LUPDATE v n vs))
                           (flat_state_refs s) with
                     NONE -> NONE
                   | SOME s' -> SOME (flat_state_refs_fupd (K s') s,Rval Unitv))
          | _ -> NONE)
     | (Src ListAppend,[x1; x2]) ->
         (match (flat_v_to_list x1,flat_v_to_list x2) with
            (SOME xs,SOME ys) -> SOME (s,Rval (flat_list_to_v (APPEND xs ys)))
          | _ -> NONE)
     | (Src ConfigGC,[flat_Litv (IntLit n1); flat_Litv (IntLit n2)]) ->
         SOME (s,Rval Unitv)
     | (Src (FFI n),[flat_Litv (StrLit conf); flat_Loc _ lnum]) ->
         (match store_lookup lnum (flat_state_refs s) with
            SOME (W8array ws) ->
              (match call_FFI (flat_state_ffi s) (ExtCall n)
                       (MAP (\c. word (ORD c)) (explode conf)) ws with
                 FFI_final outcome ->
                   SOME (s,Rerr (Rabort (Rffi_error outcome)))
               | FFI_return t' ws' ->
                   (match store_assign lnum (W8array ws') (flat_state_refs s) with
                      SOME s' ->
                        SOME (flat_state_refs_fupd (K s')
                                (flat_state_ffi_fupd (K t') s),Rval Unitv)
                    | NONE -> NONE))
          | _ -> NONE)
     | (Src Opapp,_) -> NONE
     | (Src Eval,_) -> NONE
     | (Src (ThunkOp th_op),vs) ->
         (match (th_op,vs) with
            (AllocThunk m,[v]) ->
              (if flat_bad_thunk_update m v (flat_state_refs s) then NONE else
               let (r,n) = store_alloc (Thunk m v) (flat_state_refs s) in
               SOME (flat_state_refs_fupd (K r) s,Rval (flat_Loc F n)))
          | (UpdateThunk m,[flat_Loc F lnum; v]) ->
              (if flat_bad_thunk_update m v (flat_state_refs s) then NONE else
               match store_assign lnum (Thunk m v) (flat_state_refs s) with
                 SOME r -> SOME (flat_state_refs_fupd (K r) s,
                                 Rval (flat_Conv NONE []))
               | NONE -> NONE)
          | _ -> NONE)
     | (Src _,_) -> NONE
     | (GlobalVarAlloc n,[]) ->
         SOME (flat_state_globals_fupd
                 (K (APPEND (flat_state_globals s) (REPLICATE n NONE))) s,
               Rval Unitv)
     | (GlobalVarInit n,[v]) ->
         if n < LENGTH (flat_state_globals s) /\
            IS_NONE (EL n (flat_state_globals s)) then
           SOME (flat_state_globals_fupd
                   (K (LUPDATE (SOME v) n (flat_state_globals s))) s,
                 Rval Unitv)
         else
           NONE
     | (GlobalVarLookup n,[]) ->
         if n < LENGTH (flat_state_globals s) /\
            IS_SOME (EL n (flat_state_globals s)) then
           SOME (s,Rval (THE (EL n (flat_state_globals s))))
         else
           NONE
     | (flat_TagLenEq n l,[flat_Conv (SOME (tag,_)) xs]) ->
         SOME (s,Rval (flat_Boolv (tag = n /\ LENGTH xs = l)))
     | (flat_LenEq l,[flat_Conv _ xs]) ->
         SOME (s,Rval (flat_Boolv (LENGTH xs = l)))
     | (flat_El n,[flat_Conv _ vs]) ->
         (if n < LENGTH vs then SOME (s,Rval (EL n vs)) else NONE)
     | (flat_El n,[flat_Loc _ p]) ->
         (if ~(n = 0) then NONE else
          match store_lookup p (flat_state_refs s) with
            SOME (Refv v) -> SOME (s,Rval v)
          | _ -> NONE)
     | (Id,[v1]) ->
         SOME (s,Rval v1)
     | _ -> NONE`;;

let flat_do_if_def = cake_def
  `flat_do_if v (e1:flat_exp) e2 =
     if v = flat_Boolv T then SOME e1
     else if v = flat_Boolv F then SOME e2
     else NONE`;;

let do_if_either_or = prove
 (`!v e1 e2 e. flat_do_if v e1 e2 = SOME e ==> e = e1 \/ e = e2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flat_do_if_def] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[option_INJ; option_DISTINCT] THEN
  MESON_TAC[]);;

(* the rules: exception constructors; constructors; tuples *)

let pmatch_stamps_ok_rules,pmatch_stamps_ok_ind,pmatch_stamps_ok_cases,
    pmatch_stamps_ok_strongind = cake_inductive
  `(!cn cn' n_ps n_vs.
      pmatch_stamps_ok (SOME (cn:ctor_id,NONE:type_group_id))
                       (SOME (cn':ctor_id,NONE:type_id)) n_ps n_vs) /\
   (!ty_id ty_id' cn n_ps ctor_set cn' n_vs.
      ty_id = ty_id' /\ MEM (cn,n_ps) ctor_set /\ MEM (cn',n_vs) ctor_set
      ==> pmatch_stamps_ok (SOME (cn,SOME (ty_id,ctor_set)))
                           (SOME (cn',SOME ty_id')) n_ps n_vs) /\
   (!n_ps n_vs. n_ps = n_vs ==> pmatch_stamps_ok NONE NONE n_ps n_vs)`;;

(* HOL4: pmatch_def (pmatch and pmatch_list) *)

let flat_pmatch_def = sem1aux_def_wf
  `inv_image (<)
     (\x:((C,FFI)flat_state # flat_pat # flat_v # (varN # flat_v) list) +
         ((C,FFI)flat_state # flat_pat list # flat_v list # (varN # flat_v) list).
        sum_CASE x (\t. flat_pat_size (FST (SND t)))
                   (\t. list_size flat_pat_size (FST (SND t))))`
  SEM1AUX_TC_TAC
  `(flat_pmatch (s:(C,FFI)flat_state) (flat_Pvar x) v' bindings =
      Match (CONS (x,v') bindings)) /\
   (flat_pmatch s flat_Pany v' bindings = Match bindings) /\
   (flat_pmatch s (flat_Plit l) (flat_Litv l') bindings =
      if l = l' then Match bindings
      else if lit_same_type l l' then No_match
      else Match_type_error) /\
   (flat_pmatch s (flat_Pcon stmp ps) (flat_Conv stmp' vs) bindings =
      if ~pmatch_stamps_ok stmp stmp' (LENGTH ps) (LENGTH vs) then
        Match_type_error
      else if OPTION_MAP FST stmp = OPTION_MAP FST stmp' /\
              LENGTH ps = LENGTH vs then
        flat_pmatch_list s ps vs bindings
      else No_match) /\
   (flat_pmatch s (flat_Pas p i) v bindings =
      flat_pmatch s p v (CONS (i,v) bindings)) /\
   (flat_pmatch s (flat_Pref p) (flat_Loc _ lnum) bindings =
      match store_lookup lnum (flat_state_refs s) with
        SOME (Refv v) -> flat_pmatch s p v bindings
      | _ -> Match_type_error) /\
   (flat_pmatch _ _ _ bindings = Match_type_error) /\
   (flat_pmatch_list s [] [] bindings = Match bindings) /\
   (flat_pmatch_list s (CONS p ps) (CONS v vs) bindings =
      match flat_pmatch s p v bindings with
        Match_type_error -> Match_type_error
      | Match bindings' -> flat_pmatch_list s ps vs bindings'
      | No_match ->
          (match flat_pmatch_list s ps vs bindings with
             Match_type_error -> Match_type_error
           | _ -> No_match)) /\
   (flat_pmatch_list s _ _ bindings = Match_type_error)`;;

let flat_pmatch_ind = cake_ind "flat_pmatch";;

(* the expressions of the rows are of any type, as in HOL4 *)

let pmatch_rows_def = cake_def
  `(pmatch_rows [] (s:(C,FFI)flat_state) v =
      (No_match:((varN # flat_v) list # flat_pat # A)match_result)) /\
   (pmatch_rows (CONS (p,(e:A)) pes) s v =
      match flat_pmatch s p v [] with
        Match_type_error -> Match_type_error
      | No_match -> pmatch_rows pes s v
      | Match env ->
          (match pmatch_rows pes s v with
             Match_type_error -> Match_type_error
           | _ -> Match (env,p,e)))`;;

let flat_dec_clock_def = cake_def
  `flat_dec_clock (s:(C,FFI)flat_state) =
     flat_state_clock_fupd (K (flat_state_clock s - 1)) s`;;

(* HOL4 infers the most general type: s and s1 are states of independent    *)
(* types                                                                     *)

let flat_fix_clock_def = cake_def
  `flat_fix_clock (s:(C,FFI)flat_state) ((s1:(D,E)flat_state),(res:R)) =
     (flat_state_clock_fupd (K (MIN (flat_state_clock s) (flat_state_clock s1)))
        s1,res)`;;

(* HOL4 [local] *)
let flat_fix_clock_IMP = prove
 (`!s x s1 res. flat_fix_clock (s:(C,FFI)flat_state) (x:(D,E)flat_state#R) =
                (s1,res)
                ==> flat_state_clock s1 <= flat_state_clock s`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `x:(D,E)flat_state#R` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s':(D,E)flat_state`
               (X_CHOOSE_THEN `r:R` SUBST1_TAC)) THEN
  REWRITE_TAC[flat_fix_clock_def; PAIR_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
  REWRITE_TAC[flat_state_INFO.ri_accfupds; K_THM] THEN ARITH_TAC);;

let flat_do_eval_def = cake_def
  `flat_do_eval (vs:flat_v list) (eval_config:(C)install_config) =
     match vs with
       [v1; v2] ->
         (match (flat_v_to_bytes v1,flat_v_to_words v2) with
            (SOME bytes,SOME data) ->
              let (st,decs) = install_config_compile_oracle eval_config 0 in
              let new_oracle =
                shift_seq 1 (install_config_compile_oracle eval_config) in
              (match install_config_compile eval_config st decs with
                 SOME (bytes',data',st') ->
                   if bytes = bytes' /\ data = data' /\ ~(decs = []) /\
                      FST (new_oracle 0) = st'
                   then SOME (decs,
                              install_config_compile_oracle_fupd (K new_oracle)
                                eval_config,
                              Unitv)
                   else NONE
               | _ -> NONE)
          | _ -> NONE)
     | _ -> NONE`;;

(* HOL4: AppUnit_def; HOL4's trace None is backend_common_None *)
let flat_AppUnit_def = cake_def
  `flat_AppUnit x =
     flat_App backend_common_None (Src Opapp)
       [x; flat_Con backend_common_None NONE []]`;;

(* primitive recursion over a nested datatype by direct instantiation of its *)
(* recursion theorem: the functions of the clauses are matched to those of   *)
(* the theorem by their domain types (new_recursive_definition matches the   *)
(* clauses by constructor, which is ambiguous for pairs of different types) *)

let FLATSEMAUX_prim_rec_define (rth:thm) (tm:term) =
  let cls = map (fun c -> snd(strip_forall c)) (conjuncts tm) in
  let gs = setify (map (fun c -> rator(lhs c)) cls) in
  let dom f = fst(dest_fun_ty(type_of f)) in
  let _,bod0 = strip_forall(concl rth) in
  let fns0,_ = strip_exists bod0 in
  let rthn = INST_TYPE (map (fun fn -> (snd(dest_fun_ty(type_of(
                 find (fun g -> dom g = dom fn) gs)))),
                                       snd(dest_fun_ty(type_of fn))) fns0) rth in
  let fvs,bod = strip_forall(concl rthn) in
  let fns,cls' = strip_exists bod in
  let my_of fn = find (fun g -> dom g = dom fn) gs in
  let inst_of cl' =
    let eq' = snd(strip_forall cl') in
    let l',r' = dest_eq eq' in
    let fn = rator l' and pat' = rand l' in
    let g = my_of fn in
    let cl = find (fun c -> rator(lhs c) = g &&
                            can (term_match [] pat') (rand(lhs c))) cls in
    let pat = rand(lhs cl) and rhs_ = rhs cl in
    let _,th_inst,_ = term_match [] pat' pat in
    let fj,rargs = strip_comb r' in
    let rvs = map (fun a ->
                if is_var a then (try rev_assoc a th_inst with Failure _ -> a)
                else genvar(type_of a)) rargs in
    (* the recursive calls (fn_x a) of rargs become (g_x (theta a)) in rhs_ *)
    let calls = filter (fun (a,_) -> not(is_var a)) (zip rargs rvs) in
    let sub = map (fun (a,v) ->
                let fx = rator a and x = rand a in
                let x' = try rev_assoc x th_inst with Failure _ -> x in
                v, mk_comb(my_of fx,x')) calls in
    let body = subst sub rhs_ in
    fj,list_mk_abs(rvs,body) in
  let insts = map inst_of (conjuncts cls') in
  let th1 = CONV_RULE (DEPTH_CONV BETA_CONV)
              (ISPECL (map (fun f -> assoc f insts) fvs) rthn) in
  let fnames = map (fun fn -> fst(dest_var(my_of fn))) fns in
  let sp = new_specification fnames th1 in
  let consts = map (fun g -> mk_const(fst(dest_var g),[]),g) gs in
  let tm' = subst (map (fun (c,g) -> inst (type_match (type_of c) (type_of g) []) c,g)
                       consts) tm in
  prove(tm',REWRITE_TAC[sp]);;

(* HOL4: exp_alt_size_def (HOL4 [simp]), the size of HOL4's exp_size with    *)
(* 100 more for each force of a thunk: the semantics of ForceThunk evaluates *)
(* AppUnit (Var_local None f), which is bigger than the forcing expression   *)
(* in exp_size.  exp1_alt_size .. exp6_alt_size are the sizes of the nested  *)
(* types (varN # varN # exp) list, varN # varN # exp, (pat # exp) list,      *)
(* varN # exp, pat # exp and exp list.                                       *)

let FLATSEMAUX_exp_alt_size_clauses =
  `(!a0 a1. flat_exp_alt_size (flat_Raise a0 a1) =
            1 + (tra_size a0 + flat_exp_alt_size a1)) /\
   (!a0 a1 a2. flat_exp_alt_size (flat_Handle a0 a1 a2) =
               1 + (tra_size a0 + (flat_exp_alt_size a1 + flat_exp3_alt_size a2))) /\
   (!a0 a1. flat_exp_alt_size (flat_Lit a0 a1) = 1 + (tra_size a0 + lit_size a1)) /\
   (!a0 a1 a2. flat_exp_alt_size (flat_Con a0 a1 a2) =
               1 +
               (tra_size a0 +
                (option_size (pair_size (\x. x) (option_size (\x. x))) a1 +
                 exp6_alt_size a2))) /\
   (!a0 a1. flat_exp_alt_size (Var_local a0 a1) =
            1 + (tra_size a0 + mlstring_size a1)) /\
   (!a0 a1 a2. flat_exp_alt_size (flat_Fun a0 a1 a2) =
               1 + (mlstring_size a0 + (mlstring_size a1 + flat_exp_alt_size a2))) /\
   (!a0 a1 a2. flat_exp_alt_size (flat_App a0 a1 a2) =
               (1 + (tra_size a0 + (flat_op_size a1 + exp6_alt_size a2))) +
               (if a1 = Src (ThunkOp ForceThunk) then 100 else 0)) /\
   (!a0 a1 a2 a3. flat_exp_alt_size (flat_If a0 a1 a2 a3) =
                  1 + (tra_size a0 + (flat_exp_alt_size a1 +
                                      (flat_exp_alt_size a2 + flat_exp_alt_size a3)))) /\
   (!a0 a1 a2. flat_exp_alt_size (flat_Mat a0 a1 a2) =
               1 + (tra_size a0 + (flat_exp_alt_size a1 + flat_exp3_alt_size a2))) /\
   (!a0 a1 a2 a3. flat_exp_alt_size (flat_Let a0 a1 a2 a3) =
                  1 +
                  (tra_size a0 +
                   (option_size mlstring_size a1 +
                    (flat_exp_alt_size a2 + flat_exp_alt_size a3)))) /\
   (!a0 a1 a2. flat_exp_alt_size (flat_Letrec a0 a1 a2) =
               1 + (mlstring_size a0 + (flat_exp1_alt_size a1 + flat_exp_alt_size a2))) /\
   (flat_exp1_alt_size [] = 0) /\
   (!a0 a1. flat_exp1_alt_size (CONS a0 a1) =
            1 + (flat_exp2_alt_size a0 + flat_exp1_alt_size a1)) /\
   (!a0 a1. flat_exp2_alt_size (a0,a1) = 1 + (mlstring_size a0 + exp4_alt_size a1)) /\
   (flat_exp3_alt_size [] = 0) /\
   (!a0 a1. flat_exp3_alt_size (CONS a0 a1) =
            1 + (exp5_alt_size a0 + flat_exp3_alt_size a1)) /\
   (!a0 a1. exp4_alt_size (a0,a1) = 1 + (mlstring_size a0 + flat_exp_alt_size a1)) /\
   (!a0 a1. exp5_alt_size (a0,a1) = 1 + (flat_pat_size a0 + flat_exp_alt_size a1)) /\
   (exp6_alt_size [] = 0) /\
   (!a0 a1. exp6_alt_size (CONS a0 a1) =
            1 + (flat_exp_alt_size a0 + exp6_alt_size a1))`;;

let flat_exp_alt_size_def =
  FLATSEMAUX_prim_rec_define flat_exp_RECURSION FLATSEMAUX_exp_alt_size_clauses;;
let _ = cake_add_simps [flat_exp_alt_size_def];;

let exp6_alt_size = prove
 (`!xs. exp6_alt_size xs = LENGTH xs + SUM (MAP flat_exp_alt_size xs)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[flat_exp_alt_size_def; LENGTH; MAP; SUM] THEN ARITH_TAC);;

(* HOL4 quantifies env (unused) and leaves env' and p free *)
let pmatch_rows_Match_exp_alt_size = prove
 (`!pes (s:(C,FFI)flat_state) v env' p e.
     pmatch_rows pes s v = Match (env',p,e) ==>
     flat_exp_alt_size e < flat_exp3_alt_size pes`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[pmatch_rows_def; distinctness "match_result"; FORALL_PAIR_THM] THEN
  REWRITE_TAC[flat_exp_alt_size_def] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  RW[case_eq "match_result"] THEN RES_TAC THEN ASM_ARITH_TAC);;

let dec_alt_size_def = cake_def
  `dec_alt_size a = 1 + flat_exp_alt_size a`;;
let _ = cake_add_simps [dec_alt_size_def];;

(* ------------------------------------------------------------------------- *)
(* The semantics (HOL4 evaluate_def before the clean-up below).              *)
(* ------------------------------------------------------------------------- *)

let FLATSEMAUX_evaluate_clauses1 =
  `(flat_evaluate (env:(flat_v)flat_environment) (s:(C,FFI)flat_state)
                  ([]:flat_exp list) = (s,Rval []:(flat_v list,flat_v)result)) /\
   (flat_evaluate env s (CONS e1 (CONS e2 es)) =
      match flat_fix_clock s (flat_evaluate env s [e1]) with
        (s',Rval v) ->
          (match flat_evaluate env s' (CONS e2 es) with
             (s'',Rval vs) -> (s'',Rval (CONS (HD v) vs))
           | res -> res)
      | res -> res) /\
   (flat_evaluate env s [flat_Lit _ l] = (s,Rval [flat_Litv l])) /\
   (flat_evaluate env s [flat_Raise _ e] =
      match flat_evaluate env s [e] with
        (s',Rval v) -> (s',Rerr (Rraise (HD v)))
      | res -> res) /\
   (flat_evaluate env s [flat_Handle _ e pes] =
      match flat_fix_clock s (flat_evaluate env s [e]) with
        (s',Rerr (Rraise v)) ->
          (match pmatch_rows pes s' v with
             Match_type_error -> (s',Rerr (Rabort Rtype_error))
           | No_match -> (s',Rerr (Rraise v))
           | Match (env',p',e') ->
               if ALL_DISTINCT (flat_pat_bindings p')
               then flat_evaluate (flat_environment_v_fupd
                                     (K (APPEND env' (flat_environment_v env))) env)
                                  s' [e']
               else (s',Rerr (Rabort Rtype_error)))
      | res -> res) /\
   (flat_evaluate env s [flat_Con _ NONE es] =
      match flat_evaluate env s (REVERSE es) with
        (s',Rval vs) -> (s',Rval [flat_Conv NONE (REVERSE vs)])
      | res -> res) /\
   (flat_evaluate env s [flat_Con _ (SOME cn) es] =
      match flat_evaluate env s (REVERSE es) with
        (s',Rval vs) -> (s',Rval [flat_Conv (SOME cn) (REVERSE vs)])
      | res -> res) /\
   (flat_evaluate env s [Var_local _ n] =
      (s,(match ALOOKUP (flat_environment_v env) n with
            SOME v -> Rval [v]
          | NONE -> Rerr (Rabort Rtype_error)))) /\
   (flat_evaluate env s [flat_Fun _ n e] = (s,Rval [flat_Closure env n e]))`;;

let FLATSEMAUX_evaluate_clauses2 =
  `(flat_evaluate (env:(flat_v)flat_environment) (s:(C,FFI)flat_state)
                  [flat_App _ op es] =
      match flat_fix_clock s (flat_evaluate env s (REVERSE es)) with
        (s',Rval vs) ->
          if op = Src Opapp then
            (match flat_do_opapp (REVERSE vs) with
               SOME (env',e) ->
                 if flat_state_clock s' = 0 then
                   (s',Rerr (Rabort Rtimeout_error))
                 else
                   flat_evaluate env' (flat_dec_clock s') [e]
             | NONE -> (s',Rerr (Rabort Rtype_error)))
          else if op = Src Eval then
            (match flat_do_eval (REVERSE vs) (flat_state_eval_config s') with
               SOME (decs,eval_config,retv) ->
                 if flat_state_clock
                      (flat_state_eval_config_fupd (K eval_config) s') = 0 then
                   (flat_state_eval_config_fupd (K eval_config) s',
                    Rerr (Rabort Rtimeout_error))
                 else
                   (match flat_evaluate_decs
                            (flat_dec_clock
                               (flat_state_eval_config_fupd (K eval_config) s'))
                            decs with
                      (s2,NONE) -> (s2,Rval [retv])
                    | (s2,SOME e) -> (s2,Rerr e))
             | NONE -> (s',Rerr (Rabort Rtype_error)))
          else if op = Src (ThunkOp ForceThunk) then
            (match flat_dest_thunk vs (flat_state_refs s') with
               flat_BadRef -> (s',Rerr (Rabort Rtype_error))
             | flat_NotThunk -> (s',Rerr (Rabort Rtype_error))
             | flat_IsThunk Evaluated v -> (s',Rval [v])
             | flat_IsThunk NotEvaluated f ->
                 (match flat_evaluate (flat_environment_REC [(implode "f",f)]) s'
                          [flat_AppUnit (Var_local backend_common_None (implode "f"))]
                  with
                    (s2,Rval vs2) ->
                      (match flat_update_thunk vs (flat_state_refs s2) vs2 with
                         NONE -> (s2,Rerr (Rabort Rtype_error))
                       | SOME refs -> (flat_state_refs_fupd (K refs) s2,Rval vs2))
                  | (s2,Rerr e) -> (s2,Rerr e)))
          else
            (match flat_do_app s' op (REVERSE vs) with
               NONE -> (s',Rerr (Rabort Rtype_error))
             | SOME (s'',r) -> (s'',list_result r))
      | res -> res) /\
   (flat_evaluate env s [flat_If _ e1 e2 e3] =
      match flat_fix_clock s (flat_evaluate env s [e1]) with
        (s',Rval vs) ->
          (match flat_do_if (HD vs) e2 e3 with
             SOME e -> flat_evaluate env s' [e]
           | NONE -> (s',Rerr (Rabort Rtype_error)))
      | res -> res) /\
   (flat_evaluate env s [flat_Mat _ e pes] =
      match flat_fix_clock s (flat_evaluate env s [e]) with
        (s',Rval v) ->
          (match pmatch_rows pes s' (HD v) with
             Match_type_error -> (s',Rerr (Rabort Rtype_error))
           | No_match -> (s',Rerr (Rraise flat_bind_exn_v))
           | Match (env',p',e') ->
               if ALL_DISTINCT (flat_pat_bindings p')
               then flat_evaluate (flat_environment_v_fupd
                                     (K (APPEND env' (flat_environment_v env))) env)
                                  s' [e']
               else (s',Rerr (Rabort Rtype_error)))
      | res -> res) /\
   (flat_evaluate env s [flat_Let _ n e1 e2] =
      match flat_fix_clock s (flat_evaluate env s [e1]) with
        (s',Rval vs) ->
          flat_evaluate (flat_environment_v_fupd (opt_bind n (HD vs)) env) s' [e2]
      | res -> res) /\
   (flat_evaluate env s [flat_Letrec _ funs e] =
      if ALL_DISTINCT (MAP FST funs)
      then flat_evaluate (flat_environment_v_fupd
                            (K (flat_build_rec_env funs env (flat_environment_v env)))
                            env) s [e]
      else (s,Rerr (Rabort Rtype_error)))`;;

let FLATSEMAUX_evaluate_clauses3 =
  `(evaluate_dec (s:(C,FFI)flat_state) (e:flat_exp) =
      match flat_evaluate (flat_environment_REC [] :(flat_v)flat_environment) s [e]
      with
        (s',Rval x) ->
          if x = [Unitv] then (s',NONE)
          else (s',SOME (Rabort Rtype_error))
      | (s',Rerr e') -> (s',SOME e')) /\
   (flat_evaluate_decs (s:(C,FFI)flat_state) [] =
      (s,NONE:((flat_v)error_result)option)) /\
   (flat_evaluate_decs s (CONS d ds) =
      match flat_fix_clock s (evaluate_dec s d) with
        (s',NONE) -> flat_evaluate_decs s' ds
      | (s',SOME e) -> (s',SOME e))`;;

(* The clauses in HOL4's order *)

let FLATSEMAUX_evaluate_clauses =
  list_mk_conj (conjuncts FLATSEMAUX_evaluate_clauses1 @
                conjuncts FLATSEMAUX_evaluate_clauses2 @
                conjuncts FLATSEMAUX_evaluate_clauses3);;

(* HOL4's termination relation:                                              *)
(*   inv_image ($< LEX $<) (\x. case x of                                   *)
(*     | INL (env,s,exps) =>                                                 *)
(*         (s.clock,SUM (MAP exp_alt_size exps) + LENGTH exps)               *)
(*     | INR (INL (s,d)) => (s.clock,dec_alt_size d + 1)                     *)
(*     | INR (INR (s,ds)) =>                                                 *)
(*         (s.clock,SUM (MAP dec_alt_size ds) + LENGTH ds + 1))              *)

let FLATSEMAUX_evaluate_rel =
  `inv_image ((<) LEX (<))
     (\x:((flat_v)flat_environment # (C,FFI)flat_state # flat_exp list) +
         (((C,FFI)flat_state # flat_exp) + ((C,FFI)flat_state # flat_exp list)).
        sum_CASE x
          (\t. flat_state_clock (FST (SND t)),
               SUM (MAP flat_exp_alt_size (SND (SND t))) + LENGTH (SND (SND t)))
          (\y. sum_CASE y
                 (\t. flat_state_clock (FST t),dec_alt_size (SND t) + 1)
                 (\t. flat_state_clock (FST t),
                      SUM (MAP dec_alt_size (SND t)) + LENGTH (SND t) + 1)))`;;

(* The termination tactic (HOL4: simp [dec_clock_def] \\ rw [] \\            *)
(* imp_res_tac fix_clock_IMP \\ imp_res_tac do_if_either_or \\               *)
(* imp_res_tac pmatch_rows_Match_exp_alt_size \\ fs [] \\ simp [MAP_REVERSE, *)
(* SUM_REVERSE, exp6_alt_size, AppUnit_def, char_size_def]).  It handles     *)
(* both kinds of termination conditions (R a' a, and !y. R y a' ==> R y a    *)
(* for a tail call).                                                         *)

let FLATSEMAUX_Opapp_not_Force = prove
 (`~(Src Opapp = Src (ThunkOp ForceThunk))`,
  REWRITE_TAC[injectivity "flat_op"; distinctness "op"]);;

let FLATSEMAUX_TC_TAC : tactic =
  REWRITE_TAC[IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RVEQ_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP flat_fix_clock_IMP)) THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o
                       MATCH_MP do_if_either_or)) THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP pmatch_rows_Match_exp_alt_size)) THEN
  REPEAT GEN_TAC THEN
  (fun g -> let ths = [inv_image_THM; LEX_DEF; sum_CASE; FST; SND;
                       flat_dec_clock_def; flat_state_INFO.ri_accfupds; K_THM;
                       GSYM MAP_REVERSE; SUM_REVERSE; LENGTH_REVERSE;
                       exp6_alt_size; flat_AppUnit_def; flat_exp_alt_size_def;
                       dec_alt_size_def; MAP; SUM; LENGTH;
                       FLATSEMAUX_Opapp_not_Force] @
                      !the_size_defs @ flat (map snd (!the_size_aux_eqs)) in
            (RULE_ASSUM_TAC(REWRITE_RULE ths) THEN REWRITE_TAC ths) g) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (EVALAUX_is_num_fact o concl))) THEN
  ARITH_TAC;;

(* HOL4 evaluate_def (the first one, with fix_clock); sem1aux_def_wf (the    *)
(* kit's casewise package would need hours for the clauses)                  *)

let FLATSEMAUX_evaluate_fix_def =
  sem1aux_def_wf FLATSEMAUX_evaluate_rel FLATSEMAUX_TC_TAC
    FLATSEMAUX_evaluate_clauses;;

(* HOL4's first evaluate_ind (with fix_clock) *)
let FLATSEMAUX_evaluate_fix_ind = cake_ind "flat_evaluate";;

(* HOL4: case_eq_thms (TypeBase.case_eq_of op, list, option, v, store_v,     *)
(* lit, eq_result, word_size, result, ffi_result, error_result)              *)

let flat_case_eq_thms = end_itlist CONJ
  [case_eq "flat_op"; list_case_eq; option_case_eq; case_eq "flat_v";
   case_eq "store_v"; case_eq "lit"; case_eq "eq_result"; case_eq "word_size";
   case_eq "result"; case_eq "ffi_result"; case_eq "error_result"];;

(* ------------------------------------------------------------------------- *)
(* Splitting an assumption  t = v  along the case tree of t (HOL4's          *)
(* gvs [AllCaseEqs()] on a definition like do_app_def, one case constant,    *)
(* conditional or let at a time, keeping the case equations as assumptions). *)
(* ------------------------------------------------------------------------- *)

let FLATSEMAUX_split_rewrites =
  [option_DISTINCT; option_INJ; PAIR_EQ; distinctness "result";
   injectivity "result"];;

let FLATSEMAUX_SPLIT_ONE_TAC : tactic =
  FIRST_X_ASSUM (fun th ->
    let l,_ = dest_eq (concl th) in
    if is_case_app l then
      let c,_,_ = dest_case_app l in
      let ci = case_info_of_const c in
      STRIP_ASSUME_TAC
        (REWRITE_RULE (ci.ci_case_eq :: FLATSEMAUX_split_rewrites) th)
    else if is_cond l then
      STRIP_ASSUME_TAC (REWRITE_RULE (COND_CASE_EQ :: FLATSEMAUX_split_rewrites) th)
    else if is_let l then
      ASSUME_TAC (CONV_RULE (LAND_CONV let_CONV) th)
    else failwith "FLATSEMAUX_SPLIT_ONE_TAC");;

let FLATSEMAUX_SPLIT_TAC : tactic = REPEAT FLATSEMAUX_SPLIT_ONE_TAC;;

let flat_do_app_const = prove
 (`!(s:(C,FFI)flat_state) op vs s' r.
     flat_do_app s op vs = SOME (s',r) ==> flat_state_clock s = flat_state_clock s'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[flat_do_app_def] THEN DISCH_TAC THEN
  FLATSEMAUX_SPLIT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_var o rhs o concl))) THEN
  REWRITE_TAC[flat_state_INFO.ri_accfupds]);;

(* HOL4: ho_match_mp_tac evaluate_ind >> rw[evaluate_def] >> every_case_tac *)
(* >> fs[dec_clock_def] >> rw[] >> rfs[] >> imp_res_tac fix_clock_IMP >>    *)
(* imp_res_tac do_app_const >> fs[]                                          *)

let FLATSEMAUX_clock_case_eqs =
  [pair_case_eq; option_case_eq; list_case_eq; COND_CASE_EQ] @
  map case_eq ["result"; "error_result"; "flat_dest_thunk_ret"; "thunk_mode";
               "match_result"];;

let FLATSEMAUX_CLOCK_TAC (def:thm) : tactic =
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[def] THEN
  DISCH_TAC THEN GVS(FLATSEMAUX_clock_case_eqs @ [flat_dec_clock_def]) THEN
  ASSUM_LIST (fun ths -> MAP_EVERY ASSUME_TAC
                           (mapfilter (MATCH_MP flat_fix_clock_IMP) ths)) THEN
  ASSUM_LIST (fun ths -> MAP_EVERY ASSUME_TAC
                           (mapfilter (MATCH_MP flat_do_app_const) ths)) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (EVALAUX_is_num_fact o concl))) THEN
  REWRITE_TAC[flat_state_INFO.ri_accfupds; K_THM] THEN ARITH_TAC;;

let flat_evaluate_clock = prove
 (`(!env (s:(C,FFI)flat_state) e r s2.
      flat_evaluate env s e = (s2,r) ==> flat_state_clock s2 <= flat_state_clock s) /\
   (!(s:(C,FFI)flat_state) e r s2.
      evaluate_dec s e = (s2,r) ==> flat_state_clock s2 <= flat_state_clock s) /\
   (!(s:(C,FFI)flat_state) e r s2.
      flat_evaluate_decs s e = (s2,r) ==> flat_state_clock s2 <= flat_state_clock s)`,
  MATCH_MP_TAC FLATSEMAUX_evaluate_fix_ind THEN REPEAT CONJ_TAC THEN
  FLATSEMAUX_CLOCK_TAC FLATSEMAUX_evaluate_fix_def);;

let FLATSEMAUX_fix_clock_id = prove
 (`!(s:(C,FFI)flat_state) (x:(D,E)flat_state#R).
     flat_state_clock (FST x) <= flat_state_clock s ==> flat_fix_clock s x = x`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `x:(D,E)flat_state#R` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s':(D,E)flat_state` (X_CHOOSE_THEN `r:R` SUBST1_TAC)) THEN
  REWRITE_TAC[flat_fix_clock_def; FST; PAIR_EQ] THEN DISCH_TAC THEN
  REWRITE_TAC[flat_state_component_equality; flat_state_INFO.ri_accfupds; K_THM] THEN
  REWRITE_TAC[MIN] THEN ASM_ARITH_TAC);;

let flat_fix_clock_evaluate = prove
 (`!(s:(C,FFI)flat_state) env e d ds.
     flat_fix_clock s (flat_evaluate env s e) = flat_evaluate env s e /\
     flat_fix_clock s (evaluate_dec s d) = evaluate_dec s d /\
     flat_fix_clock s (flat_evaluate_decs s ds) = flat_evaluate_decs s ds`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC FLATSEMAUX_fix_clock_id THEN
  MESON_TAC[flat_evaluate_clock; PAIR]);;

(* HOL4 rebinds evaluate_def and evaluate_ind to the versions without       *)
(* fix_clock                                                                 *)

let flat_evaluate_def =
  REWRITE_RULE[flat_fix_clock_evaluate] FLATSEMAUX_evaluate_fix_def;;

let flat_evaluate_ind =
  REWRITE_RULE[flat_fix_clock_evaluate] FLATSEMAUX_evaluate_fix_ind;;

(* cake_ind returns HOL4's final induction theorem *)
let () =
  cake_ind_store := ["flat_evaluate",flat_evaluate_ind;
                     "evaluate_dec",flat_evaluate_ind;
                     "flat_evaluate_decs",flat_evaluate_ind] @ !cake_ind_store;;

let flat_initial_state_def = cake_def
  `flat_initial_state (ffi:(FFI)ffi_state) k (ec:(C)install_config) =
     flat_state_REC k [] ffi [] ec`;;

let flat_semantics_def = cake_def
  `flat_semantics (ec:(C)install_config) (ffi:(FFI)ffi_state) prog =
     if ?k. SND (flat_evaluate_decs (flat_initial_state ffi k ec) prog) =
            SOME (Rabort Rtype_error)
     then Fail
     else
       match some res.
               ?k s r outcome.
                 flat_evaluate_decs (flat_initial_state ffi k ec) prog = (s,r) /\
                 (match r with
                    SOME (Rabort (Rffi_error e)) -> outcome = FFI_outcome e
                  | SOME (Rabort _) -> F
                  | _ -> outcome = Success) /\
                 res = Terminate outcome (ffi_state_io_events (flat_state_ffi s))
       with
         SOME res -> res
       | NONE ->
           Diverge
             (build_lprefix_lub
                (IMAGE (\k. llist_fromList
                              (ffi_state_io_events
                                 (flat_state_ffi
                                    (FST (flat_evaluate_decs
                                            (flat_initial_state ffi k ec) prog)))))
                       (:num)))`;;
