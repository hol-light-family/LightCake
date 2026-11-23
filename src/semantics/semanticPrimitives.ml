(* ========================================================================= *)
(* semanticPrimitives: port of HOL4 semantics/semanticPrimitivesScript.sml   *)
(* (CakeML v3479).  Definitions of semantic primitives (e.g., values, and    *)
(* functions for doing primitive operations) used in the semantics.          *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4's type variables 'a 'b 'v 'ffi are A B V FFI; word8 is byte and    *)
(*   word64 is int64; n2w is word, w2n is val, i2w is iword; Num is          *)
(*   num_of_int (on non-negative arguments only); FOLDR f e l is ITLIST f l e.*)
(* - Type abbreviations with a type variable (store, store_ffi) are written  *)
(*   out where used: (A store_v) list and (V store_v) list # (FFI)ffi_state.*)
(* - Record fields: env.v is sem_env_v env, s.clock is state_clock s, ...;   *)
(*   r with f := x is rec_f_fupd (K x) r; a literal <| ... |> is rec_REC.    *)
(* - The mlstring literal of x is implode "x"; s1 ^ s2 is strcat s1 s2.      *)
(* - HOL4's paired lambdas (\(f,x,e). t) are (\fxe. match fxe with           *)
(*   (f,x,e) -> t).                                                           *)
(* - Definitions with many clauses (after HOL4's completion of overlapping   *)
(*   clauses) are made with sem1aux_def / sem1aux_def_wf                      *)
(*   (semantics/sem1aux_tfl.ml): the same clauses and induction theorems as  *)
(*   cake_def, without the cost of the casewise recursion package.           *)
(* - HOL4's infix +++ (an overload of extend_dec_env) is not defined.        *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "hol4/machine_ieee.ml";;
needs "semantics/namespace.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;
needs "basis/pure/mlstring.ml";;

type_invention_error := true;;

(* Constructors and exceptions need unique identities, which we represent  *)
(* by stamps.  Each type gets a unique number, and the constructor name     *)
(* must be unique inside of the type.                                       *)

let stamp_INDUCT,stamp_RECURSION = cake_type
  "stamp = TypeStamp conN num | ExnStamp num";;

(* c: lexical mapping of constructor idents to arity, stamp pairs *)

let sem_env_INFO = cake_record "sem_env"
  ["v","(modN,varN,V)namespace";
   "c","(modN,conN,num#stamp)namespace"];;

let sem_env_component_equality = sem_env_INFO.ri_component_equality;;

(* Value forms.  Conv: constructor application (a tuple or a given         *)
(* constructor of a given type); Closure: function closures, the           *)
(* environment is used for the free variables in the function;             *)
(* Recclosure: closure for recursive functions, the last variable name     *)
(* indicates which function from the mutually recursive bundle this        *)
(* closure value represents; Loc b n: address n, = allowed if b; Env:       *)
(* environment value for Eval, and its numeric identifier.                 *)

let v_INDUCT,v_RECURSION = cake_type
  "v = Litv lit
     | Conv (stamp option) (v list)
     | Closure (v sem_env) varN exp
     | Recclosure (v sem_env) ((varN # varN # exp) list) varN
     | Loc bool num
     | Vectorv (v list)
     | Env (v sem_env) (num # num)";;

new_type_abbrev("env_ctor",`:(modN,conN,num#stamp)namespace`);;
new_type_abbrev("env_val",`:(modN,varN,v)namespace`);;

let bind_stamp_def = cake_def
  `bind_stamp = ExnStamp 0`;;
let chr_stamp_def = cake_def
  `chr_stamp = ExnStamp 1`;;
let div_stamp_def = cake_def
  `div_stamp = ExnStamp 2`;;
let subscript_stamp_def = cake_def
  `subscript_stamp = ExnStamp 3`;;

let bind_exn_v_def = cake_def
  `bind_exn_v = Conv (SOME bind_stamp) []`;;
let chr_exn_v_def = cake_def
  `chr_exn_v = Conv (SOME chr_stamp) []`;;
let div_exn_v_def = cake_def
  `div_exn_v = Conv (SOME div_stamp) []`;;
let sub_exn_v_def = cake_def
  `sub_exn_v = Conv (SOME subscript_stamp) []`;;

let bool_type_num_def = cake_def
  `bool_type_num = 0`;;
let list_type_num_def = cake_def
  `list_type_num = 1`;;
let option_type_num_def = cake_def
  `option_type_num = 2`;;
let lit_type_num_def = cake_def
  `lit_type_num = 3`;;
let id_type_num_def = cake_def
  `id_type_num = 4`;;
let ast_t_type_num_def = cake_def
  `ast_t_type_num = 5`;;
let pat_type_num_def = cake_def
  `pat_type_num = 6`;;
let lop_type_num_def = cake_def
  `lop_type_num = 7`;;
let opn_type_num_def = cake_def
  `opn_type_num = 8`;;
let opb_type_num_def = cake_def
  `opb_type_num = 9`;;
let opw_type_num_def = cake_def
  `opw_type_num = 10`;;
let shift_type_num_def = cake_def
  `shift_type_num = 11`;;
let word_size_type_num_def = cake_def
  `word_size_type_num = 12`;;
let fp_uop_type_num_def = cake_def
  `fp_uop_type_num = 13`;;
let fp_bop_type_num_def = cake_def
  `fp_bop_type_num = 14`;;
let fp_top_type_num_def = cake_def
  `fp_top_type_num = 15`;;
let fp_cmp_type_num_def = cake_def
  `fp_cmp_type_num = 16`;;

let op_type_num_def = cake_def
  `op_type_num = 20`;;
let locn_type_num_def = cake_def
  `locn_type_num = 21`;;
let locs_type_num_def = cake_def
  `locs_type_num = 22`;;
let exp_type_num_def = cake_def
  `exp_type_num = 24`;;
let dec_type_num_def = cake_def
  `dec_type_num = 25`;;

(* The result of evaluation; Rraise A should only be a value of type exn *)

let abort_INDUCT,abort_RECURSION = cake_type
  "abort = Rtype_error | Rtimeout_error | Rffi_error final_event";;

let error_result_INDUCT,error_result_RECURSION = cake_type
  "error_result = Rraise A | Rabort abort";;

let result_INDUCT,result_RECURSION = cake_type
  "result = Rval A | Rerr ((B)error_result)";;

(* Stores: a ref cell, a byte array, an array of values, a thunk *)

let store_v_INDUCT,store_v_RECURSION = cake_type
  "store_v = Refv A | W8array (byte list) | Varray (A list) | Thunk thunk_mode A";;

let store_v_same_type_def = cake_def
  `store_v_same_type (v1:A store_v) (v2:A store_v) <=>
     match (v1,v2) with
       (Refv _,Refv _) -> T
     | (W8array _,W8array _) -> T
     | (Varray _,Varray _) -> T
     | (Thunk NotEvaluated _,Thunk _ _) -> T
     | _ -> F`;;

(* The nth item in the list is the value at location n.                    *)
(* HOL4: Type store = :('a store_v) list  (written out where used)          *)

let empty_store_def = cake_def
  `empty_store = []:(A store_v) list`;;

let store_lookup_def = cake_def
  `store_lookup l (st:(A store_v) list) =
     if l < LENGTH st then SOME (EL l st) else NONE`;;

let store_alloc_def = cake_def
  `store_alloc (v:A store_v) st = (APPEND st [v],LENGTH st)`;;

let store_assign_def = cake_def
  `store_assign n (v:A store_v) st =
     if n < LENGTH st /\ store_v_same_type (EL n st) v then
       SOME (LUPDATE v n st)
     else NONE`;;

(* Compiler checker for Eval.  The current design requires the compiler to  *)
(* be run (as regular code within the semantics) before Eval is called, and *)
(* these config parameters specify how to interpret the declarations to be  *)
(* evaluated and check that the compiler was run correctly.  (Before        *)
(* attempting to build a state of this type, find out about                 *)
(* mk_init_eval_state in source_evalProof.)                                 *)

new_type_abbrev("compiler_args",`:(num#num)#v#dec list`);;
new_type_abbrev("compiler_fun",`:compiler_args->(v#byte list#int64 list)option`);;

(* compiler_state: state must be encoded as v somehow; decode_decs: decs    *)
(* must also be encoded as v                                                 *)

let eval_decs_state_INFO = cake_record "eval_decs_state"
  ["compiler","compiler_fun";
   "compiler_state","v";
   "env_id_counter","num#num#num";
   "decode_decs","v->(dec list)option"];;

let eval_decs_state_component_equality =
  eval_decs_state_INFO.ri_component_equality;;

(* Alternative mode for Eval including an oracle.  This is only for use in  *)
(* the compiler proof.                                                       *)

new_type_abbrev("eval_oracle_fun",`:num->compiler_args`);;

let eval_oracle_state_INFO = cake_record "eval_oracle_state"
  ["oracle","eval_oracle_fun";
   "custom_do_eval",
     "v list->eval_oracle_fun->((num#num)#eval_oracle_fun#dec list)option";
   "envs","((v sem_env) list) list";
   "generation","num"];;

let eval_oracle_state_component_equality =
  eval_oracle_state_INFO.ri_component_equality;;

let eval_state_INDUCT,eval_state_RECURSION = cake_type
  "eval_state = EvalDecs eval_decs_state | EvalOracle eval_oracle_state";;

let state_INFO = cake_record "state"
  ["clock","num";
   "refs","(v store_v) list";
   "ffi","(FFI)ffi_state";
   "next_type_stamp","num";
   "next_exn_stamp","num";
   "eval_state","(eval_state)option"];;

let state_component_equality = state_INFO.ri_component_equality;;

(* Other primitives *)
(* Check that a constructor is properly applied *)

let do_con_check_def = cake_def
  `do_con_check (cenv:(mlstring,mlstring,num#stamp)namespace) n_opt l <=>
     match n_opt with
       NONE -> T
     | SOME n -> (match nsLookup cenv n with
                    NONE -> F
                  | SOME (l',v2) -> l = l')`;;

let one_con_check_def = sem1aux_def
  `(one_con_check envc (Con cn es) <=> do_con_check envc cn (LENGTH es)) /\
   (one_con_check envc _ <=> T)`;;
let _ = cake_add_simps [one_con_check_def];;

let build_conv_def = cake_def
  `build_conv (envC:(mlstring,mlstring,num#stamp)namespace) cn vs =
     match cn with
       NONE -> SOME (Conv NONE vs)
     | SOME id -> (match nsLookup envC id with
                     NONE -> NONE
                   | SOME (len,stamp) -> SOME (Conv (SOME stamp) vs))`;;

let lit_same_type_def = cake_def
  `lit_same_type l1 l2 <=>
     match (l1,l2) with
       (IntLit _,IntLit _) -> T
     | (Char _,Char _) -> T
     | (StrLit _,StrLit _) -> T
     | (Word8 _,Word8 _) -> T
     | (Word64 _,Word64 _) -> T
     | (Float64 _,Float64 _) -> T
     | _ -> F`;;

let match_result_INDUCT,match_result_RECURSION = cake_type
  "match_result = No_match | Match_type_error | Match A";;

let same_type_def = cake_def
  `(same_type (TypeStamp v0 n1) (TypeStamp v1 n2) <=> n1 = n2) /\
   (same_type (ExnStamp v2) (ExnStamp v3) <=> T) /\
   (same_type _ _ <=> F)`;;

let same_ctor_def = cake_def
  `same_ctor stamp1 stamp2 <=> stamp1 = (stamp2:stamp)`;;

let ctor_same_type_def = cake_def
  `ctor_same_type c1 c2 <=>
     match (c1,c2) with
       (NONE,NONE) -> T
     | (SOME stamp1,SOME stamp2) -> same_type stamp1 stamp2
     | _ -> F`;;

(* HOL4: Boolv_def *)
let semanticPrimitives_Boolv_def = cake_def
  `Boolv b =
     if b then Conv (SOME (TypeStamp (implode "True") bool_type_num)) []
     else Conv (SOME (TypeStamp (implode "False") bool_type_num)) []`;;

(* A big-step pattern matcher.  If the value matches the pattern, return an *)
(* environment with the pattern variables bound to the corresponding sub-   *)
(* terms of the value; this environment extends the environment given as an *)
(* argument.  No_match is returned when there is no match, but any          *)
(* constructors encountered in determining the match failure are applied to *)
(* the correct number of arguments, and constructors in corresponding       *)
(* positions in the pattern and value come from the same type.             *)
(* Match_type_error is returned when one of these conditions is violated.  *)

let pmatch_def = sem1aux_def_wf
  `inv_image (<)
     (\x:(env_ctor # (v store_v) list # pat # v # (varN # v) list) +
         (env_ctor # (v store_v) list # pat list # v list # (varN # v) list).
        sum_CASE x (\t. pat_size (FST (SND (SND t))))
                   (\t. list_size pat_size (FST (SND (SND t)))))`
  SEM1AUX_TC_TAC
  `(pmatch envC s Pany v' env = Match env) /\
   (pmatch envC s (Pvar x) v' env = Match (CONS (x,v') env)) /\
   (pmatch envC s (Plit l) (Litv l') env =
      if l = l' then Match env
      else if lit_same_type l l' then No_match
      else Match_type_error) /\
   (pmatch envC s (Pcon (SOME n) ps) (Conv (SOME stamp') vs) env =
      match nsLookup envC n with
        NONE -> Match_type_error
      | SOME (l,stamp) ->
          if same_type stamp stamp' /\ LENGTH ps = l then
            if same_ctor stamp stamp' then
              if LENGTH vs = l then pmatch_list envC s ps vs env
              else Match_type_error
            else No_match
          else Match_type_error) /\
   (pmatch envC s (Pcon NONE ps) (Conv NONE vs) env =
      if LENGTH ps = LENGTH vs then pmatch_list envC s ps vs env
      else Match_type_error) /\
   (pmatch envC s (Pref p) (Loc _ lnum) env =
      match store_lookup lnum s with
        NONE -> Match_type_error
      | SOME (Refv v) -> pmatch envC s p v env
      | SOME _ -> Match_type_error) /\
   (pmatch envC s (Pas p i) v env = pmatch envC s p v (CONS (i,v) env)) /\
   (pmatch envC s (Ptannot p t) v env = pmatch envC s p v env) /\
   (pmatch envC s _ _ env = Match_type_error) /\
   (pmatch_list envC s [] [] env = Match env) /\
   (pmatch_list envC s (CONS p ps) (CONS v vs) env =
      match pmatch envC s p v env with
        No_match ->
          (match pmatch_list envC s ps vs env with
             No_match -> No_match
           | Match_type_error -> Match_type_error
           | Match v1 -> No_match)
      | Match_type_error -> Match_type_error
      | Match env' -> pmatch_list envC s ps vs env') /\
   (pmatch_list envC s _ _ env = Match_type_error)`;;

let pmatch_ind = cake_ind "pmatch";;

let can_pmatch_all_def = cake_def
  `(can_pmatch_all envC refs [] v <=> T) /\
   (can_pmatch_all envC refs (CONS p ps) v <=>
      if pmatch envC refs p v [] = Match_type_error then F
      else can_pmatch_all envC refs ps v)`;;

let can_pmatch_all_ind = cake_ind "can_pmatch_all";;

(* Bind each function of a mutually recursive set of functions to its      *)
(* closure                                                                   *)

let build_rec_env_def = cake_def
  `build_rec_env (funs:(varN#varN#exp)list) (cl_env:v sem_env)
                 (add_to_env:(mlstring,mlstring,v)namespace) =
     ITLIST (\fxe env'. match fxe with
                          (f,x,e) -> nsBind f (Recclosure cl_env funs f) env')
            funs add_to_env`;;

(* Lookup in the list of mutually recursive functions *)

let find_recfun_def = cake_def
  `find_recfun (n:mlstring) (funs:(mlstring#A#B)list) =
     match funs with
       [] -> NONE
     | CONS (f,x,e) funs' -> if f = n then SOME (x,e) else find_recfun n funs'`;;

let find_recfun_ind = cake_ind "find_recfun";;

let eq_result_INDUCT,eq_result_RECURSION = cake_type
  "eq_result = Eq_val bool | Eq_type_error";;

(* HOL4's Loc b1 l1 / Loc b2 l2 are Loc b1 n1 / Loc b2 n2 (l1 and l2 are    *)
(* the literals of the first clause)                                         *)

let do_eq_def = sem1aux_def_wf
  `inv_image (<)
     (\x:(v # v) + (v list # v list).
        sum_CASE x (\t. v_size (FST t)) (\t. list_size v_size (FST t)))`
  SEM1AUX_TC_TAC
  `(do_eq (Litv l1) (Litv l2) =
      if lit_same_type l1 l2 then Eq_val (l1 = l2) else Eq_type_error) /\
   (do_eq (Loc b1 n1) (Loc b2 n2) =
      if b1 /\ b2 then Eq_val (n1 = n2) else Eq_type_error) /\
   (do_eq (Conv cn1 vs1) (Conv cn2 vs2) =
      if cn1 = cn2 /\ LENGTH vs1 = LENGTH vs2 then do_eq_list vs1 vs2
      else if ctor_same_type cn1 cn2 then Eq_val F
      else Eq_type_error) /\
   (do_eq (Vectorv vs1) (Vectorv vs2) =
      if LENGTH vs1 = LENGTH vs2 then do_eq_list vs1 vs2 else Eq_val F) /\
   (do_eq (Closure v0 v3 v4) (Closure v5 v6 v7) = Eq_val T) /\
   (do_eq (Closure v8 v9 v10) (Recclosure v11 v12 v13) = Eq_val T) /\
   (do_eq (Recclosure v14 v15 v16) (Closure v17 v18 v19) = Eq_val T) /\
   (do_eq (Recclosure v20 v21 v22) (Recclosure v23 v24 v25) = Eq_val T) /\
   (do_eq (Env v26 (gen1,id1)) (Env v27 (gen2,id2)) =
      Eq_val (gen1 = gen2 /\ id1 = id2)) /\
   (do_eq _ _ = Eq_type_error) /\
   (do_eq_list [] [] = Eq_val T) /\
   (do_eq_list (CONS v1 vs1) (CONS v2 vs2) =
      match do_eq v1 v2 with
        Eq_val r -> if ~r then Eq_val F else do_eq_list vs1 vs2
      | Eq_type_error -> Eq_type_error) /\
   (do_eq_list _ _ = Eq_val F)`;;

let do_eq_ind = cake_ind "do_eq";;

(* Do an application *)

let do_opapp_def = cake_def
  `do_opapp vs =
     match vs with
       [Closure env n e; v] ->
         SOME (sem_env_v_fupd (K (nsBind n v (sem_env_v env))) env,e)
     | [Recclosure env' funs n'; v] ->
         if ALL_DISTINCT (MAP (\fxe. match fxe with (f,x,e) -> f) funs) then
           (match find_recfun n' funs with
              NONE -> NONE
            | SOME (n,e) ->
                SOME (sem_env_v_fupd
                        (K (nsBind n v (build_rec_env funs env' (sem_env_v env'))))
                        env',e))
         else NONE
     | _ -> NONE`;;

(* If a value represents a list, get that list.  Otherwise return Nothing *)

let v_to_list_def = sem1aux_def
  `(v_to_list (Conv (SOME stamp) []) =
      if stamp = TypeStamp (implode "[]") list_type_num then SOME [] else NONE) /\
   (v_to_list (Conv (SOME stamp) [v1; v2]) =
      if stamp = TypeStamp (implode "::") list_type_num then
        (match v_to_list v2 with NONE -> NONE | SOME vs -> SOME (CONS v1 vs))
      else NONE) /\
   (v_to_list _ = NONE)`;;

let v_to_list_ind = cake_ind "v_to_list";;

let list_to_v_def = cake_def
  `(list_to_v [] = Conv (SOME (TypeStamp (implode "[]") list_type_num)) []) /\
   (list_to_v (CONS x xs) =
      Conv (SOME (TypeStamp (implode "::") list_type_num)) [x; list_to_v xs])`;;

let list_to_v_ind = cake_ind "list_to_v";;

let v_to_char_list_def = sem1aux_def
  `(v_to_char_list (Conv (SOME stamp) []) =
      if stamp = TypeStamp (implode "[]") list_type_num then SOME "" else NONE) /\
   (v_to_char_list (Conv (SOME stamp) [Litv (Char c); v]) =
      if stamp = TypeStamp (implode "::") list_type_num then
        (match v_to_char_list v with NONE -> NONE | SOME cs -> SOME (CONS c cs))
      else NONE) /\
   (v_to_char_list _ = NONE)`;;

let v_to_char_list_ind = cake_ind "v_to_char_list";;

let vs_to_string_def = sem1aux_def
  `(vs_to_string [] = SOME (implode "")) /\
   (vs_to_string (CONS (Litv (StrLit s1)) vs) =
      match vs_to_string vs with NONE -> NONE | SOME s2 -> SOME (strcat s1 s2)) /\
   (vs_to_string (CONS _ v1) = NONE)`;;

let vs_to_string_ind = cake_ind "vs_to_string";;

let maybe_to_v_def = cake_def
  `(maybe_to_v NONE = Conv (SOME (TypeStamp (implode "None") option_type_num)) []) /\
   (maybe_to_v (SOME v) =
      Conv (SOME (TypeStamp (implode "Some") option_type_num)) [v])`;;

let v_to_id_def = sem1aux_def
  `(v_to_id (Conv (SOME stamp) [Litv (StrLit s)]) =
      if stamp = TypeStamp (implode "Short") id_type_num then SOME (Short s)
      else NONE) /\
   (v_to_id (Conv (SOME stamp) [Litv (StrLit s); v]) =
      if stamp = TypeStamp (implode "Long") id_type_num then
        (match v_to_id v with NONE -> NONE | SOME id -> SOME (Long s id))
      else NONE) /\
   (v_to_id _ = NONE)`;;

let v_to_id_ind = cake_ind "v_to_id";;

let nat_to_v_def = cake_def
  `nat_to_v n = Litv (IntLit (&n))`;;

let maybe_all_list_def = cake_def
  `maybe_all_list (v:(A option) list) =
     match v with
       [] -> SOME []
     | CONS NONE vs -> NONE
     | CONS (SOME x) vs ->
         (match maybe_all_list vs with NONE -> NONE | SOME xs -> SOME (CONS x xs))`;;

let maybe_all_list_ind = cake_ind "maybe_all_list";;

let v_to_word8_def = cake_def
  `v_to_word8 v =
     match v with
       Litv (Word8 w) -> SOME w
     | _ -> NONE`;;

let v_to_word8_list_def = cake_def
  `v_to_word8_list v =
     match v_to_list v with
       NONE -> NONE
     | SOME xs -> maybe_all_list (MAP v_to_word8 xs)`;;

let v_to_word64_def = cake_def
  `v_to_word64 v =
     match v with
       Litv (Word64 w) -> SOME w
     | _ -> NONE`;;

let v_to_word64_list_def = cake_def
  `v_to_word64_list v =
     match v_to_list v with
       NONE -> NONE
     | SOME xs -> maybe_all_list (MAP v_to_word64 xs)`;;

let lookup_env_def = cake_def
  `lookup_env s (i,j) =
     match oEL i (eval_oracle_state_envs s) with
       NONE -> NONE
     | SOME gen_envs -> oEL j gen_envs`;;

let add_decs_generation_def = cake_def
  `add_decs_generation s =
     match eval_decs_state_env_id_counter s with
       (cur_gen,next_id,next_gen) ->
         eval_decs_state_env_id_counter_fupd (K (next_gen,0,next_gen + 1)) s`;;

let add_env_generation_def = cake_def
  `add_env_generation s =
     eval_oracle_state_generation_fupd (K (LENGTH (eval_oracle_state_envs s)))
       (eval_oracle_state_envs_fupd (K (APPEND (eval_oracle_state_envs s) [[]]))
          s)`;;

let declare_env_def = cake_def
  `declare_env es (env:v sem_env) =
     match es with
       NONE -> NONE
     | SOME (EvalDecs s) ->
         (match eval_decs_state_env_id_counter s with
            (cur_gen,next_id,next_gen) ->
              SOME (Env env (cur_gen,next_id),
                    SOME (EvalDecs
                            (eval_decs_state_env_id_counter_fupd
                               (K (cur_gen,next_id + 1,next_gen)) s))))
     | SOME (EvalOracle s') ->
         (match oEL (eval_oracle_state_generation s') (eval_oracle_state_envs s') with
            NONE -> NONE
          | SOME gen_envs ->
              SOME (Conv NONE [nat_to_v (eval_oracle_state_generation s');
                               nat_to_v (LENGTH gen_envs)],
                    SOME (EvalOracle
                            (eval_oracle_state_envs_fupd
                               (K (LUPDATE (APPEND gen_envs [env])
                                     (eval_oracle_state_generation s')
                                     (eval_oracle_state_envs s'))) s'))))`;;

(* Concrete, or first-order values, which do not contain code closures and  *)
(* are unchanged by many compiler phases.                                    *)

let concrete_v_def = cake_def_wf
  `MEASURE (\x:v + v list. sum_CASE x (\v. v_size v) (\vs. list_size v_size vs))`
  SEM1AUX_TC_TAC
  `(concrete_v v <=>
      match v with
        Loc _ _ -> T
      | Litv _ -> T
      | Conv v_ vs -> concrete_v_list vs
      | Vectorv vs -> concrete_v_list vs
      | _ -> F) /\
   (concrete_v_list [] <=> T) /\
   (concrete_v_list (CONS v vs) <=> concrete_v v /\ concrete_v_list vs)`;;

let concrete_v_ind = cake_ind "concrete_v";;

let compiler_agrees_def = cake_def
  `compiler_agrees (f:(num#num)#v#dec list->(v#byte list#int64 list)option)
                   args (st_v,bs_v,ws_v) <=>
     match (f args,args,v_to_word8_list bs_v,v_to_word64_list ws_v) with
       (SOME (st,c_bs,c_ws),(v16,prev_st_v,_),SOME bs,SOME ws) ->
         st = st_v /\ c_bs = bs /\ c_ws = ws /\ concrete_v st_v /\
         concrete_v prev_st_v
     | _ -> F`;;

(* get the declarations to be evaluated in the various Eval semantics *)

let do_eval_def = cake_def
  `do_eval (vs:v list) es =
     match (es,vs) with
       (SOME (EvalDecs s),[Env env id; st_v; decs_v; st_v2; bs_v; ws_v]) ->
         (match eval_decs_state_decode_decs s decs_v with
            NONE -> NONE
          | SOME decs ->
              if st_v = eval_decs_state_compiler_state s /\ concrete_v decs_v /\
                 compiler_agrees (eval_decs_state_compiler s) (id,st_v,decs)
                   (st_v2,bs_v,ws_v)
              then
                SOME (env,decs,
                      SOME (EvalDecs
                              (add_decs_generation
                                 (eval_decs_state_compiler_state_fupd (K st_v2) s))))
              else NONE)
     | (SOME (EvalOracle s'),vs) ->
         (match eval_oracle_state_custom_do_eval s' vs (eval_oracle_state_oracle s') with
            NONE -> NONE
          | SOME (env_id,oracle,decs) ->
              (match lookup_env s' env_id with
                 NONE -> NONE
               | SOME env ->
                   SOME (env,decs,
                         SOME (EvalOracle
                                 (add_env_generation
                                    (eval_oracle_state_oracle_fupd (K oracle) s'))))))
     | _ -> NONE`;;

(* conclude an Eval generation *)

let reset_env_generation_def = cake_def
  `reset_env_generation prior_es es =
     match (prior_es,es) with
       (SOME (EvalDecs prior_s'),SOME (EvalDecs s')) ->
         (match (eval_decs_state_env_id_counter prior_s',
                 eval_decs_state_env_id_counter s') with
            ((cur_gen,next_id,v5),v6,v8,next_gen) ->
              SOME (EvalDecs
                      (eval_decs_state_env_id_counter_fupd
                         (K (cur_gen,next_id,next_gen)) s')))
     | (SOME (EvalOracle prior_s),SOME (EvalOracle s)) ->
         SOME (EvalOracle
                 (eval_oracle_state_generation_fupd
                    (K (eval_oracle_state_generation prior_s)) s))
     | _ -> es`;;

let copy_array_def = cake_def
  `copy_array (src:A list,srcoff) len d =
     if srcoff < &0 \/ len < &0 \/
        LENGTH src < num_of_int (abs (I (srcoff + len)))
     then NONE
     else
       let copied =
         TAKE (num_of_int (abs (I len))) (DROP (num_of_int (abs (I srcoff))) src) in
       match d with
         NONE -> SOME copied
       | SOME (dst,dstoff) ->
           if dstoff < &0 \/ LENGTH dst < num_of_int (abs (I (dstoff + len)))
           then NONE
           else
             SOME (APPEND (APPEND (TAKE (num_of_int (abs (I dstoff))) dst) copied)
                          (DROP (num_of_int (abs (I (dstoff + len)))) dst))`;;

let ws_to_chars_def = cake_def
  `ws_to_chars (ws:byte list) = MAP (\w. CHR (val w)) ws`;;

let chars_to_ws_def = cake_def
  `chars_to_ws cs = MAP (\c. iword (&(ORD c))) cs:byte list`;;

(* HOL4's opn_lookup, opb_lookup, opw8_lookup and opw64_lookup are in a     *)
(* comment of the script (not defined).                                     *)

let shift8_lookup_def = cake_def
  `shift8_lookup sh =
     match sh with
       Lsl -> word_shl
     | Lsr -> word_ushr
     | Asr -> word_ishr
     | Ror -> word_ror:byte->num->byte`;;

let shift64_lookup_def = cake_def
  `shift64_lookup sh =
     match sh with
       Lsl -> word_shl
     | Lsr -> word_ushr
     | Asr -> word_ishr
     | Ror -> word_ror:int64->num->int64`;;

let exp_or_val_INDUCT,exp_or_val_RECURSION = cake_type
  "exp_or_val = Exp exp | Val v";;

(* HOL4: Type store_ffi = :'v store # 'ffi ffi_state  (written out where     *)
(* used); HOL4's local overloads w64lit and f64lit are not needed.           *)

let xor_bytes_def = cake_def
  `(xor_bytes [] bs2 = SOME (bs2:byte list)) /\
   (xor_bytes bs1 [] = NONE) /\
   (xor_bytes (CONS b1 bs1) (CONS b2 bs2) =
      match xor_bytes bs1 bs2 with
        NONE -> NONE
      | SOME rest -> SOME (CONS (word_xor b1 b2) rest))`;;

let xor_bytes_ind = cake_ind "xor_bytes";;

(* With dest_thunk we check 3 things: the values contain exactly one        *)
(* reference, the reference is valid, the reference points to a thunk.  We  *)
(* distinguish between BadRef and NotThunk instead of returning an option   *)
(* with NONE for both, because we want update_thunk to succeed when         *)
(* dest_thunk fails but only when the reference actually exists and points  *)
(* to something other than a thunk.                                          *)

let dest_thunk_ret_INDUCT,dest_thunk_ret_RECURSION = cake_type
  "dest_thunk_ret = BadRef | NotThunk | IsThunk thunk_mode v";;

let dest_thunk_def = sem1aux_def
  `(dest_thunk [Loc b n] st =
      match store_lookup n st with
        NONE -> BadRef
      | SOME (Thunk Evaluated v) -> if b then BadRef else IsThunk Evaluated v
      | SOME (Thunk NotEvaluated v) -> if b then BadRef else IsThunk NotEvaluated v
      | SOME _ -> NotThunk) /\
   (dest_thunk vs st = NotThunk)`;;

(* HOL4's first clause has the pattern Loc F n, so that its completion has  *)
(* a clause for Loc T n; here Loc b n with if b then NONE (the kit does not *)
(* complete clauses with literal patterns)                                   *)

let update_thunk_def = sem1aux_def
  `(update_thunk [Loc b n] st [v] =
      if b then NONE else
      match dest_thunk [v] st with
        NotThunk -> store_assign n (Thunk Evaluated v) st
      | _ -> NONE) /\
   (update_thunk _ st _ = NONE)`;;

let bad_thunk_update_def = cake_def
  `bad_thunk_update m v st <=>
     m = Evaluated /\ ~(dest_thunk [v] st = NotThunk)`;;

let thunk_op_def = cake_def
  `thunk_op (s:(v store_v) list,t:(FFI)ffi_state) th_op vs =
     match (th_op,vs) with
       (AllocThunk m,[v]) ->
         if bad_thunk_update m v s then NONE else
         (match store_alloc (Thunk m v) s with
            (s',n) -> SOME ((s',t),(Rval (Loc F n):(v,B)result)))
     | (UpdateThunk m,[Loc F lnum; v]) ->
         if bad_thunk_update m v s then NONE else
         (match store_assign lnum (Thunk m v) s with
            SOME s' -> SOME ((s',t),Rval (Conv NONE []))
          | NONE -> NONE)
     | _ -> NONE`;;

let check_type_def = sem1aux_def
  `(check_type BoolT v <=> v = Boolv T \/ v = Boolv F) /\
   (check_type IntT v <=> ?i. v = Litv (IntLit i)) /\
   (check_type CharT v <=> ?c. v = Litv (Char c)) /\
   (check_type StrT v <=> ?s. v = Litv (StrLit s)) /\
   (check_type (WordT W8) v <=> ?w. v = Litv (Word8 w)) /\
   (check_type (WordT W64) v <=> ?w. v = Litv (Word64 w)) /\
   (check_type Float64T v <=> ?w. v = Litv (Float64 w))`;;

let dest_Litv_def = sem1aux_def
  `(dest_Litv (Litv v) = SOME v) /\
   (dest_Litv _ = NONE)`;;
let _ = cake_add_simps [dest_Litv_def];;

let the_Litv_IntLit_def = cake_def
  `the_Litv_IntLit (Litv (IntLit i)) = i`;;
let _ = cake_add_simps [the_Litv_IntLit_def];;

let the_Litv_Word8_def = cake_def
  `the_Litv_Word8 (Litv (Word8 w)) = w`;;
let _ = cake_add_simps [the_Litv_Word8_def];;

let the_Litv_Word64_def = cake_def
  `the_Litv_Word64 (Litv (Word64 w)) = w`;;
let _ = cake_add_simps [the_Litv_Word64_def];;

let the_Litv_Float64_def = cake_def
  `the_Litv_Float64 (Litv (Float64 w)) = w`;;
let _ = cake_add_simps [the_Litv_Float64_def];;

let the_Litv_Char_def = cake_def
  `the_Litv_Char (Litv (Char c)) = c`;;
let _ = cake_add_simps [the_Litv_Char_def];;

let the_Boolv_def = cake_def
  `the_Boolv v <=> v = Boolv T`;;
let _ = cake_add_simps [the_Boolv_def];;

let num_cmp_def = cake_def
  `(num_cmp Lt i j <=> i < j:num) /\
   (num_cmp Leq i j <=> i <= j) /\
   (num_cmp Gt i j <=> i > j) /\
   (num_cmp Geq i j <=> i >= j)`;;
let _ = cake_add_simps [num_cmp_def];;

let int_cmp_def = cake_def
  `(int_cmp Lt i j <=> i < j:int) /\
   (int_cmp Leq i j <=> i <= j) /\
   (int_cmp Gt i j <=> i > j) /\
   (int_cmp Geq i j <=> i >= j)`;;
let _ = cake_add_simps [int_cmp_def];;

let str_cmp_def = sem1aux_def
  `(str_cmp F Lt i j <=> mlstring_lt i j) /\
   (str_cmp F Leq i j <=> mlstring_le i j) /\
   (str_cmp F Gt i j <=> mlstring_gt i j) /\
   (str_cmp F Geq i j <=> mlstring_ge i j) /\
   (str_cmp T Lt i j <=> fast_lt i j) /\
   (str_cmp T Leq i j <=> fast_le i j) /\
   (str_cmp T Gt i j <=> fast_gt i j) /\
   (str_cmp T Geq i j <=> fast_ge i j)`;;
let _ = cake_add_simps [str_cmp_def];;

(* HOL4: TODO: extend with more cases *)

let do_test_def = sem1aux_def
  `(do_test Equal ty v1 v2 =
      if check_type ty v1 /\ check_type ty v2 then
        (if ty = Float64T
         then Eq_val (fp64_equal (the_Litv_Float64 v1) (the_Litv_Float64 v2))
         else do_eq v1 v2)
      else Eq_type_error) /\
   (do_test (Compare cmp) ty v1 v2 =
      match (ty,dest_Litv v1,dest_Litv v2) with
        (IntT,SOME (IntLit i),SOME (IntLit j)) -> Eq_val (int_cmp cmp i j)
      | (CharT,SOME (Char c),SOME (Char d)) -> Eq_val (num_cmp cmp (ORD c) (ORD d))
      | (WordT W8,SOME (Word8 w),SOME (Word8 v)) ->
          Eq_val (num_cmp cmp (val w) (val v))
      | (Float64T,SOME (Float64 w),SOME (Float64 v)) -> Eq_val (fp_cmp cmp w v)
      | (StrT,SOME (StrLit s),SOME (StrLit t)) -> Eq_val (str_cmp F cmp s t)
      | _ -> Eq_type_error) /\
   (do_test (AltCompare cmp) ty v1 v2 =
      match (ty,dest_Litv v1,dest_Litv v2) with
        (StrT,SOME (StrLit s),SOME (StrLit t)) -> Eq_val (str_cmp T cmp s t)
      | _ -> Eq_type_error)`;;

(* HOL4's $ (function application) is written out *)

let do_arith_def = sem1aux_def
  `(do_arith a Float64T vals =
      match (a,MAP the_Litv_Float64 vals) with
        (Abs,[v1]) -> SOME (INR (Litv (Float64 (fp64_abs v1))))
      | (Neg,[v1]) -> SOME (INR (Litv (Float64 (fp64_negate v1))))
      | (Sqrt,[v1]) -> SOME (INR (Litv (Float64 (fp64_sqrt roundTiesToEven v1))))
      | (Add,[v1; v2]) ->
          SOME (INR (Litv (Float64 (fp64_add roundTiesToEven v1 v2))))
      | (Sub,[v1; v2]) ->
          SOME (INR (Litv (Float64 (fp64_sub roundTiesToEven v1 v2))))
      | (Mul,[v1; v2]) ->
          SOME (INR (Litv (Float64 (fp64_mul roundTiesToEven v1 v2))))
      | (Div,[v1; v2]) ->
          SOME (INR (Litv (Float64 (fp64_div roundTiesToEven v1 v2))))
      | (FMA,[v1; v2; v3]) ->
          SOME (INR (Litv (Float64 (fp64_mul_add roundTiesToEven v2 v3 v1))))
      | _ -> NONE) /\
   (do_arith a IntT vals =
      match (a,MAP the_Litv_IntLit vals) with
        (Add,[v1; v2]) -> SOME (INR (Litv (IntLit (v1 + v2))))
      | (Sub,[v1; v2]) -> SOME (INR (Litv (IntLit (v1 - v2))))
      | (Mul,[v1; v2]) -> SOME (INR (Litv (IntLit (v1 * v2))))
      | (Div,[v1; v2]) ->
          SOME (if v2 = &0 then INL div_exn_v
                else INR (Litv (IntLit (int_div v1 v2))))
      | (Mod,[v1; v2]) ->
          SOME (if v2 = &0 then INL div_exn_v
                else INR (Litv (IntLit (integer_int_mod v1 v2))))
      | _ -> NONE) /\
   (do_arith a (WordT W8) vals =
      match (a,MAP the_Litv_Word8 vals) with
        (Add,[v1; v2]) -> SOME (INR (Litv (Word8 (word_add v1 v2))))
      | (Sub,[v1; v2]) -> SOME (INR (Litv (Word8 (word_sub v1 v2))))
      | (And,[v1; v2]) -> SOME (INR (Litv (Word8 (word_and v1 v2))))
      | (Or,[v1; v2]) -> SOME (INR (Litv (Word8 (word_or v1 v2))))
      | (Xor,[v1; v2]) -> SOME (INR (Litv (Word8 (word_xor v1 v2))))
      | _ -> NONE) /\
   (do_arith a (WordT W64) vals =
      match (a,MAP the_Litv_Word64 vals) with
        (Add,[v1; v2]) -> SOME (INR (Litv (Word64 (word_add v1 v2))))
      | (Sub,[v1; v2]) -> SOME (INR (Litv (Word64 (word_sub v1 v2))))
      | (And,[v1; v2]) -> SOME (INR (Litv (Word64 (word_and v1 v2))))
      | (Or,[v1; v2]) -> SOME (INR (Litv (Word64 (word_or v1 v2))))
      | (Xor,[v1; v2]) -> SOME (INR (Litv (Word64 (word_xor v1 v2))))
      | _ -> NONE) /\
   (do_arith a BoolT vals =
      match (a,vals) with
        (Not,[v1]) -> SOME (INR (Boolv (~(the_Boolv v1))))
      | _ -> NONE) /\
   (do_arith a _ vals = NONE)`;;

let do_conversion_def = sem1aux_def
  `(do_conversion v (WordT W8) IntT =
      SOME (INR (Litv (IntLit (&(val (the_Litv_Word8 v))))))) /\
   (do_conversion v (WordT W64) IntT =
      SOME (INR (Litv (IntLit (&(val (the_Litv_Word64 v))))))) /\
   (do_conversion v IntT (WordT W8) =
      SOME (INR (Litv (Word8 (iword (the_Litv_IntLit v)))))) /\
   (do_conversion v IntT (WordT W64) =
      SOME (INR (Litv (Word64 (iword (the_Litv_IntLit v)))))) /\
   (do_conversion v CharT IntT =
      SOME (INR (Litv (IntLit (&(ORD (the_Litv_Char v))))))) /\
   (do_conversion v IntT CharT =
      let i = the_Litv_IntLit v in
      if i < &0 \/ i > &255 then SOME (INL chr_exn_v)
      else SOME (INR (Litv (Char (CHR (num_of_int (abs i))))))) /\
   (do_conversion v CharT (WordT W8) =
      SOME (INR (Litv (Word8 (char_to_word8 (the_Litv_Char v)))))) /\
   (do_conversion v (WordT W8) CharT =
      SOME (INR (Litv (Char (word8_to_char (the_Litv_Word8 v)))))) /\
   (do_conversion v Float64T (WordT W64) =
      SOME (INR (Litv (Word64 (the_Litv_Float64 v))))) /\
   (do_conversion v (WordT W64) Float64T =
      SOME (INR (Litv (Float64 (the_Litv_Word64 v))))) /\
   (do_conversion _ _ _ = NONE)`;;

let do_app_def = sem1aux_def
  `do_app (s:(v store_v) list,t:(FFI)ffi_state) op vs =
     match (op,vs) with
       (ListAppend,[x1; x2]) ->
         (match (v_to_list x1,v_to_list x2) with
            (SOME xs,SOME ys) -> SOME ((s,t),Rval (list_to_v (APPEND xs ys)))
          | _ -> NONE)
     | (Shift W8 op n,[Litv (Word8 w)]) ->
         SOME ((s,t),Rval (Litv (Word8 (shift8_lookup op w n))))
     | (Shift W64 op n,[Litv (Word64 w)]) ->
         SOME ((s,t),Rval (Litv (Word64 (shift64_lookup op w n))))
     | (Equality,[v1; v2]) ->
         (match do_eq v1 v2 with
            Eq_type_error -> NONE
          | Eq_val b -> SOME ((s,t),Rval (Boolv b)))
     | (Opassign,[Loc b lnum; v]) ->
         (match store_assign lnum (Refv v) s with
            SOME s' -> SOME ((s',t),Rval (Conv NONE []))
          | NONE -> NONE)
     | (Opref,[v]) ->
         (match store_alloc (Refv v) s with
            (s',n) -> SOME ((s',t),Rval (Loc T n)))
     | (Opderef,[Loc b n]) ->
         (match store_lookup n s with
            SOME (Refv v) -> SOME ((s,t),Rval v)
          | _ -> NONE)
     | (Aw8alloc,[Litv (IntLit n); Litv (Word8 w)]) ->
         if n < &0 then
           SOME ((s,t),Rerr (Rraise sub_exn_v))
         else
           (match store_alloc (W8array (REPLICATE (num_of_int (abs (I n))) w)) s with
              (s',lnum) -> SOME ((s',t),Rval (Loc T lnum)))
     | (Aw8sub,[Loc _ lnum; Litv (IntLit i)]) ->
         (match store_lookup lnum s with
            SOME (W8array ws) ->
              if i < &0 then
                SOME ((s,t),Rerr (Rraise sub_exn_v))
              else
                let n = num_of_int (abs (I i)) in
                if n >= LENGTH ws then
                  SOME ((s,t),Rerr (Rraise sub_exn_v))
                else
                  SOME ((s,t),Rval (Litv (Word8 (EL n ws))))
          | _ -> NONE)
     | (Aw8sub_unsafe,[Loc _ lnum; Litv (IntLit i)]) ->
         (match store_lookup lnum s with
            SOME (W8array ws) ->
              if i < &0 then
                NONE
              else
                let n = num_of_int (abs (I i)) in
                if n >= LENGTH ws then
                  NONE
                else
                  SOME ((s,t),Rval (Litv (Word8 (EL n ws))))
          | _ -> NONE)
     | (Aw8length,[Loc _ n]) ->
         (match store_lookup n s with
            SOME (W8array ws) ->
              SOME ((s,t),Rval (Litv (IntLit (&(LENGTH ws)))))
          | _ -> NONE)
     | (Aw8update,[Loc _ lnum; Litv (IntLit i); Litv (Word8 w)]) ->
         (match store_lookup lnum s with
            SOME (W8array ws) ->
              if i < &0 then
                SOME ((s,t),Rerr (Rraise sub_exn_v))
              else
                let n = num_of_int (abs (I i)) in
                if n >= LENGTH ws then
                  SOME ((s,t),Rerr (Rraise sub_exn_v))
                else
                  (match store_assign lnum (W8array (LUPDATE w n ws)) s with
                     NONE -> NONE
                   | SOME s' -> SOME ((s',t),Rval (Conv NONE [])))
          | _ -> NONE)
     | (Aw8update_unsafe,[Loc _ lnum; Litv (IntLit i); Litv (Word8 w)]) ->
         (match store_lookup lnum s with
            SOME (W8array ws) ->
              if i < &0 then
                NONE
              else
                let n = num_of_int (abs (I i)) in
                if n >= LENGTH ws then
                  NONE
                else
                  (match store_assign lnum (W8array (LUPDATE w n ws)) s with
                     NONE -> NONE
                   | SOME s' -> SOME ((s',t),Rval (Conv NONE [])))
          | _ -> NONE)
     | (CopyStrStr,[Litv (StrLit str); Litv (IntLit off); Litv (IntLit len)]) ->
         SOME ((s,t),
               (match copy_array (explode str,off) len NONE with
                  NONE -> Rerr (Rraise sub_exn_v)
                | SOME cs -> Rval (Litv (StrLit (implode cs)))))
     | (CopyStrAw8,[Litv (StrLit str); Litv (IntLit off); Litv (IntLit len);
                    Loc _ dst; Litv (IntLit dstoff)]) ->
         (match store_lookup dst s with
            SOME (W8array ws) ->
              (match copy_array (explode str,off) len
                       (SOME (ws_to_chars ws,dstoff)) with
                 NONE -> SOME ((s,t),Rerr (Rraise sub_exn_v))
               | SOME cs ->
                   (match store_assign dst (W8array (chars_to_ws cs)) s with
                      SOME s' -> SOME ((s',t),Rval (Conv NONE []))
                    | _ -> NONE))
          | _ -> NONE)
     | (CopyAw8Str,[Loc _ src; Litv (IntLit off); Litv (IntLit len)]) ->
         (match store_lookup src s with
            SOME (W8array ws) ->
              SOME ((s,t),
                    (match copy_array (ws,off) len NONE with
                       NONE -> Rerr (Rraise sub_exn_v)
                     | SOME ws -> Rval (Litv (StrLit (implode (ws_to_chars ws))))))
          | _ -> NONE)
     | (CopyAw8Aw8,[Loc _ src; Litv (IntLit off); Litv (IntLit len);
                    Loc _ dst; Litv (IntLit dstoff)]) ->
         (match (store_lookup src s,store_lookup dst s) with
            (SOME (W8array ws),SOME (W8array ds)) ->
              (match copy_array (ws,off) len (SOME (ds,dstoff)) with
                 NONE -> SOME ((s,t),Rerr (Rraise sub_exn_v))
               | SOME ws ->
                   (match store_assign dst (W8array ws) s with
                      SOME s' -> SOME ((s',t),Rval (Conv NONE []))
                    | _ -> NONE))
          | _ -> NONE)
     | (XorAw8Str_unsafe,[Loc _ dst; Litv (StrLit str_arg)]) ->
         (match store_lookup dst s with
            SOME (W8array bs) ->
              (match xor_bytes (MAP (word o ORD) (explode str_arg)) bs with
                 NONE -> NONE
               | SOME new_bs ->
                   (match store_assign dst (W8array new_bs) s with
                      NONE -> NONE
                    | SOME s' -> SOME ((s',t),Rval (Conv NONE []))))
          | _ -> NONE)
     | (Implode,[v]) ->
         (match v_to_char_list v with
            SOME ls -> SOME ((s,t),Rval (Litv (StrLit (implode ls))))
          | NONE -> NONE)
     | (Explode,[v]) ->
         (match v with
            Litv (StrLit str) ->
              SOME ((s,t),Rval (list_to_v (MAP (\c. Litv (Char c)) (explode str))))
          | _ -> NONE)
     | (Strsub,[Litv (StrLit str); Litv (IntLit i)]) ->
         if i < &0 then
           SOME ((s,t),Rerr (Rraise sub_exn_v))
         else
           let n = num_of_int (abs (I i)) in
           if n >= strlen str then
             SOME ((s,t),Rerr (Rraise sub_exn_v))
           else
             SOME ((s,t),Rval (Litv (Char (EL n (explode str)))))
     | (Strlen,[Litv (StrLit str)]) ->
         SOME ((s,t),Rval (Litv (IntLit (&(strlen str)))))
     | (Strcat,[v]) ->
         (match v_to_list v with
            SOME vs ->
              (match vs_to_string vs with
                 SOME str -> SOME ((s,t),Rval (Litv (StrLit str)))
               | _ -> NONE)
          | _ -> NONE)
     | (VfromList,[v]) ->
         (match v_to_list v with
            SOME vs -> SOME ((s,t),Rval (Vectorv vs))
          | NONE -> NONE)
     | (Vsub_unsafe,[Vectorv vs; Litv (IntLit i)]) ->
         if &0 <= i /\ num_of_int i < LENGTH vs then
           SOME ((s,t),Rval (EL (num_of_int i) vs))
         else
           NONE
     | (Vsub,[Vectorv vs; Litv (IntLit i)]) ->
         if i < &0 then
           SOME ((s,t),Rerr (Rraise sub_exn_v))
         else
           let n = num_of_int (abs (I i)) in
           if n >= LENGTH vs then
             SOME ((s,t),Rerr (Rraise sub_exn_v))
           else
             SOME ((s,t),Rval (EL n vs))
     | (Vlength,[Vectorv vs]) ->
         SOME ((s,t),Rval (Litv (IntLit (&(LENGTH vs)))))
     | (Aalloc,[Litv (IntLit n); v]) ->
         if n < &0 then
           SOME ((s,t),Rerr (Rraise sub_exn_v))
         else
           (match store_alloc (Varray (REPLICATE (num_of_int (abs (I n))) v)) s with
              (s',lnum) -> SOME ((s',t),Rval (Loc T lnum)))
     | (AallocEmpty,[Conv NONE []]) ->
         (match store_alloc (Varray []) s with
            (s',lnum) -> SOME ((s',t),Rval (Loc T lnum)))
     | (AallocFixed,vs) ->
         (match store_alloc (Varray vs) s with
            (s',lnum) -> SOME ((s',t),Rval (Loc T lnum)))
     | (Asub,[Loc _ lnum; Litv (IntLit i)]) ->
         (match store_lookup lnum s with
            SOME (Varray vs) ->
              if i < &0 then
                SOME ((s,t),Rerr (Rraise sub_exn_v))
              else
                let n = num_of_int (abs (I i)) in
                if n >= LENGTH vs then
                  SOME ((s,t),Rerr (Rraise sub_exn_v))
                else
                  SOME ((s,t),Rval (EL n vs))
          | _ -> NONE)
     | (Asub_unsafe,[Loc _ lnum; Litv (IntLit i)]) ->
         (match store_lookup lnum s with
            SOME (Varray vs) ->
              if i < &0 then
                NONE
              else
                let n = num_of_int (abs (I i)) in
                if n >= LENGTH vs then
                  NONE
                else
                  SOME ((s,t),Rval (EL n vs))
          | _ -> NONE)
     | (Alength,[Loc _ n]) ->
         (match store_lookup n s with
            SOME (Varray ws) ->
              SOME ((s,t),Rval (Litv (IntLit (&(LENGTH ws)))))
          | _ -> NONE)
     | (Aupdate,[Loc _ lnum; Litv (IntLit i); v]) ->
         (match store_lookup lnum s with
            SOME (Varray vs) ->
              if i < &0 then
                SOME ((s,t),Rerr (Rraise sub_exn_v))
              else
                let n = num_of_int (abs (I i)) in
                if n >= LENGTH vs then
                  SOME ((s,t),Rerr (Rraise sub_exn_v))
                else
                  (match store_assign lnum (Varray (LUPDATE v n vs)) s with
                     NONE -> NONE
                   | SOME s' -> SOME ((s',t),Rval (Conv NONE [])))
          | _ -> NONE)
     | (Aupdate_unsafe,[Loc _ lnum; Litv (IntLit i); v]) ->
         (match store_lookup lnum s with
            SOME (Varray vs) ->
              if i < &0 then
                NONE
              else
                let n = num_of_int (abs (I i)) in
                if n >= LENGTH vs then
                  NONE
                else
                  (match store_assign lnum (Varray (LUPDATE v n vs)) s with
                     NONE -> NONE
                   | SOME s' -> SOME ((s',t),Rval (Conv NONE [])))
          | _ -> NONE)
     | (ConfigGC,[Litv (IntLit i); Litv (IntLit j)]) ->
         SOME ((s,t),Rval (Conv NONE []))
     | (FFI n,[Litv (StrLit conf); Loc _ lnum]) ->
         (match store_lookup lnum s with
            SOME (W8array ws) ->
              (match call_FFI t (ExtCall n) (MAP (word o ORD) (explode conf)) ws with
                 FFI_return t' ws' ->
                   (match store_assign lnum (W8array ws') s with
                      SOME s' -> SOME ((s',t'),Rval (Conv NONE []))
                    | NONE -> NONE)
               | FFI_final outcome ->
                   SOME ((s,t),Rerr (Rabort (Rffi_error outcome))))
          | _ -> NONE)
     | (Env_id,[Env env (gen,id)]) ->
         SOME ((s,t),Rval (Conv NONE [nat_to_v gen; nat_to_v id]))
     | (Env_id,[Conv NONE [gen; id]]) ->
         SOME ((s,t),Rval (Conv NONE [gen; id]))
     | (ThunkOp th_op,vs) -> thunk_op (s,t) th_op vs
     | (Arith a ty,vs) ->
         if ALL (check_type ty) vs then
           (match do_arith a ty vs with
              SOME (INR res) -> SOME ((s,t),Rval res)
            | SOME (INL exn) -> SOME ((s,t),Rerr (Rraise exn))
            | NONE -> NONE)
         else NONE
     | (FromTo ty1 ty2,[v]) ->
         if check_type ty1 v then
           (match do_conversion v ty1 ty2 with
              SOME (INR res) -> SOME ((s,t),Rval res)
            | SOME (INL exn) -> SOME ((s,t),Rerr (Rraise exn))
            | NONE -> NONE)
         else NONE
     | (Test test test_ty,[v1; v2]) ->
         (match do_test test test_ty v1 v2 with
            Eq_type_error -> NONE
          | Eq_val b -> SOME ((s,t),Rval (Boolv b)))
     | _ -> NONE`;;

(* Do a logical operation *)

let do_log_def = cake_def
  `do_log l v e =
     if l = Andalso /\ v = Boolv T \/ l = Orelse /\ v = Boolv F then SOME (Exp e)
     else if l = Andalso /\ v = Boolv F \/ l = Orelse /\ v = Boolv T
     then SOME (Val v)
     else NONE`;;

(* Do an if-then-else *)

let do_if_def = cake_def
  `do_if v (e1:exp) (e2:exp) =
     if v = Boolv T then SOME e1 else if v = Boolv F then SOME e2 else NONE`;;

(* Semantic helpers for definitions *)

let build_constrs_def = cake_def
  `build_constrs stamp (condefs:(mlstring # ast_t list) list) =
     MAP (\cts. match cts with
                  (conN,ts) -> (conN,LENGTH ts,TypeStamp conN stamp)) condefs`;;

(* Build a constructor environment for the type definition tds *)

let build_tdefs_def = cake_def
  `(build_tdefs next_stamp
      ([]:(tvarN list # mlstring # (mlstring # ast_t list) list) list) =
      (alist_to_ns []):(mlstring,mlstring,num#stamp)namespace) /\
   (build_tdefs next_stamp (CONS (tvs,tn,condefs) tds) =
      nsAppend (build_tdefs (next_stamp + 1) tds)
        (alist_to_ns (REVERSE (build_constrs next_stamp condefs))))`;;

let build_tdefs_ind = cake_ind "build_tdefs";;

(* Checks that no constructor is defined twice in a type *)

let check_dup_ctors_def = cake_def
  `check_dup_ctors
     ((tvs,tn,condefs):tvarN list # mlstring # (mlstring # ast_t list) list) <=>
     ALL_DISTINCT
       (let x2 = [] in
        ITLIST (\nts x2. match nts with (n,ts) -> if T then CONS n x2 else x2)
               condefs x2)`;;

let combine_dec_result_def = cake_def
  `combine_dec_result env (r:(v sem_env,A)result) =
     match r with
       Rval env' ->
         Rval (sem_env_REC (nsAppend (sem_env_v env') (sem_env_v env))
                           (nsAppend (sem_env_c env') (sem_env_c env)))
     | Rerr e -> Rerr e`;;

let extend_dec_env_def = cake_def
  `extend_dec_env new_env (env:v sem_env) =
     sem_env_REC (nsAppend (sem_env_v new_env) (sem_env_v env))
                 (nsAppend (sem_env_c new_env) (sem_env_c env))`;;
