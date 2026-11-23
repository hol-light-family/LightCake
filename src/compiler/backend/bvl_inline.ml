(* ========================================================================= *)
(* bvl_inline: port of HOL4 compiler/backend/bvl_inlineScript.sml (CakeML    *)
(* v3479).  A simple function-inlining optimisation within the BVL          *)
(* language.  There is a more advanced inlining optimisation as part of     *)
(* clos_known.                                                               *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/bvl.ml";;
needs "compiler/backend/bvl_handle.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* tick_inline -- a function that inlines a function body.  HOL4 infers   *)
(* cs : ('a # exp) num_map (the arity is not used here)                    *)

let tick_inline_def = sem1aux_def_wf
  `MEASURE (\p:(A#bvl_exp) spt # bvl_exp list. list_size bvl_exp_size (SND p))`
  SEM1AUX_TC_TAC
  `(tick_inline (cs:(A#bvl_exp) spt) [] = []) /\
   (tick_inline cs (CONS x (CONS y xs)) =
      CONS (HD (tick_inline cs [x])) (tick_inline cs (CONS y xs))) /\
   (tick_inline cs [bvl_Var v] = [bvl_Var v]) /\
   (tick_inline cs [bvl_If x1 x2 x3] =
      [bvl_If (HD (tick_inline cs [x1]))
              (HD (tick_inline cs [x2]))
              (HD (tick_inline cs [x3]))]) /\
   (tick_inline cs [bvl_Let xs x2] =
      [bvl_Let (tick_inline cs xs)
               (HD (tick_inline cs [x2]))]) /\
   (tick_inline cs [bvl_Raise x1] =
      [bvl_Raise (HD (tick_inline cs [x1]))]) /\
   (tick_inline cs [bvl_Handle x1 x2] =
      [bvl_Handle (HD (tick_inline cs [x1]))
                  (HD (tick_inline cs [x2]))]) /\
   (tick_inline cs [bvl_Op op xs] =
      [bvl_Op op (tick_inline cs xs)]) /\
   (tick_inline cs [bvl_Tick x] =
      [bvl_Tick (HD (tick_inline cs [x]))]) /\
   (tick_inline cs [bvl_Force m n] = [bvl_Force m n]) /\
   (tick_inline cs [bvl_Call ticks dest xs] =
      match dest with
        NONE -> [bvl_Call ticks dest (tick_inline cs xs)]
      | SOME n ->
          (match lookup n cs with
             NONE -> [bvl_Call ticks dest (tick_inline cs xs)]
           | SOME (arity,code) ->
               [bvl_Let (tick_inline cs xs) (mk_tick (SUC ticks) code)]))`;;

let tick_inline_ind = cake_ind "tick_inline";;

let tick_inline_sing_def = sem1aux_def_wf
  `MEASURE (\x:(A#bvl_exp) spt # bvl_exp + (A#bvl_exp) spt # bvl_exp list.
              sum_CASE x (\p. bvl_exp_size (SND p))
                         (\p. list_size bvl_exp_size (SND p)))`
  SEM1AUX_TC_TAC
  `(tick_inline_sing (cs:(A#bvl_exp) spt) (bvl_Var v) = bvl_Var v) /\
   (tick_inline_sing cs (bvl_If x1 x2 x3) =
      bvl_If (tick_inline_sing cs x1)
             (tick_inline_sing cs x2)
             (tick_inline_sing cs x3)) /\
   (tick_inline_sing cs (bvl_Let xs x2) =
      bvl_Let (tick_inline_list cs xs)
              (tick_inline_sing cs x2)) /\
   (tick_inline_sing cs (bvl_Raise x1) =
      bvl_Raise (tick_inline_sing cs x1)) /\
   (tick_inline_sing cs (bvl_Handle x1 x2) =
      bvl_Handle (tick_inline_sing cs x1)
                 (tick_inline_sing cs x2)) /\
   (tick_inline_sing cs (bvl_Op op xs) =
      bvl_Op op (tick_inline_list cs xs)) /\
   (tick_inline_sing cs (bvl_Tick x) =
      bvl_Tick (tick_inline_sing cs x)) /\
   (tick_inline_sing cs (bvl_Force m n) = bvl_Force m n) /\
   (tick_inline_sing cs (bvl_Call ticks dest xs) =
      match dest with
        NONE -> bvl_Call ticks dest (tick_inline_list cs xs)
      | SOME n ->
          (match lookup n cs with
             NONE -> bvl_Call ticks dest (tick_inline_list cs xs)
           | SOME (arity,code) ->
               bvl_Let (tick_inline_list cs xs) (mk_tick (SUC ticks) code))) /\
   (tick_inline_list cs [] = []) /\
   (tick_inline_list cs (CONS x xs) =
      CONS (tick_inline_sing cs x) (tick_inline_list cs xs))`;;

let tick_inline_sing = prove
 (`(!e. tick_inline (cs:(A#bvl_exp) spt) [e] = [tick_inline_sing cs e]) /\
   (!es. tick_inline_list cs es = tick_inline cs es)`,
  MATCH_MP_TAC bvl_exp_INDUCT THEN
  GVS[tick_inline_sing_def; tick_inline_def] THEN RW[] THEN
  EVERY_CASE_TAC THEN
  CASES_ON `a1:bvl_exp list` THEN GVS[tick_inline_sing_def; tick_inline_def]);;

(* This definition is written to exit as soon as possible. *)

let is_small_aux_def = sem1aux_def_wf
  `MEASURE (\p:num # bvl_exp list. list_size bvl_exp_size (SND p))`
  SEM1AUX_TC_TAC
  `(is_small_aux n [] = n) /\
   (is_small_aux n (CONS x (CONS y xs)) =
      if n = 0 then n else
        let n = is_small_aux n [x] in if n = 0 then n else
          is_small_aux n (CONS y xs)) /\
   (is_small_aux n [bvl_Var v] = n) /\
   (is_small_aux n [bvl_If x1 x2 x3] =
      let n = n - 1 in if n = 0 then 0 else
      let n = is_small_aux n [x1] in if n = 0 then 0 else
      let n = is_small_aux n [x2] in if n = 0 then 0 else
        is_small_aux n [x3]) /\
   (is_small_aux n [bvl_Let xs x2] =
      let n = n - 1 in if n = 0 then 0 else
      let n = is_small_aux n xs in if n = 0 then 0 else
        is_small_aux n [x2]) /\
   (is_small_aux n [bvl_Raise x1] =
      let n = n - 1 in if n = 0 then 0 else
        is_small_aux n [x1]) /\
   (is_small_aux n [bvl_Handle x1 x2] =
      let n = n - 1 in if n = 0 then 0 else
      let n = is_small_aux n [x1] in if n = 0 then 0 else
        is_small_aux n [x2]) /\
   (is_small_aux n [bvl_Op op xs] =
      let n = n - 1 in if n = 0 then 0 else
        is_small_aux n xs) /\
   (is_small_aux n [bvl_Tick x] = is_small_aux n [x]) /\
   (is_small_aux n [bvl_Force _ _] = n) /\
   (is_small_aux n [bvl_Call ticks dest xs] =
      let n = n - 1 in if n = 0 then 0 else
        is_small_aux n xs)`;;

let is_small_aux_ind = cake_ind "is_small_aux";;

let is_small_sing_def = sem1aux_def_wf
  `MEASURE (\x:num # bvl_exp + num # bvl_exp list.
              sum_CASE x (\p. bvl_exp_size (SND p))
                         (\p. list_size bvl_exp_size (SND p)))`
  SEM1AUX_TC_TAC
  `(is_small_sing n (bvl_Var v) = n) /\
   (is_small_sing n (bvl_If x1 x2 x3) =
      let n = n - 1 in if n = 0 then 0 else
      let n = is_small_sing n x1 in if n = 0 then 0 else
      let n = is_small_sing n x2 in if n = 0 then 0 else
        is_small_sing n x3) /\
   (is_small_sing n (bvl_Let xs x2) =
      let n = n - 1 in if n = 0 then 0 else
      let n = is_small_list n xs in if n = 0 then 0 else
        is_small_sing n x2) /\
   (is_small_sing n (bvl_Raise x1) =
      let n = n - 1 in if n = 0 then 0 else
        is_small_sing n x1) /\
   (is_small_sing n (bvl_Handle x1 x2) =
      let n = n - 1 in if n = 0 then 0 else
      let n = is_small_sing n x1 in if n = 0 then 0 else
        is_small_sing n x2) /\
   (is_small_sing n (bvl_Op op xs) =
      let n = n - 1 in if n = 0 then 0 else
        is_small_list n xs) /\
   (is_small_sing n (bvl_Tick x) = is_small_sing n x) /\
   (is_small_sing n (bvl_Force _ _) = n) /\
   (is_small_sing n (bvl_Call ticks dest xs) =
      let n = n - 1 in if n = 0 then 0 else
        is_small_list n xs) /\
   (is_small_list n [] = n) /\
   (is_small_list n (CONS x xs) =
      if n = 0 then n else
        let n = is_small_sing n x in if n = 0 then n else
          is_small_list n xs)`;;

let is_small_sing = prove
 (`(!e n. is_small_aux n [e] = is_small_sing n e) /\
   (!es n. is_small_list n es = is_small_aux n es)`,
  SUBGOAL_THEN `(!e. is_small_sing 0 e = 0) /\ (!es. is_small_list 0 es = 0)`
    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC bvl_exp_INDUCT THEN RW[is_small_sing_def; LET_DEF; LET_END_DEF];
    ALL_TAC] THEN
  MATCH_MP_TAC bvl_exp_INDUCT THEN
  GVS[is_small_sing_def; is_small_aux_def] THEN RW[] THEN
  CASES_ON `a1:bvl_exp list` THEN
  GVS[is_small_sing_def; is_small_aux_def; LET_DEF; LET_END_DEF] THEN
  RW[]);;

let is_small_def = cake_def
  `is_small limit e <=> ~(is_small_aux limit [e] = 0)`;;

let is_small_eq = prove
 (`!limit e. is_small limit e <=> ~(is_small_sing limit e = 0)`,
  REWRITE_TAC[is_small_def; is_small_sing]);;

let bvl_inline_is_rec_def = sem1aux_def_wf
  `MEASURE (\p:num # bvl_exp list. list_size bvl_exp_size (SND p))`
  SEM1AUX_TC_TAC
  `(bvl_inline_is_rec n [] <=> F) /\
   (bvl_inline_is_rec n (CONS x (CONS y xs)) <=>
      if bvl_inline_is_rec n [x] then T else
        bvl_inline_is_rec n (CONS y xs)) /\
   (bvl_inline_is_rec n [bvl_Var v] <=> F) /\
   (bvl_inline_is_rec n [bvl_If x1 x2 x3] <=>
      if bvl_inline_is_rec n [x1] then T else
      if bvl_inline_is_rec n [x2] then T else
        bvl_inline_is_rec n [x3]) /\
   (bvl_inline_is_rec n [bvl_Let xs x2] <=>
      if bvl_inline_is_rec n xs then T else
        bvl_inline_is_rec n [x2]) /\
   (bvl_inline_is_rec n [bvl_Raise x1] <=> bvl_inline_is_rec n [x1]) /\
   (bvl_inline_is_rec n [bvl_Handle x1 x2] <=>
      if bvl_inline_is_rec n [x1] then T else
        bvl_inline_is_rec n [x2]) /\
   (bvl_inline_is_rec n [bvl_Op op xs] <=> bvl_inline_is_rec n xs) /\
   (bvl_inline_is_rec n [bvl_Tick x] <=> bvl_inline_is_rec n [x]) /\
   (bvl_inline_is_rec n [bvl_Force _ _] <=> F) /\
   (bvl_inline_is_rec n [bvl_Call ticks dest xs] <=>
      if dest = SOME n then T else bvl_inline_is_rec n xs)`;;

let bvl_inline_is_rec_ind = cake_ind "bvl_inline_is_rec";;

let is_rec_sing_def = sem1aux_def_wf
  `MEASURE (\x:num # bvl_exp + num # bvl_exp list.
              sum_CASE x (\p. bvl_exp_size (SND p))
                         (\p. list_size bvl_exp_size (SND p)))`
  SEM1AUX_TC_TAC
  `(is_rec_sing n (bvl_Var v) <=> F) /\
   (is_rec_sing n (bvl_If x1 x2 x3) <=>
      if is_rec_sing n x1 then T else
      if is_rec_sing n x2 then T else
        is_rec_sing n x3) /\
   (is_rec_sing n (bvl_Let xs x2) <=>
      if is_rec_list n xs then T else
        is_rec_sing n x2) /\
   (is_rec_sing n (bvl_Raise x1) <=> is_rec_sing n x1) /\
   (is_rec_sing n (bvl_Handle x1 x2) <=>
      if is_rec_sing n x1 then T else
        is_rec_sing n x2) /\
   (is_rec_sing n (bvl_Op op xs) <=> is_rec_list n xs) /\
   (is_rec_sing n (bvl_Tick x) <=> is_rec_sing n x) /\
   (is_rec_sing n (bvl_Force _ _) <=> F) /\
   (is_rec_sing n (bvl_Call ticks dest xs) <=>
      if dest = SOME n then T else is_rec_list n xs) /\
   (is_rec_list n [] <=> F) /\
   (is_rec_list n (CONS x xs) <=>
      if is_rec_sing n x then T else
        is_rec_list n xs)`;;

let is_rec_sing = prove
 (`(!e n. bvl_inline_is_rec n [e] <=> is_rec_sing n e) /\
   (!es n. is_rec_list n es <=> bvl_inline_is_rec n es)`,
  MATCH_MP_TAC bvl_exp_INDUCT THEN
  GVS[is_rec_sing_def; bvl_inline_is_rec_def] THEN RW[] THEN
  CASES_ON `a1:bvl_exp list` THEN GVS[is_rec_sing_def; bvl_inline_is_rec_def] THEN
  RW[]);;

let must_inline_def = cake_def
  `must_inline name limit e <=>
     if is_small limit e then ~(bvl_inline_is_rec name [e]) else F`;;

(* HOL4: must_inline_def |> SRULE [is_rec_sing] (srw_ss turns the          *)
(* conditional into a conjunction, COND_BOOL_CLAUSES)                       *)

let must_inline_eq = prove
 (`!name limit e. must_inline name limit e <=>
                  is_small limit e /\ ~is_rec_sing name e`,
  REWRITE_TAC[must_inline_def; is_rec_sing] THEN MESON_TAC[]);;

let tick_inline_all_def = cake_def
  `(tick_inline_all limit cs [] aux = (cs,REVERSE aux)) /\
   (tick_inline_all limit cs (CONS (n,arity:num,e1) xs) aux =
      let e2 = HD (tick_inline cs [e1]) in
      let cs2 = if must_inline n limit e2 then insert n (arity,e2) cs else cs in
        tick_inline_all limit cs2 xs (CONS (n,arity,e2) aux))`;;

let tick_inline_all_ind = cake_ind "tick_inline_all";;

(* HOL4: tick_inline_all_def |> SRULE [tick_inline_sing] *)

let tick_inline_all_eq = prove
 (`(!limit cs aux. tick_inline_all limit cs [] aux = (cs,REVERSE aux)) /\
   (!limit cs n arity e1 xs aux.
      tick_inline_all limit cs (CONS (n,arity,e1) xs) aux =
      let e2 = tick_inline_sing cs e1 in
      let cs2 = if must_inline n limit e2 then insert n (arity,e2) cs else cs in
        tick_inline_all limit cs2 xs (CONS (n,arity,e2) aux))`,
  REWRITE_TAC[tick_inline_all_def; tick_inline_sing; HD]);;

let tick_compile_prog_def = cake_def
  `tick_compile_prog limit cs prog = tick_inline_all limit cs prog []`;;

let LENGTH_tick_inline = prove
 (`!cs:(A#bvl_exp) spt xs. LENGTH (tick_inline cs xs) = LENGTH xs`,
  MATCH_MP_TAC tick_inline_ind THEN REPEAT STRIP_TAC THEN
  FS[tick_inline_def; LET_DEF; LET_END_DEF] THEN RW[] THEN
  EVERY_CASE_TAC THEN FS[]);;

let HD_tick_inline = prove
 (`[HD (tick_inline (cs:(A#bvl_exp) spt) [x])] = tick_inline cs [x]`,
  MP_TAC (SPECL [`cs:(A#bvl_exp) spt`; `[x:bvl_exp]`] LENGTH_tick_inline) THEN
  CASES_ON `tick_inline (cs:(A#bvl_exp) spt) [x]` THEN
  RW[LENGTH; LENGTH_EQ_NIL]);;

let _ = cake_add_simps [HD_tick_inline];;

(* remove_ticks -- a function that removes Ticks *)

let bvl_inline_remove_ticks_def = sem1aux_def_wf
  `MEASURE (\xs:bvl_exp list. list_size bvl_exp_size xs)`
  SEM1AUX_TC_TAC
  `(bvl_inline_remove_ticks [] = []) /\
   (bvl_inline_remove_ticks (CONS x (CONS y xs)) =
      CONS (HD (bvl_inline_remove_ticks [x])) (bvl_inline_remove_ticks (CONS y xs))) /\
   (bvl_inline_remove_ticks [bvl_Var v] = [bvl_Var v]) /\
   (bvl_inline_remove_ticks [bvl_If x1 x2 x3] =
      [bvl_If (HD (bvl_inline_remove_ticks [x1]))
              (HD (bvl_inline_remove_ticks [x2]))
              (HD (bvl_inline_remove_ticks [x3]))]) /\
   (bvl_inline_remove_ticks [bvl_Let xs x2] =
      [bvl_Let (bvl_inline_remove_ticks xs) (HD (bvl_inline_remove_ticks [x2]))]) /\
   (bvl_inline_remove_ticks [bvl_Raise x1] =
      [bvl_Raise (HD (bvl_inline_remove_ticks [x1]))]) /\
   (bvl_inline_remove_ticks [bvl_Handle x1 x2] =
      [bvl_Handle (HD (bvl_inline_remove_ticks [x1]))
                  (HD (bvl_inline_remove_ticks [x2]))]) /\
   (bvl_inline_remove_ticks [bvl_Op op xs] =
      [bvl_Op op (bvl_inline_remove_ticks xs)]) /\
   (bvl_inline_remove_ticks [bvl_Tick x] = bvl_inline_remove_ticks [x]) /\
   (bvl_inline_remove_ticks [bvl_Force m n] = [bvl_Force m n]) /\
   (bvl_inline_remove_ticks [bvl_Call ticks dest xs] =
      [bvl_Call 0 dest (bvl_inline_remove_ticks xs)])`;;

let bvl_inline_remove_ticks_ind = cake_ind "bvl_inline_remove_ticks";;

let bvl_inline_remove_ticks_sing_def = sem1aux_def_wf
  `MEASURE (\x:bvl_exp + bvl_exp list.
              sum_CASE x (\e. bvl_exp_size e) (\es. list_size bvl_exp_size es))`
  SEM1AUX_TC_TAC
  `(bvl_inline_remove_ticks_sing (bvl_Var v) = bvl_Var v) /\
   (bvl_inline_remove_ticks_sing (bvl_If x1 x2 x3) =
      bvl_If (bvl_inline_remove_ticks_sing x1)
             (bvl_inline_remove_ticks_sing x2)
             (bvl_inline_remove_ticks_sing x3)) /\
   (bvl_inline_remove_ticks_sing (bvl_Let xs x2) =
      bvl_Let (bvl_inline_remove_ticks_list xs) (bvl_inline_remove_ticks_sing x2)) /\
   (bvl_inline_remove_ticks_sing (bvl_Raise x1) =
      bvl_Raise (bvl_inline_remove_ticks_sing x1)) /\
   (bvl_inline_remove_ticks_sing (bvl_Handle x1 x2) =
      bvl_Handle (bvl_inline_remove_ticks_sing x1)
                 (bvl_inline_remove_ticks_sing x2)) /\
   (bvl_inline_remove_ticks_sing (bvl_Op op xs) =
      bvl_Op op (bvl_inline_remove_ticks_list xs)) /\
   (bvl_inline_remove_ticks_sing (bvl_Tick x) = bvl_inline_remove_ticks_sing x) /\
   (bvl_inline_remove_ticks_sing (bvl_Force m n) = bvl_Force m n) /\
   (bvl_inline_remove_ticks_sing (bvl_Call ticks dest xs) =
      bvl_Call 0 dest (bvl_inline_remove_ticks_list xs)) /\
   (bvl_inline_remove_ticks_list [] = []) /\
   (bvl_inline_remove_ticks_list (CONS x xs) =
      CONS (bvl_inline_remove_ticks_sing x) (bvl_inline_remove_ticks_list xs))`;;

let remove_ticks_sing = prove
 (`(!e. bvl_inline_remove_ticks [e] = [bvl_inline_remove_ticks_sing e]) /\
   (!es. bvl_inline_remove_ticks_list es = bvl_inline_remove_ticks es)`,
  MATCH_MP_TAC bvl_exp_INDUCT THEN
  GVS[bvl_inline_remove_ticks_sing_def; bvl_inline_remove_ticks_def] THEN RW[] THEN
  CASES_ON `a1:bvl_exp list` THEN
  GVS[bvl_inline_remove_ticks_sing_def; bvl_inline_remove_ticks_def]);;

let bvl_inline_LENGTH_remove_ticks = prove
 (`!xs. LENGTH (bvl_inline_remove_ticks xs) = LENGTH xs`,
  MATCH_MP_TAC bvl_inline_remove_ticks_ind THEN
  FS[bvl_inline_remove_ticks_def]);;

let _ = cake_add_simps [bvl_inline_LENGTH_remove_ticks];;

let bvl_inline_remove_ticks_SING = prove
 (`[HD (bvl_inline_remove_ticks [r])] = bvl_inline_remove_ticks [r]`,
  MP_TAC (SPEC `[r:bvl_exp]` bvl_inline_LENGTH_remove_ticks) THEN
  CASES_ON `bvl_inline_remove_ticks [r]` THEN
  RW[LENGTH; LENGTH_EQ_NIL]);;

let _ = cake_add_simps [bvl_inline_remove_ticks_SING];;

(* let_op -- a function that optimises Let [...] (Op op [Var ...]); HOL4    *)
(* infers args : 'a list for var_list and dest_op                           *)

let bvl_inline_var_list_def = sem1aux_def
  `(bvl_inline_var_list n [] ([]:A list) <=> T) /\
   (bvl_inline_var_list n (CONS (bvl_Var m) xs) (CONS (y:A) ys) <=>
      m = n /\ bvl_inline_var_list (n + 1) xs ys) /\
   (bvl_inline_var_list _ _ _ <=> F)`;;

let bvl_inline_var_list_ind = cake_ind "bvl_inline_var_list";;

let bvl_inline_dest_op_def = sem1aux_def
  `(bvl_inline_dest_op (bvl_Op op xs) (args:A list) =
      if bvl_inline_var_list 0 xs args then SOME op else NONE) /\
   (bvl_inline_dest_op _ _ = NONE)`;;

let bvl_inline_let_op_def = sem1aux_def_wf
  `MEASURE (\xs:bvl_exp list. list_size bvl_exp_size xs)`
  SEM1AUX_TC_TAC
  `(bvl_inline_let_op [] = []) /\
   (bvl_inline_let_op (CONS (x:bvl_exp) (CONS y xs)) =
      CONS (HD (bvl_inline_let_op [x])) (bvl_inline_let_op (CONS y xs))) /\
   (bvl_inline_let_op [bvl_Var v] = [bvl_Var v]) /\
   (bvl_inline_let_op [bvl_If x1 x2 x3] =
      [bvl_If (HD (bvl_inline_let_op [x1]))
              (HD (bvl_inline_let_op [x2]))
              (HD (bvl_inline_let_op [x3]))]) /\
   (bvl_inline_let_op [bvl_Let xs x2] =
      let xs = bvl_inline_let_op xs in
      let x2 = HD (bvl_inline_let_op [x2]) in
        match bvl_inline_dest_op x2 xs with
          SOME op -> [bvl_Op op xs]
        | NONE -> [bvl_Let xs x2]) /\
   (bvl_inline_let_op [bvl_Raise x1] =
      [bvl_Raise (HD (bvl_inline_let_op [x1]))]) /\
   (bvl_inline_let_op [bvl_Handle x1 x2] =
      [bvl_Handle (HD (bvl_inline_let_op [x1]))
                  (HD (bvl_inline_let_op [x2]))]) /\
   (bvl_inline_let_op [bvl_Op op xs] =
      [bvl_Op op (bvl_inline_let_op xs)]) /\
   (bvl_inline_let_op [bvl_Tick x] = [bvl_Tick (HD (bvl_inline_let_op [x]))]) /\
   (bvl_inline_let_op [bvl_Force m n] = [bvl_Force m n]) /\
   (bvl_inline_let_op [bvl_Call ticks dest xs] =
      [bvl_Call ticks dest (bvl_inline_let_op xs)])`;;

let bvl_inline_let_op_ind = cake_ind "bvl_inline_let_op";;

let let_op_one_def = sem1aux_def_wf
  `MEASURE (\x:bvl_exp + bvl_exp list.
              sum_CASE x (\e. bvl_exp_size e) (\es. list_size bvl_exp_size es))`
  SEM1AUX_TC_TAC
  `(let_op_one (bvl_Var v) = bvl_Var v) /\
   (let_op_one (bvl_If x1 x2 x3) =
      bvl_If (let_op_one x1)
             (let_op_one x2)
             (let_op_one x3)) /\
   (let_op_one (bvl_Let xs x2) =
      let xs = bvl_inline_let_op_list xs in
      let x2 = let_op_one x2 in
        match bvl_inline_dest_op x2 xs with
          SOME op -> bvl_Op op xs
        | NONE -> bvl_Let xs x2) /\
   (let_op_one (bvl_Raise x1) =
      bvl_Raise (let_op_one x1)) /\
   (let_op_one (bvl_Handle x1 x2) =
      bvl_Handle (let_op_one x1)
                 (let_op_one x2)) /\
   (let_op_one (bvl_Op op xs) =
      bvl_Op op (bvl_inline_let_op_list xs)) /\
   (let_op_one (bvl_Tick x) = bvl_Tick (let_op_one x)) /\
   (let_op_one (bvl_Force m n) = bvl_Force m n) /\
   (let_op_one (bvl_Call ticks dest xs) =
      bvl_Call ticks dest (bvl_inline_let_op_list xs)) /\
   (bvl_inline_let_op_list [] = []) /\
   (bvl_inline_let_op_list (CONS (x:bvl_exp) xs) =
      CONS (let_op_one x) (bvl_inline_let_op_list xs))`;;

let let_op_one = prove
 (`(!e. bvl_inline_let_op [e] = [let_op_one e]) /\
   (!es. bvl_inline_let_op_list es = bvl_inline_let_op es)`,
  MATCH_MP_TAC bvl_exp_INDUCT THEN
  GVS[let_op_one_def; bvl_inline_let_op_def] THEN RW[] THEN
  EVERY_CASE_TAC THEN GVS[] THEN
  CASES_ON `a1:bvl_exp list` THEN GVS[let_op_one_def; bvl_inline_let_op_def]);;

let bvl_inline_let_op_sing_def = cake_def
  `bvl_inline_let_op_sing x =
     match bvl_inline_let_op [x] with
       CONS y ys -> y
     | _ -> bvl_Op (IntOp (clos_Const (&0))) []`;;

(* HOL4: let_op_sing_def |> SRULE [let_op_one] *)

let bvl_inline_let_op_sing_eq = prove
 (`!x. bvl_inline_let_op_sing x = let_op_one x`,
  REWRITE_TAC[bvl_inline_let_op_sing_def; let_op_one] THEN CASE_REWRITE_TAC[]);;

let bvl_inline_optimise_def = cake_def
  `bvl_inline_optimise split_seq cut_size (name:A,arity,exp) =
     (name,arity,
      compile_any split_seq cut_size arity
        (bvl_inline_let_op_sing (HD (bvl_inline_remove_ticks [exp]))))`;;

(* HOL4: optimise_def |> SRULE [remove_ticks_sing]; bvl_handle$compile_any  *)
(* is compile_any                                                           *)

let optimise_eq = prove
 (`!split_seq cut_size (name:A) arity exp.
     bvl_inline_optimise split_seq cut_size (name,arity,exp) =
     (name,arity,
      compile_any split_seq cut_size arity
        (bvl_inline_let_op_sing (bvl_inline_remove_ticks_sing exp)))`,
  REWRITE_TAC[bvl_inline_optimise_def; remove_ticks_sing; HD]);;

let bvl_inline_compile_inc_def = cake_def
  `bvl_inline_compile_inc limit split_seq cut_size cs prog =
     let (cs,prog1) = tick_compile_prog limit cs prog in
       (cs,MAP (bvl_inline_optimise split_seq cut_size) prog1)`;;

let bvl_inline_compile_prog_def = cake_def
  `bvl_inline_compile_prog limit split_seq cut_size prog =
     bvl_inline_compile_inc limit split_seq cut_size LN prog`;;
