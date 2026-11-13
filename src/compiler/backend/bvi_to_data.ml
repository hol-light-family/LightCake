(* ========================================================================= *)
(* bvi_to_data: port of HOL4 compiler/backend/bvi_to_dataScript.sml         *)
(* (CakeML v3479).                                                           *)
(* A compiler phase that turns programs of the functional language BVI into  *)
(* the first imperative language of the CakeML compiler: dataLang.           *)
(*                                                                           *)
(* Notes on the rendering: HOL4's pmatch is a match (case constants), so a   *)
(* NAME_pmatch theorem has the statement of the case form; HOL4 tail is the  *)
(* variable tail; ++ is left associative: vs ++ live ++ env is               *)
(* APPEND (APPEND vs live) env; GENLIST f n is list_of_seq f n.  The         *)
(* compilers compile, compile_sing and compile_list (catch-all and list      *)
(* patterns) are defined with sem1aux_def_wf (semantics/sem1aux_tfl.ml).     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_simp.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/data_space.ml";;
needs "semantics/sem1aux_tfl.ml";;

type_invention_error := true;;

(* compilation from BVI to dataLang *)

let op_space_reset_pmatch = prove
 (CASE_TERM
  `!op. op_space_reset op <=>
     match op with
       IntOp clos_Add -> T
     | IntOp clos_Sub -> T
     | IntOp Mult -> T
     | IntOp clos_Div -> T
     | IntOp clos_Mod -> T
     | IntOp clos_Less -> T
     | IntOp LessEq -> T
     | IntOp Greater -> T
     | IntOp GreaterEq -> T
     | BlockOp clos_Equal -> T
     | BlockOp clos_ListAppend -> T
     | BlockOp (FromList _) -> T
     | BlockOp (ConsExtend _) -> T
     | MemOp RefArray -> T
     | MemOp (RefByte _) -> T
     | MemOp (CopyByte new_flag) -> new_flag
     | MemOp clos_ConfigGC -> T
     | clos_FFI _ -> T
     | _ -> F`,
  GEN_TAC THEN EVERY_CASE_TAC THEN REWRITE_TAC[op_space_reset_def]);;

let op_requires_names_eqn = prove
 (CASE_TERM
  `!op. op_requires_names op <=>
     op_space_reset op \/
     (match op with
        clos_FFI n -> T
      | clos_Install -> T
      | MemOp (CopyByte new_flag) -> T
      | MemOp XorByte -> T
      | MemOp (StringCmp b cmp) -> T
      | _ -> F)`,
  GEN_TAC THEN EVERY_CASE_TAC THEN
  REWRITE_TAC[op_requires_names_def; distinctness "clos_op"; injectivity "clos_op";
              distinctness "mem_op"; injectivity "mem_op"] THEN
  MESON_TAC[]);;

(* HOL4: op_requires_names_pmatch (the same statement in this port) *)

let op_requires_names_pmatch = op_requires_names_eqn;;

let iAssign_def = cake_def
  `iAssign n1 op vs live env =
     if op_requires_names op then
       let xs = SOME (list_to_num_set (APPEND (APPEND vs live) env)) in
         if op = IntOp Greater then
           data_Assign n1 (IntOp clos_Less) (REVERSE vs) xs
         else if op = IntOp GreaterEq then
           data_Assign n1 (IntOp LessEq) (REVERSE vs) xs
         else
           data_Assign n1 op vs xs
     else
       let k = op_space_req op (LENGTH vs) in
         if k = 0 then
           (if op = WordOp (WordTest W8 (Compare Gt)) then
              data_Assign n1 (WordOp (WordTest W8 (Compare Lt))) (REVERSE vs) NONE
            else if op = WordOp (WordTest W8 (Compare Geq)) then
              data_Assign n1 (WordOp (WordTest W8 (Compare Leq))) (REVERSE vs) NONE
            else
              data_Assign n1 op vs NONE)
         else data_Seq (MakeSpace k (list_to_num_set (APPEND (APPEND vs live) env)))
                       (data_Assign n1 op vs NONE)`;;

new_type_abbrev("WORDP3AUX_bcty",
  `:num->num list->bool->num list->bvi_exp list->data_prog#num list#num`);;

let bvi_to_data_compile_def = sem1aux_def_wf
  `measure (\(n:num,env:num list,tail:bool,live:num list,xs:bvi_exp list).
              list_size bvi_exp_size xs)`
  SEM1AUX_TC_TAC
  (list_mk_conj
  [`((bvi_to_data_compile:WORDP3AUX_bcty) n env tail live [] = (data_Skip,[],n))`;
   `((bvi_to_data_compile:WORDP3AUX_bcty) n env tail live (CONS x (CONS y xs)) =
      let (c1,v1,n1) = bvi_to_data_compile n env F live [x] in
      let (c2,vs,n2) = bvi_to_data_compile n1 env F (CONS (HD v1) live) (CONS y xs) in
        (data_Seq c1 c2,CONS (HD v1) vs,n2))`;
   `((bvi_to_data_compile:WORDP3AUX_bcty) n env tail live [bvi_Var v] =
      let var = any_el v env 0 in
      if tail
      then (data_Return [var],[n],n + 1)
      else (data_Skip,[var],MAX n (var + 1)))`;
   `((bvi_to_data_compile:WORDP3AUX_bcty) n env tail live [bvi_If x1 x2 x3] =
      let (c1,v1,n1) = bvi_to_data_compile n env F live [x1] in
      let (c2,v2,n2) = bvi_to_data_compile n1 env tail live [x2] in
      let (c3,v3,n3) = bvi_to_data_compile n2 env tail live [x3] in
        if tail then
          (data_Seq c1 (data_If (HD v1) c2 c3),[n3],n3 + 1)
        else
          (data_Seq c1 (data_If (HD v1) (data_Seq c2 (data_Move n3 (HD v2)))
                                        (data_Seq c3 (data_Move n3 (HD v3)))),
           [n3],n3 + 1))`;
   `((bvi_to_data_compile:WORDP3AUX_bcty) n env tail live [bvi_Let xs x2] =
      let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
      let (c2,v2,n2) = bvi_to_data_compile n1 (APPEND vs env) tail live [x2] in
        (data_Seq c1 c2,v2,n2))`;
   `((bvi_to_data_compile:WORDP3AUX_bcty) n env tail live [bvi_Raise x1] =
      let (c1,v1,n1) = bvi_to_data_compile n env F live [x1] in
        (data_Seq c1 (data_Raise (HD v1)),v1,n1))`;
   `((bvi_to_data_compile:WORDP3AUX_bcty) n env tail live [bvi_Return xs] =
      let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
        (data_Seq c1 (data_Return vs),[n1],n1 + 1))`;
   `((bvi_to_data_compile:WORDP3AUX_bcty) n env tail live [bvi_Op op xs] =
      let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
      let c2 = data_Seq c1 (iAssign n1 op (REVERSE vs) live env) in
        ((if tail then data_Seq c2 (data_Return [n1]) else c2),[n1],n1 + 1))`;
   `((bvi_to_data_compile:WORDP3AUX_bcty) n env tail live [bvi_Tick x1] =
      let (c1,v1,n1) = bvi_to_data_compile n env tail live [x1] in
        (data_Seq data_Tick c1,v1,n1))`;
   `((bvi_to_data_compile:WORDP3AUX_bcty) n env tail live [bvi_Force loc v] =
      let var = any_el v env 0 in
      let ret = (if tail then NONE
                 else SOME (n,list_to_num_set (APPEND live env))) in
        (data_Force ret loc var,[n],MAX (n + 1) (var + 1)))`;
   `((bvi_to_data_compile:WORDP3AUX_bcty) n env tail live [bvi_Call ticks dest xs NONE] =
      let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
      let ret = (if tail then NONE
                 else SOME ([n1],list_to_num_set (APPEND live env))) in
        (data_Seq c1 (mk_ticks ticks (data_Call ret dest vs NONE)),[n1],n1 + 1))`;
   `((bvi_to_data_compile:WORDP3AUX_bcty) n env tail live [bvi_Call ticks dest xs (SOME handler)] =
      let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
      let (c2,v,n2) = bvi_to_data_compile (n1 + 1) (CONS n1 env) F live [handler] in
      let ret = SOME ([n2],list_to_num_set (APPEND live env)) in
      let c3 = (if tail then data_Return [n2] else data_Skip) in
        (data_Seq c1 (mk_ticks ticks
           (data_Seq (data_Call ret dest vs (SOME (n1,data_Seq c2 (data_Move n2 (HD v)))))
                     c3)),[n2],n2 + 1))`;
   `((bvi_to_data_compile:WORDP3AUX_bcty) n env tail live [LetCall rets ticks dest xs y] =
      let (c1,vs,n1) = bvi_to_data_compile n env F live xs in
        if y = bvi_Return (list_of_seq bvi_Var rets) then
          (data_Seq c1 (mk_ticks ticks (data_Call NONE (SOME dest) vs NONE)),[n1],n1 + 1)
        else
          let rs = list_of_seq (\i. n1 + i) rets in
          let (c2,v,n2) = bvi_to_data_compile (n1 + rets) (APPEND rs env) tail live [y] in
          let ret = SOME (rs,list_to_num_set (APPEND live env)) in
            (data_Seq (data_Seq c1 (mk_ticks ticks (data_Call ret (SOME dest) vs NONE))) c2,
             v,n2))`]);;

remove_type_abbrev "WORDP3AUX_bcty";;

let bvi_to_data_compile_ind = cake_ind "bvi_to_data_compile";;

new_type_abbrev("WORDP3AUX_sty",
  `:num->num list->bool->num list->bvi_exp->data_prog#num#num`);;
new_type_abbrev("WORDP3AUX_lty",
  `:num->num list->num list->bvi_exp list->data_prog#num list#num`);;

let bvi_to_data_compile_sing_def = sem1aux_def_wf
  (CASE_TERM
   `measure (\x:(num#num list#bool#num list#bvi_exp)+(num#num list#num list#bvi_exp list).
      match x with
        INL (n,env,t,l,x) -> bvi_exp_size x
      | INR (n,env,l,xs) -> list_size bvi_exp_size xs)`)
  (REWRITE_TAC[measure_THM] THEN CASE_REWRITE_TAC[] THEN SEM1AUX_TC_TAC)
  (list_mk_conj
  [`((bvi_to_data_compile_sing:WORDP3AUX_sty) n env tail live (bvi_Var v) =
      let var = any_el v env 0 in
      if tail
      then (data_Return [var],n,n + 1)
      else (data_Skip,var,MAX n (var + 1)))`;
   `((bvi_to_data_compile_sing:WORDP3AUX_sty) n env tail live (bvi_If x1 x2 x3) =
      let (c1,v1,n1) = bvi_to_data_compile_sing n env F live x1 in
      let (c2,v2,n2) = bvi_to_data_compile_sing n1 env tail live x2 in
      let (c3,v3,n3) = bvi_to_data_compile_sing n2 env tail live x3 in
        if tail then
          (data_Seq c1 (data_If v1 c2 c3),n3,n3 + 1)
        else
          (data_Seq c1 (data_If v1 (data_Seq c2 (data_Move n3 v2))
                                   (data_Seq c3 (data_Move n3 v3))),n3,n3 + 1))`;
   `((bvi_to_data_compile_sing:WORDP3AUX_sty) n env tail live (bvi_Let xs x2) =
      let (c1,vs,n1) = (bvi_to_data_compile_list:WORDP3AUX_lty) n env live xs in
      let (c2,v2,n2) = bvi_to_data_compile_sing n1 (APPEND vs env) tail live x2 in
        (data_Seq c1 c2,v2,n2))`;
   `((bvi_to_data_compile_sing:WORDP3AUX_sty) n env tail live (bvi_Raise x1) =
      let (c1,v1,n1) = bvi_to_data_compile_sing n env F live x1 in
        (data_Seq c1 (data_Raise v1),v1,n1))`;
   `((bvi_to_data_compile_sing:WORDP3AUX_sty) n env tail live (bvi_Return xs) =
      let (c1,vs,n1) = (bvi_to_data_compile_list:WORDP3AUX_lty) n env live xs in
        (data_Seq c1 (data_Return vs),n1,n1 + 1))`;
   `((bvi_to_data_compile_sing:WORDP3AUX_sty) n env tail live (bvi_Op op xs) =
      let (c1,vs,n1) = (bvi_to_data_compile_list:WORDP3AUX_lty) n env live xs in
      let c2 = data_Seq c1 (iAssign n1 op (REVERSE vs) live env) in
        ((if tail then data_Seq c2 (data_Return [n1]) else c2),n1,n1 + 1))`;
   `((bvi_to_data_compile_sing:WORDP3AUX_sty) n env tail live (bvi_Tick x1) =
      let (c1,v1,n1) = bvi_to_data_compile_sing n env tail live x1 in
        (data_Seq data_Tick c1,v1,n1))`;
   `((bvi_to_data_compile_sing:WORDP3AUX_sty) n env tail live (bvi_Force loc v) =
      let var = any_el v env 0 in
      let ret = (if tail then NONE
                 else SOME (n,list_to_num_set (APPEND live env))) in
        (data_Force ret loc var,n,MAX (n + 1) (var + 1)))`;
   `((bvi_to_data_compile_sing:WORDP3AUX_sty) n env tail live (bvi_Call ticks dest xs NONE) =
      let (c1,vs,n1) = (bvi_to_data_compile_list:WORDP3AUX_lty) n env live xs in
      let ret = (if tail then NONE
                 else SOME ([n1],list_to_num_set (APPEND live env))) in
        (data_Seq c1 (mk_ticks ticks (data_Call ret dest vs NONE)),n1,n1 + 1))`;
   `((bvi_to_data_compile_sing:WORDP3AUX_sty) n env tail live (bvi_Call ticks dest xs (SOME handler)) =
      let (c1,vs,n1) = (bvi_to_data_compile_list:WORDP3AUX_lty) n env live xs in
      let (c2,v,n2) = bvi_to_data_compile_sing (n1 + 1) (CONS n1 env) F live handler in
      let ret = SOME ([n2],list_to_num_set (APPEND live env)) in
      let c3 = (if tail then data_Return [n2] else data_Skip) in
        (data_Seq c1 (mk_ticks ticks
           (data_Seq (data_Call ret dest vs (SOME (n1,data_Seq c2 (data_Move n2 v)))) c3)),
         n2,n2 + 1))`;
   `((bvi_to_data_compile_sing:WORDP3AUX_sty) n env tail live (LetCall rets ticks dest xs y) =
      let (c1,vs,n1) = (bvi_to_data_compile_list:WORDP3AUX_lty) n env live xs in
        if y = bvi_Return (list_of_seq bvi_Var rets) then
          (data_Seq c1 (mk_ticks ticks (data_Call NONE (SOME dest) vs NONE)),n1,n1 + 1)
        else
          let rs = list_of_seq (\i. n1 + i) rets in
          let (c2,v,n2) = bvi_to_data_compile_sing (n1 + rets) (APPEND rs env) tail live y in
          let ret = SOME (rs,list_to_num_set (APPEND live env)) in
            (data_Seq (data_Seq c1 (mk_ticks ticks (data_Call ret (SOME dest) vs NONE))) c2,
             v,n2))`;
   `((bvi_to_data_compile_list:WORDP3AUX_lty) n env live [] = (data_Skip,[],n))`;
   `((bvi_to_data_compile_list:WORDP3AUX_lty) n env live (CONS x xs) =
      let (c1,v1,n1) = (bvi_to_data_compile_sing:WORDP3AUX_sty) n env F live x in
        if NULL xs then (c1,[v1],n1) else
          let (c2,vs,n2) = bvi_to_data_compile_list n1 env (CONS v1 live) xs in
            (data_Seq c1 c2,CONS v1 vs,n2))`]);;

remove_type_abbrev "WORDP3AUX_sty";;
remove_type_abbrev "WORDP3AUX_lty";;

let bvi_to_data_compile_sing_ind = cake_ind "bvi_to_data_compile_sing";;

(* tactics for the proof of compile_sing_eq (HOL4: rw, once_rewrite_tac,  *)
(* pairarg_tac, gvs, IF_CASES_TAC): WORDP3AUX_PAIRARG_ANT_TAC is the kit's *)
(* PAIRARG_TAC for a pair_CASE of the antecedent of the goal              *)

let WORDP3AUX_PAIRARG_ANT_TAC : tactic =
  fun (asl,w as gl) ->
    let ant = fst (dest_imp w) in
    let whole = list_mk_conj(w :: map (concl o snd) asl) in
    let is_cand t =
      is_case_app t &&
      (let c,x,fs = dest_case_app t in
       fst(dest_const c) = "pair_CASE" && not (is_pair x) &&
       free_in x whole) in
    let t = find_term is_cand ant in
    let _,x,fs = dest_case_app t in
    let f = hd fs in
    let tya,tyb = match dest_type(type_of x) with
        "prod",[a;b] -> a,b | _ -> failwith "WORDP3AUX_PAIRARG_ANT_TAC" in
    let n1,n2 =
      try let a,b = dest_abs f in let b1,_ = dest_abs b in
          fst(dest_var a),fst(dest_var b1)
      with Failure _ -> "p1","p2" in
    let avoid = frees whole in
    let v1 = variant avoid (mk_var(n1,tya)) in
    let v2 = variant (v1::avoid) (mk_var(n2,tyb)) in
    let nch = ISPEC x (nchotomy_of_type (type_of x)) in
    (MP_TAC nch THEN
     DISCH_THEN(X_CHOOSE_THEN v1 (X_CHOOSE_THEN v2
       (fun th -> if is_var x then SUBST_ALL_TAC th
                  else SUBST_ALL_TAC th THEN ASSUME_TAC th))) THEN
     CASE_ASM_TIDY_TAC THEN CASE_REWRITE_TAC[]) gl;;

let WORDP3AUX_head_is c t =
  try let h = repeat rator t in is_const h && fst (dest_const h) = c
  with Failure _ -> false;;

(* a case of compile_sing: unfold compile_sing in the assumption and       *)
(* compile in the goal, replace compile_list by compile (the induction     *)
(* hypothesis), split the results of the recursive calls                   *)

let WORDP3AUX_SING_TAC =
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o
    check (fun th -> is_eq (concl th) &&
                     WORDP3AUX_head_is "bvi_to_data_compile_sing" (lhs (concl th)))) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [bvi_to_data_compile_sing_def] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [bvi_to_data_compile_def] THEN
  REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o
    check (fun th -> is_eq (concl th) &&
                     WORDP3AUX_head_is "bvi_to_data_compile_list" (lhs (concl th))))) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ]) THEN
  REPEAT WORDP3AUX_PAIRARG_ANT_TAC THEN
  GVS[] THEN REWRITE_TAC[HD] THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[PAIR_EQ; CONS_11] THEN REPEAT STRIP_TAC THEN GVS[];;

(* LetCall: the induction hypothesis holds for every list rs              *)

let WORDP3AUX_LETCALL_TAC =
  WORDP3AUX_SING_TAC THEN
  FIRST_X_ASSUM (fun ih -> FIRST_ASSUM (fun eq -> MP_TAC (MATCH_MP ih eq))) THEN
  DISCH_THEN SUBST1_TAC THEN CASE_REWRITE_TAC[];;

let WORDP3AUX_NIL_TAC =
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [bvi_to_data_compile_sing_def] THEN
  GEN_REWRITE_TAC RAND_CONV [bvi_to_data_compile_def] THEN REFL_TAC;;

let WORDP3AUX_CONS_TAC =
  REPEAT GEN_TAC THEN
  (fun (asl,w as gl) ->
     let xs = rand (rand (lhs (rand w))) in
     STRUCT_CASES_TAC (ISPEC xs list_CASES) gl) THEN
  REWRITE_TAC[NULL] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ]) THEN
  GEN_REWRITE_TAC LAND_CONV [bvi_to_data_compile_sing_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF; NULL] THEN CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
  PAIRARG_TAC THEN PAIRARG_TAC THEN GVS[] THEN
  TRY (GEN_REWRITE_TAC RAND_CONV [bvi_to_data_compile_def] THEN
       REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC (TOP_DEPTH_CONV BETA_CONV) THEN
       GVS[HD]);;

(* HOL4: compile_sing_eq *)

let bvi_to_data_compile_sing_eq = prove
 (`(!n env t l x c1 v1 n1.
      bvi_to_data_compile_sing n env t l x = (c1,v1,n1) ==>
      bvi_to_data_compile n env t l [x] = (c1,[v1],n1)) /\
   (!n env l xs.
      bvi_to_data_compile_list n env l xs = bvi_to_data_compile n env F l xs)`,
  MATCH_MP_TAC bvi_to_data_compile_sing_ind THEN REPEAT CONJ_TAC THENL
   (replicate WORDP3AUX_SING_TAC 10 @
    [WORDP3AUX_LETCALL_TAC; WORDP3AUX_NIL_TAC; WORDP3AUX_CONS_TAC]));;

(* the induction step of compile_LESS_EQ_lemma and compile_LENGTH_lemma:  *)
(* unfold compile, split the results of the recursive calls and the ifs   *)
(* (the hypothesis of the LetCall case holds for every list rs)           *)

let WORDP3AUX_IND_STEP_TAC fin =
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[bvi_to_data_compile_def] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT PAIRARG_TAC THEN GVS[] THEN
  REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN GVS[] THEN
  TRY (FIRST_X_ASSUM (MP_TAC o SPEC `list_of_seq (\i. n1 + i) rets`) THEN
       ASM_REWRITE_TAC[]) THEN
  fin;;

(* HOL4: compile_LESS_EQ_lemma [local] *)

let compile_LESS_EQ_lemma = prove
 (`!n env tail live xs.
     n <= SND (SND (bvi_to_data_compile n env tail live xs))`,
  MATCH_MP_TAC bvi_to_data_compile_ind THEN REPEAT CONJ_TAC THEN
  WORDP3AUX_IND_STEP_TAC ASM_ARITH_TAC);;

let compile_LESS_EQ = prove
 (`!n env tail live xs c vs new_var.
     bvi_to_data_compile n env tail live xs = (c,vs,new_var) ==> n <= new_var`,
  REPEAT STRIP_TAC THEN MP_TAC (SPEC_ALL compile_LESS_EQ_lemma) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4: compile_LENGTH_lemma [local] *)

let compile_LENGTH_lemma = prove
 (`!n env tail live xs.
     LENGTH (FST (SND (bvi_to_data_compile n env tail live xs))) = LENGTH xs`,
  MATCH_MP_TAC bvi_to_data_compile_ind THEN REPEAT CONJ_TAC THEN
  WORDP3AUX_IND_STEP_TAC (ASM_REWRITE_TAC[LENGTH]));;

let bvi_to_data_compile_LENGTH = prove
 (`!n env tail live xs c vs new_var.
     bvi_to_data_compile n env tail live xs = (c,vs,new_var)
     ==> LENGTH vs = LENGTH xs`,
  REPEAT STRIP_TAC THEN MP_TAC (SPEC_ALL compile_LENGTH_lemma) THEN
  ASM_REWRITE_TAC[]);;

let compile_SING_IMP = prove
 (`bvi_to_data_compile n env tail live [x] = (c,vs,new_var) ==> ?t. vs = [t]`,
  DISCH_THEN (MP_TAC o MATCH_MP bvi_to_data_compile_LENGTH) THEN
  REWRITE_TAC[LENGTH; LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN MESON_TAC[]);;

(* combine dataLang optimisations *)

let bvi_to_data_optimise_def = cake_def
  `bvi_to_data_optimise prog =
     data_space_compile (simp (FST (data_live_compile prog LN)) data_Skip)`;;

(* the top-level compiler includes the optimisations, because the           *)
(* correctness proofs are combined                                          *)

let bvi_to_data_compile_exp_def = cake_def
  `bvi_to_data_compile_exp arg_count exp =
     bvi_to_data_optimise
       (FST (bvi_to_data_compile arg_count (COUNT_LIST arg_count) T [] [exp]))`;;

let bvi_to_data_compile_part_def = cake_def
  `bvi_to_data_compile_part (name:num,arg_count,exp) =
     (name,arg_count,bvi_to_data_compile_exp arg_count exp)`;;

let bvi_to_data_compile_prog_def = cake_def
  `bvi_to_data_compile_prog prog = MAP bvi_to_data_compile_part prog`;;

let bvi_to_data_compile_exp_eq = prove
 (`bvi_to_data_compile_exp arg_count exp =
     bvi_to_data_optimise
       (FST (bvi_to_data_compile_sing arg_count (COUNT_LIST arg_count) T [] exp))`,
  SUBGOAL_THEN `?c v k. bvi_to_data_compile_sing arg_count (COUNT_LIST arg_count) T [] exp =
                        (c,v,k)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  FIRST_ASSUM (MP_TAC o MATCH_MP (CONJUNCT1 bvi_to_data_compile_sing_eq)) THEN
  ASM_REWRITE_TAC[bvi_to_data_compile_exp_def] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[]);;
