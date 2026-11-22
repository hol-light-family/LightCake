(* ========================================================================= *)
(* pan_simp: port of HOL4 pancake/pan_simpScript.sml (CakeML v3479).         *)
(* Simplification of panLang.                                                *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "pancake/panLang.ml";;
needs "compiler/backend/backend_common.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Notes on the rendering:                                                   *)
(* - Names as notes/naming/names.tsv says: pan_simp_SmartSeq (word_simp has  *)
(*   SmartSeq), pan_simp_compile, pan_simp_compile_prog; the panLang         *)
(*   constructors with their panLang_ names.                                 *)
(* - HOL4 Overloads: TailCall = Call NONE, AssignCall s h = Call (SOME (SOME *)
(*   s,h)); r with f := v is RECTYPE_f_fupd (K v) r, r.f is RECTYPE_f r.     *)
(* - Definitions with catch-all clauses over prog are made with sem1aux_def  *)
(*   (HOL4's TFL completion, semantics/sem1aux_tfl.ml).  A clause in which   *)
(*   a variable has another type than in the other clauses (e is an exp in   *)
(*   Dec and a funname in DecCall) is parsed on its own.                     *)
(* - HOL4's pmatch case expressions are written with match like all others, *)
(*   so the NAME_pmatch theorems restate the definitions in match form.      *)
(* ------------------------------------------------------------------------- *)

(* HOL4: SmartSeq_def [simp] *)

let pan_simp_SmartSeq_def = cake_def
  `pan_simp_SmartSeq p (q:(A)panLang_prog) =
     if p = panLang_Skip then q else panLang_Seq p q`;;

let _ = cake_add_simps [pan_simp_SmartSeq_def];;

let seq_assoc_def = sem1aux_def
  (list_mk_conj
   [`(seq_assoc p (panLang_Skip:(A)panLang_prog) = p) /\
     (seq_assoc p (Dec v s e q) =
        pan_simp_SmartSeq p (Dec v s e (seq_assoc panLang_Skip q))) /\
     (seq_assoc p (panLang_Seq q r) = seq_assoc (seq_assoc p q) r) /\
     (seq_assoc p (panLang_If e q r) =
        pan_simp_SmartSeq p
          (panLang_If e (seq_assoc panLang_Skip q) (seq_assoc panLang_Skip r))) /\
     (seq_assoc p (While e q) =
        pan_simp_SmartSeq p (While e (seq_assoc panLang_Skip q))) /\
     (seq_assoc p (panLang_Call NONE name args) =
        pan_simp_SmartSeq p (panLang_Call NONE name args)) /\
     (seq_assoc p (panLang_Call (SOME (rv,exp)) name args) =
        pan_simp_SmartSeq p
          (panLang_Call
             (match exp with
                NONE -> SOME (rv,NONE)
              | SOME (eid,ev,ep) ->
                  SOME (rv,SOME (eid,ev,seq_assoc panLang_Skip ep)))
             name args))`;
    `seq_assoc p (DecCall v s e es (q:(A)panLang_prog)) =
       pan_simp_SmartSeq p (DecCall v s e es (seq_assoc panLang_Skip q))`;
    `(seq_assoc p (Annot _ _:(A)panLang_prog) = p) /\
     (seq_assoc p q = pan_simp_SmartSeq p q)`]);;

let seq_assoc_ind = cake_ind "seq_assoc";;

let seq_call_ret_def = cake_def
  `seq_call_ret (prog:(A)panLang_prog) =
     match prog with
       panLang_Seq
         (panLang_Call (SOME (SOME (panLang_Local,rv1),NONE)) trgt args)
         (panLang_Return (panLang_Var panLang_Local rv2)) ->
         if rv1 = rv2 then panLang_Call NONE trgt args else prog
     | other -> other`;;

let ret_to_tail_def = sem1aux_def
  (list_mk_conj
   [`(ret_to_tail (panLang_Skip:(A)panLang_prog) = panLang_Skip) /\
     (ret_to_tail (Dec v s e q) = Dec v s e (ret_to_tail q)) /\
     (ret_to_tail (panLang_Seq p q) =
        seq_call_ret (panLang_Seq (ret_to_tail p) (ret_to_tail q))) /\
     (ret_to_tail (panLang_If e p q) =
        panLang_If e (ret_to_tail p) (ret_to_tail q)) /\
     (ret_to_tail (While e p) = While e (ret_to_tail p)) /\
     (ret_to_tail (panLang_Call NONE name args) = panLang_Call NONE name args) /\
     (ret_to_tail (panLang_Call (SOME (rv,exp)) name args) =
        panLang_Call
          (SOME (rv,(match exp with
                       NONE -> NONE
                     | SOME (eid,ev,ep) -> SOME (eid,ev,ret_to_tail ep))))
          name args)`;
    `ret_to_tail (DecCall v s e es (q:(A)panLang_prog)) =
       DecCall v s e es (ret_to_tail q)`;
    `ret_to_tail (p:(A)panLang_prog) = p`]);;

let ret_to_tail_ind = cake_ind "ret_to_tail";;

let pan_simp_compile_def = cake_def
  `pan_simp_compile (p:(A)panLang_prog) =
     let p = seq_assoc panLang_Skip p in
     ret_to_tail p`;;

let pan_simp_compile_prog_def = cake_def
  `pan_simp_compile_prog (prog:((A)decl)list) =
     MAP (\decl. match decl with
                   Function fi ->
                     Function (fun_decl_body_fupd
                                 (K (pan_simp_compile (fun_decl_body fi))) fi)
                 | _ -> decl) prog`;;

(* HOL4 proves the pmatch forms with PMATCH_ELIM_CONV; here match is      *)
(* compiled into case constants, so they are case splits of the clauses.   *)

let seq_assoc_pmatch = prove
 (CASE_TERM
  `!p (prog:(A)panLang_prog).
     seq_assoc p prog =
     match prog with
       panLang_Skip -> p
     | Dec v s e q -> pan_simp_SmartSeq p (Dec v s e (seq_assoc panLang_Skip q))
     | panLang_Seq q r -> seq_assoc (seq_assoc p q) r
     | panLang_If e q r ->
         pan_simp_SmartSeq p
           (panLang_If e (seq_assoc panLang_Skip q) (seq_assoc panLang_Skip r))
     | While e q -> pan_simp_SmartSeq p (While e (seq_assoc panLang_Skip q))
     | panLang_Call rtyp name args ->
         pan_simp_SmartSeq p
           (panLang_Call
              (match rtyp with
                 NONE -> NONE
               | SOME (rv,NONE) -> SOME (rv,NONE)
               | SOME (rv,SOME (eid,ev,ep)) ->
                   SOME (rv,SOME (eid,ev,seq_assoc panLang_Skip ep)))
              name args)
     | DecCall v s e es q ->
         pan_simp_SmartSeq p (DecCall v s e es (seq_assoc panLang_Skip q))
     | Annot _ _ -> p
     | q -> pan_simp_SmartSeq p q`,
  GEN_TAC THEN GEN_TAC THEN CASES_ON `prog:(A)panLang_prog` THEN
  CASE_REWRITE_TAC[seq_assoc_def] THEN
  REPEAT(TOP_CASE_TAC THEN CASE_REWRITE_TAC[seq_assoc_def]));;

let ret_to_tail_pmatch = prove
 (CASE_TERM
  `!p:(A)panLang_prog.
     ret_to_tail p =
     match p with
       panLang_Skip -> panLang_Skip
     | Dec v s e q -> Dec v s e (ret_to_tail q)
     | panLang_Seq q r -> seq_call_ret (panLang_Seq (ret_to_tail q) (ret_to_tail r))
     | panLang_If e q r -> panLang_If e (ret_to_tail q) (ret_to_tail r)
     | While e q -> While e (ret_to_tail q)
     | panLang_Call rtyp name args ->
         panLang_Call
           (match rtyp with
              NONE -> NONE
            | SOME (rv,NONE) -> SOME (rv,NONE)
            | SOME (rv,SOME (eid,ev,ep)) -> SOME (rv,SOME (eid,ev,ret_to_tail ep)))
           name args
     | DecCall v s e es q -> DecCall v s e es (ret_to_tail q)
     | p -> p`,
  GEN_TAC THEN CASES_ON `p:(A)panLang_prog` THEN
  CASE_REWRITE_TAC[ret_to_tail_def] THEN
  REPEAT(TOP_CASE_TAC THEN CASE_REWRITE_TAC[ret_to_tail_def]));;

let compile_prog_pmatch = prove
 (CASE_TERM
  `pan_simp_compile_prog (prog:((A)decl)list) =
     MAP (\decl. match decl with
                   Function fi ->
                     Function (fun_decl_body_fupd
                                 (K (pan_simp_compile (fun_decl_body fi))) fi)
                 | _ -> decl) prog`,
  REWRITE_TAC[pan_simp_compile_prog_def]);;
