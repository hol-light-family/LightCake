(* ========================================================================= *)
(* pan_structs: port of HOL4 pancake/pan_structsScript.sml (CakeML v3479).   *)
(* Convert named structs to raw structs.                                     *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: the record type                            *)
(*   pan_structs_context (HOL4 context) with the fields                      *)
(*   pan_structs_context_structs, _locals and _globals;                      *)
(*   pan_structs_compile_exp, _compile_exps, _compile, _compile_decs and     *)
(*   _compile_top; the panLang constructors with their panLang_ names.       *)
(* - HOL4's paired lambdas (\(n,fs). t) are written                          *)
(*   (\p. match p with (n,fs) -> t).                                         *)
(* - r.f is RECTYPE_f r; r with f := v is RECTYPE_f_fupd (K v) r; HOL4      *)
(*   r with <| f1 updated_by g1; f2 updated_by g2 |> is                     *)
(*   RECTYPE_f1_fupd g1 (RECTYPE_f2_fupd g2 r) (the first update outermost, *)
(*   as HOL4's parser builds it); the literal <| f1 := v1; .. |> with every *)
(*   field is RECTYPE_REC v1 ...                                             *)
(* - LLOOKUP l n is oEL n l (misc); dropWhile is HOL4's (hol4/libext.ml).    *)
(* - Definitions with catch-all clauses are made with sem1aux_def(_wf)       *)
(*   (HOL4's TFL completion, semantics/sem1aux_tfl.ml).  A clause in which   *)
(*   a variable has another type than in the other clauses is parsed on its *)
(*   own (sh is a shape in Load and a shift in Shift; v is a varname in Dec *)
(*   and an exp in Store; r is an exp in ShMemStore and a varname in         *)
(*   ShMemLoad).                                                             *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "hol4/libext.ml";;
needs "pancake/panLang.ml";;
needs "compiler/backend/backend_common.ml";;

prioritize_num();;
type_invention_error := true;;

(* Context of shapes before conversion *)

let pan_structs_context_INFO = cake_record "pan_structs_context"
  ["structs","(stcname#((fldname#shape)list))list";
   "locals","(varname#shape)list";
   "globals","(varname#shape)list"];;

let pan_structs_context_component_equality =
  (record_info "pan_structs_context").ri_component_equality;;

(* Return index of x in alist *)

let afindi_def = cake_def
  `(afindi (x:A) ([]:(A#B)list) = NONE:num option) /\
   (afindi x (CONS (k,v) t) =
      if x = k then SOME 0
      else match afindi x t with
             NONE -> NONE
           | SOME i -> SOME (1 + i))`;;

(* Replace named struct shapes with raw structs *)

(* the termination tactic (HOL4: rw[] >> disj1_tac >> irule              *)
(* LESS_LESS_EQ_TRANS >> irule_at Any LENGTH_dropWhile_LESS_EQ >> ...):    *)
(* for a context dropWhile P l = t, the fact LENGTH t <= LENGTH l, then    *)
(* the kit's TERM_TAC                                                      *)

let PPASS1AUX_DROPWHILE_TAC : tactic =
  fun (asl,w as g) ->
    let is_dw t = try fst(dest_const(fst(strip_comb t))) = "dropWhile"
                  with Failure _ -> false in
    let fact th =
      let c = concl th in
      if not (is_eq c) then failwith "" else
      let th' = if is_dw (lhs c) then th else if is_dw (rhs c) then SYM th
                else failwith "" in
      match snd(strip_comb(lhs(concl th'))) with
        [p;l] -> REWRITE_RULE[th'; LENGTH] (ISPECL [p;l] LENGTH_dropWhile_LESS_EQ)
      | _ -> failwith "" in
    MAP_EVERY ASSUME_TAC (mapfilter (fact o snd) asl) g;;

let PPASS1AUX_SHAPE_TC_TAC : tactic =
  REPEAT BOSS_STRIP_TAC THEN PPASS1AUX_DROPWHILE_TAC THEN TERM_TAC;;

let compile_shape_def = cake_def_wf
  `inv_image
     (MEASURE LENGTH LEX
      MEASURE (\x. sum_CASE x (\sh:shape. shape_size sh)
                              (\shs. list_size shape_size shs)))
     (\x. sum_CASE x
            (\p:(stcname#((B#shape)list))list#shape. FST p,INL (SND p))
            (\q:(stcname#((B#shape)list))list#(shape list).
               FST q,INR (SND q)))`
  PPASS1AUX_SHAPE_TC_TAC
  `(compile_shape (sctxt:(stcname#((B#shape)list))list) One = One) /\
   (compile_shape sctxt (Comb shapes) = Comb (compile_shapes sctxt shapes)) /\
   (compile_shape sctxt (Named nm) =
      match dropWhile (\p. match p with (n,fs) -> ~(n = nm)) sctxt with
        CONS (nm,flds) sctxt' -> Comb (compile_shapes sctxt' (MAP SND flds))
      | _ -> One) /\
   (compile_shapes sctxt [] = []) /\
   (compile_shapes sctxt (CONS sh shs) =
      CONS (compile_shape sctxt sh) (compile_shapes sctxt shs))`;;

let compile_shape_ind = cake_ind "compile_shape";;

(* Returns unconverted shape of an expression *)

let old_exp_shape_def = sem1aux_def_wf
  `MEASURE (\x. sum_CASE x
                  (\p:pan_structs_context#(A)panLang_exp.
                     panLang_exp_size ARB (SND p))
                  (\q:pan_structs_context#((A)panLang_exp)list.
                     list_size (panLang_exp_size ARB) (SND q)))`
  SEM1AUX_TC_TAC
  `(old_exp_shape ctxt (panLang_Var panLang_Local v:(A)panLang_exp) =
      match ALOOKUP (pan_structs_context_locals ctxt) v with
        NONE -> One
      | SOME sh -> sh) /\
   (old_exp_shape ctxt (panLang_Var panLang_Global v) =
      match ALOOKUP (pan_structs_context_globals ctxt) v with
        NONE -> One
      | SOME sh -> sh) /\
   (old_exp_shape ctxt (RStruct es) = Comb (old_exp_shapes ctxt es)) /\
   (old_exp_shape ctxt (RField index e) =
      match old_exp_shape ctxt e with
        Comb shs -> (match oEL index shs with
                       SOME sh -> sh
                     | NONE -> One)
      | _ -> One) /\
   (old_exp_shape ctxt (NStruct nm eflds) = Named nm) /\
   (old_exp_shape ctxt (NField fld e) =
      match old_exp_shape ctxt e with
        Named nm ->
          (match ALOOKUP (pan_structs_context_structs ctxt) nm with
             SOME flds -> (match ALOOKUP flds fld with
                             SOME sh -> sh
                           | NONE -> One)
           | NONE -> One)
      | _ -> One) /\
   (old_exp_shape ctxt (panLang_Load sh e) = sh) /\
   (old_exp_shape ctxt _ = One) /\
   (old_exp_shapes ctxt [] = []) /\
   (old_exp_shapes ctxt (CONS e es) =
      CONS (old_exp_shape ctxt e) (old_exp_shapes ctxt es))`;;

(* Returns converted expression *)

let pan_structs_compile_exp_def = sem1aux_def_wf
  `MEASURE (\x. sum_CASE x
                  (\p:pan_structs_context#(A)panLang_exp.
                     panLang_exp_size ARB (SND p))
                  (\y. sum_CASE y
                         (\q:pan_structs_context#((A)panLang_exp)list.
                            list_size (panLang_exp_size ARB) (SND q))
                         (\r:pan_structs_context#((fldname#(A)panLang_exp)list).
                            list_size (pair_size mlstring_size (panLang_exp_size ARB))
                                      (SND r))))`
  SEM1AUX_TC_TAC
  (list_mk_conj
   [`(pan_structs_compile_exp ctxt (RStruct es:(A)panLang_exp) =
        RStruct (pan_structs_compile_exps ctxt es):(A)panLang_exp) /\
     (pan_structs_compile_exp ctxt (RField index e) =
        RField index (pan_structs_compile_exp ctxt e)) /\
     (pan_structs_compile_exp ctxt (NStruct nm eflds) =
        let eflds' = compile_fields ctxt eflds in
        let es' = match ALOOKUP (pan_structs_context_structs ctxt) nm with
                    SOME flds ->
                      FLAT (MAP (\p. match p with
                                       (nm',sh) ->
                                         (match ALOOKUP eflds' nm' with
                                            NONE -> []
                                          | SOME e -> [e])) flds)
                  | NONE -> [] in
        RStruct es') /\
     (pan_structs_compile_exp ctxt (NField fld e) =
        let e' = pan_structs_compile_exp ctxt e in
        let index =
          (match old_exp_shape ctxt e with
             Named nm ->
               (match ALOOKUP (pan_structs_context_structs ctxt) nm with
                  SOME flds -> (match afindi fld flds with
                                  SOME i -> i
                                | NONE -> 0)
                | NONE -> 0)
           | _ -> 0) in
        RField index e') /\
     (pan_structs_compile_exp ctxt (panLang_Load sh e) =
        panLang_Load (compile_shape (pan_structs_context_structs ctxt) sh)
                     (pan_structs_compile_exp ctxt e)) /\
     (pan_structs_compile_exp ctxt (LoadByte e) =
        LoadByte (pan_structs_compile_exp ctxt e)) /\
     (pan_structs_compile_exp ctxt (panLang_Load32 e) =
        panLang_Load32 (pan_structs_compile_exp ctxt e)) /\
     (pan_structs_compile_exp ctxt (panLang_Op bop es) =
        panLang_Op bop (pan_structs_compile_exps ctxt es)) /\
     (pan_structs_compile_exp ctxt (Panop pop es) =
        Panop pop (pan_structs_compile_exps ctxt es)) /\
     (pan_structs_compile_exp ctxt (Cmp cmp e1 e2) =
        Cmp cmp (pan_structs_compile_exp ctxt e1)
                (pan_structs_compile_exp ctxt e2))`;
    `pan_structs_compile_exp (ctxt:pan_structs_context)
       (panLang_Shift sh e e':(A)panLang_exp) =
       panLang_Shift sh (pan_structs_compile_exp ctxt e)
                        (pan_structs_compile_exp ctxt e'):(A)panLang_exp`;
    `(pan_structs_compile_exp (ctxt:pan_structs_context) (e:(A)panLang_exp) = e) /\
     (pan_structs_compile_exps ctxt [] = []:((A)panLang_exp)list) /\
     (pan_structs_compile_exps ctxt (CONS e es) =
        CONS (pan_structs_compile_exp ctxt e)
             (pan_structs_compile_exps ctxt es)) /\
     (compile_fields ctxt [] = []) /\
     (compile_fields ctxt (CONS (fld:fldname,exp) eflds) =
        CONS (fld,pan_structs_compile_exp ctxt exp)
             (compile_fields ctxt eflds))`]);;

let pan_structs_compile_exp_ind = cake_ind "pan_structs_compile_exp";;

(* Returns converted statement *)

let pan_structs_compile_def = sem1aux_def_wf
  `MEASURE (\p:pan_structs_context#(A)panLang_prog.
              panLang_prog_size ARB (SND p))`
  SEM1AUX_TC_TAC
  (list_mk_conj
   [`(pan_structs_compile ctxt (Dec v s e p:(A)panLang_prog) =
        Dec v
          (compile_shape (pan_structs_context_structs ctxt) s)
          (pan_structs_compile_exp ctxt e)
          (pan_structs_compile
             (pan_structs_context_locals_fupd
                (K (CONS (v,s) (pan_structs_context_locals ctxt))) ctxt) p):
        (A)panLang_prog) /\
     (pan_structs_compile ctxt (panLang_Assign vk v e) =
        panLang_Assign vk v (pan_structs_compile_exp ctxt e)) /\
     (pan_structs_compile ctxt (Primitive v pop es) =
        Primitive v pop (pan_structs_compile_exps ctxt es))`;
    `(pan_structs_compile (ctxt:pan_structs_context)
        (panLang_Store ad v:(A)panLang_prog) =
        panLang_Store (pan_structs_compile_exp ctxt ad)
                      (pan_structs_compile_exp ctxt v):(A)panLang_prog) /\
     (pan_structs_compile ctxt (panLang_Store32 ad v) =
        panLang_Store32 (pan_structs_compile_exp ctxt ad)
                        (pan_structs_compile_exp ctxt v))`;
    `(pan_structs_compile (ctxt:pan_structs_context)
        (StoreByte dest src:(A)panLang_prog) =
        StoreByte (pan_structs_compile_exp ctxt dest)
                  (pan_structs_compile_exp ctxt src):(A)panLang_prog) /\
     (pan_structs_compile ctxt (panLang_Seq p p') =
        panLang_Seq (pan_structs_compile ctxt p) (pan_structs_compile ctxt p')) /\
     (pan_structs_compile ctxt (panLang_If e p p') =
        panLang_If (pan_structs_compile_exp ctxt e) (pan_structs_compile ctxt p)
                   (pan_structs_compile ctxt p')) /\
     (pan_structs_compile ctxt (While e p) =
        While (pan_structs_compile_exp ctxt e) (pan_structs_compile ctxt p)) /\
     (pan_structs_compile ctxt (panLang_Call rtyp f es) =
        let cexps = pan_structs_compile_exps ctxt es in
        match rtyp with
          NONE -> panLang_Call NONE f cexps
        | SOME (tl,hdl) ->
            panLang_Call
              (SOME (tl,
                     match hdl with
                       NONE -> NONE
                     | SOME (eid,evar,p) ->
                         SOME (eid,evar,pan_structs_compile ctxt p)))
              f cexps) /\
     (pan_structs_compile ctxt (DecCall v s f es p) =
        DecCall v
          (compile_shape (pan_structs_context_structs ctxt) s) f
          (pan_structs_compile_exps ctxt es)
          (pan_structs_compile
             (pan_structs_context_locals_fupd
                (K (CONS (v,s) (pan_structs_context_locals ctxt))) ctxt) p)) /\
     (pan_structs_compile ctxt (panLang_ExtCall f ptr1 len1 ptr2 len2) =
        panLang_ExtCall f
          (pan_structs_compile_exp ctxt ptr1)
          (pan_structs_compile_exp ctxt len1)
          (pan_structs_compile_exp ctxt ptr2)
          (pan_structs_compile_exp ctxt len2)) /\
     (pan_structs_compile ctxt (panLang_Return rt) =
        panLang_Return (pan_structs_compile_exp ctxt rt)) /\
     (pan_structs_compile ctxt (panLang_Raise eid excp) =
        panLang_Raise eid (pan_structs_compile_exp ctxt excp))`;
    `pan_structs_compile (ctxt:pan_structs_context)
       (ShMemStore op r ad:(A)panLang_prog) =
       ShMemStore op (pan_structs_compile_exp ctxt r)
                  (pan_structs_compile_exp ctxt ad):(A)panLang_prog`;
    `pan_structs_compile (ctxt:pan_structs_context)
       (ShMemLoad op vk r ad:(A)panLang_prog) =
       ShMemLoad op vk r (pan_structs_compile_exp ctxt ad):(A)panLang_prog`;
    `pan_structs_compile (_:pan_structs_context) (p:(A)panLang_prog) = p`]);;

let pan_structs_compile_ind = cake_ind "pan_structs_compile";;

(* Returns converted declaration - Names are removed *)

let pan_structs_compile_decs_def = cake_def
  `(pan_structs_compile_decs ctxt ([]:((A)decl)list) = ([]:((A)decl)list,ctxt)) /\
   (pan_structs_compile_decs ctxt (CONS (Decl sh v e) ds) =
      let (ds',ctxt') =
        pan_structs_compile_decs
          (pan_structs_context_globals_fupd
             (K (CONS (v,sh) (pan_structs_context_globals ctxt))) ctxt) ds in
      (CONS (Decl (compile_shape (pan_structs_context_structs ctxt) sh) v
                  (pan_structs_compile_exp ctxt e)) ds',
       ctxt')) /\
   (pan_structs_compile_decs ctxt (CONS (Function fi) ds) =
      let (ds',ctxt') = pan_structs_compile_decs ctxt ds in
      let params = fun_decl_params fi in
      let fi' =
        fun_decl_params_fupd
          (MAP (\q. match q with
                      (p,s) -> (p,compile_shape (pan_structs_context_structs ctxt) s)))
          (fun_decl_body_fupd
             (pan_structs_compile (pan_structs_context_locals_fupd (K params) ctxt'))
             (fun_decl_return_fupd
                (compile_shape (pan_structs_context_structs ctxt)) fi)) in
      (CONS (Function fi') ds',ctxt')) /\
   (pan_structs_compile_decs ctxt (CONS (Name nm flds) ds) =
      pan_structs_compile_decs ctxt ds) /\
   (pan_structs_compile_decs ctxt (CONS (ExnDecl nm sh) ds) =
      let (ds',ctxt') = pan_structs_compile_decs ctxt ds in
      (CONS (ExnDecl nm (compile_shape (pan_structs_context_structs ctxt) sh)) ds',
       ctxt'))`;;

let pan_structs_compile_decs_ind = cake_ind "pan_structs_compile_decs";;

(* Returns struct context *)

let get_names_def = cake_def
  `(get_names ctxt ([]:((A)decl)list) = ctxt) /\
   (get_names ctxt (CONS (Name nm flds) ds) =
      get_names (pan_structs_context_structs_fupd
                   (K (CONS (nm,flds) (pan_structs_context_structs ctxt))) ctxt) ds) /\
   (get_names ctxt (CONS _ ds) = get_names ctxt ds)`;;

(* Returns converted program *)

let pan_structs_compile_top_def = cake_def
  `pan_structs_compile_top (decs:((A)decl)list) =
     let ctxt = pan_structs_context_REC [] [] [] in
     FST (pan_structs_compile_decs (get_names ctxt decs) decs)`;;
