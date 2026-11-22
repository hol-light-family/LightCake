(* ========================================================================= *)
(* crep_to_loop: port of HOL4 pancake/crep_to_loopScript.sml (CakeML v3479). *)
(* Compilation from crepLang to loopLang.                                    *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as notes/naming/names.tsv says: the record context is             *)
(*   crep_to_loop_context (fields crep_to_loop_context_vars, ..._funcs,      *)
(*   ..._vmax, ..._target); find_var, find_lab, compile_exp(s), compile,     *)
(*   mk_ctxt, make_vmap, comp_func, make_funcs and compile_prog get the      *)
(*   prefix crep_to_loop_.                                                   *)
(* - crepLang constructors are crep_Const, crep_Var, ...; loopLang's are     *)
(*   loop_Const, loop_Var, ...; LoadGlob, StoreGlob, Crepop and LLongMul     *)
(*   keep their names.                                                       *)
(* - () is one, 0w is word 0, 1w is word 1; GENLIST f n is list_of_seq f n,  *)
(*   ZIP (a,b) is ZIP a b; ++ is APPEND (left associative); $+ tmp is        *)
(*   (+) tmp.  Every MAP2 and ZIP here has lists of equal lengths (gen_temps *)
(*   n (LENGTH les) against les, the GENLIST against the list it numbers),  *)
(*   so HOL Light's MAP2 and ZIP give HOL4's values.                         *)
(* - HOL4 r with <| f1 := v1; f2 := v2 |> is                                 *)
(*   rec_f2_fupd (K v2) (rec_f1_fupd (K v1) r) (as in crepSem).              *)
(* - compile_crepop: its last argument l is unused (HOL4 gives it a type    *)
(*   variable, as here).                                                     *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/backend/backend_common.ml";;
needs "pancake/crepLang.ml";;
needs "pancake/loopLang.ml";;
needs "pancake/loop_live.ml";;
needs "pancake/crep_arith.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4: context (loc, length args in funcs) *)

let crep_to_loop_context_INFO = cake_record "crep_to_loop_context"
  ["vars","(crep_varname,num)fmap";
   "funcs","(crep_funname,num#num)fmap";
   "vmax","num";
   "target","architecture"];;

let crep_to_loop_context_component_equality =
  (record_info "crep_to_loop_context").ri_component_equality;;

let crep_to_loop_find_var_def = cake_def
  `crep_to_loop_find_var ct v =
     match FLOOKUP (crep_to_loop_context_vars ct) v with
       SOME n -> n
     | NONE -> 0`;;

let crep_to_loop_find_lab_def = cake_def
  `crep_to_loop_find_lab ct f =
     match FLOOKUP (crep_to_loop_context_funcs ct) f with
       SOME (n,_) -> n
     | NONE -> 0`;;

let prog_if_def = cake_def
  `prog_if cmp p q e e' n m l =
     APPEND (APPEND p q)
       [loop_Assign n e; loop_Assign m e';
        loop_If cmp n (Reg m) (loop_Assign n (loop_Const (word 1)))
          (loop_Assign n (loop_Const (word 0))) (list_insert [n; m] l)]
     :((A)loop_prog)list`;;

let compile_crepop_def = cake_def
  `compile_crepop crep_Mul target x y tmp (l:B) =
     if target = ARMv7 then
       ([loop_Arith (LLongMul tmp (tmp + 1) x y)]:((A)loop_prog)list,tmp + 1)
     else
       ([loop_Arith (LLongMul tmp tmp x y)],tmp)`;;

let crep_to_loop_compile_exp_def = cake_def_wf
  `measure (\x. sum_CASE x
                  (\p:crep_to_loop_context#num#num_set#(A)crep_exp.
                     crep_exp_size ARB (SND (SND (SND p))))
                  (\q:crep_to_loop_context#num#num_set#((A)crep_exp)list.
                     list_size (crep_exp_size ARB) (SND (SND (SND q)))))`
  TERM_TAC
  `(crep_to_loop_compile_exp ctxt tmp l (crep_BaseAddr:(A)crep_exp) =
      ([]:((A)loop_prog)list,loop_BaseAddr,tmp,l)) /\
   (crep_to_loop_compile_exp ctxt tmp l crep_TopAddr =
      ([],loop_TopAddr,tmp,l)) /\
   (crep_to_loop_compile_exp ctxt tmp l (crep_Const c) =
      ([],loop_Const c,tmp,l)) /\
   (crep_to_loop_compile_exp ctxt tmp l (crep_Var v) =
      ([],loop_Var (crep_to_loop_find_var ctxt v),tmp,l)) /\
   (crep_to_loop_compile_exp ctxt tmp l (crep_Load ad) =
      let (p,le,tmp,l) = crep_to_loop_compile_exp ctxt tmp l ad in
      (p,loop_Load le,tmp,l)) /\
   (crep_to_loop_compile_exp ctxt tmp l (crep_Load32 ad) =
      let (p,le,tmp,l) = crep_to_loop_compile_exp ctxt tmp l ad in
      (APPEND p [loop_Assign tmp le; loop_Load32 tmp tmp],loop_Var tmp,
       tmp + 1,insert tmp one l)) /\
   (crep_to_loop_compile_exp ctxt tmp l (crep_LoadByte ad) =
      let (p,le,tmp,l) = crep_to_loop_compile_exp ctxt tmp l ad in
      (APPEND p [loop_Assign tmp le; loop_LoadByte tmp tmp],loop_Var tmp,
       tmp + 1,insert tmp one l)) /\
   (crep_to_loop_compile_exp ctxt tmp l (LoadGlob gadr) =
      ([],loop_Lookup gadr,tmp,l)) /\
   (crep_to_loop_compile_exp ctxt tmp l (crep_Op bop es) =
      let (p,les,tmp,l) = crep_to_loop_compile_exps ctxt tmp l es in
      (p,loop_Op bop les,tmp,l)) /\
   (crep_to_loop_compile_exp ctxt tmp'' l (Crepop cop es) =
      let (p,les,tmp,l) = crep_to_loop_compile_exps ctxt tmp'' l es in
      let (p',tmp') =
        compile_crepop cop (crep_to_loop_context_target ctxt) tmp (tmp + 1)
          (tmp + LENGTH les)
          (list_insert (list_of_seq ((+) tmp) (LENGTH les)) l) in
      (APPEND (APPEND p (MAPi (\n. loop_Assign (tmp + n)) les)) p',
       loop_Var tmp',tmp' + 1,
       insert tmp' one (list_insert (list_of_seq ((+) tmp) (tmp' - tmp)) l))) /\
   (crep_to_loop_compile_exp ctxt tmp l (crep_Cmp cmp e e') =
      let (p,le,tmp,l) = crep_to_loop_compile_exp ctxt tmp l e in
      let (p',le',tmp',l) = crep_to_loop_compile_exp ctxt tmp l e' in
      (prog_if cmp p p' le le' (tmp' + 1) (tmp' + 2) l,loop_Var (tmp' + 1),
       tmp' + 3,list_insert [tmp' + 1; tmp' + 2] l)) /\
   (crep_to_loop_compile_exp ctxt tmp l (crep_Shift sh e e') =
      let (p,le,tmp,l) = crep_to_loop_compile_exp ctxt tmp l e in
      let (p',le',tmp',l) = crep_to_loop_compile_exp ctxt tmp l e' in
      (APPEND p p',loop_Shift sh le le',tmp',l)) /\
   (crep_to_loop_compile_exps ctxt tmp l cps =
      match cps with
        [] -> ([],[],tmp,l)
      | CONS e es ->
          let (p,le,tmp,l) = crep_to_loop_compile_exp ctxt tmp l e in
          let (p1,les,tmp,l) = crep_to_loop_compile_exps ctxt tmp l es in
          (APPEND p p1,CONS le les,tmp,l))`;;

let crep_to_loop_compile_exp_ind = cake_ind "crep_to_loop_compile_exp";;

let gen_temps_def = cake_def
  `gen_temps n l = list_of_seq (\x. n + x) l`;;

let rt_var_def = cake_def
  `(rt_var (fm:(A,num)fmap) NONE (n:num) (mx:num) = n) /\
   (rt_var fm (SOME v) n mx =
      match FLOOKUP fm v with
        NONE -> mx + 1
      | SOME m -> m)`;;

let rt_vars_def = cake_def
  `rt_vars (fm:(A,num)fmap) vs (mx:num) =
     match OPT_MMAP (FLOOKUP fm) vs with
       NONE -> [mx + 1]
     | SOME m -> m`;;

(* the clauses are parsed one by one (HOL4 types each clause on its own: e  *)
(* is an expression in most clauses and a function name in crep_Call)       *)

let crep_to_loop_compile_def = cake_def_wf_clauses
  `measure (\(ctxt:crep_to_loop_context,l:num_set,p:(A)crep_prog).
              crep_prog_size ARB p)`
  TERM_TAC
  [`crep_to_loop_compile (_:crep_to_loop_context) (_:num_set)
       (crep_Skip:(A)crep_prog) = loop_Skip:(A)loop_prog`;
   `crep_to_loop_compile (_:crep_to_loop_context) (_:num_set)
       (crep_Break n:(A)crep_prog) = loop_Break n:(A)loop_prog`;
   `crep_to_loop_compile (_:crep_to_loop_context) (_:num_set) (crep_Continue n:(A)crep_prog) =
      loop_Continue n:(A)loop_prog`;
   `crep_to_loop_compile (_:crep_to_loop_context) (_:num_set)
       (crep_Tick:(A)crep_prog) = loop_Tick:(A)loop_prog`;
   `crep_to_loop_compile (ctxt:crep_to_loop_context) (l:num_set) (crep_Return es:(A)crep_prog) =
      let (p,les,ntmp,nl) =
        crep_to_loop_compile_exps ctxt (crep_to_loop_context_vmax ctxt + 1) l es in
      let ntmps = gen_temps ntmp (LENGTH les) in
      loop_nested_seq
        (APPEND (APPEND p (MAP2 loop_Assign ntmps les)) [loop_Return ntmps])
      :(A)loop_prog`;
   `crep_to_loop_compile (ctxt:crep_to_loop_context) (l:num_set) (crep_Raise eid:(A)crep_prog) =
      loop_Seq (loop_Assign (crep_to_loop_context_vmax ctxt + 1) (loop_Const eid))
        (loop_Raise (crep_to_loop_context_vmax ctxt + 1)):(A)loop_prog`;
   `crep_to_loop_compile (ctxt:crep_to_loop_context) (l:num_set) (crep_ShMem op r ad:(A)crep_prog) =
      match FLOOKUP (crep_to_loop_context_vars ctxt) r with
        SOME n ->
          let (p,le,tmp,l) =
            crep_to_loop_compile_exp ctxt (crep_to_loop_context_vmax ctxt + 1) l ad in
          loop_nested_seq (APPEND p [loop_ShMem op n le])
      | NONE -> loop_Skip:(A)loop_prog`;
   `crep_to_loop_compile (ctxt:crep_to_loop_context) (l:num_set) (crep_Store dst src:(A)crep_prog) =
      let (p,le,tmp,l) =
        crep_to_loop_compile_exp ctxt (crep_to_loop_context_vmax ctxt + 1) l dst in
      let (p',le',tmp,l) = crep_to_loop_compile_exp ctxt tmp l src in
      loop_nested_seq
        (APPEND (APPEND p p') [loop_Assign tmp le'; loop_Store le tmp])
      :(A)loop_prog`;
   `crep_to_loop_compile (ctxt:crep_to_loop_context) (l:num_set)
       (crep_Store32 dst src:(A)crep_prog) =
      let (p,le,tmp,l) =
        crep_to_loop_compile_exp ctxt (crep_to_loop_context_vmax ctxt + 1) l dst in
      let (p',le',tmp,l) = crep_to_loop_compile_exp ctxt tmp l src in
      loop_nested_seq
        (APPEND (APPEND p p')
           [loop_Assign tmp le; loop_Assign (tmp + 1) le';
            loop_Store32 tmp (tmp + 1)]):(A)loop_prog`;
   `crep_to_loop_compile (ctxt:crep_to_loop_context) (l:num_set)
       (crep_StoreByte dst src:(A)crep_prog) =
      let (p,le,tmp,l) =
        crep_to_loop_compile_exp ctxt (crep_to_loop_context_vmax ctxt + 1) l dst in
      let (p',le',tmp,l) = crep_to_loop_compile_exp ctxt tmp l src in
      loop_nested_seq
        (APPEND (APPEND p p')
           [loop_Assign tmp le; loop_Assign (tmp + 1) le';
            loop_StoreByte tmp (tmp + 1)]):(A)loop_prog`;
   `crep_to_loop_compile (ctxt:crep_to_loop_context) (l:num_set) (StoreGlob adr e:(A)crep_prog) =
      let (p,le,tmp,l) =
        crep_to_loop_compile_exp ctxt (crep_to_loop_context_vmax ctxt + 1) l e in
      loop_nested_seq (APPEND p [loop_SetGlobal adr le]):(A)loop_prog`;
   `crep_to_loop_compile (ctxt:crep_to_loop_context) (l:num_set) (crep_Seq p q:(A)crep_prog) =
      loop_Seq (crep_to_loop_compile ctxt l p) (crep_to_loop_compile ctxt l q)
      :(A)loop_prog`;
   `crep_to_loop_compile (ctxt:crep_to_loop_context) (l:num_set) (crep_Assign v e:(A)crep_prog) =
      match FLOOKUP (crep_to_loop_context_vars ctxt) v with
        SOME n ->
          let (p,le,tmp,l) =
            crep_to_loop_compile_exp ctxt (crep_to_loop_context_vmax ctxt + 1) l e in
          loop_nested_seq (APPEND p [loop_Assign n le])
      | NONE -> loop_Skip:(A)loop_prog`;
   `crep_to_loop_compile (ctxt:crep_to_loop_context) (l:num_set)
       (crep_Primitive lhss pop rhss:(A)crep_prog) =
      match (OPT_MMAP (FLOOKUP (crep_to_loop_context_vars ctxt)) lhss,
             OPT_MMAP (FLOOKUP (crep_to_loop_context_vars ctxt)) rhss) with
        (SOME nlhss,SOME nrhss) -> loop_Primitive nlhss pop nrhss
      | _ -> loop_Skip:(A)loop_prog`;
   `crep_to_loop_compile (ctxt:crep_to_loop_context) (l:num_set) (crep_Dec v e prog:(A)crep_prog) =
      let (p,le,tmp,nl) =
        crep_to_loop_compile_exp ctxt (crep_to_loop_context_vmax ctxt + 1) l e in
      let nctxt =
        crep_to_loop_context_vmax_fupd (K tmp)
          (crep_to_loop_context_vars_fupd
             (K (crep_to_loop_context_vars ctxt |+ (v,tmp))) ctxt) in
      let fl = insert tmp one l in
      let lp = crep_to_loop_compile nctxt fl prog in
      loop_Seq (loop_nested_seq p) (loop_Seq (loop_Assign tmp le) lp):(A)loop_prog`;
   `crep_to_loop_compile (ctxt:crep_to_loop_context) (l:num_set) (crep_If e p q:(A)crep_prog) =
      let (np,le,tmp,nl) =
        crep_to_loop_compile_exp ctxt (crep_to_loop_context_vmax ctxt + 1) l e in
      let lp = crep_to_loop_compile ctxt l p in
      let lq = crep_to_loop_compile ctxt l q in
      loop_nested_seq
        (APPEND np [loop_Assign tmp le;
                    loop_If NotEqual tmp (Imm (word 0)) lp lq l]):(A)loop_prog`;
   `crep_to_loop_compile (ctxt:crep_to_loop_context) (l:num_set) (crep_While e p:(A)crep_prog) =
      let (np,le,tmp,nl) =
        crep_to_loop_compile_exp ctxt (crep_to_loop_context_vmax ctxt + 1) l e in
      let lp = crep_to_loop_compile ctxt l p in
      loop_Loop l
        (loop_nested_seq
           (APPEND np [loop_Assign tmp le;
                       loop_If NotEqual tmp (Imm (word 0))
                         (loop_Seq lp (loop_Continue 0)) (loop_Break 0) l]))
        l:(A)loop_prog`;
   `crep_to_loop_compile (ctxt:crep_to_loop_context) (l:num_set)
       (crep_Call call_type e es:(A)crep_prog) =
      let dest = crep_to_loop_find_lab ctxt e in
      let (p,les,tmp,nl) =
        crep_to_loop_compile_exps ctxt (crep_to_loop_context_vmax ctxt + 1) l es in
      let nargs = gen_temps tmp (LENGTH les) in
      let (rt1,rt2) =
        match call_type with
          NONE -> (NONE,NONE)
        | SOME (rts,hdl) ->
            let rns =
              rt_vars (crep_to_loop_context_vars ctxt) rts
                (crep_to_loop_context_vmax ctxt + 1) in
            let en = crep_to_loop_context_vmax ctxt + 1 in
            let pe =
              match hdl with
                NONE -> loop_Raise en
              | SOME (eid,ep) ->
                  let cpe = crep_to_loop_compile ctxt l ep in
                  loop_If NotEqual en (Imm eid) (loop_Raise en)
                    (loop_Seq loop_Tick cpe) l in
            (SOME (rns,l),SOME (en,pe,loop_Skip,l)) in
      loop_nested_seq
        (APPEND (APPEND p (MAP2 loop_Assign nargs les))
           [loop_Call rt1 (SOME dest) nargs rt2]):(A)loop_prog`;
   `crep_to_loop_compile (ctxt:crep_to_loop_context) (l:num_set)
       (crep_ExtCall f ptr1 len1 ptr2 len2:(A)crep_prog) =
      match (FLOOKUP (crep_to_loop_context_vars ctxt) ptr1,
             FLOOKUP (crep_to_loop_context_vars ctxt) len1,
             FLOOKUP (crep_to_loop_context_vars ctxt) ptr2,
             FLOOKUP (crep_to_loop_context_vars ctxt) len2) with
        (SOME pc,SOME lc,SOME pc',SOME lc') -> loop_FFI f pc lc pc' lc' l
      | _ -> loop_Skip:(A)loop_prog`];;

let crep_to_loop_compile_ind = cake_ind "crep_to_loop_compile";;

let ocompile_def = cake_def
  `ocompile ctxt l (p:(A)crep_prog) =
     (optimise o crep_to_loop_compile ctxt l) p`;;

let crep_to_loop_mk_ctxt_def = cake_def
  `crep_to_loop_mk_ctxt target vmap fs vmax =
     crep_to_loop_context_REC vmap fs vmax target`;;

let crep_to_loop_make_vmap_def = cake_def
  `crep_to_loop_make_vmap (params:num list) =
     FEMPTY |++ ZIP params (list_of_seq I (LENGTH params))`;;

let crep_to_loop_comp_func_def = cake_def
  `crep_to_loop_comp_func target fs params (body:(A)crep_prog) =
     let vmap = crep_to_loop_make_vmap params in
     let vmax = LENGTH params - 1 in
     let l = list_to_num_set (list_of_seq I (LENGTH params)) in
     crep_to_loop_compile (crep_to_loop_mk_ctxt target vmap fs vmax) l body`;;

let first_name_def = cake_def
  `first_name = 64:num`;;

let crep_to_loop_make_funcs_def = cake_def
  `crep_to_loop_make_funcs (prog:(mlstring#(num list)#(A)crep_prog)list) =
     let fnames = MAP FST prog in
     let fnums = list_of_seq (\n. n + first_name) (LENGTH prog) in
     let lens = MAP (LENGTH o FST o SND) prog in
     let fnums_lens = MAP2 (\x y. (x,y)) fnums lens in
     let fs = MAP2 (\x y. (x,y)) fnames fnums_lens in
     alist_to_fmap fs`;;

let crep_to_loop_compile_prog_def = cake_def
  `crep_to_loop_compile_prog target (prog:(mlstring#(num list)#(A)crep_prog)list) =
     let fnums = list_of_seq (\n. n + first_name) (LENGTH prog) in
     let comp = crep_to_loop_comp_func target (crep_to_loop_make_funcs prog) in
     MAP2 (\n (name,params,body).
             (n,(list_of_seq I o LENGTH) params,
              optimise (comp params (simp_prog body))))
       fnums prog`;;
