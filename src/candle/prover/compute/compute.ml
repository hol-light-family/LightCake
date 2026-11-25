(* ========================================================================= *)
(* compute: port of HOL4 candle/prover/compute/computeScript.sml (CakeML     *)
(* v3479).  Implementation of the compute primitive.                         *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - The overloads of compute_syntax (_COND, _CEXP_ADD, Cexp, ...) are read  *)
(*   by its parser extension (see the header of compute_syntax.ml).          *)
(* - Names as doc/names.tsv says: compute is compute_compute (a              *)
(*   common word).  The kernel functions are holKernel's: mk_eq, dest_eq,    *)
(*   dest_const, handle_Clash are holKernel_mk_eq, ..., and failwith is      *)
(*   holKernel_raise_Failure; HOL4's map in this theory is compute_eval's    *)
(*   (compute_map: computeProof uses compute_eval's map_LENGTH and map_thm   *)
(*   on it).                                                                 *)
(* - The do-notation is written with the constants of ml_monadBase.ml, as in *)
(*   compute_eval.ml; HOL4's x <<- e; r (monadic let) is let x = e in r, and *)
(*   m ++ m' is m otherwise m'.  HOL4's flip (combin$C) is vocab.ml's flip, *)
(*   so the stored term of compute_compute is HOL4's.  HOL4's s1 ^ s2 is     *)
(*   strcat s1 s2 (left associative), EVERY is ALL, () is one.               *)
(* - HOL4 rebinds compute_thms_def to its SIMP_RULE list_ss form (the MAP    *)
(*   evaluated); here compute_thms_def is that form and the definition       *)
(*   itself is CMPAUX_compute_thms_raw.                                      *)
(* - Local helpers that are not HOL4 theorems are CMPAUX_.                   *)
(* ========================================================================= *)

needs "candle/standard/monadic/holKernel.ml";;
needs "candle/prover/compute/compute_syntax.ml";;
needs "candle/prover/compute/compute_eval.ml";;
needs "candle/prover/compute/compute_exec.ml";;

prioritize_num();;
type_invention_error := true;;

compute_overloads_on ();;

(* ------------------------------------------------------------------------- *)
(* Theory initialization                                                     *)
(* ------------------------------------------------------------------------- *)

(* the equations, in order: COND_TRUE, COND_FALSE, IF_TRUE, IF_FALSE,     *)
(* NUMERAL, BIT0, BIT1, ADD, ADD, SUB, SUB, SUB, MUL, MUL, DIV, MOD,      *)
(* LESS, LESS, LESS, EQ, EQ, EQ, EQ, CEXP_ADD, CEXP_ADD, CEXP_ADD,        *)
(* CEXP_ADD, CEXP_SUB, CEXP_SUB, CEXP_SUB, CEXP_SUB, CEXP_MUL, CEXP_MUL,  *)
(* CEXP_MUL, CEXP_MUL, CEXP_DIV, CEXP_DIV, CEXP_DIV, CEXP_DIV, CEXP_MOD,  *)
(* CEXP_MOD, CEXP_MOD, CEXP_MOD, CEXP_LESS, CEXP_LESS, CEXP_LESS,         *)
(* CEXP_LESS, CEXP_IF, CEXP_IF, CEXP_IF, CEXP_FST, CEXP_FST, CEXP_SND,    *)
(* CEXP_SND, CEXP_ISPAIR, CEXP_ISPAIR, CEXP_EQ, PAIR_EQ1, PAIR_EQ2,       *)
(* PAIR_EQ3, PAIR_EQ4, LET                                                *)
let CMPAUX_compute_thms_raw = cake_def
  `compute_thms = MAP (Sequent [])
     [_COND _TRUE _M _N === _M;
      _COND _FALSE _M _N === _N;
      _IF _TRUE _X _Y === _X;
      _IF _FALSE _X _Y === _Y;
      _NUMERAL _N === _N;
      _BIT0 _N === _ADD _N _N;
      _BIT1 _N === _SUC (_ADD _N _N);
      _ADD (_NUMERAL _0) _N === _N;
      _ADD (_SUC _M) _N === _SUC (_ADD _M _N);
      _SUB (_NUMERAL _0) _N === _NUMERAL _0;
      _SUB _M (_NUMERAL _0) === _M;
      _SUB (_SUC _M) (_SUC _N) === _SUB _M _N;
      _MUL (_NUMERAL _0) _N === _NUMERAL _0;
      _MUL (_SUC _M) _N === _ADD _N (_MUL _M _N);
      _DIV _M _N ===
        _COND (_N === _NUMERAL _0) (_NUMERAL _0)
        (_COND (_LESS _M _N) (_NUMERAL _0)
        (_SUC (_DIV (_SUB _M _N) _N)));
      _MOD _M _N ===
        _COND (_N === _NUMERAL _0) _M
        (_COND (_LESS _M _N) _M
        (_MOD (_SUB _M _N) _N));
      _LESS _M (_NUMERAL _0) === _FALSE;
      _LESS (_NUMERAL _0) (_SUC _N) === _TRUE;
      _LESS (_SUC _M) (_SUC _N) === _LESS _M _N;
      (_NUMERAL _0 === _NUMERAL _0) === _TRUE;
      (_NUMERAL _0 === _SUC _N) === _FALSE;
      (_SUC _M === _NUMERAL _0) === _FALSE;
      (_SUC _M === _SUC _N) === (_M === _N);
      _CEXP_ADD (_CEXP_NUM _M) (_CEXP_NUM _N) ===
        _CEXP_NUM (_ADD _M _N);
      _CEXP_ADD (_CEXP_NUM _M) (_CEXP_PAIR _P1 _Q1) ===
        _CEXP_NUM _M;
      _CEXP_ADD (_CEXP_PAIR _P1 _Q1) (_CEXP_NUM _N) ===
        _CEXP_NUM _N;
      _CEXP_ADD (_CEXP_PAIR _P1 _Q1) (_CEXP_PAIR _P2 _Q2) ===
        _CEXP_NUM (_NUMERAL _0);
      _CEXP_SUB (_CEXP_NUM _M) (_CEXP_NUM _N) ===
        _CEXP_NUM (_SUB _M _N);
      _CEXP_SUB (_CEXP_NUM _M) (_CEXP_PAIR _P1 _Q1) ===
        _CEXP_NUM _M;
      _CEXP_SUB (_CEXP_PAIR _P1 _Q1) (_CEXP_NUM _N) ===
        _CEXP_NUM (_NUMERAL _0);
      _CEXP_SUB (_CEXP_PAIR _P1 _Q1) (_CEXP_PAIR _P2 _Q2) ===
        _CEXP_NUM (_NUMERAL _0);
      _CEXP_MUL (_CEXP_NUM _M) (_CEXP_NUM _N) ===
        _CEXP_NUM (_MUL _M _N);
      _CEXP_MUL (_CEXP_NUM _M) (_CEXP_PAIR _P1 _Q1) ===
        _CEXP_NUM (_NUMERAL _0);
      _CEXP_MUL (_CEXP_PAIR _P1 _Q1) (_CEXP_NUM _N) ===
        _CEXP_NUM (_NUMERAL _0);
      _CEXP_MUL (_CEXP_PAIR _P1 _Q1) (_CEXP_PAIR _P2 _Q2) ===
        _CEXP_NUM (_NUMERAL _0);
      _CEXP_DIV (_CEXP_NUM _M) (_CEXP_NUM _N) ===
        _CEXP_NUM (_DIV _M _N);
      _CEXP_DIV (_CEXP_NUM _M) (_CEXP_PAIR _P1 _Q1) ===
        _CEXP_NUM (_NUMERAL _0);
      _CEXP_DIV (_CEXP_PAIR _P1 _Q1) (_CEXP_NUM _N) ===
        _CEXP_NUM (_NUMERAL _0);
      _CEXP_DIV (_CEXP_PAIR _P1 _Q1) (_CEXP_PAIR _P2 _Q2) ===
        _CEXP_NUM (_NUMERAL _0);
      _CEXP_MOD (_CEXP_NUM _M) (_CEXP_NUM _N) ===
        _CEXP_NUM (_MOD _M _N);
      _CEXP_MOD (_CEXP_NUM _M) (_CEXP_PAIR _P1 _Q1) ===
        _CEXP_NUM _M;
      _CEXP_MOD (_CEXP_PAIR _P1 _Q1) (_CEXP_NUM _N) ===
        _CEXP_NUM (_NUMERAL _0);
      _CEXP_MOD (_CEXP_PAIR _P1 _Q1) (_CEXP_PAIR _P2 _Q2) ===
        _CEXP_NUM (_NUMERAL _0);
      _CEXP_LESS (_CEXP_NUM _M) (_CEXP_NUM _N) ===
        _CEXP_NUM (_COND (_LESS _M _N) (_SUC (_NUMERAL _0))
        (_NUMERAL _0));
      _CEXP_LESS (_CEXP_NUM _M) (_CEXP_PAIR _P1 _Q1) ===
        _CEXP_NUM (_NUMERAL _0);
      _CEXP_LESS (_CEXP_PAIR _P1 _Q1) (_CEXP_NUM _N) ===
        _CEXP_NUM (_NUMERAL _0);
      _CEXP_LESS (_CEXP_PAIR _P1 _Q1) (_CEXP_PAIR _P2 _Q2) ===
        _CEXP_NUM (_NUMERAL _0);
      _CEXP_IF (_CEXP_NUM (_SUC _M)) _P1 _Q1 === _P1;
      _CEXP_IF (_CEXP_PAIR _P2 _Q2) _P1 _Q1 === _Q1;
      _CEXP_IF (_CEXP_NUM (_NUMERAL _0)) _P1 _Q1 === _Q1;
      _CEXP_FST (_CEXP_PAIR _P1 _Q1) === _P1;
      _CEXP_FST (_CEXP_NUM _M) === _CEXP_NUM (_NUMERAL _0);
      _CEXP_SND (_CEXP_PAIR _P1 _Q1) === _Q1;
      _CEXP_SND (_CEXP_NUM _M) === _CEXP_NUM (_NUMERAL _0);
      _CEXP_ISPAIR (_CEXP_PAIR _P1 _Q1) ===
        _CEXP_NUM (_SUC (_NUMERAL _0));
      _CEXP_ISPAIR (_CEXP_NUM _M) ===
        _CEXP_NUM (_NUMERAL _0);
      _CEXP_EQ _P1 _Q1 ===
        _CEXP_NUM (_COND (_P1 === _Q1)
        (_SUC (_NUMERAL _0))
        (_NUMERAL _0));
      (_CEXP_PAIR _P1 _Q1 === _CEXP_PAIR _P2 _Q2) ===
        (_IF (_P1 === _P2) (_Q1 === _Q2) _FALSE);
      (_CEXP_NUM _M === _CEXP_NUM _N) === (_M === _N);
      (_CEXP_NUM _M === _CEXP_PAIR _P1 _Q1) === _FALSE;
      (_CEXP_PAIR _P1 _Q1 === _CEXP_NUM _N) === _FALSE;
      (_LET _F _P1 === hol_Comb _F _P1)]`;;


let compute_thms_def = REWRITE_RULE[MAP] CMPAUX_compute_thms_raw;;

let compute_init_def = cake_def
  `compute_init ths <=> ths = compute_thms`;;

(* ------------------------------------------------------------------------- *)
(* compute_add                                                               *)
(* ------------------------------------------------------------------------- *)

let compute_add_def = cake_def
  `compute_add ths tm =
     if ~(compute_init ths) then
       holKernel_raise_Failure
         (implode "compute_add: wrong theorems provided for initialization")
     else
       st_ex_bind (compute_dest_binary _ADD_TM tm) (\p.
       match p with
         (l,r) ->
           st_ex_bind (compute_dest_numeral l) (\x.
           st_ex_bind (compute_dest_numeral r) (\y.
           let res = num2bit (x + y) in
           st_ex_bind (holKernel_mk_eq (tm,_NUMERAL res)) (\c.
           st_ex_return (Sequent [] c))))) otherwise
       holKernel_raise_Failure (implode "compute_add")`;;

(* ------------------------------------------------------------------------- *)
(* compute                                                                   *)
(* ------------------------------------------------------------------------- *)

(* HOL4: Termination wf_rel_tac measure compute_exp_size *)
let const_list_def = cake_def_clauses
  [`const_list (compute_Var n) = []:(mlstring#num)list`;
   `const_list (compute_Num n) = []:(mlstring#num)list`;
   `const_list (compute_Pair x y) =
      APPEND (const_list x) (const_list y):(mlstring#num)list`;
   `const_list (compute_Uop uop x) = const_list x:(mlstring#num)list`;
   `const_list (compute_Binop bop x y) =
      APPEND (const_list x) (const_list y):(mlstring#num)list`;
   `const_list (compute_If x y z) =
      APPEND (APPEND (const_list x) (const_list y)) (const_list z):(mlstring#num)list`;
   `const_list (compute_Let s x y) =
      APPEND (const_list x) (const_list y):(mlstring#num)list`;
   `const_list (compute_App s xs) =
      CONS (s,LENGTH xs) (FLAT (MAP const_list xs))`];;

let const_list_ind = cake_ind "const_list";;

(* HOL4: Termination wf_rel_tac measure compute_exp_size *)
let var_list_def = cake_def_clauses
  [`var_list (compute_Var n) = [n]`;
   `var_list (compute_Num n) = []:mlstring list`;
   `var_list (compute_Pair x y) = APPEND (var_list x) (var_list y):mlstring list`;
   `var_list (compute_Uop uop x) = var_list x:mlstring list`;
   `var_list (compute_Binop bop x y) = APPEND (var_list x) (var_list y):mlstring list`;
   `var_list (compute_If x y z) =
      APPEND (APPEND (var_list x) (var_list y)) (var_list z):mlstring list`;
   `var_list (compute_Let s x y) =
      APPEND (var_list x) (FILTER (\n. ~(n = s)) (var_list y))`;
   `var_list (compute_App s xs) = FLAT (MAP var_list xs):mlstring list`];;

let var_list_ind = cake_ind "var_list";;

(* A valid equation is:                                                     *)
(*   [] |- const var1 ... varN = expr                                       *)
(* where:                                                                   *)
(* - var1 ... varN all have type Cexp                                       *)
(* - expr contains only the variables var1 ... varN, and has type Cexp     *)

let check_var_def = cake_def
  `(check_var (hol_Var s ty) =
      if ty = Cexp then st_ex_return s else
        holKernel_raise_Failure
          (strcat (implode "Kernel.compute: ill-typed variable: ") s)) /\
   (check_var _ =
      holKernel_raise_Failure
        (implode "Kernel.compute: non-variable argument on lhs of equation"))`;;

let check_eqn_def = cake_def
  `check_eqn (Sequent h c) =
     st_ex_ignore_bind
       (if h = [] then st_ex_return one else
          holKernel_raise_Failure
            (implode "Kernel.compute: non-empty hypotheses in equation"))
     (st_ex_bind (holKernel_dest_eq c) (\p.
      match p with
        (ls,r) ->
          st_ex_bind
            (match list_dest_comb [] ls with
               CONS f vs ->
                 if ALL_DISTINCT vs then st_ex_return (f,vs)
                 else holKernel_raise_Failure
                        (implode "Kernel.compute: variables not distinct")
             | _ -> holKernel_raise_Failure (implode "")) (\q.
          match q with
            (f,vs) ->
              st_ex_bind
                (holKernel_dest_const f otherwise
                 holKernel_raise_Failure
                   (implode "Kernel.compute: not a constant being applied on lhs"))
                (\nt.
              match nt with
                (nm,ty) ->
                  st_ex_bind (compute_map check_var vs) (\args.
                  match compute_dest_cexp r with
                    NONE -> holKernel_raise_Failure
                              (implode "Kernel.compute: rhs is not a cexp")
                  | SOME cv ->
                      st_ex_ignore_bind
                        (if ALL (\v. MEM v args) (var_list cv) then st_ex_return one
                         else holKernel_raise_Failure
                                (implode "Kernel.compute: rhs contains free variable"))
                      (st_ex_return (nm,args,cv)))))))`;;

let compute_default_clock = cake_def
  `compute_default_clock = 1000000000`;;

let check_consts_def = cake_def
  `check_consts ars fn rhs =
     if ALL (\(c,n). MEM (c,n) ars) (const_list rhs) then st_ex_return one else
     holKernel_raise_Failure
       (strcat (strcat (strcat (implode "Kernel.compute: rhs of ") fn)
                       (implode " has a constant "))
               (implode "with no equation associated to it."))`;;

(* HOL4: Termination wf_rel_tac measure (compute_exp_size o SND) *)
let check_cexp_closed_def = cake_def_clauses
  [`check_cexp_closed bvs (compute_Var n) <=> MEM n bvs`;
   `check_cexp_closed (bvs:mlstring list) (compute_Num n) <=> T`;
   `check_cexp_closed (bvs:mlstring list) (compute_Pair p q) <=>
      ALL (check_cexp_closed bvs) [p; q]`;
   `check_cexp_closed (bvs:mlstring list) (compute_Uop uop p) <=>
      check_cexp_closed bvs p`;
   `check_cexp_closed (bvs:mlstring list) (compute_Binop bop p q) <=>
      ALL (check_cexp_closed bvs) [p; q]`;
   `check_cexp_closed (bvs:mlstring list) (compute_If p q r) <=>
      ALL (check_cexp_closed bvs) [p; q; r]`;
   `check_cexp_closed (bvs:mlstring list) (compute_Let s p q) <=>
      check_cexp_closed bvs p /\ check_cexp_closed (CONS s bvs) q`;
   `check_cexp_closed (bvs:mlstring list) (compute_App f cs) <=>
      ALL (check_cexp_closed bvs) cs`];;

let check_cexp_closed_ind = cake_ind "check_cexp_closed";;

let compute_compute_def = cake_def
  `compute_compute (ths,ceqs:thm list) tm =
     flip holKernel_handle_Clash
       (\e. holKernel_raise_Failure (implode "impossible")
             :hol_refs->(thm,hol_exn)exc#hol_refs)
     (if ~compute_init ths then
        holKernel_raise_Failure
          (implode "Kernel.compute: wrong theorems provided for initialization")
      else
      match compute_dest_cexp tm with
        NONE -> holKernel_raise_Failure
                  (implode "Kernel.compute: term is not a compute_exp")
      | SOME cexp ->
          st_ex_ignore_bind
            (if check_cexp_closed [] cexp then st_ex_return one else
               holKernel_raise_Failure
                 (implode "Kernel.compute: free variables in starting expression"))
          (st_ex_bind (compute_map check_eqn ceqs) (\ceqs.
           st_ex_ignore_bind
             (if ALL_DISTINCT (MAP FST ceqs) then st_ex_return one else
                holKernel_raise_Failure
                  (implode "Kernel.compute: non-distinct function names in equations"))
           (let ars = MAP (\(f,(n,r)). (f,LENGTH n)) ceqs in
            st_ex_ignore_bind (check_consts ars (implode "starting cexpr") cexp)
            (st_ex_ignore_bind (compute_map (\(f,(n,r)). check_consts ars f r) ceqs)
             (st_ex_bind
                (exec (build_funs ceqs) [] compute_default_clock (to_ce ceqs [] cexp))
                (\res.
              st_ex_bind (holKernel_mk_eq (tm,cv2term res)) (\c.
              st_ex_return (Sequent [] c)))))))))`;;

compute_overloads_off ();;
