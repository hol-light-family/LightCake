(* ========================================================================= *)
(* loop_call: port of HOL4 pancake/loop_callScript.sml (CakeML v3479).       *)
(* Call optimisation for loopLang.                                           *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - Names as doc/names.tsv says: is_load is loop_call_is_load               *)
(*   (asm has is_load) and comp is loop_call_comp.                           *)
(* - The last row of the Arith case of comp (_ => l) is redundant, as in     *)
(*   HOL4 (every loop_arith constructor has a row before it).                *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "pancake/loopLang.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4: is_load *)

let loop_call_is_load_def = cake_def
  `(loop_call_is_load asm_Load <=> T) /\
   (loop_call_is_load Load8 <=> T) /\
   (loop_call_is_load Load16 <=> T) /\
   (loop_call_is_load asm_Load32 <=> T) /\
   (loop_call_is_load _ <=> F)`;;

(* HOL4: comp *)

let loop_call_comp_def = cake_def
  `(loop_call_comp (l:num spt) (loop_Skip:(A)loop_prog) = (loop_Skip, l)) /\
   (loop_call_comp l (loop_Call ret dest args handler) =
      ((match dest with
          SOME _ -> loop_Call ret dest args handler
        | NONE ->
            (match args with
               [] -> loop_Skip
             | _ ->
                 (match lookup (LAST args) l with
                    NONE -> loop_Call ret NONE args handler
                  | SOME n -> loop_Call ret (SOME n) (BUTLAST args) handler))),
       LN)) /\
   (loop_call_comp l (LocValue n m) = (LocValue n m, insert n m l)) /\
   (loop_call_comp l (loop_Assign n (loop_Var m)) =
      (loop_Assign n (loop_Var m),
       match (lookup n l, lookup m l) with
         (NONE, NONE) -> l
       | (SOME _, NONE) -> delete n l
       | (_, SOME loc) -> insert n loc l)) /\
   (loop_call_comp l (loop_Assign n e) =
      (loop_Assign n e,
       match lookup n l with
         NONE -> l
       | _ -> delete n l)) /\
   (loop_call_comp l (loop_ShMem op n e) = (loop_ShMem op n e, LN)) /\
   (loop_call_comp l (loop_Load32 m n) =
      (loop_Load32 m n,
       match lookup n l with
         NONE -> l
       | _ -> delete n l)) /\
   (loop_call_comp l (loop_LoadByte m n) =
      (loop_LoadByte m n,
       match lookup n l with
         NONE -> l
       | _ -> delete n l)) /\
   (loop_call_comp l (loop_Seq p q) =
      let (np, nl) = loop_call_comp l p in
      let (nq, nl) = loop_call_comp nl q in
        (loop_Seq np nq, LN)) /\
   (loop_call_comp l (loop_If c n ri p q ns) =
      let (np, nl) = loop_call_comp l p in
      let (nq, ml) = loop_call_comp l q in
        (loop_If c n ri np nq ns, LN)) /\
   (loop_call_comp l (loop_Loop ns p ms) =
      let (np, nl) = loop_call_comp LN p in
        (loop_Loop ns np ms, LN)) /\
   (loop_call_comp l (Mark p) =
      let (np, nl) = loop_call_comp l p in
        (Mark np, nl)) /\
   (loop_call_comp l (loop_FFI str n m n' m' nl) =
      (loop_FFI str n m n' m' nl, LN)) /\
   (loop_call_comp l loop_Tick = (loop_Tick, LN)) /\
   (loop_call_comp l (loop_Raise n) = (loop_Raise n, LN)) /\
   (loop_call_comp l (loop_Return vs) = (loop_Return vs, LN)) /\
   (loop_call_comp l (loop_Primitive lhss pop rhss) =
      (loop_Primitive lhss pop rhss, list_delete lhss l)) /\
   (loop_call_comp l (loop_Arith arith) =
      (loop_Arith arith,
       match arith with
         LLongMul r1 r2 r3 r4 ->
           (match (lookup r1 l, lookup r2 l) with
              (NONE, NONE) -> l
            | (SOME _, NONE) -> delete r1 l
            | (NONE, SOME loc) -> delete r2 l
            | _ -> delete r1 (delete r2 l))
       | LLongDiv r1 r2 r3 r4 r5 ->
           (match (lookup r1 l, lookup r2 l) with
              (NONE, NONE) -> l
            | (SOME _, NONE) -> delete r1 l
            | (NONE, SOME loc) -> delete r2 l
            | _ -> delete r1 (delete r2 l))
       | LDiv r1 r2 r3 ->
           (match lookup r1 l with
              NONE -> l
            | _ -> delete r1 l)
       | _ -> l)) /\
   (loop_call_comp l p = (p, l))`;;

let loop_call_comp_ind = cake_ind "loop_call_comp";;
