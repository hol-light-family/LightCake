(* ========================================================================= *)
(* setSpec: port of HOL4 candle/set-theory/setSpecScript.sml (CakeML        *)
(* v3479).  Specification of (roughly) Zermelo's set theory.  Two main       *)
(* definitions: is_set_theory (mem : U -> U -> bool) and                     *)
(* is_model (mem,indset,ch).                                                 *)
(* ========================================================================= *)

needs "misc/misc.ml";;

prioritize_num();;
type_invention_error := true;;

(* HOL4's SELECT_ELIM_TAC (HOL Light's tactic of that name is another one): *)
(* a goal Q (@x. P x) becomes (?x. P x) /\ (!x. P x ==> Q x).               *)

let CSETAUX_SELECT_ELIM_THM = prove
 (`!P (Q:A->bool). (?x. P x) /\ (!x. P x ==> Q x) ==> Q ((@) P)`,
  MESON_TAC[SELECT_AX]);;

let CSETAUX_SELECT_ELIM_TAC : tactic = fun (asl,w as gl) ->
  let t = find_term (fun t -> is_select t && subset (frees t) (frees w)) w in
  let p = rand t in
  let v = genvar (type_of t) in
  let q = mk_abs(v,subst [v,t] w) in
  let th = ISPECL [p; q] CSETAUX_SELECT_ELIM_THM in
  (MATCH_MP_TAC (CONV_RULE (RAND_CONV BETA_CONV) th) THEN BETA_TAC) gl;;

(* HOL4 writes x <: y for mem x y (an overload of the variable mem), and    *)
(* overloads suchthat, Pow, +, the empty set, Unit, One, Two, the pair     *)
(* comma, UNION, CROSS, Relspace, Funspace, the infix ' (apply), boolset    *)
(* (= Two), True, False, Boolean, Holds, Abstract, tuple and bigcross for   *)
(* the constants below applied to mem.  HOL Light has no such overloads:    *)
(* the constants are written with their mem argument, e.g. x suchthat P is *)
(* setSpec_sub mem x P and f ' x is apply mem f x.  The parameters sub,     *)
(* power, union and upair of is_separation, is_power, is_union and          *)
(* is_upair are written sub', power', union', upair' (sub and union are    *)
(* constants of other files; power and upair are constants of this file).   *)

let extensional_def = cake_def
  `extensional (mem:U->U->bool) <=> !x y. x = y <=> !a. mem a x <=> mem a y`;;

let is_separation_def = cake_def
  `is_separation (mem:U->U->bool) sub' <=>
     !x P. !a. mem a (sub' x P) <=> mem a x /\ P a`;;

let is_power_def = cake_def
  `is_power (mem:U->U->bool) power' <=>
     !x. !a. mem a (power' x) <=> !b. mem b a ==> mem b x`;;

let is_union_def = cake_def
  `is_union (mem:U->U->bool) union' <=>
     !x. !a. mem a (union' x) <=> ?b. mem a b /\ mem b x`;;

let is_upair_def = cake_def
  `is_upair (mem:U->U->bool) upair' <=>
     !x y. !a. mem a (upair' x y) <=> a = x \/ a = y`;;

let is_set_theory_def = cake_def
  `is_set_theory (mem:U->U->bool) <=>
     extensional mem /\
     (?sub. is_separation mem sub) /\
     (?power. is_power mem power) /\
     (?union. is_union mem union) /\
     (?upair. is_upair mem upair)`;;

let separation_unique = prove
 (`extensional (mem:U->U->bool) ==>
   !sub1 sub2. is_separation mem sub1 /\ is_separation mem sub2 ==> sub1 = sub2`,
  RW[is_separation_def; extensional_def; FUN_EQ_THM]);;

let power_unique = prove
 (`extensional (mem:U->U->bool) ==>
   !power1 power2. is_power mem power1 /\ is_power mem power2 ==> power1 = power2`,
  RW[is_power_def; extensional_def; FUN_EQ_THM]);;

let union_unique = prove
 (`extensional (mem:U->U->bool) ==>
   !union1 union2. is_union mem union1 /\ is_union mem union2 ==> union1 = union2`,
  RW[is_union_def; extensional_def; FUN_EQ_THM]);;

let upair_unique = prove
 (`extensional (mem:U->U->bool) ==>
   !upair1 upair2. is_upair mem upair1 /\ is_upair mem upair2 ==> upair1 = upair2`,
  RW[is_upair_def; extensional_def; FUN_EQ_THM]);;

let setSpec_sub_def = cake_def
  `setSpec_sub (mem:U->U->bool) = @sub. is_separation mem sub`;;

let power_def = cake_def
  `power (mem:U->U->bool) = @power. is_power mem power`;;

let setSpec_union_def = cake_def
  `setSpec_union (mem:U->U->bool) = @union. is_union mem union`;;

let upair_def = cake_def
  `upair (mem:U->U->bool) = @upair. is_upair mem upair`;;

let is_extensional = prove
 (`is_set_theory (mem:U->U->bool) ==> extensional mem`,
  RW[is_set_theory_def]);;

let is_separation_sub = prove
 (`is_set_theory (mem:U->U->bool) ==> is_separation mem (setSpec_sub mem)`,
  RW[setSpec_sub_def] THEN CSETAUX_SELECT_ELIM_TAC THEN FS[is_set_theory_def] THEN
  ASM_MESON_TAC[]);;

let is_power_power = prove
 (`is_set_theory (mem:U->U->bool) ==> is_power mem (power mem)`,
  RW[power_def] THEN CSETAUX_SELECT_ELIM_TAC THEN FS[is_set_theory_def] THEN
  ASM_MESON_TAC[]);;

let is_union_union = prove
 (`is_set_theory (mem:U->U->bool) ==> is_union mem (setSpec_union mem)`,
  RW[setSpec_union_def] THEN CSETAUX_SELECT_ELIM_TAC THEN FS[is_set_theory_def] THEN
  ASM_MESON_TAC[]);;

let is_upair_upair = prove
 (`is_set_theory (mem:U->U->bool) ==> is_upair mem (upair mem)`,
  RW[upair_def] THEN CSETAUX_SELECT_ELIM_TAC THEN FS[is_set_theory_def] THEN
  ASM_MESON_TAC[]);;

let mem_sub = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !x s P. mem x (setSpec_sub mem s P) <=> mem x s /\ P x`,
  STRIP_TAC THEN IMP_RES_TAC is_separation_sub THEN FS[is_separation_def]);;

let mem_power = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !x y. mem x (power mem y) <=> (!b. mem b x ==> mem b y)`,
  STRIP_TAC THEN IMP_RES_TAC is_power_power THEN FS[is_power_def]);;

let mem_union = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !x s. mem x (setSpec_union mem s) <=> ?a. mem x a /\ mem a s`,
  STRIP_TAC THEN IMP_RES_TAC is_union_union THEN FS[is_union_def]);;

let mem_upair = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !a x y. mem a (upair mem x y) <=> a = x \/ a = y`,
  STRIP_TAC THEN IMP_RES_TAC is_upair_upair THEN FS[is_upair_def]);;

let setSpec_empty_def = cake_def
  `setSpec_empty (mem:U->U->bool) = setSpec_sub mem ARB (K F)`;;

let mem_empty = prove
 (`is_set_theory (mem:U->U->bool) ==> !x. ~(mem x (setSpec_empty mem))`,
  STRIP_TAC THEN IMP_RES_TAC is_separation_sub THEN
  FS[setSpec_empty_def; is_separation_def]);;

let unit_def = cake_def
  `unit (mem:U->U->bool) x = upair mem x x`;;

let mem_unit = prove
 (`is_set_theory (mem:U->U->bool) ==> !x y. mem x (unit mem y) <=> x = y`,
  STRIP_TAC THEN IMP_RES_TAC is_upair_upair THEN FS[is_upair_def; unit_def]);;

(* HOL4 rewrites with extensionality (fs[extensional_def, mem_unit]) and    *)
(* finishes by metis; here FS also rewrites the equations a = x that        *)
(* mem_unit produces, and METIS does not finish.  Instead: x is in unit x.  *)

let unit_inj = prove
 (`is_set_theory (mem:U->U->bool) ==> !x y. unit mem x = unit mem y <=> x = y`,
  MESON_TAC[mem_unit]);;

let setSpec_one_def = cake_def
  `setSpec_one (mem:U->U->bool) = unit mem (setSpec_empty mem)`;;

let mem_one = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !x. mem x (setSpec_one mem) <=> x = setSpec_empty mem`,
  STRIP_TAC THEN ASM_SIMP_TAC[mem_unit; setSpec_one_def]);;

let two_def = cake_def
  `two (mem:U->U->bool) = upair mem (setSpec_empty mem) (setSpec_one mem)`;;

let mem_two = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !x. mem x (two mem) <=> x = setSpec_empty mem \/ x = setSpec_one mem`,
  STRIP_TAC THEN ASM_SIMP_TAC[mem_upair; mem_one; two_def]);;

let setSpec_pair_def = cake_def
  `setSpec_pair (mem:U->U->bool) x y = upair mem (unit mem x) (upair mem x y)`;;

(* extensionality on the left side only (see unit_inj) *)

let upair_inj = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !a b c d. upair mem a b = upair mem c d <=> a = c /\ b = d \/ a = d /\ b = c`,
  STRIP_TAC THEN IMP_RES_TAC is_extensional THEN REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC LAND_CONV [REWRITE_RULE[extensional_def] th]) THEN
  ASM_SIMP_TAC[mem_upair] THEN MESON_TAC[]);;

let unit_eq_upair = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !x y z. unit mem x = upair mem y z <=> x = y /\ y = z`,
  STRIP_TAC THEN IMP_RES_TAC is_extensional THEN REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC LAND_CONV [REWRITE_RULE[extensional_def] th]) THEN
  ASM_SIMP_TAC[mem_unit; mem_upair] THEN MESON_TAC[]);;

let pair_inj = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !a b c d. setSpec_pair mem a b = setSpec_pair mem c d <=> a = c /\ b = d`,
  STRIP_TAC THEN
  ASM_SIMP_TAC[setSpec_pair_def; upair_inj; unit_inj; unit_eq_upair] THEN
  ASM_MESON_TAC[unit_eq_upair]);;

let binary_union_def = cake_def
  `binary_union (mem:U->U->bool) x y = setSpec_union mem (upair mem x y)`;;

let mem_binary_union = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !a x y. mem a (binary_union mem x y) <=> mem a x \/ mem a y`,
  STRIP_TAC THEN FS[binary_union_def; mem_union; mem_upair] THEN MESON_TAC[]);;

let setSpec_product_def = cake_def
  `setSpec_product (mem:U->U->bool) x y =
     setSpec_sub mem (power mem (power mem (binary_union mem x y)))
       (\a. ?b c. mem b x /\ mem c y /\ a = setSpec_pair mem b c)`;;

let mem_product = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !a x y. mem a (setSpec_product mem x y) <=>
           ?b c. a = setSpec_pair mem b c /\ mem b x /\ mem c y`,
  STRIP_TAC THEN
  ASM_SIMP_TAC[setSpec_product_def; mem_sub; mem_power; mem_binary_union] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; STRIP_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  ASM_SIMP_TAC[setSpec_pair_def; mem_upair; mem_unit; FORALL_AND_THM;
               TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
               FORALL_UNWIND_THM2] THEN
  ASM_MESON_TAC[]);;

(* a pair in a product (helper) *)

let CSETAUX_mem_pair_product = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !a b x y. mem (setSpec_pair mem a b) (setSpec_product mem x y) <=>
             mem a x /\ mem b y`,
  STRIP_TAC THEN ASM_SIMP_TAC[mem_product; pair_inj] THEN MESON_TAC[]);;

let relspace_def = cake_def
  `relspace (mem:U->U->bool) x y = power mem (setSpec_product mem x y)`;;

let funspace_def = cake_def
  `funspace (mem:U->U->bool) x y =
     setSpec_sub mem (relspace mem x y)
       (\f. !a. mem a x ==> ?!b. mem (setSpec_pair mem a b) f)`;;

let apply_def = cake_def
  `apply (mem:U->U->bool) x y = @a. mem (setSpec_pair mem y a) x`;;

let setSpec_true_def = cake_def
  `setSpec_true (mem:U->U->bool) = setSpec_empty mem`;;

let setSpec_false_def = cake_def
  `setSpec_false (mem:U->U->bool) = setSpec_one mem`;;

let true_neq_false = prove
 (`is_set_theory (mem:U->U->bool) ==> ~(setSpec_true mem = setSpec_false mem)`,
  REWRITE_TAC[setSpec_true_def; setSpec_false_def] THEN
  MESON_TAC[mem_one; mem_empty]);;

let mem_boolset = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !x. mem x (two mem) <=> (x = setSpec_true mem \/ x = setSpec_false mem)`,
  STRIP_TAC THEN ASM_SIMP_TAC[mem_two; setSpec_true_def; setSpec_false_def]);;

let boolean_def = cake_def
  `boolean (mem:U->U->bool) b =
     if b then setSpec_true mem else setSpec_false mem`;;

let boolean_in_boolset = prove
 (`is_set_theory (mem:U->U->bool) ==> !b. mem (boolean mem b) (two mem)`,
  STRIP_TAC THEN IMP_RES_TAC mem_boolset THEN GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  ASM_SIMP_TAC[boolean_def]);;

let boolean_eq_true = prove
 (`is_set_theory (mem:U->U->bool) ==> !b. boolean mem b = setSpec_true mem <=> b`,
  STRIP_TAC THEN RW[boolean_def] THEN ASM_MESON_TAC[true_neq_false]);;

let holds_def = cake_def
  `holds (mem:U->U->bool) s x <=> apply mem s x = setSpec_true mem`;;

let abstract_def = cake_def
  `abstract (mem:U->U->bool) dom rng f =
     setSpec_sub mem (setSpec_product mem dom rng)
       (\x. ?a. x = setSpec_pair mem a (f a))`;;

let apply_abstract = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !f x s t. mem x s /\ mem (f x) t ==> apply mem (abstract mem s t f) x = f x`,
  STRIP_TAC THEN RW[apply_def; abstract_def] THEN CSETAUX_SELECT_ELIM_TAC THEN
  ASM_SIMP_TAC[mem_sub; mem_product; pair_inj] THEN ASM_MESON_TAC[]);;

let apply_abstract_matchable = prove
 (`!f x s t u. mem x s /\ mem (f x) t /\ is_set_theory (mem:U->U->bool) /\
               f x = u ==> apply mem (abstract mem s t f) x = u`,
  MESON_TAC[apply_abstract]);;

let apply_in_rng = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !f x s t. mem x s /\ mem f (funspace mem s t) ==> mem (apply mem f x) t`,
  STRIP_TAC THEN
  ASM_SIMP_TAC[funspace_def; mem_sub; relspace_def; mem_power; apply_def;
               mem_product; EXISTS_UNIQUE_THM] THEN
  REPEAT STRIP_TAC THEN CSETAUX_SELECT_ELIM_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP pair_inj) THEN ASM_MESON_TAC[]);;

let abstract_in_funspace = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !f s t. (!x. mem x s ==> mem (f x) t) ==>
           mem (abstract mem s t f) (funspace mem s t)`,
  STRIP_TAC THEN
  ASM_SIMP_TAC[funspace_def; relspace_def; abstract_def; mem_power;
               mem_product; mem_sub] THEN
  ASM_SIMP_TAC[EXISTS_UNIQUE_THM; pair_inj] THEN MESON_TAC[]);;

let abstract_in_funspace_matchable = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !f s t fs. (!x. mem x s ==> mem (f x) t) /\ fs = funspace mem s t ==>
              mem (abstract mem s t f) fs`,
  MESON_TAC[abstract_in_funspace]);;

let abstract_eq = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !s t1 t2 f g.
     (!x. mem x s ==> mem (f x) t1 /\ mem (g x) t2 /\ f x = g x)
     ==> abstract mem s t1 f = abstract mem s t2 g`,
  RW[] THEN IMP_RES_TAC is_extensional THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC I [REWRITE_RULE[extensional_def] th]) THEN
  ASM_SIMP_TAC[abstract_def; mem_sub; mem_product] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN GVS[pair_inj] THEN ASM_MESON_TAC[]);;

let in_funspace_abstract = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !z s t. mem z (funspace mem s t) ==>
           ?f. z = abstract mem s t f /\ (!x. mem x s ==> mem (f x) t)`,
  RW[funspace_def; mem_sub; relspace_def; mem_power] THEN
  QEXISTS_TAC "\\x. @y. mem (setSpec_pair mem x y) z" THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CSETAUX_mem_pair_product) THEN
  QBY "!x y. mem (setSpec_pair mem x y) z ==> mem x s /\\ mem y t"
    (ASM_MESON_TAC[]) THEN
  QBY "!x. mem x s ==>
           mem (setSpec_pair mem x (@y. mem (setSpec_pair mem x y) z)) z"
    (REPEAT STRIP_TAC THEN CSETAUX_SELECT_ELIM_TAC THEN RFS[EXISTS_UNIQUE_THM]) THEN
  QBY "!x y. mem (setSpec_pair mem x y) z ==>
             y = @y. mem (setSpec_pair mem x y) z"
    (REPEAT STRIP_TAC THEN RES_TAC THEN RFS[EXISTS_UNIQUE_THM]) THEN
  CONJ_TAC THENL [ALL_TAC; BETA_TAC THEN ASM_MESON_TAC[]] THEN
  IMP_RES_TAC is_extensional THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC I [REWRITE_RULE[extensional_def] th]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP mem_product) THEN
  ASM_SIMP_TAC[abstract_def; mem_sub] THEN GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    QBY "?b c. a = setSpec_pair mem b c /\\ mem b s /\\ mem c t" (ASM_MESON_TAC[]) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[];
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP pair_inj) THEN ASM_MESON_TAC[]]);;

let axiom_of_choice = UNDISCH(prove
 (`is_set_theory (mem:U->U->bool) ==>
   !x. (!a. mem a x ==> ?b. mem b a) ==>
       ?f. !a. mem a x ==> mem (apply mem f a) a`,
  RW[] THEN
  QEXISTS_TAC "abstract mem x (setSpec_union mem x) (\\a. @b. mem b a)" THEN
  RW[] THEN
  QSUFF_TAC "apply mem (abstract mem x (setSpec_union mem x) (\\a. @b. mem b a)) a =
             (@b. mem b a)" THENL
   [DISCH_THEN SUBST1_TAC THEN CSETAUX_SELECT_ELIM_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC apply_abstract_matchable THEN
  ASM_SIMP_TAC[mem_union] THEN
  EXISTS_TAC `a:U` THEN ASM_REWRITE_TAC[] THEN
  CSETAUX_SELECT_ELIM_TAC THEN ASM_MESON_TAC[]));;

let is_choice_def = cake_def
  `is_choice (mem:U->U->bool) ch <=> !x. (?a. mem a x) ==> mem (ch x) x`;;

let is_infinite_def = cake_def
  `is_infinite (mem:U->U->bool) s <=> INFINITE {a | mem a s}`;;

let is_model_def = cake_def
  `is_model (mem:U->U->bool,indset:U,ch:U->U) <=>
     is_set_theory mem /\ is_infinite mem indset /\ is_choice mem ch`;;

let is_model_is_set_theory = prove
 (`is_model (mem:U->U->bool,indset:U,ch:U->U) ==> is_set_theory mem`,
  RW[is_model_def]);;

let indset_inhabited = prove
 (`is_infinite (mem:U->U->bool) indset ==> ?i. mem i indset`,
  RW[is_infinite_def] THEN IMP_RES_TAC INFINITE_NONEMPTY THEN
  FS[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let funspace_inhabited = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !s t. (?x. mem x s) /\ (?x. mem x t) ==> ?f. mem f (funspace mem s t)`,
  RW[] THEN QEXISTS_TAC "abstract mem s t (\\x. @x. mem x t)" THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP abstract_in_funspace) THEN
  REPEAT STRIP_TAC THEN CSETAUX_SELECT_ELIM_TAC THEN ASM_MESON_TAC[]);;

let tuple0_def = cake_def
  `(tuple0 (mem:U->U->bool) [] = setSpec_empty mem) /\
   (tuple0 mem (CONS a as) = setSpec_pair mem a (tuple0 mem as))`;;

let pair_not_empty = prove
 (`is_set_theory (mem:U->U->bool) ==>
   ~(setSpec_pair mem x y = setSpec_empty mem)`,
  STRIP_TAC THEN IMP_RES_TAC is_extensional THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [REWRITE_RULE[extensional_def] th]) THEN
  ASM_SIMP_TAC[mem_empty; setSpec_pair_def; mem_upair] THEN MESON_TAC[]);;

let tuple_empty = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !ls. tuple0 mem ls = setSpec_empty mem <=> ls = []`,
  STRIP_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[tuple0_def; pair_not_empty; NOT_CONS_NIL]);;

let tuple_inj = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !l1 l2. tuple0 mem l1 = tuple0 mem l2 <=> l1 = l2`,
  STRIP_TAC THEN LIST_INDUCT_TAC THEN SIMP[tuple0_def] THENL
   [ASM_MESON_TAC[tuple_empty]; ALL_TAC] THEN
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[tuple0_def; pair_not_empty; NOT_CONS_NIL] THEN
  ASM_SIMP_TAC[pair_inj; CONS_11]);;

let bigcross0_def = cake_def
  `(bigcross0 (mem:U->U->bool) [] = setSpec_one mem) /\
   (bigcross0 mem (CONS a as) = setSpec_product mem a (bigcross0 mem as))`;;

let mem_bigcross = prove
 (`is_set_theory (mem:U->U->bool) ==>
   !ls x. (mem x (bigcross0 mem ls) <=> ?xs. x = tuple0 mem xs /\ ALL2 mem xs ls)`,
  STRIP_TAC THEN LIST_INDUCT_TAC THEN
  SIMP[bigcross0_def; tuple0_def; mem_one] THEN
  SIMP[mem_product; PULL_EXISTS; tuple0_def; LIST_REL_CONS2]);;
