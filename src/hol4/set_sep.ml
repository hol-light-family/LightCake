(* ========================================================================= *)
(* set_sep: port of HOL4 examples/machine-code/hoare-triple/set_sepScript.sml *)
(* (HOL4 library used by CakeML v3479): separation logic over sets of        *)
(* resources (STAR, SEP_EXISTS, emp, cond, fun2set ...), as used by the      *)
(* data_to_word proofs.                                                      *)
(*                                                                           *)
(* Notation: HOL4 overloads multiplication for STAR p q; here STAR is an   *)
(* infix, p STAR q, left associative like the HOL4 overload: p STAR q STAR  *)
(* r is (p STAR q) STAR r, and the bare constant is (STAR).  HOL4 p \/ q on *)
(* assertions is SEP_DISJ p q and ~p is SEP_HIDE p.  HOL4 one (HOL Light     *)
(* has the constant one:1) is set_sep_one, with set_sep_one_def.             *)
(* SEP_EXISTS is a binder (SEP_EXISTS x. p x); the bare constant is          *)
(* (SEP_EXISTS).  HOL4 names that HOL Light or basic.ml already use with    *)
(* another statement get the prefix set_sep_ (set_sep_DIFF_UNION,            *)
(* set_sep_IMP_IMP); helper lemmas that are not HOL4 theorems are LSORTAUX_. *)
(* SEP_ARRAY (words) is not ported: the closure does not use it.             *)
(* ========================================================================= *)

needs "hol4/vocab.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

let set_sep_one_def = new_definition
  `set_sep_one (x:A) = \s. s = {x}`;;

let emp_def = new_definition
  `emp = \s:A->bool. s = {}`;;

let cond_def = new_definition
  `cond c = \s:A->bool. s = {} /\ c`;;

let SEP_F_def = new_definition
  `SEP_F (s:A->bool) <=> F`;;

let SEP_T_def = new_definition
  `SEP_T (s:A->bool) <=> T`;;

let SPLIT_def = new_definition
  `SPLIT (s:A->bool) (u,v) <=> u UNION v = s /\ DISJOINT u v`;;

let STAR_def = new_definition
  `STAR (p:(A->bool)->bool) q = \s. ?u v. SPLIT s (u,v) /\ p u /\ q v`;;

parse_as_infix("STAR",(19,"left"));;

let SEP_EQ_def = new_definition
  `SEP_EQ (x:A->bool) = \s. s = x`;;

let SEP_EXISTS = new_definition
  `SEP_EXISTS = \(f:B->(A->bool)->bool) (s:A->bool). ?y. f y s`;;

parse_as_binder "SEP_EXISTS";;

let SEP_HIDE_def = new_definition
  `SEP_HIDE (p:B->(A->bool)->bool) = SEP_EXISTS x. p x`;;

let SEP_DISJ_def = new_definition
  `SEP_DISJ (p:(A->bool)->bool) q = \s. p s \/ q s`;;

let sidecond_def = new_definition
  `sidecond = (cond:bool->(A->bool)->bool)`;;

let precond_def = new_definition
  `precond = (cond:bool->(A->bool)->bool)`;;

let SEP_IMP_def = new_definition
  `SEP_IMP (p:(A->bool)->bool) q <=> !s. p s ==> q s`;;

let fun2set_def = new_definition
  `fun2set (f:B->A,d) = {(a,f a) | a IN d}`;;

(* ------------------------------------------------------------------------- *)
(* The separating conjunction and the clauses of the assertion language.    *)
(* HOL4 SPLIT_EQ is stated here (before STAR_COMM) since the proofs use it.  *)
(* ------------------------------------------------------------------------- *)

let SPLIT_EQ = prove
 (`!s u v:A->bool. SPLIT s (u,v) <=> u SUBSET s /\ v = s DIFF u`,
  REWRITE_TAC[SPLIT_def] THEN SET_TAC[]);;

let LSORTAUX_STAR_THM = prove
 (`!p q (s:A->bool). (p STAR q) s <=> ?u. u SUBSET s /\ p u /\ q (s DIFF u)`,
  REWRITE_TAC[STAR_def; SPLIT_EQ] THEN MESON_TAC[]);;

let STAR_COMM = prove
 (`!p q:(A->bool)->bool. p STAR q = q STAR p`,
  REWRITE_TAC[FUN_EQ_THM; STAR_def; SPLIT_def] THEN
  MESON_TAC[UNION_COMM; DISJOINT_SYM]);;

let STAR_ASSOC = prove
 (`!p q r:(A->bool)->bool. p STAR (q STAR r) = (p STAR q) STAR r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; LSORTAUX_STAR_THM] THEN
  X_GEN_TAC `s:A->bool` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v:A->bool`
        STRIP_ASSUME_TAC)))) THEN
    EXISTS_TAC `u UNION v:A->bool` THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(u UNION v) DIFF u = v:A->bool` (fun th -> ASM_REWRITE_TAC[th]) THEN
      ASM SET_TAC[];
      SUBGOAL_THEN `s DIFF (u UNION v) = (s DIFF u) DIFF v:A->bool`
        (fun th -> ASM_REWRITE_TAC[th]) THEN SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `w:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC)
        ASSUME_TAC))) THEN
    EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `w DIFF u:A->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(s DIFF u) DIFF (w DIFF u) = s DIFF w:A->bool`
      (fun th -> ASM_REWRITE_TAC[th]) THEN ASM SET_TAC[]]);;

let LSORTAUX_DIFF_EMPTY_EQ = prove
 (`!u s:A->bool. u SUBSET s ==> (s DIFF u = {} <=> u = s)`,
  SET_TAC[]);;

let SEP_CLAUSES = prove
 (`!(p:B->(A->bool)->bool) (q:(A->bool)->bool) (t:(A->bool)->bool) c c'
    (x:B) (r:(A->bool)->bool).
     ((SEP_EXISTS v. p v) STAR q = SEP_EXISTS v. p v STAR q) /\
     (q STAR (SEP_EXISTS v. p v) = SEP_EXISTS v. q STAR p v) /\
     (SEP_DISJ (SEP_EXISTS v. p v) q = SEP_EXISTS v. SEP_DISJ (p v) q) /\
     (SEP_DISJ q (SEP_EXISTS v. p v) = SEP_EXISTS v. SEP_DISJ q (p v)) /\
     ((SEP_EXISTS v:B. q) = q) /\
     ((SEP_EXISTS v. p v STAR cond (v = x)) = p x) /\
     (SEP_DISJ q SEP_F = q) /\ (SEP_DISJ SEP_F q = q) /\
     (SEP_F STAR q = SEP_F) /\ (q STAR SEP_F = SEP_F) /\
     (SEP_DISJ r r = r) /\
     (q STAR SEP_DISJ r t = SEP_DISJ (q STAR r) (q STAR t)) /\
     (SEP_DISJ r t STAR q = SEP_DISJ (r STAR q) (t STAR q)) /\
     (SEP_DISJ (cond c) (cond c') = (cond (c \/ c'):(A->bool)->bool)) /\
     (cond c STAR cond c' = (cond (c /\ c'):(A->bool)->bool)) /\
     (cond T = (emp:(A->bool)->bool)) /\ (cond F = (SEP_F:(A->bool)->bool)) /\
     (emp STAR q = q) /\ (q STAR emp = q)`,
  let RW_TAC = GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
               REWRITE_TAC[SEP_EXISTS; LSORTAUX_STAR_THM; SEP_DISJ_def;
                           cond_def; SEP_F_def; emp_def] in
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THENL
   [RW_TAC THEN MESON_TAC[]; RW_TAC THEN MESON_TAC[];
    RW_TAC THEN MESON_TAC[]; RW_TAC THEN MESON_TAC[];
    RW_TAC;
    RW_TAC THEN X_GEN_TAC `s:A->bool` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:B` (X_CHOOSE_THEN `u:A->bool`
        STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `u:A->bool = s` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[LSORTAUX_DIFF_EMPTY_EQ];
        FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[]];
      DISCH_TAC THEN EXISTS_TAC `x:B` THEN EXISTS_TAC `s:A->bool` THEN
      ASM_REWRITE_TAC[SUBSET_REFL; DIFF_EQ_EMPTY]];
    RW_TAC; RW_TAC; RW_TAC; RW_TAC; RW_TAC;
    RW_TAC THEN MESON_TAC[]; RW_TAC THEN MESON_TAC[];
    RW_TAC THEN MESON_TAC[];
    RW_TAC THEN X_GEN_TAC `s:A->bool` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `s DIFF u = {}:A->bool` THEN
      ASM_REWRITE_TAC[DIFF_EMPTY];
      STRIP_TAC THEN EXISTS_TAC `{}:A->bool` THEN
      ASM_REWRITE_TAC[EMPTY_SUBSET; DIFF_EMPTY]];
    RW_TAC; RW_TAC;
    RW_TAC THEN X_GEN_TAC `s:A->bool` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(q:(A->bool)->bool) (s DIFF u)` THEN
      ASM_REWRITE_TAC[DIFF_EMPTY];
      DISCH_TAC THEN EXISTS_TAC `{}:A->bool` THEN
      ASM_REWRITE_TAC[DIFF_EMPTY; EMPTY_SUBSET]];
    RW_TAC THEN X_GEN_TAC `s:A->bool` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `u:A->bool = s` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[LSORTAUX_DIFF_EMPTY_EQ]; ASM_REWRITE_TAC[]];
      DISCH_TAC THEN EXISTS_TAC `s:A->bool` THEN
      ASM_REWRITE_TAC[SUBSET_REFL; DIFF_EQ_EMPTY]]]);;

let SEP_EXISTS_COND = prove
 (`!(p:B->(A->bool)->bool) c.
     (SEP_EXISTS v. p v STAR cond c) = (SEP_EXISTS v. p v) STAR cond c`,
  REWRITE_TAC[SEP_CLAUSES]);;

let SEP_EXISTS_THM = prove
 (`!(p:B->(A->bool)->bool) s. (SEP_EXISTS x. p x) s <=> ?x. p x s`,
  REWRITE_TAC[SEP_EXISTS]);;

let cond_STAR = prove
 (`!c (s:A->bool) p.
     ((cond c STAR p) s <=> c /\ p s) /\ ((p STAR cond c) s <=> c /\ p s)`,
  GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN
  REWRITE_TAC[SEP_CLAUSES] THEN REWRITE_TAC[SEP_F_def]);;

let one_STAR = prove
 (`!(x:A) s p. (set_sep_one x STAR p) s <=> x IN s /\ p (s DELETE x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LSORTAUX_STAR_THM; set_sep_one_def] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(p:(A->bool)->bool) (s DIFF u)` THEN
    UNDISCH_TAC `u SUBSET (s:A->bool)` THEN
    ASM_REWRITE_TAC[SING_SUBSET; SET_RULE `s DIFF {x:A} = s DELETE x`] THEN
    MESON_TAC[];
    STRIP_TAC THEN EXISTS_TAC `{x:A}` THEN
    ASM_REWRITE_TAC[SING_SUBSET; SET_RULE `s DIFF {x:A} = s DELETE x`]]);;

let EQ_STAR = prove
 (`!p s (t:A->bool). (SEP_EQ t STAR p) s <=> p (s DIFF t) /\ t SUBSET s`,
  REWRITE_TAC[LSORTAUX_STAR_THM; SEP_EQ_def; UNWIND_THM2] THEN MESON_TAC[]);;

let SEP_IMP_REFL = prove
 (`!p:(A->bool)->bool. SEP_IMP p p`,
  REWRITE_TAC[SEP_IMP_def]);;

let SEP_IMP_TRANS = prove
 (`!p q r:(A->bool)->bool. SEP_IMP p q /\ SEP_IMP q r ==> SEP_IMP p r`,
  REWRITE_TAC[SEP_IMP_def] THEN MESON_TAC[]);;

let SEP_IMP_FRAME = prove
 (`!p q:(A->bool)->bool. SEP_IMP p q ==> !r. SEP_IMP (p STAR r) (q STAR r)`,
  REWRITE_TAC[SEP_IMP_def; STAR_def] THEN MESON_TAC[]);;

let SEP_IMP_MOVE_COND = prove
 (`!c p q:(A->bool)->bool. SEP_IMP (p STAR cond c) q <=> c ==> SEP_IMP p q`,
  GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[SEP_CLAUSES] THEN
  REWRITE_TAC[SEP_IMP_def; SEP_F_def]);;

let SEP_IMP_emp = prove
 (`!p:(A->bool)->bool. SEP_IMP emp p <=> p {}`,
  REWRITE_TAC[SEP_IMP_def; emp_def] THEN MESON_TAC[]);;

let SEP_IMP_cond = prove
 (`!g h. SEP_IMP (cond g:(A->bool)->bool) (cond h) <=> g ==> h`,
  REWRITE_TAC[SEP_IMP_def; cond_def] THEN MESON_TAC[]);;

let SEP_IMP_STAR = prove
 (`!p p' q q':(A->bool)->bool.
     SEP_IMP p p' /\ SEP_IMP q q' ==> SEP_IMP (p STAR q) (p' STAR q')`,
  REWRITE_TAC[SEP_IMP_def; STAR_def] THEN MESON_TAC[]);;

let SEP_IMP_DISJ = prove
 (`!p p' q q':(A->bool)->bool.
     SEP_IMP p p' /\ SEP_IMP q q' ==> SEP_IMP (SEP_DISJ p q) (SEP_DISJ p' q')`,
  REWRITE_TAC[SEP_IMP_def; SEP_DISJ_def] THEN MESON_TAC[]);;

let SEP_IMP_EQ = prove
 (`!p q:(A->bool)->bool. p = q <=> SEP_IMP p q /\ SEP_IMP q p`,
  REWRITE_TAC[SEP_IMP_def; FUN_EQ_THM] THEN MESON_TAC[]);;

let SEP_IMP_EXISTS_EXISTS = prove
 (`!(p:B->(A->bool)->bool) q.
     (!x. SEP_IMP (p x) (q x)) ==> SEP_IMP ((SEP_EXISTS) p) ((SEP_EXISTS) q)`,
  REWRITE_TAC[SEP_IMP_def; SEP_EXISTS] THEN MESON_TAC[]);;

let SEP_IMP_SEP_HIDE = prove
 (`!(p:B->(A->bool)->bool) x. SEP_IMP (p x) (SEP_HIDE p)`,
  REWRITE_TAC[SEP_IMP_def; SEP_HIDE_def; SEP_EXISTS_THM] THEN MESON_TAC[]);;

let SEP_IMP_PRE_DISJ = prove
 (`!p1 p2 q:(A->bool)->bool.
     SEP_IMP (SEP_DISJ p1 p2) q <=> SEP_IMP p1 q /\ SEP_IMP p2 q`,
  REWRITE_TAC[SEP_IMP_def; SEP_DISJ_def] THEN MESON_TAC[]);;

let SEP_IMP_PRE_EXISTS = prove
 (`!(p:B->(A->bool)->bool) q.
     SEP_IMP (SEP_EXISTS x. p x) q <=> !x. SEP_IMP (p x) q`,
  REWRITE_TAC[SEP_IMP_def; SEP_EXISTS_THM] THEN MESON_TAC[]);;

let SEP_DISJ_COMM = prove
 (`!p q:(A->bool)->bool. SEP_DISJ p q = SEP_DISJ q p`,
  REWRITE_TAC[SEP_DISJ_def; FUN_EQ_THM] THEN MESON_TAC[]);;

let SEP_DISJ_ASSOC = prove
 (`!p q r:(A->bool)->bool.
     SEP_DISJ (SEP_DISJ p q) r = SEP_DISJ p (SEP_DISJ q r)`,
  REWRITE_TAC[SEP_DISJ_def; FUN_EQ_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* fun2set: a function and a domain as a set of address-value pairs.        *)
(* ------------------------------------------------------------------------- *)

let IN_fun2set = prove
 (`!(a:B) (y:A) h dh. (a,y) IN fun2set (h,dh) <=> h a = y /\ a IN dh`,
  REWRITE_TAC[fun2set_def; IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;

let fun2set_thm = prove
 (`!(f:B->A) d a x. fun2set (f,d) (a,x) <=> f a = x /\ a IN d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IN_fun2set] THEN REWRITE_TAC[IN]);;

let LSORTAUX_FUN2SET_EXTENSION = prove
 (`!s (t:A#B->bool). s = t <=> !a b. (a,b) IN s <=> (a,b) IN t`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM]);;

let fun2set_DELETE = prove
 (`!(a:B) (h:B->A) dh. fun2set (h,dh) DELETE (a,h a) = fun2set (h,dh DELETE a)`,
  REWRITE_TAC[LSORTAUX_FUN2SET_EXTENSION; IN_DELETE; IN_fun2set; PAIR_EQ] THEN
  MESON_TAC[]);;

let read_fun2set = prove
 (`!(a:B) (x:A) p f d.
     (set_sep_one (a,x) STAR p) (fun2set (f,d)) ==> f a = x /\ a IN d`,
  SIMP_TAC[one_STAR; IN_fun2set]);;

let write_fun2set = prove
 (`!(y:A) (a:B) x p f d.
     (set_sep_one (a,x) STAR p) (fun2set (f,d))
     ==> (p STAR set_sep_one (a,y)) (fun2set ((a =+ y) f,d))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[one_STAR; IN_fun2set] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[STAR_COMM] THEN
  ASM_REWRITE_TAC[one_STAR; IN_fun2set; APPLY_UPDATE_THM] THEN
  SUBGOAL_THEN
   `fun2set ((a =+ y) f,d) DELETE (a,y) = fun2set ((f:B->A),d) DELETE (a,x)`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[LSORTAUX_FUN2SET_EXTENSION; IN_DELETE; IN_fun2set; PAIR_EQ;
              APPLY_UPDATE_THM] THEN
  ASM_MESON_TAC[]);;

let fun2set_eq = prove
 (`!(f:B->A) g d. fun2set (f,d) = fun2set (g,d) <=> !a. a IN d ==> f a = g a`,
  REWRITE_TAC[LSORTAUX_FUN2SET_EXTENSION; IN_fun2set] THEN MESON_TAC[]);;

let one_fun2set = prove
 (`!(a:B) (x:A) p f d.
     (set_sep_one (a,x) STAR p) (fun2set (f,d)) <=>
     f a = x /\ a IN d /\ p (fun2set (f,d DELETE a))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[one_STAR; IN_fun2set] THEN
  ASM_CASES_TAC `(f:B->A) a = x` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[fun2set_DELETE]);;

let fun2set_NEQ = prove
 (`!(a:B) b (x:A) y f g p.
     (set_sep_one (a,x) STAR set_sep_one (b,y) STAR p) (fun2set (f,g))
     ==> ~(a = b)`,
  REWRITE_TAC[GSYM STAR_ASSOC; one_STAR; IN_DELETE; PAIR_EQ; IN_fun2set] THEN
  MESON_TAC[]);;

let fun2set_DIFF = prove
 (`!(f:B->A) x y. fun2set (f,x) DIFF fun2set (f,y) = fun2set (f,x DIFF y)`,
  REWRITE_TAC[LSORTAUX_FUN2SET_EXTENSION; IN_DIFF; IN_fun2set] THEN
  MESON_TAC[]);;

let SUBSET_fun2set = prove
 (`!v df (f:A->B). v SUBSET fun2set (f,df) ==> ?z. v = fun2set (f,z)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `{x:A | (x,(f:A->B) x) IN v}` THEN
  REWRITE_TAC[LSORTAUX_FUN2SET_EXTENSION; IN_fun2set; IN_ELIM_THM] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[SUBSET; FORALL_PAIR_THM; IN_fun2set]) THEN
  MESON_TAC[]);;

let fun2set_EMPTY = prove
 (`!(f:B->A) df. fun2set (f,df) = {} <=> df = {}`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_fun2set; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let LSORTAUX_SPLIT_fun2set_IMP = prove
 (`!(f:B->A) df u v.
     SPLIT (fun2set (f,df)) (u,v)
     ==> u = fun2set (f,df DIFF {x | (x,f x) IN v})`,
  REWRITE_TAC[SPLIT_def; DISJOINT; LSORTAUX_FUN2SET_EXTENSION; EXTENSION;
              IN_UNION; IN_INTER; NOT_IN_EMPTY; FORALL_PAIR_THM; IN_fun2set;
              IN_DIFF; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let LSORTAUX_SPLIT_SYM_IMP = prove
 (`!x u v:A->bool. SPLIT x (u,v) ==> SPLIT x (v,u)`,
  REWRITE_TAC[SPLIT_def] THEN MESON_TAC[UNION_COMM; DISJOINT_SYM]);;

let fun2set_STAR_IMP = prove
 (`!p q (f:B->A) df.
     (p STAR q) (fun2set (f,df))
     ==> ?x y. p (fun2set (f,df DIFF y)) /\ q (fun2set (f,df DIFF x))`,
  REWRITE_TAC[STAR_def] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LSORTAUX_SPLIT_SYM_IMP) THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP LSORTAUX_SPLIT_fun2set_IMP)) THEN
  ASM_MESON_TAC[]);;

let one_fun2set_IMP = prove
 (`!(a:B) (x:A) f df.
     set_sep_one (a,x) (fun2set (f,df)) ==> f a = x /\ a IN df`,
  REWRITE_TAC[set_sep_one_def] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM IN_fun2set] THEN ASM_REWRITE_TAC[IN_SING]);;

let set_sep_DIFF_UNION = prove
 (`!x y z:A->bool. x DIFF y DIFF z = x DIFF (y UNION z)`,
  SET_TAC[]);;

let SEP_REWRITE_THM = prove
 (`!(q:(A->bool)->bool) (p:B->(A->bool)->bool) x y.
     (!s. q s ==> x = y) ==> q STAR p x = q STAR p y /\ p x STAR q = p y STAR q`,
  REWRITE_TAC[FUN_EQ_THM; STAR_def] THEN MESON_TAC[]);;

let cond_CONJ = prove
 (`!c d. cond (c /\ d) = (cond c STAR cond d:(A->bool)->bool)`,
  REWRITE_TAC[SEP_CLAUSES]);;

let set_sep_IMP_IMP = prove
 (`!b c d. b /\ (c ==> d) ==> (b ==> c) ==> d`,
  MESON_TAC[]);;

let cond_ELIM = prove
 (`!c c' (P:(A->bool)->bool).
     (cond c STAR cond c' = (cond (c /\ c'):(A->bool)->bool)) /\
     (P STAR cond c STAR cond c' = P STAR cond (c /\ c'))`,
  REWRITE_TAC[GSYM STAR_ASSOC; SEP_CLAUSES]);;

let cond_MOVE = prove
 (`!c (P:(A->bool)->bool) Q.
     (cond c STAR P = P STAR cond c) /\
     (P STAR cond c STAR Q = P STAR Q STAR cond c)`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [MATCH_ACCEPT_TAC STAR_COMM;
    REWRITE_TAC[GSYM STAR_ASSOC] THEN AP_TERM_TAC THEN
    MATCH_ACCEPT_TAC STAR_COMM]);;

let cond_T = prove
 (`!p:(A->bool)->bool. (cond T STAR p = p) /\ (p STAR cond T = p)`,
  REWRITE_TAC[SEP_CLAUSES]);;

let SEP_IMP_EXISTS = prove
 (`!(p:B->(A->bool)->bool) x. SEP_IMP (p x) (SEP_EXISTS x. p x)`,
  REWRITE_TAC[SEP_IMP_def; SEP_EXISTS_THM] THEN MESON_TAC[]);;

let cond_STAR1_I = prove
 (`!c p (s:A->bool). (cond c STAR p) s <=> I c /\ p s`,
  REWRITE_TAC[I_THM; cond_STAR]);;
