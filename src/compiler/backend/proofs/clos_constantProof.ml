(* ========================================================================= *)
(* clos_constantProof: port of HOL4 compiler/backend/proofs/                 *)
(* clos_constantProofScript.sml (CakeML v3479).                              *)
(* Some functions that flatten a closLang/BVL/BVI/dataLang const tree into a *)
(* sequence of operations that share common data.                            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
needs "compiler/backend/semantics/closSem.ml";;

type_invention_error := true;;

(* naive implementation *)

let make_part_def = cake_def
  `make_part n (p:A) (aux:(A # num) list) =
     match ALOOKUP aux p with
       SOME k -> (n,k,aux)
     | NONE -> (n + 1,n,CONS (p,n) aux)`;;

let clos_constantProof_parts_def = cake_def
  `(clos_constantProof_parts (ConstInt i) n (aux:(const_part # num) list) =
      make_part n (clos_Int i) aux) /\
   (clos_constantProof_parts (ConstStr s) n aux = make_part n (clos_Str s) aux) /\
   (clos_constantProof_parts (ConstWord64 w) n aux = make_part n (clos_W64 w) aux) /\
   (clos_constantProof_parts (ConstCons t cs) n aux =
      let (n,rs,aux) = parts_list cs n aux in
        make_part n (clos_Con t rs) aux) /\
   (parts_list [] n aux = (n,[],aux)) /\
   (parts_list (CONS c cs) n aux =
      let (n,r,aux) = clos_constantProof_parts c n aux in
      let (n,rs,aux) = parts_list cs n aux in
        (n,CONS r rs,aux))`;;

let clos_constantProof_to_parts_def = cake_def
  `(clos_constantProof_to_parts (ConstInt i) = [clos_Int i]) /\
   (clos_constantProof_to_parts (ConstStr s) = [clos_Str s]) /\
   (clos_constantProof_to_parts (ConstWord64 w) = [clos_W64 w]) /\
   (clos_constantProof_to_parts (ConstCons t cs) =
      let (n,rs,aux) = parts_list cs 0 [] in
        REVERSE (CONS (clos_Con t rs) (MAP FST aux)))`;;

(* semantics *)

let build_part_def = cake_def
  `(build_part (mem:num->const) (clos_Int i) = ConstInt i) /\
   (build_part mem (clos_Str s) = ConstStr s) /\
   (build_part mem (clos_W64 w) = ConstWord64 w) /\
   (build_part mem (clos_Con t ns) = ConstCons t (MAP mem ns))`;;

let clos_constantProof_build_def = cake_def
  `(clos_constantProof_build (mem:num->const) i [] = mem (i - 1)) /\
   (clos_constantProof_build mem i (CONS p rest) =
      clos_constantProof_build ((i =+ build_part mem p) mem) (i + 1) rest)`;;

let build_const_def = cake_def
  `build_const xs = clos_constantProof_build (\x. ConstInt (&0)) 0 xs`;;

(* proof *)

let clos_constantProof_build_map_def = cake_def
  `(clos_constantProof_build_map (mem:num->const) i [] = mem) /\
   (clos_constantProof_build_map mem i (CONS p rest) =
      clos_constantProof_build_map ((i =+ build_part mem p) mem) (i + 1) rest)`;;

let build_mem_thm = prove
 (`!(mem:num->const) i xs y.
     clos_constantProof_build mem i (APPEND xs [y]) =
     clos_constantProof_build (clos_constantProof_build_map mem i xs) (i + LENGTH xs) [y]`,
  SUBGOAL_THEN `!xs (mem:num->const) i y.
     clos_constantProof_build mem i (APPEND xs [y]) =
     clos_constantProof_build (clos_constantProof_build_map mem i xs) (i + LENGTH xs) [y]`
    (fun th -> REWRITE_TAC[th]) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; clos_constantProof_build_map_def; LENGTH; ADD_CLAUSES] THEN
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [clos_constantProof_build_def] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `(i + 1) + n = SUC (i + n)`]);;

(* a local resolution tactic (HOL4 res_tac): every implicational assumption, *)
(* curried, is resolved with the other assumptions by MATCH_MP, as far as    *)
(* it goes                                                                   *)
let CLOSPROPSAUX_RES1_TAC : tactic = fun (asl,w as gl) ->
  let asms = map snd asl in
  let is_impth th = is_imp(snd(strip_forall(concl th))) in
  let imps = filter is_impth asms in
  let curry th = try PURE_REWRITE_RULE[IMP_CONJ] th with Failure _ -> th in
  let rec resolve depth th =
    if depth = 0 || not (is_impth th) then [th] else
    let rs = mapfilter (fun a -> MATCH_MP th a) asms in
    if rs = [] then [th] else flat (map (resolve (depth-1)) rs) in
  let results =
    flat (map (fun th -> let th' = curry th in
                 flat (map (resolve 4) (mapfilter (fun a -> MATCH_MP th' a) asms)))
              imps) in
  let results = filter (fun th ->
    not (exists (fun a -> aconv (concl a) (concl th)) asms)) results in
  EVERY (map CAKE_ASSUME_TAC results) gl;;

let parts_acc = prove
 (`(!c n aux m r res. clos_constantProof_parts c n aux = (m,r,res) ==> ?a. res = APPEND a aux) /\
   (!cs n aux m rs res. parts_list cs n aux = (m,rs,res) ==> ?a. res = APPEND a aux)`,
  MATCH_MP_TAC const_INDUCT THEN REWRITE_TAC[clos_constantProof_parts_def] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REPEAT PAIRARG_TAC THEN REPEAT STRIP_TAC THEN
  CLOSPROPSAUX_RES1_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[make_part_def; PAIR_EQ]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    is_comb (lhs (concl th)) && (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "option_CASE"
                                 with Failure _ -> false)))) THEN
  REPEAT(TOP_CASE_TAC THEN REWRITE_TAC[PAIR_EQ]) THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[APPEND; APPEND_ASSOC]);;

let conses_ok_def = cake_def
  `conses_ok (aux:(const_part # num) list) <=>
     (!n. n < LENGTH aux ==> ?p. EL n (REVERSE aux) = (p,n)) /\
     (!n rs m r. MEM (clos_Con n rs,r) aux /\ MEM m rs ==> m < r)`;;

let IMP_conses_ok_CONS = prove
 (`!x aux. (!n rs. x = clos_Con n rs ==> ALL (\m. m < LENGTH aux) rs) ==>
           conses_ok aux ==> conses_ok (CONS (x,LENGTH aux) aux)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[conses_ok_def] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[LENGTH; REVERSE; EL_APPEND; LENGTH_REVERSE] THEN
    DISCH_TAC THEN COND_CASES_TAC THENL
     [ASM_MESON_TAC[];
      SUBGOAL_THEN `n = LENGTH (aux:(const_part # num) list)` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[SUB_REFL; EL; HD] THEN MESON_TAC[]]];
    REWRITE_TAC[MEM; PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    ASM_MESON_TAC[ALL_MEM]]);;

let build_map_APPEND = prove
 (`!xs ys (m:num->const) n.
     clos_constantProof_build_map m n (APPEND xs ys) =
     clos_constantProof_build_map (clos_constantProof_build_map m n xs) (n + LENGTH xs) ys`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; clos_constantProof_build_map_def; LENGTH; ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `(n + 1) + l = SUC (n + l)`]);;

(* HOL4: LIST_REL_eq [local] (HOL4 leaves f free; the name LIST_REL_eq is a  *)
(* theorem of src/hol4/list.ml with another statement)                       *)
let CLOSPROPSAUX_LIST_REL_eq = prove
 (`!(f:B->A) l rs. ALL2 (\c r. f r = c) l rs <=> l = MAP f rs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `rs:B list` list_CASES) THEN
  ASM_REWRITE_TAC[ALL2; MAP; NOT_CONS_NIL; CONS_11] THEN MESON_TAC[]);;

let build_map_ignore = prove
 (`!xs (m:num->const) n k. k < n ==> clos_constantProof_build_map m n xs k = m k`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[clos_constantProof_build_map_def] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(n =+ build_part (m:num->const) h) m`; `n + 1`; `k:num`]) THEN
  ASM_SIMP_TAC[ARITH_RULE `k < n ==> k < n + 1`; APPLY_UPDATE_THM] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[LT_REFL]);;

let ALOOKUP_conses_ok_IMP = prove
 (`!aux x r.
     ALOOKUP aux x = SOME r /\ conses_ok aux ==>
     ?xs:(const_part # num) list ys:(const_part # num) list.
       MAP FST (REVERSE aux) =
       APPEND (APPEND (MAP FST (REVERSE xs)) [x]) (MAP FST (REVERSE ys)) /\
       LENGTH xs = r /\ r < LENGTH aux /\
       (!t ys y. x = clos_Con t ys /\ MEM y ys ==> y < r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[conses_ok_def] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ALOOKUP_MEM) THEN
  SUBGOAL_THEN `?n. n < LENGTH (REVERSE aux) /\
                    EL n (REVERSE aux) = (x:const_part,r:num)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM_EXISTS_EL; MEM_REVERSE]; ALL_TAC] THEN
  SUBGOAL_THEN `r:num = n` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o
      check (fun th -> try is_imp (snd (dest_forall (concl th))) &&
                       length (fst (strip_forall (concl th))) = 1 with Failure _ -> false)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_REVERSE]) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `REVERSE aux = APPEND (TAKE n (REVERSE aux))
                  (CONS (x:const_part,n:num) (DROP (SUC n) (REVERSE aux)))` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
      [GSYM (ISPECL [`n:num`; `REVERSE (aux:(const_part # num) list)`] TAKE_DROP)]) THEN
    AP_TERM_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC DROP_CONS_EL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `REVERSE (TAKE n (REVERSE (aux:(const_part # num) list)))` THEN
  EXISTS_TAC `REVERSE (DROP (SUC n) (REVERSE (aux:(const_part # num) list)))` THEN
  REWRITE_TAC[REVERSE_REVERSE; LENGTH_REVERSE] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[MAP_APPEND; MAP; GSYM APPEND_ASSOC; APPEND; FST];
    MATCH_MP_TAC LENGTH_TAKE THEN REWRITE_TAC[LENGTH_REVERSE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_REVERSE]) THEN ASM_ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_REVERSE]) THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_MESON_TAC[]]);;

(* local helpers for parts_thm *)
let CLOSPROPSAUX_build_part_cong = prove
 (`!p (M:num->const) M'.
     (!t rs y. p = clos_Con t rs /\ MEM y rs ==> M y = M' y) ==>
     build_part M p = build_part M' p`,
  MATCH_MP_TAC const_part_INDUCT THEN
  REWRITE_TAC[build_part_def; injectivity "const_part"; distinctness "const_part"] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[]);;

let CLOSPROPSAUX_build_map_lookup = prove
 (`!aux p k (m0:num->const).
     ALOOKUP aux p = SOME k /\ conses_ok aux ==>
     clos_constantProof_build_map m0 0 (MAP FST (REVERSE aux)) k =
     build_part (clos_constantProof_build_map m0 0 (MAP FST (REVERSE aux))) p /\ k < LENGTH aux`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP ALOOKUP_conses_ok_IMP) THEN
  ASM_REWRITE_TAC[build_map_APPEND; LENGTH_APPEND; LENGTH_MAP; LENGTH_REVERSE;
                  LENGTH; ADD_CLAUSES] THEN
  SIMP_TAC[build_map_ignore; ARITH_RULE `k < SUC k`] THEN
  REWRITE_TAC[clos_constantProof_build_map_def; APPLY_UPDATE_THM] THEN
  MATCH_MP_TAC CLOSPROPSAUX_build_part_cong THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `y < k:num` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[build_map_ignore; ARITH_RULE `y < k ==> y < SUC k`; APPLY_UPDATE_THM;
               ARITH_RULE `y < k ==> ~(k = y)`]);;

let CLOSPROPSAUX_build_map_new = prove
 (`!aux p n (m0:num->const).
     n = LENGTH aux ==>
     clos_constantProof_build_map m0 0 (MAP FST (REVERSE (CONS (p,n) aux))) n =
     build_part (clos_constantProof_build_map m0 0 (MAP FST (REVERSE aux))) p`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[REVERSE; MAP_APPEND; MAP; build_map_APPEND; LENGTH_MAP; LENGTH_REVERSE;
                  ADD_CLAUSES; clos_constantProof_build_map_def; APPLY_UPDATE_THM]);;

let CLOSPROPSAUX_build_map_ext = prove
 (`!(a:(const_part # num) list) aux j (m0:num->const).
     j < LENGTH aux ==>
     clos_constantProof_build_map m0 0 (MAP FST (REVERSE (APPEND a aux))) j =
     clos_constantProof_build_map m0 0 (MAP FST (REVERSE aux)) j`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REVERSE_APPEND; MAP_APPEND; build_map_APPEND; LENGTH_MAP; LENGTH_REVERSE;
              ADD_CLAUSES] THEN
  MATCH_MP_TAC build_map_ignore THEN ASM_REWRITE_TAC[]);;

let CLOSPROPSAUX_not_mem_bound = prove
 (`!(aux:(const_part # num) list) n. ALL (\(p,k). k < n) aux ==> ~MEM n (MAP SND aux)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; MEM; ALL] THEN GEN_TAC THEN
  MP_TAC(ISPEC `h:const_part # num` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:const_part` (X_CHOOSE_THEN `k:num` SUBST1_TAC)) THEN
  REWRITE_TAC[SND] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC);;

let CLOSPROPSAUX_make_part_ok = prove
 (`!n p aux m r res c.
     make_part n p aux = (m,r,res) /\ ALL_DISTINCT (MAP SND aux) /\ conses_ok aux /\
     n = LENGTH aux /\ ALL (\(p,k). k < n) aux /\
     (!t rs. p = clos_Con t rs ==> ALL (\k. k < n) rs) /\
     build_part (clos_constantProof_build_map (\x. ConstInt (&0)) 0 (MAP FST (REVERSE aux))) p =
     c ==>
     clos_constantProof_build_map (\x. ConstInt (&0)) 0 (MAP FST (REVERSE res)) r = c /\
     n <= m /\ r < m /\
     ALL_DISTINCT (MAP SND res) /\ conses_ok res /\ m = LENGTH res /\
     ALL (\(p,k). k < m) res`,
  REPEAT GEN_TAC THEN REWRITE_TAC[make_part_def] THEN
  CASES_ON `ALOOKUP (aux:(const_part # num) list) p` THEN
  REWRITE_TAC[case_def "option"; PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSPROPSAUX_build_map_new THEN REFL_TAC;
      ARITH_TAC;
      ARITH_TAC;
      ASM_SIMP_TAC[MAP; ALL_DISTINCT; CLOSPROPSAUX_not_mem_bound];
      MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] IMP_conses_ok_CONS) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[LENGTH; ADD1];
      REWRITE_TAC[ALL] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN
      UNDISCH_TAC `ALL (\(p,k). k < LENGTH (aux:(const_part # num) list)) aux` THEN
      MATCH_MP_TAC MONO_ALL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ARITH_TAC];
    MP_TAC(ISPECL [`res:(const_part # num) list`; `p:const_part`; `r:num`;
                   `\x:num. ConstInt (&0)`] CLOSPROPSAUX_build_map_lookup) THEN
    ASM_SIMP_TAC[LE_REFL]]);;

let parts_thm = prove
 (`(!c n aux m r res.
      clos_constantProof_parts c n aux = (m,r,res) /\ ALL_DISTINCT (MAP SND aux) /\ conses_ok aux /\
      n = LENGTH aux /\ ALL (\(p,k). k < n) aux ==>
      clos_constantProof_build_map (\x. ConstInt (&0)) 0 (MAP FST (REVERSE res)) r = c /\
      n <= m /\ r < m /\ ALL_DISTINCT (MAP SND res) /\ conses_ok res /\ m = LENGTH res /\
      ALL (\(p,k). k < m) res) /\
   (!cs n aux m rs res.
      parts_list cs n aux = (m,rs,res) /\ ALL_DISTINCT (MAP SND aux) /\ conses_ok aux /\
      n = LENGTH aux /\ ALL (\(p,k). k < n) aux ==>
      ALL2 (\c r. clos_constantProof_build_map (\x. ConstInt (&0)) 0 (MAP FST (REVERSE res)) r =
                  c) cs rs /\
      n <= m /\ ALL_DISTINCT (MAP SND res) /\ ALL (\k. k < m) rs /\
      conses_ok res /\ m = LENGTH res /\ ALL (\(p,k). k < m) res)`,
  MATCH_MP_TAC const_INDUCT THEN REWRITE_TAC[clos_constantProof_parts_def] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:num` THEN X_GEN_TAC `cs:const list` THEN DISCH_TAC THEN
    REPEAT GEN_TAC THEN PAIRARG_TAC THEN PAIRARG_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `aux:(const_part # num) list`; `n':num`;
                                  `rs:num list`; `aux':(const_part # num) list`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`n':num`; `clos_Con t rs`; `aux':(const_part # num) list`; `m:num`;
                   `r:num`; `res:(const_part # num) list`; `ConstCons t cs`]
                  CLOSPROPSAUX_make_part_ok) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[injectivity "const_part"; build_part_def; injectivity "const"] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[GSYM CLOSPROPSAUX_LIST_REL_eq];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    GEN_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC CLOSPROPSAUX_make_part_ok THEN
    MAP_EVERY EXISTS_TAC [`clos_Int a`; `aux:(const_part # num) list`] THEN
    ASM_REWRITE_TAC[build_part_def; distinctness "const_part"];
    GEN_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC CLOSPROPSAUX_make_part_ok THEN
    MAP_EVERY EXISTS_TAC [`clos_Str a`; `aux:(const_part # num) list`] THEN
    ASM_REWRITE_TAC[build_part_def; distinctness "const_part"];
    GEN_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC CLOSPROPSAUX_make_part_ok THEN
    MAP_EVERY EXISTS_TAC [`clos_W64 a`; `aux:(const_part # num) list`] THEN
    ASM_REWRITE_TAC[build_part_def; distinctness "const_part"];
    REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
    ASM_REWRITE_TAC[ALL2; ALL; LE_REFL];
    X_GEN_TAC `c:const` THEN X_GEN_TAC `cs:const list` THEN STRIP_TAC THEN
    REPEAT GEN_TAC THEN REPEAT PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    RVEQ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`LENGTH (aux:(const_part # num) list)`;
                                  `aux:(const_part # num) list`; `n':num`;
                                  `r:num`; `aux':(const_part # num) list`] o
                  check (fun th -> is_forall (concl th) &&
                    can (find_term (fun t -> t = `clos_constantProof_parts`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n':num`; `aux':(const_part # num) list`; `m:num`;
                                  `rs':num list`; `res:(const_part # num) list`] o
                  check (fun th -> is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(X_CHOOSE_TAC `a:(const_part # num) list` o
                MATCH_MP (CONJUNCT2 parts_acc) o
                check (fun th -> can (find_term (fun t -> t = `parts_list`)) (concl th))) THEN
    ASM_REWRITE_TAC[ALL2; ALL] THEN
    SUBGOAL_THEN `r < LENGTH (aux':(const_part # num) list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[CLOSPROPSAUX_build_map_ext; LENGTH_APPEND] THEN ASM_ARITH_TAC]);;

let build_const_to_parts = prove
 (`!c. build_const (clos_constantProof_to_parts c) = c`,
  GEN_TAC THEN CASES_ON `c:const` THEN
  REWRITE_TAC[clos_constantProof_to_parts_def; build_const_def] THENL
   [PAIRARG_TAC THEN PAIRARG_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] (CONJUNCT2 parts_thm))) THEN
    REWRITE_TAC[MAP; ALL_DISTINCT; LENGTH; ALL; conses_ok_def; MEM; CONJUNCT1 LT] THEN
    STRIP_TAC THEN
    REWRITE_TAC[REVERSE; MAP_REVERSE; build_mem_thm] THEN
    REWRITE_TAC[clos_constantProof_build_def; ADD_CLAUSES; ADD_SUB; APPLY_UPDATE_THM;
                build_part_def] THEN
    REWRITE_TAC[injectivity "const"] THEN CONV_TAC SYM_CONV THEN
    ASM_REWRITE_TAC[GSYM CLOSPROPSAUX_LIST_REL_eq];
    REWRITE_TAC[clos_constantProof_build_def; build_part_def; APPLY_UPDATE_THM] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[clos_constantProof_build_def; build_part_def; APPLY_UPDATE_THM] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[clos_constantProof_build_def; build_part_def; APPLY_UPDATE_THM] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

(* verification of the efficent version in clos_to_bvlTheory *)

let update_tag_def = cake_def
  `(update_tag (clos_Con t ns) = clos_Con (clos_tag_shift t) ns) /\
   (update_tag x = x)`;;

let update_tag_11 = prove
 (`!x y. update_tag x = update_tag y <=> x = y`,
  REPEAT GEN_TAC THEN CASES_ON `x:const_part` THEN CASES_ON `y:const_part` THEN
  REWRITE_TAC[update_tag_def; injectivity "const_part"; distinctness "const_part"] THEN
  MESON_TAC[clos_tag_shift_inj]);;

let good_hash_table_def = cake_def
  `good_hash_table (m:((const_part # num) list) spt) (aux:(const_part # num) list) <=>
     !k v. ALOOKUP aux k = SOME v <=>
           ?bucket. lookup (part_hash (update_tag k)) m = SOME bucket /\
                    ALOOKUP bucket (update_tag k) = SOME v`;;

(* a local tactic for add_part_thm: the hash table after an insertion *)
let CLOSPROPSAUX_GHT_TAC : tactic =
  REWRITE_TAC[good_hash_table_def; lookup_insert] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[good_hash_table_def]) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[ALOOKUP_THM] THEN
  ASM_CASES_TAC `x:const_part = k` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[injectivity "option"; UNWIND_THM1; ALOOKUP_THM];
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[injectivity "option"; UNWIND_THM1; ALOOKUP_THM; update_tag_11;
                    distinctness "option"]];;

let add_part_thm = prove
 (`!n x (m:((const_part # num) list) spt) aux n1 rs m1 acc1 n2 rs1 aux1.
     add_part n (update_tag x) m (MAP (update_tag o FST) aux) = (n1,rs,m1,acc1) /\
     make_part n x aux = (n2,rs1,aux1) /\
     good_hash_table m aux ==>
     n1 = n2 /\ rs = rs1 /\ MAP (update_tag o FST) aux1 = acc1 /\ good_hash_table m1 aux1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[add_part_def; make_part_def; LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN (CASE_TERM `ALOOKUP aux x =
     (match lookup (part_hash (update_tag x)) (m:((const_part # num) list) spt) with
        NONE -> NONE
      | SOME bucket -> ALOOKUP bucket (update_tag x)):num option`) ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[good_hash_table_def] o
                check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                                     "good_hash_table" with Failure _ -> false)) THEN
    DISCH_THEN(MP_TAC o SPEC `x:const_part`) THEN
    CASES_ON `lookup (part_hash (update_tag x)) (m:((const_part # num) list) spt)` THEN
    REWRITE_TAC[case_def "option"; distinctness "option"; injectivity "option";
                UNWIND_THM1] THEN
    MESON_TAC[cases "option"];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_eq (concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "ALOOKUP" with Failure _ -> false)
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  CASES_ON `lookup (part_hash (update_tag x)) (m:((const_part # num) list) spt)` THEN
  REWRITE_TAC[case_def "option"] THENL
   [ALL_TAC;
    CASES_ON `ALOOKUP (a:(const_part # num) list) (update_tag x)` THEN
    REWRITE_TAC[case_def "option"]] THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  ASM_REWRITE_TAC[MAP; o_THM] THEN CLOSPROPSAUX_GHT_TAC);;

(* local tactics for add_parts_thm *)
let CLOSPROPSAUX_RES_ROUNDS_TAC : tactic =
  CLOSPROPSAUX_RES1_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  CLOSPROPSAUX_RES1_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  CLOSPROPSAUX_RES1_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  CLOSPROPSAUX_RES1_TAC THEN RVEQ_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  ASM_REWRITE_TAC[];;

let CLOSPROPSAUX_ADD_PART_LEAF_TAC (c:term) : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN RVEQ_TAC THEN
  ASSUME_TAC(REWRITE_RULE[update_tag_def] (ISPECL [`n:num`; c] add_part_thm)) THEN
  CLOSPROPSAUX_RES1_TAC THEN ASM_REWRITE_TAC[];;

let add_parts_thm = prove
 (`(!l n (m:((const_part # num) list) spt) acc n1 rs m1 acc1 aux n2 rs1 aux1.
      add_parts l n m acc = (n1,rs,m1,acc1) /\
      clos_constantProof_parts l n aux = (n2,rs1,aux1) /\
      MAP (update_tag o FST) aux = acc /\ good_hash_table m aux ==>
      n1 = n2 /\ rs = rs1 /\ MAP (update_tag o FST) aux1 = acc1 /\
      good_hash_table m1 aux1) /\
   (!l n (m:((const_part # num) list) spt) acc n1 rs m1 acc1 aux n2 rs1 aux1.
      add_parts_list l n m acc = (n1,rs,m1,acc1) /\
      parts_list l n aux = (n2,rs1,aux1) /\
      MAP (update_tag o FST) aux = acc /\ good_hash_table m aux ==>
      n1 = n2 /\ rs = rs1 /\ MAP (update_tag o FST) aux1 = acc1 /\
      good_hash_table m1 aux1)`,
  MATCH_MP_TAC const_INDUCT THEN REWRITE_TAC[add_parts_def; clos_constantProof_parts_def] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN REPEAT PAIRARG_TAC THEN
    STRIP_TAC THEN CLOSPROPSAUX_RES1_TAC THEN RVEQ_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM (CONJUNCT1 update_tag_def)]) THEN
    ASSUME_TAC add_part_thm THEN CLOSPROPSAUX_RES1_TAC THEN ASM_REWRITE_TAC[];
    CLOSPROPSAUX_ADD_PART_LEAF_TAC `clos_Int a`;
    CLOSPROPSAUX_ADD_PART_LEAF_TAC `clos_Str a`;
    CLOSPROPSAUX_ADD_PART_LEAF_TAC `clos_W64 a`;
    REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC THEN RVEQ_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN REPEAT PAIRARG_TAC THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN RVEQ_TAC THEN CLOSPROPSAUX_RES_ROUNDS_TAC]);;

let compile_const_thm = prove
 (`!c. (!i. ~(c = ConstInt i)) /\ (!t. ~(c = ConstCons t [])) ==>
       compile_const c = BlockOp (Build (MAP update_tag (clos_constantProof_to_parts c)))`,
  GEN_TAC THEN CASES_ON `c:const` THEN
  REWRITE_TAC[compile_const_def; clos_constantProof_to_parts_def; update_tag_def; MAP;
              distinctness "const";
              injectivity "const"] THENL
   [DISCH_THEN(MP_TAC o SPEC `a0:num`) THEN
    STRUCT_CASES_TAC(ISPEC `a1:const list` list_CASES) THEN
    REWRITE_TAC[NULL; NOT_CONS_NIL] THEN
    REPEAT PAIRARG_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] (CONJUNCT2 add_parts_thm)) o
                check (fun th -> can (find_term (fun t -> t = `add_parts_list`)) (concl th))) THEN
    FIRST_ASSUM(fun th -> if can (find_term (fun t -> t = `parts_list`)) (concl th)
                          then DISCH_THEN(MP_TAC o C MATCH_MP th) else NO_TAC) THEN
    REWRITE_TAC[MAP; good_hash_table_def; ALOOKUP_THM; lookup_def; distinctness "option"] THEN
    STRIP_TAC THEN RVEQ_TAC THEN
    REWRITE_TAC[GSYM MAP_REVERSE; MAP; update_tag_def; MAP_MAP_o];
    MESON_TAC[]]);;

(* connection to closSem *)

let build_part'_def = cake_def
  `(build_part' (mem:num->clos_v) (clos_Int i) = clos_Number i) /\
   (build_part' mem (clos_Str s) = ByteVector (MAP (word o ORD) (explode s))) /\
   (build_part' mem (clos_W64 w) = clos_Word64 w) /\
   (build_part' mem (clos_Con t ns) = clos_Block t (MAP mem ns))`;;

let build'_def = cake_def
  `(build' (mem:num->clos_v) i [] = mem (i - 1)) /\
   (build' mem i (CONS p rest) = build' ((i =+ build_part' mem p) mem) (i + 1) rest)`;;

let build_const'_def = cake_def
  `build_const' xs = build' (\x. clos_Number (&0)) 0 xs`;;

let make_const_thm = prove
 (`!c. make_const c = build_const' (clos_constantProof_to_parts c)`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM build_const_to_parts] THEN
  REWRITE_TAC[build_const_def; build_const'_def] THEN
  SUBGOAL_THEN `!xs (m:num->const) n.
                  make_const (clos_constantProof_build m n xs) = build' (make_const o m) n xs`
    (fun th -> REWRITE_TAC[th]) THENL
   [LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[clos_constantProof_build_def; build'_def; o_THM] THEN
    REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; APPLY_UPDATE_THM] THEN GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[o_THM] THEN
    SPEC_TAC(`h:const_part`,`p:const_part`) THEN
    MATCH_MP_TAC const_part_INDUCT THEN
    REWRITE_TAC[build_part_def; build_part'_def; make_const_def; MAP_MAP_o; o_DEF];
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; make_const_def]]);;
