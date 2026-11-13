(* ========================================================================= *)
(* unify: port of HOL4 compiler/inference/unifyScript.sml (CakeML v3479).    *)
(* Defines a unification algorithm for use in the type inferencer, based on  *)
(* the triangular unification algorithm of HOL4's examples/algorithms/       *)
(* unification/triangular/first-order (src/hol4/term.ml ... unifProps.ml):   *)
(* CakeML types are encoded into the terms used there and the definitions    *)
(* and theorems are brought over.                                            *)
(* ========================================================================= *)

needs "misc/misc.ml";;
needs "compiler/inference/infer_t.ml";;
needs "hol4/term.ml";;
needs "hol4/subst.ml";;
needs "hol4/walk.ml";;
needs "hol4/walkstar.ml";;
needs "hol4/collapse.ml";;
needs "hol4/unifDef.ml";;
needs "hol4/unifProps.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Notes on the rendering:                                                   *)
(* - The terms of the unification library: HOL4 Var, Pair, Const, vars, oc   *)
(*   are term_Var, Pair, Const, term_vars, walkstar_oc (the type is          *)
(*   atom term_term); HOL4 s ' x is FAPPLY s x, s SUBMAP s' is SUBMAP,       *)
(*   walk-star (infix in HOL4) is walkstar, BIGUNION is UNIONS, set is       *)
(*   set_of_list, EXISTS is EX, EVERY is ALL, HOL4 I_o_f is unify_I_o_f.     *)
(* - HOL4's t_vwalk_ind (t_vwalk_ind' with the hypothesis t_wfs s            *)
(*   undischarged) is stated with it discharged: !s. t_wfs s ==> ...; the    *)
(*   local t_vwalk_ind' is the same theorem and is not bound separately.     *)
(* - HOL4's t_oc_ind' and t_oc_ind are commented out in the script.          *)
(* - Not ported (only used by unify_cv, the cv translation of the            *)
(*   inferencer, which the compile_correct closure does not contain): the    *)
(*   sptree-based implementation of HOL4 lines 139-2029 (RKC, substR, cwfs,  *)
(*   cvwalk, cwalk, coc, cunify, cunifyl, capply_subst, cwalkstar and their  *)
(*   continuation-passing and tail-recursive forms kcoc ... tcunify) and     *)
(*   t_walkstar_cwalkstar; of that block only t_vars_def is kept.            *)
(* - Helper lemmas that are not HOL4 theorems are TYSYS2AUX_.  HOL4 local    *)
(*   theorems keep their names.                                              *)
(* ------------------------------------------------------------------------- *)

let unify_I_o_f = prove
 (`!m:(A,B)fmap. I o_f m = m`,
  REWRITE_TAC[fmap_eq_flookup; FLOOKUP_o_f; I_THM] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `FLOOKUP (m:(A,B)fmap) x` (cases "option")) THEN
  REWRITE_TAC[option_CASE]);;

(* HOL4 [local,simp]: not registered (descendants do not see it in HOL4)     *)

let atom_INDUCT,atom_RECURSION = cake_type
  "atom = TC_tag type_ident
        | DB_tag num
        | Tapp_tag
        | Null_tag";;

let encode_infer_t_def = cake_def
  `(encode_infer_t (Infer_Tvar_db n) = Const (DB_tag n):atom term_term) /\
   (encode_infer_t (Infer_Tapp ts tc) =
      Pair (Const Tapp_tag) (Pair (Const (TC_tag tc)) (encode_infer_ts ts))) /\
   (encode_infer_t (Infer_Tuvar n) = term_Var n) /\
   (encode_infer_ts [] = Const Null_tag) /\
   (encode_infer_ts (CONS t ts) = Pair (encode_infer_t t) (encode_infer_ts ts))`;;

let encode_infer_t_11 = prove
 (`(!it1 it2. encode_infer_t it1 = encode_infer_t it2 <=> it1 = it2) /\
   (!its1 its2. encode_infer_ts its1 = encode_infer_ts its2 <=> its1 = its2)`,
  MATCH_MP_TAC infer_t_INDUCT THEN REPEAT STRIP_TAC THENL
   [CASES_ON `it2:infer_t`; CASES_ON `it2:infer_t`; CASES_ON `it2:infer_t`;
    CASES_ON `its2:infer_t list`; CASES_ON `its2:infer_t list`] THEN
  ASM_SIMP_TAC[encode_infer_t_def; injectivity "term_term"; distinctness "term_term";
               injectivity "atom"; distinctness "atom"; injectivity "infer_t";
               distinctness "infer_t"; CONS_11; NOT_CONS_NIL] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [encode_infer_t_11];;

(* HOL4's decode_infer_t_def is the list of clauses completed by TFL (the    *)
(* catch-all clauses split by constructor).  The kit's completion of these   *)
(* clauses takes minutes, so decode_infer_t and decode_infer_ts are defined  *)
(* by a match (TYSYS2AUX_decode_infer_t_match) and the completed clauses are *)
(* proved.                                                                   *)

let TYSYS2AUX_decode_infer_t_match = cake_def_wf
  `measure (\x:atom term_term + atom term_term.
              match x with INL t -> term_term_size (\a:atom. 0) t
                         | INR t -> term_term_size (\a:atom. 0) t)`
  TERM_TAC
  `(decode_infer_t (t:atom term_term) =
      match t with
        term_Var n -> Infer_Tuvar n
      | Const (DB_tag n) -> Infer_Tvar_db n
      | Pair (Const Tapp_tag) (Pair (Const (TC_tag tc)) s) ->
          Infer_Tapp (decode_infer_ts s) tc
      | _ -> Infer_Tuvar 5) /\
   (decode_infer_ts (t:atom term_term) =
      match t with
        Const Null_tag -> []
      | Pair s1 s2 -> CONS (decode_infer_t s1) (decode_infer_ts s2)
      | _ -> [])`;;

let decode_infer_t_def = prove
 (`(!n. decode_infer_t (term_Var n) = Infer_Tuvar n) /\
   (!n. decode_infer_t (Const (DB_tag n)) = Infer_Tvar_db n) /\
   (!tc s. decode_infer_t (Pair (Const Tapp_tag) (Pair (Const (TC_tag tc)) s)) =
           Infer_Tapp (decode_infer_ts s) tc) /\
   (!v5 v3. decode_infer_t (Pair (term_Var v5) v3) = Infer_Tuvar 5) /\
   (!v6 v7 v3. decode_infer_t (Pair (Pair v6 v7) v3) = Infer_Tuvar 5) /\
   (!v9 v3. decode_infer_t (Pair (Const (TC_tag v9)) v3) = Infer_Tuvar 5) /\
   (!v10 v3. decode_infer_t (Pair (Const (DB_tag v10)) v3) = Infer_Tuvar 5) /\
   (!v11. decode_infer_t (Pair (Const Tapp_tag) (term_Var v11)) = Infer_Tuvar 5) /\
   (!v15 v13. decode_infer_t (Pair (Const Tapp_tag) (Pair (term_Var v15) v13)) =
              Infer_Tuvar 5) /\
   (!v16 v17 v13. decode_infer_t (Pair (Const Tapp_tag) (Pair (Pair v16 v17) v13)) =
                  Infer_Tuvar 5) /\
   (!v20 v13.
      decode_infer_t (Pair (Const Tapp_tag) (Pair (Const (DB_tag v20)) v13)) =
      Infer_Tuvar 5) /\
   (!v13. decode_infer_t (Pair (Const Tapp_tag) (Pair (Const Tapp_tag) v13)) =
          Infer_Tuvar 5) /\
   (!v13. decode_infer_t (Pair (Const Tapp_tag) (Pair (Const Null_tag) v13)) =
          Infer_Tuvar 5) /\
   (!v14. decode_infer_t (Pair (Const Tapp_tag) (Const v14)) = Infer_Tuvar 5) /\
   (!v3. decode_infer_t (Pair (Const Null_tag) v3) = Infer_Tuvar 5) /\
   (!v21. decode_infer_t (Const (TC_tag v21)) = Infer_Tuvar 5) /\
   decode_infer_t (Const Tapp_tag) = Infer_Tuvar 5 /\
   decode_infer_t (Const Null_tag) = Infer_Tuvar 5 /\
   decode_infer_ts (Const Null_tag) = [] /\
   (!s1 s2. decode_infer_ts (Pair s1 s2) =
            CONS (decode_infer_t s1) (decode_infer_ts s2)) /\
   (!v1. decode_infer_ts (term_Var v1) = []) /\
   (!v5. decode_infer_ts (Const (TC_tag v5)) = []) /\
   (!v6. decode_infer_ts (Const (DB_tag v6)) = []) /\
   decode_infer_ts (Const Tapp_tag) = []`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [TYSYS2AUX_decode_infer_t_match] THEN
  REWRITE_TAC[case_def "term_term"; case_def "atom"]);;

let decode_left_inverse = prove
 (`(!t. decode_infer_t (encode_infer_t t) = t) /\
   (!ts. decode_infer_ts (encode_infer_ts ts) = ts)`,
  MATCH_MP_TAC infer_t_INDUCT THEN
  ASM_SIMP_TAC[encode_infer_t_def; decode_infer_t_def]);;
let _ = cake_add_simps [decode_left_inverse];;

let decode_left_inverse_I = prove
 (`decode_infer_t o encode_infer_t = I`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM; decode_left_inverse]);;
let _ = cake_add_simps [decode_left_inverse_I];;

let encode_eq_var = prove
 (`!n i. (term_Var n = encode_infer_t i <=> i = Infer_Tuvar n) /\
         (encode_infer_t i = term_Var n <=> i = Infer_Tuvar n)`,
  REPEAT GEN_TAC THEN CASES_ON `i:infer_t` THEN
  REWRITE_TAC[encode_infer_t_def; term_term_11; term_term_distinct;
              injectivity "infer_t"; distinctness "infer_t"] THEN
  MESON_TAC[]);;
let _ = cake_add_simps [encode_eq_var];;

(* HOL4 has this local theorem twice (lines 98 and 2030)                     *)

let decode_right_inverse = prove
 (`(!t. (?t'. t = encode_infer_t t') ==> encode_infer_t (decode_infer_t t) = t) /\
   (!ts. (?ts'. ts = encode_infer_ts ts')
         ==> encode_infer_ts (decode_infer_ts ts) = ts)`,
  MESON_TAC[decode_left_inverse]);;

let option_CASE_MAP = prove
 (`!(f:A->B) v (n:C) sf.
     option_CASE (OPTION_MAP f v) n sf = option_CASE v n (sf o f)`,
  REPEAT GEN_TAC THEN CASES_ON `v:A option` THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_CASE; o_THM]);;

let list_CASE_MAP = prove
 (`!(f:A->B) l (n:C) cf.
     list_CASE (MAP f l) n cf = list_CASE l n (\h t. cf (f h) (MAP f t))`,
  REPEAT GEN_TAC THEN CASES_ON `l:A list` THEN REWRITE_TAC[MAP; list_CASE]);;

let decode_option_CASE = prove
 (`!(v:A option) n sf.
     decode_infer_t (option_CASE v n sf) =
     option_CASE v (decode_infer_t n) (decode_infer_t o sf)`,
  REPEAT GEN_TAC THEN CASES_ON `v:A option` THEN
  REWRITE_TAC[option_CASE; o_THM]);;

let decode_infer_t_CASE = prove
 (`!it dbf appf uvf.
     decode_infer_t (infer_t_CASE it dbf appf uvf) =
     infer_t_CASE it (decode_infer_t o dbf)
                     (\l n. decode_infer_t (appf l n))
                     (decode_infer_t o uvf)`,
  REPEAT GEN_TAC THEN CASES_ON `it:infer_t` THEN
  REWRITE_TAC[case_def "infer_t"; o_THM]);;

(* HOL4 line 323 (in the block of the sptree implementation)                 *)

let t_vars_def = cake_def
  `t_vars (t:infer_t) = term_vars (encode_infer_t t)`;;
let t_wfs_def = cake_def
  `t_wfs (s:(num,infer_t)fmap) <=> wfs (encode_infer_t o_f s)`;;

let t_vwalk_def = cake_def
  `t_vwalk (s:(num,infer_t)fmap) v =
     decode_infer_t (vwalk (encode_infer_t o_f s) v)`;;

let TYSYS2AUX_FLOOKUP_encode = prove
 (`!(s:(num,infer_t)fmap) v.
     FLOOKUP (encode_infer_t o_f s) v = OPTION_MAP encode_infer_t (FLOOKUP s v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FLOOKUP_o_f] THEN
  CASES_ON `FLOOKUP (s:(num,infer_t)fmap) v` THEN
  REWRITE_TAC[option_CASE; OPTION_MAP_DEF]);;

(* HOL4 t_vwalk_ind' (local) and t_vwalk_ind (its instance with the          *)
(* hypothesis t_wfs s undischarged) are this theorem                         *)

let t_vwalk_ind = prove
 (`!s:(num,infer_t)fmap. t_wfs s ==>
     !P. (!v. (!v1 u. FLOOKUP s v = SOME v1 /\ v1 = Infer_Tuvar u ==> P u) ==> P v)
         ==> !v. P v`,
  GEN_TAC THEN REWRITE_TAC[t_wfs_def] THEN
  DISCH_THEN(MP_TAC o MATCH_MP vwalk_ind) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `P:num->bool` THEN
  MATCH_MP_TAC(TAUT `(b ==> a) ==> (a ==> c) ==> (b ==> c)`) THEN
  DISCH_THEN(LABEL_TAC "B") THEN X_GEN_TAC `v:num` THEN DISCH_TAC THEN
  USE_THEN "B" MATCH_MP_TAC THEN MAP_EVERY X_GEN_TAC [`v1:infer_t`; `u:num`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[TYSYS2AUX_FLOOKUP_encode; OPTION_MAP_DEF; encode_infer_t_def]);;

let t_vwalk_eqn = prove
 (CASE_TERM `!s:(num,infer_t)fmap. t_wfs s ==>
     !v. t_vwalk s v =
         match FLOOKUP s v with
           NONE -> Infer_Tuvar v
         | SOME (Infer_Tuvar u) -> t_vwalk s u
         | SOME (Infer_Tapp ts tc) -> Infer_Tapp ts tc
         | SOME (Infer_Tvar_db n) -> Infer_Tvar_db n`,
  REWRITE_TAC[t_wfs_def; t_vwalk_def] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [MATCH_MP vwalk_def th]) THEN
  REWRITE_TAC[TYSYS2AUX_FLOOKUP_encode] THEN
  SPEC_TAC(`FLOOKUP (s:(num,infer_t)fmap) v`,`opt:infer_t option`) THEN
  MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_CASE; decode_infer_t_def] THEN
  X_GEN_TAC `a:infer_t` THEN CASES_ON `a:infer_t` THEN
  REWRITE_TAC[encode_infer_t_def; case_def "term_term"; case_def "infer_t";
              decode_infer_t_def; decode_left_inverse]);;

let t_walk_def = cake_def
  `t_walk (s:(num,infer_t)fmap) t =
     decode_infer_t (walk (encode_infer_t o_f s) (encode_infer_t t))`;;

let t_walk_eqn = prove
 (`(!(s:(num,infer_t)fmap) v. t_walk s (Infer_Tuvar v) = t_vwalk s v) /\
   (!(s:(num,infer_t)fmap) ts tc. t_walk s (Infer_Tapp ts tc) = Infer_Tapp ts tc) /\
   (!(s:(num,infer_t)fmap) n. t_walk s (Infer_Tvar_db n) = Infer_Tvar_db n)`,
  REWRITE_TAC[t_walk_def; walk_walk_thm; t_vwalk_def; encode_infer_t_def] THEN
  REWRITE_TAC[GSYM encode_infer_t_def; decode_left_inverse]);;
let t_oc_def = cake_def
  `t_oc (s:(num,infer_t)fmap) t v =
     walkstar_oc (encode_infer_t o_f s) (encode_infer_t t) v`;;

let encode_vwalk = prove
 (`!s:(num,infer_t)fmap. t_wfs s ==>
     !u. vwalk (encode_infer_t o_f s) u = encode_infer_t (t_vwalk s u)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP t_vwalk_ind) THEN
  X_GEN_TAC `u:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `wfs (encode_infer_t o_f (s:(num,infer_t)fmap))` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_wfs_def]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [MATCH_MP vwalk_def th]) THEN
  FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [MATCH_MP t_vwalk_eqn th]) THEN
  REWRITE_TAC[TYSYS2AUX_FLOOKUP_encode] THEN
  CASES_ON `FLOOKUP (s:(num,infer_t)fmap) u` THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; option_CASE; encode_infer_t_def] THEN
  CASES_ON `a:infer_t` THEN
  REWRITE_TAC[encode_infer_t_def; case_def "term_term"; case_def "infer_t"] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MESON_TAC[]);;
let t_oc_eqn_help = prove
 (`!l v (s:(num,infer_t)fmap).
     walkstar_oc (encode_infer_t o_f s) (encode_infer_ts l) v <=>
     EX (\t. walkstar_oc (encode_infer_t o_f s) (encode_infer_t t) v) l`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[encode_infer_t_def; oc_thm; EX]);;

let t_oc_eqn = prove
 (CASE_TERM `!s:(num,infer_t)fmap. t_wfs s ==>
     !t v. t_oc s t v <=>
           match t_walk s t with
             Infer_Tuvar u -> v = u
           | Infer_Tapp ts tc -> EX (\t. t_oc s t v) ts
           | Infer_Tvar_db n -> F`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `wfs (encode_infer_t o_f (s:(num,infer_t)fmap))` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_wfs_def]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[t_oc_def] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [MATCH_MP oc_walking th]) THEN
  REWRITE_TAC[t_walk_def] THEN
  CASES_ON `t:infer_t` THEN
  ASM_SIMP_TAC[encode_infer_t_def; walk_walk_thm; encode_vwalk;
               decode_left_inverse] THEN
  TRY(CASES_ON `t_vwalk (s:(num,infer_t)fmap) a`) THEN
  ASM_SIMP_TAC[encode_infer_t_def; decode_infer_t_def; decode_left_inverse;
               case_def "term_term"; case_def "infer_t"; oc_thm; t_oc_eqn_help]);;

let t_ext_s_check_def = cake_def
  `t_ext_s_check (s:(num,infer_t)fmap) v t =
     OPTION_MAP ((o_f) decode_infer_t)
       (ext_s_check (encode_infer_t o_f s) v (encode_infer_t t))`;;

let t_ext_s_check_eqn = prove
 (`!(s:(num,infer_t)fmap) v t.
     t_ext_s_check s v t = if t_oc s t v then NONE else SOME (s |+ (v,t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[t_ext_s_check_def; ext_s_check_def; t_oc_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_INJ; o_f_FUPDATE; o_f_o_f;
              decode_left_inverse_I; unify_I_o_f; decode_left_inverse]);;
let t_unify_def = cake_def
  `t_unify (s:(num,infer_t)fmap) t1 t2 =
     OPTION_MAP ((o_f) decode_infer_t)
       (unify (encode_infer_t o_f s) (encode_infer_t t1) (encode_infer_t t2))`;;

let ts_unify_def = cake_def
  `(ts_unify (s:(num,infer_t)fmap) [] [] = SOME s) /\
   (ts_unify s (CONS t1 ts1) (CONS t2 ts2) =
      match t_unify s t1 t2 with
        NONE -> NONE
      | SOME s' -> ts_unify s' ts1 ts2) /\
   (ts_unify s _ _ = NONE)`;;

let ts_unify_ind = cake_ind "ts_unify";;

let encode_walk = prove
 (`!s:(num,infer_t)fmap. t_wfs s ==>
     !t. walk (encode_infer_t o_f s) (encode_infer_t t) =
         encode_infer_t (t_walk s t)`,
  REPEAT STRIP_TAC THEN CASES_ON `t:infer_t` THEN
  ASM_SIMP_TAC[encode_infer_t_def; walk_walk_thm; t_walk_eqn; encode_vwalk]);;

let encode_pair_cases = prove
 (`!t t1 t2.
     encode_infer_t t = Pair t1 t2
     ==> t1 = Const Tapp_tag /\
         ?tc ts. t2 = Pair (Const (TC_tag tc)) (encode_infer_ts ts)`,
  GEN_TAC THEN CASES_ON `t:infer_t` THEN
  REWRITE_TAC[encode_infer_t_def; term_term_distinct; term_term_11] THEN
  MESON_TAC[]);;

(* the pairs of terms that unify meets when it unifies two encoded types:    *)
(* the substitutions it builds are encoded ones                              *)

let TYSYS2AUX_good_def = new_definition
  `TYSYS2AUX_good (t1:atom term_term) t2 <=>
     (?a b. t1 = encode_infer_t a /\ t2 = encode_infer_t b) \/
     (?c1 c2. t1 = Const c1 /\ t2 = Const c2) \/
     (?c1 c2 ts1 ts2. t1 = Pair (Const c1) (encode_infer_ts ts1) /\
                      t2 = Pair (Const c2) (encode_infer_ts ts2)) \/
     (?ts1 ts2. t1 = encode_infer_ts ts1 /\ t2 = encode_infer_ts ts2)`;;

let TYSYS2AUX_encode_ts_cases = prove
 (`!ts. encode_infer_ts ts = Const Null_tag \/
        ?t ts'. ts = CONS t ts' /\
                encode_infer_ts ts = Pair (encode_infer_t t) (encode_infer_ts ts')`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[encode_infer_t_def; CONS_11] THEN MESON_TAC[]);;

let TYSYS2AUX_good_thms = prove
 (`(!a b. TYSYS2AUX_good (encode_infer_t a) (encode_infer_t b)) /\
   (!c1 c2. TYSYS2AUX_good (Const c1) (Const c2)) /\
   (!c1 c2 ts1 ts2. TYSYS2AUX_good (Pair (Const c1) (encode_infer_ts ts1))
                                   (Pair (Const c2) (encode_infer_ts ts2))) /\
   (!ts1 ts2. TYSYS2AUX_good (encode_infer_ts ts1) (encode_infer_ts ts2))`,
  REWRITE_TAC[TYSYS2AUX_good_def] THEN MESON_TAC[]);;

let TYSYS2AUX_good_walk = prove
 (`!(s0:(num,infer_t)fmap) t1 t2. t_wfs s0 /\ TYSYS2AUX_good t1 t2 ==>
     (!v. walk (encode_infer_t o_f s0) t1 = term_Var v ==>
          ?x. walk (encode_infer_t o_f s0) t2 = encode_infer_t x) /\
     (!v. walk (encode_infer_t o_f s0) t2 = term_Var v ==>
          ?x. walk (encode_infer_t o_f s0) t1 = encode_infer_t x) /\
     (!a0 a1 b0 b1. walk (encode_infer_t o_f s0) t1 = Pair a0 a1 /\
                    walk (encode_infer_t o_f s0) t2 = Pair b0 b1
                    ==> TYSYS2AUX_good a0 b0 /\ TYSYS2AUX_good a1 b1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o REWRITE_RULE[TYSYS2AUX_good_def])) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN
    (REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN SUBST1_TAC))) THENL
   [ASM_SIMP_TAC[encode_walk] THEN REPEAT CONJ_TAC THENL
     [MESON_TAC[]; MESON_TAC[]; ALL_TAC] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN (STRIP_ASSUME_TAC o MATCH_MP encode_pair_cases)) THEN
    ASM_REWRITE_TAC[TYSYS2AUX_good_thms];
    REWRITE_TAC[walk_walk_thm; term_term_distinct];
    REWRITE_TAC[walk_walk_thm; term_term_distinct; term_term_11] THEN
    REPEAT STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[TYSYS2AUX_good_thms];
    MAP_EVERY (fun t -> DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC)
                 (SPEC t TYSYS2AUX_encode_ts_cases))
              [`ts1:infer_t list`; `ts2:infer_t list`] THEN
    ASM_REWRITE_TAC[walk_walk_thm; term_term_distinct; term_term_11] THEN
    REPEAT STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[TYSYS2AUX_good_thms]]);;
let TYSYS2AUX_encodable_FUPDATE = prove
 (`!(s0:(num,infer_t)fmap) v t. (?x. t = encode_infer_t x) ==>
     ?s1. (encode_infer_t o_f s0) |+ (v,t) = encode_infer_t o_f s1`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(s0:(num,infer_t)fmap) |+ (v,x)` THEN REWRITE_TAC[o_f_FUPDATE]);;

let TYSYS2AUX_unify_encodable = prove
 (`!s t1 t2. wfs s /\ (?s0:(num,infer_t)fmap. s = encode_infer_t o_f s0) /\
             TYSYS2AUX_good t1 t2 ==>
     !sx. unify s t1 t2 = SOME sx ==> ?s1:(num,infer_t)fmap. sx = encode_infer_t o_f s1`,
  MATCH_MP_TAC unify_ind THEN
  MAP_EVERY X_GEN_TAC [`s:(num,atom term_term)fmap`; `t1:atom term_term`; `t2:atom term_term`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `s0:(num,infer_t)fmap` SUBST_ALL_TAC) ASSUME_TAC)) THEN
  SUBGOAL_THEN `t_wfs (s0:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[t_wfs_def]; ALL_TAC] THEN
  MP_TAC(SPECL [`s0:(num,infer_t)fmap`; `t1:atom term_term`; `t2:atom term_term`]
               TYSYS2AUX_good_walk) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sv1")
    (CONJUNCTS_THEN2 (LABEL_TAC "sv2") (LABEL_TAC "sp"))) THEN
  X_GEN_TAC `sx:(num,atom term_term)fmap` THEN
  MP_TAC(ISPECL [`encode_infer_t o_f (s0:(num,infer_t)fmap)`; `t1:atom term_term`;
                `t2:atom term_term`] unify_def) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CASES_ON `walk (encode_infer_t o_f (s0:(num,infer_t)fmap)) t1` THEN
  CASES_ON `walk (encode_infer_t o_f (s0:(num,infer_t)fmap)) t2` THEN
  REWRITE_TAC[term_term_CASE; ext_s_check_def; option_DISTINCT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[term_term_11; term_term_distinct]) THENL
   [ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC;
    USE_THEN "sp" (MP_TAC o SPECL [`a0:atom term_term`; `a1:atom term_term`;
                                   `a0':atom term_term`; `a1':atom term_term`]) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN
    CASES_ON `unify (encode_infer_t o_f (s0:(num,infer_t)fmap)) a0 a0'` THEN
    REWRITE_TAC[OPTION_BIND_DEF; option_DISTINCT] THEN DISCH_TAC THEN
    REMOVE_THEN "ih2" (MP_TAC o SPECL [`a0:atom term_term`; `a1:atom term_term`;
                                    `a0':atom term_term`; `a1':atom term_term`]) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `a:(num,atom term_term)fmap`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:(num,infer_t)fmap` SUBST_ALL_TAC) THEN
    REMOVE_THEN "ih1" (MP_TAC o SPECL [`a0:atom term_term`; `a1:atom term_term`;
                                    `a0':atom term_term`; `a1':atom term_term`;
                                    `encode_infer_t o_f (s1:(num,infer_t)fmap)`]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `wfs (encode_infer_t o_f (s1:(num,infer_t)fmap))` ASSUME_TAC THENL
     [ASM_MESON_TAC[unify_unifier]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC; ALL_TAC] THEN
  TRY COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  TRY(EXISTS_TAC `s0:(num,infer_t)fmap` THEN REFL_TAC) THEN
  MATCH_MP_TAC TYSYS2AUX_encodable_FUPDATE THEN
  ASM_MESON_TAC[encode_infer_t_def]);;
let TYSYS2AUX_decode_encodable = prove
 (`!sx:(num,atom term_term)fmap. (?s1:(num,infer_t)fmap. sx = encode_infer_t o_f s1)
     ==> encode_infer_t o_f (decode_infer_t o_f sx) = sx`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[o_f_o_f; GSYM o_ASSOC; decode_left_inverse_I; I_O_ID]);;

let TYSYS2AUX_decode_o_f_encode = prove
 (`!s:(num,infer_t)fmap. decode_infer_t o_f (encode_infer_t o_f s) = s`,
  REWRITE_TAC[o_f_o_f; GSYM o_ASSOC; decode_left_inverse_I; I_O_ID; unify_I_o_f]);;

let TYSYS2AUX_unify_Const = prove
 (`!(s:(num,A term_term)fmap) c1 c2. wfs s ==>
     unify s (Const c1) (Const c2) = if c1 = c2 then SOME s else NONE`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(num,A term_term)fmap`; `Const c1:A term_term`;
                 `Const c2:A term_term`] unify_def) THEN
  ASM_REWRITE_TAC[walk_walk_thm; term_term_CASE]);;

let TYSYS2AUX_unify_Pair = prove
 (`!(s:(num,A term_term)fmap) a b c d. wfs s ==>
     unify s (Pair a b) (Pair c d) = OPTION_BIND (unify s a c) (\sx. unify sx b d)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(num,A term_term)fmap`; `Pair a b:A term_term`;
                 `Pair c d:A term_term`] unify_def) THEN
  ASM_REWRITE_TAC[walk_walk_thm; term_term_CASE]);;

let TYSYS2AUX_unify_Pair_Const = prove
 (`!(s:(num,A term_term)fmap) c t1 t2. wfs s ==>
     unify s (Pair (Const c) t1) (Pair (Const c) t2) = unify s t1 t2`,
  SIMP_TAC[TYSYS2AUX_unify_Pair; TYSYS2AUX_unify_Const; OPTION_BIND_DEF]);;

let TYSYS2AUX_unify_Tapp = prove
 (`!(s:(num,atom term_term)fmap) ts1 ts2 tc. wfs s ==>
     unify s (encode_infer_t (Infer_Tapp ts1 tc)) (encode_infer_t (Infer_Tapp ts2 tc)) =
     unify s (encode_infer_ts ts1) (encode_infer_ts ts2)`,
  SIMP_TAC[encode_infer_t_def; TYSYS2AUX_unify_Pair_Const]);;

let TYSYS2AUX_unify_good = prove
 (`!(s0:(num,infer_t)fmap) t1 t2. t_wfs s0 /\ TYSYS2AUX_good t1 t2 ==>
     OPTION_MAP ((o_f) encode_infer_t)
       (OPTION_MAP ((o_f) decode_infer_t) (unify (encode_infer_t o_f s0) t1 t2)) =
     unify (encode_infer_t o_f s0) t1 t2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`encode_infer_t o_f (s0:(num,infer_t)fmap)`; `t1:atom term_term`;
                `t2:atom term_term`] TYSYS2AUX_unify_encodable) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[t_wfs_def]; ALL_TAC] THEN
  CASES_ON `unify (encode_infer_t o_f (s0:(num,infer_t)fmap)) t1 t2` THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_INJ] THEN
  DISCH_THEN(MP_TAC o SPEC `a:(num,atom term_term)fmap`) THEN REWRITE_TAC[] THEN
  DISCH_TAC THEN MATCH_MP_TAC TYSYS2AUX_decode_encodable THEN
  FIRST_ASSUM ACCEPT_TAC);;

let encode_unify_lemma = prove
 (`!s t1 t2 (s':(num,infer_t)fmap) t1' t2'.
     s = encode_infer_t o_f s' /\
     ((t1 = encode_infer_t t1' /\ t2 = encode_infer_t t2') \/
      (?c. t1 = Const c /\ t2 = Const c /\ t1' = t2') \/
      (?c ts1 ts2.
         t1 = Pair (Const c) (encode_infer_ts ts1) /\
         t2 = Pair (Const c) (encode_infer_ts ts2) /\
         t1' = Infer_Tapp ts1 ARB /\
         t2' = Infer_Tapp ts2 ARB) \/
      (?ts1 ts2.
         t1 = encode_infer_ts ts1 /\
         t2 = encode_infer_ts ts2 /\
         t1' = Infer_Tapp ts1 ARB /\
         t2' = Infer_Tapp ts2 ARB)) /\
     t_wfs s'
     ==> unify s t1 t2 = OPTION_MAP ((o_f) encode_infer_t) (t_unify s' t1' t2')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `wfs (encode_infer_t o_f (s':(num,infer_t)fmap))` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_wfs_def]; ALL_TAC] THEN
  REWRITE_TAC[t_unify_def] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN
    (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC))) THEN
  ASM_SIMP_TAC[TYSYS2AUX_unify_good; TYSYS2AUX_good_thms; TYSYS2AUX_unify_Tapp;
               TYSYS2AUX_unify_Pair_Const] THEN
  ASM_SIMP_TAC[unify_same; OPTION_MAP_DEF; TYSYS2AUX_decode_o_f_encode]);;

let encode_unify = prove
 (`!s t1 t2 (s':(num,infer_t)fmap) t1' t2'.
     s = encode_infer_t o_f s' /\
     t1 = encode_infer_t t1' /\ t2 = encode_infer_t t2' /\
     t_wfs s'
     ==> unify s t1 t2 = OPTION_MAP ((o_f) encode_infer_t) (t_unify s' t1' t2')`,
  MESON_TAC[encode_unify_lemma]);;

let wfs_unify = prove
 (`!(s:(num,A term_term)fmap) t1 t2 s'. wfs s /\ unify s t1 t2 = SOME s' ==> wfs s'`,
  MESON_TAC[unify_unifier]);;

let TYSYS2AUX_unify_Const_Pair = prove
 (`!(s:(num,A term_term)fmap) c a b. wfs s ==>
     unify s (Const c) (Pair a b) = NONE /\ unify s (Pair a b) (Const c) = NONE`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`s:(num,A term_term)fmap`; `Const c:A term_term`;
                   `Pair a b:A term_term`] unify_def);
    MP_TAC(ISPECL [`s:(num,A term_term)fmap`; `Pair a b:A term_term`;
                   `Const c:A term_term`] unify_def)] THEN
  ASM_REWRITE_TAC[walk_walk_thm; term_term_CASE]);;

let ts_unify_thm = prove
 (`!(s:(num,infer_t)fmap) l1 l2.
     t_wfs s
     ==> ts_unify s l1 l2 =
         OPTION_MAP ((o_f) decode_infer_t)
           (unify (encode_infer_t o_f s) (encode_infer_ts l1) (encode_infer_ts l2))`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  X_GEN_TAC `s:(num,infer_t)fmap` THEN LIST_INDUCT_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[t_wfs_def]) THEN
  ASM_SIMP_TAC[ts_unify_def; encode_infer_t_def; TYSYS2AUX_unify_Const;
               TYSYS2AUX_unify_Const_Pair; OPTION_MAP_DEF;
               TYSYS2AUX_decode_o_f_encode] THEN
  ASM_SIMP_TAC[TYSYS2AUX_unify_Pair; t_unify_def] THEN
  MP_TAC(SPECL [`encode_infer_t o_f (s:(num,infer_t)fmap)`;
                `encode_infer_t h`; `encode_infer_t h'`]
               TYSYS2AUX_unify_encodable) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[TYSYS2AUX_good_thms] THEN MESON_TAC[]; ALL_TAC] THEN
  CASES_ON `unify (encode_infer_t o_f (s:(num,infer_t)fmap)) (encode_infer_t h)
                  (encode_infer_t h')` THEN
  REWRITE_TAC[OPTION_MAP_DEF; OPTION_BIND_DEF; option_CASE] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:(num,infer_t)fmap` SUBST_ALL_TAC o
             C MATCH_MP (REFL `SOME (a:(num,atom term_term)fmap)`)) THEN
  REWRITE_TAC[TYSYS2AUX_decode_o_f_encode] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[t_wfs_def] THEN ASM_MESON_TAC[wfs_unify]);;
let t_unify_eqn = prove
 (CASE_TERM `!t1 t2 (s:(num,infer_t)fmap).
     t_wfs s ==>
     t_unify s t1 t2 =
       match (t_walk s t1, t_walk s t2) with
         (Infer_Tuvar v1, Infer_Tuvar v2) ->
           SOME (if v1 = v2 then s else s |+ (v1,Infer_Tuvar v2))
       | (Infer_Tuvar v1, t2) -> t_ext_s_check s v1 t2
       | (t1, Infer_Tuvar v2) -> t_ext_s_check s v2 t1
       | (Infer_Tapp ts1 tc1, Infer_Tapp ts2 tc2) ->
           if tc1 = tc2 then ts_unify s ts1 ts2 else NONE
       | (Infer_Tvar_db n1, Infer_Tvar_db n2) ->
           if n1 = n2 then SOME s else NONE
       | _ -> NONE`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[t_wfs_def]) THEN
  REWRITE_TAC[t_unify_def] THEN
  FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [MATCH_MP unify_def th]) THEN
  ASM_SIMP_TAC[encode_walk] THEN
  CASES_ON `t_walk (s:(num,infer_t)fmap) t1` THEN
  CASES_ON `t_walk (s:(num,infer_t)fmap) t2` THEN
  ASM_SIMP_TAC[encode_infer_t_def; term_term_CASE; case_def "infer_t";
               t_ext_s_check_def; TYSYS2AUX_unify_Const; TYSYS2AUX_unify_Pair;
               OPTION_BIND_DEF; OPTION_MAP_DEF; ts_unify_thm;
               injectivity "atom"] THEN
  TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF; OPTION_BIND_DEF; o_f_FUPDATE;
                  TYSYS2AUX_decode_o_f_encode; decode_infer_t_def]);;
let t_unify_ind = prove
 (`!(P0:(num,infer_t)fmap->infer_t->infer_t->bool)
    (P1:(num,infer_t)fmap->infer_t list->infer_t list->bool).
     (!s t1 t2.
        (!ts1 ts2 tc2.
           t_walk s t1 = Infer_Tapp ts1 tc2 /\
           t_walk s t2 = Infer_Tapp ts2 tc2 ==>
           P1 s ts1 ts2) ==>
        P0 s t1 t2) /\
     (!s ts1 ts2.
        (!t1 ts1' t2 ts2' s'.
           (ts1 = CONS t1 ts1' /\ ts2 = CONS t2 ts2') /\
           t_unify s t1 t2 = SOME s' ==>
           P1 s' ts1' ts2') /\
        (!t1 ts1' t2 ts2'.
           ts1 = CONS t1 ts1' /\ ts2 = CONS t2 ts2' ==> P0 s t1 t2) ==>
        P1 s ts1 ts2) ==>
     (!s t1 t2. t_wfs s ==> P0 s t1 t2) /\
     (!s ts1 ts2. t_wfs s ==> P1 s ts1 ts2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H0") (LABEL_TAC "H1")) THEN
  SUBGOAL_THEN
   `!s t1 t2. wfs s ==>
      !us:(num,infer_t)fmap. s = encode_infer_t o_f us ==>
        (!u1 u2. t1 = encode_infer_t u1 /\ t2 = encode_infer_t u2
                 ==> P0 us u1 u2) /\
        (!c u1 u2. t1 = Pair (Const c) (encode_infer_ts u1) /\
                   t2 = Pair (Const c) (encode_infer_ts u2)
                   ==> P1 us u1 u2) /\
        (!u1 u2. t1 = encode_infer_ts u1 /\ t2 = encode_infer_ts u2
                 ==> P1 us u1 u2)`
  (LABEL_TAC "Q") THENL
   [MATCH_MP_TAC unify_ind THEN
    MAP_EVERY X_GEN_TAC [`s:(num,atom term_term)fmap`; `t1:atom term_term`;
                         `t2:atom term_term`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih1") (LABEL_TAC "ih2")) THEN
    DISCH_TAC THEN X_GEN_TAC `us:(num,infer_t)fmap` THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `t_wfs (us:(num,infer_t)fmap)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[t_wfs_def]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`u1:infer_t`; `u2:infer_t`] THEN
      DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      USE_THEN "H0" MATCH_MP_TAC THEN
      MAP_EVERY X_GEN_TAC [`ts1:infer_t list`; `ts2:infer_t list`; `tc2:num`] THEN
      STRIP_TAC THEN
      REMOVE_THEN "ih1" (MP_TAC o SPECL
        [`Const Tapp_tag:atom term_term`;
         `Pair (Const (TC_tag tc2)) (encode_infer_ts ts1):atom term_term`;
         `Const Tapp_tag:atom term_term`;
         `Pair (Const (TC_tag tc2)) (encode_infer_ts ts2):atom term_term`;
         `encode_infer_t o_f (us:(num,infer_t)fmap)`]) THEN
      ASM_SIMP_TAC[encode_walk; encode_infer_t_def; TYSYS2AUX_unify_Const] THEN
      DISCH_THEN(MP_TAC o SPEC `us:(num,infer_t)fmap`) THEN REWRITE_TAC[] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`c:atom`; `u1:infer_t list`; `u2:infer_t list`] THEN
      DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      REMOVE_THEN "ih1" (MP_TAC o SPECL
        [`Const c:atom term_term`; `encode_infer_ts u1`;
         `Const c:atom term_term`; `encode_infer_ts u2`;
         `encode_infer_t o_f (us:(num,infer_t)fmap)`]) THEN
      ASM_SIMP_TAC[walk_walk_thm; TYSYS2AUX_unify_Const] THEN
      DISCH_THEN(MP_TAC o SPEC `us:(num,infer_t)fmap`) THEN REWRITE_TAC[] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`u1:infer_t list`; `u2:infer_t list`] THEN
      DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      USE_THEN "H1" MATCH_MP_TAC THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`v1:infer_t`; `u1':infer_t list`; `v2:infer_t`;
                             `u2':infer_t list`; `s':(num,infer_t)fmap`] THEN
        DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN SUBST_ALL_TAC) MP_TAC) THEN
        REWRITE_TAC[t_unify_def] THEN
        MP_TAC(SPECL [`encode_infer_t o_f (us:(num,infer_t)fmap)`;
                      `encode_infer_t v1`; `encode_infer_t v2`]
                     TYSYS2AUX_unify_encodable) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[TYSYS2AUX_good_thms] THEN MESON_TAC[]; ALL_TAC] THEN
        CASES_ON `unify (encode_infer_t o_f (us:(num,infer_t)fmap))
                        (encode_infer_t v1) (encode_infer_t v2)` THEN
        REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
        DISCH_THEN(MP_TAC o SPEC `a:(num,atom term_term)fmap`) THEN REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `s1:(num,infer_t)fmap` SUBST_ALL_TAC) THEN
        REWRITE_TAC[TYSYS2AUX_decode_o_f_encode] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        SUBGOAL_THEN `wfs (encode_infer_t o_f (s1:(num,infer_t)fmap))` ASSUME_TAC THENL
         [ASM_MESON_TAC[wfs_unify]; ALL_TAC] THEN
        REMOVE_THEN "ih1" (MP_TAC o SPECL
          [`encode_infer_t v1`; `encode_infer_ts u1'`;
           `encode_infer_t v2`; `encode_infer_ts u2'`;
           `encode_infer_t o_f (s1:(num,infer_t)fmap)`]) THEN
        ASM_REWRITE_TAC[encode_infer_t_def; walk_walk_thm] THEN
        DISCH_THEN(MP_TAC o SPEC `s1:(num,infer_t)fmap`) THEN REWRITE_TAC[] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN MESON_TAC[];
        MAP_EVERY X_GEN_TAC [`v1:infer_t`; `u1':infer_t list`; `v2:infer_t`;
                             `u2':infer_t list`] THEN
        DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
        REMOVE_THEN "ih2" (MP_TAC o SPECL
          [`encode_infer_t v1`; `encode_infer_ts u1'`;
           `encode_infer_t v2`; `encode_infer_ts u2'`]) THEN
        ASM_REWRITE_TAC[encode_infer_t_def; walk_walk_thm] THEN
        DISCH_THEN(MP_TAC o SPEC `us:(num,infer_t)fmap`) THEN REWRITE_TAC[] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN MESON_TAC[]]];
    ALL_TAC] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [REMOVE_THEN "Q" (MP_TAC o SPECL
      [`encode_infer_t o_f (s:(num,infer_t)fmap)`;
       `encode_infer_t t1`; `encode_infer_t t2`]);
    REMOVE_THEN "Q" (MP_TAC o SPECL
      [`encode_infer_t o_f (s:(num,infer_t)fmap)`;
       `encode_infer_ts ts1`; `encode_infer_ts ts2`])] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[REWRITE_RULE[t_wfs_def] th]) THEN
  DISCH_THEN(MP_TAC o SPEC `s:(num,infer_t)fmap`) THEN REWRITE_TAC[] THEN
  MESON_TAC[]);;
let apply_subst_t_def = cake_def
  `apply_subst_t (s:(num,infer_t)fmap) t =
     decode_infer_t (subst_APPLY (encode_infer_t o_f s) (encode_infer_t t))`;;

let TYSYS2AUX_apply_subst_ts = prove
 (`!(s:(num,infer_t)fmap) ts.
     decode_infer_ts (subst_APPLY (encode_infer_t o_f s) (encode_infer_ts ts)) =
     MAP (apply_subst_t s) ts`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[encode_infer_t_def; subst_APPLY_def; decode_infer_t_def; MAP;
                  apply_subst_t_def]);;

let apply_subst_t_eqn = prove
 (CASE_TERM `(!(s:(num,infer_t)fmap) n.
     apply_subst_t s (Infer_Tuvar n) =
       match FLOOKUP s n with
         NONE -> Infer_Tuvar n
       | SOME t -> t) /\
   (!(s:(num,infer_t)fmap) ts tc.
     apply_subst_t s (Infer_Tapp ts tc) = Infer_Tapp (MAP (apply_subst_t s) ts) tc) /\
   (!(s:(num,infer_t)fmap) n.
     apply_subst_t s (Infer_Tvar_db n) = Infer_Tvar_db n)`,
  REWRITE_TAC[apply_subst_t_def; encode_infer_t_def; subst_APPLY_def;
              decode_infer_t_def; TYSYS2AUX_FLOOKUP_encode;
              TYSYS2AUX_apply_subst_ts] THEN
  REPEAT GEN_TAC THEN CASES_ON `FLOOKUP (s:(num,infer_t)fmap) n` THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_CASE; decode_infer_t_def; decode_left_inverse]);;

let t_walkstar_def = cake_def
  `t_walkstar (s:(num,infer_t)fmap) t =
     decode_infer_t (walkstar (encode_infer_t o_f s) (encode_infer_t t))`;;

let ts_walkstar_thm = prove
 (`!l (s:(num,infer_t)fmap).
     t_wfs s
     ==> decode_infer_ts (walkstar (encode_infer_t o_f s) (encode_infer_ts l)) =
         MAP (t_walkstar s) l`,
  LIST_INDUCT_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[t_wfs_def]) THEN
  ASM_SIMP_TAC[encode_infer_t_def; walkstar_thm; decode_infer_t_def; MAP;
               GSYM t_walkstar_def]);;

let t_walkstar_eqn = prove
 (CASE_TERM `!s:(num,infer_t)fmap. t_wfs s ==>
     !t. t_walkstar s t =
         match t_walk s t with
           Infer_Tuvar v -> Infer_Tuvar v
         | Infer_Tapp ts tctor -> Infer_Tapp (MAP (t_walkstar s) ts) tctor
         | Infer_Tvar_db n -> Infer_Tvar_db n`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[t_wfs_def]) THEN
  GEN_REWRITE_TAC LAND_CONV [t_walkstar_def] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
                          [MATCH_MP walkstar_def th]) THEN
  ASM_SIMP_TAC[encode_walk] THEN
  CASES_ON `t_walk (s:(num,infer_t)fmap) t` THEN
  ASM_SIMP_TAC[encode_infer_t_def; term_term_CASE; case_def "infer_t";
               walkstar_thm; decode_infer_t_def; ts_walkstar_thm]);;

let t_walkstar_ind = prove
 (`!s:(num,infer_t)fmap. t_wfs s ==>
     !P. (!t. (!ts tt a. t_walk s t = Infer_Tapp ts tt /\ MEM a ts ==> P a) ==> P t)
         ==> !t. P t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wfs (encode_infer_t o_f (s:(num,infer_t)fmap))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM t_wfs_def]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:atom term_term.
      (!u. x = encode_infer_t u ==> P u) /\
      (!tag us. x = Pair (Const (TC_tag tag)) (encode_infer_ts us) ==> ALL P us) /\
      (!u us. x = Pair (encode_infer_t u) (encode_infer_ts us) ==> ALL P (CONS u us))`
   (fun th -> MESON_TAC[th]) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP walkstar_ind) THEN
  X_GEN_TAC `x:atom term_term` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "l") (LABEL_TAC "r")) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `u:infer_t` THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY X_GEN_TAC [`ts:infer_t list`; `tt:num`; `a:infer_t`] THEN STRIP_TAC THEN
    REMOVE_THEN "r" (MP_TAC o SPECL
      [`Const Tapp_tag:atom term_term`;
       `Pair (Const (TC_tag tt)) (encode_infer_ts ts):atom term_term`]) THEN
    ASM_SIMP_TAC[encode_walk; encode_infer_t_def] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o SPECL [`tt:num`; `ts:infer_t list`]) THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`tag:num`; `us:infer_t list`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    REMOVE_THEN "r" (MP_TAC o SPECL
      [`Const (TC_tag tag):atom term_term`; `encode_infer_ts us`]) THEN
    REWRITE_TAC[walk_walk_thm] THEN
    STRUCT_CASES_TAC(ISPEC `us:infer_t list` list_CASES) THEN
    REWRITE_TAC[ALL; encode_infer_t_def] THEN MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`u:infer_t`; `us:infer_t list`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    REMOVE_THEN "l" (MP_TAC o SPECL [`encode_infer_t u`; `encode_infer_ts us`]) THEN
    REMOVE_THEN "r" (MP_TAC o SPECL [`encode_infer_t u`; `encode_infer_ts us`]) THEN
    REWRITE_TAC[walk_walk_thm] THEN
    STRUCT_CASES_TAC(ISPEC `us:infer_t list` list_CASES) THEN
    REWRITE_TAC[ALL; encode_infer_t_def] THEN MESON_TAC[]]);;
let t_collapse_def = cake_def
  `t_collapse (s:(num,infer_t)fmap) =
     decode_infer_t o_f collapse (encode_infer_t o_f s)`;;

let t_collapse_eqn = prove
 (`!s:(num,infer_t)fmap.
     t_collapse s = FUN_FMAP (\v. t_walkstar s (Infer_Tuvar v)) (FDOM s)`,
  GEN_TAC THEN
  REWRITE_TAC[t_collapse_def; collapse_def; fmap_eq_flookup; FLOOKUP_o_f;
              FDOM_o_f] THEN
  SIMP_TAC[FLOOKUP_FUN_FMAP; FDOM_FINITE] THEN GEN_TAC THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[option_CASE; t_walkstar_def; encode_infer_t_def]);;

let TYSYS2AUX_SUBMAP_encode = prove
 (`!s1 s2:(num,infer_t)fmap.
     encode_infer_t o_f s1 SUBMAP encode_infer_t o_f s2 <=> s1 SUBMAP s2`,
  REWRITE_TAC[SUBMAP_FLOOKUP_EQN; TYSYS2AUX_FLOOKUP_encode] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `encode_infer_t y`]) THEN
    ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
    CASES_ON `FLOOKUP (s2:(num,infer_t)fmap) x` THEN
    REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ; encode_infer_t_11];
    CASES_ON `FLOOKUP (s1:(num,infer_t)fmap) x` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[OPTION_MAP_DEF; option_DISTINCT; option_INJ]) THEN
    RES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN ASM_MESON_TAC[]]);;

let t_unify_unifier = prove
 (`!(s:(num,infer_t)fmap) t1 t2 sx.
     t_wfs s /\ t_unify s t1 t2 = SOME sx
     ==> t_wfs sx /\ s SUBMAP sx /\ t_walkstar sx t1 = t_walkstar sx t2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`encode_infer_t o_f (s:(num,infer_t)fmap)`; `encode_infer_t t1`;
                `encode_infer_t t2`; `s:(num,infer_t)fmap`; `t1:infer_t`; `t2:infer_t`]
               encode_unify) THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`encode_infer_t o_f (s:(num,infer_t)fmap)`; `encode_infer_t t1`;
                 `encode_infer_t t2`; `encode_infer_t o_f (sx:(num,infer_t)fmap)`]
                unify_unifier) THEN
  ASM_REWRITE_TAC[GSYM t_wfs_def; TYSYS2AUX_SUBMAP_encode] THEN
  SIMP_TAC[t_walkstar_def]);;

let t_unify_strongind' = prove
 (`!(P0:(num,infer_t)fmap->infer_t->infer_t->bool)
    (P1:(num,infer_t)fmap->infer_t list->infer_t list->bool).
     (!s t1 t2.
        t_wfs s /\
        (!ts1 ts2 tc2.
           t_walk s t1 = Infer_Tapp ts1 tc2 /\
           t_walk s t2 = Infer_Tapp ts2 tc2 ==>
           P1 s ts1 ts2) ==>
        P0 s t1 t2) /\
     (!s ts1 ts2.
        t_wfs s /\
        (!t1 ts1' t2 ts2' s'.
           (ts1 = CONS t1 ts1' /\ ts2 = CONS t2 ts2') /\
           t_unify s t1 t2 = SOME s' ==>
           P1 s' ts1' ts2') /\
        (!t1 ts1' t2 ts2'.
           ts1 = CONS t1 ts1' /\ ts2 = CONS t2 ts2' ==> P0 s t1 t2) ==>
        P1 s ts1 ts2) ==>
     (!s t1 t2. t_wfs s ==> (t_wfs s ==> P0 s t1 t2)) /\
     (!s ts1 ts2. t_wfs s ==> (t_wfs s ==> P1 s ts1 ts2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H0") (LABEL_TAC "H1")) THEN
  MATCH_MP_TAC t_unify_ind THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(LABEL_TAC "ih") THEN DISCH_TAC THENL
   [USE_THEN "H0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    USE_THEN "ih" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o SPEC_ALL) THEN
    ASM_MESON_TAC[];
    USE_THEN "H1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    REPEAT STRIP_TAC THENL
     [USE_THEN "ih" (MATCH_MP_TAC o CONJUNCT1 o REWRITE_RULE[IMP_IMP; FORALL_AND_THM;
                                        TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`]);
      USE_THEN "ih" (MATCH_MP_TAC o CONJUNCT2 o REWRITE_RULE[IMP_IMP; FORALL_AND_THM;
                                        TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`])] THEN
    ASM_MESON_TAC[t_unify_unifier]]);;

let t_unify_strongind = prove
 (`!(P0:(num,infer_t)fmap->infer_t->infer_t->bool)
    (P1:(num,infer_t)fmap->infer_t list->infer_t list->bool).
     (!s t1 t2.
        t_wfs s /\
        (!ts1 ts2 tc2.
           t_walk s t1 = Infer_Tapp ts1 tc2 /\
           t_walk s t2 = Infer_Tapp ts2 tc2 ==>
           P1 s ts1 ts2) ==>
        P0 s t1 t2) /\
     (!s ts1 ts2.
        t_wfs s /\
        (!t1 ts1' t2 ts2' s'.
           (ts1 = CONS t1 ts1' /\ ts2 = CONS t2 ts2') /\
           t_unify s t1 t2 = SOME s' ==>
           P1 s' ts1' ts2') /\
        (!t1 ts1' t2 ts2'.
           ts1 = CONS t1 ts1' /\ ts2 = CONS t2 ts2' ==> P0 s t1 t2) ==>
        P1 s ts1 ts2) ==>
     (!s t1 t2. t_wfs s ==> P0 s t1 t2) /\
     (!s ts1 ts2. t_wfs s ==> P1 s ts1 ts2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP t_unify_strongind') THEN
  MESON_TAC[]);;

let encode_walkstar = prove
 (`!(s:(num,infer_t)fmap) t.
     t_wfs s
     ==> walkstar (encode_infer_t o_f s) (encode_infer_t t) =
         encode_infer_t (t_walkstar s t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wfs (encode_infer_t o_f (s:(num,infer_t)fmap))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM t_wfs_def]; ALL_TAC] THEN
  SPEC_TAC(`t:infer_t`,`t:infer_t`) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP t_walkstar_ind) THEN
  X_GEN_TAC `t:infer_t` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
                          [MATCH_MP t_walkstar_eqn th]) THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [MATCH_MP walkstar_def th]) THEN
  ASM_SIMP_TAC[encode_walk] THEN
  CASES_ON `t_walk (s:(num,infer_t)fmap) t` THEN
  ASM_SIMP_TAC[encode_infer_t_def; term_term_CASE; case_def "infer_t";
               walkstar_thm] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a0:infer_t list`; `a1:num`]) THEN
  ASM_REWRITE_TAC[term_term_11] THEN
  SPEC_TAC(`a0:infer_t list`,`l:infer_t list`) THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[encode_infer_t_def; walkstar_thm; MAP; MEM; term_term_11] THEN
  DISCH_TAC THEN CONJ_TAC THEN TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN
  ASM_MESON_TAC[]);;

let t_walkstar_FEMPTY = prove
 (`!t. t_walkstar FEMPTY t = t`,
  REWRITE_TAC[t_walkstar_def; o_f_FEMPTY; walkstar_FEMPTY; decode_left_inverse]);;

let t_wfs_SUBMAP = prove
 (`!s1 s2:(num,infer_t)fmap. t_wfs s2 /\ s1 SUBMAP s2 ==> t_wfs s1`,
  REWRITE_TAC[t_wfs_def; GSYM TYSYS2AUX_SUBMAP_encode] THEN MESON_TAC[wfs_SUBMAP]);;

let t_walkstar_SUBMAP = prove
 (`!s1 s2:(num,infer_t)fmap t.
     s1 SUBMAP s2 /\ t_wfs s2
     ==> t_walkstar s2 t = t_walkstar s2 (t_walkstar s1 t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (s1:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_wfs_SUBMAP]; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [t_walkstar_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP encode_walkstar th)]) THEN
  GEN_REWRITE_TAC LAND_CONV [t_walkstar_def] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC walkstar_SUBMAP THEN
  ASM_REWRITE_TAC[TYSYS2AUX_SUBMAP_encode; GSYM t_wfs_def]);;
let t_vR_def = cake_def
  `t_vR (s:(num,infer_t)fmap) = vR (encode_infer_t o_f s)`;;

let t_vR_eqn = prove
 (CASE_TERM `!(s:(num,infer_t)fmap) x y.
     t_vR s y x <=> match FLOOKUP s x with SOME t -> y IN t_vars t | _ -> F`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[t_vR_def; vR_def; TYSYS2AUX_FLOOKUP_encode] THEN
  CASES_ON `FLOOKUP (s:(num,infer_t)fmap) x` THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_CASE; t_vars_def]);;

let t_wfs_eqn = prove
 (`!s:(num,infer_t)fmap. t_wfs s <=> WF (t_vR s)`,
  REWRITE_TAC[t_wfs_def; wfs_def; t_vR_def]);;

let t_rangevars_def = cake_def
  `t_rangevars (s:(num,infer_t)fmap) = rangevars (encode_infer_t o_f s)`;;

let TYSYS2AUX_FRANGE_encode = prove
 (`!s:(num,infer_t)fmap.
     FRANGE (encode_infer_t o_f s) = IMAGE encode_infer_t (FRANGE s)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; FRANGE_FLOOKUP; TYSYS2AUX_FLOOKUP_encode;
              OPTION_MAP_EQ_SOME] THEN
  MESON_TAC[]);;

let t_rangevars_eqn = prove
 (`!s:(num,infer_t)fmap. t_rangevars s = UNIONS (IMAGE t_vars (FRANGE s))`,
  REWRITE_TAC[t_rangevars_def; rangevars_def; TYSYS2AUX_FRANGE_encode;
              GSYM IMAGE_o] THEN
  REWRITE_TAC[o_DEF; GSYM t_vars_def] THEN REWRITE_TAC[ETA_AX]);;

let TYSYS2AUX_vars_encode_ts = prove
 (`!ts. term_vars (encode_infer_ts ts) = UNIONS (set_of_list (MAP t_vars ts))`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[encode_infer_t_def; term_vars_def; MAP; set_of_list;
                  UNIONS_0; UNIONS_INSERT; t_vars_def]);;

let t_vars_eqn = prove
 (`(!x. t_vars (Infer_Tvar_db x) = {}) /\
   (!ts tc. t_vars (Infer_Tapp ts tc) = UNIONS (set_of_list (MAP t_vars ts))) /\
   (!u. t_vars (Infer_Tuvar u) = {u})`,
  REWRITE_TAC[t_vars_def; encode_infer_t_def; term_vars_def; UNION_EMPTY;
              TYSYS2AUX_vars_encode_ts]);;

let t_vwalk_to_var = prove
 (`!s:(num,infer_t)fmap. t_wfs s ==>
     !v u. t_vwalk s v = Infer_Tuvar u ==> ~(u IN FDOM s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `encode_infer_t o_f (s:(num,infer_t)fmap)` vwalk_to_var) THEN
  ASM_REWRITE_TAC[GSYM t_wfs_def; FDOM_o_f] THEN
  DISCH_THEN(MP_TAC o SPECL [`v:num`; `u:num`]) THEN
  ASM_SIMP_TAC[encode_vwalk; encode_infer_t_def]);;

let t_walkstar_vars_notin = prove
 (`!s:(num,infer_t)fmap. t_wfs s ==>
     !t x. x IN t_vars (t_walkstar s t) ==> ~(x IN FDOM s)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP t_walkstar_ind) THEN
  X_GEN_TAC `t:infer_t` THEN DISCH_TAC THEN X_GEN_TAC `x:num` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP t_walkstar_eqn th]) THEN
  CASES_ON `t_walk (s:(num,infer_t)fmap) t` THEN
  REWRITE_TAC[case_def "infer_t"; t_vars_eqn; NOT_IN_EMPTY; IN_SING] THENL
   [REWRITE_TAC[IN_UNIONS; IN_SET_OF_LIST; MEM_MAP] THEN
    ASM_MESON_TAC[];
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `t_walk (s:(num,infer_t)fmap) t = Infer_Tuvar a` THEN
    CASES_ON `t:infer_t` THEN
    REWRITE_TAC[t_walk_eqn; distinctness "infer_t"; injectivity "infer_t"] THEN
    ASM_MESON_TAC[t_vwalk_to_var]]);;
let TYSYS2AUX_t_vars_o = prove
 (`term_vars o encode_infer_t = t_vars`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; t_vars_def]);;

let t_walkstar_vars_in = prove
 (`!s:(num,infer_t)fmap. t_wfs s ==>
     !t. t_vars (t_walkstar s t) SUBSET
         t_vars t UNION UNIONS (FRANGE (t_vars o_f s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `encode_infer_t o_f (s:(num,infer_t)fmap)` vars_walkstar) THEN
  ASM_REWRITE_TAC[GSYM t_wfs_def] THEN
  DISCH_THEN(MP_TAC o SPEC `encode_infer_t t`) THEN
  ASM_SIMP_TAC[encode_walkstar; o_f_o_f; TYSYS2AUX_t_vars_o; GSYM t_vars_def]);;

let t_walkstar_idempotent = prove
 (`!s:(num,infer_t)fmap. t_wfs s ==>
     !t. t_walkstar s (t_walkstar s t) = t_walkstar s t`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [t_walkstar_def] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP encode_walkstar th)]) THEN
  REWRITE_TAC[t_walkstar_def] THEN AP_TERM_TAC THEN
  MP_TAC(ISPEC `encode_infer_t o_f (s:(num,infer_t)fmap)` walkstar_idempotent) THEN
  ASM_REWRITE_TAC[GSYM t_wfs_def] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[SYM(SPEC `encode_infer_t t` th)]));;
let t_unify_apply = prove
 (`!(s1:(num,infer_t)fmap) s2 t1 t2.
     t_wfs s1 /\ t_unify s1 t1 t2 = SOME s2 ==> t_walkstar s2 t1 = t_walkstar s2 t2`,
  MESON_TAC[t_unify_unifier]);;

let t_unify_apply2 = prove
 (`!(s1:(num,infer_t)fmap) s2 t1' t2' t1 t2.
     t_wfs s1 /\ t_unify s1 t1' t2' = SOME s2 /\ t_walkstar s1 t1 = t_walkstar s1 t2
     ==> t_walkstar s2 t1 = t_walkstar s2 t2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (s2:(num,infer_t)fmap) /\ s1 SUBMAP s2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[t_unify_unifier]; ALL_TAC] THEN
  MP_TAC(SPECL [`s1:(num,infer_t)fmap`; `s2:(num,infer_t)fmap`] t_walkstar_SUBMAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[]);;

let t_unify_wfs = prove
 (`!(s1:(num,infer_t)fmap) t1 t2 s2.
     t_wfs s1 /\ t_unify s1 t1 t2 = SOME s2 ==> t_wfs s2`,
  MESON_TAC[t_unify_unifier]);;

let finite_t_rangevars = prove
 (`!t:(num,infer_t)fmap. FINITE (t_rangevars t)`,
  REWRITE_TAC[t_rangevars_def; FINITE_rangevars]);;

let t_walkstar_eqn1 = prove
 (`!(s:(num,infer_t)fmap) idx ts tc.
     t_wfs s
     ==> t_walkstar s (Infer_Tvar_db idx) = Infer_Tvar_db idx /\
         t_walkstar s (Infer_Tapp ts tc) = Infer_Tapp (MAP (t_walkstar s) ts) tc`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [MATCH_MP t_walkstar_eqn th]) THEN
  REWRITE_TAC[t_walk_eqn; case_def "infer_t"]);;

let oc_tvar_db = prove
 (`!(s:(num,infer_t)fmap) uv tvs. t_wfs s ==> ~t_oc s (Infer_Tvar_db tvs) uv`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [MATCH_MP t_oc_eqn th]) THEN
  REWRITE_TAC[t_walk_eqn; case_def "infer_t"]);;

let oc_unit = prove
 (`!(s:(num,infer_t)fmap) uv tc. t_wfs s ==> ~t_oc s (Infer_Tapp [] tc) uv`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [MATCH_MP t_oc_eqn th]) THEN
  REWRITE_TAC[t_walk_eqn; case_def "infer_t"; EX]);;

let no_vars_lem = prove
 (`!(e:A) l (f:A->B->bool).
     MEM e l /\ set_of_list (MAP f l) = {{}} ==> f e = {}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:A->B->bool) e IN set_of_list (MAP f l)` MP_TAC THENL
   [REWRITE_TAC[IN_SET_OF_LIST; MEM_MAP] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[IN_SING]]);;

let TYSYS2AUX_FLOOKUP_FUPDATE_LIST_disjoint = prove
 (`!(s:(A,B)fmap) l k.
     ~(k IN FDOM (FEMPTY |++ l)) ==> FLOOKUP (s |++ l) k = FLOOKUP s k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FDOM_FLOOKUP; flookup_fupdate_list] THEN
  CASES_ON `ALOOKUP (REVERSE (l:(A#B)list)) k` THEN
  REWRITE_TAC[option_CASE; FLOOKUP_EMPTY; option_DISTINCT]);;

let no_vars_extend_subst_vwalk = prove
 (`!s:(num,infer_t)fmap. t_wfs s ==>
     !n s'. t_wfs (s |++ s') /\
            DISJOINT (FDOM s) (FDOM (FEMPTY |++ s')) /\
            (!n'. ~(t_vwalk s n = Infer_Tuvar n'))
            ==> t_vwalk (s |++ s') n = t_vwalk s n`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP t_vwalk_ind) THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "ih") THEN
  X_GEN_TAC `s':(num#infer_t)list` THEN STRIP_TAC THEN
  ASM_CASES_TAC `n IN FDOM (s:(num,infer_t)fmap)` THENL
   [ALL_TAC;
    UNDISCH_TAC `!n'. ~(t_vwalk (s:(num,infer_t)fmap) n = Infer_Tuvar n')` THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[] THEN
    MP_TAC(SPEC `s:(num,infer_t)fmap` t_vwalk_eqn) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FDOM_FLOOKUP]) THEN
    ASM_REWRITE_TAC[option_CASE]] THEN
  SUBGOAL_THEN `FLOOKUP ((s:(num,infer_t)fmap) |++ s') n = FLOOKUP s n` ASSUME_TAC THENL
   [MATCH_MP_TAC TYSYS2AUX_FLOOKUP_FUPDATE_LIST_disjoint THEN
    UNDISCH_TAC `DISJOINT (FDOM (s:(num,infer_t)fmap))
                          (FDOM (FEMPTY |++ (s':(num#infer_t)list)))` THEN
    UNDISCH_TAC `n IN FDOM (s:(num,infer_t)fmap)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `(s:(num,infer_t)fmap) |++ s'` t_vwalk_eqn) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  MP_TAC(SPEC `s:(num,infer_t)fmap` t_vwalk_eqn) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
  ASM_REWRITE_TAC[] THEN
  CASES_ON `FLOOKUP (s:(num,infer_t)fmap) n` THEN REWRITE_TAC[option_CASE] THEN
  CASES_ON `a:infer_t` THEN REWRITE_TAC[case_def "infer_t"] THEN
  SUBGOAL_THEN `t_vwalk (s:(num,infer_t)fmap) n = t_vwalk s a'` ASSUME_TAC THENL
   [MP_TAC(SPEC `s:(num,infer_t)fmap` t_vwalk_eqn) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    ASM_REWRITE_TAC[option_CASE; case_def "infer_t"];
    ALL_TAC] THEN
  REMOVE_THEN "ih" (MP_TAC o SPECL [`Infer_Tuvar a'`; `a':num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[]);;
let no_vars_extend_subst = prove
 (`!s:(num,infer_t)fmap. t_wfs s ==>
     !t s'. t_wfs (s |++ s') /\
            DISJOINT (FDOM s) (FDOM (FEMPTY |++ s')) /\
            t_vars (t_walkstar s t) = {}
            ==> t_walkstar (s |++ s') t = t_walkstar s t`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP t_walkstar_ind) THEN
  X_GEN_TAC `t:infer_t` THEN DISCH_THEN(LABEL_TAC "ih") THEN
  X_GEN_TAC `s':(num#infer_t)list` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!ts tc. t_walk (s:(num,infer_t)fmap) t = Infer_Tapp ts tc /\
            t_vars (Infer_Tapp (MAP (t_walkstar s) ts) tc) = {}
            ==> MAP (t_walkstar (s |++ s')) ts = MAP (t_walkstar s) ts`
   (LABEL_TAC "maps") THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[t_vars_eqn; EMPTY_UNIONS; IN_SET_OF_LIST; MEM_MAP] THEN
    STRIP_TAC THEN MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    X_GEN_TAC `a:infer_t` THEN DISCH_TAC THEN
    USE_THEN "ih" (MP_TAC o SPECL [`ts:infer_t list`; `tc:num`; `a:infer_t`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `s':(num#infer_t)list`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `(s:(num,infer_t)fmap) |++ s'` t_walkstar_eqn) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  UNDISCH_TAC `t_vars (t_walkstar (s:(num,infer_t)fmap) t) = {}` THEN
  MP_TAC(SPEC `s:(num,infer_t)fmap` t_walkstar_eqn) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  CASES_ON `t:infer_t` THEN REWRITE_TAC[t_walk_eqn; case_def "infer_t"] THENL
   [DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    USE_THEN "maps" MATCH_MP_TAC THEN EXISTS_TAC `a1:num` THEN
    ASM_REWRITE_TAC[t_walk_eqn];
    ALL_TAC] THEN
  CASES_ON `t_vwalk (s:(num,infer_t)fmap) a` THEN
  REWRITE_TAC[case_def "infer_t"; t_vars_eqn; NOT_INSERT_EMPTY] THEN
  MP_TAC(SPEC `s:(num,infer_t)fmap` no_vars_extend_subst_vwalk) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:num`; `s':(num#infer_t)list`]) THEN
  ASM_REWRITE_TAC[distinctness "infer_t"] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[case_def "infer_t"] THEN
  DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  USE_THEN "maps" MATCH_MP_TAC THEN EXISTS_TAC `a1:num` THEN
  ASM_REWRITE_TAC[t_walk_eqn; t_vars_eqn]);;
let t_walk_vwalk_id = prove
 (`!s:(num,infer_t)fmap. t_wfs s ==> !n. t_walk s (t_vwalk s n) = t_vwalk s n`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP t_vwalk_ind) THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(SPEC `s:(num,infer_t)fmap` t_vwalk_eqn) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th] THEN ASSUME_TAC(SPEC `n:num` th)) THEN
  CASES_ON `FLOOKUP (s:(num,infer_t)fmap) n` THEN
  REWRITE_TAC[option_CASE] THENL
   [REWRITE_TAC[t_walk_eqn] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    REWRITE_TAC[option_CASE];
    ALL_TAC] THEN
  CASES_ON `a:infer_t` THEN REWRITE_TAC[case_def "infer_t"; t_walk_eqn] THEN
  FIRST_X_ASSUM(K ALL_TAC) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
  ASM_MESON_TAC[]);;

let t_walk_walk_id = prove
 (`!(s:(num,infer_t)fmap) h. t_wfs s ==> t_walk s (t_walk s h) = t_walk s h`,
  REPEAT STRIP_TAC THEN CASES_ON `h:infer_t` THEN
  ASM_SIMP_TAC[t_walk_eqn; t_walk_vwalk_id]);;

let eqs_t_unify = prove
 (`!(s:(num,infer_t)fmap) s2 t1 t2.
     t_wfs s /\ t_wfs s2 /\
     t_walkstar s2 (t_walkstar s t1) = t_walkstar s2 (t_walkstar s t2)
     ==> ?sx. t_unify s t1 t2 = SOME sx`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[t_unify_def] THEN
  MP_TAC(ISPECL [`encode_infer_t o_f (s:(num,infer_t)fmap)`; `encode_infer_t t1`;
                 `encode_infer_t t2`; `encode_infer_t o_f (s2:(num,infer_t)fmap)`]
                eqs_unify) THEN
  ASM_REWRITE_TAC[GSYM t_wfs_def] THEN ASM_SIMP_TAC[encode_walkstar] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN MESON_TAC[]);;

let t_unify_mgu = prove
 (`!(s:(num,infer_t)fmap) t1 t2 sx s2.
     t_wfs s /\ t_unify s t1 t2 = SOME sx /\ t_wfs s2 /\
     t_walkstar s2 (t_walkstar s t1) = t_walkstar s2 (t_walkstar s t2)
     ==> !t. t_walkstar s2 (t_walkstar sx t) = t_walkstar s2 (t_walkstar s t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `t_wfs (sx:(num,infer_t)fmap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[t_unify_wfs]; ALL_TAC] THEN
  MP_TAC(SPECL [`encode_infer_t o_f (s:(num,infer_t)fmap)`; `encode_infer_t t1`;
                `encode_infer_t t2`; `s:(num,infer_t)fmap`; `t1:infer_t`; `t2:infer_t`]
               encode_unify) THEN
  ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`encode_infer_t o_f (s:(num,infer_t)fmap)`; `encode_infer_t t1`;
                 `encode_infer_t t2`; `encode_infer_t o_f (sx:(num,infer_t)fmap)`;
                 `encode_infer_t o_f (s2:(num,infer_t)fmap)`] unify_mgu) THEN
  ASM_REWRITE_TAC[GSYM t_wfs_def] THEN ASM_SIMP_TAC[encode_walkstar] THEN
  DISCH_THEN(fun th -> X_GEN_TAC `t:infer_t` THEN MP_TAC(SPEC `encode_infer_t t` th)) THEN
  ASM_SIMP_TAC[encode_walkstar; encode_infer_t_11]);;

let t_walkstar_tuvar_props = prove
 (`!(s:(num,infer_t)fmap) uv.
     t_wfs s
     ==> (~(uv IN FDOM s) <=> t_walkstar s (Infer_Tuvar uv) = Infer_Tuvar uv)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(SPEC `s:(num,infer_t)fmap` t_walkstar_eqn) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN REWRITE_TAC[t_walk_eqn] THEN
    MP_TAC(SPEC `s:(num,infer_t)fmap` t_vwalk_eqn) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FDOM_FLOOKUP]) THEN
    ASM_REWRITE_TAC[option_CASE; case_def "infer_t"];
    DISCH_TAC THEN
    MP_TAC(SPEC `s:(num,infer_t)fmap` t_walkstar_vars_notin) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`Infer_Tuvar uv`; `uv:num`]) THEN
    ASM_REWRITE_TAC[t_vars_eqn; IN_SING]]);;

let t_compat_def = cake_def
  `t_compat (s:(num,infer_t)fmap) s' <=>
     t_wfs s /\ t_wfs s' /\
     !t. t_walkstar s' (t_walkstar s t) = t_walkstar s' t`;;

let t_compat_refl = prove
 (`!s:(num,infer_t)fmap. t_wfs s ==> t_compat s s`,
  REWRITE_TAC[t_compat_def] THEN MESON_TAC[t_walkstar_SUBMAP; SUBMAP_REFL]);;

let t_compat_trans = prove
 (`!a b c:(num,infer_t)fmap. t_compat a b /\ t_compat b c ==> t_compat a c`,
  REWRITE_TAC[t_compat_def] THEN MESON_TAC[]);;

let SUBMAP_t_compat = prove
 (`!(s:(num,infer_t)fmap) s'. t_wfs s' /\ s SUBMAP s' ==> t_compat s s'`,
  REWRITE_TAC[t_compat_def] THEN MESON_TAC[t_wfs_SUBMAP; t_walkstar_SUBMAP]);;

let t_compat_eqs_t_unify = prove
 (`!(s:(num,infer_t)fmap) t1 t2 sx.
     t_compat s sx /\ t_walkstar sx t1 = t_walkstar sx t2
     ==> ?si. t_unify s t1 t2 = SOME si /\ t_compat si sx`,
  REWRITE_TAC[t_compat_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:(num,infer_t)fmap`; `sx:(num,infer_t)fmap`; `t1:infer_t`;
                `t2:infer_t`] eqs_t_unify) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `sx':(num,infer_t)fmap` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[t_unify_wfs]; ALL_TAC] THEN
  MP_TAC(SPECL [`s:(num,infer_t)fmap`; `t1:infer_t`; `t2:infer_t`;
                `sx':(num,infer_t)fmap`; `sx:(num,infer_t)fmap`] t_unify_mgu) THEN
  ASM_REWRITE_TAC[]);;
