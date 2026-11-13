(* ========================================================================= *)
(* namespaceProps: port of HOL4 semantics/proofs/namespacePropsScript.sml    *)
(* (CakeML v3479).  Proofs about the namespace datatype.                     *)
(* ========================================================================= *)

needs "semantics/namespace.ml";;

(* HOL4 [simp] theorems are registered with cake_add_simps, after them or *)
(* in the block at the end of the file; HOL4 [mono] theorems are added   *)
(* to monotonicity_theorems.  NSPAUX_ names are local helpers.           *)

let mk_id_11 = prove
 (`!a b c d. mk_id a b:(M,N)id = mk_id c d <=> a = c /\ b = d`,
  LIST_INDUCT_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  RW[mk_id_def] THEN METIS_TAC[]);;
let _ = cake_add_simps [mk_id_11];;

let id_to_mods_mk_id = prove
 (`!mn (x:N). id_to_mods (mk_id mn x:(M,N)id) = mn`,
  LIST_INDUCT_TAC THEN RW[id_to_mods_def; mk_id_def]);;

let id_to_namemods_mk_id = prove
 (`!mn (x:N). id_to_n (mk_id mn x:(M,N)id) = x`,
  LIST_INDUCT_TAC THEN RW[id_to_n_def; mk_id_def]);;
let _ = cake_add_simps [id_to_mods_mk_id; id_to_namemods_mk_id];;

let mk_id_surj = prove
 (`!id:(M,N)id. ?p n. id = mk_id p n`,
  MATCH_MP_TAC id_INDUCT THEN RW[] THEN METIS_TAC[mk_id_def]);;

let mk_id_thm = prove
 (`!id:(M,N)id. mk_id (id_to_mods id) (id_to_n id) = id`,
  MATCH_MP_TAC id_INDUCT THEN RW[id_to_mods_def; id_to_n_def; mk_id_def]);;

let nsAll_mono = prove
 (`!P Q (e:(M,N,V)namespace).
     (!id x. P id x ==> Q id x) ==> nsAll P e ==> nsAll Q e`,
  RW[nsAll_def]);;

let nsSub_mono = prove
 (`!(R1:(M,N)id->V1->V2->bool) R2 e1 e2.
     (!x y z. R1 x y z ==> R2 x y z) ==> (nsSub R1 e1 e2 ==> nsSub R2 e1 e2)`,
  REWRITE_TAC[nsSub_def] THEN MESON_TAC[]);;

let nsSub_mono2 = prove
 (`!(R1:(M,N)id->V1->V2->bool) R2 e1 e2.
     (!x y z. nsLookup e1 x = SOME y /\ nsLookup e2 x = SOME z /\ R1 x y z
              ==> R2 x y z) ==> (nsSub R1 e1 e2 ==> nsSub R2 e1 e2)`,
  REWRITE_TAC[nsSub_def] THEN MESON_TAC[]);;

let nsAll2_mono = prove
 (`!(R1:(M,N)id->V1->V2->bool) R2 e1 e2.
     (!x y z. R1 x y z ==> R2 x y z) ==> nsAll2 R1 e1 e2 ==> nsAll2 R2 e1 e2`,
  REWRITE_TAC[nsAll2_def; nsSub_def] THEN MESON_TAC[]);;

(* HOL4 [mono]: the three theorems above are monotonicity theorems for      *)
(* inductive definitions (HOL Light's new_inductive_definition, MONO_TAC)   *)
let () = monotonicity_theorems :=
  map SPEC_ALL [nsAll_mono; nsSub_mono; nsAll2_mono] @ !monotonicity_theorems;;

let nsLookup_nsEmpty = prove
 (`!id:(M,N)id. nsLookup (nsEmpty:(M,N,V)namespace) id = NONE`,
  MATCH_MP_TAC id_INDUCT THEN RW[nsLookup_def; nsEmpty_def; ALOOKUP_DEF]);;

let nsLookupMod_nsEmpty = prove
 (`!(x:M) y. nsLookupMod (nsEmpty:(M,N,V)namespace) (CONS x y) = NONE`,
  RW[nsLookupMod_def; nsEmpty_def; ALOOKUP_DEF]);;

let nsAppend_nsEmpty = prove
 (`!env:(M,N,V)namespace. nsAppend env nsEmpty = env /\ nsAppend nsEmpty env = env`,
  GEN_TAC THEN CASES_ON `env:(M,N,V)namespace` THEN
  RW[nsAppend_def; nsEmpty_def; APPEND_NIL; APPEND]);;

let alist_to_ns_nil = prove
 (`alist_to_ns [] = nsEmpty:(M,N,V)namespace`,
  RW[alist_to_ns_def; nsEmpty_def]);;

let nsSub_nsEmpty = prove
 (`!r (env:(M,N,V2)namespace). nsSub r (nsEmpty:(M,N,V1)namespace) env`,
  RW[nsSub_def; nsLookup_nsEmpty] THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`path:M list`,`path:M list`) THEN LIST_INDUCT_TAC THEN
  CASES_ON `env:(M,N,V2)namespace` THEN
  FS[nsLookupMod_def; nsEmpty_def; ALOOKUP_DEF]);;

let nsAll_nsEmpty = prove
 (`!f. nsAll f (nsEmpty:(M,N,V)namespace)`,
  RW[nsAll_def; nsLookup_nsEmpty]);;

let nsAll2_nsEmpty = prove
 (`!f. nsAll2 f (nsEmpty:(M,N,V1)namespace) (nsEmpty:(M,N,V2)namespace)`,
  RW[nsAll2_def; nsSub_nsEmpty]);;

let nsDom_nsEmpty = prove
 (`nsDom (nsEmpty:(M,N,V)namespace) = {}`,
  RW[nsDom_def; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; nsLookup_nsEmpty]);;

let nsDomMod_nsEmpty = prove
 (`nsDomMod (nsEmpty:(M,N,V)namespace) = {[]}`,
  RW[nsDomMod_def; EXTENSION; IN_ELIM_THM; IN_SING] THEN
  CASES_ON `x:M list` THEN FS[nsLookupMod_def; nsLookupMod_nsEmpty]);;

let nsMap_nsEmpty = prove
 (`!f:V->W. nsMap f (nsEmpty:(M,N,V)namespace) = nsEmpty`,
  RW[nsMap_def; nsEmpty_def]);;

let nsBind_nsEmpty = prove
 (`!(x:N) (y:V) env:(M,N,V)namespace. ~(nsBind x y env = nsEmpty)`,
  REPEAT GEN_TAC THEN CASES_ON `env:(M,N,V)namespace` THEN
  RW[nsBind_def; nsEmpty_def]);;

let nsLookup_Bind_v_some = prove
 (`!(v:(N#V)list) k x. nsLookup (Bind v [] :(M,N,V)namespace) k = SOME x <=>
     ?y. k = Short y /\ ALOOKUP v y = SOME x`,
  GEN_TAC THEN GEN_TAC THEN CASES_ON `k:(M,N)id` THEN
  RW[nsLookup_def; ALOOKUP_DEF]);;

let _ = cake_add_simps [nsLookup_nsEmpty; nsLookupMod_nsEmpty; nsAppend_nsEmpty;
  alist_to_ns_nil; nsSub_nsEmpty; nsAll_nsEmpty; nsAll2_nsEmpty; nsDom_nsEmpty;
  nsDomMod_nsEmpty; nsMap_nsEmpty; nsBind_nsEmpty];;

let alist_to_ns_cons = prove
 (`!(k:N) (v:V) l. alist_to_ns (CONS (k,v) l) =
                   nsBind k v (alist_to_ns l):(M,N,V)namespace`,
  RW[alist_to_ns_def; nsBind_def]);;

let nsAppend_nsBind = prove
 (`!(k:N) (v:V) (e1:(M,N,V)namespace) e2.
     nsAppend (nsBind k v e1) e2 = nsBind k v (nsAppend e1 e2)`,
  REPEAT GEN_TAC THEN CASES_ON `e1:(M,N,V)namespace` THEN
  CASES_ON `e2:(M,N,V)namespace` THEN RW[nsAppend_def; nsBind_def; APPEND]);;

let nsAppend_alist_to_ns = prove
 (`!al1 al2. nsAppend (alist_to_ns al1) (alist_to_ns al2) =
             alist_to_ns (APPEND al1 al2):(M,N,V)namespace`,
  RW[alist_to_ns_def; nsAppend_def; APPEND_NIL]);;

let nsAppend_assoc = prove
 (`!(e1:(M,N,V)namespace) e2 e3.
     nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3`,
  REPEAT GEN_TAC THEN CASES_ON `e1:(M,N,V)namespace` THEN
  CASES_ON `e2:(M,N,V)namespace` THEN CASES_ON `e3:(M,N,V)namespace` THEN
  RW[nsAppend_def; APPEND_ASSOC]);;

let nsLookup_nsBind = prove
 (`(!(n:N) (v:V) (e:(M,N,V)namespace). nsLookup (nsBind n v e) (Short n) = SOME v) /\
   (!n n' (v:V) (e:(M,N,V)namespace).
      ~(n = Short n') ==> nsLookup (nsBind n' v e) n = nsLookup e n)`,
  RW[] THEN CASES_ON `e:(M,N,V)namespace` THEN TRY (CASES_ON `n:(M,N)id`) THEN
  FS[nsLookup_def; nsBind_def; ALOOKUP_DEF]);;

let nsAppend_nsSing = prove
 (`!(n:N) (x:V) (e:(M,N,V)namespace). nsAppend (nsSing n x) e = nsBind n x e`,
  RW[nsSing_def] THEN CASES_ON `e:(M,N,V)namespace` THEN
  SIMP[nsBind_def; nsAppend_def; APPEND]);;

let nsLookup_nsSing = prove
 (`!(n:N) (v:V) id. nsLookup (nsSing n v:(M,N,V)namespace) id =
                    if id = Short n then SOME v else NONE`,
  REPEAT GEN_TAC THEN CASES_ON `id:(M,N)id` THEN
  RW[nsSing_def; nsLookup_def; ALOOKUP_DEF] THEN ASM_MESON_TAC[]);;

let nsAll_nsSing = prove
 (`!R (n:N) (v:V). nsAll R (nsSing n v:(M,N,V)namespace) <=> R (Short n) v`,
  REWRITE_TAC[nsAll_def; nsLookup_nsSing] THEN REPEAT GEN_TAC THEN EQ_TAC THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN SIMP[];
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN SIMP[] THEN RW[] THEN
    ASM_REWRITE_TAC[]]);;

let nsLookupMod_nsSing = prove
 (`!n1 (n2:N) (v:V). nsLookupMod (nsSing n2 v:(M,N,V)namespace) n1 =
                     if n1 = [] then SOME (nsSing n2 v) else NONE`,
  GEN_TAC THEN CASES_ON `n1:M list` THEN
  RW[nsSing_def; nsLookupMod_def; ALOOKUP_DEF]);;

let nsAll2_nsSing = prove
 (`!R (n1:N) (v1:V1) n2 (v2:V2).
     nsAll2 R (nsSing n1 v1:(M,N,V1)namespace) (nsSing n2 v2) <=>
     n1 = n2 /\ R (Short n1) v1 v2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[nsAll2_def; nsSub_def; nsLookup_nsSing; nsLookupMod_nsSing] THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPECL [`Short n1:(M,N)id`; `v1:V1`] o CONJUNCT1 o
               CONJUNCT1) THEN
    SIMP[injectivity "id"] THEN COND_CASES_TAC THEN SIMP[];
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    SIMP[COND_CASE_EQ] THEN ASM_MESON_TAC[]]);;

let nsMap_nsSing = prove
 (`!(f:V->W) (x:N) v. nsMap f (nsSing x v:(M,N,V)namespace) = nsSing x (f v)`,
  RW[nsSing_def; nsMap_def; MAP]);;

let nsBind_11 = prove
 (`!(x:N) (y:V) (n:(M,N,V)namespace) x' y' n'.
     nsBind x y n = nsBind x' y' n' <=> x = x' /\ y = y' /\ n = n'`,
  REPEAT GEN_TAC THEN CASES_ON `n:(M,N,V)namespace` THEN
  CASES_ON `n':(M,N,V)namespace` THEN FS[nsBind_def] THEN METIS_TAC[]);;

let nsDom_nsBind = prove
 (`!(x:N) (y:V) (n:(M,N,V)namespace).
     nsDom (nsBind x y n) = Short x INSERT nsDom n`,
  REPEAT GEN_TAC THEN CASES_ON `n:(M,N,V)namespace` THEN
  REWRITE_TAC[nsBind_def; nsDom_def; EXTENSION; IN_ELIM_THM; IN_INSERT] THEN
  X_GEN_TAC `i:(M,N)id` THEN CASES_ON `i:(M,N)id` THEN
  RW[nsLookup_def; ALOOKUP_DEF] THEN METIS_TAC[]);;

let nsDom_nsSing = prove
 (`!(x:N) (y:V). nsDom (nsSing x y:(M,N,V)namespace) = {Short x}`,
  RW[nsDom_def; EXTENSION; IN_ELIM_THM; IN_SING; nsLookup_nsSing;
     COND_CASE_EQ]);;

let nsDomMod_nsBind = prove
 (`!(x:N) (y:V) (n:(M,N,V)namespace). nsDomMod (nsBind x y n) = nsDomMod n`,
  REPEAT GEN_TAC THEN CASES_ON `n:(M,N,V)namespace` THEN
  REWRITE_TAC[nsBind_def; nsDomMod_def; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `p:M list` THEN CASES_ON `p:M list` THEN
  REWRITE_TAC[nsLookupMod_def] THEN MESON_TAC[]);;

let nsDomMod_nsSing = prove
 (`!(x:N) (y:V). nsDomMod (nsSing x y:(M,N,V)namespace) = {[]}`,
  RW[nsDomMod_def; EXTENSION; IN_ELIM_THM; IN_SING; nsLookupMod_nsSing;
     COND_CASE_EQ]);;

let nsLookupMod_alist_to_ns = prove
 (`!(l:(N#V)list) (x:M) y.
     nsLookupMod (alist_to_ns l:(M,N,V)namespace) (CONS x y) = NONE`,
  RW[alist_to_ns_def; nsLookupMod_def; ALOOKUP_DEF]);;

let alist_to_ns_11 = prove
 (`!(l1:(N#V)list) l2.
     alist_to_ns l1:(M,N,V)namespace = alist_to_ns l2 <=> l1 = l2`,
  RW[alist_to_ns_def; injectivity "namespace"]);;

(* local copies of alist lemmas (alist.ml is being written in parallel) *)
let NSPAUX_ALOOKUP_APPEND = prove
 (`!(l1:(A#B)list) l2 k. ALOOKUP (APPEND l1 l2) k =
     option_CASE (ALOOKUP l1 k) (ALOOKUP l2 k) (\v. SOME v)`,
  LIST_INDUCT_TAC THEN SIMP[APPEND; ALOOKUP_DEF] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN SIMP[]);;

let NSPAUX_ALOOKUP_MEM = prove
 (`!(l:(A#B)list) k v. ALOOKUP l k = SOME v ==> MEM (k,v) l`,
  LIST_INDUCT_TAC THEN SIMP[ALOOKUP_DEF; MEM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN SIMP[] THEN
  STRIP_TAC THEN FS[] THEN ASM_MESON_TAC[PAIR]);;

let nsLookup_to_nsLookupMod = prove
 (`!(n:(M,N,V)namespace) v t.
     nsLookup n v = SOME t
     ==> ?m. nsLookupMod n (id_to_mods v) = SOME m /\
             nsLookup m (Short (id_to_n v)) = SOME t`,
  MATCH_MP_TAC nsLookup_ind THEN
  RW[id_to_n_def; nsLookup_def; nsLookupMod_def; id_to_mods_def] THEN
  POP_ASSUM MP_TAC THEN CASE_TAC THEN FS[]);;

let nsLookup_alist_to_ns_some = prove
 (`!(l:(N#V)list) id v.
     nsLookup (alist_to_ns l:(M,N,V)namespace) id = SOME v <=>
     ?x'. id = Short x' /\ ALOOKUP l x' = SOME v`,
  GEN_TAC THEN GEN_TAC THEN CASES_ON `id:(M,N)id` THEN
  FS[alist_to_ns_def; nsLookup_def; ALOOKUP_DEF]);;

let nsLookup_alist_to_ns_none = prove
 (`!(l:(N#V)list) id.
     nsLookup (alist_to_ns l:(M,N,V)namespace) id = NONE <=>
     !x'. id = Short x' ==> ALOOKUP l x' = NONE`,
  GEN_TAC THEN GEN_TAC THEN CASES_ON `id:(M,N)id` THEN
  FS[alist_to_ns_def; nsLookup_def; ALOOKUP_DEF]);;

let nsDom_alist_to_ns = prove
 (`!(l:(N#V)list). nsDom (alist_to_ns l:(M,N,V)namespace) =
                   set_of_list (MAP (Short o FST) l)`,
  RW[nsDom_def; EXTENSION; IN_ELIM_THM; IN_SET_OF_LIST; MEM_MAP;
     nsLookup_alist_to_ns_some; o_THM] THEN
  EQ_TAC THEN RW[] THENL
   [EXISTS_TAC `(x':N, v:V)` THEN ASM_MESON_TAC[NSPAUX_ALOOKUP_MEM; FST];
    POP_ASSUM MP_TAC THEN SPEC_TAC(`l:(N#V)list`,`l:(N#V)list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; ALOOKUP_DEF] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[option_INJ]]);;

let nsLookup_nsLift = prove
 (CASE_TERM `!(mn:M) (e:(M,N,V)namespace) id.
    nsLookup (nsLift mn e) id =
    match id with
      Long mn' id' -> if mn = mn' then nsLookup e id' else NONE
    | Short _ -> NONE`,
  RW[nsLift_def] THEN CASE_TAC THEN RW[nsLookup_def; ALOOKUP_DEF] THEN
  FS[]);;

let nsLookupMod_nsLift = prove
 (CASE_TERM `!(mn:M) (e:(M,N,V)namespace) path.
    nsLookupMod (nsLift mn e) path =
    match path with
      [] -> SOME (nsLift mn e)
    | CONS mn' path' -> if mn = mn' then nsLookupMod e path' else NONE`,
  RW[nsLift_def] THEN CASE_TAC THEN RW[nsLookupMod_def; ALOOKUP_DEF] THEN
  FS[]);;

let nsLookup_nsLift_append = prove
 (`!(m:M) (ns:(M,N,V)namespace) ns' m' id (n:N).
     nsLookup (nsAppend (nsLift m ns) ns') (Short n) = nsLookup ns' (Short n) /\
     nsLookup (nsAppend (nsLift m ns) ns') (Long m' id) =
       if m = m' then nsLookup ns id else nsLookup ns' (Long m' id)`,
  REPEAT GEN_TAC THEN CASES_ON `ns':(M,N,V)namespace` THEN
  RW[nsAppend_def; nsLift_def; nsLookup_def; APPEND; ALOOKUP_DEF] THEN FS[]);;

let NSPAUX_NIL_EQ_APPEND = prove
 (`!(l:A list) m. [] = APPEND l m <=> l = [] /\ m = []`,
  MESON_TAC[APPEND_EQ_NIL]);;

(* --------------- nsAppend ------------- *)

let nsLookup_nsAppend_none = prove
 (`!(e1:(M,N,V)namespace) id e2.
     nsLookup (nsAppend e1 e2) id = NONE <=>
     (nsLookup e1 id = NONE /\
      (nsLookup e2 id = NONE \/
       ?p1 p2 e3. ~(p1 = []) /\ id_to_mods id = APPEND p1 p2 /\
                  nsLookupMod e1 p1 = SOME e3))`,
  MATCH_MP_TAC nsLookup_ind THEN RW[] THEN
  CASES_ON `e2:(M,N,V)namespace` THEN
  FS[nsAppend_def; nsLookup_def; NSPAUX_ALOOKUP_APPEND] THEN
  EVERY_CASE_TAC THEN FS[id_to_mods_def; nsLookupMod_def] THENL
   [FS[NSPAUX_NIL_EQ_APPEND];
    EQ_TAC THEN RW[] THEN FS[] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    CASES_ON `p1:M list` THEN FS[nsLookupMod_def; APPEND; CONS_11] THEN
    RW[] THEN FS[];
    EQ_TAC THEN RW[] THEN DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`[mn:M]`; `id_to_mods (id:(M,N)id)`;
                          `a:(M,N,V)namespace`] THEN
    SIMP[nsLookupMod_def; APPEND; NOT_CONS_NIL]]);;

let nsLookup_nsAppend_some = prove
 (`!(e1:(M,N,V)namespace) id e2 v.
     nsLookup (nsAppend e1 e2) id = SOME v <=>
     nsLookup e1 id = SOME v \/
     (nsLookup e1 id = NONE /\ nsLookup e2 id = SOME v /\
      !p1 p2. ~(p1 = []) /\ id_to_mods id = APPEND p1 p2
              ==> nsLookupMod e1 p1 = NONE)`,
  MATCH_MP_TAC nsLookup_ind THEN RW[] THEN
  CASES_ON `e2:(M,N,V)namespace` THEN
  FS[nsAppend_def; nsLookup_def; NSPAUX_ALOOKUP_APPEND] THEN
  EVERY_CASE_TAC THEN FS[id_to_mods_def] THENL
   [FS[NSPAUX_NIL_EQ_APPEND];
    EQ_TAC THEN RW[] THEN
    CASES_ON `p1:M list` THEN FS[nsLookupMod_def; APPEND; CONS_11] THEN
    RW[] THEN FS[];
    EQ_TAC THEN RW[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`[mn:M]`; `id_to_mods (id:(M,N)id)`]) THEN
    SIMP[nsLookupMod_def; APPEND; NOT_CONS_NIL]]);;

let nsAppend_to_nsBindList = prove
 (`!(l:(N#V)list) (e:(M,N,V)namespace).
     nsAppend (alist_to_ns l) e = nsBindList l e`,
  LIST_INDUCT_TAC THEN FS[nsBindList_def; alist_to_ns_def; ITLIST] THEN
  RW[] THEN PAIRARG_TAC THEN SIMP[] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
  CASES_ON `e:(M,N,V)namespace` THEN
  REWRITE_TAC[nsAppend_def; nsBind_def; APPEND]);;

let nsLookupMod_nsAppend_none = prove
 (`!(e1:(M,N,V)namespace) e2 path.
     nsLookupMod (nsAppend e1 e2) path = NONE <=>
     (nsLookupMod e1 path = NONE /\
      (nsLookupMod e2 path = NONE \/
       ?p1 p2 e3. ~(p1 = []) /\ path = APPEND p1 p2 /\
                  nsLookupMod e1 p1 = SOME e3))`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN RW[] THEN
  CASES_ON `e2:(M,N,V)namespace` THEN CASES_ON `e1:(M,N,V)namespace` THEN
  FS[nsAppend_def; nsLookupMod_def; NSPAUX_ALOOKUP_APPEND] THEN
  EVERY_CASE_TAC THEN FS[] THEN EQ_TAC THEN RW[] THENL
   [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    CASES_ON `p1:M list` THEN FS[nsLookupMod_def; APPEND; CONS_11] THEN
    RW[] THEN FS[];
    DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`[h:M]`; `t:M list`; `a:(M,N,V)namespace`] THEN
    SIMP[nsLookupMod_def; APPEND; NOT_CONS_NIL]]);;

(* HOL4: x is free in the statement; the induction hypothesis is not     *)
(* needed and is dropped (EVERY_CASE_TAC would loop on its conditional)   *)
let nsLookupMod_nsAppend_some = prove
 (`!(e1:(M,N,V)namespace) e2 path x.
     (nsLookupMod (nsAppend e1 e2) path = SOME x <=>
      if path = [] then x = nsAppend e1 e2 else
      nsLookupMod e1 path = SOME x \/
      (nsLookupMod e2 path = SOME x /\
       !p1 p2. ~(p1 = []) /\ path = APPEND p1 p2
               ==> nsLookupMod e1 p1 = NONE))`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[nsLookupMod_def; option_INJ] THEN MESON_TAC[];
    POP_ASSUM(K ALL_TAC)] THEN
  RW[] THEN
  CASES_ON `e2:(M,N,V)namespace` THEN CASES_ON `e1:(M,N,V)namespace` THEN
  FS[nsAppend_def; nsLookupMod_def; NSPAUX_ALOOKUP_APPEND] THEN
  EVERY_CASE_TAC THEN FS[] THEN EQ_TAC THEN RW[] THENL
   [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    CASES_ON `p1:M list` THEN FS[nsLookupMod_def; APPEND; CONS_11] THEN
    RW[] THEN FS[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`[h:M]`; `t:M list`]) THEN
    SIMP[nsLookupMod_def; APPEND; NOT_CONS_NIL]]);;

let NSPAUX_ALOOKUP_NONE = prove
 (`!(l:(A#B)list) k. ALOOKUP l k = NONE <=> ~MEM k (MAP FST l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALOOKUP_DEF; MAP; MEM] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]);;

let nsDom_nsAppend_alist = prove
 (`!(x:(N#V)list) (y:(M,N,V)namespace).
     nsDom (nsAppend (alist_to_ns x) y) =
     set_of_list (MAP (Short o FST) x) UNION nsDom y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[nsDom_def; EXTENSION; IN_ELIM_THM; IN_UNION; IN_SET_OF_LIST] THEN
  X_GEN_TAC `i:(M,N)id` THEN REWRITE_TAC[nsLookup_nsAppend_some] THEN
  SUBGOAL_THEN
   `!p1 p2. ~(p1 = []) /\ id_to_mods (i:(M,N)id) = APPEND p1 p2
            ==> nsLookupMod (alist_to_ns (x:(N#V)list):(M,N,V)namespace) p1
                = NONE`
   (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN CASES_ON `p1:M list` THEN
    REWRITE_TAC[nsLookupMod_alist_to_ns];
    ALL_TAC] THEN
  REWRITE_TAC[nsLookup_alist_to_ns_some; nsLookup_alist_to_ns_none] THEN
  CASES_ON `i:(M,N)id` THEN
  SIMP[MEM_MAP; o_THM; injectivity "id"; distinctness "id"] THEN
  MP_TAC(ISPECL [`x:(N#V)list`; `a:N`] NSPAUX_ALOOKUP_NONE) THEN
  REWRITE_TAC[MEM_MAP] THEN CASES_ON `ALOOKUP (x:(N#V)list) (a:N)` THEN
  SIMP[] THEN MESON_TAC[]);;

(* -------------- nsAll ---------------- *)

let eALL_T = prove
 (`!e:(M,N,V)namespace. nsAll (\n x. T) e`,
  RW[nsAll_def]);;

let nsLookup_nsAll = prove
 (`!(env:(M,N,V)namespace) x P v.
     nsAll P env /\ nsLookup env x = SOME v ==> P x v`,
  RW[nsAll_def]);;

(* HOL4 proves this by nsLookup_ind; nsLookup_nsAppend_some gives it at once *)
let nsAll_nsAppend = prove
 (`!f (e1:(M,N,V)namespace) e2.
     nsAll f e1 /\ nsAll f e2 ==> nsAll f (nsAppend e1 e2)`,
  REWRITE_TAC[nsAll_def; nsLookup_nsAppend_some] THEN MESON_TAC[]);;

let nsAll_nsBind = prove
 (`!P (x:N) (v:V) (e:(M,N,V)namespace).
     P (Short x) v /\ nsAll P e ==> nsAll P (nsBind x v e)`,
  RW[nsAll_def] THEN CASES_ON `id = Short (x:N):(M,N)id` THEN
  GVS[nsLookup_nsBind]);;

let nsAll_nsOptBind = prove
 (`!P (x:N option) (v:V) (e:(M,N,V)namespace).
     (x = NONE \/ ?n. x = SOME n /\ P (Short n) v) /\ nsAll P e
     ==> nsAll P (nsOptBind x v e)`,
  RW[nsOptBind_def] THEN FS[] THEN MATCH_MP_TAC nsAll_nsBind THEN
  ASM_REWRITE_TAC[]);;

(* HOL4: EVERY (\(n,v). R (Short n) v) l *)
let nsAll_alist_to_ns = prove
 (CASE_TERM `!R (l:(N#V)list).
     ALL (\nv. match nv with (n,v) -> R (Short n) v) l
     ==> nsAll R (alist_to_ns l:(M,N,V)namespace)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN SIMP[ALL] THEN
  PAIRARG_TAC THEN RW[alist_to_ns_cons] THEN
  MATCH_MP_TAC nsAll_nsBind THEN SIMP[]);;

let nsAll_nsLift = prove
 (`!R (mn:M) (e:(M,N,V)namespace).
     nsAll R (nsLift mn e) <=> nsAll (\id. R (Long mn id)) e`,
  RW[nsAll_def; nsLookup_nsLift] THEN EQ_TAC THEN RW[] THEN
  POP_ASSUM MP_TAC THEN CASES_ON `id:(M,N)id` THEN RW[COND_CASE_EQ]);;

let nsAll_nsAppend_left = prove
 (`!P (n1:(M,N,V)namespace) n2. nsAll P (nsAppend n1 n2) ==> nsAll P n1`,
  RW[nsAll_def] THEN FS[nsLookup_nsAppend_some]);;

(* -------------- nsSub ---------------- *)

let nsSub_conj = prove
 (`!P Q (e1:(M,N,V1)namespace) (e2:(M,N,V2)namespace).
     nsSub (\id x y. P id x y /\ Q id x y) e1 e2 <=>
     nsSub P e1 e2 /\ nsSub Q e1 e2`,
  RW[nsSub_def] THEN EQ_TAC THEN RW[] THEN ASM_MESON_TAC[option_INJ]);;

let nsSub_refl = prove
 (`!P R. (!n x. P n x ==> R n x x) ==>
         !e:(M,N,V)namespace. nsAll P e ==> nsSub R e e`,
  RW[nsSub_def] THEN ASM_MESON_TAC[nsLookup_nsAll]);;

let nsSub_nsBind = prove
 (`!R (x:N) (v1:V1) (v2:V2) (e1:(M,N,V1)namespace) (e2:(M,N,V2)namespace).
     R (Short x) v1 v2 /\ nsSub R e1 e2
     ==> nsSub R (nsBind x v1 e1) (nsBind x v2 e2)`,
  RW[nsSub_def] THENL
   [CASES_ON `id = Short (x:N):(M,N)id` THEN GVS[nsLookup_nsBind];
    POP_ASSUM MP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `path:M list`) THEN
    CASES_ON `path:M list` THEN FS[nsLookupMod_def] THEN
    CASES_ON `e1:(M,N,V1)namespace` THEN CASES_ON `e2:(M,N,V2)namespace` THEN
    FS[nsBind_def; nsLookupMod_def]]);;

let nsSub_nsAppend2 = prove
 (`!R (e1:(M,N,V)namespace) e2 e2'.
     nsSub R e1 e1 /\ nsSub R e2 e2'
     ==> nsSub R (nsAppend e1 e2) (nsAppend e1 e2')`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[nsSub_def; nsLookup_nsAppend_some; nsLookupMod_nsAppend_none] THEN
  STRIP_TAC THEN CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_MESON_TAC[option_DISTINCT]);;

(* the nsLookupMod analogue of nsLookup_nsLift_append *)
let NSPAUX_nsLookupMod_nsLift_append = prove
 (`!(m:M) (ns:(M,N,V)namespace) ns' m' p.
     nsLookupMod (nsAppend (nsLift m ns) ns') (CONS m' p) =
       if m = m' then nsLookupMod ns p else nsLookupMod ns' (CONS m' p)`,
  REPEAT GEN_TAC THEN CASES_ON `ns':(M,N,V)namespace` THEN
  RW[nsAppend_def; nsLift_def; nsLookupMod_def; APPEND; ALOOKUP_DEF] THEN
  FS[]);;

let nsSub_nsAppend_lift = prove
 (`!R (mn:M) (e1:(M,N,V1)namespace) (e1':(M,N,V2)namespace) e2 e2'.
     nsSub (\id. R (Long mn id)) e1 e1' /\ nsSub R e2 e2'
     ==> nsSub R (nsAppend (nsLift mn e1) e2) (nsAppend (nsLift mn e1') e2')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nsSub_def] THEN STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `i:(M,N)id` THEN CASES_ON `i:(M,N)id` THEN
    REWRITE_TAC[nsLookup_nsLift_append] THEN TRY COND_CASES_TAC THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `p:M list` THEN CASES_ON `p:M list` THEN
    REWRITE_TAC[nsLookupMod_def; option_DISTINCT;
                NSPAUX_nsLookupMod_nsLift_append] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[]]);;

let alist_rel_restr_def = cake_def
  `(alist_rel_restr (R:A->B->C->bool) (l1:(A#B)list) (l2:(A#C)list) [] <=> T) /\
   (alist_rel_restr R l1 l2 (CONS k1 keys) <=>
      match ALOOKUP l1 k1 with
        NONE -> F
      | SOME v1 ->
          match ALOOKUP l2 k1 with
            NONE -> F
          | SOME v2 -> R k1 v1 v2 /\ alist_rel_restr R l1 l2 keys)`;;

let alist_rel_restr_thm = prove
 (`!(R:A->B->C->bool) e1 e2 keys.
     alist_rel_restr R e1 e2 keys <=>
     !k. MEM k keys
         ==> ?v1 v2. ALOOKUP e1 k = SOME v1 /\ ALOOKUP e2 k = SOME v2 /\
                     R k v1 v2`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  RW[alist_rel_restr_def; MEM] THEN EVERY_CASE_TAC THEN FS[] THEN
  ASM_MESON_TAC[option_DISTINCT; option_INJ]);;

let alistSub_def = cake_def
  `alistSub (R:A->B->C->bool) (e1:(A#B)list) (e2:(A#C)list) <=>
     alist_rel_restr R e1 e2 (MAP FST e1)`;;

let alistSub_cong = prove
 (`!(l1:(A#B)list) (l2:(A#C)list) l1' l2' R R'.
     l1 = l1' /\ l2 = l2' /\
     (!n x y. ALOOKUP l1' n = SOME x /\ ALOOKUP l2' n = SOME y
              ==> R n x y = R' n x y)
     ==> (alistSub R l1 l2 <=> alistSub R' l1' l2')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC
              (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[alistSub_def] THEN
  SPEC_TAC(`MAP FST (l1':(A#B)list)`,`keys:A list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[alist_rel_restr_def] THEN
  EVERY_CASE_TAC THEN ASM_MESON_TAC[]);;

(* HOL4: val _ = DefnBase.export_cong "alistSub_cong" (definition-package  *)
(* automation, no HOL Light counterpart).                                   *)

(* HOL4 Definition nsSub_compute_def, with Termination                      *)
(*   WF_REL_TAC measure (\(p,r,env,_). namespace_size (\x.0) .. env)       *)
(* The recursive call sits under alistSub, which the kit's definition       *)
(* package cannot see through (HOL4 uses the congruence rule alistSub_cong):*)
(* the function is built with WF_REC on that measure, alistSub_cong giving  *)
(* the well-definedness, and nsSub_compute_ind is proved by WF induction.   *)

let NSPAUX_namespace_size_ALOOKUP = prove
 (`!fM fN fV (e1V:(N#V)list) (e1M:(M#(M,N,V)namespace)list) k v.
     ALOOKUP e1M k = SOME v
     ==> namespace_size fM fN fV v < namespace_size fM fN fV (Bind e1V e1M)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NSPAUX_ALOOKUP_MEM) THEN
  DISCH_THEN(MP_TAC o MATCH_MP
    (ISPEC `namespace_size_aux2 (fM:M->num) (fN:N->num) (fV:V->num)`
           MEM_LIST_SIZE)) THEN
  REWRITE_TAC[type_size_def "namespace"; hd (size_aux_eqs "namespace")] THEN
  ARITH_TAC);;

let NSPAUX_nsSub_compute_exists = prove
 (`?f:M list->((M,N)id->V1->V2->bool)->(M,N,V1)namespace->(M,N,V2)namespace->bool.
     !path R e1V e1M e2V e2M.
       f path R (Bind e1V e1M) (Bind e2V e2M) <=>
       alistSub (\k v1 v2. R (mk_id (REVERSE path) k) v1 v2) e1V e2V /\
       alistSub (\k v1 v2. f (CONS k path) R v1 v2) e1M e2M`,
  MP_TAC(ISPEC
   `\(g:M list#((M,N)id->V1->V2->bool)#(M,N,V1)namespace#(M,N,V2)namespace->bool)
     (x:M list#((M,N)id->V1->V2->bool)#(M,N,V1)namespace#(M,N,V2)namespace).
      namespace_CASE (FST(SND(SND x)))
        (\(e1V:(N#V1)list) (e1M:(M#(M,N,V1)namespace)list).
           namespace_CASE (SND(SND(SND x)))
             (\(e2V:(N#V2)list) (e2M:(M#(M,N,V2)namespace)list).
                alistSub (\k v1 v2. FST(SND x) (mk_id (REVERSE (FST x)) k) v1 v2)
                         e1V e2V /\
                alistSub (\k v1 v2. g (CONS k (FST x),FST(SND x),v1,v2))
                         e1M e2M))`
   (MATCH_MP WF_REC (ISPEC
    `\x:M list#((M,N)id->V1->V2->bool)#(M,N,V1)namespace#(M,N,V2)namespace.
       namespace_size (\x:M. 0) (\x:N. 0) (\x:V1. 0) (FST(SND(SND x)))`
    WF_measure))) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC
     [`f:M list#((M,N)id->V1->V2->bool)#(M,N,V1)namespace#
         (M,N,V2)namespace->bool`;
      `g:M list#((M,N)id->V1->V2->bool)#(M,N,V1)namespace#
         (M,N,V2)namespace->bool`] THEN
    GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN X_GEN_TAC `p:M list` THEN
    GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
    X_GEN_TAC `r:(M,N)id->V1->V2->bool` THEN
    GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
    X_GEN_TAC `n1:(M,N,V1)namespace` THEN X_GEN_TAC `n2:(M,N,V2)namespace` THEN
    REWRITE_TAC[measure_THM; FST; SND] THEN DISCH_TAC THEN
    CASES_ON `n1:(M,N,V1)namespace` THEN CASES_ON `n2:(M,N,V2)namespace` THEN
    REWRITE_TAC[case_def "namespace"] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC alistSub_cong THEN REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[FST; SND] THEN MATCH_MP_TAC NSPAUX_namespace_size_ALOOKUP THEN
    ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_TAC
     `g:M list#((M,N)id->V1->V2->bool)#(M,N,V1)namespace#
        (M,N,V2)namespace->bool`) THEN
    EXISTS_TAC `\(p:M list) (r:(M,N)id->V1->V2->bool) (n1:(M,N,V1)namespace)
                  (n2:(M,N,V2)namespace). g (p,r,n1,n2):bool` THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    REWRITE_TAC[FST; SND; case_def "namespace"]]);;

let nsSub_compute_def = new_specification ["nsSub_compute"]
  NSPAUX_nsSub_compute_exists;;

let nsSub_compute_ind = prove
 (`!P:M list->((M,N)id->V1->V2->bool)->(M,N,V1)namespace->(M,N,V2)namespace->bool.
     (!path R e1V e1M e2V e2M.
        (!k v1 v2. ALOOKUP e1M k = SOME v1 /\ ALOOKUP e2M k = SOME v2
                   ==> P (CONS k path) R v1 v2)
        ==> P path R (Bind e1V e1M) (Bind e2V e2M))
     ==> !x1 x2 x3 x4. P x1 x2 x3 x4`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "hyp") THEN
  SUBGOAL_THEN
   `!(x3:(M,N,V1)namespace) x1 x2 x4.
      (P:M list->((M,N)id->V1->V2->bool)->(M,N,V1)namespace->
         (M,N,V2)namespace->bool) x1 x2 x3 x4`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC(REWRITE_RULE[WF_IND]
    (ISPEC `namespace_size (\x:M. 0) (\x:N. 0) (\x:V1. 0)` WF_measure)) THEN
  X_GEN_TAC `x3:(M,N,V1)namespace` THEN REWRITE_TAC[measure_THM] THEN
  DISCH_TAC THEN CASES_ON `x3:(M,N,V1)namespace` THEN
  X_GEN_TAC `x1:M list` THEN X_GEN_TAC `x2:(M,N)id->V1->V2->bool` THEN
  X_GEN_TAC `x4:(M,N,V2)namespace` THEN CASES_ON `x4:(M,N,V2)namespace` THEN
  USE_THEN "hyp" MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v1:(M,N,V1)namespace`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC NSPAUX_namespace_size_ALOOKUP THEN ASM_MESON_TAC[];
    SIMP_TAC[]]);;

(* HOL4: FOLDR nsLift e p is ITLIST nsLift p e *)

let nsLookup_FOLDR_nsLift = prove
 (`!(e:(M,N,V)namespace) (p:M list) (k:N).
     nsLookup (ITLIST nsLift p e) (mk_id p k) = nsLookup e (Short k)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITLIST; mk_id_def; nsLookup_nsLift; case_def "id"]);;

let nsLookup_FOLDR_nsLift_some = prove
 (`!(e:(M,N,V)namespace) (p:M list) id v.
     nsLookup (ITLIST nsLift p e) id = SOME v <=>
     (p = [] /\ nsLookup e id = SOME v) \/
     (~(p = []) /\
      ?p2 n. id = mk_id (APPEND p p2) n /\ nsLookup e (mk_id p2 n) = SOME v)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; NOT_CONS_NIL] THEN
  X_GEN_TAC `i:(M,N)id` THEN GEN_TAC THEN CASES_ON `i:(M,N)id` THEN
  REWRITE_TAC[nsLookup_nsLift; case_def "id"; APPEND; mk_id_def;
              distinctness "id"; injectivity "id"; option_DISTINCT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  ASM_CASES_TAC `t:M list = []` THEN ASM_REWRITE_TAC[APPEND] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`id_to_mods (a1:(M,N)id)`; `id_to_n (a1:(M,N)id)`] THEN
  ASM_REWRITE_TAC[mk_id_thm]);;

(* HOL4: IS_PREFIX p1 p2 \/ IS_PREFIX p2 p1, i.e. p2 <<= p1 \/ p1 <<= p2 *)
let nsLookupMod_FOLDR_nsLift_none = prove
 (`!(e:(M,N,V)namespace) (p1:M list) p2.
     nsLookupMod (ITLIST nsLift p1 e) p2 = NONE <=>
     ((p2 <<= p1 \/ p1 <<= p2) ==>
      ?p3. p2 = APPEND p1 p3 /\ nsLookupMod e p3 = NONE)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ITLIST; APPEND; isPREFIX; UNWIND_THM1] THEN
  X_GEN_TAC `p2:M list` THEN CASES_ON `p2:M list` THEN
  REWRITE_TAC[nsLookupMod_nsLift; list_CASE; isPREFIX; option_DISTINCT;
              NOT_CONS_NIL; CONS_11] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* HOL4: nsSub_compute_thm_general and nsSub_compute_thm are commented out *)
(* in the HOL4 script (not part of the theory).                            *)

(* -------------- nsAll2 ---------------- *)

let nsAll2_conj = prove
 (`!P Q (e1:(M,N,V1)namespace) (e2:(M,N,V2)namespace).
     nsAll2 (\id x y. P id x y /\ Q id x y) e1 e2 <=>
     nsAll2 P e1 e2 /\ nsAll2 Q e1 e2`,
  REWRITE_TAC[nsAll2_def; nsSub_conj] THEN CONV_TAC TAUT);;

let nsAll2_nsLookup1 = prove
 (`!R (e1:(M,N,V1)namespace) (e2:(M,N,V2)namespace) n v1.
     nsLookup e1 n = SOME v1 /\ nsAll2 R e1 e2
     ==> ?v2. nsLookup e2 n = SOME v2 /\ R n v1 v2`,
  REWRITE_TAC[nsSub_def; nsAll2_def] THEN MESON_TAC[]);;

let nsAll2_nsLookup2 = prove
 (`!R (e1:(M,N,V1)namespace) (e2:(M,N,V2)namespace) n v2.
     nsLookup e2 n = SOME v2 /\ nsAll2 R e1 e2
     ==> ?v1. nsLookup e1 n = SOME v1 /\ R n v1 v2`,
  REWRITE_TAC[nsSub_def; nsAll2_def] THEN MESON_TAC[]);;

let nsAll2_nsLookup_none = prove
 (`!R (e1:(M,N,V1)namespace) (e2:(M,N,V2)namespace) n.
     nsAll2 R e1 e2 ==> (nsLookup e1 n = NONE <=> nsLookup e2 n = NONE)`,
  REWRITE_TAC[nsSub_def; nsAll2_def] THEN
  MESON_TAC[option_DISTINCT; cases "option"]);;

let nsAll2_nsBind = prove
 (`!R (x:N) (v1:V1) (v2:V2) (e1:(M,N,V1)namespace) (e2:(M,N,V2)namespace).
     R (Short x) v1 v2 /\ nsAll2 R e1 e2
     ==> nsAll2 R (nsBind x v1 e1) (nsBind x v2 e2)`,
  RW[nsAll2_def] THEN MATCH_MP_TAC nsSub_nsBind THEN ASM_REWRITE_TAC[]);;

(* HOL4: LIST_REL (\(x,y) (x',y'). x = x' /\ R (Short x) y y') l1 l2 *)
let nsAll2_nsBindList = prove
 (CASE_TERM `!R (l1:(N#V1)list) (l2:(N#V2)list) (e1:(M,N,V1)namespace) e2.
     ALL2 (\xy xy'. match xy with (x,y) -> match xy' with (x',y') ->
                      x = x' /\ R (Short x) y y') l1 l2 /\
     nsAll2 R e1 e2
     ==> nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; nsBindList_def; ITLIST] THEN
  REWRITE_TAC[GSYM nsBindList_def] THEN
  PAIRARG_TAC THEN PAIRARG_TAC THEN
  REPEAT STRIP_TAC THEN RVEQ_TAC THEN
  MATCH_MP_TAC nsAll2_nsBind THEN ASM_SIMP_TAC[]);;

(* nsSub of two appends, with the reverse inclusion of the left operands *)
let NSPAUX_nsSub_nsAppend = prove
 (`!(R:(M,N)id->V1->V2->bool) (R':(M,N)id->V2->V1->bool)
    (e1:(M,N,V1)namespace) (e2:(M,N,V2)namespace) e1' e2'.
     nsSub R e1 e2 /\ nsSub R' e2 e1 /\ nsSub R e1' e2'
     ==> nsSub R (nsAppend e1 e1') (nsAppend e2 e2')`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[nsSub_def; nsLookup_nsAppend_some; nsLookupMod_nsAppend_none] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "l1") (LABEL_TAC "m1"))
    (CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 (LABEL_TAC "l2") (LABEL_TAC "m2"))
      (CONJUNCTS_THEN2 (LABEL_TAC "l3") (LABEL_TAC "m3")))) THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:(M,N)id`; `v:V1`] THEN STRIP_TAC THENL
     [USE_THEN "l1" (fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
      EXISTS_TAC `v2:V2` THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `nsLookup (e2:(M,N,V2)namespace) i = NONE` ASSUME_TAC THENL
       [MP_TAC(ISPEC `nsLookup (e2:(M,N,V2)namespace) i` (cases "option")) THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "l2" (fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
           lhs(concl th) = `nsLookup (e1:(M,N,V1)namespace) i` &&
           is_comb(rhs(concl th)))) THEN
        ASM_REWRITE_TAC[option_DISTINCT];
        ALL_TAC] THEN
      USE_THEN "l3" (fun th -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
      EXISTS_TAC `v2:V2` THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
      REPEAT STRIP_TAC THEN USE_THEN "m2" MATCH_MP_TAC THEN ASM_MESON_TAC[]];
    X_GEN_TAC `path:M list` THEN STRIP_TAC THEN
    (CONJ_TAC THENL [USE_THEN "m1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC])
    THENL
     [DISJ1_TAC THEN USE_THEN "m3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`p1:M list`; `p2:M list`] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `nsLookupMod (e1:(M,N,V1)namespace) p1` (cases "option")) THEN
      STRIP_TAC THENL
       [USE_THEN "m2" (fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
        ASM_REWRITE_TAC[option_DISTINCT];
        ASM_MESON_TAC[]]]]);;

let nsAll2_nsAppend = prove
 (`!R (e1:(M,N,V1)namespace) e1' (e2:(M,N,V2)namespace) e2'.
     nsAll2 R e1 e2 /\ nsAll2 R e1' e2'
     ==> nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2')`,
  REWRITE_TAC[nsAll2_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NSPAUX_nsSub_nsAppend THEN ASM_MESON_TAC[]);;

let nsAll2_alist_to_ns = prove
 (CASE_TERM `!R (l1:(N#V1)list) (l2:(N#V2)list).
     ALL2 (\xy xy'. match xy with (x,y) -> match xy' with (x',y') ->
                      x = x' /\ R (Short x) y y') l1 l2
     ==> nsAll2 R (alist_to_ns l1:(M,N,V1)namespace) (alist_to_ns l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; alist_to_ns_nil; nsAll2_nsEmpty] THEN
  PAIRARG_TAC THEN PAIRARG_TAC THEN REWRITE_TAC[alist_to_ns_cons] THEN
  STRIP_TAC THEN RVEQ_TAC THEN MATCH_MP_TAC nsAll2_nsBind THEN
  ASM_SIMP_TAC[]);;

let NSPAUX_nsSub_nsLift = prove
 (`!R (mn:M) (e1:(M,N,V1)namespace) (e2:(M,N,V2)namespace).
     nsSub R (nsLift mn e1) (nsLift mn e2) <=>
     nsSub (\id. R (Long mn id)) e1 e2`,
  REWRITE_TAC[nsSub_def] THEN REPEAT GEN_TAC THEN BINOP_TAC THEN EQ_TAC THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`Long (mn:M) id:(M,N)id`; `v1:V1`]) THEN
    ASM_REWRITE_TAC[nsLookup_nsLift; case_def "id"];
    POP_ASSUM MP_TAC THEN CASES_ON `id:(M,N)id` THEN
    REWRITE_TAC[nsLookup_nsLift; case_def "id"; option_DISTINCT] THEN
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `CONS (mn:M) path`) THEN
    ASM_REWRITE_TAC[nsLookupMod_nsLift; list_CASE];
    POP_ASSUM MP_TAC THEN CASES_ON `path:M list` THEN
    REWRITE_TAC[nsLookupMod_nsLift; list_CASE; option_DISTINCT] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[]]);;

let nsAll2_nsLift = prove
 (`!R (mn:M) (e1:(M,N,V1)namespace) (e2:(M,N,V2)namespace).
     nsAll2 R (nsLift mn e1) (nsLift mn e2) <=>
     nsAll2 (\id. R (Long mn id)) e1 e2`,
  REWRITE_TAC[nsAll2_def; NSPAUX_nsSub_nsLift]);;

(* -------------- nsMap --------------- *)

(* HOL4: MAP (\(k,v). (k, f v)) l *)
let nsMap_alist_to_ns = prove
 (CASE_TERM `!(f:V->W) (l:(N#V)list).
     nsMap f (alist_to_ns l:(M,N,V)namespace) =
     alist_to_ns (MAP (\kv. match kv with (k,v) -> (k,f v)) l)`,
  REWRITE_TAC[alist_to_ns_def; nsMap_def; MAP]);;

let nsMap_compose = prove
 (`!(g:U->V) (e:(M,N,U)namespace) (f:V->W).
     nsMap f (nsMap g e) = nsMap (f o g) e`,
  MATCH_MP_TAC nsMap_ind THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[nsMap_def; GSYM MAP_o; injectivity "namespace"] THEN
  CONJ_TAC THEN MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  REWRITE_TAC[FORALL_PAIR_THM; o_THM; pair_CASE] THEN ASM_MESON_TAC[]);;

let nsMap_I = prove
 (`!ns:(M,N,V)namespace. nsMap I ns = ns`,
  SUBGOAL_THEN `!(f:V->V) (ns:(M,N,V)namespace). f = I ==> nsMap f ns = ns`
    (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC nsMap_ind THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[nsMap_def; injectivity "namespace"] THEN CONJ_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM MAP_ID] THEN MATCH_MP_TAC MAP_EQ THEN
  REWRITE_TAC[GSYM ALL_MEM; FORALL_PAIR_THM; pair_CASE; I_THM] THEN
  ASM_MESON_TAC[]);;

(* HOL4 proves this by nsAppend_ind (no such theorem here: case splits) *)
let nsMap_nsAppend = prove
 (`!(n1:(M,N,V)namespace) n2 (f:V->W).
     nsMap f (nsAppend n1 n2) = nsAppend (nsMap f n1) (nsMap f n2)`,
  REPEAT GEN_TAC THEN CASES_ON `n1:(M,N,V)namespace` THEN
  CASES_ON `n2:(M,N,V)namespace` THEN
  REWRITE_TAC[nsAppend_def; nsMap_def; MAP_APPEND]);;

(* local copy of alist ALOOKUP_MAP, pointwise *)
let NSPAUX_ALOOKUP_MAP = prove
 (CASE_TERM `!(f:B->C) (l:(A#B)list) k.
     ALOOKUP (MAP (\p. match p with (x,y) -> (x,f y)) l) k =
     OPTION_MAP f (ALOOKUP l k)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; ALOOKUP_DEF; OPTION_MAP_DEF] THEN
  GEN_TAC THEN MP_TAC(ISPEC `h:A#B` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[pair_CASE; FST; SND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF]);;

let nsLookupMod_nsMap = prove
 (`!(n:(M,N,V)namespace) x (f:V->W).
     nsLookupMod (nsMap f n) x = OPTION_MAP (nsMap f) (nsLookupMod n x)`,
  MATCH_MP_TAC nsLookupMod_ind THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[nsMap_def; nsLookupMod_def; OPTION_MAP_DEF; NSPAUX_ALOOKUP_MAP] THEN
  CASES_ON `ALOOKUP (m:(M#(M,N,V)namespace)list) mn` THEN
  ASM_SIMP_TAC[OPTION_MAP_DEF; option_CASE]);;

let nsLookup_nsMap = prove
 (`!(n:(M,N,V)namespace) x (f:V->W).
     nsLookup (nsMap f n) x = OPTION_MAP f (nsLookup n x)`,
  MATCH_MP_TAC nsLookup_ind THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[nsMap_def; nsLookup_def; NSPAUX_ALOOKUP_MAP] THEN
  CASES_ON `ALOOKUP (m:(M#(M,N,V)namespace)list) mn` THEN
  ASM_SIMP_TAC[OPTION_MAP_DEF; option_CASE]);;

let nsAll_nsMap = prove
 (`!(f:V->W) (n:(M,N,V)namespace) P.
     nsAll P (nsMap f n) <=> nsAll (\x y. P x (f y)) n`,
  REWRITE_TAC[nsAll_def; nsLookup_nsMap] THEN REPEAT GEN_TAC THEN EQ_TAC THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[OPTION_MAP_DEF];
    POP_ASSUM MP_TAC THEN
    CASES_ON `nsLookup (n:(M,N,V)namespace) id` THEN
    REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let nsLift_nsMap = prove
 (`!(f:V->W) (n:(M,N,V)namespace) mn.
     nsLift mn (nsMap f n) = nsMap f (nsLift mn n)`,
  REWRITE_TAC[nsLift_def; nsMap_def; MAP; pair_CASE]);;

(* local copy of option OPTION_MAP_EQ_NONE *)
let NSPAUX_OPTION_MAP_EQ_NONE = prove
 (`!(f:A->B) x. OPTION_MAP f x = NONE <=> x = NONE`,
  GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT]);;

let nsSub_nsMap = prove
 (`!R (f:V->W) (n1:(M,N,V)namespace) n2.
     nsSub R (nsMap f n1) (nsMap f n2) <=>
     nsSub (\id x y. R id (f x) (f y)) n1 n2`,
  REWRITE_TAC[nsSub_def; nsLookup_nsMap; nsLookupMod_nsMap] THEN
  REPEAT GEN_TAC THEN BINOP_TAC THENL
   [EQ_TAC THEN REPEAT STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`id:(M,N)id`; `(f:V->W) v1`]) THEN
      ASM_REWRITE_TAC[OPTION_MAP_DEF] THEN
      CASES_ON `nsLookup (n2:(M,N,V)namespace) id` THEN
      REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
      MESON_TAC[];
      POP_ASSUM MP_TAC THEN
      CASES_ON `nsLookup (n1:(M,N,V)namespace) id` THEN
      REWRITE_TAC[OPTION_MAP_DEF; option_DISTINCT; option_INJ] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`id:(M,N)id`; `a:V`]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      EXISTS_TAC `(f:V->W) v2` THEN ASM_REWRITE_TAC[OPTION_MAP_DEF]];
    REWRITE_TAC[NSPAUX_OPTION_MAP_EQ_NONE]]);;

(* --------------- nsDom --------------- *)

let nsLookup_nsDom = prove
 (`!x (n:(M,N,V)namespace). x IN nsDom n <=> ?v. nsLookup n x = SOME v`,
  REWRITE_TAC[nsDom_def; IN_ELIM_THM]);;

let nsDomMod_alist_to_ns = prove
 (`!l:(N#V)list. nsDomMod (alist_to_ns l:(M,N,V)namespace) = {[]}`,
  REWRITE_TAC[nsDomMod_def; EXTENSION; IN_ELIM_THM; IN_SING] THEN
  GEN_TAC THEN X_GEN_TAC `x:M list` THEN CASES_ON `x:M list` THEN
  REWRITE_TAC[nsLookupMod_def; nsLookupMod_alist_to_ns; option_DISTINCT;
              NOT_CONS_NIL] THEN
  MESON_TAC[]);;

(* HOL4: Theorem lemma[local] *)
let lemma = prove
 (`!y:A option. (?x. y = SOME x) <=> ~(y = NONE)`,
  MATCH_MP_TAC option_INDUCT THEN
  REWRITE_TAC[option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let nsDom_nsAppend_equal = prove
 (`!(n1:(M,N,V1)namespace) n2 (n3:(M,N,V2)namespace) n4.
     nsDom n1 = nsDom n3 /\ nsDom n2 = nsDom n4 /\
     nsDomMod n1 = nsDomMod n3 /\ nsDomMod n2 = nsDomMod n4
     ==> nsDom (nsAppend n1 n2) = nsDom (nsAppend n3 n4) /\
         nsDomMod (nsAppend n1 n2) = nsDomMod (nsAppend n3 n4)`,
  REWRITE_TAC[nsDom_def; nsDomMod_def; EXTENSION; IN_ELIM_THM; lemma] THEN
  REWRITE_TAC[TAUT `(~a <=> ~b) <=> (a <=> b)`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[nsLookup_nsAppend_none; nsLookupMod_nsAppend_none;
                  RIGHT_EXISTS_AND_THM; lemma]);;

let nsDom_nsLift = prove
 (`!(mn:M) (n:(M,N,V)namespace).
     nsDom (nsLift mn n) = IMAGE (Long mn) (nsDom n)`,
  REWRITE_TAC[nsDom_def; EXTENSION; IN_ELIM_THM; IN_IMAGE; nsLookup_nsLift] THEN
  REPEAT GEN_TAC THEN CASES_ON `x:(M,N)id` THEN
  REWRITE_TAC[case_def "id"; option_DISTINCT; distinctness "id";
              injectivity "id"; GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM;
              UNWIND_THM1] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]);;

let nsDomMod_nsLift = prove
 (`!(mn:M) (n:(M,N,V)namespace).
     nsDomMod (nsLift mn n) = [] INSERT IMAGE (CONS mn) (nsDomMod n)`,
  REWRITE_TAC[nsDomMod_def; EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_INSERT;
              nsLookupMod_nsLift] THEN
  REPEAT GEN_TAC THEN CASES_ON `x:M list` THEN
  REWRITE_TAC[list_CASE; option_DISTINCT; NOT_CONS_NIL; CONS_11;
              option_INJ; GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM;
              UNWIND_THM1] THENL
   [MESON_TAC[];
    COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT]]);;

let nsDom_nsAppend_flat = prove
 (`!(n1:(M,N,V)namespace) n2.
     nsDomMod n1 = {[]} ==> nsDom (nsAppend n1 n2) = nsDom n1 UNION nsDom n2`,
  REWRITE_TAC[nsDom_def; nsDomMod_def; EXTENSION; IN_ELIM_THM; IN_SING;
              IN_UNION; lemma] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:(M,N)id` THEN
  ASM_REWRITE_TAC[nsLookup_nsAppend_none; RIGHT_EXISTS_AND_THM; lemma] THEN
  MESON_TAC[]);;

let nsDomMod_nsAppend_flat = prove
 (`!(n1:(M,N,V)namespace) n2.
     nsDomMod n1 = {[]} ==> nsDomMod (nsAppend n1 n2) = nsDomMod n2`,
  REWRITE_TAC[nsDomMod_def; EXTENSION; IN_ELIM_THM; IN_SING; lemma] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:M list` THEN
  ASM_REWRITE_TAC[nsLookupMod_nsAppend_none; RIGHT_EXISTS_AND_THM; lemma] THEN
  ASM_CASES_TAC `x:M list = []` THEN
  ASM_REWRITE_TAC[nsLookupMod_def; option_DISTINCT] THEN
  ASM_MESON_TAC[]);;

(* HOL4 [simp] theorems not registered above, registered for the files    *)
(* that load this one (HOL4 srw_ss)                                       *)
let _ = cake_add_simps [alist_to_ns_cons; nsAppend_nsBind; nsAppend_alist_to_ns;
  nsAppend_assoc; nsLookup_nsBind; nsAppend_nsSing; nsLookup_nsSing;
  nsAll_nsSing; nsAll2_nsSing; nsMap_nsSing; nsLookupMod_nsSing; nsBind_11;
  nsDom_nsBind; nsDom_nsSing; nsDomMod_nsBind; nsDomMod_nsSing;
  nsLookupMod_alist_to_ns; alist_to_ns_11; nsDom_alist_to_ns;
  nsLookup_nsLift_append; nsDom_nsAppend_alist; eALL_T; nsAll_nsLift;
  nsAll2_nsLift; nsMap_alist_to_ns; nsMap_I; nsDomMod_alist_to_ns];;
