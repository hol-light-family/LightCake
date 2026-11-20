(* ========================================================================= *)
(* data_to_word_memoryProof_p2: part 2 of 7 (HOL4 lines 2748-5513) of the    *)
(* port of HOL4 compiler/backend/proofs/data_to_word_memoryProofScript.sml   *)
(* (CakeML v3479).  Part of the correctness proof for data_to_word.          *)
(* The parts _p1 ... _p7 are loaded one after the other (each needs the     *)
(* previous one); data_to_word_memoryProof.ml needs the last.                *)
(* MP2AUX_ names are local helpers of this part.                            *)
(* ========================================================================= *)

needs "compiler/backend/proofs/data_to_word_memoryProof_p1.ml";;

prioritize_num();;
type_invention_error := true;;

(* ===== PART 2: HOL4 lines 2748-5513 ===== *)

(* MP2AUX: the v_all_vs of an element of v_all_vs l are in v_all_vs l *)
let MP2AUX_v_all_vs_trans = prove
 (`!x y z. MEM y (v_all_vs x) /\ MEM z (v_all_vs [y]) ==> MEM z (v_all_vs x)`,
  REPEAT GEN_TAC THEN CASES_ON `y:data_v` THEN
  REWRITE_TAC[v_all_vs_def; APPEND; APPEND_NIL; MEM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP v_all_vs_MEM) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[MEM_APPEND; MEM]);;

(* HOL4 line 2748 *)
let v_in_all_vs = prove
 (`!x y stack refs.
     x IN all_vs refs stack /\ MEM y (v_all_vs [x])
     ==> y IN all_vs refs stack`,
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[MP2AUX_v_all_vs_trans]);;

(* MP2AUX: a value is in its own v_all_vs, the payload of a block in the   *)
(* block's                                                                *)
let MP2AUX_MEM_v_all_vs_single = prove
 (`(!v. MEM v (v_all_vs [v])) /\
   (!a b l x. MEM x (v_all_vs l) ==> MEM x (v_all_vs [data_Block a b l]))`,
  CONJ_TAC THENL [GEN_TAC THEN CASES_ON `v:data_v`; ALL_TAC] THEN
  REWRITE_TAC[v_all_vs_def; MEM; MEM_APPEND] THEN MESON_TAC[]);;

(* MP2AUX: every element of v_all_vs l comes from one element of l *)
let MP2AUX_v_all_vs_MEM2_gen = prove
 (`!l x. MEM x (v_all_vs l) ==> ?y. MEM y l /\ MEM x (v_all_vs [y])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[v_all_vs_def; MEM] THEN
  CASES_ON `h:data_v` THEN
  REWRITE_TAC[v_all_vs_def; MEM; MEM_APPEND; APPEND_NIL; APPEND] THEN
  ASM_MESON_TAC[MP2AUX_MEM_v_all_vs_single]);;

(* HOL4 line 2778 *)
let v_all_vs_MEM2 = prove
 (`!l ts tag xs.
     MEM (data_Block ts tag xs) (v_all_vs l)
     ==> ?x. MEM x l /\ MEM (data_Block ts tag xs) (v_all_vs [x])`,
  MESON_TAC[MP2AUX_v_all_vs_MEM2_gen]);;

(* HOL4 line 2792 *)
let v_all_vs_ts = prove
 (`!x ts tag xs.
     MEM (data_Block ts tag xs) (v_all_vs [x]) ==> MEM ts (v_all_ts x)`,
  MATCH_MP_TAC data_to_word_memoryProof_v_ind THEN
  REWRITE_TAC[v_all_vs_def; v_all_ts_def; MEM; APPEND_NIL; GSYM ALL_MEM] THEN
  SIMP[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP v_all_vs_MEM2) THEN
  REWRITE_TAC[MEM_FLAT; MEM_MAP] THEN ASM_MESON_TAC[]);;

(* HOL4 line 2803 *)
let MEM_v_all_vs = prove
 (`!l v. MEM v l ==> MEM v (v_all_vs l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THEN CASES_ON `h:data_v` THEN
  REWRITE_TAC[v_all_vs_def; MEM; MEM_APPEND] THEN ASM_MESON_TAC[]);;

(* HOL4 line 2811 *)
let MEM_stack_all_vs = prove
 (`!v stack (refs:(data_v bvl_ref)spt). MEM v stack ==> v IN all_vs refs stack`,
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[MEM_v_all_vs]);;

(* HOL4 line 2817 *)
let v_all_vs_ts_MEM = prove
 (`!x y ts. MEM ts (v_all_ts x) /\ MEM x (v_all_vs [y]) ==> MEM ts (v_all_ts y)`,
  GEN_TAC THEN MATCH_MP_TAC data_to_word_memoryProof_v_ind THEN
  REWRITE_TAC[v_all_vs_def; v_all_ts_def; MEM; APPEND_NIL; GSYM ALL_MEM] THEN
  REPEAT STRIP_TAC THEN
  TRY(FIRST_X_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[v_all_ts_def; MEM]) THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  DISJ2_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MP2AUX_v_all_vs_MEM2_gen) THEN
  REWRITE_TAC[MEM_FLAT; MEM_MAP] THEN ASM_MESON_TAC[]);;

(* HOL4 line 2831 *)
let v_all_vs_trans = prove
 (`!x y z. MEM y (v_all_vs x) /\ MEM z (v_all_vs [y]) ==> MEM z (v_all_vs x)`,
  REWRITE_TAC[MP2AUX_v_all_vs_trans]);;

(* MP2AUX: the time stamps of the values of v_all_vs l come from l *)
let MP2AUX_v_all_vs_ts_lift = prove
 (`!l x ts. MEM x (v_all_vs l) /\ MEM ts (v_all_ts x) ==>
            ?y. MEM y l /\ MEM ts (v_all_ts y)`,
  MESON_TAC[MP2AUX_v_all_vs_MEM2_gen; v_all_vs_ts_MEM]);;

(* HOL4 line 2838 *)
let MEM_in_all_ts = prove
 (`!x ts stack refs.
     x IN all_vs refs stack /\ MEM ts (v_all_ts x)
     ==> ts IN all_ts refs stack`,
  REWRITE_TAC[all_vs_def; all_ts_def; LET_DEF; LET_END_DEF; IN_UNION;
              IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[MP2AUX_v_all_vs_ts_lift; find_ref_def; MEM; MEM_APPEND]);;

(* HOL4 line 2897 *)
let MEM_in_all_vs = prove
 (`!x y refs stack.
     x IN all_vs refs stack /\ MEM y (v_all_vs [x]) ==> y IN all_vs refs stack`,
  MESON_TAC[v_in_all_vs]);;

(* HOL4 line 2905 *)
let v_all_vs_ts_list = prove
 (`!x y ts.
     MEM x (v_all_vs y) /\ MEM ts (v_all_ts x) ==> MEM ts (FLAT (MAP v_all_ts y))`,
  REWRITE_TAC[MEM_FLAT; MEM_MAP] THEN MESON_TAC[MP2AUX_v_all_vs_ts_lift]);;

let MP2AUX_v_inv_ck_RefPtr = prove
 (`!ck conf b n (refs:(data_v bvl_ref)spt) x f tf
    heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
          heap_element)list.
     v_inv_ck ck conf (data_RefPtr b n) refs (x,f,tf,heap) <=>
     (n IN FDOM f /\
      (!ev v. ~(lookup n refs = SOME (bvl_Thunk ev v))) /\
      (!tg fin l c r. lookup n refs = SOME (MutBlock tg fin l c r) ==> ~b) /\
      x = Pointer (FAPPLY f n) (ref_ptr_annot conf (lookup n refs))) \/
     (?ev v y.
         lookup n refs = SOME (bvl_Thunk ev v) /\
         (ev = Evaluated ==> data_dest_thunk v refs = data_NotThunk) /\
         n IN FDOM f /\
         heap_lookup (FAPPLY f n) heap = SOME (ThunkBlock ev y) /\
         (~(ck = 0) ==> v_inv_ck (ck - 1) conf v refs (y,f,tf,heap)) /\
         ~b /\
         x = Pointer (FAPPLY f n) (wl_Word (word 0))) \/
     (?v. lookup n refs = SOME (bvl_Thunk Evaluated v) /\
          data_dest_thunk v refs = data_NotThunk /\
          ~b /\
          (~(ck = 0) ==> v_inv_ck (ck - 1) conf v refs (x,f,tf,heap)))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [v_inv_ck_cases] THEN
  SIMP[PAIR_EQ] THEN MESON_TAC[]);;

let MP2AUX_v_inv_ck_thms = end_itlist CONJ
  [MP1AUX_v_inv_ck_Number; MP1AUX_v_inv_ck_Word64; MP1AUX_v_inv_ck_CodePtr;
   MP2AUX_v_inv_ck_RefPtr; MP1AUX_v_inv_ck_Block];;

(* MP2AUX: the heap elements that v_inv_ck reads are not RefBlocks, and   *)
(* only Block values read BlockRep cells                                  *)
let MP2AUX_heap_el_facts = prove
 (`(!i zs. ~(Bignum i:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                     heap_element = RefBlock zs)) /\
   (!i tag zs. ~(Bignum i:(A word_loc,data_to_word_memoryProof_tag#
                           (A word_loc)list)heap_element = BlockRep tag zs)) /\
   (!w zs. ~(Word64Rep (:A) w:(A word_loc,data_to_word_memoryProof_tag#
                              (A word_loc)list)heap_element = RefBlock zs)) /\
   (!w tag zs. ~(Word64Rep (:A) w:(A word_loc,data_to_word_memoryProof_tag#
                              (A word_loc)list)heap_element = BlockRep tag zs)) /\
   (!ev (y:A heap_address) zs.
      ~(ThunkBlock ev y:(A,data_to_word_memoryProof_tag#B list)heap_element =
        RefBlock zs)) /\
   (!ev (y:A heap_address) tag zs.
      ~(ThunkBlock ev y:(A,data_to_word_memoryProof_tag#B list)heap_element =
        BlockRep tag zs)) /\
   (!tag (zs:(A heap_address)list) zs'.
      ~(BlockRep tag zs:(A,data_to_word_memoryProof_tag#B list)heap_element =
        RefBlock zs'))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_memoryProof_Bignum_def; Word64Rep_def; RefBlock_def;
              BlockRep_def; ThunkBlock_def] THEN
  TRY PAIRARG_TAC THEN TRY COND_CASES_TAC THEN SIMP[]);;

(* MP2AUX: ALL2 with membership *)
let MP2AUX_ALL2_MEM_IMP = prove
 (`!(P:A->B->bool) Q l xs.
     (!v x. MEM v l /\ P v x ==> Q v x) /\ ALL2 P l xs ==> ALL2 Q l xs`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; MEM] THEN ASM_MESON_TAC[]);;

(* MP2AUX: v_inv_ck reads refs, tf and heap only in a few ways; a state   *)
(* that agrees with the old one in those ways keeps v_inv_ck.  S is a set *)
(* of time stamps that contains those of the value and of every thunk.    *)
let MP2AUX_v_inv_ck_transfer = prove
 (`!conf (refs:(data_v bvl_ref)spt) refs2 f tf tf2
    (heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list) heap2 S.
     (!t p. t IN S /\ FLOOKUP tf t = SOME p ==> FLOOKUP tf2 t = SOME p) /\
     (!n ev v. lookup n refs = SOME (bvl_Thunk ev v) ==>
               !t. MEM t (v_all_ts v) ==> t IN S) /\
     (!p X. heap_lookup p heap = SOME X /\ (!zs. ~(X = RefBlock zs)) /\
            (!tag zs. X = BlockRep tag zs ==> ?t. t IN S /\ FLOOKUP tf t = SOME p)
            ==> heap_lookup p heap2 = SOME X) /\
     (!n. n IN FDOM f /\ (!ev v. ~(lookup n refs = SOME (bvl_Thunk ev v))) ==>
          (!ev v. ~(lookup n refs2 = SOME (bvl_Thunk ev v))) /\
          ref_ptr_annot conf (lookup n refs2) =
            (ref_ptr_annot conf (lookup n refs):(A)word_loc) /\
          (!tg fin l c r. lookup n refs2 = SOME (MutBlock tg fin l c r) ==>
              ?tg' fin' l' c' r'. lookup n refs = SOME (MutBlock tg' fin' l' c' r'))) /\
     (!n ev v. lookup n refs = SOME (bvl_Thunk ev v) ==>
               lookup n refs2 = SOME (bvl_Thunk ev v)) /\
     (!v. data_dest_thunk v refs = data_NotThunk ==>
          data_dest_thunk v refs2 = data_NotThunk)
     ==> !ck w (x:(A word_loc)heap_address).
           v_inv_ck ck conf w refs (x,f,tf,heap) /\
           (!t. MEM t (v_all_ts w) ==> t IN S)
           ==> v_inv_ck ck conf w refs2 (x,f,tf2,heap2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["T";"TS";"H";"R1";"R2";"R3"] (CONJUNCTS th))) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `ck:num` THEN DISCH_THEN(LABEL_TAC "IH") THEN
  SUBGOAL_THEN
   `~(ck = 0) ==>
    !w (x:(A word_loc)heap_address).
      v_inv_ck (ck - 1) conf w refs (x,f,tf,heap) /\
      (!t. MEM t (v_all_ts w) ==> t IN S)
      ==> v_inv_ck (ck - 1) conf w refs2 (x,f,tf2,heap2)`
  (LABEL_TAC "IHS") THENL
   [DISCH_TAC THEN REMOVE_THEN "IH" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REMOVE_THEN "IH" (K ALL_TAC)] THEN
  X_GEN_TAC `w:data_v` THEN
  STRUCT_CASES_TAC (ISPEC `w:data_v` (CONJUNCT1 (cases "data_v"))) THEN
  X_GEN_TAC `x:(A word_loc)heap_address` THEN
  REWRITE_TAC[MP2AUX_v_inv_ck_thms; v_all_ts_def; MEM] THENL
   [(* Number *)
    COND_CASES_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `ptr:num` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "H" MATCH_MP_TAC THEN ASM_REWRITE_TAC[MP2AUX_heap_el_facts];
    (* Word64 *)
    STRIP_TAC THEN
    EXISTS_TAC `ptr:num` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "H" MATCH_MP_TAC THEN ASM_REWRITE_TAC[MP2AUX_heap_el_facts];
    (* Block *)
    COND_CASES_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    MAP_EVERY EXISTS_TAC [`ptr:num`; `xs:((A word_loc)heap_address)list`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC MP2AUX_ALL2_MEM_IMP THEN
      EXISTS_TAC `\v (x:(A word_loc)heap_address).
                    v_inv_ck (ck - 1) conf v refs (x,f,tf,heap)` THEN
      ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
      USE_THEN "IHS" (fun th -> MATCH_MP_TAC (MP th (ASSUME `~(ck = 0)`))) THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[MEM_FLAT; MEM_MAP] THEN
      ASM_MESON_TAC[];
      USE_THEN "T" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      USE_THEN "H" MATCH_MP_TAC THEN ASM_REWRITE_TAC[MP2AUX_heap_el_facts] THEN
      ASM_MESON_TAC[]];
    (* RefPtr *)
    STRIP_TAC THENL
     [DISJ1_TAC THEN USE_THEN "R1" (MP_TAC o SPEC `a1:num`) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[];
      DISJ2_TAC THEN DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`ev:thunk_mode`; `v:data_v`;
                            `y:(A word_loc)heap_address`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [USE_THEN "R2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[];
        USE_THEN "H" MATCH_MP_TAC THEN ASM_REWRITE_TAC[MP2AUX_heap_el_facts];
        DISCH_TAC THEN
        USE_THEN "IHS" (fun th -> MATCH_MP_TAC (MP th (ASSUME `~(ck = 0)`))) THEN
        ASM_MESON_TAC[]];
      DISJ2_TAC THEN DISJ2_TAC THEN EXISTS_TAC `v:data_v` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [USE_THEN "R2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[];
        DISCH_TAC THEN
        USE_THEN "IHS" (fun th -> MATCH_MP_TAC (MP th (ASSUME `~(ck = 0)`))) THEN
        ASM_MESON_TAC[]]]]);;

(* MP2AUX: v_inv from v_inv_ck at every clock, for the transfer lemma *)
let MP2AUX_TRANSFER_TAC refs2 tf2 heap2 s =
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `refs:(data_v bvl_ref)spt`; refs2;
                 `f:(num,num)fmap`; `tf:(num,num)fmap`; tf2;
                 `heap:(((A)word_loc,data_to_word_memoryProof_tag#
                         ((A)word_loc)list)heap_element)list`; heap2; s]
                MP2AUX_v_inv_ck_transfer) THEN
  ANTS_TAC;;

(* HOL4 line 2928 *)
let v_inv_tf_update_thm_lemma = prove
 (`!conf ck v refs (y:(A word_loc)heap_address) f tf heap ts' a.
     v_inv conf v refs (y,f,tf,heap) /\
     ~(ts' IN FDOM tf) ==>
     v_inv_ck ck conf v refs (y,f,tf |+ (ts',a),heap)`,
  MP2AUX_TRANSFER_TAC `refs:(data_v bvl_ref)spt` `tf |+ (ts':num,a:num)`
    `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list` `UNIV:num->bool` THENL
   [REWRITE_TAC[IN_UNIV; FLOOKUP_UPDATE] THEN
    REPEAT CONJ_TAC THEN TRY(MESON_TAC[]) THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[FLOOKUP_DEF; distinctness "option"];
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[v_inv_eq; IN_UNIV]]);;

(* HOL4 line 2949 *)
let v_inv_tf_update_thm = prove
 (`!conf v refs (y:(A word_loc)heap_address) f tf heap ts' a.
     v_inv conf v refs (y,f,tf,heap) /\ ~(ts' IN FDOM tf) ==>
     v_inv conf v refs (y,f,tf |+ (ts',a),heap)`,
  MESON_TAC[v_inv_eq; v_inv_tf_update_thm_lemma]);;

(* MP2AUX: the time stamps of the contents of the thunks are in all_ts *)
let MP2AUX_thunk_ts_all_ts = prove
 (`!refs stack n ev v t.
     lookup n refs = SOME (bvl_Thunk ev v) /\ MEM t (v_all_ts v)
     ==> t IN all_ts refs stack`,
  REWRITE_TAC[all_ts_def; LET_DEF; LET_END_DEF; IN_ELIM_THM] THEN
  MESON_TAC[find_ref_def]);;

(* HOL4 line 2957 *)
let v_inv_tf_update_thm_alt_lemma = prove
 (`!conf stack ck v refs (y:(A word_loc)heap_address) f tf heap ts' a.
     v_inv conf v refs (y,f,tf,heap) /\
     ~(ts' IN all_ts refs stack) /\
     ~(ts' IN set_of_list (v_all_ts v)) ==>
     v_inv_ck ck conf v refs (y,f,tf |+ (ts',a),heap)`,
  MP2AUX_TRANSFER_TAC `refs:(data_v bvl_ref)spt` `tf |+ (ts':num,a:num)`
    `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list` `{t:num | ~(t = ts')}` THENL
   [REWRITE_TAC[IN_ELIM_THM; FLOOKUP_UPDATE] THEN
    REPEAT CONJ_TAC THEN TRY(MESON_TAC[]) THEN
    ASM_MESON_TAC[MP2AUX_thunk_ts_all_ts];
    DISCH_THEN MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_SET_OF_LIST]) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[v_inv_eq]]);;

(* HOL4 line 2991 *)
let v_inv_tf_update_thm_alt = prove
 (`!conf v refs (y:(A word_loc)heap_address) f tf heap ts' a stack.
     v_inv conf v refs (y,f,tf,heap) /\
     ~(ts' IN all_ts refs stack) /\
     ~(ts' IN set_of_list (v_all_ts v)) ==>
     v_inv conf v refs (y,f,tf |+ (ts',a),heap)`,
  MESON_TAC[v_inv_eq; v_inv_tf_update_thm_alt_lemma]);;

(* HOL4 line 3001 *)
let v_inv_tf_update_lemma = prove
 (`!conf stack ts' a ck v1 refs
    (v2:(A word_loc)heap_address#(num,num)fmap#(num,num)fmap#
        ((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)heap_element)
        list).
     v_inv conf v1 refs v2 ==>
     !ts tag xs y f tf heap.
       v1 = data_Block ts tag xs /\
       v2 = (y,f,tf,heap) /\
       v1 IN all_vs refs stack /\
       ~(ts' IN all_ts refs stack) ==>
       v_inv_ck ck conf v1 refs (y,f,tf |+ (ts',a),heap)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC v_inv_tf_update_thm_alt_lemma THEN
  EXISTS_TAC `stack:data_v list` THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[IN_SET_OF_LIST] THEN
  ASM_MESON_TAC[MEM_in_all_ts]);;

(* HOL4 line 3070 *)
let v_inv_tf_update = prove
 (`!conf refs (y:(A word_loc)heap_address) f tf heap
    (heap1:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
            heap_element)list) a stack ts ts' tag xs.
     data_Block ts tag xs IN all_vs refs stack /\
     ~(ts' IN all_ts refs stack) /\
     v_inv conf (data_Block ts tag xs) refs (y,f,tf,heap)
     ==> v_inv conf (data_Block ts tag xs) refs (y,f,tf |+ (ts',a),heap)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[v_inv_eq] THEN GEN_TAC THEN
  MATCH_MP_TAC v_inv_tf_update_thm_alt_lemma THEN
  EXISTS_TAC `stack:data_v list` THEN ASM_REWRITE_TAC[IN_SET_OF_LIST] THEN
  ASM_MESON_TAC[MEM_in_all_ts]);;

(* HOL4 line 3080 *)
let v_inv_tf_restrict_lemma = prove
 (`!conf stack P ck v1 refs (y:(A word_loc)heap_address) f tf heap.
     v_inv conf v1 refs (y,f,tf,heap) ==>
     (!x. MEM x (v_all_ts v1) ==> x IN P) /\
     (!x. x IN all_ts refs stack ==> x IN P) ==>
     v_inv_ck ck conf v1 refs (y,f,DRESTRICT tf P,heap)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_IMP] THEN
  MP2AUX_TRANSFER_TAC `refs:(data_v bvl_ref)spt` `DRESTRICT (tf:(num,num)fmap) (P:num->bool)`
    `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list` `P:num->bool` THENL
   [REWRITE_TAC[FLOOKUP_DRESTRICT] THEN
    REPEAT CONJ_TAC THEN TRY(MESON_TAC[]) THEN
    ASM_MESON_TAC[MP2AUX_thunk_ts_all_ts];
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[v_inv_eq]]);;

(* HOL4 line 3126 *)
let v_inv_tf_restrict = prove
 (`!conf v refs stack (y:(A word_loc)heap_address) f tf heap P.
     v_inv conf v refs (y,f,tf,heap) /\
     (!x. MEM x (v_all_ts v) ==> x IN P) /\
     (!x. x IN all_ts refs stack ==> x IN P) ==>
     v_inv conf v refs (y,f,DRESTRICT tf P,heap)`,
  MESON_TAC[v_inv_eq; v_inv_tf_restrict_lemma]);;

(* HOL4 line 3136 *)
let v_all_vs_append = prove
 (`!x y. v_all_vs (APPEND x y) = APPEND (v_all_vs x) (v_all_vs y)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; v_all_vs_def] THEN
  CASES_ON `h:data_v` THEN ASM_REWRITE_TAC[APPEND; v_all_vs_def; APPEND_ASSOC]);;

(* MP2AUX: v_all_vs of a cons *)
let MP2AUX_v_all_vs_CONS = prove
 (`!v xs. v_all_vs (CONS v xs) = APPEND (v_all_vs [v]) (v_all_vs xs)`,
  GEN_TAC THEN CASES_ON `v:data_v` THEN
  REWRITE_TAC[v_all_vs_def; APPEND; APPEND_NIL]);;

(* HOL4 line 3143 *)
let MEM_v_all_vs_split = prove
 (`!x v xs.
     MEM x (v_all_vs (CONS v xs)) ==> MEM x (v_all_vs [v]) \/ MEM x (v_all_vs xs)`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(ISPECL [`v:data_v`; `xs:data_v list`] MP2AUX_v_all_vs_CONS) THEN
  REWRITE_TAC[MEM_APPEND]);;

(* HOL4 line 3151 *)
let MEM_v_all_vs_split2 = prove
 (`!x v y xs.
     MEM x (v_all_vs (CONS v (CONS y xs))) ==>
     MEM x (v_all_vs (CONS v xs)) \/ MEM x (v_all_vs [y])`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(ISPECL [`v:data_v`; `CONS (y:data_v) xs`] MP2AUX_v_all_vs_CONS) THEN
  SUBST1_TAC(ISPECL [`y:data_v`; `xs:data_v list`] MP2AUX_v_all_vs_CONS) THEN
  SUBST1_TAC(ISPECL [`v:data_v`; `xs:data_v list`] MP2AUX_v_all_vs_CONS) THEN
  REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[]);;

(* HOL4 line 3163 *)
let MEM_v_all_vs_extend_tl = prove
 (`!x v xs. MEM x (v_all_vs [v]) ==> MEM x (v_all_vs (CONS v xs))`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(ISPECL [`v:data_v`; `xs:data_v list`] MP2AUX_v_all_vs_CONS) THEN
  REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[]);;

(* HOL4 line 3171 *)
let MEM_v_all_vs_extend_hd = prove
 (`!x v xs. MEM x (v_all_vs xs) ==> MEM x (v_all_vs (CONS v xs))`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(ISPECL [`v:data_v`; `xs:data_v list`] MP2AUX_v_all_vs_CONS) THEN
  REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[]);;

(* HOL4 line 3179 *)
let MEM_v_all_vs_extend_append = prove
 (`!x xs ys. MEM x (v_all_vs xs) ==> MEM x (v_all_vs (APPEND xs ys))`,
  REWRITE_TAC[v_all_vs_append; MEM_APPEND] THEN MESON_TAC[]);;

(* HOL4 line 3185 *)
let MEM_v_all_vs_EL = prove
 (`!xs i x.
     i < LENGTH xs /\ MEM x (v_all_vs [EL i xs]) ==> MEM x (v_all_vs xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; LT_SUC; LT_0] THENL
   [MESON_TAC[MEM_v_all_vs_extend_tl];
    ASM_MESON_TAC[MEM_v_all_vs_extend_hd]]);;

(* HOL4 line 3201 *)
let MEM_v_all_vs_LUPDATE = prove
 (`!xs i v x.
     MEM x (v_all_vs (LUPDATE v i xs)) ==>
     MEM x (v_all_vs [v]) \/ MEM x (v_all_vs xs)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LUPDATE_def; v_all_vs_def; MEM] THEN
  INDUCT_TAC THEN REWRITE_TAC[LUPDATE_def] THEN
  ASM_MESON_TAC[MEM_v_all_vs_split; MEM_v_all_vs_extend_tl;
                MEM_v_all_vs_extend_hd]);;

(* HOL4 line 3215 *)
let all_vs_Block = prove
 (`!refs t tag xs ys.
     all_vs refs (CONS (data_Block t tag xs) ys) =
     data_Block t tag xs INSERT all_vs refs (APPEND xs ys)`,
  REWRITE_TAC[all_vs_def; v_all_vs_def; v_all_vs_append; EXTENSION; IN_UNION;
              IN_INSERT; IN_ELIM_THM; MEM; MEM_APPEND] THEN
  MESON_TAC[]);;

(* HOL4 line 3224 *)
let blocks_unique_cons_thm = prove
 (`!ts s tag xs.
     blocks_unique ts s ==>
     blocks_unique (ts + 1) (data_Block ts tag xs INSERT s)`,
  REWRITE_TAC[blocks_unique_def; IN_INSERT; injectivity "data_v"] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[LT_REFL; ARITH_RULE `n < m ==> n < m + 1`;
                ARITH_RULE `m < m + 1`]);;

(* MP2AUX: allocation of a data element that is not a ref in the unused  *)
(* space at a keeps heap_ok, gc_kind_inv and unused_space_inv            *)
let MP2AUX_alloc_lemma = prove
 (`!conf a sp sp1 gens limit
    (heap:((A,data_to_word_memoryProof_tag#B)heap_element)list) x.
     heap_ok heap limit /\ gc_kind_inv conf a sp sp1 gens heap /\
     unused_space_inv a (sp + sp1) heap /\ el_length x <= sp /\
     isDataElement x /\ ~isRef x /\
     (!xs l d ptr (u:A). x = DataElement xs l d /\ MEM (Pointer ptr u) xs ==>
                         isSomeDataElement (heap_lookup ptr heap))
     ==> ?heap2. heap_store_unused_alt a (sp + sp1) x heap = (heap2,T) /\
           heap_ok heap2 limit /\
           gc_kind_inv conf (a + el_length x) (sp - el_length x) sp1 gens heap2 /\
           unused_space_inv (a + el_length x) ((sp - el_length x) + sp1) heap2 /\
           heap_store_rel heap heap2 /\ heap_lookup a heap2 = SOME x /\
           ~isSomeDataElement (heap_lookup a heap) /\
           (!p. isSomeDataElement (heap_lookup p heap2) <=>
                p = a \/ isSomeDataElement (heap_lookup p heap))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:num`; `sp + sp1:num`;
                 `heap:((A,data_to_word_memoryProof_tag#B)heap_element)list`;
                 `x:(A,data_to_word_memoryProof_tag#B)heap_element`]
                IMP_heap_store_unused_alt) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `heap2:((A,data_to_word_memoryProof_tag#B)heap_element)list`
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `heap2:((A,data_to_word_memoryProof_tag#B)heap_element)list` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(sp + sp1) - el_length (x:(A,data_to_word_memoryProof_tag#B)heap_element) =
                (sp - el_length x) + sp1` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                                                  ASSUME_TAC th) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* heap_ok *)
    UNDISCH_TAC `heap_ok (heap:((A,data_to_word_memoryProof_tag#B)heap_element)list) limit` THEN
    REWRITE_TAC[heap_ok_def] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~isForwardPointer (x:(A,data_to_word_memoryProof_tag#B)heap_element)`
      ASSUME_TAC THENL
     [UNDISCH_TAC `isDataElement (x:(A,data_to_word_memoryProof_tag#B)heap_element)` THEN
      REWRITE_TAC[isDataElement_def] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[isForwardPointer_def];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `heap_store_rel (heap:((A,data_to_word_memoryProof_tag#B)heap_element)list)
                   heap2` THEN
    REWRITE_TAC[heap_store_rel_def] THEN ASM_MESON_TAC[];
    (* gc_kind_inv *)
    UNDISCH_TAC `gc_kind_inv conf a sp sp1 gens
                   (heap:((A,data_to_word_memoryProof_tag#B)heap_element)list)` THEN
    REWRITE_TAC[gc_kind_inv_def] THEN
    CASES_ON `data_to_word_config_gc_kind conf` THEN CASE_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(a + el_length (x:(A,data_to_word_memoryProof_tag#B)heap_element)) +
                  (sp - el_length x) + sp1 = a + sp + sp1` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC heap_store_unused_alt_gen_state_ok THEN
      EXISTS_TAC `heap:((A,data_to_word_memoryProof_tag#B)heap_element)list` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`a:num`; `sp + sp1:num`;
                   `heap:((A,data_to_word_memoryProof_tag#B)heap_element)list`;
                   `h1:((A,data_to_word_memoryProof_tag#B)heap_element)list`;
                   `h2:((A,data_to_word_memoryProof_tag#B)heap_element)list`;
                   `heap2:((A,data_to_word_memoryProof_tag#B)heap_element)list`;
                   `x:(A,data_to_word_memoryProof_tag#B)heap_element`]
                  heap_store_unused_alt_thm) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `h0:((A,data_to_word_memoryProof_tag#B)heap_element)list`
      STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC
     [`APPEND (APPEND h0 [x:(A,data_to_word_memoryProof_tag#B)heap_element])
              (heap_expand (sp - el_length x + sp1))`;
      `h2:((A,data_to_word_memoryProof_tag#B)heap_element)list`] THEN
    SUBGOAL_THEN `a + sp + sp1 =
      heap_length (APPEND (APPEND h0 [x:(A,data_to_word_memoryProof_tag#B)heap_element])
                          (heap_expand (sp - el_length x + sp1)))` SUBST1_TAC THENL
     [REWRITE_TAC[heap_length_APPEND; gc_shared_heap_length_heap_expand] THEN
      ASM_REWRITE_TAC[heap_length_def; MAP; SUM] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[heap_split_length] THEN
    UNDISCH_TAC `ALL (\x. ~isRef x)
                   (h1:((A,data_to_word_memoryProof_tag#B)heap_element)list)` THEN
    ASM_REWRITE_TAC[ALL_APPEND; ALL; heap_expand_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[ALL; isRef_def];
    (* the data elements *)
    GEN_TAC THEN
    UNDISCH_TAC `{a | isSomeDataElement (heap_lookup a
                   (heap2:((A,data_to_word_memoryProof_tag#B)heap_element)list))} =
                 a INSERT {a | isSomeDataElement
                   (heap_lookup a (heap:((A,data_to_word_memoryProof_tag#B)heap_element)list))}` THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN MESON_TAC[]]);;

(* MP2AUX: bc_ref_inv of a ref is kept by a new state that keeps the       *)
(* ref, its address, its heap cell and the v_inv of its contents          *)
let MP2AUX_bc_ref_inv_transfer = prove
 (`!conf n (refs:(data_v bvl_ref)spt) refs2 f tf
    (heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list) be f2 tf2 heap2.
     bc_ref_inv conf n refs (f,tf,heap,be) /\
     lookup n refs2 = lookup n refs /\
     FLOOKUP f2 n = FLOOKUP f n /\
     (!x ys l d. FLOOKUP f n = SOME x /\
                 heap_lookup x heap = SOME (DataElement ys l d) ==>
                 heap_lookup x heap2 = SOME (DataElement ys l d)) /\
     (!r v (z:(A word_loc)heap_address).
        lookup n refs = SOME r /\ find_ref r v /\ v_inv conf v refs (z,f,tf,heap)
        ==> v_inv conf v refs2 (z,f2,tf2,heap2)) /\
     (!ev v. lookup n refs = SOME (bvl_Thunk ev v) /\
             data_dest_thunk v refs = data_NotThunk ==>
             data_dest_thunk v refs2 = data_NotThunk) /\
     (!x. FLOOKUP f n = SOME x /\ ~(x IN IMAGE (FAPPLY tf) (FDOM tf)) ==>
          ~(x IN IMAGE (FAPPLY tf2) (FDOM tf2)))
     ==> bc_ref_inv conf n refs2 (f2,tf2,heap2,be)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `bc_ref_inv conf n refs (f,tf,heap:(((A)word_loc,
    data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list,be)` THEN
  REWRITE_TAC[bc_ref_inv_def] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `FLOOKUP (f:(num,num)fmap) n` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[])
    (X_CHOOSE_THEN `x:num` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
      REWRITE_TAC[th] THEN ASSUME_TAC th))) THEN
  CASE_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `lookup n (refs:(data_v bvl_ref)spt)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th] THEN CASE_REWRITE_TAC[])
    (X_CHOOSE_THEN `r:data_v bvl_ref` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
      REWRITE_TAC[th] THEN ASSUME_TAC th))) THEN
  CASE_REWRITE_TAC[] THEN
  CASES_ON `r:data_v bvl_ref` THEN CASE_REWRITE_TAC[] THENL
   [STRIP_TAC THEN EXISTS_TAC `zs:((A word_loc)heap_address)list` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RefBlock_def];
      UNDISCH_TAC `ALL2 (\z y. v_inv conf y refs (z,f,tf,
        heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
              heap_element)list)) zs a` THEN
      MATCH_MP_TAC EVERY2_IMP_EVERY2 THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `bvl_ValueArray a:data_v bvl_ref` THEN
      ASM_REWRITE_TAC[find_ref_def]];
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN ASM_MESON_TAC[MP1AUX_Bytes_nil];
    STRIP_TAC THEN EXISTS_TAC `z:(A word_loc)heap_address` THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[ThunkBlock_def];
      ASM_MESON_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        try fst(dest_const(fst(strip_comb(rand(snd(strip_forall(concl th))))))) =
            "v_inv"
        with Failure _ -> false)) THEN
      EXISTS_TAC `bvl_Thunk a0 a1:data_v bvl_ref` THEN
      ASM_REWRITE_TAC[find_ref_def]];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      EXISTS_TAC `zs:((A word_loc)heap_address)list` THEN CONJ_TAC THENL
       [ASM_MESON_TAC[BlockRep_def];
        UNDISCH_TAC `ALL2 (\z y. v_inv conf y refs (z,f,tf,
          heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                heap_element)list)) zs (APPEND (APPEND a2 [a3]) a4)` THEN
        MATCH_MP_TAC EVERY2_IMP_EVERY2 THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        EXISTS_TAC `MutBlock a0 a1 a2 a3 a4:data_v bvl_ref` THEN
        ASM_REWRITE_TAC[find_ref_def]]]]);;

(* MP2AUX: the refs reachable from a block are reachable from its payload *)
let MP2AUX_reachable_refs_Block = prove
 (`!ts tag xs stack refs n.
     reachable_refs (CONS (data_Block ts tag xs) stack) refs n ==>
     reachable_refs (APPEND xs stack) refs n`,
  REWRITE_TAC[reachable_refs_def; MEM; MEM_APPEND] THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[get_refs_def; MEM_FLAT; MEM_MAP]) THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* HOL4 line 3234 *)
let cons_thm_alt = prove
 (`!conf xs stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts tag.
     abs_ml_inv conf (APPEND xs stack) refs (roots,heap,be,a,sp,sp1,gens) limit ts /\
     LENGTH xs < sp /\ ~(xs = []) ==>
     ?rs roots2 heap2.
       roots = APPEND rs roots2 /\ LENGTH rs = LENGTH xs /\
       heap_store_unused_alt a (sp + sp1) (BlockRep tag rs) heap = (heap2,T) /\
       abs_ml_inv conf
         (CONS (data_Block ts tag xs) stack) refs
         (CONS (Pointer a (wl_Word (ptr_bits conf tag (LENGTH xs)))) roots2,
          heap2,be,
          a + el_length (BlockRep tag rs:(A word_loc,data_to_word_memoryProof_tag#
                                          (A word_loc)list)heap_element),
          sp - el_length (BlockRep tag rs:(A word_loc,data_to_word_memoryProof_tag#
                                           (A word_loc)list)heap_element),
          sp1,gens) limit (ts + 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP EVERY2_APPEND_IMP_APPEND) THEN
  DISCH_THEN(X_CHOOSE_THEN `rs:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `roots2:((A word_loc)heap_address)list` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`rs:((A word_loc)heap_address)list`;
                        `roots2:((A word_loc)heap_address)list`] THEN
  SUBGOAL_THEN `LENGTH (rs:((A word_loc)heap_address)list) = LENGTH (xs:data_v list)`
    ASSUME_TAC THENL [ASM_MESON_TAC[EVERY2_LENGTH]; ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `a:num`; `sp:num`; `sp1:num`;
                 `gens:gen_state`; `limit:num`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element)list`;
                 `BlockRep tag rs:(A word_loc,data_to_word_memoryProof_tag#
                                   (A word_loc)list)heap_element`]
                MP2AUX_alloc_lemma) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[BlockRep_def; el_length_def; isDataElement_def; isRef_def;
                    isMutTag_def; distinctness "data_to_word_memoryProof_tag";
                    injectivity "heap_element"] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `roots_ok (roots:((A word_loc)heap_address)list)
      (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
             heap_element)list)` THEN
    ASM_REWRITE_TAC[roots_ok_def; MEM_APPEND] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `heap2:((A word_loc,data_to_word_memoryProof_tag#
                                    (A word_loc)list)heap_element)list`
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `heap2:((A word_loc,data_to_word_memoryProof_tag#
                      (A word_loc)list)heap_element)list` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(ts IN FDOM (tf:(num,num)fmap))` ASSUME_TAC THENL
   [UNDISCH_TAC `FDOM (tf:(num,num)fmap) SUBSET {n | n < ts}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v (z:(A word_loc)heap_address).
      v_inv conf v refs (z,f,tf,heap) ==>
      v_inv conf v refs (z,f,tf |+ (ts,a),heap2)`
  (LABEL_TAC "VT") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC v_inv_tf_update_thm THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC heap_store_rel_v_inv THEN
    EXISTS_TAC `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                      heap_element)list` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `roots_ok (roots:((A word_loc)heap_address)list)
      (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
             heap_element)list)` THEN
    ASM_REWRITE_TAC[roots_ok_def; MEM; MEM_APPEND; injectivity "heap_address"] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf |+ (ts:num,a:num)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `INJ (FAPPLY (f:(num,num)fmap)) (FDOM f)
      {a | isSomeDataElement (heap_lookup a
        (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
               heap_element)list))}` THEN
    REWRITE_TAC[INJ; IN_ELIM_THM] THEN MESON_TAC[];
    UNDISCH_TAC `INJ (FAPPLY (tf:(num,num)fmap)) (FDOM tf)
      {a | isSomeDataElement (heap_lookup a
        (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
               heap_element)list))}` THEN
    REWRITE_TAC[INJ; IN_ELIM_THM; FDOM_FUPDATE; FAPPLY_FUPDATE_THM; IN_INSERT] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[FDOM_FUPDATE; all_ts_cons] THEN ASM SET_TAC[];
    REWRITE_TAC[FDOM_FUPDATE] THEN
    UNDISCH_TAC `FDOM (tf:(num,num)fmap) SUBSET {n | n < ts}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT] THEN
    MESON_TAC[ARITH_RULE `x < ts ==> x < ts + 1`; ARITH_RULE `ts < ts + 1`];
    REWRITE_TAC[all_vs_Block] THEN MATCH_MP_TAC blocks_unique_cons_thm THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[ALL2] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[v_inv_def] THEN
      MAP_EVERY EXISTS_TAC [`a:num`; `rs:((A word_loc)heap_address)list`] THEN
      ASM_REWRITE_TAC[FLOOKUP_UPDATE] THEN
      UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs (x,f,tf,
        heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
              heap_element)list)) xs rs` THEN
      MATCH_MP_TAC MONO_ALL2 THEN USE_THEN "VT" (fun th -> SIMP_TAC[th]);
      UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs (x,f,tf,
        heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
              heap_element)list)) stack roots2` THEN
      MATCH_MP_TAC MONO_ALL2 THEN USE_THEN "VT" (fun th -> SIMP_TAC[th])];
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC MP2AUX_bc_ref_inv_transfer THEN
    MAP_EVERY EXISTS_TAC [`refs:(data_v bvl_ref)spt`; `f:(num,num)fmap`;
      `tf:(num,num)fmap`;
      `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
             heap_element)list`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MP2AUX_reachable_refs_Block THEN ASM_MESON_TAC[];
      REWRITE_TAC[];
      REWRITE_TAC[];
      ASM_MESON_TAC[heap_store_rel_lemma];
      USE_THEN "VT" (fun th -> MESON_TAC[th]);
      SIMP_TAC[];
      REWRITE_TAC[FDOM_FUPDATE; FAPPLY_FUPDATE_THM; IN_IMAGE; IN_INSERT] THEN
      X_GEN_TAC `y:num` THEN STRIP_TAC THEN
      UNDISCH_TAC `INJ (FAPPLY (f:(num,num)fmap)) (FDOM f)
        {a | isSomeDataElement (heap_lookup a
          (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                 heap_element)list))}` THEN
      REWRITE_TAC[INJ; IN_ELIM_THM] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[FLOOKUP_DEF]) THEN ASM_MESON_TAC[option_INJ;
        distinctness "option"]]]);;

(* HOL4 line 3385 *)
let cons_thm_EMPTY = prove
 (`!conf stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts tag.
     abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts /\
     tag < dimword (:A) DIV 16 ==>
     abs_ml_inv conf (CONS (data_Block 0 tag []) stack) refs
       (CONS (gc_shared_Data (wl_Word (BlockNil tag))) roots,heap,be,a,sp,sp1,
        gens) limit ts`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `roots_ok (roots:((A word_loc)heap_address)list)
      (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
             heap_element)list)` THEN
    REWRITE_TAC[roots_ok_def; MEM; distinctness "heap_address"];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`] THEN
  ASM_REWRITE_TAC[all_ts_cons; APPEND; ALL2] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `FDOM (tf:(num,num)fmap) SUBSET all_ts refs stack` THEN SET_TAC[];
    UNDISCH_TAC `blocks_unique ts (all_vs (refs:(data_v bvl_ref)spt) stack)` THEN
    REWRITE_TAC[blocks_unique_def; all_vs_Block; APPEND; IN_INSERT;
                injectivity "data_v"] THEN
    MESON_TAC[];
    ASM_REWRITE_TAC[v_inv_def];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP MP2AUX_reachable_refs_Block) THEN
    REWRITE_TAC[APPEND]]);;

(* MP2AUX: blocks_unique is antimonotone in the blocks of the set *)
let MP2AUX_blocks_unique_mono = prove
 (`!ts s1 s2.
     blocks_unique ts s1 /\
     (!t a xs. data_Block t a xs IN s2 ==> data_Block t a xs IN s1)
     ==> blocks_unique ts s2`,
  REWRITE_TAC[blocks_unique_def] THEN MESON_TAC[]);;

(* HOL4 line 3411 *)
let blocks_unique_Word64 = prove
 (`!ts refs ws stack w64.
     blocks_unique ts (all_vs refs (APPEND ws stack)) ==>
     blocks_unique ts (all_vs refs (CONS (data_Word64 w64) stack))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MP2AUX_blocks_unique_mono THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM; v_all_vs_def; v_all_vs_append;
              MEM; MEM_APPEND; distinctness "data_v"] THEN
  MESON_TAC[]);;

(* MP2AUX: the time stamps of the contents of the refs are in all_ts *)
let MP2AUX_find_ref_all_ts = prove
 (`!refs stack n r v t.
     lookup n refs = SOME r /\ find_ref r v /\ MEM t (v_all_ts v)
     ==> t IN all_ts refs stack`,
  REWRITE_TAC[all_ts_def; LET_DEF; LET_END_DEF; IN_ELIM_THM] THEN MESON_TAC[]);;

(* MP2AUX: the time stamps of the values of the stack are in all_ts *)
let MP2AUX_stack_all_ts = prove
 (`!refs stack v t. MEM v stack /\ MEM t (v_all_ts v) ==> t IN all_ts refs stack`,
  REWRITE_TAC[all_ts_def; LET_DEF; LET_END_DEF; IN_ELIM_THM] THEN MESON_TAC[]);;

(* MP2AUX: a value without time stamps adds none to all_ts *)
let MP2AUX_all_ts_cons_no_ts = prove
 (`!refs stack v. v_all_ts v = [] ==> all_ts refs (CONS v stack) = all_ts refs stack`,
  REWRITE_TAC[all_ts_def; LET_DEF; LET_END_DEF; EXTENSION; IN_ELIM_THM; MEM] THEN
  MESON_TAC[MEM]);;

(* MP2AUX: a value without refs adds no reachable refs *)
let MP2AUX_reachable_refs_no_refs = prove
 (`!v stack ws refs n.
     get_refs v = [] /\ reachable_refs (CONS v stack) refs n ==>
     reachable_refs (APPEND ws stack) refs n`,
  REWRITE_TAC[reachable_refs_def; MEM; MEM_APPEND] THEN MESON_TAC[MEM]);;

(* MP2AUX: allocating a non-block value (a Word64 or a bignum) stored in a *)
(* data element without pointers                                          *)
let MP2AUX_alloc_value = prove
 (`!conf ws stack refs rs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts x v.
     abs_ml_inv conf (APPEND ws stack) refs
       (APPEND rs roots,heap,be,a,sp,sp1,gens) limit ts /\
     LENGTH ws = LENGTH rs /\
     (?len tag xs. x = DataElement [] len (tag,xs) /\ ~isMutTag tag) /\
     el_length x <= sp /\
     v_all_ts v = [] /\ v_all_vs [v] = [v] /\ get_refs v = [] /\
     (!f tf heap2. heap_lookup a heap2 = SOME x ==>
                   v_inv conf v refs (Pointer a (wl_Word (word 0)),f,tf,heap2))
     ==> ?heap2. heap_store_unused_alt a (sp + sp1) x heap = (heap2,T) /\
           abs_ml_inv conf (CONS v stack) refs
             (CONS (Pointer a (wl_Word (word 0))) roots,heap2,be,
              a + el_length x,sp - el_length x,sp1,gens) limit ts`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `a:num`; `sp:num`; `sp1:num`;
                 `gens:gen_state`; `limit:num`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element)list`;
                 `x:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                    heap_element`] MP2AUX_alloc_lemma) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[isDataElement_def; isRef_def; injectivity "heap_element"; MEM] THEN
    SIMP[MEM];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `heap2:((A word_loc,data_to_word_memoryProof_tag#
                                    (A word_loc)list)heap_element)list`
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `heap2:((A word_loc,data_to_word_memoryProof_tag#
                      (A word_loc)list)heap_element)list` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs (x,f,tf,
      heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
            heap_element)list)) (APPEND ws stack) (APPEND rs roots)` THEN
  ASM_SIMP_TAC[LIST_REL_APPEND_EQ] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `roots_ok (APPEND rs roots:((A word_loc)heap_address)list)
      (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
             heap_element)list)` THEN
    ASM_REWRITE_TAC[roots_ok_def; MEM; MEM_APPEND; injectivity "heap_address"] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `tf2 = DRESTRICT (tf:(num,num)fmap) (all_ts (refs:(data_v bvl_ref)spt) stack)` THEN
  SUBGOAL_THEN
   `!w (z:(A word_loc)heap_address).
      v_inv conf w refs (z,f,tf,heap) /\
      (!t. MEM t (v_all_ts w) ==> t IN all_ts refs stack) ==>
      v_inv conf w refs (z,f,tf2,heap2)`
  (LABEL_TAC "VT") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "tf2" THEN MATCH_MP_TAC v_inv_tf_restrict THEN
    EXISTS_TAC `stack:data_v list` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC heap_store_rel_v_inv THEN
    EXISTS_TAC `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                      heap_element)list` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf2:(num,num)fmap`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `INJ (FAPPLY (f:(num,num)fmap)) (FDOM f)
      {a | isSomeDataElement (heap_lookup a
        (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
               heap_element)list))}` THEN
    REWRITE_TAC[INJ; IN_ELIM_THM] THEN MESON_TAC[];
    EXPAND_TAC "tf2" THEN
    UNDISCH_TAC `INJ (FAPPLY (tf:(num,num)fmap)) (FDOM tf)
      {a | isSomeDataElement (heap_lookup a
        (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
               heap_element)list))}` THEN
    REWRITE_TAC[INJ; IN_ELIM_THM; DRESTRICT_DEF; IN_INTER] THEN MESON_TAC[];
    EXPAND_TAC "tf2" THEN ASM_SIMP_TAC[MP2AUX_all_ts_cons_no_ts; DRESTRICT_DEF] THEN
    SET_TAC[];
    EXPAND_TAC "tf2" THEN REWRITE_TAC[DRESTRICT_DEF] THEN
    UNDISCH_TAC `FDOM (tf:(num,num)fmap) SUBSET {n | n < ts}` THEN SET_TAC[];
    MATCH_MP_TAC MP2AUX_blocks_unique_mono THEN
    EXISTS_TAC `all_vs (refs:(data_v bvl_ref)spt) (APPEND ws stack)` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`t:num`; `tg:num`; `ys:data_v list`] THEN
    SUBGOAL_THEN `~(data_Block t tg ys = v)` ASSUME_TAC THENL
     [DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      UNDISCH_TAC `v_all_ts (data_Block t tg ys) = []` THEN
      REWRITE_TAC[v_all_ts_def; NOT_CONS_NIL];
      ALL_TAC] THEN
    REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN
    SUBST1_TAC(ISPECL [`v:data_v`; `stack:data_v list`] MP2AUX_v_all_vs_CONS) THEN
    ASM_REWRITE_TAC[MEM_APPEND; MEM; v_all_vs_append] THEN MESON_TAC[];
    REWRITE_TAC[ALL2] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MATCH_MP_TAC MP2AUX_ALL2_MEM_IMP THEN
      EXISTS_TAC `\v (x:(A word_loc)heap_address). v_inv conf v refs (x,f,tf,heap)` THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      USE_THEN "VT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MP2AUX_stack_all_ts]];
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC MP2AUX_bc_ref_inv_transfer THEN
    MAP_EVERY EXISTS_TAC [`refs:(data_v bvl_ref)spt`; `f:(num,num)fmap`;
      `tf:(num,num)fmap`;
      `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
             heap_element)list`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MP2AUX_reachable_refs_no_refs THEN ASM_MESON_TAC[];
      REWRITE_TAC[];
      REWRITE_TAC[];
      ASM_MESON_TAC[heap_store_rel_lemma];
      REPEAT STRIP_TAC THEN USE_THEN "VT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MP2AUX_find_ref_all_ts];
      SIMP_TAC[];
      EXPAND_TAC "tf2" THEN REWRITE_TAC[IN_IMAGE; DRESTRICT_DEF; IN_INTER] THEN
      MESON_TAC[]]]);;

(* HOL4 line 3424 *)
let word64_alt_thm = prove
 (`!conf ws stack refs rs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts w64 len xs.
     abs_ml_inv conf (APPEND ws stack) refs
       (APPEND rs roots,heap,be,a,sp,sp1,gens) limit ts /\
     LENGTH ws = LENGTH rs /\
     Word64Rep (:A) w64 = DataElement [] len (Word64Tag,xs) /\
     LENGTH xs < sp
     ==>
     ?heap2.
       heap_store_unused_alt a (sp + sp1) (Word64Rep (:A) w64) heap = (heap2,T) /\
       abs_ml_inv conf (CONS (data_Word64 w64) stack) refs
         (CONS (Pointer a (wl_Word (word 0))) roots,heap2,
          be,a + len + 1,sp - len - 1,sp1,gens) limit ts`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (xs:((A)word_loc)list) = len` ASSUME_TAC THENL
   [UNDISCH_TAC `Word64Rep (:A) w64 = DataElement [] len (Word64Tag,xs:((A)word_loc)list)` THEN
    REWRITE_TAC[Word64Rep_def] THEN COND_CASES_TAC THEN
    REWRITE_TAC[injectivity "heap_element"; PAIR_EQ] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[LENGTH] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `ws:data_v list`; `stack:data_v list`;
                 `refs:(data_v bvl_ref)spt`; `rs:((A word_loc)heap_address)list`;
                 `roots:((A word_loc)heap_address)list`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `be:bool`; `a:num`; `sp:num`; `sp1:num`; `gens:gen_state`;
                 `limit:num`; `ts:num`;
                 `Word64Rep (:A) w64`; `data_Word64 w64`] MP2AUX_alloc_value) THEN
  ASM_REWRITE_TAC[el_length_def; v_all_ts_def; v_all_vs_def; get_refs_def;
                  v_inv_def; injectivity "heap_address"] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`len:num`; `Word64Tag`; `xs:((A)word_loc)list`] THEN
      REWRITE_TAC[isMutTag_def; distinctness "data_to_word_memoryProof_tag"];
      ASM_ARITH_TAC;
      MESON_TAC[]];
    REWRITE_TAC[ARITH_RULE `sp - len - 1 = sp - (len + 1)`]]);;

(* HOL4 line 3585 *)
let blocks_unique_Number = prove
 (`!ts refs ws stack i.
     blocks_unique ts (all_vs refs (APPEND ws stack)) ==>
     blocks_unique ts (all_vs refs (CONS (data_Number i) stack))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MP2AUX_blocks_unique_mono THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM; v_all_vs_def; v_all_vs_append;
              MEM; MEM_APPEND; distinctness "data_v"] THEN
  MESON_TAC[]);;

(* HOL4 line 3598 *)
let bignum_alt_thm = prove
 (`!conf ws stack refs rs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts i len tag xs.
     abs_ml_inv conf (APPEND ws stack) refs
       (APPEND rs roots,heap,be,a,sp,sp1,gens) limit ts /\
     LENGTH ws = LENGTH rs /\ ~small_int (:A) i /\
     Bignum i:((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
              heap_element = DataElement [] len (tag,xs) /\
     LENGTH xs < sp ==>
     ?heap2.
       heap_store_unused_alt a (sp + sp1) (Bignum i) heap = (heap2,T) /\
       abs_ml_inv conf (CONS (data_Number i) stack) refs
         (CONS (Pointer a (wl_Word (word 0:A word))) roots,heap2,be,a + len + 1,
          sp - len - 1,sp1,gens) limit ts`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (xs:((A)word_loc)list) = len /\ ~isMutTag tag`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `Bignum i:((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                 heap_element = DataElement [] len (tag,xs)` THEN
    REWRITE_TAC[data_to_word_memoryProof_Bignum_def] THEN PAIRARG_TAC THEN
    REWRITE_TAC[injectivity "heap_element"; PAIR_EQ] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[LENGTH_MAP; isMutTag_def; distinctness "data_to_word_memoryProof_tag"];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `ws:data_v list`; `stack:data_v list`;
                 `refs:(data_v bvl_ref)spt`; `rs:((A word_loc)heap_address)list`;
                 `roots:((A word_loc)heap_address)list`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `be:bool`; `a:num`; `sp:num`; `sp1:num`; `gens:gen_state`;
                 `limit:num`; `ts:num`;
                 `Bignum i:((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                           heap_element`; `data_Number i`] MP2AUX_alloc_value) THEN
  ASM_REWRITE_TAC[el_length_def; v_all_ts_def; v_all_vs_def; get_refs_def;
                  v_inv_def; injectivity "heap_address"] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`len:num`; `tag:data_to_word_memoryProof_tag`;
                            `xs:((A)word_loc)list`] THEN ASM_REWRITE_TAC[];
      ASM_ARITH_TAC;
      ASM_MESON_TAC[]];
    REWRITE_TAC[ARITH_RULE `sp - len - 1 = sp - (len + 1)`]]);;

(* HOL4 line 3759 *)
let ref_edge_ValueArray = prove
 (`!ptr xs refs x y.
     ref_edge (insert ptr (bvl_ValueArray xs) refs) x y <=>
     if x = ptr then MEM y (get_refs (data_Block 0 ARB xs))
     else ref_edge refs x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ref_edge_def; lookup_insert] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 3770 *)
let ref_edge_Thunk = prove
 (`!ptr ev v refs x y.
     ref_edge (insert ptr (bvl_Thunk ev v) refs) x y <=>
     if x = ptr then MEM y (get_refs (data_Block 0 ARB [v]))
     else ref_edge refs x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ref_edge_def; lookup_insert] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* MP2AUX: a path of a relation whose new edges all end in S is a path of *)
(* the old relation, or starts again in S                                *)
let MP2AUX_RTC_redirect = prove
 (`!(R:A->A->bool) R' S.
     (!x y. R' x y ==> R x y \/ S y) ==>
     !x z. RTC R' x z ==> RTC R x z \/ ?s. S s /\ RTC R s z`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC RTC_INDUCT_R THEN
  REWRITE_TAC[RTC_REFL] THEN ASM_MESON_TAC[RTC_RULES; RTC_CASES_R]);;

(* MP2AUX: the refs reachable from the roots stay reachable when the new  *)
(* edges of a ref end in refs of the roots                               *)
let MP2AUX_reachable_refs_redirect = prove
 (`!roots refs refs2 n.
     (!x y. ref_edge refs2 x y ==>
            ref_edge refs x y \/ ?v. MEM v roots /\ MEM y (get_refs v)) /\
     reachable_refs roots refs2 n ==> reachable_refs roots refs n`,
  REWRITE_TAC[reachable_refs_def] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ref_edge refs`; `ref_edge refs2`;
                 `\y. ?v. MEM v roots /\ MEM y (get_refs v)`] MP2AUX_RTC_redirect) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`r:num`; `n:num`]) THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 3781 *)
let reachable_refs_UPDATE = prove
 (`!xs b ptr stack refs n.
     reachable_refs (APPEND xs (CONS (data_RefPtr b ptr) stack))
       (insert ptr (bvl_ValueArray xs) refs) n ==>
     reachable_refs (APPEND xs (CONS (data_RefPtr b ptr) stack)) refs n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MP2AUX_reachable_refs_redirect THEN
  EXISTS_TAC `insert ptr (bvl_ValueArray xs) (refs:(data_v bvl_ref)spt)` THEN
  ASM_REWRITE_TAC[ref_edge_ValueArray] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[get_refs_def; MEM_FLAT; MEM_MAP] THEN
  REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[]);;

(* HOL4 line 3806 *)
let reachable_refs_Thunk_UPDATE = prove
 (`!v b ptr stack ev refs n.
     reachable_refs (CONS v (CONS (data_RefPtr b ptr) stack))
       (insert ptr (bvl_Thunk ev v) refs) n ==>
     reachable_refs (CONS v (CONS (data_RefPtr b ptr) stack)) refs n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MP2AUX_reachable_refs_redirect THEN
  EXISTS_TAC `insert ptr (bvl_Thunk ev v) (refs:(data_v bvl_ref)spt)` THEN
  ASM_REWRITE_TAC[ref_edge_Thunk] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[get_refs_def; MEM_FLAT; MEM_MAP] THEN
  REWRITE_TAC[MEM] THEN MESON_TAC[]);;

(* MP2AUX: the edges of a value array ref *)
let MP2AUX_ref_edge_ValueArray_lookup = prove
 (`!refs ptr xs2 y.
     lookup ptr refs = SOME (bvl_ValueArray xs2) ==>
     (ref_edge refs ptr y <=> ?v. MEM v xs2 /\ MEM y (get_refs v))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ref_edge_def] THEN CASE_REWRITE_TAC[] THEN
  REWRITE_TAC[get_refs_def; MEM_FLAT; MEM_MAP] THEN MESON_TAC[]);;

(* HOL4 line 3831 *)
let reachable_refs_UPDATE1 = prove
 (`!xs b ptr stack xs1 refs n.
     reachable_refs (APPEND xs (CONS (data_RefPtr b ptr) stack))
       (insert ptr (bvl_ValueArray xs1) refs) n ==>
     (!v. MEM v xs1 ==> ~MEM v xs ==>
          ?xs2. lookup ptr refs = SOME (bvl_ValueArray xs2) /\ MEM v xs2) ==>
     reachable_refs (APPEND xs (CONS (data_RefPtr b ptr) stack)) refs n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MP2AUX_reachable_refs_redirect THEN
  EXISTS_TAC `insert ptr (bvl_ValueArray xs1) (refs:(data_v bvl_ref)spt)` THEN
  ASM_REWRITE_TAC[ref_edge_ValueArray] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[get_refs_def; MEM_FLAT; MEM_MAP; MEM_APPEND] THEN
  ASM_MESON_TAC[MP2AUX_ref_edge_ValueArray_lookup]);;

(* MP2AUX: when dest_thunk is NotThunk *)
let MP2AUX_dest_thunk_NotThunk = prove
 (`!v (refs:(data_v bvl_ref)spt).
     data_dest_thunk v refs = data_NotThunk <=>
     !b p. v = data_RefPtr b p ==>
           ?r. lookup p refs = SOME r /\ !ev w. ~(r = bvl_Thunk ev w)`,
  GEN_TAC THEN CASES_ON `v:data_v` THEN
  REWRITE_TAC[data_dest_thunk_def; distinctness "data_v"; injectivity "data_v"] THEN
  GEN_TAC THEN SIMP[] THEN EVERY_CASE_TAC THEN
  ASM_REWRITE_TAC[distinctness "data_dest_thunk_ret"; distinctness "option";
                  option_INJ; distinctness "bvl_ref"; injectivity "bvl_ref"] THEN
  SIMP[distinctness "bvl_ref"; injectivity "bvl_ref"] THEN MESON_TAC[]);;

(* MP2AUX: inserting a ref that is not a thunk keeps NotThunk *)
let MP2AUX_dest_thunk_insert = prove
 (`!v (refs:(data_v bvl_ref)spt) ptr x.
     data_dest_thunk v refs = data_NotThunk /\ (!ev w. ~(x = bvl_Thunk ev w))
     ==> data_dest_thunk v (insert ptr x refs) = data_NotThunk`,
  REWRITE_TAC[MP2AUX_dest_thunk_NotThunk; lookup_insert] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* MP2AUX: v_inv_ck after inserting a ref that is not a thunk, at a place *)
(* that holds no thunk and, if f knows it, looks the same to v_inv        *)
let MP2AUX_v_inv_ck_insert = prove
 (`!conf (refs:(data_v bvl_ref)spt) ptr r f tf
    (heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list) ck w (x:(A word_loc)heap_address).
     (!ev v. ~(r = bvl_Thunk ev v)) /\
     (!ev v. ~(lookup ptr refs = SOME (bvl_Thunk ev v))) /\
     (ptr IN FDOM f ==>
      ref_ptr_annot conf (SOME r) =
        (ref_ptr_annot conf (lookup ptr refs):(A)word_loc) /\
      (!tg fin l c rr. r = MutBlock tg fin l c rr ==>
         ?tg' fin' l' c' r'. lookup ptr refs = SOME (MutBlock tg' fin' l' c' r'))) /\
     v_inv_ck ck conf w refs (x,f,tf,heap)
     ==> v_inv_ck ck conf w (insert ptr r refs) (x,f,tf,heap)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `refs:(data_v bvl_ref)spt`;
                 `insert ptr r (refs:(data_v bvl_ref)spt)`; `f:(num,num)fmap`;
                 `tf:(num,num)fmap`; `tf:(num,num)fmap`;
                 `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                        heap_element)list`;
                 `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                        heap_element)list`;
                 `UNIV:num->bool`] MP2AUX_v_inv_ck_transfer) THEN
  REWRITE_TAC[IN_UNIV] THEN ANTS_TAC THENL
   [ALL_TAC; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[lookup_insert] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n:num = ptr` THEN ASM_REWRITE_TAC[] THENL
     [STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ASM_REWRITE_TAC[option_INJ] THEN MESON_TAC[];
      MESON_TAC[]];
    MAP_EVERY X_GEN_TAC [`n:num`; `ev:thunk_mode`; `v:data_v`] THEN
    ASM_CASES_TAC `n:num = ptr` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MP2AUX_dest_thunk_insert THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 3873 *)
let v_inv_ByteArray_insert_lemma = prove
 (`!conf ptr fl xs ck v1 refs (y:(A word_loc)heap_address) f tf heap.
     v_inv conf v1 refs (y,f,tf,heap) /\
     (ptr IN domain refs ==> ?a b. lookup ptr refs = SOME (bvl_ByteArray a b)) ==>
     v_inv_ck ck conf v1 (insert ptr (bvl_ByteArray fl xs) refs) (y,f,tf,heap)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MP2AUX_v_inv_ck_insert THEN
  REWRITE_TAC[distinctness "bvl_ref"; ref_ptr_annot_def] THEN
  SUBGOAL_THEN `lookup ptr refs = (NONE:(data_v bvl_ref)option) \/
                ?a b. lookup ptr refs = SOME (bvl_ByteArray a b)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[domain_lookup; cases "option"];
    ASM_REWRITE_TAC[distinctness "option"; option_INJ; distinctness "bvl_ref";
                    ref_ptr_annot_def] THEN ASM_MESON_TAC[v_inv_eq];
    ASM_REWRITE_TAC[distinctness "option"; option_INJ; distinctness "bvl_ref";
                    ref_ptr_annot_def] THEN ASM_MESON_TAC[v_inv_eq]]);;

(* HOL4 line 3907 *)
let v_inv_ByteArray_insert = prove
 (`!conf v1 refs (v2:(A word_loc)heap_address) f tf heap ptr fl xs.
     v_inv conf v1 refs (v2,f,tf,heap) /\
     (ptr IN domain refs ==> ?a b. lookup ptr refs = SOME (bvl_ByteArray a b)) ==>
     v_inv conf v1 (insert ptr (bvl_ByteArray fl xs) refs) (v2,f,tf,heap)`,
  MESON_TAC[v_inv_eq; v_inv_ByteArray_insert_lemma]);;

(* HOL4 line 3916 *)
let isRefBlock_def = cake_def
  `isRefBlock (x:(A,data_to_word_memoryProof_tag#B list)heap_element) <=>
     ?p. x = RefBlock p`;;

(* HOL4 line 3920 *)
let RefBlock_inv_def = cake_def
  `RefBlock_inv (heap:((A,data_to_word_memoryProof_tag#B list)heap_element)list)
     heap2 <=>
     (!n x. heap_lookup n heap = SOME x /\ ~isRefBlock x ==>
            heap_lookup n heap2 = SOME x) /\
     (!n x. heap_lookup n heap2 = SOME x /\ ~isRefBlock x ==>
            heap_lookup n heap = SOME x)`;;

(* HOL4 line 3928 *)
let heap_store_RefBlock_thm = prove
 (`!(x:(A heap_address)list) y hb ha.
     LENGTH x = LENGTH y ==>
     heap_store (heap_length ha) [RefBlock x]
       (APPEND ha (CONS (RefBlock y) hb)
        :((A,data_to_word_memoryProof_tag#B list)heap_element)list) =
     (APPEND ha (CONS (RefBlock x) hb),T)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[heap_store_lemma; GSYM APPEND_ASSOC; APPEND; PAIR_EQ] THEN
  ASM_REWRITE_TAC[heap_length_def; MAP; SUM; RefBlock_def; el_length_def; ADD_CLAUSES]);;

(* MP2AUX: heap_lookup in a heap with a known element *)
let MP2AUX_heap_lookup_middle = prove
 (`!n ha (y:(A,B)heap_element) hb x.
     (heap_lookup n (APPEND ha (CONS y hb)) = SOME x) =
     if n < heap_length ha then heap_lookup n ha = SOME x
     else if n = heap_length ha then x = y
     else if heap_length ha + el_length y <= n then
       heap_lookup (n - heap_length ha - el_length y) hb = SOME x
     else F`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `n < heap_length (ha:((A,B)heap_element)list)` THEN
  ASM_SIMP_TAC[gc_shared_LESS_IMP_heap_lookup; NOT_LESS_IMP_heap_lookup] THEN
  REWRITE_TAC[heap_lookup_def] THEN
  MP_TAC(ISPEC `y:(A,B)heap_element` el_length_NOT_0) THEN
  ASM_CASES_TAC `n = heap_length (ha:((A,B)heap_element)list)` THEN
  ASM_REWRITE_TAC[SUB_REFL; option_INJ] THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(n - heap_length (ha:((A,B)heap_element)list) = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `heap_length (ha:((A,B)heap_element)list) + el_length (y:(A,B)heap_element)
                 <= n` THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(n - heap_length (ha:((A,B)heap_element)list) <
                    el_length (y:(A,B)heap_element))`
      (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `n - heap_length (ha:((A,B)heap_element)list) <
                  el_length (y:(A,B)heap_element)`
      (fun th -> REWRITE_TAC[th; distinctness "option"]) THEN ASM_ARITH_TAC]);;

(* HOL4 line 3941 *)
let heap_lookup_RefBlock_lemma = prove
 (`!n ha (y:(A heap_address)list) hb
    (x:(A,data_to_word_memoryProof_tag#B list)heap_element).
     (heap_lookup n (APPEND ha (CONS (RefBlock y) hb)) = SOME x) =
     if n < heap_length ha then heap_lookup n ha = SOME x
     else if n = heap_length ha then x = RefBlock y
     else if heap_length ha + (LENGTH y + 1) <= n then
       heap_lookup (n - heap_length ha - (LENGTH y + 1)) hb = SOME x
     else F`,
  REWRITE_TAC[MP2AUX_heap_lookup_middle] THEN
  REWRITE_TAC[RefBlock_def; el_length_def]);;

(* MP2AUX: replacing one heap element by one of the same length *)
let MP2AUX_heap_store_same = prove
 (`!n (heap:((A,B)heap_element)list) y h.
     heap_lookup n heap = SOME y /\ el_length h = el_length y ==>
     ?heap2. heap_store n [h] heap = (heap2,T) /\
             heap_lookup n heap2 = SOME h /\
             heap_length heap2 = heap_length heap /\
             (!m. ~(m = n) ==> heap_lookup m heap2 = heap_lookup m heap) /\
             (!z. MEM z heap2 ==> z = h \/ MEM z heap) /\
             (~isForwardPointer y /\ ~isForwardPointer h ==>
              FILTER isForwardPointer heap2 = FILTER isForwardPointer heap)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP heap_lookup_SPLIT) THEN
  DISCH_THEN(X_CHOOSE_THEN `ha:((A,B)heap_element)list`
    (X_CHOOSE_THEN `hb:((A,B)heap_element)list` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[heap_store_lemma; PAIR_EQ] THEN
  EXISTS_TAC `APPEND (APPEND ha [h]) (hb:((A,B)heap_element)list)` THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; heap_lookup_PREFIX] THEN
  REWRITE_TAC[heap_length_APPEND; MEM_APPEND; MEM; FILTER_APPEND; FILTER] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[heap_length_def; MAP; SUM; ADD_CLAUSES] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[heap_length_def; MAP; SUM] THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN
    ASM_CASES_TAC `m < heap_length (ha:((A,B)heap_element)list)` THEN
    ASM_SIMP_TAC[gc_shared_LESS_IMP_heap_lookup; NOT_LESS_IMP_heap_lookup] THEN
    REWRITE_TAC[heap_lookup_def] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(m - heap_length (ha:((A,B)heap_element)list) = 0)`
      (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    MESON_TAC[];
    SIMP_TAC[]]);;

(* MP2AUX: data elements are not forward pointers; isSomeDataElement of SOME *)
let MP2AUX_isDataElement_facts = prove
 (`(!x:(A,B)heap_element. isDataElement x ==> ~isForwardPointer x) /\
   (!x:(A,B)heap_element. isSomeDataElement (SOME x) <=> isDataElement x)`,
  REWRITE_TAC[isDataElement_def; isSomeDataElement_def; option_INJ] THEN
  REPEAT STRIP_TAC THEN UNDISCH_TAC `isForwardPointer (x:(A,B)heap_element)` THEN
  ASM_REWRITE_TAC[isForwardPointer_def]);;

(* MP2AUX: what is kept by replacing one data element with another *)
let MP2AUX_heap_store_same_data = prove
 (`!n (heap:((A,B)heap_element)list) y h.
     heap_lookup n heap = SOME y /\ el_length h = el_length y /\
     isDataElement y /\ isDataElement h ==>
     ?heap2. heap_store n [h] heap = (heap2,T) /\
             heap_lookup n heap2 = SOME h /\
             heap_length heap2 = heap_length heap /\
             FILTER isForwardPointer heap2 = FILTER isForwardPointer heap /\
             (!xs l d.
                MEM (DataElement xs l d) heap2 ==>
                DataElement xs l d = h \/ MEM (DataElement xs l d) heap) /\
             (!a. isSomeDataElement (heap_lookup a heap2) =
                  isSomeDataElement (heap_lookup a heap)) /\
             (!m x. ~(m = n) /\ heap_lookup m heap = SOME x ==>
                    heap_lookup m heap2 = SOME x) /\
             (!m. ~(m = n) ==> heap_lookup m heap2 = heap_lookup m heap)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `heap:((A,B)heap_element)list`; `y:(A,B)heap_element`;
                 `h:(A,B)heap_element`] MP2AUX_heap_store_same) THEN
  ASM_SIMP_TAC[MP2AUX_isDataElement_facts] THEN
  DISCH_THEN(X_CHOOSE_THEN `heap2:((A,B)heap_element)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `heap2:((A,B)heap_element)list` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC `a:num = n` THEN
    ASM_SIMP_TAC[MP2AUX_isDataElement_facts];
    ASM_SIMP_TAC[]]);;

(* HOL4 line 3964 *)
let heap_store_RefBlock = prove
 (`!(y:(A heap_address)list) h n
    (heap:((A,data_to_word_memoryProof_tag#B list)heap_element)list).
     LENGTH y = LENGTH h /\
     heap_lookup n heap = SOME (RefBlock y) ==>
     ?heap2. heap_store n [RefBlock h] heap = (heap2,T) /\
             RefBlock_inv heap heap2 /\
             heap_lookup n heap2 = SOME (RefBlock h) /\
             heap_length heap2 = heap_length heap /\
             FILTER isForwardPointer heap2 = FILTER isForwardPointer heap /\
             (!xs l d.
                MEM (DataElement xs l d) heap2 ==>
                DataElement xs l d = RefBlock h \/
                MEM (DataElement xs l d) heap) /\
             (!a. isSomeDataElement (heap_lookup a heap2) =
                  isSomeDataElement (heap_lookup a heap)) /\
             !m x. ~(m = n) /\ heap_lookup m heap = SOME x ==>
                   heap_lookup m heap2 = SOME x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`;
                 `heap:((A,data_to_word_memoryProof_tag#B list)heap_element)list`;
                 `RefBlock y:(A,data_to_word_memoryProof_tag#B list)heap_element`;
                 `RefBlock h:(A,data_to_word_memoryProof_tag#B list)heap_element`]
                MP2AUX_heap_store_same_data) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RefBlock_def; el_length_def; isDataElement_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN
    `heap2:((A,data_to_word_memoryProof_tag#B list)heap_element)list`
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `heap2:((A,data_to_word_memoryProof_tag#B list)heap_element)list` THEN
  ASM_REWRITE_TAC[RefBlock_inv_def] THEN
  CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`k:num`;
    `z:(A,data_to_word_memoryProof_tag#B list)heap_element`] THEN STRIP_TAC THEN
  (ASM_CASES_TAC `k:num = n` THENL
    [UNDISCH_TAC `~isRefBlock (z:(A,data_to_word_memoryProof_tag#B list)heap_element)` THEN
     REWRITE_TAC[isRefBlock_def] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[option_INJ]) THEN ASM_MESON_TAC[option_INJ];
     ASM_MESON_TAC[]]));;

(* HOL4 line 4001 *)
let NOT_isRefBlock = prove
 (`!x (a:A->bool) w xs n.
     ~isRefBlock (Bignum x:(A word_loc,data_to_word_memoryProof_tag#
                             (A word_loc)list)heap_element) /\
     ~isRefBlock (Word64Rep a w) /\
     ~isRefBlock (DataElement xs (LENGTH xs) (BlockTag n,[])
                  :(B,data_to_word_memoryProof_tag#C list)heap_element)`,
  REWRITE_TAC[isRefBlock_def; MP2AUX_heap_el_facts; Word64Rep_DEF; RefBlock_def] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  SIMP[injectivity "heap_element"; distinctness "data_to_word_memoryProof_tag"]);;

(* MP2AUX: v_inv_ck under a change of the heap that keeps the cells that  *)
(* are not RefBlocks                                                      *)
let MP2AUX_v_inv_ck_heap = prove
 (`!conf (refs:(data_v bvl_ref)spt) f tf
    (heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
           heap_element)list) heap2 ck w (x:(A word_loc)heap_address).
     (!p X. heap_lookup p heap = SOME X /\ ~isRefBlock X ==>
            heap_lookup p heap2 = SOME X) /\
     v_inv_ck ck conf w refs (x,f,tf,heap)
     ==> v_inv_ck ck conf w refs (x,f,tf,heap2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `refs:(data_v bvl_ref)spt`;
                 `refs:(data_v bvl_ref)spt`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
                 `tf:(num,num)fmap`;
                 `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                        heap_element)list`; `heap2:(((A)word_loc,
                  data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
                 `UNIV:num->bool`] MP2AUX_v_inv_ck_transfer) THEN
  REWRITE_TAC[IN_UNIV] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MESON_TAC[]) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[isRefBlock_def] THEN ASM_MESON_TAC[];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 4012 *)
let v_inv_Ref_lemma = prove
 (`!conf heap2 ck w refs (x:(A word_loc)heap_address) f tf heap.
     v_inv conf w refs (x,f,tf,heap) /\
     RefBlock_inv heap heap2 ==>
     (v_inv_ck ck conf w refs (x,f,tf,heap) <=>
      v_inv_ck ck conf w refs (x,f,tf,heap2))`,
  REWRITE_TAC[RefBlock_inv_def] THEN REPEAT STRIP_TAC THEN EQ_TAC THEN
  DISCH_TAC THEN MATCH_MP_TAC MP2AUX_v_inv_ck_heap THEN ASM_MESON_TAC[]);;

(* HOL4 line 4100 *)
let v_inv_Ref = prove
 (`!conf refs
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) heap2.
     RefBlock_inv heap heap2 ==>
     !x h f tf. (v_inv conf x refs (h,f,tf,heap2) <=>
                 v_inv conf x refs (h,f,tf,heap))`,
  REWRITE_TAC[RefBlock_inv_def; v_inv_eq] THEN REPEAT STRIP_TAC THEN
  EQ_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC MP2AUX_v_inv_ck_heap THEN ASM_MESON_TAC[]);;

(* HOL4 line 4114 *)
let v_inv_ValueArray_insert_lemma = prove
 (`!conf heap2 ptr xs ck v1 refs (y:(A word_loc)heap_address) f tf heap.
     v_inv conf v1 refs (y,f,tf,heap) /\
     RefBlock_inv heap heap2 /\
     (ptr IN domain refs ==> ?as. lookup ptr refs = SOME (bvl_ValueArray as)) ==>
     v_inv_ck ck conf v1 (insert ptr (bvl_ValueArray xs) refs) (y,f,tf,heap)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MP2AUX_v_inv_ck_insert THEN
  REWRITE_TAC[distinctness "bvl_ref"; ref_ptr_annot_def] THEN
  SUBGOAL_THEN `lookup ptr refs = (NONE:(data_v bvl_ref)option) \/
                ?as. lookup ptr refs = SOME (bvl_ValueArray as)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[domain_lookup; cases "option"];
    ASM_REWRITE_TAC[distinctness "option"; option_INJ; distinctness "bvl_ref";
                    ref_ptr_annot_def] THEN ASM_MESON_TAC[v_inv_eq];
    ASM_REWRITE_TAC[distinctness "option"; option_INJ; distinctness "bvl_ref";
                    ref_ptr_annot_def] THEN ASM_MESON_TAC[v_inv_eq]]);;

(* HOL4 line 4145 *)
let v_inv_ValueArray_insert = prove
 (`!conf v1 refs (v2:(A word_loc)heap_address) f tf heap ptr xs heap2.
     RefBlock_inv heap heap2 /\
     v_inv conf v1 refs (v2,f,tf,heap) /\
     (ptr IN domain refs ==> ?as. lookup ptr refs = SOME (bvl_ValueArray as)) ==>
     v_inv conf v1 (insert ptr (bvl_ValueArray xs) refs) (v2,f,tf,heap2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP v_inv_Ref th]) THEN
  REWRITE_TAC[v_inv_eq] THEN GEN_TAC THEN
  MATCH_MP_TAC v_inv_ValueArray_insert_lemma THEN ASM_MESON_TAC[]);;

(* HOL4 line 4158 *)
let v_inv_MutBlock_insert_lemma = prove
 (`!conf ptr tag fin l cv r ck v1 refs (y:(A word_loc)heap_address) f tf heap.
     v_inv conf v1 refs (y,f,tf,heap) /\
     ~(ptr IN domain refs) /\ FDOM f SUBSET domain refs ==>
     v_inv_ck ck conf v1 (insert ptr (MutBlock tag fin l cv r) refs) (y,f,tf,heap)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MP2AUX_v_inv_ck_insert THEN
  REWRITE_TAC[distinctness "bvl_ref"] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; domain_lookup]) THEN
  ASM_MESON_TAC[v_inv_eq]);;

(* HOL4 line 4178 *)
let v_inv_MutBlock_insert = prove
 (`!conf v1 refs (v2:(A word_loc)heap_address) f tf heap ptr tag fin l cv r.
     v_inv conf v1 refs (v2,f,tf,heap) /\
     ~(ptr IN domain refs) /\ FDOM f SUBSET domain refs ==>
     v_inv conf v1 (insert ptr (MutBlock tag fin l cv r) refs) (v2,f,tf,heap)`,
  MESON_TAC[v_inv_eq; v_inv_MutBlock_insert_lemma]);;

(* HOL4 line 4190 *)
let v_inv_MutBlock_fin_lemma = prove
 (`!conf ptr tag fin1 fin2 ll cv rr ck v1 refs (y:(A word_loc)heap_address) f tf
    heap.
     v_inv conf v1 refs (y,f,tf,heap) /\
     lookup ptr refs = SOME (MutBlock tag fin1 ll cv rr) ==>
     v_inv_ck ck conf v1 (insert ptr (MutBlock tag fin2 ll cv rr) refs)
       (y,f,tf,heap)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MP2AUX_v_inv_ck_insert THEN
  ASM_REWRITE_TAC[distinctness "bvl_ref"; ref_ptr_annot_def; option_INJ] THEN
  ASM_MESON_TAC[v_inv_eq]);;

(* HOL4 line 4212 *)
let v_inv_MutBlock_fin = prove
 (`!cnf vv rfs (yy:(A word_loc)heap_address) ff tff hp pp tg b1 b2 l1 c1 r1.
     v_inv cnf vv rfs (yy,ff,tff,hp) /\
     lookup pp rfs = SOME (MutBlock tg b1 l1 c1 r1) ==>
     v_inv cnf vv (insert pp (MutBlock tg b2 l1 c1 r1) rfs) (yy,ff,tff,hp)`,
  MESON_TAC[v_inv_eq; v_inv_MutBlock_fin_lemma]);;

(* HOL4 line 4223 *)
let all_ts_SUBSET_gen = prove
 (`!refs1 stack1 refs2 stack2.
     (!x. ((?n r'. lookup n refs1 = SOME r' /\ find_ref r' x) \/ MEM x stack1) ==>
          ((?n r'. lookup n refs2 = SOME r' /\ find_ref r' x) \/ MEM x stack2)) ==>
     all_ts refs1 stack1 SUBSET all_ts refs2 stack2`,
  REWRITE_TAC[all_ts_def; LET_DEF; LET_END_DEF; SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[]);;

(* HOL4 line 4234 *)
let all_ts_SUBSET_ts = prove
 (`!refs1 stack1 refs2 stack2.
     (!x t. ((?n r'. lookup n refs1 = SOME r' /\ find_ref r' x) \/
             MEM x stack1) /\ MEM t (v_all_ts x) ==>
            ?x'. ((?n r'. lookup n refs2 = SOME r' /\ find_ref r' x') \/
                  MEM x' stack2) /\ MEM t (v_all_ts x')) ==>
     all_ts refs1 stack1 SUBSET all_ts refs2 stack2`,
  REWRITE_TAC[all_ts_def; LET_DEF; LET_END_DEF; SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[]);;

(* HOL4 line 4244 *)
let all_ts_mutcons = prove
 (`!ptr refs l c r stack tag.
     ~(ptr IN domain refs) ==>
     all_ts refs (APPEND (APPEND (APPEND l [c]) r) stack) SUBSET
     all_ts (insert ptr (MutBlock tag F l c r) refs)
       (CONS (data_RefPtr F ptr) stack)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC all_ts_SUBSET_gen THEN
  REWRITE_TAC[lookup_insert; MEM_APPEND; MEM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[domain_lookup]) THEN
  REPEAT STRIP_TAC THENL
   [DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`n:num`; `r':data_v bvl_ref`] THEN
    SUBGOAL_THEN `~(n:num = ptr)` (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[];
    ALL_TAC; ALL_TAC; ALL_TAC; ASM_REWRITE_TAC[]] THEN
  DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`ptr:num`;
    `MutBlock tag F l (c:data_v) r`] THEN
  ASM_REWRITE_TAC[find_ref_def; MEM_APPEND; MEM]);;

(* HOL4 line 4256 *)
let blocks_unique_mutcons = prove
 (`!ts refs l c r stack ptr tag.
     blocks_unique ts (all_vs refs (APPEND (APPEND (APPEND l [c]) r) stack)) ==>
     blocks_unique ts
       (all_vs (insert ptr (MutBlock tag F l c r) refs)
          (CONS (data_RefPtr F ptr) stack))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MP2AUX_blocks_unique_mono THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM; v_all_vs_def; v_all_vs_append;
              MEM; MEM_APPEND; distinctness "data_v"; lookup_insert] THEN
  REPEAT GEN_TAC THEN
  REPEAT(MATCH_MP_TAC(TAUT `(a ==> c) /\ (b ==> c) ==> a \/ b ==> c`) THEN CONJ_TAC) THEN
  REPEAT STRIP_TAC THEN TRY(ASM_MESON_TAC[]) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o lhand o concl)) THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ; injectivity "bvl_ref"; distinctness "bvl_ref"] THEN
  ASM_MESON_TAC[]);;

(* HOL4 line 4268 *)
let ref_edge_MutBlock = prove
 (`!ptr tag fin l c r refs x y.
     ref_edge (insert ptr (MutBlock tag fin l c r) refs) x y <=>
     if x = ptr then MEM y (get_refs (data_Block 0 ARB (APPEND (APPEND l [c]) r)))
     else ref_edge refs x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ref_edge_def; lookup_insert] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CASE_REWRITE_TAC[]);;

(* HOL4 line 4281 *)
let reachable_refs_MutCons_lemma = prove
 (`!ptr tag l c r refs r1 n.
     RTC (ref_edge (insert ptr (MutBlock tag F l c r) refs)) r1 n ==>
     ~(n = ptr) ==>
     RTC (ref_edge refs) r1 n \/
     ?s. MEM s (get_refs (data_Block 0 ARB (APPEND (APPEND l [c]) r))) /\
         RTC (ref_edge refs) s n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ref_edge refs`;
                 `ref_edge (insert ptr (MutBlock tag F l c r) refs)`;
                 `\s. MEM s (get_refs (data_Block 0 ARB
                                        (APPEND (APPEND l [c]) r)))`]
                MP2AUX_RTC_redirect) THEN
  REWRITE_TAC[ref_edge_MutBlock] THEN ANTS_TAC THENL
   [REPEAT GEN_TAC THEN COND_CASES_TAC THEN MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* MP2AUX: no edge leaves a fresh ref *)
let MP2AUX_RTC_ref_edge_fresh = prove
 (`!refs ptr m. ~(ptr IN domain refs) /\ RTC (ref_edge refs) ptr m ==> m = ptr`,
  REPEAT GEN_TAC THEN REWRITE_TAC[domain_lookup] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lookup ptr refs = (NONE:(data_v bvl_ref)option)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cases "option"]; ALL_TAC] THEN
  UNDISCH_TAC `RTC (ref_edge refs) ptr m` THEN ONCE_REWRITE_TAC[RTC_CASES_R] THEN
  ASM_REWRITE_TAC[ref_edge_def] THEN CASE_REWRITE_TAC[] THEN MESON_TAC[]);;

(* HOL4 line 4295 *)
let reachable_refs_MutCons = prove
 (`!ptr stack tag l c r refs n.
     reachable_refs (CONS (data_RefPtr F ptr) stack)
       (insert ptr (MutBlock tag F l c r) refs) n /\
     ~(n = ptr) /\ ~(ptr IN domain refs) ==>
     reachable_refs (APPEND (APPEND (APPEND l [c]) r) stack) refs n`,
  REWRITE_TAC[reachable_refs_def] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP reachable_refs_MutCons_lemma) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [UNDISCH_TAC `MEM (x:data_v) (CONS (data_RefPtr F ptr) stack)` THEN
    REWRITE_TAC[MEM] THEN STRIP_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[get_refs_def; MEM]) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[MP2AUX_RTC_ref_edge_fresh];
      ASM_MESON_TAC[MEM_APPEND]];
    RULE_ASSUM_TAC(REWRITE_RULE[get_refs_def; MEM_FLAT; MEM_MAP]) THEN
    ASM_MESON_TAC[MEM_APPEND]]);;

(* HOL4 line 4314 *)
let v_inv_MutCons_step = prove
 (`!conf v refs (y:(A word_loc)heap_address) f tf heap ptr heap2 tag l c r a.
     v_inv conf v refs (y,f,tf,heap) /\ ~(ptr IN domain refs) /\
     FDOM f SUBSET domain refs /\ heap_store_rel heap heap2 ==>
     v_inv conf v (insert ptr (MutBlock tag F l c r) refs)
       (y,f |+ (ptr,a),tf,heap2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC v_inv_SUBMAP THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf:(num,num)fmap`;
    `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list`] THEN
  ASM_REWRITE_TAC[SUBMAP_REFL] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBMAP_DEF; FDOM_FUPDATE; FAPPLY_FUPDATE_THM; IN_INSERT] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN ASM_MESON_TAC[];
    MATCH_MP_TAC v_inv_MutBlock_insert THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 4331 *)
let take_el_drop = prove
 (`!index (vals:A list).
     index < LENGTH vals ==>
     APPEND (APPEND (TAKE index vals) [EL index vals]) (DROP (index + 1) vals) =
     vals`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP DROP_EL_CONS th)]) THEN
  REWRITE_TAC[TAKE_DROP]);;

(* HOL4 line 4344 *)
let dest_thunk_insert_fresh = prove
 (`!ptr refs v x.
     ~(ptr IN domain refs) /\ data_dest_thunk v refs = data_NotThunk ==>
     data_dest_thunk v (insert ptr x refs) = data_NotThunk`,
  REWRITE_TAC[MP2AUX_dest_thunk_NotThunk; lookup_insert; domain_lookup] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* HOL4 line 4355 *)
let mutcons_thm_alt = prove
 (`!conf l c r stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts ptr tag.
     abs_ml_inv conf (APPEND (APPEND (APPEND l [c]) r) stack) refs
       (roots,heap,be,a,sp,sp1,gens) limit ts /\
     LENGTH (APPEND (APPEND l [c]) r) < sp /\ ~(ptr IN domain refs) /\
     (!gs. ~(data_to_word_config_gc_kind conf = Generational gs)) ==>
     ?rs roots2 heap2.
       roots = APPEND rs roots2 /\ LENGTH rs = LENGTH (APPEND (APPEND l [c]) r) /\
       heap_store_unused_alt a (sp + sp1) (BlockRep tag rs) heap = (heap2,T) /\
       abs_ml_inv conf (CONS (data_RefPtr F ptr) stack)
         (insert ptr (MutBlock tag F l c r) refs)
         (CONS (Pointer a (wl_Word (ptr_bits conf tag
                                      (LENGTH (APPEND (APPEND l [c]) r)))))
               roots2,
          heap2,be,
          a + el_length (BlockRep tag rs:(A word_loc,data_to_word_memoryProof_tag#
                                          (A word_loc)list)heap_element),
          sp - el_length (BlockRep tag rs:(A word_loc,data_to_word_memoryProof_tag#
                                           (A word_loc)list)heap_element),
          sp1,gens) limit ts`,
  REPEAT GEN_TAC THEN REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN
  ABBREV_TAC `vs = APPEND (APPEND l [c:data_v]) r` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP EVERY2_APPEND_IMP_APPEND) THEN
  DISCH_THEN(X_CHOOSE_THEN `rs:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `roots2:((A word_loc)heap_address)list` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`rs:((A word_loc)heap_address)list`;
                        `roots2:((A word_loc)heap_address)list`] THEN
  SUBGOAL_THEN `LENGTH (rs:((A word_loc)heap_address)list) = LENGTH (vs:data_v list)`
    ASSUME_TAC THENL [ASM_MESON_TAC[EVERY2_LENGTH]; ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `a:num`; `sp:num`; `sp1:num`;
                 `gens:gen_state`; `limit:num`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element)list`;
                 `BlockRep tag rs:(A word_loc,data_to_word_memoryProof_tag#
                                   (A word_loc)list)heap_element`]
                MP2AUX_alloc_lemma) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[BlockRep_def; el_length_def; isDataElement_def; isRef_def;
                    isMutTag_def; distinctness "data_to_word_memoryProof_tag";
                    injectivity "heap_element"] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `roots_ok (roots:((A word_loc)heap_address)list)
      (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
             heap_element)list)` THEN
    ASM_REWRITE_TAC[roots_ok_def; MEM_APPEND] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `heap2:((A word_loc,data_to_word_memoryProof_tag#
                                    (A word_loc)list)heap_element)list`
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `heap2:((A word_loc,data_to_word_memoryProof_tag#
                      (A word_loc)list)heap_element)list` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(ptr IN FDOM (f:(num,num)fmap))` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!v (z:(A word_loc)heap_address).
      v_inv conf v refs (z,f,tf,heap) ==>
      v_inv conf v (insert ptr (MutBlock tag F l c r) refs) (z,f |+ (ptr,a),tf,heap2)`
  (LABEL_TAC "VT") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC v_inv_MutCons_step THEN
    EXISTS_TAC `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                      heap_element)list` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `roots_ok (roots:((A word_loc)heap_address)list)
      (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
             heap_element)list)` THEN
    ASM_REWRITE_TAC[roots_ok_def; MEM; MEM_APPEND; injectivity "heap_address"] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`f |+ (ptr:num,a:num)`; `tf:(num,num)fmap`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `INJ (FAPPLY (f:(num,num)fmap)) (FDOM f)
      {a | isSomeDataElement (heap_lookup a
        (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
               heap_element)list))}` THEN
    REWRITE_TAC[INJ; IN_ELIM_THM; FDOM_FUPDATE; FAPPLY_FUPDATE_THM; IN_INSERT] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[FDOM_FUPDATE; domain_insert] THEN ASM SET_TAC[];
    UNDISCH_TAC `INJ (FAPPLY (tf:(num,num)fmap)) (FDOM tf)
      {a | isSomeDataElement (heap_lookup a
        (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
               heap_element)list))}` THEN
    REWRITE_TAC[INJ; IN_ELIM_THM] THEN MESON_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `all_ts (refs:(data_v bvl_ref)spt) (APPEND vs stack)` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "vs" THEN MATCH_MP_TAC all_ts_mutcons THEN
    ASM_REWRITE_TAC[];
    EXPAND_TAC "vs" THEN MATCH_MP_TAC blocks_unique_mutcons THEN
    UNDISCH_TAC `blocks_unique ts (all_vs (refs:(data_v bvl_ref)spt) (APPEND vs stack))` THEN
    EXPAND_TAC "vs" THEN REWRITE_TAC[];
    REWRITE_TAC[ALL2] THEN CONJ_TAC THENL
     [REWRITE_TAC[v_inv_def; lookup_insert; FDOM_FUPDATE; IN_INSERT;
                  FAPPLY_FUPDATE_THM; distinctness "bvl_ref"; option_INJ;
                  ref_ptr_annot_def; injectivity "heap_address"] THEN
      EXPAND_TAC "vs" THEN REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
      REWRITE_TAC[ARITH_RULE `(l + SUC 0) + r = l + 1 + r`];
      UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs (x,f,tf,
        heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
              heap_element)list)) stack roots2` THEN
      MATCH_MP_TAC MONO_ALL2 THEN USE_THEN "VT" (fun th -> SIMP_TAC[th])];
    X_GEN_TAC `n:num` THEN REWRITE_TAC[FDOM_FUPDATE; IN_INSERT] THEN STRIP_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[bc_ref_inv_def; FLOOKUP_UPDATE; lookup_insert] THEN
      CASE_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_IMAGE] THEN
        UNDISCH_TAC `INJ (FAPPLY (tf:(num,num)fmap)) (FDOM tf)
          {a | isSomeDataElement (heap_lookup a
            (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                   heap_element)list))}` THEN
        REWRITE_TAC[INJ; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        EXISTS_TAC `rs:((A word_loc)heap_address)list` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs (x,f,tf,
          heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                heap_element)list)) vs rs` THEN
        EXPAND_TAC "vs" THEN DISCH_THEN(MP_TAC o MATCH_MP EVERY2_SWAP) THEN
        MATCH_MP_TAC MONO_ALL2 THEN USE_THEN "VT" (fun th -> SIMP_TAC[th])];
      SUBGOAL_THEN `~(n:num = ptr)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MP2AUX_bc_ref_inv_transfer THEN
      MAP_EVERY EXISTS_TAC [`refs:(data_v bvl_ref)spt`; `f:(num,num)fmap`;
        `tf:(num,num)fmap`;
        `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
               heap_element)list`] THEN
      ASM_REWRITE_TAC[lookup_insert; FLOOKUP_UPDATE] THEN REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "vs" THEN MATCH_MP_TAC reachable_refs_MutCons THEN
        MAP_EVERY EXISTS_TAC [`ptr:num`; `tag:num`] THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[heap_store_rel_lemma];
        USE_THEN "VT" (fun th -> MESON_TAC[th]);
        REPEAT STRIP_TAC THEN MATCH_MP_TAC dest_thunk_insert_fresh THEN
        ASM_REWRITE_TAC[];
        MESON_TAC[]]]]);;

(* HOL4 line 4457 *)
let mutcons_thm = prove
 (`!conf xs stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts index ptr tag.
     abs_ml_inv conf (APPEND xs stack) refs (roots,heap,be,a,sp,sp1,gens) limit ts /\
     LENGTH xs < sp /\ index < LENGTH xs /\ ~(ptr IN domain refs) /\
     (!gs. ~(data_to_word_config_gc_kind conf = Generational gs)) ==>
     ?rs roots2 heap2.
       roots = APPEND rs roots2 /\ LENGTH rs = LENGTH xs /\
       heap_store_unused_alt a (sp + sp1) (BlockRep tag rs) heap = (heap2,T) /\
       abs_ml_inv conf (CONS (data_RefPtr F ptr) stack)
         (insert ptr (MutBlock tag F (TAKE index xs) (EL index xs)
                                     (DROP (index + 1) xs)) refs)
         (CONS (Pointer a (wl_Word (ptr_bits conf tag (LENGTH xs)))) roots2,
          heap2,be,
          a + el_length (BlockRep tag rs:(A word_loc,data_to_word_memoryProof_tag#
                                          (A word_loc)list)heap_element),
          sp - el_length (BlockRep tag rs:(A word_loc,data_to_word_memoryProof_tag#
                                           (A word_loc)list)heap_element),
          sp1,gens) limit ts`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP take_el_drop) THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `TAKE index (xs:data_v list)`;
                 `EL index (xs:data_v list)`; `DROP (index + 1) (xs:data_v list)`;
                 `stack:data_v list`; `refs:(data_v bvl_ref)spt`;
                 `roots:((A word_loc)heap_address)list`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element)list`;
                 `be:bool`; `a:num`; `sp:num`; `sp1:num`; `gens:gen_state`;
                 `limit:num`; `ts:num`; `ptr:num`; `tag:num`] mutcons_thm_alt) THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 4482 *)
let heap_store_ThunkBlock_thm = prove
 (`!ev1 (v1:A heap_address) ev2 v2 hb ha.
     heap_store (heap_length ha) [ThunkBlock ev1 v1]
       (APPEND ha (CONS (ThunkBlock ev2 v2) hb)
        :((A,data_to_word_memoryProof_tag#B list)heap_element)list) =
     (APPEND ha (CONS (ThunkBlock ev1 v1) hb),T)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[heap_store_lemma; GSYM APPEND_ASSOC; APPEND; PAIR_EQ] THEN
  REWRITE_TAC[heap_length_def; MAP; SUM; ThunkBlock_def; el_length_def; ADD_CLAUSES]);;

(* HOL4 line 4497 *)
let heap_lookup_ThunkBlock_lemma = prove
 (`!n ha ev (v:A heap_address) hb
    (x:(A,data_to_word_memoryProof_tag#B list)heap_element).
     (heap_lookup n (APPEND ha (CONS (ThunkBlock ev v) hb)) = SOME x) =
     if n < heap_length ha then heap_lookup n ha = SOME x
     else if n = heap_length ha then x = ThunkBlock ev v
     else if heap_length ha + 2 <= n then
       heap_lookup (n - heap_length ha - 2) hb = SOME x
     else F`,
  REWRITE_TAC[MP2AUX_heap_lookup_middle] THEN
  REWRITE_TAC[ThunkBlock_def; el_length_def; ARITH_RULE `1 + 1 = 2`]);;

(* HOL4 line 4519 *)
let heap_store_ThunkBlock = prove
 (`!n (heap:((A,data_to_word_memoryProof_tag#B list)heap_element)list) y ev h.
     heap_lookup n heap = SOME (ThunkBlock NotEvaluated y) ==>
     ?heap2.
       heap_store n [ThunkBlock ev h] heap = (heap2,T) /\
       heap_lookup n heap2 = SOME (ThunkBlock ev h) /\
       heap_length heap2 = heap_length heap /\
       FILTER isForwardPointer heap2 = FILTER isForwardPointer heap /\
       (!xs l d.
          MEM (DataElement xs l d) heap2 ==>
          DataElement xs l d = ThunkBlock ev h \/
          MEM (DataElement xs l d) heap) /\
       (!a. isSomeDataElement (heap_lookup a heap2) =
            isSomeDataElement (heap_lookup a heap)) /\
       (!m x. ~(m = n) /\ heap_lookup m heap = SOME x ==>
              heap_lookup m heap2 = SOME x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`;
                 `heap:((A,data_to_word_memoryProof_tag#B list)heap_element)list`;
                 `ThunkBlock NotEvaluated y:(A,data_to_word_memoryProof_tag#B list)
                                            heap_element`;
                 `ThunkBlock ev h:(A,data_to_word_memoryProof_tag#B list)heap_element`]
                MP2AUX_heap_store_same_data) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ThunkBlock_def; el_length_def; isDataElement_def] THEN MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN
      `heap2:((A,data_to_word_memoryProof_tag#B list)heap_element)list`
      STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `heap2:((A,data_to_word_memoryProof_tag#B list)heap_element)list` THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 4552 *)
let INJ_NEQ = prove
 (`!(f:(num,num)fmap) (heap:((A,B)heap_element)list) n ptr.
     INJ (FAPPLY f) (FDOM f) {a | isSomeDataElement (heap_lookup a heap)} /\
     n IN FDOM f /\
     ptr IN FDOM f /\
     ~(n = ptr) ==>
     ~(FAPPLY f n = FAPPLY f ptr)`,
  REWRITE_TAC[INJ] THEN MESON_TAC[]);;

(* MP2AUX: thunk cells differ from the other cells that v_inv reads *)
let MP2AUX_heap_el_facts2 = prove
 (`(!i ev (y:(A word_loc)heap_address).
      ~(Bignum i:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                 heap_element = ThunkBlock ev y)) /\
   (!w ev (y:(A word_loc)heap_address).
      ~(Word64Rep (:A) w:(A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element = ThunkBlock ev y)) /\
   (!tag (zs:(A heap_address)list) ev y.
      ~(BlockRep tag zs:(A,data_to_word_memoryProof_tag#B list)heap_element =
        ThunkBlock ev y))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[data_to_word_memoryProof_Bignum_def; Word64Rep_def; ThunkBlock_def;
              BlockRep_def] THEN
  TRY PAIRARG_TAC THEN TRY COND_CASES_TAC THEN SIMP[]);;

(* MP2AUX: a value that is not a thunk cannot become one by changing a ref *)
(* that holds a thunk                                                     *)
let MP2AUX_dest_thunk_insert_thunk = prove
 (`!v (refs:(data_v bvl_ref)spt) ptr m w x.
     data_dest_thunk v refs = data_NotThunk /\
     lookup ptr refs = SOME (bvl_Thunk m w)
     ==> data_dest_thunk v (insert ptr x refs) = data_NotThunk`,
  REWRITE_TAC[MP2AUX_dest_thunk_NotThunk; lookup_insert] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[option_INJ]);;

(* HOL4 line 4564 *)
let v_inv_Thunk_insert_lemma = prove
 (`!conf ev h heap2 ck v1 refs (x:(A word_loc)heap_address) f tf heap ptr v y q.
     v_inv conf v1 refs (x,f,tf,heap) /\
     INJ (FAPPLY f) (FDOM f) {a | isSomeDataElement (heap_lookup a heap)} /\
     ptr IN FDOM f /\
     lookup ptr refs = SOME (bvl_Thunk NotEvaluated v) /\
     heap_lookup (FAPPLY f ptr) heap = SOME (ThunkBlock NotEvaluated y) /\
     v_inv conf v refs (y,f,tf,heap) /\
     (ev = Evaluated ==> data_dest_thunk h refs = data_NotThunk) /\
     heap_store (FAPPLY f ptr) [ThunkBlock ev q] heap = (heap2,T) /\
     heap_lookup (FAPPLY f ptr) heap2 = SOME (ThunkBlock ev q) /\
     (!m x. ~(m = FAPPLY f ptr) /\ heap_lookup m heap = SOME x ==>
            heap_lookup m heap2 = SOME x) /\
     v_inv conf h refs (q,f,tf,heap) ==>
     v_inv_ck ck conf v1 (insert ptr (bvl_Thunk ev h) refs) (x,f,tf,heap2)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `ck:num` THEN
  DISCH_THEN(LABEL_TAC "IH") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["V";"INJ";"PF";"LP";"HL";"VV";"EV";"HS";"HL2";"HM";"VH"] (CONJUNCTS th))) THEN
  SUBGOAL_THEN
   `~(ck = 0) ==>
    !w (z:(A word_loc)heap_address).
      v_inv conf w refs (z,f,tf,heap)
      ==> v_inv_ck (ck - 1) conf w (insert ptr (bvl_Thunk ev h) refs) (z,f,tf,heap2)`
  (LABEL_TAC "IHS") THENL
   [DISCH_TAC THEN REPEAT STRIP_TAC THEN
    USE_THEN "IH" (MP_TAC o SPEC `ck - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`heap:(((A)word_loc,data_to_word_memoryProof_tag#
                                  ((A)word_loc)list)heap_element)list`;
                          `v:data_v`; `y:(A word_loc)heap_address`;
                          `q:(A word_loc)heap_address`] THEN
    ASM_REWRITE_TAC[];
    REMOVE_THEN "IH" (K ALL_TAC)] THEN
  SUBGOAL_THEN
   `!p X. heap_lookup p heap = SOME X /\ ~(X = ThunkBlock NotEvaluated y) ==>
          heap_lookup p
            (heap2:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                    heap_element)list) = SOME X`
  (LABEL_TAC "HX") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "HM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[option_INJ];
    ALL_TAC] THEN
  UNDISCH_TAC `v_inv conf v1 refs (x:(A word_loc)heap_address,f,tf,
    heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
          heap_element)list)` THEN
  STRUCT_CASES_TAC (ISPEC `v1:data_v` (CONJUNCT1 (cases "data_v"))) THEN
  REWRITE_TAC[MP2AUX_v_inv_ck_thms; v_inv_def] THENL
   [(* Number *)
    COND_CASES_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `ptr':num` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "HX" MATCH_MP_TAC THEN ASM_REWRITE_TAC[MP2AUX_heap_el_facts2];
    (* Word64 *)
    STRIP_TAC THEN
    EXISTS_TAC `ptr':num` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "HX" MATCH_MP_TAC THEN ASM_REWRITE_TAC[MP2AUX_heap_el_facts2];
    (* Block *)
    COND_CASES_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ptr':num`; `xs:((A word_loc)heap_address)list`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `ALL2 (\v x. v_inv conf v refs (x,f,tf,
        heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
              heap_element)list)) a2 xs` THEN
      MATCH_MP_TAC MONO_ALL2 THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      USE_THEN "IHS" (fun th -> MATCH_MP_TAC (MP th (ASSUME `~(ck = 0)`))) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "HX" MATCH_MP_TAC THEN ASM_REWRITE_TAC[MP2AUX_heap_el_facts2]];
    (* RefPtr *)
    REWRITE_TAC[lookup_insert] THEN STRIP_TAC THENL
     [SUBGOAL_THEN `~(a1:num = ptr)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
      ASM_CASES_TAC `a1:num = ptr` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[option_INJ; injectivity "bvl_ref"]) THEN
        DISJ2_TAC THEN DISJ1_TAC THEN
        MAP_EVERY EXISTS_TAC [`ev:thunk_mode`; `h:data_v`;
                              `q:(A word_loc)heap_address`] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [DISCH_TAC THEN MATCH_MP_TAC MP2AUX_dest_thunk_insert_thunk THEN
          ASM_MESON_TAC[];
          DISCH_TAC THEN
          USE_THEN "IHS" (fun th -> MATCH_MP_TAC (MP th (ASSUME `~(ck = 0)`))) THEN
          ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN DISJ1_TAC THEN
        MAP_EVERY EXISTS_TAC [`ev':thunk_mode`; `v':data_v`;
                              `y':(A word_loc)heap_address`] THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [DISCH_TAC THEN MATCH_MP_TAC MP2AUX_dest_thunk_insert_thunk THEN
          ASM_MESON_TAC[];
          USE_THEN "HM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC(ISPECL [`f:(num,num)fmap`;
            `heap:(((A)word_loc,data_to_word_memoryProof_tag#
                    ((A)word_loc)list)heap_element)list`] INJ_NEQ) THEN
          ASM_REWRITE_TAC[];
          DISCH_TAC THEN
          USE_THEN "IHS" (fun th -> MATCH_MP_TAC (MP th (ASSUME `~(ck = 0)`))) THEN
          ASM_REWRITE_TAC[]]];
      SUBGOAL_THEN `~(a1:num = ptr)` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `lookup ptr (refs:(data_v bvl_ref)spt) =
                     SOME (bvl_Thunk NotEvaluated v)` THEN
        ASM_REWRITE_TAC[option_INJ; injectivity "bvl_ref"; distinctness "thunk_mode"];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN DISJ2_TAC THEN
      EXISTS_TAC `v':data_v` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MP2AUX_dest_thunk_insert_thunk THEN ASM_MESON_TAC[];
        DISCH_TAC THEN
        USE_THEN "IHS" (fun th -> MATCH_MP_TAC (MP th (ASSUME `~(ck = 0)`))) THEN
        ASM_REWRITE_TAC[]]]]);;

(* HOL4 line 4636 *)
let v_inv_Thunk_insert = prove
 (`!conf ev h heap2 v1 refs (x:(A word_loc)heap_address) f tf heap ptr v y q.
     v_inv conf v1 refs (x,f,tf,heap) /\
     INJ (FAPPLY f) (FDOM f) {a | isSomeDataElement (heap_lookup a heap)} /\
     ptr IN FDOM f /\
     lookup ptr refs = SOME (bvl_Thunk NotEvaluated v) /\
     heap_lookup (FAPPLY f ptr) heap = SOME (ThunkBlock NotEvaluated y) /\
     v_inv conf v refs (y,f,tf,heap) /\
     (ev = Evaluated ==> data_dest_thunk h refs = data_NotThunk) /\
     heap_store (FAPPLY f ptr) [ThunkBlock ev q] heap = (heap2,T) /\
     heap_lookup (FAPPLY f ptr) heap2 = SOME (ThunkBlock ev q) /\
     (!m x. ~(m = FAPPLY f ptr) /\ heap_lookup m heap = SOME x ==>
            heap_lookup m heap2 = SOME x) /\
     v_inv conf h refs (q,f,tf,heap) ==>
     v_inv conf v1 (insert ptr (bvl_Thunk ev h) refs) (x,f,tf,heap2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[v_inv_eq] THEN GEN_TAC THEN
  MATCH_MP_TAC v_inv_Thunk_insert_lemma THEN
  MAP_EVERY EXISTS_TAC [`heap:(((A)word_loc,data_to_word_memoryProof_tag#
                                ((A)word_loc)list)heap_element)list`;
                        `v:data_v`; `y:(A word_loc)heap_address`;
                        `q:(A word_loc)heap_address`] THEN
  ASM_REWRITE_TAC[]);;

(* HOL4 line 4642 *)
let heap_lookup_heap_split = prove
 (`!(heap:((A,B)heap_element)list) a b h1 h2 x.
     heap_split a heap = SOME (h1,h2) /\
     heap_lookup b heap = SOME x ==>
     if b < a then MEM x h1 else MEM x h2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP heap_split_heap_length) THEN
  UNDISCH_TAC `heap_lookup b (heap:((A,B)heap_element)list) = SOME x` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[gc_shared_LESS_IMP_heap_lookup; NOT_LESS_IMP_heap_lookup] THEN
  MESON_TAC[heap_lookup_MEM]);;

(* HOL4 line 4663 *)
let heap_store_heap_lookup = prove
 (`!(heap:((A,B)heap_element)list) heap2 a x n.
     heap_store a x heap = (heap2,T) /\ n < a ==>
     heap_lookup n heap = heap_lookup n heap2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[heap_store_def; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `a = 0` THEN ASM_REWRITE_TAC[LT; PAIR_EQ] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC)
    ASSUME_TAC) THEN
  REWRITE_TAC[heap_lookup_def] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `a - el_length (h:(A,B)heap_element)` THEN
  EXISTS_TAC `x:((A,B)heap_element)list` THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

(* MP2AUX: gen_state_ok is kept by a heap_store after the start a *)
let MP2AUX_heap_store_gen_state_ok = prove
 (`!b (ys:((A,B)heap_element)list) (heap:((A,B)heap_element)list)
    heap2 a k gens.
     heap_store b ys heap = (heap2,T) /\ a <= b /\
     gen_state_ok a k heap gens ==>
     gen_state_ok a k heap2 gens`,
  REPEAT GEN_TAC THEN CASES_ON `gens:gen_state` THEN
  REWRITE_TAC[gen_state_ok_def; GSYM ALL_MEM; gen_start_ok_def] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `s <= b` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:num`) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`heap:((A,B)heap_element)list`;
                 `s:num`; `h1:((A,B)heap_element)list`;
                 `h2:((A,B)heap_element)list`;
                 `b:num`; `ys:((A,B)heap_element)list`;
                 `heap2:((A,B)heap_element)list`]
                heap_split_heap_store) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* HOL4 line 4680 (val) *)
let update_ref_gen_state_ok = prove
 (`!b (t1:(A heap_address)list)
    (heap:((A,data_to_word_memoryProof_tag#B list)heap_element)list)
    heap2 a sp sp1 gens.
     heap_store b [RefBlock t1] heap = (heap2,T) /\ a <= b /\
     gen_state_ok a (a + (sp + sp1)) heap gens ==>
     gen_state_ok a (a + (sp + sp1)) heap2 gens`,
  MESON_TAC[MP2AUX_heap_store_gen_state_ok]);;

(* HOL4 line 4691 *)
let data_up_to_alt = prove
 (`(!n. data_up_to n ([]:((A,B)heap_element)list) <=> n = 0) /\
   (!n (x:(A,B)heap_element) xs.
      data_up_to n (CONS x xs) <=>
      if n = 0 then T else
      if n < el_length x \/ ~isDataElement x then F else
        data_up_to (n - el_length x) xs)`,
  REWRITE_TAC[data_up_to_def; heap_split_def] THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[distinctness "option"; option_INJ; PAIR_EQ] THEN
    MESON_TAC[ALL];
    ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[option_INJ; PAIR_EQ] THENL
     [MESON_TAC[ALL]; ALL_TAC] THEN
    ASM_CASES_TAC `n < el_length (x:(A,B)heap_element)` THEN
    ASM_REWRITE_TAC[distinctness "option"] THEN
    CASES_ON `heap_split (n - el_length (x:(A,B)heap_element))
                (xs:((A,B)heap_element)list)` THEN
    CASE_REWRITE_TAC[distinctness "option"] THENL
     [REWRITE_TAC[COND_ID]; ALL_TAC] THEN
    CASES_ON `a:((A,B)heap_element)list#((A,B)heap_element)list` THEN
    CASE_REWRITE_TAC[option_INJ; PAIR_EQ] THEN
    SIMP[ALL] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]]);;

(* HOL4 line 4704 (val) *)
let update_thunk_gen_state_ok = prove
 (`!b ev (t1:A heap_address)
    (heap:((A,data_to_word_memoryProof_tag#B list)heap_element)list)
    heap2 a sp sp1 gens.
     heap_store b [ThunkBlock ev t1] heap = (heap2,T) /\ a <= b /\
     gen_state_ok a (a + (sp + sp1)) heap gens ==>
     gen_state_ok a (a + (sp + sp1)) heap2 gens`,
  MESON_TAC[MP2AUX_heap_store_gen_state_ok]);;

(* HOL4 line 4715 *)
let data_up_to_heap_store = prove
 (`!(heap:((A,B)heap_element)list) a b heap2 y.
     data_up_to a heap /\ heap_store b [y] heap = (heap2,T) /\
     isDataElement y ==> data_up_to a heap2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[heap_store_def; PAIR_EQ] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a = 0` THEN
  ASM_REWRITE_TAC[data_up_to_def; heap_split_0] THENL
   [MESON_TAC[ALL]; ALL_TAC] THEN
  REWRITE_TAC[GSYM data_up_to_def] THEN
  ASM_CASES_TAC `b = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[APPEND; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) ASSUME_TAC)) THEN
    UNDISCH_TAC `data_up_to a (CONS (h:(A,B)heap_element) t)` THEN
    ASM_REWRITE_TAC[data_up_to_alt] THEN
    UNDISCH_TAC `el_length (h:(A,B)heap_element) = heap_length [y:(A,B)heap_element]` THEN
    REWRITE_TAC[heap_length_def; MAP; SUM; ADD_CLAUSES] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
  PAIRARG_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) ASSUME_TAC)) THEN
  UNDISCH_TAC `data_up_to a (CONS (h:(A,B)heap_element) t)` THEN
  ASM_REWRITE_TAC[data_up_to_alt] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `b - el_length (h:(A,B)heap_element)` THEN
  EXISTS_TAC `y:(A,B)heap_element` THEN ASM_REWRITE_TAC[]);;

(* MP2AUX: the values of all_vs after an insert *)
let MP2AUX_all_vs_insert = prove
 (`!ptr r (refs:(data_v bvl_ref)spt) stack x.
     x IN all_vs (insert ptr r refs) stack ==>
     x IN all_vs refs stack \/ ?y. find_ref r y /\ MEM x (v_all_vs [y])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN
  STRIP_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(lhand(concl th))))) = "lookup"
    with Failure _ -> false)) THEN
  REWRITE_TAC[lookup_insert] THEN COND_CASES_TAC THEN
  REWRITE_TAC[option_INJ] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISJ2_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_MESON_TAC[find_ref_def; MP2AUX_v_all_vs_MEM2_gen];
    ASM_MESON_TAC[];
    DISJ2_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_MESON_TAC[find_ref_def];
    ASM_MESON_TAC[];
    DISJ2_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM v_all_vs_append]) THEN
    ASM_MESON_TAC[find_ref_def; MP2AUX_v_all_vs_MEM2_gen];
    ASM_MESON_TAC[]]);;

(* HOL4 line 4735 *)
let blocks_unique_update_ref = prove
 (`!ts refs xs b ptr stack.
     blocks_unique ts (all_vs refs (APPEND xs (CONS (data_RefPtr b ptr) stack))) ==>
     blocks_unique ts
       (all_vs (insert ptr (bvl_ValueArray xs) refs)
          (APPEND xs (CONS (data_RefPtr b ptr) stack)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MP2AUX_blocks_unique_mono THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP MP2AUX_all_vs_insert) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y:data_v` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[find_ref_def]) THEN
  MATCH_MP_TAC v_in_all_vs THEN EXISTS_TAC `y:data_v` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEM_stack_all_vs THEN ASM_REWRITE_TAC[MEM_APPEND]);;

(* MP2AUX: storing one element of the same length at or after a split   *)
(* point changes only the second part of the split                      *)
let MP2AUX_heap_store_split = prove
 (`!e (heap:((A,B)heap_element)list) h1 h2 p old new heap2.
     heap_split e heap = SOME (h1,h2) /\ heap_lookup p heap = SOME old /\
     e <= p /\ heap_store p [new] heap = (heap2,T)
     ==> ?ha hb. h2 = APPEND ha (CONS old hb) /\
                 heap2 = APPEND h1 (APPEND ha (CONS new hb)) /\
                 heap_split e heap2 = SOME (h1,APPEND ha (CONS new hb))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP heap_lookup_SPLIT) THEN
  DISCH_THEN(X_CHOOSE_THEN `ha:((A,B)heap_element)list`
    (X_CHOOSE_THEN `hb:((A,B)heap_element)list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  UNDISCH_TAC `heap_store (heap_length (ha:((A,B)heap_element)list)) [new]
                 (APPEND ha (CONS old hb)) = (heap2,T)` THEN
  REWRITE_TAC[heap_store_lemma; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  UNDISCH_TAC `heap_split e (APPEND (ha:((A,B)heap_element)list) (CONS old hb)) =
               SOME (h1,h2)` THEN
  ONCE_REWRITE_TAC[heap_split_APPEND_if] THEN
  ASM_CASES_TAC `e < heap_length (ha:((A,B)heap_element)list)` THEN
  ASM_REWRITE_TAC[] THENL
   [CASES_ON `heap_split e (ha:((A,B)heap_element)list)` THEN
    CASE_REWRITE_TAC[] THEN
    CASES_ON `a:((A,B)heap_element)list#((A,B)heap_element)list` THEN
    CASE_REWRITE_TAC[option_INJ; PAIR_EQ] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`y:((A,B)heap_element)list`; `hb:((A,B)heap_element)list`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP heap_split_heap_length) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[APPEND_ASSOC];
    SUBGOAL_THEN `e = heap_length (ha:((A,B)heap_element)list)` SUBST_ALL_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUB_REFL; heap_split_0] THEN
    CASE_REWRITE_TAC[option_INJ; PAIR_EQ; APPEND_NIL] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`[]:((A,B)heap_element)list`; `hb:((A,B)heap_element)list`] THEN
    ASM_REWRITE_TAC[APPEND]]);;

(* MP2AUX: replacing a ref cell in place by another ref cell keeps the     *)
(* heap parts of abs_ml_inv                                               *)
let MP2AUX_update_heap_lemma = prove
 (`!conf a sp sp1 gens limit (roots:(A heap_address)list)
    (heap:((A,data_to_word_memoryProof_tag#B)heap_element)list) heap2 p old new.
     roots_ok roots heap /\ heap_ok heap limit /\
     gc_kind_inv conf a sp sp1 gens heap /\ unused_space_inv a (sp + sp1) heap /\
     heap_lookup p heap = SOME old /\ isDataElement old /\ isRef old /\
     isDataElement new /\ isRef new /\
     heap_store p [new] heap = (heap2,T) /\
     heap_length heap2 = heap_length heap /\
     FILTER isForwardPointer heap2 = FILTER isForwardPointer heap /\
     (!xs l d. MEM (DataElement xs l d) heap2 ==>
               DataElement xs l d = new \/ MEM (DataElement xs l d) heap) /\
     (!a. isSomeDataElement (heap_lookup a heap2) =
          isSomeDataElement (heap_lookup a heap)) /\
     (!m x. ~(m = p) /\ heap_lookup m heap = SOME x ==>
            heap_lookup m heap2 = SOME x) /\
     (!xs l d ptr (u:A). new = DataElement xs l d /\ MEM (Pointer ptr u) xs ==>
                         isSomeDataElement (heap_lookup ptr heap))
     ==> roots_ok roots heap2 /\ heap_ok heap2 limit /\
         gc_kind_inv conf a sp sp1 gens heap2 /\ unused_space_inv a (sp + sp1) heap2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `roots_ok (roots:(A heap_address)list)
                   (heap:((A,data_to_word_memoryProof_tag#B)heap_element)list)` THEN
    ASM_REWRITE_TAC[roots_ok_def];
    UNDISCH_TAC `heap_ok (heap:((A,data_to_word_memoryProof_tag#B)heap_element)list)
                   limit` THEN
    ASM_REWRITE_TAC[heap_ok_def] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `gc_kind_inv conf a sp sp1 gens
                   (heap:((A,data_to_word_memoryProof_tag#B)heap_element)list)` THEN
    REWRITE_TAC[gc_kind_inv_def] THEN
    CASES_ON `data_to_word_config_gc_kind conf` THEN CASE_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `a + sp + sp1 <= p` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`heap:((A,data_to_word_memoryProof_tag#B)heap_element)list`;
                     `a + sp + sp1`; `p:num`] heap_lookup_heap_split) THEN
      DISCH_THEN(MP_TAC o SPECL [`h1:((A,data_to_word_memoryProof_tag#B)heap_element)list`;
        `h2:((A,data_to_word_memoryProof_tag#B)heap_element)list`;
        `old:(A,data_to_word_memoryProof_tag#B)heap_element`]) THEN
      ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
      UNDISCH_TAC `ALL (\x. ~isRef x)
                     (h1:((A,data_to_word_memoryProof_tag#B)heap_element)list)` THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MP2AUX_heap_store_gen_state_ok THEN
      MAP_EVERY EXISTS_TAC [`p:num`; `[new:(A,data_to_word_memoryProof_tag#B)heap_element]`;
                            `heap:((A,data_to_word_memoryProof_tag#B)heap_element)list`] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`a + sp + sp1`;
                   `heap:((A,data_to_word_memoryProof_tag#B)heap_element)list`;
                   `h1:((A,data_to_word_memoryProof_tag#B)heap_element)list`;
                   `h2:((A,data_to_word_memoryProof_tag#B)heap_element)list`;
                   `p:num`; `old:(A,data_to_word_memoryProof_tag#B)heap_element`;
                   `new:(A,data_to_word_memoryProof_tag#B)heap_element`;
                   `heap2:((A,data_to_word_memoryProof_tag#B)heap_element)list`]
                  MP2AUX_heap_store_split) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`h1:((A,data_to_word_memoryProof_tag#B)heap_element)list`;
      `APPEND ha (CONS (new:(A,data_to_word_memoryProof_tag#B)heap_element) hb)`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ALL isRef (h2:((A,data_to_word_memoryProof_tag#B)heap_element)list)` THEN
    ASM_REWRITE_TAC[ALL_APPEND; ALL] THEN SIMP_TAC[];
    UNDISCH_TAC `unused_space_inv a (sp + sp1)
                   (heap:((A,data_to_word_memoryProof_tag#B)heap_element)list)` THEN
    REWRITE_TAC[unused_space_inv_def] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `p:num`)) (concl th))) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `isDataElement (old:(A,data_to_word_memoryProof_tag#B)heap_element)` THEN
      REWRITE_TAC[isDataElement_def] THEN STRIP_TAC THEN
      UNDISCH_TAC `heap_lookup p
        (heap:((A,data_to_word_memoryProof_tag#B)heap_element)list) = SOME old` THEN
      ASM_SIMP_TAC[option_INJ; distinctness "heap_element"];
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[data_up_to_heap_store]]]);;

(* MP2AUX: the root of a RefPtr to a ref that is not a thunk *)
let MP2AUX_v_inv_RefPtr_nonthunk = prove
 (`!conf b n (refs:(data_v bvl_ref)spt) (x:(A word_loc)heap_address) f tf heap r.
     v_inv conf (data_RefPtr b n) refs (x,f,tf,heap) /\
     lookup n refs = SOME r /\ (!ev v. ~(r = bvl_Thunk ev v))
     ==> n IN FDOM f /\ x = Pointer (FAPPLY f n) (ref_ptr_annot conf (SOME r))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[v_inv_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th]) ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[option_INJ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* MP2AUX: a RefPtr of the stack makes its ref reachable *)
let MP2AUX_reachable_refs_root = prove
 (`!stack refs b ptr. MEM (data_RefPtr b ptr) stack ==> reachable_refs stack refs ptr`,
  REWRITE_TAC[reachable_refs_def] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`data_RefPtr b ptr`; `ptr:num`] THEN
  ASM_REWRITE_TAC[get_refs_def; MEM; RTC_REFL]);;

(* MP2AUX: the contents of a ref of refs, for bc_ref_inv *)
let MP2AUX_find_ref_ValueArray = prove
 (`!l (v:A). find_ref (bvl_ValueArray l) v <=> MEM v l`,
  REWRITE_TAC[find_ref_def]);;

(* MP2AUX: the strip of abs_ml_inv used by the update theorems *)
let MP2AUX_ABS_ML_INV_TAC =
  REWRITE_TAC[abs_ml_inv_def; bc_stack_ref_inv_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "HYP")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "RO") (CONJUNCTS_THEN2 (LABEL_TAC "HO")
    (CONJUNCTS_THEN2 (LABEL_TAC "GK") (CONJUNCTS_THEN2 (LABEL_TAC "US") MP_TAC)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(num,num)fmap` (X_CHOOSE_THEN `tf:(num,num)fmap`
    (fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
      (zip ["INJF";"FDF";"INJT";"FDT1";"FDT2";"BE";"BU";"ALL";"REACH"]
           (CONJUNCTS th)))));;

(* HOL4 line 4750 *)
let update_ref_thm = prove
 (`!conf xs b ptr stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts xs1.
     abs_ml_inv conf (APPEND xs (CONS (data_RefPtr b ptr) stack)) refs
       (roots,heap,be,a,sp,sp1,gens) limit ts /\
     lookup ptr refs = SOME (bvl_ValueArray xs1) /\ LENGTH xs = LENGTH xs1 ==>
     ?p rs roots2 heap2 u.
       roots = APPEND rs (CONS (Pointer p u) roots2) /\
       heap_store p [RefBlock rs] heap = (heap2,T) /\
       abs_ml_inv conf (APPEND xs (CONS (data_RefPtr b ptr) stack))
         (insert ptr (bvl_ValueArray xs) refs)
         (roots,heap2,be,a,sp,sp1,gens) limit ts`,
  REPEAT GEN_TAC THEN MP2AUX_ABS_ML_INV_TAC THEN
  USE_THEN "HYP" (CONJUNCTS_THEN2 (LABEL_TAC "LP") (LABEL_TAC "LEN")) THEN
  USE_THEN "ALL" (MP_TAC o MATCH_MP EVERY2_APPEND_CONS) THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `t:(A word_loc)heap_address`
    (X_CHOOSE_THEN `t2:((A word_loc)heap_address)list` MP_TAC))) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["RT";"LT1";"A1";"AP";"A2"] (CONJUNCTS th))) THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `b:bool`; `ptr:num`;
                 `refs:(data_v bvl_ref)spt`; `t:(A word_loc)heap_address`;
                 `f:(num,num)fmap`; `tf:(num,num)fmap`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `bvl_ValueArray xs1:data_v bvl_ref`]
                MP2AUX_v_inv_RefPtr_nonthunk) THEN
  ASM_REWRITE_TAC[distinctness "bvl_ref"; ref_ptr_annot_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "PF") (LABEL_TAC "TEQ")) THEN
  REMOVE_THEN "TEQ" SUBST_ALL_TAC THEN REMOVE_THEN "RT" SUBST_ALL_TAC THEN
  ABBREV_TAC `stk = APPEND xs (CONS (data_RefPtr b ptr) stack)` THEN
  ABBREV_TAC `refs2 = insert ptr (bvl_ValueArray xs) (refs:(data_v bvl_ref)spt)` THEN
  (* the ref ptr *)
  SUBGOAL_THEN
   `?zs:((A word_loc)heap_address)list.
         heap_lookup (FAPPLY f ptr)
           (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                  heap_element)list) = SOME (RefBlock zs) /\
         ALL2 (\z y. v_inv conf y refs (z,f,tf,heap)) zs xs1`
  (X_CHOOSE_THEN `zs:((A word_loc)heap_address)list`
     (CONJUNCTS_THEN2 (LABEL_TAC "HZ") (LABEL_TAC "AZ"))) THENL
   [USE_THEN "REACH" (MP_TAC o SPEC `ptr:num`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MP2AUX_reachable_refs_root THEN
      EXISTS_TAC `b:bool` THEN EXPAND_TAC "stk" THEN REWRITE_TAC[MEM_APPEND; MEM];
      ASM_REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF] THEN CASE_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`zs:((A word_loc)heap_address)list`;
                 `t1:((A word_loc)heap_address)list`; `FAPPLY (f:(num,num)fmap) ptr`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`] heap_store_RefBlock) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    USE_THEN "AZ" (MP_TAC o MATCH_MP EVERY2_LENGTH) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `heap2:((A word_loc,data_to_word_memoryProof_tag#
                                    (A word_loc)list)heap_element)list`
    (fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
      (zip ["HS";"RBI";"HL2";"HLEN";"FIL";"MEMD";"ISD";"HM"] (CONJUNCTS th)))) THEN
  MAP_EVERY EXISTS_TAC [`FAPPLY (f:(num,num)fmap) ptr`; `t1:((A word_loc)heap_address)list`;
    `t2:((A word_loc)heap_address)list`;
    `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
            heap_element)list`; `wl_Word (word 0):(A)word_loc`] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the heap parts *)
  MP_TAC(ISPECL [`conf:data_to_word_config`; `a:num`; `sp:num`; `sp1:num`;
                 `gens:gen_state`; `limit:num`;
                 `APPEND t1 (CONS (Pointer (FAPPLY (f:(num,num)fmap) ptr) (wl_Word (word 0))) t2)
                    :((A word_loc)heap_address)list`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element)list`; `FAPPLY (f:(num,num)fmap) ptr`;
                 `RefBlock zs:(A word_loc,data_to_word_memoryProof_tag#
                               (A word_loc)list)heap_element`;
                 `RefBlock t1:(A word_loc,data_to_word_memoryProof_tag#
                               (A word_loc)list)heap_element`]
                MP2AUX_update_heap_lemma) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[isDataElement_lemmas; RefBlock_def; isRef_def; isMutTag_def;
                    injectivity "heap_element"] THEN
    REWRITE_TAC[GSYM RefBlock_def] THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    USE_THEN "RO" (MP_TAC o REWRITE_RULE[roots_ok_def]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM_APPEND] THEN ASM_MESON_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  (* the refs part *)
  ABBREV_TAC `tf2 = DRESTRICT (tf:(num,num)fmap) (all_ts (refs2:(data_v bvl_ref)spt) (stk:data_v list))` THEN
  SUBGOAL_THEN
   `!v (z:(A word_loc)heap_address).
      v_inv conf v refs (z,f,tf,heap) /\
      (!t. MEM t (v_all_ts v) ==> t IN all_ts refs2 stk) ==>
      v_inv conf v refs2 (z,f,tf2,heap2)`
  (LABEL_TAC "VT") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "tf2" THEN MATCH_MP_TAC v_inv_tf_restrict THEN
    EXISTS_TAC `stk:data_v list` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "refs2" THEN MATCH_MP_TAC v_inv_ValueArray_insert THEN
    EXISTS_TAC `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                      heap_element)list` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf2:(num,num)fmap`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "refs2" THEN REWRITE_TAC[domain_insert] THEN ASM SET_TAC[];
    EXPAND_TAC "tf2" THEN USE_THEN "INJT" MP_TAC THEN
    REWRITE_TAC[INJ; DRESTRICT_DEF; IN_INTER] THEN MESON_TAC[];
    EXPAND_TAC "tf2" THEN REWRITE_TAC[DRESTRICT_DEF] THEN SET_TAC[];
    EXPAND_TAC "tf2" THEN REWRITE_TAC[DRESTRICT_DEF] THEN
    USE_THEN "FDT2" MP_TAC THEN SET_TAC[];
    MAP_EVERY EXPAND_TAC ["refs2"; "stk"] THEN
    MATCH_MP_TAC blocks_unique_update_ref THEN
    USE_THEN "BU" MP_TAC THEN EXPAND_TAC "stk" THEN REWRITE_TAC[];
    MATCH_MP_TAC MP2AUX_ALL2_MEM_IMP THEN
    EXISTS_TAC `\v (x:(A word_loc)heap_address). v_inv conf v refs (x,f,tf,heap)` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "VT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MP2AUX_stack_all_ts];
      USE_THEN "ALL" MP_TAC THEN EXPAND_TAC "stk" THEN REWRITE_TAC[]];
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `reachable_refs stk (refs:(data_v bvl_ref)spt) n` ASSUME_TAC THENL
     [UNDISCH_TAC `reachable_refs stk (refs2:(data_v bvl_ref)spt) n` THEN
      MAP_EVERY EXPAND_TAC ["stk"; "refs2"] THEN REWRITE_TAC[reachable_refs_UPDATE];
      ALL_TAC] THEN
    ASM_CASES_TAC `n:num = ptr` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      EXPAND_TAC "refs2" THEN
      ASM_REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF; lookup_insert] THEN
      CASE_REWRITE_TAC[] THEN EXISTS_TAC `t1:((A word_loc)heap_address)list` THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "A1" (MP_TAC o MATCH_MP EVERY2_SWAP) THEN
      MATCH_MP_TAC EVERY2_IMP_EVERY2 THEN
      REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      USE_THEN "VT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MP2AUX_stack_all_ts THEN
      EXISTS_TAC `y:data_v` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "stk" THEN ASM_REWRITE_TAC[MEM_APPEND];
      ALL_TAC] THEN
    MATCH_MP_TAC MP2AUX_bc_ref_inv_transfer THEN
    MAP_EVERY EXISTS_TAC [`refs:(data_v bvl_ref)spt`; `f:(num,num)fmap`;
      `tf:(num,num)fmap`;
      `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
             heap_element)list`] THEN
    EXPAND_TAC "refs2" THEN ASM_REWRITE_TAC[lookup_insert] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "REACH" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FLOOKUP_DEF] THEN REPEAT STRIP_TAC THEN
      USE_THEN "HM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[COND_RAND; COND_RATOR; option_INJ;
                                  distinctness "option"]) THEN
      FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC(ISPECL [`f:(num,num)fmap`;
        `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
               heap_element)list`] INJ_NEQ) THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      USE_THEN "VT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MP2AUX_find_ref_all_ts THEN
      MAP_EVERY EXISTS_TAC [`n:num`; `r:data_v bvl_ref`; `v:data_v`] THEN
      EXPAND_TAC "refs2" THEN ASM_REWRITE_TAC[lookup_insert];
      EXPAND_TAC "refs2" THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC MP2AUX_dest_thunk_insert THEN
      ASM_REWRITE_TAC[distinctness "bvl_ref"];
      EXPAND_TAC "tf2" THEN REWRITE_TAC[IN_IMAGE; DRESTRICT_DEF; IN_INTER] THEN
      MESON_TAC[]]]);;

(* HOL4 line 4932 *)
let blocks_unique_update_ref1 = prove
 (`!xs ptr refs xs1 ts b stack i.
     0 < LENGTH xs /\
     lookup ptr refs = SOME (bvl_ValueArray xs1) /\
     blocks_unique ts (all_vs refs (APPEND xs (CONS (data_RefPtr b ptr) stack))) ==>
     blocks_unique ts
       (all_vs (insert ptr (bvl_ValueArray (LUPDATE (HD xs) i xs1)) refs)
          (APPEND xs (CONS (data_RefPtr b ptr) stack)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MP2AUX_blocks_unique_mono THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `MEM (HD xs:data_v) xs` ASSUME_TAC THENL
   [UNDISCH_TAC `0 < LENGTH (xs:data_v list)` THEN
    SPEC_TAC(`xs:data_v list`,`xs:data_v list`) THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC[LENGTH; LT_REFL; HD; MEM];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP MP2AUX_all_vs_insert) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y:data_v` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[find_ref_def]) THEN
  MATCH_MP_TAC v_in_all_vs THEN EXISTS_TAC `y:data_v` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP MEM_LUPDATE_E) THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEM_stack_all_vs THEN
    ASM_REWRITE_TAC[MEM_APPEND];
    REWRITE_TAC[all_vs_def; IN_UNION; IN_ELIM_THM] THEN
    ASM_MESON_TAC[MEM_v_all_vs]]);;

(* HOL4 line 4952 *)
let heap_deref_def = cake_def
  `heap_deref a (heap:((A,data_to_word_memoryProof_tag#B list)heap_element)list) =
     match heap_lookup a heap with
       SOME (DataElement xs l (RefTag,[])) -> SOME xs
     | _ -> NONE`;;

(* HOL4 line 4959 *)
let update_ref_thm1 = prove
 (`!conf xs b ptr stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts xs1 i.
     abs_ml_inv conf (APPEND xs (CONS (data_RefPtr b ptr) stack)) refs
       (roots,heap,be,a,sp,sp1,gens) limit ts /\
     lookup ptr refs = SOME (bvl_ValueArray xs1) /\ i < LENGTH xs1 /\
     0 < LENGTH xs
     ==>
     ?p rs roots2 vs1 heap2 u.
       roots = APPEND rs (CONS (Pointer p u) roots2) /\ LENGTH rs = LENGTH xs /\
       heap_deref p heap = SOME vs1 /\ LENGTH vs1 = LENGTH xs1 /\
       heap_store p [RefBlock (LUPDATE (HD rs) i vs1)] heap = (heap2,T) /\
       abs_ml_inv conf (APPEND xs (CONS (data_RefPtr b ptr) stack))
         (insert ptr (bvl_ValueArray (LUPDATE (HD xs) i xs1)) refs)
         (roots,heap2,be,a,sp,sp1,gens) limit ts`,
  REPEAT GEN_TAC THEN MP2AUX_ABS_ML_INV_TAC THEN
  USE_THEN "HYP" (CONJUNCTS_THEN2 (LABEL_TAC "LP")
    (CONJUNCTS_THEN2 (LABEL_TAC "LI") (LABEL_TAC "LX"))) THEN
  USE_THEN "ALL" (MP_TAC o MATCH_MP EVERY2_APPEND_CONS) THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:((A word_loc)heap_address)list`
    (X_CHOOSE_THEN `t:(A word_loc)heap_address`
    (X_CHOOSE_THEN `t2:((A word_loc)heap_address)list` MP_TAC))) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
    (zip ["RT";"LT1";"A1";"AP";"A2"] (CONJUNCTS th))) THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `b:bool`; `ptr:num`;
                 `refs:(data_v bvl_ref)spt`; `t:(A word_loc)heap_address`;
                 `f:(num,num)fmap`; `tf:(num,num)fmap`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `bvl_ValueArray xs1:data_v bvl_ref`]
                MP2AUX_v_inv_RefPtr_nonthunk) THEN
  ASM_REWRITE_TAC[distinctness "bvl_ref"; ref_ptr_annot_def] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "PF") (LABEL_TAC "TEQ")) THEN
  REMOVE_THEN "TEQ" SUBST_ALL_TAC THEN REMOVE_THEN "RT" SUBST_ALL_TAC THEN
  ABBREV_TAC `stk = APPEND xs (CONS (data_RefPtr b ptr) stack)` THEN
  ABBREV_TAC `refs2 = insert ptr (bvl_ValueArray (LUPDATE (HD xs) i xs1))
                         (refs:(data_v bvl_ref)spt)` THEN
  (* the ref ptr *)
  SUBGOAL_THEN
   `?zs:((A word_loc)heap_address)list.
         heap_lookup (FAPPLY f ptr)
           (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                  heap_element)list) = SOME (RefBlock zs) /\
         ALL2 (\z y. v_inv conf y refs (z,f,tf,heap)) zs xs1`
  (X_CHOOSE_THEN `zs:((A word_loc)heap_address)list`
     (CONJUNCTS_THEN2 (LABEL_TAC "HZ") (LABEL_TAC "AZ"))) THENL
   [USE_THEN "REACH" (MP_TAC o SPEC `ptr:num`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MP2AUX_reachable_refs_root THEN
      EXISTS_TAC `b:bool` THEN EXPAND_TAC "stk" THEN REWRITE_TAC[MEM_APPEND; MEM];
      ASM_REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF] THEN CASE_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `MEM (HD t1) (t1:((A word_loc)heap_address)list) /\
                v_inv conf (HD xs) refs (HD t1,f,tf,heap)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`t1:((A word_loc)heap_address)list`; `0`] MEM_EL) THEN
      REWRITE_TAC[EL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      USE_THEN "A1" (MP_TAC o REWRITE_RULE[LIST_REL_EL_EQN]) THEN
      DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT2) THEN ASM_REWRITE_TAC[EL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`zs:((A word_loc)heap_address)list`;
                 `LUPDATE (HD t1) i zs:((A word_loc)heap_address)list`;
                 `FAPPLY (f:(num,num)fmap) ptr`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`] heap_store_RefBlock) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[LENGTH_LUPDATE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `heap2:((A word_loc,data_to_word_memoryProof_tag#
                                    (A word_loc)list)heap_element)list`
    (fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
      (zip ["HS";"RBI";"HL2";"HLEN";"FIL";"MEMD";"ISD";"HM"] (CONJUNCTS th)))) THEN
  MAP_EVERY EXISTS_TAC [`FAPPLY (f:(num,num)fmap) ptr`; `t1:((A word_loc)heap_address)list`;
    `t2:((A word_loc)heap_address)list`; `zs:((A word_loc)heap_address)list`;
    `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
            heap_element)list`; `wl_Word (word 0):(A)word_loc`] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[heap_deref_def; RefBlock_def] THEN CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "AZ" (MP_TAC o MATCH_MP EVERY2_LENGTH) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the heap parts *)
  MP_TAC(ISPECL [`conf:data_to_word_config`; `a:num`; `sp:num`; `sp1:num`;
                 `gens:gen_state`; `limit:num`;
                 `APPEND t1 (CONS (Pointer (FAPPLY (f:(num,num)fmap) ptr) (wl_Word (word 0))) t2)
                    :((A word_loc)heap_address)list`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element)list`; `FAPPLY (f:(num,num)fmap) ptr`;
                 `RefBlock zs:(A word_loc,data_to_word_memoryProof_tag#
                               (A word_loc)list)heap_element`;
                 `RefBlock (LUPDATE (HD t1) i zs):(A word_loc,data_to_word_memoryProof_tag#
                               (A word_loc)list)heap_element`]
                MP2AUX_update_heap_lemma) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[isDataElement_lemmas; RefBlock_def; isRef_def; isMutTag_def;
                    injectivity "heap_element"] THEN
    REWRITE_TAC[GSYM RefBlock_def] THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      is_eq(concl th) && is_var(rhs(concl th)) &&
      type_of(rhs(concl th)) = `:((A word_loc)heap_address)list`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "MEM" with Failure _ -> false)) THEN
    DISCH_THEN(DISJ_CASES_TAC o MATCH_MP MEM_LUPDATE_E) THENL
     [USE_THEN "RO" (MP_TAC o REWRITE_RULE[roots_ok_def]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM_APPEND] THEN ASM_MESON_TAC[];
      USE_THEN "HO" (MP_TAC o REWRITE_RULE[heap_ok_def]) THEN
      DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
      MAP_EVERY EXISTS_TAC [`zs:((A word_loc)heap_address)list`;
        `LENGTH (zs:((A word_loc)heap_address)list)`;
        `(RefTag,[]):data_to_word_memoryProof_tag#((A)word_loc)list`;
        `u:(A)word_loc`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC heap_lookup_MEM THEN
      EXISTS_TAC `FAPPLY (f:(num,num)fmap) ptr` THEN
      USE_THEN "HZ" (fun th -> REWRITE_TAC[REWRITE_RULE[RefBlock_def] th]) THEN
      ASM_REWRITE_TAC[]];
    STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  (* the refs part *)
  ABBREV_TAC `tf2 = DRESTRICT (tf:(num,num)fmap) (all_ts (refs2:(data_v bvl_ref)spt) (stk:data_v list))` THEN
  SUBGOAL_THEN
   `!v (z:(A word_loc)heap_address).
      v_inv conf v refs (z,f,tf,heap) /\
      (!t. MEM t (v_all_ts v) ==> t IN all_ts refs2 stk) ==>
      v_inv conf v refs2 (z,f,tf2,heap2)`
  (LABEL_TAC "VT") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "tf2" THEN MATCH_MP_TAC v_inv_tf_restrict THEN
    EXISTS_TAC `stk:data_v list` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "refs2" THEN MATCH_MP_TAC v_inv_ValueArray_insert THEN
    EXISTS_TAC `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                      heap_element)list` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf2:(num,num)fmap`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "refs2" THEN REWRITE_TAC[domain_insert] THEN ASM SET_TAC[];
    EXPAND_TAC "tf2" THEN USE_THEN "INJT" MP_TAC THEN
    REWRITE_TAC[INJ; DRESTRICT_DEF; IN_INTER] THEN MESON_TAC[];
    EXPAND_TAC "tf2" THEN REWRITE_TAC[DRESTRICT_DEF] THEN SET_TAC[];
    EXPAND_TAC "tf2" THEN REWRITE_TAC[DRESTRICT_DEF] THEN
    USE_THEN "FDT2" MP_TAC THEN SET_TAC[];
    MAP_EVERY EXPAND_TAC ["refs2"; "stk"] THEN
    MATCH_MP_TAC blocks_unique_update_ref1 THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "BU" MP_TAC THEN EXPAND_TAC "stk" THEN REWRITE_TAC[];
    MATCH_MP_TAC MP2AUX_ALL2_MEM_IMP THEN
    EXISTS_TAC `\v (x:(A word_loc)heap_address). v_inv conf v refs (x,f,tf,heap)` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "VT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MP2AUX_stack_all_ts];
      USE_THEN "ALL" MP_TAC THEN EXPAND_TAC "stk" THEN REWRITE_TAC[]];
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `reachable_refs stk (refs:(data_v bvl_ref)spt) n` ASSUME_TAC THENL
     [UNDISCH_TAC `reachable_refs stk (refs2:(data_v bvl_ref)spt) n` THEN
      MAP_EVERY EXPAND_TAC ["stk"; "refs2"] THEN DISCH_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] reachable_refs_UPDATE1) THEN
      EXISTS_TAC `LUPDATE (HD xs) i (xs1:data_v list)` THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN EXISTS_TAC `xs1:data_v list` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP MEM_LUPDATE_E o
        check (fun th -> can (find_term (fun t -> is_const t &&
                 fst(dest_const t) = "LUPDATE")) (concl th) &&
               (try fst(dest_const(fst(strip_comb(concl th)))) = "MEM"
                with Failure _ -> false))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~MEM (v:data_v) xs` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`xs:data_v list`; `0`] MEM_EL) THEN
      REWRITE_TAC[EL] THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `n:num = ptr` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      EXPAND_TAC "refs2" THEN
      ASM_REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF; lookup_insert] THEN
      CASE_REWRITE_TAC[] THEN
      EXISTS_TAC `LUPDATE (HD t1) i zs:((A word_loc)heap_address)list` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\z (y:data_v). v_inv conf y refs (z,f,tf,
                        heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                              heap_element)list)`;
                     `zs:((A word_loc)heap_address)list`; `xs1:data_v list`;
                     `HD t1:(A word_loc)heap_address`; `HD xs:data_v`; `i:num`]
                    EVERY2_LUPDATE_same) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC EVERY2_IMP_EVERY2 THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      USE_THEN "VT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC MP2AUX_find_ref_all_ts THEN
      MAP_EVERY EXISTS_TAC [`ptr:num`;
        `bvl_ValueArray (LUPDATE (HD xs) i xs1):data_v bvl_ref`; `y:data_v`] THEN
      EXPAND_TAC "refs2" THEN ASM_REWRITE_TAC[lookup_insert; find_ref_def];
      ALL_TAC] THEN
    MATCH_MP_TAC MP2AUX_bc_ref_inv_transfer THEN
    MAP_EVERY EXISTS_TAC [`refs:(data_v bvl_ref)spt`; `f:(num,num)fmap`;
      `tf:(num,num)fmap`;
      `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
             heap_element)list`] THEN
    EXPAND_TAC "refs2" THEN ASM_REWRITE_TAC[lookup_insert] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "REACH" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FLOOKUP_DEF] THEN REPEAT STRIP_TAC THEN
      USE_THEN "HM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[COND_RAND; COND_RATOR; option_INJ;
                                  distinctness "option"]) THEN
      FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC(ISPECL [`f:(num,num)fmap`;
        `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
               heap_element)list`] INJ_NEQ) THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      USE_THEN "VT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MP2AUX_find_ref_all_ts THEN
      MAP_EVERY EXISTS_TAC [`n:num`; `r:data_v bvl_ref`; `v:data_v`] THEN
      EXPAND_TAC "refs2" THEN ASM_REWRITE_TAC[lookup_insert];
      EXPAND_TAC "refs2" THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC MP2AUX_dest_thunk_insert THEN
      ASM_REWRITE_TAC[distinctness "bvl_ref"];
      EXPAND_TAC "tf2" THEN REWRITE_TAC[IN_IMAGE; DRESTRICT_DEF; IN_INTER] THEN
      MESON_TAC[]]]);;

(* HOL4 line 5161 *)
let blocks_unique_update_thunk = prove
 (`!ts refs h ptr stack ev.
     blocks_unique ts (all_vs refs (CONS h (CONS (data_RefPtr F ptr) stack))) ==>
     blocks_unique ts
       (all_vs (insert ptr (bvl_Thunk ev h) refs)
          (CONS h (CONS (data_RefPtr F ptr) stack)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MP2AUX_blocks_unique_mono THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP MP2AUX_all_vs_insert) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y:data_v` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[find_ref_def]) THEN
  MATCH_MP_TAC v_in_all_vs THEN EXISTS_TAC `y:data_v` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEM_stack_all_vs THEN ASM_REWRITE_TAC[MEM]);;

(* HOL4 line 5176 *)
let thunk_deref_def = cake_def
  `thunk_deref a (heap:((A,data_to_word_memoryProof_tag#B list)heap_element)list) =
     match heap_lookup a heap with
       SOME (DataElement xs l (ThunkTag NotEvaluated,[])) -> SOME xs
     | _ -> NONE`;;

(* HOL4 line 5183 *)
let update_thunk_thm = prove
 (`!conf h ptr stack refs roots
    (heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
           heap_element)list) be a sp sp1 gens limit ts v ev.
     abs_ml_inv conf (CONS h (CONS (data_RefPtr F ptr) stack)) refs
       (roots,heap,be,a,sp,sp1,gens) limit ts /\
     lookup ptr refs = SOME (bvl_Thunk NotEvaluated v) /\
     (ev = Evaluated ==> data_dest_thunk h refs = data_NotThunk) ==>
     ?p r roots2 v1 heap2 u.
       roots = CONS r (CONS (Pointer p u) roots2) /\
       thunk_deref p heap = SOME v1 /\
       heap_store p [ThunkBlock ev r] heap = (heap2,T) /\
       abs_ml_inv conf (CONS h (CONS (data_RefPtr F ptr) stack))
         (insert ptr (bvl_Thunk ev h) refs)
         (roots,heap2,be,a,sp,sp1,gens) limit ts`,
  REPEAT GEN_TAC THEN MP2AUX_ABS_ML_INV_TAC THEN
  USE_THEN "HYP" (CONJUNCTS_THEN2 (LABEL_TAC "LP") (LABEL_TAC "EV")) THEN
  USE_THEN "ALL" (MP_TAC o REWRITE_RULE[LIST_REL_CONS1]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(A word_loc)heap_address`
    (X_CHOOSE_THEN `rt:((A word_loc)heap_address)list`
     (CONJUNCTS_THEN2 (LABEL_TAC "RT1") (CONJUNCTS_THEN2 (LABEL_TAC "VH0")
       (MP_TAC o REWRITE_RULE[LIST_REL_CONS1]))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(A word_loc)heap_address`
    (X_CHOOSE_THEN `roots2:((A word_loc)heap_address)list`
     (CONJUNCTS_THEN2 (LABEL_TAC "RT2") (CONJUNCTS_THEN2 (LABEL_TAC "AP")
       (LABEL_TAC "A2"))))) THEN
  RULE_ASSUM_TAC BETA_RULE THEN
  SUBGOAL_THEN
   `ptr IN FDOM f /\
    ?y:(A word_loc)heap_address.
      heap_lookup (FAPPLY f ptr) heap = SOME (ThunkBlock NotEvaluated y) /\
      v_inv conf v refs (y,f,tf,heap) /\
      t:(A word_loc)heap_address = Pointer (FAPPLY f ptr) (wl_Word (word 0))`
  (CONJUNCTS_THEN2 (LABEL_TAC "PF") (X_CHOOSE_THEN `y:(A word_loc)heap_address`
     (CONJUNCTS_THEN2 (LABEL_TAC "HY") (CONJUNCTS_THEN2 (LABEL_TAC "VV")
        (LABEL_TAC "TEQ"))))) THENL
   [USE_THEN "AP" (MP_TAC o REWRITE_RULE[v_inv_def]) THEN
    USE_THEN "LP" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[option_INJ; injectivity "bvl_ref"; distinctness "thunk_mode"] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "TEQ" SUBST_ALL_TAC THEN
  REMOVE_THEN "RT2" SUBST_ALL_TAC THEN REMOVE_THEN "RT1" SUBST_ALL_TAC THEN
  ABBREV_TAC `stk = CONS h (CONS (data_RefPtr F ptr) stack)` THEN
  ABBREV_TAC `refs2 = insert ptr (bvl_Thunk ev h) (refs:(data_v bvl_ref)spt)` THEN
  MP_TAC(ISPECL [`FAPPLY (f:(num,num)fmap) ptr`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`; `y:(A word_loc)heap_address`;
                 `ev:thunk_mode`; `r:(A word_loc)heap_address`]
                heap_store_ThunkBlock) THEN
  USE_THEN "HY" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `heap2:((A word_loc,data_to_word_memoryProof_tag#
                                    (A word_loc)list)heap_element)list`
    (fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
      (zip ["HS";"HL2";"HLEN";"FIL";"MEMD";"ISD";"HM"] (CONJUNCTS th)))) THEN
  MAP_EVERY EXISTS_TAC [`FAPPLY (f:(num,num)fmap) ptr`; `r:(A word_loc)heap_address`;
    `roots2:((A word_loc)heap_address)list`; `[y:(A word_loc)heap_address]`;
    `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
            heap_element)list`; `wl_Word (word 0):(A)word_loc`] THEN
  REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [USE_THEN "HY" (fun th -> REWRITE_TAC[thunk_deref_def; th; ThunkBlock_def]) THEN
    CASE_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the heap parts *)
  MP_TAC(ISPECL [`conf:data_to_word_config`; `a:num`; `sp:num`; `sp1:num`;
                 `gens:gen_state`; `limit:num`;
                 `CONS r (CONS (Pointer (FAPPLY (f:(num,num)fmap) ptr) (wl_Word (word 0)))
                         roots2):((A word_loc)heap_address)list`;
                 `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                        heap_element)list`;
                 `heap2:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
                         heap_element)list`; `FAPPLY (f:(num,num)fmap) ptr`;
                 `ThunkBlock NotEvaluated y:(A word_loc,data_to_word_memoryProof_tag#
                               (A word_loc)list)heap_element`;
                 `ThunkBlock ev r:(A word_loc,data_to_word_memoryProof_tag#
                               (A word_loc)list)heap_element`]
                MP2AUX_update_heap_lemma) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[isDataElement_lemmas; ThunkBlock_def; isRef_def; isMutTag_def;
                    injectivity "heap_element"] THEN
    REWRITE_TAC[GSYM ThunkBlock_def] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [MESON_TAC[]; MESON_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    USE_THEN "RO" (MP_TAC o REWRITE_RULE[roots_ok_def]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[MEM];
    STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  (* the refs part *)
  ABBREV_TAC `tf2 = DRESTRICT (tf:(num,num)fmap)
                      (all_ts (refs2:(data_v bvl_ref)spt) (stk:data_v list))` THEN
  SUBGOAL_THEN
   `!w (z:(A word_loc)heap_address).
      v_inv conf w refs (z,f,tf,heap) /\
      (!t. MEM t (v_all_ts w) ==> t IN all_ts refs2 stk) ==>
      v_inv conf w refs2 (z,f,tf2,heap2)`
  (LABEL_TAC "VT") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "tf2" THEN MATCH_MP_TAC v_inv_tf_restrict THEN
    EXISTS_TAC `stk:data_v list` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "refs2" THEN MATCH_MP_TAC v_inv_Thunk_insert THEN
    MAP_EVERY EXISTS_TAC
     [`heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
             heap_element)list`; `v:data_v`; `y:(A word_loc)heap_address`;
      `r:(A word_loc)heap_address`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`f:(num,num)fmap`; `tf2:(num,num)fmap`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "refs2" THEN REWRITE_TAC[domain_insert] THEN ASM SET_TAC[];
    EXPAND_TAC "tf2" THEN USE_THEN "INJT" MP_TAC THEN
    REWRITE_TAC[INJ; DRESTRICT_DEF; IN_INTER] THEN MESON_TAC[];
    EXPAND_TAC "tf2" THEN REWRITE_TAC[DRESTRICT_DEF] THEN SET_TAC[];
    EXPAND_TAC "tf2" THEN REWRITE_TAC[DRESTRICT_DEF] THEN
    USE_THEN "FDT2" MP_TAC THEN SET_TAC[];
    MAP_EVERY EXPAND_TAC ["refs2"; "stk"] THEN
    MATCH_MP_TAC blocks_unique_update_thunk THEN
    USE_THEN "BU" MP_TAC THEN EXPAND_TAC "stk" THEN REWRITE_TAC[];
    MATCH_MP_TAC MP2AUX_ALL2_MEM_IMP THEN
    EXISTS_TAC `\v (x:(A word_loc)heap_address). v_inv conf v refs (x,f,tf,heap)` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "VT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MP2AUX_stack_all_ts];
      USE_THEN "ALL" MP_TAC THEN EXPAND_TAC "stk" THEN REWRITE_TAC[]];
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `reachable_refs stk (refs:(data_v bvl_ref)spt) n` ASSUME_TAC THENL
     [UNDISCH_TAC `reachable_refs stk (refs2:(data_v bvl_ref)spt) n` THEN
      MAP_EVERY EXPAND_TAC ["stk"; "refs2"] THEN REWRITE_TAC[reachable_refs_Thunk_UPDATE];
      ALL_TAC] THEN
    ASM_CASES_TAC `n:num = ptr` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      EXPAND_TAC "refs2" THEN
      ASM_REWRITE_TAC[bc_ref_inv_def; FLOOKUP_DEF; lookup_insert] THEN
      CASE_REWRITE_TAC[] THEN EXISTS_TAC `r:(A word_loc)heap_address` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [DISCH_TAC THEN EXPAND_TAC "refs2" THEN
        MATCH_MP_TAC MP2AUX_dest_thunk_insert_thunk THEN ASM_MESON_TAC[];
        USE_THEN "VT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC MP2AUX_stack_all_ts THEN
        EXISTS_TAC `h:data_v` THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "stk" THEN REWRITE_TAC[MEM]];
      ALL_TAC] THEN
    MATCH_MP_TAC MP2AUX_bc_ref_inv_transfer THEN
    MAP_EVERY EXISTS_TAC [`refs:(data_v bvl_ref)spt`; `f:(num,num)fmap`;
      `tf:(num,num)fmap`;
      `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
             heap_element)list`] THEN
    EXPAND_TAC "refs2" THEN ASM_REWRITE_TAC[lookup_insert] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "REACH" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FLOOKUP_DEF] THEN REPEAT STRIP_TAC THEN
      USE_THEN "HM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[COND_RAND; COND_RATOR; option_INJ;
                                  distinctness "option"]) THEN
      FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC(ISPECL [`f:(num,num)fmap`;
        `heap:((A word_loc,data_to_word_memoryProof_tag#(A word_loc)list)
               heap_element)list`] INJ_NEQ) THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      USE_THEN "VT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MP2AUX_find_ref_all_ts THEN
      MAP_EVERY EXISTS_TAC [`n:num`; `r':data_v bvl_ref`; `v':data_v`] THEN
      EXPAND_TAC "refs2" THEN ASM_REWRITE_TAC[lookup_insert];
      EXPAND_TAC "refs2" THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC MP2AUX_dest_thunk_insert_thunk THEN ASM_MESON_TAC[];
      EXPAND_TAC "tf2" THEN REWRITE_TAC[IN_IMAGE; DRESTRICT_DEF; IN_INTER] THEN
      MESON_TAC[]]]);;

(* HOL4 line 5397 *)
let heap_store_BlockRep_thm = prove
 (`!tag (x:(A heap_address)list) y hb ha.
     LENGTH x = LENGTH y ==>
     heap_store (heap_length ha) [BlockRep tag x]
       (APPEND ha (CONS (BlockRep tag y) hb)
        :((A,data_to_word_memoryProof_tag#B list)heap_element)list) =
     (APPEND ha (CONS (BlockRep tag x) hb),T)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[heap_store_lemma; GSYM APPEND_ASSOC; APPEND; PAIR_EQ] THEN
  ASM_REWRITE_TAC[heap_length_def; MAP; SUM; BlockRep_def; el_length_def;
                  ADD_CLAUSES]);;

(* HOL4 line 5410 *)
let heap_lookup_BlockRep_lemma = prove
 (`!n ha tag (y:(A heap_address)list) hb
    (x:(A,data_to_word_memoryProof_tag#B list)heap_element).
     (heap_lookup n (APPEND ha (CONS (BlockRep tag y) hb)) = SOME x) =
     if n < heap_length ha then heap_lookup n ha = SOME x
     else if n = heap_length ha then x = BlockRep tag y
     else if heap_length ha + (LENGTH y + 1) <= n then
       heap_lookup (n - heap_length ha - (LENGTH y + 1)) hb = SOME x
     else F`,
  REWRITE_TAC[MP2AUX_heap_lookup_middle] THEN
  REWRITE_TAC[BlockRep_def; el_length_def]);;

(* HOL4 line 5433 *)
let heap_store_BlockRep = prove
 (`!(y:(A heap_address)list) h n tag
    (heap:((A,data_to_word_memoryProof_tag#B list)heap_element)list).
     LENGTH y = LENGTH h /\
     heap_lookup n heap = SOME (BlockRep tag y) ==>
     ?heap2. heap_store n [BlockRep tag h] heap = (heap2,T) /\
             heap_lookup n heap2 = SOME (BlockRep tag h) /\
             heap_length heap2 = heap_length heap /\
             FILTER isForwardPointer heap2 = FILTER isForwardPointer heap /\
             (!xs l d.
                MEM (DataElement xs l d) heap2 ==>
                DataElement xs l d = BlockRep tag h \/
                MEM (DataElement xs l d) heap) /\
             (!a. isSomeDataElement (heap_lookup a heap2) =
                  isSomeDataElement (heap_lookup a heap)) /\
             !m x. ~(m = n) /\ heap_lookup m heap = SOME x ==>
                   heap_lookup m heap2 = SOME x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`;
                 `heap:((A,data_to_word_memoryProof_tag#B list)heap_element)list`;
                 `BlockRep tag y:(A,data_to_word_memoryProof_tag#B list)heap_element`;
                 `BlockRep tag h:(A,data_to_word_memoryProof_tag#B list)heap_element`]
                MP2AUX_heap_store_same_data) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[BlockRep_def; el_length_def; isDataElement_def] THEN MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN
      `heap2:((A,data_to_word_memoryProof_tag#B list)heap_element)list`
      STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `heap2:((A,data_to_word_memoryProof_tag#B list)heap_element)list` THEN
    ASM_REWRITE_TAC[]]);;

(* HOL4 line 5469 *)
let v_inv_BlockRep_upd_lemma = prove
 (`!ck conf v1 refs (x:(A word_loc)heap_address) f tf heap heap2 p tag zs.
     v_inv conf v1 refs (x,f,tf,heap) /\
     heap_lookup p heap = SOME (BlockRep tag zs) /\
     (!t. t IN FDOM tf ==> ~(FAPPLY tf t = p)) /\
     (!m y. ~(m = p) /\ heap_lookup m heap = SOME y ==>
            heap_lookup m heap2 = SOME y) ==>
     v_inv_ck ck conf v1 refs (x,f,tf,heap2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`conf:data_to_word_config`; `refs:(data_v bvl_ref)spt`;
                 `refs:(data_v bvl_ref)spt`; `f:(num,num)fmap`; `tf:(num,num)fmap`;
                 `tf:(num,num)fmap`;
                 `heap:(((A)word_loc,data_to_word_memoryProof_tag#((A)word_loc)list)
                        heap_element)list`; `heap2:(((A)word_loc,
                  data_to_word_memoryProof_tag#((A)word_loc)list)heap_element)list`;
                 `UNIV:num->bool`] MP2AUX_v_inv_ck_transfer) THEN
  REWRITE_TAC[IN_UNIV] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MESON_TAC[]) THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `X:(A word_loc,data_to_word_memoryProof_tag#
                                     (A word_loc)list)heap_element`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `heap_lookup p (heap:(((A)word_loc,data_to_word_memoryProof_tag#
                  ((A)word_loc)list)heap_element)list) = SOME X` THEN
    ASM_REWRITE_TAC[option_INJ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FLOOKUP_DEF]) THEN ASM_MESON_TAC[option_INJ;
      distinctness "option"];
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[v_inv_eq]]);;

