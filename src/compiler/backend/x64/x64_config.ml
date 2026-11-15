(* ========================================================================= *)
(* x64_config: port of HOL4 compiler/backend/x64/x64_configScript.sml        *)
(* (CakeML v3479).                                                           *)
(* Define the compiler configuration for x64.                                *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 rebinds x64_names_def to its evaluation (CONV_RULE (RAND_CONV      *)
(*   EVAL)): x64_names_DEF is the definition, x64_names_def the              *)
(*   evaluated statement (computed with HOL Light Compute).                  *)
(* - The clos_conf and bvl_conf of the backend configuration are, as in      *)
(*   HOL4, the evaluations of clos_to_bvl_default_config and                 *)
(*   bvl_to_bvi_default_config (computed by rewriting); the other parts      *)
(*   are record literals (fields in record order; gc_kind Simple is          *)
(*   data_to_word_Simple).                                                   *)
(* - The target theory x64_target of the HOL4 Ancestors is outside the       *)
(*   port: nothing of it is used here.                                       *)
(* ========================================================================= *)

needs "compiler/backend/backend.ml";;

prioritize_num();;
type_invention_error := true;;

(* 16 regs, must avoid 4 and 5, names:                                       *)
(*   r0=rax, r1=rcx, r2=rdx, r3=rbx, r4=rsp, r5=rbp, r6=rsi,                 *)
(*   r7=rdi, r8=r8, r9, r10, r11, r12, r13, r14, r15                         *)
(* The first six arguments are passed in registers. The first                *)
(* argument (1) is passed in rdi(r7), the second(2) in rsi(r6),              *)
(* the third(3) in rdx(r3), the fourth(4) in rcx(2), the fifth(5)            *)
(* in r8 and the sixth in r9.                                                *)
(* Callee-saved regs: r12-r15, rbx;                                          *)
(* the inserts after the first nine just ensure that the mapping is          *)
(* well-formed                                                               *)

let x64_names_DEF = cake_def
  `x64_names =
     (insert 1 7 o insert 2 6 o insert 3 2 o insert 4 1 o insert 5 8 o insert 6 9 o
      insert 11 14 o insert 12 13 o insert 13 12 o insert 7 3 o insert 8 15 o
      insert 9 11 o insert 14 4 o insert 15 5) LN:num spt`;;

(* HOL4: x64_names_def[compute,allow_rebind] =                              *)
(*   CONV_RULE (RAND_CONV EVAL) x64_names_def                               *)

let x64_names_def =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  num_compute_add_convs cs;
  Compute.add_thms [insert_def] cs;
  CONV_RULE (RAND_CONV (REWRITE_CONV[o_THM] THENC Compute.WEAK_CBV_CONV cs))
    x64_names_DEF;;

let x64_backend_config_def =
  let ev = rand o concl o
           (REWRITE_CONV[clos_to_bvl_default_config_def;
                         clos_known_default_config_def; mk_config_def;
                         default_max_body_size_def; default_inline_factor_def;
                         bvl_to_bvi_default_config_def; bvl_num_stubs_def;
                         data_num_stubs_def; word_num_stubs_def;
                         stack_num_stubs_def] THENC NUM_REDUCE_CONV) in
  let clos_conf = ev `clos_to_bvl_default_config`
  and bvl_conf = ev `bvl_to_bvi_default_config` in
  new_definition
   (vsubst [clos_conf,`clos_conf:clos_to_bvl_config`;
            bvl_conf,`bvl_conf:bvl_to_bvi_config`]
    `x64_backend_config =
       backend_config_REC prim_src_config clos_conf bvl_conf
         (data_to_word_config_REC 4 4 2 32 F T T F F F data_to_word_Simple)
         (word_to_word_config_REC 2 [])
         (word_to_stack_config_REC 0 LN)
         (stack_to_lab_config_REC x64_names T F)
         (lab_to_target_config_REC LN [] 0 5 NONE [] 104729)
         [] default_tap_config []`);;
