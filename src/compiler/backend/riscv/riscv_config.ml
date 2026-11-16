(* ========================================================================= *)
(* riscv_config: port of HOL4 compiler/backend/riscv/riscv_configScript.sml  *)
(* (CakeML v3479).                                                           *)
(* Define the compiler configuration for RISC-V.                             *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 rebinds riscv_names_def to its evaluation (CONV_RULE (RAND_CONV    *)
(*   EVAL)): riscv_names_DEF is the definition, riscv_names_def the          *)
(*   evaluated statement (computed with HOL Light Compute).                  *)
(* - The clos_conf and bvl_conf of the backend configuration are, as in      *)
(*   HOL4, the evaluations of clos_to_bvl_default_config and                 *)
(*   bvl_to_bvi_default_config (computed by rewriting); the other parts      *)
(*   are record literals (fields in record order; gc_kind Simple is          *)
(*   data_to_word_Simple).                                                   *)
(* - The target theory riscv_target of the HOL4 Ancestors is outside the     *)
(*   port: nothing of it is used here.                                       *)
(* ========================================================================= *)

needs "compiler/backend/backend.ml";;

prioritize_num();;
type_invention_error := true;;

(* arguments: 10-17                                                          *)
(*   including return values: 10-11                                          *)
(* temporaries: 5-7, 28-31                                                   *)
(* return address: 1                                                         *)
(* saved regs: 8-9, 18-27                                                    *)
(* 3 = global pointer, 4 = thread pointer                                    *)
(* 0 avoided (hardwired zero)                                                *)
(* 2 avoided (stack pointer)                                                 *)
(* 3 avoided (global pointer)                                                *)
(* 4 avoided (thread pointer)                                                *)
(* 31 avoided (used by encoder)                                              *)
(* 5 avoid regs means 27 regs available for CakeML                           *)
(* constraints:                                                              *)
(*   the last 3 of these (24, 25, 26) must be mapped to callee saved regs    *)
(*   0 must be mapped to link reg (1)                                        *)
(*   1-4 must be mapped to 1st-4st args (10-13);                             *)
(* the last eight inserts make the mapping well-formed                       *)

let riscv_names_DEF = cake_def
  `riscv_names =
     (insert 0 1 o insert 1 10 o insert 2 11 o insert 3 12 o insert 4 13 o insert 10 27 o
      insert 11 28 o insert 12 29 o insert 13 30 o insert 27 0 o insert 28 2 o
      insert 29 3 o insert 30 4) LN:num spt`;;

(* HOL4: riscv_names_def[compute,allow_rebind] =                            *)
(*   CONV_RULE (RAND_CONV EVAL) riscv_names_def                             *)

let riscv_names_def =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  num_compute_add_convs cs;
  Compute.add_thms [insert_def] cs;
  CONV_RULE (RAND_CONV (REWRITE_CONV[o_THM] THENC Compute.WEAK_CBV_CONV cs))
    riscv_names_DEF;;

let riscv_backend_config_def =
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
    `riscv_backend_config =
       backend_config_REC prim_src_config clos_conf bvl_conf
         (data_to_word_config_REC 4 4 2 32 T F F F F F data_to_word_Simple)
         (word_to_word_config_REC 3 [])
         (word_to_stack_config_REC 0 LN)
         (stack_to_lab_config_REC riscv_names F F)
         (lab_to_target_config_REC LN [] 0 5 NONE [] 104729)
         [] default_tap_config []`);;
