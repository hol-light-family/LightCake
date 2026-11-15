(* ========================================================================= *)
(* arm8_config: port of HOL4 compiler/backend/arm8/arm8_configScript.sml     *)
(* (CakeML v3479).                                                           *)
(* Define the compiler configuration for ARMv8.                              *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 rebinds arm8_names_def to its evaluation (CONV_RULE (RAND_CONV     *)
(*   EVAL)): arm8_names_DEF is the definition, arm8_names_def the            *)
(*   evaluated statement (computed with HOL Light Compute).                  *)
(* - The clos_conf and bvl_conf of the backend configuration are, as in      *)
(*   HOL4, the evaluations of clos_to_bvl_default_config and                 *)
(*   bvl_to_bvi_default_config (computed by rewriting); the other parts      *)
(*   are record literals (fields in record order; gc_kind Simple is          *)
(*   data_to_word_Simple).                                                   *)
(* - The target theory arm8_target of the HOL4 Ancestors is outside the      *)
(*   port: nothing of it is used here.                                       *)
(* ========================================================================= *)

needs "compiler/backend/backend.ml";;

prioritize_num();;
type_invention_error := true;;

(* source can use 29 regs (0-28),                                            *)
(* target r18 should be avoided (platform reserved),                         *)
(* target r26 must be avoided (extra encoding register),                     *)
(* target r31 must be avoided (stack pointer),                               *)
(* source 0 must represent r30 (link register),                              *)
(* source 1-4 must be r0-r3 (1st 4 args),                                    *)
(* top three (26-28) must be callee-saved (in r19-r28);                      *)
(* the last two inserts are for well-formedness only                         *)

let arm8_names_DEF = cake_def
  `arm8_names =
     (insert 0 30 o insert 1 0 o insert 2 1 o insert 3 2 o insert 4 3 o insert 18 4 o
      insert 25 29 o insert 26 25 o insert 29 18 o insert 30 26) LN:num spt`;;

(* HOL4: arm8_names_def[compute,allow_rebind] =                             *)
(*   CONV_RULE (RAND_CONV EVAL) arm8_names_def                              *)

let arm8_names_def =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  num_compute_add_convs cs;
  Compute.add_thms [insert_def] cs;
  CONV_RULE (RAND_CONV (REWRITE_CONV[o_THM] THENC Compute.WEAK_CBV_CONV cs))
    arm8_names_DEF;;

let arm8_backend_config_def =
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
    `arm8_backend_config =
       backend_config_REC prim_src_config clos_conf bvl_conf
         (data_to_word_config_REC 4 4 2 32 T F F F F F data_to_word_Simple)
         (word_to_word_config_REC 2 [])
         (word_to_stack_config_REC 0 LN)
         (stack_to_lab_config_REC arm8_names F F)
         (lab_to_target_config_REC LN [] 0 5 NONE [] 104729)
         [] default_tap_config []`);;
