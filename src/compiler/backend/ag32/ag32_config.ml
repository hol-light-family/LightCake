(* ========================================================================= *)
(* ag32_config: port of HOL4 compiler/backend/ag32/ag32_configScript.sml     *)
(* (CakeML v3479).                                                           *)
(* Define the compiler configuration for ag32.                               *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 rebinds ag32_names_def to its evaluation (CONV_RULE (RAND_CONV     *)
(*   EVAL)): ag32_names_DEF is the definition, ag32_names_def the            *)
(*   evaluated statement (computed with HOL Light Compute).                  *)
(* - The clos_conf and bvl_conf of the backend configuration are, as in      *)
(*   HOL4, the evaluations of clos_to_bvl_default_config and                 *)
(*   bvl_to_bvi_default_config (computed by rewriting); the other parts      *)
(*   are record literals (fields in record order; gc_kind Simple is          *)
(*   data_to_word_Simple).                                                   *)
(* - The target theory ag32_target of the HOL4 Ancestors is                  *)
(*   compiler/encoders/ag32/ag32_target.ml; nothing of it is used here       *)
(*   (backend_compile takes the asm configuration as an argument).           *)
(* ========================================================================= *)

needs "compiler/backend/backend.ml";;

prioritize_num();;
type_invention_error := true;;

let ag32_names_DEF = cake_def
  `ag32_names = LN:num spt`;;

(* HOL4: ag32_names_def[compute,allow_rebind] =                             *)
(*   CONV_RULE (RAND_CONV EVAL) ag32_names_def                              *)

let ag32_names_def =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  num_compute_add_convs cs;
  Compute.add_thms [insert_def] cs;
  CONV_RULE (RAND_CONV (REWRITE_CONV[o_THM] THENC Compute.WEAK_CBV_CONV cs))
    ag32_names_DEF;;

let ag32_backend_config_def =
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
    `ag32_backend_config =
       backend_config_REC prim_src_config clos_conf bvl_conf
         (data_to_word_config_REC 0 0 1 20 F F F F F F data_to_word_Simple)
         (word_to_word_config_REC 2 [])
         (word_to_stack_config_REC 0 LN)
         (stack_to_lab_config_REC ag32_names T F)
         (lab_to_target_config_REC LN [] 0 5 NONE [] 104729)
         [] default_tap_config []`);;
