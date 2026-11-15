(* ========================================================================= *)
(* mips_config: port of HOL4 compiler/backend/mips/mips_configScript.sml     *)
(* (CakeML v3479).                                                           *)
(* Define the compiler configuration for MIPS.                               *)
(*                                                                           *)
(* Notes on the rendering:                                                   *)
(* - HOL4 rebinds mips_names_def to its evaluation (CONV_RULE (RAND_CONV     *)
(*   EVAL)): mips_names_DEF is the definition, mips_names_def the            *)
(*   evaluated statement (computed with HOL Light Compute).                  *)
(* - The clos_conf and bvl_conf of the backend configuration are, as in      *)
(*   HOL4, the evaluations of clos_to_bvl_default_config and                 *)
(*   bvl_to_bvi_default_config (computed by rewriting); the other parts      *)
(*   are record literals (fields in record order; gc_kind Simple is          *)
(*   data_to_word_Simple).                                                   *)
(* - The target theory mips_target of the HOL4 Ancestors is outside the      *)
(*   port: nothing of it is used here.                                       *)
(* ========================================================================= *)

needs "compiler/backend/backend.ml";;

prioritize_num();;
type_invention_error := true;;

(* source can use 24 regs (r2-r24,r31),                                      *)
(* target r0 must be avoided (hardcoded to 0),                               *)
(* target r1 must be avoided (used by encoder in asm),                       *)
(* target r25 and r28 are used to set up PIC                                 *)
(* target r29 must be avoided (stack pointer),                               *)
(* target r26-r27 avoided (reserved for OS kernel),                          *)
(* target r30 must be avoided (used by encoder in asm),                      *)
(* source 0 must represent r31 (link register),                              *)
(* source 1-4 must be r4-r7 (1st 4 args),                                    *)
(* top 3 (21-23) must be callee-saved (in 16-23, 28, 30);                    *)
(* the last five inserts just ensure that the mapping is well-formed         *)

let mips_names_DEF = cake_def
  `mips_names =
     (insert 0 31 o insert 1 4 o insert 2 5 o insert 3 6 o insert 4 7 o insert 7 2 o
      insert 5 24 o insert 6 3 o insert 24 0 o insert 31 1) LN:num spt`;;

(* HOL4: mips_names_def[compute,allow_rebind] =                             *)
(*   CONV_RULE (RAND_CONV EVAL) mips_names_def                              *)

let mips_names_def =
  let cs = Compute.bool_compset () in
  Compute.set_skip cs `COND: bool -> A -> A -> A` (Some 1);
  num_compute_add_convs cs;
  Compute.add_thms [insert_def] cs;
  CONV_RULE (RAND_CONV (REWRITE_CONV[o_THM] THENC Compute.WEAK_CBV_CONV cs))
    mips_names_DEF;;

let mips_backend_config_def =
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
    `mips_backend_config =
       backend_config_REC prim_src_config clos_conf bvl_conf
         (data_to_word_config_REC 4 4 2 32 T F F F T F data_to_word_Simple)
         (word_to_word_config_REC 2 [])
         (word_to_stack_config_REC 0 LN)
         (stack_to_lab_config_REC mips_names F F)
         (lab_to_target_config_REC LN [] 0 5 NONE [] 104729)
         [] default_tap_config []`);;
