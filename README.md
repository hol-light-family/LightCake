# LightCake: CakeML in HOL Light

LightCake is a HOL Light port of [CakeML](https://cakeml.org), the verified implementation
of a dialect of ML, from CakeML's HOL4 development. It is not the CakeML project itself:
for CakeML, its compiler and its HOL4 sources see https://cakeml.org and
https://github.com/CakeML/cakeml. LightCake proves the main correctness theorem of the CakeML
compiler, HOL4's `compilerProofTheory.compile_correct`, and its instance for the ag32
("Silver") target, HOL4's `ag32_configProofTheory.ag32_compile_correct`, in HOL Light from HOL
Light's three axioms only. It also ports the compiler for Pancake, CakeML's low-level language,
with its end-to-end correctness theorem (HOL4's `pan_to_target_compile_semantics`); the logic
part of Candle, the "HOL in HOL" development behind CakeML's verified HOL Light kernel, with the
soundness and consistency theorems of HOL (`proves_sound`, `extends_consistent`,
`hol_consistent` and `hol_light_consistent`); and CakeML's proof-producing translator from HOL
functions to CakeML programs. With the translator it builds the CakeML code of the basis
library and of the Candle kernel, and proves the soundness theorem of the Candle prover (HOL4's
`candle_prover_semanticsTheory.semantics_thm`): if a program running on top of the kernel
neither builds kernel values nor writes on the kernel's output channel itself, every theorem
that it prints through the kernel is provable in HOL, in the context of definitions and axioms
in which the kernel proved it.

The port follows CakeML release v3479 (commit `e8eca63`, 2026-08-24). Every HOL4 script
`foo/barScript.sml` of the dependency closures of these theorems becomes a HOL Light file
`src/foo/bar.ml` with the same definitions and theorems, in the same order, with the same
names (made unique where HOL4 relies on theory-qualified names), and with proofs written
in HOL Light. Long scripts are split into consecutive parts `bar_p1.ml`, `bar_p2.ml`, ...,
and `bar.ml` then loads them. The HOL4 tool libraries that the scripts call, `foo/barLib.sml`,
become OCaml files `src/foo/barLib.ml`. Of the basis scripts that mix CakeML code with its
specifications, only the code part is ported (see the end of the next section).

## The headline theorems

`src/compiler/proofs/compile_correct_statement.ml` is a short file that states the two
end-to-end theorems of HOL4's `compilerProofScript.sml` as HOL Light terms:
`compile_correct_statement` (HOL4's `compile_correct`) and
`compile_correct_safe_for_space_statement` (HOL4's `compile_correct_safe_for_space`). Like
HOL4's theorems they are polymorphic in the machine word size, the target machine and the
state of the foreign function interface. It also defines `config_ok`, the condition on the
compiler configuration and the target machine that both theorems assume, and the two
auxiliary notions of the space-safety version; its header lists every notion the statements
use and the file that defines it.

`src/compiler/proofs/compilerProof.ml` proves them as `compilerProof_compile_correct` and
`compile_correct_safe_for_space`, and fails unless each theorem has no hypotheses and its
conclusion is alpha-equivalent to the corresponding statement term. `check.ml` repeats these
checks after loading everything (see Loading below).

In words, `compile_correct` says: for a compiler configuration and a target machine
configuration satisfying `config_ok`, if compiling a program (a prelude and an input string)
succeeds, then the program has a CakeML semantics (it parses, type-checks and its semantics
is a set of behaviours), and on every machine state in which the compiled code and data are
installed, every behaviour of the machine is one of these behaviours or a prefix of one that
ends because a resource limit of the machine was hit; if compilation fails with a parse or a
type error, the semantics of the program is CannotParse or IllTyped (for assembler and
configuration errors it says nothing). The space-safety version gives equality of the
behaviours when the source program is safe for space.

`src/compiler/backend/ag32/proofs/ag32_compile_correct_statement.ml` states the ag32 theorem in
the same way, as the term `ag32_compile_correct_statement`, and defines
`is_ag32_machine_config`, the condition on the machine configuration. It is the correctness
theorem of the compiler backend (HOL4's `backendProof` `compile_correct`) instantiated with the
ag32 assembler configuration `ag32_config`, the compiler configuration `ag32_backend_config`
and a machine configuration for the ag32 ISA (`src/compiler/encoders/ag32/ag32.ml`, the ISA
definition that HOL4 generates with L3): if the backend compiles a program whose source
semantics does not fail, then every behaviour of an ag32 machine on which the compiled code is
installed is a behaviour of the program, or a prefix of one that ends at a resource limit. The
proof uses the correctness of the ag32 instruction encoder (`ag32_encoder_correct` in
`src/compiler/encoders/ag32/proofs/ag32_targetProof.ml`).
`src/compiler/backend/ag32/proofs/ag32_configProof.ml` proves it as `ag32_compile_correct` and
checks it against the statement in the same way.

`src/pancake/proofs/pan_to_target_statement.ml` states HOL4's `pan_to_target_compile_semantics`
as the term `pan_to_target_compile_semantics_statement`, with the four notions only it uses
(`pancake_good_code`, `pan_installed`, `compile_prog_max` and `option_lt`). In words: for a
compiler configuration and a target machine (other than ag32) satisfying the backend's
conditions, if the Pancake compiler compiles a well-formed program with distinct function
names and parameters, the initial state and memory are laid out as the statement requires, the
compiled code is installed, and the program's semantics from `main` does not fail, then every
behaviour of the machine is the program's behaviour, or a prefix of it that ends at a resource
limit; if the stack bound that the compiler computes is below the machine's stack size, the
machine's behaviour is exactly the program's.
`src/pancake/proofs/pan_to_targetProof.ml` proves it and checks it against the statement in the
same way.

`src/candle/standard/semantics/candle_logic_statement.ml` states four theorems of HOL in HOL
(Kumar, Arthan, Myreen and Owens) as terms and, loaded after them, checks them in the same way:
`proves_sound` (every derivable sequent is valid in every model, for any model `mem` of set
theory), `extends_consistent` (a model of a theory extends to a model of any extension by
definitions, i.e. by updates without new axioms), `hol_consistent` (every such extension of
HOL's standard context, with the axioms of extensionality, choice and infinity, is consistent,
for a set theory with an infinite set) and `hol_light_consistent` (the same for contexts of the
shape that HOL Light actually builds, in which the axioms are interleaved with definitions and
stated in closed form, for the set model of `src/candle/set-theory/setModel.ml`). HOL4's
overloads (`thyof`, `tysof`, `|=`, `models`, ...) are written out, so the statements are longer
than in HOL4, and `===` and `|-` are infix constants, as in HOL Light's `Model/syntax.ml`.

`src/candle/prover/candle_prover_statement.ml` states the soundness theorem of the Candle
prover, HOL4's `semantics_thm` (`candle_prover_semanticsScript.sml`), as the term
`candle_prover_semantics_statement`; its header lists the notions it uses and the files that
define them. `candle_code` is the Candle program: the CakeML code of the basis library followed
by the kernel's datatypes and the kernel module, which the translator produces from the monadic
kernel `src/candle/standard/monadic/holKernel.ml`, proving a certificate theorem for each kernel
function. In words: run `candle_code` followed by any program `prog` that is safe (`safe_dec`:
it neither builds values with the constructors of the kernel's types, such as theorems, nor
makes FFI calls on the kernel's channel), from the initial state, with any evaluation state that
is ok (`candle_eval_state_ok`) and an FFI state with no events yet. If the result is not `Fail`,
every event of the terminating or diverging run is ok (`ok_event`): whatever is written on the
kernel's FFI channel is the printed form (`thm2bytes`) of a theorem that the kernel's logic
proves (`holKernelProof_THM`) in a context that extends HOL's initial context `init_ctxt`. As in
HOL4, that context may contain axioms that the program added through the kernel; the printed
form includes it. The statement keeps HOL4's hypothesis `prog_syntax_ok candle_code`;
`candle_prover_semantics_strong_statement` (not in HOL4) is the same theorem without it, since
LightCake proves the hypothesis by evaluation. `src/candle/prover/candle_prover_semantics.ml`
proves both, as `semantics_thm` and `semantics_thm_strong`, and checks them against the
statements in the same way.

Not ported, because they need parts of CakeML outside the port: the entry points of
`compiler.ml` that choose the target machine from the command line (`parse_target_64/32`,
`compile_64/32`, `compile_pancake_64/32`, `full_compile_64/32`), and two set-relation lemmas of
HOL4's `miscScript.sml` (`domain_rrestrict_subset`, `range_rrestrict_subset`). The entry points
need the assembler configurations `x64_config`, `arm8_config`, `mips_config`, `riscv_config` and
`arm7_config` of HOL4's target theories, which are built on the L3 models of these ISAs (of the
targets only ag32 is ported); `full_compile_64/32` also need the basis library's model of the
file system (`add_stdout` and `add_stderr` of `TextIOProof`, `fastForwardFD` of `fsFFIProps`).

Not yet ported: the characteristic formulae (CF) proper (HOL4's `cfScript.sml`,
`cfAppScript.sml`, `cfNormaliseScript.sml`, `cfTacticsScript.sml`, `cfMainScript.sml` and the
CF tactics of `cfTacticsLib` and its companions), and with them the specifications of the basis
library. Of the basis scripts that mix CakeML code with CF specifications (`basisProg`,
`ListProg`, `mlbasicsProg`, `MarshallingProg`, `DoubleProg`, `SexpProg`, `TextIOProg`, `cfDiv`,
...) only the code part is ported: the definitions, translations and CakeML declarations, in
HOL4's order and with HOL4's names (comments marked M10, the next milestone, name the omitted
theorems). The proof scripts (`TextIOProof`, `CommandLineProof`, `ListProof`, ...) and the FFI
models (`fsFFI`, `fsFFIProps`, `clFFI`, `basis_ffi`) are not ported. The soundness theorem of
the Candle prover needs none of them: it is about the code of the basis library, not its
specifications.

## Contents

| directory | files |
|---|---|
| `src/kit/` | the proof kit (see below) |
| `src/hol4/` | the HOL4 library layer (61 files): `alist`, `alist_tree`, `alist_treeLib`, `ASCIInumbers`, `bag`, `balanced_map`, `balanced_map_part2`, `basic`, `binary_ieee`, `bitstring`, `collapse`, `comparison`, `cps`, `errorLogMonad`, `errorMonad`, `finite_map`, `fmsp`, `gcd`, `grammar`, `int_bitwise`, `itreeTau`, `libext`, `list`, `llist`, `location`, `lprefix_lub`, `machine_ieee`, `mc_multiword`, `mergesort`, `multiword`, `NTproperties`, `numposrep`, `path`, `peg`, `pegexec`, `rat`, `regexp_compiler`, `rich_list`, `rmfmap`, `set_sep`, `simpleSexp`, `simpleSexpParse`, `simpleSexpPEG`, `sorting`, `spt_closure`, `sptree`, `state_transformer`, `string4`, `subst`, `tailrec`, `tcallUnif`, `term`, `ternaryComparisons`, `toto`, `transfer`, `unifDef`, `unifProps`, `vocab`, `walk`, `walkstar`, `words4` |
| `src/misc/` | `misc`, `misc_p1`, `misc_p2`, `misc_p3` |
| `src/basis/pure/` | `mlint`, `mllist`, `mlmap`, `mloption`, `mlprettyprinter`, `mlrat`, `mlset`, `mlsexp`, `mlstring`, `mlvector` |
| `src/semantics/` | `ast`, `cmlPtreeConversion`, `evaluate`, `fpSem`, `gram`, `lexer_fun`, `namespace`, `primTypes`, `sem1aux_tfl`, `semanticPrimitives`, `semantics`, `tokenUtils`, `tokens`, `typeSystem` |
| `src/semantics/ffi/` | `ffi` |
| `src/semantics/proofs/` | `evaluateProps`, `gramProps`, `namespaceProps`, `primSemEnv`, `semanticPrimitivesProps`, `semanticsProps`, `typeSound`, `typeSoundInvariants`, `typeSysProps`, `weakening` |
| `src/compiler/parsing/` | `cmlPEG`, `cmlParse`, `fromSexp`, `lexer_impl` |
| `src/compiler/parsing/proofs/` | `cmlNTProps`, `pegComplete`, `pegSound` |
| `src/compiler/inference/` | `infer`, `inferProps`, `infer_t`, `unify` |
| `src/compiler/encoders/asm/` | `asm`, `asmProps`, `asmSem` |
| `src/translator/monadic/monad_base/` | `ml_monadBase`, `ml_monadBaseLib` |
| `src/compiler/backend/` | `backend`, `backend_common`, `backend_passes`, `bvi`, `bvi_inline`, `bvi_let`, `bvi_tailrec`, `bvi_tmc`, `bvi_to_data`, `bvl`, `bvl_const`, `bvl_handle`, `bvl_inline`, `bvl_jump`, `bvl_to_bvi`, `closLang`, `clos_annotate`, `clos_call`, `clos_fvs`, `clos_interp`, `clos_known`, `clos_letop`, `clos_mti`, `clos_number`, `clos_op`, `clos_ticks`, `clos_to_bvl`, `dataLang`, `data_live`, `data_simp`, `data_space`, `data_to_word`, `db_vars`, `displayLang`, `export`, `flatLang`, `flat_elim`, `flat_pattern`, `flat_to_clos`, `il1aux_mutual`, `jsonLang`, `labLang`, `lab_filter`, `lab_to_target`, `presLang`, `source_let`, `source_to_flat`, `source_to_source`, `stackLang`, `stack_alloc`, `stack_names`, `stack_rawcall`, `stack_remove`, `stack_to_lab`, `wordLang`, `word_alloc`, `word_bignum`, `word_copy`, `word_cse`, `word_depth`, `word_elim`, `word_inst`, `word_remove`, `word_simp`, `word_to_stack`, `word_to_word`, `word_unreach` |
| `src/compiler/backend/semantics/` | `backendProps`, `bviProps`, `bviSem`, `bvlProps`, `bvlSem`, `closProps`, `closSem`, `dataProps`, `dataSem`, `flatProps`, `flatSem`, `labProps`, `labSem`, `stackProps`, `stackSem`, `targetProps`, `targetSem`, `wordConvs`, `wordProps`, `wordSem` |
| `src/compiler/backend/gc/` | `copying_gc`, `gc_combined`, `gc_shared`, `gen_gc`, `gen_gc_partial` |
| `src/compiler/backend/reg_alloc/` | `linear_scan`, `parmove`, `reg_alloc` |
| `src/compiler/backend/reg_alloc/proofs/` | `linear_scanProof`, `reg_allocProof` |
| `src/compiler/backend/pattern_matching/` | `pattern_common`, `pattern_comp`, `pattern_exh`, `pattern_semantics` |
| `src/compiler/backend/proofs/` | `backendProof`, `backendProof_p1`, `backendProof_p2`, `bvi_inlineProof`, `bvi_letProof`, `bvi_tailrecProof`, `bvi_tmcProof`, `bvi_to_dataProof`, `bvl_constProof`, `bvl_handleProof`, `bvl_inlineProof`, `bvl_jumpProof`, `bvl_to_bviProof`, `bvl_to_bviProof_p1`, `bvl_to_bviProof_p2`, `clos_annotateProof`, `clos_callProof`, `clos_constantProof`, `clos_fvsProof`, `clos_interpProof`, `clos_knownProof`, `clos_knownProps`, `clos_letopProof`, `clos_mtiProof`, `clos_numberProof`, `clos_opProof`, `clos_ticksProof`, `clos_to_bvlProof`, `clos_to_bvlProof_p1`, `clos_to_bvlProof_p2`, `clos_to_bvlProof_p3`, `data_liveProof`, `data_simpProof`, `data_spaceProof`, `data_to_wordProof`, `data_to_word_assignProof`, `data_to_word_assignProof_p1`, `data_to_word_assignProof_p2`, `data_to_word_assignProof_p3`, `data_to_word_assignProof_p4`, `data_to_word_assignProof_p5`, `data_to_word_assignProof_p6`, `data_to_word_bignumProof`, `data_to_word_gcProof`, `data_to_word_gcProof_p1`, `data_to_word_gcProof_p2`, `data_to_word_gcProof_p3`, `data_to_word_memoryProof`, `data_to_word_memoryProof_p1`, `data_to_word_memoryProof_p2`, `data_to_word_memoryProof_p3`, `data_to_word_memoryProof_p4`, `data_to_word_memoryProof_p5`, `data_to_word_memoryProof_p6`, `data_to_word_memoryProof_p7`, `flat_elimProof`, `flat_patternProof`, `flat_to_closProof`, `lab_filterProof`, `lab_to_targetProof`, `lab_to_targetProof_p1`, `lab_to_targetProof_p2`, `lab_to_targetProof_p3`, `lab_to_targetProof_p4`, `source_evalProof`, `source_letProof`, `source_to_flatProof`, `source_to_flatProof_p1`, `source_to_flatProof_p2`, `source_to_sourceProof`, `stack_allocProof`, `stack_allocProof_p1`, `stack_allocProof_p2`, `stack_namesProof`, `stack_rawcallProof`, `stack_removeProof`, `stack_to_labProof`, `stack_to_labProof_p1`, `stack_to_labProof_p2`, `wordConvsProof`, `word_allocProof`, `word_allocProof_p1`, `word_allocProof_p2`, `word_bignumProof`, `word_copyProof`, `word_cseProof`, `word_depthProof`, `word_elimProof`, `word_gcFunctions`, `word_instProof`, `word_removeProof`, `word_simpProof`, `word_to_stackProof`, `word_to_stackProof_p1`, `word_to_stackProof_p2`, `word_to_stackProof_p3`, `word_to_stackProof_p4`, `word_to_wordProof`, `word_unreachProof` |
| `src/compiler/` | `compiler` |
| `src/compiler/backend/ag32/` | `ag32_config`, `export_ag32` |
| `src/compiler/backend/ag32/proofs/` | `ag32_compile_correct_statement`, `ag32_configProof` |
| `src/compiler/encoders/ag32/` | `ag32`, `ag32_target` |
| `src/compiler/encoders/ag32/proofs/` | `ag32_targetProof` |
| `src/compiler/backend/arm7/` | `arm7_config`, `export_arm7` |
| `src/compiler/backend/arm8/` | `arm8_config`, `export_arm8` |
| `src/compiler/backend/mips/` | `export_mips`, `mips_config` |
| `src/compiler/backend/riscv/` | `export_riscv`, `riscv_config` |
| `src/compiler/backend/x64/` | `export_x64`, `x64_config` |
| `src/compiler/inference/proofs/` | `envRel`, `inferComplete`, `inferSound`, `infer_eComplete`, `infer_eSound`, `type_dCanon`, `type_eDeterm` |
| `src/compiler/proofs/` | `compile_correct_statement`, `compilerProof` |
| `src/pancake/` | `crepLang`, `crep_arith`, `crep_inline`, `crep_to_loop`, `loopLang`, `loop_call`, `loop_live`, `loop_to_word`, `panLang`, `panStatic`, `pan_common`, `pan_globals`, `pan_passes`, `pan_simp`, `pan_structs`, `pan_to_crep`, `pan_to_target`, `pan_to_word` |
| `src/pancake/parser/` | `panLexer`, `panPEG`, `panPtreeConversion` |
| `src/pancake/semantics/` | `crepProps`, `crepSem`, `loopProps`, `loopSem`, `panProps`, `panSem`, `pan_commonProps`, `pan_itreeProps`, `pan_itreeSem` |
| `src/pancake/proofs/` | `crep_arithProof`, `crep_inlineProof`, `crep_to_loopProof`, `loop_callProof`, `loop_liveProof`, `loop_to_wordProof`, `pan_globalsProof`, `pan_itreeEquivProof`, `pan_simpProof`, `pan_structsProof`, `pan_to_crepProof`, `pan_to_targetProof`, `pan_to_target_statement`, `pan_to_wordProof` |
| `src/candle/set-theory/` | `setModel`, `setSpec` |
| `src/candle/syntax-lib/` | `holSyntaxLib` |
| `src/candle/standard/syntax/` | `holAxiomsSyntax`, `holBoolSyntax`, `holConservative`, `holSyntax`, `holSyntaxExtra`, `holSyntaxExtra_p1`, `holSyntaxExtra_p2`, `holSyntaxExtra_p3`, `holSyntaxExtra_p4`, `holSyntaxExtra_p5`, `holSyntaxExtra_p6`, `holSyntaxExtra_p7`, `holSyntaxExtra_p8` |
| `src/candle/standard/syntax/little_theories/` | `littleTheoriesSyntax`, `littleTheoriesSyntaxNewSystem`, `littleTheoriesSyntaxOldSystem`, `littleTheoriesSyntaxOldSystem_p1`, `littleTheoriesSyntaxOldSystem_p2`, `littleTheoriesSyntaxOldSystem_p3`, `littleTheoriesSyntaxOldSystem_p4`, `littleTheoriesSyntaxOldSystem_p5`, `littleTheoriesSyntaxOldSystem_p6`, `littleTheoriesSyntaxOldSystem_p7` |
| `src/candle/standard/semantics/` | `candle_logic_statement`, `holAxioms`, `holBool`, `holConsistency`, `holExtension`, `holLightConsistency`, `holSemantics`, `holSemanticsExtra`, `holSoundness` |
| `src/translator/` | `evaluate_dec`, `ml_optimise`, `ml_parseLib`, `ml_prog`, `ml_progLib`, `ml_translator`, `ml_translatorLib`, `ml_translatorSyntax`, `std_prelude` |
| `src/translator/monadic/` | `ml_monadStore`, `ml_monadStoreLib`, `ml_monad_translator`, `ml_monad_translatorBase`, `ml_monad_translatorLib`, `ml_monad_translator_interfaceLib` |
| `src/characteristic/` | `cfDiv`, `cfFFIType`, `cfHeaps`, `cfHeapsBase`, `cfLetAuto`, `cfStore` |
| `src/compiler/printing/` | `typeDecToPP` |
| `src/basis/` | `ArrayProg`, `CharProg`, `CommandLineProg`, `DoubleProg`, `HashtableProg`, `IntProg`, `ListProg`, `MapProg`, `Marshalling`, `MarshallingProg`, `OptionProg`, `PrettyPrinterProg`, `RatProg`, `RuntimeProg`, `SetProg`, `SexpProg`, `StringProg`, `TextIOProg`, `VectorProg`, `Word64Prog`, `Word8ArrayProg`, `Word8Prog`, `addPrettyPrintersLib`, `basisFunctionsLib`, `basisProg`, `mlbasicsProg` |
| `src/candle/standard/monadic/` | `holKernel`, `holKernelProof` |
| `src/candle/standard/ml_kernel/` | `ml_hol_kernel_funsProg`, `print_thm`, `runtime_check`, `runtime_checkLib` |
| `src/candle/prover/compute/` | `compute`, `computeProof`, `compute_eval`, `compute_evalProof`, `compute_exec`, `compute_execProof`, `compute_syntax`, `compute_syntaxProof` |
| `src/candle/prover/` | `ast_extras`, `candle_basis_evaluate`, `candle_kernelProg`, `candle_kernel_funs`, `candle_kernel_perms`, `candle_kernel_vals`, `candle_prover_evaluate`, `candle_prover_inv`, `candle_prover_semantics`, `candle_prover_statement`, `perms` |

The numbers of files, lines and theorems are in `doc/contents.tsv`. Everything loads in one
fresh HOL Light session with no axioms beyond HOL Light's three (`check.ml` shows it).

## Loading

You need HOL Light from commit `be9b91e` (24 November 2026, pull request #218) or later; the
port uses its core and `Library/words.ml`, `Library/rstc.ml`, `Library/iter.ml` and
`Library/floor.ml`. Start HOL Light in the root directory of this repository and load everything
with

    loadt "make.ml";;

or check it with

    loadt "check.ml";;

which loads `make.ml`, prints the number of axioms (3) and the list of axioms, checks the
headline theorems (`HEADLINE true`: no hypotheses, conclusions alpha-equivalent to the
statements of `compile_correct_statement.ml`; `HEADLINE_AG32 true`, `HEADLINE_PANCAKE true`,
`HEADLINE_CANDLE true` and `HEADLINE_CANDLE_PROVER true`: the same for
`ag32_compile_correct_statement.ml`, `pan_to_target_statement.ml`, `candle_logic_statement.ml`
and `candle_prover_statement.ml`) and ends with `CHECK_OK`. Everything loads in one HOL Light
session; `check.ml` was run this way with two versions of HOL Light:

| HOL Light | time of `check.ml` |
|---|---|
| commit `096417c` of jrh13/hol-light (master, 24 November 2026) | 2.6 hours |
| commit `29c0925` of jargh/hol-light-dev (pull request #219 of jrh13/hol-light: no uses of `genvar` in the core and its libraries) | 2.6 hours |

After `loadt "src/prelude.ml";;` any single
file can be loaded on its own with `needs`, for example `needs "semantics/namespace.ml";;`
(paths relative to `src/`).

## HOL Light libraries after LightCake

All of LightCake lives in one HOL Light session, with one namespace for its about 15,000
constants, its theorems and its OCaml values, so a library loaded afterwards meets LightCake's
names. LightCake avoids the clashes that matter for HOL Light's main libraries:
- `make.ml` restores your settings of `use_file_raise_failure` and `type_invention_error` at
  its end (the port's files set `type_invention_error` to true), and removes the interface of
  `<<=`, `-->` and `##`, LightCake's notations for `isPREFIX`, `ml_Arrow` and `PAIR_MAP`, as
  HOL Light's own `realax.ml` does for its symbols: HOL Light's libraries use these symbols
  themselves. After `make.ml`, LightCake's theorems print `isPREFIX`, `ml_Arrow` and
  `PAIR_MAP`; `override_interface` brings a notation back.
- Constants that HOL Light's main libraries use as variables or define themselves carry a
  theory prefix: `combin_K` (HOL4's `K`), `PAIR_MAP` (HOL4's `##`), `mlstring_shrink`,
  `pegexec_EV`, `grammar_Lf`, `grammar_Nd`, `grammar_TOK`, `grammar_NT` and `ast_pat_size`.
  LightCake's OCaml values never rebind a top-level name of HOL Light, apart from the kit's
  deliberate replacements: the rewriting front ends (memoised nets, the same results),
  `parse_term`, `g`, `needs` and the METIS wrappers.

With that, the libraries of `Library/`, `Multivariate/`, `Complex/` and `Probability/` load after
LightCake: tested on HOL Light master with `Library/integer.ml`, `prime.ml`, `card.ml`,
`permutations.ml`, `pocklington.ml`, `ringtheory.ml`, `szemeredi.ml`, `poly.ml` and
`bitmatch.ml`, `Multivariate/vectors.ml` and `cauchy.ml`, `Complex/cpoly.ml` and
`Probability/expectation.ml`. A library takes about 1.5 to 2 times as long to load as in a plain
session (up to 5 times for small files): HOL Light's kernel looks up constants in a list, and
LightCake defines about 15,000 of them (the kit's parser avoids most of that cost for
quotations). The exception is `Library/llist.ml`: LightCake's `src/hol4/llist.ml` ports HOL4's
llistTheory, whose type `llist` and constants (`LNIL`, `LCONS`, `LHD`, `LTL`, `LNTH`, `LMAP`,
..., and `THE` and `OPTION_MAP` of `src/hol4/vocab.ml`) have the same names; use LightCake's
instead.

Outside these four directories, several of HOL Light's examples and side developments define
or use names that LightCake also defines, so they do not load after LightCake: `Logic/`,
`Arithmetic/`, `GL/` and `Autoformalization/` (formula constructors such as `Not`, `True`,
`Atom` and `Fn`, and `FV`, `functions`, `language`, `LEX`), `Model/` (HOL Light's own model of
the HOL logic, whose names Candle's syntax shares: `VARIANT`, `TYPE_SUBST`, `ACONV`, `VSUBST`,
`typeof`, `welltyped`, `|-`, ...), `Rqe/` (`Neg`, `Pos`, `Unknown`), `Sieve/` (`sptree`'s
`LN` and `BS`), `Jordan/` (`compose`), `Unity/` and `Functionspaces/` (their own `K`), and some
files of `Examples/` and `100/`. Two effects of the kit stay in force for later files:
`parse_term` reads each `_` of a quotation as its own variable (as HOL4 does), and `g`
compiles HOL4-style `match` expressions.

## How the port is written

- **Case constants.** HOL4's `case x of C1 a => e1 | C2 b => e2` is the constant
  application `ty_CASE x (\a. e1) (\b. e2)`, with rewrite equations, a case-equality theorem
  (HOL4's `AllCaseEqs`) and a cases theorem for every datatype (`cake_type`). Case splits
  are rewriting. Definitions and statements may be written with HOL Light's `match` syntax
  (nested patterns, wildcards, first match wins); `src/kit/pmatch.ml` compiles every match
  into case constants before anything is defined or proved, and goals print with HOL4's
  case syntax.
- **Definitions.** `cake_def` and `cake_def_wf` make recursive definitions from clauses as
  HOL4's `Definition` does: each `_` is its own variable, overlapping clauses mean that the
  first match wins and are completed into the instances HOL4 derives, termination is proved
  automatically (HOL Light's analysis, else a size measure) or with HOL4's termination
  relation, and mutual recursion is allowed. Recursive calls under `case`, `MAP`, `ALL`, `EX`,
  `IMAGE`, `ITLIST`, `OPT_MMAP`, the option monad and `==>` get the contexts of HOL4's
  congruence rules, and the variables are quantified in HOL4's order.
  Every recursive definition gets a HOL4-style induction theorem (`cake_ind`) with one case per
  clause and one hypothesis per recursive call. Records (`cake_record`) get accessors, updates
  and their algebra; size functions are generated for every datatype.
- **Tactics.** HOL4-style tactics over a project simpset: `SIMP`, `FS`, `GVS`, `RW`,
  `CASES_ON`, `TOP_CASE_TAC`, `EVERY_CASE_TAC`, `INDUCT_ON`, `DRULE`, `IRULE`,
  `IMP_RES_TAC`, `PAIRARG_TAC`, ... so that a HOL4 proof can usually be followed step by step.
- **Names.** One global namespace and no overloading: constants of the backend intermediate
  languages carry the language as a prefix (`clos_`, `bvl_`, `bvi_`, `data_`, `wl_` for
  wordLang, `stack_`, `lab_`, ...), other clashes and constants with short or common-word
  names the theory name (`sptree_union`, `misc_the`, `peg_nt`; since update 012 also in the HOL4
  library layer). `doc/names.tsv` maps every HOL4 type, constructor, constant, field and theorem of
  the closure to its HOL Light name; `doc/library_renames.tsv` lists the HOL4 library names that
  had to change. OCaml-level names do not clash with HOL Light's either (see the previous
  section).
  HOL4 library notions that HOL Light already has use HOL Light's constants (`EVERY` is `ALL`,
  `LIST_REL` is `ALL2`, `set` is `set_of_list`, `FUNPOW f n x` is `ITER n f x`, `measure` is
  `MEASURE`, ...). HOL4's rationals are the subtype of HOL Light's reals of the rational numbers
  (`src/hol4/rat.ml`), with HOL4's names and theorems for what the basis library uses.
- **Translations.** The translator (`src/translator/ml_translatorLib.ml`), the monadic
  translator (`src/translator/monadic/`) and `ml_progLib` follow HOL4's algorithms step by step
  (the same certificate theorems, refinement invariants and generated names), so that the basis
  and Candle scripts port one to one, and the CakeML identifiers in the generated programs are
  HOL4's. CakeML source text in the basis scripts is parsed, as in HOL4, by evaluating CakeML's
  verified lexer and parser (`src/translator/ml_parseLib.ml`, with HOL Light's `Compute`).
  Pattern matching is translated from the case constants, not from HOL4's `PMATCH`
  restatements: the bodies of 27 kernel functions in `candle_code` are nested one-level `Mat`s
  where HOL4's have one `Mat` with nested patterns, and a few others may split cases in another
  order than HOL4's. The names, constructors, type stamps and exports of `candle_code` are
  HOL4's, and so is every theorem about it.

`doc/CONVENTIONS.md` describes the conventions in detail.

## Layout

    make.ml, check.ml     load / check everything (HOL Light started in this directory)
    src/prelude.ml        load path, HOL Light libraries, the kit
    src/kit/              datatypes and case constants, simpset and tactics, pattern
                          compilation, definitions with termination and induction, records,
                          printing
    src/hol4/             the HOL4 library theories CakeML uses
    src/<CakeML path>/    the CakeML theories, at the paths of the CakeML sources
    doc/                  conventions, the naming tables, contents

## Credits and licence

The port is BSD-3-Clause licensed (`LICENSE`). Its definitions, theorem statements and
names follow the CakeML sources (BSD-3-Clause, `LICENSE-CakeML`) and, in `src/hol4/`, the
HOL4 library theories (BSD, `LICENSE-HOL4`). An earlier, generated port of the same scope by
Freek Wiedijk (https://github.com/cverified/cakeml-hol-light) was a useful reference for HOL
Light renderings of the CakeML definitions and for the naming table.
