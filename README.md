# LightCake: CakeML in HOL Light

LightCake is a HOL Light port of [CakeML](https://cakeml.org), the verified implementation
of a dialect of ML, from CakeML's HOL4 development. It is not the CakeML project itself:
for CakeML, its compiler and its HOL4 sources see https://cakeml.org and
https://github.com/CakeML/cakeml. LightCake proves the main correctness theorem of the CakeML
compiler, HOL4's `compilerProofTheory.compile_correct`, and its instance for the ag32
("Silver") target, HOL4's `ag32_configProofTheory.ag32_compile_correct`, in HOL Light from HOL
Light's three axioms only.

The port follows CakeML release v3479 (commit `e8eca63`, 2026-08-24). Every HOL4 script
`foo/barScript.sml` of the dependency closures of these theorems becomes a HOL Light file
`src/foo/bar.ml` with the same definitions and theorems, in the same order, with the same
names (made unique where HOL4 relies on theory-qualified names), and with proofs written
in HOL Light. Long scripts are split into consecutive parts `bar_p1.ml`, `bar_p2.ml`, ...,
and `bar.ml` then loads them.

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

Not ported, because `compile_correct` does not use them and they need theories outside its
closure: the entry points of `compiler.ml` for the Pancake language and for parsing target
names (`compile_pancake` and its 64- and 32-bit versions, `parse_target_64/32`,
`compile_64/32`, `full_compile_64/32`), and two set-relation lemmas of HOL4's
`miscScript.sml` (`domain_rrestrict_subset`, `range_rrestrict_subset`).

## Contents

| directory | files |
|---|---|
| `src/kit/` | the proof kit (see below) |
| `src/hol4/` | the HOL4 library layer (53 files): `ASCIInumbers`, `NTproperties`, `alist`, `bag`, `balanced_map`, `basic`, `binary_ieee`, `bitstring`, `collapse`, `comparison`, `cps`, `finite_map`, `fmsp`, `gcd`, `grammar`, `int_bitwise`, `list`, `llist`, `location`, `lprefix_lub`, `machine_ieee`, `mc_multiword`, `mergesort`, `multiword`, `numposrep`, `path`, `peg`, `pegexec`, `regexp_compiler`, `rich_list`, `rmfmap`, `set_sep`, `simpleSexp`, `simpleSexpPEG`, `simpleSexpParse`, `sorting`, `spt_closure`, `sptree`, `state_transformer`, `string4`, `subst`, `tailrec`, `tcallUnif`, `term`, `ternaryComparisons`, `toto`, `transfer`, `unifDef`, `unifProps`, `vocab`, `walk`, `walkstar`, `words4` |
| `src/misc/` | `misc`, `misc_p1`, `misc_p2`, `misc_p3` |
| `src/basis/pure/` | `mlint`, `mllist`, `mloption`, `mlsexp`, `mlstring`, `mlvector` |
| `src/semantics/` | `ast`, `cmlPtreeConversion`, `evaluate`, `fpSem`, `gram`, `lexer_fun`, `namespace`, `primTypes`, `sem1aux_tfl`, `semanticPrimitives`, `semantics`, `tokenUtils`, `tokens`, `typeSystem` |
| `src/semantics/ffi/` | `ffi` |
| `src/semantics/proofs/` | `evaluateProps`, `gramProps`, `namespaceProps`, `primSemEnv`, `semanticPrimitivesProps`, `semanticsProps`, `typeSound`, `typeSoundInvariants`, `typeSysProps`, `weakening` |
| `src/compiler/parsing/` | `cmlPEG`, `cmlParse`, `fromSexp`, `lexer_impl` |
| `src/compiler/parsing/proofs/` | `cmlNTProps`, `pegComplete`, `pegSound` |
| `src/compiler/inference/` | `infer`, `inferProps`, `infer_t`, `unify` |
| `src/compiler/encoders/asm/` | `asm`, `asmProps`, `asmSem` |
| `src/translator/monadic/monad_base/` | `ml_monadBase` |
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
| `src/pancake/` | `panLang` |

The numbers of files, lines and theorems are in `doc/contents.tsv`. Everything loads in one
fresh HOL Light session with no axioms beyond HOL Light's three (`check.ml` shows it).

## Loading

You need HOL Light from commit `2828953` (10 November 2026) or later; the port uses its core and
`Library/words.ml`, `Library/rstc.ml` and `Library/iter.ml`. Start HOL Light in the root
directory of this repository and load everything with

    loadt "make.ml";;

or check it with

    loadt "check.ml";;

which loads `make.ml`, prints the number of axioms (3) and the list of axioms, checks the
headline theorems (`HEADLINE true`: no hypotheses, conclusions alpha-equivalent to the
statements of `compile_correct_statement.ml`; `HEADLINE_AG32 true`: the same for
`ag32_compile_correct_statement.ml`) and ends with `CHECK_OK`. Everything loads in one
HOL Light session; `check.ml` was run this way with three versions of HOL Light:

| HOL Light | time of `check.ml` |
|---|---|
| commit `1a0c0e6` of jrh13/hol-light (with pull request #215: faster definitions and derived rules) | 1.6 hours |
| commit `55cac39` of jargh/hol-light-dev (pull request #218 of jrh13/hol-light: MESON, X_CHOOSE_TAC and simplifier fixes) | 1.6 hours |
| commit `6dbb775` of jrh13/hol-light | 3.3 hours |

After `loadt "src/prelude.ml";;` any single
file can be loaded on its own with `needs`, for example `needs "semantics/namespace.ml";;`
(paths relative to `src/`).

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
  wordLang, `stack_`, `lab_`, ...), other clashes and constants with common variable names the
  theory name. `doc/names.tsv` maps every HOL4 type, constructor, constant, field and theorem of
  the closure to its HOL Light name; `doc/library_renames.tsv` lists the HOL4 library names that
  had to change.
  HOL4 library notions that HOL Light already has use HOL Light's constants (`EVERY` is `ALL`,
  `LIST_REL` is `ALL2`, `set` is `set_of_list`, `FUNPOW f n x` is `ITER n f x`, ...).

`doc/CONVENTIONS.md` describes the conventions in detail.

## Layout

    make.ml, check.ml     load / check everything (HOL Light started in this directory)
    src/prelude.ml        load path, HOL Light libraries, the kit
    src/kit/              datatypes and case constants, simpset and tactics, pattern
                          compilation, definitions with termination and induction, records,
                          printing
    src/hol4/             the HOL4 library theories CakeML uses
    src/<CakeML path>/    the CakeML theories, at the paths of the CakeML sources
    doc/                  conventions, the naming table, contents

## Credits and licence

The port is BSD-3-Clause licensed (`LICENSE`). Its definitions, theorem statements and
names follow the CakeML sources (BSD-3-Clause, `LICENSE-CakeML`) and, in `src/hol4/`, the
HOL4 library theories (BSD, `LICENSE-HOL4`). An earlier, generated port of the same scope by
Freek Wiedijk (https://github.com/cverified/cakeml-hol-light) was a useful reference for HOL
Light renderings of the CakeML definitions and for the naming table.
