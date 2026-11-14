# LightCake: CakeML in HOL Light

LightCake is a HOL Light port of [CakeML](https://cakeml.org), the verified implementation
of a dialect of ML, from CakeML's HOL4 development. It is not the CakeML project itself:
for CakeML, its compiler and its HOL4 sources see https://cakeml.org and
https://github.com/CakeML/cakeml. The aim of LightCake is the main correctness theorem of
the CakeML compiler, HOL4's `compilerProofTheory.compile_correct`, proved in HOL Light from
HOL Light's three axioms only.

The port follows CakeML release v3479 (commit `e8eca63`, 2026-08-24). Every HOL4 script
`foo/barScript.sml` of the dependency closure of `compile_correct` becomes a HOL Light file
`src/foo/bar.ml` with the same definitions and theorems, in the same order, with the same
names (made unique where HOL4 relies on theory-qualified names), and with proofs written
in HOL Light.

## Contents of this snapshot

| part | files |
|---|---|
| proof kit | `src/kit/` (see below) |
| HOL4 library layer | `src/hol4/` (53 files): `ASCIInumbers`, `NTproperties`, `alist`, `bag`, `balanced_map`, `basic`, `binary_ieee`, `bitstring`, `collapse`, `comparison`, `cps`, `finite_map`, `fmsp`, `gcd`, `grammar`, `int_bitwise`, `list`, `llist`, `location`, `lprefix_lub`, `machine_ieee`, `mc_multiword`, `mergesort`, `multiword`, `numposrep`, `path`, `peg`, `pegexec`, `regexp_compiler`, `rich_list`, `rmfmap`, `set_sep`, `simpleSexp`, `simpleSexpPEG`, `simpleSexpParse`, `sorting`, `spt_closure`, `sptree`, `state_transformer`, `string4`, `subst`, `tailrec`, `tcallUnif`, `term`, `ternaryComparisons`, `toto`, `transfer`, `unifDef`, `unifProps`, `vocab`, `walk`, `walkstar`, `words4` |
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
| `src/compiler/backend/semantics/` | `backendProps`, `bviProps`, `bviSem`, `bvlProps`, `bvlSem`, `closProps`, `closSem`, `dataProps`, `dataSem`, `flatProps`, `flatSem`, `labSem`, `stackProps`, `stackSem`, `targetSem`, `wordConvs`, `wordProps`, `wordSem` |
| `src/compiler/backend/gc/` | `copying_gc`, `gc_combined`, `gc_shared`, `gen_gc`, `gen_gc_partial` |
| `src/compiler/backend/reg_alloc/` | `linear_scan`, `parmove`, `reg_alloc` |
| `src/compiler/backend/reg_alloc/proofs/` | `linear_scanProof`, `reg_allocProof` |
| `src/compiler/backend/pattern_matching/` | `pattern_common`, `pattern_comp`, `pattern_exh`, `pattern_semantics` |
| `src/compiler/backend/proofs/` | `bvl_constProof`, `bvl_handleProof`, `bvl_jumpProof`, `clos_callProof`, `clos_constantProof`, `clos_fvsProof`, `clos_knownProps`, `clos_mtiProof`, `clos_numberProof`, `data_to_word_memoryProof_p1`, `data_to_word_memoryProof_p2`, `flat_elimProof`, `flat_patternProof`, `source_evalProof`, `stack_namesProof`, `stack_rawcallProof`, `word_allocProof_p1`, `word_bignumProof`, `word_gcFunctions`, `word_simpProof` |
| `src/compiler/backend/ag32/` | `export_ag32` |
| `src/compiler/backend/arm7/` | `export_arm7` |
| `src/compiler/backend/arm8/` | `export_arm8` |
| `src/compiler/backend/mips/` | `export_mips` |
| `src/compiler/backend/riscv/` | `export_riscv` |
| `src/compiler/backend/x64/` | `export_x64` |

The numbers of files, lines and theorems are in `doc/contents.tsv`. Every file loads in a
fresh HOL Light session with no axioms beyond HOL Light's three (`check.ml` shows it).

## Loading

You need HOL Light; the port uses its core and `Library/words.ml`, `Library/rstc.ml` and
`Library/iter.ml` (tested with HOL Light commit `924faf0`). Start HOL Light in the root
directory of this repository and load everything with

    loadt "make.ml";;

or check it with

    loadt "check.ml";;

which loads `make.ml` and prints the number of axioms (3) and the list of axioms. After
`loadt "src/prelude.ml";;` any single file can be loaded on its own with `needs`, for
example `needs "semantics/namespace.ml";;` (paths relative to `src/`).

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
