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
| HOL4 library layer | `src/hol4/`: `vocab.ml` (shared vocabulary), `list.ml`, `rich_list.ml`, `basic.ml` (combinators, options, pairs, arithmetic, relations, `While`, extra set theory), `finite_map.ml`, `alist.ml`, `sptree.ml` (with `spt_closure.ml`), `words4.ml` (words, bytes, alignment, integer words), `ternaryComparisons.ml`, `toto.ml`, `comparison.ml`, `binary_ieee.ml` and `machine_ieee.ml` (IEEE floating point), `string4.ml`, `numposrep.ml`, `ASCIInumbers.ml`, `bitstring.ml`, `llist.ml`, `lprefix_lub.ml` and `path.ml` (lazy lists), `set_sep.ml`, `sorting.ml`, `mergesort.ml`, `bag.ml`, `location.ml`, `grammar.ml`, `peg.ml`, `pegexec.ml` and `NTproperties.ml` (context-free grammars and PEGs), `simpleSexp.ml`, `simpleSexpPEG.ml`, `simpleSexpParse.ml`, `balanced_map.ml`, `gcd.ml`, `tailrec.ml`, `regexp_compiler.ml` (the vector type) |
| CakeML | `src/misc/` (the misc theory, in three parts); `src/basis/pure/`: `mloption.ml`, `mllist.ml`, `mlstring.ml`; `src/semantics/`: `namespace.ml`, `proofs/namespaceProps.ml`; `src/compiler/backend/`: `backend_common.ml`, `db_vars.ml`, `semantics/backendProps.ml`, `gc/gc_shared.ml`, `reg_alloc/parmove.ml`, `pattern_matching/pattern_common.ml` |

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
  relation, and mutual recursion is allowed. Recursive calls under `MAP`, `ALL`, `EX`, `IMAGE`,
  `ITLIST`, `OPT_MMAP`, the option monad and `==>` get the contexts of HOL4's congruence rules.
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
