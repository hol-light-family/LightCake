# Conventions of LightCake, the HOL Light port of CakeML

## Files
- One HOL Light file per HOL4 script: `cakeml/foo/barScript.sml` becomes `src/foo/bar.ml`,
  with the same blocks in the same order. HOL4 library theories are in `src/hol4/`; the
  vocabulary they share is `src/hol4/vocab.ml`.
- A file starts with a header comment naming the HOL4 script it ports, then the `needs` of the
  files whose names it uses (paths relative to `src/`; `src/prelude.ml` puts `src/` on the load
  path and loads the kit).
- Every definition is made with HOL Light's principles (`define_type`, recursive and inductive
  definitions, `new_specification`), every theorem is proved, and no file adds an axiom.

## Names
- The backend intermediate languages prefix their types, constructors and constants with
  the language: `clos_`, `bvl_`, `bvi_`, `data_`, `flat_`, `stack_`, `lab_`, `asm_`, `target_`,
  and `wl_` for wordLang. The source language (`semantics/`) keeps HOL4's names. Other theories
  prefix a name with the theory name only where it clashes. `doc/names.tsv` is the table
  (columns: file, theory, kind, HOL4 name, HOL Light name, reason).
- Record fields: the accessor of field `f` of record type `r` is `r_f`, its update `r_f_fupd`
  (HOL4 `x with f := v` is `r_f_fupd (K v) x`); the literal `<| f1 := v1; ... |>` is
  `r_REC v1 ...` with the fields in declaration order.
- Definition theorems are `NAME_def`, induction theorems `NAME_ind` (`cake_ind "NAME"`).
- HOL4 library notions use HOL Light's constants where they mean the same (`ALL`, `EX`, `ALL2`,
  `set_of_list`, `UNIONS`, `BUTLAST`, `list_of_seq`, `ITLIST` for `FOLDR` with its arguments
  reordered, `ITER` for `FUNPOW`, `minimal` for `LEAST`, curried `ZIP`); the others keep their HOL4
  names. A HOL4 theorem whose name HOL Light already uses for another statement gets the
  theory name as a prefix (for example `list_MEM_EL`).

## Writing definitions and statements
- `cake_type "ty = C1 num | C2 ty (ty list)"` defines a datatype with its case constant
  `ty_CASE`, `case_eq "ty"` (HOL4's case_eq), the cases theorem and the size function
  `ty_size` (one size argument per type variable; `type_size_def "ty"`, `size_aux_eqs "ty"`).
- HOL4 `case` expressions are written with `match` and compiled into case constants and
  conditionals (HOL4 semantics: each `_` is independent, numeral and other literal patterns are
  equality tests, an unmatched value is `ARB`). `CASE_TERM` compiles a statement:
  `prove(CASE_TERM `...`, tac)`.
- `cake_def tm` for definitions whose termination HOL Light finds itself (structural or tail
  recursion); `cake_def_wf R tac tm` with HOL4's termination relation `R` on the tupled
  arguments (on their sum `INL`/`INR` for mutual recursion), built from `measure`,
  `inv_image` and `LEX`; `tac` proves each termination condition (`TERM_TAC` handles size
  measures).
- `cake_record "r" ["f1","ty1"; ...]` for records; `cake_inductive tm` for inductive relations
  (rules, induction, cases, strong induction).

## Proofs
- Proofs follow the HOL4 proofs, written in HOL Light with the kit's tactics: `SIMP` (simp),
  `FS` (fs), `GVS` (gvs), `RW` (rw), `RVEQ_TAC`, `CASES_ON` (Cases_on), `TOP_CASE_TAC`,
  `CASE_TAC`, `EVERY_CASE_TAC`, `PAIRARG_TAC`, `INDUCT_ON` (Induct_on), `DRULE`, `DXRULE`,
  `DRULE_ALL`, `IRULE`, `IMP_RES_TAC`, `RES_TAC`; `COND_CASE_EQ` and `all_case_eqs()` are HOL4's
  `bool_case_eq` and `AllCaseEqs()`; HOL Light's own tactics are used freely.
- Theorems that HOL4 marks `[simp]` are added to the project simpset with `cake_add_simps`
  when later proofs rely on them.
