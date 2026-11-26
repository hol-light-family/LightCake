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
  and `wl_` for wordLang. The source language (`semantics/`) keeps HOL4's names. Other theories,
  the HOL4 library theories of `src/hol4/` included, prefix a name with the theory name where it
  clashes, and also where it is short or a common word or variable name (`parmove_step`,
  `clos_annotate_shift`, `infer_read`, `sptree_union`, `misc_the`, `peg_nt`): all files are
  loaded into one session, where a constant would capture every later variable of the same
  name, also in files that do not load it, and a short constant name would take namespace from
  every user of the library. `doc/names.tsv` is the table (columns: file, theory, kind, HOL4
  name, HOL Light name, reason); `doc/library_renames.tsv` lists the HOL4 library names that
  changed.
- Record fields: the accessor of field `f` of record type `r` is `r_f`, its update `r_f_fupd`
  (HOL4 `x with f := v` is `r_f_fupd (combin_K v) x`, HOL4's `K` being `combin_K`); the literal
  `<| f1 := v1; ... |>` is `r_REC v1 ...` with the fields in declaration order.
- OCaml-level names. Every file of the port is loaded into one session, so a top-level OCaml
  binding of the port (a theorem, a tactic, a conversion, a table) replaces every earlier binding
  of the same name for all later files and for the user. No file rebinds a top-level name of
  HOL Light (its core, the module signatures it includes, such as the kernel's, and the
  libraries the port loads): a HOL4 theorem named like a HOL Light value gets its theory prefix
  (`typeSysProps_type_subst`, not `type_subst`, which would hide the kernel function;
  `integer_int_mod`, as `Library/ringtheory.ml` uses `int.ml`'s `int_mod`), and so does a
  theorem whose name a tool function of the port takes (`holSyntaxExtra`'s `trans` is
  `hol_trans`). The kit's deliberate replacements of HOL Light functions are the only
  exceptions: the rewriting front ends (memoised nets, the same results), `parse_term` (each
  `_` is its own variable, and `match` is compiled into case constants), `g`, `needs` (it
  records the file being loaded for the per-file simpsets, so code that wraps `needs` must be
  bound after the prelude) and the METIS wrappers. Tactics of the kit whose HOL4 behaviour
  differs from a HOL Light tactic of the same name get another name (`HOL4_IMP_RES_THEN`,
  `HOL4_SELECT_ELIM_TAC`, `CAKE_REWRITE_TAC`).
- Definition theorems are `NAME_def`, induction theorems `NAME_ind` (`cake_ind "NAME"`).
- HOL4 library notions use HOL Light's constants where they mean the same (`ALL`, `EX`, `ALL2`,
  `set_of_list`, `UNIONS`, `BUTLAST`, `list_of_seq`, `ITLIST` for `FOLDR` with its arguments
  reordered, `ITER` for `FUNPOW`, `minimal` for `LEAST`, `MEASURE` for `measure`, curried
  `ZIP`); the others keep their HOL4 names, prefixed where the rule above says so. A HOL4
  theorem whose name HOL Light already uses for another statement gets the theory name as a
  prefix (for example `list_MEM_EL`).
- HOL4's `Num` is `num_of_int`. They agree on non-negative integers; on negative ones HOL4's
  `Num` is the absolute value and `num_of_int` is unspecified. Every use in the semantics is
  guarded by a sign test, except dataLang's `space_consumed`, whose negative cases compiled
  code never reaches.

## Writing definitions and statements
- `cake_type "ty = C1 num | C2 ty (ty list)"` defines a datatype with its case constant
  `ty_CASE`, `case_eq "ty"` (HOL4's case_eq), the cases theorem and the size function
  `ty_size` (one size argument per type variable; `type_size_def "ty"`, `size_aux_eqs "ty"`).
  The sizes are HOL4's: `list_size f (h::t) = 1 + f h + list_size f t`,
  `pair_size f g (a,b) = 1 + f a + g b` (`min_pair_size` without the `1 +`).
- HOL4 `case` expressions are written with `match` and compiled into case constants and
  conditionals (HOL4 semantics: each `_` is independent, numeral and other literal patterns are
  equality tests, an unmatched value is `ARB`). `CASE_TERM` compiles a statement:
  `prove(CASE_TERM `...`, tac)`. HOL Light's paired `let (a,b) = e in t` becomes
  `pair_CASE e (\a b. t)` in the same way.
- `cake_def tm` for definitions with automatic termination (HOL Light's own analysis, else the
  size of one argument or of all of them, as HOL4's `Define`); `cake_def_wf R tac tm` with
  HOL4's termination relation `R` on the tupled arguments (on their sum `INL`/`INR` for mutual
  recursion), built from `MEASURE` (HOL4's `measure`), `inv_image` and `LEX`; `tac` proves each termination
  condition (`TERM_TAC` handles size measures). `cake_ind "f"` is the induction theorem.
- Clauses follow HOL4: each `_` is a separate variable (`(_:num)` is a typed wildcard);
  overlapping clauses mean that the first match wins and are completed into the instances that
  no earlier clause matches, as HOL4 does (literal patterns other than `0` must not overlap).
  Recursive calls under `MAP`, `ALL`, `EX`, `IMAGE`, `ITLIST`, `OPT_MMAP`, `OPTION_MAP`,
  `OPTION_BIND`, `OPTION_IGNORE_BIND` and `==>` get the contexts of HOL4's congruence rules
  (`MEM y l`, `y IN s`, `o = SOME y`, the antecedent); `cake_register_admissible` adds a rule
  for another constant. A recursive call in an arm of a case expression gets the context
  scrutinee = pattern, as with HOL4's case congruence rules (a rule for each case constant).
  The variables of a definition are quantified in HOL4's order (left to right).
  `cake_def_clauses [`c1`; `c2`]` takes clauses parsed one by one (a variable name may then
  have different types in different clauses, as in HOL4).
- Mutual recursion: the functions of one definition are encoded as one function on the sum of
  their argument tuples; any number of functions is allowed, and the induction theorem has one
  predicate per function.
- `sem1aux_def tm` and `sem1aux_def_wf R tac tm` (`src/semantics/sem1aux_tfl.ml`) take the same
  clauses as `cake_def` and `cake_def_wf` and prove the same clause theorems, with a
  clause-shaped induction theorem, but compile the clauses into one case tree before the
  recursion package sees them, as HOL4's TFL does. They are much
  faster for long definitions with catch-all clauses (the evaluate functions of the semantics).
- `cake_record "r" ["f1","ty1"; ...]` for records; `cake_inductive tm` for inductive relations
  (rules, induction, cases, strong induction).

## Proofs
- Proofs follow the HOL4 proofs, written in HOL Light with the kit's tactics: `SIMP` (simp),
  `FS` (rfs, see below), `RFS` (fs), `GVS` (gvs), `RW` (rw), `RVEQ_TAC`, `CASES_ON` (Cases_on),
  `PAIR_CASES_ON` (PairCases_on), `TOP_CASE_TAC`, `CASE_TAC`, `EVERY_CASE_TAC`, `PAIRARG_TAC`,
  `INDUCT_ON` (Induct_on), `REC_IND_TAC` (recInduct), `DRULE`, `DXRULE`, `DRULE_ALL`, `DRULE_AT`,
  `IRULE`, `IRULE_AT` (irule_at), `ASM_EXISTS_TAC`, `IMP_RES_TAC`, `RES_TAC`, `FULL_RES_TAC`,
  `SUFF_TAC`, `SAME_RUN_TAC` (the qpat_abbrev_tac/qsuff_tac idiom for two runs from equal
  states), `DECIDE_TAC`, `RENAME1` / `RENAME_TAC` (rename1, rename), and the string-quoted
  `QEXISTS_TAC`, `QSUFF_TAC`, `QPAT_X_ASSUM`, `QSPEC_THEN`, `QCASES_ON`; `COND_CASE_EQ` and
  `all_case_eqs()` are HOL4's `bool_case_eq` and `AllCaseEqs()`; the markers `ARITH_ss`, `ONCE th`
  and `ELIM_UNCURRY` can be put in any kit simp list. HOL Light's own tactics are used freely.
- Further HOL4 tactics: `GVS_ASM` (gvs on the assumptions only), `QREFINE_TAC` / `QREFINEL_TAC`
  (qrefine), `DEP_REWRITE_TAC` (dep_rewrite), `ONELINE` (oneline), `NAMED_CASES_ON`
  (namedCases_on), `QINDUCT_ON` (Induct_on, also on a bound variable), `TOP_CASE_NOPAIR_TAC`
  (HOL4's TOP_CASE_TAC), `MATCH_GOALSUB_ABBREV_TAC` / `MATCH_ASMSUB_ABBREV_TAC`
  (qmatch_goalsub_abbrev_tac, qmatch_asmsub_abbrev_tac), `QBY` and `QSUFFICES_BY` (`"t" by tac`,
  `"t" suffices_by tac`), and the simp-list markers `ARITH_LIN_ss` (HOL4's arithmetic
  normalisation, with cut-off subtraction), `NOT_ss` (HOL4's NOT_ss: De Morgan and friends),
  `RECORD_SELFID_ss` (`r with f := r.f = r`), `CONGR th` (HOL4's Cong) and `IGNASM "pat"`
  (HOL4's IgnAsm). The comments in `src/kit/tactics.ml` and `src/kit/simp.ml` describe them.
- More HOL4 tactics and tools: `HOL4_INDUCT_ON` and `HOL4_INDUCT_TAC` (Induct_on and Induct
  with HOL4's goals: the induction hypotheses are assumptions and the arguments are named after
  the variable; `INDUCT_ON` leaves the cases as `MATCH_MP_TAC` gives them), `HOL4_SELECT_ELIM_TAC`
  (HOL4's SELECT_ELIM_TAC; HOL Light's own `SELECT_ELIM_TAC` is a different tactic),
  `cake_enum_bijections` (HOL4's `ty2num` and `num2ty` for an enumeration type, with their
  theorems), and `cake_register_case_type`, `cake_define_case_type` and `cake_register_induction`
  for case types that are not HOL Light datatypes (`itree`, `llist`).
- Quoted terms of the string-quoted tactics are OCaml strings: a backslash followed by a space
  is a space, so write `/\\` for conjunction (the kit reads a lone `/` as `/\` when the string
  does not typecheck otherwise, with a warning), and `\\n` for a lambda over `n`.
- The kit's `FS` simplifies the assumptions oldest first and `RFS` newest first: HOL4's fs takes
  the newest first, so HOL4's fs corresponds to `RFS` and its rfs to `FS`.
- Theorems that HOL4 marks `[simp]` are added to the project simpset with `cake_add_simps`
  when later proofs rely on them.
- The kit's simplifier tactics use HOL Light's simplifier without its `satisfy_prover` (part of
  `basic_ss` since November 2026), as HOL4's default simpsets have no `SATISFY_ss`. HOL Light's
  own `SIMP_TAC` and `ASM_SIMP_TAC` keep it.
- HOL Light's `SIMP_CONV`, `SIMP_TAC`, `ASM_SIMP_TAC` and the other names of its simplifier are
  HOL Light's own: the kit does not redefine them. The kit's tactics (`SIMP`, `FS`, `RFS`, `GVS`,
  `RW`) run HOL Light's simplifier with the kit's strategy, which also gives up the rewriting of
  a bound variable named like a free variable of the context at once, and stops a rewrite chain
  that returns to a term it passed; `CAKE_SIMP_TAC`, `CAKE_ASM_SIMP_TAC` and `CAKE_SIMPLIFY_CONV`
  are HOL Light's `SIMP_TAC`, `ASM_SIMP_TAC` and `SIMPLIFY_CONV` on that strategy, for the goals
  on which HOL Light's simplifier does not terminate. `CAKE_REWRITE_TAC`, `CAKE_REWRITE_CONV` and
  `CAKE_REWRITE_RULE` rewrite with the case-constant equations of the kit's datatypes as well
  as HOL Light's basic rewrites.

## Translations
- The proof-producing translator (`src/translator/ml_translatorLib.ml`, HOL4's
  ml_translatorLib), the monadic translator (`src/translator/monadic/`), the program state of
  `src/translator/ml_progLib.ml` (HOL4's ml_progLib) and the CakeML parser of the basis
  scripts (`src/translator/ml_parseLib.ml`: `add_cakeml` and `process_topdecs` parse CakeML
  text by evaluating CakeML's verified lexer and parser with `Compute`) follow HOL4's
  algorithms step by step: the same certificate theorems, refinement invariants and generated
  names, so that the basis and Candle scripts port one to one.
- HOL Light has no theory database: the translator keeps its state in OCaml tables, and a
  translation file starts with `translation_extends "THY";;` (or `translation_reset ();;`) and
  ends with `finalise_translation ();;`.
- Generated names are HOL4's: per translated function `f` the closure `f_v` with `f_v_def`,
  the certificate `f_v_thm`, the side condition `f_side` with `f_side_def`; per registered type
  the refinement invariant `FOO_TYPE` with `FOO_TYPE_def`; ml_progLib's abbreviations
  `THY_env_N` and `THY_st_N`. All files share one session, so if a generated name is taken,
  every name generated for that function gets the theory name as a prefix
  (`ListProg_filter_v`: sptree has `filter_v`), and a side-condition constant made a second
  time under the same HOL4 name becomes `THY_f_side` (`StringProg_collate_aux_side`; the
  theorem keeps HOL4's name). `doc/reserved_generated.tsv` lists the generated names that
  later files use.
- The CakeML identifiers (the names of values, constructors and modules in generated programs)
  are HOL4's, whatever the HOL Light names: `doc/ident_map.tsv` maps the HOL Light names that
  differ back to them.
- Pattern matching is translated from the case constants (`ty_CASE`): nested patterns give
  nested one-level `Mat` expressions, where HOL4's PMATCH route gives one `Mat` with nested
  patterns (PMATCH is not ported). The Candle kernel's code differs from HOL4's in this way in
  27 functions; the theorems about it keep HOL4's statements.
- HOL Light gives no value to the cases that no clause of a definition covers: a partial
  function's certificate has the precondition `pattern_complete`, as HOL4's has when TFL's
  definition contains `ARB`. Bound variables that the translator invents are named
  `v1`, `v2`, ... (HOL4's names contain a session counter). HOL4's `case v of () => e` is
  `one_CASE v e`.
- The CF heap notation keeps HOL4's infixes where HOL Light's lexer takes them (`*+`, `==>>`,
  `==+>`, `~~>>`, `~~>`); HOL4's `==v>`, `==e>`, `==f>`, `==d>` are the constants
  `SEP_IMPPOSTv`, `SEP_IMPPOSTe`, `SEP_IMPPOSTf`, `SEP_IMPPOSTd`.
- Comments of the translator files refer to the design decisions of this part of the port:
  D2 (a basis script that mixes CakeML code with CF specifications is ported in its code part;
  the specifications are left for the next milestone, M10), D4 (the CakeML identifiers are
  HOL4's), D5 (pattern matching is translated from the case constants; PMATCH is not ported),
  D6 (`rat` is a subtype of `real`), D8 (the corollary `semantics_thm_strong` without the
  hypothesis `prog_syntax_ok candle_code`).
