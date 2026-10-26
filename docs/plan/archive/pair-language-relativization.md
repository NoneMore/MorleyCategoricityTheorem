# Pair Language and Formula Relativization

## Implementation status

Implemented in [PR #42](https://github.com/NoneMore/MorleyCategoricityTheorem/pull/42): the pair
language, the pair structures, relativization `φ ↦ φ^U`, and its semantics are in
[`PairLanguage.lean`](../../../MorleyCategoricityTheorem/ModelTheory/PairLanguage.lean).

This archived plan preserves the pre-implementation investigation and design. Statements below
about unproved obligations, plan-only scope, and future validation describe that earlier stage;
they are not remaining tasks. Elementary-pair axiomatization remains a separate capability.

## Intent and scope

Implement the reusable pair-language infrastructure needed by the blueprint's
[`def:pair-language`](../../../blueprint/src/content.tex) and
[`lem:pair-relativization`](../../../blueprint/src/content.tex). Given an
`L`-structure `M` and an `L`-substructure `S`, form the language
`L₀ = L ∪ {U}` and the pair structure `(M, S)`, with `U` interpreted as
the underlying set of `S`. Relativization `φ ↦ φ^U` restricts each
quantifier to `U`.

The deliverable is the semantics of this construction for bounded formulas
and ordinary formulas, including a transport theorem for arbitrary
`L`-embeddings. The elementary-embedding statement used by the blueprint
is a specialization, **not** the fundamental proof.

This capability ends at formula relativization. In particular,
[`lem:elementary-pair-axiomatization`](../../../blueprint/src/content.tex) is
a separate blueprint node and is not included here. No edits to
`blueprint/` are authorized by this plan.

## Experiment evidence and current boundary

The source of this design is
[`experiment/pair-relativization`](https://github.com/NoneMore/MorleyCategoricityTheorem/tree/experiment/pair-relativization)
at commit
[`31269c9f0c62f93ccf41c5f1f6df933161ef6e7e`](https://github.com/NoneMore/MorleyCategoricityTheorem/commit/31269c9f0c62f93ccf41c5f1f6df933161ef6e7e).
At the time of review, comparison against `main`
(`4005e89da6edbf87c10cf1c9c95587a8b3522004`) shows one additional
commit, two affected files:

- New `MorleyCategoricityTheorem/ModelTheory/PairLanguage.lean`
  (266 added lines in the compare view).
- One import in `MorleyCategoricityTheorem.lean`.

The experimental file has definitions and proof terms for the API below
and contains no explicit `sorry` or `axiom` declarations. This is **source
inspection**, not proof of a successful full build: no GitHub Actions
checks/runs were found for that experimental commit, and the Lean build
has not been rerun as part of this review. Do not describe the result as
validated until the target branch passes the required checks. In
particular, source inspection alone cannot exclude axioms hidden in
dependencies.

The experiment demonstrates that:

1. The pair-language construction can use `Language.sum` with a
   one-unary-predicate language.
2. Semantics of `φ^U` can be proved for any `L.Substructure M`, without
   assuming elementarity.
3. For `f : M ↪[L] N`, the pair `(N, range f)` realizes `φ^U` at
   `f ∘ a` precisely when `M` realizes `φ` at `a`. The transport uses
   `f.equivRange : M ≃[L] range f`, not an elementary-embedding argument.
4. The elementary case follows from `e.toEmbedding` and is already the
   appropriate public bridge to the blueprint.

These observations fix the initial public API; they do not establish
elementary-pair axiomatization or any Vaughtian-pair transfer theorem.

## Existing API and design choices

The repository pins Lean `v4.34.1` and uses Mathlib. The experimental
module imports `Mathlib.ModelTheory.ElementaryMaps`, and relies on:

| Existing interface | Purpose |
| --- | --- |
| `Language.sum`, `LHom.sumInl` | Extend `L` by one independent relation symbol and include old symbols. |
| `L.Substructure M` | Ensure that the `U`-part supports the original functions and relations. |
| `BoundedFormula.mapTermRel` | Recurse over terms, relations, connectives, and quantifiers. |
| `BoundedFormula.Realize`, `Formula.Realize` | State semantics first for arbitrary binder depth, then at depth zero. |
| `pairStructure_isExpansionOn_sumInl` | Tell Mathlib that the `L`-reduct of the pair is its original structure. |
| `Embedding.equivRange`, `StrongHomClass.realize_formula` | Transport satisfaction from the induced range substructure back to the source. |

### Language and structure

Keep the experimental representation unless validation exposes a
specific defect:

- `predicateLanguage : Language.{0, 0}` has no function symbols and
  exactly one relation symbol of arity one.
- `PairLanguage L := L.sum predicateLanguage` is an `abbrev`.
- `pairPredicate L` picks the right summand's unary relation, while
  `pairRelationInl` makes the left-summand relation explicit for rewriting.
- `predicateStructure (S : Set M)` interprets the one predicate on an
  arbitrary set, but **`pairStructure` accepts `S : L.Substructure M`**.
  Do not silently generalize the main semantics to an arbitrary `Set M`.
- `pairStructure` explicitly dispatches the function and relation
  symbols by summand so that the original `L`-part computes
  definitionally. It proves
  `pairStructure_isExpansionOn_sumInl` and
  `pairStructure_RelMap_pairPredicate`.

Do not introduce a new bundled pair object or notation without a
concrete consumer. The public names should stay in
`FirstOrder.Language`, following adjacent modules.

### Relativization

Retain
`FirstOrder.Language.BoundedFormula.relativize` as the fundamental
translation, using `mapTermRel`:

- Map old terms through `LHom.sumInl.onTerm`.
- Map old relations through `pairRelationInl`.
- Preserve falsity, equality, implication, and their derived Boolean
  operations.
- At an `all` binder, replace the translated body `ψ` with
  `U(Fin.last n) → ψ`. Thus quantified variables are guarded by `U`;
  the free-variable assignment must already lie in `S`.

Keep the simp-compatible equations
`relativize_falsum`, `relativize_equal`, `relativize_rel`,
`relativize_imp`, and `relativize_all`. There is no reason to introduce
a parallel translation for ordinary `Formula`: that interface is the
zero-binder specialization of the same construction.

### Semantic contract

The key statements, in dependency order, are:

1. `realize_guard`: the guard on the last bound variable is true
   exactly when that variable belongs to `S`.
2. `BoundedFormula.realize_relativize`: for `v : α → S` and
   `xs : Fin n → S`, realizing `φ.relativize` in `(M, S)` at the
   coerced assignments is equivalent to realizing `φ` in `S`.
3. `Formula.realize_relativize`: the preceding theorem at `n = 0`.
4. `embedding_relativization`: for `f : M ↪[L] N`, satisfaction of
   `φ.relativize` at `f ∘ a` in `(N, f.toHom.range)` is equivalent to
   satisfaction of `φ` at `a` in `M`.
5. `pair_relativization`: the corresponding statement for
   `e : M ↪ₑ[L] N`, delegated to `embedding_relativization
   e.toEmbedding`.

Prove the bounded-formula theorem by structural induction. Equality
and relation cases use the expansion/reduct and substructure semantic
bridges. Implication is compositional. The universal-quantifier case
uses `realize_guard` and the compatibility of `Fin.snoc` with
substructure coercions. Then use `f.equivRange` for the embedding
theorem; do not duplicate the induction for elementary embeddings.

## Constraints and non-goals

- Respect `AGENTS.md` and `CONTRIBUTING.md`: explicit variables
  (`autoImplicit = false`), minimal acyclic imports, existing
  Mathlib/neighboring names, concise mathematical docstrings, and no
  `sorry` added to the delivered Lean files.
- Keep the ambient-structure statement and the substructure statement
  distinct. Relativization works for a substructure; elementarity is
  needed for later elementary-pair theory, not for this lemma.
- Retain the existing public API in `VaughtianPair.lean`. This scope
  does not rewrite `Theory.IsVaughtianPair`, prove a new Vaughtian-pair
  result, or change its parameter layout (`Fin n ⊕ Fin 1`).
- Avoid broad downstream refactors, new imports in foundational syntax
  modules, a second semantics hierarchy, and speculative helper
  lemmas. Keep proof-local conveniences private.
- Remove both file-wide settings from the experimental implementation:
  `set_option warn.classDefReducibility false` and
  `set_option linter.style.haveILetI false`. Address any resulting
  warnings in the code instead of suppressing them.
- No `blueprint/`, `blueprint/lean_decls`, website, CI-workflow, or
  dependency-lockfile edits in this change. Blueprint annotation
  (`\lean`/`\leanok`) requires separate authorization.
- Do not treat the experiment branch as an automatically trusted
  upstream. Recheck the target base and the exact diff before
  incorporating code.

## Implementation sequence

After the plan is approved, use a focused feature branch such as
`feat/pair-language-relativization` **from the then-current `main`**,
not from the experiment branch. The branch's **first commit** adds this
plan at `docs/plan/pair-language-relativization.md`, before any Lean
implementation changes. Compare its base against the pinned experiment,
and transplant only the reviewed changes; cherry-picking the single
experiment commit is acceptable only after inspecting its exact file
diff and verifying there are no new conflicts or unrelated changes.
Remove the two file-wide linter settings when incorporating the experiment.

1. **Revalidate the baseline.** Confirm Mathlib and Lean versions,
   existing names, the current `main` head, and the two-file experiment
   diff. Check that the proposed API has not already been added or
   superseded.
2. **Introduce the language and structure layer** in
   `MorleyCategoricityTheorem/ModelTheory/PairLanguage.lean`:
   `predicateLanguage`, `PairLanguage`, `pairPredicate`,
   `pairRelationInl`, `predicateStructure`, `pairStructure`, reduct
   and predicate-interpretation lemmas.
3. **Introduce the translation** `BoundedFormula.relativize`, the five
   computation lemmas, and `realize_guard`.
4. **Prove the semantic bridge** for bounded formulas; derive
   `Formula.realize_relativize`.
5. **Expose embedding transports**:
   `embedding_relativization` using `equivRange`, followed by the
   elementary special case `pair_relativization`.
6. **Integrate the module** with one appropriately ordered import in
   `MorleyCategoricityTheorem.lean`. Inspect exported theorem
   statements and any unexpected dependencies. Do not modify
   `VaughtianPair.lean` merely to advertise the new functionality.
7. **Validate and review the diff**. Compare declaration names and
   conclusions with the experiment, verify all gates below, and
   prepare one focused PR to `main`. Use a conventional subject such as
   `feat(pair-language): add pair structures and formula relativization`.
   Keep the PR description short: change summary, checks, and
   caveats; link this plan for the design rationale.

## Verification and completion criteria

Run from the repository root on the implementation branch:

```bash
lake exe cache get
lake build MorleyCategoricityTheorem
lake exe mk_all --check
lake exe checkdecls blueprint/lean_decls
```

`lake exe cache get` is setup, not a proof-validation result.
`checkdecls` should remain green even though this scope does not edit
blueprint references. CI runs the full Lean, root-import, and
declaration-reference checks for a relevant PR; CI is the final gate.
If a check cannot run, record precisely which check and why in the PR.

Add small Lean examples only if needed to cover a real regression risk:
an empty binder context, an equality/relation atom, and a guarded universal
quantifier. Do not introduce a separate test framework just for these examples.

Completion requires:

- The specified language, structure, translation, and semantic
  declarations exist under the agreed names and compile.
- The arbitrary-substructure and arbitrary-embedding theorems remain
  available, and `pair_relativization` is derived without a duplicate
  induction.
- Root imports are synchronized and imports remain acyclic.
- No new `sorry`, unexplained axioms, unrelated source changes, or
  unauthorized blueprint changes are introduced.
- The relevant local checks and PR CI pass; any unavailable local
  checks are explicitly disclosed.

## Deferred consumers and plan lifecycle

The blueprint's
`lem:elementary-pair-axiomatization` (a theory for elementary pairs,
closure under `L`-functions, and the Tarski–Vaught/relativization
scheme) is the immediate **separate** capability. Subsequent work on
countable Vaughtian pairs, realizing types in elementary pair
extensions, and homogeneous pairs can consume the API above but is
not included in this plan.

Keep this document at
`docs/plan/pair-language-relativization.md` while it describes active
infrastructure work. Update it when an important design decision
changes, not as a running work log. After implementation, put durable
facts in Lean docstrings and archive the plan under
`docs/plan/archive/` only if retaining the design history is useful,
as prescribed by `docs/plan/README.md`. Update relative blueprint links
if the plan is moved to the archive.
