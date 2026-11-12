# Syntax–Semantics Separation for First-Order Transformations

## Intent

Establish a maintainable boundary between *operations on first-order syntax* and *interpretation
of that syntax in structures*. In particular, stop proving a fact about how a term, bounded
formula, formula, or sentence is represented by repeating its structural recursion inside
a semantic theorem.

The rule is: **prove representation equalities and coherence/naturality of syntax operations
without any model; then derive their semantic compatibility from a small set of generic
realization theorems**. This is a proof-allocation rule, not a ban on all induction in semantic
files. Induction which establishes genuine interpretation behavior (quantifiers, homomorphisms
between models, witnesses, and the generic realization theorems themselves) remains legitimate.

This is a repo-local refactor with an upstream migration path, not a fork of Mathlib syntax.
The primary public vocabulary stays Mathlib's `Formula.relabel`, `Formula.equivSentence`,
`LHom.onFormula`, and `BoundedFormula.constantsVarsEquiv`. The arity-preserving
`BoundedFormula.relabelFree` may serve as an internal normal form but must not become a
competing public representation for `Formula.relabel`.

The active scope has two concrete outcomes:

1. A syntax-only, Mathlib-portable `ModelTheory/SyntaxKernel.lean` establishing the needed
   representations and naturality laws, especially the commutation of `equivSentence` with
   constant renaming.
2. Project-level syntax naturality for `Formula.bindParam` (defined in the project's
   `ModelTheory/Syntax.lean`), with existing semantic consumers reusing the resulting
   syntax equalities rather than building composite `IsExpansionOn` chains.

`LHom.realize_onSentence_equivSentence` in `ModelTheory/Semantics.lean` is the immediate
regression target; `DefinablyFull.lean` is the second concrete consumer. The existing
`PartialElementaryEmbedding.map_sentence`, type-transport, and type-space results remain
compatibility checks, not owners of the infrastructure.

## Facts / Observations

### Checked evidence and its limits

The project pins Lean and Mathlib `v4.34.1` (`lakefile.toml` / `lean-toolchain`).
The five archived investigations in `Scratch/` were reported compiled against this
dependency when PR #35 was drafted. They are **not imported by the root project build**;
`lake build MorleyCategoricityTheorem` does not independently check them.

- `Scratch/ReconSyntaxKernel.lean` contains three representation identities:
  `Term.relabel` as `Term.subst`, `LHom.onTerm` as `Term.substFunc`, and
  `LHom.onBoundedFormula` as identity-arity `mapTermRel`.
- `Scratch/ReconSemanticsKernel.lean` derives `Term.realize_relabel`,
  `LHom.realize_onTerm`, and `LHom.realize_onBoundedFormula` from those identities
  and Mathlib's generic realization theorems, without re-induction for each operation.
- `Scratch/ReconRelabelFree.lean` gives an identity-arity
  `BoundedFormula.relabelFree`, its algebra and the cast bridge to the upstream
  `BoundedFormula.relabel`.
- `Scratch/ReconSyntaxKernel2.lean` gives the `constantsVarsEquiv` naturality
  family and `equivSentence` naturality, including a version for Mathlib's own
  `Formula.relabel`.
- `Scratch/ReconAll.lean` experiments with shifted-arity `mapTermRel`
  composition and records the required binder/coherence bookkeeping.
  `Scratch/relabel_arity_preserving.diff` explores changing upstream's
  definitional `Formula.relabel`, including resulting downstream simp changes.

The two end-to-end outcomes reported in the original investigation are:

```lean
(L.lhomWithConstantsMap f).onSentence (Formula.equivSentence θ) =
  Formula.equivSentence (θ.relabel f)
```

and a version of `LHom.realize_onSentence_equivSentence` obtained by rewriting with
this equality, constructing only the *target* constants interpretation and using the
existing `Formula.realize_equivSentence` and `Formula.realize_relabel`. The current
project proof instead constructs a temporary source constants structure and two
`IsExpansionOn` witnesses for the composite map.

These are evidence for the design, not evidence that the new library declarations are
already implemented. Proposed `bindParam`, finite-support, and constants-to-variables
improvements below have **not** been verified by those experiments.

### Where the syntax/semantics boundary is currently crossed

The Mathlib `ModelTheory/Semantics.lean` at the pinned revision contains 21 textual
`induction` occurrences. They are **not 21 candidates for deletion**:

| Group | Lines in pinned Mathlib Semantics | Assessment |
| --- | --- | --- |
| Specific transformation realizations | 90, 224, 513 | Refactor using syntax representations (`Term.realize_relabel`, `LHom.realize_onTerm`, `LHom.realize_onBoundedFormula`); experiments exist |
| Constants ↔ variables | 178, 199 | Investigate factoring through a syntax equality and `subst` / `onTerm` |
| Finite free-variable support | 142, 159, 447 | Investigate a support/reconstruction syntax API before changing proofs |
| `liftAt` and indexed binder arithmetic | 400 | Possible generalization, not justified by one caller |
| Generic interpretation recursion | 126, 134, 363, 381 | Retain (`realize_subst`, `realize_substFunc`, `realize_mapTermRel_id`, `realize_mapTermRel_add_castLe`) |
| Maps between models | 234, 988 | Retain genuine model semantics |
| `toFormula` / binder interpretation | 874 | Retain unless an independent simplification is demonstrated |
| Lists / natural-number recursion | 282, 297, 330, 803, 812 | Retain; unrelated to the representation duplication |

The project itself already avoids almost all structural recursion over first-order terms and
bounded formulas outside its syntax proofs. Its main issue is repeated hand-off between
syntax and semantics:

- `ModelTheory/Semantics.lean`: `LHom.realize_onSentence_equivSentence` (the
  composite-expansion instance chain); `realize_bindParam` and `realize_unbindParam`
  (already reuse Mathlib realization theorems); `exists_fin_params` and
  `realize_iff_of_realize_fin` (finite-support/variable-reindexing bookkeeping).
- `ModelTheory/DefinablyFull.lean`: the proof of
  `exists_elementaryExtension_card_eq_with_full_unary_realizations` translates a
  formula with parameters using `constantsVarsEquiv.symm` and `relabel`, later
  renames its constants with `onFormula` and repeats realization conversions
  (notably around the current lines 256–312). This is a real second consumer for
  syntax naturality, although interpreting the final constants still requires
  semantic hypotheses.
- `ModelTheory/PartialEmbedding.lean`: `map_sentence` goes through
  `Formula.equivSentence` and the existing semantic bridge; it must continue
  using the actual elementarity hypothesis.
- `ModelTheory/Types.lean`, `TypeSpaceHomeomorphism.lean`: parameter-language
  transport, theory membership and realized types are genuine semantic/topological
  applications. Their use of `relabel` or sentence maps does not alone imply that
  their proofs should move to Syntax.

Also relevant upstream: `BoundedFormula.subst` is already identity-arity `mapTermRel`
and `BoundedFormula.realize_subst` is already derived from
`BoundedFormula.realize_mapTermRel_id`. Whether
`relabelFree f φ = φ.subst (fun a => Term.var (f a))` is a useful replacement for a
separate `realize_relabelFree` is an **open experiment**, not an established fact
in this plan.

### Meaning of the boundary

An equality of *syntax* must be proved without `Structure`, `Realize`, or an
interpretation-dependent hypothesis. Semantic equivalence from different constants
denoting equal elements is not syntactic equality: for example
`realize_bind_unbind` allows distinct constant names with the same interpretation.
Witness existence, quantifier movement (such as prenex normalization), finite-cardinality
realization statements, model embeddings, quotients, and ultraproducts likewise
contain real semantic work and must not be described as syntax equalities.

## Design

### Architecture and dependencies

```text
Mathlib.ModelTheory.Syntax
  └── ModelTheory/SyntaxKernel        (generic representation + coherence;
        │                               no Mathlib Semantics or Structure)
        └── ModelTheory/Syntax       (project syntax constructors, bindParam,
              │                       project-specific naturality)
              └── ModelTheory/Semantics  (Mathlib Semantics + syntax laws;
                                         semantic bridges / consumers)
                    └── downstream model-theory modules
```

The diagram omits direct imports of Mathlib semantic modules and other project dependencies.
`Syntax.lean` must actually import `SyntaxKernel.lean`. The new kernel stays
Mathlib-portable and imports `Mathlib.ModelTheory.Syntax` only.
`Formula.bindParam` is defined in *project* `Syntax.lean`, so its naturality belongs
there, **not** in `SyntaxKernel.lean`; placing it in the kernel would invert this
dependency and risk a cycle.

A new `SemanticsKernel.lean` is **not required now**. The immediate bridge rewrite uses
Mathlib's `Formula.realize_relabel` and `Formula.realize_equivSentence`, and does not
consume a new `realize_relabelFree` theorem. A small generic semantic module can
be extracted later if two or more real callers need a genuinely new interpretation
principle. No extra module should be created just for architectural symmetry.

### A. Representation identities (syntax only)

Keep all three experimentally established equations together, or their named
equivalents, in `SyntaxKernel`:

```lean
t.relabel g = t.subst (fun a => Term.var (g a))

Φ.onTerm t =
  t.substFunc (fun {_} f => (Φ.onFunction f).term)

Φ.onBoundedFormula ψ =
  ψ.mapTermRel (fun _ => Φ.onTerm) (fun _ R => Φ.onRelation R)
    (fun _ => id)
```

These identities specify *how a syntax operation is constructed*. They are the
upstream-facing foundation for eventually replacing the three duplicate semantic
inductions, but this repo-local PR does **not** replace Mathlib's existing proofs.

Add only the minimum congruence and term-level coherence facts needed to derive
the naturality below. `mapTermRel_mapTermRel` already exists at identity arity;
do not introduce a general shifted-arity functor solely to avoid one cast proof.

### B. Free-variable relabel normalization

Use `BoundedFormula.relabelFree` as an identity-arity `mapTermRel` helper where it
makes composition, naturality and the comparison with `relabelEquiv` tractable.
Give it identity/composition and the single cast bridge back to Mathlib's
`BoundedFormula.relabel`, deriving the formula-level comparison
`BoundedFormula.relabelFree f θ = θ.relabel f`.

This is a proof-internal normal form. Public formula-level theorems and all existing
callers continue to state results with `Formula.relabel`. Do not change Mathlib's
definition or rewrite all of the project's relabel sites.

**Before adding a public realization lemma**, test the alternate expression through
`BoundedFormula.subst` and the existing `realize_subst` theorem. Decide on
`realize_relabelFree` only if a concrete consumer demonstrably needs it; do not
create the separate SemanticsKernel simply to house it.

### C. Naturality and commuting representations

The principal public API is the equality

```lean
theorem Formula.onSentence_equivSentence_relabel
    (f : α → β) (θ : L.Formula α) :
    (L.lhomWithConstantsMap f).onSentence
      (Formula.equivSentence θ) =
    Formula.equivSentence (θ.relabel f)
```

The kernel proof may use the `constantsToVars` and `constantsVarsEquiv`
naturality family, `relabelEquiv`, `Sum.map` and `relabelFree`. Keep the
arity-/cast-level calculations inside this syntax-only implementation.

A symmetric formula for `equivSentence.symm` can be obtained by bijectivity and
added if a caller benefits. No bundled `Functor` or `NaturalTransformation` API
is needed merely to express these commuting squares.

The second public interface is project-local naturality for parameter binding:

```lean
-- Candidate statement in ModelTheory/Syntax.lean; proof not yet checked.
theorem Formula.onFormula_bindParam
    (f : γ → δ) (φ : L.Formula (β ⊕ α)) (b : β → γ) :
    (L.lhomWithConstantsMap f).onFormula (φ.bindParam b) =
      φ.bindParam (f ∘ b)
```

It should follow from the constants/variables naturality and the relabel
composition law; establish it *without any structure*. Check its actual elaborated
statement and needed auxiliary lemmas before committing to this exact signature.

A language-homomorphism variant (`L →ᴸ L'` with constants unchanged) is a
potential future companion, not a prerequisite. General naturality in both
dimensions and bundled categorical structure are outside the present scope.

### D. Interpretation layer and consumers

The semantic interface should remain thin: use Mathlib's
`Term.realize_subst`, `Term.realize_substFunc`,
`BoundedFormula.realize_mapTermRel_id` and, where shifts genuinely occur,
`BoundedFormula.realize_mapTermRel_add_castLe`. Specific semantic theorems
should cite syntax representation lemmas before these generic interpretation
theorems instead of re-proving how a syntax operation recursively maps constructors.

For `LHom.realize_onSentence_equivSentence`, retain the exact statement and
replace only its proof by syntax naturality followed by
`Formula.realize_equivSentence` and `Formula.realize_relabel`. The verified
experiment needs only the target constants structure; it no longer needs the
temporary source constants structure or the two composite-expansion
`IsExpansionOn` witnesses.

For `DefinablyFull.lean`, use `onFormula_bindParam` or a closely related
syntax law to simplify the existing parameter-renaming/realization conversions.
Preserve the genuinely necessary `constantsOn` interpretation and model
hypotheses. Verify at least one of the repeated conversion sites as an
end-to-end regression; do not promise that every structure instance disappears.

`PartialElementaryEmbedding.map_sentence` and complete-type transport remain
semantic consumers. Their statements and their elementarity/model assumptions
must not change merely to fit the syntactic reorganization.

### E. Further work, outside this PR

The following are **investigations**, not acceptance criteria for this PR:

- Upstream Mathlib proof-only replacement of the three duplicate inductions
  `Term.realize_relabel`, `LHom.realize_onTerm` and
  `LHom.realize_onBoundedFormula`, after the representation lemmas are upstream.
- Expressing `varsToConstants` with `onTerm` + `subst` and deriving
  `constantsToVars` realization via its inverse; may remove two additional
  transformation-specific inductions, but needs a compiling proof.
- A support/reconstruction syntax theorem for `restrictVar`,
  `restrictVarLeft` and `restrictFreeVar`, then extracting an exact
  finite-parameter syntax representation before applying interpretation.
  Partial maps on the free-variable support do not automatically extend to
  a global relabel, so this needs a deliberate API.
- Generalized arity shifts / `liftAt` coherence; optional upstream change
  `Formula.relabel := relabelFree`; proof refactors for `toFormula`.
  Each must be justified independently rather than by an induction count.

## Specs / Constraints

### Non-goals

- No Mathlib, `.lake/packages/`, `lake-manifest.json`, or toolchain change.
- No statement change for an existing project theorem, especially the semantic bridge.
- No definitional change to `Formula.relabel` and no blanket migration of call sites.
- No duplicate general syntax representation exposed as a second public
  `Formula.relabel` API; `relabelFree` is a supporting normal form.
- No mandatory `SemanticsKernel`, general shifted-arity algebra, categorical
  packaging, or speculative naturality variants without verified consumers.
- No changes to `blueprint/` unless the eventual implementation actually
  affects blueprint-linked declarations.
- No removal of Mathlib's existing semantic induction proofs in a repo-local PR.

### Invariants

- **Dependency boundary:** `SyntaxKernel` imports only
  `Mathlib.ModelTheory.Syntax`, is independent of structures/realization,
  and contains the generic equality and naturality proofs. `Syntax.lean`
  imports it and owns naturality of its own constructors such as `bindParam`.
- **Proof allocation:** syntax representations and commuting diagrams
  precede any semantic compatibility proof. Interpretation-dependent
  equalities, witnesses, model morphisms and generic realization recursion
  remain semantic.
- **Public vocabulary:** state formula-facing APIs via Mathlib's
  `Formula.relabel` and `equivSentence`; keep the cast and arity
  arithmetic behind the syntax boundary.
- **No absolute induction ban:** a new Term/BoundedFormula induction
  in a semantic module requires justification that it establishes
  genuine interpretation rather than duplicates an existing transformation
  representation. Grepping `induction` is a review aid, not a formal test.
- **Simp discipline:** computation rules may be `[simp]`; composition
  normalizations and bridges changing public normal form should generally
  be explicit. Check that formula-level and bounded-formula-level
  lemmas do not create duplicate simp rules at arity zero.
- **Portability:** avoid adding local declarations which duplicate an
  identically named Mathlib theorem. If Mathlib later adopts a proposed
  lemma, remove/replace the local adapter and validate all imports.

### Design risks

- A proof of `relabelFree = subst` may be possible but could lead to
  worse elaboration/simplification; treat it as an experiment, not a
  decision that the existing `relabelFree` route is wrong.
- The cast bridge and the `constantsVarsEquiv` naturality proof depend
  on the precise Mathlib binder/variable ordering; keep this sensitivity
  localized and test with the pinned dependency.
- Syntactic equality for `bindParam` is not the same as the semantic
  `realize_bind_unbind` theorem, whose hypotheses can equate interpretations
  of distinct constant symbols.
- Consumer simplification in `DefinablyFull` must not accidentally rely
  on a local structure instance that differs from the intended target
  interpretation. Keep the resulting proof typechecked end to end.

## Implementation / Verification

### Dependencies and implementation sequence

1. **Syntax representations.** Add `SyntaxKernel.lean` importing only
   `Mathlib.ModelTheory.Syntax`. Port the three checked representation
   lemmas from `ReconSyntaxKernel`, the required `mapTermRel` congruence
   and minimum relabel/constant-variable coherence facts.
2. **Arity-preserving proof form.** Implement `relabelFree` and the
   cast/`Formula.relabel` comparison needed by the naturality proof.
   Separately test whether `BoundedFormula.subst` makes an additional
   realization lemma unnecessary. Do not alter public `Formula.relabel`.
3. **Generic syntax naturality.** Establish the `constantsVarsEquiv`
   naturality chain and *both proof-internal and Mathlib-facing forms*
   of `Formula.onSentence_equivSentence_relabel`. This step must
   compile **before** migrating the semantic bridge.
4. **Project-specific syntax naturality.** Make `Syntax.lean` import
   `SyntaxKernel.lean` and prove `Formula.onFormula_bindParam` there,
   using the verified signature. Keep it syntax-only.
5. **Consumers.** Rewrite the proof (not statement) of
   `LHom.realize_onSentence_equivSentence`. Check
   `PartialElementaryEmbedding.map_sentence` and the downstream imports.
   Apply the new binding naturality to a real conversion in
   `DefinablyFull.lean`, retaining necessary semantic interpretation.
6. **Imports and documentation.** Update module headers, root
   `MorleyCategoricityTheorem.lean` imports and the current TODO pointer;
   keep the planned syntax facts in the syntax layer. Do not add
   `SemanticsKernel.lean` unless the experiment reveals a concrete need.
7. **Close out the scratch evidence.** Before leaving Draft, remove
   unused `Scratch/` copies or retain only a justified reproducible
   regression. Do not represent ordinary project build success as
   independent compilation of unimported scratch files.

### Verification

The eventual implementation must run:

```bash
lake build MorleyCategoricityTheorem checkdecls
lake exe mk_all --check
lake exe checkdecls blueprint/lean_decls
```

The last command is already executed by the repository's Lean CI job;
absence of blueprint edits does **not** mean that job skips the declaration
check. These commands validate compiled library modules, not unimported
`Scratch/` experiments. Re-run relevant experimental files explicitly if
they are used as proof evidence, with their scratch import dependencies
available; record the actual commands and outputs with the implementation.

Specific review checks:

- The principal `equivSentence` naturality theorem has no `Structure`
  or `Realize` dependency and uses the public `Formula.relabel`.
- `bindParam` naturality lives in project `Syntax.lean`, compiles in the
  syntax-only import graph and needs no model.
- The semantic bridge keeps precisely its original type and no longer
  constructs a source constants structure or composite `IsExpansionOn` chain.
- At least one end-to-end `DefinablyFull` parameter-renaming conversion
  uses the syntactic naturality interface without adding a new model
  interpretation assumption.
- No `sorry` is added and the affected downstream library still builds.

### Completion and rollback

The capability is complete when the representation/naturality interfaces and
the two consumers above compile and the validation passes. Completion does
**not** wait for all 21 upstream induction sites, finite-support research,
or every motivating blueprint node. Move durable knowledge into the
relevant module docs and archive this plan according to
`docs/plan/README.md`; remove the module TODO pointer at that time.

The new syntax module and new theorems are additive. Reverting their imports
and the proof-only consumer rewrites should restore the prior project
without changing Mathlib or existing declaration types.
