# Partial-Type Realization in Elementary Extensions

## Goal and scope

Build a reusable compactness interface for unary partial types realized in an **elementary extension**,
including finitely many pairwise distinct witnesses. The first consumer is blueprint
[`lem:nonalgebraic-type-many-realizations`](../../blueprint/src/content.tex): if `b ∉ L.algebraicClosure B`
, then for every `n` there is an elementary extension with `n + 1` distinct realizations of `tp(b/B)` .

[`DefinablyFull.lean`](../../MorleyCategoricityTheorem/ModelTheory/DefinablyFull.lean) already constructs
many witnesses using an elementary diagram, finite satisfiability, and compactness. Extract the reusable
realization machinery, not its cardinality control or an immediate refactor of that working proof. Adapt
only the necessary declarations from
[`NoneMore/StabilityTheory`](https://github.com/NoneMore/StabilityTheory); do not add it as a dependency.

This plan adds three Lean modules. It does **not** authorize edits to `blueprint/` , `DefinablyFull.lean` ,
or dependency/lock files.

## Existing APIs and porting boundary

The target uses Lean/Mathlib `v4.34.1` with `autoImplicit = false` ; upstream `StabilityTheory` uses
`v4.30.0-rc1` and a different Mathlib revision. Upstream proofs are design references, not guaranteed
drop-in code.

| Source | Needed capability |
|---|---|
| [Upstream `PartialTypes.lean`](https://github.com/NoneMore/StabilityTheory/blob/master/StabilityTheory/ModelTheory/PartialTypes.lean) | `Theory.withSet`, `Theory.PartialType`, finite-realizability and elementary-extension equivalences |
| [Upstream `LanguageMap.lean`](https://github.com/NoneMore/StabilityTheory/blob/master/StabilityTheory/ModelTheory/LanguageMap.lean) | Formula-set transport and injectivity, only if missing locally |
| Target [`Syntax.lean`](../../MorleyCategoricityTheorem/ModelTheory/Syntax.lean) | Existing `LHom.onFormula_injective`, `LHom.onTheory_comp` and language-map constructions |
| Target [`Types.lean`](../../MorleyCategoricityTheorem/ModelTheory/Types.lean) | Existing `L.CompleteTypeOver` and `typeOf`; no new complete-type framework |
| Target [`Semantics.lean`](../../MorleyCategoricityTheorem/ModelTheory/Semantics.lean) | `Formula.realizationSet₁` and `Formula.realize_iInf` |
| Target [`AlgebraicClosure.lean`](../../MorleyCategoricityTheorem/ModelTheory/AlgebraicClosure.lean) | `isAlgebraicOver_iff_exists_realizationSet₁` |
| Mathlib | `Theory.isSatisfiable_iff_isFinitelySatisfiable` and `ElementaryEmbedding.ofModelsElementaryDiagram` |

Do not port upstream `Types.lean` or duplicate names already defined in the target. Before copying upstream
text verbatim, verify reuse permission and retain provenance; otherwise reprove the needed results against
target APIs.

### Audit outcome

The audit compares the upstream declarations consumed by the three planned modules against this
repository and Mathlib `v4.34.1`.

- **Reuse.** Upstream `StabilityTheory` carries no license file, so no upstream text is copied
  verbatim. The ported results below are reproved against target APIs, and the module documentation
  records the reference project as provenance.
- **Ported.** `LHom.onFormulaSet`, `LHom.mem_onFormulaSet`, `LHom.onFormulaSet_id`,
  `LHom.onFormulaSet_comp`, and `LHom.onFormulaSet_mono` in
  [`LanguageMap.lean`](../../MorleyCategoricityTheorem/ModelTheory/LanguageMap.lean), plus
  `LHom.onFormulaEmbedding` in
  [`Syntax.lean`](../../MorleyCategoricityTheorem/ModelTheory/Syntax.lean).
- **Already available, not ported.** Formula injectivity (`LHom.onFormula_injective`), the sum-map
  laws (`LHom.sumMap_id`, `LHom.sumMap_comp`), the constants-map injectivity API
  (`lhomWithConstantsMap_injective`), `Formula.realize_exClosure`,
  `Formula.realize_exClosure_of_realize_equivSentence`, and
  `Formula.exists_realize_equivSentence_iff_realize_exClosure` (Mathlib, replacing upstream
  `Semantics.lean`), `Theory.isSatisfiable_iff_isFinitelySatisfiable`,
  `ElementaryEmbedding.ofModelsElementaryDiagram`, and the `Theory.ModelType` API.
- **Out of scope.** Upstream `Types.lean`, the order, maximality, and type-space APIs, and the
  parameter restriction/lifting API (`liftSet`, `restrictSet`, `liftParams`, `restrictParams`) are
  not needed by the three planned modules.

## Chosen design

### 1. Minimal partial-type layer

Create `ModelTheory/PartialTypes.lean` under `FirstOrder.Language.Theory` , with the upstream conceptual
representation:

```lean
-- Schematic: supply explicit universes and binders in the implementation.
def Theory.withSet (T : L.Theory) (S : Set (L.Formula α)) : L[[α]].Theory :=
  (L.lhomWithConstants α).onTheory T ∪ Formula.equivSentence '' S

structure Theory.PartialType (T : L.Theory) (α : Type*) where
  toSet : Set (L.Formula α)
  isSatisfiable' : (T.withSet toSet).IsSatisfiable

abbrev Theory.PartialTypeOver (L : Language) (A : Set M) (α : Type*) :=
  (L[[A]].completeTheory M).PartialType α
```

Required public contracts (exact Lean binder order may differ):

-  `PartialType.partialTypeOver_iff_finitelyRealizable` : consistency over `L[[A]].completeTheory M` iff
  every finite fragment is realized simultaneously in the fixed model `M` .
-  `PartialType.partialTypeOver_iff_realizedIn_elementaryExtension` : consistency iff realizable in a model
  of `L.elementaryDiagram M` , after transporting parameter constants `A → M` .

Recover the elementary embedding with `ElementaryEmbedding.ofModelsElementaryDiagram` . Include only proof
dependencies (constructors, realization/reduct and language transport); avoid upstream order, maximality,
type-space, and complete-type APIs. An unbundled `withSet` compactness lemma is fine if it reduces
boilerplate.

### 2. Finite, distinct unary realizations

Create `ModelTheory/PartialTypeRealizations.lean` , depending only on `PartialTypes` and unary formula
semantics. Prove the constant-family `I = Fin (n + 1)` version **first**, without a new typeclass or
structure.

For `B : Set M` and `p : Set (L[[B]].Formula (Fin 1))` , assume:

```lean
∀ (s : Finset (L[[B]].Formula (Fin 1))),
  (↑s : Set _) ⊆ p →
    {x : M | ∀ φ ∈ s, φ.Realize (fun _ : Fin 1 => x)}.Infinite
```

Conclude that some model `N` of the elementary diagram of `M` carries `n + 1` distinct witnesses realizing
every formula of `p` , with parameter interpretations transported through the **same canonical embedding**
`e : M ↪ₑ[L] N` . State the formula-level semantics explicitly; do not identify types over different
structures by definitional equality.

Construct a joint `Fin (n + 1)` -variable formula set containing the coordinate-relabelled formulas of `p`
and all inequalities `x_i ≠ x_j` . For a finite fragment, choose one witness per mentioned coordinate
outside the finitely many previous choices. Each coordinate's **whole finite conjunction** has infinitely
many candidates. Fill unused coordinates from `[Nonempty M]` , apply the two compactness/extension
equivalences, and unpack the resulting realization.

Keep `Fin 1` , `Sum` relabelling, and expansion bookkeeping private unless another consumer needs them.

### 3. Nonalgebraic-type application

Create `ModelTheory/NonalgebraicTypes.lean` , importing `AlgebraicClosure` and `PartialTypeRealizations`
(not `Minimality` , `Pregeometry` , or `DefinablyFull` ).

For `b ∉ L.algebraicClosure B` , form the unary formulas over `B` true at `b` , using
`(L.CompleteTypeOver B (Fin 1)).typeOf` only if the existing API makes that simpler; avoid an otherwise
unused public definition. Every finite conjunction true at `b` has infinitely many realizations: a finite
realization set would be a finite `B` -definable set containing `b` , contradicting nonalgebraicity. Use
`isAlgebraicOver_iff_exists_realizationSet₁` and `BoundedFormula.constantsVarsEquiv` for the semantic
conversion.

Apply the finite distinct-realization theorem to prove the blueprint statement. Express preservation of `B`
-formulas along the canonical embedding; a `CompleteTypeOver` restatement is optional, not a proof
prerequisite.

## Correctness invariants and boundaries

-  **Canonical embedding:** an arbitrary existential `e : M ↪ₑ[L] N` need not equal interpretation of `M`
  -named constants. Retain the elementary-diagram model and its canonical `e` , or prove compatibility.
-  **Parameters:** realize `tp(b/B)` , not `tp(b/M)` ; the latter contains `x = b` and cannot have distinct
  realizations.
-  **Finite fragments:** infinite realization of individual formulas does not imply infinite realization of
  their finite conjunction.
-  **Universes:** compactness may produce `N` in a larger universe; the reusable theorem must not claim
  cardinal equality.
-  **Import graph:** `PartialTypes` uses only low-level target/Mathlib APIs; `PartialTypeRealizations` adds
  unary semantics; `NonalgebraicTypes` adds algebraic closure. Keep imports acyclic.
-  **API hygiene:** no duplicate `CompleteTypeOver` , `onTheory_comp` , or competing variable-order
  conventions; declare all universes and assumptions with `autoImplicit = false` .
-  **Scope:** no new dependencies, no edits to `blueprint/` or `DefinablyFull` in this change. Only add
  blueprint `\lean{...}` and `\leanok` after a separately authorized, sorry-free proof.

## Implementation milestones

1.  **Audit and port.** Compare upstream against target Mathlib, syntax, and language-map helpers. Port only
  missing foundations and settle source-reuse permission.
2.  **Compactness.** Compile `withSet` , minimal `PartialType` , `partialTypeOver_iff_finitelyRealizable` ,
  and the elementary-diagram realization theorem; verify canonical parameter interpretation.
3.  **Finite witnesses.** Compile the one-type `Fin (n + 1)` theorem. Check singleton, empty fragment, and
  pairwise-inequality cases.
4.  **Blueprint consumer.** Compile the finite-conjunction lemma and
  `lem:nonalgebraic-type-many-realizations` . Update root imports in `MorleyCategoricityTheorem.lean`
  without touching `blueprint/` .

## Validation and completion

Run from the repository root after implementation:

```bash
lake build MorleyCategoricityTheorem
lake exe mk_all --check
```

For a separately authorized blueprint wiring change, update `blueprint/lean_decls` and run
`lake exe checkdecls blueprint/lean_decls` . Inspect axioms of new public theorems where feasible: no
`sorry` or hidden `sorryAx` in the claimed proofs or their new dependencies.

Done means the three layers compile, the canonical parameter-transport invariant is proved, root imports are
synchronized, and checks pass. This **plan-only** commit needs Markdown/link review, not a Lean build.

## Deferred work

Only if an actual consumer warrants it, generalize to a family `p : I → Set (L[[B]].Formula (Fin 1))` with
an injective `I → N` , assuming each finite conjunction in each `p i` has infinitely many realizations. A
finite joint fragment uses only finitely many indices; no injection of all `I` into `M` is needed. Avoid
arbitrary arities or general constraint-language infrastructure.

In a **separate validated change**, `DefinablyFull` may use that generalization with `I = F × κ.out` ,
retaining its Löwenheim–Skolem cardinality reduction. Neither extension is required for the blueprint node.
Update this plan when design decisions change; archive it under `docs/plan/archive/` when durable knowledge
has moved into Lean module documentation.
