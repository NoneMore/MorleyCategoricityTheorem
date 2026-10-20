# Algebraic Closure Over Definable Sets

## Intent

Give the semantic layer a first-class notion of model-theoretic algebraicity: a predicate "`b` is
algebraic over the parameter set `A`" and the set `algebraicClosure A`, both matching blueprint
`def:algebraic-closure` ("An element `b ∈ M` is algebraic over `A` if it belongs to a finite set
definable with parameters from `A`. The algebraic closure `acl(A)` is the set of all elements
algebraic over `A`.").

The public definitions are intended to be

```lean
def FirstOrder.Language.IsAlgebraicOver (A : Set M) (b : M) : Prop
def FirstOrder.Language.algebraicClosure (A : Set M) : Set M
```

The capability is the semantic layer's only notion of "parameter-definable finiteness", so it is
also the entry point for the strongly-minimal pregeometry and dimension chain. Its direct blueprint
consumers are all currently blocked on this node:

- `prop:algebraic-implies-isolated` (algebraic types are isolated),
- `def:strongly-minimal-pregeometry` (`cl_A X = D ∩ acl(A ∪ X)`),
- `lem:strongly-minimal-closure-laws` (reflexive, monotone, idempotent, finite character),
- `lem:nonalgebraic-type-many-realizations` (many distinct conjugates of a nonalgebraic type),
- `lem:algebraic-closure-cardinality` (`|acl(A)| ≤ |A| + ℵ₀`).

Scope of *this* capability is the definition and the laws that follow from definability and
finiteness alone. Idempotence, exchange, bases, dimension, and any matroid packaging are separate
capabilities; the observations below record why that boundary is the right one rather than an
implementation shortcut.

## Facts / Observations

### Status of the blueprint node

`python3 scripts/blueprint_status.py --milestone reverse_direction --top 12` ranks
`def:algebraic-closure` first on the goal-aware frontier: ready, five direct pending dependents, and
twelve pending path descendants. `python3 scripts/blueprint_status.py --why def:algebraic-closure`
reports no blockers, so nothing else has to land first.

### Mathlib has no model-theoretic algebraic closure

`Mathlib/ModelTheory/` has no algebraic-closure notion: the only occurrences of "algebraic" there
describe relation-free languages (`FirstOrder.Language.IsAlgebraic`) and field-theoretic algebraic
closure. What Mathlib does provide is the definability layer this plan builds on:

| Declaration | Role here |
|---|---|
| `Set.Definable A L s : Prop` (a formula with parameters witnesses it) | parameter-definability |
| `Set.Definable₁ A L s` (`Definability.lean:298`) | unary specialization on `Fin 1`-tuples |
| `Set.Definable.mono` (`Definability.lean:92`) | monotonicity in the parameter set |
| `Set.Definable.singleton_of_mem` | reflexivity of the closure |
| `Set.definable_iff_finitely_definable` | finitely many parameters suffice |
| `L.DefinableSet A α` (`Definability.lean:332`) | bundled variant, not needed by this capability |

`Set.definable_iff_finitely_definable` is the decisive one: it states
`A.Definable L s ↔ ∃ A₀ : Finset M, ↑A₀ ⊆ A ∧ (A₀ : Set M).Definable L s`, which is exactly the
finite-character law the strongly-minimal chain consumes. Finite character therefore costs one
rewrite, not a new argument.

### Name collision

`FirstOrder.Language.IsAlgebraic` already exists (`Mathlib/ModelTheory/Basic.lean:73`) with the
unrelated meaning "the language has no relation symbols". The element predicate must therefore not
be called `IsAlgebraic`; the draft uses `IsAlgebraicOver`. `algebraicClosure` is free in
`FirstOrder.Language` (the only existing `algebraicClosure` is
`IntermediateField.algebraicClosure` in field theory, a different namespace).

### Verified draft

`Scratch/AlgebraicClosure.lean` compiles against the pin with `lake env lean`, contains no `sorry`,
and needs no tactic import. It fixes the definition and proves:

- `mem_algebraicClosure_iff` (unfolding, `Iff.rfl`);
- `definable₁_iff_definable : A.Definable₁ L s ↔ A.Definable L {x : Fin 1 → M | x 0 ∈ s}`,
  which is `Iff.rfl` — `Definable₁` *is* the one-dimensional `Definable`;
- `subset_algebraicClosure` (reflexivity), from `Set.Definable.singleton_of_mem`;
- `algebraicClosure_mono` (monotonicity), from `Set.Definable.mono`;
- `mem_algebraicClosure_iff_exists_finset` (finite character), from
  `Set.definable_iff_finitely_definable` plus `definable₁_iff_definable`;
- `isAlgebraicOver_iff_exists_formula`, the formula-level form
  `IsAlgebraicOver A b ↔ ∃ φ : L.Formula (A ⊕ Fin 1), (φ.realizationSet ↑).Finite ∧ φ.Realize …`,
  which is what `prop:algebraic-implies-isolated` and `lem:nonalgebraic-type-many-realizations`
  need, in both directions.

The two facts that shape the statement design came out of this draft:

- **`Definable₁` is defeq to one-dimensional `Definable`, but `Fin 1` extensionality is not.**
  `fun _ : Fin 1 => x 0` and `x` are propositionally equal only, so converting the project's
  `α`-ary `Set.definable_iff_exists_realizationSet` to the unary shape needs
  `funext` plus `Fin.eq_zero`. `rw [Fin.eq_zero i]` and `congrArg` suffice; no tactic import is
  required, which keeps the module inside the `Mathlib.ModelTheory` import boundary.
- **Finiteness of the unary realization set is a preimage, not an image.**
  `{x : Fin 1 → M | x 0 ∈ s}` is `(fun x => x 0) ⁻¹' s`, so it is `s.Finite.preimage` with an
  `InjOn` proof (`Set.Finite.preimage` requires injectivity; the projection is injective on the
  preimage because `Fin 1` is a subsingleton). The reverse direction of the formula bridge goes the
  other way, through `Set.Finite.image`, and needs the same `Fin 1` extensionality to identify the
  two set-builders. This local reasoning is the only non-`ext; simp` proof in the capability.

### Matroid experiment and why it does not change this plan

Mathlib has a complete infinite-matroid library (`Mathlib/Combinatorics/Matroid/`): `Matroid` with
ground set `E`, `IsBase`, `Indep`, `Matroid.ExchangeProperty`, `eRank : ℕ∞`
(`Rank/ENat.lean`), rank-finite classes, restrictions, duals, minors, and `Matroid.closure` as a
`ClosureOperator` (`Closure.lean`). It has no pregeometry notion and no constructor from a closure
operator with exchange: the available entry points are `IndepMatroid.ofFinitary*` (independence
first) and `Matroid.ofBase`.

`Scratch/MatroidBridge.lean` measures what packaging `cl_A X = acl (A ∪ X) ∩ D` as a `Matroid`
would cost, using `IndepMatroid.ofFinitaryCardAugment`. Its five obligations split as follows.

| Obligation | Status |
|---|---|
| `indep_empty` | glue, checked |
| `indep_subset` | glue, checked |
| `indep_compact` | glue from finite character of `acl`, checked |
| `subset_ground` | glue, checked |
| finite Steinitz augmentation | **real mathematics, left as the file's single `sorry`** |

The augmentation obligation is

```lean
I J finite and independent over `A`, I.ncard < J.ncard →
  ∃ e ∈ J, e ∉ I ∧ Indep (insert e I)
```

and it is precisely the content of "any two bases of the relative pregeometry have the same
cardinality", that is, of dimension being well defined. It consumes `lem:strongly-minimal-exchange`
and cannot be discharged before that node. Once it is supplied,
`IndepMatroid.ofFinitaryCardAugment … .matroid` type-checks (the `Payoff` section of the draft
constructs the `Matroid` from the five obligations), and the following API becomes available
without further work:

- `Matroid.eRk : Set α → ℕ∞` for `dim_A`,
- `Matroid.IsBase.encard_eq_eRank` and `ExchangeProperty.encard_isBase_eq`, which give
  "any two bases have the same `encard`" outright,
- `Matroid.Indep.notMem_closure_iff_of_notMem : e ∉ M.closure I ↔ M.Indep (insert e I)`, the bridge
  between the matroid closure and `acl`, which is the only form the exchange and basis arguments
  need,
- `Matroid.closure` as a `ClosureOperator`, for the pregeometry presentation.

Conclusion recorded as a design fact: the matroid layer belongs to the pregeometry/dimension
capability and is gated on exchange. Nothing about `def:algebraic-closure` needs it, and adding it
here would force the augmentation proof into a definition node.

## Design

### Definitions

```lean
namespace FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- `b` is algebraic over the parameter set `A` if it lies in a finite set definable with
parameters from `A`. -/
def IsAlgebraicOver (A : Set M) (b : M) : Prop :=
  ∃ s : Set M, s.Finite ∧ A.Definable₁ L s ∧ b ∈ s

/-- The algebraic closure of a parameter set: all elements algebraic over it. -/
def algebraicClosure (A : Set M) : Set M := {b | IsAlgebraicOver (L := L) A b}
```

Rationale for the choices:

- **Unbundled, `Prop`-valued predicate plus a plain `def` set.** The blueprint's `acl(A)` is used as
  a set (`b ∈ acl(A)`, `D ∩ acl(A ∪ X)`, `acl(A) ⊆ acl(A ∪ X)`), and one consumer only needs the
  predicate (`lem:algebraic-closure-cardinality` counts over formulas). A `def` with an `∃` body
  keeps both uses definitionally transparent and lets downstream proofs unpack the
  components without unfolding lemmas. Bundling into `L.DefinableSet` is wrong here: algebraicity is
  not itself a definable set, only witnessed by one.
- **`Definable₁` as the definability primitive.** It is the shape produced by
  `Definable.mono`/`Definable.singleton_of_mem` and consumed by
  `Set.definable_iff_finitely_definable` after the `Fin 1` bridge; choosing `Definable` over an
  abstract `α` would reintroduce the tuple index at every call site.
- **`∃ s, s.Finite ∧ …` rather than "finite cardinality of a type of tuple".** This matches the
  blueprint text literally and keeps `Set.Finite` (the project's finiteness vocabulary) as the only
  finiteness notion; `encard`-based phrasing would complicate the downstream counting argument.
- **Namespace `FirstOrder.Language`, no notation.** Consistent with `Theory.IsOmegaStable` and with
  Mathlib's own predicate placement; a custom `acl` notation would only add blueprint-matching
  friction and no caller needs infix support.

### Derived API in this capability

`definable₁_iff_definable`, `mem_algebraicClosure_iff`, `subset_algebraicClosure`,
`algebraicClosure_mono`, `mem_algebraicClosure_iff_exists_finset`,
`isAlgebraicOver_iff_exists_formula`, each with a module-doc mention. The formula-level statement is
the interface downstream nodes should use; the set-level definition stays available for direct
`rintro` arguments.

### Deliberately deferred

| Property | Why not here |
|---|---|
| idempotence `acl(acl A) = acl A` | nontrivial; follows from exchange on `D` |
| exchange | `lem:strongly-minimal-exchange`, a separate node with a long proof |
| the cardinality bound | needs a counting argument over formulas and parameters |
| pregeometry and dimension | `prop:strongly-minimal-pregeometry` onward |
| matroid packaging | gated on exchange; see Facts |

### Why not `ClosureOperator`

`Set.algebraicClosure` is extensive and monotone but not obviously idempotent at this layer.
Packaging it as `ClosureOperator (Set M)` would make the general idempotence proof a prerequisite of
the definition, which inverts the blueprint dependency order. The operator structure, if wanted,
belongs to the pregeometry capability, where the exchange argument supplies idempotence.

## Specs / Constraints

### Non-goals

- Do not introduce a matroid, pregeometry, or dimension definition in this capability.
- Do not package `algebraicClosure` as a `ClosureOperator` or any bundled structure.
- Do not prove idempotence, exchange, or the cardinality bound here.
- Do not add notation or a `DefinableSet`-valued API without a concrete caller.
- Do not modify `blueprint/` as part of this work; wiring the `\lean{}` labels of
  `def:algebraic-closure` is an authorized blueprint change and is tracked as a follow-up.

### Invariants

- `IsAlgebraicOver` keeps the definitional body `∃ s, s.Finite ∧ A.Definable₁ L s ∧ b ∈ s`, and
  `algebraicClosure A` keeps the body `{b | IsAlgebraicOver A b}`, so downstream `rintro` and the
  formula bridge stay stable and the definitions can be unfolded without stored lemmas.
- Module boundary: the new module imports `Mathlib.ModelTheory.Definability` only, plus whatever the
  formula bridge needs from the same library. It must not import `ModelTheory.Semantics`,
  `ModelTheory.Types`, or any type-space module: the closure must not pull the semantic and type
  layers into every consumer.
- Explicit variables and universes (`universes u v w`), because the project builds with
  `autoImplicit = false`.
- No declaration may be named `IsAlgebraic`, `Definable.isAlgebraic`, or anything else that clashes
  with the relation-free-language class.

### Risks

- **`lem:algebraic-closure-cardinality` shape.** That node needs to bound the number of finite
  parameter-definable sets. The current definition exposes only "there exists a finite set", so the
  counting proof will want the formula form plus
  `definable_iff_finitely_definable`; if the counting argument turns out to need a canonical
  enumeration of formulas, add that as a lemma in the cardinality capability rather than weakening
  this definition.
- **Name stability for the blueprint.** `def:algebraic-closure` currently has no `\lean{}` label.
  When the labels are wired, the names above are the ones to record; renaming later would orphan
  the blueprint reference. Decide the names before the blueprint edit, not after.
- **`Set.mem_setOf_eq` deprecation.** The formula bridge currently needs
  `simp only [Set.mem_ofPred_eq, …]`; `Set.mem_setOf_eq` is deprecated in the pin. Keep the
  non-deprecated form so the module does not fail on linter upgrades.
- **Import creep.** The `Fin 1` bridge is the only reason to consider `Mathlib.Tactic.FinCases`;
  the draft avoids it with `Fin.eq_zero`, and the production module should keep doing so.

## Implementation / Verification

### File plan

1. New `MorleyCategoricityTheorem/ModelTheory/AlgebraicClosure.lean`, built from
   `Scratch/AlgebraicClosure.lean` with a proper module docstring (purpose, main results, the
   blueprint nodes it serves, and a TODO-free header; the deferred items above stay in this plan).
2. `MorleyCategoricityTheorem.lean`: add the import after `MorleyCategoricityTheorem.BinaryTree`,
   preserving alphabetical order.
3. No existing module changes. No blueprint change. `Scratch/AlgebraicClosure.lean` is deleted once
   the module lands; `Scratch/MatroidBridge.lean` stays as evidence until the matroid follow-up
   plan exists.

### Implementation order

1. Re-check that Mathlib still has no model-theoretic `acl` (the pinned revision may move); confirm
   the `Definable` API names used by the draft.
2. Create the module with the two definitions and `definable₁_iff_definable`.
3. Add reflexivity, monotonicity, and finite character.
4. Add the formula-level characterization, checking both directions against
   `Set.definable_iff_exists_realizationSet` and `Set.definable_realizationSet`.
5. Add the module docstring, wire the root import, run the verification commands.
6. Delete `Scratch/AlgebraicClosure.lean` in the same change that lands the module.

### Estimated cost

The draft is roughly 95 lines including docstrings, and the proof content is dominated by the
formula bridge (the `InjOn` preimage argument and the two `Fin 1` extensionality steps). The
production module should be about the same size; the only expected additions are the module
docstring and possibly one `@[simp]` membership lemma.

### Verification

For the draft (no library change):

```bash
lake env lean Scratch/AlgebraicClosure.lean
```

For the module change:

```bash
lake build MorleyCategoricityTheorem
lake exe mk_all --check
```

`lake exe checkdecls blueprint/lean_decls` is not triggered while `blueprint/` is untouched and no
blueprint-referenced declaration changes. `Scratch/MatroidBridge.lean` keeps one intentional `sorry`
and is never built: `Scratch/` is not a Lake library, and both the draft headers and the pull
request say so.

### Completion criteria

- `FirstOrder.Language.IsAlgebraicOver` and `FirstOrder.Language.algebraicClosure` exist with the
  bodies above and no `sorry`.
- Reflexivity, monotonicity, finite character, and the formula-level characterization are proved
  with the names listed in Design.
- The root import file reflects the new module and `lake exe mk_all --check` passes.
- `blueprint/` is untouched; the intended `\lean{}` label for `def:algebraic-closure` is recorded in
  this plan for a later authorized blueprint change.
- `Scratch/AlgebraicClosure.lean` no longer exists once the module lands.

### Deferred follow-ups

- **Idempotence and closure laws.** `lem:strongly-minimal-closure-laws` needs idempotence of `cl_A`.
  On a strongly minimal set this follows from exchange; the general case needs an automorphism-orbit
  argument. Start from exchange rather than from a general `acl` closure-operator theorem.
- **Cardinality bound.** `lem:algebraic-closure-cardinality` needs a counting lemma over formulas
  and finite parameter tuples; it consumes `isAlgebraicOver_iff_exists_formula` and finite
  character, so it should be planned after this module exists.
- **Matroid packaging.** Once `lem:strongly-minimal-exchange` lands, supply the finite Steinitz
  augmentation obligation recorded in `Scratch/MatroidBridge.lean` and package `cl_A` with
  `IndepMatroid.ofFinitaryCardAugment`; then `Matroid.eRk` and `IsBase.encard_eq_eRank` replace a
  bespoke basis-cardinality development. That is a separate plan, not a step of this one.
