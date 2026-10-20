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

Scope is the definition, the laws that follow from definability and finiteness, and **idempotence**,
which the blueprint needs before exchange (see below). The cardinality bound and the
pregeometry/dimension layer are separate capabilities.

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
| `Set.definable_iff_exists_formula_sum` | definability as a formula with parameter tuple |
| `L.DefinableSet A α` (`Definability.lean:332`) | bundled variant, not needed here |

The project's `MorleyCategoricityTheorem/ModelTheory/Semantics.lean` adds `Formula.realizationSet`
on top of `Mathlib.ModelTheory.Semantics` and the counting formulas
`Formula.iExsAtLeast`/`iExsAtMost`/`iExsExactly`. Both are below the semantic bridges: importing
`Semantics` does not pull in `ElementaryMaps` or the type-space layer.

### Name collision

`FirstOrder.Language.IsAlgebraic` already exists (`Mathlib/ModelTheory/Basic.lean:73`) with the
unrelated meaning "the language has no relation symbols". The element predicate must therefore not
be called `IsAlgebraic`; the draft uses `IsAlgebraicOver`. `algebraicClosure` is free in
`FirstOrder.Language` (the only existing `algebraicClosure` is
`IntermediateField.algebraicClosure` in field theory, a different namespace).

### Verified draft, with the intended import boundary

`Scratch/AlgebraicClosure.lean` compiles with `lake env lean`, contains no `sorry`, and imports only
`Mathlib.ModelTheory.Definability` and `MorleyCategoricityTheorem.ModelTheory.Semantics`. An earlier
revision imported `ModelTheory.DefinablyFull`, which transitively pulls in `ElementaryMaps` and the
semantic bridges; that was an accident of using the project's
`Set.definable_iff_exists_realizationSet`, and it is fixed: the `Set.Definable` bridge now goes
through Mathlib's `Set.definable_iff_exists_formula_sum` directly.

The draft fixes the definition and proves:

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

Facts that shaped the statements:

- **`Definable₁` is defeq to one-dimensional `Definable`, but `Fin 1` extensionality is not.**
  `fun _ : Fin 1 => x 0` and `x` are propositionally equal only, so the unary shape needs `funext`
  plus `Fin.eq_zero`; no tactic import is required, which keeps the module inside the
  `Mathlib.ModelTheory` boundary.
- **Finiteness of the unary realization set is a preimage.** `{x : Fin 1 → M | x 0 ∈ s}` is
  `(fun x => x 0) ⁻¹' s`, so it is `s.Finite.preimage` with an `InjOn` proof (`Fin 1` is a
  subsingleton). The reverse direction uses `Set.Finite.image` and the same extensionality step.

### Idempotence is needed before exchange, and is provable there

The blueprint orders `lem:strongly-minimal-closure-laws` **before** `lem:strongly-minimal-exchange`
and lists idempotence among the closure laws, so idempotence cannot be deferred to the exchange
proof, and exchange alone does not give it in general. It does not have to be deferred: `acl` is
idempotent for every first-order structure, by an elementary counting argument that needs only
counting formulas and finite parameter sets.

Take `b ∈ acl(acl A)`. By finite character, `b ∈ acl(A ∪ F)` for a finite `F = {c₁, …, cₙ} ⊆ acl A`,
and each `cᵢ` lies in a finite `A`-definable `Sᵢ`. Finiteness of the witnessing set is definable
over `A ∪ F`, so there is an `A`-formula `φ(x, ȳ)` and a realization `φ(M, c̄)` that is finite of
cardinality `m` and contains `b`. Then the `A`-definable set

```text
ψ(x) := ∃ ȳ (⋀ᵢ yᵢ ∈ Sᵢ ∧ φ(x, ȳ) ∧ ∃^{≤m} x′ φ(x′, ȳ))
```

contains `b`, and `ψ(M)` is contained in the union of the fibers `φ(M, ȳ)` over the *finite* set
`∏ᵢ Sᵢ`, with each contributing fiber bounded by `m`. Hence `ψ(M)` is finite. This is the general
form of "an algebraic family of finite sets has finite union", and the blueprint's
`def:counting-formulas` node already plans the formula constructors it consumes.

Two pieces of infrastructure are needed and belong to this capability:

- **Parameter splitting.** A set definable over `A ∪ {c}` is the `c`-fiber of a set definable over
  `A`: move the single parameter `c` from the parameter set into a free variable. Mathlib's
  `Definable` API moves parameters only along `⊆` (`Set.Definable.mono`), so this needs a small
  reindexing lemma, and the finite-family version needs it for a tuple of parameters. This is the
  main new proof work of the capability.
- **Finite-family collapse.** A finite union of finite fibers over a finite definable parameter set
  is finite and definable over the same base; it consumes `Formula.iExsAtMost` and
  `Set.Finite.biUnion`.

### Matroid packaging: real but gated, and not with `eRk`

Mathlib has a complete infinite-matroid library (`Mathlib/Combinatorics/Matroid/`): `Matroid` with
ground set `E`, `IsBase`, `Indep`, `Matroid.ExchangeProperty`, `closure` as a `ClosureOperator`,
`Finitary`, the `ℕ∞`-valued `eRank`/`eRk`, and the **cardinal-valued** `cRank`/`cRk` in
`Rank/Cardinal.lean` with the typeclass `InvariantCardinalRank`, whose
`invariantCardinalRank_of_finitary` instance covers finitary matroids. There is no pregeometry
notion and no constructor from a closure operator with exchange; the entry points are
`IndepMatroid.ofFinitary*` (independence first, and it yields `Finitary`) and `Matroid.ofBase`.

`Scratch/MatroidBridge.lean` measures the cost of packaging `cl_A X = acl (A ∪ X) ∩ D` as a matroid
through `IndepMatroid.ofFinitaryCardAugment`:

| Obligation | Status |
|---|---|
| `indep_empty` | glue, checked |
| `indep_subset` | glue, checked |
| `indep_compact` | glue from finite character of `acl`, checked |
| `subset_ground` | glue, checked |
| finite Steinitz augmentation | real mathematics, the file's single `sorry` |

**Augmentation is false without exchange, so this is not merely an unproved lemma.** On
`M = ℕ × ℕ` with the unary function `f (i, j) = (i, 0)`, take `A = ∅`, `D = M`, `I = {(0, 0)}` and
`J = {(0, 1), (0, 2)}`. Both sets are independent and `|I| < |J|`, but no `e ∈ J \ I` can be added
to `I`, because `f e = (0, 0)` is then algebraic over `I ∪ {e}`.

**Exchange itself must be restricted to `D`.** Quantifying the exchanged element over all of `M`
makes the hypothesis false even when `D` is strongly minimal. On `M = ℕ × Bool` with the unary
function `f (n, t) = (n, false)`, the set `D = {x | f x = x} = ℕ × {false}` is strongly minimal
(its definable subsets with finitely many parameters are finite or cofinite, by permuting the
remaining indices), and with `A = X = ∅`, `b = (0, false) ∈ D`, `c = (0, true) ∉ D` we have
`b = f c ∈ acl {c} ∩ D` and `b ∉ acl ∅`, yet `c ∉ D`, so `c ∉ relClosure ∅ D {b}`. The draft
therefore states `RelExchange` with `X ⊆ D` and `c ∈ D`, which is the standard exchange form and
still suffices for finite augmentation because every independent set is a subset of `D`.

**The blueprint statement of `lem:strongly-minimal-exchange` needs those hypotheses too.** As
written, "`b ∈ cl_A(X ∪ {c}) \ cl_A(X)` implies `c ∈ cl_A(X ∪ {b})`" quantifies `c` freely and
would force `c ∈ D`, which the counterexample above refutes. Its formal statement must carry
`X ⊆ D` and `c ∈ D`. That is a blueprint-text fix, out of scope for this pull request; it is
recorded here so the authorized blueprint change does not inherit the gap, and so the plan does not
claim that the blueprint as written supplies the restricted hypothesis verbatim.

The draft states augmentation under the restricted `RelExchange`; the `Payoff` namespace then
constructs the matroid from it.

**`eRk` is the wrong rank for the blueprint.** `Matroid.eRk : Set α → ℕ∞` sends every infinite base
to `∞`, so it cannot state `dim_A(Y) = |Y|` for uncountable `Y`. The cardinal-valued `cRk` is the
right notion, and for a `Finitary` matroid it is well behaved: `IsBasis'.cardinalMk_eq` gives equal
cardinals for bases of the same set, and `IsBasis'.cardinalMk_eq_cRk` identifies that cardinal with
`cRk X`. The blueprint's `dim_A^M(Y)` should therefore be `cRk`, not `eRk`.

**Closure identification is a deliverable, not an assumption.** Constructing the matroid and
checking that `Matroid.closure` exists does not prove `M.closure X = D ∩ acl (A ∪ X)`. The bridge
the exchange and basis arguments need is `M.Indep.notMem_closure_iff_of_notMem`
(`e ∉ M.closure I ↔ M.Indep (insert e I)` for independent `I`), plus a proof that this determines
`M.closure` on all `X ⊆ D`. Any matroid follow-up must prove
`M.closure X = D ∩ algebraicClosure (A ∪ X)` explicitly before using the closure API for
model-theoretic closure.

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

Rationale:

- **Unbundled, `Prop`-valued predicate plus a plain `def` set.** The blueprint's `acl(A)` is used as
  a set (`b ∈ acl(A)`, `D ∩ acl(A ∪ X)`, `acl(A) ⊆ acl(A ∪ X)`), and
  `lem:algebraic-closure-cardinality` only needs the predicate. A `def` with an `∃` body keeps both
  uses definitionally transparent. Bundling into `L.DefinableSet` is wrong here: algebraicity is not
  itself a definable set, only witnessed by one.
- **`Definable₁` as the definability primitive.** It is the shape produced by
  `Definable.mono`/`Definable.singleton_of_mem` and consumed by
  `Set.definable_iff_finitely_definable` after the `Fin 1` bridge.
- **`∃ s, s.Finite ∧ …` rather than a count-based phrasing.** This matches the blueprint text and
  keeps `Set.Finite` as the only finiteness notion; counting formulas enter only in idempotence,
  where they are genuinely needed.
- **Namespace `FirstOrder.Language`, no notation.** Consistent with `Theory.IsOmegaStable`; a custom
  `acl` notation would add blueprint-matching friction without a caller.

### Laws in this capability

Easy layer (already checked in the draft): `definable₁_iff_definable`, `mem_algebraicClosure_iff`,
`subset_algebraicClosure`, `algebraicClosure_mono`, `mem_algebraicClosure_iff_exists_finset`,
`isAlgebraicOver_iff_exists_formula`.

Idempotence layer (planned, and the reason this capability is not definition-only):

- `Definable.fiber`: parameter splitting — `(A ∪ {c}).Definable₁ L s` yields an `A`-definable
  two-variable set whose `c`-fiber is `s`, plus the finite-tuple version;
- `Set.Finite.biUnion_fibers`: the finite-family collapse, stated for a finite parameter set and a
  family whose contributing fibers are bounded;
- `algebraicClosure_idem : algebraicClosure (algebraicClosure A) = algebraicClosure A`, from those
  two, with `⊇` following from monotonicity.

This is one capability and not two because the counting formulas and the parameter-splitting lemma
have no other consumer in the blueprint before exchange; splitting them would create a second plan
whose completion is a precondition of this one.

### What stays out: matroid packaging

The matroid layer is a separate capability gated on `lem:strongly-minimal-exchange`, for two
independent reasons established above: augmentation needs exchange, and the only rank that expresses
the blueprint's dimension is the cardinal-valued `cRk` of a `Finitary` matroid, which requires the
matroid to exist first. This capability must not depend on Mathlib's matroid module.

### Deliberately deferred

| Property | Why not here |
|---|---|
| exchange | `lem:strongly-minimal-exchange`, a separate node with a long proof |
| the cardinality bound | needs a counting argument over formulas and parameters |
| pregeometry and dimension | `prop:strongly-minimal-pregeometry` onward |
| matroid packaging | gated on exchange and on the closure identification theorem |

## Specs / Constraints

### Non-goals

- Do not introduce a matroid, pregeometry, or dimension definition in this capability.
- Do not package `algebraicClosure` as a `ClosureOperator`; the operator form becomes available with
  idempotence and can be added then if a caller wants it.
- Do not prove exchange or the cardinality bound here.
- Do not use `Matroid.eRk` anywhere a cardinal-valued dimension is meant.
- Do not add notation or a `DefinableSet`-valued API without a concrete caller.
- Do not modify `blueprint/` as part of this work; wiring the `\lean{}` labels of
  `def:algebraic-closure` is an authorized blueprint change tracked as a follow-up.

### Invariants

- `IsAlgebraicOver` keeps the definitional body `∃ s, s.Finite ∧ A.Definable₁ L s ∧ b ∈ s`, and
  `algebraicClosure A` keeps the body `{b | IsAlgebraicOver A b}`, so downstream `rintro` and the
  formula bridge stay stable.
- Import boundary: the module imports `Mathlib.ModelTheory.Definability` and
  `MorleyCategoricityTheorem.ModelTheory.Semantics` only. It must not import `DefinablyFull`,
  `ElementaryMaps`, `Types`, or any type-space module. The idempotence layer adds counting formulas
  from `Semantics`, not the semantic bridges.
- Explicit variables and universes (`universes u v w`), because the project builds with
  `autoImplicit = false`.
- No declaration may be named `IsAlgebraic` or otherwise clash with the relation-free-language
  class.
- If a matroid follow-up is opened, it must prove
  `M.closure X = D ∩ algebraicClosure (A ∪ X)` for `X ⊆ D` before using the closure API, must state
  dimension through `cRk`, not `eRk`, and must carry exchange in the restricted form (`X ⊆ D`,
  `c ∈ D`) that the strongly-minimal exchange lemma actually gives.

### Risks

- **`lem:algebraic-closure-cardinality` shape.** That node bounds the number of finite
  parameter-definable sets. The definition exposes only "there exists a finite set", so the counting
  proof will want the formula form plus `definable_iff_finitely_definable`; if it needs a canonical
  enumeration of formulas, add that as a lemma in the cardinality capability rather than weakening
  this definition.
- **Idempotence effort.** Parameter splitting is the piece with uncertain size: Mathlib's parameter
  handling is set-based (`A ⊆ B`), and moving one parameter into a variable has no ready-made lemma.
  The completion criteria therefore separate the definition layer from the idempotence layer, so the
  module can land and unblock `prop:algebraic-implies-isolated` and
  `lem:algebraic-closure-cardinality` before idempotence is finished.
- **Name stability for the blueprint.** `def:algebraic-closure` currently has no `\lean{}` label.
  Record the names above when the labels are wired; renaming later would orphan the reference.
- **Deprecated set-builder lemmas.** The formula bridge uses `Set.mem_ofPred_eq`;
  `Set.mem_setOf_eq` is deprecated in the pin.

## Implementation / Verification

### File plan

1. New `MorleyCategoricityTheorem/ModelTheory/AlgebraicClosure.lean`, built from
   `Scratch/AlgebraicClosure.lean`: definitions, easy layer, then the idempotence layer in the same
   module (it already imports `Semantics`, so no import change is needed).
2. `MorleyCategoricityTheorem.lean`: add the import after `MorleyCategoricityTheorem.BinaryTree`,
   preserving alphabetical order.
3. No existing module changes. No blueprint change.
4. `Scratch/AlgebraicClosure.lean` and `Scratch/MatroidBridge.lean` are both deleted when the module
   lands; the matroid conclusions above are the design record, and the experiment's code is not
   maintained in the tree.

### Implementation order

1. Re-check that Mathlib still has no model-theoretic `acl` (the pinned revision may move); confirm
   the `Definable` API names used by the draft.
2. Land the module with the two definitions, `definable₁_iff_definable`, and the easy layer. Run the
   full verification; this is the increment that releases the node's direct consumers.
3. Add `Definable.fiber` (parameter splitting), starting with the single-parameter case and only
   then the finite-tuple case.
4. Add `Set.Finite.biUnion_fibers` on top of `Formula.iExsAtMost`.
5. Prove `algebraicClosure_idem`, then restate the closure-law facts that
   `lem:strongly-minimal-closure-laws` needs in the pregeometry plan.
6. Delete both `Scratch/` files in the change that completes step 5.

### Estimated cost

The definition layer is the 100-line draft. The idempotence layer is the real work: parameter
splitting plus the finite-family collapse, estimated at 150–300 lines dominated by formula
bookkeeping, with the single-parameter case as the fallback if the tuple case explodes.

### Verification

For the drafts (no library change):

```bash
lake env lean Scratch/AlgebraicClosure.lean
lake env lean Scratch/MatroidBridge.lean
```

For the module change:

```bash
lake build MorleyCategoricityTheorem
lake exe mk_all --check
lake exe checkdecls blueprint/lean_decls
```

`mk_all --check` and `checkdecls` run unconditionally in the "Validate Lean" CI job and currently
pass; they are not skipped for documentation-only pull requests, so the verification statement must
not call them "not triggered". `Scratch/` is never built by CI or Lake, so its `lake env lean`
validation is author-run and is not part of the CI gate.

### Completion criteria

- `FirstOrder.Language.IsAlgebraicOver` and `FirstOrder.Language.algebraicClosure` exist with the
  bodies above and no `sorry`.
- The easy layer is proved with the names listed in Design, and the module imports only the
  permitted modules.
- `algebraicClosure_idem` is proved, so `lem:strongly-minimal-closure-laws` can be discharged
  without depending on exchange.
- The root import file reflects the new module and `lake exe mk_all --check` passes.
- `blueprint/` is untouched; the intended `\lean{}` label for `def:algebraic-closure` is recorded in
  this plan for a later authorized blueprint change.
- Both `Scratch/` files no longer exist once the idempotence layer lands.

### Deferred follow-ups

- **Cardinality bound.** `lem:algebraic-closure-cardinality` needs a counting lemma over formulas
  and finite parameter tuples; it consumes `isAlgebraicOver_iff_exists_formula` and finite
  character.
- **Matroid packaging.** After `lem:strongly-minimal-exchange`, package `cl_A` with
  `IndepMatroid.ofFinitaryCardAugment` (which also supplies `Finitary`), prove the closure
  identification theorem, and define `dim_A Y := (relMatroid A D).cRk Y` with its
  `InvariantCardinalRank` instance. Supplying the finite Steinitz augmentation is the one proof
  obligation; `Scratch/MatroidBridge.lean` records the shape of the five constructor inputs.
- **Upstream candidates.** Parameter splitting and the finite-family collapse are the kind of
  Mathlib-level lemmas the project has promoted before; record them for a possible upstream
  contribution only after a downstream proof uses them.
