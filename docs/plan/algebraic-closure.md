# Algebraic Closure Over Definable Sets

## Intent

Give the semantic layer a first-class notion of model-theoretic algebraicity: a predicate "`b` is
algebraic over the parameter set `A`" and the set `algebraicClosure A`, both matching blueprint
`def:algebraic-closure` ("An element `b ∈ M` is algebraic over `A` if it belongs to a finite set
definable with parameters from `A`. The algebraic closure `acl(A)` is the set of all elements
algebraic over `A`.").

The public definitions are

```lean
def FirstOrder.Language.IsAlgebraicOver (L : Language.{u, v}) {M : Type w} [L.Structure M]
    (A : Set M) (b : M) : Prop
def FirstOrder.Language.algebraicClosure (L : Language.{u, v}) {M : Type w} [L.Structure M]
    (A : Set M) : Set M
```

The language is explicit in both, so callers write `L.algebraicClosure A` rather than threading
`(L := L)` through every use.

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
be called `IsAlgebraic`; the element predicate is `IsAlgebraicOver`. `algebraicClosure` is free in
`FirstOrder.Language` (the only existing `algebraicClosure` is
`IntermediateField.algebraicClosure` in field theory, a different namespace).

### The landed module and its import boundary

`MorleyCategoricityTheorem/ModelTheory/AlgebraicClosure.lean` landed in `dc9f88e` with no `sorry`
and no tactic import. Its import boundary is Mathlib's `ModelTheory.Definability`, the project's
low-level `ModelTheory.Definability`, and `ModelTheory.Semantics`. The project bridge module was
split out of `ModelTheory.DefinablyFull`: the two bridges `Set.definable_iff_exists_realizationSet`
and `Set.definable_realizationSet` used to live there, so reaching them pulled in `ElementaryMaps`
and with it the semantic bridges and the type-space layer. They now live in
`ModelTheory/Definability.lean` together with the unary bridge
`Set.definable₁_iff_exists_realizationSet₁` and the set-level identity `Set.image_fin_one_eq`;
`DefinablyFull` imports that module, so no declaration moved out of reach.

The landed easy layer, before the idempotence layer:

- `IsAlgebraicOver` and `algebraicClosure`, with the language as an explicit argument;
- `mem_algebraicClosure_iff` (unfolding, `Iff.rfl`, tagged `@[simp]`);
- `subset_algebraicClosure` (reflexivity), from `Set.Definable.singleton_of_mem`;
- `algebraicClosure_mono` (monotonicity), from `Set.Definable.mono`;
- `mem_algebraicClosure_iff_exists_finset` (finite character), from
  `Set.definable_iff_finitely_definable`; its `Definable` statement unifies with `Definable₁` by
  defeq, so no bridge lemma is needed;
- `isAlgebraicOver_iff_exists_realizationSet₁`, the unary formula-level form
  `IsAlgebraicOver A b ↔ ∃ φ : L.Formula (A ⊕ Fin 1), (φ.realizationSet₁ ↑).Finite ∧
  b ∈ φ.realizationSet₁ ↑`,
  which is what `prop:algebraic-implies-isolated` and `lem:nonalgebraic-type-many-realizations`
  need;
- `isAlgebraicOver_iff_exists_formula`, the `Fin 1 → M` restatement for consumers that work with
  `Formula.realizationSet` directly, derived from the unary form.

Facts that shaped the statements:

- **The unary shape is the primary statement.** `Formula.realizationSet₁` and
  `Formula.realizationSet_fin_one_image` in `ModelTheory.Semantics` already carry the `Fin 1`
  bookkeeping, so the unary characterization needs no `funext`/`Fin.eq_zero` argument. The
  `Fin 1 → M` form is derived from it with `Set.Finite.of_finite_image` and
  `Formula.realizationSet_fin_one_image` instead of a bespoke image identity.
- **The unary definability bridge belongs to `Set`, not to `FirstOrder.Language`.**
  `Set.definable₁_iff_exists_realizationSet₁` follows from
  `Set.definable_iff_exists_realizationSet` plus the set identity `Set.image_fin_one_eq`
  (`(fun x : M => fun _ : Fin 1 => x) '' s = {x : Fin 1 → M | x 0 ∈ s}`), which replaces the
  hand-written image equality and the `funext` step of the first draft. The `Iff.rfl` restatement
  `definable₁_iff_definable` that the first draft exposed was dropped: `Definable₁` is
  definitionally one-dimensional `Definable`, and `change` covers the only uses.

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

The reconnaissance experiment (removed with `Scratch/` once the module landed) measured the cost of
packaging `cl_A X = acl (A ∪ X) ∩ D` as a matroid through `IndepMatroid.ofFinitaryCardAugment`:

| Obligation | Status |
|---|---|
| `indep_empty` | glue, checked |
| `indep_subset` | glue, checked |
| `indep_compact` | glue from finite character of `acl`, checked |
| `subset_ground` | glue, checked |
| finite Steinitz augmentation | real mathematics, the experiment's single `sorry` |

**Augmentation is false without exchange, so this is not merely an unproved lemma.** On
`M = ℕ × ℕ` with the unary function `f (i, j) = (i, 0)`, take `A = ∅`, `D = M`, `I = {(0, 0)}` and
`J = {(0, 1), (0, 2)}`. Both sets are independent and `|I| < |J|`, but no `e ∈ J \ I` can be added
to `I`, because `f e = (0, 0)` is then algebraic over `I ∪ {e}`.

**Exchange itself must be restricted to `D`.** Quantifying the exchanged element over all of `M`
makes the hypothesis false even when `D` is strongly minimal. On `M = ℕ × Bool` with the unary
function `f (n, t) = (n, false)`, the set `D = {x | f x = x} = ℕ × {false}` is strongly minimal
(its definable subsets with finitely many parameters are finite or cofinite, by permuting the
remaining indices), and with `A = X = ∅`, `b = (0, false) ∈ D`, `c = (0, true) ∉ D` we have
`b = f c ∈ acl {c} ∩ D` and `b ∉ acl ∅`, yet `c ∉ D`, so `c ∉ relClosure ∅ D {b}`. The restricted
form therefore states `RelExchange` with `X ⊆ D` and `c ∈ D`, which is the standard exchange form
and still suffices for finite augmentation because every independent set is a subset of `D`.

**The blueprint statement of `lem:strongly-minimal-exchange` needs those hypotheses too.** As
written, "`b ∈ cl_A(X ∪ {c}) \ cl_A(X)` implies `c ∈ cl_A(X ∪ {b})`" quantifies `c` freely and
would force `c ∈ D`, which the counterexample above refutes. Its formal statement must carry
`X ⊆ D` and `c ∈ D`. That is a blueprint-text fix, out of scope for this pull request; it is
recorded here so the authorized blueprint change does not inherit the gap, and so the plan does not
claim that the blueprint as written supplies the restricted hypothesis verbatim.

Any matroid follow-up states augmentation under the restricted `RelExchange` and constructs the
matroid from it; nothing claims unconditional augmentation.

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

variable (L : Language.{u, v}) {M : Type w} [L.Structure M]

/-- `b` is algebraic over the parameter set `A` if it lies in a finite set definable with
parameters from `A`. -/
def IsAlgebraicOver (A : Set M) (b : M) : Prop :=
  ∃ s : Set M, s.Finite ∧ A.Definable₁ L s ∧ b ∈ s

/-- The algebraic closure of a parameter set: all elements algebraic over it. -/
def algebraicClosure (A : Set M) : Set M := {b | IsAlgebraicOver L A b}
```

Rationale:

- **Unbundled, `Prop`-valued predicate plus a plain `def` set.** The blueprint's `acl(A)` is used as
  a set (`b ∈ acl(A)`, `D ∩ acl(A ∪ X)`, `acl(A) ⊆ acl(A ∪ X)`), and
  `lem:algebraic-closure-cardinality` only needs the predicate. A `def` with an `∃` body keeps both
  uses definitionally transparent. Bundling into `L.DefinableSet` is wrong here: algebraicity is not
  itself a definable set, only witnessed by one.
- **The language is an explicit argument of both objects and of every public lemma about them.**
  `A : Set M` and `b : M` do not determine `L`, so an implicit language forces `(L := L)` at every
  call site and in every statement. With `L` explicit, the intended reading is
  `L.IsAlgebraicOver A b`, `L.algebraicClosure A`, and `L.algebraicClosure_mono hAB`.
- **`Definable₁` as the definability primitive.** It is the shape produced by
  `Definable.mono`/`Definable.singleton_of_mem` and consumed by
  `Set.definable_iff_finitely_definable` by defeq, and by
  `Set.definable₁_iff_exists_realizationSet₁` when a formula is needed.
- **`∃ s, s.Finite ∧ …` rather than a count-based phrasing.** This matches the blueprint text and
  keeps `Set.Finite` as the only finiteness notion; counting formulas enter only in idempotence,
  where they are genuinely needed.
- **Namespace `FirstOrder.Language`, no notation.** Consistent with `Theory.IsOmegaStable`; a custom
  `acl` notation would add blueprint-matching friction without a caller.

### Laws in this capability

Easy layer (landed): `mem_algebraicClosure_iff`, `subset_algebraicClosure`,
`algebraicClosure_mono`, `mem_algebraicClosure_iff_exists_finset`,
`isAlgebraicOver_iff_exists_realizationSet₁`, `isAlgebraicOver_iff_exists_formula`, plus the
low-level bridges `Set.definable₁_iff_exists_realizationSet₁` and `Set.image_fin_one_eq` in
`ModelTheory.Definability`.

Idempotence layer (the reason this capability is not definition-only):

- `Definable.fiber`: parameter splitting — `(A ∪ {c}).Definable₁ L s` yields an `A`-definable
  two-variable set in `Fin 2 → M` whose `c`-fiber is `s`, plus the finite-tuple version
  `Definable.fiber_finset` for `F : Finset M`, producing an `A`-definable set in `↥F ⊕ Fin 1 → M`
  whose fiber over `F` is `s`. Both witness maps send each parameter variable either to its
  `A`-parameter variable or to its tuple slot; `Formula.relabel` and `Formula.realize_relabel`
  reduce the fiber identity to a pointwise check on that map, so no separate formula surgery is
  needed. These are general definability facts, so they live in the low-level
  `ModelTheory.Definability` rather than in `AlgebraicClosure`; the finite-family collapse and
  idempotence stay with the closure definitions;
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

- `L.IsAlgebraicOver A b` keeps the definitional body `∃ s, s.Finite ∧ A.Definable₁ L s ∧ b ∈ s`,
  and `L.algebraicClosure A` keeps the body `{b | L.IsAlgebraicOver A b}`, so downstream `rintro`
  and the formula bridge stay stable.
- The language stays the first explicit argument of both objects and of every public lemma about
  them, so callers reach them by dot notation (`L.algebraicClosure A`) instead of passing
  `(L := L)`.
- Import boundary: `AlgebraicClosure` imports `Mathlib.ModelTheory.Definability`, the low-level
  `MorleyCategoricityTheorem.ModelTheory.Definability`, and
  `MorleyCategoricityTheorem.ModelTheory.Semantics`. The semantic-layering requirement is what
  forbids the rest: it must not import `DefinablyFull`, `ElementaryMaps`, `Types`, or any type-space
  module, and the permitted low-level `Definability` module likewise imports only Mathlib's
  definability layer and `Semantics`. The idempotence layer adds counting formulas from `Semantics`,
  not the semantic bridges.
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
- **`Fin 1` shape conversion is the fragile seam.** The unary bridge and the `Fin 1 → M` form both
  go through `Formula.realizationSet_fin_one_image`. `Set.image_fin_one_eq` isolates the set-level
  half, so a change to the formula-level conversion is a one-place repair.

## Implementation / Verification

### File plan

1. `MorleyCategoricityTheorem/ModelTheory/AlgebraicClosure.lean`: definitions and easy layer
   (landed), then the finite-family collapse and idempotence in the same module (it already imports
   `Semantics`, so the counting formulas need no further import).
2. `MorleyCategoricityTheorem/ModelTheory/Definability.lean`: the realization-set bridges moved
   out of `ModelTheory/DefinablyFull.lean`, plus `Set.definable₁_iff_exists_realizationSet₁`,
   `Set.image_fin_one_eq`, and the parameter-splitting lemmas `Set.Definable.fiber` and
   `Set.Definable.fiber_finset`. `DefinablyFull` imports it; no other existing module changes.
3. `MorleyCategoricityTheorem.lean`: import both modules, preserving alphabetical order.
4. No blueprint change.
5. `Scratch/AlgebraicClosure.lean` and `Scratch/MatroidBridge.lean` are deleted once the module has
   landed; the matroid conclusions above are the design record, and the experiment's code is not
   maintained in the tree. Deleting them at landing rather than after idempotence keeps the tree
   free of copies that diverge from the production definitions.

### Implementation order

1. Re-check that Mathlib still has no model-theoretic `acl` (the pinned revision may move); confirm
   the `Definable` API names the modules use. Done: Mathlib `v4.34.1` (`d13f23b7`) has neither
   `algebraicClosure` nor `IsAlgebraicOver` under `Mathlib/ModelTheory/`, and the names used below
   are unchanged.
2. Extract the realization-set bridges into the low-level `ModelTheory/Definability.lean`, and add
   the unary bridge, so that the algebraic-closure module reaches them without `DefinablyFull`.
3. Land `AlgebraicClosure` with the two definitions and the easy layer, with the language explicit.
   Run the full verification; this is the increment that releases the node's direct consumers.
4. Add `Definable.fiber` (parameter splitting), starting with the single-parameter case and only
   then the finite-tuple case. Done: `Set.Definable.fiber` and `Set.Definable.fiber_finset` live in
   `ModelTheory.Definability` with the shapes recorded in Design.
5. Add `Set.Finite.biUnion_fibers` on top of `Formula.iExsAtMost`.
6. Prove `algebraicClosure_idem`, then restate the closure-law facts that
   `lem:strongly-minimal-closure-laws` needs in the pregeometry plan.

### Estimated cost

The definition layer is the ~110-line module. The idempotence layer is the real work: parameter
splitting plus the finite-family collapse, estimated at 150–300 lines dominated by formula
bookkeeping, with the single-parameter case as the fallback if the tuple case explodes.

### Verification

For the module changes:

```bash
lake build MorleyCategoricityTheorem
lake exe mk_all --check
lake exe checkdecls blueprint/lean_decls
```

`mk_all --check` and `checkdecls` run unconditionally in the "Validate Lean" CI job and currently
pass; they are not skipped for documentation-only pull requests, so the verification statement must
not call them "not triggered". `Scratch/` is never built by CI or Lake, so while it existed the
`lake env lean` check on its files was author-run and outside the CI gate; after the deletion above
that check no longer applies.

### Completion criteria

- `FirstOrder.Language.IsAlgebraicOver` and `FirstOrder.Language.algebraicClosure` exist with the
  bodies above, the language explicit, and no `sorry`.
- The easy layer is proved with the names listed in Design, the low-level bridges are in
  `ModelTheory.Definability`, and the modules import only the permitted modules.
- `algebraicClosure_idem` is proved, so `lem:strongly-minimal-closure-laws` can be discharged
  without depending on exchange.
- The root import file reflects both new modules and `lake exe mk_all --check` passes.
- `blueprint/` is untouched; the intended `\lean{}` label for `def:algebraic-closure` is recorded in
  this plan for a later authorized blueprint change.
- Both `Scratch/` files no longer exist once the module has landed.

### Deferred follow-ups

- **Cardinality bound.** `lem:algebraic-closure-cardinality` needs a counting lemma over formulas
  and finite parameter tuples; it consumes `isAlgebraicOver_iff_exists_formula` and finite
  character.
- **Matroid packaging.** After `lem:strongly-minimal-exchange`, package `cl_A` with
  `IndepMatroid.ofFinitaryCardAugment` (which also supplies `Finitary`), prove the closure
  identification theorem, and define `dim_A Y := (relMatroid A D).cRk Y` with its
  `InvariantCardinalRank` instance. Supplying the finite Steinitz augmentation is the one proof
  obligation; the shape of the five constructor inputs is the obligation table in Facts above.
- **Upstream candidates.** Parameter splitting and the finite-family collapse are the kind of
  Mathlib-level lemmas the project has promoted before; record them for a possible upstream
  contribution only after a downstream proof uses them.
