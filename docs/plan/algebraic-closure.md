# Algebraic Closure Over Definable Sets

## Intent

Give the semantic layer a first-class notion of model-theoretic algebraicity: a predicate "`b` is
algebraic over the parameter set `A`" and the set `algebraicClosure A`, both matching blueprint
`def:algebraic-closure` ("An element `b ∈ M` is algebraic over `A` if it belongs to a finite set
definable with parameters from `A`. The algebraic closure `acl(A)` is the set of all elements
algebraic over `A`.").

```lean
def FirstOrder.Language.IsAlgebraicOver (L : Language.{u, v}) {M : Type w} [L.Structure M]
    (A : Set M) (b : M) : Prop :=
  ∃ s : Set M, s.Finite ∧ A.Definable₁ L s ∧ b ∈ s

def FirstOrder.Language.algebraicClosure (L : Language.{u, v}) {M : Type w} [L.Structure M]
    (A : Set M) : Set M :=
  {b | IsAlgebraicOver L A b}
```

This is the semantic layer's only notion of "parameter-definable finiteness", so it is also the
entry point for the strongly-minimal pregeometry and dimension chain. Its direct blueprint consumers
are `prop:algebraic-implies-isolated`, `def:strongly-minimal-pregeometry`
(`cl_A X = D ∩ acl(A ∪ X)`), `lem:strongly-minimal-closure-laws` (reflexive, monotone, idempotent,
finite character), `lem:nonalgebraic-type-many-realizations`, and
`lem:algebraic-closure-cardinality`.

Scope: the definition, the laws that follow from definability and finiteness, and idempotence, which
the blueprint needs before exchange. Exchange, the cardinality bound, pregeometry, and matroid
packaging stay out (see Deferred follow-ups).

## API facts

Mathlib (`v4.34.1`) has no model-theoretic algebraic closure. Below the project's semantic bridges
it provides the definability layer: `Set.Definable A L s` (a formula with parameters witnesses it),
the unary `Set.Definable₁`, `Set.Definable.mono` (monotonicity in parameters),
`Set.Definable.singleton_of_mem` (reflexivity), `Set.definable_iff_finitely_definable` (finite
character), `Set.definable_iff_exists_formula_sum` (formula witness), and the bundled
`L.DefinableSet` (not needed). The project's `ModelTheory/Semantics.lean` adds
`Formula.realizationSet`/`realizationSet₁`, their `Fin 1` shape conversions, and the counting
formulas `Formula.iExsAtLeast`/`iExsAtMost`/`iExsExactly`; importing it does not pull in
`ElementaryMaps` or the type-space layer.

`FirstOrder.Language.IsAlgebraic` already exists (`Mathlib/ModelTheory/Basic.lean`) meaning "the
language has no relation symbols", so the element predicate is `IsAlgebraicOver`. `algebraicClosure`
is free in `FirstOrder.Language` (`IntermediateField.algebraicClosure` is a different namespace).

## Design

### Definitions and rationale

- **Unbundled.** A plain `Prop` with an `∃` body plus a plain `Set`, both definitionally
  transparent, so `b ∈ acl A`, `D ∩ acl (A ∪ X)`, `rintro`, and the formula bridge work directly.
  Bundling into `L.DefinableSet` is wrong: algebraicity is not itself a definable set, only
  witnessed by one.
- **Language explicit on the objects, implicit on the lemmas.** `A : Set M` and `b : M` do not
  determine `L`, so the objects take it explicitly and callers write `L.algebraicClosure A`. Every
  lemma statement mentions `L.algebraicClosure`, `L.IsAlgebraicOver`, or `L.Formula`, so the lemmas
  take `{L}` and callers write `algebraicClosure_mono hAB` or `mem_algebraicClosure_iff.mp h`; a
  lemma that needs `(L := L)` at a call site has lost the occurrence from its statement.
- **`Definable₁` is the definability primitive.** It is what `Definable.mono` and
  `Definable.singleton_of_mem` produce, and what `definable_iff_finitely_definable` consumes by
  defeq.
- **`∃ s, s.Finite ∧ …` rather than a count-based phrasing**: matches the blueprint, keeps
  `Set.Finite` as the only finiteness notion, and leaves counting formulas to idempotence, where
  they are genuinely needed.
- **Namespace `FirstOrder.Language`, no notation**: consistent with `Theory.IsOmegaStable`; notation
  would add blueprint-matching friction without a caller.

### Public API and module placement

- Easy layer: `mem_algebraicClosure_iff` (unfolding, `@[simp]`), `subset_algebraicClosure`
  (reflexive), `algebraicClosure_mono`, `mem_algebraicClosure_iff_exists_finset` (finite
  character), `isAlgebraicOver_iff_exists_realizationSet₁` (the unary formula form that
  `prop:algebraic-implies-isolated` and `lem:nonalgebraic-type-many-realizations` need), and
  `isAlgebraicOver_iff_exists_formula` (the `Fin 1 → M` restatement).
- Idempotence layer: `isAlgebraicOver_of_isAlgebraicOver_union_singleton` (the single-parameter
  counting step), `isAlgebraicOver_of_finset_subset_algebraicClosure` (`Finset.induction` over it),
  `algebraicClosure_idem`, and the absorption form `algebraicClosure_union_eq`.

Low-level lemmas live where their content belongs. `ModelTheory.Definability` holds the
realization-set bridges (`Set.definable_iff_exists_realizationSet`,
`Set.definable_realizationSet`), the unary bridge `Set.definable₁_iff_exists_realizationSet₁`, and
the counting-definability facts `Set.definable_setOf_fiber_encard_le` and
`Set.Definable.exists_fiber`. `ModelTheory.Semantics` holds the set-level unary identity
`Set.image_fin_one_eq` beside its formula-level counterpart
`Formula.realizationSet_fin_one_image`. `ModelTheory.AlgebraicClosure` keeps the finite-family
collapse at its single use site, applying `Set.Finite.biUnion` with
`Set.finite_of_encard_le_coe` directly rather than exporting a one-use wrapper. The bridges were
split out of `ModelTheory.DefinablyFull`, which imports `ElementaryMaps`; `DefinablyFull` imports
the bridge module, so no declaration moved out of reach.

The unary shape is the primary statement because `Formula.realizationSet₁` and
`Formula.realizationSet_fin_one_image` already carry the `Fin 1` bookkeeping; the `Fin 1 → M` form
derives from it. `Set.definable₁_iff_exists_realizationSet₁` is the unary specialization of the
realization-set bridge, using `Set.image_fin_one_eq` for the set-level image step.

### Idempotence

The blueprint orders `lem:strongly-minimal-closure-laws` **before** `lem:strongly-minimal-exchange`,
so idempotence cannot be deferred to exchange, and exchange alone does not give it. It is provable
here: `acl` is idempotent for every first-order structure, by a counting argument that needs only
counting formulas and finite parameter sets.

Take `b ∈ acl (acl A)`. Finite character gives `b ∈ acl (A ∪ F)` for a finite
`F = {c₁, …, cₙ} ⊆ acl A`, and each `cᵢ` lies in a finite `A`-definable `Sᵢ`; take a formula
`φ(x, ȳ)` over `A` whose realization set at `c̄` is finite of cardinality `m` and contains `b`. Then

```text
ψ(x) := ∃ ȳ (⋀ᵢ yᵢ ∈ Sᵢ ∧ φ(x, ȳ) ∧ ∃^{≤m} x′ φ(x′, ȳ))
```

contains `b`, and `ψ(M)` sits inside the union of the fibers `φ(M, ȳ)` over the finite set
`∏ᵢ Sᵢ`, each contributing fiber bounded by `m`; hence `ψ(M)` is finite. This is "an algebraic
family of finite sets has finite union", and `def:counting-formulas` already provides the
constructors it consumes.

One piece of infrastructure is private to the capability:

- **Parameter splitting** (`exists_fiber_formula`): `(A ∪ {c}).Definable₁ L s` yields a formula of
  type `L.Formula (A ⊕ (Fin 1 ⊕ Fin 1))` whose `c`-fiber is `s`, which is the shape
  `Formula.iExsAtMost` bounds. Mathlib moves parameters only along `⊆` (`Set.Definable.mono`), so
  this is a relabelling along a map that keeps the `A`-parameters in place and moves the rest into
  the tuple. It stays private: the counting step is the only consumer, and it needs the formula
  shape rather than a set-shaped splitting lemma.

The finite-family collapse is inlined instead of named: `hVfin.biUnion` with
`Set.finite_of_encard_le_coe` is applied at its only use site, where the "contributing" formulation
lets the caller exclude the fibers that the counting conjunct rejects. The unary `Fin 1`/`M` shape
conversions go through one private `finOne_eta` helper built on `Equiv.funUnique`, so the round trip
appears once rather than at each call site.

Two design points: the step is single-parameter and iteration is `Finset.induction`, which keeps the
argument in `Fin 1` coordinates and avoids conjoining one formula per parameter; and the bound is
the size of the fiber through `c`, supplied honestly by `Finite.exists_encard_eq_coe` and identified
with the `c`-fiber by `Set.InjOn.encard_image`, so no `ncard`/`encard` conversion is needed. The
counting formulas and the splitting lemma have no consumer before exchange, so they landed in this
capability rather than in a separate plan.

### Exchange and matroid packaging (recorded for the follow-up)

Mathlib has infinite matroids (`Mathlib/Combinatorics/Matroid/`): `Matroid`, `IsBase`, `Indep`,
`Matroid.ExchangeProperty`, `closure` as a `ClosureOperator`, `Finitary`, the `ℕ∞`-valued
`eRank`/`eRk`, and the cardinal-valued `cRank`/`cRk` with `InvariantCardinalRank`. It has no
pregeometry and no constructor from a closure operator with exchange; the entry points are
`IndepMatroid.ofFinitary*` (independence first, also yielding `Finitary`) and `Matroid.ofBase`.

Four facts constrain any follow-up:

- **Augmentation is false without exchange.** On `M = ℕ × ℕ` with the unary function
  `f (i, j) = (i, 0)`, take `A = ∅`, `D = M`, `I = {(0, 0)}`, `J = {(0, 1), (0, 2)}`: both sets are
  independent and `|I| < |J|`, but no `e ∈ J \ I` can be added to `I`, because `f e = (0, 0)` is
  then algebraic over `I ∪ {e}`.
- **Exchange must be restricted to `D`.** On `M = ℕ × Bool` with `f (n, t) = (n, false)`,
  `D = {x | f x = x} = ℕ × {false}` is strongly minimal, yet with `A = X = ∅`, `b = (0, false)`,
  `c = (0, true)` we have `b = f c ∈ acl {c} ∩ D` and `b ∉ acl ∅`, but `c ∉ D`. The restricted form
  states exchange with `X ⊆ D` and `c ∈ D`, which is the standard form and suffices for finite
  augmentation, since every independent set is a subset of `D`.
- **The blueprint statement of `lem:strongly-minimal-exchange` needs those hypotheses.** As written
  it quantifies `c` freely, which the counterexample refutes; its formal statement must carry
  `X ⊆ D` and `c ∈ D`. That is an authorized blueprint-text fix outside this capability.
- **`cRk`, not `eRk`.** `eRk` sends every infinite base to `∞` and cannot state `dim_A(Y) = |Y|` for
  uncountable `Y`; `cRk` is well behaved for a finitary matroid (`IsBasis'.cardinalMk_eq`,
  `IsBasis'.cardinalMk_eq_cRk`), so the blueprint's `dim_A^M(Y)` must be `cRk`.

**Closure identification is a deliverable, not an assumption.** Constructing the matroid does not
prove `M.closure X = D ∩ acl (A ∪ X)`. The follow-up must prove it on all `X ⊆ D` from
`M.Indep.notMem_closure_iff_of_notMem` (`e ∉ M.closure I ↔ M.Indep (insert e I)` for independent `I`)
before using `Matroid.closure` for model-theoretic closure.

## Constraints

- The definitional bodies above stay fixed, so downstream `rintro` and the formula bridge stay
  stable.
- Import boundary: `AlgebraicClosure` imports Mathlib's `ModelTheory.Definability`, the low-level
  `MorleyCategoricityTheorem.ModelTheory.Definability`, `ModelTheory.Semantics`, and
  `Mathlib.Data.Set.Finite.Lattice` (for `Set.Finite.biUnion`). It must not import `DefinablyFull`,
  `ElementaryMaps`, `Types`, or any type-space module, and the low-level `Definability` module
  imports only Mathlib's definability layer plus `Semantics`.
- Variables and universes are explicit, because the project builds with `autoImplicit = false`.
- No declaration may be named `IsAlgebraic` or otherwise clash with the relation-free-language
  class.
- No matroid, pregeometry, dimension, `ClosureOperator`, notation, or `DefinableSet`-valued API
  without a concrete caller; no exchange or cardinality bound in this capability.
- No `blueprint/` change here; the `\lean{}` label for `def:algebraic-closure` is a later authorized
  change.

## Deferred follow-ups

| Item | State |
|---|---|
| exchange (`lem:strongly-minimal-exchange`) | separate node; state with `X ⊆ D`, `c ∈ D` |
| cardinality bound (`lem:algebraic-closure-cardinality`) | counting over formulas and finite parameter tuples; consumes `isAlgebraicOver_iff_exists_formula` and finite character |
| pregeometry and dimension | `def:strongly-minimal-pregeometry` onward |
| matroid packaging | gated on exchange and on the closure identification theorem |

The pregeometry plan defines `cl_A X = D ∩ acl (A ∪ X)` and should cite the `acl`-level laws rather
than reprove them: reflexive `subset_algebraicClosure`, monotone `algebraicClosure_mono`, idempotent
`algebraicClosure_idem`, finite character `mem_algebraicClosure_iff_exists_finset`, and absorption
`algebraicClosure_union_eq` (`B ⊆ acl A → acl (A ∪ B) = acl A`). Note that `cl_A`
is idempotent only for `X ⊆ D`: without that restriction the inclusion
`cl_A X ⊆ cl_A (cl_A X)` can fail, because an element of `acl (A ∪ X) ∩ D` may need parameters
outside `D`. No `cl_A`-level restatement belongs to this capability.

`lem:algebraic-closure-cardinality` needs a counting lemma over formulas and finite parameter tuples.
The definition deliberately exposes only "there exists a finite set", so add a canonical enumeration
of formulas in that capability rather than weakening this definition.

Matroid packaging: after exchange, package `cl_A` with `IndepMatroid.ofFinitaryCardAugment` (which
also supplies `Finitary`), prove the closure identification, and define
`dim_A Y := (relMatroid A D).cRk Y` with its `InvariantCardinalRank` instance; the finite Steinitz
augmentation is the one proof obligation. Parameter splitting and the unary shape helper stay
private; promoting either needs a second caller.

Wire the `\lean{}` label of `def:algebraic-closure` to the names above in an authorized blueprint
change; renaming later would orphan the reference.

## Verification

```bash
lake build MorleyCategoricityTheorem
lake exe mk_all --check
lake exe checkdecls blueprint/lean_decls
```

`mk_all --check` and `checkdecls` run unconditionally in the "Validate Lean" CI job, including for
documentation-only pull requests. Completion: both objects exist with the bodies above and no
`sorry`; the API above is proved; the modules import only the permitted modules; the root import
file reflects the new modules and `mk_all --check` passes; `blueprint/` is untouched.
