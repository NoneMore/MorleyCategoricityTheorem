# Two-cardinal models

## Implementation status

Blueprint [`def:kappa-lambda-model`](../../../blueprint/src/content.tex) is implemented in
[`TwoCardinal.lean`](../../../MorleyCategoricityTheorem/ModelTheory/TwoCardinal.lean) and annotated
in the blueprint ([PR #52](https://github.com/NoneMore/MorleyCategoricityTheorem/pull/52)).

The Vaughtian-pair bridge and the corollary designed below are **not yet formalized**.  The plan is
archived because the definition-node scope is complete; the design of the remaining bridge is kept
here so it can be picked up without repeating the analysis.  The Löwenheim–Skolem side condition
recorded below is not optional bookkeeping: it must be added to the blueprint statement of
`lem:kappa-lambda-model-gives-vaughtian-pair` when the bridge is formalized.

## Scope and status

Blueprint [`def:kappa-lambda-model`](../../../blueprint/src/content.tex) introduces `(κ, λ)`-models: a
model of size `κ` with a one-variable parameter-definable subset of size `λ`.  It is implemented in
[`TwoCardinal.lean`](../../../MorleyCategoricityTheorem/ModelTheory/TwoCardinal.lean) and carries
`\lean{}`/`\leanok` in the blueprint, with its declarations listed in `blueprint/lean_decls`.
The definition node itself is complete; the bridge to Vaughtian pairs
([`lem:kappa-lambda-model-gives-vaughtian-pair`](../../../blueprint/src/content.tex)) and its corollary
are designed below but not yet formalized.

The nodes downstream of the definition are

| node | role of the definition |
|---|---|
| `lem:kappa-lambda-model-gives-vaughtian-pair` | produce a Vaughtian pair from a two-cardinal model |
| `cor:no-small-infinite-definable-sets-without-vaughtian-pairs` | contrapositive: no Vaughtian pairs means no intermediate infinite definable sets |
| `thm:vaught-two-cardinal` | pass from a `(κ, λ)`-model to an `(ℵ₁, ℵ₀)`-model |
| `thm:vaughtian-pair-gives-aleph-one-aleph-zero-model` | states its conclusion as an `(ℵ₁, ℵ₀)`-model |
| `thm:two-cardinal-transfer` | transfers `(ℵ₁, ℵ₀)` upward under `ω`-stability |

## Intent

The two-cardinal notion is the bridge between cardinal arithmetic of definable sets and Vaughtian
pairs.  The only quantitative input is `κ > λ ≥ ℵ₀`: the small definable set has an intermediate
infinite size, and a small elementary submodel containing it turns the pair into a Vaughtian pair.
Everything downstream — Vaught's two-cardinal theorem and the no-Vaughtian-pairs dichotomy — is
stated in terms of this notion, so its interface has to be usable both for a fixed model and as an
existential statement about a theory.

## Existing API

The pieces needed by the definition already exist:

| ingredient | declaration | location |
|---|---|---|
| unary realization set | `Formula.realizationSet₁` | [`Semantics.lean`](../../../MorleyCategoricityTheorem/ModelTheory/Semantics.lean) |
| finite parameter presentation | `Language.definable₁_iff_exists_fin_realizationSet₁` | [`Definability.lean`](../../../MorleyCategoricityTheorem/ModelTheory/Definability.lean) |
| realizability of a definable set | `Formula.realizationSet₁_definable` | [`Definability.lean`](../../../MorleyCategoricityTheorem/ModelTheory/Definability.lean) |
| transport of unary realization sets | `Equiv.image_realizationSet₁` | [`ElementaryMaps.lean`](../../../MorleyCategoricityTheorem/ModelTheory/ElementaryMaps.lean) |
| theory transport along an embedding | `ElementaryEmbedding.theory_model_iff` | Mathlib `ModelTheory.ElementaryMaps` |
| Vaughtian pairs | `Theory.IsVaughtianPair`, `Theory.HasVaughtianPair` | [`VaughtianPair.lean`](../../../MorleyCategoricityTheorem/ModelTheory/VaughtianPair.lean) |
| downward Löwenheim–Skolem | `exists_elementarySubstructure_card_eq` | Mathlib `ModelTheory.Skolem` |
| elementary substructure interface | `ElementarySubstructure.subtype`, `theory_model_iff` | Mathlib `ModelTheory.ElementarySubstructures` |

No Mathlib declaration names two-cardinal models, `(κ, λ)`-models, or Vaught's two-cardinal
theorem, so nothing is duplicated.

## Chosen interface

The definition is unbundled, with the model as an explicit type and the theory as a conjunct, and
its existential companion bundles the model as `ModelType`:

```lean
def FirstOrder.Language.Theory.IsKappaLambdaModel
    (T : L.Theory) (M : Type w) [L.Structure M] (κ μ : Cardinal.{w}) : Prop :=
  M ⊨ T ∧ #M = κ ∧
    ∃ (n : ℕ) (φ : L.Formula (Fin n ⊕ Fin 1)) (a : Fin n → M), #(φ.realizationSet₁ a) = μ

def FirstOrder.Language.Theory.HasKappaLambdaModel
    (T : L.Theory) (κ μ : Cardinal.{w}) : Prop :=
  ∃ M : ModelType.{u, v, w} T, IsKappaLambdaModel T M κ μ
```

Design points:

- **Unbundled model, like `IsVaughtianPair`.**  The bridge proof has to build an elementary
  substructure of the given model and read off its parameters, so consumers work with a concrete
  `M : Type w` and `[L.Structure M]`.  The `M ⊨ T` conjunct keeps the predicate meaningful without
  a `ModelType` binder.  `HasKappaLambdaModel` mirrors `HasVaughtianPair` and is what
  `thm:vaught-two-cardinal` quantifies over; `ModelType` supplies the nonemptiness a Vaughtian
  pair needs.  There is deliberately no introduction lemma `IsKappaLambdaModel T M κ μ →
  HasKappaLambdaModel T κ μ`: `ModelType` requires `Nonempty`, which `#M = κ` does not supply when
  `κ = 0`.  Every planned consumer has `ℵ₀ ≤ μ`, so it gets nonemptiness from `#M = κ ≥ ℵ₀`.
- **The small set is a unary realization set with a `Fin n` parameter tuple.**  This is exactly the
  witness shape of `Theory.IsVaughtianPair`, so the bridge lemma transports the same formula and
  parameters to the elementary submodel instead of translating between encodings.  It loses no
  generality: `Language.definable₁_iff_exists_fin_realizationSet₁` converts every unary set
  definable with parameters in `M` into this form.  The `L[[A]]`-constants presentation is avoided
  for the same reason it is avoided in `VaughtianPair.lean`.
- **`Cardinal.mk`, not `Set.encard`.**  `Set.encard` identifies all infinite cardinalities, which
  is precisely the distinction a two-cardinal notion records.  `Cardinal.mk` also matches the
  cardinality convention of `DefinablyFull.lean` and `ElementaryMaps.lean`.
- **The ordering `κ > λ ≥ ℵ₀` is not part of the definition.**  It is a hypothesis of the
  statements that consume the notion (as it is in the blueprint's own lemma statements), and it
  keeps `HasKappaLambdaModel` usable when `κ`, `λ` are themselves existentially quantified.  The
  price is that degenerate instantiations satisfy the predicate; the docstring records the
  interesting range.
- **The second cardinal is named `μ`.**  `λ` is a keyword in Lean and cannot be a binder; the
  blueprint's `λ` is the mathematical reading of `μ` throughout.

The implemented API is small on purpose:

```lean
theorem isKappaLambdaModel_iff : IsKappaLambdaModel T M κ μ ↔  -- defining form
theorem isKappaLambdaModel_iff_exists_definable₁ :
  IsKappaLambdaModel T M κ μ ↔
    M ⊨ T ∧ #M = κ ∧ ∃ s : Set M, (Set.univ : Set M).Definable₁ L s ∧ #s = μ
namespace IsKappaLambdaModel
theorem model (h : …) : M ⊨ T
theorem card_eq (h : …) : #M = κ
theorem exists_realizationSet₁_card_eq (h : …) : ∃ n φ a, #(φ.realizationSet₁ a) = μ
theorem of_equiv (h : …) (e : M ≃[L] N) : IsKappaLambdaModel T N κ μ
theorem iff_of_equiv (e : M ≃[L] N) : IsKappaLambdaModel T M κ μ ↔ IsKappaLambdaModel T N κ μ
end IsKappaLambdaModel
```

`isKappaLambdaModel_iff_exists_definable₁` is the faithfulness statement of the node: it identifies
the formal definition with the blueprint's prose "one-variable parameter-definable subset".  No
other API is added before a caller needs it.

## Universes and cardinal parameters

`M : Type w` and `κ μ : Cardinal.{w}` keep `#M = κ` a type-correct equation in one universe, as in
`Theory.exists_elementaryExtension_card_eq_with_full_unary_realizations`.  Statements that must
compare with `Cardinal.lift` carry the lifts locally (the Löwenheim–Skolem hypothesis is the only
place this happens).  `HasKappaLambdaModel` fixes the model universe to `w` because a
`ModelType.{u, v, w}` has cardinality in `Cardinal.{w}`; weakening this would only add lifts to
every downstream statement, and no node needs it.

For the same reason `IsKappaLambdaModel.of_equiv` and `iff_of_equiv` take both models in a common
universe: `Equiv.image_realizationSet₁` supports distinct universes for realization sets, but
transporting `#M = κ` across universes would compare `Cardinal.{w}` and `Cardinal.{w'}` values and
needs a lift-stated variant.  No consumer needs that yet; add a lifted version rather than widening
the current API if one appears.

## The Vaughtian-pair bridge

The planned interface for `lem:kappa-lambda-model-gives-vaughtian-pair` is

```lean
theorem IsKappaLambdaModel.hasVaughtianPair
    {T : L.Theory} {M : Type w} [L.Structure M] {κ μ : Cardinal.{w}}
    (h : IsKappaLambdaModel T M κ μ) (hμκ : μ < κ) (hμ : ℵ₀ ≤ μ)
    (hL : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} μ) :
    HasVaughtianPair T
```

Proof plan:

1. Unpack `hT : M ⊨ T`, `hcard : #M = κ` and the witness `φ`, `a`, `hreal : #(φ.realizationSet₁ a) = μ`.
2. Let `s := Set.range a ∪ φ.realizationSet₁ a`.  Then `#s ≤ μ`: the parameter range is bounded by
   the finite type `Fin n`, and `#(φ.realizationSet₁ a) = μ`.
3. Apply `exists_elementarySubstructure_card_eq s μ hμ _ hL _` to obtain `S : L.ElementarySubstructure M`
   with `s ⊆ S` and `lift #S = lift μ`, hence `#S = μ` by `Cardinal.lift_inj`.  The remaining
   hypotheses are `μ ≤ #M`, from `hμκ` and `hcard`.
4. Set `e := S.subtype : S ↪ₑ[L] M`.  Then `S ⊨ T` by
   `ElementarySubstructure.theory_model_iff`, and `e` is not surjective: surjectivity would give
   `#S = #M`, i.e. `μ = κ`, contradicting `hμκ`.
5. Transport the parameters: `a' : Fin n → S` sends `i` to `⟨a i, …⟩`, using `Set.range a ⊆ s ⊆ S`.
   The `M`-realization set `φ.realizationSet₁ a` is contained in `s ⊆ S` by construction, so no
   cardinality comparison is needed to place it inside `S`.
6. Infinitude of the `S`-side witness: `ElementaryEmbedding.mem_realizationSet₁_iff` for
   `e = S.subtype` identifies `φ.realizationSet₁ a'` with the preimage of `φ.realizationSet₁ a`
   under the subtype bijection, so the two sets are equinumerous.  The `M`-side has cardinality
   `μ ≥ ℵ₀`, hence `φ.realizationSet₁ a'` is infinite.
7. Equality of realization sets in the Vaughtian condition: the inclusion
   `e '' φ.realizationSet₁ a' ⊆ φ.realizationSet₁ (e ∘ a')` is
   `ElementaryEmbedding.image_realizationSet₁_subset`.  For the reverse inclusion, take
   `y ∈ φ.realizationSet₁ (e ∘ a')`; then `y ∈ φ.realizationSet₁ a ⊆ S` by step 5, so `y = e ⟨y, _⟩`
   and elementarity puts `⟨y, _⟩` in `φ.realizationSet₁ a'`.

**Blueprint fidelity.**  The blueprint states the lemma without a language-cardinality hypothesis,
but step 3 needs `max (#s, |L|, ℵ₀) ≤ λ`, and that is the only available route: the blueprint's own
`thm:downward-lowenheim-skolem` bounds an elementary submodel by `|X| + |L| + ℵ₀`, not by `λ`.

The resolution is to align the statement with the side condition rather than to look for an
Löwenheim–Skolem-free proof.  The Lean statement carries `hL : |L| ≤ μ`, and when the bridge is
formalized the blueprint statement of `lem:kappa-lambda-model-gives-vaughtian-pair` gains the
matching hypothesis `|L| ≤ λ`.  Countable-language consumers (`thm:vaught-two-cardinal`) discharge
it through `ℵ₀ ≤ λ`, so no downstream node changes.  The hypothesis is not cosmetic: a language with
`λ⁺` distinct constants admits no `L`-substructure of size `λ`.

The corollary `cor:no-small-infinite-definable-sets-without-vaughtian-pairs` is the
contrapositive: given `¬ HasVaughtianPair T`, a model `M ⊨ T` with `#M = κ`, and `s` definable,
infinite, with `#s ≠ κ`, one has `#s < κ` by `#s ≤ #M`, so `isKappaLambdaModel_iff_exists_definable₁`
makes `M` a `(κ, #s)`-model and the bridge lemma contradicts `¬ HasVaughtianPair T`.  This
statement inherits the same language-cardinality side condition; the blueprint's uses are in a
countable language.

A direct `IsVaughtianPair`-shaped conclusion (naming the elementary substructure) is deliberately
not part of the interface: `HasVaughtianPair` is what every downstream node consumes, and the
explicit substructure is an implementation detail of the proof.

## Module layout

`TwoCardinal.lean` is the two-cardinal layer.  It currently imports `Mathlib.ModelTheory.Bundled`
and `ElementaryMaps` and contains the definition and its API.  Adding the bridge will add
`VaughtianPair` and `Mathlib.ModelTheory.Skolem` to the imports; the corollary lives in the same
module because it is a one-step contrapositive of the bridge.  `VaughtianPair.lean` is not modified:
the dependency direction stays `TwoCardinal → VaughtianPair`, so the Vaughtian-pair module remains
usable without the two-cardinal notion.

`thm:vaught-two-cardinal` and `thm:two-cardinal-transfer` need the homogeneous-pair and
`ω`-stability material, so they belong to later modules that import `TwoCardinal`; they are out of
scope here.

## Implementation order

1. Definition, projection and characterization lemmas, isomorphism transport (done).
2. `isKappaLambdaModel_iff_exists_definable₁` as the faithfulness bridge (done).
3. `IsKappaLambdaModel.hasVaughtianPair` by the Löwenheim–Skolem route above.
4. `HasKappaLambdaModel.hasVaughtianPair` by unpacking the `ModelType`, for the blueprint's
   theory-level phrasing.
5. `cor:no-small-infinite-definable-sets-without-vaughtian-pairs`.
6. Annotate the two nodes and regenerate `blueprint/lean_decls`.

## Verification

- `lake build MorleyCategoricityTheorem` after each step.
- `lake exe mk_all --check` whenever a module is added (already needed for `TwoCardinal.lean`).
- `lake exe checkdecls blueprint/lean_decls` after annotating nodes.
- `python3 -m unittest discover -s scripts/tests -v` and
  `python3 scripts/blueprint_status.py --milestones` for the blueprint tooling.
