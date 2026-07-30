# TODO: Complete-Type Reindexing Along Variable Maps

## Branch boundary

Implement this work on a new branch based on commit
`49aad642283e2d7fe41ba938894effa42aa298e1`.

This file records the design only. Do not mix the implementation with the current proof-development
changes in `MorleyCategoricityTheorem/ModelTheory/Types.lean`.

## Motivation

The proof of
`FirstOrder.Language.Theory.CompleteType.isIsolated_typeOf_left` repeatedly transports formulas and
types along

```lean
Sum.inl : α → α ⊕ β
```

For a sentence `ϕ ∈ T.typeOf a`, the proof currently constructs

```lean
let χ : L.Formula (α ⊕ β) :=
  (Formula.equivSentence.symm ϕ).relabel Sum.inl
```

and then manually proves that `Formula.equivSentence χ` belongs to
`T.typeOf (Sum.elim a b)`. This is an instance of a general reindexing operation on complete types
and should not expose formula relabeling, temporary constant structures, or realization
bookkeeping at each call site.

## Variance

Reindexing is contravariant. A function

```lean
f : α → β
```

should induce

```lean
CompleteType.reindex f : T.CompleteType β → T.CompleteType α
```

by restricting a `β`-indexed type to formulas whose variables are relabeled along `f`.

Consequently:

- if `f` is injective, `CompleteType.reindex f` is expected to be surjective;
- if `f` is surjective, `CompleteType.reindex f` is expected to be injective;
- an injection `α ↪ β` does not canonically extend an `α`-type to a `β`-type;
- an actual embedding in the covariant direction requires a chosen retraction, or equivalently a
  section of the induced restriction map.

For `Sum.inl : α ↪ α ⊕ β`, the natural map is therefore the projection

```lean
T.CompleteType (α ⊕ β) → T.CompleteType α.
```

## Reference design in `StabilityTheory`

Follow the pattern already used in the sibling `StabilityTheory` repository:

- `LHom.lhomWithConstantsMap_injective` shows that an injection of index types induces an
  injective map of languages with constants.
- `PartialType.restrictSet` defines restriction as a preimage under the induced formula map.
- `CompleteTypeOver.restrict` passes through
  `CompleteType.toPartialType`, restriction, and `PartialType.toCompleteType`.
- `CompleteTypeOver.restrict_surjective` proves that restriction along an inclusion of parameter
  sets is surjective.

The present repository does not depend on `StabilityTheory`. Mirror the interface and proof
structure locally; do not introduce a filesystem or Lake dependency on the sibling repository.

## Core interface

Introduce the main operation in the `CompleteType` namespace:

```lean
def CompleteType.reindex
    (f : α → β) (p : T.CompleteType β) :
    T.CompleteType α
```

The implementation should stay behind this interface. Callers should not need to know how the
underlying maximal theory, model reduct, or temporary constants structures are constructed.

The fundamental membership theorem should be stated for formulas:

```lean
@[simp]
theorem CompleteType.formula_mem_reindex
    (f : α → β) (p : T.CompleteType β) (φ : L.Formula α) :
    Formula.equivSentence φ ∈ p.reindex f ↔
      Formula.equivSentence (φ.relabel f) ∈ p
```

If the implementation naturally produces a sentence-level transport operation, keep it private
unless a second caller needs it. Formula-level membership is the intended public test surface.

## Semantic naturality

Prove compatibility with realized types:

```lean
@[simp]
theorem CompleteType.reindex_typeOf
    {M : Type*} [L.Structure M] [Nonempty M] [M ⊨ T]
    (f : α → β) (v : β → M) :
    (T.typeOf v).reindex f = T.typeOf (v ∘ f)
```

This theorem should reduce to `Formula.realize_relabel`. Also expose the direct formula-level
corollary when it shortens callers:

```lean
@[simp]
theorem CompleteType.relabel_mem_typeOf_iff
    {M : Type*} [L.Structure M] [Nonempty M] [M ⊨ T]
    (f : α → β) (v : β → M) (φ : L.Formula α) :
    Formula.equivSentence (φ.relabel f) ∈ T.typeOf v ↔
      Formula.equivSentence φ ∈ T.typeOf (v ∘ f)
```

Add the functorial laws:

```lean
@[simp]
theorem CompleteType.reindex_id
    (p : T.CompleteType α) :
    p.reindex id = p

@[simp]
theorem CompleteType.reindex_comp
    (p : T.CompleteType β) (f : α → β) (g : γ → α) :
    (p.reindex f).reindex g = p.reindex (f ∘ g)
```

Prefer proving these through `formula_mem_reindex` and extensionality rather than unfolding the
implementation.

## Injectivity and surjectivity

Prove the variance-sensitive mapping properties:

```lean
theorem CompleteType.reindex_surjective_of_injective
    {f : α → β} (hf : Function.Injective f) :
    Function.Surjective (CompleteType.reindex (T := T) f)

theorem CompleteType.reindex_injective_of_surjective
    {f : α → β} (hf : Function.Surjective f) :
    Function.Injective (CompleteType.reindex (T := T) f)
```

For an equivalence `e : α ≃ β`, package reindexing as an equivalence of complete-type spaces only
if this removes repeated inverse calculations:

```lean
def CompleteType.reindexEquiv (e : α ≃ β) :
    T.CompleteType β ≃ T.CompleteType α
```

Do not add both specialized `restrictVars` and generic `reindex` interfaces unless a caller
demonstrates that the former materially improves readability.

## Topology and isolation

After the semantic interface is stable, prove continuity:

```lean
theorem CompleteType.continuous_reindex (f : α → β) :
    Continuous (CompleteType.reindex (T := T) f)
```

For injective `f`, investigate the stronger statement that reindexing is an open map:

```lean
theorem CompleteType.isOpenMap_reindex
    {f : α → β} (hf : Function.Injective f) :
    IsOpenMap (CompleteType.reindex (T := T) f)
```

The image of a basic open set should be represented by existentially quantifying the variables
outside the image of `f`. For a general injection, keep the finite support of the formula explicit
internally; do not require a global complement type in the public statement.

Use openness, or its direct semantic proof if substantially simpler, to obtain:

```lean
theorem CompleteType.IsIsolated.reindex
    {f : α → β} {p : T.CompleteType β}
    (hp : p.IsIsolated) (hf : Function.Injective f) :
    (p.reindex f).IsIsolated
```

This is the abstraction that should absorb the existential-closure argument currently written
inside `isIsolated_typeOf_left`.

## Refactor `isIsolated_typeOf_left`

Once `reindex_typeOf` and isolation under injective reindexing are available, reduce
`isIsolated_typeOf_left` to the specialization `f := Sum.inl`. Its proof should have the shape

```lean
simpa only [CompleteType.reindex_typeOf, Sum.elim_comp_inl] using
  h.reindex (f := Sum.inl) Sum.inl_injective
```

Adjust argument order and names to the final interface.

The local formula `χ` and all explicit manipulation of:

- `Formula.equivSentence`;
- `Formula.relabel`;
- `BoundedFormula.constantsVarsEquiv`;
- `Function.extend`;
- temporary `constantsOn` structures;
- reduct and expansion instances;

should disappear from this theorem.

## Implementation order

1. Search the current Mathlib dependency again for an upstream complete-type reindexing operation.
2. Define `CompleteType.reindex`.
3. Prove `formula_mem_reindex`.
4. Prove `reindex_typeOf`, `reindex_id`, and `reindex_comp`.
5. Prove the injectivity and surjectivity results.
6. Prove continuity.
7. Prove openness or the direct isolation-preservation theorem for injective maps.
8. Refactor `isIsolated_typeOf_left`.
9. Check whether the blueprint proof of projection of isolated types should mention the generic
   reindexing result.

## Validation

For Lean-only changes without new imports:

```bash
lake build MorleyCategoricityTheorem
```

If modules or imports change, additionally run:

```bash
lake exe mk_all --check
```

If the blueprint statement, proof, declaration link, or status changes, also run:

```bash
leanblueprint all
```

## Non-goals

- Do not assume that `T` is complete; the reindexing and isolated-projection results hold for an
  arbitrary theory admitting the relevant complete types.
- Do not add a canonical covariant extension of complete types along an injection.
- Do not expose witness-extension or temporary-structure bookkeeping in the public interface.
- Do not import or depend directly on the sibling `StabilityTheory` repository.
- Do not retain the current long proof merely as a private helper behind the new theorem.
