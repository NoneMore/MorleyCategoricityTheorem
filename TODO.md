# TODO

## Finite Cardinality of Formula Fibers under Elementary Embeddings

### Intended abstraction

Treat exact finite realization count as a formula constructor, not merely as a meta-level
predicate. The general object is the fiber of a formula

```lean
φ : L.Formula (β ⊕ α)
```

over a fixed parameter tuple `v : β → M`. Its realizations are the `α`-tuples

```lean
{x : α → M | φ.Realize (Sum.elim v x)}.
```

Require `[Finite α]`, since the construction must quantify an entire `α`-tuple. Do not require
`[Finite β]`: the `β`-variables remain free. Put the free variables on the left and the variables
to be quantified on the right so that the API agrees with Mathlib's `Formula.iExs` and
`Formula.iExsUnique` conventions.

Implement three constructors in `FirstOrder.Language.Formula`:

```lean
noncomputable def iExsAtLeast (α : Type*) [Finite α]
    (n : ℕ) (φ : L.Formula (β ⊕ α)) : L.Formula β

noncomputable def iExsAtMost (α : Type*) [Finite α]
    (n : ℕ) (φ : L.Formula (β ⊕ α)) : L.Formula β

noncomputable def iExsExactly (α : Type*) [Finite α]
    (n : ℕ) (φ : L.Formula (β ⊕ α)) : L.Formula β
```

The first constructor is primitive. Define the other two by

```lean
φ.iExsAtMost α n  := (φ.iExsAtLeast α (n + 1)).not
φ.iExsExactly α n := φ.iExsAtLeast α n ⊓ φ.iExsAtMost α n
```

This is simpler than directly asserting that `n` witnesses exhaust the realization set. It also
separates the reusable lower- and upper-bound formulas needed in later arguments.

### Construction of `iExsAtLeast`

Use the finite variable block

```lean
Fin n × α
```

to encode `n` candidate `α`-tuples. An assignment `w : Fin n × α → M` represents the tuple
`fun a ↦ w (i, a)` at index `i : Fin n`.

For each `i`, relabel `φ` so that its `α`-variables refer to the `i`th candidate:

```lean
private def realizeAt (φ : L.Formula (β ⊕ α)) (i : Fin n) :
    L.Formula (β ⊕ (Fin n × α)) :=
  φ.relabel (Sum.map id (fun a ↦ (i, a)))
```

Express inequality of the candidates at `i` and `j` by saying that not every coordinate is equal:

```lean
private noncomputable def tupleNe (i j : Fin n) :
    L.Formula (β ⊕ (Fin n × α)) :=
  (Formula.iInf fun a : α ↦
    (Term.var (Sum.inr (i, a))).equal
      (Term.var (Sum.inr (j, a)))).not
```

Index the distinctness conjunction by unequal pairs, for example

```lean
private abbrev NePair (n : ℕ) :=
  {ij : Fin n × Fin n // ij.1 ≠ ij.2}
```

and form a body asserting that every candidate realizes `φ` and all candidates are distinct:

```lean
let witnessesRealize := Formula.iInf fun i : Fin n ↦ realizeAt φ i
let witnessesDistinct := Formula.iInf fun ij : NePair n ↦ tupleNe ij.1.1 ij.1.2
let body := witnessesRealize ⊓ witnessesDistinct
```

Finally quantify the complete witness block:

```lean
body.iExs (Fin n × α)
```

The displayed code is an implementation blueprint. Adjust explicit type annotations and namespace
qualification as required during elaboration, while preserving this variable layout.

The use of `tupleNe` correctly handles an empty `α`: there is only one empty tuple, because the
conjunction of coordinate equalities is vacuously true and its negation is false.

### Semantic specifications

Prove semantics in two layers. First normalize the formula into an injective enumeration of
solutions:

```lean
theorem realize_iExsAtLeast_iff_exists_injective
    [Finite α] [L.Structure M] (φ : L.Formula (β ⊕ α)) (v : β → M) :
    (φ.iExsAtLeast α n).Realize v ↔
      ∃ f : Fin n → (α → M),
        (∀ i, φ.Realize (Sum.elim v (f i))) ∧ Function.Injective f
```

The proof should unfold only the local constructors and simplify with:

- `Formula.realize_iExs`;
- `Formula.realize_iInf`;
- `Formula.realize_inf` and `Formula.realize_not`;
- `Formula.realize_relabel`;
- `Formula.realize_equal` and `Term.realize_var`;
- `Function.injective_iff_pairwise_ne` or an equivalent pairwise formulation.

Then isolate the set-cardinality reasoning in a pure helper relating an injection from `Fin n` to a
set with its extended cardinality. Use it to expose the public semantic API:

```lean
@[simp]
theorem realize_iExsAtLeast [L.Structure M]
    [Finite α] (φ : L.Formula (β ⊕ α)) (v : β → M) :
    (φ.iExsAtLeast α n).Realize v ↔
      (n : ℕ∞) ≤ {x : α → M | φ.Realize (Sum.elim v x)}.encard

@[simp]
theorem realize_iExsAtMost [L.Structure M]
    [Finite α] (φ : L.Formula (β ⊕ α)) (v : β → M) :
    (φ.iExsAtMost α n).Realize v ↔
      {x : α → M | φ.Realize (Sum.elim v x)}.encard ≤ n

@[simp]
theorem realize_iExsExactly [L.Structure M]
    [Finite α] (φ : L.Formula (β ⊕ α)) (v : β → M) :
    (φ.iExsExactly α n).Realize v ↔
      {x : α → M | φ.Realize (Sum.elim v x)}.encard = n
```

`Set.encard` is appropriate here because the right-hand sides compare with a natural number. In
particular, an infinite realization set has `encard = ⊤`, so it satisfies every `iExsAtLeast` but
no `iExsExactly`.

Record the following semantic boundary cases after the main theorem, either as lemmas or as
documented consequences:

- `iExsExactly α 0` means that `φ` has no `α`-tuple realization;
- `iExsExactly α 1` is semantically equivalent to `iExsUnique α`;
- `iExsAtMost α n` rules out `n + 1` pairwise distinct realizations;
- the definitions work when `α` or `Fin n` is empty.

### Wrapper for variables ordered as `α ⊕ β`

When a caller naturally supplies the solution variables first, provide a small wrapper using
`Sum.swap` rather than duplicating the construction:

```lean
noncomputable def existsExactlyLeft [Finite α]
    (φ : L.Formula (α ⊕ β)) (n : ℕ) : L.Formula β :=
  (φ.relabel Sum.swap).iExsExactly α n
```

Its semantic corollary should have the caller-facing orientation

```lean
(φ.existsExactlyLeft n).Realize v ↔
  {x : α → M | φ.Realize (Sum.elim x v)}.encard = n.
```

The core API should nevertheless remain `β ⊕ α`, matching Mathlib's indexed quantifiers.

### Preservation by elementary embeddings

Once `realize_iExsExactly` is available, finite realization counts are first-order properties.
Apply `ElementaryEmbedding.map_formula` to `φ.iExsExactly α n`, then rewrite both sides with its
semantic theorem. The explicit-parameter result should be:

```lean
theorem ElementaryEmbedding.encard_realizations_eq_coe_iff
    [Finite α] (e : M ↪ₑ[L] N) (φ : L.Formula (β ⊕ α)) (b : β → M) (n : ℕ) :
    {x : α → N | φ.Realize (Sum.elim (e ∘ b) x)}.encard = n ↔
      {x : α → M | φ.Realize (Sum.elim b x)}.encard = n
```

For formulas whose parameters are encoded as constants, do not add a parallel family of
constants-language lemmas. Convert `φ : L[[A]].Formula α` with
`BoundedFormula.constantsVarsEquiv` and apply the explicit-parameter result with parameter type
`A` and parameter map `(↑) : A → M`. At the definability boundary,
`Set.definable_iff_exists_formula_sum` packages exactly this conversion.

Finally derive the interface required by the elementary-chain proof:

```lean
Set.Infinite targetRealizations ↔ Set.Infinite sourceRealizations
```

For the forward implication, argue contrapositively: a finite source set has some exact natural
cardinality, which is preserved in the target. For the reverse implication, use the realization
subtype embedding from the Cardinal monotonicity section below. This rules out a realization set
that is finite at one stage but infinite in the elementary-chain limit.

### Generalization boundary

The `β ⊕ α` constructor already handles arbitrary finite tuple arity and arbitrary parameter
tuples, so it is more general than the unary application needed in `DefinableSet.lean`. A further
indexed variant may replace `Fin n` by an arbitrary finite type `ι` to express at least
`ENat.card ι` realizations. Keep the natural-number API primary, since `atMost` and `exactly` use
the successor `n + 1`.

Do not attempt to drop `[Finite α]`. Quantifying a complete assignment `α → M` for infinite `α`
is not expressible by a single ordinary first-order formula.

## Cardinal Monotonicity under Elementary Extensions

Mathlib currently has no dedicated lemma stating that the cardinality of a parameter-definable set
cannot decrease under an elementary embedding. Add a local lemma asserting that if
`e : M ↪ₑ[L] N`, then the realization subtype of a formula in `M` embeds into the corresponding
realization subtype in `N`, with every parameter transported along `e`.

The result must compare `Cardinal.mk`, not `Set.encard`:

```lean
#({x : α → M | φ.Realize (Sum.elim b x)}) ≤
  #({x : α → N | φ.Realize (Sum.elim (e ∘ b) x)})
```

This distinction is essential: `Set.encard` has value `⊤` for every infinite set, so an
`encard` inequality cannot transfer a lower bound by an arbitrary infinite cardinal `κ`. The
final theorem needs the displayed `Cardinal.mk` inequality to transport `κ` realizations from a
successor stage into the elementary-chain limit.

The intended proof should combine the following existing APIs:

- `ElementaryEmbedding.map_formula`, which preserves and reflects formula realization;
- a bundled embedding between the two realization subtypes, whose underlying function sends
  `⟨x, hx⟩` to `⟨e ∘ x, ...⟩`; use `e.map_formula` to prove realization and `e.injective`
  pointwise to prove injectivity;
- `Cardinal.mk_le_of_injective`, applied to that subtype embedding.

State the explicit-parameter version for `φ : L.Formula (β ⊕ α)` without a finiteness assumption
on `α`; pointwise transport of a free tuple does not require first-order quantification over all of
`α`. Keep `Set.encard` only for the finite exact-`n` specification in the preceding section; do not
use it for infinite-cardinal monotonicity.
