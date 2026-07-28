# TODO: Refactor the One-Step Full Unary Realization Construction

## Goal

Refactor the proof of
`Theory.exists_elementaryExtension_card_eq_with_full_unary_realizations` in
`MorleyCategoricityTheorem/ModelTheory/DefinablyFull.lean` so that its structure matches the
model-theoretic argument:

1. collect the unary formulas over the base model with infinite realization sets;
2. regard each formula as a singleton partial type and form indexed, pairwise-distinct copies;
3. prove the resulting formula set consistent by finite realizability and compactness;
4. use downward Löwenheim--Skolem to obtain a model of cardinality `κ`;
5. decode the realizing tuple into cardinality bounds for the original parameter-definable sets.

The current proof implements all five steps correctly, but exposes the set-theoretic encoding of
the auxiliary theory throughout a single long theorem. The refactor should introduce a reusable
partial-type construction rather than merely move the existing local `have` blocks into
parameter-heavy private lemmas.

## Dependencies and abstraction boundary

Coordinate this work with two independent interfaces:

- `PLAN.md` introduces `Formula.realizationSet` as the canonical semantic representation of a
  formula fiber.
- [mathlib4 PR #36719](https://github.com/leanprover-community/mathlib4/pull/36719), or its eventual
  successor, introduces `Theory.withFormulaSet`, `Theory.IsConsistentWith`, `Theory.PartialType`,
  `partialType_iff_finitelyRealizable`, and
  `partialType_completeTheory_iff_finitelyRealizable`.

Do not build a parallel compactness API specialized to unary formulas. The primary syntactic
object should be a set of formulas in a common variable type. Its associated theory should be
obtained with `Theory.withFormulaSet`; the existing local sentence sets `T₂` and `T₃` should
disappear behind that interface.

The partial-type API is not present in the repository's current Mathlib dependency. Work that only
depends on `Formula.realizationSet`, parameter binding, or cardinal estimates can proceed
independently. Do not copy the full unmerged partial-type development into this repository merely
to unblock this refactor. If a temporary local bridge is unavoidable, keep it small and give it a
statement that can later be replaced directly by the upstream API.

## Named family of infinite unary formulas

Introduce a named type for unary formulas with a complete tuple of parameters indexed by the base
model. Keep the explicit-parameter representation canonical and apply `bindParameters` only when
constructing a partial type over the elementary diagram:

```lean
abbrev InfiniteUnaryFormula
    (L : Language) (M : Type*) [L.Structure M] :=
  {φ : L.Formula (M ⊕ Fin 1) //
    Set.Infinite (φ.realizationSet id)}
```

The equivalence `BoundedFormula.constantsVarsEquiv` identifies this type of formula with a
constants-language formula in `L[[M]].Formula (Fin 1)`. Using the explicit representation here
avoids introducing a second constants-language notion of realization set.

Do not make the subtype estimate the foundational cardinal theorem. First add or upstream a bound
for the complete formula space:

```lean
theorem Formula.card_le :
    #(L.Formula α) ≤
      max ℵ₀ (Cardinal.lift #α + Cardinal.lift L.card)
```

The current proof already derives this from `BoundedFormula.card_le` by embedding `Formula α` into
`Σ n, BoundedFormula α n`. The subtype bound should then be a short corollary:

```lean
lemma mk_infiniteUnaryFormula_le
    (hM : #M = κ) (hκ : ℵ₀ ≤ κ)
    (hL : Cardinal.lift L.card ≤ Cardinal.lift κ) :
    #(InfiniteUnaryFormula L M) ≤ Cardinal.lift κ
```

Adjust universe lifts in the actual declarations without weakening them.

## Parameter binding and semantic transport

Package the repeated conversion between formulas with explicit parameters and formulas in a
language expanded by constants. Define the conversion for arbitrary tuple type `α`, not only
`Fin 1`:

```lean
def Formula.bindParameters
    (ψ : L.Formula (β ⊕ α)) (b : β → M) :
    L[[M]].Formula α :=
  BoundedFormula.constantsVarsEquiv.symm
    (ψ.relabel (Sum.map b id))
```

Provide semantic lemmas expressing:

```lean
(ψ.bindParameters b).Realize x ↔
  ψ.Realize (Sum.elim b x)
```

and the corresponding statement after transporting the parameters along a map or elementary
embedding. These lemmas should replace the manual `constantsVarsEquiv`, `relabel`, and `Sum.elim`
simplifications at both ends of the one-step theorem.

`bindParameters` is a syntax adapter, not a competing semantic representation. State its main
specification as an equality or equivalence involving `ψ.realizationSet b`, for example:

```lean
theorem Formula.realizationSet_bindParameters :
    {x | (ψ.bindParameters b).Realize x} = ψ.realizationSet b
```

Once partial types are available, add the corresponding semantic object:

```lean
def Theory.PartialType.realizationSet
    (p : T.PartialType α) (M : Type*) [L.Structure M] :
    Set (α → M) :=
  {v | p.RealizedBy v}
```

This should be characterized as the intersection of the realization sets of formulas in `p`.
Downstream minimality arguments should use named realization sets and should not unfold
`constantsVarsEquiv`, `Formula.equivSentence`, or temporary constants structures.

## Compatibility with inequality constraints

For a variable type `C`, a formula set `S : Set (L.Formula C)`, and a relation
`R : C → C → Prop`, define the disequality formula

```lean
def Formula.neVar (c d : C) : L.Formula C :=
  ((Term.var c).equal (Term.var d)).not
```

and the formula set expressing the requested inequalities:

```lean
def Formula.apartFormulaSet (R : C → C → Prop) :
    Set (L.Formula C) :=
  {ψ | ∃ c d, R c d ∧ ψ = Formula.neVar c d}
```

The statement that `S` is compatible with these inequalities is simply

```lean
T.IsConsistentWith (S ∪ Formula.apartFormulaSet R)
```

By `partialType_iff_finitelyRealizable`, the exact criterion is:

```lean
∀ s ⊆fin S, ∀ r ⊆fin R,
  ∃ M : T.ModelType, ∃ v : C → M,
    (∀ φ ∈ s, φ.Realize v) ∧
    (∀ (c, d) ∈ r, v c ≠ v d)
```

This general relation need not be made public unless another caller needs it. It records the
correct abstraction boundary: compatibility with distinctness is finite joint realizability, not
merely infinitude of each formula considered separately. For the current proof,

```lean
R (a, i) (b, j) ↔ a = b ∧ i ≠ j
```

so distinctness is required only within a formula fiber.

## Pairwise-distinct copies of a partial type

The reusable construction should work for a partial type in an arbitrary finite tuple type:

```lean
def Theory.PartialType.distinctCopiesFormulaSet
    [Finite α] (p : T.PartialType α) (I : Type*) :
    Set (L.Formula (I × α))
```

For every `i : I` and `φ ∈ p`, include `φ` relabeled into the `i`th variable block. For `i ≠ j`,
include the formula saying that the `i`th and `j`th `α`-tuples differ in at least one coordinate.
The tuple-disequality formula should reuse the construction underlying
`Formula.iExsAtLeast`. Requiring `[Finite α]` is essential because tuple inequality is a finite
first-order disjunction.

For a family

```lean
p : A → T.PartialType α
```

provide a family variant with variables `A × I × α`, imposing inequalities only between copies
with the same `a`.

Use a neutral name such as

```lean
def Theory.PartialType.HasArbitrarilyManyRealizations
    [Finite α] (p : T.PartialType α) : Prop := ...
```

until an algebraic-type API fixes the intended terminology. Its finite-fragment formulation should
say that every finite subset of `p` has `n` pairwise-distinct joint realizations for every `n`.
Express this with `Formula.iInf` and `Formula.iExsAtLeast` where convenient.

For an arbitrary, possibly incomplete theory, a family of such partial types requires a joint
finite-realizability condition in one model of `T`; separate consistency of each fiber is not
enough. For a complete theory, independent fibers factor, and it is enough to check that each
partial type has arbitrarily many realizations. In the current application the theory is the
complete theory of the base model in the constants language, and that base model witnesses all
finite requirements simultaneously.

The main compactness theorem for this layer should have the shape:

```lean
theorem isConsistentWith_distinctCopiesFormulaSet_iff :
    T.IsConsistentWith (p.distinctCopiesFormulaSet I) ↔
      every finite fragment of p has enough pairwise-distinct joint realizations
```

When `I` is infinite, "enough" is equivalent to arbitrary finite multiplicity. No cardinality
assumption on `I` is needed for the forward construction beyond the sizes of its finite subsets.

## Models of distinct copies and cardinal lower bounds

A model of the theory associated to `p.distinctCopiesFormulaSet I` canonically supplies a map from
`I` into the realization set of `p` in the reduct to `L`. Package the semantic elimination in two
stages. The following signatures suppress the explicit reduct operation:

```lean
def PartialType.distinctCopiesEmbedding
    (p : T.PartialType α)
    (N : (T.withFormulaSet (p.distinctCopiesFormulaSet I)).ModelType) :
    I ↪ p.realizationSet (reduct of N to L)

theorem PartialType.mk_le_mk_realizationSet_distinctCopies :
    #I ≤ #(p.realizationSet N)
```

For a family `p : A → T.PartialType α`, provide the corresponding embedding for each `a : A`.
These declarations should replace the manual construction of `f : I → rsN`, the extraction of
injectivity from `distinctConstantsTheory`, and the direct use of `Cardinal.le_def` in the current
proof.

## General small-family extension theorem

The central reusable model-theoretic theorem should accept an arbitrary small family of formulas,
rather than immediately taking all infinite unary formulas. A schematic unary version is:

```lean
theorem exists_elementaryExtension_card_eq_realizing_family
    (M : ModelType T)
    (φ : A → L.Formula (M ⊕ Fin 1))
    (hM : #M = κ)
    (hA : #A ≤ Cardinal.lift κ)
    (hφ : ∀ a, Set.Infinite ((φ a).realizationSet id))
    (hκ : ℵ₀ ≤ κ)
    (hL : Cardinal.lift L.card ≤ Cardinal.lift κ) :
    ∃ (N : ModelType T) (e : M ↪ₑ[L] N),
      #N = κ ∧
      ∀ a, #((φ a).realizationSet e) = κ
```

Prefer a version for arbitrary finite tuple type `α` if it does not substantially complicate the
language-map interface. Internally, apply `bindParameters` to obtain formulas in
`L[[M]].Formula α` before forming singleton partial types over `L.elementaryDiagram M`. The theorem
should assume `#A ≤ κ`; it should not know that `A` is a subtype of the complete formula space.

The existing
`exists_elementaryExtension_card_eq_with_full_unary_realizations` should become the corollary
obtained by taking

```lean
A := InfiniteUnaryFormula L M
```

and applying `mk_infiniteUnaryFormula_le`.

## Expanded-language cardinal estimates

Mathlib already provides the exact equality

```lean
Language.card_withConstants :
  L[[C]].card = Cardinal.lift L.card + Cardinal.lift #C
```

Extract the standard infinite-cardinal consequence:

```lean
theorem Language.card_withConstants_le
    (hκ : ℵ₀ ≤ κ)
    (hL : Cardinal.lift L.card ≤ Cardinal.lift κ)
    (hC : Cardinal.lift #C ≤ Cardinal.lift κ) :
    Cardinal.lift L[[C]].card ≤ Cardinal.lift κ
```

Together with `Formula.card_le`, this should reduce the current `hFcard` and `hL'card` blocks to
short applications. Keep all universe lifts explicit in the final declarations.

## Main theorem after refactoring

Keep the existing public statement and blueprint link unchanged. Its proof should read at the
level of the blueprint:

1. bind explicit parameters into constants-language formulas through `Formula.bindParameters`;
2. define `F := InfiniteUnaryFormula L M` and derive `#F ≤ κ` from `Formula.card_le`;
3. apply the small-family extension theorem with `I := κ.out`;
4. recover `M ↪ₑ[L] N` from the elementary diagram;
5. obtain `κ ≤ #realizationSet` from the distinct-copies embedding;
6. combine it with `#realizationSet ≤ #N = κ`;
7. use the realization-set parameter-binding theorem to return to the original explicit-parameter
   formula.

The elementary-diagram and downward Löwenheim--Skolem orchestration may remain inside the
small-family theorem. Do not extract another layer until a second caller demonstrates a useful
more general interface.

## Non-goals

- Do not change the statement or blueprint link of
  `exists_elementaryExtension_card_eq_with_full_unary_realizations`.
- Do not make `indexedUnaryRealizationTheory` the primary public abstraction. If retained at all,
  it should be a thin abbreviation for `T.withFormulaSet` applied to a formula-set construction.
- Do not expose `T₁`, `T₂`, `T₃`, `Γ`, `Sigma_eq_iUnion`, or raw
  `distinctConstantsTheory` manipulations to callers.
- Do not duplicate the partial-type and finite-realizability API from mathlib4 PR #36719.
- Do not create helpers whose signatures reproduce the full local `let` context.
- Do not replace `Cardinal.mk` with `Set.encard`; the theorem needs an arbitrary infinite
  cardinal lower bound.
- Do not call a partial type "nonalgebraic" until the project fixes the intended relation with
  complete and algebraic types.
- Do not introduce new `sorry` placeholders.

## Implementation order

1. Implement `Formula.realizationSet` and the semantic adapters from `PLAN.md`.
2. Implement `Formula.bindParameters` and state its specifications through realization sets.
3. Add `Formula.card_le` and `Language.card_withConstants_le`; derive
   `mk_infiniteUnaryFormula_le`.
4. After the upstream partial-type API is available, add `PartialType.realizationSet`.
5. Define `PartialType.distinctCopiesFormulaSet` and its family variant, reusing `iExsAtLeast`
   tuple inequality.
6. Prove the finite-realizability characterization and the realization-set embedding supplied by a
   model of distinct copies.
7. Prove `exists_elementaryExtension_card_eq_realizing_family`.
8. Rewrite `exists_elementaryExtension_card_eq_with_full_unary_realizations` as its all-formulas
   corollary.
9. Remove the local `T₂`, `T₃`, `Γ`, and `Sigma_eq_iUnion` machinery only after the replacement
   proof compiles.

## Validation

After each extraction, inspect the affected declarations with Lean LSP diagnostics. Since the
refactor changes Lean declarations without adding imports, the final gate is:

```bash
lake build MorleyCategoricityTheorem
```

If modules or imports are added or reorganized, also run:

```bash
lake exe mk_all --check
```

If the blueprint statement, dependencies, declaration link, or status is changed, run:

```bash
leanblueprint all
```

Confirm that the refactored scope contains no new `sorry`, and that the blueprint continues to
describe the compiled declaration accurately.
