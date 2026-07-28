# Plan: Formula Realization Sets and Minimality

## Goal

Introduce a named semantic object for the realization set of a formula after fixing its
parameters. This should replace repeated set comprehensions, simplify the definably-full model
construction, and provide the basic interface for minimal and strongly minimal formulas.

The canonical representation should use tuples. Element-valued unary realization sets are a
derived view of the `Fin 1` case, not a second primary representation.

## Canonical interface

Add the following definition in
`MorleyCategoricityTheorem/ModelTheory/Semantics.lean`, in the
`FirstOrder.Language.Formula` namespace:

```lean
def realizationSet
    {L : Language.{u, v}} {M : Type w} [L.Structure M]
    {β : Type x} {α : Type y}
    (φ : L.Formula (β ⊕ α)) (b : β → M) :
    Set (α → M) :=
  {x | φ.Realize (Sum.elim b x)}
```

Here `β` indexes the fixed parameters and `α` indexes the tuple being realized. This variable
order agrees with the existing `iExs` semantics and the explicit-parameter elementary-embedding
interface.

Do not require `[Finite α]` for this definition. Evaluating a free tuple and transporting it along
an embedding do not require finiteness. Add finiteness assumptions only to results that quantify a
whole tuple inside a first-order formula.

Provide the basic membership theorem immediately:

```lean
@[simp]
theorem mem_realizationSet
    (φ : L.Formula (β ⊕ α)) (b : β → M) (x : α → M) :
    x ∈ φ.realizationSet b ↔ φ.Realize (Sum.elim b x) :=
  Iff.rfl
```

## Core semantic interface

Develop the realization-set laws needed by current and future callers.

1. Prove that formula conjunction, disjunction, negation, top, and bottom correspond to set
   intersection, union, complement, univ, and empty.
2. Prove compatibility with relabeling. In particular, relabeling parameter variables along
   `c : β → γ` should identify the resulting realization set with the original realization set at
   the composed parameter assignment.
3. Package the compatibility of `BoundedFormula.constantsVarsEquiv` with realization sets. This is
   the representation adapter between constants-language formulas and formulas with explicit
   parameter variables.
4. For `α = Fin 1`, provide a subtype equivalence between the canonical tuple realization set and
   its element-valued view:

   ```lean
   def realizationSetFinOneEquiv
       (φ : L.Formula (β ⊕ Fin 1)) (b : β → M) :
       φ.realizationSet b ≃
         {x : M | φ.Realize (Sum.elim b fun _ ↦ x)}
   ```

   Derive preservation of `Set.Infinite` and equality of `Cardinal.mk` from this equivalence rather
   than reproving them with ad hoc injections.
5. Add only those simp lemmas whose right-hand sides are a clear semantic normal form. Avoid simp
   rules that repeatedly expand `realizationSet` back into a set comprehension.

## Elementary embeddings

Refactor the declarations in `MorleyCategoricityTheorem/ModelTheory/ElementaryMaps.lean` to use the
new definition while preserving their existing public names where practical:

```lean
def ElementaryEmbedding.realizations_embedding
    (e : M ↪ₑ[L] N) (φ : L.Formula (β ⊕ α)) (b : β → M) :
    φ.realizationSet b ↪ φ.realizationSet (e ∘ b)
```

Express `mk_realizations_le`, `encard_realizations_eq_coe_iff`, and
`infinite_realizations_iff` in terms of `Formula.realizationSet`. The implementation should use
`ElementaryEmbedding.map_formula`; callers should not need to unfold the realization set.

The named set should become the shared seam for:

- embeddings between realization subtypes;
- `Cardinal.mk` inequalities;
- exact finite `Set.encard` calculations;
- preservation and reflection of infinitude.

## Definably-full construction

Use `Formula.realizationSet` in the explicit-parameter unary-fiber adapter from `TODO.md` and in the
elementary-chain proof. Keep the one-step compactness theorem's existing public statement unless a
separate interface change is justified.

The `Fin 1` equivalence should be used exactly at the seam between:

- the compactness construction, which naturally chooses elements interpreting new constants; and
- the elementary-chain and elementary-embedding arguments, which naturally use tuple realization
  sets.

The chain proof should contain neither manual `Fin 1` injections nor repeated set extensionality
proofs for unary tuple/element conversion.

## Minimal formulas

After the semantic interface is stable, introduce minimality in a separate model-theory module.
For

```lean
φ : L.Formula (β ⊕ α)
b : β → M
D := φ.realizationSet b
```

minimality in `M` should assert:

1. `D` is infinite; and
2. every subset of `D` definable in `M` with parameters is finite or cofinite in `D`.

An equivalent formula-level presentation may quantify over definable sets `X` and require

```lean
(D ∩ X).Finite ∨ (D \ X).Finite.
```

Choose the final declaration form only after checking which representation gives the cleanest
elementary-extension theorem. The definition must cover finite tuple arities; unary minimal
formulas should be a specialization, not the foundational definition.

Strong minimality should state that the transported formula and parameters are minimal in every
elementary extension. Its implementation should reuse the realization-set transport interface
rather than compare raw `Realize` expressions.

## Implementation order

1. Add `Formula.realizationSet` and `mem_realizationSet` to `Semantics.lean`.
2. Add Boolean-operation, relabeling, constants-variable, and `Fin 1` equivalence lemmas.
3. Refactor the cardinality semantics in `Semantics.lean` to use the named set.
4. Refactor `ElementaryMaps.lean` to use the named set without changing theorem content.
5. Use the new interface in the one-step adapter and elementary-chain construction from `TODO.md`.
6. Design and implement minimal and strongly minimal formulas in a separate module.
7. Synchronize root imports and blueprint declaration links only after the new declarations compile.

## Non-goals

- Do not introduce separate competing definitions for tuple and element-valued unary realization
  sets.
- Do not restrict the foundational definition to `Fin 1` or require finite tuple arity.
- Do not expose `constantsVarsEquiv`, temporary constants structures, or `onFormula` semantic
  calculations to downstream minimality arguments.
- Do not change existing blueprint status markers before the corresponding Lean declarations are
  complete.

## Validation

For changes confined to existing Lean modules, run:

```bash
lake build MorleyCategoricityTheorem
```

When adding the new minimality module or changing root imports, also run:

```bash
lake exe mk_all --check
```

When blueprint declarations or status markers are updated, run:

```bash
leanblueprint all
```

Before considering this plan complete, confirm that the new semantic and minimality declarations
contain no `sorry`, and that no caller needs to unfold `Formula.realizationSet` merely to apply a
standard semantic or elementary-embedding fact.
