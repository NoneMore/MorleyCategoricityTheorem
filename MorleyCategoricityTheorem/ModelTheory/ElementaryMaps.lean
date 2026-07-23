/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.ElementaryMaps
import MorleyCategoricityTheorem.ModelTheory.Semantics

/-!
# Additional Results on Elementary Maps

This file extends `Mathlib.ModelTheory.ElementaryMaps` with cardinality results for formula fibers.
Its declarations are intended to migrate directly to `Mathlib/ModelTheory/ElementaryMaps.lean`,
primarily in the `FirstOrder.Language.ElementaryEmbedding` namespace.

## Main results

- `ElementaryEmbedding.realizations_embedding`: embed the source realization subtype into the
  corresponding target realization subtype by sending a tuple `x` to `e ∘ x`.
- `ElementaryEmbedding.mk_realizations_le`: the resulting `Cardinal.mk` inequality, with no
  finiteness assumption on the tuple index type.
- `ElementaryEmbedding.encard_realizations_eq_coe_iff`: preservation and reflection of exact
  natural-number cardinality of a formula fiber.
- `ElementaryEmbedding.infinite_realizations_iff`: source and target realization sets are infinite
  simultaneously.

## Implementation order

1. Use `ElementaryEmbedding.map_formula` and pointwise injectivity of `e` to build the realization
   subtype embedding.
2. Apply `Cardinal.mk_le_of_injective` to prove cardinal monotonicity. This is the interface needed
   for arbitrary infinite-cardinal lower bounds.
3. Apply `ElementaryEmbedding.map_formula` to `Formula.iExsExactly`, then rewrite with
   `Formula.realize_iExsExactly` to prove preservation of exact finite cardinality.
4. Prove the equivalence of infinitude. One direction uses cardinal monotonicity, while the other
   argues contrapositively from preservation of exact finite cardinality.

Formulas in `L[[A]]` should be converted with `BoundedFormula.constantsVarsEquiv` and then passed
to the explicit-parameter API with parameter map `(↑) : A → M`. This is also the representation
provided by `Set.definable_iff_exists_formula_sum`, so no parallel constants-language API is needed.

## Cardinality boundary

Use `Set.encard` only for statements comparing a realization set with a natural number. Use
`Cardinal.mk` for monotonicity and for transporting arbitrary infinite-cardinal lower bounds,
because `Set.encard` identifies all infinite cardinalities with `⊤`.
-/

universe u v w w'

open scoped Cardinal FirstOrder

namespace FirstOrder

namespace Language

namespace ElementaryEmbedding

variable {L : Language.{u, v}} {M N : Type w} {α β : Type w'}
variable [L.Structure M] [L.Structure N]

section ExplicitParameters

/-- The embedding of realization subtypes induced by an elementary embedding.

A realizing tuple `x : α → M` is sent pointwise to `e ∘ x`; all parameters are transported by
`e` as well. No finiteness assumption on `α` is needed for this construction. -/
def realizations_embedding (e : M ↪ₑ[L] N) (φ : L.Formula (β ⊕ α))
    (b : β → M) :
    {x : α → M | φ.Realize (Sum.elim b x)} ↪
      {x : α → N | φ.Realize (Sum.elim (e ∘ b) x)} where
  toFun x := ⟨e ∘ x, show φ.Realize _ by
    simpa only [← Sum.comp_elim] using (e.map_formula φ (Sum.elim b x)).mpr x.2⟩
  inj' x y h := Subtype.ext <| e.injective.comp_left <| congrArg Subtype.val h

/-- Cardinality of a formula fiber cannot decrease under an elementary embedding.

This uses `Cardinal.mk`, rather than `Set.encard`, so that it retains information about arbitrary
infinite cardinalities. -/
theorem mk_realizations_le (e : M ↪ₑ[L] N) (φ : L.Formula (β ⊕ α)) (b : β → M) :
    #({x : α → M | φ.Realize (Sum.elim b x)}) ≤
      #({x : α → N | φ.Realize (Sum.elim (e ∘ b) x)}) :=
  Function.Embedding.cardinal_le <| realizations_embedding e φ b

/-- An elementary embedding preserves and reflects exact finite cardinality of a formula fiber. -/
theorem encard_realizations_eq_coe_iff [Finite α] (e : M ↪ₑ[L] N)
    (φ : L.Formula (β ⊕ α)) (b : β → M) (n : ℕ) :
    {x : α → N | φ.Realize (Sum.elim (e ∘ b) x)}.encard = n ↔
      {x : α → M | φ.Realize (Sum.elim b x)}.encard = n := by
  simp only [← Formula.realize_iExsExactly, map_formula]

/-- A formula fiber is infinite in the target exactly when it is infinite in the source. -/
theorem infinite_realizations_iff [Finite α] (e : M ↪ₑ[L] N)
    (φ : L.Formula (β ⊕ α)) (b : β → M) :
    Set.Infinite {x : α → N | φ.Realize (Sum.elim (e ∘ b) x)} ↔
      Set.Infinite {x : α → M | φ.Realize (Sum.elim b x)} := by
  simp [Set.encard_eq_top_iff.symm.trans ENat.eq_top_iff_forall_ge, ← Formula.realize_iExsAtLeast]

end ExplicitParameters

end ElementaryEmbedding

end Language

end FirstOrder
