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

The statements below are phrased through `Formula.realizationSet`, the unbundled realization set
of a formula under an assigned parameter tuple: for `φ : L.Formula (β ⊕ α)` the parameters are
`b : β → M` and the realized tuples live in `α → M`.

- `ElementaryEmbedding.realizations_embedding`: embed the source realization set into the
  corresponding target realization set by sending a tuple `x` to `e ∘ x`.
- `ElementaryEmbedding.image_realizationSet_subset`: the same containment as an image inclusion, in
  the general `β ⊕ α` shape.
- `ElementaryEmbedding.image_realizationSet₁_subset`: the unary `β ⊕ Fin 1` specialization, which is
  the image inclusion underlying the Vaughtian-pair condition.
- `ElementaryEmbedding.mk_realizations_le`: the resulting `Cardinal.mk` inequality, with no
  finiteness assumption on the tuple index type.
- `ElementaryEmbedding.encard_realizations_eq_coe_iff`: preservation and reflection of exact
  natural-number cardinality of a formula fiber.
- `ElementaryEmbedding.infinite_realizations_iff`: source and target realization sets are infinite
  simultaneously.
- `ElementaryEmbedding.infinite_realizationSet₁_iff`: the unary specialization of the previous
  statement.
- `ElementaryEmbedding.mem_realizationSet₁_iff`: the elementwise form of unary formula transport.
- `Equiv.image_realizationSet₁`: a first-order equivalence transports unary realization sets.

## Implementation order

1. Use `ElementaryEmbedding.map_formula` and pointwise injectivity of `e` to build the realization
   set embedding.
2. Read off the image inclusion `image_realizationSet_subset` from that embedding, and specialize it
   to the unary shape as `image_realizationSet₁_subset`.
3. Apply `Cardinal.mk_le_of_injective` to prove cardinal monotonicity. This is the interface needed
   for arbitrary infinite-cardinal lower bounds.
4. Apply `ElementaryEmbedding.map_formula` to `Formula.iExsExactly`, then rewrite with
   `Formula.realize_iExsExactly` to prove preservation of exact finite cardinality.
5. Prove the equivalence of infinitude. One direction uses cardinal monotonicity, while the other
   argues contrapositively from preservation of exact finite cardinality.

Because `Formula.realizationSet` is a plain `def` whose body is the set-builder, these restated
declaration types are definitionally equal to the previous set-builder statements.

Formulas in `L[[A]]` should be converted with `BoundedFormula.constantsVarsEquiv` and then passed
to the explicit-parameter API with parameter map `(↑) : A → M`. This is also the representation
provided by `Set.definable_iff_exists_formula_sum`, so no parallel constants-language API is needed.

## Cardinality boundary

Use `Set.encard` only for statements comparing a realization set with a natural number. Use
`Cardinal.mk` for monotonicity and for transporting arbitrary infinite-cardinal lower bounds,
because `Set.encard` identifies all infinite cardinalities with `⊤`.
-/

universe u v w w' x x'

open scoped Cardinal FirstOrder

namespace FirstOrder

namespace Language

namespace ElementaryEmbedding

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} {α : Type x} {β : Type x'}
variable [L.Structure M] [L.Structure N]

section ExplicitParameters

/-- The embedding of realization sets induced by an elementary embedding.

A realizing tuple `x : α → M` is sent pointwise to `e ∘ x`; all parameters are transported by
`e` as well. No finiteness assumption on `α` is needed for this construction. -/
def realizations_embedding (e : M ↪ₑ[L] N) (φ : L.Formula (β ⊕ α)) (b : β → M) :
    φ.realizationSet b ↪ φ.realizationSet (e ∘ b) where
  toFun x := ⟨e ∘ x, by
    simpa only [Formula.mem_realizationSet, ← Sum.comp_elim] using
      (e.map_formula φ (Sum.elim b x)).mpr x.2⟩
  inj' x y h := Subtype.ext <| e.injective.comp_left <| congrArg Subtype.val h

/-- An elementary embedding maps the source realization set into the target realization set with
transported parameters.

Its unary specialization is `image_realizationSet₁_subset`; the reverse inclusion need not hold. -/
theorem image_realizationSet_subset (e : M ↪ₑ[L] N) (φ : L.Formula (β ⊕ α)) (b : β → M) :
    (fun x : α → M => (e : M → N) ∘ x) '' φ.realizationSet b ⊆ φ.realizationSet (e ∘ b) :=
  Set.image_subset_iff.mpr fun x hx => (realizations_embedding e φ b ⟨x, hx⟩).2

/-- The unary specialization of `image_realizationSet_subset`: an elementary embedding maps the
source unary realization set into the target unary realization set with transported parameters.

This is the image inclusion underlying the Vaughtian-pair condition, whose distinguished variable is
indexed by `Fin 1`. The reverse inclusion need not hold in general; for a Vaughtian witness it is
exactly the additional condition that, together with this theorem, yields equality. -/
theorem image_realizationSet₁_subset (e : M ↪ₑ[L] N) (φ : L.Formula (β ⊕ Fin 1)) (b : β → M) :
    (e : M → N) '' φ.realizationSet₁ b ⊆ φ.realizationSet₁ (e ∘ b) := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : (fun _ : Fin 1 => x) ∈ φ.realizationSet b := by simpa using hx
  exact image_realizationSet_subset e φ b ⟨_, hx', rfl⟩

/-- Cardinality of a formula fiber cannot decrease under an elementary embedding.

This uses `Cardinal.mk`, rather than `Set.encard`, so that it retains information about arbitrary
infinite cardinalities. -/
theorem mk_realizations_le (e : M ↪ₑ[L] N) (φ : L.Formula (β ⊕ α)) (b : β → M) :
    Cardinal.lift.{max w' x} (#(φ.realizationSet b)) ≤
      Cardinal.lift.{max w x} (#(φ.realizationSet (e ∘ b))) :=
  Cardinal.lift_mk_le_lift_mk_of_injective (realizations_embedding e φ b).injective

/-- An elementary embedding preserves and reflects exact finite cardinality of a formula fiber. -/
theorem encard_realizations_eq_coe_iff [Finite α] (e : M ↪ₑ[L] N)
    (φ : L.Formula (β ⊕ α)) (b : β → M) (n : ℕ) :
    (φ.realizationSet (e ∘ b)).encard = n ↔ (φ.realizationSet b).encard = n := by
  simp only [← Formula.realize_iExsExactly, map_formula]

/-- A formula fiber is infinite in the target exactly when it is infinite in the source. -/
theorem infinite_realizations_iff [Finite α] (e : M ↪ₑ[L] N)
    (φ : L.Formula (β ⊕ α)) (b : β → M) :
    (φ.realizationSet (e ∘ b)).Infinite ↔ (φ.realizationSet b).Infinite := by
  simp [Set.encard_eq_top_iff.symm.trans ENat.eq_top_iff_forall_ge,
    ← Formula.realize_iExsAtLeast]

/-- A unary realization set is infinite in the target of an elementary embedding exactly when it is
infinite in the source. -/
theorem infinite_realizationSet₁_iff (e : M ↪ₑ[L] N) (φ : L.Formula (β ⊕ Fin 1)) (b : β → M) :
    (φ.realizationSet₁ (e ∘ b)).Infinite ↔ (φ.realizationSet₁ b).Infinite := by
  rw [← Formula.infinite_realizationSet_fin_one_iff φ (e ∘ b),
    ← Formula.infinite_realizationSet_fin_one_iff φ b]
  exact infinite_realizations_iff e φ b

/-- An elementary embedding preserves unary realization: an element realizes a formula with
transported parameters exactly when its image realizes the transported formula.

This is the elementwise form of `Equiv.image_realizationSet₁` and the reason `realizationSet₁` can be
compared across an elementary embedding at all. -/
theorem mem_realizationSet₁_iff (e : M ↪ₑ[L] N) (φ : L.Formula (β ⊕ Fin 1)) (b : β → M) (x : M) :
    x ∈ φ.realizationSet₁ b ↔ e x ∈ φ.realizationSet₁ (e ∘ b) := by
  simp only [Formula.mem_realizationSet₁]
  rw [show Sum.elim (e ∘ b) (fun _ : Fin 1 => e x) =
      (e : M → N) ∘ Sum.elim b (fun _ : Fin 1 => x) from (Sum.comp_elim _ _ _).symm]
  exact (e.map_formula φ (Sum.elim b (fun _ : Fin 1 => x))).symm

end ExplicitParameters


end ElementaryEmbedding

namespace Equiv

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} {β : Type x'}
variable [L.Structure M] [L.Structure N]

/-- A first-order equivalence maps unary realization sets to unary realization sets with transported
parameters. -/
theorem image_realizationSet₁ (f : M ≃[L] N) (φ : L.Formula (β ⊕ Fin 1)) (b : β → M) :
    (f : M → N) '' φ.realizationSet₁ b = φ.realizationSet₁ (f ∘ b) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Formula.mem_realizationSet₁] at hx ⊢
    have hcomp : (⇑f.toElementaryEmbedding) ∘ Sum.elim b (fun _ : Fin 1 => x) =
        Sum.elim (f ∘ b) (fun _ : Fin 1 => f x) := by
      funext i
      rcases i with i | j <;> rfl
    rw [← hcomp]
    exact (f.toElementaryEmbedding.map_formula φ (Sum.elim b (fun _ => x))).mpr hx
  · intro hy
    rw [Formula.mem_realizationSet₁] at hy
    refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
    rw [Formula.mem_realizationSet₁]
    have hcomp : (⇑f.toElementaryEmbedding) ∘ Sum.elim b (fun _ : Fin 1 => f.symm y) =
        Sum.elim (f ∘ b) (fun _ : Fin 1 => y) := by
      funext i
      rcases i with i | j
      · rfl
      · simp
    refine (f.toElementaryEmbedding.map_formula φ
      (Sum.elim b (fun _ : Fin 1 => f.symm y))).mp ?_
    rw [hcomp]
    exact hy

end Equiv

end Language

end FirstOrder
