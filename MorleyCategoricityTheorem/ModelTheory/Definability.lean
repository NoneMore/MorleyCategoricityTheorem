/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.Definability
import MorleyCategoricityTheorem.ModelTheory.Semantics

/-!
# Definability bridges

Relates `Set.Definable` and `Set.Definable₁` to formula realization sets,
without importing the higher model-theory layers.

## Main results

- `Set.definable_iff_exists_realizationSet`, `Set.definable_realizationSet`:
  realization-set bridges.
- `Set.definable₁_iff_exists_realizationSet₁`: unary bridge.
- `Set.definable_setOf_fiber_encard_le`, `Set.Definable.exists_fiber`:
  bounded-fiber definability and existential projection, used for
  algebraic-closure idempotence.
-/

universe u v w

namespace Set

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {A : Set M} {α β : Type*}

/-- Definability over `A` is equivalent to being a realization set with
parameters indexed by `A`. -/
theorem definable_iff_exists_realizationSet {s : Set (α → M)} :
    A.Definable L s ↔ ∃ φ : L.Formula (A ⊕ α), s = φ.realizationSet (Subtype.val : A → M) := by
  rw [definable_iff_exists_formula_sum]
  rfl

/-- A formula's realization set is definable over its parameters. -/
theorem definable_realizationSet (φ : L.Formula (A ⊕ β)) :
    A.Definable L (φ.realizationSet (Subtype.val : A → M)) :=
  definable_iff_exists_realizationSet.mpr ⟨φ, rfl⟩

/-- The unary realization-set characterization of `Definable₁`. -/
theorem definable₁_iff_exists_realizationSet₁ {s : Set M} :
    A.Definable₁ L s ↔
      ∃ φ : L.Formula (A ⊕ Fin 1), s = φ.realizationSet₁ (Subtype.val : A → M) := by
  change A.Definable L {x : Fin 1 → M | x 0 ∈ s} ↔
    ∃ φ : L.Formula (A ⊕ Fin 1), s = φ.realizationSet₁ (Subtype.val : A → M)
  rw [definable_iff_exists_realizationSet]
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, ?_⟩
    have himg : {x : Fin 1 → M | x 0 ∈ s} =
        (fun a : M => fun _ : Fin 1 => a) '' φ.realizationSet₁ (Subtype.val : A → M) := by
      rw [hφ, Formula.realizationSet_fin_one_image]
    have hpre : s = (fun a : M => fun _ : Fin 1 => a) ⁻¹' {x : Fin 1 → M | x 0 ∈ s} := rfl
    rw [hpre, himg, preimage_image_eq _ (fun x y h => congrFun h 0)]
  · rintro ⟨φ, rfl⟩
    exact ⟨φ, by rw [Formula.realizationSet_fin_one_image, image_fin_one_eq]⟩

/-- The set of parameters whose formula fibers have `encard ≤ n` is definable. -/
theorem definable_setOf_fiber_encard_le {α β : Type*} [Finite β]
    {φ : L.Formula (A ⊕ (α ⊕ β))} (n : ℕ) :
    A.Definable L {v : α → M |
      ({w : β → M | φ.Realize (Sum.elim (Subtype.val : A → M) (Sum.elim v w))}).encard ≤ n} := by
  have hrelabel : ∀ (v : α → M) (w : β → M),
      (φ.relabel (Equiv.sumAssoc A α β).symm).Realize
          (Sum.elim (Sum.elim (Subtype.val : A → M) v) w) ↔
        φ.Realize (Sum.elim (Subtype.val : A → M) (Sum.elim v w)) := by
    intro v w
    rw [Formula.realize_relabel]
    exact iff_of_eq <| congrArg φ.Realize <| funext fun z => by rcases z with a | b | c <;> simp
  have hfiber : ∀ v : α → M,
      (φ.relabel (Equiv.sumAssoc A α β).symm).realizationSet (Sum.elim (Subtype.val : A → M) v) =
        {w : β → M | φ.Realize (Sum.elim (Subtype.val : A → M) (Sum.elim v w))} := by
    intro v
    ext w
    exact hrelabel v w
  have hset : {v : α → M |
        ({w : β → M | φ.Realize (Sum.elim (Subtype.val : A → M) (Sum.elim v w))}).encard ≤ n} =
      ((φ.relabel (Equiv.sumAssoc A α β).symm).iExsAtMost β n).realizationSet
        (Subtype.val : A → M) := by
    ext v
    simp only [Set.mem_ofPred_eq, Formula.mem_realizationSet, Formula.realize_iExsAtMost, hfiber v]
  rw [hset]
  exact definable_realizationSet _

/-- Existential projection of a definable family over a definable parameter set
preserves definability. -/
theorem Definable.exists_fiber {α β : Type*} [Finite α] {V : Set (α → M)}
    {φ : L.Formula (A ⊕ (α ⊕ β))} (hV : A.Definable L V) :
    A.Definable L {w : β → M |
      ∃ v : α → M, v ∈ V ∧
        φ.Realize (Sum.elim (Subtype.val : A → M) (Sum.elim v w))} := by
  have hS : A.Definable L {u : (β ⊕ α) → M |
      u ∘ Sum.inr ∈ V ∧ u ∘ Sum.swap ∈ φ.realizationSet (Subtype.val : A → M)} :=
    (hV.preimage_comp Sum.inr).inter ((definable_realizationSet φ).preimage_comp Sum.swap)
  have h := hS.exists_of_finite
  convert h using 1
  ext w
  simp only [Set.mem_ofPred_eq, Formula.mem_realizationSet, Sum.elim_comp_inr, Sum.elim_swap]

end Set
