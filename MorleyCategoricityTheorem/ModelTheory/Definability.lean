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
- `Formula.realizationSet₁_definable`: a unary realization set is definable over the whole ambient
  model.
- `definable₁_iff_exists_fin_realizationSet₁`: a unary set definable over the whole model is a
  realization set with a finite parameter tuple.
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

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {β : Type*}

/-- A unary realization set of a formula with assigned parameters is definable with parameters from
the whole ambient model. -/
theorem Formula.realizationSet₁_definable (φ : L.Formula (β ⊕ Fin 1)) (a : β → M) :
    (Set.univ : Set M).Definable₁ L (φ.realizationSet₁ a) := by
  rw [Set.definable₁_iff_exists_realizationSet₁]
  let g : β ⊕ Fin 1 → (Set.univ : Set M) ⊕ Fin 1 :=
    Sum.map (fun i => ⟨a i, Set.mem_univ _⟩) id
  refine ⟨Formula.relabel g φ, ?_⟩
  ext x
  have h : (Sum.elim (fun y : {y : M // y ∈ (Set.univ : Set M)} => y.1)
        (fun _ : Fin 1 => x)) ∘ g = Sum.elim a (fun _ : Fin 1 => x) := by
    funext i
    rcases i with i | j <;> rfl
  simp only [Formula.mem_realizationSet₁, Formula.realize_relabel, h]

/-- A unary set is definable over the whole model exactly when it is the unary realization set of a
one-variable formula with a finite tuple of parameters. -/
theorem definable₁_iff_exists_fin_realizationSet₁ {s : Set M} :
    (Set.univ : Set M).Definable₁ L s ↔
      ∃ (n : ℕ) (φ : L.Formula (Fin n ⊕ Fin 1)) (b : Fin n → M), s = φ.realizationSet₁ b := by
  constructor
  · intro hs
    obtain ⟨A0, -, hA0⟩ := Set.definable_iff_finitely_definable.mp hs
    obtain ⟨θ, hθ⟩ := hA0
    obtain ⟨n, b, φ', hφ'⟩ := Formula.exists_fin_params θ
    refine ⟨n, Formula.relabel (Equiv.sumComm (Fin 1) (Fin n)) φ', fun i => (b i : M), ?_⟩
    ext x
    simp only [Formula.mem_realizationSet₁, Formula.realize_relabel]
    rw [show (Sum.elim (fun i => (b i : M)) (fun _ : Fin 1 => x)) ∘
        Equiv.sumComm (Fin 1) (Fin n) = Sum.elim (fun _ : Fin 1 => x) (fun i => (b i : M)) from by
      funext i
      rcases i with i | j <;> rfl]
    rw [← hφ' (fun _ : Fin 1 => x)]
    have hx : ((fun _ : Fin 1 => x) ∈ ({y : Fin 1 → M | y 0 ∈ s} : Set (Fin 1 → M))) ↔ x ∈ s :=
      Iff.rfl
    rw [← hx, hθ]
    rfl
  · rintro ⟨n, φ, b, rfl⟩
    exact Formula.realizationSet₁_definable φ b

end Language

end FirstOrder
