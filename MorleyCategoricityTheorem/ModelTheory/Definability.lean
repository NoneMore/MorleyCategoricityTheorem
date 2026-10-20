/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.Definability
import MorleyCategoricityTheorem.ModelTheory.Semantics

/-!
# Definability bridges to realization sets

This file hosts the correspondence between `Set.Definable` and `Formula.realizationSet` at the
bottom of the project's model-theory import graph.  Keeping it separate lets foundational modules --
notably `ModelTheory.AlgebraicClosure` -- stay inside Mathlib's definability layer plus the
low-level `ModelTheory.Semantics`: `ModelTheory.DefinablyFull`, the previous home of these bridges,
imports `ModelTheory.ElementaryMaps` and hence the semantic bridges and the type-space layer.

## Main results

- `Set.definable_iff_exists_realizationSet`: a set is definable over `A` exactly when it is the
  realization set of a formula with parameter variables indexed by `A`.
- `Set.definable_realizationSet`: the realization set of a formula with parameters from `A` is
  definable over `A`.
- `Set.image_fin_one_eq`: the `Fin 1 → M` tuple with a single entry is the image of that entry.
- `Set.definable₁_iff_exists_realizationSet₁`: the unary `Definable₁` specialization of the first
  bridge, in terms of `Formula.realizationSet₁`.

The first two are the same statements that were previously proved in `ModelTheory.DefinablyFull`;
they moved here so that the algebraic-closure layer can reuse them without importing the semantic
bridges.
-/

universe u v w

namespace Set

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {A : Set M} {α β : Type*}

/-- A set is definable with parameters in `A` exactly when it is the realization set of a formula
whose parameter variables are indexed by `A`.

This restates `Set.definable_iff_exists_formula_sum` through `Formula.realizationSet`, so that the
witnessing formula of a definable set is the formula whose realization set it is. -/
theorem definable_iff_exists_realizationSet {s : Set (α → M)} :
    A.Definable L s ↔ ∃ φ : L.Formula (A ⊕ α), s = φ.realizationSet (Subtype.val : A → M) := by
  rw [definable_iff_exists_formula_sum]
  rfl

/-- The realization set of a formula with parameters drawn from `A` is definable over `A`.

The formula itself is the witness; use this bridge to pass from the unbundled realization-set
representation to `L.DefinableSet` when the Boolean-algebra structure is needed. -/
theorem definable_realizationSet (φ : L.Formula (A ⊕ β)) :
    A.Definable L (φ.realizationSet (Subtype.val : A → M)) :=
  definable_iff_exists_realizationSet.mpr ⟨φ, rfl⟩

/-- The `Fin 1 → M` tuple with a single entry is the image of that entry.

This is the set-level bridge between the `Fin 1`-indexed and unary shapes; the formula-level
counterpart is `Formula.realizationSet_fin_one_image`. -/
theorem image_fin_one_eq (s : Set M) :
    (fun x : M => fun _ : Fin 1 => x) '' s = {x : Fin 1 → M | x 0 ∈ s} := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro hx
    exact ⟨x 0, hx, funext fun i => by rw [Fin.eq_zero i]⟩

/-- A set is definable in one dimension over `A` exactly when it is the unary realization set
`Formula.realizationSet₁` of a formula with parameters indexed by `A`.

This is the unary specialization of `Set.definable_iff_exists_realizationSet`, and the form in which
the algebraic-closure layer consumes definability. -/
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

end Set
