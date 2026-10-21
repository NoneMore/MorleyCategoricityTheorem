/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.Definability
import MorleyCategoricityTheorem.ModelTheory.Definability

/-!
# Minimal unary definable sets

An infinite unary definable set `D` in an `L`-structure `M` is *minimal* when every subset of `D`
that is definable with parameters from `M` is finite or cofinite in `D` (blueprint
`def:minimality`).  Strong minimality, the requirement that this hold in every elementary
extension, is built on this local predicate.

The parameters allowed in a defining formula are those of the whole model: `univ.Definable₁` admits
any finite tuple of elements of `M`.  The base over which `D` itself is defined is recorded
separately, for example by `A.Definable₁ L D`, and does not restrict the parameters of the subsets
being tested.  Consequently minimality is a predicate on a model and a set, not on a formula or a
theory, which is why `L` is explicit in `Language.IsMinimal` and implicit where the formula
determines it.

## Main definitions

- `FirstOrder.Language.IsMinimal`: minimality of a set in a structure.
- `FirstOrder.Language.Formula.IsMinimal`: the formula-level wrapper, evaluating a one-variable
  formula at an assigned parameter tuple.

## Main results

- `FirstOrder.Language.isMinimal_iff`: the split form of the definition, testing `D ∩ S` and
  `D \ S` against an arbitrary definable set `S` without requiring `S ⊆ D`.
- `FirstOrder.Language.IsMinimal.finite_or_sdiff_finite`: the defining dichotomy for a definable
  subset.
- `FirstOrder.Language.IsMinimal.sdiff_finite_of_infinite`: an infinite definable subset of a
  minimal set is cofinite in it.
- `FirstOrder.Language.not_isMinimal_of_finite`: a finite set is not minimal.
-/

universe u v w p

namespace FirstOrder

namespace Language

/-- A set `D` is minimal in `M` when it is infinite, definable with parameters from `M`, and every
definable subset of `D` is finite or cofinite in `D`.

This is blueprint `def:minimality`.  Definability is tested over all of `M`, so the subsets tested
below may use any parameters; the base over which `D` is defined can be recorded separately by
`A.Definable₁ L D`.  Minimality is a property of the set in its model, not of a chosen defining
formula. -/
def IsMinimal (L : Language.{u, v}) {M : Type w} [L.Structure M] (D : Set M) : Prop :=
  D.Infinite ∧
    (Set.univ : Set M).Definable₁ L D ∧
    ∀ S : Set M, (Set.univ : Set M).Definable₁ L S → S ⊆ D →
      S.Finite ∨ (D \ S).Finite

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {D : Set M}

/-- Minimality can be tested by splitting `D` along an arbitrary definable set: one of
`D ∩ S` and `D \ S` is finite.  The hypothesis `S ⊆ D` of the definition is not needed here. -/
theorem isMinimal_iff (D : Set M) :
    L.IsMinimal D ↔
      D.Infinite ∧ (Set.univ : Set M).Definable₁ L D ∧
        ∀ S : Set M, (Set.univ : Set M).Definable₁ L S →
          (D ∩ S).Finite ∨ (D \ S).Finite := by
  constructor
  · rintro ⟨hDinf, hDdef, hDichotomy⟩
    refine ⟨hDinf, hDdef, fun S hS => ?_⟩
    have hDS : (Set.univ : Set M).Definable₁ L (D ∩ S) := by
      have hDdef' : (Set.univ : Set M).Definable L {x : Fin 1 → M | x 0 ∈ D} := hDdef
      have hS' : (Set.univ : Set M).Definable L {x : Fin 1 → M | x 0 ∈ S} := hS
      simpa only [Set.Definable₁, Set.mem_inter_iff, Set.ofPred_and] using hDdef'.inter hS'
    rcases hDichotomy (D ∩ S) hDS Set.inter_subset_left with h | h
    · exact Or.inl h
    · exact Or.inr (by rwa [Set.inter_comm D S, Set.sdiff_inter_self_eq_sdiff] at h)
  · rintro ⟨hDinf, hDdef, hSplit⟩
    refine ⟨hDinf, hDdef, fun S hS hSD => ?_⟩
    rcases hSplit S hS with h | h
    · exact Or.inl (by rwa [Set.inter_eq_right.mpr hSD] at h)
    · exact Or.inr h

/-- A minimal set is infinite. -/
theorem IsMinimal.infinite (hD : L.IsMinimal D) : D.Infinite :=
  hD.1

/-- A minimal set is definable with parameters from the ambient model. -/
theorem IsMinimal.definable (hD : L.IsMinimal D) :
    (Set.univ : Set M).Definable₁ L D :=
  hD.2.1

/-- Every definable subset of a minimal set is finite or cofinite in it. -/
theorem IsMinimal.finite_or_sdiff_finite (hD : L.IsMinimal D) {S : Set M}
    (hS : (Set.univ : Set M).Definable₁ L S) (hSD : S ⊆ D) :
    S.Finite ∨ (D \ S).Finite :=
  hD.2.2 S hS hSD

/-- The split form of the defining dichotomy: for any definable set `S`, the part of `D` inside
`S` and the part of `D` outside `S` are not both infinite. -/
theorem IsMinimal.inter_finite_or_sdiff_finite (hD : L.IsMinimal D) {S : Set M}
    (hS : (Set.univ : Set M).Definable₁ L S) :
    (D ∩ S).Finite ∨ (D \ S).Finite :=
  ((isMinimal_iff D).mp hD).2.2 S hS

/-- An infinite definable subset of a minimal set is cofinite in it. -/
theorem IsMinimal.sdiff_finite_of_infinite (hD : L.IsMinimal D) {S : Set M}
    (hS : (Set.univ : Set M).Definable₁ L S) (hSD : S ⊆ D) (hSinf : S.Infinite) :
    (D \ S).Finite :=
  (hD.finite_or_sdiff_finite hS hSD).resolve_left hSinf.not_finite

/-- A finite set is not minimal. -/
theorem not_isMinimal_of_finite (hD : D.Finite) : ¬ L.IsMinimal D :=
  fun h => h.infinite.not_finite hD

namespace Formula

/-- A one-variable formula with assigned parameters is minimal when its unary realization set is a
minimal set.

The formula determines the language, so `L` is implicit here, unlike in `Language.IsMinimal`. -/
def IsMinimal {L : Language.{u, v}} {M : Type w} [L.Structure M] {β : Type p}
    (φ : L.Formula (β ⊕ Fin 1)) (a : β → M) : Prop :=
  L.IsMinimal (φ.realizationSet₁ a)

variable {β : Type p} {φ : L.Formula (β ⊕ Fin 1)} {a : β → M}

/-- Minimality of a formula with assigned parameters is minimality of its unary realization set. -/
theorem isMinimal_iff (φ : L.Formula (β ⊕ Fin 1)) (a : β → M) :
    φ.IsMinimal a ↔ L.IsMinimal (φ.realizationSet₁ a) :=
  Iff.rfl

/-- The realization set of a minimal formula with assigned parameters is infinite. -/
theorem IsMinimal.realizationSet₁_infinite (h : φ.IsMinimal a) :
    (φ.realizationSet₁ a).Infinite :=
  h.1

/-- The realization set of a minimal formula with assigned parameters is definable with parameters
from the ambient model. -/
theorem IsMinimal.realizationSet₁_definable (h : φ.IsMinimal a) :
    (Set.univ : Set M).Definable₁ L (φ.realizationSet₁ a) :=
  h.2.1

/-- Every definable subset of the realization set of a minimal formula is finite or cofinite in
that realization set. -/
theorem IsMinimal.finite_or_sdiff_finite (h : φ.IsMinimal a) {S : Set M}
    (hS : (Set.univ : Set M).Definable₁ L S) (hSD : S ⊆ φ.realizationSet₁ a) :
    S.Finite ∨ (φ.realizationSet₁ a \ S).Finite :=
  h.2.2 S hS hSD

/-- An infinite definable subset of the realization set of a minimal formula is cofinite in it. -/
theorem IsMinimal.sdiff_finite_of_infinite (h : φ.IsMinimal a) {S : Set M}
    (hS : (Set.univ : Set M).Definable₁ L S) (hSD : S ⊆ φ.realizationSet₁ a)
    (hSinf : S.Infinite) :
    (φ.realizationSet₁ a \ S).Finite :=
  (h.finite_or_sdiff_finite hS hSD).resolve_left hSinf.not_finite

end Formula

end Language

end FirstOrder
