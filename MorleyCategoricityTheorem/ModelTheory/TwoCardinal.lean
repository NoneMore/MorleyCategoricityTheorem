/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.Bundled
import MorleyCategoricityTheorem.ModelTheory.ElementaryMaps

/-!
# Two-cardinal models

A `(κ, λ)`-model of a theory `T` is a model of `T` of cardinality `κ` that carries a one-variable
parameter-definable subset of cardinality `λ`.  For `κ > λ ≥ ℵ₀` it is the two-cardinal hypothesis
of Vaught's theorem: in a language of size at most `λ`, passing to an elementary submodel of size
`λ` that contains the small definable set turns the model into a Vaughtian pair.

## Main definitions

- `FirstOrder.Language.Theory.IsKappaLambdaModel`: `M` is a `(κ, λ)`-model of `T`.
- `FirstOrder.Language.Theory.HasKappaLambdaModel`: `T` has a `(κ, λ)`-model.

## Main results

- `FirstOrder.Language.Theory.isKappaLambdaModel_iff`: the defining form of a `(κ, λ)`-model.
- `FirstOrder.Language.Theory.isKappaLambdaModel_iff_exists_definable₁`: the definition agrees with
  the blueprint's description as a model with a one-variable parameter-definable subset of size
  `λ`.
- `FirstOrder.Language.Theory.IsKappaLambdaModel.of_equiv`: `(κ, λ)`-modelhood is invariant under
  isomorphism.

## Implementation notes

The small definable subset is presented as the unary realization set `φ.realizationSet₁ a` of a
formula `φ : L.Formula (Fin n ⊕ Fin 1)` under the parameter tuple `a : Fin n → M`, the witness
shape of `Theory.IsVaughtianPair`; by
`FirstOrder.Language.definable₁_iff_exists_fin_realizationSet₁` this loses no generality.
Cardinalities use `Cardinal.mk`, since `Set.encard` collapses the infinite cardinals, and the
ordering `κ > λ ≥ ℵ₀` is a hypothesis of the statements using the notion rather than part of the
definition.  The second cardinal is named `μ` because `λ` is a keyword in Lean.

Design rationale and the planned Vaughtian-pair bridge are in `docs/plan/two-cardinal.md`.
-/

universe u v w

open scoped Cardinal

namespace FirstOrder

namespace Language

namespace Theory

variable {L : Language.{u, v}}

/-- A `(κ, λ)`-model of a theory `T` is a model `M` of `T` of cardinality `κ` with a one-variable
parameter-definable subset of cardinality `λ`.

The definable subset is presented as the unary realization set of a formula with a finite parameter
tuple; this is the shape of a Vaughtian-pair witness.  The interesting case is `κ > λ ≥ ℵ₀`; the
ordering assumptions are not built into the definition, see
`Theory.isKappaLambdaModel_iff_exists_definable₁` for the parameter-definability reading. -/
def IsKappaLambdaModel (T : L.Theory) (M : Type w) [L.Structure M] (κ μ : Cardinal.{w}) : Prop :=
  M ⊨ T ∧ #M = κ ∧
    ∃ (n : ℕ) (φ : L.Formula (Fin n ⊕ Fin 1)) (a : Fin n → M), #(φ.realizationSet₁ a) = μ

/-- A theory has a `(κ, λ)`-model if some model of it of cardinality `κ` carries a one-variable
parameter-definable subset of cardinality `λ`.

Models are bundled as `ModelType` to keep the nonemptiness of a model available, matching
`Theory.HasVaughtianPair`. -/
def HasKappaLambdaModel (T : L.Theory) (κ μ : Cardinal.{w}) : Prop :=
  ∃ M : ModelType.{u, v, w} T, IsKappaLambdaModel T M κ μ

/-- The defining form of a `(κ, λ)`-model. -/
theorem isKappaLambdaModel_iff {T : L.Theory} {M : Type w} [L.Structure M] {κ μ : Cardinal.{w}} :
    IsKappaLambdaModel T M κ μ ↔
      M ⊨ T ∧ #M = κ ∧
        ∃ (n : ℕ) (φ : L.Formula (Fin n ⊕ Fin 1)) (a : Fin n → M),
          #(φ.realizationSet₁ a) = μ :=
  Iff.rfl

/-- A `(κ, λ)`-model has a one-variable parameter-definable subset of cardinality `λ`, in the form
of definability over the whole model.

The reverse direction presents a unary set definable with parameters by a formula with a finite
parameter tuple, using `FirstOrder.Language.definable₁_iff_exists_fin_realizationSet₁`. -/
theorem isKappaLambdaModel_iff_exists_definable₁ {T : L.Theory} {M : Type w} [L.Structure M]
    {κ μ : Cardinal.{w}} :
    IsKappaLambdaModel T M κ μ ↔
      M ⊨ T ∧ #M = κ ∧ ∃ s : Set M, (Set.univ : Set M).Definable₁ L s ∧ #s = μ := by
  rw [isKappaLambdaModel_iff]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨n, φ, a, h⟩
    exact ⟨_, Formula.realizationSet₁_definable φ a, h⟩
  · rintro ⟨s, hs, h⟩
    obtain ⟨n, φ, a, rfl⟩ := definable₁_iff_exists_fin_realizationSet₁.mp hs
    exact ⟨n, φ, a, h⟩

namespace IsKappaLambdaModel

variable {T : L.Theory} {M : Type w} [L.Structure M] {κ μ : Cardinal.{w}}

/-- A `(κ, λ)`-model is a model of the theory. -/
theorem model (h : IsKappaLambdaModel T M κ μ) : M ⊨ T :=
  h.1

/-- A `(κ, λ)`-model has cardinality `κ`. -/
theorem card_eq (h : IsKappaLambdaModel T M κ μ) : #M = κ :=
  h.2.1

/-- A `(κ, λ)`-model has a one-variable parameter-definable subset of cardinality `λ`, presented as
the unary realization set of a formula with a finite parameter tuple. -/
theorem exists_realizationSet₁_card_eq (h : IsKappaLambdaModel T M κ μ) :
    ∃ (n : ℕ) (φ : L.Formula (Fin n ⊕ Fin 1)) (a : Fin n → M), #(φ.realizationSet₁ a) = μ :=
  h.2.2

/-- `(κ, λ)`-modelhood is invariant under `L`-isomorphism: the definable set is transported by the
equivalence, which preserves its cardinality. -/
theorem of_equiv {N : Type w} [L.Structure N] (h : IsKappaLambdaModel T M κ μ)
    (e : M ≃[L] N) : IsKappaLambdaModel T N κ μ := by
  obtain ⟨hT, hcard, n, φ, a, hreal⟩ := h
  refine ⟨(e.toElementaryEmbedding.theory_model_iff T).mp hT, ?_, n, φ, e ∘ a, ?_⟩
  · rw [← Cardinal.mk_congr e.toEquiv]
    exact hcard
  · rw [← Equiv.image_realizationSet₁ e φ a, Cardinal.mk_image_eq e.injective]
    exact hreal

/-- `(κ, λ)`-modelhood is invariant under `L`-isomorphism, in both directions. -/
theorem iff_of_equiv {N : Type w} [L.Structure N] (e : M ≃[L] N) :
    IsKappaLambdaModel T M κ μ ↔ IsKappaLambdaModel T N κ μ :=
  ⟨fun h => h.of_equiv e, fun h => h.of_equiv e.symm⟩

end IsKappaLambdaModel

end Theory

end Language

end FirstOrder
