import Mathlib.ModelTheory.Definability
import Mathlib.ModelTheory.Satisfiability

/-!
# Large models without small infinite definable sets

This file states the existence of large models in which every parameter-definable
unary set is either finite or of full cardinality.

## Main results

- `Theory.exists_elementaryExtension_card_eq_with_full_unary_realizations`:
  one-step elementary extension of cardinality `κ` that fully realizes every
  infinite unary formula with parameters from the base model.
- `Theory.exists_large_model_no_small_infinite_definable_sets`: for a countable
  language and an infinite theory, every uncountable cardinal admits a model with
  no intermediate infinite definable sets.
-/

universe u v w

namespace FirstOrder

namespace Language

namespace Theory

open Cardinal Set

variable {L : Language.{u, v}} (T : L.Theory)

/-- One-step growth: given a model `M` of cardinality `κ`, there is an elementary
extension `N` of the same cardinality such that every infinite unary formula over
`M` already has `κ` many realizations in `N`. -/
theorem exists_elementaryExtension_card_eq_with_full_unary_realizations
    {κ : Cardinal.{w}} (M : ModelType.{u, v, w} T) (hM : #M = κ)
    (hκ : ℵ₀ ≤ κ)
    (hL : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ (N : ModelType.{u, v, w} T) (e : M ↪ₑ[L] N),
      #N = κ ∧
        ∀ (φ : L[[M]].Formula (Fin 1)),
          Set.Infinite {x : M | φ.Realize fun _ ↦ x} →
            #({x : N |
                ((L.lhomWithConstantsMap e).onFormula φ).Realize fun _ ↦ x}) = κ := by
  sorry

/-- For a theory `T` in a countable language with an infinite model and a cardinal
`κ ≥ ℵ₁`, there is a model of cardinality `κ` in which every parameter-definable
subset is either finite or of cardinality `κ`. -/
theorem exists_large_model_no_small_infinite_definable_sets
    {κ : Cardinal.{w}}
    (hL : L.card ≤ ℵ₀)
    (hT : ∃ M : ModelType.{u, v, max u v} T, Infinite M)
    (hκ : ℵ₁ ≤ κ) :
    ∃ M : ModelType.{u, v, w} T, #M = κ ∧
      ∀ (A : Set M) (X : Set M), A.Definable₁ L X → X.Finite ∨ #X = κ := by
  sorry

end Theory

end Language

end FirstOrder
