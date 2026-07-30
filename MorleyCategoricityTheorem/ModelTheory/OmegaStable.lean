import Mathlib.Data.Set.Countable
import MorleyCategoricityTheorem.ModelTheory.Types

/-!
# Omega-stable theories

This file defines omega-stability using complete types over countable parameter sets.
-/

universe u v w

namespace FirstOrder

namespace Language

namespace Theory

variable {L : Language.{u, v}} (T : L.Theory)

/-- A theory is omega-stable if every space of complete positive finite-arity types over a
countable parameter set in a model of the theory is countable. -/
def IsOmegaStable : Prop :=
  ∀ (M : ModelType.{u, v, w} T) (A : Set M), A.Countable →
    ∀ n : ℕ, 1 ≤ n → Countable (L.CompleteTypeOver A (Fin n))

end Theory

end Language

end FirstOrder
