/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import MorleyCategoricityTheorem.ModelTheory.AlgebraicClosure
import MorleyCategoricityTheorem.ModelTheory.IsolatedTypes

/-!
# Algebraic types are isolated

If `b` lies in the algebraic closure of a parameter set `A` in a structure `M`, then its complete
type over `A` is isolated (blueprint `prop:algebraic-implies-isolated`).

The proof takes a finite `A`-definable set `s` containing `b`, with defining formula `φ`.  Every
element of `s` whose type over `A` differs from `tp(b/A)` is separated from `tp(b/A)` by a formula
`θ_x` true at `b` but false at that element.  Then `φ ∧ ⋀_x θ_x` belongs to `tp(b/A)`, and a tuple
realizing it lies in `s` without being one of the separated elements, so it has type `tp(b/A)`.
Since the theory `completeTheory M` expanded by constants for `A` is complete,
`CompleteType.isIsolated_typeOf_iff_of_isComplete` upgrades this model-internal uniqueness to
isolation of the complete type.

## Main results

- `FirstOrder.Language.Theory.CompleteType.isIsolated_typeOf_of_mem_algebraicClosure`: the type
  over `A` of an element algebraic over `A` is isolated.
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {A : Set M} {b : M}

namespace Theory

namespace CompleteType

/-- **Algebraic types are isolated.**  If `b ∈ acl A`, then `tp(b/A)` is an isolated complete
type over `A`.

Isolation is expressed through the model `M` itself:
`CompleteType.isIsolated_typeOf_iff_of_isComplete` reduces it to finding a formula true of `b` that
is true only of tuples with the same type as `b` in `M`. -/
theorem isIsolated_typeOf_of_mem_algebraicClosure [Nonempty M]
    (hb : b ∈ L.algebraicClosure A) :
    ((L[[A]].completeTheory M).typeOf (fun _ : Fin 1 => b)).IsIsolated := by
  classical
  -- a finite `A`-definable set containing `b`, with its defining formula over `A`
  obtain ⟨s, hsf, hsdef, hbs⟩ := hb
  obtain ⟨φ, hφ⟩ := hsdef
  have hφmem (x : M) : x ∈ s ↔ φ.Realize (fun _ : Fin 1 => x) := by
    simpa using Set.ext_iff.mp hφ (fun _ : Fin 1 => x)
  let T := L[[A]].completeTheory M
  let p : T.CompleteType (Fin 1) := T.typeOf (fun _ : Fin 1 => b)
  -- the elements of `s` whose type differs from `p`
  let F : Finset M := hsf.toFinset.filter fun x => T.typeOf (fun _ : Fin 1 => x) ≠ p
  -- each of them is separated from `b` by a formula true at `b` and false at it
  have hsep : ∀ x : ↥F, ∃ χ : (L[[A]]).Formula (Fin 1),
      χ.Realize (fun _ : Fin 1 => b) ∧ ¬ χ.Realize (fun _ : Fin 1 => x.1) := by
    intro x
    obtain ⟨-, hx⟩ := Finset.mem_filter.mp x.2
    have hnotsub : ¬(p ≤ T.typeOf (fun _ : Fin 1 => x.1)) :=
      mt CompleteType.eq_of_le hx.symm
    obtain ⟨σ, hσp, hσx⟩ := Set.not_subset.mp hnotsub
    exact ⟨Formula.equivSentence.symm σ, CompleteType.mem_typeOf.mp hσp,
      mt CompleteType.mem_typeOf.mpr hσx⟩
  choose χ hχb hχx using hsep
  have hT : T.IsComplete := completeTheory.isComplete (L[[A]]) M
  rw [CompleteType.isIsolated_typeOf_iff_of_isComplete hT]
  -- the conjunction confines realizations to `s` and rules out the elements of `F`
  refine ⟨φ ⊓ Formula.iInf χ, ?_, ?_⟩
  · simp only [Formula.realize_inf, Formula.realize_iInf]
    exact ⟨(hφmem b).mp hbs, hχb⟩
  · intro v hv
    have hv' : v = fun _ : Fin 1 => v 0 := funext fun i => by rw [Fin.eq_zero i]
    rw [hv'] at hv ⊢
    simp only [Formula.realize_inf, Formula.realize_iInf] at hv
    by_contra hne
    have hmem : v 0 ∈ F :=
      Finset.mem_filter.mpr ⟨hsf.mem_toFinset.mpr ((hφmem (v 0)).mpr hv.1), hne⟩
    exact hχx ⟨v 0, hmem⟩ (hv.2 ⟨v 0, hmem⟩)

end CompleteType

end Theory

end Language

end FirstOrder
