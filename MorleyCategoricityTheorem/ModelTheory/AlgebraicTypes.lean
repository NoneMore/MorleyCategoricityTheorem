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

The proof takes a finite `A`-definable set `s` containing `b`, with defining formula `φ`.  The
elements of `s` realize only finitely many complete types over `A`; for every such type `q` other
than `tp(b/A)` a formula `θ_q` in `tp(b/A)` but not in `q` separates the two.  Then
`φ ∧ ⋀_q θ_q` belongs to `tp(b/A)`, and any tuple realizing it lies in `s` and hence has one of the
finitely many types of elements of `s`; all of those except `tp(b/A)` are ruled out by the
conjuncts.  Since the theory `completeTheory M` expanded by constants for `A` is complete,
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
  -- the finitely many complete types realized by the elements of `s`
  let ts : Finset (T.CompleteType (Fin 1)) :=
    hsf.toFinset.image (fun x : M => T.typeOf (fun _ : Fin 1 => x))
  -- every other type of an element of `s` admits a formula in `p` but not in it
  have hsep : ∀ q ∈ ts.erase p, ∃ χ : (L[[A]]).Formula (Fin 1),
      Formula.equivSentence χ ∈ p ∧ Formula.equivSentence χ ∉ q := by
    intro q hq
    obtain ⟨hqp, -⟩ := Finset.mem_erase.mp hq
    have hnotsub : ¬((p : (L[[A]])[[Fin 1]].Theory) ⊆ (q : (L[[A]])[[Fin 1]].Theory)) :=
      fun hsub ↦ hqp (CompleteType.eq_of_le hsub).symm
    obtain ⟨σ, hσp, hσq⟩ := Set.not_subset.mp hnotsub
    exact ⟨Formula.equivSentence.symm σ, by simpa using hσp, by simpa using hσq⟩
  choose χ hχp hχq using hsep
  have hT : T.IsComplete := completeTheory.isComplete (L[[A]]) M
  rw [CompleteType.isIsolated_typeOf_iff_of_isComplete hT]
  refine ⟨φ ⊓ Formula.iInf (fun q : ↥(ts.erase p) => χ q.1 q.2), ?_, ?_⟩
  · simp only [Formula.realize_inf, Formula.realize_iInf]
    exact ⟨(hφmem b).mp hbs, fun q ↦ CompleteType.formula_mem_typeOf.mp (hχp q.1 q.2)⟩
  · intro v hv
    have hv' : v = fun _ : Fin 1 => v 0 := funext fun i => by rw [Fin.eq_zero i]
    rw [hv'] at hv ⊢
    simp only [Formula.realize_inf, Formula.realize_iInf] at hv
    obtain ⟨hφv, hχv⟩ := hv
    have hv0 : v 0 ∈ s := (hφmem (v 0)).mpr hφv
    have hmem : T.typeOf (fun _ : Fin 1 => v 0) ∈ ts :=
      Finset.mem_image.mpr ⟨v 0, hsf.mem_toFinset.mpr hv0, rfl⟩
    by_contra hne
    have hqmem : T.typeOf (fun _ : Fin 1 => v 0) ∈ ts.erase p :=
      Finset.mem_erase.mpr ⟨hne, hmem⟩
    exact (hχq _ hqmem) (CompleteType.formula_mem_typeOf.mpr (hχv ⟨_, hqmem⟩))

end CompleteType

end Theory

end Language

end FirstOrder
