import Mathlib.ModelTheory.Definability
import MorleyCategoricityTheorem.ModelTheory.Semantics

/-!
Reconnaissance draft for blueprint `def:algebraic-closure`; see `docs/plan/algebraic-closure.md`.

`Scratch/` is outside the Lake library, so `lake build MorleyCategoricityTheorem` and
`lake exe mk_all --check` ignore this file.  The declarations are intended to move into
`MorleyCategoricityTheorem/ModelTheory/AlgebraicClosure.lean` once the plan is approved.

The import list is the planned production boundary: Mathlib's definability layer plus the
project's low-level semantic layer (`ModelTheory.Semantics`, which supplies
`Formula.realizationSet`).  In particular this file does not import `DefinablyFull`,
`ElementaryMaps`, or any type-space module.  The `Set.Definable` bridge below is Mathlib's
`Set.definable_iff_exists_formula_sum`, not the project's `Definable`-only restatement.

Checked with `lake env lean Scratch/AlgebraicClosure.lean` against Lean `v4.34.1` and Mathlib
`v4.34.1`; the file contains no `sorry` and needs no tactic import.
-/

universe u v w

open FirstOrder FirstOrder.Language

namespace FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- `b` is algebraic over the parameter set `A` if it lies in a finite set definable with
parameters from `A`. -/
def IsAlgebraicOver (A : Set M) (b : M) : Prop :=
  ∃ s : Set M, s.Finite ∧ A.Definable₁ L s ∧ b ∈ s

/-- The algebraic closure of a parameter set: all elements algebraic over it. -/
def algebraicClosure (A : Set M) : Set M := {b | IsAlgebraicOver (L := L) A b}

variable {A B : Set M} {s : Set M} {b c : M}

/-- `Definable₁` and one-dimensional `Definable` are the same notion. -/
theorem definable₁_iff_definable :
    A.Definable₁ L s ↔ A.Definable L {x : Fin 1 → M | x 0 ∈ s} :=
  Iff.rfl

/-- Unfolding of membership in the algebraic closure. -/
theorem mem_algebraicClosure_iff :
    b ∈ algebraicClosure (L := L) A ↔ IsAlgebraicOver (L := L) A b :=
  Iff.rfl

/-- Parameter sets are contained in their algebraic closure (reflexivity). -/
theorem subset_algebraicClosure : A ⊆ algebraicClosure (L := L) A := by
  intro a ha
  exact ⟨{a}, Set.finite_singleton a, Set.Definable.singleton_of_mem L ha, rfl⟩

/-- Algebraic closure is monotone in the parameter set. -/
theorem algebraicClosure_mono (hAB : A ⊆ B) :
    algebraicClosure (L := L) A ⊆ algebraicClosure (L := L) B := by
  rintro b ⟨s, hfin, hdef, hb⟩
  exact ⟨s, hfin, Set.Definable.mono hdef hAB, hb⟩

/-- Finite character: only finitely many parameters matter. -/
theorem mem_algebraicClosure_iff_exists_finset :
    b ∈ algebraicClosure (L := L) A ↔
      ∃ A₀ : Finset M, (A₀ : Set M) ⊆ A ∧ b ∈ algebraicClosure (L := L) (A₀ : Set M) := by
  constructor
  · rintro ⟨s, hfin, hdef, hb⟩
    obtain ⟨A₀, hA₀, hdef₀⟩ := (Set.definable_iff_finitely_definable).1
      ((definable₁_iff_definable).1 hdef)
    exact ⟨A₀, hA₀, ⟨s, hfin, (definable₁_iff_definable).2 hdef₀, hb⟩⟩
  · rintro ⟨A₀, hA₀, ⟨s, hfin, hdef, hb⟩⟩
    exact ⟨s, hfin, Set.Definable.mono hdef hA₀, hb⟩

/-- The formula-level form: `b` is algebraic over `A` iff some formula with parameters from `A`
whose realization set is finite is realized at `b`. -/
theorem isAlgebraicOver_iff_exists_formula {A : Set M} {b : M} :
    IsAlgebraicOver (L := L) A b ↔
      ∃ (φ : L.Formula (A ⊕ Fin 1)), (φ.realizationSet (Subtype.val : A → M)).Finite ∧
        φ.Realize (Sum.elim (Subtype.val : A → M) (fun _ : Fin 1 => b)) := by
  constructor
  · rintro ⟨s, hfin, hdef, hb⟩
    obtain ⟨φ, hφ⟩ := (Set.definable_iff_exists_formula_sum (α := Fin 1)).1
      ((definable₁_iff_definable).1 hdef)
    refine ⟨φ, ?_, ?_⟩
    · change ({x : Fin 1 → M | φ.Realize (Sum.elim (Subtype.val : A → M) x)} : Set _).Finite
      rw [← hφ]
      exact hfin.preimage (f := fun x : Fin 1 → M => x 0)
        (fun x _ y _ h => funext fun i => by rw [Fin.eq_zero i]; exact h)
    · have : (fun _ : Fin 1 => b) ∈ {x : Fin 1 → M | φ.Realize (Sum.elim (Subtype.val) x)} := by
        rw [← hφ]; exact hb
      simpa [Formula.realizationSet, Set.mem_ofPred_eq] using this
  · rintro ⟨φ, hfin, hb⟩
    refine ⟨{b' : M | φ.Realize (Sum.elim (Subtype.val : A → M) (fun _ : Fin 1 => b'))},
      ?_, ?_, hb⟩
    · have himg :
          {b' : M | φ.Realize (Sum.elim (Subtype.val : A → M) (fun _ : Fin 1 => b'))} =
            (fun x : Fin 1 → M => x 0) '' φ.realizationSet (Subtype.val : A → M) := by
        ext b'
        constructor
        · intro h
          exact ⟨fun _ => b', h, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          have hx' : (fun _ : Fin 1 => x 0) = x :=
            funext fun i => (congrArg x (Fin.eq_zero i)).symm
          simpa [Formula.realizationSet, Set.mem_ofPred_eq, hx'] using hx
      rw [himg]
      exact hfin.image _
    · refine (definable₁_iff_definable).2 ((Set.definable_iff_exists_formula_sum).2 ⟨φ, ?_⟩)
      ext x
      have hx : (fun _ : Fin 1 => x 0) = x :=
        funext fun i => (congrArg x (Fin.eq_zero i)).symm
      simp only [Set.mem_ofPred_eq, hx]

end FirstOrder.Language
