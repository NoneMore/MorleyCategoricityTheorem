/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.Definability
import MorleyCategoricityTheorem.ModelTheory.Semantics

/-!
# Algebraic closure over definable sets

An element `b` of an `L`-structure `M` is *algebraic over* a parameter set `A : Set M` when it lies
in a finite set definable with parameters from `A`; the algebraic closure `algebraicClosure A` is
the set of all such elements.  This is blueprint node `def:algebraic-closure`, and it is the
semantic layer's only notion of parameter-definable finiteness.

Both public objects are transparent by design.  `IsAlgebraicOver A b` is a plain `Prop` with body
`∃ s, s.Finite ∧ A.Definable₁ L s ∧ b ∈ s`, and `algebraicClosure A` is the plain set
`{b | IsAlgebraicOver A b}`.  Callers unfold both.  The bundled `L.DefinableSet` would be the wrong
carrier here: algebraicity is not itself a definable set, only witnessed by one.

The element predicate is not named `IsAlgebraic`: that name already belongs to
`FirstOrder.Language.IsAlgebraic`, which says that the language has no relation symbols.

## Main results

- `FirstOrder.Language.definable₁_iff_definable`: `Definable₁` is one-dimensional `Definable`.
- `FirstOrder.Language.mem_algebraicClosure_iff`: unfolding of membership.
- `FirstOrder.Language.subset_algebraicClosure`: a parameter set is contained in its closure.
- `FirstOrder.Language.algebraicClosure_mono`: the closure is monotone in the parameter set.
- `FirstOrder.Language.mem_algebraicClosure_iff_exists_finset`: finite character, so only finitely
  many parameters matter.
- `FirstOrder.Language.isAlgebraicOver_iff_exists_formula`: `b` is algebraic over `A` exactly when
  some formula with parameters from `A` has a finite realization set and is realized at `b`.

## TODO

- Prove idempotence, `algebraicClosure (algebraicClosure A) = algebraicClosure A`, with the
  parameter-splitting and finite-family-collapse lemmas it needs.  The counting argument is recorded
  in `docs/plan/algebraic-closure.md`; the closure laws of `lem:strongly-minimal-closure-laws` need
  the result.
- Prove the cardinality bound `|acl(A)| ≤ |A| + ℵ₀` and the strongly-minimal pregeometry.  Both are
  separate capabilities that consume this module.

## Import boundary

The module imports Mathlib's definability layer plus the project's low-level
`ModelTheory.Semantics`.  It deliberately does not import the semantic bridges
(`ModelTheory.DefinablyFull`, `ModelTheory.ElementaryMaps`) or the type-space modules; the
`Set.Definable` bridge below goes through Mathlib's `Set.definable_iff_exists_formula_sum` directly.
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- `b` is algebraic over the parameter set `A` if it lies in a finite set definable with parameters
from `A`. -/
def IsAlgebraicOver (A : Set M) (b : M) : Prop :=
  ∃ s : Set M, s.Finite ∧ A.Definable₁ L s ∧ b ∈ s

/-- The algebraic closure of a parameter set: the set of all elements algebraic over it. -/
def algebraicClosure (A : Set M) : Set M := {b | IsAlgebraicOver (L := L) A b}

variable {A B : Set M} {s : Set M} {b : M}

/-- `Definable₁` and one-dimensional `Definable` are the same notion. -/
theorem definable₁_iff_definable :
    A.Definable₁ L s ↔ A.Definable L {x : Fin 1 → M | x 0 ∈ s} :=
  Iff.rfl

/-- Unfolding of membership in the algebraic closure. -/
@[simp]
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
theorem isAlgebraicOver_iff_exists_formula :
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

end Language

end FirstOrder
