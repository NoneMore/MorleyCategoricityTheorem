/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.Definability
import MorleyCategoricityTheorem.ModelTheory.Definability
import MorleyCategoricityTheorem.ModelTheory.Semantics

/-!
# Algebraic closure over definable sets

An element `b` of an `L`-structure `M` is *algebraic over* a parameter set `A : Set M` when it lies
in a finite set definable with parameters from `A`; the algebraic closure `algebraicClosure A` is
the set of all such elements.  This is blueprint node `def:algebraic-closure`, and it is the
semantic layer's only notion of parameter-definable finiteness.

Both public objects are transparent by design.  `L.IsAlgebraicOver A b` is a plain `Prop` with body
`∃ s, s.Finite ∧ A.Definable₁ L s ∧ b ∈ s`, and `L.algebraicClosure A` is the plain set
`{b | L.IsAlgebraicOver A b}`.  Callers unfold both.  The bundled `L.DefinableSet` would be the
wrong carrier here: algebraicity is not itself a definable set, only witnessed by one.

The language is an explicit argument of both, so callers write `L.algebraicClosure A` rather than
threading `(L := L)` through every use: `A : Set M` and `b : M` do not determine `L`.

The element predicate is not named `IsAlgebraic`: that name already belongs to
`FirstOrder.Language.IsAlgebraic`, which says that the language has no relation symbols.

## Main results

- `FirstOrder.Language.IsAlgebraicOver` and `FirstOrder.Language.algebraicClosure`: the notion of
  algebraicity and the closure it generates.
- `FirstOrder.Language.mem_algebraicClosure_iff`: unfolding of membership.
- `FirstOrder.Language.subset_algebraicClosure`: a parameter set is contained in its closure.
- `FirstOrder.Language.algebraicClosure_mono`: the closure is monotone in the parameter set.
- `FirstOrder.Language.mem_algebraicClosure_iff_exists_finset`: finite character, so only finitely
  many parameters matter.
- `FirstOrder.Language.isAlgebraicOver_iff_exists_realizationSet₁`: `b` is algebraic over `A`
  exactly when some formula with parameters from `A` has a finite unary realization set containing
  `b`; the unary form is the primary statement.
- `FirstOrder.Language.isAlgebraicOver_iff_exists_formula`: the `Fin 1 → M` form of the same
  characterization, for consumers that work with `Formula.realizationSet` directly.

## TODO

- Prove idempotence, `L.algebraicClosure (L.algebraicClosure A) = L.algebraicClosure A`, with the
  parameter-splitting and finite-family-collapse lemmas it needs.  The counting argument is recorded
  in `docs/plan/algebraic-closure.md`; the closure laws of `lem:strongly-minimal-closure-laws` need
  the result.
- Prove the cardinality bound `|acl(A)| ≤ |A| + ℵ₀` and the strongly-minimal pregeometry.  Both are
  separate capabilities that consume this module.

## Import boundary

The module imports Mathlib's definability layer, the project's low-level `ModelTheory.Definability`
bridges, and `ModelTheory.Semantics`.  It deliberately does not import `ModelTheory.DefinablyFull`,
`ModelTheory.ElementaryMaps`, or the type-space modules: the unary definability bridge used below is
`Set.definable₁_iff_exists_realizationSet₁`, not the `DefinablyFull` realization-set restatement.
-/

universe u v w

namespace FirstOrder

namespace Language

variable (L : Language.{u, v}) {M : Type w} [L.Structure M]

/-- `b` is algebraic over the parameter set `A` if it lies in a finite set definable with parameters
from `A`. -/
def IsAlgebraicOver (A : Set M) (b : M) : Prop :=
  ∃ s : Set M, s.Finite ∧ A.Definable₁ L s ∧ b ∈ s

/-- The algebraic closure of a parameter set: the set of all elements algebraic over it. -/
def algebraicClosure (A : Set M) : Set M := {b | IsAlgebraicOver L A b}

variable {A B : Set M} {s : Set M} {b : M}

/-- Unfolding of membership in the algebraic closure. -/
@[simp]
theorem mem_algebraicClosure_iff : b ∈ L.algebraicClosure A ↔ L.IsAlgebraicOver A b :=
  Iff.rfl

/-- Parameter sets are contained in their algebraic closure (reflexivity). -/
theorem subset_algebraicClosure : A ⊆ L.algebraicClosure A := by
  intro a ha
  exact ⟨{a}, Set.finite_singleton a, Set.Definable.singleton_of_mem L ha, rfl⟩

/-- Algebraic closure is monotone in the parameter set. -/
theorem algebraicClosure_mono (hAB : A ⊆ B) : L.algebraicClosure A ⊆ L.algebraicClosure B := by
  rintro b ⟨s, hfin, hdef, hb⟩
  exact ⟨s, hfin, Set.Definable.mono hdef hAB, hb⟩

/-- Finite character: only finitely many parameters matter. -/
theorem mem_algebraicClosure_iff_exists_finset :
    b ∈ L.algebraicClosure A ↔
      ∃ A₀ : Finset M, (A₀ : Set M) ⊆ A ∧ b ∈ L.algebraicClosure (A₀ : Set M) := by
  constructor
  · rintro ⟨s, hfin, hdef, hb⟩
    obtain ⟨A₀, hA₀, hdef₀⟩ := Set.definable_iff_finitely_definable.1 hdef
    exact ⟨A₀, hA₀, ⟨s, hfin, hdef₀, hb⟩⟩
  · rintro ⟨A₀, hA₀, ⟨s, hfin, hdef, hb⟩⟩
    exact ⟨s, hfin, Set.Definable.mono hdef hA₀, hb⟩

/-- The unary formula-level form: `b` is algebraic over `A` iff some formula with parameters from
`A` has a finite unary realization set containing `b`.

This is the primary form; `isAlgebraicOver_iff_exists_formula` rewrites it to `Fin 1 → M` tuples. -/
theorem isAlgebraicOver_iff_exists_realizationSet₁ :
    L.IsAlgebraicOver A b ↔
      ∃ φ : L.Formula (A ⊕ Fin 1),
        (φ.realizationSet₁ (Subtype.val : A → M)).Finite ∧
          b ∈ φ.realizationSet₁ (Subtype.val : A → M) := by
  constructor
  · rintro ⟨s, hfin, hdef, hb⟩
    obtain ⟨φ, rfl⟩ := Set.definable₁_iff_exists_realizationSet₁.1 hdef
    exact ⟨φ, hfin, hb⟩
  · rintro ⟨φ, hfin, hb⟩
    exact ⟨_, hfin, Set.definable₁_iff_exists_realizationSet₁.2 ⟨φ, rfl⟩, hb⟩

/-- The `Fin 1 → M` form of `isAlgebraicOver_iff_exists_realizationSet₁`, for consumers that work
with `Formula.realizationSet` directly. -/
theorem isAlgebraicOver_iff_exists_formula :
    L.IsAlgebraicOver A b ↔
      ∃ φ : L.Formula (A ⊕ Fin 1),
        (φ.realizationSet (Subtype.val : A → M)).Finite ∧
          φ.Realize (Sum.elim (Subtype.val : A → M) (fun _ : Fin 1 => b)) := by
  rw [isAlgebraicOver_iff_exists_realizationSet₁]
  constructor
  · rintro ⟨φ, hfin, hb⟩
    exact ⟨φ, by rw [Formula.realizationSet_fin_one_image]; exact hfin.image _, hb⟩
  · rintro ⟨φ, hfin, hreal⟩
    refine ⟨φ, ?_, hreal⟩
    rw [Formula.realizationSet_fin_one_image] at hfin
    exact hfin.of_finite_image (fun x _ y _ h => congrFun h 0)

end Language

end FirstOrder
