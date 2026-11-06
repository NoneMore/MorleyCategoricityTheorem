/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import MorleyCategoricityTheorem.ModelTheory.AlgebraicClosure
import MorleyCategoricityTheorem.ModelTheory.PartialTypeRealizations

/-!
# Nonalgebraic types have many distinct realizations

If `b` is not algebraic over a parameter set `B ⊆ M`, then for every `n` some elementary extension of
`M` carries `n + 1` pairwise distinct realizations of `tp(b/B)` (blueprint
`lem:nonalgebraic-type-many-realizations`).

The proof forms the partial type of unary formulas over `B` true at `b`. Every finite conjunction of
such formulas has infinitely many realizations in `M`: otherwise its realization set would be a
finite `B`-definable set containing `b`, contradicting nonalgebraicity. The finite-witness theorem
`Theory.PartialType.exists_distinct_realizations` then produces the elementary extension. Parameters
are compared through the canonical embedding into the model of the elementary diagram, whose action
on all of `M` is recorded explicitly.

## Main results

- `Language.infinite_finset_realizations_of_not_mem_algebraicClosure`: every finite conjunction of
  formulas of `tp(b/B)` has infinitely many realizations in `M`.
- `Language.exists_distinct_realizations_of_not_mem_algebraicClosure`: arbitrarily many pairwise
  distinct realizations of `tp(b/B)` in an elementary extension.

The results follow the design of the reference project
[`NoneMore/StabilityTheory`](https://github.com/NoneMore/StabilityTheory); they are reproved here
against this repository's APIs and its Mathlib revision.
-/

universe u v w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M : Type w'} [L.Structure M] {B : Set M} {b : M}

/-- Every finite conjunction of unary formulas over `B` true at `b` has infinitely many
realizations in `M`, provided `b` is not algebraic over `B`.

A finite realization set of such a conjunction is a finite `B`-definable set containing `b`. -/
theorem infinite_finset_realizations_of_not_mem_algebraicClosure
    (hb : b ∉ L.algebraicClosure B) (s : Finset (L[[B]].Formula (Fin 1)))
    (hs : ∀ φ ∈ s, φ.Realize (fun _ : Fin 1 => b)) :
    {x : M | ∀ φ ∈ s, φ.Realize (fun _ : Fin 1 => x)}.Infinite := by
  intro hfin
  -- Collect the fragment into a single formula so that it becomes one definable set.
  set ψ : L[[B]].Formula (Fin 1) := Formula.iInf fun φ : s => (φ : L[[B]].Formula (Fin 1))
    with hψdef
  have hψ : ∀ x : M, ψ.Realize (fun _ : Fin 1 => x) ↔
      ∀ φ ∈ s, φ.Realize (fun _ : Fin 1 => x) := by
    intro x
    simp only [hψdef, Formula.realize_iInf, Subtype.forall]
  -- Its realizations form a finite `B`-definable set containing `b`.
  have hfin' : {x : M | ψ.Realize (fun _ : Fin 1 => x)}.Finite :=
    hfin.subset fun _ hx => (hψ _).1 hx
  have hdef : B.Definable₁ L {x : M | ψ.Realize (fun _ : Fin 1 => x)} :=
    ⟨ψ, Set.ext fun w => by
      have hw : (fun _ : Fin 1 => w 0) = w := funext fun i => congrArg w (Fin.eq_zero i).symm
      simp only [Set.mem_ofPred_eq, hw]⟩
  exact hb ⟨_, hfin', hdef, (hψ b).2 hs⟩

/-- **Nonalgebraic types have arbitrarily many distinct conjugates.** If `b` is not algebraic over
`B ⊆ M`, then for every `n` some model of the elementary diagram of `M` carries `n + 1` pairwise
distinct realizations of `tp(b/B)`.

Parameters are interpreted along the canonical elementary embedding `e : M ↪ₑ[L] N`, which acts on
all of `M` as the corresponding constants, so the last conjunct transports the `L[[B]]`-formulas
true at `b` to their `L[[M]]`-counterparts realized by the witnesses. -/
theorem exists_distinct_realizations_of_not_mem_algebraicClosure
    (hb : b ∉ L.algebraicClosure B) (n : ℕ) :
    ∃ N : Theory.ModelType.{max u w', v, max (max u w') v} (L.elementaryDiagram M),
      ∃ e : M ↪ₑ[L] N, ∃ x : Fin (n + 1) → N,
        Function.Injective x ∧
          (∀ a : M, e a = (L.con a : N)) ∧
            ∀ (i : Fin (n + 1)) (φ : L[[B]].Formula (Fin 1)),
              φ.Realize (fun _ : Fin 1 => b) →
                ((L.lhomWithConstantsMap ((↑) : B → M)).onFormula φ).Realize
                  (fun _ : Fin 1 => x i) := by
  have : Nonempty M := ⟨b⟩
  -- `tp(b/B)`, as a set of formulas with constants for the parameters.
  let p : Set (L[[B]].Formula (Fin 1)) := {φ | φ.Realize (fun _ : Fin 1 => b)}
  have hp : ∀ s : Finset (L[[B]].Formula (Fin 1)),
      (↑s : Set (L[[B]].Formula (Fin 1))) ⊆ p →
        {x : M | ∀ φ ∈ s, φ.Realize (fun _ : Fin 1 => x)}.Infinite :=
    fun s hs => infinite_finset_realizations_of_not_mem_algebraicClosure hb s hs
  exact Theory.PartialType.exists_distinct_realizations (p := p) hp n

end Language

end FirstOrder
