/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.Definability
import MorleyCategoricityTheorem.ModelTheory.Semantics

/-!
# Definability bridges

This file hosts the correspondence between `Set.Definable` and `Formula.realizationSet` at the
bottom of the project's model-theory import graph, together with the unary definability bridge and
the two counting-definability facts that the idempotence proof of algebraic closure consumes.  The
set-level half of the unary shape conversion, `Set.image_fin_one_eq`, stays in
`ModelTheory.Semantics` beside its formula-level counterpart `Formula.realizationSet_fin_one_image`.
Keeping the module separate lets foundational modules -- notably `ModelTheory.AlgebraicClosure` --
stay inside Mathlib's definability layer plus the low-level `ModelTheory.Semantics`.  The previous
home of these bridges, `ModelTheory.DefinablyFull`, imports `ModelTheory.ElementaryMaps` and hence
the semantic bridges and the type-space layer.

## Main results

- `Set.definable_iff_exists_realizationSet`: a set is definable over `A` exactly when it is the
  realization set of a formula with parameter variables indexed by `A`.
- `Set.definable_realizationSet`: the realization set of a formula with parameters from `A` is
  definable over `A`.
- `Set.definable₁_iff_exists_realizationSet₁`: the unary `Definable₁` specialization of the first
  bridge, in terms of `Formula.realizationSet₁`.
- `Set.definable_setOf_fiber_encard_le`: the tuples over which a formula's `β`-fiber is bounded by
  a natural number form a definable set, which is the definability half of the counting argument
  behind idempotence of algebraic closure.
- `Set.Definable.exists_fiber`: existentially quantifying a definable fibre over a definable set of
  parameters preserves definability, which is the other half.

The first two are the same statements that were previously proved in `ModelTheory.DefinablyFull`;
they moved here so that the algebraic-closure layer can reuse them without importing the semantic
bridges.  The counting-definability lemmas are general definability facts with the same import
requirement; the algebraic-closure idempotence proof consumes them from this module.

Parameter splitting -- moving one split-off parameter of a definable set into a free variable -- is
deliberately not part of this module's API.  Its only consumer is the private counting step
`exists_fiber_formula` of `ModelTheory.AlgebraicClosure`, which needs the split in the
`L.Formula (A ⊕ (Fin 1 ⊕ Fin 1))` shape that `Formula.iExsAtMost` bounds; the construction lives
there so that its coordinates are fixed by its one use rather than guessed here.
-/

universe u v w

namespace Set

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {A : Set M} {α β : Type*}

/-- A set is definable with parameters in `A` exactly when it is the realization set of a formula
whose parameter variables are indexed by `A`.

This restates `Set.definable_iff_exists_formula_sum` through `Formula.realizationSet`, so that the
witnessing formula of a definable set is the formula whose realization set it is. -/
theorem definable_iff_exists_realizationSet {s : Set (α → M)} :
    A.Definable L s ↔ ∃ φ : L.Formula (A ⊕ α), s = φ.realizationSet (Subtype.val : A → M) := by
  rw [definable_iff_exists_formula_sum]
  rfl

/-- The realization set of a formula with parameters drawn from `A` is definable over `A`.

The formula itself is the witness; use this bridge to pass from the unbundled realization-set
representation to `L.DefinableSet` when the Boolean-algebra structure is needed. -/
theorem definable_realizationSet (φ : L.Formula (A ⊕ β)) :
    A.Definable L (φ.realizationSet (Subtype.val : A → M)) :=
  definable_iff_exists_realizationSet.mpr ⟨φ, rfl⟩

/-- A set is definable in one dimension over `A` exactly when it is the unary realization set
`Formula.realizationSet₁` of a formula with parameters indexed by `A`.

This is the unary specialization of `Set.definable_iff_exists_realizationSet`, and the form in which
the algebraic-closure layer consumes definability. -/
theorem definable₁_iff_exists_realizationSet₁ {s : Set M} :
    A.Definable₁ L s ↔
      ∃ φ : L.Formula (A ⊕ Fin 1), s = φ.realizationSet₁ (Subtype.val : A → M) := by
  change A.Definable L {x : Fin 1 → M | x 0 ∈ s} ↔
    ∃ φ : L.Formula (A ⊕ Fin 1), s = φ.realizationSet₁ (Subtype.val : A → M)
  rw [definable_iff_exists_realizationSet]
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, ?_⟩
    have himg : {x : Fin 1 → M | x 0 ∈ s} =
        (fun a : M => fun _ : Fin 1 => a) '' φ.realizationSet₁ (Subtype.val : A → M) := by
      rw [hφ, Formula.realizationSet_fin_one_image]
    have hpre : s = (fun a : M => fun _ : Fin 1 => a) ⁻¹' {x : Fin 1 → M | x 0 ∈ s} := rfl
    rw [hpre, himg, preimage_image_eq _ (fun x y h => congrFun h 0)]
  · rintro ⟨φ, rfl⟩
    exact ⟨φ, by rw [Formula.realizationSet_fin_one_image, image_fin_one_eq]⟩

/-- The tuples over which the `β`-fiber of a formula is bounded by a natural number form a set
definable over the same parameter set.

The fiber over `v : α → M` is `{w : β → M | φ(v, w)}`.  Relabelling the free variables along
`Equiv.sumAssoc` moves the `β`-block into the position quantified by `Formula.iExsAtMost`, whose
semantics is exactly a bound on the extended cardinality of that fiber; this is the definability
half of the counting argument behind idempotence of algebraic closure. -/
theorem definable_setOf_fiber_encard_le {α β : Type*} [Finite β]
    {φ : L.Formula (A ⊕ (α ⊕ β))} (n : ℕ) :
    A.Definable L {v : α → M |
      ({w : β → M | φ.Realize (Sum.elim (Subtype.val : A → M) (Sum.elim v w))}).encard ≤ n} := by
  have hrelabel : ∀ (v : α → M) (w : β → M),
      (φ.relabel (Equiv.sumAssoc A α β).symm).Realize
          (Sum.elim (Sum.elim (Subtype.val : A → M) v) w) ↔
        φ.Realize (Sum.elim (Subtype.val : A → M) (Sum.elim v w)) := by
    intro v w
    rw [Formula.realize_relabel]
    exact iff_of_eq <| congrArg φ.Realize <| funext fun z => by rcases z with a | b | c <;> simp
  have hfiber : ∀ v : α → M,
      (φ.relabel (Equiv.sumAssoc A α β).symm).realizationSet (Sum.elim (Subtype.val : A → M) v) =
        {w : β → M | φ.Realize (Sum.elim (Subtype.val : A → M) (Sum.elim v w))} := by
    intro v
    ext w
    exact hrelabel v w
  have hset : {v : α → M |
        ({w : β → M | φ.Realize (Sum.elim (Subtype.val : A → M) (Sum.elim v w))}).encard ≤ n} =
      ((φ.relabel (Equiv.sumAssoc A α β).symm).iExsAtMost β n).realizationSet
        (Subtype.val : A → M) := by
    ext v
    simp only [Set.mem_ofPred_eq, Formula.mem_realizationSet, Formula.realize_iExsAtMost, hfiber v]
  rw [hset]
  exact definable_realizationSet _

/-- Existentially quantifying the fiber of a definable set over a definable set of parameters
preserves definability.

The result is the set of `w : β → M` for which some `v ∈ V` realizes `φ` on `(v, w)`; the
quantified block `α` is finite, so this is a finite existential quantification.  Together with
`Set.definable_setOf_fiber_encard_le` it is the second half of the counting argument behind
idempotence of algebraic closure, where the parameters `v` range over a finite definable set and
each contributing fiber is bounded. -/
theorem Definable.exists_fiber {α β : Type*} [Finite α] {V : Set (α → M)}
    {φ : L.Formula (A ⊕ (α ⊕ β))} (hV : A.Definable L V) :
    A.Definable L {w : β → M |
      ∃ v : α → M, v ∈ V ∧
        φ.Realize (Sum.elim (Subtype.val : A → M) (Sum.elim v w))} := by
  have hS : A.Definable L {u : (β ⊕ α) → M |
      u ∘ Sum.inr ∈ V ∧ u ∘ Sum.swap ∈ φ.realizationSet (Subtype.val : A → M)} :=
    (hV.preimage_comp Sum.inr).inter ((definable_realizationSet φ).preimage_comp Sum.swap)
  have h := hS.exists_of_finite
  convert h using 1
  ext w
  simp only [Set.mem_ofPred_eq, Formula.mem_realizationSet, Sum.elim_comp_inr, Sum.elim_swap]

end Set
