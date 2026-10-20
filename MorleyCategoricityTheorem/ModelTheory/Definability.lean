/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.Definability
import MorleyCategoricityTheorem.ModelTheory.Semantics

/-!
# Definability bridges and parameter splitting

This file hosts the correspondence between `Set.Definable` and `Formula.realizationSet` at the
bottom of the project's model-theory import graph, together with the parameter-splitting lemmas
that move parameters of a definable set from the parameter set into free variables.  Keeping the
module separate lets foundational modules -- notably `ModelTheory.AlgebraicClosure` -- stay inside
Mathlib's definability layer plus the low-level `ModelTheory.Semantics`.  The previous home of these
bridges, `ModelTheory.DefinablyFull`, imports `ModelTheory.ElementaryMaps` and hence the semantic
bridges and the type-space layer.

## Main results

- `Set.definable_iff_exists_realizationSet`: a set is definable over `A` exactly when it is the
  realization set of a formula with parameter variables indexed by `A`.
- `Set.definable_realizationSet`: the realization set of a formula with parameters from `A` is
  definable over `A`.
- `Set.image_fin_one_eq`: the `Fin 1 → M` tuple with a single entry is the image of that entry.
- `Set.definable₁_iff_exists_realizationSet₁`: the unary `Definable₁` specialization of the first
  bridge, in terms of `Formula.realizationSet₁`.
- `Set.mem_realizationSet_relabel`: relabelling a formula transports membership between the
  realization sets of the original and the relabelled formula, which is the mechanism behind
  parameter splitting: the splitting lemmas relabel along a map that keeps the `A` parameters in
  place and moves the others into the tuple.
- `Set.Definable.fiber`: parameter splitting for one parameter: a set definable over `A ∪ {c}` is
  the `c`-fiber of a set definable over `A` in two variables.
- `Set.Definable.fiber_finset`: the finite-tuple form of parameter splitting, for `F : Finset M`.

The first two are the same statements that were previously proved in `ModelTheory.DefinablyFull`;
they moved here so that the algebraic-closure layer can reuse them without importing the semantic
bridges.  The parameter-splitting lemmas are general definability facts with the same import
requirement; the algebraic-closure idempotence proof consumes them from this module.
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

/-- The `Fin 1 → M` tuple with a single entry is the image of that entry.

This is the set-level bridge between the `Fin 1`-indexed and unary shapes; the formula-level
counterpart is `Formula.realizationSet_fin_one_image`. -/
theorem image_fin_one_eq (s : Set M) :
    (fun x : M => fun _ : Fin 1 => x) '' s = {x : Fin 1 → M | x 0 ∈ s} := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro hx
    exact ⟨x 0, hx, funext fun i => by rw [Fin.eq_zero i]⟩

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

variable {s : Set M}

/-- Membership in a relabelled realization set: a reindexing `g` of the parameters and variables
transports a valuation `v` of a formula with parameters in `A'` into the valuation `e` of the
relabelled formula with parameters in `A`, as long as `g` turns `e` back into `v` pointwise on the
parameter-and-variable part.

The hypothesis is pointwise because that is the form in which reindexings are checked: the
parameter part and the tuple part are read off `g` by cases on the sum, one point at a time.

This is the mechanism behind parameter splitting below: those lemmas choose `g` so that the
parameters of `A'` that lie in `A` keep their variable and the others move into the tuple, which
reduces the fiber statement to this transport. -/
theorem mem_realizationSet_relabel {A' : Set M} {β γ : Type*} {g : ↥A' ⊕ β → ↥A ⊕ γ}
    {φ : L.Formula (↥A' ⊕ β)} {e : γ → M} {v : β → M}
    (h : ∀ x, Sum.elim (Subtype.val : ↥A → M) e (g x) =
      Sum.elim (Subtype.val : ↥A' → M) v x) :
    e ∈ (φ.relabel g).realizationSet (Subtype.val : ↥A → M) ↔
      v ∈ φ.realizationSet (Subtype.val : ↥A' → M) := by
  simp only [Formula.mem_realizationSet, Formula.realize_relabel]
  rw [show Sum.elim (Subtype.val : ↥A → M) e ∘ g =
    Sum.elim (Subtype.val : ↥A' → M) v from funext h]

/-- Parameter splitting: a set definable over `A ∪ {c}` is the `c`-fiber of a set definable over
`A` in two variables.

The witness reads a tuple `x : Fin 2 → M` as the pair `(x 0, x 1)`; the split-off parameter `c`
comes first and the element of the original set second, so the fiber statement is
`s = {a : M | ![c, a] ∈ t}`. -/
theorem Definable.fiber {c : M} (h : (A ∪ {c}).Definable₁ L s) :
    ∃ t : Set (Fin 2 → M), A.Definable L t ∧ {a : M | ![c, a] ∈ t} = s := by
  classical
  obtain ⟨φ, rfl⟩ := definable₁_iff_exists_realizationSet₁ (A := A ∪ {c}) (L := L) |>.1 h
  let g : ↥(A ∪ {c}) ⊕ Fin 1 → ↥A ⊕ Fin 2 := fun x =>
    match x with
    | Sum.inl p =>
      if hp : (p : M) = c then Sum.inr 0
      else Sum.inl ⟨p, by simpa [Set.mem_union, Set.mem_singleton_iff, hp] using p.2⟩
    | Sum.inr _ => Sum.inr 1
  refine ⟨(φ.relabel g).realizationSet (Subtype.val : A → M), definable_realizationSet _, ?_⟩
  ext a
  refine mem_realizationSet_relabel (φ := φ) ?_
  rintro (p | i)
  · by_cases hp : (p : M) = c <;> simp [g, hp]
  · simp [g]

/-- Parameter splitting for a finite tuple of parameters: a set definable over `A ∪ ↑F` is the
fiber over `F` of a set definable over `A`.

The witness reads a tuple `x : ↥F ⊕ Fin 1 → M` with the parameters on the left and the element on
the right, so the fiber statement is `s = {a : M | Sum.elim Subtype.val (fun _ => a) ∈ t}`. -/
theorem Definable.fiber_finset (F : Finset M) (h : (A ∪ (F : Set M)).Definable₁ L s) :
    ∃ t : Set (↥F ⊕ Fin 1 → M), A.Definable L t ∧
      {a : M | Sum.elim (Subtype.val : ↥F → M) (fun _ : Fin 1 => a) ∈ t} = s := by
  classical
  obtain ⟨φ, rfl⟩ :=
    definable₁_iff_exists_realizationSet₁ (A := A ∪ (F : Set M)) (L := L) |>.1 h
  -- a parameter of `A ∪ ↑F` outside `F` is a parameter of `A`
  have hmem : ∀ p : ↥(A ∪ (F : Set M)), (p : M) ∉ (F : Set M) → (p : M) ∈ A := fun p hp => by
    rcases (Set.mem_union _ _ _).1 p.2 with h' | h'
    · exact h'
    · exact absurd h' hp
  let g : ↥(A ∪ (F : Set M)) ⊕ Fin 1 → ↥A ⊕ (↥F ⊕ Fin 1) := fun x =>
    match x with
    | Sum.inl p =>
      if hp : (p : M) ∈ (F : Set M) then Sum.inr (Sum.inl ⟨p, hp⟩)
      else Sum.inl ⟨p, hmem p hp⟩
    | Sum.inr _ => Sum.inr (Sum.inr 0)
  refine ⟨(φ.relabel g).realizationSet (Subtype.val : A → M), definable_realizationSet _, ?_⟩
  ext a
  refine mem_realizationSet_relabel (φ := φ) ?_
  rintro (p | i)
  · by_cases hp : (p : M) ∈ (F : Set M)
    · simp only [g, dite_eq_left hp]
      simp
    · simp only [g, dite_eq_right hp]
      simp
  · simp [g]

end Set
