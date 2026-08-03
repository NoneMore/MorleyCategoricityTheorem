/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.Data.Set.Card
import Mathlib.ModelTheory.Semantics
import MorleyCategoricityTheorem.ModelTheory.Syntax

/-!
# Additional First-Order Semantics

This file extends `Mathlib.ModelTheory.Semantics` with realization theorems for the constructors in
`MorleyCategoricityTheorem.ModelTheory.Syntax`. Its model-theoretic declarations are intended to
migrate directly to `Mathlib/ModelTheory/Semantics.lean`, near `Formula.realize_iExsUnique`.

For `φ : L.Formula (α ⊕ β)` and parameters `v : α → M`, the relevant fiber is the set of
assignments `x : β → M` for which `φ.Realize (Sum.elim v x)` holds.

Variable layout matches the local syntax layer and Mathlib's `Formula.iExs` / `Formula.iExsUnique`:
free parameters are indexed by `α`, and the quantified tuple is indexed by a finite type `β`.

## Main results

- `FirstOrder.Language.Formula.realize_iExsAtLeast_iff_exists_injective`: normalize realization of
  `iExsAtLeast` into an injective family `Fin n → (β → M)` of solutions.
- `FirstOrder.Language.Formula.realize_iExsAtLeast`: characterize the lower-bound constructor by
  `(n : ℕ∞) ≤ Set.encard` of the realization fiber.
- `FirstOrder.Language.Formula.realize_iExsAtMost`: characterize the upper-bound constructor by
  `Set.encard ≤ n`.
- `FirstOrder.Language.Formula.realize_iExsExactly`: characterize exact finite cardinality by
  `Set.encard = n`.
- `FirstOrder.Language.Formula.realize_existsExactlyLeft`: semantic theorem for the caller-facing
  variable order `Sum.elim x v`.
- `FirstOrder.Language.Formula.realize_existsRight`: characterize `existsRight` by existence of an
  assignment to the right variables.
- `FirstOrder.Language.Formula.realize_existsLeft`: the symmetric statement for `existsLeft`.
- `FirstOrder.Language.Formula.exists_fin_params` (and the `BoundedFormula` analogue): every formula
  over a parameter set is, up to realization, a substitution instance of a constant-free formula in
  finitely many extra variables.

## Proof outline

First unfold only the new formula constructors and simplify with the existing realization theorems
for indexed existential quantification, finite conjunctions, relabeling, equality, negation, and
conjunction. Convert pairwise coordinate inequality into injectivity of the candidate family.

Then isolate the set-theoretic step in a pure helper relating an injection from `Fin n` into a set
to a lower bound on its extended cardinality. Search `Mathlib.Data.Set.Card` and the `ENat` API
before filling this helper. If Mathlib lacks it, a generally stated helper should migrate to the
appropriate cardinality file rather than into `Mathlib.ModelTheory.Semantics`.

The public cardinality characterizations are tagged with `@[simp]`. The injective-family normal form
is an intermediate theorem and is not a simp lemma.

## Boundary cases

- Exact cardinality zero is equivalent to having no realizing `β`-tuple.
- Exact cardinality one is semantically equivalent to `Formula.iExsUnique`.
- Having at most `n` realizations rules out `n + 1` pairwise distinct realizations.
- The statements remain correct when `β` is empty or when `n = 0`.

This module must not import `Mathlib.ModelTheory.ElementaryMaps`; those applications belong to the
corresponding local extension of `ElementaryMaps`.
-/

universe u v w

open Function Set

namespace Set

/-- An injection `Fin n → α` into a set is equivalent to a lower bound of `n` on its extended
cardinality.

This is pure set-cardinality scaffolding for the semantic theorems below. Prefer an existing Mathlib
lemma if one is available; otherwise migrate a general form to `Mathlib.Data.Set.Card`. -/
theorem le_encard_iff_exists_injection_fin {α : Type*} (s : Set α) (n : ℕ) :
    (n : ℕ∞) ≤ s.encard ↔ ∃ f : Fin n → α, (∀ i, f i ∈ s) ∧ Injective f := by
  constructor
  · intro h
    obtain ⟨t, hts, hte⟩ := exists_subset_encard_eq h
    letI := (finite_of_encard_eq_coe hte).fintype
    let e := Fintype.equivFinOfCardEq <| ENat.coe_inj.mp <| (coe_fintypeCard t).trans hte
    exact ⟨Subtype.val ∘ e.symm, fun i ↦ hts (e.symm i).2,
      (Equiv.injective_comp e.symm Subtype.val).mpr Subtype.val_injective⟩
  · rintro ⟨f, hf, hfi⟩
    simpa only [ENat.card_eq_coe_fintype_card, Fintype.card_fin,
      ENat.card_coe_set_eq] using ENat.card_le_card_of_injective
        (f := fun i : Fin n ↦ ⟨f i, hf i⟩) (fun _ _ hi ↦ hfi (Subtype.ext_iff.mp hi))

end Set

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {α β : Type*} {M : Type w}

namespace Formula

variable [L.Structure M]

/-- Realization of `iExsAtLeast` is equivalent to the existence of an injective family of `n`
pairwise distinct realizing `β`-tuples. -/
theorem realize_iExsAtLeast_iff_exists_injective [Finite β]
    (φ : L.Formula (α ⊕ β)) (v : α → M) (n : ℕ) :
    (φ.iExsAtLeast β n).Realize v ↔
      ∃ f : Fin n → (β → M), (∀ i, φ.Realize (Sum.elim v (f i))) ∧ Injective f := by
  simp [iExsAtLeast]
  refine (Equiv.curry (Fin n) β M).exists_congr fun u ↦ and_congr ?_ ?_
  · refine forall_congr' fun i ↦ iff_of_eq <| congrArg φ.Realize ?_
    funext x
    cases x <;> rfl
  · rw [Function.injective_iff_pairwise_ne]
    simp [Pairwise, funext_iff, Function.onFun]

/-- The lower-bound constructor asserts that the realization fiber has extended cardinality at least
`n`. -/
@[simp]
theorem realize_iExsAtLeast [Finite β] (φ : L.Formula (α ⊕ β)) (v : α → M) (n : ℕ) :
    (φ.iExsAtLeast β n).Realize v ↔
      (n : ℕ∞) ≤ {x : β → M | φ.Realize (Sum.elim v x)}.encard := by
  rw [realize_iExsAtLeast_iff_exists_injective]
  exact Iff.symm (le_encard_iff_exists_injection_fin _ _)

/-- The upper-bound constructor asserts that the realization fiber has extended cardinality at most
`n`. -/
@[simp]
theorem realize_iExsAtMost [Finite β] (φ : L.Formula (α ⊕ β)) (v : α → M) (n : ℕ) :
    (φ.iExsAtMost β n).Realize v ↔
      {x : β → M | φ.Realize (Sum.elim v x)}.encard ≤ n := by
  simpa [iExsAtMost] using ENat.lt_coe_add_one_iff

/-- Exact finite cardinality of the realization fiber. -/
@[simp]
theorem realize_iExsExactly [Finite β] (φ : L.Formula (α ⊕ β)) (v : α → M) (n : ℕ) :
    (φ.iExsExactly β n).Realize v ↔
      {x : β → M | φ.Realize (Sum.elim v x)}.encard = n := by
  simpa [iExsExactly] using Iff.symm ge_antisymm_iff

/-- Semantic characterization of `existsExactlyLeft` in the caller-facing variable order
`β ⊕ α`, where free parameters are on the right. -/
@[simp]
theorem realize_existsExactlyLeft [Finite β] (φ : L.Formula (β ⊕ α)) (v : α → M) (n : ℕ) :
    (φ.existsExactlyLeft n).Realize v ↔
      {x : β → M | φ.Realize (Sum.elim x v)}.encard = n := by
  simp [existsExactlyLeft]

/-- `existsRight` realizes exactly when some assignment to the right variables realizes `φ`.

The `[Nonempty M]` hypothesis is needed to extend a witness on the free right variables of `φ` to a
total assignment on `β`. -/
@[simp]
theorem realize_existsRight [DecidableEq α] [DecidableEq β] [Nonempty M]
    (φ : L.Formula (α ⊕ β)) (v : α → M) :
    (φ.existsRight).Realize v ↔ ∃ x : β → M, φ.Realize (Sum.elim v x) := by
  simp only [existsRight, Formula.realize_iExs, Formula.realize_relabel]
  constructor
  · rintro ⟨x, hx⟩
    let y : β → M := fun b =>
      if h : b ∈ φ.freeVarFinset.toRight then x ⟨b, h⟩ else Classical.choice ‹Nonempty M›
    exact ⟨y, (BoundedFormula.realize_restrictFreeVar (Sum.elim v y) (by grind)).mp hx⟩
  · rintro ⟨y, hy⟩
    exact ⟨fun b ↦ y b,
      (BoundedFormula.realize_restrictFreeVar (Sum.elim v y) (by grind)).mpr hy⟩

/-- `existsLeft` realizes exactly when some assignment to the left variables realizes `φ`.

This is the left-handed counterpart of `realize_existsRight`; the `[Nonempty M]` hypothesis is
needed to extend the witness to a total assignment on `α`. -/
@[simp]
theorem realize_existsLeft [DecidableEq α] [DecidableEq β] [Nonempty M]
    (φ : L.Formula (α ⊕ β)) (v : β → M) :
    (φ.existsLeft).Realize v ↔ ∃ x : α → M, φ.Realize (Sum.elim x v) := by
  rw [existsLeft, realize_existsRight]
  simp only [Formula.realize_relabel]
  refine exists_congr fun x ↦ iff_of_eq <| congrArg φ.Realize ?_
  funext z
  cases z <;> rfl

section BoundaryCases

/-- Exact cardinality zero means there is no realizing `β`-tuple. -/
theorem realize_iExsExactly_zero [Finite β] (φ : L.Formula (α ⊕ β)) (v : α → M) :
    (φ.iExsExactly β 0).Realize v ↔ ¬∃ x : β → M, φ.Realize (Sum.elim v x) := by
  simp only [realize_iExsExactly, Nat.cast_zero, Set.encard_eq_zero, not_exists]
  exact Set.eq_empty_iff_forall_notMem

/-- Exact cardinality one is semantically equivalent to unique existence. -/
theorem realize_iExsExactly_one_iff_iExsUnique [Finite β]
    (φ : L.Formula (α ⊕ β)) (v : α → M) :
    (φ.iExsExactly β 1).Realize v ↔ (φ.iExsUnique β).Realize v := by
  simp [realize_iExsUnique, Set.encard_eq_one]
  constructor
  · rintro ⟨x, hx⟩
    have hmem := Set.ext_iff.mp hx
    exact ⟨x, (hmem x).2 rfl, fun y hy ↦ (hmem y).1 hy⟩
  · rintro ⟨x, hx, hunique⟩
    refine ⟨x, Set.ext fun y ↦ ?_⟩
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨hunique y, fun hy ↦ hy ▸ hx⟩

/-- Having at most `n` realizations is the negation of having at least `n + 1` realizations. -/
theorem realize_iExsAtMost_iff_not_iExsAtLeast_succ [Finite β]
    (φ : L.Formula (α ⊕ β)) (v : α → M) (n : ℕ) :
    (φ.iExsAtMost β n).Realize v ↔ ¬(φ.iExsAtLeast β (n + 1)).Realize v := by
  simpa using Iff.symm ENat.lt_coe_add_one_iff

/-- Having at most `n` realizations rules out any injective family of `n + 1` solutions. -/
theorem realize_iExsAtMost_iff_not_exists_injection [Finite β]
    (φ : L.Formula (α ⊕ β)) (v : α → M) (n : ℕ) :
    (φ.iExsAtMost β n).Realize v ↔
      ¬∃ f : Fin (n + 1) → (β → M),
        (∀ i, φ.Realize (Sum.elim v (f i))) ∧ Injective f := by
  simpa only [realize_iExsAtMost_iff_not_iExsAtLeast_succ] using
    not_congr (realize_iExsAtLeast_iff_exists_injective φ v (n + 1))

end BoundaryCases

end Formula

namespace BoundedFormula

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- Every bounded formula over a parameter set is, up to realization, a substitution instance of a
constant-free bounded formula in finitely many extra variables. -/
lemma exists_fin_params {α : Type*} {B : Set M} {k : ℕ} (φ : (L[[B]]).BoundedFormula α k) :
    ∃ n : ℕ, ∃ b : Fin n → B, ∃ φ' : L.BoundedFormula (α ⊕ Fin n) k,
      ∀ v : α → M, ∀ xs : Fin k → M,
        φ.Realize v xs ↔ φ'.Realize (Sum.elim v (fun i => (b i : M))) xs := by
  classical
  let φ₀ : L.BoundedFormula (B ⊕ α) k := BoundedFormula.constantsVarsEquiv φ
  let S : Finset B := φ₀.freeVarFinset.toLeft
  let n : ℕ := S.card
  let e : S ≃ Fin n := Finset.equivFin S
  let b : Fin n → B := fun i => (e.symm i : B)
  let f : φ₀.freeVarFinset → (α ⊕ Fin n) := fun z =>
    match h : z.1 with
    | Sum.inl x => Sum.inr (e ⟨x, (Finset.mem_toLeft).mpr (h ▸ z.2)⟩)
    | Sum.inr w => Sum.inl w
  refine ⟨n, b, BoundedFormula.restrictFreeVar φ₀ f, fun v xs => ?_⟩
  simp_rw [φ₀]
  rw [BoundedFormula.realize_restrictFreeVar (Sum.elim (fun x : B => (L.con x : M)) v) (by
    rintro ⟨z, hz⟩
    cases z <;> simp [f, b]), BoundedFormula.realize_constantsVarsEquiv]

end BoundedFormula

namespace Formula

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- Every formula over a parameter set is, up to realization, a substitution instance of a
constant-free formula in finitely many extra variables. -/
lemma exists_fin_params {α : Type*} {B : Set M} (φ : (L[[B]]).Formula α) :
    ∃ n : ℕ, ∃ b : Fin n → B, ∃ φ' : L.Formula (α ⊕ Fin n),
      ∀ v : α → M, φ.Realize v ↔ φ'.Realize (Sum.elim v (fun i => (b i : M))) := by
  classical
  rcases BoundedFormula.exists_fin_params φ with ⟨n, b, φ', h⟩
  exact ⟨n, b, φ', fun v => h v default⟩

end Formula

end Language

end FirstOrder
