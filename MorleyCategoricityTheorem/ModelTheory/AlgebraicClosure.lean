/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.Data.Set.Finite.Lattice
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

The language is an explicit argument of both objects, since `A : Set M` and `b : M` do not determine
`L`, so callers write `L.algebraicClosure A`.  It is implicit in the lemmas about them: every lemma
statement mentions `L.algebraicClosure`, `L.IsAlgebraicOver`, or `L.Formula`, so `L` is inferred from
the goal and callers apply the lemmas directly instead of naming it.

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
- `FirstOrder.Language.isAlgebraicOver_of_isAlgebraicOver_union_singleton`: adjoining a single
  element that is already algebraic over the base does not enlarge the algebraic closure.
- `FirstOrder.Language.isAlgebraicOver_of_finset_subset_algebraicClosure`: the same for a finite set
  of parameters that are already algebraic.
- `FirstOrder.Language.algebraicClosure_idem`: algebraic closure is idempotent.
- `Set.Finite.biUnion_fibers`: the finite-family collapse consumed by the counting step of
  idempotence.

The closure laws that `lem:strongly-minimal-closure-laws` needs are therefore all available here:
reflexivity (`subset_algebraicClosure`), monotonicity (`algebraicClosure_mono`), idempotence
(`algebraicClosure_idem`), and finite character (`mem_algebraicClosure_iff_exists_finset`).

## TODO

- Prove the cardinality bound `|acl(A)| ≤ |A| + ℵ₀` and the strongly-minimal pregeometry.  Both are
  separate capabilities that consume this module.

## Import boundary

The module imports Mathlib's definability layer, the project's low-level `ModelTheory.Definability`
bridges, and `ModelTheory.Semantics`.  It also imports `Mathlib.Data.Set.Finite.Lattice` for
`Set.Finite.biUnion`, which the finite-family collapse of the counting step needs.  It deliberately
does not import `ModelTheory.DefinablyFull`, `ModelTheory.ElementaryMaps`, or the type-space modules:
the unary definability bridge used below is `Set.definable₁_iff_exists_realizationSet₁`, not the
`DefinablyFull` realization-set restatement.
-/

universe u v w

namespace Set

/-- Finite-family collapse: a union over a finite index set of sets whose contributing members share
a common extended-cardinality bound is finite.

The counting constructor `Formula.iExsAtMost` supplies the bound `(F i).encard ≤ n` at every
parameter `i` where its counting conjunct holds (see `Formula.realize_iExsAtMost`), and
`Set.finite_of_encard_le_coe` turns that bound into finiteness, so the union over the finitely many
contributing parameters is finite.  This is the set-theoretic half of "an algebraic family of finite
sets has finite union", and it is what the counting step of `algebraicClosure_idem` below consumes;
the index set is an arbitrary finite set so that the caller can restrict it to the fibers the
counting conjunct accepts.

This is pure set-cardinality scaffolding with a single consumer here; promote it to
`Mathlib.Data.Set.Card` when a second caller appears. -/
theorem Finite.biUnion_fibers {ι α : Type*} {I : Set ι} (hI : I.Finite) {F : ι → Set α} {n : ℕ}
    (hF : ∀ i ∈ I, (F i).encard ≤ n) : (⋃ i ∈ I, F i).Finite :=
  hI.biUnion fun i hi => finite_of_encard_le_coe (hF i hi)

end Set

namespace FirstOrder

namespace Language

variable (L : Language.{u, v}) {M : Type w} [L.Structure M]

/-- `b` is algebraic over the parameter set `A` if it lies in a finite set definable with parameters
from `A`. -/
def IsAlgebraicOver (A : Set M) (b : M) : Prop :=
  ∃ s : Set M, s.Finite ∧ A.Definable₁ L s ∧ b ∈ s

/-- The algebraic closure of a parameter set: the set of all elements algebraic over it. -/
def algebraicClosure (A : Set M) : Set M := {b | IsAlgebraicOver L A b}

-- Re-declare the language implicitly for the lemmas: every statement below mentions `L` through
-- `L.algebraicClosure` or `L.IsAlgebraicOver`, so it is inferred and callers need not name it.
variable {L : Language.{u, v}} {M : Type w} [L.Structure M]
variable {A B : Set M} {b : M}

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

/-! ### Idempotence

Idempotence is the only closure law that is not immediate from the definition.  Finite character
writes `b ∈ acl (acl A)` as `b ∈ acl (A ∪ ↑F)` for a finite `F ⊆ acl A`, so it suffices to adjoin
one algebraic element at a time and iterate over `F`.

Adjoining a single `c ∈ acl A` is a counting argument.  Split the parameter
(`exists_fiber_formula`): a set definable over `A ∪ {c}` becomes the `c`-fiber of a formula over `A`
whose two free-variable blocks are the split-off parameter and the element.  Since the fiber through
`c` is finite, the tuples whose fiber has at most that many elements are the only ones that can
contribute an element of `acl A`; they form a definable set
(`Set.definable_setOf_fiber_encard_le`), they sit over the finite `A`-definable set of possible
values of `c`, and the union of their fibers is finite (`Set.Finite.biUnion_fibers`).  Projecting
that union (`Set.Definable.exists_fiber`) gives the finite `A`-definable set witnessing
`b ∈ acl A`. -/

/-- Parameter splitting in the shape the counting argument needs: the `c`-fiber of a formula with
parameters from `A`.

The split-off parameter `c` occupies its own `Fin 1` block and the original element a second one, so
that `Formula.iExsAtMost` can bound the element block and `Set.Definable.exists_fiber` can quantify
over the parameter block.  The split is private because its conclusion is fixed to the
`L.Formula (A ⊕ (Fin 1 ⊕ Fin 1))` coordinates of this one argument; `ModelTheory.Definability`
deliberately exports no parameter-splitting lemma. -/
private theorem exists_fiber_formula {A : Set M} {s : Set M} {c : M}
    (h : (A ∪ {c}).Definable₁ L s) :
    ∃ φ : L.Formula (A ⊕ (Fin 1 ⊕ Fin 1)),
      ∀ x : M, φ.Realize (Sum.elim (Subtype.val : A → M)
        (Sum.elim (fun _ : Fin 1 => c) (fun _ : Fin 1 => x))) ↔ x ∈ s := by
  classical
  obtain ⟨φ, rfl⟩ := Set.definable₁_iff_exists_realizationSet₁.1 h
  let g : ↥(A ∪ {c}) ⊕ Fin 1 → ↥A ⊕ (Fin 1 ⊕ Fin 1) := fun z =>
    match z with
    | Sum.inl p =>
      if hp : (p : M) = c then Sum.inr (Sum.inl 0)
      else Sum.inl ⟨p, by simpa [Set.mem_union, Set.mem_singleton_iff, hp] using p.2⟩
    | Sum.inr _ => Sum.inr (Sum.inr 0)
  refine ⟨φ.relabel g, fun x => ?_⟩
  rw [Formula.realize_relabel, Formula.mem_realizationSet₁]
  refine iff_of_eq <| congrArg φ.Realize <| funext fun z => ?_
  rcases z with p | i
  · by_cases hp : (p : M) = c <;> simp [g, hp]
  · simp [g]

/-- Adjoining a single element that is already algebraic over the base does not enlarge the
algebraic closure: `b ∈ acl (A ∪ {c})` implies `b ∈ acl A` when `c ∈ acl A`.

This is the counting step of idempotence.  A finite set definable over `A ∪ {c}` is the `c`-fiber
of an `A`-definable family; the tuples of that family whose fiber is bounded by the size of the
fiber through `c` form a finite `A`-definable set, and the projection of the bounded fibers over it
is finite, `A`-definable, and contains everything algebraic over `A ∪ {c}`. -/
theorem isAlgebraicOver_of_isAlgebraicOver_union_singleton {A : Set M} {c b : M}
    (hc : L.IsAlgebraicOver A c) (hb : L.IsAlgebraicOver (A ∪ {c}) b) :
    L.IsAlgebraicOver A b := by
  classical
  obtain ⟨S, hSfin, hSdef, hcS⟩ := hc
  obtain ⟨s, hsfin, hsdef, hbs⟩ := hb
  obtain ⟨φ, hφ⟩ := exists_fiber_formula hsdef
  -- the fiber through `c` is `s`, so its size bounds the fibers that may contribute
  obtain ⟨m, hm⟩ := hsfin.exists_encard_eq_coe
  set Fib : (Fin 1 → M) → Set (Fin 1 → M) :=
    fun v => {w | φ.Realize (Sum.elim (Subtype.val : A → M) (Sum.elim v w))} with hFibdef
  -- the tuples whose fiber is small: they sit over the finite set `S`, hence are finite
  set V : Set (Fin 1 → M) := {v | v 0 ∈ S} ∩ {v | (Fib v).encard ≤ m} with hVdef
  have hFibc : Fib (fun _ : Fin 1 => c) = {w : Fin 1 → M | w 0 ∈ s} := by
    ext w
    have hw : w = fun _ : Fin 1 => w 0 := funext fun i => by rw [Fin.eq_zero i]
    simp only [hFibdef, Set.mem_ofPred_eq]
    rw [hw]
    exact hφ (w 0)
  have hFibc_encard : (Fib (fun _ : Fin 1 => c)).encard = (m : ℕ∞) := by
    have hinj : Set.InjOn (fun x : M => fun _ : Fin 1 => x) s := fun _ _ _ _ h => congrFun h 0
    rw [hFibc, ← Set.image_fin_one_eq, Set.InjOn.encard_image hinj, hm]
  have hVbound : ∀ v ∈ V, (Fib v).encard ≤ (m : ℕ∞) := by
    intro v hv
    rw [hVdef] at hv
    exact hv.2
  have hVfin : V.Finite := by
    rw [hVdef, ← Set.image_fin_one_eq]
    exact (hSfin.image _).subset Set.inter_subset_left
  have hVdefin : A.Definable L V := by
    rw [hVdef]
    exact hSdef.inter (Set.definable_setOf_fiber_encard_le m)
  have hcV : (fun _ : Fin 1 => c) ∈ V := by
    rw [hVdef, Set.mem_inter_iff]
    exact ⟨by simpa using hcS, hFibc_encard.le⟩
  -- the elements that are algebraic over `A` through this family, in tuple coordinates
  set T : Set (Fin 1 → M) :=
    {w | ∃ v : Fin 1 → M, v ∈ V ∧
      φ.Realize (Sum.elim (Subtype.val : A → M) (Sum.elim v w))} with hTdef
  have hTfin : T.Finite := by
    refine (Set.Finite.biUnion_fibers hVfin hVbound).subset ?_
    rintro w ⟨v, hv, hw⟩
    exact Set.mem_iUnion₂.mpr ⟨v, hv, hw⟩
  have hTdefin : A.Definable L T := hVdefin.exists_fiber
  -- an element of `M` is the one-entry tuple of itself, so `U` is the range of `w ↦ w 0` on `T`
  set U : Set M := {x | (fun _ : Fin 1 => x) ∈ T} with hUdef
  refine ⟨U, ?_, ?_, ⟨fun _ : Fin 1 => c, hcV, (hφ b).2 hbs⟩⟩
  · refine (hTfin.image (fun w : Fin 1 → M => w 0)).subset ?_
    rintro x hx
    exact ⟨fun _ : Fin 1 => x, hx, rfl⟩
  · show A.Definable L {w : Fin 1 → M | w 0 ∈ U}
    have hset : {w : Fin 1 → M | w 0 ∈ U} = T := by
      ext w
      have hw : (fun _ : Fin 1 => w 0) = w := funext fun i => by rw [Fin.eq_zero i]
      simp only [Set.mem_ofPred_eq, hUdef, hw]
    rw [hset]
    exact hTdefin

/-- Adjoining finitely many elements that are already algebraic over the base does not enlarge the
algebraic closure: `b ∈ acl (A ∪ ↑F)` implies `b ∈ acl A` for finite `F ⊆ acl A`, hence
`acl (A ∪ ↑F) = acl A` by monotonicity. -/
theorem isAlgebraicOver_of_finset_subset_algebraicClosure {b : M} :
    ∀ F : Finset M, (F : Set M) ⊆ L.algebraicClosure A →
      L.IsAlgebraicOver (A ∪ (F : Set M)) b → L.IsAlgebraicOver A b := by
  classical
  intro F
  induction F using Finset.induction with
  | empty =>
    intro _ hb
    simpa using hb
  | insert c F hcF ih =>
    intro hF hb
    -- the remaining parameters are still algebraic, and so is the newly adjoined one
    have hF' : (F : Set M) ⊆ L.algebraicClosure A := fun x hx =>
      hF (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hx))
    have hc : c ∈ L.algebraicClosure A :=
      hF (Finset.mem_coe.mpr (Finset.mem_insert_self c F))
    -- move the adjoined element to the end of the parameter set
    have hAset : A ∪ (↑(insert c F) : Set M) = (A ∪ ↑F) ∪ {c} := by
      ext x
      simp only [Set.mem_union, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_insert]
      tauto
    rw [hAset] at hb
    exact ih hF' (isAlgebraicOver_of_isAlgebraicOver_union_singleton
      (algebraicClosure_mono Set.subset_union_left hc) hb)

/-- Algebraic closure is idempotent: closing a parameter set twice gives the same set.

This is the closure law that `lem:strongly-minimal-closure-laws` needs before exchange, so it is
proved here rather than deferred to the pregeometry layer. -/
theorem algebraicClosure_idem (A : Set M) :
    L.algebraicClosure (L.algebraicClosure A) = L.algebraicClosure A := by
  refine Set.Subset.antisymm ?_ (algebraicClosure_mono subset_algebraicClosure)
  intro b hb
  -- finite character reduces the outer parameters to a finite set of algebraic elements
  rw [mem_algebraicClosure_iff_exists_finset] at hb
  obtain ⟨F, hF, hbF⟩ := hb
  exact isAlgebraicOver_of_finset_subset_algebraicClosure F hF
    (algebraicClosure_mono Set.subset_union_right hbF)

end Language

end FirstOrder
