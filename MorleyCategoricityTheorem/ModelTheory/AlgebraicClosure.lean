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
# Algebraic closure

`L.IsAlgebraicOver A b` means that `b` belongs to a finite `A`-definable set.
`L.algebraicClosure A` is the set of such elements (blueprint
`def:algebraic-closure`).

## Main results

- `subset_algebraicClosure`, `algebraicClosure_mono`,
  `mem_algebraicClosure_iff_exists_finset`: basic closure laws and finite character.
- `isAlgebraicOver_iff_exists_realizationSet₁`,
  `isAlgebraicOver_iff_exists_formula`: formula characterizations.
- `isAlgebraicOver_of_isAlgebraicOver_union_singleton`,
  `isAlgebraicOver_of_finset_subset_algebraicClosure`,
  `algebraicClosure_idem`: idempotence via counting finite fibers.

The cardinality bound and strongly-minimal pregeometry are deferred.
-/

universe u v w

namespace Set

/-- A finite union of fibers with uniformly bounded `encard` is finite. -/
theorem Finite.biUnion_fibers {ι α : Type*} {I : Set ι} (hI : I.Finite) {F : ι → Set α} {n : ℕ}
    (hF : ∀ i ∈ I, (F i).encard ≤ n) : (⋃ i ∈ I, F i).Finite :=
  hI.biUnion fun i hi => finite_of_encard_le_coe (hF i hi)

end Set

namespace FirstOrder

namespace Language

variable (L : Language.{u, v}) {M : Type w} [L.Structure M]

/-- `b` is algebraic over `A` if it belongs to a finite `A`-definable set. -/
def IsAlgebraicOver (A : Set M) (b : M) : Prop :=
  ∃ s : Set M, s.Finite ∧ A.Definable₁ L s ∧ b ∈ s

/-- The set of elements algebraic over `A`. -/
def algebraicClosure (A : Set M) : Set M := {b | IsAlgebraicOver L A b}

-- Re-declare the language implicitly for the lemmas: every statement below mentions `L` through
-- `L.algebraicClosure` or `L.IsAlgebraicOver`, so it is inferred and callers need not name it.
variable {L : Language.{u, v}} {M : Type w} [L.Structure M]
variable {A B : Set M} {b : M}

/-- Membership in the algebraic closure unfolds to algebraicity. -/
@[simp]
theorem mem_algebraicClosure_iff : b ∈ L.algebraicClosure A ↔ L.IsAlgebraicOver A b :=
  Iff.rfl

/-- Every parameter is algebraic over its parameter set. -/
theorem subset_algebraicClosure : A ⊆ L.algebraicClosure A := by
  intro a ha
  exact ⟨{a}, Set.finite_singleton a, Set.Definable.singleton_of_mem L ha, rfl⟩

/-- Algebraic closure is monotone in its parameters. -/
theorem algebraicClosure_mono (hAB : A ⊆ B) : L.algebraicClosure A ⊆ L.algebraicClosure B := by
  rintro b ⟨s, hfin, hdef, hb⟩
  exact ⟨s, hfin, Set.Definable.mono hdef hAB, hb⟩

/-- Algebraicity depends on only finitely many parameters. -/
theorem mem_algebraicClosure_iff_exists_finset :
    b ∈ L.algebraicClosure A ↔
      ∃ A₀ : Finset M, (A₀ : Set M) ⊆ A ∧ b ∈ L.algebraicClosure (A₀ : Set M) := by
  constructor
  · rintro ⟨s, hfin, hdef, hb⟩
    obtain ⟨A₀, hA₀, hdef₀⟩ := Set.definable_iff_finitely_definable.1 hdef
    exact ⟨A₀, hA₀, ⟨s, hfin, hdef₀, hb⟩⟩
  · rintro ⟨A₀, hA₀, ⟨s, hfin, hdef, hb⟩⟩
    exact ⟨s, hfin, Set.Definable.mono hdef hA₀, hb⟩

/-- Characterize algebraicity by a finite unary formula realization set. -/
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

/-- Characterize algebraicity using `Fin 1 → M` realization tuples. -/
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

Finite character reduces `b ∈ acl (acl A)` to finitely many algebraic
parameters. To eliminate one such parameter, bound the fibers of a definable
family by a counting formula and project their finite union.
-/

/-- Express an `(A ∪ {c})`-definable set as a `c`-fiber over `A`. -/
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

/-- Adjoining an element algebraic over `A` does not enlarge its closure.

The proof bounds the relevant fibers of an `A`-definable family and
projects their finite union.
-/
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

/-- Eliminate finitely many algebraic parameters by induction. -/
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

/-- Algebraic closure is idempotent. -/
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
