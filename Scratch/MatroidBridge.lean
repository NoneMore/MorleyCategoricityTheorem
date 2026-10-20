import MorleyCategoricityTheorem.ModelTheory.DefinablyFull
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Rank.ENat

/-!
Reconnaissance draft for the matroid bridge discussed in `docs/plan/algebraic-closure.md`.

This file is evidence for one design decision: whether the relative acl closure on a definable set
should be packaged as a Mathlib `Matroid` now.  It is not part of the Lake library.  Everything in
it compiles except the single deliberate `sorry` below, which marks the finite Steinitz
augmentation obligation -- the one piece that is real mathematics rather than glue.  The `Payoff`
section shows that `IndepMatroid.ofFinitaryCardAugment` accepts the five obligations and yields a
`Matroid` once the augmentation hypothesis is supplied, which is why the missing lemma is recorded
as a downstream capability instead of being discharged here.
-/

universe u v w

open FirstOrder FirstOrder.Language

namespace FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- Algebraicity. -/
def IsAlgebraicOver (A : Set M) (b : M) : Prop :=
  ∃ s : Set M, s.Finite ∧ A.Definable₁ L s ∧ b ∈ s

/-- Algebraic closure. -/
def algebraicClosure (A : Set M) : Set M := {b | IsAlgebraicOver (L := L) A b}

theorem subset_algebraicClosure (A : Set M) : A ⊆ algebraicClosure (L := L) A := by
  intro a ha
  exact ⟨{a}, Set.finite_singleton a, Set.Definable.singleton_of_mem L ha, rfl⟩

theorem algebraicClosure_mono {A B : Set M} (hAB : A ⊆ B) :
    algebraicClosure (L := L) A ⊆ algebraicClosure (L := L) B := by
  rintro b ⟨s, hfin, hdef, hb⟩
  exact ⟨s, hfin, Set.Definable.mono hdef hAB, hb⟩

theorem definable₁_iff_definable {A : Set M} {s : Set M} :
    A.Definable₁ L s ↔ A.Definable L {x : Fin 1 → M | x 0 ∈ s} := Iff.rfl

/-- Finite character. -/
theorem mem_algebraicClosure_iff_exists_finset {A : Set M} {b : M} :
    b ∈ algebraicClosure (L := L) A ↔
      ∃ A₀ : Finset M, (A₀ : Set M) ⊆ A ∧ b ∈ algebraicClosure (L := L) (A₀ : Set M) := by
  constructor
  · rintro ⟨s, hfin, hdef, hb⟩
    obtain ⟨A₀, hA₀, hdef₀⟩ := (Set.definable_iff_finitely_definable).1
      ((definable₁_iff_definable).1 hdef)
    exact ⟨A₀, hA₀, ⟨s, hfin, (definable₁_iff_definable).2 hdef₀, hb⟩⟩
  · rintro ⟨A₀, hA₀, ⟨s, hfin, hdef, hb⟩⟩
    exact ⟨s, hfin, Set.Definable.mono hdef hA₀, hb⟩

variable (A D : Set M)

/-- The relative closure of `def:strongly-minimal-pregeometry`: `cl_A X = acl (A ∪ X) ∩ D`. -/
def relClosure (X : Set M) : Set M := algebraicClosure (L := L) (A ∪ X) ∩ D

/-- Independence in the relative pregeometry: no element lies in the closure of the rest. -/
def RelIndep (X : Set M) : Prop :=
  X ⊆ D ∧ ∀ x ∈ X, x ∉ algebraicClosure (L := L) (A ∪ (X \ {x}))

theorem relIndep_empty : RelIndep (L := L) A D ∅ := by
  refine ⟨Set.empty_subset _, ?_⟩
  intro x hx
  exact absurd hx (Set.notMem_empty x)

theorem relIndep_subset {X Y : Set M} (hY : RelIndep (L := L) A D Y) (hXY : X ⊆ Y) :
    RelIndep (L := L) A D X := by
  refine ⟨hXY.trans hY.1, ?_⟩
  intro x hx hxcl
  exact hY.2 x (hXY hx) (algebraicClosure_mono (L := L) (by
    intro y hy
    rcases hy with hy | hy
    · exact Or.inl hy
    · exact Or.inr (by
        have : y ∈ Y \ {x} := by
          refine ⟨hXY hy.1, hy.2⟩
        exact this)) hxcl)

/-- Compactness of independence follows from finite character of `acl`. -/
theorem relIndep_compact {I : Set M}
    (h : ∀ J, J ⊆ I → J.Finite → RelIndep (L := L) A D J) :
    RelIndep (L := L) A D I := by
  refine ⟨fun x hx => (h {x} ?_ (Set.finite_singleton x)).1 (Set.mem_singleton x), ?_⟩
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    simpa [hy] using hx
  · intro x hxI hxcl
    obtain ⟨A₀, hA₀, hxA₀⟩ := (mem_algebraicClosure_iff_exists_finset (L := L)).1 hxcl
    set J : Set M := ((A₀ : Set M) ∩ (I \ {x})) ∪ {x} with hJdef
    have hJfin : J.Finite :=
      (A₀.finite_toSet.subset Set.inter_subset_left).union (Set.finite_singleton x)
    have hJI : J ⊆ I := by
      intro y hy
      rcases hy with hy | hy
      · exact hy.2.1
      · rw [Set.mem_singleton_iff] at hy
        simpa [hy] using hxI
    have hIndep := h J hJI hJfin
    refine hIndep.2 x (by simp [hJdef]) (algebraicClosure_mono (L := L) ?_ hxA₀)
    intro y hy
    rcases hA₀ hy with hyA | hyI
    · exact Or.inl hyA
    · exact Or.inr ⟨Or.inl ⟨hy, hyI⟩, hyI.2⟩

end FirstOrder.Language

namespace TestMatroid

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- The remaining obligation: finite Steinitz augmentation for relative acl-independence. -/
example (A D : Set M) {I J : Set M} (hI : RelIndep (L := L) A D I) (hIfin : I.Finite)
    (hJ : RelIndep (L := L) A D J) (hJfin : J.Finite) (hcard : I.ncard < J.ncard) :
    ∃ e ∈ J, e ∉ I ∧ RelIndep (L := L) A D (insert e I) := by
  sorry

end TestMatroid

namespace Payoff

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- If the finite Steinitz augmentation is supplied, the relative acl closure is a matroid. -/
noncomputable example (A D : Set M)
    (haug : ∀ I J : Set M, RelIndep (L := L) A D I → I.Finite →
      RelIndep (L := L) A D J → J.Finite → I.ncard < J.ncard →
        ∃ e ∈ J, e ∉ I ∧ RelIndep (L := L) A D (insert e I)) : Matroid M :=
  (IndepMatroid.ofFinitaryCardAugment D (RelIndep (L := L) A D)
    (relIndep_empty (L := L) A D) (fun _ _ => relIndep_subset (L := L) A D)
    haug (fun _ => relIndep_compact (L := L) A D) (fun _ hI => hI.1)).matroid

#check @Matroid.eRk
#check @Matroid.IsBase.encard_eq_eRank
#check @Matroid.ExchangeProperty.encard_isBase_eq
#check @Matroid.closure
#check @Matroid.Indep.notMem_closure_iff_of_notMem

end Payoff
